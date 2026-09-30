-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.shapley_unique_symmetric_strongly_monotonic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:11:51.727205+00:00
-- url     : https://prove2.me/submissions/4c84bbc1-d91e-4425-9690-7e9c944c6ade

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms



namespace MonotonicSolutions.StrongMono

open Finset

noncomputable def shF {n : ℕ} (v : Game n) : Fin n → ℝ :=
  Supermodularity.Cooperative.ShapleyValue v.1

lemma mem_pe {n : ℕ} (a : Fin n) (S : Finset (Fin n)) :
    S ∈ (univ.erase a).powerset ↔ a ∉ S := by
  rw [Finset.mem_powerset, Finset.subset_erase]; simp

lemma marginal_of_not_mem {n : ℕ} (v : Finset (Fin n) → ℝ) (i : Fin n) (S : Finset (Fin n))
    (h : i ∉ S) : marginal v i S = v (insert i S) - v S := by
  simp [marginal, h]

lemma shF_mono {n : ℕ} (v w : Game n) (i : Fin n)
    (h : ∀ S, marginal w.1 i S ≤ marginal v.1 i S) : shF w i ≤ shF v i := by
  unfold shF Supermodularity.Cooperative.ShapleyValue
  apply Finset.sum_le_sum
  intro S hS
  have hiS : i ∉ S := (mem_pe i S).mp hS
  apply mul_le_mul_of_nonneg_left
  · have := h S; rwa [marginal_of_not_mem _ _ _ hiS, marginal_of_not_mem _ _ _ hiS] at this
  · positivity

lemma shF_SM {n : ℕ} : IsStronglyMonotonic (@shF n) := fun v w i h => shF_mono v w i h

lemma shF_marg {n : ℕ} : IsMarginal (@shF n) := fun v w i h =>
  le_antisymm (shF_mono w v i (fun S => (h S).le)) (shF_mono v w i (fun S => (h S).ge))

lemma shF_symm {n : ℕ} : IsSymmetric (@shF n) := by
  intro π v i
  unfold shF Supermodularity.Cooperative.ShapleyValue permGame
  apply Finset.sum_nbij' (fun S => S.map π.symm.toEmbedding) (fun R => R.map π.toEmbedding)
  · intro S hS
    simp only [Finset.mem_coe, mem_pe] at hS ⊢
    rw [Finset.mem_map_equiv]; simpa using hS
  · intro S hS
    simp only [Finset.mem_coe, mem_pe] at hS ⊢
    rw [Finset.mem_map_equiv]; simpa using hS
  · intro S _; ext x; simp [Finset.mem_map_equiv]
  · intro S _; ext x; simp [Finset.mem_map_equiv]
  · intro S _
    simp [Finset.map_insert]


lemma coef_eq {n : ℕ} (v : Game n) (T : Finset (Fin n)) :
    (T.card : ℝ) * ((((T.card - 1).factorial * (n - (T.card - 1) - 1).factorial : ℝ)
        / n.factorial) * v.1 T)
      - ((n - T.card : ℕ) : ℝ) * (((T.card.factorial * (n - T.card - 1).factorial : ℝ)
        / n.factorial) * v.1 T)
      = if T = univ then v.1 T else 0 := by
  classical
  by_cases h0 : T = ∅
  · subst h0; simp [v.2]
  have ht : T.card ≤ n := by simpa using Finset.card_le_univ T
  have hpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
  by_cases hu : T = univ
  · rw [if_pos hu]
    have hc : T.card = n := by rw [hu]; simp
    rw [hc]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, sub_zero,
      show m + 1 - 1 = m by omega, show m + 1 - m - 1 = 0 by omega, Nat.factorial_zero]
    rw [Nat.factorial_succ]; push_cast
    have : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [if_neg hu]
    have hlt : T.card < n := by
      by_contra hh
      apply hu
      exact Finset.eq_univ_of_card T (by simp; omega)
    obtain ⟨s, hs⟩ : ∃ s, T.card = s + 1 := ⟨T.card - 1, by omega⟩
    obtain ⟨r, hr⟩ : ∃ r, n = s + r + 2 := ⟨n - s - 2, by omega⟩
    rw [hs]
    subst hr
    simp only [show s + 1 - 1 = s by omega, show s + r + 2 - s - 1 = r + 1 by omega,
      show s + r + 2 - (s + 1) = r + 1 by omega, show s + r + 2 - (s + 1) - 1 = r by omega]
    rw [Nat.factorial_succ s, Nat.factorial_succ r]; push_cast; ring

lemma shF_eff {n : ℕ} (v : Game n) : ∑ i, shF v i = v.1 univ := by
  classical
  let w : ℕ → ℝ := fun s => (s.factorial * (n - s - 1).factorial : ℝ) / n.factorial
  have hA : ∀ i : Fin n, ∑ S ∈ (univ.erase i).powerset, w S.card * v.1 (insert i S)
      = ∑ T : Finset (Fin n), if i ∈ T then w (T.card - 1) * v.1 T else 0 := by
    intro i
    rw [← Finset.sum_filter]
    apply Finset.sum_nbij' (fun S => insert i S) (fun T => T.erase i)
    · intro S hS; simp
    · intro T hT
      simp only [Finset.mem_coe, Finset.mem_filter] at hT
      simp only [Finset.mem_coe, mem_pe]; simp
    · intro S hS
      simp only [Finset.mem_coe, mem_pe] at hS
      exact Finset.erase_insert hS
    · intro T hT
      simp only [Finset.mem_coe, Finset.mem_filter] at hT
      exact Finset.insert_erase hT.2
    · intro S hS
      simp only [Finset.mem_coe, mem_pe] at hS
      rw [Finset.card_insert_of_notMem hS]; simp
  have hB : ∀ i : Fin n, ∑ S ∈ (univ.erase i).powerset, w S.card * v.1 S
      = ∑ T : Finset (Fin n), if i ∉ T then w T.card * v.1 T else 0 := by
    intro i
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S; rw [Finset.mem_filter, mem_pe]; simp
  have hsplit : ∑ i, shF v i = ∑ i, (∑ S ∈ (univ.erase i).powerset, w S.card * v.1 (insert i S))
      - ∑ i, ∑ S ∈ (univ.erase i).powerset, w S.card * v.1 S := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
    unfold shF Supermodularity.Cooperative.ShapleyValue
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro S _; ring
  rw [hsplit]
  simp_rw [hA, hB]
  rw [Finset.sum_comm (s := (univ : Finset (Fin n))), Finset.sum_comm (s := (univ : Finset (Fin n)))]
  have h1 : ∀ T : Finset (Fin n), ∑ i : Fin n, (if i ∈ T then w (T.card - 1) * v.1 T else 0)
      = (T.card : ℝ) * (w (T.card - 1) * v.1 T) := by
    intro T; rw [Finset.sum_ite_mem]; simp
  have h2 : ∀ T : Finset (Fin n), ∑ i : Fin n, (if i ∉ T then w T.card * v.1 T else 0)
      = ((n - T.card : ℕ) : ℝ) * (w T.card * v.1 T) := by
    intro T
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  simp_rw [h1, h2]
  rw [← Finset.sum_sub_distrib]
  simp only [w]
  simp_rw [coef_eq v]
  simp


def uf {n : ℕ} (D : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ T ∈ D, if T ⊆ S then c T else 0

lemma marginal_uf_filter {n : ℕ} (D : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℝ)
    (i : Fin n) (S : Finset (Fin n)) :
    marginal (uf D c) i S = marginal (uf (D.filter (i ∈ ·)) c) i S := by
  classical
  unfold marginal uf
  have key : ∀ S' S'' : Finset (Fin n), (∀ T : Finset (Fin n), i ∉ T → (T ⊆ S' ↔ T ⊆ S'')) →
      (∑ T ∈ D, if T ⊆ S' then c T else 0) - (∑ T ∈ D, if T ⊆ S'' then c T else 0) =
      (∑ T ∈ D.filter (i ∈ ·), if T ⊆ S' then c T else 0)
        - (∑ T ∈ D.filter (i ∈ ·), if T ⊆ S'' then c T else 0) := by
    intro S' S'' h
    rw [← Finset.sum_filter_add_sum_filter_not D (i ∈ ·) (fun T => if T ⊆ S' then c T else 0),
      ← Finset.sum_filter_add_sum_filter_not D (i ∈ ·) (fun T => if T ⊆ S'' then c T else 0)]
    have : ∑ T ∈ D.filter (fun T => ¬ i ∈ T), (if T ⊆ S' then c T else 0)
        = ∑ T ∈ D.filter (fun T => ¬ i ∈ T), (if T ⊆ S'' then c T else 0) := by
      apply Finset.sum_congr rfl; intro T hT; rw [Finset.mem_filter] at hT; simp only [h T hT.2]
    rw [this]; ring
  split_ifs with hi
  · apply key; intro T hT; constructor
    · intro h x hx; rw [Finset.mem_erase]
      exact ⟨fun e => hT (e ▸ hx), h hx⟩
    · intro h; exact h.trans (Finset.erase_subset _ _)
  · apply key; intro T hT; constructor
    · intro h x hx
      have := h hx
      rw [Finset.mem_insert] at this
      rcases this with e | e
      · exact absurd (e ▸ hx) hT
      · exact e
    · intro h; exact h.trans (Finset.subset_insert _ _)

lemma swap_mem {n : ℕ} (i j : Fin n) (T : Finset (Fin n)) (hi : i ∈ T) (hj : j ∈ T) :
    ∀ x ∈ T, Equiv.swap i j x ∈ T := by
  intro x hx
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

theorem agree_uf {n : ℕ} (φ₁ φ₂ : Game n → Fin n → ℝ)
    (hA1 : IsAllocationProcedure φ₁) (hS1 : IsSymmetric φ₁) (hM1 : IsMarginal φ₁)
    (hA2 : IsAllocationProcedure φ₂) (hS2 : IsSymmetric φ₂) (hM2 : IsMarginal φ₂) :
    ∀ D : Finset (Finset (Fin n)), (∀ T ∈ D, T.Nonempty) →
      ∀ (c : Finset (Fin n) → ℝ) (v : Game n), v.1 = uf D c → φ₁ v = φ₂ v := by
  classical
  intro D
  induction D using Finset.strongInduction with
  | H D ih =>
  intro hne c v hv
  have hout : ∀ i, (∃ T ∈ D, i ∉ T) → φ₁ v i = φ₂ v i := by
    rintro i ⟨T0, hT0, hiT0⟩
    have hsub : D.filter (i ∈ ·) ⊂ D := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro h
      have : T0 ∈ D.filter (i ∈ ·) := by rw [h]; exact hT0
      exact hiT0 (Finset.mem_filter.mp this).2
    let w : Game n := ⟨uf (D.filter (i ∈ ·)) c, by
      unfold uf; apply Finset.sum_eq_zero; intro T hT
      have := hne T (Finset.mem_filter.mp hT).1
      rw [if_neg]; intro h; obtain ⟨x, hx⟩ := this
      exact absurd (h hx) (Finset.notMem_empty x)⟩
    have hmw : ∀ S, marginal v.1 i S = marginal w.1 i S := by
      intro S; rw [hv]; exact marginal_uf_filter D c i S
    have := ih _ hsub (fun T hT => hne T (Finset.mem_filter.mp hT).1) c w rfl
    rw [hM1 v w i hmw, hM2 v w i hmw, this]
  have hin_eq : ∀ (φ : Game n → Fin n → ℝ), IsSymmetric φ → ∀ i j,
      (∀ T ∈ D, i ∈ T ∧ j ∈ T) → φ v i = φ v j := by
    intro φ hS i j hij
    have hp : permGame (Equiv.swap i j) v = v := by
      apply Subtype.ext; funext S
      show v.1 (S.map (Equiv.swap i j).symm.toEmbedding) = v.1 S
      rw [hv]; unfold uf; apply Finset.sum_congr rfl; intro T hT
      obtain ⟨hi, hj⟩ := hij T hT
      have hsw := swap_mem i j T hi hj
      have : T ⊆ S.map (Equiv.swap i j).symm.toEmbedding ↔ T ⊆ S := by
        constructor
        · intro h x hx
          have := h (hsw x hx)
          rw [Finset.mem_map_equiv] at this
          simpa using this
        · intro h x hx
          rw [Finset.mem_map_equiv]
          simpa using h (hsw x hx)
      simp only [this]
    have := hS (Equiv.swap i j) v i
    rw [hp, Equiv.swap_apply_left] at this
    exact this.symm
  funext k
  by_cases hk : ∃ T ∈ D, k ∉ T
  · exact hout k hk
  · push_neg at hk
    have hsum1 := hA1 v
    have hsum2 := hA2 v
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => ∀ T ∈ D, i ∈ T)] at hsum1 hsum2
    have e1 : ∑ i ∈ univ.filter (fun i => ¬ ∀ T ∈ D, i ∈ T), φ₁ v i
        = ∑ i ∈ univ.filter (fun i => ¬ ∀ T ∈ D, i ∈ T), φ₂ v i := by
      apply Finset.sum_congr rfl; intro i hi
      simp only [Finset.mem_filter] at hi; push_neg at hi; exact hout i hi.2
    have c1 : ∑ i ∈ univ.filter (fun i => ∀ T ∈ D, i ∈ T), φ₁ v i
        = ((univ.filter (fun i => ∀ T ∈ D, i ∈ T)).card : ℝ) * φ₁ v k := by
      rw [Finset.sum_congr rfl (g := fun _ => φ₁ v k), Finset.sum_const, nsmul_eq_mul]
      intro i hi; simp only [Finset.mem_filter] at hi
      exact hin_eq φ₁ hS1 i k (fun T hT => ⟨hi.2 T hT, hk T hT⟩)
    have c2 : ∑ i ∈ univ.filter (fun i => ∀ T ∈ D, i ∈ T), φ₂ v i
        = ((univ.filter (fun i => ∀ T ∈ D, i ∈ T)).card : ℝ) * φ₂ v k := by
      rw [Finset.sum_congr rfl (g := fun _ => φ₂ v k), Finset.sum_const, nsmul_eq_mul]
      intro i hi; simp only [Finset.mem_filter] at hi
      exact hin_eq φ₂ hS2 i k (fun T hT => ⟨hi.2 T hT, hk T hT⟩)
    have hpos : (0:ℝ) < ((univ.filter (fun i => ∀ T ∈ D, i ∈ T)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨k, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hk⟩
    have : ((univ.filter (fun i => ∀ T ∈ D, i ∈ T)).card : ℝ) * φ₁ v k
        = ((univ.filter (fun i => ∀ T ∈ D, i ∈ T)).card : ℝ) * φ₂ v k := by linarith
    exact mul_left_cancel₀ hpos.ne' this

noncomputable def mob {n : ℕ} (v : Finset (Fin n) → ℝ) (T : Finset (Fin n)) : ℝ :=
  v T - ∑ R ∈ T.ssubsets.attach, mob v R.1
termination_by T.card
decreasing_by exact Finset.card_lt_card (Finset.mem_ssubsets.mp R.2)

lemma mob_sum {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    v S = ∑ T ∈ S.powerset, mob v T := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self S)]
  rw [mob, Finset.sum_attach S.ssubsets (fun R => mob v R)]
  have : S.ssubsets = S.powerset.erase S := rfl
  rw [this]; ring

lemma mob_empty {n : ℕ} (v : Finset (Fin n) → ℝ) (h : v ∅ = 0) : mob v ∅ = 0 := by
  have := mob_sum v ∅
  simp at this; linarith

theorem agree {n : ℕ} (φ₁ φ₂ : Game n → Fin n → ℝ)
    (hA1 : IsAllocationProcedure φ₁) (hS1 : IsSymmetric φ₁) (hM1 : IsMarginal φ₁)
    (hA2 : IsAllocationProcedure φ₂) (hS2 : IsSymmetric φ₂) (hM2 : IsMarginal φ₂)
    (v : Game n) : φ₁ v = φ₂ v := by
  classical
  apply agree_uf φ₁ φ₂ hA1 hS1 hM1 hA2 hS2 hM2 (univ.filter (fun T => T.Nonempty))
    (fun T hT => (Finset.mem_filter.mp hT).2) (mob v.1) v
  funext S
  rw [mob_sum v.1 S]
  unfold uf
  rw [Finset.sum_filter]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun T => T ⊆ S)]
  rw [Finset.sum_eq_zero (s := univ.filter (fun T => ¬ T ⊆ S))]
  · rw [add_zero]
    have hps : univ.filter (fun T => T ⊆ S) = S.powerset := by ext T; simp
    rw [hps]
    apply Finset.sum_congr rfl
    intro T hTS
    by_cases hT : T.Nonempty
    · simp [hT, Finset.mem_powerset.mp hTS]
    · rw [Finset.not_nonempty_iff_eq_empty] at hT
      subst hT; simp [mob_empty v.1 v.2]
  · intro T hT; simp only [Finset.mem_filter] at hT; simp [hT.2]

theorem marg_core {n : ℕ} (φ : Game n → Fin n → ℝ) :
    (IsAllocationProcedure φ ∧ IsSymmetric φ ∧ IsMarginal φ) ↔
      ∀ v : Game n, φ v = Supermodularity.Cooperative.ShapleyValue v.1 := by
  constructor
  · rintro ⟨hA, hS, hM⟩ v
    exact agree φ shF hA hS hM shF_eff shF_symm shF_marg v
  · intro h
    have : φ = shF := funext h
    subst this
    exact ⟨shF_eff, shF_symm, shF_marg⟩

theorem sm_core {n : ℕ} (φ : Game n → Fin n → ℝ) :
    (IsAllocationProcedure φ ∧ IsSymmetric φ ∧ IsStronglyMonotonic φ) ↔
      ∀ v : Game n, φ v = Supermodularity.Cooperative.ShapleyValue v.1 := by
  constructor
  · rintro ⟨hA, hS, hSM⟩
    refine (marg_core φ).mp ⟨hA, hS, ?_⟩
    intro v w i h
    exact le_antisymm (hSM w v i (fun S => (h S).le)) (hSM v w i (fun S => (h S).ge))
  · intro h
    have : φ = shF := funext h
    subst this
    exact ⟨shF_eff, shF_symm, shF_SM⟩

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono


theorem solution {n : ℕ} (φ : Game n → Fin n → ℝ) :
    (IsAllocationProcedure φ ∧ IsSymmetric φ ∧ IsStronglyMonotonic φ) ↔
      ∀ v : Game n, φ v = Supermodularity.Cooperative.ShapleyValue v.1 := by
  exact sm_core φ
