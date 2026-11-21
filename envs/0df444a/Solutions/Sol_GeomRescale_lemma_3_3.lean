-- Prove2me | solution 1 for GeomRescale.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:59:14.519374+00:00
-- url     : https://prove2.me/submissions/5c588781-717d-4b00-9834-62817c57f1e6

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_IsSortedBy
import Definitions.Def_GeomRescale_IsMinSet
import Definitions.Def_GeomRescale_enlarge

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace Aux_GeomRescale_lemma_3_3
open GeomRescale

theorem mem_before {n : ℕ} (σ : Equiv.Perm (Fin n)) (u v : Fin n) :
    u ∈ before σ v ↔ σ u < σ v := by
  simp [before]

theorem univ_lower {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsLowerIdeal σ Finset.univ :=
  fun _ _ w _ => Finset.mem_univ w

theorem dimret {n : ℕ} {f : Finset (Fin n) → ℝ} (hsub : Submodular f) {A B : Finset (Fin n)}
    (hAB : A ⊆ B) {v : Fin n} (hv : v ∉ B) :
    f (insert v B) - f B ≤ f (insert v A) - f A := by
  have h := hsub (insert v A) B
  have h1 : insert v A ∪ B = insert v B := by
    ext x
    have := @hAB x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have h2 : insert v A ∩ B = A := by
    ext x
    have := @hAB x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, h'⟩
      · subst h
        exact absurd h' hv
      · exact h
    · intro h
      exact ⟨Or.inr h, this h⟩
  rw [h1, h2] at h
  linarith

theorem xsum_insert {n : ℕ} (x : Fin n → ℝ) {a : Fin n} {s : Finset (Fin n)} (ha : a ∉ s) :
    xsum x (insert a s) = x a + xsum x s := by
  unfold xsum
  rw [Finset.sum_insert ha]

theorem greedy_le {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n)) :
    xsum (greedy f σ) U ≤ f U - f ∅ := by
  induction U using Finset.induction_on_max_value (fun v => σ v) with
  | empty => simp [xsum]
  | insert a s ha hmax ih =>
    have hs : s ⊆ before σ a := by
      intro x hx
      rw [mem_before]
      rcases lt_or_eq_of_le (hmax x hx) with h | h
      · exact h
      · exact absurd (by rw [← σ.injective h]; exact hx) ha
    have hnot : a ∉ before σ a := by
      rw [mem_before]
      exact lt_irrefl _
    have h1 := dimret hsub hs hnot
    rw [xsum_insert _ ha]
    have h3 : greedy f σ a = f (insert a (before σ a)) - f (before σ a) := rfl
    linarith

theorem greedy_eq {n : ℕ} (f : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n))
    (U : Finset (Fin n)) (hU : IsLowerIdeal σ U) : xsum (greedy f σ) U = f U - f ∅ := by
  induction U using Finset.induction_on_max_value (fun v => σ v) with
  | empty => simp [xsum]
  | insert a s ha hmax ih =>
    have hb : before σ a = s := by
      ext x
      rw [mem_before]
      constructor
      · intro h
        have hx := hU a (Finset.mem_insert_self a s) x h
        rcases Finset.mem_insert.mp hx with hx | hx
        · subst hx
          exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx
        rcases lt_or_eq_of_le (hmax x hx) with h | h
        · exact h
        · exact absurd (by rw [← σ.injective h]; exact hx) ha
    have hs : IsLowerIdeal σ s := by
      intro u hu w hw
      have := hU u (Finset.mem_insert_of_mem hu) w hw
      rcases Finset.mem_insert.mp this with h | h
      · subst h
        exact absurd (lt_of_lt_of_le hw (hmax u hu)) (lt_irrefl _)
      · exact h
    rw [xsum_insert _ ha, ih hs]
    show f (insert a (before σ a)) - f (before σ a) + (f s - f ∅) = f (insert a s) - f ∅
    rw [hb]
    ring

theorem greedy_mem {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (σ : Equiv.Perm (Fin n)) : greedy f σ ∈ baseB f := by
  simp only [baseB, Set.mem_setOf_eq]
  refine ⟨fun U => ?_, ?_⟩
  · have := greedy_le f hsub σ U
    linarith
  · have := greedy_eq f σ Finset.univ (univ_lower σ)
    linarith

theorem mem_pref {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) (v : Fin n) :
    v ∈ pref σ i ↔ (σ v : ℕ) < i := by
  simp [pref]

theorem pref_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : pref σ 0 = ∅ := by
  ext v
  simp [pref]

theorem pref_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) :
    pref σ (k + 1) = insert (σ.symm ⟨k, hk⟩) (pref σ k) := by
  ext v
  rw [Finset.mem_insert, mem_pref, mem_pref]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · left
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
  · rintro (h | h)
    · subst h
      simp
    · omega

theorem not_mem_pref {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) :
    σ.symm ⟨k, hk⟩ ∉ pref σ k := by
  rw [mem_pref]
  simp

theorem pref_le {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : n ≤ k) :
    pref σ k = Finset.univ := by
  ext v
  simp only [mem_pref, Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (σ v).isLt hk

theorem pref_lower {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : IsLowerIdeal σ (pref σ k) := by
  intro u hu w hw
  rw [mem_pref] at hu ⊢
  exact lt_trans (Fin.lt_iff_val_lt_val.mp hw) hu

theorem abel (a b : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), b j * a j =
      ∑ j ∈ Finset.range k, (∑ i ∈ Finset.range (j + 1), a i) * (b j - b (j + 1)) +
        (∑ i ∈ Finset.range (k + 1), a i) * b k := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ (fun j => b j * a j) (k + 1), ih]
    simp only [Finset.sum_range_succ]
    ring

noncomputable def seq {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (j : ℕ) : ℝ :=
  if h : j < N then x (σ.symm ⟨j, h⟩) else 0

theorem seq_of_lt {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) {j : ℕ} (h : j < N) :
    seq x σ j = x (σ.symm ⟨j, h⟩) := by
  rw [seq, dif_pos h]

theorem xsum_pref {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ∀ k, k ≤ N → xsum x (pref σ k) = ∑ j ∈ Finset.range k, seq x σ j
  | 0, _ => by simp [pref_zero, xsum]
  | k + 1, hk => by
    have hk' : k < N := hk
    rw [pref_succ σ hk', Finset.sum_range_succ, ← xsum_pref x σ k (le_of_lt hk'),
      xsum_insert _ (not_mem_pref σ hk'), seq_of_lt x σ hk']
    ring

theorem dot_eq {N : ℕ} (w x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    w ⬝ᵥ x = ∑ j ∈ Finset.range N, seq w σ j * seq x σ j := by
  have h1 : ∑ v, w v * x v = ∑ i, w (σ.symm i) * x (σ.symm i) :=
    (Equiv.sum_comp σ.symm (fun v => w v * x v)).symm
  unfold dotProduct
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun j => seq w σ j * seq x σ j)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [seq_of_lt w σ i.isLt, seq_of_lt x σ i.isLt]

theorem key_abel {m : ℕ} (w x : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1))) :
    w ⬝ᵥ x = ∑ j ∈ Finset.range m, xsum x (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
      xsum x Finset.univ * seq w σ m := by
  rw [dot_eq w x σ, abel]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [xsum_pref x σ (j + 1) (by omega)]
  · rw [← pref_le σ (le_refl (m + 1)), xsum_pref x σ (m + 1) (le_refl _)]

theorem sorted_step {m : ℕ} (w : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : IsSortedBy w σ) {j : ℕ} (hj : j < m) : seq w σ j ≤ seq w σ (j + 1) := by
  rw [seq_of_lt w σ (show j < m + 1 by omega), seq_of_lt w σ (show j + 1 < m + 1 by omega)]
  apply hσ
  simp [Fin.lt_iff_val_lt_val]

theorem greedy_min_aux {m : ℕ} (f : Finset (Fin (m + 1)) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (w : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : IsSortedBy w σ) :
    greedy f σ ∈ baseB f ∧
      (∀ x ∈ baseB f, w ⬝ᵥ greedy f σ ≤ w ⬝ᵥ x) ∧
      w ⬝ᵥ greedy f σ =
        ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
          f Finset.univ * seq w σ m := by
  have hg : ∀ k, xsum (greedy f σ) (pref σ k) = f (pref σ k) := by
    intro k
    rw [greedy_eq f σ _ (pref_lower σ k), hf0, sub_zero]
  have hgu : xsum (greedy f σ) Finset.univ = f Finset.univ := by
    rw [greedy_eq f σ _ (univ_lower σ), hf0, sub_zero]
  have hform : w ⬝ᵥ greedy f σ =
      ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
        f Finset.univ * seq w σ m := by
    rw [key_abel w (greedy f σ) σ, hgu]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hg]
  refine ⟨greedy_mem f hsub hf0 σ, ?_, hform⟩
  intro x hx
  simp only [baseB, Set.mem_setOf_eq] at hx
  rw [hform, key_abel w x σ, hx.2]
  have : ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) ≤
      ∑ j ∈ Finset.range m, xsum x (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have h1 := sorted_step w σ hσ hj
    exact mul_le_mul_of_nonpos_right (hx.1 _) (by linarith)
  linarith

theorem enl_empty {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) : enlarge f m ∅ = 0 :=
  if_pos (Or.inl rfl)

theorem enl_univ {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) : enlarge f m Finset.univ = 0 :=
  if_pos (Or.inr rfl)

theorem enl_mid {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) (U : Finset (Fin n)) (h1 : U ≠ ∅)
    (h2 : U ≠ Finset.univ) : enlarge f m U = f U + m :=
  if_neg (not_or.mpr ⟨h1, h2⟩)

theorem enlarge_sub {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) : Submodular (enlarge f μ) := by
  have hμ0 : 0 ≤ μ := le_trans (le_max_left _ _) hμ
  have hμ1 : -f Finset.univ ≤ μ := le_trans (le_max_right _ _) hμ
  have hg0 : ∀ m, enlarge f m ∅ = 0 := fun m => if_pos (Or.inl rfl)
  have hgu : ∀ m, enlarge f m Finset.univ = 0 := fun m => if_pos (Or.inr rfl)
  have hgp : ∀ m U, U ≠ ∅ → U ≠ Finset.univ → enlarge f m U = f U + m :=
    fun m U h1 h2 => if_neg (not_or.mpr ⟨h1, h2⟩)
  intro S T
  by_cases hS0 : S = ∅
  · rw [hS0, Finset.empty_union, Finset.empty_inter, hg0] <;> linarith
  by_cases hT0 : T = ∅
  · rw [hT0, Finset.union_empty, Finset.inter_empty, hg0] <;> linarith
  by_cases hSu : S = Finset.univ
  · rw [hSu, Finset.union_eq_left.2 (Finset.subset_univ T),
      Finset.inter_eq_right.2 (Finset.subset_univ T), hgu] <;> linarith
  by_cases hTu : T = Finset.univ
  · rw [hTu, Finset.union_eq_right.2 (Finset.subset_univ S),
      Finset.inter_eq_left.2 (Finset.subset_univ S), hgu] <;> linarith
  rw [hgp μ S hS0 hSu, hgp μ T hT0 hTu]
  have hST := hsub S T
  have hU0 : S ∪ T ≠ ∅ := fun h => hS0 (Finset.union_eq_empty.mp h).1
  have hIu : S ∩ T ≠ Finset.univ := by
    intro h
    apply hSu
    refine Finset.eq_univ_of_forall (fun x => ?_)
    have hx := Finset.mem_univ x
    rw [← h] at hx
    exact (Finset.mem_inter.mp hx).1
  by_cases hUu : S ∪ T = Finset.univ
  · rw [hUu, hgu]
    rw [hUu] at hST
    by_cases hI0 : S ∩ T = ∅
    · rw [hI0, hg0]; rw [hI0, hf0] at hST; linarith
    · rw [hgp μ _ hI0 hIu]; linarith
  · rw [hgp μ _ hU0 hUu]
    by_cases hI0 : S ∩ T = ∅
    · rw [hI0, hg0]; rw [hI0, hf0] at hST; linarith
    · rw [hgp μ _ hI0 hIu]; linarith

end Aux_GeomRescale_lemma_3_3

open GeomRescale Aux_GeomRescale_lemma_3_3 in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) (w : Fin n → ℝ)
    (hw : ∀ x ∈ baseB (enlarge f μ), 0 < w ⬝ᵥ x)
    (σ : Equiv.Perm (Fin n)) (hσ : IsSortedBy w σ) (S : Finset (Fin n))
    (hS : IsMinSet (enlarge f μ) σ S) :
    f S < -μ := by
  have hgs := enlarge_sub f hsub hf0 μ hμ
  have hg0 := enl_empty f μ
  have hx := greedy_mem (enlarge f μ) hgs hg0 σ
  have hpos := hw _ hx
  by_contra hcon
  have hgS : 0 ≤ enlarge f μ S := by
    by_cases h0 : S = ∅
    · rw [h0, enl_empty]
    by_cases h1 : S = Finset.univ
    · rw [h1, enl_univ]
    rw [enl_mid f μ S h0 h1]
    linarith
  have hall : ∀ k, k ≤ n → 0 ≤ enlarge f μ (pref σ k) := fun k hk => le_trans hgS (hS.2 k hk)
  rcases n with _ | m
  · have : w ⬝ᵥ greedy (enlarge f μ) σ = 0 := by
      unfold dotProduct
      simp
    linarith
  · rw [key_abel w _ σ] at hpos
    have hgu : xsum (greedy (enlarge f μ) σ) Finset.univ = 0 := by
      rw [greedy_eq _ σ _ (univ_lower σ), hg0, enl_univ, sub_zero]
    rw [hgu, zero_mul, add_zero] at hpos
    have : ∑ j ∈ Finset.range m, xsum (greedy (enlarge f μ) σ) (pref σ (j + 1)) *
        (seq w σ j - seq w σ (j + 1)) ≤ 0 := by
      refine Finset.sum_nonpos (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [greedy_eq _ σ _ (pref_lower σ _), hg0, sub_zero]
      have h1 := sorted_step w σ hσ hj
      exact mul_nonpos_iff.mpr (Or.inl ⟨hall (j + 1) (by omega), by linarith⟩)
    linarith

