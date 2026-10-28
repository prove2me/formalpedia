-- Prove2me | solution 1 for NetInspect.Rate.lemma_EC_4
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-28T05:55:47.070464+00:00
-- url     : https://prove2.me/submissions/1bff656e-1393-474a-a103-5526cca099a6

import Definitions.Def_NetInspect_Rate_Model
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

namespace NetInspect.Rate
open Finset Matrix

set_option backward.isDefEq.respectTransparency.types false in
theorem marginals_doubly_stochastic {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : E → ℝ) (B : Finset E) (hB : B.Nonempty) (hBc : Bᶜ.Nonempty)
    (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1) (hs : ∑ e, ρ e = (B.card : ℝ)) :
    ((fun i j => if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card) : Matrix E E ℝ) ∈
      doublyStochastic ℝ E := by
  have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hc : (Bᶜ.card : ℝ) ≠ 0 := by exact_mod_cast hBc.card_pos.ne'
  refine (mem_doublyStochastic_iff_sum (M :=
    (fun i j => if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card : Matrix E E ℝ))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    split_ifs <;> exact div_nonneg (by linarith [(hρ j).1, (hρ j).2]) (Nat.cast_nonneg _)
  · intro i
    by_cases hi : i ∈ B
    · simp [hi, ← sum_div, hs, hb]
    · simp only [hi, ↓reduceIte, ← sum_div, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, hs]
      have hcard : (Fintype.card E : ℝ) - B.card = (Bᶜ.card : ℝ) := by
        have hh : (B.card : ℝ) + Bᶜ.card = Fintype.card E := by
          exact_mod_cast Finset.card_add_card_compl B
        linarith
      rw [hcard, div_self hc]
  · intro j
    rw [sum_ite]
    simp only [filter_mem_eq_inter, univ_inter]
    have hfilter : (univ.filter fun i => i ∉ B) = Bᶜ := by ext i; simp
    rw [hfilter]
    simp only [sum_const, nsmul_eq_mul]
    field_simp [hb, hc]
    <;> ring
theorem realize_from_finite_family {E K : Type*} [Fintype E] [DecidableEq E]
    [Fintype K] {b : ℕ} (A : K → Act E b) (w : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    ∃ σ : Act E b → ℝ, BlottoLP.Flow.IsMixed σ ∧
      ∀ e, marg σ e = ∑ k, if e ∈ (A k).1 then w k else 0 := by
  classical
  let σ : Act E b → ℝ := fun T => ∑ k, if A k = T then w k else 0
  refine ⟨σ, ⟨?_, ?_⟩, ?_⟩
  · intro T
    exact sum_nonneg fun k _ => by split_ifs <;> simp_all
  · dsimp [σ]
    rw [sum_comm]
    simpa using hs
  · intro e
    unfold marg
    dsimp [σ]
    simp_rw [Finset.ite_sum_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    by_cases he : e ∈ (A k).1
    · simp only [he, ↓reduceIte]
      rw [sum_eq_single (A k)]
      · simp [he]
      · intro T _ hT
        by_cases ht : e ∈ T.1 <;> simp [ht, Ne.symm hT]
      · simp
    · simp only [he, ↓reduceIte]
      apply sum_eq_zero
      intro T _
      by_cases ht : e ∈ T.1
      · have hn : A k ≠ T := by intro h; exact he (h ▸ ht)
        simp [ht, hn]
      · simp [ht]

theorem sum_permMatrix_subset {E : Type*} [Fintype E] [DecidableEq E]
    (B : Finset E) (π : Equiv.Perm E) (e : E) :
    ∑ i ∈ B, π.permMatrix ℝ i e = if e ∈ B.image π then 1 else 0 := by
  classical
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  by_cases he : π.symm e ∈ B
  · rw [sum_eq_single (π.symm e)]
    · simp [mem_image, he, Equiv.apply_eq_iff_eq_symm_apply]
    · intro i hi hn
      simp [show π i ≠ e by intro h; exact hn (π.injective (by simpa using h))]
    · simp [he]
  · have he' : e ∉ B.image π := by
      rintro he'
      obtain ⟨i, hi, hie⟩ := mem_image.mp he'
      exact he (by simpa [← hie] using hi)
    rw [if_neg he']
    apply sum_eq_zero
    intro i hi
    have hn : π i ≠ e := by intro h; exact he (by simpa [← h] using hi)
    simp [hn]
theorem realize_marginals_of_subset {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : E → ℝ) (B : Finset E) (hB : B.Nonempty) (hBc : Bᶜ.Nonempty)
    (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1) (hs : ∑ e, ρ e = (B.card : ℝ)) :
    ∃ σ : Act E B.card → ℝ, BlottoLP.Flow.IsMixed σ ∧ ∀ e, marg σ e = ρ e := by
  classical
  let M : Matrix E E ℝ := fun i j =>
    if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card
  obtain ⟨w, hw, hw1, hM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (marginals_doubly_stochastic ρ B hB hBc hρ hs)
  let A : Equiv.Perm E → Act E B.card := fun π =>
    ⟨B.image π, by rw [card_image_of_injective _ π.injective]⟩
  obtain ⟨σ, hσ, hm⟩ := realize_from_finite_family A w hw hw1
  refine ⟨σ, hσ, fun e => ?_⟩
  rw [hm]
  change (∑ π : Equiv.Perm E, if e ∈ B.image π then w π else 0) = ρ e
  calc
    _ = ∑ π : Equiv.Perm E, w π * ∑ i ∈ B, π.permMatrix ℝ i e := by
      apply sum_congr rfl
      intro π _
      rw [sum_permMatrix_subset]
      split_ifs <;> simp
    _ = ∑ i ∈ B, M i e := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      have hij := congrArg (fun X : Matrix E E ℝ => X i e) hM
      simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, M] using hij
    _ = ρ e := by
      have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
      calc
        _ = ∑ _i ∈ B, ρ e / (B.card : ℝ) := by
          apply sum_congr rfl
          intro i hi
          simp [M, hi]
        _ = ρ e := by simp only [sum_const, nsmul_eq_mul]; field_simp
theorem realize_marginals {E : Type*} [Fintype E] [DecidableEq E]
    (b : ℕ) (ρ : E → ℝ) (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1)
    (hs : ∑ e, ρ e = (b : ℝ)) :
    ∃ σ : Act E b → ℝ, BlottoLP.Flow.IsMixed σ ∧ ∀ e, marg σ e = ρ e := by
  classical
  have hb : b ≤ Fintype.card E := by
    have hh : (b : ℝ) ≤ Fintype.card E := by
      rw [← hs]
      calc
        _ ≤ ∑ _ : E, (1 : ℝ) := sum_le_sum fun e _ => (hρ e).2
        _ = _ := by simp
    exact_mod_cast hh
  by_cases hz : b = 0
  · subst b
    have hr : ∀ e, ρ e = 0 := by
      have hs0 : ∑ e, ρ e = 0 := by simpa using hs
      have hh := (sum_eq_zero_iff_of_nonneg (s := univ) (fun e _ => (hρ e).1)).1 hs0
      exact fun e => hh e (mem_univ e)
    obtain ⟨σ, hσ, hm⟩ := realize_from_finite_family
      (fun _ : Unit => (⟨∅, by simp⟩ : Act E 0)) (fun _ => (1 : ℝ)) (by simp) (by simp)
    refine ⟨σ, hσ, fun e => ?_⟩
    simpa [hr e] using hm e
  by_cases hn : b = Fintype.card E
  · have hr : ∀ e, ρ e = 1 := by
      have hh : ∑ e, (1 - ρ e) = 0 := by simp [sum_sub_distrib, hs, hn]
      have hh' := (sum_eq_zero_iff_of_nonneg
        (fun e _ => sub_nonneg.mpr (hρ e).2)).1 hh
      intro e
      have := hh' e (mem_univ e)
      linarith
    obtain ⟨σ, hσ, hm⟩ := realize_from_finite_family
      (fun _ : Unit => (⟨univ, by simp [hn]⟩ : Act E b))
      (fun _ => (1 : ℝ)) (by simp) (by simp)
    refine ⟨σ, hσ, fun e => ?_⟩
    simpa [hr e] using hm e
  obtain ⟨B, _, hB⟩ := exists_subset_card_eq (s := (univ : Finset E)) (by simpa using hb)
  have hne : B.Nonempty := card_pos.mp (by omega)
  have hcne : Bᶜ.Nonempty := card_pos.mp (by rw [card_compl, hB]; omega)
  subst b
  exact realize_marginals_of_subset ρ B hne hcne hρ hs

theorem lemma_EC_4 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b2 : ℕ} (hb2 : b2 < G.mStar) (ρ : E → ℝ) (hρ : ∀ e : E, 0 ≤ ρ e ∧ ρ e ≤ 1)
    (hsum : ∑ e : E, ρ e = (b2 : ℝ)) :
    ∃ σ2 : Act E b2 → ℝ, BlottoLP.Flow.IsMixed σ2 ∧ ∀ e : E, marg σ2 e = ρ e :=
  realize_marginals b2 ρ hρ hsum

end NetInspect.Rate


open NetInspect.Rate NetInspect.Rate.DetectionModel Finset

theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b2 : ℕ} (hb2 : b2 < G.mStar) (ρ : E → ℝ) (hρ : ∀ e : E, 0 ≤ ρ e ∧ ρ e ≤ 1)
    (hsum : ∑ e : E, ρ e = (b2 : ℝ)) :
    ∃ σ2 : Act E b2 → ℝ, BlottoLP.Flow.IsMixed σ2 ∧ ∀ e : E, marg σ2 e = ρ e := by
  exact NetInspect.Rate.lemma_EC_4 G hb2 ρ hρ hsum

#print axioms solution
