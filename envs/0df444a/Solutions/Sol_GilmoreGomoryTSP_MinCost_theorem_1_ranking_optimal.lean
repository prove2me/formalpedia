-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.theorem_1_ranking_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:43:47.908+00:00
-- url     : https://prove2.me/submissions/899a39d8-9f98-4f6a-b8fe-5be1de870730

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate



namespace GilmoreGomoryTSP.MinCost

open MeasureTheory

variable {n : ℕ}

lemma cnt_int_ind (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) :
    Integrable ((Set.Ico a b).indicator f) :=
  (integrable_indicator_iff measurableSet_Ico).mpr
    ((hf.integrableOn_isCompact isCompact_Icc).mono_set Set.Ico_subset_Icc_self)

lemma cnt_ico (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) (h : a ≤ b) :
    ∫ x, (Set.Ico a b).indicator f x = ∫ x in a..b, f x := by
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le h]

/-- the integrand of the cost of one changeover -/
noncomputable def cntT (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (x : ℝ) : ℝ :=
  (Set.Ico (B i) (A j)).indicator f x + (Set.Ico (A j) (B i)).indicator g x

lemma cnt_T_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : Integrable (cntT f g A B i j) :=
  (cnt_int_ind f hf _ _).add (cnt_int_ind g hg _ _)

lemma cnt_c (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    c f g A B i j = ∫ x, cntT f g A B i j x := by
  unfold cntT
  rw [integral_add (cnt_int_ind f hf _ _) (cnt_int_ind g hg _ _)]
  unfold c
  split_ifs with h
  · have : Set.Ico (A j) (B i) = ∅ := Set.Ico_eq_empty (not_lt.mpr h)
    rw [this, cnt_ico f hf _ _ h]
    simp
  · have h' : A j ≤ B i := (not_le.mp h).le
    have : Set.Ico (B i) (A j) = ∅ := Set.Ico_eq_empty (not_lt.mpr h')
    rw [this, cnt_ico g hg _ _ h']
    simp

noncomputable def cntW (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1)))
    (x : ℝ) : ℝ := ∑ i, cntT f g A B i (ψ i) x

lemma cnt_W_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) : Integrable (cntW f g A B ψ) := by
  unfold cntW
  exact integrable_finsetSum _ (fun i _ => cnt_T_int f g hf hg A B i (ψ i))

lemma cnt_cost (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) :
    cost f g A B ψ = ∫ x, cntW f g A B ψ x := by
  unfold cost cntW
  rw [integral_finsetSum _ (fun i _ => cnt_T_int f g hf hg A B i (ψ i))]
  exact Finset.sum_congr rfl (fun i _ => cnt_c f g hf hg A B i (ψ i))

/-- counts -/
noncomputable def cntNf (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) : ℝ :=
  ∑ i, if B i ≤ x ∧ x < A (ψ i) then (1:ℝ) else 0

noncomputable def cntNg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) : ℝ :=
  ∑ i, if A (ψ i) ≤ x ∧ x < B i then (1:ℝ) else 0

noncomputable def cntD (A B : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  (∑ i, if B i ≤ x then (1:ℝ) else 0) - ∑ i, if A i ≤ x then (1:ℝ) else 0

lemma cntNf_nonneg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    0 ≤ cntNf A B ψ x :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

lemma cntNg_nonneg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    0 ≤ cntNg A B ψ x :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

lemma cnt_W_eq (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntW f g A B ψ x = cntNf A B ψ x * f x + cntNg A B ψ x * g x := by
  unfold cntW cntNf cntNg cntT
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Set.indicator_apply, Set.mem_Ico]
  split_ifs <;> simp

lemma cnt_diff (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntNf A B ψ x - cntNg A B ψ x = cntD A B x := by
  unfold cntNf cntNg cntD
  rw [← Finset.sum_sub_distrib]
  have h2 : ∑ i, (if A (ψ i) ≤ x then (1:ℝ) else 0) = ∑ i, if A i ≤ x then (1:ℝ) else 0 :=
    Equiv.sum_comp ψ (fun j => if A j ≤ x then (1:ℝ) else 0)
  rw [← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  generalize B i = b
  generalize A (ψ i) = a
  rcases le_or_gt b x with hb | hb <;> rcases le_or_gt a x with ha | ha <;>
    simp [hb, ha, not_lt_of_ge, not_le_of_gt, le_of_lt]

lemma cnt_sorted (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) (x : ℝ) :
    cntNf A B φ x = 0 ∨ cntNg A B φ x = 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : ∃ i, B i ≤ x ∧ x < A (φ i) := by
    by_contra hh
    push Not at hh
    apply hcon.1
    exact Finset.sum_eq_zero (fun i _ => by
      rw [if_neg]; intro h; exact absurd h.2 (not_lt.mpr (hh i h.1)))
  have h2 : ∃ j, A (φ j) ≤ x ∧ x < B j := by
    by_contra hh
    push Not at hh
    apply hcon.2
    exact Finset.sum_eq_zero (fun i _ => by
      rw [if_neg]; intro h; exact absurd h.2 (not_lt.mpr (hh i h.1)))
  obtain ⟨i, hi1, hi2⟩ := h1
  obtain ⟨j, hj1, hj2⟩ := h2
  have hij : i < j := by
    by_contra h; push Not at h
    have := hB h; linarith
  have hji : j < i := by
    by_contra h; push Not at h
    have := hφ h; simp only [Function.comp] at this; linarith
  exact lt_asymm hij hji

lemma cnt_Ng_le (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) (ψ : Equiv.Perm (Fin (n + 1)))
    (x : ℝ) : cntNg A B φ x ≤ cntNg A B ψ x := by
  have h1 := cnt_diff A B φ x
  have h2 := cnt_diff A B ψ x
  have := cnt_sorted A B hB φ hφ x
  have := cntNf_nonneg A B ψ x
  have := cntNg_nonneg A B ψ x
  have := cntNf_nonneg A B φ x
  have := cntNg_nonneg A B φ x
  rcases cnt_sorted A B hB φ hφ x with h | h <;> linarith

lemma cnt_W_sub (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ φ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntW f g A B ψ x - cntW f g A B φ x =
      (cntNg A B ψ x - cntNg A B φ x) * (f x + g x) := by
  rw [cnt_W_eq, cnt_W_eq]
  have h1 := cnt_diff A B φ x
  have h2 := cnt_diff A B ψ x
  have e1 : cntNf A B ψ x = cntNg A B ψ x + cntD A B x := by linarith
  have e2 : cntNf A B φ x = cntNg A B φ x + cntD A B x := by linarith
  rw [e1, e2]; ring

theorem theorem_1_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), cost f g A B φ ≤ cost f g A B ψ := by
  intro ψ
  rw [cnt_cost f g hf hg, cnt_cost f g hf hg, ← sub_nonneg,
    ← integral_sub (cnt_W_int f g hf hg A B ψ) (cnt_W_int f g hf hg A B φ)]
  apply integral_nonneg
  intro x
  show 0 ≤ cntW f g A B ψ x - cntW f g A B φ x
  rw [cnt_W_sub]
  exact mul_nonneg (sub_nonneg.mpr (cnt_Ng_le A B hB φ hφ ψ x)) (hfg x)

end GilmoreGomoryTSP.MinCost

open GilmoreGomoryTSP.MinCost


theorem solution {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), cost f g A B φ ≤ cost f g A B ψ := by
  exact theorem_1_core f g hf hg hfg A B hB φ hφ
