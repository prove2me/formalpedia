-- Prove2me | solution 1 for GilmoreGomory1961.step4_current_solution_is_minimum_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:13:28.257728+00:00
-- url     : https://prove2.me/submissions/50d99446-649e-4eb8-ae34-64b3233710ba

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

open GilmoreGomory61.CuttingStock

namespace GG84b

variable {m k : ℕ} (I : Instance m k)

theorem sum_eq_lc (g : Col I → ℝ) (z : Col I →₀ ℝ) :
    (z.sum fun j v => g j * v) = Finsupp.linearCombination ℝ g z := by
  rw [Finsupp.linearCombination_apply]
  simp [smul_eq_mul, mul_comm]

theorem lc_basic (g : Col I → ℝ) (β : Fin m → Col I) (x : Fin m → ℝ) :
    Finsupp.linearCombination ℝ g (∑ r : Fin m, Finsupp.single (β r) (x r)) = ∑ r, g (β r) * x r := by
  rw [map_sum]; simp [mul_comm]

theorem bordered_det (β : Fin m → Col I) : (bordered I β).det = (basisMat I β).det := by
  unfold bordered
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

end GG84b

open GG84b in
theorem solution {m k : ℕ} (I : Instance m k)
    (hℓ : ∀ i, 0 < I.ℓ i) (hL : ∀ j, 0 < I.L j) (hfit : ∃ j : Fin k, ∀ i, I.ℓ i ≤ I.L j)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (h3 : ∀ i, Sum.inr i ∉ Set.range β → 0 ≤ mult I β i)
    (h4 : ∀ j : Fin k, ¬ ∃ a : Fin m → ℕ,
      patLen I a ≤ I.L j ∧ I.c j < ∑ i, mult I β i * (a i : ℝ)) :
    Feasible I (basicSol I β) ∧
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) ∧
    ∀ z : Col I →₀ ℝ, Feasible I z → Nbar I β (Sum.inl ()) ≤ cost I z := by
  classical
  set B := bordered I β with hB
  set M := B⁻¹ with hM
  have hdet : IsUnit B.det := by rw [hB, bordered_det]; exact hβ.1
  have hBM : B * M = 1 := Matrix.mul_nonsing_inv B hdet
  have hMB : M * B = 1 := Matrix.nonsing_inv_mul B hdet
  set x : Fin m → ℝ := fun r => Nbar I β (Sum.inr r) with hx
  set π : Fin m → ℝ := mult I β with hπ
  -- B * Nbar = N'
  have hBN : B.mulVec (Nbar I β) = Nprime I := by
    unfold Nbar; rw [Matrix.mulVec_mulVec, ← hM, hBM, Matrix.one_mulVec]
  have hrow0 : Nbar I β (Sum.inl ()) = ∑ r, costRow I β r * x r := by
    have := congrFun hBN (Sum.inl ())
    simp [hB, bordered, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Nprime] at this
    simp only [hx]; linarith
  have hrowi : ∀ i, ∑ r, colVec I (β r) i * x r = I.N i := by
    intro i
    have := congrFun hBN (Sum.inr i)
    simp [hB, bordered, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Nprime, basisMat] at this
    simpa [hx] using this
  -- M * B = 1 gives π A = C
  have hM11 : M (Sum.inl ()) (Sum.inl ()) = 1 := by
    have := congrFun (congrFun hMB (Sum.inl ())) (Sum.inl ())
    simpa [hB, bordered, Matrix.mul_apply, Fintype.sum_sum_type] using this
  have hpiA : ∀ r, ∑ i, π i * colVec I (β r) i = colCost I (β r) := by
    intro r
    have := congrFun (congrFun hMB (Sum.inl ())) (Sum.inr r)
    simp [hB, bordered, Matrix.mul_apply, Fintype.sum_sum_type, basisMat, costRow, hM11] at this
    simp only [hπ, mult, ← hM, ← hB]
    linarith
  -- reduced costs are nonnegative
  have hred : ∀ j : Col I, ∑ i, π i * colVec I j i ≤ colCost I j := by
    intro j
    cases j with
    | inl p =>
      show ∑ i, π i * (p.1.2 i : ℝ) ≤ I.c p.1.1
      by_contra h
      exact h4 p.1.1 ⟨p.1.2, p.2, lt_of_not_ge h⟩
    | inr i0 =>
      show ∑ i, π i * (if i = i0 then -1 else 0) ≤ 0
      simp only [mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      by_cases hr : Sum.inr i0 ∈ Set.range β
      · obtain ⟨r, hr⟩ := hr
        have := hpiA r
        rw [hr] at this
        have h2 : ∑ i, π i * colVec I (Sum.inr i0 : Col I) i = -π i0 := by
          show ∑ i, π i * (if i = i0 then -1 else 0) = -π i0
          simp
        have h3' : colCost I (Sum.inr i0 : Col I) = 0 := rfl
        linarith
      · have := h3 i0 hr; linarith
  have hlc : ∀ (g : Col I → ℝ) (z : Col I →₀ ℝ), (z.sum fun j v => g j * v) = Finsupp.linearCombination ℝ g z :=
    fun g z => sum_eq_lc I g z
  have hval : Nbar I β (Sum.inl ()) = ∑ i, π i * I.N i := by
    rw [hrow0]
    simp only [costRow, ← hpiA, ← hrowi, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; congr 1; funext i; congr 1; funext r; ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro j
    unfold basicSol
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_nonneg; intro r _
    rw [Finsupp.single_apply]; split_ifs
    · exact hβ.2 r
    · exact le_refl 0
  · intro i
    rw [hlc, basicSol, lc_basic]
    exact hrowi i
  · unfold cost; rw [hlc, basicSol, lc_basic, hrow0]; rfl
  · intro z hz
    rw [hval]
    unfold cost; rw [hlc]
    have hN : ∀ i, (I.N i : ℝ) = Finsupp.linearCombination ℝ (fun j => colVec I j i) z := by
      intro i; rw [← hz.2 i, hlc]
    simp only [hN]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j _
    have := mul_le_mul_of_nonneg_left (hred j) (hz.1 j)
    calc ∑ i, π i * (z j * colVec I j i) = z j * ∑ i, π i * colVec I j i := by
          rw [Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ z j * colCost I j := this
