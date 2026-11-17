-- Prove2me | solution 1 for N25.unitAnalytic25_A7
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:27.633202+00:00
-- url     : https://prove2.me/submissions/3fef5fee-bb17-4624-9a87-d77ee6f2f8bf

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_etaAnalytic25_pair_A7

set_option autoImplicit false

namespace N25

/-- The common signed square multiplier of the generator cancels in each
of the five original unpowered Siegel ratios. -/
theorem _root_.solution (i : Fin 5) (τ : UpperHalfPlane) :
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![7,5;25,18], by norm_num [Matrix.det_fin_two]⟩
    unitAnalytic25 i (A • τ) = unitAnalytic25 i τ := by
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![7,5;25,18], by norm_num [Matrix.det_fin_two]⟩
  obtain ⟨μ, hμ, hcov⟩ := etaAnalytic25_pair_A7
  let P (j : Fin 5) (z : UpperHalfPlane) : ℂ :=
    etaAnalytic25 (unitResidues25 j).1 z * etaAnalytic25 (unitResidues25 j).2 z
  have H (j : Fin 5) (z : UpperHalfPlane) : P j (A • z) = (-μ^2) * P j z := hcov j z
  have hμne : μ ≠ 0 := by
    intro hz
    rw [hz] at hμ
    norm_num at hμ
  change P i (A • τ) / P (i+1) (A • τ) = P i τ / P (i+1) τ
  rw [H i τ, H (i+1) τ]
  exact mul_div_mul_left _ _ (neg_ne_zero.mpr (pow_ne_zero 2 hμne))

end N25
