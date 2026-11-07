-- Prove2me | solution 1 for OAI.SharpPlanar.sharp_moment_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T04:05:24.513139+00:00
-- url     : https://prove2.me/submissions/43982b18-605c-4b8c-922d-0a6cab8c7241

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_sharp_atomic_bound_e
import Theorems.Thm_OAI_SharpPlanar_sharp_integral_piece_bound_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis


theorem sharp_moment_bound_e_oai (p : CardinalData) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |K p ell s| ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*(∑ j : Fin 6, densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell)
      +|p.C| *(∑ j : Fin 7, atomL j s*(Real.pi*zCap j)^ell) := by
  have hatom : ‖(p.C:ℂ)*(Pcoeff 0*kernelMoment ell s 0+
      ∑ j ∈ Finset.Icc 1 6, 2*Pcoeff j*kernelMoment ell s ((j:ℝ)/6))‖ ≤
      |p.C| *(∑ j : Fin 7, atomL j s*(Real.pi*zCap j)^ell) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (sharp_atomic_bound_e ell hs) (abs_nonneg _)
  have hsum : ‖∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t*kernelMoment ell s t‖ ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*(∑ j : Fin 6, densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell) := by
    rw [← Fin.sum_univ_eq_sum_range,Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_assoc] using sharp_integral_piece_bound_e p j ell hs
  unfold K
  exact (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by linarith))

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.sharp_moment_bound_e_oai := @OAI.SharpPlanar.sharp_moment_bound_e_oai
