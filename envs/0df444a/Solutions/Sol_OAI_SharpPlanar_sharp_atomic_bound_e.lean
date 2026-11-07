-- Prove2me | solution 1 for OAI.SharpPlanar.sharp_atomic_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:24:04.259203+00:00
-- url     : https://prove2.me/submissions/7e3da74a-a861-41a8-a9e6-7ca942652ea3

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_atomicCoefficient_norm_e
import Theorems.Thm_OAI_SharpPlanar_kernelMoment_endpoint_bound_e

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

lemma sharp_atomic_bound_e_oai (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Pcoeff 0*kernelMoment ell s 0+
      ∑ j ∈ Finset.Icc 1 6, 2*Pcoeff j*kernelMoment ell s ((j:ℝ)/6)‖ ≤
      ∑ j : Fin 7, atomL j s*(Real.pi*zCap j)^ell := by
  have he : Pcoeff 0*kernelMoment ell s 0+
      ∑ j ∈ Finset.Icc 1 6, 2*Pcoeff j*kernelMoment ell s ((j:ℝ)/6) =
      ∑ j : Fin 7, atomicCoefficient j*kernelMoment ell s ((j.val:ℝ)/6) := by
    norm_num [Fin.sum_univ_succ,Finset.sum_Icc_succ_top,atomicCoefficient]
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,atomicCoefficient_norm_e]
  have hh := mul_le_mul_of_nonneg_left (kernelMoment_endpoint_bound_e j ell hs)
    (by fin_cases j <;> norm_num [atomMass] : 0 ≤ atomMass j)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold atomL
  ring


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.sharp_atomic_bound_e_oai := @OAI.SharpPlanar.sharp_atomic_bound_e_oai
