-- Prove2me | solution 1 for GlobalTheory.SW.Vac.exists_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:04.412935+00:00
-- url     : https://prove2.me/submissions/458bb9cc-3ff0-4dae-8b4d-7b483f67c99a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (f : Matrix κ ι ℚ →ₗ[ℤ] ℚ) : ∃ x, ∀ v, f v = pr x v := by
  classical
  let g : Matrix κ ι ℚ →ₗ[ℚ] ℚ := f.toAddMonoidHom.toRatLinearMap
  refine ⟨fun k i => g (Matrix.single k i 1), fun v => ?_⟩
  change g v = _
  conv_lhs => rw [Matrix.matrix_eq_sum_single v]
  simp only [map_sum, pr, dotProduct]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  have : Matrix.single k i (v k i) = v k i • Matrix.single k i (1 : ℚ) := by
    simp [Matrix.smul_single]
  rw [this, map_smul, smul_eq_mul, mul_comm]
end GlobalTheory.SW.Vac
