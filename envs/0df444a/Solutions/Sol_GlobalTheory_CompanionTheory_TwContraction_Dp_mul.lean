-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.Dp.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:43.645918+00:00
-- url     : https://prove2.me/submissions/b4740cc1-d3cf-430c-9f64-20af8d9518d9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
namespace Dp
theorem _root_.solution {ρ : ValueGroupWithZero F} {a b : ℕ} {M N : Matrix (Fin n) (Fin n) F}
    (hM : Dp ρ a M) (hN : Dp ρ b N) : Dp ρ (a + b) (M * N) := by
  intro i l
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun r _ => ?_
  rw [map_mul, pow_add]
  exact mul_le_mul' (hM i r) (hN r l)
end Dp
end GlobalTheory.CompanionTheory.TwContraction
