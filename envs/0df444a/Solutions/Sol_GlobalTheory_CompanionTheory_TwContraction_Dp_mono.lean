-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.Dp.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:42:59.717701+00:00
-- url     : https://prove2.me/submissions/dc665895-c060-48a5-afaf-983df8775b6c

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
theorem _root_.solution {ρ : ValueGroupWithZero F} (hρ : ρ ≤ 1) {a b : ℕ} (hab : a ≤ b)
    {M : Matrix (Fin n) (Fin n) F} (hM : Dp ρ b M) : Dp ρ a M := fun i l =>
  (hM i l).trans (pow_le_pow_right_of_le_one' hρ hab)
end Dp
end GlobalTheory.CompanionTheory.TwContraction
