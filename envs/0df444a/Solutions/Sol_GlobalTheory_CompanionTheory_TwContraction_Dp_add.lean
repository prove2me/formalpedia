-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.Dp.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:42:58.758129+00:00
-- url     : https://prove2.me/submissions/87d56ff8-5df3-482b-b3b0-2784bc393e6b

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
theorem _root_.solution {ρ : ValueGroupWithZero F} {a : ℕ} {M N : Matrix (Fin n) (Fin n) F}
    (hM : Dp ρ a M) (hN : Dp ρ a N) : Dp ρ a (M + N) := fun i l =>
  (Valuation.map_add _ _ _).trans (max_le (hM i l) (hN i l))
end Dp
end GlobalTheory.CompanionTheory.TwContraction
