-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.continuous_of_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:48:50.913813+00:00
-- url     : https://prove2.me/submissions/e61b8a68-f4ec-4214-a255-cce71ee81f55

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution (τ : F ≃+* F) (hτ : ∀ a, valuation F (τ a) = valuation F a) :
    Continuous τ := by
  refine continuous_of_continuousAt_zero τ ?_
  rw [ContinuousAt, map_zero,
    (IsValuativeTopology.hasBasis_nhds_zero' F).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero' F)]
  intro γ hγ
  exact ⟨γ, hγ, fun y hy => by simpa [hτ] using hy⟩
end GlobalTheory.CompanionTheory.TwContraction
