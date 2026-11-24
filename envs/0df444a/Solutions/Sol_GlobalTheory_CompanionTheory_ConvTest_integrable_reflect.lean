-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ConvTest.integrable_reflect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:34.705101+00:00
-- url     : https://prove2.me/submissions/12974d35-6ab9-4d5a-bb5b-3ead5f19b910

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableReflect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConvTest
variable (X : Ctx)
namespace GlobalTheory.CompanionTheory.ConvTest
theorem _root_.solution {ψ : X.G → ℂ} (hψ : Tst ψ) (y : X.G) :
    Integrable (fun z => ‖ψ (z⁻¹ * y)‖) X.μ := by
  have hc : Continuous fun z : X.G => ψ (z⁻¹ * y) :=
    hψ.1.comp (continuous_inv.mul continuous_const)
  have hs : HasCompactSupport fun z : X.G => ψ (z⁻¹ * y) :=
    hψ.2.comp_homeomorph ((Homeomorph.inv X.G).trans (Homeomorph.mulRight y))
  exact (hc.integrable_of_hasCompactSupport hs).norm
end GlobalTheory.CompanionTheory.ConvTest
