-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.osc_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:36:08.676272+00:00
-- url     : https://prove2.me/submissions/c81f0f42-de8f-4f43-9341-dcca431bee90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_pr_one
import Theorems.Thm_GlobalTheory_RealWeil_Osc_pr_osc
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_pr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}
variable {G : Type} [Group G] {k : G →* (V →L[ℝ] V)} {c : G → ℂ}
variable (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y)
include hJ
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (g : G) {f : B} (hf : Sm ρ f) : osc h hk c g (proj h f) = c g • pr h hk g (proj h f) := by
  rw [← pr_osc hJ h hk g hf, ← pr_one h hk, osc_pr hJ h hk g 1 hf, mul_one]
end GlobalTheory.RealWeil.Osc
