-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.osc_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:03.310134+00:00
-- url     : https://prove2.me/submissions/feec26d1-26fd-4979-9108-b81b0764a6a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_of_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_vacOp_apply
import Theorems.Thm_GlobalTheory_RealWeil_Osc_pr_one
import Theorems.Thm_GlobalTheory_RealWeil_Good_inversion


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
theorem _root_.solution (hc : c 1 = 1) {f : B} (hf : Sm ρ f) : osc h hk c 1 f = f := by
  refine Eq.trans ?_ ((good_of_sm hJ h hf).inversion hJ)
  simp only [osc, intw, vacOp_apply, pr_one, proj_proj hJ, hc, one_smul, map_one, ContinuousLinearMap.one_apply]
end GlobalTheory.RealWeil.Osc
