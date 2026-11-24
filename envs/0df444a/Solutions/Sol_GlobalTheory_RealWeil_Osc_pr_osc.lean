-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.pr_osc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:08.483518+00:00
-- url     : https://prove2.me/submissions/76a6ef2d-151a-47dd-be16-b8120ffe5e47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_of_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_heis_intw
import Theorems.Thm_GlobalTheory_RealWeil_Osc_vacOp_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_vacOp
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_twist


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
theorem _root_.solution (g : G) {f : B} (hf : Sm ρ f) : pr h hk g (osc h hk c g f) = c g • pr h hk g (proj h f) := by
  have := proj_heis_intw hJ (h.twist (k g) (hk g)) (vacOp_proj (c := c) hJ h hk g)
    (proj_vacOp hJ h hk g) (good_of_sm hJ h hf) 0
  simp only [map_zero, h.1] at this
  exact this
end GlobalTheory.RealWeil.Osc
