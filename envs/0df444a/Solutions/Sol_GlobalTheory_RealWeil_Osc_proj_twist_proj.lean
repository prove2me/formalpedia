-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.proj_twist_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:02.953907+00:00
-- url     : https://prove2.me/submissions/1f48baa4-45b4-47af-822a-d73a3159a743

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_proj_apply
import Theorems.Thm_GlobalTheory_RealWeil_proj_heis_proj


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
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (h' : IsHeis (omJ J) ρ') (a : V → V)
    (ha : ∀ u, ρ' u = ρ (a u)) (x : B) : proj h (proj h' (proj h x)) = lam a • proj h x := by
  rw [proj_apply h', ← (proj h).integral_comp_comm (h'.integrable _), lam, ← integral_smul_const]
  simp only [ha, map_smul, proj_heis_proj hJ, smul_smul]
end GlobalTheory.RealWeil.Osc
