-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.proj_twist_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:53.682794+00:00
-- url     : https://prove2.me/submissions/0f0cbfbe-baf3-4488-a0ea-ca5eb294d375

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_twist
import Theorems.Thm_GlobalTheory_RealWeil_proj_apply


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
theorem _root_.solution (h : IsHeis (omJ J) ρ) (a b : V →L[ℝ] V) (hab : ∀ v, a (b v) = v)
    (ha : ∀ x y, omJ J (a x) (a y) = omJ J x y) (hn : ∀ x, ‖a x‖ = ‖x‖) (x : B) :
    proj (h.twist a ha) x = proj h x := by
  let e : V ≃ₗᵢ[ℝ] V := LinearIsometryEquiv.ofSurjective ⟨a.toLinearMap, hn⟩ fun v => ⟨b v, hab v⟩
  have he : ∀ v, e v = a v := fun v => rfl
  rw [proj_apply, proj_apply, ← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun u => gau u • ρ u x)]
  simp only [he, gau, hn]
end GlobalTheory.RealWeil.Osc
