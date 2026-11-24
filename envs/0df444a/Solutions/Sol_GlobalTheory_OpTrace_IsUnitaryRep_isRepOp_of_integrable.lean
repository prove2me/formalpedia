-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.isRepOp_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:38.680186+00:00
-- url     : https://prove2.me/submissions/0e6347b6-776c-4472-ab22-1a0e3c21c196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsRepOp_repOp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {G : Type*} [Group G] [TopologicalSpace G]
  {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [MeasurableSpace G]
variable {π : G →* (H →L[ℂ] H)} {μ : Measure G} {f f' : G → ℂ}
omit [CompleteSpace H]
namespace GlobalTheory.OpTrace
namespace IsUnitaryRep
theorem _root_.solution (hπ : IsUnitaryRep π) (hf : Integrable f μ)
    (hm : ∀ v, AEStronglyMeasurable (fun g => f g • π g v) μ) : IsRepOp π μ f (repOp π μ f) := by
  have hi : ∀ v, Integrable (fun g => f g • π g v) μ := fun v =>
    (hf.norm.mul_const ‖v‖).mono' (hm v) (.of_forall fun g => by simp [norm_smul, hπ.norm_apply])
  let T : H →ₗ[ℂ] H :=
    { toFun := fun v => ∫ g, f g • π g v ∂μ
      map_add' := fun v w => by simp only [map_add, smul_add, integral_add (hi v) (hi w)]
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply, ← integral_smul, smul_comm c] }
  have hT : IsRepOp π μ f (T.mkContinuous (∫ g, ‖f g‖ ∂μ) fun v => by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp only [norm_smul, hπ.norm_apply, integral_mul_const]) := fun v => ⟨hi v, rfl⟩
  rwa [hT.repOp_eq]
end IsUnitaryRep
end GlobalTheory.OpTrace
