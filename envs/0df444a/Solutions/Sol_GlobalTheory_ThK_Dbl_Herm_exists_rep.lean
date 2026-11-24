-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Herm.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:44.618829+00:00
-- url     : https://prove2.me/submissions/c7460ed5-7508-4e19-8029-c3386ad8b1ad

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HermAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Herm
open scoped InnerProductSpace
open PositivityTheory.ThKF.Abs
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace GlobalTheory.ThK.Dbl.Herm
theorem _root_.solution (b : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ) (Y : Submodule ℂ U) [FiniteDimensional ℂ Y] :
    ∃ T : U →ₗ[ℂ] Y, ∀ x, ∀ y ∈ Y, ⟪(T x : U), y⟫_ℂ = b x y := by
  have := FiniteDimensional.complete ℂ Y
  have ex : ∀ x, ∃ t : Y, ∀ y : Y, ⟪t, y⟫_ℂ = b x y := fun x =>
    ⟨(InnerProductSpace.toDual ℂ Y).symm (LinearMap.toContinuousLinearMap (b x ∘ₗ Y.subtype)), fun y => by simp⟩
  choose t ht using ex
  refine ⟨⟨⟨t, fun x x' => ext_inner_right ℂ fun y => ?_⟩, fun c x => ext_inner_right ℂ fun y => ?_⟩, fun x y hy => ht x ⟨y, hy⟩⟩
  · simp [inner_add_left, ht]
  · simp [inner_smul_left, ht]
end GlobalTheory.ThK.Dbl.Herm
