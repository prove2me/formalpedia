-- Prove2me | solution 1 for GlobalTheory.LinDescent.FunctionsAreInvariants.exists_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:45:07.551827+00:00
-- url     : https://prove2.me/submissions/922a8865-4164-4286-a21a-c47daf41d342

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfInvGenOfInvariants
import Theorems.Thm_GlobalTheory_LinDescent_gs_appLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}
namespace GlobalTheory.LinDescent
namespace FunctionsAreInvariants
theorem _root_.solution (h : FunctionsAreInvariants t π) (V : Y.Opens)
    (f : Γ(X, π ⁻¹ᵁ V))
    (hf : ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ t c) z _ f = gs r z _ f) :
    ∃ a : Γ(Y, V), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ π) z V a = gs r z _ f := by
  obtain ⟨a, rfl⟩ := (h V).2 f fun c e => fn_ext fun x hx =>
    (gs_appLE (𝟙 X) (t c) x _ _ e hx f).trans (hf c X (𝟙 X) x hx)
  exact ⟨a, fun Z r z hz => (gs_pull r π z V hz a).symm⟩
end FunctionsAreInvariants
end GlobalTheory.LinDescent
