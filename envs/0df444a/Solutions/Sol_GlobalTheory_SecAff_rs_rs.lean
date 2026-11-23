-- Prove2me | solution 1 for GlobalTheory.SecAff.rs_rs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:50.097435+00:00
-- url     : https://prove2.me/submissions/40b721ee-610a-4838-bd16-f835e630f7f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    rs h₂ (rs h₁ x) = rs (h₂.trans h₁) x := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) x = _
  rw [← Functor.map_comp]
  rfl
end GlobalTheory.SecAff
