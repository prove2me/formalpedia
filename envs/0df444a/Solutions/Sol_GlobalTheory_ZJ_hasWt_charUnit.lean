-- Prove2me | solution 1 for GlobalTheory.ZJ.hasWt_charUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:43:30.985244+00:00
-- url     : https://prove2.me/submissions/004d7f0f-97b4-41ae-aaad-f1bec3d19a8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Theorems.Thm_GlobalTheory_SplitTorusPoints_coord_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZJ
attribute [instance] Charts.fin Charts.finC
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
private theorem appLE_univ_univ_apply_eq_appTop {A B : Scheme.{0}} (f : A ⟶ B) (u : Γ(B, ⊤)) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    (f.appLE ⊤ ⊤ h).hom u = f.appTop.hom u := by
  show _ = (f.app ⊤).hom u
  rw [Scheme.Hom.app_eq_appLE]
  rfl
example (X : Scheme.{0}) [IsAffine X] (f : Γ(X, ⊤)) :
    ∃ (C : Charts X) (i i' : {i // C.wt i = C.c₀}), C.W i = X.basicOpen f ∧ C.W i' = X.basicOpen (1 - f) := by
  refine ⟨Charts.ofSections X (fun _ : Bool => ()) () (fun b => if b then f else 1 - f) ?_,
    ⟨true, rfl⟩, ⟨false, rfl⟩, rfl, rfl⟩
  have h := X.basicOpen_add_le f (1 - f)
  rw [add_sub_cancel, X.basicOpen_of_isUnit isUnit_one] at h
  exact top_unique (h.trans (sup_le (le_iSup_of_le ⟨true, rfl⟩ le_rfl) (le_iSup_of_le ⟨false, rfl⟩ le_rfl)))
example (S : Scheme.{0}) [IsAffine S] (a) :
    (Charts.ofTorus S 1).r a (some 0) = (charUnit S (Fin 1 → ℤ) (Pi.single 0 1)).val := rfl
end GlobalTheory.ZJ
end
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZJ
attribute [instance] Charts.fin Charts.finC
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
namespace GlobalTheory.ZJ
theorem _root_.solution (χ : X) : HasWt (𝟙 (splitTorus S X)) ⊤ (charUnit S X χ).val χ := by
  intro Y t g h h'
  rw [appLE_univ_univ_apply_eq_appTop, appLE_univ_univ_apply_eq_appTop, Category.comp_id, ← SplitTorusPoints.coord_single,
    ← SplitTorusPoints.coord_single, ← SplitTorusPoints.coord_single, SplitTorusPoints.coord_mul_single]
end GlobalTheory.ZJ
