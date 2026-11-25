-- Prove2me | solution 1 for GlobalTheory.ZJ.hasWt_iso_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:46.657719+00:00
-- url     : https://prove2.me/submissions/17ebf82a-d9a7-49d3-9f3b-7a8bd976802e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Theorems.Thm_GlobalTheory_ZJ_hasWt_top_iff
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
private theorem scheme_appTop_comp_apply {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (u : Γ(C, ⊤)) :
    (f ≫ g).appTop.hom u = f.appTop.hom (g.appTop.hom u) :=
  rfl
private theorem over_left_appTop_comp_apply {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (u : Γ(C.left, ⊤)) :
    (f ≫ g).left.appTop.hom u = f.left.appTop.hom (g.left.appTop.hom u) := by
  rw [Over.comp_left, scheme_appTop_comp_apply]
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
theorem _root_.solution (e : splitTorus S X ≅ H) [IsMonHom e.hom] (u : Γ(H.left, ⊤)) (χ : X) :
    HasWt e.hom ⊤ u χ ↔ HasWt (𝟙 (splitTorus S X)) ⊤ (e.hom.left.appTop.hom u) χ := by
  rw [hasWt_top_iff, hasWt_top_iff]
  constructor
  · intro hw Y t g
    rw [Category.comp_id, ← over_left_appTop_comp_apply (t * g) e.hom u, ← over_left_appTop_comp_apply g e.hom u, MonObj.mul_comp]
    exact hw Y t (g ≫ e.hom)
  · intro hw Y t g
    have key := hw Y t (g ≫ e.inv)
    rw [Category.comp_id, ← over_left_appTop_comp_apply (t * (g ≫ e.inv)) e.hom u, ← over_left_appTop_comp_apply (g ≫ e.inv) e.hom u,
      MonObj.mul_comp, Category.assoc, e.inv_hom_id, Category.comp_id] at key
    exact key
end GlobalTheory.ZJ
