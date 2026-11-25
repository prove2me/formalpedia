-- Prove2me | solution 1 for GlobalTheory.ZJ.HasWt.mem_range_of_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:51:59.595461+00:00
-- url     : https://prove2.me/submissions/b2d9d85f-656f-4668-b5a9-2868fe8f45ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Theorems.Thm_GlobalTheory_ZJ_charUnit_zero_val
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
private theorem scheme_appTop_comp_apply {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (u : Γ(C, ⊤)) :
    (f ≫ g).appTop.hom u = f.appTop.hom (g.appTop.hom u) :=
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
namespace HasWt
theorem _root_.solution {u : Γ((splitTorus S X).left, ⊤)} (hu : HasWt (𝟙 (splitTorus S X)) ⊤ u 0) :
    u ∈ Set.range ((splitTorus S X).hom.appLE ⊤ ⊤ le_top).hom := by
  have key := hu (splitTorus S X) (𝟙 _) 1 (Scheme.Hom.preimage_top _).ge (Scheme.Hom.preimage_top _).ge
  rw [appLE_univ_univ_apply_eq_appTop, appLE_univ_univ_apply_eq_appTop, charUnit_zero_val, map_one, _root_.one_mul, Category.comp_id, _root_.mul_one] at key
  refine ⟨(η : 𝟙_ (Over S) ⟶ splitTorus S X).left.appTop.hom u, ?_⟩
  have e1 : (1 : splitTorus S X ⟶ splitTorus S X).left =
      (splitTorus S X).hom ≫ (η : 𝟙_ (Over S) ⟶ splitTorus S X).left := rfl
  rw [e1, scheme_appTop_comp_apply] at key
  refine (appLE_univ_univ_apply_eq_appTop _ _ _).trans ?_
  rw [← key]
  rfl
end HasWt
end GlobalTheory.ZJ
