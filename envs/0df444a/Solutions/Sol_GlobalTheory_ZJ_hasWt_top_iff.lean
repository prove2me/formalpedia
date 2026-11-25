-- Prove2me | solution 1 for GlobalTheory.ZJ.hasWt_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:41:08.452575+00:00
-- url     : https://prove2.me/submissions/25fb3a7d-bd01-4d2d-8e1e-826bd1578eb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
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
theorem _root_.solution (i : splitTorus S X ⟶ H) (u : Γ(H.left, ⊤)) (χ : X) :
    HasWt i ⊤ u χ ↔ ∀ (Y : Over S) (t : Y ⟶ splitTorus S X) (g : Y ⟶ H),
      ((t ≫ i) * g).left.appTop.hom u = t.left.appTop.hom (charUnit S X χ).val * g.left.appTop.hom u := by
  constructor
  · intro hw Y t g
    have key := hw Y t g (Scheme.Hom.preimage_top _).ge (Scheme.Hom.preimage_top _).ge
    rwa [appLE_univ_univ_apply_eq_appTop, appLE_univ_univ_apply_eq_appTop] at key
  · intro hw Y t g h h'
    rw [appLE_univ_univ_apply_eq_appTop, appLE_univ_univ_apply_eq_appTop]
    exact hw Y t g
end GlobalTheory.ZJ
