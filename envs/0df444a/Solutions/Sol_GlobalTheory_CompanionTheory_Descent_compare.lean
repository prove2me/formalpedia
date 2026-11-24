-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:59.60634+00:00
-- url     : https://prove2.me/submissions/f488c5da-0c33-42a4-a6c9-5d931a419650

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_rm_rm
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_rm_id
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_allQIso_of_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_fub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution (hCx : CxSt) (hQ : QCalcSt) (hFub : FubiniSt) [Quiver.IsThin C] [Quiver.IsThin D]
    (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (w : C × D ⥤ AffOp X) (σ : D ⥤ C)
    (h₁ : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1) (h₂ : ∀ T, (w.obj T).unop.1 ≤ (g.obj T.2).unop.1)
    (h₃ : ∀ d, (g.obj d).unop.1 ≤ (w.obj (σ.obj d, d)).unop.1)
    (A₁ : ∀ c, Acyc s (CategoryTheory.Prod.sectR c D ⋙ w) (f.obj c).unop.1 (fun T ↦ h₁ (c, T)))
    (A₂ : ∀ d, Acyc s (CategoryTheory.Prod.sectR d C ⋙ CategoryTheory.Prod.swap D C ⋙ w) (g.obj d).unop.1 (fun T ↦ h₂ (T, d))) :
    AllQIso (rm s f g σ (fun d ↦ (h₃ d).trans (h₁ (σ.obj d, d)))) := by
  have Q₁ := fub s hFub f w h₁ A₁
  let w' : D × C ⥤ AffOp X := CategoryTheory.Prod.swap D C ⋙ w
  have h₂' : ∀ T : D × C, (w'.obj T).unop.1 ≤ (g.obj T.1).unop.1 := fun T ↦ h₂ (T.2, T.1)
  have Q₂ := fub s hFub g w' h₂' A₂
  let sc : D ⥤ D × C := (𝟭 D).prod' σ
  have ht : ∀ d, (g.obj d).unop.1 ≤ (w'.obj (sc.obj d)).unop.1 := h₃
  have Qid : AllQIso (rm s g g (𝟭 D) (fun _ ↦ le_rfl)) :=
    allQIso_of_inv hCx _ (rm s g g (𝟭 D) (fun _ ↦ le_rfl))
      (fun i z ↦ by rw [pull_rm_id, pull_rm_id]) (fun i z ↦ by rw [pull_rm_id, pull_rm_id])
  have Qt : AllQIso (rm s w' g sc ht) :=
    ((hQ R D (g ⋙ OAff s) (D × C) D (w' ⋙ OAff s) (g ⋙ OAff s) (rm s g w' (CategoryTheory.Prod.fst D C) h₂')
      (rm s w' g sc ht) (rm s g g (𝟭 D) (fun _ ↦ le_rfl))
      (fun i z ↦ (pull_rm_rm s g w' g (CategoryTheory.Prod.fst D C) sc h₂' ht (fun _ ↦ le_rfl) i z).symm)).2.1 Q₂ Qid)
  have hsw : ∀ T, (w'.obj T).unop.1 ≤ (w.obj ((CategoryTheory.Prod.swap D C).obj T)).unop.1 := fun _ ↦ le_rfl
  have hsw' : ∀ T, (w.obj T).unop.1 ≤ (w'.obj ((CategoryTheory.Prod.swap C D).obj T)).unop.1 := fun _ ↦ le_rfl
  have Qsw : AllQIso (rm s w w' (CategoryTheory.Prod.swap D C) hsw) :=
    allQIso_of_inv hCx _ (rm s w' w (CategoryTheory.Prod.swap C D) hsw')
      (fun i z ↦ (pull_rm_rm s w w' w _ _ hsw hsw' (fun _ ↦ le_rfl) i z).trans (pull_rm_id s w _ i z))
      (fun i z ↦ (pull_rm_rm s w' w w' _ _ hsw' hsw (fun _ ↦ le_rfl) i z).trans (pull_rm_id s w' _ i z))
  have hk₁ : ∀ T, (w'.obj T).unop.1 ≤ (f.obj ((CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D).obj T)).unop.1 :=
    fun T ↦ h₁ _
  have Qk₁ : AllQIso (rm s f w' (CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D) hk₁) :=
    ((hQ R C (f ⋙ OAff s) (C × D) (D × C) (w ⋙ OAff s) (w' ⋙ OAff s) (rm s f w (CategoryTheory.Prod.fst C D) h₁)
      (rm s w w' (CategoryTheory.Prod.swap D C) hsw) (rm s f w' (CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D) hk₁)
      (fun i z ↦ (pull_rm_rm s f w w' _ _ h₁ hsw hk₁ i z).symm)).1 Q₁ Qsw)
  have hk₂ : ∀ T, (g.obj T).unop.1 ≤ (f.obj ((sc ⋙ CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D).obj T)).unop.1 :=
    fun d ↦ (h₃ d).trans (h₁ (σ.obj d, d))
  exact ((hQ R C (f ⋙ OAff s) (D × C) D (w' ⋙ OAff s) (g ⋙ OAff s)
      (rm s f w' (CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D) hk₁) (rm s w' g sc ht)
      (rm s f g (sc ⋙ CategoryTheory.Prod.swap D C ⋙ CategoryTheory.Prod.fst C D) hk₂)
      (fun i z ↦ (pull_rm_rm s f w' g _ _ hk₁ ht hk₂ i z).symm)).1 Qk₁ Qt)
end GlobalTheory.CompanionTheory.Descent
