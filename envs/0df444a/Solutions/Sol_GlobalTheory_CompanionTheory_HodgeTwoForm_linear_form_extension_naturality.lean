-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.linear_form_extension_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:40:06.572107+00:00
-- url     : https://prove2.me/submissions/62a0ac6f-6879-403c-b41c-2f2982c63c4c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_Lf_ev
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_form_pullback_evaluation
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution (hP : Par F) (l : Module.Dual R (Glob1 F)) {T T' : C} (φ : T ⟶ T')
    (α : Ω[F.obj T⁄R]) : Lf hP l T' (p1 F φ α) = mp F φ (Lf hP l T α) := by
  refine (hP T).inductionOn α _ (by simp) (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [form_pullback_evaluation, Lf_ev, Lf_ev, AlgHom.commutes]
  · rw [oneFormsMapOfFunctorMorphism_smul, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  · simp only [map_add, hy, hz]
end GlobalTheory.CompanionTheory.HodgeTwoForm
