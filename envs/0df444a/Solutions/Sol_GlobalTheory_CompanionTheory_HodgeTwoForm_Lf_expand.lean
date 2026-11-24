-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.Lf_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:10.150173+00:00
-- url     : https://prove2.me/submissions/d9552c1e-7d66-4a8b-afd7-860ad99a4ccf

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_Lf_ev
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
theorem _root_.solution (hP : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Module.Dual R (Glob1 F))
    (h : ∀ x, x = ∑ i, l i x • w i) (T : C) (α : Ω[F.obj T⁄R]) :
    α = ∑ i, Lf hP (l i) T α • evForm F T (w i) := by
  refine (hP T).inductionOn α _ (by simp) (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · conv_lhs => rw [h x]
    simp only [map_sum, map_smul, Lf_ev, algebraMap_smul]
  · conv_lhs => rw [hy]
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]
  · conv_lhs => rw [hy, hz]
    simp only [map_add, add_smul, Finset.sum_add_distrib]
end GlobalTheory.CompanionTheory.HodgeTwoForm
