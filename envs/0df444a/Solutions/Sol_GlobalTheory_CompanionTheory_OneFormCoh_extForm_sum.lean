-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneFormCoh.extForm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:12.193507+00:00
-- url     : https://prove2.me/submissions/7c89a46e-0ae8-4b3d-b5f9-adb6a51b9cb4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneFormCoh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.OneFormCoh
theorem _root_.solution (hp : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (T : C) (α : Ω[F.obj T⁄R]) :
    ∑ i, extForm F hp (l i) T α • (w i).1 T = α := by
  refine (hp T).inductionOn α (fun α => ∑ i, GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T α • (w i).1 T = α) ?_ ?_ ?_ ?_
  · simp only [map_zero, zero_smul, Finset.sum_const_zero]
  · intro v
    change ∑ i, GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T (v.1 T) • (w i).1 T = v.1 T
    simp only [GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, algebraMap_smul]
    have h := congrArg (MainStatements.Hodge.evForm F T) (hw v)
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h
  · intro s m hm
    conv_rhs => rw [← hm]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_smul]
  · intro m₁ m₂ h₁ h₂
    conv_rhs => rw [← h₁, ← h₂]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, add_smul]
end GlobalTheory.CompanionTheory.OneFormCoh
