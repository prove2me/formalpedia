-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneFormCoh.sum_contr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:54.285326+00:00
-- url     : https://prove2.me/submissions/c58fa2bd-edef-45a8-8a33-d84082176ca3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_OneFormCoh_contr_tmul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
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
theorem _root_.solution {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (t : Z1 F ⊗[R] Glob1 F) :
    ∑ i, contr F (l i) t ⊗ₜ[R] w i = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul f v =>
    simp_rw [GlobalTheory.CompanionTheory.OneFormCoh.contr_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, hw]
end GlobalTheory.CompanionTheory.OneFormCoh
