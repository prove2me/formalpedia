-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.z_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:51.006705+00:00
-- url     : https://prove2.me/submissions/319df12a-135c-4022-b94c-168258938096

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_z_eq
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (z : Cn F 0) (hz : dn F 0 z = 0) {T T' : Pᵒᵖ} (φ : T ⟶ T') :
    mp F φ (z ((Functor.const (Fin 1)).obj T)) = z ((Functor.const (Fin 1)).obj T') := by
  have hA : ∀ (h : T' ⟶ T') (x : F.obj T'), mp F h x = x := fun h x ↦ by
    rw [show h = 𝟙 T' from Quiver.Hom.unop_inj (Subsingleton.elim _ _), mp_id]
  have hB : ∀ (h : T ⟶ T') (x : F.obj T), mp F h x = mp F φ x := fun h x ↦ by
    rw [show h = φ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
  let c : Fin 2 ⥤ Pᵒᵖ := ComposableArrows.mk₁ φ
  have e := congrFun hz c
  rw [dn_apply, Fin.sum_univ_two] at e
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at e
  have e1 := add_neg_eq_zero.1 e
  have e2 : z (face 0 c) = z ((Functor.const (Fin 1)).obj T') := z_eq F z (face 0 c)
  have e3 : z (face 1 c) = z ((Functor.const (Fin 1)).obj T) := z_eq F z (face 1 c)
  exact (congrArg (mp F φ) e3).symm.trans ((hB _ _).symm.trans (e1.symm.trans ((hA _ _).trans e2)))
end GlobalTheory.CompanionTheory.AffAcyc
