-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.CoD.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:36.980833+00:00
-- url     : https://prove2.me/submissions/0fb07627-2770-4816-b314-a4f85fb2f5a0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_fc_zero_snoc
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
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
variable {E : Type} [Category.{0} E]
variable [Quiver.IsThin E]
variable {H : E ⥤ ModuleCat.{0} R} {B : E → ModuleCat.{0} R}
namespace GlobalTheory.CompanionTheory.NerveCoh
namespace CoD
theorem _root_.solution (A : CoD H B) (a : MCn H 0) (ha : mdn H 0 a = 0) (c : Fin 1 ⥤ E) {y : E}
    (g : c.obj (Fin.last 0) ⟶ y) : A.ev g (a c) = A.ev (𝟙 y) (a (pt y)) := by
  have h := A.ev_mdn a (snoc c y g) (lastH c y g)
  rw [ha, Fin.sum_univ_two] at h
  have e1 : ∀ m : (fc 0 (snoc c y g)).obj (Fin.last 0) ⟶ y, A.ev m (a (fc 0 (snoc c y g))) = A.ev (𝟙 y) (a (pt y)) :=
    fun m ↦ A.ev_congr a (fc_zero_snoc c y g) m _
  have e2 : ∀ m : (fc 1 (snoc c y g)).obj (Fin.last 0) ⟶ y, A.ev m (a (fc 1 (snoc c y g))) = A.ev g (a c) :=
    fun m ↦ A.ev_congr a (fc_last_snoc c y g) m g
  have h' : (0 : B y) = ((-1 : R) ^ ((0 : Fin 2) : ℕ)) • A.ev (𝟙 y) (a (pt y)) +
      ((-1 : R) ^ ((1 : Fin 2) : ℕ)) • A.ev g (a c) :=
    (map_zero _).symm.trans (h.trans (congrArg₂ (· + ·) (congrArg _ (e1 _)) (congrArg _ (e2 _))))
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h'
  exact (sub_eq_zero.1 ((sub_eq_add_neg _ _).trans h'.symm)).symm
end CoD
end GlobalTheory.CompanionTheory.NerveCoh
