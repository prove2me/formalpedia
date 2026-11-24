-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.intS_addP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:09.616052+00:00
-- url     : https://prove2.me/submissions/becb0f7f-217c-4cbf-a434-0061abf82e8b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_subst
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_log_add_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ} {V : VF C}
namespace GlobalTheory.RowLaw.GermRing
theorem _root_.solution (hY : RLaw Y V) {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (ia : ∀ i, IntS V (a i)) (ib : ∀ i, IntS V (b i)) (i : κ) :
    IntS V (addP Y a b i) := by
  set ab : Fin 2 × κ → MvPowerSeries τ C := fun p => if p.1 = 0 then a p.2 else b p.2 with hab
  have h0 : ∀ p, constantCoeff (ab p) = 0 := fun p => by
    simp only [hab]; split_ifs; exacts [ha _, hb _]
  have hi : ∀ p, IntS V (ab p) := fun p => by
    simp only [hab]; split_ifs; exacts [ia _, ib _]
  have hs := hasSubst_of_constantCoeff_zero h0
  have hg : ∀ (j : Fin 2) x, constantCoeff (gp C κ j x) = 0 := fun j x => constantCoeff_X _
  have key : addP Y a b i = subst ab (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1) i) := by
    unfold addP
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (log_add_const hY (hg 0) (hg 1))) hs]
    congr 1
    funext x
    rw [subst_add hs, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (hg 0)) hs,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (hg 1)) hs]
    have e0 : (fun s => subst ab (gp C κ (0 : Fin 2) s)) = a := funext fun s => by
      rw [gp, subst_X hs]; simp [hab]
    have e1 : (fun s => subst ab (gp C κ (1 : Fin 2) s)) = b := funext fun s => by
      rw [gp, subst_X hs]; simp [hab]
    rw [e0, e1]
  rw [key]
  exact intS_subst h0 hi (hY.addInt i)
end GlobalTheory.RowLaw.GermRing
