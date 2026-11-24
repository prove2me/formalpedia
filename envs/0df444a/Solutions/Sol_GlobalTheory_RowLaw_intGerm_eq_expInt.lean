-- Prove2me | solution 1 for GlobalTheory.RowLaw.intGerm_eq_expInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:04:12.827891+00:00
-- url     : https://prove2.me/submissions/26bb20ae-5c59-4ede-a2c8-fac55645593d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_subst
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_X
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_subst_sum_smul
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_one_group
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_upG_subst
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_upG_const
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero
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
open GlobalTheory GlobalTheory.RowLaw
open GermRing
namespace GlobalTheory.RowLaw
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type)
    [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V →
    ∀ (H : ∀ g, X.CartHyp V g) (S : ∀ g, Sys (RawChart.cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g, (S g).IsT (t g)) → IntGerm V t = ExpInt X V := by
  intro C _ V d _ I _ κ _ Y hY H S t ht
  let E : ∀ g, κ → MvPowerSeries (I g) C := fun g x =>
    subst (fun i : κ => ∑ c : I g, Y.u g c i • (X c : MvPowerSeries (I g) C)) (Y.ex x)
  have hL : ∀ g (i : κ), constantCoeff (∑ c : I g, Y.u g c i • (X c : MvPowerSeries (I g) C)) = 0 := fun g i => by
    simp [map_sum]
  have hE0 : ∀ g x, constantCoeff (E g x) = 0 := fun g x => constantCoeff_subst_zero (hL g) (hY.exc x)
  have hexp : ∀ g x, Y.expPt g x = upG g (E g x) := by
    intro g x
    rw [upG_subst g (hL g)]
    unfold RawChart.expPt
    congr 1
    funext i
    have hs : HasSubst (fun x : I g => (X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    unfold upG
    rw [subst_sum_smul hs]
    simp only [subst_X hs]
  have key := fun g => one_group hY g (H g) (S g) (t g) (ht g) (E g) fun _ => rfl
  choose Φ hΦ0 hΦi hΦ using fun g => (key g).1
  choose Ψ hΨ0 hΨi hΨ using fun g => (key g).2
  have hts : HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    hasSubst_of_constantCoeff_zero fun w => upG_const _ ((ht w.1).1 _)
  have hes : HasSubst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by rw [hexp]; exact upG_const _ (hE0 _ _)
  ext F
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hx : ∀ (g : Fin 2) (x : κ), constantCoeff (X (g, x) : MvPowerSeries (Fin 2 × κ) C) = 0 :=
      fun _ _ => constantCoeff_X _
    have h0 : ∀ w : WV I, constantCoeff (subst (fun x : κ => (X (w.1, x) : MvPowerSeries (Fin 2 × κ) C))
        (Ψ w.1 w.2)) = 0 := fun w => constantCoeff_subst_zero (hx _) (hΨ0 _ _)
    refine ⟨_, intS_subst h0 (fun w => intS_subst (hx _) (fun _ => intS_X _) (hΨi _ _)) hγ, ?_⟩
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hes]
    congr 1
    funext w
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (hx _)) hes, hΨ, upG_subst _ (hE0 _)]
    congr 1
    funext x
    rw [subst_X hes, hexp]
  · rintro ⟨f, hf, rfl⟩
    have h0 : ∀ p : Fin 2 × κ, constantCoeff (upG p.1 (Φ p.1 p.2)) = 0 := fun p => upG_const _ (hΦ0 _ _)
    refine ⟨_, intS_subst h0
      (fun p => intS_subst (fun _ => constantCoeff_X _) (fun _ => intS_X _) (hΦi _ _)) hf, ?_⟩
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hts]
    congr 1
    funext p
    rw [hexp, hΦ, upG_subst _ (ht _).1]
    conv_rhs => unfold upG
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    · congr 1
      funext c
      exact (subst_X hts (⟨p.1, c⟩ : WV I)).symm
    · exact hts
end GlobalTheory.RowLaw
