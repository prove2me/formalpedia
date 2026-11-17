-- Prove2me | solution 1 for N25.gamma0_genus_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:42.340828+00:00
-- url     : https://prove2.me/submissions/74aab7fe-2048-4877-8e4d-d4e8086bc133

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_N25_level25_gamma0_index
import Theorems.Thm_N25_level25_gamma0_S_doubleCosets
import Theorems.Thm_N25_level25_gamma0_ST_doubleCosets
import Theorems.Thm_N25_level25_gamma0_T_doubleCosets
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

open ModularCurve CongruenceSubgroup AlgebraicCurve

namespace N25

private theorem jq_mem_baseChange (Γ : Subgroup SL(2, ℤ)) :
    jqModC (AlgebraicClosure ℚ) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := by
  have hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ Γ :=
    intFormRatiosC_subset ℚ Γ (jqModC_mem_intFormRatiosC ℚ Γ)
  have hm : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := by
    change (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
    exact map_jqModC _
  rw [←hm]
  exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hj

/-- The full-unit level-25 modular function field has genus zero. -/
theorem _root_.solution :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 25))) = 0 := by
  let Γ := CohCarrier.GammaH 25 (⊤ : Subgroup (ZMod 25)ˣ)
  let L := laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
  let y : L := ⟨jqModC (AlgebraicClosure ℚ),jq_mem_baseChange Γ⟩
  have hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := rfl
  have hΓ : Gamma1 25 ≤ Γ := Gamma1_le_GammaH 25 ⊤
  have hminus : (-1 : SL(2, ℤ))∈Γ := by
    change (-1 : SL(2, ℤ))∈CohCarrier.GammaH 25 ⊤
    rw [CohCarrier.GammaH_top,Gamma0_mem]
    decide
  have hjoin : Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) = Γ :=
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr hminus)
  have hfull : Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set L)) L =
      (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index :=
    finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
      (AlgebraicClosure ℚ) 25 ⊤ y hy
  have hindex : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = 30 := by
    rw [hjoin]
    change (CohCarrier.GammaH 25 ⊤).index=30
    rw [CohCarrier.GammaH_top]
    exact level25_gamma0_index
  have hdegree := hfull.trans hindex
  have hST : Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
      (Subgroup.zpowers (ModularGroup.S*ModularGroup.T) : Set SL(2, ℤ))) = 10 := by
    change Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH 25 ⊤ : Set SL(2, ℤ)) _) = 10
    rw [CohCarrier.GammaH_top]
    exact level25_gamma0_ST_doubleCosets
  have hS : Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
      (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) = 16 := by
    change Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH 25 ⊤ : Set SL(2, ℤ)) _) = 16
    rw [CohCarrier.GammaH_top]
    exact level25_gamma0_S_doubleCosets
  have hT : Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
      ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) :
        Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) = 6 := by
    change Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH 25 ⊤ : Set SL(2, ℤ)) _) = 6
    rw [CohCarrier.GammaH_top]
    exact level25_gamma0_T_doubleCosets
  have hc := natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index 25 Γ hΓ y hy hfull
  have hzero := hc.1.trans hST
  have hspecial := hc.2.1.trans hS
  have hpole := hc.2.2.trans hT
  have hg := two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le 25 Γ hΓ y hy
  rw [hpole,hzero,hspecial,hdegree] at hg
  change 2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ) L + 6 + 10 + 16 = 30 + 2 at hg
  have hgenus : AlgebraicCurve.genusFF (AlgebraicClosure ℚ) L = 0 := by omega
  have hfield : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 25)) = L := by
    dsimp only [L,Γ]
    rw [CohCarrier.GammaH_top]
  exact (congrArg (fun E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) =>
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ) E) hfield).trans hgenus

end N25
