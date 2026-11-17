-- Prove2me | solution 1 for N25.genus_four
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:22.939408+00:00
-- url     : https://prove2.me/submissions/5a05560b-c79d-4dff-8f6c-71c50436b85e

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_N25_level25_subgroup_membership
import Theorems.Thm_N25_level25_indices
import Theorems.Thm_N25_level25_S_doubleCosets
import Theorems.Thm_N25_level25_ST_doubleCosets
import Theorems.Thm_N25_level25_T_doubleCosets

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

/-- The prescribed intermediate modular function field has genus four. -/
theorem _root_.solution :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 N25.H25) = 4 := by
  let Γ := CohCarrier.GammaH 25 H25
  let L := laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
  let y : L := ⟨jqModC (AlgebraicClosure ℚ),jq_mem_baseChange Γ⟩
  have hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := rfl
  have hΓ : Gamma1 25 ≤ Γ := Gamma1_le_GammaH 25 H25
  have hminus : (-1 : SL(2, ℤ))∈Γ := by
    apply CohCarrier.mem_GammaH_iff.mpr
    have h0 : (-1 : SL(2, ℤ))∈Gamma0 25 := by rw [Gamma0_mem]; decide
    refine ⟨h0,?_⟩
    rw [level25_subgroup_membership]
    change (-1 : ZMod 25)=1 ∨ (-1 : ZMod 25)=7 ∨ (-1 : ZMod 25)=18 ∨ (-1 : ZMod 25)=24
    decide
  have hjoin : Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) = Γ :=
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr hminus)
  have hfull : Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set L)) L =
      (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index :=
    finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
      (AlgebraicClosure ℚ) 25 H25 y hy
  have hindex : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = 150 := by
    rw [hjoin]
    exact level25_indices.1
  have hdegree := hfull.trans hindex
  have hc := natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index 25 Γ hΓ y hy hfull
  have hzero := hc.1.trans level25_ST_doubleCosets
  have hspecial := hc.2.1.trans level25_S_doubleCosets
  have hpole := hc.2.2.trans level25_T_doubleCosets
  have hg := two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le 25 Γ hΓ y hy
  rw [hpole,hzero,hspecial,hdegree] at hg
  change 2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ) L + 14 + 50 + 80 = 150 + 2 at hg
  change AlgebraicCurve.genusFF (AlgebraicClosure ℚ) L = 4
  omega

end N25
