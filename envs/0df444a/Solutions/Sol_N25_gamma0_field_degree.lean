-- Prove2me | solution 1 for N25.gamma0_field_degree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:49.966498+00:00
-- url     : https://prove2.me/submissions/3597990f-eaa2-4273-803e-4df2d6cb4c36

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_subgroup_index
import Theorems.Thm_N25_level25_subgroup_membership
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le

set_option autoImplicit false

namespace N25

/-- The geometric Gamma-zero field is a subfield of the level-H field,
and their relative degree is five. -/
theorem _root_.solution :
    let F₀ := ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 25))
    let F := ModularCurve.xHFunctionFieldBar 25 H25
    F₀ ≤ F ∧ F₀.relfinrank F = 5 := by
  let E₀ := ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 25)
  let E := ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH 25 H25)
  have hle : E₀ ≤ E :=
    ModularCurve.qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 H25)
  have hminus : (-1 : (ZMod 25)ˣ) ∈ H25 := by
    rw [level25_subgroup_membership]
    decide
  have hsup : H25 ⊔ Subgroup.zpowers (-1 : (ZMod 25)ˣ) = H25 :=
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr hminus)
  have hdegree : E₀.relfinrank E = 5 := by
    have h := ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
      ℚ 25 H25
    rw [hsup, level25_subgroup_index] at h
    exact h
  have hpositive : 0 < E₀.relfinrank E := by rw [hdegree]; decide
  have hbase := ModularCurve.relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
    ℚ (AlgebraicClosure ℚ) E₀ E hle hpositive
  constructor
  · change ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) E₀ ≤
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) E
    exact IntermediateField.adjoin.mono _ _ _ (Set.image_mono hle)
  · change (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) E₀).relfinrank
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) E) = 5
    exact hbase.trans hdegree

end N25
