-- Prove2me | solution 1 for GlobalTheory.CosetCrit.posDef_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:35.569056+00:00
-- url     : https://prove2.me/submissions/31cd635d-0679-43d4-90ad-30d67926f6c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorsionTwistTsumNormGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.CosetCrit
namespace GlobalTheory.CosetCrit
theorem _root_.solution {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) : q.PosDef := by
  intro x hx
  by_contra h
  have hinj : Function.Injective fun k : ℤ => k • x := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually_gt_atTop 0
  obtain ⟨k, hk⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul] at hk
  have : (0 : ℝ) ≤ ((k * k : ℤ) : ℝ) := by exact_mod_cast mul_self_nonneg k
  nlinarith [not_lt.1 h]
end GlobalTheory.CosetCrit
