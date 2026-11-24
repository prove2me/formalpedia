-- Prove2me | solution 1 for GlobalTheory.CosetCrit.tendsto_class
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:35.975798+00:00
-- url     : https://prove2.me/submissions/2287fb2c-2bae-4230-93b8-de78e0c38ebd

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
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (y : X) {m : ℕ} (hm : m ≠ 0) :
    Filter.Tendsto (fun χ => q (y + m • χ)) Filter.cofinite Filter.atTop := by
  have hinj : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have h1 : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (by exact_mod_cast hm : (m : ℤ) ≠ 0) h1
  exact hq.comp hinj.tendsto_cofinite
end GlobalTheory.CosetCrit
