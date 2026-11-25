-- Prove2me | solution 1 for GlobalTheory.SW.SwdHeat.isHeat_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:18:44.324223+00:00
-- url     : https://prove2.me/submissions/914b3eac-6033-4095-bc60-318a62456713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThHStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwd
import Theorems.Thm_GlobalTheory_SW_SwdHeat_isHeat_sum
import Theorems.Thm_GlobalTheory_SW_EisHeat_isHeat_const_mul
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SwdHeat
open GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.SwdHeat
theorem _root_.solution {D D' : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D)
    (hD' : IsHeat Ψ D') : IsHeat Ψ fun Z z z' => D Z z z' - D' Z z z' := by
  have h := isHeat_sum Ψ (ι := Bool)
    (D := fun b => bif b then D else fun Z z z' => (-1) * D' Z z z') fun b => by
      cases b
      · exact isHeat_const_mul Ψ hD' _
      · exact hD
  simpa only [Fintype.sum_bool, cond_true, cond_false, neg_one_mul, ← sub_eq_add_neg] using h
end GlobalTheory.SW.SwdHeat
