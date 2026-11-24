-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobiGroup.colE_conj_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:54.494799+00:00
-- url     : https://prove2.me/submissions/afe0a006-0b04-455d-b121-2760ea853c24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_conj_colE
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_VolN_exists_of_mem_R


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.FourierJacobiGroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.FourierJacobiGroup
theorem _root_.solution (q : ℕ) (β : n → k) {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c q) :
    ∃ r' ∈ R k n c q, ∃ γ : n → k, colE c q β * r = r' * colE c q γ := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  refine ⟨embX c x * (colE c q ((x⁻¹).val.mulVec β) * u * (colE c q ((x⁻¹).val.mulVec β))⁻¹),
    mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right (colE_conj_mem q _ hu)),
    (x⁻¹).val.mulVec β, ?_⟩
  rw [← QuotStep.conj_colE, map_inv]
  group
end GlobalTheory.RootEx.FourierJacobiGroup
