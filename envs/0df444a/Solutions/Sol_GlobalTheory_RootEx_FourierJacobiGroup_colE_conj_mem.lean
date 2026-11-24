-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobiGroup.colE_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:17:35.881837+00:00
-- url     : https://prove2.me/submissions/ad7b5e53-064a-4e47-a2de-01655c3a91aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_uni_conj
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_inv
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_offdiag
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_colE_neg
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff


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
theorem _root_.solution (q : ℕ) (β : n → k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c q) :
    colE c q β * u * (colE c q β)⁻¹ ∈ N k n c q := by
  rw [Radical.mem_N_iff] at hu ⊢
  rw [colE_inv]
  exact uni_conj (b := lev q) (colE_offdiag q β) (colE_offdiag q (-β))
    (congrArg Units.val (QuotStep.colE_neg q β)) hu
end GlobalTheory.RootEx.FourierJacobiGroup
