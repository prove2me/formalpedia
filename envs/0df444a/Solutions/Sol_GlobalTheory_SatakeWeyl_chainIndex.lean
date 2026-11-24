-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.chainIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:18:19.611304+00:00
-- url     : https://prove2.me/submissions/2102d460-5829-45bf-a2ca-b356acf7cfe3

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutomorphismSubgroupChainIndex
import Theorems.Thm_GlobalTheory_SatakeWeyl_chain_step
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution : ChainIndex := by
  intro A _ U c Q hc hQ j l
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨h1, h2⟩ := chain_step U c hc (j + l)
    have e : j + ((l + 1 : ℕ) : ℤ) = j + l + 1 := by push_cast; ring
    rw [e]
    refine ⟨ih.1.trans h1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ ih.1 h1, ih.2, h2, hQ, pow_succ]
end GlobalTheory.SatakeWeyl
