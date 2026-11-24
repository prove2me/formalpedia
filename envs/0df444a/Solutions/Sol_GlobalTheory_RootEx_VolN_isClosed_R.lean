-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.isClosed_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:34:12.848458+00:00
-- url     : https://prove2.me/submissions/9fd527db-3dcb-4ff2-a87a-e18c2fc42071

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_mem_R_iff
import Theorems.Thm_GlobalTheory_RootEx_VolN_continuous_entry
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution (p : ℕ) : IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) := by
  have := (SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have h : IsClosed {g : GL (n ⊕ Fin c) k | InR p g} := by
    simp only [InR, Set.ofPred_forall]
    exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_entry r s) continuous_const
  have e : (R k n c p : Set (GL (n ⊕ Fin c) k)) = {g | InR p g} ∩ (fun g => g⁻¹) ⁻¹' {g | InR p g} :=
    Set.ext fun g => mem_R_iff
  rw [e]
  exact h.inter (h.preimage continuous_inv)
end GlobalTheory.RootEx.VolN
