-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.isClosed_N
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:04.370569+00:00
-- url     : https://prove2.me/submissions/6c50a2d2-6b5b-46c2-b077-6b23f06e768d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
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
theorem _root_.solution (p : ℕ) : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  have := (SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = {g | InN p g} := Set.ext fun g => mem_N_iff
  rw [e]
  simp only [InN, Set.ofPred_forall]
  exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq (continuous_entry r s) continuous_const
end GlobalTheory.RootEx.VolN
