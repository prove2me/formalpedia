-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.result_headsize
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:41:43.028194+00:00
-- url     : https://prove2.me/submissions/d7278aa2-8f6a-46c6-a689-63612e4a6d7c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_localResult_outputs

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem exportedState_frame (a : State 16 896) (i : Fin 896)
    (hi : i≠659 ∧ i≠668 ∧ i≠669 ∧ i≠846 ∧ i≠847) :
    (exportedState a).stacks i=a.stacks i := by
  simp only [exportedState,clearMany_stacks,List.mem_cons,
    List.not_mem_nil,hi.2.1,hi.2.2.1,hi.2.2.2.1,or_self]
  rw [copyState_frame _ _ _ _ hi.2.2.2.2]
  simp [clearState,hi.1]

theorem lowResultFrom_low (src : Fin 896) (a : State 16 896) (b : Data) (i : Fin 768)
    (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (exportedState (lowResultFrom src a b)).stacks (lowStacks i)=b.stacks i := by
  have hlow (j : Fin 768) (hj : i≠j) : lowStacks i≠lowStacks j :=
    fun h => hj (lowStacks.injective h)
  have hhigh (j : Fin 896) (hj : 768 ≤ j.val) : lowStacks i≠j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=j.val at hv
    have := i.isLt
    omega
  rw [exportedState_frame _ _ ⟨hlow 659 h659,hlow 668 h668,hlow 669 h669,
    hhigh 846 (by decide),hhigh 847 (by decide)⟩]
  exact embedState_stack id lowStacks _ b lowStacks.injective i


theorem leafFrom_head_outputs (src : Fin 896) (frame : State 40 896) (a : State 16 896) (b : Data)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    let result := localResult b rp rm rs n N W z rows low raw shifted
    let e := embedState leafRegs id frame (exportedState (lowResultFrom src a result))
    let js := selectedHeads n rows low z
    e.stacks 650=HeadScatterProgram.indices js ∧
    e.stacks 651=List.replicate js.length false ∧
    e.stacks 670=HeadScatterProgram.mask n js (List.replicate js.length true) ∧
    e.stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
        Encoding.encodeNat) := by
  dsimp only
  have hh := localResult_outputs b rp rm rs n N W z rows low raw shifted
  have hstack (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
      (embedState leafRegs id frame (exportedState (lowResultFrom src a
        (localResult b rp rm rs n N W z rows low raw shifted)))).stacks (lowStacks i)=
          (localResult b rp rm rs n N W z rows low raw shifted).stacks i :=
    (embedState_stack leafRegs id frame _ Function.injective_id (lowStacks i)).trans
      (lowResultFrom_low src a _ i h659 h668 h669)
  exact ⟨(hstack 650 (by decide) (by decide) (by decide)).trans hh.1,
    (hstack 651 (by decide) (by decide) (by decide)).trans hh.2.1,
    (hstack 670 (by decide) (by decide) (by decide)).trans hh.2.2.1,
    (hstack 671 (by decide) (by decide) (by decide)).trans hh.2.2.2⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem result_headsize_oai (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 651=
      List.replicate (selectedHeads s.n s.rows s.low z).length false := by
  exact (SignatureHeadLoader.leafFrom_head_outputs headAddress frame _ _ rp rm rs
    s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).2.1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.result_headsize_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.result_headsize_oai
