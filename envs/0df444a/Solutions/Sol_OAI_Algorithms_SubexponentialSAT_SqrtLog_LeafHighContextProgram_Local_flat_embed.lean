-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flat_embed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:53:28.050982+00:00
-- url     : https://prove2.me/submissions/4a5d307d-444b-4f80-bceb-522426b17e3e

import Mathlib
import Definitions.Def_OAIQ081S126

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramFlatPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flat_stack_injective : Function.Injective flatStacks := by decide

theorem flat_reg_ports (regs : Fin 4 → Bool) :
    ∀ i, flatOutRegs regs (flatRegs i) = (![false,false,false] : Fin 3 → Bool) i := by
  refine Fin.cases ?_ ?_
  · rfl
  refine Fin.cases ?_ ?_
  · rfl
  refine Fin.cases ?_ ?_
  · rfl
  intro i; exact Fin.elim0 i

theorem flat_reg_frame (regs : Fin 4 → Bool) :
    ∀ i, (¬ ∃ j, flatRegs j = i) → flatOutRegs regs i = regs i := by
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨0,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨1,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨2,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro _; rfl
  intro i; exact Fin.elim0 i

theorem flat_stack_ports (counter mask forward high : List Bool) :
    ∀ i, tapes counter mask forward [] [] [] high [] [] [] (flatStacks i) =
      (![[],[],high] : Fin 3 → List Bool) i := by
  refine Fin.cases ?_ ?_
  · rfl
  refine Fin.cases ?_ ?_
  · rfl
  refine Fin.cases ?_ ?_
  · rfl
  intro i; exact Fin.elim0 i

theorem flat_stack_frame (counter mask forward high : List Bool) :
    ∀ i, (¬ ∃ j, flatStacks j = i) →
      tapes counter mask forward [] [] [] high [] [] [] i =
      tapes counter mask forward [] counter [] [] [] [] [] i := by
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨0,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨1,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨2,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  intro i; exact Fin.elim0 i

end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramFlatEmbed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flat_embed_generic (regs : Fin 4 → Bool) (counter mask forward high : List Bool) :
    embedState flatRegs flatStacks (state regs counter mask forward [] counter [] [] [] [] [])
      (SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] high) =
    state (flatOutRegs regs) counter mask forward [] [] [] high [] [] [] := by
  exact embedState_eq_of_ports flatRegs flatStacks
    (state regs counter mask forward [] counter [] [] [] [] [])
    (state (flatOutRegs regs) counter mask forward [] [] [] high [] [] [])
    (SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] high)
    (Fin.castAdd_injective 3 1) flat_stack_injective
    (flat_reg_ports regs) (flat_reg_frame regs)
    (flat_stack_ports counter mask forward high) (flat_stack_frame counter mask forward high)

theorem flat_embed_oai (regs : Fin 4 → Bool) (words : List (List Bool)) (mask forward : List Bool) :
    embedState flatRegs flatStacks (flatInitial regs words mask forward)
      (SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] (words.flatten ++ [])) =
    state (flatOutRegs regs) (ProgramEncoding.encodeRecords words) mask forward [] [] [] words.flatten [] [] [] := by
  have h := flat_embed_generic regs (ProgramEncoding.encodeRecords words) mask forward words.flatten
  have hs : SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] (words.flatten ++ []) =
      SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] words.flatten :=
    congrArg (fun high => SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] high)
      (List.append_nil words.flatten)
  exact (congrArg (embedState flatRegs flatStacks (flatInitial regs words mask forward)) hs).trans h

end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flat_embed_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flat_embed_oai
