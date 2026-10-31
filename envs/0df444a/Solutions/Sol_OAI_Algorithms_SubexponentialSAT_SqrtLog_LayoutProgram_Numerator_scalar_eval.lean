-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:24:02.36998+00:00
-- url     : https://prove2.me/submissions/77540e9e-4a55-4612-9cee-849042d79af1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_FromCounts_program_runsIn

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for one universal integer constraint entry. The concrete
local stages are lifted into one bank; subsequent lemmas compose their traces.
No ring inversion or field-valued matrix is used in this integer procedure. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.MulticolorTypes

theorem scalarRegs_inj : Function.Injective scalarRegs := Fin.castAdd_injective _ _
theorem scalarPorts_inj : Function.Injective scalarPorts := by decide

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete universal numerator evaluation from encoded type words and the
paid unsigned coefficient cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

theorem scalar_project (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) (uc hc : List Bool) :
    projectState scalarRegs scalarPorts (state c regs t u y uc hc ([],[])) =
      LayoutProgramScalar.FromCounts.state c (regs ∘ scalarRegs) uc hc [] [] [] [] [] ([],[]) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  fin_cases j <;> simp [scalarPorts,state,baseStacks,Guard.guardInput,
    Scan.scanInput,MatrixEntryProgram.input]

theorem scalar_embed (c : Saved) (regs : Fin 10 → Bool) (rr : Fin 9 → Bool)
    (t : Fin Q) (u y : UniversalType r Q 1) (uc hc : List Bool) (result : WordPair) :
    let start := state c regs t u y uc hc ([],[])
    let out := LayoutProgramScalar.FromCounts.state c rr [] [] [] [] [] [] [] result
    let e := embedState scalarRegs scalarPorts start out
    e = state c e.regs t u y [] [] result := by
  intro start out e
  apply embedState_eq_of_ports scalarRegs scalarPorts _ _ _ scalarRegs_inj scalarPorts_inj
  · intro j; exact embedState_register scalarRegs scalarPorts start out scalarRegs_inj j
  · intro j hj; exact embedState_register_frame scalarRegs scalarPorts start out j hj
  · intro j
    fin_cases j <;> simp [out,state,baseStacks,scalarPorts,Guard.guardInput,Scan.scanInput,
      MatrixEntryProgram.input,LayoutProgramScalar.FromCounts.state]
  · intro j hj
    have h2 : j ≠ 2 := by
      intro h; exact hj ⟨7,(show scalarPorts 7=2 by decide).trans h.symm⟩
    have h3 : j ≠ 3 := by
      intro h; exact hj ⟨8,(show scalarPorts 8=3 by decide).trans h.symm⟩
    have h50 : j ≠ 50 := by
      intro h; exact hj ⟨37,(show scalarPorts 37=50 by decide).trans h.symm⟩
    have h51 : j ≠ 51 := by
      intro h; exact hj ⟨38,(show scalarPorts 38=51 by decide).trans h.symm⟩
    simp [start,state,h2,h3,h50,h51]

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumeratorScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
variable {r Q : ℕ}

theorem scalar_eval_oai (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 10 → Bool) (a : List Bool) (R d : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1) (h : List Bool)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : h.length+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) (hhQ : h.length ≤ Q) :
    let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
    ∃ n ≤ LayoutProgramScalar.FromCounts.totalCost a.length R d h.length width.length (pairLength power),
      ∃ rf result, Eval scalar n (state c regs t u y (List.replicate (d+1) true) h ([],[]))
        (state c rf t u y [] [] result) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum a.length R d h.length ∧
      LayoutProgramScalar.wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*LayoutProgramScalar.termGrowth (2*width.length+pairLength power) := by
  intro c
  obtain ⟨rr,result,⟨n,hn,he⟩,hv,hm,hl⟩ := LayoutProgramScalar.FromCounts.program_runsIn
    Hwords width power (regs ∘ scalarRegs) a h R d Q hlen hwords hvalues hp hpt hwidth hAQ hQ hhQ
  let start := state c regs t u y (List.replicate (d+1) true) h ([],[])
  have hh := eval_call_from_state LayoutProgramScalar.FromCounts.program scalarRegs scalarPorts start
    scalarRegs_inj scalarPorts_inj (by rw [scalar_project]; exact he)
  rw [scalar_embed] at hh
  exact ⟨n,hn,_,result,hh,hv,hm,hl⟩


end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval_oai
