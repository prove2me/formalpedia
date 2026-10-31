-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:15:15.013909+00:00
-- url     : https://prove2.me/submissions/21e77e9f-2d01-49d7-a291-17d64a015d32

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S169
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafOuterProgram_stage_bounded_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem dimensionFor_le (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : m ≤ D * 2 ^ r) : dimensionFor m D ≤ r := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_min' (exists_dimension m hD) hr

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

/-- The minimal graph dimension is computed by one division and a binary size,
including the one-vertex case. No unbounded semantic search is needed by the
physical parameter program. -/
theorem dimensionFor_eq_size {m D : ℕ} (hm : 0 < m) (hD : 0 < D) :
    SparseCode.dimensionFor m D = Nat.size ((m-1)/D) := by
  apply Nat.le_antisymm
  · apply SparseCode.dimensionFor_le m hD
    have h := Nat.lt_size_self ((m-1)/D)
    have hh := (Nat.div_lt_iff_lt_mul hD).mp h
    rw [Nat.mul_comm] at hh
    omega
  · apply Nat.size_le.mpr
    apply (Nat.div_lt_iff_lt_mul hD).mpr
    have h := SparseCode.dimensionFor_spec m hD
    rw [Nat.mul_comm]
    omega

theorem dimension_eq_size {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    SparseCode.dimension m B = Nat.size ((m-1)/SparseCode.degree m B) :=
  dimensionFor_eq_size hm (SparseCode.degree_pos hm hB)

/-- A branch-free implementation of binary size using the existing positive
logarithm primitive. -/
theorem size_eq_log2_odd (z : ℕ) : Nat.size z = Nat.log2 (2*z+1) := by
  have ha := LeafParametersProgram.size_eq_log2_add_one (n := 2*z+1) (by omega)
  have hb : Nat.size (2*z+1) = Nat.size z+1 := by
    simpa [Nat.bit, Nat.two_mul] using
      (Nat.size_bit (b := true) (n := z) (by simp [Nat.bit]))
  omega

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

theorem minCommand_eval (r : Regs) (w : Words)
    (h62 : w 62 = []) (h63 : w 63 = []) (h9 : w 9 = []) :
    ∃ t rf word, Eval minCommand t (state r w) (state rf (Function.update w 9 word))  ∧
      BinaryArithmetic.toNat word = min (BinaryArithmetic.toNat (w 0)) (BinaryArithmetic.toNat (w 8))  ∧
      word.length  ≤  (w 0).length+(w 8).length  ∧
      t  ≤  40*((w 0).length+(w 8).length+1) := by
  obtain ⟨r1,h1⟩ := copy_eval r w 0 62 (by decide) h62
  let w1 := Function.update w 62 (w 0)
  obtain ⟨r2,h2⟩ := copy_eval r1 w1 8 63 (by decide) (by simpa [w1] using h63)
  let w2 := Function.update w1 63 (w1 8)
  have hinj : Function.Injective minComparePorts := by decide
  obtain ⟨e,he,hflag,_,hframe,hclear⟩ := SubexpGuardProgram.compare_call id minComparePorts
    Function.injective_id hinj (state r2 w2)
  have ee : e = state e.regs w := by
    apply CounterForPrograms.data_ext (a := e) (b := state e.regs w) rfl
    funext i
    by_cases hi62 : i = port 62
    · subst i
      exact (hclear 0).trans (by simpa only [state_port] using h62.symm)
    by_cases hi63 : i = port 63
    · subst i
      exact (hclear 1).trans (by simpa only [state_port] using h63.symm)
    have hf := hframe i (by
      rintro ⟨j,hj⟩
      fin_cases j
      · exact hi62 hj.symm
      · exact hi63 hj.symm)
    rw [hf]
    have hv62 : i.val ≠ 62 := by intro h; apply hi62; exact Fin.ext h
    have hv63 : i.val ≠ 63 := by intro h; apply hi63; exact Fin.ext h
    simp [state,w2,w1,Function.update_apply,Fin.ext_iff,Fin.coe_ofNat_eq_mod,hv62,hv63]
  have hs0 : (state r2 w2).stacks (minComparePorts 0)=w 0 := by
    change (state r2 w2).stacks (port 62)=_
    rw [state_port]
    simp [w2,w1]
  have hs1 : (state r2 w2).stacks (minComparePorts 1)=w 8 := by
    change (state r2 w2).stacks (port 63)=_
    rw [state_port]
    simp [w2,w1]
  have hcmp : e.regs 0 = true ↔ BinaryArithmetic.toNat (w 0) < BinaryArithmetic.toNat (w 8) := by
    simpa only [hs0,hs1,id_eq] using hflag
  have hem : Eval (.call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program id minComparePorts))
      (10*max (w 0).length (w 8).length+6) (state r2 w2) (state e.regs w) := by
    rw [ee] at he
    simpa only [hs0,hs1] using he
  by_cases hlt : BinaryArithmetic.toNat (w 0) < BinaryArithmetic.toNat (w 8)
  · obtain ⟨rf,hf⟩ := copy_eval e.regs w 0 9 (by decide) h9
    refine ⟨7*(w 0).length+5 + (7*(w1 8).length+5 +
      (10*max (w 0).length (w 8).length+6 + (7*(w 0).length+5+1))),
      rf,w 0,?_,(Nat.min_eq_left hlt.le).symm,by omega,?_⟩
    · exact h1.seq (h2.seq (hem.seq (.ite_true (hcmp.mpr hlt) hf)))
    · simp only [w1,Function.update_of_ne (by decide : (8 : Fin 64)  ≠  62)]
      have hm := max_le (Nat.le_add_right (w 0).length (w 8).length)
        (Nat.le_add_left (w 8).length (w 0).length)
      omega
  · obtain ⟨rf,hf⟩ := copy_eval e.regs w 8 9 (by decide) h9
    refine ⟨7*(w 0).length+5 + (7*(w1 8).length+5 +
      (10*max (w 0).length (w 8).length+6 + (7*(w 8).length+5+1))),
      rf,w 8,?_,(Nat.min_eq_right (by omega)).symm,by omega,?_⟩
    · exact h1.seq (h2.seq (hem.seq (.ite_false (Bool.eq_false_iff.mpr (fun h => hlt (hcmp.mp h))) hf)))
    · simp only [w1,Function.update_of_ne (by decide : (8 : Fin 64)  ≠  62)]
      have hm := max_le (Nat.le_add_right (w 0).length (w 8).length)
        (Nat.le_add_left (w 8).length (w 0).length)
      omega

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank
open LeafParametersProgram.Circuit

theorem prefix_values (m B ml Bl : ℕ) :
    (prefixModel m B ml Bl).val 0=m  ∧
    (prefixModel m B ml Bl).val 5=SparseCode.gapDenom m B  ∧
    (prefixModel m B ml Bl).val 8=SparseCode.degreeBound m B := by
  simp [prefixModel,prefixCode,result,next,output,value,initialModel,BinaryArithmetic.toNat,bitVal,SparseCode.gapDenom,SparseCode.degreeBound,
    SparseCode.logSize,Nat.log2_eq_log_two]
  ; ring_nf ; simp

theorem prefix_admissible (m B ml Bl : ℕ) :
    AdmissibleCode prefixCode (initialModel m B ml Bl) := by
  simp [prefixCode,AdmissibleCode,Admissible,next,output,lengthBound,initialModel]

theorem suffix_admissible {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    AdmissibleCode suffixCode (middleModel m B ml Bl) := by
  have hd := SparseCode.degree_pos hm hB
  simp [suffixCode,AdmissibleCode,Admissible,middleModel,prefixModel,prefixCode,
    result,next,output,value,lengthBound,initialModel,BinaryArithmetic.toNat,bitVal,hB,hd]


theorem final_values {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    (finalModel m B ml Bl).val 5=SparseCode.gapDenom m B  ∧
    (finalModel m B ml Bl).val 9=SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 11=SparseCode.localRows m B  ∧
    (finalModel m B ml Bl).val 12=SparseCode.localRows m B*SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 15=SparseCode.degree m B/(100*B*SparseCode.logSize m)+1  ∧
    (finalModel m B ml Bl).val 18=SparseCode.dimension m B  ∧
    (finalModel m B ml Bl).val 19=SparseCode.dimension m B*SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 21=2^SparseCode.dimension m B := by
  have hr := dimension_eq_size hm hB
  rw [size_eq_log2_odd] at hr
  have hr' : Nat.log 2 (((m-1)/SparseCode.degree m B)+((m-1)/SparseCode.degree m B)+1) =
      SparseCode.dimension m B := by
    simpa [Nat.two_mul,Nat.log2_eq_log_two] using hr.symm
  simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,result,next,output,
    value,initialModel,BinaryArithmetic.toNat,bitVal,SparseCode.gapDenom,SparseCode.localRows,
    SparseCode.logSize,Nat.log2_eq_log_two,Nat.mul_assoc,hr']

/-- The actual binary search words have length linear in the lengths of the
input metadata, independently of their numeric values. -/
theorem final_search_lengths (m B ml Bl : ℕ) :
    (finalModel m B ml Bl).len 5 = ml+Bl+11 ∧
    (finalModel m B ml Bl).len 9 = 4*ml+2*Bl+30 := by
  simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,result,next,
    output,lengthBound,initialModel]
  ; omega

/-- Execute the fixed arithmetic table and the concrete minimum comparator.
All copy, division, logarithm and exponentiation costs are included. -/
theorem command_eval {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (ml Bl : ℕ) (w : Words) (r : Regs) (hw : Shape (initialModel m B ml Bl) w) :
    ∃ t rf w', Eval command t (state r w) (state rf w')  ∧
      Shape (finalModel m B ml Bl) w'  ∧  t ≤ runtimeBound m B ml Bl := by
  obtain ⟨t1,r1,w1,h1,hs1,ht1⟩ := program_eval prefixCode (initialModel m B ml Bl)
    w r hw (prefix_admissible m B ml Bl)
  have hz (i : Fin 64) (hi : (prefixModel m B ml Bl).len i=0) : w1 i=[] := by
    have hh := hs1.2 i
    change (w1 i).length  ≤  (prefixModel m B ml Bl).len i at hh
    rw [hi] at hh
    exact List.length_eq_zero_iff.mp (by omega)
  have hzero (i : Fin 64) (hi : i=9  ∨  i=62  ∨  i=63) :
      (prefixModel m B ml Bl).len i=0 := by
    rcases hi with rfl|rfl|rfl <;>
      simp [prefixModel,prefixCode,result,next,output,lengthBound,initialModel]
  obtain ⟨t2,r2,v2,h2,hv2,hl2,ht2⟩ := minCommand_eval r1 w1
    (hz 62 (hzero _ (by simp))) (hz 63 (hzero _ (by simp))) (hz 9 (hzero _ (by simp)))
  let w2 := Function.update w1 9 v2
  have hs2 : Shape (middleModel m B ml Bl) w2 := by
    constructor
    · intro i
      by_cases hi : i=9
      · subst i
        simp only [w2,Function.update_self,middleModel]
        rw [hv2,hs1.1,hs1.1]
        exact congrArg₂ min (prefix_values m B ml Bl).1 (prefix_values m B ml Bl).2.2
      · simpa [w2,middleModel,prefixModel,hi] using hs1.1 i
    · intro i
      by_cases hi : i=9
      · subst i
        simp only [w2,Function.update_self,middleModel]
        exact hl2.trans (Nat.add_le_add (hs1.2 0) (hs1.2 8))
      · simpa [w2,middleModel,prefixModel,hi] using hs1.2 i
  obtain ⟨t3,r3,w3,h3,hs3,ht3⟩ := program_eval suffixCode (middleModel m B ml Bl)
    w2 r2 hs2 (suffix_admissible hm hB ml Bl)
  refine ⟨t1+(t2+t3),r3,w3,h1.seq (h2.seq h3),hs3,?_⟩
  have ht2' : t2 ≤ 40*((prefixModel m B ml Bl).len 0+(prefixModel m B ml Bl).len 8+1) :=
    ht2.trans (Nat.mul_le_mul_left 40 (by
      have h0 : (w1 0).length ≤ (prefixModel m B ml Bl).len 0 := hs1.2 0
      have h8 : (w1 8).length ≤ (prefixModel m B ml Bl).len 8 := hs1.2 8
      omega))
  exact Nat.add_le_add ht1 (Nat.add_le_add ht2' ht3)

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! Explicit paid binary-to-unary copies for code-search metadata. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

theorem conversionPorts_injective (o : Fin 64) (ho : o ≠ 62) :
    Function.Injective (conversionPorts o) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [conversionPorts,port,work,Fin.ext_iff,Fin.coe_ofNat_eq_mod] <;> omega

theorem unaryCopy_eval (r : Regs) (w : Words) (a o : Fin 64)
    (ha : a ≠ 62) (ho : o ≠ 62) (_hao : a ≠ o) (h62 : w 62=[]) (hout : w o=[]) :
    ∃ t rf, Eval (unaryCopy a o) t (state r w)
        (state rf (Function.update w o (List.replicate (BinaryArithmetic.toNat (w a)) true)))  ∧
      t ≤ 7*(w a).length+6+CounterConversions.coreBound (w a) := by
  obtain ⟨r1,h1⟩ := copy_eval r w a 62 (Ne.symm ha) h62
  let w1 := Function.update w 62 (w a)
  let d := state r1 w1
  let p := conversionPorts o
  have hp : Function.Injective p := conversionPorts_injective o ho
  let localState := projectState smallRegs p d
  have hwork : localState.stacks 2=[] := by
    change (state r1 w1).stacks (work 1 (by decide) 0)=[]
    exact state_work _ _ _ (by decide)
  obtain ⟨u,hu,hub⟩ := CounterConversions.unary_correct localState hwork
  let z := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (BinaryArithmetic.toNat (w a)) true)
  have hlocal : Eval CounterConversions.unaryCmd u localState z := by
    have hs : localState.stacks 0=w a := by
      change (state r1 w1).stacks (port 62)=_
      rw [state_port]
      simp [w1]
    have he : localState.stacks 1=[] := by
      change (state r1 w1).stacks (port o)=_
      rw [state_port]
      simp [w1,ho,hout]
    simpa only [hs,he,List.append_nil,CounterPrograms.value_eq_toNat] using hu
  let e := embedState smallRegs p d z
  have h2 : Eval (conversion o) (u+1) d e :=
    eval_liftCommand_from_state _ _ _ _ _ _ (Fin.castAdd_injective 3 5) hp hlocal
  have es : e = state e.regs (Function.update w o (List.replicate (BinaryArithmetic.toNat (w a)) true)) := by
    apply CounterForPrograms.data_ext (a := e)
      (b := state e.regs (Function.update w o (List.replicate (BinaryArithmetic.toNat (w a)) true))) rfl
    funext i
    by_cases hi62 : i=port 62
    · subst i
      have hh := embedState_stack smallRegs p d z hp 0
      change e.stacks (port 62)=[] at hh
      rw [state_port,Function.update_of_ne (Ne.symm ho)]
      exact hh.trans h62.symm
    by_cases hio : i=port o
    · subst i
      have hh := embedState_stack smallRegs p d z hp 1
      change e.stacks (port o)=List.replicate (BinaryArithmetic.toNat (w a)) true at hh
      simpa only [state_port,Function.update_self] using hh
    by_cases hiw : i=work 1 (by decide) 0
    · subst i
      have hh := embedState_stack smallRegs p d z hp 2
      change e.stacks (work 1 (by decide) 0)=[] at hh
      rw [state_work _ _ _ (by decide)]
      exact hh
    have hf := embedState_stack_frame smallRegs p d z i (by
      rintro ⟨j,hj⟩
      fin_cases j
      · exact hi62 hj.symm
      · exact hio hj.symm
      · exact hiw hj.symm)
    rw [hf]
    have hv62 : i.val ≠ 62 := by
      intro h
      apply hi62
      exact Fin.ext h
    have hvo : i.val ≠ o.val := by
      intro h
      apply hio
      exact Fin.ext h
    simp [d,w1,state,Function.update_apply,Fin.ext_iff,Fin.coe_ofNat_eq_mod,hv62,hvo]
  refine ⟨7*(w a).length+5+(u+1),e.regs,?_,?_⟩
  · rw [← es]
    exact h1.seq h2
  · have hs : localState.stacks 0=w a := by
      change (state r1 w1).stacks (port 62)=_
      rw [state_port]
      simp [w1]
    rw [hs] at hub
    omega

theorem unaryCommand_eval (r : Regs) (w : Words) (h62 : w 62=[])
    (h24 : w 24=[]) (h25 : w 25=[]) (h26 : w 26=[]) (h27 : w 27=[])
    (h28 : w 28=[]) (h29 : w 29=[]) (h30 : w 30=[]) :
    ∃ t rf, Eval unaryCommand t (state r w) (state rf (unaryWords w))  ∧  t ≤ unaryBudget w := by
  obtain ⟨t1,r1,he1,ht1⟩ := unaryCopy_eval r w 9 24
    (by decide) (by decide) (by decide) (by exact h62) (by exact h24)
  let w1 := Function.update w 24 (List.replicate (BinaryArithmetic.toNat (w 9)) true)
  obtain ⟨t2,r2,he2,ht2⟩ := unaryCopy_eval r1 w1 11 25
    (by decide) (by decide) (by decide) (by simpa [w1] using h62) (by simpa [w1] using h25)
  let w2 := Function.update w1 25 (List.replicate (BinaryArithmetic.toNat (w1 11)) true)
  obtain ⟨t3,r3,he3,ht3⟩ := unaryCopy_eval r2 w2 12 26
    (by decide) (by decide) (by decide) (by simpa [w1,w2] using h62) (by simpa [w1,w2] using h26)
  let w3 := Function.update w2 26 (List.replicate (BinaryArithmetic.toNat (w2 12)) true)
  obtain ⟨t4,r4,he4,ht4⟩ := unaryCopy_eval r3 w3 15 27
    (by decide) (by decide) (by decide) (by simpa [w1,w2,w3] using h62) (by simpa [w1,w2,w3] using h27)
  let w4 := Function.update w3 27 (List.replicate (BinaryArithmetic.toNat (w3 15)) true)
  obtain ⟨t5,r5,he5,ht5⟩ := unaryCopy_eval r4 w4 18 28
    (by decide) (by decide) (by decide) (by simpa [w1,w2,w3,w4] using h62) (by simpa [w1,w2,w3,w4] using h28)
  let w5 := Function.update w4 28 (List.replicate (BinaryArithmetic.toNat (w4 18)) true)
  obtain ⟨t6,r6,he6,ht6⟩ := unaryCopy_eval r5 w5 19 29
    (by decide) (by decide) (by decide) (by simpa [w1,w2,w3,w4,w5] using h62) (by simpa [w1,w2,w3,w4,w5] using h29)
  let w6 := Function.update w5 29 (List.replicate (BinaryArithmetic.toNat (w5 19)) true)
  obtain ⟨t7,r7,he7,ht7⟩ := unaryCopy_eval r6 w6 21 30
    (by decide) (by decide) (by decide) (by simpa [w1,w2,w3,w4,w5,w6] using h62) (by simpa [w1,w2,w3,w4,w5,w6] using h30)
  let w7 := Function.update w6 30 (List.replicate (BinaryArithmetic.toNat (w6 21)) true)
  refine ⟨t1+(t2+(t3+(t4+(t5+(t6+t7))))),r7,?_,?_⟩
  · have he := he1.seq (he2.seq (he3.seq (he4.seq (he5.seq (he6.seq he7)))))
    simpa [unaryCommand,unaryWords,unaryPairs,w1,w2,w3,w4,w5,w6,w7] using he
  · simp [w1,w2,w3,w4,w5,w6] at ht1 ht2 ht3 ht4 ht5 ht6 ht7
    simp only [unaryBudget,unaryPairs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega

theorem unaryBudget_le (z : LeafParametersProgram.Circuit.Model) (w : Words)
    (hs : LeafParametersProgram.Circuit.Shape z w) : unaryBudget w ≤ unaryModelBudget z := by
  have hb (a : Fin 64) : 7*(w a).length+6+CounterConversions.coreBound (w a)  ≤
      7*z.len a+6+(2*z.val a+(z.val a+1)*(16*z.len a+16)+2*z.len a+6) := by
    simp only [CounterConversions.coreBound,CounterPrograms.value_eq_toNat,hs.1]
    gcongr <;> exact hs.2 a
  have h9 := hb 9
  have h11 := hb 11
  have h12 := hb 12
  have h15 := hb 15
  have h18 := hb 18
  have h19 := hb 19
  have h21 := hb 21
  simp only [unaryBudget,unaryModelBudget,unaryPairs,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  omega

theorem fullCommand_eval_with_lengths {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (r : Regs) (w : Words) (hs : LeafParametersProgram.Circuit.Shape (initialModel m B ml Bl) w) :
    ∃ t rf w', Eval fullCommand t (state r w) (state rf w')  ∧  t ≤ fullBudget m B ml Bl  ∧
      BinaryArithmetic.toNat (w' 0)=m  ∧  BinaryArithmetic.toNat (w' 5)=SparseCode.gapDenom m B  ∧
      (∀ j, BinaryArithmetic.toNat (w' (binaryPorts j))=parameterValues m B j)  ∧
      (∀ j, w' (unaryPorts j)=List.replicate (parameterValues m B j) true) ∧
      (w' 5).length ≤ ml+Bl+11 ∧ (w' 9).length ≤ 4*ml+2*Bl+30 := by
  obtain ⟨t1,r1,w1,h1,hs1,ht1⟩ := command_eval hm hB ml Bl w r hs
  have hz (i : Fin 64) (hi : i=62  ∨  (24 ≤ i.val  ∧  i.val ≤ 30)) : w1 i=[] := by
    have hlen : (finalModel m B ml Bl).len i=0 := by
      rcases hi with rfl|hi
      · simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,
          LeafParametersProgram.Circuit.result,LeafParametersProgram.Circuit.next,
          LeafParametersProgram.Circuit.output,LeafParametersProgram.Circuit.lengthBound,initialModel]
      · have hi' : i=24  ∨  i=25  ∨  i=26  ∨  i=27  ∨  i=28  ∨  i=29  ∨  i=30 := by omega
        rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,
            LeafParametersProgram.Circuit.result,LeafParametersProgram.Circuit.next,
            LeafParametersProgram.Circuit.output,LeafParametersProgram.Circuit.lengthBound,initialModel]
    have hh:=hs1.2 i
    rw [hlen] at hh
    exact List.length_eq_zero_iff.mp (by omega)
  obtain ⟨t2,r2,h2,ht2⟩ := unaryCommand_eval r1 w1 (hz 62 (by simp))
    (hz 24 (by decide)) (hz 25 (by decide)) (hz 26 (by decide)) (hz 27 (by decide))
    (hz 28 (by decide)) (hz 29 (by decide)) (hz 30 (by decide))
  have hv:=final_values hm hB ml Bl
  have hp (j : Fin 7) : BinaryArithmetic.toNat (w1 (binaryPorts j))=parameterValues m B j := by
    rw [hs1.1]
    fin_cases j
    · exact hv.2.1
    · exact hv.2.2.1
    · exact hv.2.2.2.1
    · exact hv.2.2.2.2.1
    · exact hv.2.2.2.2.2.1
    · exact hv.2.2.2.2.2.2.1
    · exact hv.2.2.2.2.2.2.2
  refine ⟨t1+t2,r2,unaryWords w1,h1.seq h2,
    Nat.add_le_add ht1 (ht2.trans (unaryBudget_le _ _ hs1)),?_,?_,?_,?_,?_,?_⟩
  · have hm0 : (finalModel m B ml Bl).val 0=m := by
      simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,
        LeafParametersProgram.Circuit.result,LeafParametersProgram.Circuit.next,
        LeafParametersProgram.Circuit.output,initialModel]
    simpa [unaryWords,unaryPairs] using (hs1.1 0).trans hm0
  · simpa [unaryWords,unaryPairs] using (hs1.1 5).trans hv.1
  · intro j
    have hf : unaryWords w1 (binaryPorts j)=w1 (binaryPorts j) := by
      fin_cases j <;> simp [unaryWords,unaryPairs,binaryPorts]
    rw [hf]
    exact hp j
  · intro j
    have hf : unaryWords w1 (unaryPorts j)=List.replicate (BinaryArithmetic.toNat (w1 (binaryPorts j))) true := by
      fin_cases j <;> simp [unaryWords,unaryPairs,binaryPorts,unaryPorts]
    rw [hf,hp j]
  · have hh := hs1.2 5
    rw [(final_search_lengths m B ml Bl).1] at hh
    simpa [unaryWords,unaryPairs] using hh
  · have hh := hs1.2 9
    rw [(final_search_lengths m B ml Bl).2] at hh
    simpa [unaryWords,unaryPairs] using hh

theorem program_runs_with_lengths {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (r : Regs) (w : Words) (hs : LeafParametersProgram.Circuit.Shape (initialModel m B ml Bl) w) :
    ∃ rf w', RunsIn program (fullBudget m B ml Bl+1)
      ((state r w).withPC (some program.entry)) ((state rf w').withPC none) ∧
      BinaryArithmetic.toNat (w' 0)=m ∧ BinaryArithmetic.toNat (w' 5)=SparseCode.gapDenom m B ∧
      (∀ j, BinaryArithmetic.toNat (w' (binaryPorts j))=parameterValues m B j) ∧
      (∀ j, w' (unaryPorts j)=List.replicate (parameterValues m B j) true) ∧
      (w' 5).length ≤ ml+Bl+11 ∧ (w' 9).length ≤ 4*ml+2*Bl+30 := by
  obtain ⟨t,rf,w',he,ht,hm0,hq,hbin,hunary,hql,hDl⟩ :=
    fullCommand_eval_with_lengths hm hB ml Bl r w hs
  exact ⟨rf,w',⟨t+1,by omega,compiled_halt_trace he 0 30⟩,hm0,hq,hbin,hunary,hql,hDl⟩

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

theorem clearWorker_stack (a : Data) (i : Fin 768) :
    (workerCleared a).stacks (workerStack i) = [] :=
  embedState_stack id workerStack a LeafProgram.Cleanup.Wide.blank
    (Fin.castAdd_injective 768 128) i

theorem clearWorker_frame (a : Data) (i : Fin 896) (hi : 768 ≤ i.val) :
    (workerCleared a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp only [workerStack,Fin.val_castAdd] at hv
  omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared fixed port maps and the paid native code-parameter stage. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls


theorem parameterInputs_valid : ∀ p ∈ parameterInputs, routeValid p := by
  intro p hp
  simp only [parameterInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  all_goals unfold routeValid; decide
theorem parameterOutputs_valid : ∀ p ∈ parameterOutputs, routeValid p := by
  intro p hp
  simp only [parameterOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold routeValid; decide

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupBoundSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured bounds for composition of the concrete setup phases

The predicates below retain actual executions. Polynomial coefficients and
degrees are chosen before the input size and the incoming machine state.
-/

namespace SubexponentialSAT.SubexpSetupBoundSpec

open BitProgram StructuredCalls SubexpSetupStorage Filter

theorem wordBound_mono {r s B C : ℕ} {a : State r s}
    (ha : WordBound B a) (hBC : B ≤ C) : WordBound C a :=
  fun i => (ha i).trans hBC

/-- A fixed stack gains at most one bit per actual instruction. -/
theorem eval_wordBound {r s B t : ℕ} {cmd : Cmd r s} {a b : State r s}
    (ha : WordBound B a) (he : Eval cmd t a b) : WordBound (B + t) b := by
  intro i
  have hg := BitProgram.trace_selectedStackBits (compiled cmd i i) {i}
    (compiled_trace he i i)
  have hi : (b.stacks i).length ≤ (a.stacks i).length + t := by
    simpa only [BitProgram.selectedStackBits, Finset.sum_singleton,
      StructuredProgram.State.withPC] using hg
  exact hi.trans (Nat.add_le_add_right (ha i) t)

end SubexponentialSAT.SubexpSetupBoundSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact composition and memory charging for fixed outer-leaf stages. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexpSetupStorage

theorem stageResult_empty {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (i : Fin 768) :
    (stageResult inputs outputs register stack a out).stacks (workerStack i) = [] :=
  clearWorker_stack _ i

theorem stageResult_frame {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (i : Fin 896) (hi : 768 ≤ i.val)
    (hinput : ∀ q ∈ inputs, q.2 ≠ i) (houtput : ∀ q ∈ outputs, q.2 ≠ i)
    (hstack : ∀ j, stack j ≠ i) :
    (stageResult inputs outputs register stack a out).stacks i = a.stacks i := by
  rw [stageResult,clearWorker_frame _ i hi,stageSaved,routes_frame _ _ _ houtput,
    stageReturned,embedState_stack_frame register stack (routesState inputs a) out i
      (by rintro ⟨j,hj⟩; exact hstack j hj),routes_frame _ _ _ hinput]

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer-leaf parameter stage: input copies, native arithmetic,
output copies, and complete worker cleanup, with every command charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank

private theorem input_projection (a : Data) (he : WorkerEmpty a) :
    projectState regs8 stacks77 (routesState parameterInputs a) =
      state ((projectState regs8 stacks77 (routesState parameterInputs a)).regs) (inputWords a) := by
  apply CounterForPrograms.data_ext
    (a := projectState regs8 stacks77 (routesState parameterInputs a))
    (b := state ((projectState regs8 stacks77 (routesState parameterInputs a)).regs) (inputWords a)) rfl
  funext i
  have hemp : a.stacks (stacks77 i) = [] := he ⟨i.val, by omega⟩
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    simp [projectState,parameterInputs,routesState,routed,stacks77,state,inputWords]
  by_cases h1 : i.val=1
  · have hi : i=1 := Fin.ext h1
    subst i
    simp [projectState,parameterInputs,routesState,routed,stacks77,state,inputWords]
  have hn0 : stacks77 i ≠ 0 := by intro h; apply h0; exact congrArg Fin.val h
  have hn1 : stacks77 i ≠ 1 := by intro h; apply h1; exact congrArg Fin.val h
  change (routesState parameterInputs a).stacks (stacks77 i) = _
  rw [routes_frame parameterInputs a (stacks77 i) (by
    intro p hp
    simp only [parameterInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact Ne.symm hn0
    · exact Ne.symm hn1)]
  rw [hemp]
  by_cases h64 : i.val < 64
  · have hz : (⟨i.val,h64⟩ : Fin 64) ≠ 0 := by
      intro h; apply h0; exact congrArg Fin.val h
    have ho : (⟨i.val,h64⟩ : Fin 64) ≠ 1 := by
      intro h; apply h1; exact congrArg Fin.val h
    simp only [state,dite_eq_left h64,inputWords,ite_eq_right hz,ite_eq_right ho]
  · simp only [state,dite_eq_right h64]

private theorem input_shape (a : Data) {m B : ℕ}
    (hm : BinaryArithmetic.toNat (a.stacks 782)=m) (hB : BinaryArithmetic.toNat (a.stacks 786)=B) :
    LeafParametersProgram.Circuit.Shape
      (CodeParametersProgram.initialModel m B (a.stacks 782).length (a.stacks 786).length)
      (inputWords a) := by
  constructor <;> intro i <;> by_cases h0 : i=0 <;> by_cases h1 : i=1 <;>
    simp [inputWords,CodeParametersProgram.initialModel,h0,h1,hm,hB]

private theorem saved_parameter (a : Data) (out : State 8 77) (p : Route)
    (hp : p ∈ parameterOutputs) :
    (routesState parameterOutputs (stageReturned parameterInputs regs8 stacks77 a out)).stacks p.2 =
      (stageReturned parameterInputs regs8 stacks77 a out).stacks p.1 := by
  simp only [parameterOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [parameterOutputs,routesState,routed]

private theorem result_parameter (a : Data) (r : Regs) (w : Words)
    (src : Fin 64) (dst : Fin 896) (hdst : 768 ≤ dst.val)
    (hp : (stacks77 (port src),dst) ∈ parameterOutputs) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state r w)).stacks dst = w src := by
  rw [stageResult,clearWorker_frame _ dst hdst]
  change (routesState parameterOutputs (stageReturned parameterInputs regs8 stacks77 a (state r w))).stacks dst = _
  rw [saved_parameter a (state r w) _ hp]
  exact (embedState_stack regs8 stacks77 (routesState parameterInputs a) (state r w)
    (Fin.castAdd_injective 77 819) (port src)).trans (state_port r w src)

private theorem result_q (a : Data) (r : Regs) (w : Words) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state r w)).stacks 800 = w 5 :=
  result_parameter a r w 5 800 (by decide) (by decide)

private theorem result_binary (a : Data) (r : Regs) (w : Words) (j : Fin 7) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state r w)).stacks
      (binaryMetadataPort j) = w (CodeParametersProgram.binaryPorts j) := by
  apply result_parameter a r w (CodeParametersProgram.binaryPorts j) (binaryMetadataPort j)
  · simp only [binaryMetadataPort]; omega
  · fin_cases j <;> decide

private theorem result_unary (a : Data) (r : Regs) (w : Words) (j : Fin 7) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state r w)).stacks
      (unaryMetadataPort j) = w (CodeParametersProgram.unaryPorts j) := by
  apply result_parameter a r w (CodeParametersProgram.unaryPorts j) (unaryMetadataPort j)
  · simp only [unaryMetadataPort]; omega
  · fin_cases j <;> decide

private theorem result_frame (a : Data) (out : State 8 77) (i : Fin 896)
    (hi : 768 ≤ i.val) (hout : i.val < 800 ∨ 814 < i.val) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a out).stacks i = a.stacks i := by
  apply stageResult_frame _ _ _ _ _ _ i hi
  · intro p hp
    simp only [parameterInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> intro h <;> have := congrArg Fin.val h <;> simp at this <;> omega
  · intro p hp
    have hb : 800 ≤ p.2.val ∧ p.2.val ≤ 814 := by
      simp only [parameterOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    intro h
    have hv := congrArg Fin.val h
    omega
  · intro j h
    have hv := congrArg Fin.val h
    simp only [stacks77,Fin.val_castAdd] at hv
    omega

/-- Native parameter preparation on the actual outer-leaf machine. Its bound
includes input copies, arithmetic and unary generation, output copies, and
clearing every worker stack and register. No prepared-metadata premise occurs. -/
theorem parameters_eval (a : Data) {m B L : ℕ} (hm : 0 < m) (hB : 0 < B)
    (he : WorkerEmpty a) (hmv : BinaryArithmetic.toNat (a.stacks 782)=m) (hBv : BinaryArithmetic.toNat (a.stacks 786)=B)
    (hL : SubexpSetupStorage.WordBound L a) :
    ∃ n ≤ 10000*(L+CodeParametersProgram.fullBudget m B
      (a.stacks 782).length (a.stacks 786).length+2), ∃ b,
      Eval parameters n a b ∧ WorkerEmpty b ∧ (∀ i, b.regs i=false) ∧ Metadata m B b ∧
      (b.stacks 800).length ≤ (a.stacks 782).length+(a.stacks 786).length+11 ∧
      (b.stacks 801).length ≤ 4*(a.stacks 782).length+2*(a.stacks 786).length+30 ∧
      (∀ i : Fin 896, 768 ≤ i.val → (i.val < 800 ∨ 814 < i.val) → b.stacks i=a.stacks i) := by
  let r := (projectState regs8 stacks77 (routesState parameterInputs a)).regs
  obtain ⟨rf,w,hrun,_,hq,hbin,hun,hql,hDl⟩ :=
    CodeParametersProgram.program_runs_with_lengths hm hB
      (a.stacks 782).length (a.stacks 786).length r (inputWords a) (input_shape a hmv hBv)
  have hrun' : RunsIn CodeParametersProgram.program
      (CodeParametersProgram.fullBudget m B (a.stacks 782).length (a.stacks 786).length+1)
      ((projectState regs8 stacks77 (routesState parameterInputs a)).withPC
        (some CodeParametersProgram.program.entry)) ((state rf w).withPC none) := by
    rw [input_projection a he]
    exact hrun
  have ht : a.stacks 767=[] := he 767
  obtain ⟨n,hn,hnative⟩ := stage_bounded_eval parameterInputs parameterOutputs
    CodeParametersProgram.program regs8 stacks77 (Fin.castAdd_injective 8 32)
    (Fin.castAdd_injective 77 819) (by
      intro i h
      have hv := congrArg Fin.val h
      simp only [stacks77,Fin.val_castAdd] at hv
      have := i.isLt
      omega)
    parameterInputs_valid parameterOutputs_valid (by decide) (by decide)
    a L hL ht (state rf w) _ hrun'
  refine ⟨n,by omega,stageResult parameterInputs parameterOutputs regs8 stacks77 a (state rf w),
    hnative,?_,?_,?_,?_,?_,?_⟩
  · exact stageResult_empty _ _ _ _ _ _
  · intro i
    exact embedState_register id workerStack _ LeafProgram.Cleanup.Wide.blank Function.injective_id i
  · constructor
    · simpa only [result_q] using hq
    · intro j; simpa only [result_binary] using hbin j
    · intro j; simpa only [result_unary] using hun j
  · simpa only [result_q] using hql
  · have h := result_binary a rf w 0
    change (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state rf w)).stacks 801 = w 9 at h
    rw [h]
    exact hDl
  · exact result_frame a (state rf w)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual sparse-code metadata production, with paid polynomial time and every-prefix word bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- Actual metadata production preserves all saved high words outside its
fifteen output ports. In particular 768,780,781,783 and817 are preserved. -/
theorem parameters_trace_space_oai (a : Data) {m B W : ℕ} (hm : 0 < m) (hB : 0 < B)
    (he : WorkerEmpty a) (hmv : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hBv : BinaryArithmetic.toNat (a.stacks 786) = B)
    (hW : ∀ i, (a.stacks i).length ≤ W) :
    ∃ steps b, steps ≤ parameterTime m B W (a.stacks 782).length (a.stacks 786).length ∧
      Eval parameters steps a b ∧ WorkerEmpty b ∧ (∀ i, b.regs i = false) ∧
      Metadata m B b ∧
      (b.stacks 800).length ≤ (a.stacks 782).length + (a.stacks 786).length + 11 ∧
      (b.stacks 801).length ≤ 4 * (a.stacks 782).length + 2 * (a.stacks 786).length + 30 ∧
      (∀ i : Fin 896, 768 ≤ i.val → (i.val < 800 ∨ 814 < i.val) →
        b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤
        W + parameterTime m B W (a.stacks 782).length (a.stacks 786).length) ∧
      Trace (compiled parameters 784 788) (steps + 1)
        (a.withPC (some (compiled parameters 784 788).entry)) (b.withPC none) ∧
      ∀ k c, k ≤ steps + 1 → Trace (compiled parameters 784 788) k
        (a.withPC (some (compiled parameters 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          W + parameterTime m B W (a.stacks 782).length (a.stacks 786).length + 1 := by
  obtain ⟨steps, ht, b, hrun, hempty, hregs, hmeta, hq, hD, hf⟩ :=
    parameters_eval a hm hB he hmv hBv hW
  change steps ≤ parameterTime m B W (a.stacks 782).length (a.stacks 786).length at ht
  refine ⟨steps, b, ht, hrun, hempty, hregs, hmeta, hq, hD, hf, ?_,
    compiled_halt_trace hrun 784 788, ?_⟩
  · exact SubexpSetupBoundSpec.wordBound_mono
      (SubexpSetupBoundSpec.eval_wordBound hW hrun) (Nat.add_le_add_left ht W)
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (a.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hW i
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space_oai
