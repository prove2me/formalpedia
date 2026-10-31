-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:26:28.984905+00:00
-- url     : https://prove2.me/submissions/a0a10687-bb94-4280-b18f-9a7295ac8edb

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_Numerator_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_TypeCompare_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_UniversalEntry_guard_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramDefect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical clearing-defect entries from the actual signed numerator pair.
A diagonal entry is D−(P−N), an off-diagonal entry is −(P−N). The numerator
and cached denominator remain intact; the result is a fresh signed pair.
The diagonal flag is a runtime bit, supplied by the type equality scan. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Defect

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem command_eval (d : Data) (hd : Ready d) :
    ∃ t ≤ budget d, ∃ rf pos neg,
      Eval command t d ⟨rf,output d pos neg⟩ ∧
      (BinaryArithmetic.toNat pos : ℤ) - BinaryArithmetic.toNat neg =
        (if d.regs 7 then (BinaryArithmetic.toNat (d.stacks 2) : ℤ) else 0) -
          ((BinaryArithmetic.toNat (d.stacks 0) : ℤ)-BinaryArithmetic.toNat (d.stacks 1)) ∧
      BinaryArithmetic.toNat pos + BinaryArithmetic.toNat neg = BinaryArithmetic.toNat (d.stacks 0)+BinaryArithmetic.toNat (d.stacks 1)+
        (if d.regs 7 then BinaryArithmetic.toNat (d.stacks 2) else 0) ∧
      pos.length+neg.length ≤
        (d.stacks 0).length+(d.stacks 1).length+(d.stacks 2).length+1 := by
  let mid := SubexponentialSAT.ArithmeticCalls.afterCopy 0 4 d
  have hc := SubexponentialSAT.ArithmeticCalls.copyAt_eval 0 4 5 d
    (by decide) (by decide) (by decide) (hd 4 (by decide)) (hd 5 (by decide))
  have hm7 : mid.regs 7 = d.regs 7 := by simp [mid,SubexponentialSAT.ArithmeticCalls.afterCopy,readRegs]
  cases hg : d.regs 7 with
  | false =>
    have hp := SubexponentialSAT.ArithmeticCalls.copyAt_eval 1 3 5 mid
      (by decide) (by decide) (by decide)
      (by simpa [mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hd 3 (by decide))
      (by simpa [mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hd 5 (by decide))
    have he := hc.seq (Eval.ite_false (yes := SubexponentialSAT.ArithmeticCalls.addAt addPorts) (hm7.trans hg) hp)
    refine ⟨7*(d.stacks 0).length+5+(7*(mid.stacks 1).length+5+1),?_,
      (SubexponentialSAT.ArithmeticCalls.afterCopy 1 3 mid).regs,d.stacks 1,d.stacks 0,?_,?_,?_,?_⟩
    · simp only [mid,SubexponentialSAT.ArithmeticCalls.afterCopy,Function.update_of_ne (by decide : (1:Fin 10) ≠ 4),budget]
      nlinarith [Nat.zero_le (d.stacks 1).length, Nat.zero_le (d.stacks 2).length,
        sq_nonneg ((d.stacks 1).length+(d.stacks 2).length : ℤ)]
    · simpa [command,mid,SubexponentialSAT.ArithmeticCalls.afterCopy,output] using he
    · simp []
    · simp [Nat.add_comm]
    · omega
  | true =>
    have hv : SubexponentialSAT.ArithmeticCalls.Valid addPorts mid := by
      constructor
      · simpa [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hd 3 (by decide)
      · intro j
        fin_cases j <;> simp [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] <;> apply hd <;> decide
    obtain ⟨ta,rf,pos,ha,hval,hlen,htime⟩ := SubexponentialSAT.ArithmeticCalls.addAt_eval addPorts mid hv
    have hval' : BinaryArithmetic.toNat pos = BinaryArithmetic.toNat (d.stacks 1)+BinaryArithmetic.toNat (d.stacks 2) := by
      simpa [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hval
    have hlen' : pos.length ≤ (d.stacks 1).length+(d.stacks 2).length+1 := by
      simpa [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using hlen
    have ht' : ta ≤ 100*((d.stacks 1).length+(d.stacks 2).length+1)^2 := by
      simpa [addPorts,mid,SubexponentialSAT.ArithmeticCalls.afterCopy] using htime
    have he := hc.seq (Eval.ite_true (no := SubexponentialSAT.ArithmeticCalls.copyAt 1 3 5) (hm7.trans hg) ha)
    refine ⟨7*(d.stacks 0).length+5+(ta+1),by unfold budget; omega,
      rf,pos,d.stacks 0,?_,?_,?_,by omega⟩
    · simpa [command,mid,SubexponentialSAT.ArithmeticCalls.afterCopy,output,addPorts] using he
    · simp only [ite_true, if_true,hval',Nat.cast_add]
      ring
    · simp only [ite_true, if_true,hval']
      omega

end SubexponentialSAT.SqrtLog.LayoutProgram.Defect

end OAI.Algorithms
end

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

theorem smallRegs_inj : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem defectPorts_inj : Function.Injective defectPorts := by decide

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final physical defect conversion, preserving all caller inputs and
removing the temporary numerator pair. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp RowSelectionProgram
open UniversalEntry

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem command_eval (a : Data) (ha : Ready a) :
    ∃ t ≤ budget a, ∃ e p n, Eval command t a e ∧ e.stacks=output a p n ∧
      (BinaryArithmetic.toNat p : ℤ)-BinaryArithmetic.toNat n =
        (if a.regs 7 then (BinaryArithmetic.toNat (a.stacks 45):ℤ) else 0)-
          ((BinaryArithmetic.toNat (a.stacks 50):ℤ)-BinaryArithmetic.toNat (a.stacks 51)) ∧
      BinaryArithmetic.toNat p+BinaryArithmetic.toNat n=
        BinaryArithmetic.toNat (a.stacks 50)+BinaryArithmetic.toNat (a.stacks 51)+
          (if a.regs 7 then BinaryArithmetic.toNat (a.stacks 45) else 0) ∧
      p.length+n.length ≤ (a.stacks 50).length+(a.stacks 51).length+(a.stacks 45).length+1 := by
  let d := projectState smallRegs defectPorts a
  have hd : Defect.Ready d := by
    intro j hj
    fin_cases j <;> simp_all [d,projectState,defectPorts,Ready]
  obtain ⟨nd,hnd,rd,p,n,hdone,hvalue,hmass,hlen⟩ := Defect.command_eval d hd
  let m := embedState smallRegs defectPorts a ⟨rd,Defect.output d p n⟩
  have he := eval_liftCommand_from_state Defect.command 0 3 smallRegs defectPorts a
    smallRegs_inj defectPorts_inj hdone
  have hms : m.stacks=Function.update (Function.update a.stacks 54 n) 53 p := by
    change Function.extend defectPorts (Defect.output d p n) a.stacks = _
    unfold Defect.output
    rw [ProgramLinking.extend_update defectPorts_inj,ProgramLinking.extend_update defectPorts_inj]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs defectPorts a smallRegs_inj defectPorts_inj)
    change Function.extend defectPorts d.stacks a.stacks=a.stacks at hb
    rw [hb]
    rfl
  let s₁ : Data := ⟨readRegs m.regs 0 1 none,StackRoutines.clearStacks 50 m.stacks⟩
  let e : Data := ⟨readRegs s₁.regs 0 1 none,StackRoutines.clearStacks 51 s₁.stacks⟩
  have h₁ := Subexp.TupleProgram.clear_eval 50 0 1 m
  have h₂ := Subexp.TupleProgram.clear_eval 51 0 1 s₁
  have hout : e.stacks=output a p n := by
    funext j
    by_cases h50 : j=50 <;> by_cases h51 : j=51 <;> by_cases h53 : j=53 <;>
      by_cases h54 : j=54 <;> simp_all [e,s₁,StackRoutines.clearStacks,output]
  have hrun : Eval command ((nd+1)+(2*(m.stacks 50).length+3+(2*(s₁.stacks 51).length+3))) a e :=
    he.seq (h₁.seq h₂)
  refine ⟨_,?_,e,p,n,hrun,hout,?_,?_,?_⟩
  · simp [d,projectState,defectPorts,Defect.budget] at hnd
    simp [budget,s₁,StackRoutines.clearStacks,hms]
    omega
  · simpa [d,projectState,defectPorts,smallRegs] using hvalue
  · simpa [d,projectState,defectPorts,smallRegs] using hmass
  · simpa [d,projectState,defectPorts] using hlen

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish

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

theorem guard_project (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) :
    projectState id guardPorts (state c regs t u y [] [] ([],[])) =
      Guard.guardInput (0 : Fin 1) t u y [] [] [] [] regs := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  fin_cases j <;> simp [guardPorts,state,baseStacks,Guard.guardInput,
    Scan.scanInput,MatrixEntryProgram.input]

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal integer universal constraints from the actual numerator program.
The outer anchor test also suppresses the clearing diagonal outside the joint. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

theorem output_empty (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q) (u y : UniversalType r Q 1) :
    output c regs t u y ([],[]) = Numerator.state c regs t u y [] [] ([],[]) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  by_cases h53 : j=53 <;> by_cases h54 : j=54 <;>
    simp [Numerator.state,Numerator.baseStacks,Function.update_apply,h53,h54]

theorem command_eval_oai (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 10 → Bool) (a : List Bool) (R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) :
    let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
    ∃ n ≤ budget a.length R width.length (pairLength power) power.1.length t u y,
      ∃ rf result, Eval command n (Numerator.state c regs t u y [] [] ([],[]))
        (output c rf t u y result) ∧
      pairValue result=value a.length R t u y ∧
      LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧
      pairLength result ≤ lengthBound R width.length (pairLength power) u y+power.1.length+1 := by
  intro c
  obtain ⟨ng,hng,m,hg,hms,hflag⟩ := UniversalEntry.guard_eval t u y
    (Numerator.state c regs t u y [] [] ([],[])) (Numerator.guard_project c regs t u y)
  have hm : m=Numerator.state c m.regs t u y [] [] ([],[]) :=
    congrArg₂ StructuredProgram.State.mk rfl hms
  rw [hm] at hg
  by_cases ha : anchorValid (0 : Fin 1) t u y
  · have h9 : (Numerator.state c m.regs t u y [] [] ([],[])).regs 9=true := by
      simpa [Numerator.state,ha] using hflag
    obtain ⟨nn,hnn,rn,num,hen,hvn,hmn,hln⟩ := Numerator.command_eval Hwords width power m.regs a R t u y
      hlen hwords hvalues hp hpt hwidth hAQ hQ
    let s := Numerator.state c rn t u y [] [] num
    obtain ⟨nc,hnc,z,hec,hzs,h7⟩ := TypeCompare.command_eval s
      (by simp [s,Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input])
      (by simp [s,Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input])
      (by simp [s,Numerator.state]) (by simp [s,Numerator.state])
    have hz : z=Numerator.state c z.regs t u y [] [] num :=
      congrArg₂ StructuredProgram.State.mk rfl hzs
    rw [hz] at hec
    have hz7 : z.regs 7=decide (u=y) := by
      simpa [s,Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input] using h7
    let z' := Numerator.state c z.regs t u y [] [] num
    have hready : IntegerFinish.Ready z' := by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [z',Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input]
    obtain ⟨nf,hnf,e,p,n,hef,hes,hvf,hmf,hlf⟩ := IntegerFinish.command_eval z' hready
    have heout : e=output c e.regs t u y (p,n) := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      rw [hes]
      funext j
      by_cases h50 : j=50 <;> by_cases h51 : j=51 <;> by_cases h53 : j=53 <;>
        by_cases h54 : j=54 <;> simp [IntegerFinish.output,z',Numerator.state,Function.update_apply,h50,h51,h53,h54]
    rw [heout] at hef
    have hrun := hg.seq (Eval.ite_true (no := .base .skip) h9 (hen.seq (hec.seq hef)))
    have hlenNum : num.1.length+num.2.length ≤ lengthBound R width.length (pairLength power) u y := hln
    have htimef : nf ≤ 9*num.1.length+2*num.2.length+100*(num.2.length+power.1.length+1)^2+19 := by
      simpa [IntegerFinish.budget,z',Numerator.state,Numerator.baseStacks,c,
        LayoutProgramScalar.FromCounts.unsignedSaved] using hnf
    have htimec : nc ≤ 27*CollisionProgram.typeWidth r Q 1+34 := by
      have hc : nc ≤ 18*CollisionProgram.typeWidth r Q 1+9*CollisionProgram.typeWidth r Q 1+34 := by
        simpa [s,Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,
          MatrixEntryProgram.input,CollisionProgram.encodeType_length] using hnc
      omega
    have hsquare : (num.2.length+power.1.length+1)^2 ≤
        (lengthBound R width.length (pairLength power) u y+power.1.length+1)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    refine ⟨ng+(nn+(nc+nf)+1),?_,e.regs,(p,n),hrun,?_,?_,?_⟩
    · unfold budget
      omega
    · simp [z',Numerator.state,Numerator.baseStacks,c,
        LayoutProgramScalar.FromCounts.unsignedSaved,hz7,hpos] at hvf
      change (BinaryArithmetic.toNat num.1:ℤ)-BinaryArithmetic.toNat num.2 = _ at hvn
      simp only [Numerator.value,ite_eq_left ha] at hvn
      simpa [pairValue,RowSelectionProgram.signedValue,value,ha,hvn] using hvf
    · simp [z',Numerator.state,Numerator.baseStacks,c,
        LayoutProgramScalar.FromCounts.unsignedSaved,hpos] at hmf
      change BinaryArithmetic.toNat num.1+BinaryArithmetic.toNat num.2 ≤ _ at hmn
      change BinaryArithmetic.toNat p+BinaryArithmetic.toNat n ≤ _
      unfold constraintMassBound
      split_ifs at hmf <;> omega
    · have hh : p.length+n.length ≤ num.1.length+num.2.length+power.1.length+1 := by
        simpa [z',Numerator.state,Numerator.baseStacks,c,
          LayoutProgramScalar.FromCounts.unsignedSaved] using hlf
      change p.length+n.length ≤ _
      omega
  · have h9 : (Numerator.state c m.regs t u y [] [] ([],[])).regs 9=false := by
      simpa [Numerator.state,ha] using hflag
    have ht := hg.seq (Eval.ite_false (yes := good) h9 (Eval.base (StructuredProgram.Eval.skip _)))
    rw [← output_empty c m.regs t u y] at ht
    refine ⟨ng+1,?_,m.regs,([],[]),ht,?_,?_,?_⟩
    · unfold budget; omega
    · simp [pairValue,RowSelectionProgram.signedValue,value,ha,BinaryArithmetic.toNat]
    · simp [LayoutProgramScalar.wordTotal,pairTotal]
    · simp [pairLength]

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command_eval_oai
