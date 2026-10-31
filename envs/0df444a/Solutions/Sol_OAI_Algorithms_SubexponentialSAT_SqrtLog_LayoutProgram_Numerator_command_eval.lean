-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:24:01.284982+00:00
-- url     : https://prove2.me/submissions/91780054-9cd8-43ed-9a6d-952111dad0e1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_Numerator_scalar_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_Scan_scanStage_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_UniversalEntry_guard_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_scanCounts_bounds_of_anchor
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_scanFormula_eq_scalarEntry

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

theorem encodeColor_injective {r : ℕ} : Function.Injective (@encodeColor r) := by
  intro c d h
  have he := congrFun (List.ofFn_injective h) c
  simp only [decide_true] at he
  exact (of_decide_eq_true he.symm).symm

@[simp] theorem encodeColor_eq_iff {r : ℕ} (c d : Fin r) :
    encodeColor c = encodeColor d ↔ c = d := encodeColor_injective.eq_iff

theorem encodeColor_pair_eq {r : ℕ} (a b c d : Fin r) :
    encodeColor a ++ encodeColor b = encodeColor c ++ encodeColor d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    exact ⟨encodeColor_injective h1, encodeColor_injective h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem same_typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) :
    same (typedRow i u y l) = decide (u.head l = y.head l ∧ u.slot i l = y.slot i l) := by
  simp [same, typedRow, encodeColor_pair_eq]

theorem swapped_typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) :
    swapped (typedRow i u y l) = decide (u.slot i l = y.head l ∧ u.head l = y.slot i l) := by
  simp [swapped, typedRow, encodeColor_pair_eq]

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Connect the concrete scan counters and adjacent-add value to the actual
joint matrix. These are refinement lemmas for the physical component programs,
not alternative definitions of their runtime instructions. -/

namespace SubexponentialSAT.Subexp.MatrixEntryEvaluation

open MulticolorTypes MatrixScanProgram
open scoped BigOperators

variable {r Q Δ : ℕ}

theorem same_pair (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    same (typedRow i u y l) = decide (MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) := by
  simpa [MatrixEntryKernel.pair, Prod.mk.injEq] using same_typedRow i u y l

theorem swapped_pair (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    swapped (typedRow i u y l) = decide ((u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) := by
  simpa [MatrixEntryKernel.pair, Prod.mk.injEq] using swapped_typedRow i u y l

theorem compatibility_rows (i : Fin Δ) (u y : UniversalType r Q Δ) :
    (decide (MatrixEntryKernel.SpectatorsAgree i u y) && (rows i u y).all compatible) =
      decide (MatrixEntryKernel.AllCompatible i u y) := by
  apply Bool.eq_iff_iff.mpr
  simp [rows, compatible, same_pair, swapped_pair, List.all_eq_true,
    MatrixEntryKernel.AllCompatible, decide_eq_true_eq]
  by_cases h : MatrixEntryKernel.SpectatorsAgree i u y ∧
      ∀ a : Fin Q, MatrixEntryKernel.pair i u a = MatrixEntryKernel.pair i y a ∨
        (u.slot i a, u.head a) = MatrixEntryKernel.pair i y a
  · simp [h]
  · simp [h]

end SubexponentialSAT.Subexp.MatrixEntryEvaluation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScanRestore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The old classifier parks the unary Q word on33. This wrapper physically
returns that word to22 and exposes only the two new counters and flag. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram

theorem scanRegisters_inj : Function.Injective scanRegisters := Fin.castAdd_injective _ _
theorem scanPorts_inj : Function.Injective scanPorts := Fin.castAdd_injective _ _

variable {r Q : ℕ}

theorem command_eval (u y : UniversalType r Q 1) (a : Data)
    (ha : projectState scanRegisters scanPorts a =
      Scan.scanInput (0 : Fin 1) u y [] [] [] [] (a.regs ∘ scanRegisters)) :
    ∃ n ≤ scanStageCost r Q 1 0+3*Q+4, ∃ e : Data,
      Eval command n a e ∧
      e.stacks = Function.update (Function.update a.stacks 2
        (List.replicate (MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows 0 u y)) true)) 3
        (List.replicate (MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows 0 u y)) true) ∧
      e.regs 7 = decide (MatrixEntryKernel.AllCompatible (0 : Fin 1) u y) := by
  let base := Scan.scanInput (0 : Fin 1) u y [] [] [] [] (a.regs ∘ scanRegisters)
  let U := MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows 0 u y)
  let H := MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows 0 u y)
  obtain ⟨ns,hns,rs,hs,hflag⟩ := Scan.scanStage_eval (0 : Fin 1) u y [] [] [] []
    (a.regs ∘ scanRegisters)
  change Eval scanStage ns base (counted base rs U H) at hs
  have hs' : Eval scanStage ns (projectState scanRegisters scanPorts a) (counted base rs U H) := by
    rw [ha]
    exact hs
  let m := embedState scanRegisters scanPorts a (counted base rs U H)
  have he := eval_liftCommand_from_state scanStage 23 0 scanRegisters scanPorts a
    scanRegisters_inj scanPorts_inj hs'
  have hslot (j : Fin 37) : a.stacks (scanPorts j) = base.stacks j :=
    congrFun (congrArg StructuredProgram.State.stacks ha) j
  have hcounted : (counted base rs U H).stacks =
      Function.update (Function.update (Function.update (Function.update base.stacks
        2 (List.replicate U true)) 3 (List.replicate H true)) 22 []) 33 (List.replicate Q true) := by
    funext j
    fin_cases j <;> simp [counted,base,Scan.scanInput,input,Function.update]
  have hbase : Function.extend scanPorts base.stacks a.stacks = a.stacks := by
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project scanRegisters scanPorts a scanRegisters_inj scanPorts_inj)
    rw [ha] at h
    exact h
  have hm : m.stacks = Function.update (Function.update (Function.update (Function.update
      a.stacks 2 (List.replicate U true)) 3 (List.replicate H true)) 22 [])
      33 (List.replicate Q true) := by
    change Function.extend scanPorts (counted base rs U H).stacks a.stacks = _
    rw [hcounted,ProgramLinking.extend_update scanPorts_inj,
      ProgramLinking.extend_update scanPorts_inj,ProgramLinking.extend_update scanPorts_inj,
      ProgramLinking.extend_update scanPorts_inj,hbase]
    rfl
  have hr := SubexpScanPrimitives.transfer_eval m (33 : Fin 64) 22 (0 : Fin 10) 1
    (by decide) (by decide)
  let e := SubexpScanPrimitives.afterTransfer m 33 22 0 1
  have hout : e.stacks = Function.update (Function.update a.stacks 2
      (List.replicate U true)) 3 (List.replicate H true) := by
    have h22 : a.stacks 22 = List.replicate Q true := by
      simpa [scanPorts,base,Scan.scanInput,input] using hslot 22
    have h33 : a.stacks 33 = [] := by
      simpa [scanPorts,base,Scan.scanInput,input] using hslot 33
    funext j
    by_cases h2 : j=2 <;> by_cases h3 : j=3 <;>
      by_cases h22' : j=22 <;> by_cases h33' : j=33 <;>
      simp [e,SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks,hm,
        h2,h3,h22',h33',h22,h33,Function.update]
  have hm7 : m.regs 7 = rs 7 := by
    exact embedState_register scanRegisters scanPorts a (counted base rs U H)
      scanRegisters_inj 7
  have h7 : e.regs 7 = rs 7 := by
    simpa [e,SubexpScanPrimitives.afterTransfer,readRegs] using hm7
  have spectator : MatrixEntryKernel.SpectatorsAgree (0 : Fin 1) u y := by
    intro j hj
    exact (hj (Subsingleton.elim j 0)).elim
  have hall : rs 7 = decide (MatrixEntryKernel.AllCompatible (0 : Fin 1) u y) := by
    rw [hflag]
    simpa [spectator] using MatrixEntryEvaluation.compatibility_rows (0 : Fin 1) u y
  refine ⟨(ns+1)+(3*(m.stacks 33).length+3),?_,e,he.seq hr,hout,h7.trans hall⟩
  simp only [hm,Function.update_self,List.length_replicate]
  have hns0 : ns ≤ scanStageCost r Q 1 0 := by simpa using hns
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

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

theorem scan_project (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) :
    projectState ScanRestore.scanRegisters ScanRestore.scanPorts (state c regs t u y [] [] ([],[])) =
      Scan.scanInput (0 : Fin 1) u y [] [] [] [] (regs ∘ ScanRestore.scanRegisters) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  fin_cases j <;> simp [ScanRestore.scanPorts,state,baseStacks,Guard.guardInput,
    Scan.scanInput,MatrixEntryProgram.input]

theorem clearCounts_eval (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) (uc hc : List Bool) :
    ∃ rf, Eval clearCounts (2*uc.length+2*hc.length+6)
      (state c regs t u y uc hc ([],[])) (state c rf t u y [] [] ([],[])) := by
  let s := state c regs t u y uc hc ([],[])
  let s₁ : Data := ⟨readRegs regs 0 1 none,StackRoutines.clearStacks 2 s.stacks⟩
  let s₂ : Data := ⟨readRegs s₁.regs 0 1 none,StackRoutines.clearStacks 3 s₁.stacks⟩
  have h₁ := Subexp.TupleProgram.clear_eval 2 0 1 s
  have h₂ := Subexp.TupleProgram.clear_eval 3 0 1 s₁
  have hs : s₂ = state c s₂.regs t u y [] [] ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    by_cases h2 : j=2 <;> by_cases h3 : j=3 <;>
      simp [s₁,s,state,StackRoutines.clearStacks,Function.update_apply,h2,h3]
  have hh := h₁.seq h₂
  change Eval clearCounts _ s s₂ at hh
  rw [hs] at hh
  refine ⟨s₂.regs,?_⟩
  convert hh using 1 ; simp [s₁,s,state,StackRoutines.clearStacks] ; omega

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumeratorRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
open MatrixScanProgram MatrixEntryEvaluation MatrixEntryKernel MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

theorem state_counted (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) (uc hc : List Bool) :
    Function.update (Function.update (state c regs t u y [] [] ([],[])).stacks 2 uc) 3 hc =
      (state c regs t u y uc hc ([],[])).stacks := by
  funext j
  by_cases h2 : j=2 <;> by_cases h3 : j=3 <;> by_cases h50 : j=50 <;>
    by_cases h51 : j=51 <;> simp_all [state,Function.update_apply]

/-- The fixed program computes the literal guarded integer numerator and
returns all type words and reusable caches intact. -/
theorem command_eval_oai (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 10 → Bool) (a : List Bool) (R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) :
    let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
    ∃ n ≤ budget a.length R width.length (pairLength power) t u y,
      ∃ rf result, Eval command n (state c regs t u y [] [] ([],[]))
        (state c rf t u y [] [] result) ∧
      pairValue result=value a.length R t u y ∧
      LayoutProgramScalar.wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-(unchangedCount (rows 0 u y)-1))*
        LayoutProgramScalar.termGrowth (2*width.length+pairLength power) := by
  intro c
  obtain ⟨ng,hng,m,hg,hms,hflag⟩ := UniversalEntry.guard_eval t u y
    (state c regs t u y [] [] ([],[])) (guard_project c regs t u y)
  have hm : m = state c m.regs t u y [] [] ([],[]) :=
    congrArg₂ StructuredProgram.State.mk rfl hms
  rw [hm] at hg
  by_cases ha : anchorValid (0 : Fin 1) t u y
  · have h9 : (state c m.regs t u y [] [] ([],[])).regs 9=true := by
      simpa [state,ha] using hflag
    obtain ⟨ns,hns,z,hs,hzs,hcomp⟩ := ScanRestore.command_eval u y
      (state c m.regs t u y [] [] ([],[])) (scan_project c m.regs t u y)
    have hz : z = state c z.regs t u y
        (List.replicate (unchangedCount (rows 0 u y)) true)
        (List.replicate (transposedCount (rows 0 u y)) true) ([],[]) := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      exact hzs.trans (state_counted c m.regs t u y _ _)
    rw [hz] at hs
    by_cases hc : AllCompatible (0 : Fin 1) u y
    · have h7 : (state c z.regs t u y
          (List.replicate (unchangedCount (rows 0 u y)) true)
          (List.replicate (transposedCount (rows 0 u y)) true) ([],[])).regs 7=true := by
        simpa [state,hc] using hcomp
      obtain ⟨hu,huQ,hhQ⟩ := LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor t u y ha hc
      have hu' : unchangedCount (rows 0 u y)-1+1=unchangedCount (rows 0 u y) := by omega
      obtain ⟨nc,hnc,rf,result,he,hv,hmass,hlength⟩ := scalar_eval Hwords width power z.regs a R
        (unchangedCount (rows 0 u y)-1) t u y
        (List.replicate (transposedCount (rows 0 u y)) true)
        hlen hwords hvalues hp hpt (by simpa using (by omega : transposedCount (rows 0 u y)+1 ≤ width.length))
        hAQ hQ (by simpa using hhQ)
      simp only [hu',List.length_replicate] at he hv hnc
      have ht := hg.seq (Eval.ite_true (no := .base .skip) h9
        (hs.seq (Eval.ite_true (no := clearCounts) h7 he)))
      refine ⟨ng+(ns+(nc+1)+1),?_,rf,result,ht,?_,hmass,hlength⟩
      · unfold budget
        omega
      · have hformula := LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry
          a.length R t u y ha
        simpa [value,ha,hc] using hv.trans (by simpa [hc] using hformula)
    · have h7 : (state c z.regs t u y
          (List.replicate (unchangedCount (rows 0 u y)) true)
          (List.replicate (transposedCount (rows 0 u y)) true) ([],[])).regs 7=false := by
        simpa [state,hc] using hcomp
      obtain ⟨rf,he⟩ := clearCounts_eval c z.regs t u y
        (List.replicate (unchangedCount (rows 0 u y)) true)
        (List.replicate (transposedCount (rows 0 u y)) true)
      simp only [List.length_replicate] at he
      have ht := hg.seq (Eval.ite_true (no := .base .skip) h9
        (hs.seq (Eval.ite_false (yes := scalar) h7 he)))
      refine ⟨ng+(ns+(2*unchangedCount (rows 0 u y)+2*transposedCount (rows 0 u y)+6+1)+1),
        ?_,rf,([],[]),ht,?_,?_,?_⟩
      · unfold budget
        omega
      · have hformula := LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry
          a.length R t u y ha
        simpa [value, ha, hc, pairValue, RowSelectionProgram.signedValue] using hformula
      · simp [LayoutProgramScalar.wordTotal,pairTotal]
      · simp [pairLength]
  · have h9 : (state c m.regs t u y [] [] ([],[])).regs 9=false := by
      simpa [state,ha] using hflag
    have ht := hg.seq (Eval.ite_false (yes := guarded) h9
      (Eval.base (StructuredProgram.Eval.skip _)))
    refine ⟨ng+1,?_,m.regs,([],[]),ht,?_,?_,?_⟩
    · unfold budget
      omega
    · simp [value,ha,pairValue,RowSelectionProgram.signedValue,BinaryArithmetic.toNat]
    · simp [LayoutProgramScalar.wordTotal,pairTotal]
    · simp [pairLength]

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval_oai
