-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.mass_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:40:45.688995+00:00
-- url     : https://prove2.me/submissions/6e608e0c-ffff-414d-acdd-86c97375c10c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMassAdapter_finish_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMassAdapter_references_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- This adds two binary words with an actual execution of the fixed adder. -/
theorem command_eval (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 1, ∃ regs',
      Eval command n (data regs acc next) (data regs' (BinaryArithmetic.add acc next) []) := by
  let reset := Function.update regs 0 false
  obtain ⟨regs', n, hn, ht⟩ := BinaryPrograms.Add.littleEndian_run reset acc next
  have hs : (StructuredProgram.Atom.set 0 false).eval (data regs acc next) =
      data reset acc next := by
    rfl
  refine ⟨1 + n, by omega, regs', ?_⟩
  apply Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 0 false) _))
  rw [hs]
  apply Eval.call
  have hentry : BinaryPrograms.Add.littleEndianProgram.entry = 0 := rfl
  simpa [data, reset, BinaryArithmetic.add, StructuredProgram.State.withPC, hentry] using ht

theorem program_trace (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 2, ∃ regs',
      Trace program n ((data regs acc next).withPC (some program.entry))
        ((data regs' (BinaryArithmetic.add acc next) []).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := command_eval regs acc next
  exact ⟨n + 1, by omega, regs', compiled_halt_trace ht 1 0⟩

variable {r s : ℕ}

theorem invoke_eval (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 3, ∃ regs',
      Eval (invoke p) n (state p frame regs acc next)
        (state p frame regs' (BinaryArithmetic.add acc next) []) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs acc next
  exact ⟨n, by omega, regs', eval_call_lifted program p.register p.stack frame
    p.register_injective p.stack_injective ht⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

private theorem workPort_ne (i : Fin 891) (j : Fin 896) (hj : 320 ≤ j.val ∧ j.val ≤ 324) :
    workPort i ≠ j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [workPort] at hv
  split_ifs at hv <;> simp only at hv <;> omega

@[simp] theorem workspace_recordState (a : Data) (v pr f : Bool) (src payload : List Bool) :
    workspace (RecordPrograms.state recordPorts a v pr f src payload) = workspace a := by
  funext i
  have hs := workPort_ne i 320 (by decide)
  have hp := workPort_ne i 321 (by decide)
  simp [workspace, RecordPrograms.state, recordPorts, hs, hp]

private theorem mass_state_eq_self (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (hr : ∀ i, regs i = a.regs (massPorts.register i))
    (hs : ∀ i, (Mass.data regs acc next).stacks i = a.stacks (massPorts.stack i)) :
    Mass.state massPorts a regs acc next = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, massPorts.register j = i
    · obtain ⟨j, rfl⟩ := h
      exact (embedState_register massPorts.register massPorts.stack a (Mass.data regs acc next) massPorts.register_injective j).trans (hr j)
    · exact embedState_register_frame massPorts.register massPorts.stack a (Mass.data regs acc next) i h
  · funext i
    by_cases h : ∃ j, massPorts.stack j = i
    · obtain ⟨j, rfl⟩ := h
      exact (embedState_stack massPorts.register massPorts.stack a (Mass.data regs acc next) massPorts.stack_injective j).trans (hs j)
    · exact embedState_stack_frame massPorts.register massPorts.stack a (Mass.data regs acc next) i h

private theorem mass_stack_local (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 3) :
    (Mass.state massPorts a regs acc next).stacks (massPorts.stack i) =
      (Mass.data regs acc next).stacks i :=
  embedState_stack _ _ _ _ massPorts.stack_injective i

private theorem mass_stack_frame (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 896) (hi : i.val < 322 ∨ 324 < i.val) :
    (Mass.state massPorts a regs acc next).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  fin_cases j <;> simp [massPorts] at hh <;> omega

private theorem mass_reg_frame (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (Mass.state massPorts a regs acc next).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  simp [massPorts] at hh
  omega

@[simp] theorem workspace_mass_state (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool) :
    workspace (Mass.state massPorts a regs acc next) = workspace a := by
  funext i
  apply mass_stack_frame
  dsimp [workPort]
  split_ifs <;> simp <;> omega

/-- Consume one physically computed count word, without requiring a canonical
representation of that integer. -/
theorem add_count_eval (ready : (Fin 891 → List Bool) → Prop)
    (middle : Data) (tail acc word : List Bool)
    (hm : ready (workspace middle)) (hr : read middle = acc)
    (hc : middle.stacks 323 = word) (hs : middle.stacks 324 = []) :
    ∃ n next, n ≤ 16*(max acc.length word.length+1)+3 ∧
      Ready ready next ∧ read next = BinaryArithmetic.add acc word ∧
      Eval (Mass.invoke massPorts) n
        (RecordPrograms.state recordPorts middle false true false tail [])
        (RecordPrograms.state recordPorts next false true false tail []) := by
  let a := RecordPrograms.state recordPorts middle false true false tail []
  let regs := fun i => a.regs (massPorts.register i)
  have ha : Mass.state massPorts a regs acc word = a := by
    apply mass_state_eq_self _ _ _ _ (fun _ => rfl)
    intro i
    fin_cases i <;>
      simp [Mass.data, BinaryPrograms.Add.stackState, massPorts, a,
        RecordPrograms.state, recordPorts, read] at hr ⊢
    · exact hr.symm
    · exact hc.symm
    · exact hs
  obtain ⟨n, hn, regs', he⟩ := Mass.invoke_eval massPorts a regs acc word
  let b := Mass.state massPorts a regs' (BinaryArithmetic.add acc word) []
  have hb322 : b.stacks 322 = BinaryArithmetic.add acc word := mass_stack_local a regs' _ [] 0
  have hb323 : b.stacks 323 = [] := mass_stack_local a regs' _ [] 1
  have hb324 : b.stacks 324 = [] := mass_stack_local a regs' _ [] 2
  have hb320 : b.stacks 320 = tail := by rw [mass_stack_frame _ _ _ _ _ (by decide)]; rfl
  have hb321 : b.stacks 321 = [] := by rw [mass_stack_frame _ _ _ _ _ (by decide)]; rfl
  have hb16 : b.regs 16 = false := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hb17 : b.regs 17 = true := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hb18 : b.regs 18 = false := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hstate : RecordPrograms.state recordPorts b false true false tail [] = b :=
    RecordPrograms.state_eq_self recordPorts b _ _ _ _ _ hb16 hb17 hb18 hb320 hb321
  refine ⟨n,b,hn,⟨?_,hb323,hb324⟩,hb322,?_⟩
  · simpa [b,a] using hm
  · rw [hstate]
    simpa only [ha,b] using he
theorem value_callback (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 891 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : ∀ bits tail (base : Data), valid bits → Ready ready base →
      ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (bits tail : List Bool) (base : Data) (hv : valid bits) (hb : Ready ready base) :
    ∃ n next, n ≤ queryCost bits + 16*(max (read base).length (width bits)+1)+3 ∧
      Ready ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+count bits ∧
      (read next).length ≤ (read base).length + width bits + 1 ∧
      Eval (callback query) n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts next false true false tail []) := by
  obtain ⟨n,middle,hn,hm,hr,hv,hl,hs,ht⟩ := hq bits tail base hv hb
  obtain ⟨m,next,hmn,hi,ha,he⟩ :=
    add_count_eval ready middle tail (read base) (middle.stacks 323) hm hr rfl hs
  refine ⟨n+m,next,by omega,hi,?_,?_,ht.seq he⟩
  · rw [ha,BinaryArithmetic.toNat_add,hv]
  · rw [ha]
    have := BinaryArithmetic.length_add (read base) (middle.stacks 323)
    omega

theorem value_loop_run_length (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 891 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : ∀ bits tail (base : Data), valid bits → Ready ready base →
      ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (records : List (List Bool)) (suffix : List Bool) (base : Data) (M : ℕ)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : Ready ready base)
    (hsize : (read base).length + valueInputSize width records ≤ M) :
    ∃ n next, n ≤ 1+(records.map queryCost).sum + records.length*(22*M+26) ∧
      Ready ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+(records.map count).sum ∧
      (read next).length ≤ (read base).length+outputGrowth width records ∧
      Eval (loop recordPorts (callback query)) n (afterTag recordPorts base records suffix)
        (state recordPorts next false true false suffix []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1,base,by simp,hb,by simp,by simp [outputGrowth],?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n,middle,hn,hm,hvalue,hlen,hcall⟩ :=
        value_callback query count queryCost width ready valid hq bits tail base
          (hrecords bits (by simp)) hb
      have hs : (read base).length+bits.length+width bits+1+valueInputSize width rest ≤ M := by
        simpa [valueInputSize,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize
      have hrsize : (read middle).length + valueInputSize width rest ≤ M := by omega
      obtain ⟨m,next,hmn,hi,hv,hfinal,ht⟩ :=
        ih middle (fun b hh => hrecords b (by simp [hh])) hm hrsize
      have hreader : Eval (reader recordPorts) (6*bits.length+4)
          (afterTag recordPorts base (bits::rest) suffix)
          (state recordPorts base false true false tail bits.reverse) := by
        simpa [afterTag,tail] using reader_eval recordPorts base bits tail [] true true false
      have hpop : Eval
          (.ite recordPorts.found (atom (.set recordPorts.tag false))
            (atom (.pop recordPorts.source recordPorts.tag recordPorts.present))) 2
          (state recordPorts middle false true false tail [])
          (afterTag recordPorts middle rest suffix) := by
        apply Eval.ite_false (by simp)
        exact pop_list_eval recordPorts middle rest suffix false true
      refine ⟨(6*bits.length+4+(n+2))+m+1,next,?_,hi,?_,?_,?_⟩
      · have hc : n ≤ queryCost bits + 16*(M+1)+3 := by omega
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
      · rw [hv,hvalue]
        simp only [List.map_cons,List.sum_cons]
        omega
      · simp only [outputGrowth,List.map_cons,List.sum_cons] at hfinal ⊢
        omega
      · exact Eval.while_true (by simp [afterTag])
          (hreader.seq (hcall.seq hpop)) ht

theorem value_program_run_length (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 891 → List Bool) → Prop) (valid : List Bool → Prop)
    (hq : ∀ bits tail (base : Data), valid bits → Ready ready base →
      ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (records : List (List Bool)) (suffix : List Bool) (base : Data)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : Ready ready base) (v pr f : Bool) :
    ∃ next, Ready ready next ∧
      BinaryArithmetic.toNat (read next) = BinaryArithmetic.toNat (read base)+(records.map count).sum ∧
      (read next).length ≤ (read base).length+outputGrowth width records ∧
      RunsIn (program query) (valueBudget queryCost width records (read base))
        ((state recordPorts base v pr f (Encoding.encodeList id records++suffix) []).withPC
          (some (program query).entry))
        ((state recordPorts next false true false suffix []).withPC none) := by
  obtain ⟨n,next,hn,hi,hv,hfinal,ht⟩ := value_loop_run_length query count queryCost width ready valid hq
    records suffix base ((read base).length+valueInputSize width records) hrecords hb le_rfl
  have hrun := (set_found_eval recordPorts base v pr f false _ []).seq
    ((pop_list_eval recordPorts base records suffix v pr).seq ht)
  refine ⟨next,hi,hv,hfinal,1+(1+n)+1,?_,compiled_halt_trace hrun 320 322⟩
  dsimp [valueBudget]
  omega

variable {X Row : Type*} [Fintype X] {m : ℕ}



/-- Equality of the retained workspace frames every port outside the five
physical collector words, including all high query and selector ports. -/
theorem workspace_frame (a b : Data) (h : workspace b = workspace a)
    (i : Fin 896) (h320 : i ≠ 320) (h321 : i ≠ 321) (h322 : i ≠ 322)
    (h323 : i ≠ 323) (h324 : i ≠ 324) : b.stacks i = a.stacks i := by
  have h320' : i.val ≠ 320 := by intro hh; exact h320 (Fin.ext hh)
  have h321' : i.val ≠ 321 := by intro hh; exact h321 (Fin.ext hh)
  have h322' : i.val ≠ 322 := by intro hh; exact h322 (Fin.ext hh)
  have h323' : i.val ≠ 323 := by intro hh; exact h323 (Fin.ext hh)
  have h324' : i.val ≠ 324 := by intro hh; exact h324 (Fin.ext hh)
  by_cases hlow : i.val < 320
  · let j : Fin 891 := ⟨i.val, by omega⟩
    have hj : workPort j = i := by simp [workPort, j, hlow]
    simpa only [workspace, hj] using congrFun h j
  · let j : Fin 891 := ⟨i.val - 5, by omega⟩
    have hj : workPort j = i := by
      apply Fin.ext
      simp [workPort, j, show ¬i.val - 5 < 320 by omega]
      omega
    simpa only [workspace, hj] using congrFun h j

/-- Actual execution of the complete collector gives an exact whole-bank
frame. Its source stream is consumed, its aggregate is retained on322, and all
other words have their entry values. -/
theorem collector_eval (query : Code) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : Data) (records : List (List Bool))
    (hsource : a.stacks 320 = Encoding.encodeList id records)
    (h321 : a.stacks 321 = []) (h322 : a.stacks 322 = [])
    (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = [])
    (hrecords : ∀ bits ∈ records, valid bits)
    (hq : ∀ bits tail (base : Data), valid bits →
      Ready (fun words => words = workspace a) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace a ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ n ≤ valueBudget queryCost width records [], ∃ b,
      Eval (.call (program query)) n a b ∧
      BinaryArithmetic.toNat (b.stacks 322) = (records.map count).sum ∧
      (b.stacks 322).length ≤ outputGrowth width records ∧
      b.stacks = Function.update (Function.update a.stacks 320 []) 322 (b.stacks 322) := by
  have hi : Ready (fun words => words = workspace a) a := ⟨rfl,h323,h324⟩
  obtain ⟨next, hnext, hv, hl, n, hn, ht⟩ := value_program_run_length query count queryCost width
    (fun words => words = workspace a) valid hq records [] a hrecords hi
    (a.regs 16) (a.regs 17) (a.regs 18)
  have hstart : state recordPorts a (a.regs 16) (a.regs 17) (a.regs 18)
      (Encoding.encodeList id records ++ []) [] = a := by
    apply state_eq_self recordPorts a _ _ _ _ _ rfl rfl rfl
    · simpa only [recordPorts, List.append_nil] using hsource
    · exact h321
  rw [hstart] at ht
  let b := state recordPorts next false true false [] []
  have hread : b.stacks 322 = read next := by simp [b, state, recordPorts, read]
  refine ⟨n, by simpa [read, h322] using hn, b, Eval.call _ ht,
    ?_, ?_, ?_⟩
  · simpa [hread, read, h322] using hv
  · simpa [hread, read, h322] using hl
  · funext i
    by_cases hi320 : i = 320
    · subst i; simp [b, state, recordPorts]
    by_cases hi321 : i = 321
    · subst i; simp [b, state, recordPorts, h321]
    by_cases hi322 : i = 322
    · subst i; simp
    by_cases hi323 : i = 323
    · subst i; simp [b, state, recordPorts, h323, hnext.result_empty]
    by_cases hi324 : i = 324
    · subst i; simp [b, state, recordPorts, h324, hnext.scratch_empty]
    simpa [b, state, recordPorts, hi320, hi321, hi322] using
      workspace_frame a next hnext.workspace_ready i hi320 hi321 hi322 hi323 hi324


open LeafOuterProgram

open scoped BigOperators

/-- The full stack effect is exactly the selector ABI. No query temporary,
reference stream, or aggregate word remains outside the score slot. -/
theorem mass_eval_oai (query : Code) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : Data) (m : ℕ) (ha : ReferencesReady a)
    (hm : CounterPrograms.value (a.stacks 782) = m)
    (h321 : a.stacks 321 = []) (h322 : a.stacks 322 = [])
    (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = [])
    (hvalid : ∀ e : Fin m, valid (Encoding.encodeNat e.val))
    (hq : ∀ bits tail (base : Data), valid bits →
      Ready (fun words => words = workspace a) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace a ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ n ≤ massBudget a queryCost width m, ∃ b, Eval (mass query) n a b ∧
      b.stacks = Function.update a.stacks 769
        (DisjointReuse.binaryNat (((RowSelectionProgram.Index.alphabet m).map count).sum)) := by
  obtain ⟨np, prepared, hnp, hp, hprepared⟩ := references_eval a ha
  have hws : workspace prepared = workspace a := by
    funext i
    have hi := workPort_ne i 320 (by decide)
    simp [workspace, hprepared, hi]
  have hq' : ∀ bits tail (base : Data), valid bits →
      Ready (fun words => words = workspace prepared) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace prepared ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []) := by simpa only [hws] using hq
  have hrecords : ∀ bits ∈ RowSelectionProgram.Index.alphabet m, valid bits := by
    intro bits hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact hvalid ⟨j, by simpa using hj⟩
  obtain ⟨nc, hnc, collected, hc, hvalue, hlen, hframe⟩ :=
    collector_eval query count queryCost width valid prepared (RowSelectionProgram.Index.alphabet m)
      (by simp [hprepared, hm, ProgramEncoding.encodeRecords])
      (by simp [hprepared, h321]) (by simp [hprepared, h322])
      (by simp [hprepared, h323]) (by simp [hprepared, h324]) hrecords hq'
  let total := collected.stacks 322
  change collected.stacks = Function.update (Function.update prepared.stacks 320 []) 322 total at hframe
  have htotal : BinaryArithmetic.toNat total = ((RowSelectionProgram.Index.alphabet m).map count).sum := hvalue
  have hcollected : collected.stacks = Function.update a.stacks 322 total := by
    funext i
    by_cases h320 : i = 320
    · subst i; simp [hframe, hprepared, ha.empty 320 (by decide)]
    simp [hframe, hprepared, Function.update_apply, h320]
  obtain ⟨nf, hnf, b, hf, hb⟩ := finish_eval collected
    (by simp [hcollected, h323]) (by simp [hcollected, h324])
    (by simp [hcollected, ha.scratch])
    (outputGrowth width (RowSelectionProgram.Index.alphabet m) + (a.stacks 769).length)
    (by omega) (by simp [hcollected])
  refine ⟨np + (nc + nf), by dsimp [massBudget]; omega, b, hp.seq (hc.seq hf), ?_⟩
  rw [hb]
  funext i
  by_cases hi : i = 322
  · subst i; simp [finishedStacks, hcollected, h322]
  simp [finishedStacks, hcollected, Function.update_apply, htotal, hi]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.mass_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.mass_eval_oai
