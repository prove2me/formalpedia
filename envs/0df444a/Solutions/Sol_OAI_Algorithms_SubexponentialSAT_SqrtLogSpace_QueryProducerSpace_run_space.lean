-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:38:45.982706+00:00
-- url     : https://prove2.me/submissions/f181296a-47e1-464e-b3cb-2bc9cb321612

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Normalize_program_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram_Specialization_raw_dictionary_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable normalized sparse coefficient lists. Zero coefficients may stay
in the list; keys are unique, so this does not enlarge the finite index bound.
No equality decision for coefficients or full ambient Boolean table is used. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {K R A : Type*} [DecidableEq K] [AddCommMonoid R]

omit [AddCommMonoid R] in
theorem length_le_card (l : Data K R) (s : Finset K) (hn : (keys l).Nodup)
    (hs : ∀ k ∈ keys l, k ∈ s) : l.length ≤ s.card := by
  have hsub : (keys l).toFinset ⊆ s := by
    intro k hk
    exact hs k (List.mem_toFinset.mp hk)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at hcard
  simpa only [keys, List.length_map] using hcard

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem mem_indexUniverse (vars : Finset V) (t J : ℕ) (a : Index V) :
    a ∈ indexUniverse vars t J ↔ a.Kept t J ∧ a.vars ⊆ vars ∧ a.vars.card < J := by
  rcases a with ⟨u, z, s⟩
  simp [indexUniverse, supportUniverse, Index.Kept, Finset.mem_image]

theorem indexUniverse_card_le (vars : Finset V) (t J : ℕ) :
    (indexUniverse vars t J).card ≤ t * J * (supportUniverse vars J).card := by
  exact (Finset.card_image_le).trans (by simp)

omit [CommSemiring R] in
theorem ValidData.in_universe {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) : ∀ a ∈ keys l, a ∈ indexUniverse vars t J := by
  intro a ha
  rcases h a ha with ⟨hk, hv, hs⟩
  exact (mem_indexUniverse vars t J a).mpr ⟨hk, hs, hv.trans_lt hk.2⟩

omit [CommSemiring R] in
theorem ValidData.length_le {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) (hn : (keys l).Nodup) :
    l.length ≤ t * J * (supportUniverse vars J).card :=
  (length_le_card l _ hn h.in_universe).trans (indexUniverse_card_le vars t J)

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Restricted sums over the actual Boolean heads. All products are formed in
one coefficient ring before any additive coefficient readout. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

variable {V R : Type*} [DecidableEq V]

theorem specializeEntries_length (U : Finset V) (xs : List (Squarefree.Index V × R)) :
    (specializeEntries U xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [specializeEntries]
  | cons a xs ih =>
    rcases a with ⟨a,c⟩
    by_cases h : a.vars ⊆ U <;> simp [specializeEntries,h] <;> omega

theorem mem_specializeEntries (U : Finset V) (xs : List (Squarefree.Index V × R))
    (b : Squarefree.Index V × R) (hb : b ∈ specializeEntries U xs) :
    ∃ a ∈ xs, a.1.vars ⊆ U ∧ b = (⟨a.1.u,a.1.z,∅⟩,a.2) := by
  induction xs with
  | nil => simp [specializeEntries] at hb
  | cons a xs ih =>
    by_cases h : a.1.vars ⊆ U
    · simp only [specializeEntries, h, ite_true, if_true, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨a,List.mem_cons_self,h,rfl⟩
      · obtain ⟨c,hc,hU,he⟩ := ih hb
        exact ⟨c,List.mem_cons_of_mem a hc,hU,he⟩
    · simp only [specializeEntries, h, ite_false] at hb
      obtain ⟨c,hc,hU,he⟩ := ih hb
      exact ⟨c,List.mem_cons_of_mem a hc,hU,he⟩

theorem specializeEntries_map {S : Type*} (U : Finset V)
    (xs : List (Squarefree.Index V × R)) (f : R → S) :
    specializeEntries U (xs.map (fun a => (a.1,f a.2))) =
      (specializeEntries U xs).map (fun a => (a.1,f a.2)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a.1.vars ⊆ U <;> simp [specializeEntries,h,ih]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_injective {n : ℕ} :
    Function.Injective (encodeMask (n := n)) := by
  intro a b h
  have hf : (fun i : Fin n => decide (i ∈ a)) =
      (fun i : Fin n => decide (i ∈ b)) := List.ofFn_injective h
  ext i
  have hi := congrFun hf i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all

theorem encodeIndex_injective {n : ℕ} :
    Function.Injective (encodeIndex (n := n)) := by
  intro a b h
  have hfirst : a.u = b.u ∧
      Encoding.encodeNat a.z ++ encodeMask a.vars =
        Encoding.encodeNat b.z ++ encodeMask b.vars := by
    simpa [encodeIndex, List.append_assoc] using congrArg Encoding.readNat h
  have hsecond : a.z = b.z ∧ encodeMask a.vars = encodeMask b.vars := by
    simpa using congrArg Encoding.readNat hfirst.2
  have hs := encodeMask_injective hsecond.2
  cases a
  cases b
  cases hfirst.1
  cases hsecond.1
  cases hs
  rfl

theorem encodeIndex_length_le {n t J : ℕ} (a : Index (Fin n))
    (h : a.Kept t J) : (encodeIndex a).length ≤ t + J + n := by
  rw [encodeIndex_length]
  obtain ⟨hu, hz⟩ := h
  omega

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive dictionary lookup. Dictionary normalization guarantees
unique keys. All key and coefficient bits are scanned by the existing finite
record program; key width, coefficient width and dictionary length are runtime
data and do not affect the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

variable {K C : Type*} [DecidableEq K]

/-- All scan costs, including failed key comparisons, are linear in serialized
key/payload lengths times the number of entries, with explicit query scans. -/
theorem lookupBudget_bound (query : List Bool) (entries : List (List Bool × List Bool))
    (W B : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W)
    (hc : ∀ a ∈ entries, a.2.length ≤ B) :
    lookupBudget query entries ≤ entries.length * (17 * W + 9 * query.length + 13 * B + 40) + 1 := by
  induction entries with
  | nil => simp [lookupBudget, SubexponentialSAT.Subexp.SelectorProgram.scanBudget]
  | cons a entries ih =>
    rcases a with ⟨k,c⟩
    have h1 := hk (k,c) (by simp)
    have h2 := hc (k,c) (by simp)
    have h3 := ih (fun a ha => hk a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
    simp only [lookupBudget, SubexponentialSAT.Subexp.SelectorProgram.scanBudget,
      recordCost, List.length_cons] at *
    nlinarith

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem eraseBudget_bound (query : List Bool) (entries : List ByteRecord) (W B : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ B) :
    eraseBudget query entries ≤ entries.length * (28*W+9*query.length+13*B+53)+1 := by
  induction entries with
  | nil => simp [eraseBudget]
  | cons a entries ih =>
    rcases a with ⟨k,c⟩
    have h1 := hk (k,c) (by simp)
    have h2 := hc (k,c) (by simp)
    have h3 := ih (fun a ha => hk a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
    simp only [eraseBudget,List.length_cons] at *
    nlinarith
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization using the actual dictionary scanner. -/

/-! The dictionary framing, key rewrite and record traversal follow the actual
MomentsProjectionProgramNative implementation. The replacement comparator tests
support inclusion, so this scan implements evaluation at a Boolean correction
assignment. Numeric-key collisions are intentionally left for normalization. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProjectionProgram


open Squarefree

/-- Every stack, including retained mask, parser buffers, original records and
new records, is included throughout this polynomial local routine. -/
theorem raw_dictionary_run_space {n : ℕ} (U : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) (regs : Fin 5 → Bool) :
    let source := Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))
    let budget := 200*(source.length+1)*(n+2)+1
    ∃ steps ≤ budget, ∃ rf,
      Trace program steps
        ((machine regs {input:=Encoding.frame (encodeMask U)++source}).withPC (some program.entry))
        ((machine rf {target:=(encodeMask U).reverse,framed:=
          Squarefree.Program.rawEntries ((HeadEvaluation.specializeEntries U l).map
            fun a => (encodeIndex a.1,a.2))}).withPC none) ∧
      ∀ j ≤ steps, ∀ c, Trace program j
        ((machine regs {input:=Encoding.frame (encodeMask U)++source}).withPC (some program.entry)) c →
        dataBits c ≤ source.length+2*n+2+budget := by
  dsimp only
  obtain ⟨rf,steps,hsteps,ht⟩ := raw_dictionary_runsIn U l regs
  refine ⟨steps,hsteps,rf,ht,?_⟩
  intro j hj c hc
  have hb := trace_dataBits program hc
  have hi : dataBits ((machine regs {input:=Encoding.frame (encodeMask U)++
        Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))}).withPC (some program.entry)) =
      (Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))).length+2*n+1 := by
    simp [dataBits,stackBits,machine,tapes,Fin.sum_univ_succ,
      Nat.add_assoc,Nat.add_comm]
  rw [hi] at hb
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K C R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_keys (f : C → R) (entries : List (K × C)) :
    Squarefree.Sparse.keys (denoteTable f entries) = Squarefree.Sparse.keys entries := by
  simp [denoteTable,Squarefree.Sparse.keys,List.map_map,Function.comp_def]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

 theorem rawEntries_length_le (entries : List (List Bool × List Bool)) (W C : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C) :
    (Squarefree.Program.rawEntries entries).length ≤ entries.length * (2*W+2*C+2) := by
  induction entries with
  | nil => simp [Squarefree.Program.rawEntries]
  | cons a entries ih =>
    have h1 := hk a (by simp)
    have h2 := hc a (by simp)
    have h3 := ih (fun b hb => hk b (by simp [hb])) (fun b hb => hc b (by simp [hb]))
    simp only [Squarefree.Program.rawEntries,List.length_append,Encoding.length_frame,List.length_cons]
    nlinarith

theorem updatedBytes_length_le (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (W C : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C)
    (hq : query.length ≤ W) (hv : coeff.length ≤ C) :
    (updatedBytes entries query coeff).length ≤ (entries.length+1)*(2*W+2*C+2) := by
  have hn : (((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse)).length ≤ entries.length+1 := by
    simpa [Squarefree.Program.erasedEntries] using Nat.add_le_add_right
      (List.length_filter_le (fun a : List Bool × List Bool => decide (a.1 ≠ query)) entries) 1
  have hb := rawEntries_length_le ((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse) W C
    (by intro a ha; simp only [List.mem_cons,List.mem_reverse] at ha; rcases ha with rfl|ha; exact hq
        exact hk a (List.mem_filter.mp ha).1)
    (by intro a ha; simp only [List.mem_cons,List.mem_reverse] at ha; rcases ha with rfl|ha; exact hv
        exact hc a (List.mem_filter.mp ha).1)
  exact hb.trans (Nat.mul_le_mul_right _ hn)

/-- Total insertion work includes both full table scans, copied table bytes,
coefficient addition, and final replacement serialization. -/
theorem insertBudget_le (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (branch W C : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C)
    (hq : query.length ≤ W) (hv : coeff.length ≤ C) :
    insertBudget entries query coeff branch ≤ 200*(entries.length+1)*(W+C+1)+branch := by
  have hr := rawEntries_length_le entries W C hk hc
  have hu := updatedBytes_length_le entries query coeff W C hk hc hq hv
  have hl := Squarefree.Program.lookupBudget_bound query entries W C hk hc
  have he := Squarefree.Program.eraseBudget_bound query entries W C hk hc
  unfold insertBudget finishBudget
  nlinarith [Nat.mul_le_mul_left entries.length hq]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

theorem insertCode_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (Dictionary.insertCode p t M cache k x seed)).Nodup := by
  unfold Dictionary.insertCode
  have heq : Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed) =
      (Squarefree.Sparse.keys seed).filter (fun j => decide (j ≠ k)) := by
    clear hn
    induction seed with
    | nil => rfl
    | cons a seed ih =>
      by_cases h : a.1=k <;> simpa [Squarefree.Sparse.erase,Squarefree.Sparse.keys,h] using ih
  have he : (Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed)).Nodup := by
    rw [heq]
    exact hn.filter _
  have hnot : k ∉ Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed) := by
    rw [heq]
    simp
  simp only [Squarefree.Sparse.keys,List.map_cons,List.map_reverse]
  exact List.nodup_cons.mpr ⟨by simpa [Squarefree.Sparse.keys] using hnot,
    by simpa [Squarefree.Sparse.keys] using he⟩

theorem run_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (run p t M cache source seed)).Nodup := by
  induction source generalizing seed with
  | nil => exact hn
  | cons a source ih => exact ih _ (insertCode_nodup p t M cache a.1 a.2 seed hn)

theorem insertCode_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :
    (Dictionary.insertCode p t M cache k x seed).length ≤ seed.length+1 := by
  unfold Dictionary.insertCode
  have h := List.length_filter_le (fun a : K × RingProgram.Code (Word (baseWidth p t)) d => decide (a.1 ≠ k)) seed
  simpa [Squarefree.Sparse.erase] using Nat.add_le_add_right h 1

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

theorem insertCode_keyBound (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W : ℕ)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hk : (key k).length ≤ W) (hs : KeyBound key W seed) :
    KeyBound key W (Dictionary.insertCode p t M cache k x seed) := by
  intro a ha
  simp only [Dictionary.insertCode,List.mem_cons,List.mem_reverse] at ha
  rcases ha with rfl|ha
  · exact hk
  · exact hs a (List.mem_filter.mp ha).1

theorem stepBudget_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W : ℕ)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hk : (key k).length ≤ W) (hs : KeyBound key W seed) :
    stepBudget p t M cache key seed k x ≤
      220*(seed.length+1)*(W+d*baseWidth p t+1) + Dictionary.codeBranchBudget (baseWidth p t) d := by
  let value := match seed.lookup k with
    | none => x
    | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
  have hv : (RingProgram.flat value).length ≤ d*baseWidth p t := by rw [RingProgram.flat_length]
  have h := Dictionary.insertBudget_le (Squarefree.Program.encodeDictionary key RingProgram.flat seed)
    (key k) (RingProgram.flat value) (Dictionary.codeBranchBudget (baseWidth p t) d) W (d*baseWidth p t)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact hs b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2)) hk hv
  simp only [Squarefree.Program.encodeDictionary,List.length_map] at h
  change 6*(key k).length+11*(RingProgram.flat x).length+15+ _ ≤ _
  rw [RingProgram.flat_length]
  change Dictionary.insertBudget _ _ (RingProgram.flat value) _ ≤ _ at h
  dsimp only [value,Squarefree.Program.encodeDictionary] at h ⊢
  have hmul : 1 * (W + d * baseWidth p t + 1) ≤ (seed.length + 1) * (W + d * baseWidth p t + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  refine le_trans (Nat.add_le_add_left h _) ?_
  nlinarith [hmul, hk]

/-- A uniform polynomial bound for the complete runtime normalization loop. -/
theorem work_le (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (W N : ℕ)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hs : KeyBound key W source) (hi : KeyBound key W seed)
    (hn : source.length+seed.length ≤ N) :
    work p t M cache key source seed ≤ source.length *
      (220*(N+1)*(W+d*baseWidth p t+1) + Dictionary.codeBranchBudget (baseWidth p t) d + 2) + 1 := by
  induction source generalizing seed with
  | nil => simp [work]
  | cons a source ih =>
    have ha := hs a (by simp)
    have htail : KeyBound key W source := fun b hb => hs b (by simp [hb])
    have hnext := insertCode_keyBound p t M cache key W seed a.1 a.2 ha hi
    have hlen := insertCode_length p t M cache a.1 a.2 seed
    have hcap : source.length + (Dictionary.insertCode p t M cache a.1 a.2 seed).length ≤ N := by
      simp only [List.length_cons] at hn; omega
    have hrec := ih _ htail hnext hcap
    have hstep := stepBudget_le p t M cache key W seed a.1 a.2 ha hi
    have hsize : seed.length+1 ≤ N+1 := by simp only [List.length_cons] at hn; omega
    have hmul := Nat.mul_le_mul_right (W+d*baseWidth p t+1) (Nat.mul_le_mul_left 220 hsize)
    simp only [work,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramValidity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

namespace Normalize
variable {K : Type*} [DecidableEq K]

theorem insertCode_preserves_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (P : K → Prop) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hk : P k) (hs : ∀ a ∈ seed, P a.1) :
    ∀ a ∈ Dictionary.insertCode p t M cache k x seed, P a.1 := by
  intro a ha
  simp only [Dictionary.insertCode,List.mem_cons,List.mem_reverse] at ha
  rcases ha with rfl|ha
  · exact hk
  · exact hs a (List.mem_filter.mp ha).1

theorem run_preserves_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (P : K → Prop)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hs : ∀ a ∈ source, P a.1) (hi : ∀ a ∈ seed, P a.1) :
    ∀ a ∈ run p t M cache source seed, P a.1 := by
  induction source generalizing seed with
  | nil => exact hi
  | cons a source ih =>
    apply ih _ (fun b hb => hs b (by simp [hb]))
    exact insertCode_preserves_keys p t M cache P a.1 a.2 seed (hs a (by simp)) hi
end Normalize

namespace Product

theorem decoded_valid {R : Type*} [CommRing R] {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) (h : ∀ a ∈ entries, ValidKey vars u J a.1) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f entries) := by
  intro k hk
  simp only [Squarefree.Sparse.keys,Dictionary.denoteTable,List.map_map,Function.comp_def] at hk
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hk
  exact h a ha

end Product
end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/
section NativeValidity

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

theorem decoded_valid {R : Type*} [CommRing R]
    {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (f : RingProgram.Code (Word B) d → R) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f a) :=
  Product.decoded_valid f vars u J a h.valid

theorem length_le {a : List (Product.Entry n B d)} (h : Good vars u J a) :
    a.length ≤ u*J*(Squarefree.Sparse.supportUniverse vars J).card := by
  have hv := h.decoded_valid (fun _ => (0 : ℤ))
  have hn : (Squarefree.Sparse.keys (Dictionary.denoteTable (fun _ => (0 : ℤ)) a)).Nodup := by
    simpa only [Dictionary.denoteTable_keys] using h.nodup
  simpa only [Dictionary.denoteTable,List.length_map] using hv.length_le hn

end Good

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (vars : Finset (Fin n)) (u J : ℕ)

theorem normalize_good (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : ∀ x ∈ source, Product.ValidKey vars u J x.1) (hi : Good vars u J seed) :
    Good vars u J (Normalize.run p t M cache source seed) :=
  ⟨Normalize.run_preserves_keys p t M cache _ source seed hs hi.valid,
    Normalize.run_nodup p t M cache source seed hi.nodup⟩


end NativeValidity

variable {V R : Type*} [DecidableEq V] [CommRing R]

omit [DecidableEq V] in
/-- Empty formal support has at most one possible support, also when `J = 0`. -/
theorem empty_support_card_le (J : ℕ) :
    (Squarefree.Sparse.supportUniverse (∅ : Finset V) J).card ≤ 1 := by
  calc
    _ ≤ ((∅ : Finset V).powerset).card := Finset.card_filter_le _ _
    _ = 1 := by simp

theorem empty_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) : a.length ≤ u * J := by
  exact ha.length_le.trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (u * J)
      (empty_support_card_le (V := Fin n) J))

/-- Specialization can create equal keys; normalization accepts those collisions.
The source bound counts every emitted record, before equal keys are merged. -/
theorem normalization_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J N : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : ∀ x ∈ source, Product.ValidKey ∅ u J x.1)
    (hN : source.length ≤ N) (hseed : Good ∅ u J seed)
    (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let start := (Normalize.state regs M.bits width degree (Product.bytes seed)
      (Product.bytes source)).withPC (some Normalize.program.entry)
    let result := Normalize.run p t M cache source seed
    ∃ steps rr,
      steps ≤ normalizationBudget n (baseWidth p t) d u J N ∧
      Trace Normalize.program steps start
        ((Normalize.state rr M.bits width degree (Product.bytes result) []).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace Normalize.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + normalizationBudget n (baseWidth p t) d u J N := by
  dsimp only
  have hr := empty_length_le hseed
  have hs : Normalize.KeyBound Squarefree.encodeIndex (n + u + J) source := by
    intro x hx
    have h := Squarefree.encodeIndex_length_le x.1 (hsource x hx).1
    omega
  have hi : Normalize.KeyBound Squarefree.encodeIndex (n + u + J) seed := by
    intro x hx
    have h := Squarefree.encodeIndex_length_le x.1 (hseed.valid x hx).1
    omega
  have hc := Normalize.work_le p t M cache Squarefree.encodeIndex (n + u + J)
    (N + u * J) source seed hs hi (by omega)
  have hbudget : Normalize.work p t M cache Squarefree.encodeIndex source seed + 2 ≤
      normalizationBudget n (baseWidth p t) d u J N := by
    have hm := Nat.mul_le_mul_right
      (220 * (N + u * J + 1) * (n + u + J + d * baseWidth p t + 1) +
        Dictionary.codeBranchBudget (baseWidth p t) d + 2) hN
    unfold normalizationBudget
    omega
  obtain ⟨rr, steps, hsteps, htrace⟩ := Normalize.program_run p t M cache
    Squarefree.encodeIndex Squarefree.encodeIndex_injective source seed regs width degree hd hw
  have hb := hsteps.trans hbudget
  refine ⟨steps, rr, hb, htrace,
    normalize_good p t M cache ∅ u J source seed hsource hseed, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound Normalize.program le_rfl prefixSteps intermediate
    (hprefix.trans hb) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProducerSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization followed by the actual additive dictionary
normalizer. The input is a polynomial-size origin/singleton incidence stream;
no multivariate product is materialized before specialization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

theorem normalizePorts_injective : Function.Injective normalizePorts :=
  Fin.castAdd_injective _ _

theorem scanPorts_injective : Function.Injective scanPorts := by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

theorem scanRegisters_injective : Function.Injective scanRegisters :=
  Fin.castAdd_injective _ _

theorem scanOverlay_same (regs : Fin 8 → Bool) :
    scanOverlay regs (regs ∘ scanRegisters) = regs := by
  funext i
  by_cases hi : ∃ j, scanRegisters j = i
  · obtain ⟨j, rfl⟩ := hi
    exact scanRegisters_injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hi

theorem embed_scan (regs : Fin 8 → Bool) (rr : Fin 5 → Bool)
    (modulus width degree dict source : List Bool) (a b : MomentsProjectionProgram.Tape) :
    embedState scanRegisters scanPorts (state regs modulus width degree dict source a)
      (MomentsProjectionProgram.machine rr b) =
      state (scanOverlay regs rr) modulus width degree dict source b := by
  apply SubexpScanPrimitives.embedState_eq _ _ scanRegisters_injective scanPorts_injective
  · intro i
    exact scanRegisters_injective.extend_apply _ _ _
  · intro i
    simp [state, scanPorts, MomentsProjectionProgram.machine]
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i hi
    have hlt : i.val < 28 := by
      by_contra h
      let j : Fin 10 := ⟨i.val - 28, by omega⟩
      apply hi
      refine ⟨j, ?_⟩
      apply Fin.ext
      simp only [scanPorts, Fin.val_natAdd, j]
      omega
    let j : Fin 28 := ⟨i.val, hlt⟩
    have hj : normalizePorts j = i := Fin.ext rfl
    rw [← hj]
    simp [state, normalizePorts, Normalize.state, Normalize.extend, Dictionary.machine]

theorem embed_normalize (regs rr : Fin 8 → Bool)
    (modulus width degree dict source dict' source' : List Bool)
    (scan : MomentsProjectionProgram.Tape) :
    embedState id normalizePorts (state regs modulus width degree dict source scan)
      (Normalize.state rr modulus width degree dict' source') =
      state rr modulus width degree dict' source' scan := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id normalizePorts_injective
  · intro i
    rfl
  · intro i
    simp [state, normalizePorts]
  · intro i hi
    exact (hi ⟨i, rfl⟩).elim
  · intro i hi
    have hge : 28 ≤ i.val := by
      by_contra h
      apply hi
      exact ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    let j : Fin 10 := ⟨i.val - 28, by omega⟩
    have hj : scanPorts j = i := by
      apply Fin.ext
      simp only [scanPorts, Fin.val_natAdd, j]
      omega
    rw [← hj]
    simp [state, scanPorts]

/-- Both transfers are executed: the normalizer receives the original byte
order, while all handoff scratch is emptied. -/
theorem handoff_eval (regs : Fin 8 → Bool) (modulus width degree mask bits : List Bool) :
    Eval handoff (6 * bits.length + 6)
      (state regs modulus width degree [] [] {target := mask, framed := bits})
      (state (readRegs (readRegs regs 0 1 none) 0 1 none)
        modulus width degree [] bits {target := mask}) := by
  let a := state regs modulus width degree [] [] {target := mask, framed := bits}
  let b := SubexpScanPrimitives.afterTransfer a 37 36 0 1
  have h₁ := SubexpScanPrimitives.transfer_eval a 37 36 0 1 (by decide) (by decide)
  have h₂ := SubexpScanPrimitives.transfer_eval b 36 27 0 1 (by decide) (by decide)
  have hfinal : SubexpScanPrimitives.afterTransfer b 36 27 0 1 =
      state (readRegs (readRegs regs 0 1 none) 0 1 none)
        modulus width degree [] bits {target := mask} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;> first | rfl |
        simp [a, b, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
          state, Fin.addCases, Normalize.state, Normalize.extend, Dictionary.machine,
          Dictionary.outputTape, Dictionary.tapes, MomentsProjectionProgram.tapes, Fin.snoc, Fin.coe_ofNat_eq_mod]
  have h := h₁.seq h₂
  rw [hfinal] at h
  unfold handoff
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  have ha37 : (a.stacks 37).length = bits.length := by
    simp [a, state, MomentsProjectionProgram.tapes, Fin.addCases, Fin.coe_ofNat_eq_mod]
  have hb36 : (b.stacks 36).length = bits.length := by
    simp [b, a, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
      state, MomentsProjectionProgram.tapes, Fin.addCases, Fin.coe_ofNat_eq_mod]
  rw [ha37, hb36]
  omega

/-- Specialization retains only valid empty-support keys, allowing collisions
which the following actual normalizer adds in the coefficient ring. -/
theorem specialized_valid {n B d u J : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n B d))
    (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1) :
    ∀ a ∈ HeadEvaluation.specializeEntries U source, Product.ValidKey ∅ u J a.1 := by
  intro a ha
  obtain ⟨b, hb, _, rfl⟩ := HeadEvaluation.mem_specializeEntries U source a ha
  exact ⟨(hsource b hb).1, by simp [Squarefree.Index.Valid], by simp⟩

theorem specialized_bytes_length {n B d : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n B d)) :
    (Product.bytes (HeadEvaluation.specializeEntries U source)).length ≤
      (Product.bytes source).length := by
  induction source with
  | nil => rfl
  | cons a source ih =>
    by_cases h : a.1.vars ⊆ U <;>
      simp [HeadEvaluation.specializeEntries, h, Product.bytes, Normalize.bytes,
        Squarefree.Program.encodeDictionary, Squarefree.Program.rawEntries,
        Squarefree.encodeIndex] at * <;> omega

/-- A single finite program specializes raw records and normalizes equal keys.
Every stack at every prefix, including both copies and scalar caches, is charged. -/
theorem run_space_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J N : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n (baseWidth p t) d))
    (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1)
    (hN : source.length ≤ N) (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let result := Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []
    let start := state regs M.bits width degree [] []
      {input := Encoding.frame (Squarefree.encodeMask U) ++ Product.bytes source}
    ∃ steps rr, steps ≤ budget n (baseWidth p t) d u J N (Product.bytes source).length ∧
      Trace program steps (start.withPC (some program.entry))
        ((state rr M.bits width degree (Product.bytes result) []
          {target := (Squarefree.encodeMask U).reverse}).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (start.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits start.stacks +
          budget n (baseWidth p t) d u J N (Product.bytes source).length := by
  dsimp only
  let entries := source.map (fun a => (a.1, RingProgram.flat a.2))
  obtain ⟨scanSteps, hscanSteps, scanRegs, hscan, _⟩ :=
    HeadEvaluationProgram.Specialization.raw_dictionary_run_space U entries (regs ∘ scanRegisters)
  have hbytes : Squarefree.Program.rawEntries
      (entries.map (fun a => (Squarefree.encodeIndex a.1, a.2))) = Product.bytes source := by
    simp [entries, Product.bytes, Normalize.bytes, Squarefree.Program.encodeDictionary,
      List.map_map, Function.comp_def]
  have hselected : Squarefree.Program.rawEntries
      ((HeadEvaluation.specializeEntries U entries).map
        (fun a => (Squarefree.encodeIndex a.1, a.2))) =
      Product.bytes (HeadEvaluation.specializeEntries U source) := by
    rw [show entries = source.map (fun a => (a.1, RingProgram.flat a.2)) from rfl,
      HeadEvaluation.specializeEntries_map]
    simp [Product.bytes, Normalize.bytes, Squarefree.Program.encodeDictionary, List.map_map, Function.comp_def]
  rw [hbytes] at hscanSteps hscan
  rw [hselected] at hscan
  have hscanCall := eval_call_lifted HeadEvaluationProgram.Specialization.program
    scanRegisters scanPorts
    (state regs M.bits width degree [] []
      {input := Encoding.frame (Squarefree.encodeMask U) ++ Product.bytes source})
    scanRegisters_injective scanPorts_injective hscan
  rw [embed_scan, scanOverlay_same, embed_scan] at hscanCall
  let midRegs := scanOverlay regs scanRegs
  have hhand := handoff_eval midRegs M.bits width degree (Squarefree.encodeMask U).reverse
    (Product.bytes (HeadEvaluation.specializeEntries U source))
  let normRegs := readRegs (readRegs midRegs 0 1 none) 0 1 none
  obtain ⟨normSteps, rr, hnormSteps, hnorm, hgood, _⟩ :=
    TruncatedRingProgram.normalization_run_space p t M cache
      (HeadEvaluation.specializeEntries U source) [] (specialized_valid U source hsource)
      ((HeadEvaluation.specializeEntries_length U source).trans hN) Good.nil
      normRegs width degree hd hw
  have hnormCall := eval_call_lifted Normalize.program id normalizePorts
    (state normRegs M.bits width degree []
      (Product.bytes (HeadEvaluation.specializeEntries U source))
      {target := (Squarefree.encodeMask U).reverse})
    Function.injective_id normalizePorts_injective hnorm
  rw [embed_normalize, embed_normalize] at hnormCall
  have heval := hscanCall.seq (hhand.seq hnormCall)
  have hbound : scanSteps + (6 * (Product.bytes
      (HeadEvaluation.specializeEntries U source)).length + 6) + normSteps + 1 ≤
      budget n (baseWidth p t) d u J N (Product.bytes source).length := by
    have hlen := specialized_bytes_length U source
    unfold budget
    omega
  refine ⟨_, rr, hbound, ?_, hgood, ?_⟩
  · simpa [program, command, scanCall, normalizeCall, Nat.add_assoc] using
      compiled_halt_trace heval 28 15
  · intro prefixSteps intermediate hp ht i
    exact StructuredSpace.local_stack_bound program (steps :=
      budget n (baseWidth p t) d u J N (Product.bytes source).length)
      (by rfl) prefixSteps intermediate (hp.trans hbound) ht i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space_oai
