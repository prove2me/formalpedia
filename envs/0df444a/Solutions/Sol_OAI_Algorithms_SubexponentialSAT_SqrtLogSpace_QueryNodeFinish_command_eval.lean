-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:49:54.079124+00:00
-- url     : https://prove2.me/submissions/1863364d-08c1-4671-ba19-9764f9978061

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsReadoutProgram_program_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeIndex_length_le {n t J : ℕ} (a : Index (Fin n))
    (h : a.Kept t J) : (encodeIndex a).length ≤ t + J + n := by
  rw [encodeIndex_length]
  obtain ⟨hu, hz⟩ := h
  omega

end SubexponentialSAT.SqrtLog.Squarefree

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramValidity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem outputBits_length {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d) (z J : ℕ) :
    (outputBits p e M cache entries t zero z J).length=J*(d*baseWidth p e) := by
  induction J generalizing z with
  | zero => simp [outputBits,outputCodes]
  | succ J ih =>
      simp only [outputBits,outputCodes,List.map_cons,List.flatten_cons,List.length_append,
        RingProgram.flat_length] at *
      rw [ih]
      simp [Nat.succ_mul,Nat.add_comm]

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial accounting for all primitive readout loops. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem slotBudget_le (B d n t J W u z : ℕ)
    (entries : List (List Bool × List Bool))
    (hk : ∀ a∈entries, a.1.length ≤ W) (hc : ∀ a∈entries, a.2.length ≤ d*B)
    (hu : u ≤ t) (hz : z ≤ J) :
    slotBudget B d n u z entries ≤ uniformSlotBudget B d n t J W entries.length := by
  have hr := MomentsProgram.Dictionary.rawEntries_length_le entries W (d*B) hk hc
  have hl := Squarefree.Program.lookupBudget_bound
    (Squarefree.encodeIndex (⟨u,z,∅⟩ : Squarefree.Index (Fin n))) entries W (d*B) hk hc
  have hq : (Squarefree.encodeIndex (⟨u,z,∅⟩ : Squarefree.Index (Fin n))).length ≤ n+t+J+2 := by
    simp only [Squarefree.encodeIndex_length]
    omega
  have hmul := Nat.mul_le_mul_left entries.length hq
  have hinside : 35*W+31*(d*B)+9*(n+t+J)+76 ≤
      100*(W+d*B+n+t+J+3) := by omega
  have hscaled := Nat.mul_le_mul_left entries.length hinside
  have hrest : 9*(n+u+z)+62 ≤ 100*(W+d*B+n+t+J+3)+100 := by omega
  dsimp [slotBudget,accumulateBudget,fetchBudget,uniformSlotBudget]
  simp only [Squarefree.encodeIndex_length] at hl hq hmul
  nlinarith

theorem innerBudget_le (B d n t J W z u k : ℕ)
    (entries : List (List Bool × List Bool))
    (hk : ∀ a∈entries, a.1.length ≤ W) (hc : ∀ a∈entries, a.2.length ≤ d*B)
    (hu : u+k ≤ t) (hz : z ≤ J) :
    innerBudget B d n z entries u k ≤ k*(uniformSlotBudget B d n t J W entries.length+2)+2 := by
  induction k generalizing u with
  | zero => simp [innerBudget]
  | succ k ih =>
      have hs := slotBudget_le B d n t J W u z entries hk hc (by omega) hz
      have hi := ih (u+1) (by omega)
      simp only [innerBudget]
      nlinarith

theorem outerBudget_le (B d n t J W z k : ℕ)
    (entries : List (List Bool × List Bool))
    (hk : ∀ a∈entries, a.1.length ≤ W) (hc : ∀ a∈entries, a.2.length ≤ d*B)
    (hz : z+k ≤ J) :
    outerBudget B d n t entries z k ≤
      k*(t*(uniformSlotBudget B d n t J W entries.length+2)+10*(d*B)+9*t+22)+2 := by
  induction k generalizing z with
  | zero => simp [outerBudget]
  | succ k ih =>
      have hs := innerBudget_le B d n t J W z 0 t entries hk hc (by omega) (by omega)
      have hi := ih (z+1) (by omega)
      simp only [outerBudget,rowBudget]
      nlinarith

theorem readoutBudget_polynomial (B d n t J W : ℕ)
    (entries : List (List Bool × List Bool))
    (hk : ∀ a∈entries, a.1.length ≤ W) (hc : ∀ a∈entries, a.2.length ≤ d*B) :
    readoutBudget B d n t J entries+1 ≤ uniformReadoutBudget B d n t J W entries.length := by
  have h := outerBudget_le B d n t J W 0 J entries hk hc (by omega)
  dsimp [readoutBudget,uniformReadoutBudget]
  omega

theorem program_runsIn_polynomial {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count t J shape : List Bool) (W : ℕ)
    (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n)
    (hk : ∀ a∈entries, (Squarefree.encodeIndex a.1).length ≤ W) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let bits := outputBits p e M cache entries t.length zero 0 J.length
    ∃ rr, RunsIn program (uniformReadoutBudget (baseWidth p e) d n t.length J.length W entries.length)
      ((wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
        (inputHigh (RingProgram.flat zero) t J shape)).withPC (some program.entry))
      ((wideState rr {MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [] with out:=bits}
        (inputHigh (RingProgram.flat zero) t J shape)).withPC none) := by
  dsimp only
  let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
  have hk' : ∀ a∈encoded, a.1.length ≤ W := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact hk x hx
  have hc' : ∀ a∈encoded, a.2.length ≤ d*baseWidth p e := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    simp [RingProgram.flat_length]
  have hb := readoutBudget_polynomial (baseWidth p e) d n t.length J.length W encoded hk' hc'
  have hl : encoded.length=entries.length := by simp [encoded,Squarefree.Program.encodeDictionary]
  rw [hl] at hb
  obtain ⟨rr,tm,ht,he⟩ := program_runsIn p e M cache entries zero regs width count t J shape hc hw hs
  exact ⟨rr,tm,ht.trans hb,he⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

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

/-- The readout uses only `u * J` records and returns exactly `J` coefficient words. -/
theorem readout_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let start := (MomentsReadoutProgram.wideState regs
      (Dictionary.inputTape M.bits width degree encoded [] [])
      (MomentsReadoutProgram.inputHigh (RingProgram.flat zero) marker taylor shape)).withPC
        (some MomentsReadoutProgram.program.entry)
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    let budget := MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J
      (n + u + J) (u * J)
    ∃ steps rr,
      steps ≤ budget ∧
      Trace MomentsReadoutProgram.program steps start
        ((MomentsReadoutProgram.wideState rr
          {Dictionary.inputTape M.bits width degree encoded [] [] with out := bits}
          (MomentsReadoutProgram.inputHigh (RingProgram.flat zero) marker taylor shape)).withPC none) ∧
      bits.length = J * (d * baseWidth p t) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace MomentsReadoutProgram.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤ dataBits start + budget := by
  dsimp only
  obtain ⟨rr, steps, hsteps, htrace⟩ :=
    MomentsReadoutProgram.program_runsIn_polynomial p t M cache entries zero regs width degree
      marker taylor shape (n + u + J) hd hw hs (by
        intro a ha
        have h := Squarefree.encodeIndex_length_le a.1 (he.valid a ha).1
        omega)
  rw [hu, hJ] at hsteps htrace
  have hbudget : MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J
      (n + u + J) entries.length ≤
      MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J (n + u + J) (u * J) := by
    have hlen := empty_length_le he
    dsimp [MomentsReadoutProgram.uniformReadoutBudget, MomentsReadoutProgram.uniformSlotBudget]
    gcongr
  have hb := hsteps.trans hbudget
  refine ⟨steps, rr, hb, htrace, MomentsReadoutProgram.outputBits_length _ _ _ _ _ _ _ _ _, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound MomentsReadoutProgram.program le_rfl prefixSteps intermediate
    (hprefix.trans hb) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _

private theorem portIndex_ports (i : Fin 40) : portIndex (ports i).val = i.val := by
  fin_cases i <;> rfl

theorem ports_injective : Function.Injective ports := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun k : Fin 896 => portIndex k.val) h
  simpa only [portIndex_ports] using hv

theorem mem_scratchIndices (i : Fin 40) : i ∈ scratchIndices ↔
    i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
      i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36 := by
  simp only [scratchIndices, List.mem_filter, List.mem_ofFn, exists_eq,
    decide_eq_true_eq, true_and]

theorem scratchPorts_low {i : Fin 896} (hi : i ∈ scratchPorts) :
    88 ≤ i.val ∧ i.val < 128 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩ := (mem_scratchIndices j).mp hj
  simp only [ports, h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  omega

theorem clearPorts_length : clearPorts.length ≤ 41 := by
  have h := List.length_filter_le
    (p := fun i : Fin 40 => decide
      (i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
        i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36)) (l := List.ofFn (fun i : Fin 40 => i))
  simpa only [clearPorts, scratchPorts, scratchIndices, List.length_cons,
    List.length_map, List.length_ofFn] using Nat.succ_le_succ h

theorem clearOne_eval (i : Fin 896) (a : Data) :
    Eval (clearOne i) (2 * (a.stacks i).length + 3) a (cleared i a) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem clearMany_eval (ps : List (Fin 896)) (a : Data) :
    Eval (clearMany ps) (clearCost ps a) a (clearedMany ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih => exact (clearOne_eval p a).seq (ih _)

theorem clearCost_le (ps : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : clearCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearCost]
  | cons p ps ih =>
      have hb : ∀ i, ((cleared p a).stacks i).length ≤ B := by
        intro i
        by_cases hi : i = p
        · subst i; simp [cleared]
        · simpa [cleared, hi] using ha i
      have ht := ih (cleared p a) hb
      have hp := ha p
      simp only [clearCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem localState_stack (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape output : List Bool) (i : Fin 40) :
    (localState rr modulus width degree dictionary zero marker taylor shape output).stacks i =
      if i = 0 then output else if i = 5 then modulus else if i = 12 then width
      else if i = 15 then dictionary else if i = 24 then degree else if i = 27 then zero
      else if i = 28 then marker else if i = 29 then taylor else if i = 36 then shape else [] := by
  fin_cases i <;> rfl

theorem clearedMany_frame (a : Data) (i : Fin 896) (hi : i ∉ clearPorts) :
    (clearedMany clearPorts a).stacks i = a.stacks i := by
  rw [clearedMany_stack, ite_eq_right hi]

theorem prepared_eq (a : Data)
    (modulus width degree dictionary zero marker taylor shape : List Bool)
    (h : Ready a modulus width degree dictionary zero marker taylor shape) :
    let b := clearedMany clearPorts a
    embedState registers ports b
      (localState (fun i => b.regs (registers i))
        modulus width degree dictionary zero marker taylor shape []) = b := by
  dsimp only
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
  · intro i; rfl
  · intros; rfl
  · intro i
    rw [localState_stack]
    by_cases h0 : i = 0
    · subst i
      simp [ports, clearedMany_stack,
        show (862 : Fin 896) ∈ clearPorts from List.mem_cons_self]
    by_cases h5 : i = 5
    · subst i
      simpa [ports, clearedMany_frame a 5 (by decide)] using h.modulus
    by_cases h12 : i = 12
    · subst i
      simpa [ports, clearedMany_frame a 12 (by decide)] using h.width
    by_cases h15 : i = 15
    · subst i
      simpa [ports, clearedMany_frame a 850 (by decide)] using h.dictionary
    by_cases h24 : i = 24
    · subst i
      simpa [ports, clearedMany_frame a 39 (by decide)] using h.degree
    by_cases h27 : i = 27
    · subst i
      simpa [ports, clearedMany_frame a 280 (by decide)] using h.zero
    by_cases h28 : i = 28
    · subst i
      simpa [ports, clearedMany_frame a 212 (by decide)] using h.marker
    by_cases h29 : i = 29
    · subst i
      simpa [ports, clearedMany_frame a 243 (by decide)] using h.taylor
    by_cases h36 : i = 36
    · subst i
      simpa [ports, clearedMany_frame a 128 (by decide)] using h.shape
    have hm : ports i ∈ scratchPorts := List.mem_map.mpr
      ⟨i, (mem_scratchIndices i).mpr ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩, rfl⟩
    have hmc : ports i ∈ clearPorts := List.mem_cons_of_mem 862 hm
    rw [clearedMany_stack, ite_eq_left hmc]
    simp only [h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  · intros; rfl

theorem result_output (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 862 = bits := by
  change (embedState registers ports _ _).stacks (ports 0) = bits
  rw [embedState_stack _ _ _ _ ports_injective]
  rfl

theorem result_stack (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      if i = 862 then bits else (clearedMany clearPorts a).stacks i := by
  by_cases hi : ∃ j, ports j = i
  · obtain ⟨j, rfl⟩ := hi
    change (embedState registers ports _ _).stacks (ports j) = _
    rw [embedState_stack _ _ _ _ ports_injective]
    by_cases hj : j = 0
    · subst j
      simp only [localState_stack, ports, ↓reduceIte]
    have hn : ports j ≠ 862 := fun h => hj (ports_injective (show ports j = ports 0 from h))
    rw [ite_eq_right hn]
    have hp := congrArg (fun d : Data => d.stacks (ports j))
      (prepared_eq a modulus width degree dictionary zero marker taylor shape hr)
    rw [embedState_stack _ _ _ _ ports_injective] at hp
    rw [← hp]
    simp only [localState_stack, hj, ite_false]
  · have hn : i ≠ 862 := fun h => hi ⟨0, (show ports 0 = 862 from rfl).trans h.symm⟩
    change (embedState registers ports _ _).stacks i = _
    rw [embedState_stack_frame _ _ _ _ i hi, ite_eq_right hn]

/-- All input masters and other high query buffers survive exactly. -/
theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (ho : i ≠ 862) (hs : i ∉ scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  rw [result_stack a rr _ _ _ _ _ _ _ _ _ hr i, ite_eq_right ho, clearedMany_stack]
  exact ite_eq_right (by simpa only [clearPorts, List.mem_cons, not_or] using And.intro ho hs)

theorem result_scratch (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (hs : i ∈ scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i = [] := by
  have ho : i ≠ 862 := by
    have := scratchPorts_low hs
    intro h
    subst i
    change 88 ≤ 862 ∧ 862 < 128 at this
    omega
  rw [result_stack a rr _ _ _ _ _ _ _ _ _ hr i, ite_eq_right ho, clearedMany_stack]
  exact ite_eq_left (List.mem_cons_of_mem 862 hs)

theorem result_bound (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (bound : ℕ) (ha : ∀ i, (a.stacks i).length ≤ bound) (hb : bits.length ≤ bound) :
    ∀ i, ((result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i).length ≤ bound := by
  intro i
  rw [result_stack a rr _ _ _ _ _ _ _ _ _ hr i]
  by_cases ho : i = 862
  · simpa only [ite_eq_left ho] using hb
  rw [ite_eq_right ho, clearedMany_stack]
  by_cases hc : i ∈ clearPorts
  · simp only [ite_eq_left hc, List.length_nil, Nat.zero_le]
  · simpa only [ite_eq_right hc] using ha i

/-- One fixed instruction sequence clears scratch and performs the actual readout. -/
theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : Ready a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps + 1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a
        (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits) ∧ bits.length = J * (d * baseWidth p t) := by
  dsimp only
  let b := clearedMany clearPorts a
  obtain ⟨steps, rr, hb, ht, hl, _⟩ := readout_run_space p t M cache entries he zero
    (fun i => b.regs (registers i)) width degree marker taylor shape hd hw hu hJ hs
  have call := eval_call_lifted MomentsReadoutProgram.program registers ports b
    registers_injective ports_injective ht
  change Eval _ steps
    (embedState registers ports b
      (localState (fun i => b.regs (registers i)) M.bits width degree (Product.bytes entries)
        (RingProgram.flat zero) marker taylor shape []))
    (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape _) at call
  rw [prepared_eq a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
    marker taylor shape hr] at call
  refine ⟨clearCost clearPorts a + steps, rr, ?_, (clearMany_eval clearPorts a).seq call, hl⟩
  have hc := (clearCost_le clearPorts a incoming ha).trans
    (Nat.mul_le_mul_right _ clearPorts_length)
  unfold budget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeAppendSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem transfer_eval (src dst : Fin 896) (h : src ≠ dst) (a : Data) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a (transferred src dst a) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 h (by decide) a.regs a.stacks)

theorem append_eval (a : Data) (hs : a.stacks 89 = []) :
    Eval append (appendCost a) a (appendResult a) := by
  have h1 := transfer_eval 863 89 (by decide) a
  have h2 := transfer_eval 862 89 (by decide) (transferred 863 89 a)
  have h3 := transfer_eval 89 863 (by decide) (transferred 862 89 (transferred 863 89 a))
  convert h1.seq (h2.seq h3) using 1
  · rfl
  · simp [appendCost, transferred, StackRoutines.transferStacks, hs]
    omega
  · rfl

theorem appendResult_stacks (a : Data) (hs : a.stacks 89 = []) :
    (appendResult a).stacks = Function.update (Function.update
      (Function.update a.stacks 863 (a.stacks 863 ++ a.stacks 862)) 862 []) 89 [] := by
  funext i
  by_cases h863 : i = 863
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  by_cases h862 : i = 862
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  by_cases h89 : i = 89
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  simp [appendResult, transferred, StackRoutines.transferStacks, h863, h862, h89]

theorem copy_eval (src dst : Fin 896) (a : Data)
    (hsd : src ≠ dst) (hst : src ≠ 89) (htd : (89 : Fin 896) ≠ dst)
    (ht : a.stacks 89 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied src dst a) :=
  .call _ (ListRegisterProgram.copy_run src dst 89 0 1 hsd hst htd (by decide) a.regs a.stacks ht)

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) := by
  let b := NodeReadoutSpace.clearedMany [89,5,12,39] a
  have hc := NodeReadoutSpace.clearMany_eval [89,5,12,39] a
  have h1 := copy_eval 194 5 b (by decide) (by decide) (by decide)
    (by simp [b, NodeReadoutSpace.clearedMany_stack])
  have h2 := copy_eval 202 12 (copied 194 5 b) (by decide) (by decide) (by decide)
    (by simp [copied, StackRoutines.copyStacks, b, NodeReadoutSpace.clearedMany_stack])
  have h3 := copy_eval 204 39 (copied 202 12 (copied 194 5 b)) (by decide) (by decide) (by decide)
    (by simp [copied, StackRoutines.copyStacks, b, NodeReadoutSpace.clearedMany_stack])
  convert hc.seq (h1.seq (h2.seq h3)) using 1
  · rfl
  · simp [prepareCost, copied, StackRoutines.copyStacks, b,
      NodeReadoutSpace.clearedMany_stack]
    omega
  · rfl

theorem prepared_stacks (a : Data) (i : Fin 896) :
    (prepared a).stacks i = if i = 5 then a.stacks 194 else if i = 12 then a.stacks 202
      else if i = 39 then a.stacks 204 else if i = 89 then [] else a.stacks i := by
  by_cases h5 : i = 5
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h12 : i = 12
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h39 : i = 39
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h89 : i = 89
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack,
    h5, h12, h39, h89]

theorem prepareCost_le (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    prepareCost a ≤ 29 * B + 27 := by
  have hc := NodeReadoutSpace.clearCost_le [89,5,12,39] a B ha
  have h194 := ha 194
  have h202 := ha 202
  have h204 := ha 204
  simp only [List.length_cons, List.length_nil] at hc
  unfold prepareCost
  omega

theorem prepared_bound (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((prepared a).stacks i).length ≤ B := by
  intro i
  rw [prepared_stacks]
  split_ifs <;> first | exact ha _ | exact Nat.zero_le _

theorem prepared_ready (a : Data)
    (modulus width degree dictionary zero marker taylor shape : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    NodeReadoutSpace.Ready (prepared a) modulus width degree dictionary zero marker taylor shape := by
  constructor
  · simpa [prepared_stacks] using hr.modulus
  · simpa [prepared_stacks] using hr.width
  · simpa [prepared_stacks] using hr.degree
  · simpa [prepared_stacks] using hr.dictionary
  · simpa [prepared_stacks] using hr.zero
  · simpa [prepared_stacks] using hr.marker
  · simpa [prepared_stacks] using hr.taylor
  · simpa [prepared_stacks] using hr.shape



theorem appendResult_bound (a : Data) (B : ℕ) (hs : a.stacks 89 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + (a.stacks 862).length ≤ B) :
    ∀ i, ((appendResult a).stacks i).length ≤ B := by
  intro i
  rw [appendResult_stacks a hs]
  by_cases h89 : i = 89
  · subst i; simp
  by_cases h862 : i = 862
  · subst i; simp
  by_cases h863 : i = 863
  · subst i; simpa using hout
  simpa [Function.update_of_ne h89, Function.update_of_ne h862,
    Function.update_of_ne h863] using ha i

theorem readout_scratch (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (NodeReadoutSpace.result (prepared a) rr modulus width degree dictionary zero
      marker taylor shape bits).stacks 89 = [] :=
  NodeReadoutSpace.result_scratch _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) 89 (by decide)

theorem readout_stream (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (NodeReadoutSpace.result (prepared a) rr modulus width degree dictionary zero
      marker taylor shape bits).stacks 863 = a.stacks 863 := by
  rw [NodeReadoutSpace.result_frame _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) 863 (by decide) (by decide)]
  simp [prepared_stacks]

theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (h5 : i ≠ 5) (h12 : i ≠ 12) (h39 : i ≠ 39)
    (h862 : i ≠ 862) (h863 : i ≠ 863) (hs : i ∉ NodeReadoutSpace.scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  have h89 : i ≠ 89 := by
    intro hi
    subst i
    exact hs (by decide)
  unfold result
  rw [appendResult_stacks _ (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)]
  simp only [Function.update_of_ne h89, Function.update_of_ne h862, Function.update_of_ne h863]
  rw [NodeReadoutSpace.result_frame _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) i h862 hs]
  simp only [prepared_stacks, h5, h12, h39, h89, ite_false]

theorem result_bound (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape)
    (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + bits.length ≤ B) :
    ∀ i, ((result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i).length ≤ B := by
  apply appendResult_bound _ B (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)
  · exact NodeReadoutSpace.result_bound _ rr _ _ _ _ _ _ _ _ _
      (prepared_ready a _ _ _ _ _ _ _ _ hr) B (prepared_bound a B ha) (by omega)
  · rw [readout_stream a rr _ _ _ _ _ _ _ _ _ hr, NodeReadoutSpace.result_output]
    exact hout


/-- This fixed command includes the actual cache copies, native readout and all
three transfers. No staging or concatenation service is assumed. -/
theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : MasterReady a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps + 1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a
        (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits) ∧ bits.length = J * (d * baseWidth p t) := by
  dsimp only
  obtain ⟨steps, rr, hb, ht, hl⟩ := NodeReadoutSpace.command_eval p t M cache entries he zero
    width degree marker taylor shape hd hw hu hJ hs (prepared a) incoming
    (prepared_bound a incoming ha) (prepared_ready a _ _ _ _ _ _ _ _ hr)
  have heval := (prepare_eval a).seq (ht.seq (append_eval _
    (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)))
  refine ⟨_, rr, ?_, heval, hl⟩
  have hp := prepareCost_le a incoming ha
  have hslen := ha 863
  simp only [appendCost, readout_stream a rr _ _ _ _ _ _ _ _ _ hr,
    NodeReadoutSpace.result_output, hl]
  unfold budget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem guardCursor_eval (a : Data) : Eval guardCursor 1 a (guarded a) :=
  .base (.atom (.peek 301 37 38) a)

theorem advanceIndex_eval (a : Data) : Eval advanceIndex 2 a (advanced a) := by
  have he := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 40) true) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (307 : Fin 896) 0) _))
  simpa [advanceIndex,advanced,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using he

theorem finishNode_eval (a : Data) : Eval finishNode (finishNodeCost a) a (finished a) := by
  have he := (NodeReadoutSpace.clearMany_eval [78,850] a).seq
    ((advanceIndex_eval _).seq (guardCursor_eval _))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first
  | rfl
  | (simp [finishNodeCost,NodeReadoutSpace.clearCost,NodeReadoutSpace.cleared]; omega)

theorem finished_stacks (a : Data) : (finished a).stacks =
    Function.update (Function.update (Function.update a.stacks 78 []) 850 [])
      307 (true::a.stacks 307) := by
  funext i
  by_cases h307 : i=307
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  by_cases h850 : i=850
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  by_cases h78 : i=78
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack,h307,h850,h78]

theorem finished_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B)
    (hx : (a.stacks 307).length+1 ≤ B) : ∀ i,((finished a).stacks i).length ≤ B := by
  intro i
  rw [finished_stacks]
  by_cases h307 : i=307
  · subst i
    simpa using hx
  by_cases h850 : i=850
  · subst i
    simp
  by_cases h78 : i=78
  · subst i
    simp
  simpa [Function.update_of_ne h307,Function.update_of_ne h850,Function.update_of_ne h78] using hb i

theorem result_bound (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + bits.length ≤ B)
    (hx : (a.stacks 307).length + 1 ≤ B) :
    ∀ i, ((result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i).length
      ≤ B := by
  apply finished_bound _ B (NodeAppendSpace.result_bound a rr _ _ _ _ _ _ _ _ _ hr B ha hout)
  rw [NodeAppendSpace.result_frame a rr _ _ _ _ _ _ _ _ _ hr 307
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact hx

/-- Actual scalar caches and a Good empty-support node array suffice for the
whole readout, ordered append, cleanup, index update and fresh guard. -/
theorem command_eval_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : NodeAppendSpace.MasterReady a M.bits width degree (Product.bytes entries)
      (RingProgram.flat zero) marker taylor shape)
    (hout : (a.stacks 863).length + J * (d * baseWidth p t) ≤ incoming)
    (hx : (a.stacks 307).length + 1 ≤ incoming) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps + 1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a
        (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits) ∧
      bits.length = J * (d * baseWidth p t) ∧
      (∀ i, ((result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
        marker taylor shape bits).stacks i).length ≤ incoming) := by
  dsimp only
  obtain ⟨steps, rr, hb, first, hl⟩ := NodeAppendSpace.command_eval p t M cache entries he zero
    width degree marker taylor shape hd hw hu hJ hs a incoming ha hr
  have hout' : (a.stacks 863).length +
      (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J).length ≤ incoming := by
    simpa only [hl] using hout
  have ha' := NodeAppendSpace.result_bound a rr _ _ _ _ _ _ _ _ _ hr incoming ha hout'
  have h78 := ha' 78
  have h850 := ha' 850
  refine ⟨_, rr, ?_, first.seq (finishNode_eval _), hl,
    result_bound a rr _ _ _ _ _ _ _ _ _ hr incoming ha hout' hx⟩
  unfold budget finishNodeCost
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval_oai
