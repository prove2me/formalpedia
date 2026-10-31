-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:47:44.117469+00:00
-- url     : https://prove2.me/submissions/a10c83e7-395f-4c1c-8df9-81254b87eccb

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Normalize_program_run
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEnvironment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The seven fixed persistent cache words are physically copied into the
native arithmetic environment. Cleanup clears those seven copies; both
commands frame all other stacks, including the query buffers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment

open OAI BitProgram StructuredCalls
open SubexpSetupStorage SqrtLog.MomentsProgram

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetResult a) := by
  have he := clearMany_eval environmentPorts (projectState registerMap id a)
  exact eval_liftCommand_from_state reset16 5 5 registerMap id a
    (Fin.castAdd_injective 16 24) Function.injective_id he

private theorem embed_identity_stacks (a : Data) (b : State 16 896) :
    (embedState registerMap id a b).stacks = b.stacks := by
  funext i
  exact Function.injective_id.extend_apply b.stacks a.stacks i

theorem reset_stacks (a : Data) (i : Fin 896) :
    (resetResult a).stacks i = if i ∈ environmentPorts then [] else a.stacks i := by
  rw [resetResult, embed_identity_stacks, clearMany_stacks]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
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

/-- Native addition normalizes one bounded array into another bounded array. -/
theorem addition_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let start := (Normalize.state regs M.bits width degree (Product.bytes seed)
      (Product.bytes source)).withPC (some Normalize.program.entry)
    let result := Normalize.run p t M cache source seed
    ∃ steps rr,
      steps ≤ additionBudget n (baseWidth p t) d u J ∧
      Trace Normalize.program steps start
        ((Normalize.state rr M.bits width degree (Product.bytes result) []).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace Normalize.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + additionBudget n (baseWidth p t) d u J := by
  dsimp only
  have hl := empty_length_le hsource
  have hr := empty_length_le hseed
  have hbound : ∀ a : List (Product.Entry n (baseWidth p t) d), Good ∅ u J a →
      Normalize.KeyBound Squarefree.encodeIndex (n + u + J) a := by
    intro a ha x hx
    have h := Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1
    omega
  have hc := Normalize.work_le p t M cache Squarefree.encodeIndex (n + u + J)
    (2 * (u * J)) source seed (hbound source hsource) (hbound seed hseed) (by omega)
  have hbudget : Normalize.work p t M cache Squarefree.encodeIndex source seed + 2 ≤
      additionBudget n (baseWidth p t) d u J := by
    have hm := Nat.mul_le_mul_right
      (220 * (2 * (u * J) + 1) * (n + u + J + d * baseWidth p t + 1) +
        Dictionary.codeBranchBudget (baseWidth p t) d + 2) hl
    unfold additionBudget
    omega
  obtain ⟨rr, steps, hsteps, htrace⟩ := Normalize.program_run p t M cache
    Squarefree.encodeIndex Squarefree.encodeIndex_injective source seed regs width degree hd hw
  have hb := hsteps.trans hbudget
  refine ⟨steps, rr, hb, htrace,
    normalize_good p t M cache ∅ u J source seed hsource.valid hseed, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound Normalize.program le_rfl prefixSteps intermediate
    (hprefix.trans hb) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram

theorem additionRegisters_injective : Function.Injective additionRegisters :=
  Fin.castAdd_injective _ _

theorem additionStacks_injective : Function.Injective additionStacks := by decide

/-- The local projection uses the actual product idle layout left by the
factor interpreter; no array is copied and no layout service is assumed. -/
theorem addition_project (a : Data) (modulus width zero table degree uCap zCap : List Bool)
    (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle modulus width zero table degree uCap zCap) i)
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = []) :
    projectState additionRegisters additionStacks a =
      Normalize.state (a.regs ∘ additionRegisters) modulus width degree
        (a.stacks 853) (a.stacks 854) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    have hl := hlow (if i = 24 then 39 else Fin.castAdd 28 i)
    fin_cases i <;> first | rfl | exact hs0 | exact hs1 | exact hl

private theorem normalize_stacks_update (regs rr : Fin 8 → Bool)
    (modulus width degree seed source result : List Bool) :
    (Normalize.state rr modulus width degree result []).stacks =
      Function.update (Function.update
        (Normalize.state regs modulus width degree seed source).stacks 15 result) 27 [] := by
  first | done | (funext i; fin_cases i <;> rfl)

/-- One concrete dense addition preserves every caller stack except the two
named arrays. Its local temporary growth is polynomial in their bounded size. -/
theorem add_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a : Data) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hp : projectState additionRegisters additionStacks a =
      Normalize.state (a.regs ∘ additionRegisters) M.bits width degree
        (Product.bytes seed) (Product.bytes source)) :
    let result := Normalize.run p t M cache source seed
    ∃ steps e, steps ≤ additionBudget n (baseWidth p t) d u J ∧
      Eval add steps a e ∧ Good ∅ u J result ∧
      e.stacks = Function.update (Function.update a.stacks 853 (Product.bytes result)) 854 [] := by
  dsimp only
  obtain ⟨steps, rr, hb, ht, hg, _⟩ := addition_run_space p t M cache source seed
    hsource hseed (a.regs ∘ additionRegisters) width degree hd hw
  rw [← hp] at ht
  let e := embedState additionRegisters additionStacks a
    (Normalize.state rr M.bits width degree (Product.bytes (Normalize.run p t M cache source seed)) [])
  refine ⟨steps, e, hb, eval_call_from_state Normalize.program additionRegisters
    additionStacks a additionRegisters_injective additionStacks_injective ht, hg, ?_⟩
  have hs := normalize_stacks_update (a.regs ∘ additionRegisters) rr M.bits width degree
    (Product.bytes seed) (Product.bytes source) (Product.bytes (Normalize.run p t M cache source seed))
  have hproject := congrArg StructuredProgram.State.stacks hp
  change Function.extend additionStacks
    (Normalize.state rr M.bits width degree
      (Product.bytes (Normalize.run p t M cache source seed)) []).stacks a.stacks = _
  rw [hs, ← hproject, ProgramLinking.extend_update additionStacks_injective,
    ProgramLinking.extend_update additionStacks_injective]
  change Function.update (Function.update
    (embedState additionRegisters additionStacks a
      (projectState additionRegisters additionStacks a)).stacks
    853 (Product.bytes (Normalize.run p t M cache source seed))) 854 [] = _
  rw [embedState_project additionRegisters additionStacks a
    additionRegisters_injective additionStacks_injective]


theorem accumulate_eval_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a : Data) (width degree zero table uCap zCap : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i)
    (hseedWord : a.stacks 853 = Product.bytes seed)
    (hsourceWord : a.stacks 854 = Product.bytes source)
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = []) :
    let result := Normalize.run p t M cache source seed
    let budget := additionBudget n (baseWidth p t) d u J + FactorEnvironment.resetCost a
    ∃ steps e, steps ≤ budget ∧ Eval accumulate steps a e ∧ Good ∅ u J result ∧
      e.stacks = Function.update (Function.update (FactorEnvironment.resetResult a).stacks
        853 (Product.bytes result)) 854 [] ∧
      (∀ i : Fin 56, e.stacks (Fin.castAdd 840 i) = []) ∧
      ∀ q z, q ≤ steps + 1 → Trace (compiled accumulate 854 853) q
        (a.withPC (some (compiled accumulate 854 853).entry)) z →
        dataBits z ≤ stackBits a.stacks + budget + 1 := by
  dsimp only
  have hp := addition_project a M.bits width zero table degree uCap zCap hlow hs0 hs1
  rw [hseedWord, hsourceWord] at hp
  obtain ⟨steps, e, hb, he, hg, hs⟩ := add_eval p t M cache source seed hsource hseed
    a width degree hd hw hp
  have henv : FactorEnvironment.resetCost e = FactorEnvironment.resetCost a := by
    simp [FactorEnvironment.resetCost, FactorEnvironment.environmentPorts,
      SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, projectState, hs]
  have hframe : (FactorEnvironment.resetResult e).stacks =
      Function.update (Function.update (FactorEnvironment.resetResult a).stacks
        853 (Product.bytes (Normalize.run p t M cache source seed))) 854 [] := by
    funext i
    rw [FactorEnvironment.reset_stacks, hs]
    by_cases h853 : i = 853
    · subst i; simp [FactorEnvironment.environmentPorts]
    by_cases h854 : i = 854
    · subst i; simp [FactorEnvironment.environmentPorts]
    simp [h853, h854, FactorEnvironment.reset_stacks]
  have hlowe : ∀ i : Fin 56, e.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i := by
    intro i
    have h853 : Fin.castAdd 840 i ≠ (853 : Fin 896) := by
      intro h; have hx : i.val = 853 := congrArg Fin.val h; have := i.isLt; omega
    have h854 : Fin.castAdd 840 i ≠ (854 : Fin 896) := by
      intro h; have hx : i.val = 854 := congrArg Fin.val h; have := i.isLt; omega
    simpa [hs, h853, h854] using hlow i
  refine ⟨steps + FactorEnvironment.resetCost e, FactorEnvironment.resetResult e,
    by omega, he.seq (FactorEnvironment.reset_eval e), hg, hframe, ?_, ?_⟩
  · intro i
    rw [FactorEnvironment.reset_stacks, hlowe]
    fin_cases i <;> rfl
  intro q z hq hz
  have ht := trace_dataBits (compiled accumulate 854 853) hz
  change dataBits z ≤ stackBits a.stacks + q at ht
  omega


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval_oai
