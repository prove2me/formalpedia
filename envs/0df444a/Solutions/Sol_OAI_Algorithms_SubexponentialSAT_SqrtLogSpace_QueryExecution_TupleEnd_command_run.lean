-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:47:28.3717+00:00
-- url     : https://prove2.me/submissions/9cecf9b3-5cf5-4847-9b7e-8c1c6531e44b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Normalize_program_run
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem bytes_length_le {n B d : ℕ} (entries : List (Entry n B d)) (W : ℕ)
    (h : Normalize.KeyBound Squarefree.encodeIndex W entries) :
    (bytes entries).length ≤ entries.length*(2*W+2*(d*B)+2) := by
  have hh := Dictionary.rawEntries_length_le
    (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) W (d*B)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact h b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2))
  simpa [bytes,Normalize.bytes,Squarefree.Program.encodeDictionary] using hh

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

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

theorem empty_bytes_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) :
    (Product.bytes a).length ≤ u * J * (2 * (u + J + n) + 2 * (d * B) + 2) := by
  exact (Product.bytes_length_le a (u + J + n)
    (fun x hx => Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1)).trans
      (Nat.mul_le_mul_right _ (empty_length_le ha))

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

theorem clear_eval (ports : List (Fin 896)) (a : Data) :
    Eval (clearBank ports) (clearCost ports a) a (cleared ports a) :=
  eval_liftCommand_from_state (clearMany ports) 841 841
    FactorAssignmentProgram.localRegister id a (Fin.castAdd_injective _ _)
    Function.injective_id (clearMany_eval ports _)

theorem cleared_stacks (ports : List (Fin 896)) (a : Data) (i : Fin 896) :
    (cleared ports a).stacks i = if i ∈ ports then [] else a.stacks i := by
  exact (embedState_stack FactorAssignmentProgram.localRegister id a
    (clearManyState ports (projectState FactorAssignmentProgram.localRegister id a))
    Function.injective_id i).trans (clearMany_stacks ports _ i)

theorem cleared_bound (ports : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : WordBound B a) : WordBound B (cleared ports a) := by
  intro i
  rw [cleared_stacks]
  split_ifs
  · simp
  · exact ha i

theorem clearCost_le (ports : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : WordBound B a) : clearCost ports a ≤ ports.length * (2 * B + 3) + 1 :=
  Nat.add_le_add_right (clearManyCost_le ports _ B ha) 1


open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleSum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _

private theorem portIndex_ports (i : Fin 28) : portIndex (ports i).val = i.val := by
  fin_cases i <;> rfl

theorem ports_injective : Function.Injective ports := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun k : Fin 896 => portIndex k.val) h
  simpa only [portIndex_ports] using hv

theorem mem_scratchIndices (i : Fin 28) : i ∈ scratchIndices ↔
    i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 24 ∧ i ≠ 15 ∧ i ≠ 27 := by
  simp only [scratchIndices,List.mem_filter,List.mem_ofFn,exists_eq,
    decide_eq_true_eq,true_and]

theorem scratchPorts_length : scratchPorts.length = 23 := by decide

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) :=
  (NodeAppendSpace.prepare_eval a).seq
    (NodeReadoutSpace.clearMany_eval scratchPorts (NodeAppendSpace.prepared a))

theorem prepared_stacks (a : Data) (i : Fin 896) :
    (prepared a).stacks i = if i ∈ scratchPorts then [] else
      if i = 5 then a.stacks 194 else if i = 12 then a.stacks 202 else
      if i = 39 then a.stacks 204 else if i = 89 then [] else a.stacks i := by
  rw [prepared,NodeReadoutSpace.clearedMany_stack,NodeAppendSpace.prepared_stacks]

theorem prepared_bound (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((prepared a).stacks i).length ≤ B := by
  intro i
  rw [prepared_stacks]
  split_ifs <;> first | exact ha _ | exact Nat.zero_le _

theorem prepareCost_le (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    prepareCost a ≤ 75*B+96 := by
  have h1 := NodeAppendSpace.prepareCost_le a B ha
  have h2 := NodeReadoutSpace.clearCost_le scratchPorts (NodeAppendSpace.prepared a) B
    (NodeAppendSpace.prepared_bound a B ha)
  rw [scratchPorts_length] at h2
  unfold prepareCost
  omega

theorem localState_stack (rr : Fin 8 → Bool)
    (modulus width degree seed source : List Bool) (i : Fin 28) :
    (Normalize.state rr modulus width degree seed source).stacks i =
      if i = 5 then modulus else if i = 12 then width else if i = 24 then degree
      else if i = 15 then seed else if i = 27 then source else [] := by
  fin_cases i <;> rfl

theorem prepared_eq (a : Data) (modulus width degree seed source : List Bool)
    (hr : Ready a modulus width degree seed source) :
    embedState registers ports (prepared a)
      (Normalize.state (fun i => (prepared a).regs (registers i))
        modulus width degree seed source) = prepared a := by
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
  · intro i; rfl
  · intros; rfl
  · intro i
    rw [localState_stack]
    by_cases h5 : i = 5
    · subst i; simpa [ports,prepared_stacks,show (5 : Fin 896) ∉ scratchPorts from by decide]
        using hr.modulus
    by_cases h12 : i = 12
    · subst i; simpa [ports,prepared_stacks,show (12 : Fin 896) ∉ scratchPorts from by decide]
        using hr.width
    by_cases h24 : i = 24
    · subst i; simpa [ports,prepared_stacks,show (39 : Fin 896) ∉ scratchPorts from by decide]
        using hr.degree
    by_cases h15 : i = 15
    · subst i; simpa [ports,prepared_stacks,show (851 : Fin 896) ∉ scratchPorts from by decide]
        using hr.seed
    by_cases h27 : i = 27
    · subst i; simpa [ports,prepared_stacks,show (852 : Fin 896) ∉ scratchPorts from by decide]
        using hr.source
    have hm : ports i ∈ scratchPorts := List.mem_map.mpr
      ⟨i,(mem_scratchIndices i).mpr ⟨h5,h12,h24,h15,h27⟩,rfl⟩
    simp only [prepared_stacks, hm, ite_true, if_true, h5, h12, h24, h15, h27,
      ite_false]
  · intros; rfl

theorem result_bound (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree seed source output : List Bool)
    (hr : Ready a modulus width degree seed source)
    (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) (hout : output.length ≤ B) :
    ∀ i, ((result a rr modulus width degree output).stacks i).length ≤ B := by
  have hm : modulus.length ≤ B := by simpa only [hr.modulus] using ha 194
  have hw : width.length ≤ B := by simpa only [hr.width] using ha 202
  have hd : degree.length ≤ B := by simpa only [hr.degree] using ha 204
  intro i
  by_cases hi : ∃ j, ports j = i
  · obtain ⟨j,rfl⟩ := hi
    change ((embedState registers ports _ _).stacks (ports j)).length ≤ B
    rw [embedState_stack _ _ _ _ ports_injective,localState_stack]
    split_ifs <;> first | exact hm | exact hw | exact hd | exact hout | exact Nat.zero_le _
  · unfold result
    rw [embedState_stack_frame _ _ _ _ i hi]
    exact prepared_bound a B ha i

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J source) (hi : Good ∅ u J seed)
    (width degree : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : Ready a M.bits width degree (Product.bytes seed) (Product.bytes source)) :
    let output := Normalize.run p t M cache source seed
    ∃ steps rr, steps+1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a (result a rr M.bits width degree (Product.bytes output)) ∧
      Good ∅ u J output := by
  dsimp only
  obtain ⟨steps,rr,hb,ht,hg,_⟩ := addition_run_space p t M cache source seed hs hi
    (fun i => (prepared a).regs (registers i)) width degree hd hw
  have he := eval_call_lifted Normalize.program registers ports (prepared a)
    registers_injective ports_injective ht
  rw [prepared_eq a M.bits width degree (Product.bytes seed) (Product.bytes source) hr] at he
  refine ⟨prepareCost a+steps,rr,?_,(prepare_eval a).seq he,hg⟩
  have hc := prepareCost_le a incoming ha
  unfold budget
  omega

/-- A fixed boundary cap is restored after each tuple. The temporary prefix
bound is kept separate and is never recursively substituted for this cap. -/
theorem result_bound_of_good {n B d u J : ℕ}
    (output : List (Product.Entry n B d)) (hg : Good ∅ u J output)
    (a : Data) (rr : Fin 8 → Bool) (modulus width degree seed source : List Bool)
    (hr : Ready a modulus width degree seed source)
    (bound : ℕ) (ha : ∀ i, (a.stacks i).length ≤ bound)
    (hcap : u*J*(2*(u+J+n)+2*(d*B)+2) ≤ bound) :
    ∀ i, ((result a rr modulus width degree (Product.bytes output)).stacks i).length ≤ bound :=
  result_bound a rr modulus width degree seed source (Product.bytes output) hr bound ha
    ((empty_bytes_length_le hg).trans hcap)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

namespace TupleEnd

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram

theorem command_run_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J source) (hi : Good ∅ u J seed)
    (width degree : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hr : QueryTupleSum.Ready a M.bits width degree (Product.bytes seed) (Product.bytes source))
    (hcap : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2) ≤ B) :
    let output := Normalize.run p t M cache source seed
    ∃ steps rr, Eval command steps a (result a rr M.bits width degree (Product.bytes output)) ∧
      Good ∅ u J output ∧
      (∀ i, ((result a rr M.bits width degree (Product.bytes output)).stacks i).length ≤ B) ∧
      steps+1 ≤ QueryTupleSum.budget n (baseWidth p t) d u J B+16*B+25 := by
  dsimp only
  obtain ⟨steps,rr,ht,he,hg⟩ := QueryTupleSum.command_eval p t M cache source seed hs hi
    width degree hd hw a B ha hr
  have hb := QueryTupleSum.result_bound_of_good _ hg a rr M.bits width degree
    (Product.bytes seed) (Product.bytes source) hr B ha hcap
  have hc := QueryTupleInit.clear_eval currentHeadPorts
    (QueryTupleSum.result a rr M.bits width degree (Product.bytes (Normalize.run p t M cache source seed)))
  have hcost := QueryTupleInit.clearCost_le currentHeadPorts _ B hb
  rw [show currentHeadPorts.length=8 by rfl] at hcost
  refine ⟨_,rr,he.seq hc,hg,QueryTupleInit.cleared_bound currentHeadPorts _ B hb,?_⟩
  omega

end TupleEnd

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run_oai
