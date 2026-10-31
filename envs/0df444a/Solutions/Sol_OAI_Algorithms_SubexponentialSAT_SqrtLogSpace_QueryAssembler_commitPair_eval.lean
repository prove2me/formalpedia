-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:43:50.626991+00:00
-- url     : https://prove2.me/submissions/37cbf234-9d7e-46a6-aceb-909641e0f5be

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Normalize_program_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryProgram_signedScale_run_space
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEnvironment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem pairs_valid : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ 159 ∧ (159 : Fin 896) ≠ p.2 := by
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem bootstrap_eval (a : Data) (htmp : a.stacks 159 = []) :
    Eval bootstrap (bootstrapCost a) a (bootstrapResult a) := by
  have he := copyMany_eval 159 pairs (projectState registerMap id a) pairs_valid htmp
  exact eval_liftCommand_from_state bootstrap16 194 5 registerMap id a
    (Fin.castAdd_injective 16 24) Function.injective_id he

private theorem embed_identity_stacks (a : Data) (b : State 16 896) :
    (embedState registerMap id a b).stacks = b.stacks := by
  funext i
  exact Function.injective_id.extend_apply b.stacks a.stacks i

theorem bootstrap_stacks (a : Data) :
    (bootstrapResult a).stacks =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update a.stacks 5 (a.stacks 194 ++ a.stacks 5))
          12 (a.stacks 202 ++ a.stacks 12)) 17 (a.stacks 203 ++ a.stacks 17))
          22 (a.stacks 201 ++ a.stacks 22)) 39 (a.stacks 204 ++ a.stacks 39))
          45 (a.stacks 212 ++ a.stacks 45)) 46 (a.stacks 243 ++ a.stacks 46) := by
  funext i
  rw [bootstrapResult, embed_identity_stacks]
  simp only [pairs, copyManyState, copyState, StackRoutines.copyStacks, projectState,
    Function.comp_apply, id_eq, Function.update_of_ne (by decide : (202 : Fin 896) ≠ 5),
    Function.update_of_ne (by decide : (12 : Fin 896) ≠ 5)]
  simp

theorem bootstrap_frame (a : Data) (i : Fin 896) (hi : i ∉ environmentPorts) :
    (bootstrapResult a).stacks i = a.stacks i := by
  rw [bootstrapResult, embed_identity_stacks]
  apply copyMany_frame
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  simp only [environmentPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hi
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only; tauto

private theorem word_le_total (a : Data) (i : Fin 896) :
    (a.stacks i).length ≤ stackBits a.stacks :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((a.stacks j).length)) (Finset.mem_univ i)

theorem bootstrapCost_le (a : Data) : bootstrapCost a ≤ 49 * stackBits a.stacks + 36 := by
  have h194 := word_le_total a 194
  have h202 := word_le_total a 202
  have h203 := word_le_total a 203
  have h201 := word_le_total a 201
  have h204 := word_le_total a 204
  have h212 := word_le_total a 212
  have h243 := word_le_total a 243
  simp [bootstrapCost, pairs, copyManyCost, copyState, StackRoutines.copyStacks, projectState]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

theorem parity_nil_trace (regs : Fin 3 → Bool) :
    Trace parityProgram 3 (parityStart regs []) (parityFinish (regs 2)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, parityProgram, parityStart, parityFinish,
    execInstr, readRegs]
  funext j
  fin_cases j <;> simp

theorem parity_cons_trace (regs : Fin 3 → Bool) (bit : Bool) (bits : List Bool) :
    Trace parityProgram 3 (parityStart regs (bit :: bits))
      (parityStart ![bit, true, Bool.xor (regs 2) bit] bits) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, parityProgram, parityStart, execInstr, readRegs]
  ext j
  fin_cases j <;> simp

theorem parity_program_trace (regs : Fin 3 → Bool) (bits : List Bool) :
    Trace parityProgram (3 * bits.length + 3) (parityStart regs bits)
      (parityFinish (parity bits (regs 2))) := by
  induction bits generalizing regs with
  | nil => exact parity_nil_trace regs
  | cons bit bits ih =>
      have h := (parity_cons_trace regs bit bits).trans
        (ih ![bit, true, Bool.xor (regs 2) bit])
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      simp only [List.length_cons]
      omega
      congr 1

open StructuredCalls

theorem scanCall_eval {s : ℕ} (d : State 3 s) (src : Fin s) :
    Eval (scanCall src) (3 * (d.stacks src).length + 3) d (afterScan d src) := by
  have hi : Function.Injective (fun _ : Fin 1 => src) := fun a b _ => Subsingleton.elim a b
  have h := eval_call_lifted parityProgram id (fun _ => src) d
    Function.injective_id hi
    (a := ⟨d.regs, fun _ => d.stacks src⟩)
    (b := ⟨![false, false, parity (d.stacks src) (d.regs 2)], fun _ => []⟩)
    (parity_program_trace d.regs (d.stacks src))
  have ha : embedState id (fun _ : Fin 1 => src) d
      ⟨d.regs, fun _ => d.stacks src⟩ = d := by
    apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id hi
    · intro i; rfl
    · intro i; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j _; rfl
  have hb : embedState id (fun _ : Fin 1 => src) d
      ⟨![false, false, parity (d.stacks src) (d.regs 2)], fun _ => []⟩ =
        afterScan d src := by
    apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id hi
    · intro i; rfl
    · intro i; simp [afterScan]
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      have hj' : j ≠ src := fun h => hj ⟨0, h.symm⟩
      simp [afterScan, hj']
  change Eval (scanCall src) _ (embedState _ _ d _) (embedState _ _ d _) at h
  rwa [ha, hb] at h

theorem pairSign_eval (regs : Fin 3 → Bool) (E U : List Bool) :
    Eval pairSign (10 * (E.length + U.length) + 18)
      (pairStart regs E U) (pairFinish E U) := by
  let a₀ := pairStart regs E U
  let a₁ := StructuredProgram.Atom.eval (.set 2 false) a₀
  let a₂ := SubexpScanPrimitives.afterCopy a₁ 0 2 0 1
  let a₃ := afterScan a₂ 2
  let a₄ := SubexpScanPrimitives.afterCopy a₃ 1 2 0 1
  let a₅ := afterScan a₄ 2
  have h₀ : Eval (.base (.atom (.set 2 false))) 1 a₀ a₁ :=
    .base (.atom _ _)
  have h₁ := SubexpScanPrimitives.copy_eval a₁ 0 2 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have h₂ := scanCall_eval a₂ 2
  have h₃ := SubexpScanPrimitives.copy_eval a₃ 1 2 3 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [a₃, afterScan, a₂, SubexpScanPrimitives.afterCopy,
      StackRoutines.copyStacks, a₁, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, a₀,
      pairStart, StructuredProgram.State.ofCfg, execInstr])
  have h₄ := scanCall_eval a₄ 2
  have h₅ : Eval (.base (.atom (.push 2 2))) 1 a₅
      (StructuredProgram.Atom.eval (.push 2 2) a₅) := .base (.atom _ _)
  have h := h₀.seq (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅))))
  have hs : StructuredProgram.Atom.eval (.push 2 2) a₅ = pairFinish E U := by
    apply SubexpScanPrimitives.state_ext
    · funext i
      fin_cases i <;>
        simp [a₅, afterScan, a₄, a₃, a₂, a₁, a₀, pairStart, pairFinish,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
          SubexpScanPrimitives.afterCopy,
          StackRoutines.copyStacks, execInstr, readRegs]
    · funext i
      fin_cases i <;>
        simp [a₅, afterScan, a₄, a₃, a₂, a₁, a₀, pairStart, pairFinish,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
          SubexpScanPrimitives.afterCopy,
          StackRoutines.copyStacks, execInstr, readRegs]
  rw [hs] at h
  convert h using 1
  · rfl
  · simp [afterScan, a₄, a₃, a₂, a₁, a₀, pairStart,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, execInstr]
    omega

theorem pairSign_trace (regs : Fin 3 → Bool) (E U : List Bool) :
    Trace pairSignProgram (10 * (E.length + U.length) + 19)
      ((pairStart regs E U).withPC (some pairSignProgram.entry))
      ((pairFinish E U).withPC none) := by
  simpa [pairSignProgram, Nat.add_assoc] using compiled_halt_trace (pairSign_eval regs E U) 0 2

theorem pairRegisters_injective : Function.Injective pairRegisters := Fin.castAdd_injective _ _

theorem pairStacks_injective : Function.Injective pairStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [pairStacks]

theorem pairSignCall_eval (d : State 40 896)
    (hout : d.stacks 848 = []) (htmp : d.stacks 849 = []) :
    Eval pairSignCall (10 * ((d.stacks 834).length + (d.stacks 835).length) + 19)
      d (pairCallResult d) := by
  let src := pairStart (fun i => d.regs (pairRegisters i)) (d.stacks 834) (d.stacks 835)
  let dst := pairFinish (d.stacks 834) (d.stacks 835)
  have hi : embedState pairRegisters pairStacks d src = d := by
    apply SubexpScanPrimitives.embedState_eq _ _ pairRegisters_injective pairStacks_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [src, pairStart, pairStacks, hout, htmp]
    · intro i _; rfl
    · intro i _; rfl
  have ho : embedState pairRegisters pairStacks d dst = pairCallResult d := by
    apply SubexpScanPrimitives.embedState_eq _ _ pairRegisters_injective pairStacks_injective
    · intro i
      fin_cases i <;> simp [dst, pairFinish, pairCallResult, pairRegisters]
    · intro i
      fin_cases i <;> simp [dst, pairFinish, pairCallResult, pairStacks, htmp]
    · intro i hi
      have h₀ : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h₁ : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have h₂ : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
      simp [pairCallResult, h₀, h₁, h₂]
    · intro i hi
      have h₈ : i ≠ 848 := fun h => hi ⟨2, h.symm⟩
      simp [pairCallResult, h₈]
  have h := eval_call_lifted pairSignProgram pairRegisters pairStacks d
    pairRegisters_injective pairStacks_injective
    (pairSign_trace (fun i => d.regs (pairRegisters i)) (d.stacks 834) (d.stacks 835))
  change Eval pairSignCall _ (embedState _ _ d src) (embedState _ _ d dst) at h
  rwa [hi, ho] at h

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem leafArithmeticRegs_injective : Function.Injective leafArithmeticRegs :=
  Fin.castAdd_injective _ _

theorem leafScalePorts_injective : Function.Injective leafScalePorts := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [leafScalePorts] at hv
  split_ifs at hv <;> simp_all [Fin.ext_iff] <;> omega

theorem leafNormalizePorts_injective : Function.Injective leafNormalizePorts := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [leafNormalizePorts] at hv
  split_ifs at hv <;> simp_all [Fin.ext_iff] <;> omega

theorem leafScalePorts_not_acc : ¬ ∃ j, leafScalePorts j = 850 := by
  rintro ⟨j, hj⟩
  have h := congrArg Fin.val hj
  simp only [leafScalePorts] at h
  split_ifs at h <;> simp_all
  omega

theorem leafScalePorts_not_scratch (i : Fin 28) :
    ¬ ∃ j, leafScalePorts j = (⟨100 + i.val, by omega⟩ : Fin 896) := by
  rintro ⟨j, hj⟩
  have h := congrArg Fin.val hj
  simp only [leafScalePorts] at h
  split_ifs at h <;> simp_all <;> omega

theorem embed_scale_ready (d : State 40 896) (e : Squarefree.ScaleProgram.Environment)
    (source : List Bool) (sign : Bool) (h : ScaleReady d e source sign) :
    embedState leafArithmeticRegs leafScalePorts d
      (signedState (fun j => d.regs (leafArithmeticRegs j))
        (Squarefree.ScaleProgram.idle e source []) sign) = d := by
  apply SubexpScanPrimitives.embedState_eq _ _ leafArithmeticRegs_injective
    leafScalePorts_injective
  · intro i; rfl
  · exact h.stacks
  · intros; rfl
  · intros; rfl

theorem normalize_after_scale (d : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr : Fin 8 → Bool)
    (source seed : List Bool) (sign : Bool) (hs : NormalizeScratchReady d)
    (ha : d.stacks 850 = seed) :
    let mid := embedState leafArithmeticRegs leafScalePorts d
      (signedState rr {Squarefree.ScaleProgram.idle e [] [] with output := source} sign)
    embedState leafArithmeticRegs leafNormalizePorts mid
      (Normalize.state rr e.modulus e.width e.count seed source) = mid := by
  dsimp only
  let mid := embedState leafArithmeticRegs leafScalePorts d
    (signedState rr {Squarefree.ScaleProgram.idle e [] [] with output := source} sign)
  apply SubexpScanPrimitives.embedState_eq _ _ leafArithmeticRegs_injective
    leafNormalizePorts_injective
  · intro i
    exact embedState_register _ _ _ _ leafArithmeticRegs_injective i
  · intro i
    by_cases h5 : i = 5
    · subst i
      change mid.stacks (leafScalePorts 5) = e.modulus
      rw [embedState_stack _ _ _ _ leafScalePorts_injective]
      rfl
    by_cases h12 : i = 12
    · subst i
      change mid.stacks (leafScalePorts 12) = e.width
      rw [embedState_stack _ _ _ _ leafScalePorts_injective]
      rfl
    by_cases h24 : i = 24
    · subst i
      change mid.stacks (leafScalePorts 39) = e.count
      rw [embedState_stack _ _ _ _ leafScalePorts_injective]
      rfl
    by_cases h15 : i = 15
    · subst i
      change mid.stacks 850 = seed
      rw [embedState_stack_frame _ _ _ _ _ leafScalePorts_not_acc]
      exact ha
    by_cases h27 : i = 27
    · subst i
      change mid.stacks (leafScalePorts 38) = source
      rw [embedState_stack _ _ _ _ leafScalePorts_injective]
      rfl
    have hh : (Normalize.state rr e.modulus e.width e.count seed source).stacks i = [] := by
      have hn5 : i.val ≠ 5 := by simpa [Fin.ext_iff] using h5
      have hn12 : i.val ≠ 12 := by simpa [Fin.ext_iff] using h12
      have hn24 : i.val ≠ 24 := by simpa [Fin.ext_iff] using h24
      have hn15 : i.val ≠ 15 := by simpa [Fin.ext_iff] using h15
      have hn27 : i.val ≠ 27 := by simpa [Fin.ext_iff] using h27
      have hi : i.val < 27 := by omega
      change Fin.snoc (α := fun _ : Fin 28 => List Bool) (Dictionary.tapes (Dictionary.outputTape
        e.modulus e.width e.count seed [])) source i = []
      rw [show i = (⟨i.val, hi⟩ : Fin 27).castSucc from rfl, Fin.snoc_castSucc]
      have hj5 : (⟨i.val, hi⟩ : Fin 27) ≠ 5 := fun h => hn5 (congrArg Fin.val h)
      have hj12 : (⟨i.val, hi⟩ : Fin 27) ≠ 12 := fun h => hn12 (congrArg Fin.val h)
      have hj24 : (⟨i.val, hi⟩ : Fin 27) ≠ 24 := fun h => hn24 (congrArg Fin.val h)
      have hj15 : (⟨i.val, hi⟩ : Fin 27) ≠ 15 := fun h => hn15 (congrArg Fin.val h)
      simp only [Dictionary.outputTape, Dictionary.tapes, hj5, hj12, hj24, hj15,
        ite_false, ite_self]
    rw [hh]
    have hp : leafNormalizePorts i = ⟨100 + i.val, by omega⟩ := by
      simp [leafNormalizePorts, h5, h12, h24, h15, h27]
    rw [hp, embedState_stack_frame _ _ _ _ _ (leafScalePorts_not_scratch i)]
    simpa only [hp] using hs.empty i h5 h12 h24 h15 h27
  · intros; rfl
  · intros; rfl

/-- Both arithmetic branches and the additive normalization execute on one
fixed physical command. The initial hypotheses describe its actual input words. -/
theorem signedAccumulate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d) (sign : Bool)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (caller : State 40 896)
    (hscale : ScaleReady caller (Squarefree.ScaleProgram.environment p t M cache table
      minusOne degree width) (Product.bytes source) sign)
    (hscratch : NormalizeScratchReady caller) (hacc : caller.stacks 850 = Product.bytes seed) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let scaled := signedEntries p t M cache table minusOne sign source
    let result := signedSum p t M cache table minusOne sign source seed
    ∃ steps rr ss,
      steps + 1 ≤ signedAccumulateBudget n (baseWidth p t) d u J ∧
      Eval signedAccumulate steps caller
        (accumulateLeafResult caller e rr ss (Product.bytes scaled) (Product.bytes result) sign) ∧
      Good ∅ u J result := by
  dsimp only
  let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
  let scaled := signedEntries p t M cache table minusOne sign source
  obtain ⟨st, rr, hb, ht, hg, _⟩ := signedScale_run_space p t M cache hz table minusOne
    source hsource degree width hd hw (fun i => caller.regs (leafArithmeticRegs i)) sign
  have he := eval_call_lifted signedScaleProgram leafArithmeticRegs leafScalePorts caller
    leafArithmeticRegs_injective leafScalePorts_injective ht
  rw [embed_scale_ready caller e (Product.bytes source) sign hscale] at he
  let mid := scaleLeafResult caller e rr (Product.bytes scaled) sign
  change Eval _ st caller mid at he
  obtain ⟨atime, ss, hab, hat, hag, _⟩ := TruncatedRingProgram.addition_run_space
    p t M cache scaled seed hg hseed rr width degree hd hw
  have hae := eval_call_lifted Normalize.program leafArithmeticRegs leafNormalizePorts mid
    leafArithmeticRegs_injective leafNormalizePorts_injective hat
  have hi : embedState leafArithmeticRegs leafNormalizePorts mid
      (Normalize.state rr M.bits width degree (Product.bytes seed) (Product.bytes scaled)) = mid :=
    normalize_after_scale caller e rr (Product.bytes scaled) (Product.bytes seed) sign
      hscratch hacc
  rw [hi] at hae
  refine ⟨st + atime, rr, ss, ?_, ?_, hag⟩
  · unfold signedAccumulateBudget
    omega
  · exact he.seq hae

theorem signedState_unchanged (regs rr : Fin 8 → Bool)
    (e : Squarefree.ScaleProgram.Environment) (source output : List Bool) (sign : Bool)
    (i : Fin 41) (h32 : i ≠ 32) (h38 : i ≠ 38) :
    (signedState rr {Squarefree.ScaleProgram.idle e [] [] with output := output} sign).stacks i =
      (signedState regs (Squarefree.ScaleProgram.idle e source []) sign).stacks i := by
  simp only [signedState]
  split_ifs with hi
  · have hj32 : (⟨i.val, hi⟩ : Fin 40) ≠ 32 := by simpa [Fin.ext_iff] using h32
    have hj38 : (⟨i.val, hi⟩ : Fin 40) ≠ 38 := by simpa [Fin.ext_iff] using h38
    simp only [Squarefree.ScaleProgram.tapes, Squarefree.ScaleProgram.idle,
      hj32, hj38, ite_false]
  · rfl

theorem scaleLeafResult_frame (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr : Fin 8 → Bool)
    (source output : List Bool) (sign : Bool) (h : ScaleReady caller e source sign)
    (i : Fin 896) (h38 : i ≠ 38) (h851 : i ≠ 851) :
    (scaleLeafResult caller e rr output sign).stacks i = caller.stacks i := by
  by_cases hi : ∃ j, leafScalePorts j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [scaleLeafResult, embedState_stack _ _ _ _ leafScalePorts_injective, h.stacks j]
    apply signedState_unchanged
    · intro he; subst j; exact h851 rfl
    · intro he; subst j; exact h38 rfl
  · exact embedState_stack_frame _ _ _ _ _ hi

theorem normalizeState_unchanged (regs rr : Fin 8 → Bool)
    (modulus width degree source seed result : List Bool)
    (i : Fin 28) (h15 : i ≠ 15) (h27 : i ≠ 27) :
    (Normalize.state rr modulus width degree result []).stacks i =
      (Normalize.state regs modulus width degree seed source).stacks i := by
  have hn27 : i.val ≠ 27 := by simpa [Fin.ext_iff] using h27
  have hi : i.val < 27 := by omega
  change Fin.snoc (α := fun _ : Fin 28 => List Bool)
    (Dictionary.tapes (Dictionary.outputTape modulus width degree result [])) [] i =
      Fin.snoc (α := fun _ : Fin 28 => List Bool)
        (Dictionary.tapes (Dictionary.outputTape modulus width degree seed [])) source i
  rw [show i = (⟨i.val, hi⟩ : Fin 27).castSucc from rfl,
    Fin.snoc_castSucc, Fin.snoc_castSucc]
  have hj15 : (⟨i.val, hi⟩ : Fin 27) ≠ 15 := by simpa [Fin.ext_iff] using h15
  simp only [Dictionary.tapes, Dictionary.outputTape, hj15, ite_false]

theorem accumulateLeafResult_normalize_frame (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source seed result : List Bool) (sign : Bool)
    (hs : NormalizeScratchReady caller) (ha : caller.stacks 850 = seed)
    (i : Fin 896) (h850 : i ≠ 850) (h38 : i ≠ 38) :
    (accumulateLeafResult caller e rr ss source result sign).stacks i =
      (scaleLeafResult caller e rr source sign).stacks i := by
  by_cases hi : ∃ j, leafNormalizePorts j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [accumulateLeafResult, embedState_stack _ _ _ _ leafNormalizePorts_injective]
    have hready := normalize_after_scale caller e rr source seed sign hs ha
    have he := congrArg (fun d : State 40 896 => d.stacks (leafNormalizePorts j)) hready
    dsimp only at he
    rw [embedState_stack _ _ _ _ leafNormalizePorts_injective] at he
    change (Normalize.state rr e.modulus e.width e.count seed source).stacks j =
      (scaleLeafResult caller e rr source sign).stacks (leafNormalizePorts j) at he
    rw [← he]
    apply normalizeState_unchanged
    · intro hh; subst j; exact h850 rfl
    · intro hh; subst j; exact h38 rfl
  · exact embedState_stack_frame _ _ _ _ _ hi

@[simp] theorem accumulateLeafResult_accumulator (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source result : List Bool) (sign : Bool) :
    (accumulateLeafResult caller e rr ss source result sign).stacks 850 = result := by
  change (accumulateLeafResult caller e rr ss source result sign).stacks (leafNormalizePorts 15) = _
  rw [accumulateLeafResult, embedState_stack _ _ _ _ leafNormalizePorts_injective]
  rfl

@[simp] theorem accumulateLeafResult_source (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source result : List Bool) (sign : Bool) :
    (accumulateLeafResult caller e rr ss source result sign).stacks 38 = [] := by
  change (accumulateLeafResult caller e rr ss source result sign).stacks (leafNormalizePorts 27) = _
  rw [accumulateLeafResult, embedState_stack _ _ _ _ leafNormalizePorts_injective]
  rfl

theorem accumulateLeafResult_frame (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (input source seed result : List Bool) (sign : Bool)
    (hscale : ScaleReady caller e input sign)
    (hs : NormalizeScratchReady caller) (ha : caller.stacks 850 = seed)
    (i : Fin 896) (h850 : i ≠ 850) (h851 : i ≠ 851) :
    (accumulateLeafResult caller e rr ss source result sign).stacks i = caller.stacks i := by
  by_cases h38 : i = 38
  · subst i
    rw [accumulateLeafResult_source]
    exact (hscale.stacks 38).symm
  · rw [accumulateLeafResult_normalize_frame caller e rr ss source seed result sign hs ha i h850 h38]
    exact scaleLeafResult_frame caller e rr input source sign hscale i h38 h851

@[simp] theorem accumulateLeafResult_consumed (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source seed result : List Bool) (sign : Bool)
    (hs : NormalizeScratchReady caller) (ha : caller.stacks 850 = seed) :
    (accumulateLeafResult caller e rr ss source result sign).stacks 851 = [] := by
  rw [accumulateLeafResult_normalize_frame caller e rr ss source seed result sign hs ha
    851 (by decide) (by decide)]
  change (scaleLeafResult caller e rr source sign).stacks (leafScalePorts 32) = _
  rw [scaleLeafResult, embedState_stack _ _ _ _ leafScalePorts_injective]
  rfl

theorem pairCallResult_scaleReady (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (input : List Bool)
    (h : ∀ i : Fin 40, caller.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle e input []) i) :
    ScaleReady (pairCallResult caller) e input
      (parity (caller.stacks 835) (parity (caller.stacks 834) false)) := by
  constructor
  intro i
  induction i using (Fin.addCases (m := 40) (n := 1)) with
  | left i =>
    have hne : leafScalePorts (Fin.castAdd 1 i) ≠ 848 := by
      intro he
      have hh := leafScalePorts_injective (show leafScalePorts (Fin.castAdd 1 i) =
        leafScalePorts 40 from he)
      have hv := congrArg Fin.val hh
      change i.val = 40 at hv
      omega
    rw [pairCallResult_stack_frame _ _ hne, h i]
    simp [signedState]
  | right i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

theorem pairCallResult_normalizeScratch (caller : State 40 896)
    (h : NormalizeScratchReady caller) : NormalizeScratchReady (pairCallResult caller) := by
  constructor
  intro i h5 h12 h24 h15 h27
  have hn : leafNormalizePorts i ≠ 848 := by
    simp [leafNormalizePorts, h5, h12, h24, h15, h27, Fin.ext_iff]
    omega
  rw [pairCallResult_stack_frame _ _ hn]
  exact h.empty i h5 h12 h24 h15 h27

/-- Exact actual signed update, including mask scans and sign cleanup. -/
theorem pairUpdate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (caller : State 40 896)
    (hlow : ∀ i : Fin 40, caller.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle
        (Squarefree.ScaleProgram.environment p t M cache table minusOne degree width)
        (Product.bytes source) []) i)
    (hscratch : NormalizeScratchReady caller) (hacc : caller.stacks 850 = Product.bytes seed)
    (hsign : caller.stacks 848 = []) (htmp : caller.stacks 849 = []) :
    let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
    let sign := parity (caller.stacks 835) (parity (caller.stacks 834) false)
    let scaled := signedEntries p t M cache table minusOne sign source
    let result := signedSum p t M cache table minusOne sign source seed
    ∃ steps rr ss,
      steps + 1 ≤ pairUpdateBudget n (baseWidth p t) d u J
        (caller.stacks 834).length (caller.stacks 835).length ∧
      Eval pairUpdate steps caller
        (pairUpdateResult (accumulateLeafResult (pairCallResult caller) e rr ss
          (Product.bytes scaled) (Product.bytes result) sign)) ∧ Good ∅ u J result := by
  dsimp only
  let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
  let sign := parity (caller.stacks 835) (parity (caller.stacks 834) false)
  let scaled := signedEntries p t M cache table minusOne sign source
  let result := signedSum p t M cache table minusOne sign source seed
  have hs := pairCallResult_scaleReady caller e (Product.bytes source) hlow
  have hsc := pairCallResult_normalizeScratch caller hscratch
  have ha : (pairCallResult caller).stacks 850 = Product.bytes seed := by
    rw [pairCallResult_stack_frame _ _ (by decide)]
    exact hacc
  obtain ⟨steps, rr, ss, hb, he, hg⟩ := signedAccumulate_eval p t M cache hz table minusOne
    sign source seed hsource hseed degree width hd hw (pairCallResult caller) hs hsc ha
  let out := accumulateLeafResult (pairCallResult caller) e rr ss
    (Product.bytes scaled) (Product.bytes result) sign
  have ho : out.stacks 848 = [sign] := by
    rw [accumulateLeafResult_frame (pairCallResult caller) e rr ss (Product.bytes source)
      (Product.bytes scaled) (Product.bytes seed) (Product.bytes result) sign hs hsc ha
      848 (by decide) (by decide)]
    rfl
  have hp : Eval (.base (.atom (.pop 848 0 1))) 1 out (pairUpdateResult out) := by
    convert Eval.base (StructuredProgram.Eval.atom (.pop 848 0 1) out) using 1
    all_goals try with_reducible_and_instances rfl
    apply SubexpScanPrimitives.state_ext
    · rfl
    · change Function.update out.stacks 848 [] =
        Function.update out.stacks 848 (out.stacks 848).tail
      rw [ho]
      rfl
  refine ⟨10 * ((caller.stacks 834).length + (caller.stacks 835).length) + 19 + (steps + 1),
    rr, ss, ?_, (pairSignCall_eval caller hsign htmp).seq (he.seq hp), hg⟩
  unfold pairUpdateBudget
  omega

/-- Exact stack framing of the complete pair arithmetic: only node850 and
consumed pair851 differ from the input state. In particular E/U, all suspended
representatives, and every loader/cache master survive. -/
theorem pairUpdateResult_frame (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (input source seed result : List Bool)
    (hlow : ∀ i : Fin 40, caller.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle e input []) i)
    (hs : NormalizeScratchReady caller) (ha : caller.stacks 850 = seed)
    (hsign : caller.stacks 848 = [])
    (i : Fin 896) (h850 : i ≠ 850) (h851 : i ≠ 851) :
    let sign := parity (caller.stacks 835) (parity (caller.stacks 834) false)
    (pairUpdateResult (accumulateLeafResult (pairCallResult caller) e rr ss source result sign)).stacks i =
      caller.stacks i := by
  dsimp only
  by_cases hi : i = 848
  · subst i
    simp [pairUpdateResult, hsign]
  · simp only [pairUpdateResult, Function.update_of_ne hi]
    have hscale := pairCallResult_scaleReady caller e input hlow
    have hscratch := pairCallResult_normalizeScratch caller hs
    have hacc : (pairCallResult caller).stacks 850 = seed := by
      rw [pairCallResult_stack_frame _ _ (by decide)]
      exact ha
    rw [accumulateLeafResult_frame (pairCallResult caller) e rr ss input source seed result
      _ hscale hscratch hacc i h850 h851, pairCallResult_stack_frame _ _ hi]

@[simp] theorem pairUpdateResult_accumulator (caller : State 40 896)
    (e : Squarefree.ScaleProgram.Environment) (rr ss : Fin 8 → Bool)
    (source result : List Bool) (sign : Bool) :
    (pairUpdateResult (accumulateLeafResult caller e rr ss source result sign)).stacks 850 = result := by
  simp [pairUpdateResult]

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

private theorem clear_eval (dst : Fin 896) (a : Data) :
    Eval (.call (StackRoutines.clearProgram dst 0 1)) (2 * (a.stacks dst).length + 3)
      a ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks dst a.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run dst (0 : Fin 40) 1 a.regs a.stacks)

theorem overwrite_eval (src dst : Fin 896) (hsd : src ≠ dst)
    (hst : src ≠ 841) (htd : (841 : Fin 896) ≠ dst)
    (a : Data) (htmp : a.stacks 841 = []) :
    Eval (overwrite src dst) (2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8)
      a (overwriteState src dst a) := by
  have hc := clear_eval dst a
  have ht : (StackRoutines.clearStacks dst a.stacks) 841 = [] := by
    simp [StackRoutines.clearStacks, htd, htmp]
  have hp := copyWord_eval src dst 841 hsd hst htd
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩ ht
  have hs : (StackRoutines.clearStacks dst a.stacks) src = a.stacks src := by
    simp [StackRoutines.clearStacks,hsd]
  simpa only [overwrite, overwriteState, hs, show 2 * (a.stacks dst).length + 3 +
    (7 * (a.stacks src).length + 5) =
    2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8 by omega] using hc.seq hp

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

/-- Repeated passes retain the same word bound: overwrite replaces one word,
rather than appending to a growing visit history. -/
theorem overwriteState_bound (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((overwriteState src dst a).stacks i).length ≤ B := by
  intro i
  rw [overwriteState_stacks src dst hsd]
  by_cases hi : i = dst
  · subst i
    rw [Function.update_self]
    exact hb src
  · rw [Function.update_of_ne hi]
    exact hb i

theorem overwriteState_frame (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (i : Fin 896) (hi : i ≠ dst) :
    (overwriteState src dst a).stacks i = a.stacks i := by
  rw [overwriteState_stacks src dst hsd,Function.update_of_ne hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem low_mem (i : Fin 896) :
    i∈(List.finRange 56).map (Fin.castAdd 840) ↔ i.val<56 := by
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  · intro h
    exact List.mem_map.mpr ⟨⟨i.val,h⟩,List.mem_finRange _,Fin.ext rfl⟩

private theorem normalize_mem (i : Fin 896) :
    i∈(List.finRange 28).map (fun j => (⟨100+j.val,by omega⟩ : Fin 896)) ↔
      100 ≤ i.val ∧ i.val<128 := by
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change 100+j.val=i.val at hv
    omega
  · intro h
    refine List.mem_map.mpr ⟨⟨i.val-100,by omega⟩,List.mem_finRange _,?_⟩
    apply Fin.ext
    dsimp
    omega

theorem pairScratch_mem (i : Fin 896) : i∈pairScratch ↔
    i.val<56 ∨ (100 ≤ i.val ∧ i.val<128) ∨ i=159 ∨ i=841 ∨ i=848 ∨ i=849 := by
  simp [pairScratch,low_mem,normalize_mem]

theorem clearPair_eval (a : Data) : Eval clearPair (clearPairCost a) a (clearPairState a) :=
  eval_liftCommand_from_state _ 0 0 FactorEnvironment.registerMap id a
    (Fin.castAdd_injective 16 24) Function.injective_id
    (SubexpSetupStorage.clearMany_eval pairScratch _)

theorem clearPair_stacks (a : Data) (i : Fin 896) :
    (clearPairState a).stacks i = if i∈pairScratch then [] else a.stacks i := by
  unfold clearPairState
  rw [show (embedState FactorEnvironment.registerMap id a
    (SubexpSetupStorage.clearManyState pairScratch
      (projectState FactorEnvironment.registerMap id a))).stacks i =
    (SubexpSetupStorage.clearManyState pairScratch
      (projectState FactorEnvironment.registerMap id a)).stacks i from
        embedState_stack FactorEnvironment.registerMap id a _ Function.injective_id i]
  rw [SubexpSetupStorage.clearMany_stacks]
  rfl

theorem clearPair_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((clearPairState a).stacks i).length≤ B := by
  intro i
  rw [clearPair_stacks]
  split
  · exact Nat.zero_le _
  · exact hb i

theorem preparePair_eval (a : Data) :
    Eval preparePair (preparePairCost a) a (preparedPair a) := by
  have ht : (clearPairState a).stacks 159=[] := by
    rw [clearPair_stacks,ite_eq_left (by decide : (159 : Fin 896)∈pairScratch)]
  have hcopy : (FactorEnvironment.bootstrapResult (clearPairState a)).stacks 841=[] := by
    rw [FactorEnvironment.bootstrap_frame _ _ (by decide),clearPair_stacks]
    rw [ite_eq_left (by decide : (841 : Fin 896)∈pairScratch)]
  exact (clearPair_eval a).seq ((FactorEnvironment.bootstrap_eval _ ht).seq
    (overwrite_eval 211 34 (by decide) (by decide) (by decide) _ hcopy))

theorem preparedPair_low (a : Data) (i : Fin 40) :
    (preparedPair a).stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle (pairEnvironment a)
        (a.stacks 851) []) i := by
  rw [preparedPair,overwriteState_stacks 211 34 (by decide),FactorEnvironment.bootstrap_stacks]
  fin_cases i <;> simp [leafScalePorts,pairEnvironment,Squarefree.ScaleProgram.tapes,
    Squarefree.ScaleProgram.idle,Squarefree.ScaleProgram.nativeIdle,clearPair_stacks,pairScratch_mem]

theorem preparedPair_normalize (a : Data) : NormalizeScratchReady (preparedPair a) := by
  constructor
  intro i h5 h12 h24 h15 h27
  rw [preparedPair,overwriteState_stacks 211 34 (by decide),FactorEnvironment.bootstrap_stacks]
  fin_cases i <;> simp_all [leafNormalizePorts,clearPair_stacks,pairScratch_mem]

theorem preparedPair_frame (a : Data) (i : Fin 896) (hi : i∉pairScratch) :
    (preparedPair a).stacks i=a.stacks i := by
  have h34 : i≠34 := by
    intro h; subst i; exact hi (by decide)
  have he : i∉FactorEnvironment.environmentPorts := by
    intro h
    simp only [FactorEnvironment.environmentPorts,List.mem_cons,
      List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hi (by decide)
  rw [preparedPair,overwriteState_frame _ _ (by decide) _ _ h34,
    FactorEnvironment.bootstrap_frame _ _ he,clearPair_stacks,ite_eq_right hi]

theorem preparedPair_sign (a : Data) :
    (preparedPair a).stacks 848=[] ∧ (preparedPair a).stacks 849=[] := by
  simp [preparedPair,overwriteState_stacks 211 34 (by decide),
    FactorEnvironment.bootstrap_stacks,clearPair_stacks,pairScratch_mem]

private theorem bootstrapPair_bound (a : Data) (B : ℕ)
    (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((FactorEnvironment.bootstrapResult (clearPairState a)).stacks i).length≤ B := by
  intro i
  by_cases hi : i∈FactorEnvironment.environmentPorts
  · simp only [FactorEnvironment.environmentPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [FactorEnvironment.bootstrap_stacks]
    all_goals simp [clearPair_stacks,pairScratch_mem]
    all_goals exact hb _
  · rw [FactorEnvironment.bootstrap_frame _ _ hi]
    exact clearPair_bound a B hb i

/-- Bootstrap replaces cleared scratch words with existing master words and
therefore restores the same retained bound independently of visit count. -/
theorem preparedPair_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((preparedPair a).stacks i).length≤ B :=
  overwriteState_bound 211 34 (by decide) _ B (bootstrapPair_bound a B hb)

theorem clearPairCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    clearPairCost a ≤ 176*B+265 := by
  have h := SubexpSetupStorage.clearManyCost_le pairScratch
    (projectState FactorEnvironment.registerMap id a) B hb
  have hl : pairScratch.length=88 := by simp [pairScratch]
  rw [hl] at h
  unfold clearPairCost
  omega

theorem preparePairCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    preparePairCost a ≤ 50000*(B+1) := by
  have hc := clearPairCost_le a B hb
  have hbclear := clearPair_bound a B hb
  have hsum : stackBits (clearPairState a).stacks ≤ 896*B := by
    exact StreamResources.dataBits_le_mul ((clearPairState a).withPC (none : Option (Fin 1))) hbclear
  have hboot := FactorEnvironment.bootstrapCost_le (clearPairState a)
  have hbboot := bootstrapPair_bound a B hb
  have h34 := hbboot 34
  have h211 := hbboot 211
  unfold preparePairCost
  omega

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram

/-- An actual signed pair commit from physical retained cache words. Good
empty-support storage and the semantic accumulator describe the same entries.
The caller boundary remains B; the polynomial transient is not iterated. -/
theorem commitPair_eval_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (a : Data) (B : ℕ)
    (henv : pairEnvironment a = Squarefree.ScaleProgram.environment p t M cache table minusOne degree width)
    (hpair : a.stacks 851=Product.bytes source) (hnode : a.stacks 850=Product.bytes seed)
    (hb : ∀ i,(a.stacks i).length≤ B)
    (hcapacity : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2)≤ B) :
    let sign := parity (a.stacks 835) (parity (a.stacks 834) false)
    let result := signedSum p t M cache table minusOne sign source seed
    ∃ steps b, Eval commitPair steps a b ∧ Good ∅ u J result ∧
      b.stacks 850=Product.bytes result ∧ b.stacks 851=[] ∧
      (∀ i,i∉pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length≤ B) ∧
      steps+1≤51000*(B+1)+pairUpdateBudget n (baseWidth p t) d u J
        (a.stacks 834).length (a.stacks 835).length ∧
      Trace commitPairProgram (steps+1) (a.withPC (some commitPairProgram.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps≤ steps+1 →
        Trace commitPairProgram prefixSteps (a.withPC (some commitPairProgram.entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤896*B+51000*(B+1)+
          pairUpdateBudget n (baseWidth p t) d u J (a.stacks 834).length (a.stacks 835).length := by
  dsimp only
  let c := preparedPair a
  let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
  let sign := parity (a.stacks 835) (parity (a.stacks 834) false)
  let scaled := signedEntries p t M cache table minusOne sign source
  let result := signedSum p t M cache table minusOne sign source seed
  have hE : c.stacks 834=a.stacks 834 := preparedPair_frame a 834 (by decide)
  have hU : c.stacks 835=a.stacks 835 := preparedPair_frame a 835 (by decide)
  have hs : ∀ i : Fin 40,c.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle e (Product.bytes source) []) i := by
    intro i
    rw [preparedPair_low,henv,hpair]
  have ha : c.stacks 850=Product.bytes seed :=
    (preparedPair_frame a 850 (by decide)).trans hnode
  obtain ⟨nt,rr,ss,hcost,he,hgood⟩ := pairUpdate_eval p t M cache hz table minusOne source seed
    hsource hseed degree width hd hw c hs (preparedPair_normalize a) ha
    (preparedPair_sign a).1 (preparedPair_sign a).2
  rw [hE,hU] at hcost he hgood
  let b := pairUpdateResult (accumulateLeafResult (pairCallResult c) e rr ss
    (Product.bytes scaled) (Product.bytes result) sign)
  have h850 : b.stacks 850=Product.bytes result := pairUpdateResult_accumulator _ _ _ _ _ _ _
  have h851 : b.stacks 851=[] := by
    simp only [b,pairUpdateResult,Function.update_of_ne (by decide : (851 : Fin 896) ≠ 848)]
    apply accumulateLeafResult_consumed _ _ _ _ _ (Product.bytes seed) _ _
      (pairCallResult_normalizeScratch c (preparedPair_normalize a))
    rw [pairCallResult_stack_frame _ _ (by decide)]
    exact ha
  have hframe (i : Fin 896) (h850 : i≠850) (h851 : i≠851) : b.stacks i=c.stacks i := by
    have hf := pairUpdateResult_frame c e rr ss (Product.bytes source) (Product.bytes scaled)
      (Product.bytes seed) (Product.bytes result) hs (preparedPair_normalize a) ha
      (preparedPair_sign a).1 i h850 h851
    simpa only [hE,hU] using hf
  have hbb : ∀ i,(b.stacks i).length≤ B := by
    intro i
    by_cases hi : i=850
    · subst i
      rw [h850]
      exact (empty_bytes_length_le hgood).trans hcapacity
    by_cases hi' : i=851
    · subst i
      rw [h851]
      exact Nat.zero_le _
    rw [hframe i hi hi']
    exact preparedPair_bound a B hb i
  have hc := clearPair_eval b
  have hex : Eval commitPair (preparePairCost a+(nt+clearPairCost b)) a (clearPairState b) :=
    (preparePair_eval a).seq (he.seq hc)
  have htotal : preparePairCost a+(nt+clearPairCost b)+1 ≤
      51000*(B+1)+pairUpdateBudget n (baseWidth p t) d u J
        (a.stacks 834).length (a.stacks 835).length := by
    have hp := preparePairCost_le a B hb
    have hclear := clearPairCost_le b B hbb
    omega
  refine ⟨_,clearPairState b,hex,hgood,?_,?_,?_,clearPair_bound b B hbb,htotal,
    compiled_halt_trace hex 851 850,?_⟩
  · rw [clearPair_stacks,ite_eq_right (by decide : (850 : Fin 896)∉pairScratch)]
    exact h850
  · rw [clearPair_stacks,ite_eq_right (by decide : (851 : Fin 896)∉pairScratch)]
    exact h851
  · intro i hi hi850 hi851
    rw [clearPair_stacks,ite_eq_right hi,hframe i hi850 hi851,preparedPair_frame a i hi]
  · have hin : dataBits (a.withPC (some commitPairProgram.entry))≤896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hle htrace i
    have hx := StructuredSpace.local_stack_bound commitPairProgram hin
      prefixSteps intermediate (hle.trans htotal) htrace i
    simpa only [Nat.add_assoc] using hx


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval_oai
