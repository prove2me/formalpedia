-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:52:08.298378+00:00
-- url     : https://prove2.me/submissions/a21d38b5-f0df-449f-8cdb-a18b2f5a8709

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Bounds_mulCost_le

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Index

variable {V : Type*} [DecidableEq V]

theorem Valid.join {a b : Index V} (ha : a.Valid) (hb : b.Valid) : (a.join b).Valid :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)

end Index

end SubexponentialSAT.SqrtLog.Squarefree

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

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem run_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (run p t M cache table u J left right seed)).Nodup := by
  induction left generalizing seed with
  | nil => exact hn
  | cons a left ih =>
    exact ih _ (Normalize.run_nodup p t M cache _ seed hn)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact stored-list specification of the native Horner application. The
operations here are the functional results of the concrete normalized-add
and sparse-product machines, rather than operations on noncomputable jets. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}

omit [Fact (Nat.Prime p)] in
theorem constantStored_nodup (word : RingProgram.ScalarCode p t) :
    (Squarefree.Sparse.keys (constantStored p t cache (n:=n) (d:=d) word)).Nodup := by
  simp [constantStored,Squarefree.Sparse.keys]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

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

theorem keptJoin_valid {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (a : Squarefree.Index (Fin n)) (entries : List (Entry n B d))
    (ha : a.Valid ∧ a.vars ⊆ vars) (he : ∀ b ∈ entries, ValidKey vars u J b.1) :
    ∀ b ∈ keptJoin a u J entries, ValidKey vars u J b.1 := by
  induction entries with
  | nil => intro b hb; simp [keptJoin] at hb
  | cons b entries ih =>
    intro c hc
    have hb := he b (by simp)
    have ht := ih (fun c hc => he c (by simp [hc]))
    by_cases h : (a.join b.1).Kept u J
    · simp only [keptJoin,h,ite_true, if_true,List.mem_cons] at hc
      rcases hc with rfl|hc
      · exact ⟨h,ha.1.join hb.2.1,Finset.union_subset ha.2 hb.2.2⟩
      · exact ht c hc
    · simp only [keptJoin,h,ite_false] at hc
      exact ht c hc

theorem block_valid (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d))
    (ha : ValidKey vars u J a.1) (hr : ∀ b ∈ right, ValidKey vars u J b.1) :
    ∀ b ∈ block p t M cache table u J a right, ValidKey vars u J b.1 := by
  intro b hb
  have h := keptJoin_valid vars u J a.1
    (Squarefree.ScaleProgram.scaled p t M cache table a.2 right) ha.2
    (by intro c hc; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc; exact hr e he)
  exact h b (by simpa [block] using hb)

theorem run_valid (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hl : ∀ a ∈ left, ValidKey vars u J a.1)
    (hr : ∀ b ∈ right, ValidKey vars u J b.1) (hi : ∀ b ∈ seed, ValidKey vars u J b.1) :
    ∀ b ∈ run p t M cache table u J left right seed, ValidKey vars u J b.1 := by
  induction left generalizing seed with
  | nil => exact hi
  | cons a left ih =>
    apply ih _ (fun b hb => hl b (by simp [hb]))
    exact Normalize.run_preserves_keys p t M cache (ValidKey vars u J) _ seed
      (block_valid p t M cache table vars u J a right (hl a (by simp)) hr) hi

end Product
end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsCapacity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Finite record capacity for the actual normalized stored lists. The finite
universe is used for counting only; the program never enumerates it. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

theorem valid_nil {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ) :
    Valid vars u J ([] : List (Product.Entry n B d)) := by
  intro a ha
  simp at ha

theorem length_le_capacity {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : Good vars u J entries) :
    entries.length ≤ capacity vars u J := by
  have hs : (Squarefree.Sparse.keys entries).toFinset ⊆
      Squarefree.Sparse.indexUniverse vars u J := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    have hh := h.1 a ha
    exact (Squarefree.Sparse.mem_indexUniverse vars u J a.1).mpr
      ⟨hh.1, hh.2.2, hh.2.1.trans_lt hh.1.2⟩
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup h.2] at hc
  have hl : entries.length ≤ (Squarefree.Sparse.indexUniverse vars u J).card := by
    simpa only [Squarefree.Sparse.keys,List.length_map] using hc
  exact hl.trans (Squarefree.Sparse.indexUniverse_card_le vars u J)

theorem valid_keyBound {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : Valid vars u J entries) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) entries := by
  intro a ha
  have hh := Squarefree.encodeIndex_length_le a.1 (h a ha).1
  omega

variable {p t n d : ℕ} [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
theorem constant_good (cache : RingProgram.ScalarCache p t)
    (vars : Finset (Fin n)) (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (word : RingProgram.ScalarCode p t) :
    Good vars u J (constantStored p t cache (d:=d) word) := by
  refine ⟨?_, constantStored_nodup p t cache word⟩
  intro a ha
  simp only [constantStored,List.mem_singleton] at ha
  subst a
  simp [Product.ValidKey,Squarefree.Index.origin,Squarefree.Index.Kept,
    Squarefree.Index.Valid,hu,hJ]

theorem add_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (vars : Finset (Fin n)) (u J : ℕ)
    (a b : Stored p t (n:=n) (d:=d)) (ha : Valid vars u J a) (hb : Good vars u J b) :
    Good vars u J (addStored p t M cache a b) := by
  exact ⟨Normalize.run_preserves_keys p t M cache (Product.ValidKey vars u J) a b ha hb.1,
    Normalize.run_nodup p t M cache a b hb.2⟩

theorem mul_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ) (a b : Stored p t (n:=n) (d:=d))
    (ha : Valid vars u J a) (hb : Valid vars u J b) :
    Good vars u J (mulStored p t M cache table u J a b) := by
  exact ⟨Product.run_valid p t M cache table vars u J a b [] ha hb (valid_nil vars u J),
    Product.run_nodup p t M cache table u J a b [] (by simp [Squarefree.Sparse.keys])⟩

theorem triple_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (h : Stored p t (n:=n) (d:=d)) (hh : Valid vars u J h)
    (v : Triple (RingProgram.ScalarCode p t)) :
    Good vars u J (tripleStored p t M cache table u J h v) := by
  have hc := constant_good (d:=d) cache vars u J hu hJ v.c
  have hb := constant_good (d:=d) cache vars u J hu hJ v.b
  have ha := constant_good (d:=d) cache vars u J hu hJ v.a
  have hch := mul_good M cache table vars u J _ h hc.1 hh
  have hchb := add_good M cache vars u J _ _ hch.1 hb
  have hchbh := mul_good M cache table vars u J _ h hchb.1 hh
  exact add_good M cache vars u J _ _ hchbh.1 ha

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial envelopes for the concrete degree-two coefficient and
Horner machines. Every byte copy, dictionary scan, product and tape reversal
in the native cost definitions is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
theorem good_bounded (ctx : Context p t n d) (vars : Finset (Fin n))
    (a : Stored p t (n:=n) (d:=d)) (ha : Good vars ctx.u ctx.J a) :
    Bounded ctx vars a := ⟨ha.1, length_le_capacity vars ctx.u ctx.J a ha⟩

omit [Fact (Nat.Prime p)] in
theorem bounded_bytes (ctx : Context p t n d) (vars : Finset (Fin n))
    (a : Stored p t (n:=n) (d:=d)) (ha : Bounded ctx vars a) :
    (Product.bytes a).length ≤
      byteCapacity n (baseWidth p t) d ctx.u ctx.J (capacity vars ctx.u ctx.J) :=
  (Product.bytes_length_le a (n+ctx.u+ctx.J)
    (valid_keyBound vars ctx.u ctx.J a ha.1)).trans (Nat.mul_le_mul_right _ ha.2)

theorem wordCost_le (B d n : ℕ) : ReadScalar.wordCost B d n ≤ wordEnvelope B d n := by
  have h := Nat.mul_le_mul_right (7*B+7) (Nat.sub_le d 1)
  dsimp [ReadScalar.wordCost,wordEnvelope]
  omega

theorem addCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (a b : Stored p t (n:=n) (d:=d)) (ha : Bounded ctx vars a) (hb : Good vars ctx.u ctx.J b) :
    addCost ctx a b ≤ addEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  let N := capacity vars ctx.u ctx.J
  have hbb := good_bounded ctx vars b hb
  have hout := add_good ctx.modulus ctx.cache vars ctx.u ctx.J a b ha.1 hb
  have ba := bounded_bytes ctx vars a ha
  have bb := bounded_bytes ctx vars b hbb
  have bo := bounded_bytes ctx vars (plus ctx a b) (good_bounded ctx vars _ hout)
  have hw := Normalize.work_le p t ctx.modulus ctx.cache Squarefree.encodeIndex
    (n+ctx.u+ctx.J) (2*N) a b (valid_keyBound vars ctx.u ctx.J a ha.1)
    (valid_keyBound vars ctx.u ctx.J b hb.1)
    (by have haN := ha.2; have hbN := hbb.2; dsimp [N]; omega)
  have hm := Nat.mul_le_mul_right
    (220*(2*N+1)*(n+ctx.u+ctx.J+d*baseWidth p t+1)+
      MomentsProgram.Dictionary.codeBranchBudget (baseWidth p t) d+2) ha.2
  have hwork := hw.trans (Nat.add_le_add_right hm 1)
  dsimp only [addCost,addEnvelope,N] at *
  omega

theorem quadraticCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (v : Triple (RingProgram.ScalarCode p t)) :
    quadraticCost ctx h v ≤
      quadraticEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  have hc := constant_good (d:=d) ctx.cache vars ctx.u ctx.J hu hJ v.c
  have hb := constant_good (d:=d) ctx.cache vars ctx.u ctx.J hu hJ v.b
  have ha := constant_good (d:=d) ctx.cache vars ctx.u ctx.J hu hJ v.a
  have hch := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ h hc.1 hh.1
  have hchb := add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ _ hch.1 hb
  have hchbh := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ h hchb.1 hh.1
  have b1 := mulCost_le ctx vars (constant ctx v.c) h (good_bounded ctx vars _ hc) hh
  have b2 := addCost_le ctx vars (mul ctx (constant ctx v.c) h) (constant ctx v.b)
    (good_bounded ctx vars _ hch) hb
  have b3 := mulCost_le ctx vars (plus ctx (mul ctx (constant ctx v.c) h) (constant ctx v.b)) h
    (good_bounded ctx vars _ hchb) hh
  have b4 := addCost_le ctx vars
    (mul ctx (plus ctx (mul ctx (constant ctx v.c) h) (constant ctx v.b)) h) (constant ctx v.a)
    (good_bounded ctx vars _ hchbh) ha
  have bw := wordCost_le (baseWidth p t) d n
  have bh := bounded_bytes ctx vars h hh
  dsimp only [quadraticCost,quadraticEnvelope]
  omega

theorem accumulatorCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (e a g : Stored p t (n:=n) (d:=d))
    (he : Good vars ctx.u ctx.J e) (ha : Bounded ctx vars a) (hg : Bounded ctx vars g) :
    accumulatorCost ctx e a g ≤
      accumulatorEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  have hag := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J a g ha.1 hg.1
  have hout := add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ e hag.1 he
  have bm := mulCost_le ctx vars a g ha hg
  have ba := addCost_le ctx vars (mul ctx a g) e (good_bounded ctx vars _ hag) he
  have be := bounded_bytes ctx vars e (good_bounded ctx vars e he)
  have baa := bounded_bytes ctx vars a ha
  have bg := bounded_bytes ctx vars g hg
  have bo := bounded_bytes ctx vars (plus ctx (mul ctx a g) e) (good_bounded ctx vars _ hout)
  dsimp only [accumulatorCost,accumulatorEnvelope]
  omega

theorem loopCost_le_oai (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h g : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (hg : Bounded ctx vars g)
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Stored p t (n:=n) (d:=d))
    (ha : Bounded ctx vars a) :
    loopCost ctx h g vs a ≤
      loopEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) vs.length := by
  induction vs generalizing a with
  | nil => simp [loopCost,loopEnvelope]
  | cons v vs ih =>
    let e := tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v
    have he : Good vars ctx.u ctx.J e :=
      triple_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J hu hJ h hh.1 v
    have hm := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J a g ha.1 hg.1
    have hn := add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ e hm.1 he
    have br := ih (plus ctx (mul ctx a g) e) (good_bounded ctx vars _ hn)
    have bq := quadraticCost_le ctx vars hu hJ h hh v
    have ba := accumulatorCost_le ctx vars e a g he ha hg
    dsimp only [loopCost,loopEnvelope] at *
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    dsimp only [e] at *
    omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le_oai
