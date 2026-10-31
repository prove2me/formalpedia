-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:00:12.835826+00:00
-- url     : https://prove2.me/submissions/f491400c-2a35-4da4-8e6d-59ae796b50c0

import Mathlib
import Definitions.Def_OAIQ081S139

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native injection of a base coefficient into the first coordinate of an
extension-ring coefficient. The remaining coordinates are physically copied
from the canonical zero word. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing SubexpScanPrimitives
open IdempotentPreparationProgram

theorem scalarVector_denote (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {R : Type*} [CommRing R] (φ : ZMod (p^t) →+* R)
    {dimension : ℕ} (hd : 0 < dimension) (basis : Fin dimension → R)
    (hb : basis ⟨0,hd⟩=1) (word : RingProgram.ScalarCode p t) :
    RingProgram.denote (RingProgram.scalarRing p t M cache) φ basis
      (scalarVector cache.zero word) = φ (wordValue p t word) := by
  unfold RingProgram.denote
  rw [Finset.sum_eq_single ⟨0,hd⟩]
  · simp [scalarVector,RingProgram.scalarRing,hb]
  · intro i _ hi
    have hiv : i.val≠0 := by intro h; apply hi; exact Fin.ext h
    simp [scalarVector,hiv,RingProgram.scalarRing,cache.zero_correct]
  · simp

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

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

section Decode

variable [AddCommMonoid A]

omit [DecidableEq K] [AddCommMonoid R] in
theorem decode_append (atom : K → R → A) (a b : Data K R) :
    decode atom (a ++ b) = decode atom a + decode atom b := by
  induction a with
  | nil => simp [decode]
  | cons h a ih => simp [decode, ih, add_assoc]

theorem decode_split (atom : K → R → A) (hzero : ∀ k, atom k 0 = 0)
    (hadd : ∀ k a b, atom k (a + b) = atom k a + atom k b) (k : K) (l : Data K R) :
    decode atom l = atom k (fetch k l) + decode atom (erase k l) := by
  induction l with
  | nil => simp [decode, fetch, erase, hzero]
  | cons a l ih =>
      rcases a with ⟨j, c⟩
      by_cases h : j = k
      · subst j
        simpa [decode, fetch, erase, hadd, add_assoc] using congrArg (atom k c + ·) ih
      · simp [decode, fetch, erase, h, ih, add_left_comm]

theorem decode_insert (atom : K → R → A) (hzero : ∀ k, atom k 0 = 0)
    (hadd : ∀ k a b, atom k (a + b) = atom k a + atom k b)
    (k : K) (c : R) (l : Data K R) :
    decode atom (insert k c l) = atom k c + decode atom l := by
  simp only [insert, decode, hadd, add_assoc]
  rw [← decode_split atom hzero hadd]

end Decode
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

section Semantic
variable [AddCommMonoid C]

private theorem fetch_zero_of_not_mem (entries : Sparse.Data K C) (k : K)
    (h : k ∉ Sparse.keys entries) : Sparse.fetch k entries = 0 := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    have hj : j ≠ k := by intro he; subst j; exact h (by simp [Sparse.keys])
    have ht : k ∉ Sparse.keys entries := by
      intro he; exact h (by simp only [Sparse.keys, List.map_cons, List.mem_cons]; exact Or.inr he)
    simp [Sparse.fetch, hj, ih ht]

/-- On a normalized dictionary, mathematical additive fetch is first-match lookup. -/
theorem fetch_eq_lookup (entries : Sparse.Data K C) (k : K)
    (hn : (Sparse.keys entries).Nodup) :
    Sparse.fetch k entries = (entries.lookup k).getD 0 := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    have hh : j ∉ Sparse.keys entries ∧ (Sparse.keys entries).Nodup := by
      simpa [Sparse.keys] using hn
    by_cases h : j = k
    · subst j
      simp [Sparse.fetch, fetch_zero_of_not_mem entries k hh.1]
    · simp [Sparse.fetch, h, List.lookup_cons, beq_false_of_ne (Ne.symm h), ih hh.2]
end Semantic

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Semantic contract of the primitive dictionary replacement, including its
use as the storage step of normalized additive insertion. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram

variable {K C A : Type*} [DecidableEq K] [AddCommMonoid C]

section Decode
variable [AddCommMonoid A]

omit [DecidableEq K] [AddCommMonoid C] in
theorem decode_reverse (atom : K → C → A) (entries : Sparse.Data K C) :
    Sparse.decode atom entries.reverse = Sparse.decode atom entries := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    simp [List.reverse_cons,Sparse.decode_append,Sparse.decode,ih,add_comm]

omit [AddCommMonoid C] in
theorem decode_put (atom : K → C → A) (k : K) (c : C) (entries : Sparse.Data K C) :
    Sparse.decode atom (put k c entries) = atom k c + Sparse.decode atom (Sparse.erase k entries) := by
  simp only [put,Sparse.decode,decode_reverse]


/-- Reversal changes storage order only. Adding the old coefficient first
makes primitive replacement exactly the semantic additive insertion. -/
theorem decode_put_add (atom : K → C → A) (k : K) (c : C) (entries : Sparse.Data K C) :
    Sparse.decode atom (put k (c + Sparse.fetch k entries) entries) =
      Sparse.decode atom (Sparse.insert k c entries) := by
  simp only [decode_put,Sparse.insert,Sparse.decode]
end Decode

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
theorem denoteTable_cons (f : C → R) (a : K × C) (entries : List (K × C)) :
    denoteTable f (a::entries) = (a.1,f a.2)::denoteTable f entries := rfl

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_reverse (f : C → R) (entries : List (K × C)) :
    denoteTable f entries.reverse = (denoteTable f entries).reverse := by
  simp [denoteTable]

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_keys (f : C → R) (entries : List (K × C)) :
    Squarefree.Sparse.keys (denoteTable f entries) = Squarefree.Sparse.keys entries := by
  simp [denoteTable,Squarefree.Sparse.keys,List.map_map,Function.comp_def]

omit [CommRing R] in
theorem denoteTable_lookup (f : C → R) (entries : List (K × C)) (k : K) :
    (denoteTable f entries).lookup k = (entries.lookup k).map f := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    by_cases h : j=k
    · subst j; simp [denoteTable]
    · simp only [denoteTable,List.map_cons,List.lookup_cons] at ih ⊢
      simp [beq_false_of_ne (Ne.symm h),ih]

omit [CommRing R] in
theorem denoteTable_erase (f : C → R) (entries : List (K × C)) (k : K) :
    denoteTable f (Squarefree.Sparse.erase k entries) =
      Squarefree.Sparse.erase k (denoteTable f entries) := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    by_cases h : a.1=k <;> simp [denoteTable,Squarefree.Sparse.erase,h] at ih ⊢ <;> exact ih

theorem denoteTable_insertCode (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (scalar : ZMod (p^t) →+* R)
    {d : ℕ} (basis : Fin d → R)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    denoteTable f (insertCode p t M cache k x entries) =
      Squarefree.Program.put k (f x + Squarefree.Sparse.fetch k (denoteTable f entries)) (denoteTable f entries) := by
  dsimp only
  let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
  have hf := Squarefree.Program.fetch_eq_lookup (denoteTable f entries) k
    (by simpa only [denoteTable_keys] using hn)
  rw [denoteTable_lookup] at hf
  have ha (y : RingProgram.Code (Word (baseWidth p t)) d) :
      f (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1 = f x + f y :=
    RingProgram.denote_add (RingProgram.scalarRing p t M cache) scalar basis x y
  change denoteTable f _ = Squarefree.Program.put k
    (f x + Squarefree.Sparse.fetch k (denoteTable f entries)) (denoteTable f entries)
  cases he : entries.lookup k
  · have hz : Squarefree.Sparse.fetch k (denoteTable f entries) = 0 := by simpa [he] using hf
    simp only [insertCode,he,denoteTable_cons,denoteTable_reverse,Squarefree.Program.put]
    change (k,f x)::(denoteTable f (Squarefree.Sparse.erase k entries)).reverse =
      (k,f x + Squarefree.Sparse.fetch k (denoteTable f entries))::
        (Squarefree.Sparse.erase k (denoteTable f entries)).reverse
    rw [hz,add_zero,denoteTable_erase]
  · rename_i y
    have hy : Squarefree.Sparse.fetch k (denoteTable f entries) = f y := by simpa [he] using hf
    simp only [insertCode,he,denoteTable_cons,denoteTable_reverse,Squarefree.Program.put]
    change (k,f (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)::
        (denoteTable f (Squarefree.Sparse.erase k entries)).reverse =
      (k,f x + Squarefree.Sparse.fetch k (denoteTable f entries))::
        (Squarefree.Sparse.erase k (denoteTable f entries)).reverse
    rw [ha,hy,denoteTable_erase]

/-- Actual code insertion preserves sparse polynomial addition semantics. -/
theorem insertCode_decode (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (scalar : ZMod (p^t) →+* R)
    {d : ℕ} (basis : Fin d → R) (atom : K → R → A)
    (hz : ∀ k, atom k 0 = 0) (ha : ∀ k x y, atom k (x+y) = atom k x + atom k y)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Squarefree.Sparse.decode atom (denoteTable f (insertCode p t M cache k x entries)) =
      atom k (f x) + Squarefree.Sparse.decode atom (denoteTable f entries) := by
  dsimp only
  rw [denoteTable_insertCode p t M cache scalar basis entries k x hn,
    Squarefree.Program.decode_put_add,Squarefree.Sparse.decode_insert atom hz ha]

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

/-- The streaming machine's output is exactly the sum of source and seed
polynomials, despite the implementation's reversal of stored table order. -/
theorem run_decode (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (scalar : ZMod (p^t) →+* R)
    {d : ℕ} (basis : Fin d → R) (atom : K → R → A)
    (hz : ∀ k, atom k 0 = 0) (ha : ∀ k x y, atom k (x+y) = atom k x + atom k y)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Squarefree.Sparse.decode atom (Dictionary.denoteTable f (run p t M cache source seed)) =
      Squarefree.Sparse.decode atom (Dictionary.denoteTable f source) +
      Squarefree.Sparse.decode atom (Dictionary.denoteTable f seed) := by
  dsimp only
  induction source generalizing seed with
  | nil => simp [run,Dictionary.denoteTable,Squarefree.Sparse.decode]
  | cons a source ih =>
    rw [run,ih _ (insertCode_nodup p t M cache a.1 a.2 seed hn),
      Dictionary.insertCode_decode p t M cache scalar basis atom hz ha seed a.1 a.2 hn]
    simp only [Dictionary.denoteTable,List.map_cons,Squarefree.Sparse.decode]
    simp only [add_assoc,add_left_comm]

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

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem atom_add (a : Index V) (c d : R) : atom a (c + d) = atom a c + atom a d := by
  simp [atom, monomial ]

theorem atom_mul (a b : Index V) (c d : R) : atom a c * atom b d = atom (a.join b) (c*d) := by
  simp [atom, Index.join, Polynomial.monomial_mul_monomial, monomial_mul]

theorem denote_row (t J : ℕ) (a : Index V × R) (b : Data (Index V) R) :
    denote (row t J a b) = canonical t J (atom a.1 a.2 * denote b) := by
  induction b with
  | nil => simp [row, denote, decode]
  | cons h b ih =>
      simp only [row, denote, decode, mul_add, map_add, atom_mul]
      rw [canonical_atom]
      by_cases hk : (a.1.join h.1).Kept t J <;> simp [hk, decode, ih, denote]

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem decoded_row (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Dictionary.denoteTable f
      (keptJoin a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right)) =
      Squarefree.Sparse.row u J (a.1,f a.2) (Dictionary.denoteTable f right) := by
  dsimp only
  induction right with
  | nil => rfl
  | cons b right ih =>
    have hm := RingProgram.denote_mul (RingProgram.scalarRing p t M cache) scalar basis table htable a.2 b.2
    by_cases h : (a.1.join b.1).Kept u J <;>
      simp only [Squarefree.ScaleProgram.scaled,List.map_cons,keptJoin,h,ite_true, if_true,ite_false,
        Dictionary.denoteTable,Squarefree.Sparse.row] at ih ⊢
    · rw [ih]
      congr 2
    · exact ih

theorem block_denote (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Squarefree.Sparse.denote (Dictionary.denoteTable f (block p t M cache table u J a right)) =
      Squarefree.canonical u J (Squarefree.Sparse.atom a.1 (f a.2) *
        Squarefree.Sparse.denote (Dictionary.denoteTable f right)) := by
  dsimp only
  unfold block
  rw [show Dictionary.denoteTable
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis)
      (keptJoin a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right)).reverse =
    (Dictionary.denoteTable
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis)
      (keptJoin a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right))).reverse by
        simp [Dictionary.denoteTable]]
  rw [Squarefree.Sparse.denote,Squarefree.Program.decode_reverse,
    decoded_row p t M cache scalar basis table htable u J a right]
  exact Squarefree.Sparse.denote_row u J _ _

theorem run_denote (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (left right seed : List (Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Squarefree.Sparse.denote (Dictionary.denoteTable f (run p t M cache table u J left right seed)) =
      Squarefree.canonical u J (Squarefree.Sparse.denote (Dictionary.denoteTable f left) *
        Squarefree.Sparse.denote (Dictionary.denoteTable f right)) +
      Squarefree.Sparse.denote (Dictionary.denoteTable f seed) := by
  dsimp only
  induction left generalizing seed with
  | nil => simp [run,Dictionary.denoteTable,Squarefree.Sparse.denote,Squarefree.Sparse.decode]
  | cons a left ih =>
    rw [run,ih _ (Normalize.run_nodup p t M cache _ seed hn)]
    have hsum := Normalize.run_decode p t M cache scalar basis
      Squarefree.Sparse.atom Squarefree.Sparse.atom_zero Squarefree.Sparse.atom_add
      (block p t M cache table u J a right) seed hn
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    change Squarefree.Sparse.denote (Dictionary.denoteTable f
      (Normalize.run p t M cache (block p t M cache table u J a right) seed)) =
      Squarefree.Sparse.denote (Dictionary.denoteTable f (block p t M cache table u J a right)) +
      Squarefree.Sparse.denote (Dictionary.denoteTable f seed) at hsum
    rw [hsum,block_denote p t M cache scalar basis table htable u J a right]
    let lv := Squarefree.Sparse.denote (Dictionary.denoteTable f left)
    let rv := Squarefree.Sparse.denote (Dictionary.denoteTable f right)
    let sv := Squarefree.Sparse.denote (Dictionary.denoteTable f seed)
    let av := Squarefree.Sparse.atom a.1 (f a.2)
    change Squarefree.canonical u J (lv*rv) +
      (Squarefree.canonical u J (av*rv)+sv) =
      Squarefree.canonical u J ((av+lv)*rv)+sv
    rw [add_mul,map_add]
    exact (add_assoc _ _ _).symm.trans (congrArg (fun x => x+sv) (add_comm _ _))

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable support extraction for the normalized sparse squarefree jets.
Projection erases X after extracting one requested support, leaving U and Z.
All operations preserve the same bounded sparse representation. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem ringScalar_eq_atom (c : R) :
    ringScalar (V := V) c = Sparse.atom Index.origin c := by
  simp [ringScalar, Sparse.atom, Index.origin]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem tripleStored_nodup
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (h : Stored p t (n:=n) (d:=d)) (v : Triple (RingProgram.ScalarCode p t)) :
    (Squarefree.Sparse.keys (tripleStored p t M cache table uCap J h v)).Nodup := by
  exact Normalize.run_nodup p t M cache _ _ (constantStored_nodup p t cache v.a)

variable {R : Type*} [CommRing R] (φ : ZMod (p^t) →+* R) (basis : Fin d → R)

theorem addStored_denote (a b : Stored p t (n:=n) (d:=d))
    (hb : (Squarefree.Sparse.keys b).Nodup) :
    storedDenote p t M cache φ basis (addStored p t M cache a b)=
      storedDenote p t M cache φ basis a+storedDenote p t M cache φ basis b := by
  exact Normalize.run_decode p t M cache φ basis Squarefree.Sparse.atom
    Squarefree.Sparse.atom_zero Squarefree.Sparse.atom_add a b hb

theorem mulStored_denote
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (uCap J : ℕ) (a b : Stored p t (n:=n) (d:=d)) :
    storedDenote p t M cache φ basis (mulStored p t M cache table uCap J a b)=
      Squarefree.canonical (V:=Fin n) (R:=R) uCap J
        (storedDenote p t M cache φ basis a*storedDenote p t M cache φ basis b) := by
  simpa [mulStored,storedDenote,MomentsProgram.Dictionary.denoteTable,
    Squarefree.Sparse.denote,Squarefree.Sparse.decode] using
    Product.run_denote p t M cache φ basis table htable uCap J a b [] (by simp [Squarefree.Sparse.keys])

theorem constantStored_denote (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J) (word : RingProgram.ScalarCode p t) :
    storedDenote p t M cache φ basis (constantStored p t cache (n:=n) word)=
      Squarefree.canonical (V:=Fin n) (R:=R) uCap J
        ((Moments.ringScalar (V:=Fin n)).comp φ (wordValue p t word)) := by
  simp only [storedDenote,constantStored,MomentsProgram.Dictionary.denoteTable,
    List.map_cons,List.map_nil,Squarefree.Sparse.denote,Squarefree.Sparse.decode,
    RingHom.comp_apply,add_zero]
  rw [scalarVector_denote p t M cache φ hd basis hb,Moments.ringScalar_eq_atom,
    Squarefree.Sparse.canonical_atom]
  simp [Squarefree.Index.origin,Squarefree.Index.Kept,hu,hj]

theorem tripleStored_denote
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J)
    (h : Stored p t (n:=n) (d:=d)) (v : Triple (RingProgram.ScalarCode p t)) :
    storedDenote p t M cache φ basis (tripleStored p t M cache table uCap J h v)=
      tripleAlgebra (LeafProgram.projectedAlgebra (Squarefree.canonical (V:=Fin n) (R:=R) uCap J))
        (fun c => Squarefree.canonical (V:=Fin n) (R:=R) uCap J
          ((Moments.ringScalar (V:=Fin n)).comp φ (wordValue p t c)))
        (storedDenote p t M cache φ basis h) v := by
  unfold tripleStored
  rw [addStored_denote p t M cache φ basis _ _ (constantStored_nodup p t cache v.a)]
  rw [mulStored_denote p t M cache φ basis table htable]
  rw [addStored_denote p t M cache φ basis _ _ (constantStored_nodup p t cache v.b)]
  rw [mulStored_denote p t M cache φ basis table htable]
  simp only [constantStored_denote p t M cache φ basis hd hb uCap J hu hj,
    tripleAlgebra,LeafProgram.projectedAlgebra]

theorem descendingStored_denote_oai
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J)
    (h g : Stored p t (n:=n) (d:=d)) (vs : List (Triple (RingProgram.ScalarCode p t)))
    (acc : Stored p t (n:=n) (d:=d)) :
    storedDenote p t M cache φ basis (descendingStored p t M cache table uCap J h g vs acc)=
      descendingAlgebra (LeafProgram.projectedAlgebra (Squarefree.canonical (V:=Fin n) (R:=R) uCap J))
        (fun c => Squarefree.canonical (V:=Fin n) (R:=R) uCap J
          ((Moments.ringScalar (V:=Fin n)).comp φ (wordValue p t c)))
        (storedDenote p t M cache φ basis h) (storedDenote p t M cache φ basis g)
        vs (storedDenote p t M cache φ basis acc) := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
    change storedDenote p t M cache φ basis
      (descendingStored p t M cache table uCap J h g vs
        (addStored p t M cache (mulStored p t M cache table uCap J acc g)
          (tripleStored p t M cache table uCap J h v))) = _
    rw [ih,addStored_denote p t M cache φ basis _ _ (tripleStored_nodup p t M cache table uCap J h v),
      mulStored_denote p t M cache φ basis table htable,
      tripleStored_denote p t M cache φ basis table htable hd hb uCap J hu hj]
    rfl

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingStored_denote_oai.{u_1}
