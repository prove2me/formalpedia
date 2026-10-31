-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:14:11.939043+00:00
-- url     : https://prove2.me/submissions/4964765c-6e1b-4d30-a088-6e61d50ec3f9

import Mathlib
import Definitions.Def_OAIQ081S183
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_nativeStored_fixed_rows

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

end Sparse
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

end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

variable [CommSemiring R]

theorem subset_weight (U E : Finset V) :
    Squarefree.weight (fun v => if v ∈ U then (1:R) else 0) E =
      if E ⊆ U then 1 else 0 := by
  simp only [Squarefree.weight, Finset.prod_boole, Finset.subset_iff]

theorem specialize_atom (U : Finset V) (a : Squarefree.Index V) (c : R) :
    Moments.jetScalar (V := V) (Moments.jetEval (fun v => if v ∈ U then (1:R) else 0)
      (by intro v; split <;> simp) (Squarefree.Sparse.atom a c)) =
      if a.vars ⊆ U then Squarefree.Sparse.atom ⟨a.u,a.z,∅⟩ c else 0 := by
  simp only [Moments.jetScalar,Moments.jetEval,Polynomial.coe_mapRingHom,
    Squarefree.Sparse.atom,Polynomial.map_monomial,Squarefree.eval_monomial]
  rw [subset_weight]
  split <;> simp [Squarefree.scalar,Squarefree.monomial,show (1 : Squarefree.Support V) = ⟨∅⟩ from rfl]

theorem specializeEntries_denote (U : Finset V) (xs : List (Squarefree.Index V × R)) :
    Squarefree.Sparse.denote (specializeEntries U xs) =
      Moments.jetScalar (V := V) (Moments.jetEval (fun v => if v ∈ U then (1:R) else 0)
        (by intro v; split <;> simp) (Squarefree.Sparse.denote xs)) := by
  induction xs with
  | nil => simp [specializeEntries,Squarefree.Sparse.denote,Squarefree.Sparse.decode]
  | cons a xs ih =>
    rcases a with ⟨a,c⟩
    change Squarefree.Sparse.denote (if a.vars ⊆ U then _ else _) = _
    simp only [Squarefree.Sparse.denote,Squarefree.Sparse.decode,map_add,specialize_atom]
    by_cases h : a.vars ⊆ U <;> simp [h,Squarefree.Sparse.decode,ih,Squarefree.Sparse.denote]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
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

noncomputable section


section NativeDenotation
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (htable : ∀ i j, basis i * basis j =
  ∑ k, scalar (wordValue p t (table i j k)) * basis k)
local notation "f" => RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
local notation "D" => rawDenote (n := n) f
 theorem normalize_denote (source seed : List (Product.Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    D (Normalize.run p t M cache source seed) = D source + D seed :=
  Normalize.run_decode p t M cache scalar basis Squarefree.Sparse.atom
    Squarefree.Sparse.atom_zero Squarefree.Sparse.atom_add source seed hn


end NativeDenotation

end

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

/-- Specialization retains only valid empty-support keys, allowing collisions
which the following actual normalizer adds in the coefficient ring. -/
theorem specialized_valid {n B d u J : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n B d))
    (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1) :
    ∀ a ∈ HeadEvaluation.specializeEntries U source, Product.ValidKey ∅ u J a.1 := by
  intro a ha
  obtain ⟨b, hb, _, rfl⟩ := HeadEvaluation.mem_specializeEntries U source a ha
  exact ⟨(hsource b hb).1, by simp [Squarefree.Index.Valid], by simp⟩

noncomputable section

variable {R : Type*} [CommRing R]

/-- The physically filtered record stream evaluates at the current Boolean
correction assignment. Erasing supports alone would not imply this identity. -/
theorem specialized_raw_denote {n B d : ℕ} (U : Finset (Fin n))
    (f : RingProgram.Code (Word B) d → R) (source : List (Product.Entry n B d)) :
    rawDenote f (HeadEvaluation.specializeEntries U source) =
      Moments.jetScalar (V := Fin n) (Moments.jetEval
        (fun v => if v ∈ U then (1 : R) else 0)
        (by intro v; split <;> simp) (rawDenote f source)) := by
  unfold rawDenote Dictionary.denoteTable
  rw [← HeadEvaluation.specializeEntries_map]
  exact HeadEvaluation.specializeEntries_denote U _


end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

noncomputable section
variable {R : Type*} [CommRing R]


/-- The emitted dictionary has the same bounded keys as its decoded source;
this premise is obtained from the actual incidence constructor. -/
theorem incidence_valid {n B d : ℕ}
    (ops : SubexpSymbolicCost.RepresentedRing (RingProgram.Code (Word B) d) R)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta beta : RingProgram.Code (Word B) d)
    (rows : Fin n → List (RingProgram.Code (Word B) d)) :
    ∀ a ∈ PerturbationAssembly.outputWords ops.program J theta beta rows,
      Product.ValidKey Finset.univ u J a.1 := by
  intro a ha
  apply PerturbationAssembly.outputWords_valid ops u J hu hJ theta beta rows a.1
  simp only [Squarefree.Sparse.keys, PerturbationProgram.decodeRecords,
    List.map_map, Function.comp_def]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

end


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Coordinatewise meaning and serialization facts for the completed source
table. The row order is the original ambient order. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem RowProperty.getElem {Wit : Type*} (encode : Wit → List Bool)
    (R : ℕ → Wit → Prop) (W j : ℕ) (ws : List Wit)
    (h : RowProperty encode R W j ws) (i : ℕ) (hi : i < ws.length) :
    R (j+i) ws[i] ∧ (encode ws[i]).length=W := by
  induction ws generalizing j i with
  | nil => simp at hi
  | cons w ws ih =>
      obtain ⟨hw,hlen,ht⟩ := h
      cases i with
      | zero => simpa using And.intro hw hlen
      | succ i =>
          have hi' : i < ws.length := by simpa using hi
          simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (j+1) ht i hi'

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryJetCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical cutoff identities for immediate Boolean scalarization. These
identities retain precisely the same lifting and Taylor coefficient ranges. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog

section CanonicalSpecialization
variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- Immediate scalar specialization commutes with the exact two cutoffs.
This identifies the actual producer's canonical incidence denotation. -/
theorem jetScalar_eval_canonical {W : Type*} [DecidableEq W]
    (u J : ℕ) (U : V → Bool) (f : Squarefree.Jet V R) :
    Moments.jetScalar (V := W) (Moments.jetEval (Squarefree.boolValue U)
      (Squarefree.boolValue_idempotent U) (Squarefree.canonical u J f)) =
      Squarefree.canonical u J (Moments.jetScalar (V := W)
        (Moments.jetEval (Squarefree.boolValue U) (Squarefree.boolValue_idempotent U) f)) := by
  apply Polynomial.ext
  intro a
  apply Polynomial.ext
  intro b
  by_cases h : a < u ∧ b < J <;>
    simp [Moments.jetScalar, Moments.jetEval_coeff, Squarefree.coeff_canonical, h]

end CanonicalSpecialization

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblySourceStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The executed source predicate determines the incidence jet independently
of the particular coefficient-array witness returned by each source call. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram LeafProgram.NativeSemantics
open scoped BigOperators

theorem sourceRowProperty_polynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (xs : List (Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
    (hs : sourceRowProperty p ps P n f j xs) (i : ℕ) (hi : i < xs.length) :
    PerturbationProgram.polynomial p.ops xs[i].val =
      sourceRowFamily ps n f j (totalPackedSource p P) i := by
  have he := (RowProperty.getElem Fixed.encode _ _ 0 xs hs i hi).1
  simpa only [PolynomialExecutorProgram.meaning,PerturbationProgram.polynomial,
    SubexponentialSAT.SubexpDensePolynomial.decodeList,Nat.zero_add] using he

/-- Concrete low-branch semantics from the actual source-call postcondition. -/
theorem sourceRows_nativeStored {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (xs : List (Fixed.Array (baseWidth 3 p.t) d (p.R+1))) (hx : xs.length=n)
    (choice : List Bool) (hc : choice.length=n)
    (hs : sourceRowProperty p ps P n f j xs) :
    castJet ((pairChoice_length xs choice (hx.trans hc.symm)).trans hx)
      (nativeStored p.t p.ht p.hd p.model p.modulus p.cache u J (p.R+1) hu hJ theta
        (pairChoice xs choice)).denote =
      Squarefree.canonical u J (Moments.incidenceJet (fixedSourceRow p ps P n f j)
        (p.ops.decode theta)
        (∑ v : Fin n, (fixedSourceRow p ps P n f j v).eval (p.ops.decode theta) *
          (if choice.getD v.val false then 1 else 0))) := by
  apply nativeStored_fixed_rows p.t p.ht p.hd p.model p.modulus p.cache u J (p.R+1) n
    hu hJ theta (pairChoice xs choice) _ (fixedSourceRow p ps P n f j)
    (fun v => choice.getD v.val false)
  · intro i
    have hi : i.val < xs.length := by
      have := i.isLt
      simp only [pairChoice,List.length_zip] at this
      omega
    have he := sourceRowProperty_polynomial p ps P n f j xs hs i.val hi
    change PerturbationProgram.polynomial p.ops ((xs.zip choice)[i.val]).1.val = _
    rw [List.getElem_zip]
    exact he
  · intro i
    have hi : i.val < choice.length := by
      have := i.isLt
      simp only [pairChoice,List.length_zip] at this
      omega
    change ((xs.zip choice)[i.val]).2 = choice.getD i.val false
    simp only [List.getElem_zip,List.getD_eq_getElem _ _ hi]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableDenotation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual normalized incidence payload has the canonical scalarized
source denotation. Source arrays are witnesses produced by the finite source
machine; their full polynomial meanings identify one fixed incidence jet. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes LayoutProgram
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

theorem normalized_specialization_raw (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (U : Finset (Fin n)) (source : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawDenote f (Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []) =
      Moments.jetScalar (Moments.jetEval (fun v => if v ∈ U then (1 : R) else 0)
        (by intro v; split <;> simp) (rawDenote f source)) := by
  dsimp only
  rw [normalize_denote p t M cache scalar basis _ [] (by simp [Squarefree.Sparse.keys])]
  have hz : rawDenote (n := n)
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) [] = 0 := by
    simp [rawDenote, Dictionary.denoteTable, Squarefree.Sparse.denote, Squarefree.Sparse.decode]
  rw [hz, add_zero, QueryProducerSpace.specialized_raw_denote]

/-- Normalization and dimension transport retain the exact canonical raw
identity; the native source theorem instantiates its source equality below. -/
theorem specialized_source_realizes (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {m n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (u J : ℕ) (mask : List Bool) (source : List (Product.Entry m (baseWidth p t) d))
    (hn : m = n) (hvalid : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1)
    (jet : Squarefree.Jet (Fin n) R)
    (hsource : PerturbationAssembly.castJet hn
      (rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) source) =
        Squarefree.canonical u J jet) :
    ∃ entries : List (Product.Entry n (baseWidth p t) d),
      Product.bytes (Normalize.run p t M cache
        (HeadEvaluation.specializeEntries (Squarefree.decodeMask m mask) source) []) =
          Product.bytes entries ∧ Good ∅ u J entries ∧
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) entries =
        specializedJet u J mask jet := by
  cases hn
  refine ⟨_, rfl, normalize_good p t M cache ∅ u J _ []
    (QueryProducerSpace.specialized_valid _ source hvalid) Good.nil, ?_⟩
  rw [normalized_specialization_raw]
  change rawDenote _ source = Squarefree.canonical u J jet at hsource
  rw [hsource]
  have hh := QueryJetSemantics.jetScalar_eval_canonical (W := Fin m) u J
    (fun v => decide (v ∈ Squarefree.decodeMask m mask)) jet
  have hf : Squarefree.boolValue (R := R) (fun v => decide (v ∈ Squarefree.decodeMask m mask)) =
      (fun v => if v ∈ Squarefree.decodeMask m mask then (1 : R) else 0) := by
    funext v
    simp [Squarefree.boolValue]
  simpa only [specializedJet, hf] using hh

/-- The actual additive normalizer returns an empty-support dictionary whose
whole raw denotation is the intended specialized incidence, at both cutoffs. -/
theorem low_payload_realizes_oai {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (xs : List (Fixed.Array (baseWidth 3 p.t) d (p.R + 1)))
    (hx : xs.length = n) (choice mask : List Bool) (hc : choice.length = n)
    (hs : PerturbationAssembly.sourceRowProperty p ps P n f j xs) :
    ∃ entries : List (Product.Entry n (baseWidth 3 p.t) d),
      FactorTableNative.specializedRowPayload p.t p.model p.modulus p.cache J (p.R + 1)
        theta (PerturbationAssembly.pairChoice xs choice) mask = Product.bytes entries ∧
      Good ∅ u J entries ∧
      rawDenote p.ops.decode entries =
        specializedJet u J mask (fixedLowJet p ps P n f j theta choice) := by
  let pairs := PerturbationAssembly.pairChoice xs choice
  have hpairs : pairs.length = n :=
    (PerturbationAssembly.pairChoice_length xs choice (hx.trans hc.symm)).trans hx
  let source := QueryProducerSpace.emittedSource p.t p.model p.modulus p.cache
    J (p.R + 1) theta pairs
  have hvalid : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1 :=
    QueryProducerSpace.incidence_valid p.ops u J hu hJ theta _ _
  have hsources := PerturbationAssembly.sourceRows_nativeStored p ps P u J n f j hu hJ
    theta xs hx choice hc hs
  change PerturbationAssembly.castJet hpairs (rawDenote p.ops.decode source) =
    Squarefree.canonical u J (fixedLowJet p ps P n f j theta choice) at hsources
  exact specialized_source_realizes 3 p.t p.modulus p.cache
    (LiftRing.of (p.model.F p.t)) (RingBasis.basis (p.model.F p.t))
    u J mask source hpairs hvalid (fixedLowJet p ps P n f j theta choice) hsources


end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes_oai
