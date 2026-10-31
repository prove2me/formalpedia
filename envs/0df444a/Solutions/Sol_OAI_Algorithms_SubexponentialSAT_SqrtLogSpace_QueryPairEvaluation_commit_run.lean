-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.commit_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:26:53.012722+00:00
-- url     : https://prove2.me/submissions/59e1ae01-74b3-4969-a6f8-b55b40aea6e0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryAssembler_commitPair_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Pruned finite-difference traversal. `none`, `some false`, and `some true`
encode membership in neither set, in `E \ U`, and in `U`, respectively.
`words` specifies visit order; the streaming fold does not construct it. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs

open scoped BigOperators
open BooleanDifferences

theorem countP_ofFn {α : Type*} (p : α → Bool) (n : ℕ) (f : Fin n → α) :
    (List.ofFn f).countP p = ∑ i, if p (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih]
      omega

@[simp] theorem encodePair_weight {n : ℕ} (E U : Finset (Fin n)) :
    (encodePair E U).countP Option.isSome = E.card := by
  rw [encodePair, countP_ofFn]
  have h (i : Fin n) :
      (if (if i ∈ E then some (decide (i ∈ U)) else none).isSome then 1 else 0) =
        (if i ∈ E then 1 else 0 : ℕ) := by
    by_cases hi : i ∈ E <;> simp [hi]
  simp_rw [h]
  simp

@[simp] theorem encodePair_outer_count {n : ℕ} (E U : Finset (Fin n)) :
    ((encodePair E U).map Option.isSome).reverse.count true = E.card := by
  simp [List.count_eq_countP, List.countP_map, Function.comp_def]

theorem encodePair_inner_count {n : ℕ} (E U : Finset (Fin n)) (hU : U ⊆ E) :
    ((encodePair E U).map (fun a => a.getD false)).reverse.count true = U.card := by
  have hm : (encodePair E U).map (fun a => a.getD false) =
      List.ofFn (fun i => decide (i ∈ U)) := by
    rw [encodePair, List.map_ofFn]
    congr 1
    funext i
    by_cases hi : i ∈ E
    · simp [hi]
    · have hu : i ∉ U := fun h => hi (hU h)
      simp [hi, hu]
  rw [hm, List.count_reverse, List.count_eq_countP, countP_ofFn]
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs
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

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommRing R]

theorem denote_neg (l : Data (Index V) R) : denote (neg l) = -denote l := by
  induction l with
  | nil =>
      ext u z s
      simp [neg, denote, decode, Polynomial.coeff_neg]
  | cons a l ih =>
      have ha : atom a.1 (-a.2) = -atom a.1 a.2 := by
        simp [atom, monomial]
      simp only [neg, List.map_cons, denote, decode]
      rw [ha]
      change -atom a.1 a.2 + denote (neg l) = -(atom a.1 a.2 + denote l)
      rw [ih]
      ext u z s
      simp [Polynomial.coeff_neg, Polynomial.coeff_add, add_comm]

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {K V R : Type*} [DecidableEq V] [CommRing R]

omit [DecidableEq V] in
theorem decoded_scaled (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexponentialSAT.SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (constant : RingProgram.Code (Word (baseWidth p t)) d)
    (entries : List (Index V × RingProgram.Code (Word (baseWidth p t)) d)) :
    decoded p t M cache scalar basis (scaled p t M cache table constant entries) =
      Sparse.scale (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis constant)
        (decoded p t M cache scalar basis entries) := by
  simp only [decoded,scaled,Sparse.scale,List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply]
  congr 1
  simpa only [valueMul,RingProgram.scalarRing_program] using
    RingProgram.denote_mul (RingProgram.scalarRing p t M cache) scalar basis table htable constant a.2

omit [DecidableEq V] in
theorem decoded_neg (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexponentialSAT.SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (entries : List (Index V × RingProgram.Code (Word (baseWidth p t)) d)) :
    decoded p t M cache scalar basis (scaled p t M cache table minusOne entries) =
      Sparse.neg (decoded p t M cache scalar basis entries) := by
  rw [decoded_scaled p t M cache scalar basis table htable,hminus]
  simp [Sparse.scale,Sparse.neg]

theorem denote_neg (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexponentialSAT.SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (entries : List (Index V × RingProgram.Code (Word (baseWidth p t)) d)) :
    Sparse.denote (decoded p t M cache scalar basis (scaled p t M cache table minusOne entries)) =
      -Sparse.denote (decoded p t M cache scalar basis entries) := by
  rw [decoded_neg p t M cache scalar basis table htable minusOne hminus,Sparse.denote_neg]

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem normalize_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R) (u J : ℕ)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawValue u J f (Normalize.run p t M cache source seed) =
      rawValue u J f source + rawValue u J f seed := by
  dsimp only [rawValue]
  rw [normalize_denote p t M cache scalar basis source seed hn, map_add]

/-- A physically represented negative unit supplies the finite-difference sign. -/
theorem negation_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
      minusOne = -1)
    (a : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawValue u J f (Squarefree.ScaleProgram.scaled p t M cache table minusOne a) =
      -rawValue u J f a := by
  dsimp only [rawValue]
  have h := Squarefree.ScaleProgram.denote_neg p t M cache scalar basis table htable
    minusOne hminus a
  change rawDenote _ _ = -rawDenote _ a at h
  rw [h]
  exact map_neg (jetProjection (V := Fin n) (R := R) u J) _

end

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

/-- The sign is determined by the number of true bits, not the length or
numeric value of the binary word. -/
theorem parity_sign {R : Type*} [Ring R] (bits : List Bool) (b : Bool) :
    (if parity bits b then (-1 : R) else 1) =
      (-1 : R) ^ bits.count true * (if b then -1 else 1) := by
  induction bits generalizing b with
  | nil => cases b <;> simp [parity]
  | cons bit bits ih =>
      rw [parity, ih]
      cases b <;> cases bit <;> simp [pow_succ]

open StructuredCalls

/-- Subset pairs have the finite-difference sign even though the machine only
computes XOR and never subtracts an unbounded integer. -/
theorem pairSign_correct {R : Type*} [Ring R] (E U : List Bool)
    (hU : U.count true ≤ E.count true) :
    (if parity U (parity E false) then (-1 : R) else 1) =
      (-1 : R) ^ (E.count true - U.count true) := by
  rw [parity_sign, parity_sign]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  rw [← pow_add]
  have h : U.count true + E.count true =
      E.count true - U.count true + 2 * U.count true := by omega
  rw [h, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram


noncomputable section
variable {R : Type*} [CommRing R]

theorem signedEntries_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (sign : Bool) (a : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    TruncatedRingProgram.rawValue u J f (signedEntries p t M cache table minusOne sign a) =
      (if sign then -1 else 1) * TruncatedRingProgram.rawValue u J f a := by
  cases sign
  · simp [signedEntries]
  · simpa [signedEntries] using
      TruncatedRingProgram.negation_dense p t M cache scalar basis table htable u J minusOne hminus a

end

noncomputable section
variable {R : Type*} [CommRing R]

theorem signedSum_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (sign : Bool) (source seed : List (Product.Entry n (baseWidth p t) d))
    (hseed : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    TruncatedRingProgram.rawValue u J f (signedSum p t M cache table minusOne sign source seed) =
      (if sign then -1 else 1) * TruncatedRingProgram.rawValue u J f source +
        TruncatedRingProgram.rawValue u J f seed := by
  dsimp only [signedSum]
  rw [TruncatedRingProgram.normalize_dense p t M cache scalar basis u J _ seed hseed,
    signedEntries_dense p t M cache scalar basis table htable u J minusOne hminus sign source]

end

noncomputable section
variable {R : Type*} [CommRing R]

/-- The actual Boolean parity used by the program is the exact
finite-difference sign, including the empty support. -/
theorem pair_signedSum_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (E U : List Bool) (hU : U.count true ≤ E.count true)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hseed : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    TruncatedRingProgram.rawValue u J f
      (signedSum p t M cache table minusOne (parity U (parity E false)) source seed) =
        (-1 : Dense R u J) ^ (E.count true - U.count true) *
          TruncatedRingProgram.rawValue u J f source + TruncatedRingProgram.rawValue u J f seed := by
  dsimp only
  rw [signedSum_dense p t M cache scalar basis table htable u J minusOne hminus _ source seed hseed,
    pairSign_correct E U hU]

end

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
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

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/


/-! Denotation of the concrete raw row recurrence used by the native program. -/


/-! Instantiation at the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

theorem model_table_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (i j : Fin d) :
    RingBasis.basis (a.F t) i * RingBasis.basis (a.F t) j =
      ∑ k, SubexponentialSAT.LiftRing.of (a.F t) (wordValue 3 t (modelTable t a M cache i j k)) *
        RingBasis.basis (a.F t) k := by
  let _ : Fact (1 < 3^t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  rw [RingBasis.basis_mul (a.F t) (a.F_monic t ht) (a.F_degree t ht) i j]
  apply Finset.sum_congr rfl
  intro k _
  have hc : wordValue 3 t (modelTable t a M cache i j k) =
      RingBasis.structureConstant (a.F t) i j k := by
    change (RingProgram.scalarRing 3 t M cache).decode
      ((RingProgram.structureTableRun (RingProgram.scalarRing 3 t M cache).program
        (RingProgram.liftCoefficientsRun t a.coefficients).1).1 i j k) = _
    rw [RingProgram.structureTableRun_remainder (RingProgram.scalarRing 3 t M cache) hd]
    change (Polynomial.X ^ (i.val+j.val) %ₘ RingProgram.quotientPolynomial
      (RingProgram.scalarRing 3 t M cache) (RingProgram.liftCoefficientsRun t a.coefficients).1).coeff k = _
    rw [RingProgram.modelPolynomial t ht a M cache]
    all_goals rfl
  rw [hc]

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One executed factor step, specialized to the actual source ring, its
computed multiplication table, and the three physical assignment masters. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native
open LeafProgram.NativeSemantics LeafProgram.AssignmentSemantics
open scoped BigOperators

variable {r Q d n : ℕ}

theorem context_table_correct (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t) (i j : Fin d) :
    RingBasis.basis (p.model.F p.t) i * RingBasis.basis (p.model.F p.t) j =
      ∑ k, LiftRing.of (p.model.F p.t)
        (wordValue 3 p.t ((sourceContext p n u J width hw).table i j k)) *
        RingBasis.basis (p.model.F p.t) k :=
  model_table_correct p.t p.ht p.hd p.model p.modulus p.cache i j

end SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairCommit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The signed finite-difference term is committed to the actual node word.
The pair product and the node sum use the same stored dictionaries as their
validity and readout witnesses. Marker readout remains additive. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram
open TruncatedRingProgram QueryProgram QueryTupleState

/-- Additive readout commutes with the integer sign. No multiplicativity of
marker readout is asserted or used. -/
theorem readout_neg_one_pow_mul {R : Type*} [CommRing R] {t J : ℕ}
    (k : ℕ) (x : Dense R t J) :
    Dense.readout ((-1 : Dense R t J)^k*x)=
      (-1 : Truncated R J)^k*Dense.readout x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_assoc,neg_one_mul,map_neg,ih,
      pow_succ',mul_assoc,neg_one_mul]

/-- The coefficient-ring decoder and multiplication table are those of the
actual produced ternary ring. The sign scans the two physical pair masks. -/
theorem signed_readout {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (E U : List Bool) (hU : U.count true≤E.count true)
    (source seed : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hseed : Good ∅ q.p.t q.J seed) :
    Dense.readout (rawValue q.p.t q.J q.p.ops.decode
      (signedSum 3 q.p.t q.p.modulus q.p.cache q.ctx.table q.minus
        (parity U (parity E false)) source seed)) =
      (-1 : Truncated (q.p.model.O q.p.t) q.J)^(E.count true-U.count true)*
        Dense.readout (rawValue q.p.t q.J q.p.ops.decode source)+
        Dense.readout (rawValue q.p.t q.J q.p.ops.decode seed) := by
  have hv := pair_signedSum_dense 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.ctx.table (Factor.Semantics.context_table_correct q.p q.u q.J q.width q.widthLength)
    q.p.t q.J q.minus q.minusValue E U hU source seed hseed.nodup
  change rawValue q.p.t q.J q.p.ops.decode _ =
    (-1 : Dense (q.p.model.O q.p.t) q.p.t q.J)^(E.count true-U.count true)*
      rawValue q.p.t q.J q.p.ops.decode source+
      rawValue q.p.t q.J q.p.ops.decode seed at hv
  rw [hv,map_add,readout_neg_one_pow_mul]

theorem ready_environment {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a : Data}
    (h : QueryReady q node H high E U P a) :
    QueryAssembler.pairEnvironment a=Squarefree.ScaleProgram.environment 3 q.p.t
      q.p.modulus q.p.cache q.ctx.table q.minus (List.replicate d true) q.width := by
  simp only [QueryAssembler.pairEnvironment,h.modulus,h.width,h.scalarZero,h.table,
    h.minus,h.degree]
  rfl

/-- The actual commit changes its node word while retaining every physical
input inspected by the next pair. -/
theorem ready_frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a)
    (hf : ∀ i,i∉QueryAssembler.pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf 128 (by decide) (by decide) (by decide)).trans h.ambient
    theta := (hf 78 (by decide) (by decide) (by decide)).trans h.theta
    modulus := (hf 194 (by decide) (by decide) (by decide)).trans h.modulus
    table := (hf 201 (by decide) (by decide) (by decide)).trans h.table
    width := (hf 202 (by decide) (by decide) (by decide)).trans h.width
    scalarZero := (hf 203 (by decide) (by decide) (by decide)).trans h.scalarZero
    degree := (hf 204 (by decide) (by decide) (by decide)).trans h.degree
    one := (hf 207 (by decide) (by decide) (by decide)).trans h.one
    minus := (hf 211 (by decide) (by decide) (by decide)).trans h.minus
    precision := (hf 212 (by decide) (by decide) (by decide)).trans h.precision
    order := (hf 243 (by decide) (by decide) (by decide)).trans h.order
    zero := (hf 280 (by decide) (by decide) (by decide)).trans h.zero
    code := (hf 281 (by decide) (by decide) (by decide)).trans h.code
    clauses := (hf 700 (by decide) (by decide) (by decide)).trans h.clauses
    rows := (hf 701 (by decide) (by decide) (by decide)).trans h.rows
    rowCount := (hf 704 (by decide) (by decide) (by decide)).trans h.rowCount
    markedIndex := (hf 705 (by decide) (by decide) (by decide)).trans h.markedIndex
    markedFlag := (hf 706 (by decide) (by decide) (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf 707 (by decide) (by decide) (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf 708 (by decide) (by decide) (by decide))).trans h.indexWidth
    highMask := (hf 702 (by decide) (by decide) (by decide)).trans h.highMask
    highBits := (hf 703 (by decide) (by decide) (by decide)).trans h.highBits
    outer := (hf 858 (by decide) (by decide) (by decide)).trans h.outer
    inner := (hf 857 (by decide) (by decide) (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf 130 (by decide) (by decide) (by decide)).trans h.colors
    nodes := (hf 131 (by decide) (by decide) (by decide)).trans h.nodes
    typeWidth := (hf 132 (by decide) (by decide) (by decide)).trans h.typeWidth
    positive := (hf 710 (by decide) (by decide) (by decide)).trans h.positive
    negative := (hf 711 (by decide) (by decide) (by decide)).trans h.negative
    sourceWidth := (hf 140 (by decide) (by decide) (by decide)).trans h.sourceWidth
    power := (hf 712 (by decide) (by decide) (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf 138 (by decide) (by decide) (by decide)).trans h.radius
    offset := (hf 139 (by decide) (by decide) (by decide)).trans h.offset
    metadata := (hf 135 (by decide) (by decide) (by decide)).trans h.metadata
    plans := (hf 136 (by decide) (by decide) (by decide)).trans h.plans
    inverses := (hf 713 (by decide) (by decide) (by decide)).trans h.inverses
    negatives := (hf 714 (by decide) (by decide) (by decide)).trans h.negatives
    differences := (hf 715 (by decide) (by decide) (by decide)).trans h.differences
    ringWidth := (hf 717 (by decide) (by decide) (by decide)).trans h.ringWidth
    rowWidth := (hf 716 (by decide) (by decide) (by decide)).trans h.rowWidth
    inverseDenominator := (hf 728 (by decide) (by decide) (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hs : p.1.castAdd 128∉QueryAssembler.pairScratch ∧
        p.1.castAdd 128≠(850:Fin 896) ∧ p.1.castAdd 128≠(851:Fin 896) := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf _ hs.1 hs.2.1 hs.2.2]
    exact h.cacheCaps p hp
  · rw [hf 128 (by decide) (by decide) (by decide)]
    exact h.ambientCap
  · rw [hf 207 (by decide) (by decide) (by decide)]
    exact h.oneCap

open CommandRegisterFrames

/-- One real native commit, with the sign derived from the exact encoded
supports emitted by the bounded-memory pair traversal. All boundary, time,
and prefix conclusions concern this same execution. -/
theorem run {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool)
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E) (P B : ℕ) (a : Data)
    (hready : QueryReady q node H high
      (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
      (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P a)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (pairValue nodeValue : Truncated (q.p.model.O q.p.t) q.J)
    (hpair : PairAccumulatorMeaning q pairValue a)
    (hnode : NodeAccumulatorMeaning q nodeValue a)
    (hb : ∀ i,(a.stacks i).length≤B)
    (hcapacity : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2)≤B) :
    ∃ steps b, Eval QueryAssembler.commitPair steps a b ∧
      NodeAccumulatorMeaning q (nodeValue+(-1)^ (E.card-U.card)*pairValue) b ∧
      QueryReady q node H high
        (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
        (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P b ∧
      b.stacks 851=[] ∧
      (∀ i,i∉QueryAssembler.pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length≤B) ∧
      steps+1≤51000*(B+1)+pairUpdateBudget n (baseWidth 3 q.p.t) d q.p.t q.J
        (a.stacks 834).length (a.stacks 835).length ∧
      Trace QueryAssembler.commitPairProgram (steps+1)
        (a.withPC (some QueryAssembler.commitPairProgram.entry)) (b.withPC none) ∧
      ∀ (prefixSteps : ℕ) intermediate, prefixSteps ≤ steps + 1 →
        Trace QueryAssembler.commitPairProgram prefixSteps
          (a.withPC (some QueryAssembler.commitPairProgram.entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤896*B+51000*(B+1)+
          pairUpdateBudget n (baseWidth 3 q.p.t) d q.p.t q.J
            (a.stacks 834).length (a.stacks 835).length := by
  obtain ⟨source,hsource,hsourceGood,hsourceValue⟩ := hpair.entries
  obtain ⟨seed,hseed,hseedGood,hseedValue⟩ := hnode.entries
  have hEcount : (a.stacks 834).count true=E.card := by
    rw [he,DifferencePairs.encodePair_outer_count]
  have hUcount : (a.stacks 835).count true=U.card := by
    rw [hu,DifferencePairs.encodePair_inner_count E U hU]
  have hcount : (a.stacks 835).count true≤(a.stacks 834).count true := by
    rw [hEcount,hUcount]
    exact Finset.card_le_card hU
  obtain ⟨steps,b,hex,hgood,h850,h851,hframe,hbound,htime,htrace,hspace⟩ :=
    QueryAssembler.commitPair_eval 3 q.p.t q.p.modulus q.p.cache q.p.hz
      q.ctx.table q.minus source seed hsourceGood hseedGood
      (List.replicate d true) q.width (List.length_replicate ..) q.widthLength
      a B (ready_environment hready) hsource hseed hb hcapacity
  refine ⟨steps,b,hex,?_,ready_frame hready hframe,h851,hframe,hbound,htime,htrace,hspace⟩
  refine ⟨_,h850,hgood,?_⟩
  rw [signed_readout q (a.stacks 834) (a.stacks 835) hcount source seed hseedGood,
    hsourceValue,hseedValue,hEcount,hUcount,add_comm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem common_of_ready {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H E U : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a : State 40 896}
    (h : QueryReady q node H high E U P a) : CommonReady q node H high P a :=
  {h with}

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

private theorem start_masters {source : ProducedSource} {a b : State 40 896}
    (hm : SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : ∀ i,i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 → b.stacks i=a.stacks i) :
    SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  have hn : SignatureHeadLoader.lowStacks i∉PairNativeSetup.scratch ∧
      SignatureHeadLoader.lowStacks i≠851 ∧ SignatureHeadLoader.lowStacks i≠857 ∧
      SignatureHeadLoader.lowStacks i≠858 := by
    simp only [SignatureHeadLoader.masters,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (hf _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans (hm.stored i hi)

private theorem commit_masters {source : ProducedSource} {a b : State 40 896}
    (hm : SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : ∀ i,i∉QueryAssembler.pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) :
    SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  have hn : SignatureHeadLoader.lowStacks i∉QueryAssembler.pairScratch ∧
      SignatureHeadLoader.lowStacks i≠850 ∧ SignatureHeadLoader.lowStacks i≠851 := by
    simp only [SignatureHeadLoader.masters,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (hf _ hn.1 hn.2.1 hn.2.2).trans (hm.stored i hi)

/-- The concrete signed commit restores the loop invariant at the SAME
compact cap. Its readout is additive and occurs after the complete tuple sum. -/
theorem commit_run_oai {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin : State 40 896} (total pairValue : Truncated (q.p.model.O q.p.t) q.J)
    (a : State 40 896) (hi : Invariant q node H high P F source origin total a)
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E)
    (hready : QueryReady q node H high
      (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
      (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P a)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (hpair : PairAccumulatorMeaning q pairValue a) (hb : ∀ i,(a.stacks i).length ≤ F)
    (hcapacity : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F) :
    ∃ steps b, Eval QueryAssembler.commitPair steps a b ∧
      Invariant q node H high P F source origin (total+(-1)^(E.card-U.card)*pairValue) b ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      (∀ i,(b.stacks i).length ≤ F) ∧ steps+1 ≤ commitBudget q (n-H.card) F ∧
      QueryExecution.PrefixBound QueryAssembler.commitPair (steps+1) a
        (896*F+commitBudget q (n-H.card) F) := by
  obtain ⟨steps,b,hEval,hnode,hready',_h851,hframe,hbound,htime,_htrace,hprefix⟩ :=
    QueryPairCommit.run q node H high E U hU P F a hready he hu pairValue total
      hpair hi.accumulator hb hcapacity
  have hElen : (a.stacks 834).length=n-H.card := by
    simp [he,DifferencePairs.encodePair]
  have hUlen : (a.stacks 835).length=n-H.card := by
    simp [hu,DifferencePairs.encodePair]
  rw [hElen,hUlen] at htime hprefix
  have hf : ∀ i ∈ framePorts,b.stacks i=origin.stacks i := by
    intro i him
    have hp : ∀ j ∈ framePorts,j∉QueryAssembler.pairScratch ∧ j≠850 ∧ j≠851 := by
      simp [framePorts,QueryAssembler.pairScratch_mem,Fin.coe_ofNat_eq_mod]
    exact (hframe i (hp i him).1 (hp i him).2.1 (hp i him).2.2).trans (hi.frame i him)
  refine ⟨steps,b,hEval,⟨common_of_ready hready',hnode,fun i _=>hbound i,
    commit_masters hi.masters hframe,hf⟩,?_,hbound,htime,⟨?_⟩⟩
  · intro j
    fin_cases j <;> exact hframe _ (by decide) (by decide) (by decide)
  · intro elapsed z hz htrace i
    simpa only [commitBudget,Nat.add_assoc] using hprefix elapsed z hz htrace i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.commit_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.commit_run_oai
