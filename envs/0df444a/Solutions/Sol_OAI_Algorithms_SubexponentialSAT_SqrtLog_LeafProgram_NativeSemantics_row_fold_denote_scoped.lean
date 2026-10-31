-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:15:00.660485+00:00
-- url     : https://prove2.me/submissions/2c74da5a-a9b1-438a-b0d2-79aedc195737

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NativeSemantics_clause_denote_scoped

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Truncation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Canonical truncation before substitution

Polynomials are represented with U outermost, Z in the middle, and the X variables
innermost.  Truncation is an operation on canonical polynomial representatives;
we never assert that U = 1 defines a map out of the truncated quotient.
-/

namespace SubexponentialSAT.Truncation

noncomputable section

open scoped BigOperators

variable {R ι : Type*} [CommSemiring R]

/-- A stable coefficient reduction stays stable after adjoining a variable
and deleting high powers of that variable. -/
theorem clipAddHom_mul {A : Type*} [Semiring A] (n : ℕ) (f : A →+ A)
    (hf : ∀ a b, f (f a * f b) = f (a * b)) (P Q : Polynomial A) :
    clipAddHom n f (clipAddHom n f P * clipAddHom n f Q) =
      clipAddHom n f (P * Q) := by
  classical
  ext j
  by_cases hj : j < n
  · simp only [coeff_clipAddHom, ite_eq_left hj, Polynomial.coeff_mul, map_sum]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' : ab.1 + ab.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have ha : ab.1 < n := by omega
    have hb : ab.2 < n := by omega
    simp only [ ite_eq_left ha, ite_eq_left hb]
    exact hf _ _
  · simp [hj]

end

end SubexponentialSAT.Truncation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! U is the outer polynomial variable, Z the inner one. Support cardinality
is charged only to Z degree; no formal X support is charged to U. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

noncomputable section

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem canonical_mul (t J : ℕ) (f g : Jet V R) :
    canonical t J (canonical t J f * canonical t J g) = canonical t J (f * g) := by
  apply Truncation.clipAddHom_mul
  intro a b
  have h := Truncation.clipAddHom_mul J (AddMonoidHom.id (Poly V R))
    (fun _ _ => rfl) a b
  simpa [Truncation.clipAddHom, Truncation.truncAddHom,
    Truncation.mapCoeffs, AddMonoidHom.comp_apply] using h

end
end SubexponentialSAT.SqrtLog.Squarefree

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

namespace Index

variable {V : Type*} [DecidableEq V]

theorem Valid.join {a b : Index V} (ha : a.Valid) (hb : b.Valid) : (a.join b).Valid :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)

end Index

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem atom_add (a : Index V) (c d : R) : atom a (c + d) = atom a c + atom a d := by
  simp [atom, monomial ]

theorem atom_mul (a b : Index V) (c d : R) : atom a c * atom b d = atom (a.join b) (c*d) := by
  simp [atom, Index.join, Polynomial.monomial_mul_monomial, monomial_mul]

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

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem denote_scale (c : R) (l : Data (Index V) R) :
    denote (scale c l) = atom Index.origin c * denote l := by
  induction l with
  | nil => simp [scale, denote, decode]
  | cons a l ih =>
      simp only [scale, List.map_cons, denote, decode, mul_add]
      rw [atom_mul, Index.origin_join]
      exact congrArg (atom a.1 (c * a.2) + ·) ih

end Sparse

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

theorem ValidData.canonical {vars : Finset V} {t J : ℕ} {a : Data (Index V) R}
    (ha : ValidData vars t J a) : canonical t J (denote a) = denote a := by
  induction a with
  | nil => simp [denote, decode]
  | cons q a ih =>
      have hq : q.1 ∈ keys (q :: a) := by simp [keys]
      have htail : ValidData vars t J a := by
        intro k hk; exact ha k (by simp [keys] at hk ⊢; exact Or.inr hk)
      change Squarefree.canonical t J (atom q.1 q.2 + denote a) = atom q.1 q.2 + denote a
      rw [map_add, canonical_atom, ite_eq_left (ha q.1 hq).1, ih htail]

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
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

theorem scaled_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (entries) :
    (scaled (K := K) p t M cache table scalar entries).map Prod.fst = entries.map Prod.fst := by
  simp [scaled, List.map_map, Function.comp_def]

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Cost stage. -/

/-! Semantics stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {K V R : Type*} [DecidableEq V] [CommRing R]

theorem scaled_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (constant : RingProgram.Code (Word (baseWidth p t)) d) (entries)
    (h : (entries.map Prod.fst).Nodup) :
    ((scaled (K := K) p t M cache table constant entries).map Prod.fst).Nodup := by
  rwa [scaled_keys]

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

theorem denote_scaled (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexponentialSAT.SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (constant : RingProgram.Code (Word (baseWidth p t)) d)
    (entries : List (Index V × RingProgram.Code (Word (baseWidth p t)) d)) :
    Sparse.denote (decoded p t M cache scalar basis (scaled p t M cache table constant entries)) =
      Sparse.atom Index.origin
        (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis constant) *
          Sparse.denote (decoded p t M cache scalar basis entries) := by
  rw [decoded_scaled p t M cache scalar basis table htable,Sparse.denote_scale]

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual normalized sparse representation used by the head loops.
Proof fields erase at execution; every operation is a finite list operation.
The associated costs count ring operations and key scans. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

namespace Stored

variable {vars : Finset V} {t J : ℕ}

theorem canonical (a : Stored (R := R) vars t J) :
    Squarefree.canonical t J a.denote = a.denote := a.valid.canonical

end Stored
end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramScalarRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Flat ring coefficients may scale sparse dictionaries directly. They need
not first be serialized as a singleton sparse dictionary. This interface is
used by the native weighted-clause interpreter. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {V R : Type*} [DecidableEq V] [CommRing R]
variable {vars : Finset V} {t J : ℕ}

/-- Direct scalar scaling has precisely the truncated-multiplication meaning
used by the generic row fold. -/
theorem stored_scale_correct (c : R) (a : Moments.Stored (R := R) vars t J) :
    (Moments.Stored.scale c a).denote =
      (squarefreeAlgebra t J).mul (Squarefree.canonical t J (scalarJet c)) a.denote := by
  have hcanon := (a.valid.scale c).canonical
  rw [Sparse.denote_scale] at hcanon
  have hprod := Squarefree.canonical_mul t J (scalarJet (V := V) c) a.denote
  rw [a.canonical] at hprod
  change Sparse.denote (Sparse.scale c a.data) =
    Squarefree.canonical t J (Squarefree.canonical t J (scalarJet c) * a.denote)
  rw [Sparse.denote_scale]
  change Sparse.atom Index.origin c * a.denote =
    Squarefree.canonical t J (Squarefree.canonical t J (scalarJet c) * a.denote)
  exact hcanon.symm.trans hprod.symm

end SubexponentialSAT.SqrtLog.LeafProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native

namespace Good
variable {n B d u J : ℕ} {vars : Finset (Fin n)}

theorem decoded_valid {R : Type*} [CommRing R]
    {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (f : RingProgram.Code (Word B) d → R) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f a) :=
  Product.decoded_valid f vars u J a h.valid

end Good

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (vars : Finset (Fin n)) (u J : ℕ)

 theorem scaled_good (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (h : Good vars u J a) :
    Good vars u J (Squarefree.ScaleProgram.scaled p t M cache table c a) := by
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact h.valid y hy
  · exact Squarefree.ScaleProgram.scaled_nodup p t M cache table c a h.nodup

theorem normalize_good (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : ∀ x ∈ source, Product.ValidKey vars u J x.1) (hi : Good vars u J seed) :
    Good vars u J (Normalize.run p t M cache source seed) :=
  ⟨Normalize.run_preserves_keys p t M cache _ source seed hs hi.valid,
    Normalize.run_nodup p t M cache source seed hi.nodup⟩

theorem product_good (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good vars u J left) (hr : Good vars u J right) :
    Good vars u J (Product.run p t M cache table u J left right []) :=
  ⟨Product.run_valid p t M cache table vars u J left right [] hl.valid hr.valid (by simp),
    Product.run_nodup p t M cache table u J left right [] (by simp [Squarefree.Sparse.keys])⟩

variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))

include hone in
theorem literal_good (payload : List (Product.Entry n (baseWidth p t) d))
    (hp : Good vars u J payload) (positive : Bool) :
    Good vars u J (LiteralCallback.value p t M cache table minusOne one payload positive) := by
  cases positive
  · exact hp
  · exact normalize_good p t M cache vars u J _ one
      (scaled_good p t M cache table vars u J minusOne payload hp).valid hone

include hone hi in
theorem step_good (l : SAT.Literal (Fin n))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (Clause.step p t M cache table minusOne one incidence u J l acc) :=
  product_good p t M cache table vars u J acc _ ha
    (literal_good p t M cache table vars u J minusOne one hone _ (hi l.variable) l.positive)

include hone hi in
theorem clause_fold_good (ls : List (SAT.Literal (Fin n)))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (DynamicFold.value
      (Clause.step p t M cache table minusOne one incidence u J) ls acc) := by
  induction ls generalizing acc with
  | nil => exact ha
  | cons l ls ih => exact ih _ (step_good p t M cache table vars u J minusOne one incidence hone hi l acc ha)

include hone hi in
theorem row_step_good (w : Row.WeightedClause n (baseWidth p t) d)
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (Row.value p t M cache table minusOne one incidence u J w acc) :=
  normalize_good p t M cache vars u J _ acc
    (scaled_good p t M cache table vars u J w.scalar _
      (clause_fold_good p t M cache table vars u J minusOne one incidence hone hi w.literals one hone)).valid ha

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Denotation of the concrete raw row recurrence used by the native program. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

variable {R : Type*} [CommRing R]
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

include htable in
theorem scale_denote (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) :
    D (Squarefree.ScaleProgram.scaled p t M cache table c a) = scalarJet (f c) * D a :=
  Squarefree.ScaleProgram.denote_scaled p t M cache scalar basis table htable c a

include htable in
theorem scale_denote_canonical (vars : Finset (Fin n)) (u J : ℕ)
    (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J a) :
    D (Squarefree.ScaleProgram.scaled p t M cache table c a) =
      (squarefreeAlgebra u J).mul (Squarefree.canonical u J (scalarJet (f c))) (D a) := by
  let stored : Moments.Stored (R := R) vars u J :=
    ⟨Dictionary.denoteTable f a,ha.decoded_valid f,
      by simpa only [Dictionary.denoteTable_keys] using ha.nodup⟩
  rw [scale_denote p t M cache scalar basis table htable]
  simpa only [Moments.Stored.denote,Moments.Stored.scale,Squarefree.Sparse.denote_scale,
    scalarJet,stored,rawDenote] using stored_scale_correct (f c) stored

variable (vars : Finset (Fin n)) (u J : ℕ)
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))
variable (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
variable (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) one =
  Squarefree.canonical u J 1)

variable (jet : Fin n → Squarefree.Jet (Fin n) R)
variable (hjet : ∀ v,
  rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) (incidence v) =
    Squarefree.canonical u J (jet v))

include htable hone hi hminus honeval in
theorem row_step_denote_scoped (w : Row.WeightedClause n (baseWidth p t) d)
    (hs : ∀ l ∈ w.literals, D (incidence l.variable) = Squarefree.canonical u J (jet l.variable))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    D (Row.value p t M cache table minusOne one incidence u J w acc) =
      D acc + (squarefreeAlgebra u J).mul (Squarefree.canonical u J (scalarJet (f w.scalar)))
        (clauseValue (squarefreeAlgebra u J) (fun v => Squarefree.canonical u J (jet v)) w.literals) := by
  unfold Row.value
  rw [normalize_denote p t M cache scalar basis _ acc ha.nodup]
  rw [scale_denote_canonical p t M cache scalar basis table htable vars u J w.scalar
    (Row.clauseValue p t M cache table minusOne one incidence u J w)
    (clause_fold_good p t M cache table vars u J minusOne one incidence hone hi w.literals one hone)]
  rw [clause_denote_scoped p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval jet w hs]
  exact add_comm _ _

include htable hone hi hminus honeval in
theorem row_fold_denote_scoped_oai (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (hs : ∀ w ∈ ws, ∀ l ∈ w.literals,
      D (incidence l.variable) = Squarefree.canonical u J (jet l.variable))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    D (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws acc) =
      rowFoldValue (squarefreeAlgebra u J) (fun c => Squarefree.canonical u J (scalarJet c))
        (fun v => Squarefree.canonical u J (jet v)) (sourceTerms f ws) (D acc) := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    simp only [DynamicFold.value]
    rw [ih (fun a ha => hs a (by simp [ha])) _
      (row_step_good p t M cache table vars u J minusOne one incidence hone hi w acc ha)]
    rw [row_step_denote_scoped p t M cache scalar basis table htable vars u J
      minusOne one incidence hone hi hminus honeval jet w (hs w (by simp)) acc ha]
    rfl

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Instantiation at the actual supplied-polynomial unramified ring. -/


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped_oai.{u_1}
