-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:56:08.066247+00:00
-- url     : https://prove2.me/submissions/c1cfc85d-8ecf-4969-9c1d-1da675415bb8

import Mathlib
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S151

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact semantics for the concrete loops when multiplication clips U and Z.
The normal form is additive but is not falsely treated as a ring homomorphism.
Every intermediate clipping is justified by the two-sided product identity. -/

namespace SubexponentialSAT.SqrtLog.Moments

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

/-- The two actual truncations are idempotent, coefficient by coefficient. -/
theorem canonical_idempotent (t J : ℕ) (a : Squarefree.Jet V R) :
    Squarefree.canonical t J (Squarefree.canonical t J a) = Squarefree.canonical t J a := by
  ext u z
  by_cases h : u < t ∧ z < J <;> simp [Squarefree.coeff_canonical, h]


theorem canonical_mul_left (t J : ℕ) (a b : Squarefree.Jet V R) :
    Squarefree.canonical t J (Squarefree.canonical t J a * b) =
      Squarefree.canonical t J (a * b) := by
  calc
    _ = Squarefree.canonical t J
        (Squarefree.canonical t J (Squarefree.canonical t J a) * Squarefree.canonical t J b) :=
      (Squarefree.canonical_mul t J (Squarefree.canonical t J a) b).symm
    _ = _ := by rw [canonical_idempotent, Squarefree.canonical_mul]

theorem canonical_mul_right (t J : ℕ) (a b : Squarefree.Jet V R) :
    Squarefree.canonical t J (a * Squarefree.canonical t J b) =
      Squarefree.canonical t J (a * b) := by
  rw [mul_comm a (Squarefree.canonical t J b), canonical_mul_left, mul_comm b a]

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

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierArithmetic. -/

/-! Native construction of the cubic multiplier before its U shift. -/

/-! Source component: IdempotentApplyProgramMultiplier. -/

/-! Concrete preparation of the stored multiplier used by native Horner evaluation. -/

/-! Source component: IdempotentApplyProgramMultiplierSemantics. -/

/-! The multiplier produced by the native preparation is U H(H-1)(H-2). -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open scoped BigOperators
open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R]

private theorem decode_reverse {K C A : Type*} [AddCommMonoid C] [AddCommMonoid A]
    (atom : K → C → A) (xs : List (K×C)) :
    Squarefree.Sparse.decode atom xs.reverse=Squarefree.Sparse.decode atom xs := by
  classical
  exact Squarefree.Program.decode_reverse atom xs

omit [Fact p.Prime] in
theorem shiftForward_denote (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (f : RingProgram.Code (Word (baseWidth p t)) d → R)
    (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    Squarefree.Sparse.denote (MomentsProgram.Dictionary.denoteTable f (shiftForward a u J xs))=
      Squarefree.canonical u J (Squarefree.Sparse.atom a 1 *
        Squarefree.Sparse.denote (MomentsProgram.Dictionary.denoteTable f xs)) := by
  induction xs with
  | nil => simp [shiftForward,MomentsProgram.Dictionary.denoteTable,Squarefree.Sparse.denote,
      Squarefree.Sparse.decode]
  | cons x xs ih =>
    rcases x with ⟨b,c⟩
    by_cases hk:(a.join b).Kept u J
    all_goals
      simp only [shiftForward,hk,ite_true, if_true,ite_false,MomentsProgram.Dictionary.denoteTable,
        List.map_cons,Squarefree.Sparse.denote,Squarefree.Sparse.decode,mul_add,map_add,
        Squarefree.Sparse.atom_mul,one_mul,Squarefree.Sparse.canonical_atom,ite_true,ite_false,
        zero_add] at ih ⊢
      first
      | exact congrArg (fun z => Squarefree.Sparse.atom (a.join b) (f c)+z) ih
      | exact ih

theorem shifted_denote (c : Context p t n d) (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
    (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    storedDenote p t c.modulus c.cache φ basis (shifted c xs)=
      Squarefree.canonical c.u c.J (Squarefree.Sparse.atom (uKey n) 1 *
        storedDenote p t c.modulus c.cache φ basis xs) := by
  unfold storedDenote shifted
  rw [MomentsProgram.Dictionary.denoteTable_reverse]
  change Squarefree.Sparse.decode _ _ = _
  rw [decode_reverse]
  exact shiftForward_denote _ _ _ _ _

/-- Cached one and minus-one are checked by their represented ring meanings;
no premise supplies the desired multiplier or its denotation. -/
theorem prepared_denote_oai (c : Context p t n d) (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (c.table i j k))*basis k)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t c.modulus c.cache) φ basis minus = -1)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (honeKeys : (Squarefree.Sparse.keys one).Nodup)
    (hone : storedDenote p t c.modulus c.cache φ basis one=Squarefree.canonical c.u c.J 1)
    (H : Squarefree.Jet (Fin n) R)
    (hh : storedDenote p t c.modulus c.cache φ basis h=Squarefree.canonical c.u c.J H) :
    storedDenote p t c.modulus c.cache φ basis (prepared c minus h one)=
      Squarefree.canonical c.u c.J
        (Squarefree.Sparse.atom (uKey n) 1 * IdempotentProgram.hValue H) := by
  let a:=complemented c minus h one
  let b:=plus c a one
  let q:=mul c b a
  have hscaled : storedDenote p t c.modulus c.cache φ basis (Squarefree.ScaleProgram.scaled p t c.modulus c.cache c.table minus h) = -storedDenote p t c.modulus c.cache φ basis h := by
    exact Squarefree.ScaleProgram.denote_neg p t c.modulus c.cache φ basis c.table htable minus hminus h
  have ha : storedDenote p t c.modulus c.cache φ basis a=Squarefree.canonical c.u c.J (1-H) := by
    change storedDenote p t c.modulus c.cache φ basis (addStored p t c.modulus c.cache
      (Squarefree.ScaleProgram.scaled p t c.modulus c.cache c.table minus h) one)=_
    rw [addStored_denote p t c.modulus c.cache φ basis _ _ honeKeys,hscaled,hone,hh]
    have hs : Squarefree.canonical c.u c.J (1-H) =
        Squarefree.canonical c.u c.J 1 - Squarefree.canonical c.u c.J H :=
      map_sub (Squarefree.canonical (V:=Fin n) (R:=R) c.u c.J) 1 H
    rw [hs]
    abel
  have hb : storedDenote p t c.modulus c.cache φ basis b=Squarefree.canonical c.u c.J (2-H) := by
    change storedDenote p t c.modulus c.cache φ basis (addStored p t c.modulus c.cache a one)=_
    rw [addStored_denote p t c.modulus c.cache φ basis _ _ honeKeys,ha,hone,←map_add]
    congr 1
    ring
  have hq : storedDenote p t c.modulus c.cache φ basis q=Squarefree.canonical c.u c.J ((2-H)*(1-H)) := by
    change storedDenote p t c.modulus c.cache φ basis (mulStored p t c.modulus c.cache c.table c.u c.J b a)=_
    rw [mulStored_denote p t c.modulus c.cache φ basis c.table htable,hb,ha,Squarefree.canonical_mul]
  have hidempotent : ((2-H)*(1-H))*H = IdempotentProgram.hValue H := by
    unfold IdempotentProgram.hValue
    ring
  have hg : storedDenote p t c.modulus c.cache φ basis (cubic c minus h one)=Squarefree.canonical c.u c.J (IdempotentProgram.hValue H) := by
    change storedDenote p t c.modulus c.cache φ basis (mulStored p t c.modulus c.cache c.table c.u c.J q h)=_
    rw [mulStored_denote p t c.modulus c.cache φ basis c.table htable,hq,hh,Squarefree.canonical_mul]
    exact congrArg (Squarefree.canonical c.u c.J) hidempotent
  change storedDenote p t c.modulus c.cache φ basis (shifted c (cubic c minus h one))=_
  rw [shifted_denote c φ basis,hg,Moments.canonical_mul_right]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepared_denote_oai.{u_1}
