-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.clause_denote_scoped
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:17:47.903087+00:00
-- url     : https://prove2.me/submissions/4e66e869-2010-4e9c-8b0f-09bc2475312f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S144
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramProjection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse hash circuits commute with a canonical additive projection whose
product is stable. This is the bridge from truncated sparse operations to the
single untruncated source polynomial; no false ring-homomorphism claim about
canonical representatives is required. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [CommRing R]

theorem literalValue_projected (project : R →+ R) (value : V → R)
    (l : SAT.Literal V) :
    literalValue (projectedAlgebra project) (fun v => project (value v)) l =
      project (literalValue (ringAlgebra R) value l) := by
  cases hp : l.positive <;>
    simp [literalValue, projectedAlgebra, ringAlgebra, hp]

theorem clauseValue_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (value : V → R) (ls : List (SAT.Literal V)) :
    clauseValue (projectedAlgebra project) (fun v => project (value v)) ls =
      project (clauseValue (ringAlgebra R) value ls) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      change project (literalValue (projectedAlgebra project) (fun v => project (value v)) l *
        clauseValue (projectedAlgebra project) (fun v => project (value v)) ls) = _
      rw [literalValue_projected, ih, hprod]
      rfl

end SubexponentialSAT.SqrtLog.LeafProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFolded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Left-fold semantics for the physical record interpreter. Canonical sparse
lists need not be equal under reassociation; their denotations are the same
canonical projection of the common source polynomial. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [CommRing R]

theorem clauseFoldValue_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (value : V → R) (ls : List (SAT.Literal V)) (init : R) :
    clauseFoldValue (projectedAlgebra project) (fun v => project (value v)) ls (project init) =
      project (init * clauseValue (ringAlgebra R) value ls) := by
  induction ls generalizing init with
  | nil => simp [clauseFoldValue, clauseValue, ringAlgebra]
  | cons l ls ih =>
      change clauseFoldValue (projectedAlgebra project) (fun v => project (value v)) ls
        (project (project init * literalValue (projectedAlgebra project)
          (fun v => project (value v)) l)) = _
      rw [literalValue_projected, hprod, ih]
      change project ((init * literalValue (ringAlgebra R) value l) *
        clauseValue (ringAlgebra R) value ls) =
          project (init * (literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls))
      rw [mul_assoc]

theorem clauseFoldValue_projected_one (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (value : V → R) (ls : List (SAT.Literal V)) :
    clauseFoldValue (projectedAlgebra project) (fun v => project (value v)) ls (project 1) =
      clauseValue (projectedAlgebra project) (fun v => project (value v)) ls := by
  rw [clauseFoldValue_projected project hprod, one_mul, clauseValue_projected project hprod]

end SubexponentialSAT.SqrtLog.LeafProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/


/-! Denotation of the concrete raw row recurrence used by the native program. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

/-- A clause fold only reads the variables of its listed literals. -/
theorem clauseFold_congr {A V : Type*} (alg : Algebra A) (x y : V → A)
    (ls : List (SAT.Literal V))
    (h : ∀ l ∈ ls, x l.variable = y l.variable) (acc : A) :
    clauseFoldValue alg x ls acc = clauseFoldValue alg y ls acc := by
  induction ls generalizing acc with
  | nil => rfl
  | cons l ls ih =>
    have hl : literalValue alg x l = literalValue alg y l := by
      simp only [literalValue,h l (by simp)]
    change clauseFoldValue alg x ls (alg.mul acc (literalValue alg x l)) =
      clauseFoldValue alg y ls (alg.mul acc (literalValue alg y l))
    rw [hl]
    exact ih (fun a ha => h a (by simp [ha])) _

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
theorem product_denote (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d)) :
    D (Product.run p t M cache table u J left right []) =
      Squarefree.canonical u J (D left * D right) := by
  have h := Product.run_denote p t M cache scalar basis table htable u J left right []
    (by simp [Squarefree.Sparse.keys])
  simpa only [rawDenote,Dictionary.denoteTable,List.map_nil,Squarefree.Sparse.denote,
    Squarefree.Sparse.decode,add_zero] using h

variable (vars : Finset (Fin n)) (u J : ℕ)
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))
variable (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
variable (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) one =
  Squarefree.canonical u J 1)

include htable hone hminus honeval in
 theorem literal_denote (payload : List (Product.Entry n (baseWidth p t) d)) (positive : Bool) :
    D (LiteralCallback.value p t M cache table minusOne one payload positive) =
      if positive then Squarefree.canonical u J 1 + -(D payload) else D payload := by
  cases positive
  · rfl
  · change D (Normalize.run p t M cache _ one) = _
    rw [normalize_denote p t M cache scalar basis _ one hone.nodup]
    have hn := Squarefree.ScaleProgram.denote_neg p t M cache scalar basis table htable
      minusOne hminus payload
    change D (Squarefree.ScaleProgram.scaled p t M cache table minusOne payload) = -D payload at hn
    rw [hn,honeval,add_comm]
    all_goals rfl

include htable hone hminus honeval in
theorem step_denote (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) :
    D (Clause.step p t M cache table minusOne one incidence u J l acc) =
      (squarefreeAlgebra u J).mul (D acc)
        (literalValue (squarefreeAlgebra u J) (fun v => D (incidence v)) l) := by
  unfold Clause.step LiteralCallback.result
  rw [product_denote p t M cache scalar basis table htable]
  rw [literal_denote p t M cache scalar basis table htable vars u J minusOne one hone hminus honeval]
  all_goals rfl

include htable hone hminus honeval in
theorem clause_fold_denote (ls : List (SAT.Literal (Fin n)))
    (acc : List (Product.Entry n (baseWidth p t) d)) :
    D (DynamicFold.value (Clause.step p t M cache table minusOne one incidence u J) ls acc) =
      clauseFoldValue (squarefreeAlgebra u J) (fun v => D (incidence v)) ls (D acc) := by
  induction ls generalizing acc with
  | nil => rfl
  | cons l ls ih =>
    simp only [DynamicFold.value]
    rw [ih,step_denote p t M cache scalar basis table htable vars u J
      minusOne one incidence hone hminus honeval]
    rfl

variable (jet : Fin n → Squarefree.Jet (Fin n) R)
variable (hjet : ∀ v,
  rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) (incidence v) =
    Squarefree.canonical u J (jet v))

include htable hone hminus honeval in
/-- Only the incidence rows referenced by this clause need the intended value. -/
theorem clause_denote_scoped_oai (w : Row.WeightedClause n (baseWidth p t) d)
    (hs : ∀ l ∈ w.literals, D (incidence l.variable) = Squarefree.canonical u J (jet l.variable)) :
    D (Row.clauseValue p t M cache table minusOne one incidence u J w) =
      clauseValue (squarefreeAlgebra u J) (fun v => Squarefree.canonical u J (jet v)) w.literals := by
  unfold Row.clauseValue
  rw [clause_fold_denote p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval]
  rw [clauseFold_congr (squarefreeAlgebra u J) (fun v => D (incidence v))
    (fun v => Squarefree.canonical u J (jet v)) w.literals hs]
  rw [honeval]
  exact clauseFoldValue_projected_one (Squarefree.canonical u J)
    (Squarefree.canonical_mul u J) jet w.literals

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Instantiation at the actual supplied-polynomial unramified ring. -/


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.clause_denote_scoped_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.clause_denote_scoped_oai.{u_1}
