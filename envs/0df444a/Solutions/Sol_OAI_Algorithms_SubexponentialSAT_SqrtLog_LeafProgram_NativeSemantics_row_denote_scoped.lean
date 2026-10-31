-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_denote_scoped
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:14:34.117842+00:00
-- url     : https://prove2.me/submissions/e8ed21ec-618b-42b4-a4bc-56ece2878d88

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NativeSemantics_row_fold_denote_scoped

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {V C A : Type*}

section PolynomialSemantics

variable {R : Type*} [CommRing R]

theorem clauseValue_eq_eval (value : V → R) (ls : List (SAT.Literal V)) :
    clauseValue (ringAlgebra R) value ls = MvPolynomial.eval value (clausePolynomial ls) := by
  induction ls with
  | nil => simp [clauseValue, clausePolynomial, ringAlgebra]
  | cons l ls ih =>
      change literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls = _
      simp only [clausePolynomial, List.map_cons, List.prod_cons, map_mul]
      rw [ih]
      congr 1
      cases hp : l.positive <;>
        simp [literalValue, ringAlgebra, HashInput.falsifyingLiteral, hp, sub_eq_add_neg]

theorem rowValue_eq_eval (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (ringAlgebra R) decode value terms =
      MvPolynomial.eval value (rowPolynomial decode terms) := by
  induction terms with
  | nil => simp [rowValue, rowPolynomial, ringAlgebra]
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      change decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value terms = _
      rw [clauseValue_eq_eval, ih]
      simp [rowPolynomial]

end PolynomialSemantics
end SubexponentialSAT.SqrtLog.LeafProgram

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

theorem rowValue_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (projectedAlgebra project) (fun c => project (decode c))
      (fun v => project (value v)) terms =
      project (rowValue (ringAlgebra R) decode value terms) := by
  induction terms with
  | nil => exact (map_zero project).symm
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      change project (project (decode c) *
          clauseValue (projectedAlgebra project) (fun v => project (value v)) ls) +
        rowValue (projectedAlgebra project) (fun c => project (decode c))
          (fun v => project (value v)) terms = _
      rw [clauseValue_projected project hprod, ih, hprod, ← map_add]
      rfl

theorem rowValue_projected_eq_eval (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (projectedAlgebra project) (fun c => project (decode c))
      (fun v => project (value v)) terms =
      project (MvPolynomial.eval value (rowPolynomial decode terms)) := by
  rw [rowValue_projected project hprod, rowValue_eq_eval]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSquarefree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The sparse-hash circuit projection theorem instantiated at the actual
Boolean-support U/Z jet algebra. This ties local circuit evaluation to the
same source polynomial used by the global interpolation proof. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [DecidableEq V] [CommRing R]

theorem squarefree_rowValue (t J : ℕ)
    (decode : C → Squarefree.Jet V R) (value : V → Squarefree.Jet V R)
    (terms : SparseRow V C) :
    rowValue (squarefreeAlgebra t J)
      (fun c => Squarefree.canonical t J (decode c))
      (fun v => Squarefree.canonical t J (value v)) terms =
      Squarefree.canonical t J
        (MvPolynomial.eval value (rowPolynomial decode terms)) := by
  simpa only [squarefreeAlgebra] using
    (rowValue_projected_eq_eval (R := Squarefree.Jet V R) (Squarefree.canonical t J)
      (Squarefree.canonical_mul t J) decode value terms)

end SubexponentialSAT.SqrtLog.LeafProgram

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

theorem rowFoldValue_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (decode : C → R) (value : V → R) (terms : SparseRow V C) (init : R) :
    rowFoldValue (projectedAlgebra project) (fun c => project (decode c))
      (fun v => project (value v)) terms (project init) =
      project (init + rowValue (ringAlgebra R) decode value terms) := by
  induction terms generalizing init with
  | nil => simp [rowFoldValue, rowValue, ringAlgebra]
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      change rowFoldValue (projectedAlgebra project) (fun c => project (decode c))
        (fun v => project (value v)) terms
        (project init + project (project (decode c) *
          clauseValue (projectedAlgebra project) (fun v => project (value v)) ls)) = _
      rw [clauseValue_projected project hprod, hprod, ← map_add, ih]
      change project ((init + decode c * clauseValue (ringAlgebra R) value ls) +
        rowValue (ringAlgebra R) decode value terms) =
          project (init + (decode c * clauseValue (ringAlgebra R) value ls +
            rowValue (ringAlgebra R) decode value terms))
      rw [add_assoc]

theorem rowFoldValue_projected_zero (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y) = project (x * y))
    (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowFoldValue (projectedAlgebra project) (fun c => project (decode c))
      (fun v => project (value v)) terms 0 =
      rowValue (projectedAlgebra project) (fun c => project (decode c))
        (fun v => project (value v)) terms := by
  have h := rowFoldValue_projected project hprod decode value terms 0
  simpa only [map_zero, zero_add, rowValue_projected project hprod] using h

end SubexponentialSAT.SqrtLog.LeafProgram

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

/-- The native left fold with flat scalar weights denotes the same source
polynomial as the generic weighted sparse-row evaluator. -/
theorem scalar_rowFold_source (t J : ℕ) (value : V → Jet V R)
    (terms : SparseRow V R) :
    rowFoldValue (squarefreeAlgebra t J)
      (fun c => Squarefree.canonical t J (scalarJet c))
      (fun v => Squarefree.canonical t J (value v)) terms 0 =
        Squarefree.canonical t J (MvPolynomial.eval value (rowPolynomial (R := Jet V R) (scalarJet (V := V)) terms)) := by
  have h := rowFoldValue_projected_zero (Squarefree.canonical t J)
    (Squarefree.canonical_mul t J) (scalarJet (V := V)) value terms
  exact h.trans (squarefree_rowValue t J (scalarJet (V := V)) value terms)

end SubexponentialSAT.SqrtLog.LeafProgram

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

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

end Good

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
/-- Missing variables may have zero rows: only literals actually read by this
factor require the intended incidence semantics. -/
theorem row_denote_scoped_oai (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (hs : ∀ w ∈ ws, ∀ l ∈ w.literals,
      D (incidence l.variable) = Squarefree.canonical u J (jet l.variable)) :
    D (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws []) =
      Squarefree.canonical u J
        (MvPolynomial.eval jet (rowPolynomial (scalarJet (V := Fin n)) (sourceTerms f ws))) := by
  rw [row_fold_denote_scoped p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hi hminus honeval jet ws hs [] Good.nil]
  exact scalar_rowFold_source u J jet (sourceTerms f ws)

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Instantiation at the actual supplied-polynomial unramified ring. -/


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_denote_scoped_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_denote_scoped_oai.{u_1}
