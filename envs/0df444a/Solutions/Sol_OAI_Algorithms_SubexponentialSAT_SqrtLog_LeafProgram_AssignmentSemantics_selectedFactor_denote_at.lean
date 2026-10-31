-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:08:59.695924+00:00
-- url     : https://prove2.me/submissions/37cf98a5-e91d-4562-a841-8f6ec194f882

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Multiplier_prepared_denote
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_descendingStored_denote
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NativeSemantics_clause_denote_scoped
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NativeSemantics_row_denote_scoped

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

theorem digitPolynomial_eval (ops : RepresentedRing C A) (φ : A →+* R) {t : ℕ}
    (v : Fin (3*t) → C) (s : Fin t) (x : R) :
    (digitPolynomial ops v s).eval₂ φ x = digitValue ops φ v s x := by
  simp only [digitPolynomial, digitValue, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Algebraic invariant for the native descending Horner application. Each
coefficient digit has three entries, and no power is recomputed by expansion. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators

variable {C A R : Type*} [CommRing A] [CommRing R]

theorem descendingValue_reverse (decode : C → A) (φ : A →+* R) (h g : R)
    (vs : List (Triple C)) :
    descendingValue decode φ h g vs.reverse 0=hornerValue decode φ h g vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.reverse_cons,descendingValue,List.foldl_append,List.foldl_cons,
      List.foldl_nil,hornerValue]
    rw [←descendingValue,ih]

theorem hornerValue_ofFn (decode : C → A) (φ : A →+* R) (h g : R)
    (t : ℕ) (vs : Fin t → Triple C) :
    hornerValue decode φ h g (List.ofFn vs)=
      ∑ s : Fin t, tripleValue decode φ h (vs s)*g^s.val := by
  induction t with
  | zero => simp [hornerValue]
  | succ t ih =>
    rw [List.ofFn_succ,hornerValue,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring

theorem coefficientTriple_value (ops : SubexpSymbolicCost.RepresentedRing C A)
    (φ : A →+* R) (h : R) (t : ℕ) (code : RingProgram.Code C (3*t)) (s : Fin t) :
    tripleValue ops.decode φ h (coefficientTriple t code s)=
      (IdempotentProgram.digitPolynomial ops code s).eval₂ φ h := by
  rw [IdempotentProgram.digitPolynomial_eval]
  simp [tripleValue,coefficientTriple,IdempotentProgram.digitValue,
    IdempotentProgram.digitCode,Fin.sum_univ_succ]
  ; ring

/-- Horner application equals the exact H-adic indicator polynomial, with U
combined into the Horner multiplier rather than expanded into stored powers. -/
theorem apply_coefficients (ops : SubexpSymbolicCost.RepresentedRing C A)
    (φ : A →+* R) (h u : R) (t : ℕ) (code : RingProgram.Code C (3*t)) :
    descendingValue ops.decode φ h (u*IdempotentProgram.hValue h)
      (List.ofFn (coefficientTriple t code)).reverse 0 =
      ∑ s : Fin t,
        u^s.val * (IdempotentProgram.digitPolynomial ops code s).eval₂ φ h *
          IdempotentProgram.hValue h^s.val := by
  rw [descendingValue_reverse,hornerValue_ofFn]
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficientTriple_value,mul_pow]
  ring

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

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

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramProjection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Projection invariant for sparse Horner application. It permits the native
product to truncate after every multiplication while retaining exactly the
canonical projection of the complete indicator polynomial. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open LeafProgram

variable {C A R : Type*} [CommRing A] [CommRing R]

theorem tripleAlgebra_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y)=project (x*y))
    (decode : C → A) (φ : A →+* R) (h : R) (v : Triple C) :
    tripleAlgebra (projectedAlgebra project) (fun c => project (φ (decode c)))
      (project h) v=project (tripleValue decode φ h v) := by
  unfold tripleAlgebra projectedAlgebra
  dsimp only
  rw [hprod,←map_add project (φ (decode v.c)*h) (φ (decode v.b)),hprod,←map_add]
  congr 1
  unfold tripleValue
  ring

theorem descendingAlgebra_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y)=project (x*y))
    (decode : C → A) (φ : A →+* R) (h g : R) (vs : List (Triple C)) (acc : R) :
    descendingAlgebra (projectedAlgebra project) (fun c => project (φ (decode c)))
      (project h) (project g) vs (project acc)=
        project (descendingValue decode φ h g vs acc) := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
    simp only [descendingAlgebra,List.foldl_cons,descendingValue]
    rw [tripleAlgebra_projected project hprod]
    change descendingAlgebra (projectedAlgebra project) (fun c => project (φ (decode c)))
      (project h) (project g) vs
      (project (project acc*project g)+project (tripleValue decode φ h v)) = _
    rw [hprod,←map_add,ih]
    congr 2
    ring

theorem apply_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y)=project (x*y))
    (ops : SubexpSymbolicCost.RepresentedRing C A) (φ : A →+* R)
    (h u : R) (t : ℕ) (code : RingProgram.Code C (3*t)) :
    descendingAlgebra (projectedAlgebra project) (fun c => project (φ (ops.decode c)))
      (project h) (project (u*IdempotentProgram.hValue h))
      (List.ofFn (coefficientTriple t code)).reverse 0 =
      project (∑ s : Fin t,
        u^s.val * (IdempotentProgram.digitPolynomial ops code s).eval₂ φ h *
          IdempotentProgram.hValue h^s.val) := by
  have he:=descendingAlgebra_projected project hprod ops.decode φ h
    (u*IdempotentProgram.hValue h) (List.ofFn (coefficientTriple t code)).reverse 0
  simpa only [map_zero,apply_coefficients] using he

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

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

private theorem apply_projected_scalar (uCap J : ℕ)
    (H U : Squarefree.Jet (Fin n) R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    let project := Squarefree.canonical (V:=Fin n) (R:=R) uCap J
    let ops := RingProgram.scalarRing p t M cache
    let ψ := (Moments.ringScalar (V:=Fin n)).comp φ
    descendingAlgebra (LeafProgram.projectedAlgebra project)
        (fun c => project (ψ (ops.decode c))) (project H)
        (project (U * IdempotentProgram.hValue H))
        (List.ofFn (coefficientTriple t code)).reverse 0 =
      project (∑ s : Fin t,
        U^s.val * (IdempotentProgram.digitPolynomial ops code s).eval₂ ψ H *
          IdempotentProgram.hValue H^s.val) := by
  dsimp only
  exact apply_projected _ (Squarefree.canonical_mul uCap J) _ _ H U t code

theorem applyStored_denote
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J)
    (h g : Stored p t (n:=n) (d:=d)) (H U : Squarefree.Jet (Fin n) R)
    (hH : storedDenote p t M cache φ basis h=Squarefree.canonical (V:=Fin n) (R:=R) uCap J H)
    (hG : storedDenote p t M cache φ basis g=
      Squarefree.canonical (V:=Fin n) (R:=R) uCap J (U*IdempotentProgram.hValue H))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    storedDenote p t M cache φ basis
      (descendingStored p t M cache table uCap J h g
        (List.ofFn (coefficientTriple t code)).reverse []) =
      Squarefree.canonical (V:=Fin n) (R:=R) uCap J (∑ s : Fin t,
        U^s.val * (IdempotentProgram.digitPolynomial (RingProgram.scalarRing p t M cache)
          code s).eval₂ ((Moments.ringScalar (V:=Fin n)).comp φ) H *
        IdempotentProgram.hValue H^s.val) := by
  rw [descendingStored_denote p t M cache φ basis table htable hd hb uCap J hu hj,hH,hG]
  have hz : storedDenote p t M cache φ basis ([] : Stored p t (n:=n) (d:=d))=0 := rfl
  rw [hz]
  let project := Squarefree.canonical (V:=Fin n) (R:=R) uCap J
  let ops := RingProgram.scalarRing p t M cache
  let ψ := (Moments.ringScalar (V:=Fin n)).comp φ
  change descendingAlgebra (LeafProgram.projectedAlgebra project)
      (fun c => project (ψ (ops.decode c))) (project H)
      (project (U * IdempotentProgram.hValue H))
      (List.ofFn (coefficientTriple t code)).reverse 0 =
    project (∑ s : Fin t,
      U^s.val * (IdempotentProgram.digitPolynomial ops code s).eval₂ ψ H *
        IdempotentProgram.hValue H^s.val)
  exact apply_projected_scalar p t M cache φ uCap J H U code

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Native high-register services for the quadratic and Horner steps. -/


/-! Complete native evaluation of one degree-two coefficient digit. -/


/-! The native Horner accumulator update, including every move and cleanup. -/


/-! Measured descending Horner loop over the actual computed coefficient tape. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem loopResult_eq (ctx : Context p t n d) (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    loopResult ctx h g vs a=descendingStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h g vs a := by
  induction vs generalizing a with
  | nil => rfl
  | cons v vs ih => exact ih _

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full native application of a computed idempotent coefficient array.
The multiplier is built from H and ordinary cached constants; the indicator
is then computed by the measured Horner loop. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

variable {R : Type*} [CommRing R]

/-- Exact semantics of the bytes produced by the native application command. -/
theorem applied_coefficients_denote (ctx : Context p t n d)
    (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hj : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) φ basis minus = -1)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (honeKeys : (Squarefree.Sparse.keys one).Nodup)
    (hone : storedDenote p t ctx.modulus ctx.cache φ basis one=Squarefree.canonical ctx.u ctx.J 1)
    (H : Squarefree.Jet (Fin n) R)
    (hh : storedDenote p t ctx.modulus ctx.cache φ basis h=Squarefree.canonical ctx.u ctx.J H)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    storedDenote p t ctx.modulus ctx.cache φ basis
      (applied ctx minus h one (List.ofFn (coefficientTriple t code)))=
      Squarefree.canonical ctx.u ctx.J (∑ s : Fin t,
        (Squarefree.Sparse.atom (Multiplier.uKey n) 1)^s.val *
          (IdempotentProgram.digitPolynomial (RingProgram.scalarRing p t ctx.modulus ctx.cache)
            code s).eval₂ ((Moments.ringScalar (V:=Fin n)).comp φ) H *
          IdempotentProgram.hValue H^s.val) := by
  unfold applied
  rw [loopResult_eq]
  exact applyStored_denote p t ctx.modulus ctx.cache φ basis ctx.table htable hd hb ctx.u ctx.J hu hj
    h (Multiplier.prepared ctx minus h one) H (Squarefree.Sparse.atom (Multiplier.uKey n) 1) hh
    (Multiplier.prepared_denote ctx φ basis htable minus hminus h one honeKeys hone H hh) code


end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

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

include htable hone hminus honeval in
theorem clause_list_polynomial_scoped (ls : List (SAT.Literal (Fin n)))
    (hs : ∀ l ∈ ls, D (incidence l.variable) = Squarefree.canonical u J (jet l.variable)) :
    D (DynamicFold.value (Clause.step p t M cache table minusOne one incidence u J) ls one) =
      Squarefree.canonical u J (MvPolynomial.eval jet (clausePolynomial (R := Squarefree.Jet (Fin n) R) ls)) := by
  let w : Row.WeightedClause n (baseWidth p t) d := ⟨fun _ => cache.zero,ls⟩
  change D (Row.clauseValue p t M cache table minusOne one incidence u J w) = _
  rw [clause_denote_scoped p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval jet w hs]
  change clauseValue (projectedAlgebra (Squarefree.canonical u J))
    (fun v => Squarefree.canonical u J (jet v)) ls = _
  exact (clauseValue_projected (Squarefree.canonical u J) (Squarefree.canonical_mul u J)
    jet ls).trans (congrArg (Squarefree.canonical u J) (clauseValue_eq_eval jet ls))

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Instantiation at the actual supplied-polynomial unramified ring. -/


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsDenote
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-scoped semantics of each actual selected factor, followed by the
canonical product in the selected ID order. The marked clause is not lifted
through the hash idempotent. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators

variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

theorem indicator_denote (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ v, Good vars ctx.u ctx.J (incidence v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) one = Squarefree.canonical ctx.u ctx.J 1)
    (jet : Fin n → Squarefree.Jet (Fin n) R)
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (hjet : ∀ w ∈ ws, ∀ l ∈ w.literals,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence l.variable) = Squarefree.canonical ctx.u ctx.J (jet l.variable))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis)
      (Indicator.result ctx minus one incidence ws (List.ofFn (IdempotentApplyProgram.coefficientTriple t code))) =
      Squarefree.canonical ctx.u ctx.J (indicatorPolynomial ctx scalar code
        (MvPolynomial.eval jet (rowPolynomial (scalarJet (V:=Fin n))
          (sourceTerms (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
            scalar basis) ws)))) := by
  have hh := row_denote_scoped p t ctx.modulus ctx.cache scalar basis ctx.table htable
    vars ctx.u ctx.J minus one incidence hone hi hminus honeval jet ws hjet
  exact IdempotentApplyProgram.applied_coefficients_denote ctx scalar basis htable
    hd hb hu hJ minus hminus _ one hone.nodup honeval _ hh code

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsSelected
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Selected-ID scope sharpening. Unexecuted factors require no source-row
identity; existing all-ID interfaces remain unchanged. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators
variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

/-- Only literals actually read by an ID require the source incidence identity.
Other entries need validity, but need not have any particular denotation. -/
theorem selectedFactor_denote_at_oai (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) one = Squarefree.canonical ctx.u ctx.J 1)
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (id : ℕ)
    (hhash : ∀ (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J (jet id l.variable))
    (hmark : marked=true → id=hashes.length → ∀ l ∈ clause,
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        scalar basis) (incidence id l.variable) =
          Squarefree.canonical ctx.u ctx.J (jet id l.variable))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hfactor : selectedFactor ctx minus one incidence hashes marked clause
      (List.ofFn (IdempotentApplyProgram.coefficientTriple t code)) id = some factor) :
    rawDenote (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis) factor = Squarefree.canonical ctx.u ctx.J
        (selectedValue ctx scalar basis code jet hashes marked clause id) := by
  unfold selectedFactor at hfactor
  by_cases h : id < hashes.length
  · simp only [h, dite_true] at hfactor
    cases hfactor
    simpa only [selectedValue,h,dite_true] using
      indicator_denote ctx scalar basis htable hd hb hu hJ vars minus one (incidence id)
        hone (hi id) hminus honeval (jet id) hashes[id] (hhash h) code
  · simp only [h,dite_false] at hfactor
    by_cases hm : (marked && decide (id=hashes.length)) = true
    · simp only [hm,ite_true, if_true] at hfactor
      cases hfactor
      have hp : marked=true ∧ id=hashes.length := by simpa using hm
      have he : id=hashes.length := hp.2
      have hb' : marked=true := hp.1
      subst id
      simpa [selectedValue,h,hb'] using
        clause_list_polynomial_scoped p t ctx.modulus ctx.cache scalar basis ctx.table htable
          vars ctx.u ctx.J minus one (incidence hashes.length) hone hminus honeval
          (jet hashes.length) clause (hmark hb' rfl)
    · simp [hm] at hfactor

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at_oai.{u_1}
