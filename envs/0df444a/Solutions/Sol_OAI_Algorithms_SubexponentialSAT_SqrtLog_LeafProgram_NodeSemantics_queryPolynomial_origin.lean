-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:06:52.373134+00:00
-- url     : https://prove2.me/submissions/8d326195-8ace-4976-b0e8-d2075fbcb0b0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S076

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_NilpotentDefect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Divisibility of the marked defect

After the input coordinates have been substituted, the coefficient of U in
each incidence argument is divisible by p. Polynomial operations preserve
the stronger invariant that the coefficient of U^j is divisible by p^j.
This proves the high-U vanishing needed by canonical truncation.
-/

namespace SubexponentialSAT.NilpotentDefect

noncomputable section

open scoped BigOperators

section General

variable {A : Type*} [CommSemiring A]

theorem powerDivisible_mul {p : A} {P Q : Polynomial A}
    (hP : PowerDivisible p P) (hQ : PowerDivisible p Q) :
    PowerDivisible p (P * Q) := by
  classical
  intro j
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro ab hab
  have hj : ab.1 + ab.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [← hj, pow_add]
  exact mul_dvd_mul (hP ab.1) (hQ ab.2)

theorem powerDivisible_monomial (p a : A) (n : ℕ) (ha : p ^ n ∣ a) :
    PowerDivisible p (Polynomial.monomial n a) := by
  intro j
  by_cases h : n = j
  · subst j
    simpa using ha
  · simp [Polynomial.coeff_monomial, h]

theorem powerDivisible_C (p a : A) :
    PowerDivisible p (Polynomial.C a) := by
  simpa using powerDivisible_monomial p a 0 (by simp)

theorem powerDivisible_one (p : A) :
    PowerDivisible p (1 : Polynomial A) := by
  simpa using powerDivisible_C p 1

theorem powerDivisible_prod {α : Type*} (p : A) (s : Finset α)
    (f : α → Polynomial A) (hf : ∀ a ∈ s, PowerDivisible p (f a)) :
    PowerDivisible p (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using powerDivisible_one p
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact powerDivisible_mul (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- Nilpotence kills every complete high-degree coefficient, after evaluation. -/
theorem high_coeff_eq_zero {p : A} {P : Polynomial A} {μ : ℕ}
    (hP : PowerDivisible p P) (hnil : p ^ μ = 0) (j : ℕ) (hj : μ ≤ j) :
    P.coeff j = 0 := by
  apply eq_zero_of_zero_dvd
  simpa only [pow_eq_zero_of_le hj hnil] using hP j

end General

end

end SubexponentialSAT.NilpotentDefect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer representative lifting of the ternary selector coefficients.
Only reduction is a ring homomorphism. The lift itself is a finite choice of
0, 1, or 2, and no ring homomorphism from `ZMod 3` into the thickened ring is
assumed. All statements use the supplied irreducible polynomial. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

section Naturality
variable {V C R S : Type*} [CommRing R] [CommRing S]

theorem map_literalValue (rho : R →+* S) (value : V → R) (l : SAT.Literal V) :
    rho (literalValue (ringAlgebra R) value l) =
      literalValue (ringAlgebra S) (fun v => rho (value v)) l := by
  cases hp : l.positive <;> simp [literalValue, ringAlgebra, hp]

theorem map_clauseValue (rho : R →+* S) (value : V → R) (ls : List (SAT.Literal V)) :
    rho (clauseValue (ringAlgebra R) value ls) =
      clauseValue (ringAlgebra S) (fun v => rho (value v)) ls := by
  induction ls with
  | nil => simp [clauseValue, ringAlgebra]
  | cons l ls ih =>
      change rho (literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls) =
        literalValue (ringAlgebra S) (fun v => rho (value v)) l *
          clauseValue (ringAlgebra S) (fun v => rho (value v)) ls
      rw [map_mul, map_literalValue, ih]

theorem map_rowValue (rho : R →+* S) (decode : C → R) (value : V → R)
    (terms : SparseRow V C) :
    rho (rowValue (ringAlgebra R) decode value terms) =
      rowValue (ringAlgebra S) (fun c => rho (decode c)) (fun v => rho (value v)) terms := by
  induction terms with
  | nil => simp [rowValue, ringAlgebra]
  | cons term rest ih =>
      rcases term with ⟨c, ls⟩
      change rho (decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value rest) =
        rho (decode c) * clauseValue (ringAlgebra S) (fun v => rho (value v)) ls +
          rowValue (ringAlgebra S) (fun c => rho (decode c)) (fun v => rho (value v)) rest
      rw [map_add, map_mul, map_clauseValue, ih]

end Naturality

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared total-order truncation of nilpotent expansions

The outer variable is a formal marker U. `output` evaluates the canonical
representative after truncation at U = 1. This is an additive operation on
polynomials, not a homomorphism out of the quotient by U^t.
-/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section

open scoped BigOperators
open SubexponentialSAT.Truncation SubexponentialSAT.NilpotentDefect

variable {R S α : Type*} [CommSemiring R] [CommSemiring S]

theorem trunc_eq_sum (t : ℕ) (P : Polynomial R) :
    trunc t P = ∑ j ∈ Finset.range t, Polynomial.monomial j (P.coeff j) := by
  classical
  ext j
  simp [ Polynomial.coeff_monomial]

theorem eval_one_trunc (t : ℕ) (P : Polynomial R) :
    (trunc t P).eval 1 = ∑ j ∈ Finset.range t, P.coeff j := by
  rw [trunc_eq_sum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one]

theorem output_eq_sum_coeff (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) :
    output s t e h = ∑ j ∈ Finset.range t, (fullProduct s t e h).coeff j :=
  eval_one_trunc t _

theorem map_output (f : R →+* S) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) :
    f (output s t e h) =
      output s t (fun i j => f (e i j)) (fun i => f (h i)) := by
  simp only [output_eq_sum_coeff, map_sum]
  congr 1
  funext j
  simpa only [Polynomial.coeff_map] using
    congrArg (fun P : Polynomial S => P.coeff j) (map_fullProduct f s t e h)

/-- Each row has the divisibility invariant needed to kill discarded terms. -/
theorem powerDivisible_row (q : R) (t : ℕ) (e : ℕ → R) (h : R)
    (hh : q ∣ h) : PowerDivisible q (row t e h) := by
  intro j
  rw [coeff_row]
  split_ifs
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hh j) _
  · exact dvd_zero _

theorem powerDivisible_fullProduct (q : R) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) (hh : ∀ i ∈ s, q ∣ h i) :
    PowerDivisible q (fullProduct s t e h) := by
  apply powerDivisible_prod
  intro i hi
  exact powerDivisible_row q t (e i) (h i) (hh i hi)

/-- After substitution into a nilpotent setting, EVERY discarded coefficient
vanishes; therefore truncating the shared total order is exact. -/
theorem retainedProduct_eq_fullProduct (q : R) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) (hh : ∀ i ∈ s, q ∣ h i)
    (hq : q ^ t = 0) :
    retainedProduct s t e h = fullProduct s t e h := by
  ext j
  change (trunc t (fullProduct s t e h)).coeff j = _
  rw [coeff_trunc]
  split_ifs with hj
  · rfl
  · symm
    exact high_coeff_eq_zero (powerDivisible_fullProduct q s t e h hh) hq j
      (Nat.le_of_not_gt hj)

/-- The exact shared truncation equals the product of local exact values. -/
theorem output_eq_prod (q : R) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) (hh : ∀ i ∈ s, q ∣ h i)
    (hq : q ^ t = 0) :
    output s t e h = ∏ i ∈ s, (∑ j ∈ Finset.range t, e i j * h i ^ j) := by
  unfold output
  rw [retainedProduct_eq_fullProduct q s t e h hh hq]
  simp only [fullProduct, row, Polynomial.eval_prod, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]

/-- Apply after evaluating symbolic coefficients at an actual input. -/
theorem map_output_eq_prod (f : R →+* S) (q : S) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) (hh : ∀ i ∈ s, q ∣ f (h i))
    (hq : q ^ t = 0) :
    f (output s t e h) =
      ∏ i ∈ s, (∑ j ∈ Finset.range t, f (e i j) * f (h i) ^ j) := by
  rw [map_output]
  exact output_eq_prod q s t _ _ hh hq

end

end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact fixed-high query count for the code-derived shared-order target. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section
attribute [local instance] Classical.propDecidable

variable {R K : Type*} [CommRing R] [CommRing K] [DecidableEq K]
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem clauseValue_boolean (clause : List (SAT.Literal V)) (x : V → Bool) :
    clauseValue (ringAlgebra R) (fun v => HashInput.boolValue (x v)) clause =
      if violates clause x then 1 else 0 := by
  induction clause with
  | nil => simp [clauseValue,ringAlgebra,violates]
  | cons l ls ih =>
    change literalValue (ringAlgebra R) (fun v => HashInput.boolValue (x v)) l *
      clauseValue (ringAlgebra R) (fun v => HashInput.boolValue (x v)) ls = _
    rw [ih]
    simp only [violates,List.all_cons]
    cases hl : l.positive <;> cases hx : x l.variable <;>
      simp [literalValue,ringAlgebra,SAT.Literal.eval,HashInput.boolValue,hl,hx]

omit [Fintype V] [DecidableEq V] in
theorem hashPath_origin (hashes : List (SparseRow V R)) (path : ℕ → V → R[X])
    (x : V → Bool) (hpath : ∀ i v, (path i v).eval 0 = HashInput.boolValue (x v))
    (i : Fin hashes.length) :
    (hashPath hashes path i).eval 0 = sourceHash hashes x i := by
  unfold hashPath sourceHash
  have h := map_rowValue (Polynomial.evalRingHom (0:R)) Polynomial.C (path i.val) hashes[i]
  change (hashPath hashes path i).eval 0 =
    rowValue (ringAlgebra R) (fun c => c)
      (fun v => HashInput.boolValue (x v)) hashes[i]
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C, hpath] using h

omit [Fintype V] [DecidableEq V] in
theorem markedPath_origin (hashes : List (SparseRow V R)) (marked : Bool)
    (clause : List (SAT.Literal V)) (path : ℕ → V → R[X])
    (x : V → Bool) (hpath : ∀ i v, (path i v).eval 0 = HashInput.boolValue (x v)) :
    (markedPath hashes marked clause path).eval 0 =
      if marked then (if violates clause x then 1 else 0) else 1 := by
  cases hm : marked
  · simp [markedPath]
  · simp only [markedPath,ite_true, if_true]
    have h := map_clauseValue (Polynomial.evalRingHom (0:R)) (path hashes.length) clause
    simpa only [Polynomial.coe_evalRingHom,hpath,clauseValue_boolean] using h

omit [Fintype V] [DecidableEq V] in
/-- Local idempotent correctness is required only at the source value. The
  shared truncation is discharged here by nilpotent divisibility. -/
theorem queryPolynomial_origin_oai (rho : R →+* K) (q : R) (t : ℕ) (hq : q^t=0)
    (hker : ∀ y, rho y=0 → q∣y) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) (x : V → Bool)
    (hpath : ∀ i v, (path i v).eval 0 = HashInput.boolValue (x v))
    (hres : ∀ i, rho (sourceHash hashes x i)=0 ∨ rho (sourceHash hashes x i)=1 ∨
      rho (sourceHash hashes x i)=2)
    (hdigit : ∀ i, (∑ s : Fin t, (digits s).eval (sourceHash hashes x i) *
      IdempotentProgram.hValue (sourceHash hashes x i)^s.val) =
        if rho (sourceHash hashes x i)=0 then 1 else 0) :
    (queryPolynomial t digits hashes marked clause path).eval 0 =
      if accepted rho hashes marked clause x then 1 else 0 := by
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin hashes.length)),
      q ∣ (Polynomial.evalRingHom (0:R)) (IdempotentProgram.hValue (hashPath hashes path i)) := by
    intro i _
    apply hker
    simp only [IdempotentProgram.hValue,map_mul,map_sub,map_one,map_ofNat,
      Polynomial.coe_evalRingHom,hashPath_origin hashes path x hpath]
    rcases hres i with h|h|h <;> rw [h] <;> ring
  have ho := TotalOrder.map_output_eq_prod (Polynomial.evalRingHom (0:R)) q
    (Finset.univ : Finset (Fin hashes.length)) t
    (fun i => digitAt digits (hashPath hashes path i))
    (fun i => IdempotentProgram.hValue (hashPath hashes path i)) hh hq
  have he (i : Fin hashes.length) :
      (∑ j ∈ Finset.range t, (Polynomial.evalRingHom (0:R))
        (digitAt digits (hashPath hashes path i) j) *
        (Polynomial.evalRingHom (0:R)) (IdempotentProgram.hValue (hashPath hashes path i))^j) =
      if rho (sourceHash hashes x i)=0 then 1 else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [digitAt,dite_eq_left (Fin.isLt _),Polynomial.coe_evalRingHom,Polynomial.eval_comp,
      hashPath_origin hashes path x hpath,IdempotentProgram.hValue,Polynomial.eval_mul,
      Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_ofNat] using hdigit i
  simp_rw [he] at ho
  simp only [Polynomial.coe_evalRingHom] at ho
  have hp : (∏ i : Fin hashes.length, if rho (sourceHash hashes x i)=0 then (1:R) else 0) =
      if ∀ i, rho (sourceHash hashes x i)=0 then 1 else 0 := by
    split_ifs with h
    · exact Finset.prod_eq_one (fun i _ => ite_eq_left (h i))
    · push Not at h
      obtain ⟨i,hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  rw [queryPolynomial,Polynomial.eval_mul,ho,markedPath_origin hashes marked clause path x hpath,hp]
  unfold accepted
  by_cases ha : ∀ i, rho (sourceHash hashes x i)=0 <;>
    cases hm : marked <;> cases hv : violates clause x <;> simp [ha]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin_oai.{u_1, u_2, u_3} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin_oai.{u_1, u_2, u_3}
