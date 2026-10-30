-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:48:18.620501+00:00
-- url     : https://prove2.me/submissions/1bcf144d-7bc2-496c-9a7e-00cd0b3ee1bc

import Mathlib
import Definitions.Def_OAIQ081S121

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The integral Newton operation for lifting an idempotent through a
nilpotent ideal. No division, characteristic hypothesis, or field structure
is used in the iteration. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem newton_error (e : R) :
    (newton e) ^ 2 - newton e =
      -(e ^ 2 - e) ^ 2 * (3 - 2 * e) * (1 + 2 * e) := by
  unfold newton
  ring

theorem newton_sub (e : R) :
    newton e - e = (1 - 2 * e) * (e ^ 2 - e) := by
  unfold newton
  ring

theorem newton_fixed {e : R} (he : e ^ 2 = e) : newton e = e := by
  apply sub_eq_zero.mp
  rw [newton_sub, he, sub_self, mul_zero]

theorem iterate_fixed {e : R} (he : e ^ 2 = e) (n : ℕ) : iterate e n = e := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [iterate, ih] using newton_fixed he

theorem map_newton (φ : R →+* S) (e : R) : φ (newton e) = newton (φ e) := by
  have h2 : φ (2 : R) = (2 : S) := by
    rw [show (2 : R) = 1 + 1 by ring, map_add, map_one]
    ring
  have h3 : φ (3 : R) = (3 : S) := by
    rw [show (3 : R) = 1 + 1 + 1 by ring, map_add, map_add, map_one]
    ring
  simp only [newton, map_sub, map_mul, map_pow, h2, h3]

theorem map_iterate (φ : R →+* S) (e : R) (n : ℕ) :
    φ (iterate e n) = iterate (φ e) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterate, map_newton, ih]

theorem iterate_residue (φ : R →+* S) {e : R}
    (he : (φ e) ^ 2 = φ e) (n : ℕ) : φ (iterate e n) = φ e := by
  rw [map_iterate, iterate_fixed he]

theorem error_dvd_power {q e : R} (h : q ∣ e ^ 2 - e) (n : ℕ) :
    q ^ (2 ^ n) ∣ (iterate e n) ^ 2 - iterate e n := by
  induction n with
  | zero => simpa [iterate] using h
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨-(c ^ 2) * (3 - 2 * iterate e n) * (1 + 2 * iterate e n), ?_⟩
      rw [iterate, newton_error, hc, Nat.pow_succ, pow_mul]
      ring

theorem iterate_idempotent {q e : R} {t n : ℕ}
    (h : q ∣ e ^ 2 - e) (hq : q ^ t = 0) (ht : t ≤ 2 ^ n) :
    (iterate e n) ^ 2 = iterate e n := by
  obtain ⟨c, hc⟩ := error_dvd_power h n
  have hpow : q ^ (2 ^ n) = 0 := by
    have hexp : 2 ^ n = t + (2 ^ n - t) := by omega
    rw [hexp, pow_add, hq, zero_mul]
  apply sub_eq_zero.mp
  rw [hc, hpow, zero_mul]

theorem idempotent_zero_of_dvd {q e : R} {t : ℕ}
    (he : e ^ 2 = e) (hq : q ^ t = 0) (hd : q ∣ e) : e = 0 := by
  obtain ⟨c, rfl⟩ := hd
  apply IsIdempotentElem.eq_zero_of_isNilpotent
  · simpa [IsIdempotentElem, pow_two] using he
  · exact ⟨t, by rw [mul_pow, hq, zero_mul]⟩

theorem idempotent_one_of_dvd {q e : R} {t : ℕ}
    (he : e ^ 2 = e) (hq : q ^ t = 0) (hd : q ∣ 1 - e) : e = 1 := by
  have hcomp : (1 - e) ^ 2 = 1 - e := by
    linear_combination he
  have hz := idempotent_zero_of_dvd hcomp hq hd
  exact (sub_eq_zero.mp hz).symm

theorem idempotent_zero_of_residue (φ : R →+* S) {q e : R} {t : ℕ}
    (hker : ∀ x, φ x = 0 → q ∣ x)
    (he : e ^ 2 = e) (hq : q ^ t = 0) (hres : φ e = 0) : e = 0 :=
  idempotent_zero_of_dvd he hq (hker e hres)

theorem idempotent_one_of_residue (φ : R →+* S) {q e : R} {t : ℕ}
    (hker : ∀ x, φ x = 0 → q ∣ x)
    (he : e ^ 2 = e) (hq : q ^ t = 0) (hres : φ e = 1) : e = 1 := by
  apply idempotent_one_of_dvd he hq
  apply hker
  simp [hres]

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTernary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The three-residue idempotent coefficient family.  The only coefficient
assumption is a supplied inverse `u` of two. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial

variable {A O K : Type*} [CommRing A] [CommRing O] [CommRing K]

theorem map_two (φ : A →+* O) : φ (2 : A) = (2 : O) := by
  rw [show (2 : A) = 1 + 1 by ring, map_add, map_one]
  ring

theorem map_initialValue (φ : A →+* O) (u x : A) :
    φ (initialValue u x) = initialValue (φ u) (φ x) := by
  simp only [initialValue, map_mul, map_sub, map_one, map_two]

theorem eval_ternaryH (φ : A →+* O) (x : O) :
    (ternaryH : A[X]).eval₂ φ x = x * (x - 1) * (x - 2) := by
  simp only [ternaryH, eval₂_mul, eval₂_sub, eval₂_X,
    eval₂_one, eval₂_ofNat, map_one, map_two]

theorem initialValue_error (u x : A) (hu : 2 * u = 1) :
    (initialValue u x) ^ 2 - initialValue u x =
      (x * (x - 1) * (x - 2)) * (u ^ 2 * (x - 3)) := by
  unfold initialValue
  linear_combination u * (x - 1) * (x - 2) * hu

theorem initialValue_zero (u : A) (hu : 2 * u = 1) : initialValue u 0 = 1 := by
  unfold initialValue
  linear_combination hu

theorem mapped_inverse_two (φ : A →+* O) {u : A} (hu : 2 * u = 1) :
    2 * φ u = 1 := by
  simpa only [map_mul, map_two, map_one] using congrArg φ hu

theorem eval_H_nilpotent (φ : A →+* O) (ρ : O →+* K) (q : O) (t : ℕ)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (hq : q ^ t = 0)
    (x : O) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    ((ternaryH : A[X]).eval₂ φ x) ^ t = 0 := by
  have hres : ρ ((ternaryH : A[X]).eval₂ φ x) = 0 := by
    rw [eval_ternaryH]
    simp only [map_mul, map_sub, map_one, map_two]
    rcases hx with h | h | h <;> rw [h] <;> ring
  obtain ⟨c, hc⟩ := hker _ hres
  rw [hc, mul_pow, hq, zero_mul]

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable Newton control over a supplied represented coefficient ring.
The measured counters below charge every callback and seven control events.
They are an intermediate interface, not a primitive bit-runtime certificate;
the supplied callbacks must be refined by actual serialized-array services. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*} [CommRing R]

theorem liftRun_correct (ops : RepresentedRing C R) (e : C) (t : ℕ) :
    ops.decode (liftRun ops.program e t).1 =
      Idempotent.iterate (ops.decode e) (Nat.clog 2 t) :=
  iterateRun_correct ops e (Nat.clog 2 t)

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

/-- General coefficient version of the atom evaluation lemma. -/
theorem atom_eval (t s a : ℕ) (c x : R) (ha : a < 3) (ht : hValue x ^ t = 0) :
    (∑ k : Fin (3*t), (if k.val = 3*s+a then c else 0) * hadicBasis t x k) =
      c * (x^a * hValue x^s) := by
  have h := atomInteger_eval t s a 1 x ha ht
  simp only [Int.cast_one, one_mul] at h
  calc
    _ = c * (∑ k : Fin (3*t), (atomInteger (3*s+a) 1 k : R) * hadicBasis t x k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.val = 3*s+a <;> simp [atomInteger, hk]
    _ = _ := by rw [h]

theorem initialRun_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) (u : C) :
    evaluate ops φ t x (initialRun ops.program t u).1 =
      Idempotent.initialValue (φ (ops.decode u)) x := by
  let c := φ (ops.decode u)
  have heval : evaluate ops φ t x (initialRun ops.program t u).1 =
      (∑ k : Fin (3*t), (if k.val = 0 then 2*c else 0) * hadicBasis t x k) +
      (∑ k : Fin (3*t), (if k.val = 1 then -(3*c) else 0) * hadicBasis t x k) +
      (∑ k : Fin (3*t), (if k.val = 2 then c else 0) * hadicBasis t x k) := by
    simp only [evaluate, RingProgram.denote, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [initialRun]
    by_cases h0 : k.val = 0
    · simp [h0, ops.add_correct, map_add, c]
      ring
    · by_cases h1 : k.val = 1
      · simp [ h1, ops.add_correct,
          ops.neg_correct, map_add, map_neg, c]
        ring
      · by_cases h2 : k.val = 2
        · simp [ h2, c]
        · simp [h0, h1, h2, ops.zero_correct]
  rw [heval]
  have h0 := atom_eval t 0 0 (2*c) x (by omega) ht
  have h1 := atom_eval t 0 1 (-(3*c)) x (by omega) ht
  have h2 := atom_eval t 0 2 c x (by omega) ht
  simp only [Nat.mul_zero, Nat.zero_add, pow_zero, mul_one ] at h0 h1 h2
  rw [h0, h1, h2]
  dsimp [Idempotent.initialValue, c]
  ring

theorem coefficientRun_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) (u : C) :
    evaluate ops φ t x (coefficientRun ops.program t u).1 =
      Idempotent.iterate (Idempotent.initialValue (φ (ops.decode u)) x) (Nat.clog 2 t) := by
  have h := liftRun_correct (arrayRepresented ops φ t x ht) (initialRun ops.program t u).1 t
  simp only [arrayRepresented_program, arrayRepresented_decode] at h
  change evaluate ops φ t x
    (liftRun (arrayProgram ops.program t) (initialRun ops.program t u).1 t).1 = _
  simpa only [initialRun_correct ops φ t x ht] using h

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

theorem evaluate_digits (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (v : Fin (3*t) → C) :
    evaluate ops φ t x v = ∑ s : Fin t, digitValue ops φ v s x * hValue x^s.val := by
  rw [evaluate, RingProgram.denote, ← (digitEquiv t).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  simp only [digitValue, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  have hmod : (digitIndex s a).val % 3 = a.val := by
    dsimp [digitIndex]; have := a.isLt; omega
  have hdiv : (digitIndex s a).val / 3 = s.val := by
    dsimp [digitIndex]; have := a.isLt; omega
  simp only [digitEquiv_apply, hadicBasis, hmod, hdiv, digitCode]
  ring

/-- The finite algorithm produces exactly the desired zero-residue indicator. -/
theorem coefficientRun_indicator [DecidableEq K]
    (ops : RepresentedRing C A) (φ : A →+* R) (ρ : R →+* K)
    (t : ℕ) (u : C) (hu : 2*ops.decode u = 1)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    evaluate ops φ t x (coefficientRun ops.program t u).1 =
      if ρ x = 0 then 1 else 0 := by
  have hH : hValue x^t = 0 := by
    simpa only [Idempotent.eval_ternaryH, hValue] using
      Idempotent.eval_H_nilpotent φ ρ q t hker hq x hx
  rw [coefficientRun_correct ops φ t x hH]
  have huR : 2*φ (ops.decode u) = 1 := Idempotent.mapped_inverse_two φ hu
  have huK : 2*ρ (φ (ops.decode u)) = 1 := Idempotent.mapped_inverse_two ρ huR
  have herr : hValue x ∣
      (Idempotent.initialValue (φ (ops.decode u)) x)^2 -
        Idempotent.initialValue (φ (ops.decode u)) x := by
    rw [Idempotent.initialValue_error _ _ huR]
    exact dvd_mul_right _ _
  have he := Idempotent.iterate_idempotent herr hH (Nat.le_pow_clog (by decide) t)
  by_cases hz : ρ x = 0
  · simp only [hz, ↓reduceIte]
    have hi : ρ (Idempotent.initialValue (φ (ops.decode u)) x) = 1 := by
      rw [Idempotent.map_initialValue, hz]
      exact Idempotent.initialValue_zero _ huK
    apply Idempotent.idempotent_one_of_residue ρ hker he hq
    rw [Idempotent.iterate_residue ρ (by rw [hi]; ring), hi]
  · simp only [hz, ↓reduceIte]
    have hi : ρ (Idempotent.initialValue (φ (ops.decode u)) x) = 0 := by
      rw [Idempotent.map_initialValue]
      rcases hx.resolve_left hz with h | h <;> rw [h] <;> simp
    apply Idempotent.idempotent_zero_of_residue ρ hker he hq
    rw [Idempotent.iterate_residue ρ (by rw [hi]; ring), hi]

end SubexponentialSAT.SqrtLog.IdempotentProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramBinary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Negation through multiplication by a cached negative unit. This permits
the native implementation to use only addition and multiplication services. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

/-- The seven-register instruction sequence remains valid when its negation
instruction dispatches to the multiplication service with the cached unit. -/
theorem binaryArrayLift_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) (u : C) :
    evaluate ops φ t x
      (liftRun (binaryArrayProgram ops.program t) (initialRun ops.program t u).1 t).1 =
    Idempotent.iterate (Idempotent.initialValue (φ (ops.decode u)) x) (Nat.clog 2 t) := by
  have h := liftRun_correct (binaryArrayRepresented ops φ t x ht)
    (initialRun ops.program t u).1 t
  rw [← initialRun_correct ops φ t x ht u]
  change (binaryArrayRepresented ops φ t x ht).decode
      (liftRun (binaryArrayProgram ops.program t) (initialRun ops.program t u).1 t).1 =
    Idempotent.iterate
      ((binaryArrayRepresented ops φ t x ht).decode (initialRun ops.program t u).1)
      (Nat.clog 2 t) at h
  change (arrayRepresented ops φ t x ht).decode
      (liftRun (binaryArrayProgram ops.program t) (initialRun ops.program t u).1 t).1 =
    Idempotent.iterate
      ((arrayRepresented ops φ t x ht).decode (initialRun ops.program t u).1)
      (Nat.clog 2 t) at h
  rw [arrayRepresented_decode, arrayRepresented_decode] at h
  exact h

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

theorem binaryArrayLift_indicator [DecidableEq K]
    (ops : RepresentedRing C A) (φ : A →+* R) (ρ : R →+* K)
    (t : ℕ) (u : C) (hu : 2*ops.decode u = 1)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    evaluate ops φ t x
      (liftRun (binaryArrayProgram ops.program t) (initialRun ops.program t u).1 t).1 =
      if ρ x = 0 then 1 else 0 := by
  have hH : hValue x^t = 0 := by
    simpa only [Idempotent.eval_ternaryH, hValue] using
      Idempotent.eval_H_nilpotent φ ρ q t hker hq x hx
  rw [binaryArrayLift_correct ops φ t x hH, ← coefficientRun_correct ops φ t x hH]
  exact coefficientRun_indicator ops φ ρ t u hu q hq hker x hx

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete native Newton lift and the exact degree-three coefficient output.
The input-state contract includes prepared scalar constants and the cached
H-adic table; native preparation is a separate remaining construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {R K : Type*} [CommRing R] [CommRing K]

attribute [local instance] OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.ternaryPrimeFinal
/-- The words computed by the native lift have exactly the required indicator
semantics. Degree below three is structural via `digitPolynomial_degree`. -/
theorem binaryLiftWords_indicator_oai [DecidableEq K]
    (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (hu : 2*wordValue 3 t u = 1)
    (φ : ZMod (3^t) →+* R) (ρ : R →+* K)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    (∑ s : Fin t,
      (digitPolynomial (RingProgram.scalarRing 3 t M cache)
        (binaryLiftWords t M cache u) s).eval₂ φ x * hValue x^s.val) =
      if ρ x = 0 then 1 else 0 := by
  simp only [digitPolynomial_eval]
  rw [← evaluate_digits]
  exact binaryArrayLift_indicator (RingProgram.scalarRing 3 t M cache) φ ρ t u hu q hq hker x hx

end SubexponentialSAT.SqrtLog.IdempotentProgram


end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator_oai.{u_1, u_2}
