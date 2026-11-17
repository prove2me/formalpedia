-- Prove2me | solution 1 for MazurProof.TateOrder25Factor.order25_to_explicit_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:06.806712+00:00
-- url     : https://prove2.me/submissions/7eb0f260-eee6-497f-a309-6e6f1a6dba06

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor
import Definitions.Def_TateOriginDivision
import Definitions.Def_TorsionDefs
import Theorems.Thm_MazurProof_TateOriginDivision_prePsi_eval_ne_zero_of_lt_addOrder
import Theorems.Thm_MazurProof_TateOriginDivision_exists_tate_parameters_of_has_rational_point_of_odd_order

/-! Proofs of the lemmas stated in `Theorems.Thm_TateNormalForm_OrderTwentyFiveFactorization` and their helpers. -/

open Polynomial

open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder25Factor

open TateOriginDivision

open Scratch.TateZ2xZ10Reduction

noncomputable section

set_option linter.style.longLine false

/-- Exact order 25 produces the raw Tate-division obstruction. -/
theorem order25_to_raw_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h25 : HasRationalPointOfOrder E 25) :
    RawOrder25TateObstruction := by
  obtain ⟨b, c, hEll, hord, hb, h25eval⟩ :=
    exists_tate_parameters_of_has_rational_point_of_odd_order
      E (n := 25) (by norm_num) (by decide) h25
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have h5eval : ((W b c).preΨ' 5).eval 0 ≠ 0 :=
    prePsi_eval_ne_zero_of_lt_addOrder b c
      (n := 25) (m := 5) (by norm_num) (by norm_num) (by norm_num)
      (by decide) hord
  exact ⟨b, c, inferInstance, hb, h25eval, h5eval⟩

/-! ## Recurrence unrollings at the origin

The origin evaluations of the auxiliary polynomials `preΨ'ₖ` follow Mathlib's
elliptic-divisibility recurrence, read off exactly as in the order-`11`,
order-`18` and order-`27` developments.  Each step extracts a power of `b`,
keeping the compact factor symbolic. -/

private lemma eval_prePsi_five (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 =
      ((W b c).preΨ₄).eval 0 * ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 0)
  simpa using h

private lemma eval_prePsi_six (b c : ℚ) :
    ((W b c).preΨ' 6).eval 0 =
      ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 -
        ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 0)
  simpa using h

private lemma eval_prePsi_seven (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 =
      ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 3).eval 0) ^ 3 -
        ((W b c).preΨ' 4).eval 0 ^ 3 * ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 1)
  simpa using h

private lemma eval_prePsi_eight (b c : ℚ) :
    ((W b c).preΨ' 8).eval 0 =
      (((W b c).preΨ' 3).eval 0) ^ 2 * ((W b c).preΨ' 4).eval 0 *
          ((W b c).preΨ' 6).eval 0 -
        ((W b c).preΨ' 4).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 1)
  simpa using h

private lemma eval_prePsi_nine (b c : ℚ) :
    ((W b c).preΨ' 9).eval 0 =
      ((W b c).preΨ' 6).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 2)
  simpa [show Even (2 : ℕ) by decide] using h

private lemma eval_prePsi_eleven (b c : ℚ) :
    ((W b c).preΨ' 11).eval 0 =
      ((W b c).preΨ' 7).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 3 -
        ((W b c).preΨ' 4).eval 0 * (((W b c).preΨ' 6).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 3)
  simpa [show ¬ Even (3 : ℕ) by decide] using h

private lemma eval_prePsi_twelve (b c : ℚ) :
    ((W b c).preΨ' 12).eval 0 =
      (((W b c).preΨ' 5).eval 0) ^ 2 * ((W b c).preΨ' 6).eval 0 *
          ((W b c).preΨ' 8).eval 0 -
        ((W b c).preΨ' 4).eval 0 * ((W b c).preΨ' 6).eval 0 *
          (((W b c).preΨ' 7).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 3)
  simpa using h

private lemma eval_prePsi_thirteen (b c : ℚ) :
    ((W b c).preΨ' 13).eval 0 =
      ((W b c).preΨ' 8).eval 0 * (((W b c).preΨ' 6).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 7).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 4)
  simpa [show Even (4 : ℕ) by decide] using h

private lemma eval_prePsi_fourteen (b c : ℚ) :
    ((W b c).preΨ' 14).eval 0 =
      (((W b c).preΨ' 6).eval 0) ^ 2 * ((W b c).preΨ' 7).eval 0 *
          ((W b c).preΨ' 9).eval 0 -
        ((W b c).preΨ' 5).eval 0 * ((W b c).preΨ' 7).eval 0 *
          (((W b c).preΨ' 8).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 4)
  simpa using h

private lemma eval_prePsi_twentyfive (b c : ℚ) :
    ((W b c).preΨ' 25).eval 0 =
      ((W b c).preΨ' 14).eval 0 * (((W b c).preΨ' 12).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 11).eval 0 * (((W b c).preΨ' 13).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 10)
  simpa [show Even (10 : ℕ) by decide] using h

/-! ## Base origin evaluations (fully expanded, low degree) -/

private lemma Psi2Sq_eval (b c : ℚ) : ((W b c).Ψ₂Sq).eval 0 = b ^ 2 := by
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

private lemma prePsi_4_eval (b c : ℚ) :
    ((W b c).preΨ' 4).eval 0 = -(b ^ 4 * c) := by
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_four, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-! ## Reduced origin evaluations through the Kubert factors `F₅,…,F₉` -/

private lemma prePsi_5_eval (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 = b ^ 8 * TateNFDivision.F5 b c := by
  rw [eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F5]
  ring

private lemma prePsi_6_eval (b c : ℚ) :
    ((W b c).preΨ' 6).eval 0 = -(b ^ 11 * TateNFDivision.F6 b c) := by
  rw [eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F6]
  ring

private lemma prePsi_7_eval (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 = b ^ 16 * TateNFDivision.F7 b c := by
  rw [eval_prePsi_seven, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F7]
  ring

private lemma prePsi_8_eval (b c : ℚ) :
    ((W b c).preΨ' 8).eval 0 = b ^ 20 * c * TateNFDivision.F8 b c := by
  rw [eval_prePsi_eight, eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F8]
  ring

private lemma prePsi_9_eval (b c : ℚ) :
    ((W b c).preΨ' 9).eval 0 = b ^ 27 * TateNFDivision.F9 b c := by
  rw [eval_prePsi_nine, eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F9]
  ring

private lemma prePsi_11_eval (b c : ℚ) :
    ((W b c).preΨ' 11).eval 0 = b ^ 40 * G11 b c := by
  rw [eval_prePsi_eleven, prePsi_7_eval, prePsi_5_eval, prePsi_4_eval,
    prePsi_6_eval, Psi2Sq_eval]
  simp only [G11]
  ring

private lemma prePsi_12_eval (b c : ℚ) :
    ((W b c).preΨ' 12).eval 0 = -(b ^ 47 * G12 b c) := by
  rw [eval_prePsi_twelve, prePsi_5_eval, prePsi_6_eval, prePsi_8_eval,
    prePsi_4_eval, prePsi_7_eval]
  simp only [G12]
  ring

private lemma prePsi_13_eval (b c : ℚ) :
    ((W b c).preΨ' 13).eval 0 = -(b ^ 56 * G13 b c) := by
  rw [eval_prePsi_thirteen, prePsi_8_eval, prePsi_6_eval, prePsi_5_eval,
    prePsi_7_eval, Psi2Sq_eval]
  simp only [G13]
  ring

private lemma prePsi_14_eval (b c : ℚ) :
    ((W b c).preΨ' 14).eval 0 = b ^ 64 * G14 b c := by
  rw [eval_prePsi_fourteen, prePsi_6_eval, prePsi_7_eval, prePsi_9_eval,
    prePsi_5_eval, prePsi_8_eval]
  simp only [G14]
  ring

/-! ## The compact and primitive order-25 identities -/

/-- **Compact order-25 division identity at the Tate origin.**  The `25 = 2·12+1`
recurrence step, with every power of `b` extracted and the Kubert factors kept
atomic:
`preΨ'₂₅(0,0) = b²⁰⁸ · (G₁₁·G₁₃³ − b·G₁₄·G₁₂³)`. -/
theorem prePsi_twentyfive_eval_compact (b c : ℚ) :
    ((W b c).preΨ' 25).eval 0 =
      b ^ 208 * (G11 b c * G13 b c ^ 3 - b * G14 b c * G12 b c ^ 3) := by
  rw [eval_prePsi_twentyfive, prePsi_14_eval, prePsi_12_eval,
    prePsi_11_eval, prePsi_13_eval, Psi2Sq_eval]
  ring

/-- **Separation of the order-`5` factor.**  `F₅ = b - c` divides the compact
order-25 bracket, and the quotient is the primitive polynomial `F₂₅`:
`G₁₁·G₁₃³ − b·G₁₄·G₁₂³ = F₅ · F₂₅`. -/
theorem compact_bracket_factor (b c : ℚ) :
    G11 b c * G13 b c ^ 3 - b * G14 b c * G12 b c ^ 3 =
      TateNFDivision.F5 b c * F25 b c := by
  simp only [G11, G12, G13, G14, F25, F25DegreeTwentyFive, F25DegreeTwentySix, F25DegreeTwentySeven, F25DegreeTwentyEight, F25DegreeTwentyNine, F25DegreeThirty, F25DegreeThirtyOne, F25DegreeThirtyTwo, F25DegreeThirtyThree, F25DegreeThirtyFour, F25DegreeThirtyFive, F25DegreeThirtySix, F25DegreeThirtySeven, F25DegreeThirtyEight, F25DegreeThirtyNine, F25DegreeForty, TateNFDivision.F5, TateNFDivision.F6,
    TateNFDivision.F7, TateNFDivision.F8, TateNFDivision.F9]
  ring

/-- **Order-25 division-polynomial identity at the Tate origin, primitive form.**
`preΨ'₂₅(0,0) = b²⁰⁸ · F₅ · F₂₅`, i.e. the order-`5` factor `F₅` and the unit
power `b²⁰⁸` are fully separated from the primitive `F₂₅`. -/
theorem prePsi_twentyfive_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 25).eval 0 = b ^ 208 * TateNFDivision.F5 b c * F25 b c := by
  rw [prePsi_twentyfive_eval_compact, compact_bracket_factor]
  ring

/-- **Order-5 division-polynomial identity at the Tate origin.**
`preΨ'₅(0,0) = b⁸ · F₅`; its nonvanishing is `b ≠ 0 ∧ F₅ b c ≠ 0`. -/
theorem prePsi_five_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 = b ^ 8 * TateNFDivision.F5 b c :=
  prePsi_5_eval b c

/-- **Main theorem.**  The raw order-25 Tate-division system is equivalent to the
single explicit polynomial equation `F₂₅(b,c) = 0` on the locus `b ≠ 0`,
`F₅(b,c) ≠ 0`.  The `b²⁰⁸` unit power and the proper order-`5` factor `F₅`
(whose nonvanishing is exactly `preΨ'₅(0,0) ≠ 0`) are fully separated. -/
theorem raw_order25_obstruction_iff :
    RawOrder25TateObstruction ↔
      ExplicitOrder25Obstruction := by
  constructor
  · rintro ⟨b, c, hEll, hb, h25, h5⟩
    rw [prePsi_five_eval_tate_origin] at h5
    have hF5 : TateNFDivision.F5 b c ≠ 0 := by
      intro hF5; apply h5; rw [hF5, mul_zero]
    refine ⟨b, c, hEll, hb, hF5, ?_⟩
    rw [prePsi_twentyfive_eval_tate_origin] at h25
    have hb208 : b ^ 208 ≠ 0 := pow_ne_zero _ hb
    rcases mul_eq_zero.mp h25 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hb208
      · exact absurd h' hF5
    · exact h
  · rintro ⟨b, c, hEll, hb, hF5, hF25⟩
    refine ⟨b, c, hEll, hb, ?_, ?_⟩
    · rw [prePsi_twentyfive_eval_tate_origin, hF25, mul_zero]
    · rw [prePsi_five_eval_tate_origin]
      exact mul_ne_zero (pow_ne_zero _ hb) hF5

/-- A rational point of exact order 25 produces the explicit primitive
order-25 obstruction. -/
theorem _root_.solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h25 : HasRationalPointOfOrder E 25) :
    ExplicitOrder25Obstruction :=
  raw_order25_obstruction_iff.mp (order25_to_raw_tate_obstruction E h25)

end

end MazurProof.TateOrder25Factor
