-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.global_denominator_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:30:08.451324+00:00
-- url     : https://prove2.me/submissions/f8f7f6be-e5da-4c25-944f-58e694d0e568

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (A B : Fin m → ℕ) (S v0 F : ℝ)
    (hv0 : 0 < v0) (hF : 0 ≤ F) (hS : 0 ≤ S)
    (hBA : ∀ i, B i ≤ A i)
    (hA : (∑ i, ((A i : ℝ) *
      OAI.PiExponent.MatrixArithmetic.logWeights q i)) ≤ S) :
    0 < (∏ i, (q i ^ (A i - B i) *
      Nat.lcmUpto (OAI.PiExponent.MatrixArithmetic.truncationOrders q F v0 i) ^ A i)) ∧
    Real.log ((∏ i, (q i ^ (A i - B i) *
      Nat.lcmUpto (OAI.PiExponent.MatrixArithmetic.truncationOrders q F v0 i) ^ A i) : ℕ) : ℝ) ≤
      S - (∑ i, ((B i : ℝ) * OAI.PiExponent.MatrixArithmetic.logWeights q i)) +
        S * (OAI.PiExponent.Arithmetic.lcmConstant * F * m / v0 +
          OAI.PiExponent.Arithmetic.lcmConstant *
            (∑ i, 1 / OAI.PiExponent.MatrixArithmetic.logWeights q i)) := by
  set w := OAI.PiExponent.MatrixArithmetic.logWeights q with hw
  set T := OAI.PiExponent.MatrixArithmetic.truncationOrders q F v0 with hT
  set Λ := OAI.PiExponent.Arithmetic.lcmConstant with hΛ
  have hΛ0 : 0 < Λ := OAI.PiExponent.Arithmetic.lcmConstant_pos
  have hq0 : ∀ i, 0 < q i := fun i => by have := hq i; omega
  have hlogq : ∀ i, Real.log (q i) ≤ w i := fun i => Nat.le_ceil _
  have hw1 : ∀ i, 1 ≤ w i := by
    intro i
    have : 0 < Real.log (q i) := Real.log_pos (by exact_mod_cast (by have := hq i; omega : 1 < q i))
    have h := Nat.le_ceil (Real.log (q i))
    show (1 : ℝ) ≤ (⌈Real.log (q i)⌉₊ : ℝ)
    have : 0 < ⌈Real.log (q i)⌉₊ := Nat.ceil_pos.mpr this
    exact_mod_cast this
  have hw0 : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw1 i)
  have hTle : ∀ i, (T i : ℝ) ≤ F * w i / v0 + 1 := by
    intro i
    have := Nat.ceil_lt_add_one (show 0 ≤ F * w i / v0 by
      have := hw0 i; positivity)
    exact this.le
  have hlcm : ∀ n : ℕ, Real.log (Nat.lcmUpto n) ≤ Λ * n := by
    intro n
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
  have hpos : ∀ i, 0 < q i ^ (A i - B i) * Nat.lcmUpto (T i) ^ A i := fun i =>
    Nat.mul_pos (pow_pos (hq0 i) _) (pow_pos (Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _)) _)
  refine ⟨Finset.prod_pos fun i _ => hpos i, ?_⟩
  have hAw : ∀ i, (A i : ℝ) * w i ≤ S := fun i =>
    le_trans (Finset.single_le_sum (f := fun i => (A i : ℝ) * w i)
      (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hw0 j).le) (Finset.mem_univ i)) hA
  rw [Nat.cast_prod, Real.log_prod (fun i _ => by exact_mod_cast (hpos i).ne')]
  have hterm : ∀ i, Real.log ((q i ^ (A i - B i) * Nat.lcmUpto (T i) ^ A i : ℕ) : ℝ) ≤
      ((A i : ℝ) * w i - (B i : ℝ) * w i) + (Λ * F / v0 * S + Λ * (S * (1 / w i))) := by
    intro i
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      Real.log_mul (by exact_mod_cast (pow_pos (hq0 i) _).ne')
        (by exact_mod_cast (pow_pos (Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _)) _).ne'),
      Real.log_pow, Real.log_pow, Nat.cast_sub (hBA i)]
    have h1 : ((A i : ℝ) - B i) * Real.log (q i) ≤ ((A i : ℝ) - B i) * w i :=
      mul_le_mul_of_nonneg_left (hlogq i) (by have := hBA i; rw [sub_nonneg]; exact_mod_cast this)
    have h2 : (A i : ℝ) * Real.log (Nat.lcmUpto (T i)) ≤ (A i : ℝ) * (Λ * (F * w i / v0 + 1)) :=
      mul_le_mul_of_nonneg_left ((hlcm _).trans (mul_le_mul_of_nonneg_left (hTle i) hΛ0.le))
        (Nat.cast_nonneg _)
    have h3 : (A i : ℝ) * (Λ * (F * w i / v0 + 1)) = Λ * F / v0 * ((A i : ℝ) * w i) +
        Λ * (((A i : ℝ) * w i) * (1 / w i)) := by
      field_simp [(hw0 i).ne']
    have h4 : Λ * F / v0 * ((A i : ℝ) * w i) ≤ Λ * F / v0 * S :=
      mul_le_mul_of_nonneg_left (hAw i) (by positivity)
    have h5 : Λ * (((A i : ℝ) * w i) * (1 / w i)) ≤ Λ * (S * (1 / w i)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hAw i) (by have := hw0 i; positivity))
        hΛ0.le
    nlinarith
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  have e : (m : ℝ) * (Λ * F / v0 * S) + Λ * (S * ∑ i, 1 / w i) =
      S * (Λ * F * m / v0 + Λ * ∑ i, 1 / w i) := by ring
  linarith
