-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.rhoApprox_spec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:27:34.798249+00:00
-- url     : https://prove2.me/submissions/665060ef-5940-4216-a260-0b50a7ca5dd4

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Polynomial
open scoped NNReal
theorem h44_rc (n : ℕ) : ∀ j, (rhoCoeffs n).getD j 0 = (rhoPolynomial n).coeff j := by
  induction n with
  | zero =>
    intro j
    rcases j with _ | j
    · simp [rhoCoeffs, rhoPolynomial]
    · simp [rhoCoeffs, rhoPolynomial, Polynomial.coeff_one]
  | succ n ih =>
    intro j
    simp only [rhoCoeffs, rhoPolynomial, rhoCoeffStep]
    rw [Polynomial.coeff_X_pow_mul']
    rcases j with _ | _ | m
    · simp
    · simp
    · rw [if_pos (by omega), show m + 1 + 1 - 2 = m by omega, Polynomial.coeff_sub,
        Polynomial.coeff_derivative, ← ih, ← ih]
      simp only [List.getD_cons_succ]
      by_cases hm : m < (rhoCoeffs n).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
        simp only [Option.map_some, Option.getD_some]
        push_cast; ring
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
        simp
theorem h44_len_pos (n : ℕ) : 0 < (rhoCoeffs n).length := by
  cases n <;> simp [rhoCoeffs, rhoCoeffStep]

theorem h44_eval (n : ℕ) (x : ℝ) : (rhoPolynomial n).eval₂ (Int.castRingHom ℝ) x =
    ∑ j ∈ Finset.range (rhoCoeffs n).length, (((rhoCoeffs n).getD j 0 : ℤ) : ℝ) * x ^ j := by
  have hl := h44_len_pos n
  have hdeg : (rhoPolynomial n).natDegree < (rhoCoeffs n).length := by
    have : (rhoPolynomial n).natDegree ≤ (rhoCoeffs n).length - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [← h44_rc, List.getD_eq_default _ _ (by omega)]
    omega
  rw [Polynomial.eval₂_eq_sum_range' _ hdeg]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [h44_rc]; rfl

theorem h44_abs_le_num (r : ℚ) : |(r : ℝ)| ≤ (r.num.natAbs : ℝ) := by
  have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  rw [Rat.cast_def, abs_div, Nat.abs_cast]
  calc |(r.num : ℝ)| / r.den ≤ |(r.num : ℝ)| := div_le_self (abs_nonneg _) hd
    _ = _ := by rw [Nat.cast_natAbs, Int.cast_abs]

theorem h44_mul_error_le (N : ℕ) : (N : ℝ) * error N ≤ 1 := by
  unfold error
  have hk : (N : ℝ) ≤ 2 ^ N := by exact_mod_cast (Nat.lt_two_pow_self).le
  rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]; exact hk

theorem solution (n : ℕ) (q : ℚ) (p : ℕ) :
    |(rhoApprox n q p : ℝ) - rhoJet n (q : ℝ)| ≤ error p := by
  unfold rhoApprox rhoJet
  by_cases hq : q ≤ 0
  · rw [if_pos hq]
    have : expNegInvGlue (q : ℝ) = 0 := expNegInvGlue.zero_of_nonpos (by exact_mod_cast hq)
    rw [this]; simp only [Rat.cast_zero, mul_zero, sub_zero, abs_zero]
    unfold error; positivity
  · rw [if_neg hq]
    have hq' : (0 : ℝ) < q := by exact_mod_cast (not_le.mp hq)
    have hg : expNegInvGlue (q : ℝ) = Real.exp (-(q : ℝ)⁻¹) := by
      simp [expNegInvGlue, not_le.mpr hq']
    set V := rhoPolyValue n q⁻¹ with hVdef
    have hV : (V : ℝ) = (rhoPolynomial n).eval₂ (Int.castRingHom ℝ) (q : ℝ)⁻¹ := by
      rw [h44_eval, hVdef, rhoPolyValue]; push_cast; rfl
    have hE := expApprox_spec (-q⁻¹) (p + V.num.natAbs)
    rw [show ((-q⁻¹ : ℚ) : ℝ) = -(q : ℝ)⁻¹ by push_cast; rfl] at hE
    rw [hg, Rat.cast_mul, ← hV, ← mul_sub, abs_mul]
    have hA := h44_abs_le_num V
    have hM := h44_mul_error_le V.num.natAbs
    have herr : error (p + V.num.natAbs) = error p * error V.num.natAbs := by
      unfold error; rw [pow_add]
    rw [herr] at hE
    have h0 : 0 ≤ error p := by unfold error; positivity
    have h1 : 0 ≤ error V.num.natAbs := by unfold error; positivity
    calc |(V : ℝ)| * |(expApprox (-q⁻¹) (p + V.num.natAbs) : ℝ) - Real.exp (-(q : ℝ)⁻¹)|
        ≤ (V.num.natAbs : ℝ) * (error p * error V.num.natAbs) :=
          mul_le_mul hA hE (abs_nonneg _) (by positivity)
      _ = error p * ((V.num.natAbs : ℝ) * error V.num.natAbs) := by ring
      _ ≤ error p * 1 := mul_le_mul_of_nonneg_left hM h0
      _ = error p := mul_one _

