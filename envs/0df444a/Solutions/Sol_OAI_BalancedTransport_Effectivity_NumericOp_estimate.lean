-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.NumericOp.estimate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:32:37.2668+00:00
-- url     : https://prove2.me/submissions/d42d3e93-7aa4-4dc1-8509-e98b99e9cb99

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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp
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

theorem h44_rhoApprox_spec (n : ℕ) (q : ℚ) (p : ℕ) :
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

theorem h44_le_num {r : ℚ} (hr : 0 < r) : (r : ℝ) ≤ (r.num.natAbs : ℝ) := by
  have h1 : r ≤ (r.num : ℚ) := by
    have hn : (0 : ℚ) ≤ r.num := by exact_mod_cast (Rat.num_pos.mpr hr).le
    have hd : (1 : ℚ) ≤ r.den := by exact_mod_cast r.den_pos
    calc r = (r.num : ℚ) / r.den := (Rat.num_div_den r).symm
      _ ≤ r.num := div_le_self hn hd
  have h2 : ((r.num : ℤ) : ℝ) = (r.num.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg (Rat.num_pos.mpr hr).le]
  rw [← h2]; exact_mod_cast h1

theorem h44_log_abs {q : ℚ} (hq : 0 < q) :
    |Real.log (q : ℝ)| ≤ (q.num.natAbs + q⁻¹.num.natAbs : ℕ) := by
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have hA := h44_le_num hq
  have hB := h44_le_num (inv_pos.mpr hq)
  push_cast
  rw [Rat.cast_inv] at hB
  rcases le_total 1 (q : ℝ) with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hq'
    have : (0:ℝ) ≤ (q⁻¹.num.natAbs : ℝ) := by positivity
    linarith
  · rw [abs_of_nonpos (Real.log_nonpos hq'.le h), ← Real.log_inv]
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hq')
    have : (0:ℝ) ≤ (q.num.natAbs : ℝ) := by positivity
    linarith

theorem h44_rhoJet_eq (n : ℕ) : rhoJet n = fun x =>
    ((rhoPolynomial n).map (Int.castRingHom ℝ)).eval x⁻¹ * expNegInvGlue x := by
  funext x; simp only [rhoJet, Polynomial.eval₂_eq_eval_map]

theorem h44_rho_hasDeriv (n : ℕ) (x : ℝ) : HasDerivAt (rhoJet n) (rhoJet (n+1) x) x := by
  rw [h44_rhoJet_eq n]
  have := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    ((rhoPolynomial n).map (Int.castRingHom ℝ)) x
  convert this using 1
  simp only [rhoJet, rhoPolynomial, Polynomial.eval₂_eq_eval_map, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.derivative_map]

theorem h44_rho_bound (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoBound n 0 : ℝ) := by
  have h0 : (0 : ℝ) ≤ (rhoBound n 0 : ℝ) := Nat.cast_nonneg _
  by_cases hx : x ≤ 0
  · rw [rhoJet, expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]; exact h0
  · have hx' : 0 < x := lt_of_not_ge hx
    have hg : expNegInvGlue x = Real.exp (-x⁻¹) := by simp [expNegInvGlue, not_le.mpr hx']
    rw [rhoJet, h44_eval, hg, Finset.sum_mul, rhoBound]
    push_cast
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    have ht : 0 ≤ x⁻¹ := inv_nonneg.mpr hx'.le
    have hf := Real.pow_div_factorial_le_exp (x := x⁻¹) ht j
    have hfp : (0:ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
    have he : x⁻¹ ^ j * Real.exp (-x⁻¹) ≤ (j.factorial : ℝ) := by
      rw [div_le_iff₀ hfp] at hf
      have := Real.exp_pos x⁻¹
      rw [Real.exp_neg]
      calc x⁻¹ ^ j * (Real.exp x⁻¹)⁻¹ ≤ (Real.exp x⁻¹ * j.factorial) * (Real.exp x⁻¹)⁻¹ :=
            mul_le_mul_of_nonneg_right hf (by positivity)
        _ = j.factorial := by field_simp
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (pow_nonneg ht _),
      add_zero, mul_assoc, Nat.cast_natAbs, Int.cast_abs]
    exact mul_le_mul_of_nonneg_left he (abs_nonneg _)

theorem h44_rho_lip (n : ℕ) (u w : ℝ) :
    |rhoJet n u - rhoJet n w| ≤ (rhoBound (n+1) 0 : ℝ) * |u - w| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := rhoJet n)
    (f' := fun y => rhoJet (n+1) y) (C := (rhoBound (n+1) 0 : ℝ)) (s := Set.univ)
    (fun y _ => (h44_rho_hasDeriv n y).hasDerivWithinAt) (fun y _ => h44_rho_bound (n+1) y)
    convex_univ (Set.mem_univ w) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using this

theorem h44_exp_lip (M u w : ℝ) (hu : |u| ≤ M) (hw : |w| ≤ M) :
    |Real.exp u - Real.exp w| ≤ Real.exp M * |u - w| := by
  have hs : Convex ℝ (Set.Icc (-M) M) := convex_Icc _ _
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.exp)
    (f' := Real.exp) (C := Real.exp M) (s := Set.Icc (-M) M)
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun y hy => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr hy.2)
    hs ⟨(abs_le.mp hw).1, (abs_le.mp hw).2⟩ ⟨(abs_le.mp hu).1, (abs_le.mp hu).2⟩
  simpa [Real.norm_eq_abs] using this

theorem h44_exp_le_three (A : ℕ) : Real.exp A ≤ (3:ℝ) ^ A := by
  have h := Real.exp_one_lt_d9
  rw [← mul_one (A : ℝ), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) A

theorem h44_log_spec {q : ℚ} (hq : 0 < q) (n : ℕ) :
    |(logApprox q n : ℝ) - Real.log q| ≤ error n := by
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have hc : logBracket q n (logCutoff (q, n)) := by
    have := Nat.find_spec (exists_logSearchPredicate (q, n))
    unfold logSearchPredicate at this
    rw [if_pos hq] at this
    exact this
  rw [logApprox, if_pos hq]
  dsimp only [logBracket] at hc
  obtain ⟨h1, h2⟩ := hc
  generalize Denumerable.ofNat ℚ (logCutoff (q, n)).unpair.1 = r at h1 h2 ⊢
  generalize (logCutoff (q, n)).unpair.2 = k at h1 h2
  have hl := (abs_le.mp (expApprox_spec (r - (1 / 2 : ℚ) ^ n) k)).1
  have hu := (abs_le.mp (expApprox_spec (r + (1 / 2 : ℚ) ^ n) k)).2
  simp only [Rat.cast_sub, Rat.cast_add, cast_error] at hl hu
  have h1' := (Rat.cast_lt (K := ℝ)).mpr h1
  have h2' := (Rat.cast_lt (K := ℝ)).mpr h2
  rw [Rat.cast_add, cast_error] at h1'
  rw [Rat.cast_sub, cast_error] at h2'
  have e1 : Real.exp ((r : ℝ) - error n) < q := by linarith
  have e2 : (q : ℝ) < Real.exp ((r : ℝ) + error n) := by linarith
  have l1 := (Real.lt_log_iff_exp_lt hq').mpr e1
  have l2 := (Real.log_lt_iff_lt_exp hq').mpr e2
  rw [abs_le]; constructor <;> linarith

theorem h44_add_acc {qa qb sa sb E F e : ℝ} (h1 : |qa - sa| ≤ E * e) (h2 : |qb - sb| ≤ F * e) :
    |(qa + qb) - (sa + sb)| ≤ (E + F) * e := by
  rw [show (qa + qb) - (sa + sb) = (qa - sa) + (qb - sb) by ring, add_mul]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem h44_mul_acc {qa qb sa sb A B E F e : ℝ} (hA : |sa| ≤ A) (hB : |sb| ≤ B)
    (h1 : |qa - sa| ≤ E * e) (h2 : |qb - sb| ≤ F * e) (e1 : e ≤ 1) (E0 : 0 ≤ E) :
    |qa * qb - sa * sb| ≤ ((A + E) * F + B * E) * e := by
  have hq : |qa| ≤ A + E := by
    have := abs_sub_abs_le_abs_sub qa sa
    have : E * e ≤ E := mul_le_of_le_one_right E0 e1
    linarith
  calc |qa * qb - sa * sb| = |qa * (qb - sb) + sb * (qa - sa)| := by congr 1; ring
    _ ≤ |qa| * |qb - sb| + |sb| * |qa - sa| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (A + E) * (F * e) + B * (E * e) :=
        add_le_add (mul_le_mul hq h2 (abs_nonneg _) (le_trans (abs_nonneg _) hq))
          (mul_le_mul hB h1 (abs_nonneg _) (le_trans (abs_nonneg _) hB))
    _ = _ := by ring

theorem h44_inv_acc {N qa sa E e : ℝ} (hN : 0 < N) (hv : N⁻¹ ≤ sa) (h1 : |qa - sa| ≤ E * e) :
    |(max N⁻¹ qa)⁻¹ - sa⁻¹| ≤ N ^ 2 * E * e := by
  have hc : 0 < N⁻¹ := inv_pos.mpr hN
  have hs0 : 0 < sa := lt_of_lt_of_le hc hv
  have hm0 : N⁻¹ ≤ max N⁻¹ qa := le_max_left _ _
  have hmp : 0 < max N⁻¹ qa := lt_of_lt_of_le hc hm0
  have hmd : |max N⁻¹ qa - sa| ≤ |qa - sa| := by
    rcases le_total N⁻¹ qa with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have hprod : 1 ≤ N ^ 2 * (max N⁻¹ qa * sa) := by
    have h3 : N⁻¹ * N⁻¹ ≤ max N⁻¹ qa * sa := mul_le_mul hm0 hv hc.le hmp.le
    calc (1:ℝ) = N ^ 2 * (N⁻¹ * N⁻¹) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  have hEe : 0 ≤ E * e := le_trans (abs_nonneg _) h1
  rw [inv_sub_inv hmp.ne' hs0.ne', abs_div, abs_of_pos (mul_pos hmp hs0),
    div_le_iff₀ (mul_pos hmp hs0), abs_sub_comm]
  calc |max N⁻¹ qa - sa| ≤ E * e := hmd.trans h1
    _ ≤ E * e * (N ^ 2 * (max N⁻¹ qa * sa)) := le_mul_of_one_le_right hEe hprod
    _ = N ^ 2 * E * e * (max N⁻¹ qa * sa) := by ring

theorem solution (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℚ)
    (p C : ℕ) (s : List ℝ) (q : List ℚ) (b : List (ℕ × ℕ))
    (hi : ∀ i, |(x i : ℝ)| ≤ C) (hb : RegisterEstimate p s q b) (hv : Valid o s) :
    |real d o (fun i => (x i : ℝ)) s| ≤ ((bound o C b).1 : ℝ) ∧
    |(rational d o x p q : ℝ) - real d o (fun i => (x i : ℝ)) s| ≤
      ((bound o C b).2 : ℝ) * error p := by
  have hm := hb.magnitude
  have ha := hb.accuracy
  have e0 : 0 ≤ error p := by unfold error; positivity
  have e1 : error p ≤ 1 := by unfold error; exact pow_le_one₀ (by norm_num) (by norm_num)
  rcases o with ⟨tg, r, i, j⟩
  fin_cases tg <;> simp only [NumericOp.real, rational, rationalCase, NumericOp.bound, boundCase,
    tag, left, right, rat, Valid] at hv ⊢
  · refine ⟨h44_abs_le_num r, ?_⟩
    simp
  · refine ⟨hi _, ?_⟩
    simp
  · constructor
    · push_cast; exact (abs_add_le _ _).trans (add_le_add (hm i) (hm j))
    · push_cast; exact h44_add_acc (ha i) (ha j)
  · constructor
    · push_cast; rw [abs_mul]
      exact mul_le_mul (hm i) (hm j) (abs_nonneg _) (le_trans (abs_nonneg _) (hm i))
    · push_cast; exact h44_mul_acc (hm i) (hm j) (ha i) (ha j) e1 (Nat.cast_nonneg _)
  · constructor
    · push_cast; rw [abs_neg]; exact hm i
    · push_cast
      rw [show -(q.getD i 0 : ℝ) - -s.getD i 0 = -((q.getD i 0 : ℝ) - s.getD i 0) by ring, abs_neg]
      exact ha i
  · have hv' := hv rfl
    push_cast at hv' ⊢
    have hN : (0:ℝ) < (j:ℝ) + 1 := by positivity
    have hs0 : 0 < s.getD i 0 := lt_of_lt_of_le (inv_pos.mpr hN) hv'
    constructor
    · rw [abs_of_pos (inv_pos.mpr hs0)]; exact (inv_le_comm₀ hN hs0).mp hv'
    · exact h44_inv_acc hN hv' (ha i)
  · constructor
    · exact h44_rho_bound _ _
    · push_cast
      have h1 := h44_rhoApprox_spec i (q.getD j 0) p
      have h2 := h44_rho_lip i (q.getD j 0 : ℝ) (s.getD j 0)
      have h3 := ha j
      have hR : (0:ℝ) ≤ (rhoBound (i+1) 0 : ℝ) := Nat.cast_nonneg _
      calc |(rhoApprox i (q.getD j 0) p : ℝ) - rhoJet i (s.getD j 0)|
          ≤ |(rhoApprox i (q.getD j 0) p : ℝ) - rhoJet i (q.getD j 0 : ℝ)| +
            |rhoJet i (q.getD j 0 : ℝ) - rhoJet i (s.getD j 0)| := abs_sub_le _ _ _
        _ ≤ error p + (rhoBound (i+1) 0 : ℝ) * (((b.getD j (0,0)).2 : ℝ) * error p) :=
            add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hR))
        _ = _ := by ring
  · have hA := hm i
    have h3 := ha i
    have E0 : (0:ℝ) ≤ ((b.getD i (0,0)).2 : ℝ) := Nat.cast_nonneg _
    have hq : |(q.getD i 0 : ℝ)| ≤ ((b.getD i (0,0)).1 : ℝ) + ((b.getD i (0,0)).2 : ℝ) := by
      have := abs_sub_abs_le_abs_sub (q.getD i 0 : ℝ) (s.getD i 0)
      have : ((b.getD i (0,0)).2 : ℝ) * error p ≤ ((b.getD i (0,0)).2 : ℝ) :=
        mul_le_of_le_one_right E0 e1
      linarith
    have h3A := h44_exp_le_three (b.getD i (0,0)).1
    have h3AE := h44_exp_le_three ((b.getD i (0,0)).1 + (b.getD i (0,0)).2)
    push_cast at h3AE ⊢
    constructor
    · rw [abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_le_exp.mpr ((le_abs_self _).trans hA)).trans h3A
    · have h1 := expApprox_spec (q.getD i 0) p
      have h2 := h44_exp_lip _ (q.getD i 0 : ℝ) (s.getD i 0) hq (by linarith)
      calc |(expApprox (q.getD i 0) p : ℝ) - Real.exp (s.getD i 0)|
          ≤ |(expApprox (q.getD i 0) p : ℝ) - Real.exp (q.getD i 0 : ℝ)| +
            |Real.exp (q.getD i 0 : ℝ) - Real.exp (s.getD i 0)| := abs_sub_le _ _ _
        _ ≤ error p + (3:ℝ) ^ ((b.getD i (0,0)).1 + (b.getD i (0,0)).2) *
              (((b.getD i (0,0)).2 : ℝ) * error p) :=
            add_le_add h1 (h2.trans (mul_le_mul h3AE h3 (abs_nonneg _) (by positivity)))
        _ = _ := by ring
  · by_cases h : 0 < r
    · simp only [h, ↓reduceIte]
      refine ⟨h44_log_abs h, ?_⟩
      push_cast; rw [one_mul]; exact h44_log_spec h p
    · simp only [h, ↓reduceIte]
      refine ⟨by rw [abs_zero]; positivity, ?_⟩
      simp [logApprox, h, e0]

