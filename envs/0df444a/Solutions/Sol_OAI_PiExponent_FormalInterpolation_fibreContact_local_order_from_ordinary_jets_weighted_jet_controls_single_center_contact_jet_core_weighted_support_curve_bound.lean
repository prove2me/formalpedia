-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core_weighted_support_curve_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:17:43.428241+00:00
-- url     : https://prove2.me/submissions/c9b2e6d8-e9f9-4bc7-b55b-e1ac763a3d47

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
import Mathlib.FieldTheory.IsAlgClosed.Basic

section

open OAI.PiExponent.FormalInterpolation

namespace PiL28

lemma val_prod {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {ι : Type*} (s : Finset ι) (f : ι → E) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem curve_bound
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E]
    (x : Fin (m + 1) → E) (N : Nat)
    (f : MvPolynomial (Fin m) Complex)
    (P : MvPolynomial (Fin m) Complex)
    (hsupport : ∀ a ∈ P.support,
      ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
        ∑ i : Fin m, (a i : Real) * (v i.succ : Real))
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0)
    (j : Fin K) (C : Real) (hC : 0 ≤ C)
    (hcontact : ∀ i : Fin m, C ≤ (e i.succ : Real) *
      (polynomialCurveOrder nu
        (x i.succ - algebraMap Complex E (c j i)) : Real))
    (heval : MvPolynomial.aeval (fun i => x i.succ) f =
      MvPolynomial.aeval
        (fun i => x i.succ - algebraMap Complex E (c j i)) P) :
    C * ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := by
  classical
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  set S := (1 + 2 * (sigma : Real)) * (N : Real)
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · rw [← hC0, zero_mul]; positivity
  set y : Fin m → E := fun i => x i.succ - algebraMap Complex E (c j i)
  -- orders of the y_i
  have hy : ∀ i, C * (v i.succ : ℝ) / R ≤ (polynomialCurveOrder nu (y i) : ℝ) := by
    intro i
    have h1 := hcontact i
    have h2 := hscale i.succ
    have he' : (0 : ℝ) < e i.succ := by exact_mod_cast he i.succ
    rw [div_le_iff₀ hR', h2]
    have hv' := hv i.succ
    nlinarith
  have hyne : ∀ i, y i ≠ 0 := by
    intro i h0
    have := hy i
    rw [h0] at this
    rw [show polynomialCurveOrder nu 0 = 0 by simp [polynomialCurveOrder]] at this
    simp only [Int.cast_zero] at this
    have : 0 < C * (v i.succ : ℝ) / R := div_pos (mul_pos hCpos (hv i.succ)) hR'
    linarith
  have hyv : ∀ i, nu.1 (y i) = ((polynomialCurveOrder nu (y i) : ℤ) : WithTop ℤ) := by
    intro i
    have htop : nu.1 (y i) ≠ ⊤ := by rw [Ne, AddValuation.top_iff]; exact hyne i
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 htop
    unfold polynomialCurveOrder; rw [← hk]; rfl
  set k0 : ℤ := ⌈C * S / R⌉
  -- each term has valuation ≥ k0
  have hterm : ∀ a ∈ P.support, ((k0 : ℤ) : WithTop ℤ) ≤
      nu.1 (algebraMap ℂ E (P.coeff a) * ∏ i, y i ^ a i) := by
    intro a ha
    rw [AddValuation.map_mul, val_prod]
    have hc0 : 0 ≤ nu.1 (algebraMap ℂ E (P.coeff a)) := by
      rw [nu.2.1 _ (MvPolynomial.mem_support_iff.1 ha)]
    have hprod : ∑ i, nu.1 (y i ^ a i) = (((∑ i, (a i : ℤ) * polynomialCurveOrder nu (y i)) : ℤ) : WithTop ℤ) := by
      rw [WithTop.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [AddValuation.map_pow, hyv i, ← WithTop.coe_nsmul, nsmul_eq_mul]
    rw [hprod]
    have hk : k0 ≤ ∑ i, (a i : ℤ) * polynomialCurveOrder nu (y i) := by
      apply Int.ceil_le.2
      push_cast
      have hs := hsupport a ha
      calc C * S / R ≤ C * (∑ i : Fin m, (a i : Real) * (v i.succ : Real)) / R := by
            apply div_le_div_of_nonneg_right _ hR'.le
            exact mul_le_mul_of_nonneg_left hs hC
        _ = ∑ i, (a i : ℝ) * (C * (v i.succ : ℝ) / R) := by
            rw [Finset.mul_sum, Finset.sum_div]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ ∑ i, (a i : ℝ) * (polynomialCurveOrder nu (y i) : ℝ) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (Nat.cast_nonneg _)
    calc ((k0 : ℤ) : WithTop ℤ) = 0 + ((k0 : ℤ) : WithTop ℤ) := by rw [zero_add]
      _ ≤ _ := add_le_add hc0 (by exact_mod_cast hk)
  have hval : ((k0 : ℤ) : WithTop ℤ) ≤ nu.1 (MvPolynomial.aeval (fun i => x i.succ) f) := by
    rw [heval, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    exact AddValuation.map_le_sum _ hterm
  have htop : nu.1 (MvPolynomial.aeval (fun i => x i.succ) f) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]; exact hne
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 htop
  have hord : polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) = k := by
    unfold polynomialCurveOrder; rw [← hk]; rfl
  rw [hord]
  rw [← hk] at hval
  have hkk : k0 ≤ k := by exact_mod_cast hval
  have h1 : C * S / R ≤ (k : ℝ) := le_trans (Int.le_ceil _) (by exact_mod_cast hkk)
  rw [div_le_iff₀ hR'] at h1
  calc C * S ≤ (k : ℝ) * R := h1
    _ ≤ (R : ℝ) * max 0 (k : ℝ) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR'.le

end PiL28

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (N : Nat) (hN : 0 < N)
    (f : MvPolynomial (Fin m) Complex)
    (P : MvPolynomial (Fin m) Complex)
    (hsupport : ∀ a ∈ P.support,
      ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
        ∑ i : Fin m, (a i : Real) * (v i.succ : Real))
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0)
    (j : Fin K) (C : Real) (hC : 0 ≤ C)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hcontact : ∀ i : Fin m, C ≤ (e i.succ : Real) *
      (polynomialCurveOrder nu
        (x i.succ - algebraMap Complex E (c j i)) : Real))
    (heval : MvPolynomial.aeval (fun i => x i.succ) f =
      MvPolynomial.aeval
        (fun i => x i.succ - algebraMap Complex E (c j i)) P) :
    C * ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := by
  apply PiL28.curve_bound <;> assumption
