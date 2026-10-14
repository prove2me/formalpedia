-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_packets_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T06:57:10.183599+00:00
-- url     : https://prove2.me/submissions/6836aa6d-33fc-4bcd-8f2e-2fb6cc9fa4ac

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Tactic.Ring

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

lemma jet_logarithmic_coordinate {m : Nat} (c : Fin m → Complex)
    (T : Fin m → Nat) (i : Fin (m + 1)) :
    truncatedPolynomialJet c T (logarithmicCoordinate c T i) = MvPolynomial.X i := by
  have hzero : truncatedPolynomialJet c T (MvPolynomial.X 0 - 1) =
      MvPolynomial.X 0 := by
    simp [truncatedPolynomialJet]
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hzero
  · change truncatedPolynomialJet c T
      (MvPolynomial.X j.succ - MvPolynomial.C (c j) -
        Polynomial.aeval (MvPolynomial.X 0 - 1)
          (InterpolationMatrix.truncatedLog (T j))) = _
    rw [map_sub, map_sub, ← Polynomial.aeval_algHom_apply, hzero]
    simp only [truncatedPolynomialJet, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Fin.cases_succ, MvPolynomial.algebraMap_eq]
    ring

lemma jet_ideal_coeff_zero {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (Q : MvPolynomial (Fin (m + 1)) Complex)
    (hQ : Q ∈ logarithmicCenterIdeal c T e) (a : Fin (m + 1) →₀ Nat)
    (ha : ∀ i, a i < e i) : (truncatedPolynomialJet c T Q).coeff a = 0 := by
  classical
  obtain ⟨f, hf⟩ := Ideal.mem_span_range_iff_exists_fun.mp hQ
  rw [← hf, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_mul, map_pow, jet_logarithmic_coordinate, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_mul_monomial']
  have hnot : ¬ Finsupp.single i (e i) ≤ a := by
    simpa only [Finsupp.single_le_iff, not_le] using ha i
  rw [if_neg hnot]

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (hscale : ∀ i, R ≤ (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (Q : MvPolynomial (Fin (m + 1)) Complex)
    (hQ : Q ∈ logarithmicCentersIdeal
      (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) :
    truncatedPolynomialPacket K v0 theta w R r T Q = 0 := by
  classical
  funext rho
  have hle : (∏ j : Fin K,
      logarithmicCenterIdeal (fun i => (j.val : Complex) * r i) T e) ≤
      logarithmicCenterIdeal (fun i => (rho.1.val : Complex) * r i) T e := by
    calc
      _ ≤ Finset.univ.inf
          (fun j : Fin K => logarithmicCenterIdeal
            (fun i => (j.val : Complex) * r i) T e) := Ideal.prod_le_inf
      _ ≤ logarithmicCenterIdeal (fun i => (rho.1.val : Complex) * r i) T e :=
        Finset.inf_le (Finset.mem_univ rho.1)
  have hlocal : Q ∈ logarithmicCenterIdeal
      (fun i => (rho.1.val : Complex) * r i) T e := hle hQ
  change (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T Q).coeff
    (InterpolationMatrix.exponentVector rho.2.val) = 0
  apply jet_ideal_coeff_zero _ T e Q hlocal
  intro i
  have hweights : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i := by
    intro j
    refine Fin.cases hv0 (fun k => ?_) j
    exact div_pos (hw k) htheta
  have hsum : (∑ j, InterpolationMatrix.rowWeights v0 theta w j *
      (rho.2.val j : Real)) < R := (Finset.mem_filter.mp rho.2.property).2
  have hterm : InterpolationMatrix.rowWeights v0 theta w i * (rho.2.val i : Real) ≤
      ∑ j, InterpolationMatrix.rowWeights v0 theta w j * (rho.2.val j : Real) := by
    apply Finset.single_le_sum (s := Finset.univ) (a := i)
      (f := fun j : Fin (m + 1) =>
        InterpolationMatrix.rowWeights v0 theta w j * (rho.2.val j : Real))
    · intro j hj
      exact mul_nonneg (hweights j).le (Nat.cast_nonneg _)
    · exact Finset.mem_univ i
  change rho.2.val i < e i
  by_contra h
  have hcast : (e i : Real) ≤ (rho.2.val i : Real) := by exact_mod_cast (Nat.le_of_not_gt h)
  have hmul := mul_le_mul_of_nonneg_left hcast (hweights i).le
  have hthreshold := hscale i
  rw [mul_comm (e i : Real)] at hthreshold
  linarith
