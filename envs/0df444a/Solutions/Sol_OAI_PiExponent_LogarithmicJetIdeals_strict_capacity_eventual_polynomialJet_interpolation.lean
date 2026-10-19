-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_eventual_polynomialJet_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:02:40.92227+00:00
-- url     : https://prove2.me/submissions/9ddf49de-5ea9-4715-bb73-4af603b6f387
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomialJet_pow_membership_iff
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomialJet_interpolation_of_injective_centers
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_affine_normal_form_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) (R S : ℝ)
    (e : Fin (d.m + 1) → ℕ) (T : Fin d.m → ℕ)
    (hR : 0 < R) (hRS : R < S)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (hcapacity : 2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ))
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ <
      (T i : ℝ) * (d.v0 : ℝ)) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ f : Fin d.K → (Fin (d.m + 1) →₀ ℕ) → ℂ,
        ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ,
          (∀ u ∈ Q.support,
            (∑ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i *
              (u i : ℝ)) ≤ (k : ℝ) * R) ∧
          (∀ j : Fin d.K, ∀ u : Fin (d.m + 1) →₀ ℕ,
            (∑ i, u i / e i) < k →
              MvPolynomial.coeff u
                (polynomialJet
                  (fun i => (j.val : ℂ) *
                    MatrixArithmetic.rationalCenters (finiteNumerators d)
                      (finiteDenominators d) i) T Q) = f j u) := by
  classical
  obtain ⟨ρ, B, hρ, hρR, hB, hforms⟩ :=
    strict_capacity_affine_normal_form_bound d R S e T hR hRS he hcommon hcapacity hT
  let r : Fin d.m → ℂ :=
    MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)
  let c : Fin d.K → Fin d.m → ℂ := fun j i => (j.val : ℂ) * r i
  let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
  have hp : (d.p i.val : ℂ) ≠ 0 := by
    exact_mod_cast (d.approximations i.val).2.1
  have hq : (d.q i.val : ℂ) ≠ 0 := by
    exact_mod_cast (show d.q i.val ≠ 0 by
      have := (d.approximations i.val).1
      omega)
  have hr : r i ≠ 0 := by
    change 2 * Complex.I * (d.p i.val : ℂ) / (d.q i.val : ℂ) ≠ 0
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  have hc : Function.Injective c := by
    intro j l h
    have hij : (j.val : ℂ) * r i = (l.val : ℂ) * r i := congrFun h i
    have hv : (j.val : ℂ) = (l.val : ℂ) := mul_right_cancel₀ hr hij
    apply Fin.ext
    exact_mod_cast hv
  obtain ⟨N, hN⟩ := exists_nat_ge (B / (R - ρ))
  refine ⟨N, ?_⟩
  intro k hk f
  have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have habsorb : B ≤ (k : ℝ) * (R - ρ) :=
    (div_le_iff₀ (sub_pos.mpr hρR)).mp (hN.trans hNk)
  obtain ⟨P, hP⟩ :=
    polynomialJet_interpolation_of_injective_centers c T e he hc k f
  obtain ⟨Q, hQ, hPQ⟩ := hforms k P
  refine ⟨Q, ?_, ?_⟩
  · intro u hu
    have hbound : (k : ℝ) * ρ + B ≤ (k : ℝ) * R := by nlinarith [habsorb]
    exact (hQ u hu).trans hbound
  · intro j u hu
    have hI : simultaneousJetIdeal d.K r T e ≤ localJetIdeal (c j) T e := by
      unfold simultaneousJetIdeal
      exact iInf_le _ j
    have hmem : P - Q ∈ localJetIdeal (c j) T e ^ k :=
      (pow_le_pow_left' hI k) hPQ
    have hzero : MvPolynomial.coeff u (polynomialJet (c j) T (P - Q)) = 0 :=
      (polynomialJet_pow_membership_iff (c j) T e he k (P - Q)).mp hmem u hu
    rw [map_sub, MvPolynomial.coeff_sub] at hzero
    change MvPolynomial.coeff u (polynomialJet (c j) T Q) = f j u
    calc
      MvPolynomial.coeff u (polynomialJet (c j) T Q) =
          MvPolynomial.coeff u (polynomialJet (c j) T P) :=
        (sub_eq_zero.mp hzero).symm
      _ = f j u := hP j u hu
