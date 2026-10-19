-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.ideal_power_raw_packet_of_coefficient_profile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:54:53.821721+00:00
-- url     : https://prove2.me/submissions/e17f1666-cbb0-4747-a87c-d2954afff5c5

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.Tactic
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (r : Fin m → ℂ)
    (R : ℝ) (n : ℕ)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ), Q ∈ I →
      ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
        (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (AdmissibleFormalInterpolation.formalJet
            (fun i => (j.val : ℂ) * r i) Q) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ I ^ n) :
    rawPacketMap K v0 theta w ((n : ℝ) * R) r P = 0 := by
  classical
  let v : Fin (m + 1) → ℝ := InterpolationMatrix.rowWeights v0 theta w
  have hw (a : Fin (m + 1) →₀ ℕ) : 0 ≤ Finsupp.weight v a := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_nonneg (fun i _ => nsmul_nonneg (hv i).le (a i))
  let J (S : ℝ) : Ideal (MvPowerSeries (Fin (m + 1)) ℂ) :=
    { carrier := {F | ∀ a, Finsupp.weight v a < S → MvPowerSeries.coeff a F = 0}
      zero_mem' := by simp
      add_mem' := by
        intro F G hF hG a ha
        rw [map_add, hF a ha, hG a ha, add_zero]
      smul_mem' := by
        intro F G hG a ha
        change MvPowerSeries.coeff a (F * G) = 0
        rw [MvPowerSeries.coeff_mul]
        apply Finset.sum_eq_zero
        intro ab hab
        have he : ab.1 + ab.2 = a := (Finset.HasAntidiagonal.mem_antidiagonal).mp hab
        have hwa : Finsupp.weight v ab.2 ≤ Finsupp.weight v a := by
          rw [← he, map_add]
          exact le_add_of_nonneg_left (hw ab.1)
        rw [hG ab.2 (hwa.trans_lt ha), mul_zero] }
  have hJmul (A B : ℝ) : J A * J B ≤ J (A + B) := by
    apply Ideal.mul_le.mpr
    intro F hF G hG a ha
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ab hab
    have he : ab.1 + ab.2 = a := (Finset.HasAntidiagonal.mem_antidiagonal).mp hab
    by_cases hfirst : Finsupp.weight v ab.1 < A
    · rw [hF ab.1 hfirst, zero_mul]
    · have hsecond : Finsupp.weight v ab.2 < B := by
        by_contra hsecond
        have hsum := add_le_add (le_of_not_gt hfirst) (le_of_not_gt hsecond)
        rw [← map_add, he] at hsum
        exact (not_le_of_gt ha) hsum
      rw [hG ab.2 hsecond, mul_zero]
  funext ρ
  let c : Fin m → ℂ := fun i => (ρ.1.val : ℂ) * r i
  let φ : MvPolynomial (Fin (m + 1)) ℂ →+*
      MvPowerSeries (Fin (m + 1)) ℂ :=
    (AdmissibleFormalInterpolation.formalJet c).toRingHom
  have hI : I ≤ Ideal.comap φ (J R) := by
    intro Q hQ a ha
    have he : InterpolationMatrix.exponentVector (fun i => a i) = a := by
      ext i
      simp [InterpolationMatrix.exponentVector]
    have hwa : (∑ i, v i * (a i : ℝ)) < R := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, nsmul_eq_mul,
        mul_comm] using ha
    have hh := hcoeff Q hQ ρ.1 (fun i => a i) hwa
    change MvPowerSeries.coeff a (AdmissibleFormalInterpolation.formalJet c Q) = 0
    rw [← he]
    exact hh
  have hpow : ∀ k : ℕ, I ^ k ≤ Ideal.comap φ (J ((k : ℝ) * R)) := by
    intro k
    induction k with
    | zero =>
        intro Q hQ a ha
        have h0 := hw a
        simp only [Nat.cast_zero, zero_mul] at ha
        exact (False.elim ((not_lt_of_ge h0) ha))
    | succ k ih =>
        rw [pow_succ]
        apply Ideal.mul_le.mpr
        intro F hF G hG
        have hh := (Ideal.mul_le.mp (hJmul ((k : ℝ) * R) R))
          (φ F) (ih hF) (φ G) (hI hG)
        change φ (F * G) ∈ J (((k + 1 : ℕ) : ℝ) * R)
        simpa only [map_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          using hh
  have hp := hpow n hP
  change MvPowerSeries.coeff
    (InterpolationMatrix.exponentVector ρ.2.val)
    (AdmissibleFormalInterpolation.formalJet c P) = 0
  apply hp
  have hrow : (∑ i, v i * (ρ.2.val i : ℝ)) < (n : ℝ) * R := by
    exact (Finset.mem_filter.mp ρ.2.property).2
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, nsmul_eq_mul,
    InterpolationMatrix.exponentVector, mul_comm] using hrow
