-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_local_power_coeff_transfer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:41:47.771647+00:00
-- url     : https://prove2.me/submissions/4eb26d5c-f9f8-4e16-9a93-67e331be06f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_vanishing_subst_triangular_tails
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localCoordinatePolynomial_eq_subst_formalJet_log_tail

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

private theorem quotient_sum_lt_implies_weighted_sum_lt
    {m : ℕ} (q : Fin (m + 1) → ℝ) (S : ℝ)
    (e : Fin (m + 1) → ℕ)
    (hS : 0 < S) (hq : ∀ i, 0 < q i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (e i : ℝ) * q i ≤ S)
    (n : ℕ) (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, a i / e i : ℕ) < n) :
    (∑ i, q i * (a i : ℝ)) < ((n + m : ℕ) : ℝ) * S := by
  classical
  have hterm (i : Fin (m + 1)) :
      q i * (a i : ℝ) < (((a i / e i : ℕ) : ℝ) + 1) * S := by
    have hnat : a i < e i * (a i / e i + 1) :=
      Nat.lt_mul_div_succ (a i) (he i)
    have hreal : (a i : ℝ) < (e i : ℝ) * (((a i / e i : ℕ) : ℝ) + 1) := by
      exact_mod_cast hnat
    calc
      q i * (a i : ℝ) < q i * ((e i : ℝ) * (((a i / e i : ℕ) : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left hreal (hq i)
      _ = (((a i / e i : ℕ) : ℝ) + 1) * ((e i : ℝ) * q i) := by ring
      _ ≤ (((a i / e i : ℕ) : ℝ) + 1) * S :=
        mul_le_mul_of_nonneg_left (hscale i) (by positivity)
  have hsum : (∑ i, q i * (a i : ℝ)) <
      ∑ i, (((a i / e i : ℕ) : ℝ) + 1) * S := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hterm i).le
    · exact ⟨0, Finset.mem_univ 0, hterm 0⟩
  have hsum_eq : (∑ i, (((a i / e i : ℕ) : ℝ) + 1) * S) =
      (((∑ i, a i / e i : ℕ) + (m + 1) : ℕ) : ℝ) * S := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    simp
  have hcount : (∑ i, a i / e i : ℕ) + (m + 1) ≤ n + m := by omega
  have hcount_real :
      (((∑ i, a i / e i : ℕ) + (m + 1) : ℕ) : ℝ) ≤ ((n + m : ℕ) : ℝ) := by
    exact_mod_cast hcount
  calc
    (∑ i, q i * (a i : ℝ)) <
        (((∑ i, a i / e i : ℕ) + (m + 1) : ℕ) : ℝ) * S := hsum.trans_eq hsum_eq
    _ ≤ ((n + m : ℕ) : ℝ) * S :=
      mul_le_mul_of_nonneg_right hcount_real hS.le

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (S : ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hS : 0 < S)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i ≤ S)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ (a : Fin (m + 1) → ℕ),
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        ((n + m : ℕ) : ℝ) * S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet c P) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, a i / e i : ℕ) < n →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (localCoordinatePolynomial c T P) = 0 := by
  have htail : ∀ (i : Fin m) (k : ℕ), k < T i →
      PowerSeries.coeff k
        ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
          PowerSeries.log ℂ) = 0 := by
    intro i k hk
    change PowerSeries.coeff k
      ((PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) -
        PowerSeries.log ℂ) = 0
    rw [map_sub, PowerSeries.coeff_coe_trunc_of_lt hk, sub_self]
  have hT' : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤
        (T i : ℝ) * InterpolationMatrix.rowWeights v0 theta w 0 := by
    intro i
    simpa [InterpolationMatrix.rowWeights] using hT i
  intro a ha
  have hweight := quotient_sum_lt_implies_weighted_sum_lt
    (InterpolationMatrix.rowWeights v0 theta w) S e hS hv he hscale n a ha
  have hz := weighted_vanishing_subst_triangular_tails
    (InterpolationMatrix.rowWeights v0 theta w) T
    (fun i => (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
      PowerSeries.log ℂ)
    hv hT' htail (((n + m : ℕ) : ℝ) * S) (formalJet c P) hcoeff a hweight
  rw [← localCoordinatePolynomial_eq_subst_formalJet_log_tail c T P] at hz
  simpa only [MvPolynomial.coeff_coe] using hz
