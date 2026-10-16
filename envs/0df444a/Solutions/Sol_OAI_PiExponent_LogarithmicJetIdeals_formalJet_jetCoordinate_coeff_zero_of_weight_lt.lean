-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_jetCoordinate_coeff_zero_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:41:36.358757+00:00
-- url     : https://prove2.me/submissions/db7eacb7-2742-4af4-8a30-9b6472f44764

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

private theorem liftLogSeries_C_candidate (m : ℕ) (z : ℂ) :
    liftLogSeries m (PowerSeries.C z) =
      (MvPowerSeries.C z : MvPowerSeries (Fin (m + 1)) ℂ) := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  simp [liftLogSeries, RingHom.comp_apply]

private theorem liftLogSeries_X_candidate (m : ℕ) :
    liftLogSeries m PowerSeries.X =
      (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℂ) := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  simp [liftLogSeries, RingHom.comp_apply]

private theorem liftLogSeries_polynomial_candidate (m : ℕ) (p : Polynomial ℂ) :
    liftLogSeries m (p : PowerSeries ℂ) =
      p.eval₂ MvPowerSeries.C (MvPowerSeries.X 0) := by
  have hC : (liftLogSeries m).comp PowerSeries.C =
      (MvPowerSeries.C : ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ) := by
    ext1 z
    simp only [RingHom.comp_apply, liftLogSeries_C_candidate]
  calc
    liftLogSeries m (p : PowerSeries ℂ) =
        liftLogSeries m (p.eval₂ PowerSeries.C PowerSeries.X) := by
          rw [Polynomial.eval₂_C_X_eq_coe]
    _ = p.eval₂ ((liftLogSeries m).comp PowerSeries.C)
        (liftLogSeries m PowerSeries.X) :=
          Polynomial.hom_eval₂ p PowerSeries.C (liftLogSeries m) PowerSeries.X
    _ = p.eval₂ MvPowerSeries.C (MvPowerSeries.X 0) := by
          rw [hC, liftLogSeries_X_candidate]

private theorem formalJet_first_candidate {m : ℕ} (c : Fin m → ℂ) :
    formalJet c (MvPolynomial.X 0 - 1) = MvPowerSeries.X 0 := by
  simp [formalJet]

private theorem formalJet_polynomial_candidate {m : ℕ} (c : Fin m → ℂ)
    (p : Polynomial ℂ) :
    formalJet c (p.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1)) =
      liftLogSeries m (p : PowerSeries ℂ) := by
  have hC : (formalJet c).toRingHom.comp MvPolynomial.C =
      (MvPowerSeries.C : ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ) := by
    ext1 z
    simp [RingHom.comp_apply, formalJet, MvPolynomial.aeval_C,
      MvPowerSeries.algebraMap_apply]
  calc
    formalJet c (p.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1)) =
        p.eval₂ ((formalJet c).toRingHom.comp MvPolynomial.C)
          (formalJet c (MvPolynomial.X 0 - 1)) :=
      Polynomial.hom_eval₂ p MvPolynomial.C (formalJet c).toRingHom
        (MvPolynomial.X 0 - 1)
    _ = p.eval₂ MvPowerSeries.C (MvPowerSeries.X 0) := by
      rw [hC, formalJet_first_candidate]
    _ = liftLogSeries m (p : PowerSeries ℂ) :=
      (liftLogSeries_polynomial_candidate m p).symm

private theorem formalJet_successor_candidate {m : ℕ} (c : Fin m → ℂ)
    (T : Fin m → ℕ) (k : Fin m) :
    formalJet c (jetCoordinate c T k.succ) =
      MvPowerSeries.X k.succ + liftLogSeries m
        (PowerSeries.log ℂ - (InterpolationMatrix.truncatedLog (T k) : PowerSeries ℂ)) := by
  have hx : formalJet c (MvPolynomial.X k.succ) =
      MvPowerSeries.C (c k) + MvPowerSeries.X k.succ +
        liftLogSeries m (PowerSeries.log ℂ) := by
    simp [formalJet]
  have hc : formalJet c (MvPolynomial.C (c k)) = MvPowerSeries.C (c k) := by
    simp [formalJet, MvPolynomial.aeval_C, MvPowerSeries.algebraMap_apply]
  change formalJet c (MvPolynomial.X k.succ - MvPolynomial.C (c k) -
      (InterpolationMatrix.truncatedLog (T k)).eval₂ MvPolynomial.C
        (MvPolynomial.X 0 - 1)) = _
  rw [map_sub, map_sub, hx, hc, formalJet_polynomial_candidate, map_sub]
  ring

-- Splitting the exponent into its zeroth entry and its tail identifies the
-- lifted coefficient with a coefficient of a constant multivariate series.
private theorem liftLogSeries_coeff_zero_candidate {m : ℕ} (f : PowerSeries ℂ)
    (d : Fin (m + 1) →₀ ℕ) (h : PowerSeries.coeff (d 0) f = 0) :
    MvPowerSeries.coeff d (liftLogSeries m f) = 0 := by
  have he : MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m f) =
      PowerSeries.map MvPowerSeries.C f := by
    simp [liftLogSeries, RingHom.comp_apply]
  calc
    MvPowerSeries.coeff d (liftLogSeries m f) =
        MvPowerSeries.coeff d.tail (PowerSeries.coeff (d 0)
          (MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m f))) := by
      simpa only [Finsupp.cons_tail] using
        (MvPowerSeries.coeff_coeff_finSuccEquiv (liftLogSeries m f)
          (k := d 0) (x := d.tail)).symm
    _ = 0 := by
      rw [he, PowerSeries.coeff_map, h, map_zero, MvPowerSeries.coeff_zero]

private theorem X_coeff_zero_candidate {m : ℕ}
    (v0 theta : ℝ) (w : Fin m → ℝ)
    (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) <
      InterpolationMatrix.rowWeights v0 theta w i) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPowerSeries.X i : MvPowerSeries (Fin (m + 1)) ℂ) = 0 := by
  classical
  have hne : InterpolationMatrix.exponentVector a ≠ Finsupp.single i 1 := by
    intro h
    have hab : ∀ j, a j = if j = i then 1 else 0 := by
      intro j
      have hj := congrArg (fun d : Fin (m + 1) →₀ ℕ => d j) h
      simpa [InterpolationMatrix.exponentVector, Finsupp.single_apply, eq_comm] using hj
    have hs : (∑ k : Fin (m + 1),
        InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) =
        InterpolationMatrix.rowWeights v0 theta w i := by
      simp_rw [hab]
      simp [mul_ite]
    rw [hs] at ha
    exact (lt_irrefl _ ha)
  simp [MvPowerSeries.coeff_X, hne]

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ)
    (hweights : ∀ k, 0 < InterpolationMatrix.rowWeights v0 theta w k)
    (hT : ∀ k, InterpolationMatrix.rowWeights v0 theta w k.succ ≤ (T k : ℝ) * v0)
    (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) <
      InterpolationMatrix.rowWeights v0 theta w i) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet c (jetCoordinate c T i)) = 0 := by
  classical
  cases i using Fin.cases with
  | zero =>
      change MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (formalJet c (MvPolynomial.X 0 - 1)) = 0
      rw [formalJet_first_candidate]
      exact X_coeff_zero_candidate v0 theta w 0 a ha
  | succ k =>
      have hv0 : 0 < v0 := by
        simpa [InterpolationMatrix.rowWeights] using hweights 0
      have hlow : InterpolationMatrix.rowWeights v0 theta w 0 * (a 0 : ℝ) ≤
          ∑ j : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w j * (a j : ℝ) :=
        Finset.single_le_sum
          (fun j _ => mul_nonneg (le_of_lt (hweights j)) (Nat.cast_nonneg (a j)))
          (Finset.mem_univ 0)
      have hz : InterpolationMatrix.rowWeights v0 theta w 0 = v0 := rfl
      rw [hz] at hlow
      have hmul : (a 0 : ℝ) * v0 < (T k : ℝ) * v0 := by
        calc
          (a 0 : ℝ) * v0 = v0 * (a 0 : ℝ) := mul_comm _ _
          _ ≤ ∑ j : Fin (m + 1),
              InterpolationMatrix.rowWeights v0 theta w j * (a j : ℝ) := hlow
          _ < InterpolationMatrix.rowWeights v0 theta w k.succ := ha
          _ ≤ (T k : ℝ) * v0 := hT k
      have hn : a 0 < T k := by
        exact_mod_cast (mul_lt_mul_iff_left₀ hv0).mp hmul
      have htail : PowerSeries.coeff (a 0)
          (PowerSeries.log ℂ -
            (InterpolationMatrix.truncatedLog (T k) : PowerSeries ℂ)) = 0 := by
        simp only [map_sub, InterpolationMatrix.truncatedLog,
          PowerSeries.coeff_coe_trunc_of_lt hn, sub_self]
      have htail' : PowerSeries.coeff ((InterpolationMatrix.exponentVector a) 0)
          (PowerSeries.log ℂ -
            (InterpolationMatrix.truncatedLog (T k) : PowerSeries ℂ)) = 0 := by
        simpa [InterpolationMatrix.exponentVector] using htail
      rw [formalJet_successor_candidate, map_add,
        X_coeff_zero_candidate v0 theta w k.succ a ha, zero_add]
      exact liftLogSeries_coeff_zero_candidate _ (InterpolationMatrix.exponentVector a) htail'
