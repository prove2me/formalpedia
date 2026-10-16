-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_roundtrip
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:12:19.596445+00:00
-- url     : https://prove2.me/submissions/21a9d2d1-1714-4da5-929d-98beada58271
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_constantCoeff
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_liftLogSeries_of_X_zero

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0) :
    MvPowerSeries.HasSubst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) ∧
      MvPowerSeries.HasSubst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i))) ∧
      (fun j => MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i)) j)) =
        MvPowerSeries.X := by
  let plus : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))
  let minus : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i))
  have hD0 (i : Fin m) : PowerSeries.coeff 0 (D i) = 0 :=
    hD i 0 (by simpa using hq i.succ)
  have hL (i : Fin m) :
      MvPowerSeries.constantCoeff (liftLogSeries m (D i)) = 0 := by
    rw [OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_constantCoeff]
    exact hD0 i
  have hplus : MvPowerSeries.HasSubst plus := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro j
    cases j using Fin.cases with
    | zero => simp [plus]
    | succ i => simp [plus, hL]
  have hminus : MvPowerSeries.HasSubst minus := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro j
    cases j using Fin.cases with
    | zero => simp [minus]
    | succ i => simp [minus, hL]
  refine ⟨hplus, hminus, ?_⟩
  funext j
  cases j using Fin.cases with
  | zero =>
      change MvPowerSeries.subst minus (MvPowerSeries.X 0) = MvPowerSeries.X 0
      rw [MvPowerSeries.subst_X hminus]
      simp [minus]
  | succ i =>
      change MvPowerSeries.subst minus
        (MvPowerSeries.X i.succ + liftLogSeries m (D i)) = MvPowerSeries.X i.succ
      rw [MvPowerSeries.subst_add hminus, MvPowerSeries.subst_X hminus]
      rw [OAI.PiExponent.AdmissibleFormalInterpolation.subst_liftLogSeries_of_X_zero
        (D i) minus hminus (by simp [minus])]
      change (MvPowerSeries.X i.succ - liftLogSeries m (D i)) +
        liftLogSeries m (D i) = MvPowerSeries.X i.succ
      exact sub_add_cancel _ _
