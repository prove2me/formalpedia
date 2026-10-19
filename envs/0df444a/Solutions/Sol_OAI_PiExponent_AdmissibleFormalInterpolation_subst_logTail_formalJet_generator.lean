-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_generator
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:24:15.89958+00:00
-- url     : https://prove2.me/submissions/9a96bfd8-b3f8-4587-be83-a35daed55ca5

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Tactic.Abel

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

set_option maxHeartbeats 800000

-- The lift is precisely the inclusion of a univariate series in variable zero.
private theorem liftLogSeries_eq_toMvPowerSeries (m : ℕ) (f : PowerSeries ℂ) :
    liftLogSeries m f = f.toMvPowerSeries (0 : Fin (m + 1)) := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  change (MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm (PowerSeries.map MvPowerSeries.C f)) = _
  rw [AlgEquiv.apply_symm_apply]
  apply PowerSeries.ext
  intro k
  apply MvPowerSeries.ext
  intro x
  rw [PowerSeries.coeff_map, MvPowerSeries.coeff_coeff_finSuccEquiv,
    PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.coeff_subst_single]
  simp [MvPowerSeries.coeff_C, Finsupp.cons_eq_single_zero_iff]

private theorem constantCoeff_liftLogSeries (m : ℕ) (f : PowerSeries ℂ) :
    MvPowerSeries.constantCoeff (liftLogSeries m f) = PowerSeries.constantCoeff f := by
  rw [liftLogSeries_eq_toMvPowerSeries, PowerSeries.toMvPowerSeries_apply,
    MvPowerSeries.constantCoeff_rename]
  rfl

-- Any admissible substitution fixing variable zero fixes the entire lifted series.
private theorem subst_liftLogSeries_of_zero_fixed
    {m : ℕ} {a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ}
    (ha : MvPowerSeries.HasSubst a)
    (hzero : a 0 = MvPowerSeries.X 0) (f : PowerSeries ℂ) :
    MvPowerSeries.subst a (liftLogSeries m f) = liftLogSeries m f := by
  simp only [liftLogSeries_eq_toMvPowerSeries]
  rw [PowerSeries.subst_toMvPowerSeries ha, hzero,
    ← PowerSeries.toMvPowerSeries_eq_subst]

theorem solution
    {m : ℕ} (T : Fin m → ℕ) (c : Fin m → ℂ)
    (s : Fin (m + 1)) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
          (fun i : Fin m =>
            MvPowerSeries.X i.succ +
              liftLogSeries m
                ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                  PowerSeries.log ℂ)))
        (formalJet c (MvPolynomial.X s)) =
      truncatedFormalJet T c (MvPolynomial.X s) := by
  classical
  let a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i : Fin m => MvPowerSeries.X i.succ + liftLogSeries m
        ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) - PowerSeries.log ℂ))
  have htrunc (t : ℕ) :
      PowerSeries.constantCoeff
        (InterpolationMatrix.truncatedLog t : PowerSeries ℂ) = 0 := by
    rw [Polynomial.constantCoeff_coe, InterpolationMatrix.truncatedLog,
      PowerSeries.coeff_trunc]
    simp
  have ha : MvPowerSeries.HasSubst a := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [a]
    · simp [a, constantCoeff_liftLogSeries, htrunc]
  have hzero : a 0 = MvPowerSeries.X 0 := by simp [a]
  have hone : MvPowerSeries.subst a (1 : MvPowerSeries (Fin (m + 1)) ℂ) = 1 := by
    rw [← MvPowerSeries.substAlgHom_apply ha, map_one]
  change MvPowerSeries.subst a (formalJet c (MvPolynomial.X s)) =
    truncatedFormalJet T c (MvPolynomial.X s)
  refine Fin.cases ?_ (fun i => ?_) s
  · simp only [formalJet, truncatedFormalJet, MvPolynomial.aeval_X, Fin.cases_zero]
    rw [MvPowerSeries.subst_add ha, hone, MvPowerSeries.subst_X ha, hzero]
  · simp only [formalJet, truncatedFormalJet, MvPolynomial.aeval_X, Fin.cases_succ]
    rw [MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
      MvPowerSeries.subst_C, MvPowerSeries.subst_X ha,
      subst_liftLogSeries_of_zero_fixed ha hzero]
    dsimp only [a, Fin.cases_succ]
    rw [map_sub]
    abel