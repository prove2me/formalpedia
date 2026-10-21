-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_subst_seriesJet
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:11:40.179227+00:00
-- url     : https://prove2.me/submissions/b5888967-ac96-438a-9bdf-bb9c56326363

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_liftLogSeries_of_X_zero
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_constantCoeff

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

/-- Substituting the shear family into a series jet amounts to adding the shear series to the
coefficients, because substitution is compatible with the `MvPolynomial` evaluation defining the jet
and fixes the lifted logarithm series (which has no `X 0`-constant). -/
theorem solution {m : ℕ} (D F : Fin m → PowerSeries ℂ) (c : Fin m → ℂ)
    (hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i)))
        (seriesJet c F P) =
      seriesJet c (fun i => F i + D i) P := by
  classical
  let S : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))
  let E : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (1 + MvPowerSeries.X 0)
      (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + liftLogSeries m (F i))
  let E' : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (1 + MvPowerSeries.X 0)
      (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
        liftLogSeries m ((fun i => F i + D i) i))
  have hS0 : S 0 = MvPowerSeries.X 0 := by
    dsimp only [S]
    rw [Fin.cases_zero]
  have hSsucc : ∀ j : Fin m,
      S j.succ = MvPowerSeries.X j.succ + liftLogSeries m (D j) := by
    intro j
    dsimp only [S]
    rw [Fin.cases_succ]
  have hconst : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 := by
    intro i
    cases i using Fin.cases with
    | zero => rw [hS0]; exact MvPowerSeries.constantCoeff_X 0
    | succ j =>
        rw [hSsucc j,
          map_add (MvPowerSeries.constantCoeff (σ := Fin (m + 1)) (R := ℂ)),
          MvPowerSeries.constantCoeff_X,
          show MvPowerSeries.constantCoeff (liftLogSeries m (D j)) = PowerSeries.coeff 0 (D j) from
            liftLogSeries_constantCoeff (m := m) (D j),
          hD0 j, zero_add]
  have haS : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hconst
  have hsub_lift : ∀ f : PowerSeries ℂ,
      MvPowerSeries.subst S (liftLogSeries m f) = liftLogSeries m f :=
    fun f => subst_liftLogSeries_of_X_zero f S haS hS0
  have hE0 : E 0 = 1 + MvPowerSeries.X 0 := by
    dsimp only [E]
    rw [Fin.cases_zero]
  have hE'0 : E' 0 = 1 + MvPowerSeries.X 0 := by
    dsimp only [E']
    rw [Fin.cases_zero]
  have hEsucc : ∀ j : Fin m,
      E j.succ = MvPowerSeries.C (c j) + MvPowerSeries.X j.succ + liftLogSeries m (F j) := by
    intro j
    dsimp only [E]
    rw [Fin.cases_succ]
  have hE'succ : ∀ j : Fin m,
      E' j.succ = MvPowerSeries.C (c j) + MvPowerSeries.X j.succ +
        liftLogSeries m (F j + D j) := by
    intro j
    dsimp only [E']
    rw [Fin.cases_succ]
  have hone : MvPowerSeries.subst S (1 : MvPowerSeries (Fin (m + 1)) ℂ) = 1 := by
    rw [show (1 : MvPowerSeries (Fin (m + 1)) ℂ) = MvPowerSeries.C 1 from
      (map_one (MvPowerSeries.C (σ := Fin (m + 1)) (R := ℂ))).symm,
      MvPowerSeries.subst_C]
  have hcoord : ∀ i, MvPowerSeries.subst S (E i) = E' i := by
    intro i
    cases i using Fin.cases with
    | zero =>
        rw [hE0, hE'0, MvPowerSeries.subst_add haS, MvPowerSeries.subst_X haS, hS0, hone]
    | succ j =>
        rw [hEsucc j, hE'succ j, MvPowerSeries.subst_add haS, MvPowerSeries.subst_add haS,
          MvPowerSeries.subst_C, MvPowerSeries.subst_X haS, hSsucc j, hsub_lift (F j)]
        rw [show liftLogSeries m (F j + D j) =
            liftLogSeries m (F j) + liftLogSeries m (D j) from
          map_add (liftLogSeries m) (F j) (D j)]
        abel
  change MvPowerSeries.subst S (MvPolynomial.aeval E P) = MvPolynomial.aeval E' P
  rw [← MvPowerSeries.substAlgHom_apply haS (MvPolynomial.aeval E P)]
  rw [MvPolynomial.comp_aeval_apply (f := E) (φ := MvPowerSeries.substAlgHom haS) (p := P)]
  rw [show (fun i => MvPowerSeries.substAlgHom haS (E i)) = E' from
    funext (fun i => by
      rw [MvPowerSeries.substAlgHom_apply]
      exact hcoord i)]
