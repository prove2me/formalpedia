-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:23:37.901548+00:00
-- url     : https://prove2.me/submissions/3f1b0e17-efe3-4acf-9b0d-addf27972bce

import Mathlib
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators
theorem pie_coeff_lift {m : ℕ} (D : PowerSeries ℂ) (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b (liftLogSeries m D) =
      if b.tail = 0 then PowerSeries.coeff (b 0) D else 0 := by
  conv_lhs => rw [← Finsupp.cons_tail b]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp only [liftLogSeries, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    Function.comp_apply, RingEquiv.coe_toRingHom]
  rw [show (MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm.toRingEquiv (PowerSeries.map MvPowerSeries.C D))
      = PowerSeries.map MvPowerSeries.C D from
    (MvPowerSeries.finSuccEquiv ℂ m).apply_symm_apply _]
  rw [PowerSeries.coeff_map, MvPowerSeries.coeff_C]

theorem pie_subst_fix_lift {m : ℕ} (σ : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hσ : MvPowerSeries.HasSubst σ) (h0 : σ 0 = MvPowerSeries.X 0) (D : PowerSeries ℂ) :
    MvPowerSeries.subst σ (liftLogSeries m D) = liftLogSeries m D := by
  classical
  ext e
  rw [MvPowerSeries.coeff_subst hσ]
  rw [finsum_eq_single _ e]
  · by_cases ht : e.tail = 0
    · have he : e = Finsupp.single 0 (e 0) := by
        rw [← Finsupp.cons_tail e, ht]
        ext i
        induction i using Fin.cases with
        | zero => simp
        | succ k => simp [Finsupp.single_apply, Fin.succ_ne_zero]
      have hprod : (e.prod fun s n => σ s ^ n) = MvPowerSeries.X 0 ^ (e 0) := by
        conv_lhs => rw [he]
        rw [Finsupp.prod_single_index (by simp), h0]
      rw [hprod, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, ← he, if_pos rfl,
        smul_eq_mul, mul_one]
    · rw [pie_coeff_lift, if_neg ht, zero_smul]
  · intro d hd
    by_cases ht : d.tail = 0
    · have hdd : d = Finsupp.single 0 (d 0) := by
        rw [← Finsupp.cons_tail d, ht]
        ext i
        induction i using Fin.cases with
        | zero => simp
        | succ k => simp [Finsupp.single_apply, Fin.succ_ne_zero]
      have hprod : (d.prod fun s n => σ s ^ n) = MvPowerSeries.X 0 ^ (d 0) := by
        conv_lhs => rw [hdd]
        rw [Finsupp.prod_single_index (by simp), h0]
      rw [hprod, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, ← hdd, if_neg (Ne.symm hd),
        smul_zero]
    · rw [pie_coeff_lift, if_neg ht, zero_smul]

theorem solution
    {m : ℕ} (T : Fin m → ℕ) (c : Fin m → ℂ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
          (fun i : Fin m =>
            MvPowerSeries.X i.succ +
              liftLogSeries m
                ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                  PowerSeries.log ℂ)))
        (formalJet c P) = truncatedFormalJet T c P := by
  classical
  set σ : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ := Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
          (fun i : Fin m =>
            MvPowerSeries.X i.succ +
              liftLogSeries m
                ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                  PowerSeries.log ℂ)) with hσdef
  have hσ : MvPowerSeries.HasSubst σ := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    induction s using Fin.cases with
    | zero => simp [σ]
    | succ k =>
      simp only [σ, Fin.cases_succ, map_add, MvPowerSeries.constantCoeff_X, zero_add]
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, pie_coeff_lift]
      simp [InterpolationMatrix.truncatedLog, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  have key : (MvPowerSeries.substAlgHom hσ).comp (formalJet c) = truncatedFormalJet T c := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply]
    induction i using Fin.cases with
    | zero =>
      simp only [formalJet, truncatedFormalJet, MvPolynomial.aeval_X, Fin.cases_zero, map_add, map_one,
        MvPowerSeries.substAlgHom_X]
      rfl
    | succ k =>
      simp only [formalJet, truncatedFormalJet, MvPolynomial.aeval_X, Fin.cases_succ, map_add,
        MvPowerSeries.substAlgHom_X]
      have hC : MvPowerSeries.substAlgHom hσ (MvPowerSeries.C (c k)) = MvPowerSeries.C (c k) := by
        rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C]
      have hL : MvPowerSeries.substAlgHom hσ (liftLogSeries m (PowerSeries.log ℂ)) =
          liftLogSeries m (PowerSeries.log ℂ) := by
        rw [MvPowerSeries.coe_substAlgHom]; exact pie_subst_fix_lift σ hσ rfl _
      rw [hC, hL]
      simp only [σ, Fin.cases_succ, map_sub]
      ring
  have := congrArg (fun φ => φ P) key
  simpa [MvPowerSeries.coe_substAlgHom] using this
