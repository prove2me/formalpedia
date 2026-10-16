-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_truncation_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:18:44.567976+00:00
-- url     : https://prove2.me/submissions/8455cc6e-2589-4492-a5e5-0451df5c9463

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_algHom_congr_below_totalDegree
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_liftLogSeries_coeff_truncation
import Mathlib.Tactic.Ring

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (center : Fin m → ℂ)
    (R : MvPolynomial (Fin (m + 1)) ℂ) (T : ℕ) :
    ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ d : Fin (m + 1) → ℕ,
        (∑ i, d i) < T →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (formalJet center Q) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (MvPolynomial.toMvPowerSeries R) := by
  classical
  let L : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ n ∈ Finset.range T,
      MvPolynomial.C (PowerSeries.coeff n (PowerSeries.log ℂ)) *
        (MvPolynomial.X (0 : Fin (m + 1)) - 1) ^ n
  let B : MvPowerSeries (Fin (m + 1)) ℂ :=
    ∑ n ∈ Finset.range T,
      MvPowerSeries.C (PowerSeries.coeff n (PowerSeries.log ℂ)) *
        (MvPowerSeries.X (0 : Fin (m + 1))) ^ n
  let v : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ :=
    Fin.cases (MvPolynomial.X 0 - 1)
      (fun i => MvPolynomial.X i.succ - MvPolynomial.C (center i) - L)
  let F : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
      MvPowerSeries (Fin (m + 1)) ℂ :=
    (formalJet center).comp (MvPolynomial.aeval v)
  let G : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
      MvPowerSeries (Fin (m + 1)) ℂ :=
    MvPolynomial.coeToMvPowerSeries.algHom ℂ
  have hzero :
      formalJet center (MvPolynomial.X (0 : Fin (m + 1)) - 1) =
        MvPowerSeries.X 0 := by
    rw [map_sub, map_one, formalJet, MvPolynomial.aeval_X]
    change (1 + MvPowerSeries.X (0 : Fin (m + 1))) - 1 =
      MvPowerSeries.X 0
    ring
  have hconst (z : ℂ) :
      formalJet center (MvPolynomial.C z) = MvPowerSeries.C z := by
    simp [formalJet, MvPowerSeries.algebraMap_apply]
  have hsucc (i : Fin m) :
      formalJet center (MvPolynomial.X i.succ) =
        MvPowerSeries.C (center i) + MvPowerSeries.X i.succ +
          liftLogSeries m (PowerSeries.log ℂ) := by
    simp only [formalJet, MvPolynomial.aeval_X, Fin.cases_succ]
  have hL : formalJet center L = B := by
    dsimp only [L, B]
    simp only [map_sum, map_mul, map_pow, hconst, hzero]
  have hGX (i : Fin (m + 1)) : G (MvPolynomial.X i) = MvPowerSeries.X i := by
    simp [G, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPowerSeries.map_id]
  have hvar (i : Fin (m + 1)) (d : Fin (m + 1) → ℕ)
      (hd : (∑ j, d j) < T) :
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (F (MvPolynomial.X i)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (G (MvPolynomial.X i)) := by
    have hd0 : d 0 < T :=
      lt_of_le_of_lt
        (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ 0)) hd
    have hlog :
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
            (liftLogSeries m (PowerSeries.log ℂ)) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) B := by
      exact OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_truncation
        m (PowerSeries.log ℂ) T d hd0
    simp only [F, AlgHom.comp_apply, MvPolynomial.aeval_X, hGX]
    refine Fin.cases ?_ (fun j => ?_) i
    · change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (formalJet center (MvPolynomial.X (0 : Fin (m + 1)) - 1)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X 0)
      rw [hzero]
    · change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (formalJet center
            (MvPolynomial.X j.succ - MvPolynomial.C (center j) - L)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X j.succ)
      simp only [map_sub, map_add, hsucc, hconst, hL]
      rw [hlog]
      ring
  refine ⟨MvPolynomial.aeval v R, ?_⟩
  intro d hd
  have h := OAI.PiExponent.LogarithmicJetIdeals.coeff_algHom_congr_below_totalDegree
    F G T hvar R d hd
  simpa only [F, G, AlgHom.comp_apply,
    MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
    MvPowerSeries.map_id, RingHom.id_apply] using h