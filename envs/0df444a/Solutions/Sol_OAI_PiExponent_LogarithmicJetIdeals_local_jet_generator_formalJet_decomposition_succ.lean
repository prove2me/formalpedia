-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_formalJet_decomposition_succ
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T15:58:47.498924+00:00
-- url     : https://prove2.me/submissions/b64cadbc-178d-4d3a-b731-0e60799b21b7

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation OAI.PiExponent.LogarithmicJetIdeals
open MvPowerSeries

namespace TestLemmas

variable {m : ℕ} (c : Fin m → ℂ)

lemma finSuccEquiv_liftLogSeries (s : PowerSeries ℂ) :
    (MvPowerSeries.finSuccEquiv ℂ m) (liftLogSeries m s) =
      PowerSeries.map MvPowerSeries.C s := by
  simp [liftLogSeries]

lemma liftLogSeries_C (a : ℂ) :
    liftLogSeries m (PowerSeries.C a) = MvPowerSeries.C a := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  rw [finSuccEquiv_liftLogSeries, PowerSeries.map_C, MvPowerSeries.finSuccEquiv_C]

lemma liftLogSeries_X :
    liftLogSeries m (PowerSeries.X (R := ℂ)) = MvPowerSeries.X (0 : Fin (m + 1)) := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  rw [finSuccEquiv_liftLogSeries, PowerSeries.map_X, MvPowerSeries.finSuccEquiv_X_zero]

lemma formalJet_C (a : ℂ) : formalJet c (MvPolynomial.C a) = MvPowerSeries.C a := by
  rw [MvPolynomial.C_eq_algebraMap]
  have h := MvPolynomial.aeval_C (Fin.cases (1 + MvPowerSeries.X (0 : Fin (m + 1)))
    (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ
      + liftLogSeries m (PowerSeries.log ℂ))) a
  rw [MvPowerSeries.c_eq_algebraMap] at h
  exact h

lemma formalJet_X_zero :
    formalJet c (MvPolynomial.X (0 : Fin (m + 1))) =
      (1 : MvPowerSeries (Fin (m + 1)) ℂ) + MvPowerSeries.X 0 := by
  simp [formalJet]

lemma formalJet_subst (q : Polynomial ℂ) :
    formalJet c (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1) q) =
      liftLogSeries m (Polynomial.toPowerSeries q) := by
  let F : Polynomial ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
    (formalJet c).toRingHom.comp (Polynomial.aeval (MvPolynomial.X 0 - 1)).toRingHom
  let G : Polynomial ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
    (liftLogSeries m).comp Polynomial.coeToPowerSeries.ringHom
  have hFG : F = G := by
    apply Polynomial.ringHom_ext
    · intro a
      show formalJet c ((Polynomial.aeval (MvPolynomial.X 0 - 1)) (Polynomial.C a)) =
        liftLogSeries m ((Polynomial.C a : Polynomial ℂ) : PowerSeries ℂ)
      rw [Polynomial.aeval_C, show formalJet c (algebraMap ℂ (MvPolynomial (Fin (m + 1)) ℂ) a)
        = MvPowerSeries.C a from formalJet_C c a,
        Polynomial.coe_C, liftLogSeries_C]
    · show formalJet c ((Polynomial.aeval (MvPolynomial.X 0 - 1)) Polynomial.X) =
        liftLogSeries m ((Polynomial.X : Polynomial ℂ) : PowerSeries ℂ)
      rw [Polynomial.aeval_X, Polynomial.coe_X, liftLogSeries_X, map_sub, map_one,
        formalJet_X_zero c]
      ring
  have hq := RingHom.congr_fun hFG q
  dsimp only [F, G, RingHom.comp_apply] at hq
  have haeval : (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)) - 1)).toRingHom q
      = Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1) q := by
    change (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)) - 1)) q
      = Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1) q
    rw [Polynomial.aeval_def, MvPolynomial.C_eq_algebraMap]
  rw [haeval] at hq
  have hcoe : liftLogSeries m (Polynomial.coeToPowerSeries.ringHom q) =
      liftLogSeries m (Polynomial.toPowerSeries q) := rfl
  rw [hcoe] at hq
  exact hq

end TestLemmas

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation OAI.PiExponent.LogarithmicJetIdeals
open MvPowerSeries

theorem solution {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (i : Fin m) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.formalJet c
        (OAI.PiExponent.LogarithmicJetIdeals.jetCoordinate c T i.succ)) =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (MvPowerSeries.X i.succ) +
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.liftLogSeries m
          (PowerSeries.log ℂ -
            (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) := by
  have hsubst := TestLemmas.formalJet_subst c (InterpolationMatrix.truncatedLog (T i))
  have hdec : AdmissibleFormalInterpolation.formalJet c
      (OAI.PiExponent.LogarithmicJetIdeals.jetCoordinate c T i.succ) =
      (MvPowerSeries.X i.succ : MvPowerSeries (Fin (m + 1)) ℂ) +
        AdmissibleFormalInterpolation.liftLogSeries m
          (PowerSeries.log ℂ - (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ)) := by
    rw [show OAI.PiExponent.LogarithmicJetIdeals.jetCoordinate c T i.succ =
        (MvPolynomial.X i.succ - MvPolynomial.C (c i) -
          Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1)
            (InterpolationMatrix.truncatedLog (T i))) from by
      simp [OAI.PiExponent.LogarithmicJetIdeals.jetCoordinate]]
    rw [map_sub, map_sub, hsubst]
    have hX : AdmissibleFormalInterpolation.formalJet c (MvPolynomial.X i.succ) =
        MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
          AdmissibleFormalInterpolation.liftLogSeries m (PowerSeries.log ℂ) := by
      simp [AdmissibleFormalInterpolation.formalJet]
    have hC : AdmissibleFormalInterpolation.formalJet c (MvPolynomial.C (c i)) =
        MvPowerSeries.C (c i) := TestLemmas.formalJet_C c (c i)
    rw [hX, hC, map_sub]
    ring
  rw [hdec, map_add]
