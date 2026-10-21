-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.simultaneous_jet_ideal_coeff_vanish_below_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T22:46:10.02998+00:00
-- url     : https://prove2.me/submissions/e1f9e604-6d5b-458f-87ac-a16c94f161ee

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_coeff_vanish_below_scale

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (r : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ simultaneousJetIdeal K r T e)
    (j : Fin K) (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet
        (fun i => (j.val : ℂ) * r i) Q) = 0 := by
  have hQ' : Q ∈ (⨅ k : Fin K,
      localJetIdeal (fun i => (k.val : ℂ) * r i) T e) := by
    exact hQ
  have hlocal : Q ∈ localJetIdeal (fun i => (j.val : ℂ) * r i) T e :=
    (Ideal.mem_iInf.mp hQ') j
  exact local_jet_ideal_coeff_vanish_below_scale
    v0 theta w (fun i => (j.val : ℂ) * r i) R T e
    hv0 htheta hw hR he hT Q hlocal a ha