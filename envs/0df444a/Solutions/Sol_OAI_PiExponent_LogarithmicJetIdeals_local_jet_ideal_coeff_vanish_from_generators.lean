-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_coeff_vanish_from_generators
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T07:04:20.693021+00:00
-- url     : https://prove2.me/submissions/ebe22645-38f2-4888-a583-555cbcc47fde

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_mem_span_image
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_mvPowerSeries_span_weighted_coeff_vanish

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hweights : ∀ j : Fin (m + 1), 0 < InterpolationMatrix.rowWeights v0 theta w j)
    (hgen : ∀ b : Fin (m + 1) → ℕ,
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R →
      ∀ i : Fin (m + 1),
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
          (AdmissibleFormalInterpolation.formalJet c (jetCoordinate c T i ^ e i)) = 0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ localJetIdeal c T e)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (a j : ℝ)) < R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet c Q) = 0 := by
  let G : Set (MvPolynomial (Fin (m + 1)) ℂ) :=
    Set.range (fun i : Fin (m + 1) => jetCoordinate c T i ^ e i)
  have hQ' : Q ∈ Ideal.span G := by
    simpa [G, localJetIdeal] using hQ
  have hmap : formalJet c Q ∈ Ideal.span (formalJet c '' G) :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_mem_span_image c G Q hQ'
  have hgens : ∀ F ∈ formalJet c '' G, ∀ b : Fin (m + 1) → ℕ,
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F = 0 := by
    intro F hF b hb
    rcases hF with ⟨P, hP, rfl⟩
    rcases hP with ⟨i, rfl⟩
    exact hgen b hb i
  exact OAI.PiExponent.LogarithmicJetIdeals.mvPowerSeries_span_weighted_coeff_vanish
    (ω := InterpolationMatrix.rowWeights v0 theta w) R hweights
    (formalJet c '' G) hgens a ha (formalJet c Q) hmap