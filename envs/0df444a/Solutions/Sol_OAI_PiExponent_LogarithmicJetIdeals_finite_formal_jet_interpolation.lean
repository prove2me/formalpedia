-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_formal_jet_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T23:22:19.129102+00:00
-- url     : https://prove2.me/submissions/d19131c3-93a0-4ed9-9111-7adb53678afa

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formal_jet_interpolation_of_injective_requests

theorem solution
    {m : ℕ} {ι : Type} [Fintype ι]
    (K : ℕ) (r : Fin m → ℂ)
    (center : ι → Fin K)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (values : ι → ℂ)
    (hcenters : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (hindex : Function.Injective (fun x => (center x, exponent x))) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ x, MvPowerSeries.coeff (exponent x)
        (OAI.PiExponent.AdmissibleFormalInterpolation.formalJet
          (fun i => ((center x).val : ℂ) * r i) P) = values x := by
  let c : ι → Fin m → ℂ := fun x i => ((center x).val : ℂ) * r i
  have hc : Function.Injective (fun x : ι => (c x, exponent x)) := by
    intro x y h
    apply hindex
    have h₁ : c x = c y := congrArg Prod.fst h
    have h₂ : exponent x = exponent y := congrArg Prod.snd h
    have hcenter : center x = center y := hcenters (by simpa [c] using h₁)
    exact Prod.ext hcenter h₂
  simpa [c] using
    OAI.PiExponent.LogarithmicJetIdeals.formal_jet_interpolation_of_injective_requests
      (c := c) (exponent := exponent) (values := values) hc