-- Prove2me | solution 3 for OAI.PiExponent.LogarithmicJetIdeals.raw_packets_surjective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T19:41:31.909745+00:00
-- url     : https://prove2.me/submissions/5d0d3a10-908b-487f-9bc0-59b3c993669e

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_formal_jet_interpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hcenters : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i)) :
    Function.Surjective (rawPacketMap K v0 theta w H r) := by
  classical
  intro y
  have hindex : Function.Injective
      (fun ρ : InterpolationMatrix.Row K v0 theta w H =>
        (ρ.1, InterpolationMatrix.exponentVector ρ.2.val)) := by
    intro x z hxz
    have hc : x.1 = z.1 :=
      congrArg (fun p : Fin K × (Fin (m + 1) →₀ ℕ) => p.1) hxz
    have hf : InterpolationMatrix.exponentVector x.2.val =
        InterpolationMatrix.exponentVector z.2.val :=
      congrArg (fun p : Fin K × (Fin (m + 1) →₀ ℕ) => p.2) hxz
    have he : x.2.val = z.2.val := by
      funext i
      have hi := congrArg (fun a : Fin (m + 1) →₀ ℕ => a i) hf
      simpa [InterpolationMatrix.exponentVector] using hi
    exact Prod.ext hc (Subtype.ext he)
  obtain ⟨P, hP⟩ := finite_formal_jet_interpolation K r
    (fun ρ : InterpolationMatrix.Row K v0 theta w H => ρ.1)
    (fun ρ => InterpolationMatrix.exponentVector ρ.2.val)
    y hcenters hindex
  refine ⟨P, ?_⟩
  funext ρ
  exact hP ρ
