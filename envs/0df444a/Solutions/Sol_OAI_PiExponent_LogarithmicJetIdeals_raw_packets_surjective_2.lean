-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.raw_packets_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:26:57.746745+00:00
-- url     : https://prove2.me/submissions/e3caac5d-b75a-4de9-9308-eafdf1928094
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_formal_jet_interpolation
import Mathlib.Tactic
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
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
  intro values
  let α := InterpolationMatrix.Row K v0 theta w H
  have hindex : Function.Injective
      (fun rho : α => (rho.1, InterpolationMatrix.exponentVector rho.2.val)) := by
    intro rho sigma h
    apply Prod.ext
    · exact congrArg (fun p : Fin K × (Fin (m + 1) →₀ ℕ) => p.1) h
    · apply Subtype.ext
      have he : InterpolationMatrix.exponentVector rho.2.val =
          InterpolationMatrix.exponentVector sigma.2.val :=
        congrArg (fun p : Fin K × (Fin (m + 1) →₀ ℕ) => p.2) h
      exact Finsupp.equivFunOnFinite.symm.injective he
  obtain ⟨P, hP⟩ := finite_formal_jet_interpolation K r
    (fun rho : α => rho.1)
    (fun rho : α => InterpolationMatrix.exponentVector rho.2.val)
    values hcenters hindex
  refine ⟨P, ?_⟩
  funext rho
  simpa only [rawPacketMap] using hP rho
