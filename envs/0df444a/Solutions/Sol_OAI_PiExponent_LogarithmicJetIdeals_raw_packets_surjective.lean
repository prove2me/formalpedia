-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.raw_packets_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T22:19:45.28528+00:00
-- url     : https://prove2.me/submissions/62604dae-3164-4fa7-bbae-4b3d3b0c88e8

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_formal_jet_interpolation

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
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_formal_jet_interpolation
      (ι := InterpolationMatrix.Row K v0 theta w H) K r
      (fun rho => rho.1)
      (fun rho => Finsupp.equivFunOnFinite.symm rho.2.1)
      values hcenters (by
        intro rho sigma h
        change (rho.1, Finsupp.equivFunOnFinite.symm rho.2.1) =
          (sigma.1, Finsupp.equivFunOnFinite.symm sigma.2.1) at h
        have hj : rho.1 = sigma.1 := congrArg (fun z => z.1) h
        have he : Finsupp.equivFunOnFinite.symm rho.2.1 =
            Finsupp.equivFunOnFinite.symm sigma.2.1 := congrArg (fun z => z.2) h
        have hrow : rho.2.1 = sigma.2.1 :=
          (Finsupp.equivFunOnFinite.symm).injective he
        apply Prod.ext hj
        exact Subtype.ext hrow)
  refine ⟨P, ?_⟩
  funext rho
  exact hP rho