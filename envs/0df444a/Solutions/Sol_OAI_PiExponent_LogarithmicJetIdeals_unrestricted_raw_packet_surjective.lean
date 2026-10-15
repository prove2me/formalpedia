-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.unrestricted_raw_packet_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:45:19.355273+00:00
-- url     : https://prove2.me/submissions/fa1040fb-917c-40d6-848e-c28875c8b910
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_formalJet_coefficients_surjective
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_nat_scalar_centers_pairwise_distinct

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (hr : ∃ i, r i ≠ 0) :
    Function.Surjective (rawPacketMap K v0 theta w H r) := by
  classical
  have hcenters : ∀ j l : Fin K, j ≠ l →
      ∃ i : Fin m, (j.val : ℂ) * r i ≠ (l.val : ℂ) * r i :=
    OAI.PiExponent.LogarithmicJetIdeals.nat_scalar_centers_pairwise_distinct K r hr
  have hindex : Function.Injective
      (fun rho : InterpolationMatrix.Row K v0 theta w H =>
        (rho.1, rho.2.1)) := by
    intro rho sigma h
    have hfst : rho.1 = sigma.1 :=
      congrArg (fun p : Fin K × (Fin (m + 1) → ℕ) => p.1) h
    have hsnd : rho.2.val = sigma.2.val :=
      congrArg (fun p : Fin K × (Fin (m + 1) → ℕ) => p.2) h
    exact Prod.ext hfst (Subtype.ext hsnd)
  change Function.Surjective
    (fun P : MvPolynomial (Fin (m + 1)) ℂ =>
      fun rho : InterpolationMatrix.Row K v0 theta w H =>
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (AdmissibleFormalInterpolation.formalJet
            (fun i => (rho.1.val : ℂ) * r i) P))
  simpa [InterpolationMatrix.exponentVector] using
    (OAI.PiExponent.LogarithmicJetIdeals.finite_formalJet_coefficients_surjective
      (ι := Fin K) (α := InterpolationMatrix.Row K v0 theta w H) (m := m)
      (center := fun j i => (j.val : ℂ) * r i)
      (slot := fun rho => rho.1)
      (degree := fun rho => rho.2.val)
      hindex hcenters)