-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.finite_truncated_polynomial_jets_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:34:25.409463+00:00
-- url     : https://prove2.me/submissions/6610b5a5-417c-44b4-8450-85ef0a19492b

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_translated_polynomial_coefficients_interpolate
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_log_shear_pullback

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

set_option maxHeartbeats 1000000

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hcenters : Function.Injective
      (fun j : Fin K => fun i : Fin m => (j.val : Complex) * r i)) :
    Function.Surjective (truncatedPolynomialPacket K v0 theta w H r T) := by
  classical
  intro y
  let A : Type := {a : Fin (m + 1) → Nat //
    a ∈ strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H}
  let e : A → (Fin (m + 1) →₀ Nat) :=
    fun a => InterpolationMatrix.exponentVector a.1
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm.injective hab
  let c : Fin K → Fin (m + 1) → Complex :=
    fun j i => Fin.cases (0 : Complex) (fun i => (j.val : Complex) * r i) i
  have hc : Function.Injective c := by
    intro j k hjk
    apply hcenters
    funext i
    simpa [c] using congrFun hjk i.succ
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_translated_polynomial_coefficients_interpolate
      c hc e he y
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.FormalInterpolation.truncated_log_shear_pullback T Q
  refine ⟨P, ?_⟩
  funext rho
  change (truncatedPolynomialJet
      (fun i => (rho.1.val : Complex) * r i) T P).coeff
      (InterpolationMatrix.exponentVector rho.2.1) = y rho
  have hp := hP (fun i => (rho.1.val : Complex) * r i)
  rw [hp]
  exact hQ rho.1 rho.2