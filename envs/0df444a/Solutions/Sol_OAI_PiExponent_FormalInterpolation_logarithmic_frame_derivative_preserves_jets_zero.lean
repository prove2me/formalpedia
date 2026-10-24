-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:11:16.981515+00:00
-- url     : https://prove2.me/submissions/a3983d27-b425-49ed-b173-7cfe3700ecd4

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_logarithmicFrameDerivative_zero_coeff_correct

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (H : Real) (h0 : 0 < (v 0 : Real))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hjet : logarithmicJetBound c v H F) :
    logarithmicJetBound c v (H - (v 0 : Real)) (logarithmicFrameDerivative 0 F) := by
  classical
  intro j a ha
  rw [OAI.PiExponent.FormalInterpolation.formalJet_logarithmicFrameDerivative_zero_coeff_correct]
  let e : Fin (m + 1) →₀ Nat := Finsupp.single (0 : Fin (m + 1)) 1
  have hweight : (∑ i, (v i : Real) * (a i : Real)) < H := by
    calc
      (∑ i, (v i : Real) * (a i : Real)) < (H - (v 0 : Real)) + (v 0 : Real) := by
        linarith [ha, h0]
      _ = H := by ring
  have hsum :
      (∑ i, (v i : Real) * ((a + e) i : Real)) =
        (∑ i, (v i : Real) * (a i : Real)) + (v 0 : Real) := by
    calc
      (∑ i, (v i : Real) * ((a + e) i : Real)) =
          ∑ i, ((v i : Real) * (a i : Real) + (v i : Real) * (e i : Real)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finsupp.add_apply, Nat.cast_add]
        ring
      _ = (∑ i, (v i : Real) * (a i : Real)) +
          (∑ i, (v i : Real) * (e i : Real)) := by rw [Finset.sum_add_distrib]
      _ = (∑ i, (v i : Real) * (a i : Real)) + (v 0 : Real) := by
        simp [e, Finsupp.single_apply]
  have hweight' : (∑ i, (v i : Real) * ((a + e) i : Real)) < H := by
    rw [hsum]
    linarith [ha]
  rw [hjet j a hweight, hjet j (a + e) hweight']
  simp [e]