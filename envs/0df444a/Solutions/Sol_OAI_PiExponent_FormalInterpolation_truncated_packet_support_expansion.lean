-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_support_expansion
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:46:43.353647+00:00
-- url     : https://prove2.me/submissions/c050a990-b18a-42c9-a7d1-0d9c78a8012d

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

-- The center is multiplied by the row index twice on the right-hand side.
theorem solution :
    ¬ (∀ {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
      (r : Fin m → Complex) (T : Fin m → Nat)
      (P : MvPolynomial (Fin (m + 1)) Complex)
      (rho : InterpolationMatrix.Row K v0 theta w H),
      truncatedPolynomialPacket K v0 theta w H r T P rho =
        ∑ e ∈ P.support,
          P.coeff e * InterpolationMatrix.entry
            (fun i => (rho.1.val : Complex) * r i)
            (fun i => InterpolationMatrix.truncatedLog (T i))
            rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
            (e 0) (fun i => e i.succ)) := by
  classical
  intro hall
  have hzero2 :
      InterpolationMatrix.exponentVector (fun _ : Fin 2 => 0) = 0 := by
    ext i
    rfl
  have hzero1 :
      InterpolationMatrix.exponentVector (fun _ : Fin 1 => 0) = 0 := by
    ext i
    rfl
  have hrow : (fun _ : Fin 2 => 0) ∈
      strictWeightedSimplex
        (InterpolationMatrix.rowWeights 0 1 (fun _ : Fin 1 => 0)) 1 := by
    simp [strictWeightedSimplex, realWeightedSimplex]
  let rho : InterpolationMatrix.Row 3 0 1 (fun _ : Fin 1 => 0) 1 :=
    (⟨2, by decide⟩, ⟨fun _ => 0, hrow⟩)
  have hpacket :
      truncatedPolynomialPacket 3 0 1 (fun _ : Fin 1 => 0) 1
        (fun _ => 1) (fun _ => 0)
        (MvPolynomial.X (0 : Fin 1).succ) rho = (2 : Complex) := by
    norm_num [truncatedPolynomialPacket, truncatedPolynomialJet, rho,
      InterpolationMatrix.truncatedLog, hzero2]
    -- Expose the successor constructor after numeral normalization.
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, Fin.cases_succ]
    simp
  have hbad := hall (m := 1) 3 0 0 1 (fun _ => 0) 1
    (fun _ => 1) (fun _ => 0) (MvPolynomial.X (0 : Fin 1).succ) rho
  rw [hpacket] at hbad
  norm_num [MvPolynomial.support_X, rho, InterpolationMatrix.entry,
    InterpolationMatrix.monomialImage, InterpolationMatrix.truncatedLog,
    Fin.prod_univ_one, hzero1, Finsupp.single_apply] at hbad