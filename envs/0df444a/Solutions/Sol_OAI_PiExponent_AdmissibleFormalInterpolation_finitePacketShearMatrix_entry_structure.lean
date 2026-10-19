-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_entry_structure
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:32:25.264216+00:00
-- url     : https://prove2.me/submissions/dfdcc3b4-80d6-4b3a-a5d4-ad0e2f157a38

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_diagonal
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_degree

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (S : Finset (Fin (m + 1) → ℕ))
    (delta : Fin m → PowerSeries ℂ) :
    (∀ i : Fin K × ↥S,
      finitePacketShearMatrix K S delta i i = 1) ∧
    (∀ i j : Fin K × ↥S, i ≠ j →
      finitePacketShearMatrix K S delta i j ≠ 0 →
      (∑ k : Fin m, (InterpolationMatrix.exponentVector i.2.val) k.succ) <
      (∑ k : Fin m, (InterpolationMatrix.exponentVector j.2.val) k.succ)) := by
  constructor
  · intro i
    simp only [finitePacketShearMatrix, if_pos rfl]
    exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_diagonal
      delta i.2.val
  · intro i j hij hentry
    by_cases hpacket : i.1 = j.1
    · have hvec : InterpolationMatrix.exponentVector i.2.val ≠
          InterpolationMatrix.exponentVector j.2.val := by
        intro heq
        apply hij
        apply Prod.ext hpacket
        apply Subtype.ext
        funext x
        have hx := congrArg (fun v : Fin (m + 1) →₀ ℕ => v x) heq
        simpa [InterpolationMatrix.exponentVector] using hx
      have hcoeff : MvPowerSeries.coeff
          (InterpolationMatrix.exponentVector i.2.val)
          (formalShear delta (MvPolynomial.monomial
            (InterpolationMatrix.exponentVector j.2.val) 1)) ≠ 0 := by
        simpa [finitePacketShearMatrix, hpacket] using hentry
      exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_degree
        delta i.2.val j.2.val hvec hcoeff
    · simp [finitePacketShearMatrix, hpacket] at hentry