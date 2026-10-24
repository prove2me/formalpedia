-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_word_persistent_prime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:43:35.70682+00:00
-- url     : https://prove2.me/submissions/05281030-e730-4855-a648-9003388e55da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_bounded_word_prime_selection
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_word_preserves_degree_bound

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin (m + 1)) Complex) (hF : F ≠ 0)
    (hdegree : logarithmicDegreeBound w (N : Real) F)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [Q.IsPrime]
    (hwords : ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real) →
        logarithmicFrameWord word F ∈ Q) :
    ∃ P : Ideal (MvPolynomial (Fin (m + 1)) Complex),
      P.IsPrime ∧ P ≠ ⊥ ∧ P ≤ Q ∧
      ∃ S : Finset (MvPolynomial (Fin (m + 1)) Complex),
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P ∧
        (∀ f ∈ S, logarithmicDegreeBound w (N : Real) f) ∧
        (∀ f ∈ S, ∀ word : List (Fin (m + 1)),
          logarithmicFrameCost v word <
            ((sigma : Real) / ((m : Real) + 2)) * (N : Real) →
          logarithmicFrameWord word f ∈ P) := by
  obtain ⟨P, hPprime, hPne, hPle, S, hmin, hFmem, hsource, hpersist⟩ :=
    OAI.PiExponent.FormalInterpolation.logarithmic_bounded_word_prime_selection
      v sigma hsigma hv N hN F hF Q hwords
  refine ⟨P, hPprime, hPne, hPle, S, hmin, ?_, hpersist⟩
  intro f hf
  obtain ⟨word, hword, hcost⟩ := hsource f hf
  rw [hword]
  exact OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree_bound
    w (N : Real) hw F hdegree word