-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree_and_jets
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T08:50:38.324221+00:00
-- url     : https://prove2.me/submissions/d6b85e50-bb0b-4031-940e-96b558a0bd06

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_word_preserves_degree
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_word_preserves_jets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (w v : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (N M : Real) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hjet : logarithmicJetBound c v M F)
    (word : List (Fin (m + 1)))
    (hword : logarithmicFrameCost v word ≤ M) :
    logarithmicDegreeBound w N (logarithmicFrameWord word F) ∧
      logarithmicJetBound c v (M - logarithmicFrameCost v word)
        (logarithmicFrameWord word F) := by
  constructor
  · exact OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree
      c hc hm hK w v hw hv R e hR he hscale N M hN hM F hF hjet word hword
  · exact OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_jets
      c hc hm hK w v hw hv R e hR he hscale N M hN hM F hF hjet word hword
