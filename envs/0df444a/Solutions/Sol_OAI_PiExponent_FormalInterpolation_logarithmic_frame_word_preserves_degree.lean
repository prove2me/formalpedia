-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T08:59:13.237855+00:00
-- url     : https://prove2.me/submissions/44c97c70-9c80-4c28-bc69-665f36caad46

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicFrameDerivative_preserves_degree

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
    logarithmicDegreeBound w N (logarithmicFrameWord word F) := by
  have hiter : ∀ l : List (Fin (m + 1)),
      logarithmicDegreeBound w N (logarithmicFrameWord l F) := by
    intro l
    induction l with
    | nil => simpa [logarithmicFrameWord] using hF
    | cons i l ih =>
        simpa [logarithmicFrameWord] using
          OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_preserves_degree
            w hw N (logarithmicFrameWord l F) ih i
  exact hiter word