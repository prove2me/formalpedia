-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_jets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T05:57:15.777388+00:00
-- url     : https://prove2.me/submissions/f2f06397-86fc-4155-bd86-58810934a390
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_derivative_preserves_jets

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
    logarithmicJetBound c v (M - logarithmicFrameCost v word)
      (logarithmicFrameWord word F) := by
  clear hword hF hc hm hK hw hR he hscale hN hM w R e N
  induction word with
  | nil =>
      simpa [logarithmicFrameWord, logarithmicFrameCost] using hjet
  | cons i word ih =>
      have htail :
          logarithmicJetBound c v (M - logarithmicFrameCost v word)
            (logarithmicFrameWord word F) := ih
      have hstep :=
        OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets
          c v (M - logarithmicFrameCost v word) i (hv i)
          (logarithmicFrameWord word F) htail
      have hcost :
          logarithmicFrameCost v (i :: word) =
            (v i : Real) + logarithmicFrameCost v word := by
        simp [logarithmicFrameCost]
      rw [hcost]
      have hthreshold :
          M - ((v i : Real) + logarithmicFrameCost v word) =
            (M - logarithmicFrameCost v word) - (v i : Real) := by
        ring
      rw [hthreshold]
      exact hstep
