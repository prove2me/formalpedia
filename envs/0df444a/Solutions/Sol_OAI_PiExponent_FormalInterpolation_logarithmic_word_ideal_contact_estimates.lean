-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_word_ideal_contact_estimates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T08:43:04.317089+00:00
-- url     : https://prove2.me/submissions/41b6a77e-a8cd-4985-8f13-d4c7b372bd13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_word_preserves_degree_and_jets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_jet_contact_bound

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
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (N M : Real) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hjet : logarithmicJetBound c v M F)
    (word : List (Fin (m + 1))) (hword : logarithmicFrameCost v word ≤ M) :
    logarithmicDegreeBound w N (logarithmicFrameWord word F) ∧
      ∀ nu : PolynomialCurvePlace E,
        0 < (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) →
        MvPolynomial.aeval x (logarithmicFrameWord word F) ≠ 0 →
        (M - logarithmicFrameCost v word) *
            (polynomialCurveIdealContact nu x
              (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) ≤
          (R : Real) * (polynomialCurveOrder nu
            (MvPolynomial.aeval x (logarithmicFrameWord word F)) : Real) := by
  have hpres := OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree_and_jets
    c hc hm hK w v hw hv R e hR he hscale N M hN hM F hF hjet word hword
  refine ⟨hpres.1, ?_⟩
  intro nu hcontact hne
  exact OAI.PiExponent.FormalInterpolation.logarithmic_jet_contact_bound
    c hc hm hK v hv R e hR he hscale E htrdeg x hgen
    (M - logarithmicFrameCost v word)
    (logarithmicFrameWord word F) hpres.2 nu hcontact hne