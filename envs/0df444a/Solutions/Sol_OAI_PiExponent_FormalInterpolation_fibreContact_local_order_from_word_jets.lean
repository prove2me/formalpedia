-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_word_jets
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:34:39.11905+00:00
-- url     : https://prove2.me/submissions/c53efe8b-de68-4214-84ae-45a939a5e6a8

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (N : Nat) (hN : 0 < N) (F : MvPolynomial (Fin m) Complex)
    (word : List (Fin m))
    (hwordJet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 2 * (sigma : Real)) * (N : Real)) (fibreContactWord word F))
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) (fibreContactWord word F) ≠ 0) :
    ((polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) *
      ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu
          (MvPolynomial.aeval (fun i => x i.succ) (fibreContactWord word F)) : Real) := by
  exact OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets
    c hc v sigma hsigma hv R e hR he hscale E htrdeg x hgen hfibre hnonconst
    N hN (fibreContactWord word F) hwordJet nu hne
