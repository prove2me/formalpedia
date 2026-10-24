-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_excess_forces_derivative_vanishing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:25:27.831993+00:00
-- url     : https://prove2.me/submissions/3dc51d8f-6520-427d-80df-21ffad17d0d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_word_support_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_lower
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_divisor_vanishing

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (N : Nat) (hN : 0 < N) (F : MvPolynomial (Fin m) Complex)
    (hF : fibreContactSupportBound (fun i => w i.succ) N F)
    (hjet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 3 * (sigma : Real)) * (N : Real)) F)
    (hexcess :
      (R : Real) / (1 + (sigma : Real)) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))) :
    ∀ word : List (Fin m),
      fibreContactWordCost (fun i => v i.succ) word ≤ (sigma : Real) * (N : Real) →
        MvPolynomial.aeval (fun i => x i.succ) (fibreContactWord word F) = 0 := by
  intro word hword
  let P : MvPolynomial (Fin m) Complex := fibreContactWord word F
  have hP : fibreContactSupportBound (fun i => w i.succ) N P := by
    simpa [P] using
      OAI.PiExponent.FormalInterpolation.fibreContact_word_support_bound
        (fun i => w i.succ) N F hF word (fun i => (hw i.succ).le)
  apply OAI.PiExponent.FormalInterpolation.fibreContact_divisor_vanishing
    (K := K) (htrdeg := htrdeg) (x := x) (hgen := hgen) (hfibre := hfibre)
    (w := w) (R := R) (sigma := sigma) (hR := hR) (hsigma := hsigma)
    (N := N) (hN := hN) (P := P)
    (I := logarithmicCentersIdeal c (fun _ => e 0) e)
    (hP := hP) (hexcess := hexcess)
  intro hne nu
  exact OAI.PiExponent.FormalInterpolation.fibreContact_local_order_lower
    (c := c) (hc := hc) (v := v) (sigma := sigma) (hsigma := hsigma)
    (hv := hv) (R := R) (e := e) (hR := hR) (he := he) (hscale := hscale)
    (E := E) (htrdeg := htrdeg) (x := x) (hgen := hgen) (hfibre := hfibre)
    (hnonconst := hnonconst) (N := N) (hN := hN) (F := F) (hjet := hjet)
    (word := word) (hword := hword) (nu := nu) hne