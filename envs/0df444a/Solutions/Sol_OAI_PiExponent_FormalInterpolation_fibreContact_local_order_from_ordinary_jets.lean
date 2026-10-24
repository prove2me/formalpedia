-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:41:04.448596+00:00
-- url     : https://prove2.me/submissions/f99721c5-9e37-4ba6-95a7-e28a16938d7b

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_product_contact_is_zero_or_one_center
import Mathlib.FieldTheory.IsAlgClosed.Basic

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
    (N : Nat) (hN : 0 < N) (f : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 2 * (sigma : Real)) * (N : Real)) f)
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0) :
    ((polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) *
      ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := by
  have hsplit :=
    OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_product_contact_is_zero_or_one_center
      c hc v sigma hsigma hv R e hR he hscale E htrdeg x hgen hfibre hnonconst
      N hN f hjet nu hne
  rcases hsplit with hz | ⟨j, hcontact⟩
  · simp [hz]
    have hRreal : 0 < (R : Real) := by exact_mod_cast hR
    have hmax : 0 ≤ max 0
        (polynomialCurveOrder nu
          (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := le_max_left _ _
    nlinarith [mul_nonneg (le_of_lt hRreal) hmax]
  · have hlocal :=
      OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact
        c hc v sigma hsigma hv R e hR he hscale E htrdeg x hgen hfibre hnonconst
        N hN f hjet nu hne j
    have hcontactReal :
        (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) =
        (polynomialCurveIdealContact nu x
          (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) := by
      exact_mod_cast hcontact
    rw [hcontactReal]
    exact hlocal
