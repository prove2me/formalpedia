-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_jet_contact_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T09:15:54.584386+00:00
-- url     : https://prove2.me/submissions/1472e3ff-a85e-4b81-b18c-ddaebce3be78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_centers_contact_is_single_center
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_jet_bound_controls_center_contact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (v : Fin (m + 1) → Rat) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (H : Real) (G : MvPolynomial (Fin (m + 1)) Complex)
    (hjet : logarithmicJetBound c v H G)
    (nu : PolynomialCurvePlace E)
    (hcontact : 0 < (polynomialCurveIdealContact nu x
      (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))
    (hne : MvPolynomial.aeval x G ≠ 0) :
    H * (polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) ≤
      (R : Real) * (polynomialCurveOrder nu (MvPolynomial.aeval x G) : Real) := by
  obtain ⟨j, hjpos, hj_eq⟩ :=
    logarithmic_centers_contact_is_single_center c hc e E nu x hcontact
  have hlocal := logarithmic_jet_bound_controls_center_contact
    c hc hm hK v hv R e hR he hscale E htrdeg x hgen H G hjet nu j hjpos hne
  rw [hj_eq] at hlocal
  exact hlocal