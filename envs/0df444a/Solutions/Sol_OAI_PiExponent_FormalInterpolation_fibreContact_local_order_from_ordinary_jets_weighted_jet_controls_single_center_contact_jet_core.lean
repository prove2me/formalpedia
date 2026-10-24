-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:07:39.935071+00:00
-- url     : https://prove2.me/submissions/eeb75d5c-93bf-478e-a113-ae3137ae4d3a

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core_weighted_support_curve_bound
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (N : Nat) (hN : 0 < N)
    (f : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 2 * (sigma : Real)) * (N : Real)) f)
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0)
    (j : Fin K) (C : Real) (hC : 0 ≤ C)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hcontact : ∀ i : Fin m, C ≤ (e i.succ : Real) *
      (polynomialCurveOrder nu
        (x i.succ - algebraMap Complex E (c j i)) : Real)) :
    C * ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := by
  let P := MvPolynomial.aeval
    (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i) f
  have hsupport : ∀ a ∈ P.support,
      ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
        ∑ i : Fin m, (a i : Real) * (v i.succ : Real) := by
    intro a ha
    by_contra hlt
    have hlt' : (∑ i : Fin m, (a i : Real) * (v i.succ : Real)) <
        ((1 + 2 * (sigma : Real)) * (N : Real)) := lt_of_not_ge hlt
    have hzero := hjet j a hlt'
    exact (MvPolynomial.mem_support_iff.mp ha) hzero
  have hmaps : MvPolynomial.aeval (fun i => x i.succ) =
      (MvPolynomial.aeval
        (fun i => x i.succ - algebraMap Complex E (c j i))).comp
        (MvPolynomial.aeval
          (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i)) := by
    ext i
    simp [sub_add_cancel]
  have heval : MvPolynomial.aeval (fun i => x i.succ) f =
      MvPolynomial.aeval
        (fun i => x i.succ - algebraMap Complex E (c j i)) P := by
    simpa [P] using congrArg (fun φ => φ f) hmaps
  exact OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core_weighted_support_curve_bound
    c v sigma hsigma hv R e hR he hscale E x N hN f P hsupport nu
    hne j C hC hchart hcontact heval