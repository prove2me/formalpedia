-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:51:51.709727+00:00
-- url     : https://prove2.me/submissions/cbdb5d72-8096-4b77-b2ee-d70589a2b1d1

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_generator_bound

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
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0)
    (j : Fin K) :
    ((polynomialCurveIdealContact nu x
      (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) *
      ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := by
  by_cases hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
  · exact fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core
      (c := c) (v := v) (sigma := sigma) (hsigma := hsigma) (hv := hv)
      (R := R) (e := e) (hR := hR) (he := he) (hscale := hscale)
      (E := E) (x := x) (N := N) (hN := hN)
      (f := f) (hjet := hjet) (nu := nu) (hne := hne) (j := j)
      (C := (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real))
      (hC := Nat.cast_nonneg _)
      (hchart := hchart)
      (hcontact := by
        intro i
        exact fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_generator_bound
          (c := c) (e := e) (E := E) (x := x) (hfibre := hfibre)
          (hnonconst := hnonconst) (nu := nu) (hchart := hchart) (j := j) i)
  · have hcontact0 : polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) = 0 := by
      simp [polynomialCurveIdealContact, hchart]
    rw [hcontact0]
    have hR0 : 0 ≤ (R : Real) := by exact_mod_cast (le_of_lt hR)
    have horder0 : 0 ≤ max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) :=
      le_max_left _ _
    simpa using (mul_nonneg hR0 horder0)