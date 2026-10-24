-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_generator_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:59:18.786922+00:00
-- url     : https://prove2.me/submissions/7a2ba690-1ba4-4f5c-bd12-a51b0fbb885b

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveIdealContact_le_order_of_mem_nonzero_eval
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCoordinate_power_order_on_fibre
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.FieldTheory.IsAlgClosed.Basic

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (nu : PolynomialCurvePlace E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (j : Fin K) :
    ∀ i : Fin m,
      (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) ≤
        (e i.succ : Real) *
          (polynomialCurveOrder nu
            (x i.succ - algebraMap Complex E (c j i)) : Real) := by
  intro i
  let f := (logarithmicCoordinate (c j) (fun _ => e 0) i.succ) ^ e i.succ
  have hmem : f ∈ logarithmicCenterIdeal (c j) (fun _ => e 0) e := by
    dsimp [f, logarithmicCenterIdeal]
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  have hdata := logarithmicCoordinate_power_order_on_fibre
    (K := K) (c j) e E x hfibre hnonconst nu i
  have hcontact := polynomialCurveIdealContact_le_order_of_mem_nonzero_eval
    nu x (logarithmicCenterIdeal (c j) (fun _ => e 0) e) f hchart hmem hdata.1
  rw [hdata.2] at hcontact
  exact hcontact
