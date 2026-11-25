-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_martingale_of_event_increment_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:15:42.213961+00:00
-- url     : https://prove2.me/submissions/e817bfce-8589-461a-8a61-c89c778195d3

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → Real) (hAdapt : StronglyAdapted F M)
    (hInt : ∀ t, Integrable (M t) P)
    (hZero : ∀ a b : NNReal, a ≤ b → ∀ A : Set Omega, MeasurableSet[F a] A →
      (∫ w in A, (M a w - M b w) ∂P) = 0) :
    Martingale M F P  := by
  refine ⟨hAdapt, ?_⟩
  intro a b hab
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le a) (hInt b)
    (fun A _ _ => (hInt a).integrableOn) _ (hAdapt a).aestronglyMeasurable
  intro A hA _
  have h := hZero a b hab A hA
  rw [integral_sub (hInt a).integrableOn (hInt b).integrableOn] at h
  exact sub_eq_zero.mp h
