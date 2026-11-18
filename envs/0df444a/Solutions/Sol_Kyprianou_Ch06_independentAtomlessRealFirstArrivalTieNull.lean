-- Prove2me | solution 1 for Kyprianou.Ch06.independentAtomlessRealFirstArrivalTieNull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:31:41.802018+00:00
-- url     : https://prove2.me/submissions/18c4e374-f3a7-4f5f-8226-3827ad4611bd

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f g : Omega → Real) (hf : Measurable f) (hg : Measurable g)
    (hIndep : ProbabilityTheory.IndepFun f g P)
    (hNoAtoms : ∀ x : Real, (Measure.map g P) {x} = 0) :
    P {omega | f omega = g omega} = 0 := by
  let diag : Set (Real × Real) := {p | p.1 = p.2}
  have hDiag : MeasurableSet diag := by
    exact measurableSet_eq_fun measurable_fst measurable_snd
  have hJoint :
      Measure.map (fun omega => (f omega, g omega)) P =
        (Measure.map f P).prod (Measure.map g P) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hf.aemeasurable hg.aemeasurable).mp hIndep
  have hZero :
      (Measure.map f P).prod (Measure.map g P) diag = 0 := by
    apply Measure.measure_prod_null_of_ae_null hDiag
    apply Filter.Eventually.of_forall
    intro x
    have hSection :
        (Prod.mk x) ⁻¹' diag = ({x} : Set Real) := by
      ext y
      simp [diag, eq_comm]
    change (Measure.map g P) ((Prod.mk x) ⁻¹' diag) = 0
    rw [hSection]
    exact hNoAtoms x
  have hMap :
      P {omega | f omega = g omega} =
        (Measure.map (fun omega => (f omega, g omega)) P) diag := by
    rw [Measure.map_apply (hf.prodMk hg) hDiag]
    rfl
  rw [hMap, hJoint]
  exact hZero
