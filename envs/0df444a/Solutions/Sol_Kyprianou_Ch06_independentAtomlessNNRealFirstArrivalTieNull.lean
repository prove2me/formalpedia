-- Prove2me | solution 1 for Kyprianou.Ch06.independentAtomlessNNRealFirstArrivalTieNull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:11:13.670459+00:00
-- url     : https://prove2.me/submissions/c7eacce9-ea66-4f68-a970-77339939645b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f g : Omega → NNReal) (hf : Measurable f) (hg : Measurable g)
    (hIndep : ProbabilityTheory.IndepFun f g P)
    (hNoAtoms : ∀ x : NNReal, (Measure.map g P) {x} = 0) :
    P {omega | f omega = g omega} = 0 := by
  let diag : Set (NNReal × NNReal) := {p | p.1 = p.2}
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
        (Prod.mk x) ⁻¹' diag = ({x} : Set NNReal) := by
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
