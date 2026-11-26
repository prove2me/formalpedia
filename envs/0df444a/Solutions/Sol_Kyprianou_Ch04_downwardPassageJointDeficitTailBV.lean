-- Prove2me | solution 1 for Kyprianou.Ch04.downwardPassageJointDeficitTailBV
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:24:57.929798+00:00
-- url     : https://prove2.me/submissions/4ccca7e5-b1ce-41c0-9bc5-74ab7d82f264

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_deficit_law_equal
import Theorems.Thm_Kyprianou_Ch04_cor412_passage_position_meas
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_passage_meas
import Theorems.Thm_Kyprianou_Ch04_cor412_tail_law_eval
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Joint finite downward-passage probability and deficit distribution. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (hMeanPositive : 0 < derivWithin L.ψ (Set.Ici (0 : Real)) 0) :
    let tau : Omega → WithTop NNReal := fun omega =>
      Kyprianou.Ch03.firstHittingTime L.X (Set.Iio 0) omega
    ∀ (finiteTime : Omega → NNReal),
      (∀ omega : Omega, tau omega ≠ ⊤ →
        tau omega = (finiteTime omega : WithTop NNReal)) →
      ∀ x : Real, 0 ≤ x →
        let ruinAndDeficit : Set Omega :=
          {omega : Omega |
            tau omega ≠ ⊤ ∧
              -(L.X (finiteTime omega) omega) ≤ x}
        let integratedTail : Real :=
          ∫ y in Set.Icc (0 : Real) x,
            (L.ν (Set.Iio (-y))).toReal ∂volume
        (P ruinAndDeficit).toReal =
          (1 / L.drift) * integratedTail := by
  classical
  intro tau finiteTime hfin x hx A D
  letI : IsProbabilityMeasure P := L.isProbability
  let B : Set Omega := {w | tau w ≠ ⊤}
  let f : Omega → ℝ := fun w => L.X (finiteTime w) w
  let κ := (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun y : ℝ => ENNReal.ofReal (1/L.drift) * L.ν (Iio (-y)))
  let μ := (P.restrict B).map f
  have hB : MeasurableSet B := Kyprianou.Ch04.cor412_finite_passage_meas L
  have hf : AEMeasurable f (P.restrict B) :=
    Kyprianou.Ch04.cor412_passage_position_meas L finiteTime hfin
  have he : μ = κ.map (fun y => -y) :=
    Kyprianou.Ch04.cor412_deficit_law_equal L hBV hd hMeanPositive finiteTime hfin
  have hpre : f ⁻¹' Ici (-x) ∩ B = A := by
    ext w
    change (-x ≤ L.X (finiteTime w) w ∧ tau w ≠ ⊤) ↔
      (tau w ≠ ⊤ ∧ -L.X (finiteTime w) w ≤ x)
    rw [and_comm, neg_le]
  have hmass : μ (Ici (-x)) = P A := by
    change (P.restrict B).map f (Ici (-x)) = _
    rw [Measure.map_apply_of_aemeasurable hf measurableSet_Ici, Measure.restrict_apply' hB, hpre]
  have hκfin : κ (Iic x) ≠ ⊤ := by
    have hpre' : (fun y : ℝ => -y) ⁻¹' Ici (-x) = Iic x := by ext y; simp
    have hmap : κ.map (fun y => -y) (Ici (-x)) = κ (Iic x) := by
      rw [Measure.map_apply (by fun_prop) measurableSet_Ici, hpre']
    rw [← hmap, ← he, hmass]
    exact measure_ne_top _ _
  rw [← hmass, he]
  exact Kyprianou.Ch04.cor412_tail_law_eval L.ν L.drift x hd hx hκfin
