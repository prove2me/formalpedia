-- Prove2me | solution 1 for Kyprianou.Ch04.bvDyadicDeficitZeroAeTimeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:28:48.403185+00:00
-- url     : https://prove2.me/submissions/ed674912-6374-47d5-be45-0156ef9ad449

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_dyadic_zero_slope_path_event_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedPath_ae_event_transfer
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
open Set

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) :
    ∀ᵐ omega ∂P, ∀ᵐ t : Real ∂(volume.restrict (Ici 0)),
      Tendsto (fun n : Nat =>
        (L.drift * ((((1 : NNReal) / 2) ^ n : NNReal) : Real) -
          (L.X (Real.toNNReal t + ((1 : NNReal) / 2) ^ n) omega -
            L.X (Real.toNNReal t) omega)) /
          ((((1 : NNReal) / 2) ^ n : NNReal) : Real))
        atTop (𝓝 (0 : Real)) := by
  letI : IsProbabilityMeasure P := L.isProbability
  let delta : Nat → NNReal := fun n => ((1 : NNReal) / 2) ^ n
  let G : Set (NNReal → Real) := {f | Tendsto
    (fun n => (L.drift * (delta n : Real) - f (delta n)) / (delta n : Real))
    atTop (𝓝 (0 : Real))}
  have hG : MeasurableSet G := bv_dyadic_zero_slope_path_event_measurable_ws01c L.drift delta
  let orig : Omega → NNReal → Real := fun omega t => L.X t omega
  let shift : Real × Omega → NNReal → Real := fun z t =>
    L.X (z.1.toNNReal + t) z.2 - L.X z.1.toNNReal z.2
  have hX := chat04_levy_joint_time_state_measurable L
  have ho : Measurable orig :=
    measurable_pi_lambda _ (fun t => hX.comp (measurable_const.prodMk measurable_id))
  have hs : Measurable shift := by
    apply measurable_pi_lambda
    intro t
    have ht := measurable_real_toNNReal.comp (measurable_fst : Measurable
      (Prod.fst : Real × Omega → Real))
    exact (hX.comp ((ht.add_const t).prodMk measurable_snd)).sub
      (hX.comp (ht.prodMk measurable_snd))
  have hOrig : ∀ᵐ omega ∂P, orig omega ∈ G :=
    bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c L hBV
  have hFor (t : Real) : ∀ᵐ omega ∂P, shift (t, omega) ∈ G := by
    have htime (u : NNReal) : MeasurableSet[F u]
        {omega : Omega | t.toNNReal ≤ u} := by
      by_cases h : t.toNNReal ≤ u <;> simp [h]
    exact levy_finiteStopping_shiftedPath_ae_event_transfer L
      (fun _ : Omega => t.toNNReal) htime (isStoppingTime_const F t.toNNReal)
      ho G hG hOrig
  have hjoint : MeasurableSet {z : Real × Omega | shift z ∈ G} := hs hG
  exact (Measure.ae_ae_comm (μ := volume.restrict (Ici 0)) (ν := P) hjoint).mp
    (ae_of_all _ hFor)
