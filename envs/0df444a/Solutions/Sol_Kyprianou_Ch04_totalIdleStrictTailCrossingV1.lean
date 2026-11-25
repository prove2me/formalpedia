-- Prove2me | solution 1 for Kyprianou.Ch04.totalIdleStrictTailCrossingV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:12:35.828298+00:00
-- url     : https://prove2.me/submissions/236341f9-d8cf-48d7-babd-cafe4e8c4f1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorFiniteIdentityV1
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorIncrementBoundsV1
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_Kyprianou_Ch04_idleOccupationNatHorizonSupV1
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorCrossingFromFiniteV1
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Set


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (w : Real) (hw : 0 ≤ w) :
    let supX : NNReal → Omega → Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
    let W : NNReal → Omega → Real := fun t omega =>
      max w (supX t omega) - L.X t omega
    let totalIdle : Omega → ENNReal := fun omega =>
      ∫⁻ t in Set.Ici (0 : Real),
        (if W (Real.toNNReal t) omega = 0 then (1 : ENNReal) else 0) ∂volume
    Measurable totalIdle ∧
    (∀ᵐ omega ∂P, ∀ x : Real, 0 ≤ x →
      (ENNReal.ofReal x < totalIdle omega ↔
        ∃ t : NNReal, w + L.drift * x < L.X t omega)) := by
  classical
  intro supX W totalIdle
  refine ⟨Kyprianou.Ch04.totalIdleMeasurableV1 P F L hBV hd w hw, ?_⟩
  filter_upwards [Kyprianou.Ch04.idleRegulatorFiniteIdentityV1 P F L hBV hd w hw,
    bv_actual_levy_residual_ae_monotone_all_times L hBV] with omega hfin hm
  let f : NNReal → Real := fun t => L.X t omega
  let R : NNReal → Real := fun t => max w (supX t omega)
  have hf (s t : NNReal) (hst : s ≤ t) :
      f t - f s ≤ L.drift * ((t : Real) - (s : Real)) := by
    have h := hm hst
    dsimp [f] at *
    linarith
  obtain ⟨_, _, _, hLip⟩ :=
    Kyprianou.Ch04.idleRegulatorIncrementBoundsV1 f L.drift w hd hw (L.X_zero omega) hf
  let A : Set Real := {t | W t.toNNReal omega = 0}
  have hR : Measurable (fun t : Real => R t.toNNReal) :=
    hLip.continuous.measurable.comp measurable_real_toNNReal
  have hX : Measurable (fun t : Real => f t.toNNReal) :=
    (chat04_levy_joint_time_state_measurable L).comp
      (measurable_real_toNNReal.prodMk measurable_const)
  have hA : MeasurableSet A := measurableSet_eq_fun (hR.sub hX) measurable_const
  let I : Nat → ENNReal := fun n =>
    ∫⁻ t in Icc (0 : Real) (n : Real),
      (if W t.toNNReal omega = 0 then (1 : ENNReal) else 0) ∂volume
  have hT : totalIdle omega = ⨆ n, I n := by
    exact Kyprianou.Ch04.idleOccupationNatHorizonSupV1 A hA
  have hI (n : Nat) : ENNReal.ofReal (max w (sSup (f '' Iic (n : NNReal))) - w) =
      ENNReal.ofReal L.drift * I n := by
    exact hfin (n : NNReal)
  rw [hT]
  exact Kyprianou.Ch04.idleRegulatorCrossingFromFiniteV1 f L.drift w hd hw
    (L.X_zero omega) hf I hI
