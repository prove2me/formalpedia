-- Prove2me | solution 1 for Kyprianou.Ch04.totalIdleMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:28:59.243308+00:00
-- url     : https://prove2.me/submissions/64bbfc83-8892-4e58-a3fe-23f50d55ccc1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
open Set

set_option maxHeartbeats 600000 in
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
    Measurable totalIdle := by
  classical
  intro supX W totalIdle
  have he (t : NNReal) (omega : Omega) : supX t omega = runningSup L t omega := by
    rw [(runningSup_eq_rawSup_nonneg L t omega).1]
    change sSup ((fun s : NNReal => L.X s omega) '' Iic t) =
      sSup (Set.range fun s : Icc (0 : NNReal) t => L.X s.1 omega)
    apply congrArg sSup
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, zero_le, hs⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, s.2.2, rfl⟩
  have hsup : Measurable (fun z : NNReal × Omega => supX z.1 z.2) := by
    simpa only [he] using levy_runningSup_joint_time_path_measurable L
  have hW : Measurable (fun z : NNReal × Omega => W z.1 z.2) :=
    (measurable_const.max hsup).sub (chat04_levy_joint_time_state_measurable L)
  have hReal : Measurable (fun z : Real × Omega => W z.1.toNNReal z.2) :=
    hW.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hInd : Measurable (Function.uncurry
      (fun t : Real => fun omega : Omega =>
        if W t.toNNReal omega = 0 then (1 : ENNReal) else 0)) :=
    Measurable.ite (measurableSet_eq_fun hReal measurable_const)
      measurable_const measurable_const
  exact hInd.lintegral_prod_left
