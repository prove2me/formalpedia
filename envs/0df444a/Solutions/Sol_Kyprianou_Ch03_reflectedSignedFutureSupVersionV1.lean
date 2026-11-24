-- Prove2me | solution 1 for Kyprianou.Ch03.reflectedSignedFutureSupVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:12:12.014803+00:00
-- url     : https://prove2.me/submissions/2c74c473-4f26-444e-8ee3-6d3030bec7b5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_reflectedDenseSupFunctionalV1
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_Kyprianou_Ch01_isCadlag_realScalarMultiple
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (c : ℝ) (r : Omega → NNReal) (t : NNReal) :
    ∃ H : (NNReal → ℝ) → ℝ, Measurable H ∧
      (∀ᵐ w ∂P, H (fun u => X u w) =
        LevyExtrema.SBA.runSup (fun u => c * X u w) t) ∧
      (∀ᵐ w ∂P, H (fun u => X (r w + u) w - X (r w) w) =
        LevyExtrema.SBA.runSup (fun u => c * (X (r w + u) w - X (r w) w)) t) := by
  obtain ⟨H,hH,hEq⟩ := reflectedDenseSupFunctionalV1 c t
  refine ⟨H,hH,?_,?_⟩
  · filter_upwards [hX.cadlag_ae] with w hw
    apply hEq _ (fun u => (hw u).1)
    exact (Kyprianou.Ch01.cadlag_runningSup_bddAbove _
      (Kyprianou.Ch01.isCadlag_realScalarMultiple c _ hw) t).mono
      (by rintro _ ⟨u,hu,rfl⟩; exact ⟨u,hu.2,rfl⟩)
  · filter_upwards [hX.cadlag_ae] with w hw
    apply hEq
    · intro u
      have hc : ContinuousWithinAt (fun v : NNReal => r w + v) (Ici u) u :=
        (continuous_const.add continuous_id).continuousWithinAt
      have hm : MapsTo (fun v : NNReal => r w + v) (Ici u) (Ici (r w + u)) :=
        fun v hv => add_le_add_right hv (r w)
      have hh : ContinuousWithinAt (fun v : NNReal => X (r w+v) w) (Ici u) u :=
        (hw (r w+u)).1.comp hc hm
      exact hh.sub continuousWithinAt_const
    · obtain ⟨M,hM⟩ := Kyprianou.Ch01.cadlag_runningSup_bddAbove _
        (Kyprianou.Ch01.isCadlag_realScalarMultiple c _ hw) (r w+t)
      refine ⟨M-c*X (r w) w, ?_⟩
      rintro _ ⟨u,hu,rfl⟩
      change c * (X (r w+u) w - X (r w) w) ≤ M-c*X (r w) w
      rw [mul_sub]
      exact sub_le_sub_right (hM ⟨r w+u,add_le_add_right hu.2 _,rfl⟩) _
