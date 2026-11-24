-- Prove2me | solution 1 for Kyprianou.Ch03.reflectedSignedAdaptedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:03:31.820833+00:00
-- url     : https://prove2.me/submissions/bb7987bf-a231-4137-b6ef-e48aee2dd135

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted_of_adapted
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_Kyprianou_Ch01_isCadlag_realScalarMultiple
import Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAEModV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalCoordinateAdaptedV1
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (c y : ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F) :
    Adapted F (reflectedSup (fun u v => c * X u v) y) := by
  classical
  let g (u : NNReal) (w : Omega) := c * X u w
  have ha : Adapted F g := fun u => measurable_const.mul
    (completedNaturalCoordinateAdaptedV1 P X F hNatural u)
  obtain ⟨D,hD,hDense⟩ := TopologicalSpace.exists_countable_dense (α := NNReal)
  let S := insert (0 : NNReal) D
  have hS : S.Countable := hD.insert _
  have hd : Dense S := hDense.mono (Set.subset_insert _ _)
  have hCount := AvramDividend.Classical.countable_pastSup_adapted_of_adapted g ha S hS
  intro t B hB
  let U (w : Omega) := max y (max
    (⨆ u : {u : NNReal // u ∈ S ∧ u ≤ t}, g u.1 w) (g t w)) - g t w
  have hUm : Measurable[F t] U :=
    (measurable_const.max ((hCount t).max (ha t))).sub (ha t)
  apply completedNaturalMeasurableAEModV1 P F X hNatural t _ (U ⁻¹' B) (hUm hB)
  filter_upwards [hX.cadlag_ae] with w hw
  have hc := Kyprianou.Ch01.isCadlag_realScalarMultiple c (fun u => X u w) hw
  have hb : BddAbove (Set.range (fun u : Set.Icc (0 : NNReal) t => g u.1 w)) := by
    apply (Kyprianou.Ch01.cadlag_runningSup_bddAbove _ hc t).mono
    rintro _ ⟨u,rfl⟩
    exact ⟨u.1,u.2.2,rfl⟩
  have hrepr := AvramDividend.Classical.dense_timeSup_with_endpoint
    (fun u => g u w) (fun u => (hc u).1) S hd (by simp [S]) t hb
  have hr : Set.range (fun u : Set.Icc (0 : NNReal) t => g u.1 w) =
      (fun u => g u w) '' Set.Icc 0 t := by
    ext z
    exact ⟨fun ⟨u,hu⟩ => ⟨u.1,u.2,hu⟩, fun ⟨u,hu,hz⟩ => ⟨⟨u,hu⟩,hz⟩⟩
  change sSup _ = _ at hrepr
  rw [hr] at hrepr
  simp only [Set.mem_preimage, U, reflectedSup, LevyExtrema.SBA.runSup, ← hrepr]
  rfl
