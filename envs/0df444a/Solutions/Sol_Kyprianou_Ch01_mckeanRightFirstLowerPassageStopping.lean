-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanRightFirstLowerPassageStopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:34:26.607066+00:00
-- url     : https://prove2.me/submissions/5ea1d994-5f55-46fb-a2c4-56a5fc45b074

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_rawNaturalPast_later
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassageEqShiftedNegUpperPublic
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (x barrier : ℝ) :
    IsNaturalRightStoppingTime (fun t ω => x + X t ω)
      (firstLowerPassage X x barrier) := by
  have hfiltration (v : ℝ≥0) :
      naturalSigma (fun t ω => -X t ω) v ≤
        naturalSigma (fun t ω => x + X t ω) v := by
    change
      (⨆ u : ℝ≥0, ⨆ (_hu : u ≤ v),
        MeasurableSpace.comap (fun ω => -X u ω) inferInstance) ≤
      (⨆ u : ℝ≥0, ⨆ (_hu : u ≤ v),
        MeasurableSpace.comap (fun ω => x + X u ω) inferInstance)
    refine iSup_le fun u => iSup_le fun hu => ?_
    have hshift : @Measurable Ω ℝ
        (naturalSigma (fun t ω => x + X t ω) v) inferInstance
        (fun ω => x + X u ω) :=
      Kyprianou.Ch01.naturalSigma_measurable_past
        (fun t ω => x + X t ω) u v hu
    have hneg : @Measurable Ω ℝ
        (naturalSigma (fun t ω => x + X t ω) v) inferInstance
        (fun ω => -X u ω) := by
      have hrepl :
          (fun ω => x - (x + X u ω)) = (fun ω => -X u ω) := by
        funext ω
        ring
      rw [← hrepl]
      exact measurable_const.sub hshift
    exact hneg.comap_le
  intro t
  change @MeasurableSet Ω
    (⨅ v : ℝ≥0, ⨅ (_hv : t < v),
      naturalSigma (fun t ω => x + X t ω) v)
    {ω | firstLowerPassage X x barrier ω ≤ (t : WithTop ℝ≥0)}
  rw [MeasurableSpace.measurableSet_iInf]
  intro v
  rw [MeasurableSpace.measurableSet_iInf]
  intro htv
  rw [Kyprianou.Ch01.firstLowerPassageEqShiftedNegUpperPublic
    X x barrier]
  have hcontneg :
      ∀ ω, Continuous (fun u : ℝ≥0 => -X u ω) :=
    fun ω => (hAllContinuous ω).neg
  exact (hfiltration v) _
    (Kyprianou.Ch01.firstUpperPassage_le_rawNaturalPast_later
      (fun t ω => -X t ω) hcontneg (x - barrier) t v htv)
