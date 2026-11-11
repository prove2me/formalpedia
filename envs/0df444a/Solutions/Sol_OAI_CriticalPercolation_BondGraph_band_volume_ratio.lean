-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.band_volume_ratio
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:21.180696+00:00
-- url     : https://prove2.me/submissions/84ef59ce-773b-4b9a-8f5f-73863c7d4de0

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_clusterPeakRatio_le_one

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_NormalizedDiscrepancy
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma band_volume_ratio_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) :
    (G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)*G.clusterPeakRatio ω x =
      G.discrepancyVolumeBand p T U ω x := by
  unfold discrepancyVolumeBand
  split_ifs with h
  · have hne : G.clusterPeakRatio ω x≠0 := by
      intro he
      have hz : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,he]
      rw [hz] at h
      exact (not_le.mpr hT) h.1
    rw [normalizedClusterVolume,ite_eq_right hne,mul_assoc,
      ENNReal.inv_mul_cancel hne (ne_top_of_le_ne_top ENNReal.one_ne_top (G.clusterPeakRatio_le_one hc hl ω x)),mul_one]
  · simp

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.band_volume_ratio_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.band_volume_ratio_oai.{u_1, u_2}
