-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.band_volume_peak
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:41.528944+00:00
-- url     : https://prove2.me/submissions/4ddd1ec1-964c-4aad-9dde-7504841873ee

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_normalizedClusterVolume_eq_at_peak
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_pos

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularClusterMass
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S =
      G.stabilizerWeight o a * G.modularMass a S := by
  unfold modularMass
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  split_ifs with hx
  · exact G.stabilizerWeight_change_base hc hl o a x
  · exact (mul_zero _).symm

lemma modularMass_eq_top_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S = ∞ ↔ G.modularMass a S = ∞ := by
  rw [G.modularMass_change_base hc hl o a S,ENNReal.mul_eq_top]
  simp [G.stabilizerWeight_ne_top o a,(G.stabilizerWeight_pos hc hl o a).ne']

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakRatioTransport
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma one_le_modularClusterMass (ω : Set E) (x : V) :
    1 ≤ G.modularMass x (G.cluster ω x) := by
  have h := ENNReal.le_tsum (f := fun y => if y∈G.cluster ω x then G.stabilizerWeight x y else 0) x
  have hx : x∈G.cluster ω x := SimpleGraph.Reachable.refl x
  simpa only [modularMass,ite_eq_left hx,G.stabilizerWeight_self] using h

lemma clusterPeakRatio_eq_zero_of_heavy (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hh : G.modularMass x (G.cluster ω x) = ∞) :
    G.clusterPeakRatio ω x = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro y
  unfold peakRatioTransport
  split_ifs
  · have hy : G.modularMass y (G.cluster ω x) = ∞ :=
      (G.modularMass_eq_top_change_base hc hl x y _).mp hh
    simp [hy]
  · rfl

end CriticalPercolation.BondGraph
end
end

end OAI
end

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

lemma band_volume_peak_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) :
    (G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)*G.peakReturn ω x =
      ENNReal.ofReal |G.weightedDiscrepancy p ω x| *G.peakVolumeBand T U ω x := by
  by_cases h : T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U
  · by_cases hp : G.clusterPeak ω x
    · have hm : G.modularMass x (G.cluster ω x)≠∞ := by
        intro he
        have hz := G.clusterPeakRatio_eq_zero_of_heavy hc hl ω x he
        have hv : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,hz]
        rw [hv] at h
        exact (not_le.mpr hT) h.1
      rw [discrepancyVolumeBand,peakVolumeBand,ite_eq_left h,ite_eq_left h,
        G.normalizedClusterVolume_eq_at_peak hc hl ω x hp hm,normalizedAbsoluteDiscrepancy,
        ENNReal.div_mul_cancel (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm]
    · simp only [discrepancyVolumeBand,peakVolumeBand,ite_eq_left h,peakReturn,ite_eq_right hp,mul_zero]
  · simp only [discrepancyVolumeBand,peakVolumeBand,ite_eq_right h,zero_mul,mul_zero]

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.band_volume_peak_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.band_volume_peak_oai.{u_1, u_2}
