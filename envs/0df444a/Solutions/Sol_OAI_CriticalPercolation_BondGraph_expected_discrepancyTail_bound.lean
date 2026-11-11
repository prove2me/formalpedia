-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:49.131546+00:00
-- url     : https://prove2.me/submissions/0da29926-39f3-42ee-8c04-d167eb84dce9

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_band_volume_peak
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_band_volume_ratio
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_expected_discrepancy_peakBand_fourth
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_expected_weighted_peakRatio
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_pos

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_GeometricFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped ENNReal

namespace CriticalPercolation

lemma geometric_fourth_bound (I : ℝ≥0∞) (A : ℝ) (hA : 0≤A) (n : ℕ)
    (h : I^4≤ENNReal.ofReal (A/(16:ℝ)^n)) :
    I≤ENNReal.ofReal ((A+1)*(1/2:ℝ)^n) := by
  apply (ENNReal.pow_le_pow_left_iff (by decide : 4≠0)).mp
  rw [←ENNReal.ofReal_pow (by positivity)]
  apply h.trans (ENNReal.ofReal_le_ofReal _)
  have hpow : ((1/2:ℝ)^n)^4 = (1/16:ℝ)^n := by
    rw [←pow_mul,Nat.mul_comm n 4,pow_mul]
    norm_num
  rw [mul_pow,hpow,one_div_pow,mul_one_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsq : A≤(A+1)^2 := by nlinarith
  have ht : 1≤(A+1)^2 := by nlinarith
  nlinarith [sq_nonneg ((A+1)^2-1)]

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.cluster_image (φ : G.Aut) (ω : Set E) (o : V) :
    φ.vertex '' G.cluster ω o = G.cluster (φ.edge '' ω) (φ.vertex o) := by
  ext v
  obtain ⟨w, rfl⟩ := φ.vertex.surjective v
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]
  change (G.openGraph ω).Reachable o w ↔
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex o) (φ.vertex w)
  exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := o) (v := w)).symm

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

omit [Fintype V] in
lemma cluster_eq_of_reachable {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : G.cluster ω u = G.cluster ω v := by
  ext z
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularClusterMass
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

lemma Aut.modularMass_image (φ : G.Aut) (o : V) (S : Set V) :
    G.modularMass (φ.vertex o) (φ.vertex '' S) = G.modularMass o S := by
  unfold modularMass
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro x
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,Aut.stabilizerWeight]

lemma measurable_modularClusterMass [Countable V] [Countable E] (o v : V) :
    Measurable (fun ω : Set E => G.modularMass o (G.cluster ω v)) := by
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (G.measurable_reachable v x).setOf measurable_const

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakClusters
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma clusterPeaks_eq_of_reachable {ω : Set E} {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.clusterPeaks ω x = G.clusterPeaks ω y := by
  ext z
  exact and_congr (⟨fun hz => h.symm.trans hz,fun hz => h.trans hz⟩) Iff.rfl

lemma Aut.clusterPeak_iff (φ : G.Aut) (ω : Set E) (x : V) :
    G.clusterPeak (φ.edge '' ω) (φ.vertex x) ↔ G.clusterPeak ω x := by
  unfold clusterPeak
  constructor
  · intro h z hz
    have hr : (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex x) (φ.vertex z) :=
      (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mpr hz
    simpa only [Aut.stabilizerWeight] using h (φ.vertex z) hr
  · intro h z hz
    obtain ⟨y,rfl⟩ := φ.vertex.surjective z
    rw [Aut.stabilizerWeight]
    exact h y ((SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mp hz)

lemma Aut.clusterPeaks_image (φ : G.Aut) (ω : Set E) (v : V) :
    φ.vertex '' G.clusterPeaks ω v = G.clusterPeaks (φ.edge '' ω) (φ.vertex v) := by
  ext z
  obtain ⟨y,rfl⟩ := φ.vertex.surjective z
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,clusterPeaks,Set.mem_ofPred_eq,
    φ.clusterPeak_iff]
  exact and_congr (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).symm Iff.rfl

lemma measurable_clusterPeak [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeak ω x) := by
  exact .forall (fun z => (G.measurable_reachable x z).imp measurable_const)

lemma measurable_mem_clusterPeaks [Countable V] [Countable E] (v x : V) :
    Measurable (fun ω : Set E => x∈G.clusterPeaks ω v) :=
  (G.measurable_reachable v x).and (G.measurable_clusterPeak x)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakRatioTransport
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma measurable_peakRatioTransport [Countable V] [Countable E] (x y : V) :
    Measurable (fun ω : Set E => G.peakRatioTransport ω x y) := by
  apply Measurable.ite (G.measurable_mem_clusterPeaks x y).setOf _ measurable_const
  apply Measurable.mul (G.measurable_modularClusterMass y x).inv
  apply Measurable.inv
  apply Measurable.of_discrete.comp
  apply measurable_ncard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

lemma peakRatioTransport_aut (φ : G.Aut) (ω : Set E) (x y : V) :
    G.peakRatioTransport (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.peakRatioTransport ω x y := by
  unfold peakRatioTransport
  rw [←φ.cluster_image,φ.modularMass_image,←φ.clusterPeaks_image,
    Set.ncard_image_of_injective _ φ.vertex.injective]
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakReturn
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurable_peakReturn [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.peakReturn ω x) := by
  apply Measurable.ite (G.measurable_clusterPeak x).setOf _ measurable_const
  apply Measurable.inv
  apply (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
  apply measurable_encard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedPeakTransport
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma clusterPeakRatio_eq_of_reachable (ω : Set E) {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.clusterPeakRatio ω x=G.clusterPeakRatio ω y := by
  unfold clusterPeakRatio peakRatioTransport
  simp only [G.cluster_eq_of_reachable h,G.clusterPeaks_eq_of_reachable h]

lemma measurable_clusterPeakRatio [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeakRatio ω x) :=
  Measurable.tsum (fun y => G.measurable_peakRatioTransport x y)

lemma Aut.clusterPeakRatio (φ : G.Aut) (ω : Set E) (x : V) :
    G.clusterPeakRatio (φ.edge '' ω) (φ.vertex x)=G.clusterPeakRatio ω x := by
  unfold CriticalPercolation.BondGraph.clusterPeakRatio
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro y
  exact G.peakRatioTransport_aut φ ω x y

lemma measurable_normalizedClusterVolume [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.normalizedClusterVolume ω x) := by
  unfold normalizedClusterVolume
  exact measurable_const.ite
    (measurableSet_eq_fun (G.measurable_clusterPeakRatio x) measurable_const)
    (G.measurable_clusterPeakRatio x).inv

lemma Aut.normalizedClusterVolume (φ : G.Aut) (ω : Set E) (x : V) :
    G.normalizedClusterVolume (φ.edge '' ω) (φ.vertex x)=G.normalizedClusterVolume ω x := by
  unfold CriticalPercolation.BondGraph.normalizedClusterVolume
  rw [φ.clusterPeakRatio]

lemma normalizedClusterVolume_eq_of_reachable (ω : Set E) {x y : V}
    (h : (G.openGraph ω).Reachable x y) :
    G.normalizedClusterVolume ω x=G.normalizedClusterVolume ω y := by
  unfold normalizedClusterVolume
  rw [G.clusterPeakRatio_eq_of_reachable ω h]

lemma normalizedClusterVolume_mul_ratio_le (ω : Set E) (x : V) :
    G.normalizedClusterVolume ω x*G.clusterPeakRatio ω x≤1 := by
  unfold normalizedClusterVolume
  split_ifs with h
  · simp
  · by_cases ht : G.clusterPeakRatio ω x=∞
    · simp [ht]
    · rw [ENNReal.inv_mul_cancel h ht]

theorem expected_peak_volume_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    (∑ x∈(G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.normalizedClusterVolume ω x*G.peakReturn ω x ∂G.law p) ≤
    (G.orbitRepresentatives hq).roots.card := by
  rw [←G.expected_weighted_peakRatio hc hl hq p G.normalizedClusterVolume
    G.measurable_normalizedClusterVolume (fun φ => φ.normalizedClusterVolume)
    (fun ω _ _ h => G.normalizedClusterVolume_eq_of_reachable ω h)]
  calc _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro x _
        calc _ ≤ ∫⁻ ω, (1 : ℝ≥0∞) ∂G.law p := lintegral_mono (fun ω =>
              G.normalizedClusterVolume_mul_ratio_le ω x)
             _ = 1 := by simp
       _ = _ := by simp

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakVolumeBand
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma measurable_peakVolumeBand [Countable V] [Countable E] (T U : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.peakVolumeBand T U ω x) := by
  unfold peakVolumeBand
  exact (G.measurable_peakReturn x).ite
    ((measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)).inter
      (measurableSet_lt (G.measurable_normalizedClusterVolume x) measurable_const)) measurable_const

lemma peakVolumeBand_mul_le (T U : ℝ≥0∞) (ω : Set E) (x : V) :
    T*G.peakVolumeBand T U ω x ≤ G.normalizedClusterVolume ω x*G.peakReturn ω x := by
  unfold peakVolumeBand
  split_ifs with h
  · gcongr
    exact h.1
  · simp

theorem expected_peakVolumeBand_mul_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (T U : ℝ≥0∞) :
    T*(∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, G.peakVolumeBand T U ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card := by
  calc _ = ∑ x∈(G.orbitRepresentatives hq).roots,
      ∫⁻ ω, T*G.peakVolumeBand T U ω x ∂G.law p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        exact (lintegral_const_mul'' T (G.measurable_peakVolumeBand T U x).aemeasurable).symm
       _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots,
          ∫⁻ ω, G.normalizedClusterVolume ω x*G.peakReturn ω x ∂G.law p := by
        apply Finset.sum_le_sum
        intro x _
        exact lintegral_mono (fun ω => G.peakVolumeBand_mul_le T U ω x)
       _ ≤ _ := G.expected_peak_volume_le hc hl hq p

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularIncidence
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

lemma bondWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (e : E) : G.bondWeight o e = G.stabilizerWeight o a * G.bondWeight a e := by
  unfold bondWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact G.stabilizerWeight_change_base hc hl o a v

lemma Aut.bondWeight (φ : G.Aut) (o : V) (e : E) :
    G.bondWeight (φ.vertex o) (φ.edge e) = G.bondWeight o e := by
  unfold CriticalPercolation.BondGraph.bondWeight
  rw [φ.preserves]
  have himg : (Sym2.map φ.vertex (G.ends e)).toFinset = (G.ends e).toFinset.image φ.vertex := by
    ext v
    simp only [Sym2.mem_toFinset,Sym2.mem_map,Finset.mem_image]
  rw [himg,Finset.sum_image]
  · simp only [Aut.stabilizerWeight]
  · exact fun _ _ _ _ h => φ.vertex.injective h

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurable_weightedDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.weightedDiscrepancy p ω x) := by
  apply Measurable.tsum
  intro e
  unfold weightedIncidenceTerm centeredCoefficient
  apply Measurable.ite
    (Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)).setOf
    _ measurable_const
  exact measurable_const.mul (measurable_const.ite (measurable_set_mem e).setOf measurable_const)

lemma weightedIncidenceTerm_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) (x y : V) (h : (G.openGraph ω).Reachable x y) (e : E) :
    G.weightedIncidenceTerm p ω x e =
      (G.stabilizerWeight x y).toReal*G.weightedIncidenceTerm p ω y e := by
  unfold weightedIncidenceTerm
  rw [G.cluster_eq_of_reachable h,G.bondWeight_change_base hc hl x y,ENNReal.toReal_mul]
  split_ifs <;> ring

lemma weightedDiscrepancy_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) (x y : V) (h : (G.openGraph ω).Reachable x y) :
    G.weightedDiscrepancy p ω x = (G.stabilizerWeight x y).toReal*G.weightedDiscrepancy p ω y := by
  unfold weightedDiscrepancy
  simp only [G.weightedIncidenceTerm_change_base hc hl p ω x y h,tsum_mul_left]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_NormalizedDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma measurable_normalizedAbsoluteDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.normalizedAbsoluteDiscrepancy p ω x) :=
  (G.measurable_weightedDiscrepancy p x).norm.ennreal_ofReal.div
    (G.measurable_modularClusterMass x x)

lemma Aut.weightedDiscrepancy (φ : G.Aut) (p : ℝ) (ω : Set E) (x : V) :
    G.weightedDiscrepancy p (φ.edge '' ω) (φ.vertex x) = G.weightedDiscrepancy p ω x := by
  unfold CriticalPercolation.BondGraph.weightedDiscrepancy
  rw [←φ.edge.tsum_eq]
  apply tsum_congr
  intro e
  unfold weightedIncidenceTerm centeredCoefficient
  rw [←φ.cluster_image]
  have hend (v : V) : φ.vertex v∈G.ends (φ.edge e) ↔ v∈G.ends e := by
    rw [φ.preserves]
    simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]
  have hi : φ.edge e∈G.incidentEdges (φ.vertex '' G.cluster ω x) ↔ e∈G.incidentEdges (G.cluster ω x) := by
    constructor
    · rintro ⟨z,⟨v,hv,rfl⟩,hz⟩
      exact ⟨v,hv,(hend v).mp hz⟩
    · rintro ⟨v,hv,hve⟩
      exact ⟨φ.vertex v,⟨v,hv,rfl⟩,(hend v).mpr hve⟩
  rw [hi]
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,φ.bondWeight]

lemma Aut.normalizedAbsoluteDiscrepancy (φ : G.Aut) (p : ℝ) (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p (φ.edge '' ω) (φ.vertex x) =
      G.normalizedAbsoluteDiscrepancy p ω x := by
  unfold CriticalPercolation.BondGraph.normalizedAbsoluteDiscrepancy
  rw [φ.weightedDiscrepancy,←φ.cluster_image,φ.modularMass_image]

lemma normalizedAbsoluteDiscrepancy_eq_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) {x y : V} (h : (G.openGraph ω).Reachable x y) :
    G.normalizedAbsoluteDiscrepancy p ω x = G.normalizedAbsoluteDiscrepancy p ω y := by
  unfold normalizedAbsoluteDiscrepancy
  rw [G.weightedDiscrepancy_change_base hc hl p ω x y h,abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg,ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (G.stabilizerWeight_ne_top x y),
    G.modularMass_change_base hc hl x y,G.cluster_eq_of_reachable h]
  exact ENNReal.mul_div_mul_left _ _ (G.stabilizerWeight_pos hc hl x y).ne'
    (G.stabilizerWeight_ne_top x y)

lemma measurable_discrepancyVolumeBand [Countable V] [Countable E]
    (p : ℝ) (T U : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.discrepancyVolumeBand p T U ω x) := by
  exact (G.measurable_normalizedAbsoluteDiscrepancy p x).ite
    ((measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)).inter
      (measurableSet_lt (G.measurable_normalizedClusterVolume x) measurable_const)) measurable_const

theorem expected_discrepancyBand_peak [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (T U : ℝ≥0∞) (hT : 0<T) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, G.discrepancyVolumeBand p T U ω x ∂G.law p) =
      ∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω,
        ENNReal.ofReal |G.weightedDiscrepancy p ω x| *G.peakVolumeBand T U ω x ∂G.law p := by
  have ht := G.expected_weighted_peakRatio hc hl hq p
    (fun ω x => G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)
    (fun x => (G.measurable_discrepancyVolumeBand p T U x).mul (G.measurable_normalizedClusterVolume x))
    (fun φ ω x => by
      simp only [discrepancyVolumeBand,φ.normalizedClusterVolume,φ.normalizedAbsoluteDiscrepancy])
    (fun ω x y h => by
      simp only [discrepancyVolumeBand,G.normalizedClusterVolume_eq_of_reachable ω h,
        G.normalizedAbsoluteDiscrepancy_eq_of_reachable hc hl p ω h])
  simpa only [G.band_volume_ratio hc hl p T U hT,G.band_volume_peak hc hl p T U hT] using ht

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_GeometricPeakBand
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma expected_peakBand_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (p : unitInterval) (T U : ℝ) (hT : 0<T)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p) ≤
      ENNReal.ofReal ((G.orbitRepresentatives hq).roots.card/T) := by
  rw [ENNReal.ofReal_div_of_pos hT,ENNReal.ofReal_natCast]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hT).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm]
  apply le_trans _ (G.expected_peakVolumeBand_mul_le hc hl hq p (ENNReal.ofReal T) (ENNReal.ofReal U))
  apply mul_le_mul_right
  exact Finset.single_le_sum (f := fun y => ∫⁻ ω,
    G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω y ∂G.law p)
    (fun _ _ => zero_le) hx

lemma expected_discrepancy_peakBand_geometric (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (n : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, ENNReal.ofReal |G.weightedDiscrepancy p ω x| *
      G.peakVolumeBand (ENNReal.ofReal ((16:ℝ)^n)) (ENNReal.ofReal ((16:ℝ)^(n+1))) ω x ∂G.law p) ≤
      ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
  let C : ℝ := (D*(2*K)^2 : ℕ)
  let N : ℝ := (G.orbitRepresentatives hq).roots.card
  have ht : (0:ℝ)<16^n := by positivity
  have h4 := G.expected_discrepancy_peakBand_fourth hc hl D K hD hK p
    ((16:ℝ)^n) ((16:ℝ)^(n+1)) ht (by positivity) x
  apply geometric_fourth_bound _ (5*(C*16)^2*N^3) (by dsimp [N] <;> positivity) n
  apply h4.trans
  calc
    _ ≤ ENNReal.ofReal (5*(C*(16:ℝ)^(n+1))^2)*
        (ENNReal.ofReal (N/(16:ℝ)^n))^3 := by
          apply mul_le_mul_right
          exact ENNReal.pow_le_pow_left (G.expected_peakBand_le hc hl hq p _ _ ht x hx)
    _ = ENNReal.ofReal ((5*(C*16)^2*N^3)/(16:ℝ)^n) := by
      rw [←ENNReal.ofReal_pow (by dsimp [N] <;> positivity),←ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_succ]
      field_simp
      ring

lemma expected_discrepancyBand_geometric (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (n : ℕ) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω,
      G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^n))
        (ENNReal.ofReal ((16:ℝ)^(n+1))) ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
  rw [G.expected_discrepancyBand_peak hc hl hq p _ _ (ENNReal.ofReal_pos.mpr (by positivity))]
  calc _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots,
      ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
          exact Finset.sum_le_sum (fun x hx => G.expected_discrepancy_peakBand_geometric hc hl hq D K hD hK p n x hx)
       _ = _ := by simp [nsmul_eq_mul]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_DiscrepancyTail
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators Topology

namespace CriticalPercolation

lemma ennreal_geometric_band (v : ℝ≥0∞) (hv : v≠∞) (N : ℕ)
    (hN : ENNReal.ofReal ((16:ℝ)^N)≤v) :
    ∃ m : ℕ, ENNReal.ofReal ((16:ℝ)^(N+m))≤v ∧ v<ENNReal.ofReal ((16:ℝ)^(N+m+1)) := by
  have hNr : (16:ℝ)^N≤v.toReal := (ENNReal.ofReal_le_iff_le_toReal hv).mp hN
  have hone : 1≤v.toReal := (one_le_pow₀ (by norm_num : (1:ℝ)≤16)).trans hNr
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hone (by norm_num : (1:ℝ)<16)
  have hNk : N≤k := by
    by_contra h
    have hkle : k+1≤N := by omega
    have hp : (16:ℝ)^(k+1)≤16^N := pow_le_pow_right₀ (by norm_num) hkle
    exact (not_lt_of_ge hNr) (hk'.trans_le hp)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hNk
  exact ⟨m,ENNReal.ofReal_le_of_le_toReal hk,(ENNReal.lt_ofReal_iff_toReal_lt hv).mpr hk'⟩

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma normalizedClusterVolume_ne_top (ω : Set E) (x : V) : G.normalizedClusterVolume ω x≠∞ := by
  unfold normalizedClusterVolume
  split_ifs with h
  · exact ENNReal.zero_ne_top
  · exact ENNReal.inv_ne_top.mpr h

omit [Countable V] [Countable E] in
lemma discrepancyVolumeTail_le_bands (p : ℝ) (N : ℕ) (ω : Set E) (x : V) :
    G.discrepancyVolumeTail p (ENNReal.ofReal ((16:ℝ)^N)) ω x ≤
      ∑' m : ℕ, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x := by
  unfold discrepancyVolumeTail
  split_ifs with h
  · obtain ⟨m,hm⟩ := ennreal_geometric_band _ (G.normalizedClusterVolume_ne_top ω x) N h
    calc
      _ = G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
          (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x := (ite_eq_left hm).symm
      _ ≤ _ := ENNReal.le_tsum (f := fun index : ℕ =>
        G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+index)))
          (ENNReal.ofReal ((16:ℝ)^(N+index+1))) ω x) m
  · exact zero_le

lemma expected_discrepancyTail_bound_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (N : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, G.discrepancyVolumeTail p (ENNReal.ofReal ((16:ℝ)^N)) ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
          (ENNReal.ofReal (1/2:ℝ))^N*2 := by
  let A : ℝ := 5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1
  let R : ℝ≥0∞ := (G.orbitRepresentatives hq).roots.card
  calc
    _ ≤ ∫⁻ ω, ∑' m : ℕ, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x ∂G.law p :=
      lintegral_mono (fun ω => G.discrepancyVolumeTail_le_bands p N ω x)
    _ = ∑' m : ℕ, ∫⁻ ω, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x ∂G.law p :=
      lintegral_tsum (fun m => (G.measurable_discrepancyVolumeBand p _ _ x).aemeasurable)
    _ ≤ ∑' m : ℕ, R * ENNReal.ofReal (A*(1/2:ℝ)^(N+m)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      exact (Finset.single_le_sum (f := fun y => ∫⁻ ω,
        G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
          (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω y ∂G.law p) (fun _ _ => zero_le) hx).trans
        (G.expected_discrepancyBand_geometric hc hl hq D K hD hK p (N+m))
    _ = _ := by
      have he (m : ℕ) : ENNReal.ofReal (A*(1/2:ℝ)^(N+m)) =
          ENNReal.ofReal A * (ENNReal.ofReal (1/2:ℝ))^N * (ENNReal.ofReal (1/2:ℝ))^m := by
        rw [ENNReal.ofReal_mul (show 0≤A by dsimp [A] <;> positivity),
          ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),pow_add,mul_assoc]
      simp_rw [he,←mul_assoc]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      norm_num [R,A,ENNReal.ofReal_div_of_pos]

end BondGraph
end CriticalPercolation
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.expected_discrepancyTail_bound_oai.{u_1, u_2}
