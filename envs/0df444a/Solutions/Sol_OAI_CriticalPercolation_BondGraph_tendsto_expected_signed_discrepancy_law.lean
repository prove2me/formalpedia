-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:23:11.528745+00:00
-- url     : https://prove2.me/submissions/fdbe2df0-7e66-41bb-a079-22131ce74d15

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_tilted_massTransport_ennreal
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_bondWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_clusterPeakRatio_le_one
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_clusterPeakRatio_ne_zero_of_mass_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_expected_discrepancyTail_bound
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_heavyRestrictedPeakTransport_incoming_ae
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_tendsto_expected_heavy_peakReturn
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_weighted_incidence_le

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BernoulliProduct

variable {E : Type*}

lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

lemma mem_cluster_finite_witness {ω : Set E} {v w : V} (h : w ∈ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v := by
  classical
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp h
  clear h
  induction hr with
  | refl => exact ⟨∅, Set.finite_empty, Set.empty_subset _, .refl _⟩
  | @tail u w hr huw ih =>
      obtain ⟨s, hs, hsω, hvs⟩ := ih
      obtain ⟨⟨e, heω, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      refine ⟨insert e s, hs.insert e, Set.insert_subset heω hsω, ?_⟩
      have hvu : (G.openGraph (insert e s)).Reachable v u :=
        hvs.mono (G.openGraph_mono (Set.subset_insert _ _))
      apply hvu.trans
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, Set.mem_insert _ _, heq⟩, hne⟩

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

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

lemma one_le_modularClusterMass (ω : Set E) (x : V) :
    1 ≤ G.modularMass x (G.cluster ω x) := by
  have h := ENNReal.le_tsum (f := fun y => if y∈G.cluster ω x then G.stabilizerWeight x y else 0) x
  have hx : x∈G.cluster ω x := SimpleGraph.Reachable.refl x
  simpa only [modularMass,ite_eq_left hx,G.stabilizerWeight_self] using h

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

lemma eventually_cluster_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) {x y : V} (hy : y∈G.cluster ω x) :
    ∀ᶠ n in atTop, y∈G.cluster (a n) x := by
  obtain ⟨S,hS,hSω,hSy⟩ := G.mem_cluster_finite_witness hy
  have h : ∀ e∈S, ∀ᶠ n in atTop, e∈a n := by
    intro e he
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hu ▸ hSω he)
    exact eventually_atTop.mpr ⟨n,fun m hm => ha hm hn⟩
  filter_upwards [(Filter.eventually_all_finite hS).mpr h] with n hn
  exact G.cluster_mono hn x hSy

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedPeakTransport
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

lemma measurable_clusterPeakRatio [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeakRatio ω x) :=
  Measurable.tsum (fun y => G.measurable_peakRatioTransport x y)

lemma measurable_normalizedClusterVolume [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.normalizedClusterVolume ω x) := by
  unfold normalizedClusterVolume
  exact measurable_const.ite
    (measurableSet_eq_fun (G.measurable_clusterPeakRatio x) measurable_const)
    (G.measurable_clusterPeakRatio x).inv

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma abs_centeredCoefficient_le_one (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (e : E) :
    |centeredCoefficient p ω e|≤1 := by
  unfold centeredCoefficient
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [hp.1,hp.2]

lemma norm_weightedIncidenceTerm_le (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (x : V) (e : E) :
    ‖G.weightedIncidenceTerm p ω x e‖ ≤
      (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
  unfold weightedIncidenceTerm
  split_ifs
  · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_centeredCoefficient_le_one p hp ω e)
  · simp

lemma summable_weightedIncidence_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (ω : Set E) (x : V)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Summable (fun e => (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal) := by
  apply ENNReal.summable_toReal
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
    (G.weighted_incidence_le hc hl D K hD hK x _)

lemma abs_weightedDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1)
    (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    |G.weightedDiscrepancy p ω x| ≤ (D*(2*K) : ℕ)*(G.modularMass x (G.cluster ω x)).toReal := by
  have hs := G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm
  calc
    _ ≤ ∑' e, (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal :=
      tsum_of_norm_bounded hs.hasSum (G.norm_weightedIncidenceTerm_le p hp ω x)
    _ = (∑' e : E, if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro e
      split_ifs
      · exact G.bondWeight_ne_top x e
      · exact ENNReal.zero_ne_top
    _ ≤ ((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
        (G.weighted_incidence_le hc hl D K hD hK x _)
    _ = _ := by rw [ENNReal.toReal_mul,ENNReal.toReal_natCast]

lemma measurable_weightedDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.weightedDiscrepancy p ω x) := by
  apply Measurable.tsum
  intro e
  unfold weightedIncidenceTerm centeredCoefficient
  apply Measurable.ite
    (Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)).setOf
    _ measurable_const
  exact measurable_const.mul (measurable_const.ite (measurable_set_mem e).setOf measurable_const)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_NormalizedDiscrepancy
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

lemma measurable_normalizedAbsoluteDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.normalizedAbsoluteDiscrepancy p ω x) :=
  (G.measurable_weightedDiscrepancy p x).norm.ennreal_ofReal.div
    (G.measurable_modularClusterMass x x)

lemma normalizedAbsoluteDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p ω x ≤ (D*(2*K) : ℕ) := by
  unfold normalizedAbsoluteDiscrepancy
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [hm]
  · apply (ENNReal.div_le_iff (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm).mpr
    calc _ ≤ ENNReal.ofReal ((D*(2*K) : ℕ)*(G.modularMass x (G.cluster ω x)).toReal) :=
          ENNReal.ofReal_le_ofReal (G.abs_weightedDiscrepancy_le hc hl D K hD hK p hp ω x hm)
         _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_toReal hm]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_DiscrepancyTail
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma measurable_discrepancyVolumeTail (p : ℝ) (T : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.discrepancyVolumeTail p T ω x) :=
  (G.measurable_normalizedAbsoluteDiscrepancy p x).ite
    (measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)) measurable_const

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_MonotoneBernoulli
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

namespace CriticalPercolation.BernoulliProduct

lemma uniform01_map_threshold (p : unitInterval) :
    Priority.uniform01.map (fun t : ℝ => t < p) = bitMeasure p := by
  have hm : Measurable (fun t : ℝ => t < p) := (measurable_id.lt measurable_const)
  have ht : Priority.uniform01 {t : ℝ | t < p} = ENNReal.ofReal p := by
    rw [Priority.uniform01,Measure.restrict_apply hm.setOf]
    have he : {t : ℝ | t < p} ∩ Icc 0 1 = Ico (0 : ℝ) (p : ℝ) := by
      ext t
      simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_Icc,Set.mem_Ico]
      exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,h.2.le.trans p.property.2⟩⟩
    rw [he,Real.volume_Ico,sub_zero]
  have htrue : (Priority.uniform01.map (fun t : ℝ => t < p)) {True} = bitMeasure p {True} := by
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun t : ℝ => t < p) ⁻¹' {True} = {t : ℝ | t < p} := by ext t; simp
    rw [he,ht]
    simp [bitMeasure,ENNReal.coe_nnreal_eq]
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b=True := propext (iff_true_intro hb)
    simpa only [he] using htrue
  · have he : b=False := propext (iff_false_intro hb)
    rw [he]
    have hcompl : ({True} : Set Prop)ᶜ = {False} := by ext a; simp
    rw [←hcompl,measure_compl (measurableSet_singleton _) (measure_ne_top _ _),
      measure_compl (measurableSet_singleton _) (measure_ne_top _ _),htrue,
      Measure.map_apply hm MeasurableSet.univ]
    simp

variable {E : Type*}

lemma measurable_atParameter (p : unitInterval) : Measurable (atParameter (E := E) p) :=
  Measurable.of_eval (fun edge => (measurable_pi_apply edge).lt measurable_const)

lemma markLaw_map_atParameter (p : unitInterval) :
    (markLaw (E := E)).map (atParameter p) = law (fun _ => p) := by
  have he : atParameter (E := E) p = MeasurableEquiv.setOfPred ∘ (fun u : E → ℝ => fun e => u e < p) := rfl
  rw [he,←Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    markLaw,Measure.infinitePi_map_pi (fun _ : E => Priority.uniform01)
      (f := fun _ : E => fun t : ℝ => t < (p : ℝ))
      (fun _ => measurable_id.lt measurable_const)]
  simp only [uniform01_map_threshold,law]

lemma atParameter_mono (u : E → ℝ) : Monotone (fun p : unitInterval => atParameter p u) :=
  fun _ _ hp _ he => (show _ < (_ : ℝ) from he).trans_le hp

lemma atParameter_iUnion (p : unitInterval) (q : ℕ → unitInterval)
    (hqp : ∀ n, q n ≤ p) (hq : Tendsto q atTop (𝓝 p)) (u : E → ℝ) :
    (⋃ n, atParameter (q n) u) = atParameter p u := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun n => atParameter_mono u (hqp n))
  · intro e he
    have he' : u e < (p : ℝ) := he
    have hq' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (p : ℝ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp hq
    obtain ⟨n,hn⟩ := (hq'.eventually (lt_mem_nhds he')).exists
    exact Set.mem_iUnion.mpr ⟨n,hn⟩

lemma measurable_reindexMarks (e : E ≃ E) : Measurable (reindexMarks e) :=
  Measurable.of_eval (fun edge => measurable_pi_apply (e.symm edge))

lemma markLaw_map_reindex (e : E ≃ E) :
    (markLaw (E := E)).map (reindexMarks e) = markLaw := by
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : E => ℝ) e)) = reindexMarks e := by
    funext u x
    obtain ⟨y,rfl⟩ := e.surjective x
    simp [MeasurableEquiv.piCongrLeft_apply_apply,reindexMarks]
  rw [←he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : E => Priority.uniform01) e

lemma atParameter_reindex (e : E ≃ E) (p : unitInterval) (u : E → ℝ) :
    atParameter p (reindexMarks e u) = e '' atParameter p u := by
  ext x
  obtain ⟨y,rfl⟩ := e.surjective x
  simp [atParameter,reindexMarks]

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_MarkedTiltedTransport
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
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma expected_mark_transport_aut
    (F : (E → ℝ) → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun u => F u x y))
    (ha : ∀ (φ : G.Aut) u x y,
      F (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) = F u x y)
    (φ : G.Aut) (x y : V) :
    (∫⁻ u, F u (φ.vertex x) (φ.vertex y) ∂markLaw) = ∫⁻ u, F u x y ∂markLaw := by
  conv_lhs => rw [←markLaw_map_reindex φ.edge]
  rw [lintegral_map (hm _ _) (measurable_reindexMarks φ.edge)]
  simp only [ha]

omit [Countable E] in
lemma OrbitRepresentatives.mark_tilted_transport (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : (E → ℝ) → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun u => F u x y))
    (ha : ∀ (φ : G.Aut) u x y,
      F (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) = F u x y) :
    (∑ x ∈ R.roots, ∫⁻ u, ∑' y, F u x y ∂markLaw) =
      ∑ y ∈ R.roots, ∫⁻ u, ∑' x, F u x y * G.stabilizerWeight y x ∂markLaw := by
  simp_rw [lintegral_tsum (fun y => (hm _ y).aemeasurable),
    lintegral_tsum (fun x => ((hm x _).mul_const _).aemeasurable),
    lintegral_mul_const _ (hm _ _)]
  exact OrbitRepresentatives.tilted_massTransport_ennreal G R hc hl _
    (G.expected_mark_transport_aut F hm ha)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyThinning
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
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_heavyFlag (p : unitInterval) (x : V) :
    Measurable (fun u => G.heavyFlag p u x) :=
  ((G.measurable_modularClusterMass x x).comp (measurable_atParameter p)).eq_const ∞

omit [Countable V] [Countable E] in
lemma heavyFlag_aut (φ : G.Aut) (p : unitInterval) (u : E → ℝ) (x : V) :
    G.heavyFlag p (reindexMarks φ.edge u) (φ.vertex x) ↔ G.heavyFlag p u x := by
  unfold heavyFlag
  rw [atParameter_reindex,←φ.cluster_image,φ.modularMass_image]

lemma measurable_heavyRestrictedPeakTransport (p q : unitInterval) (x y : V) :
    Measurable (fun u => G.heavyRestrictedPeakTransport p q u x y) :=
  ((G.measurable_peakRatioTransport x y).comp (measurable_atParameter q)).ite
    (G.measurable_heavyFlag p x).setOf measurable_const

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_aut (p q : unitInterval) (φ : G.Aut)
    (u : E → ℝ) (x y : V) :
    G.heavyRestrictedPeakTransport p q (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) =
    G.heavyRestrictedPeakTransport p q u x y := by
  simp only [heavyRestrictedPeakTransport,G.heavyFlag_aut,atParameter_reindex,G.peakRatioTransport_aut]

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_out (p q : unitInterval) (u : E → ℝ) (x : V) :
    (∑' y, G.heavyRestrictedPeakTransport p q u x y) =
    if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 := by
  by_cases h : G.heavyFlag p u x <;> simp only [heavyRestrictedPeakTransport,h,ite_true, if_true,ite_false, if_false,
    clusterPeakRatio,tsum_zero]

lemma expected_heavy_clusterPeakRatio
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    {p q : unitInterval} (hqp : q≤p) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 ∂markLaw) =
    ∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.peakReturn (atParameter q u) x else 0 ∂markLaw := by
  simp_rw [←G.heavyRestrictedPeakTransport_out]
  rw [OrbitRepresentatives.mark_tilted_transport G (G.orbitRepresentatives hq) hc hl
    (G.heavyRestrictedPeakTransport p q) (G.measurable_heavyRestrictedPeakTransport p q)
    (G.heavyRestrictedPeakTransport_aut p q)]
  apply Finset.sum_congr rfl
  intro x _
  exact lintegral_congr_ae (G.heavyRestrictedPeakTransport_incoming_ae hc hl hq hqp x)

theorem tendsto_sum_expected_heavy_clusterPeakRatio
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => ∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter (q n) u) x else 0 ∂markLaw)
      atTop (𝓝 0) := by
  simp_rw [G.expected_heavy_clusterPeakRatio hc hl hq (hqp _)]
  have ht := tendsto_finsetSum (G.orbitRepresentatives hq).roots
    (fun x _ => G.tendsto_expected_heavy_peakReturn hc hl hq p q hmono hqp hlim x)
  simpa only [Finset.sum_const_zero] using ht

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyDiscrepancy
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
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation

lemma ennreal_tendsto_zero_of_uniform_tail (f g : ℕ → ℝ≥0∞) (c b : ℕ → ℝ≥0∞)
    (hc : ∀ N, c N≠∞) (hg : Tendsto g atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hle : ∀ N n, f n ≤ c N*g n+b N) : Tendsto f atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hh := ENNReal.half_pos hε.ne'
  obtain ⟨N,hN⟩ := (ENNReal.tendsto_nhds_zero.mp hb (ε/2) hh).exists
  have ht : Tendsto (fun n => c N*g n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hg (Or.inr (hc N))
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht (ε/2) hh] with n hn
  exact (hle N n).trans ((add_le_add hn hN).trans_eq (ENNReal.add_halves ε))

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma normalizedDiscrepancy_le_ratio_add_tail (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (T : ℝ≥0∞)
    (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p ω x ≤
      (D*(2*K) : ℕ)*T*G.clusterPeakRatio ω x + G.discrepancyVolumeTail p T ω x := by
  by_cases ht : T≤G.normalizedClusterVolume ω x
  · rw [discrepancyVolumeTail,ite_eq_left ht]
    exact le_add_left le_rfl
  · by_cases hm : G.modularMass x (G.cluster ω x)=∞
    · simp only [normalizedAbsoluteDiscrepancy,hm,ENNReal.div_top,zero_le]
    · have hr := G.clusterPeakRatio_ne_zero_of_mass_ne_top hc hl ω x hm
      have hr' := ne_top_of_le_ne_top ENNReal.one_ne_top (G.clusterPeakRatio_le_one hc hl ω x)
      have hv : G.normalizedClusterVolume ω x*G.clusterPeakRatio ω x=1 := by
        rw [normalizedClusterVolume,ite_eq_right hr,ENNReal.inv_mul_cancel hr hr']
      have hone : 1≤T*G.clusterPeakRatio ω x := by
        rw [←hv]
        exact mul_le_mul_left (le_of_not_ge ht) _
      calc _ ≤ ((D*(2*K) : ℕ) : ℝ≥0∞) := G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK p p.property ω x
           _ ≤ (D*(2*K) : ℕ)*T*G.clusterPeakRatio ω x := by
             simpa only [mul_one,mul_assoc] using mul_le_mul_right hone ((D*(2*K) : ℕ) : ℝ≥0∞)
           _ ≤ _ := le_add_right le_rfl

lemma expected_heavy_normalizedDiscrepancy_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p q : unitInterval) (N : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ u, if G.heavyFlag p u x then G.normalizedAbsoluteDiscrepancy q (atParameter q u) x else 0 ∂markLaw) ≤
      ((D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N)) *
        (∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 ∂markLaw) +
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
          (ENNReal.ofReal (1/2:ℝ))^N*2 := by
  let C : ℝ≥0∞ := (D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N)
  let r := fun u => if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0
  have hm : Measurable r := ((G.measurable_clusterPeakRatio x).comp (measurable_atParameter q)).ite
    (G.measurable_heavyFlag p x).setOf measurable_const
  calc
    _ ≤ ∫⁻ u, C*r u+G.discrepancyVolumeTail q (ENNReal.ofReal ((16:ℝ)^N)) (atParameter q u) x ∂markLaw := by
      apply lintegral_mono
      intro u
      by_cases h : G.heavyFlag p u x
      · simpa only [h,ite_true, if_true,r,C] using G.normalizedDiscrepancy_le_ratio_add_tail hc hl D K hD hK q
          (ENNReal.ofReal ((16:ℝ)^N)) (atParameter q u) x
      · simp only [h,ite_false, if_false,zero_le]
    _ = C*(∫⁻ u, r u ∂markLaw) + (∫⁻ ω, G.discrepancyVolumeTail q (ENNReal.ofReal ((16:ℝ)^N)) ω x ∂G.law q) := by
      rw [lintegral_add_left (show Measurable (fun u => C*r u) from measurable_const.mul hm),
        lintegral_const_mul'' C hm.aemeasurable]
      congr 1
      rw [show G.law q=(markLaw (E := E)).map (atParameter q) from by simpa only [BondGraph.law, BernoulliProduct.law_const] using (markLaw_map_atParameter (E := E) q).symm,
        lintegral_map (G.measurable_discrepancyVolumeTail q _ x) (measurable_atParameter q)]
    _ ≤ _ := add_le_add le_rfl (G.expected_discrepancyTail_bound hc hl hq D K hD hK q N x hx)

theorem tendsto_expected_heavy_normalizedDiscrepancy
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫⁻ u, if G.heavyFlag p u x then
      G.normalizedAbsoluteDiscrepancy (q n) (atParameter (q n) u) x else 0 ∂markLaw) atTop (𝓝 0) := by
  let r := fun n => ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter (q n) u) x else 0 ∂markLaw
  have hr : Tendsto r atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (G.tendsto_sum_expected_heavy_clusterPeakRatio hc hl hq p q hmono hqp hlim)
    · exact fun _ => zero_le
    · intro n
      exact Finset.single_le_sum (f := fun y => ∫⁻ u,
        if G.heavyFlag p u y then G.clusterPeakRatio (atParameter (q n) u) y else 0 ∂markLaw)
        (fun _ _ => zero_le) hx
  apply ennreal_tendsto_zero_of_uniform_tail _ r
    (fun N => (D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N))
    (fun N => (G.orbitRepresentatives hq).roots.card *
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (ENNReal.ofReal (1/2:ℝ))^N*2)
  · intro N
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  · exact hr
  · let A : ℝ≥0∞ := (G.orbitRepresentatives hq).roots.card *
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)
    have hA : A≠∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have ht := ENNReal.Tendsto.const_mul (a := A) (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show ENNReal.ofReal (1/2:ℝ)<1 by norm_num)) (Or.inr hA)
    simpa only [mul_zero,zero_mul] using ENNReal.Tendsto.mul_const ht (Or.inr (by norm_num : (2:ℝ≥0∞)≠∞))
  · intro N n
    exact G.expected_heavy_normalizedDiscrepancy_bound hc hl hq D K hD hK p (q n) N x hx

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_SignedDiscrepancyContinuity
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
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma normalizedSignedDiscrepancy_heavy (p : ℝ) (ω : Set E) (x : V)
    (h : G.modularMass x (G.cluster ω x)=∞) : G.normalizedSignedDiscrepancy p ω x=0 := by
  simp [normalizedSignedDiscrepancy,h]

lemma enorm_normalizedSignedDiscrepancy (p : ℝ) (ω : Set E) (x : V) :
    ‖G.normalizedSignedDiscrepancy p ω x‖ₑ=G.normalizedAbsoluteDiscrepancy p ω x := by
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [G.normalizedSignedDiscrepancy_heavy p ω x hm,normalizedAbsoluteDiscrepancy,hm]
  · have hpos : 0<(G.modularMass x (G.cluster ω x)).toReal :=
      ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm
    rw [Real.enorm_eq_ofReal_abs,normalizedSignedDiscrepancy,abs_div,abs_of_pos hpos,
      ENNReal.ofReal_div_of_pos hpos,ENNReal.ofReal_toReal hm]
    rfl

lemma measurable_normalizedSignedDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.normalizedSignedDiscrepancy p ω x) :=
  (G.measurable_weightedDiscrepancy p x).div (G.measurable_modularClusterMass x x).ennreal_toReal

lemma norm_normalizedSignedDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (ω : Set E) (x : V) :
    ‖G.normalizedSignedDiscrepancy p ω x‖≤(D*(2*K) : ℕ) := by
  have h := G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK p p.property ω x
  rw [←G.enorm_normalizedSignedDiscrepancy,←ENNReal.ofReal_natCast,Real.enorm_eq_ofReal_abs] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

lemma eventually_incident_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n=ω) (x : V) (e : E) :
    ∀ᶠ n in atTop, (e∈G.incidentEdges (G.cluster (a n) x))=(e∈G.incidentEdges (G.cluster ω x)) := by
  by_cases h : e∈G.incidentEdges (G.cluster ω x)
  · obtain ⟨v,hv,hve⟩ := h
    filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hv] with n hn
    exact propext ⟨fun _ => ⟨v,hv,hve⟩,fun _ => ⟨v,hn,hve⟩⟩
  · apply Eventually.of_forall
    intro n
    apply propext
    constructor
    · rintro ⟨v,hv,hve⟩
      exact ⟨v,G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hv,hve⟩
    · exact fun hn => False.elim (h hn)

lemma eventually_mem_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n=ω) (e : E) :
    ∀ᶠ n in atTop, (e∈a n)=(e∈ω) := by
  by_cases h : e∈ω
  · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hu ▸ h)
    exact eventually_atTop.mpr ⟨n,fun m hm => propext ⟨fun _ => h,fun _ => ha hm hn⟩⟩
  · apply Eventually.of_forall
    intro n
    exact propext ⟨fun hn => hu ▸ Set.mem_iUnion.mpr ⟨n,hn⟩, fun hn => False.elim (h hn)⟩

lemma tendsto_weightedDiscrepancy_of_exhaustion (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (p : unitInterval) (q : ℕ → unitInterval) (hq : Tendsto q atTop (𝓝 p))
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.weightedDiscrepancy (q n) (a n) x) atTop (𝓝 (G.weightedDiscrepancy p ω x)) := by
  have hq' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (p : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hq
  apply tendsto_tsum_of_dominated_convergence (G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm)
  · intro e
    have heq : ∀ᶠ n in atTop, G.weightedIncidenceTerm (q n) (a n) x e=G.weightedIncidenceTerm (q n) ω x e := by
      filter_upwards [G.eventually_incident_of_exhaustion a ω ha hu x e,
        eventually_mem_of_exhaustion a ω ha hu e] with n hn hn'
      simp only [weightedIncidenceTerm,centeredCoefficient,hn,hn']
    have heq' : (fun n => G.weightedIncidenceTerm (q n) (a n) x e) =ᶠ[atTop]
        (fun n => G.weightedIncidenceTerm (q n) ω x e) := heq
    apply Tendsto.congr' heq'.symm
    by_cases hi : e∈G.incidentEdges (G.cluster ω x)
    · by_cases ho : e∈ω
      · simp only [weightedIncidenceTerm,centeredCoefficient,ite_eq_left hi,ite_eq_left ho]
        exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hq')
      · simp only [weightedIncidenceTerm,centeredCoefficient,ite_eq_left hi,ite_eq_right ho]
        exact tendsto_const_nhds.mul hq'.neg
    · simp only [weightedIncidenceTerm,ite_eq_right hi]
      exact tendsto_const_nhds
  · apply Eventually.of_forall
    intro n e
    apply (G.norm_weightedIncidenceTerm_le (q n) (q n).property (a n) x e).trans
    by_cases hi : e∈G.incidentEdges (G.cluster (a n) x)
    · have hf : e∈G.incidentEdges (G.cluster ω x) := by
        obtain ⟨v,hv,hve⟩ := hi
        exact ⟨v,G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hv,hve⟩
      simp only [ite_eq_left hi,ite_eq_left hf,le_refl]
    · simp only [ite_eq_right hi,ENNReal.toReal_zero]
      exact ENNReal.toReal_nonneg

lemma tendsto_modularMass_toReal_of_exhaustion
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => (G.modularMass x (G.cluster (a n) x)).toReal) atTop
      (𝓝 (G.modularMass x (G.cluster ω x)).toReal) := by
  have hterm (S : Set V) (y : V) : (if y∈S then G.stabilizerWeight x y else 0)≠∞ := by
    split_ifs
    · exact G.stabilizerWeight_ne_top x y
    · exact ENNReal.zero_ne_top
  simp only [modularMass,ENNReal.tsum_toReal_eq (hterm _)]
  apply tendsto_tsum_of_dominated_convergence (ENNReal.summable_toReal hm)
  · intro y
    by_cases hy : y∈G.cluster ω x
    · apply tendsto_const_nhds.congr'
      filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy] with n hn
      simp only [ite_eq_left hy,ite_eq_left hn]
    · have hn (n : ℕ) : y∉G.cluster (a n) x := fun h => hy (G.cluster_mono (hu ▸ Set.subset_iUnion a n) x h)
      simp only [ite_eq_right hy,ite_eq_right (hn _)]
      exact tendsto_const_nhds
  · apply Eventually.of_forall
    intro n y
    by_cases hn : y∈G.cluster (a n) x
    · have hy : y∈G.cluster ω x := G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hn
      simp only [ite_eq_left hn,ite_eq_left hy,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,le_refl]
    · simp only [ite_eq_right hn,ENNReal.toReal_zero,norm_zero]
      exact ENNReal.toReal_nonneg

lemma tendsto_normalizedSignedDiscrepancy_finiteMass
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (p : unitInterval) (q : ℕ → unitInterval) (hq : Tendsto q atTop (𝓝 p))
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.normalizedSignedDiscrepancy (q n) (a n) x) atTop
      (𝓝 (G.normalizedSignedDiscrepancy p ω x)) := by
  exact (G.tendsto_weightedDiscrepancy_of_exhaustion hc hl D K hD hK a ω ha hu p q hq x hm).div
    (G.tendsto_modularMass_toReal_of_exhaustion a ω ha hu x hm)
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm).ne'

lemma integrable_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (x : V) :
    Integrable (fun u => G.normalizedSignedDiscrepancy p (atParameter p u) x) markLaw := by
  apply Integrable.of_bound
    (((G.measurable_normalizedSignedDiscrepancy p x).comp (measurable_atParameter p)).aestronglyMeasurable)
    (D*(2*K) : ℕ)
  exact Eventually.of_forall (fun u => G.norm_normalizedSignedDiscrepancy_le hc hl D K hD hK p _ x)

theorem tendsto_L1_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫⁻ u, ‖G.normalizedSignedDiscrepancy (q n) (atParameter (q n) u) x -
      G.normalizedSignedDiscrepancy p (atParameter p u) x‖ₑ ∂markLaw) atTop (𝓝 0) := by
  let f := fun (r : unitInterval) u => G.normalizedSignedDiscrepancy r (atParameter r u) x
  have hfm (r : unitInterval) : Measurable (f r) :=
    (G.measurable_normalizedSignedDiscrepancy r x).comp (measurable_atParameter r)
  let a := fun n u => if G.heavyFlag p u x then
    G.normalizedAbsoluteDiscrepancy (q n) (atParameter (q n) u) x else 0
  let b := fun n u => if G.heavyFlag p u x then 0 else ‖f (q n) u-f p u‖ₑ
  have hbm (n : ℕ) : Measurable (b n) :=
    measurable_const.ite (G.measurable_heavyFlag p x).setOf ((hfm _).sub (hfm _)).enorm
  have hb : Tendsto (fun n => ∫⁻ u, b n u ∂markLaw) atTop (𝓝 0) := by
    have hbound (n : ℕ) : ∀ᵐ u ∂markLaw, b n u≤((D*(2*K) : ℕ) : ℝ≥0∞)+((D*(2*K) : ℕ) : ℝ≥0∞) := by
      apply Eventually.of_forall
      intro u
      dsimp only [b]
      split_ifs
      · exact zero_le
      · apply enorm_sub_le.trans
        simpa only [f,G.enorm_normalizedSignedDiscrepancy] using
          add_le_add (G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK _ (q n).property _ x)
            (G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK _ p.property _ x)
    have ht : ∀ᵐ u ∂markLaw, Tendsto (fun n => b n u) atTop (𝓝 (0:ℝ≥0∞)) := by
      apply Eventually.of_forall
      intro u
      by_cases hh : G.heavyFlag p u x
      · simp only [b,ite_eq_left hh]
        exact tendsto_const_nhds
      · simp only [b,ite_eq_right hh]
        have ht := G.tendsto_normalizedSignedDiscrepancy_finiteMass hc hl D K hD hK
          (fun n => atParameter (q n) u) (atParameter p u) ((atParameter_mono u).comp hmono)
          (atParameter_iUnion p q hqp hlim u) p q hlim x hh
        simpa only [f,sub_self,enorm_zero] using (ht.sub_const (f p u)).enorm
    simpa only [lintegral_zero] using tendsto_lintegral_of_dominated_convergence
      (μ := (markLaw : Measure (E → ℝ)))
      (fun _ => ((D*(2*K) : ℕ) : ℝ≥0∞)+((D*(2*K) : ℕ) : ℝ≥0∞)) hbm hbound (by
        simpa only [lintegral_const,measure_univ,mul_one] using
          (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _,ENNReal.natCast_ne_top _⟩)) ht
  have ha := G.tendsto_expected_heavy_normalizedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx
  have heq (n : ℕ) (u : E → ℝ) : ‖f (q n) u-f p u‖ₑ=a n u+b n u := by
    by_cases hh : G.heavyFlag p u x
    · simp only [a,b,ite_eq_left hh,add_zero,f,G.normalizedSignedDiscrepancy_heavy p _ x hh,
        sub_zero,G.enorm_normalizedSignedDiscrepancy]
    · simp only [a,b,ite_eq_right hh,zero_add]
  change Tendsto (fun n => ∫⁻ u, ‖f (q n) u-f p u‖ₑ ∂markLaw) atTop (𝓝 0)
  have hi (n : ℕ) : (∫⁻ u, ‖f (q n) u-f p u‖ₑ ∂markLaw) =
      (∫⁻ u, a n u ∂markLaw)+(∫⁻ u, b n u ∂markLaw) := by
    simp_rw [heq]
    exact lintegral_add_right _ (hbm n)
  simp_rw [hi]
  simpa only [add_zero] using ha.add hb

 theorem tendsto_expected_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫ u, G.normalizedSignedDiscrepancy (q n) (atParameter (q n) u) x ∂markLaw)
      atTop (𝓝 (∫ u, G.normalizedSignedDiscrepancy p (atParameter p u) x ∂markLaw)) := by
  apply tendsto_integral_of_L1 (fun u => G.normalizedSignedDiscrepancy p (atParameter p u) x)
  · exact (G.integrable_normalizedSignedDiscrepancy hc hl D K hD hK p x).aestronglyMeasurable
  · exact Eventually.of_forall (fun n => G.integrable_normalizedSignedDiscrepancy hc hl D K hD hK (q n) x)
  · exact G.tendsto_L1_normalizedSignedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ForcedDisconnectContinuity
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
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma integral_atParameter [Countable V] [Countable E] (p : unitInterval)
    (f : Set E → ℝ) (hf : Measurable f) :
    (∫ u, f (atParameter p u) ∂markLaw) = ∫ ω, f ω ∂G.law p := by
  rw [←integral_map (measurable_atParameter p).aemeasurable hf.aestronglyMeasurable,
    markLaw_map_atParameter,BernoulliProduct.law_const]
  rfl

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_CriticalHeavyDrop
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
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma tendsto_expected_signed_discrepancy_law_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => ∑ x∈(G.orbitRepresentatives hq).roots,
      ∫ ω, G.normalizedSignedDiscrepancy (q n) ω x ∂G.law (q n)) atTop
      (𝓝 (∑ x∈(G.orbitRepresentatives hq).roots,
        ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p)) := by
  apply tendsto_finsetSum _
  intro x hx
  have h := G.tendsto_expected_normalizedSignedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx
  simpa only [G.integral_atParameter _ _ (G.measurable_normalizedSignedDiscrepancy _ x)] using h

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law_oai.{u_1, u_2}
