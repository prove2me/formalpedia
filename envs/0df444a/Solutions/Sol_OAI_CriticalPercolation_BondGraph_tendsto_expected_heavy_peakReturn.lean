-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:58.644303+00:00
-- url     : https://prove2.me/submissions/3310089c-8446-48f9-97be-da043a731dd0

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_incoming_finite_ae
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_pos

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

lemma measurableSet_heavyClusterEvent [Countable V] [Countable E] (o v : V) :
    MeasurableSet (G.heavyClusterEvent o v) :=
  measurableSet_eq_fun (G.measurable_modularClusterMass o v) measurable_const

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

lemma peakBound_iff_of_reachable (N : ℕ) {ω : Set E} {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.peakBound N ω x ↔ G.peakBound N ω y := by
  unfold peakBound
  rw [G.clusterPeaks_eq_of_reachable h]

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

lemma Aut.peakBound_iff (φ : G.Aut) (N : ℕ) (ω : Set E) (v : V) :
    G.peakBound N (φ.edge '' ω) (φ.vertex v) ↔ G.peakBound N ω v := by
  change (∃ S : Finset V, S.card ≤ N ∧ G.clusterPeaks (φ.edge '' ω) (φ.vertex v) ⊆ S) ↔ _
  rw [←φ.clusterPeaks_image]
  constructor
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex.symm,(Finset.card_image_le).trans hS,?_⟩
    intro x hx
    exact Finset.mem_image.mpr ⟨φ.vertex x,h ⟨x,hx,rfl⟩,φ.vertex.symm_apply_apply x⟩
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex,(Finset.card_image_le).trans hS,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact Finset.mem_image.mpr ⟨x,h hx,rfl⟩

lemma measurable_clusterPeak [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeak ω x) := by
  exact .forall (fun z => (G.measurable_reachable x z).imp measurable_const)

lemma measurable_mem_clusterPeaks [Countable V] [Countable E] (v x : V) :
    Measurable (fun ω : Set E => x∈G.clusterPeaks ω v) :=
  (G.measurable_reachable v x).and (G.measurable_clusterPeak x)

lemma measurable_peakBound [Countable V] [Countable E] (N : ℕ) (v : V) :
    Measurable (fun ω : Set E => G.peakBound N ω v) := by
  exact .exists (fun S : Finset V => measurable_const.and
    (.forall (fun x => (G.measurable_mem_clusterPeaks v x).imp measurable_const)))

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyPeaks
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_heavyPeakTransport (N : ℕ) (x y : V) :
    Measurable (fun ω : Set E => G.heavyPeakTransport N ω x y) := by
  apply measurable_const.ite _ measurable_const
  exact (G.measurableSet_heavyClusterEvent x x).inter
    ((G.measurable_peakBound N x).and (G.measurable_mem_clusterPeaks x y)).setOf

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_aut (N : ℕ) (φ : G.Aut) (ω : Set E) (x y : V) :
    G.heavyPeakTransport N (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.heavyPeakTransport N ω x y := by
  unfold heavyPeakTransport
  rw [←φ.cluster_image,φ.modularMass_image,φ.peakBound_iff,←φ.clusterPeaks_image]
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_out_bound (N : ℕ) (ω : Set E) (x : V) :
    (∑' y, G.heavyPeakTransport N ω x y) ≤ N := by
  by_cases hb : G.peakBound N ω x
  · obtain ⟨S,hS,hcover⟩ := hb
    calc
      _ ≤ ∑' y, if y∈S then (1 : ℝ≥0∞) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro y
        unfold heavyPeakTransport
        split_ifs with hh hs
        · rfl
        · exact False.elim (hs (hcover hh.2.2))
        · exact zero_le
        · rfl
      _ = (S.card : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun y hy => ite_eq_right hy)]
        calc
          _ = ∑ y ∈ S, (1 : ℝ≥0∞) := Finset.sum_congr rfl (fun y hy => ite_eq_left hy)
          _ = _ := by simp
      _ ≤ N := by exact_mod_cast hS
  · simp only [heavyPeakTransport,hb,false_and,and_false,ite_false, if_false,tsum_zero,zero_le]

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_infinite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (N : ℕ) (ω : Set E) (y : V)
    (hh : G.modularMass y (G.cluster ω y) = ∞) (hb : G.peakBound N ω y)
    (hp : G.clusterPeak ω y) :
    (∑' x, G.heavyPeakTransport N ω x y * G.stabilizerWeight y x) = ∞ := by
  apply top_unique
  rw [←hh]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ G.cluster ω y
  · have hxy : (G.openGraph ω).Reachable x y := hx.symm
    have he : G.cluster ω x = G.cluster ω y := G.cluster_eq_of_reachable hxy
    have hhx : G.modularMass x (G.cluster ω x) = ∞ := by
      rw [he,G.modularMass_eq_top_change_base hc hl x y]
      exact hh
    have hbx : G.peakBound N ω x := (G.peakBound_iff_of_reachable N hxy).mpr hb
    have hcond : G.modularMass x (G.cluster ω x) = ∞ ∧ G.peakBound N ω x ∧
        y∈G.clusterPeaks ω x := ⟨hhx,hbx,⟨hxy,hp⟩⟩
    simp only [ite_eq_left hx,heavyPeakTransport,ite_eq_left hcond,one_mul,le_refl]
  · simp only [ite_eq_right hx,zero_le]

lemma no_heavy_finite_peaks_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (p : unitInterval) :
    ∀ᵐ ω ∂G.law p, ∀ y : V, ∀ N : ℕ,
      ¬ (G.modularMass y (G.cluster ω y) = ∞ ∧ G.peakBound N ω y ∧ G.clusterPeak ω y) := by
  apply ae_all_iff.mpr
  intro y
  apply ae_all_iff.mpr
  intro N
  have hfin := OrbitRepresentatives.incoming_finite_ae G (G.orbitRepresentatives hq)
    hc hl p (G.heavyPeakTransport N) (G.measurable_heavyPeakTransport N)
    (G.heavyPeakTransport_aut N) N (ENNReal.natCast_lt_top N) (G.heavyPeakTransport_out_bound N) y
  filter_upwards [hfin] with ω hω
  rintro ⟨hh,hb,hp⟩
  rw [G.heavyPeakTransport_infinite hc hl N ω y hh hb hp] at hω
  exact (lt_irrefl _ hω)

end CriticalPercolation.BondGraph
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
lemma marks_ae_of_law_ae (p : unitInterval) (P : Set E → Prop) (h : ∀ᵐ ω ∂G.law p, P ω) :
    ∀ᵐ u ∂markLaw, P (atParameter p u) := by
  apply ae_of_ae_map (measurable_atParameter p).aemeasurable
  rwa [markLaw_map_atParameter,BernoulliProduct.law_const]

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

lemma peakReturn_le_one (ω : Set E) (x : V) : G.peakReturn ω x ≤ 1 := by
  unfold peakReturn
  split_ifs with hp
  · apply ENNReal.inv_le_one.mpr
    have hh : (1 : ℕ∞) ≤ (G.clusterPeaks ω x).encard :=
      Set.one_le_encard_iff_nonempty.mpr ⟨x,SimpleGraph.Reachable.refl x,hp⟩
    exact_mod_cast hh
  · exact zero_le

lemma clusterPeak_of_subset {ω τ : Set E} (h : ω⊆τ) {x : V}
    (hp : G.clusterPeak τ x) : G.clusterPeak ω x :=
  fun y hy => hp y (hy.mono (G.openGraph_mono h))

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

lemma eventually_peaks_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) {x y : V} (hy : y∈G.clusterPeaks ω x) :
    ∀ᶠ n in atTop, y∈G.clusterPeaks (a n) x := by
  filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy.1] with n hn
  refine ⟨hn,G.clusterPeak_of_subset ?_ hy.2⟩
  exact hu ▸ Set.subset_iUnion a n

lemma tendsto_peakCount_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) (x : V)
    (hi : (G.clusterPeaks ω x).Infinite) :
    Tendsto (fun n => ((G.clusterPeaks (a n) x).encard : ℝ≥0∞)) atTop (𝓝 ∞) := by
  apply ENNReal.tendsto_nhds_top_iff_nat.mpr
  intro N
  obtain ⟨S,hS,hcard⟩ := hi.exists_subset_card_eq (N+1)
  have he : ∀ y∈(S : Set V), ∀ᶠ n in atTop, y∈G.clusterPeaks (a n) x :=
    fun y hy => G.eventually_peaks_of_exhaustion a ω ha hu (hS hy)
  filter_upwards [(Filter.eventually_all_finite S.finite_toSet).mpr he] with n hn
  have hh := ENat.toENNReal_mono (Set.encard_mono hn)
  have hb : ((N+1 : ℕ) : ℝ≥0∞) ≤ ((G.clusterPeaks (a n) x).encard : ℝ≥0∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard,ENat.toENNReal_coe,hcard] using hh
  have hN : (N : ℝ≥0∞) < ((N+1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.lt_succ_self N
  exact hN.trans_le hb

lemma tendsto_peakReturn_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) (x : V)
    (h : ¬ G.clusterPeak ω x ∨ (G.clusterPeaks ω x).Infinite) :
    Tendsto (fun n => G.peakReturn (a n) x) atTop (𝓝 0) := by
  rcases h with hp|hi
  · have hw : ∃ y, (G.openGraph ω).Reachable x y ∧ ¬G.stabilizerWeight x y ≤ 1 := by
      obtain ⟨y,hy⟩ := not_forall.mp hp
      exact ⟨y,Classical.not_imp.mp hy⟩
    obtain ⟨y,hy,hyw⟩ := hw
    have he : ∀ᶠ n in atTop, G.peakReturn (a n) x = 0 := by
      filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy] with n hn
      exact ite_eq_right (fun hh => hyw (hh y hn))
    exact tendsto_const_nhds.congr' (he.mono (fun _ hh => hh.symm))
  · have ht := (G.tendsto_peakCount_of_exhaustion a ω ha hu x hi).inv
    simp only [ENNReal.inv_top] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall (fun _ => zero_le))
    apply Eventually.of_forall
    intro n
    unfold peakReturn
    split_ifs
    · rfl
    · exact zero_le

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyThinning
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

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_heavyFlag (p : unitInterval) (x : V) :
    Measurable (fun u => G.heavyFlag p u x) :=
  ((G.measurable_modularClusterMass x x).comp (measurable_atParameter p)).eq_const ∞

lemma tendsto_expected_heavy_peakReturn_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (x : V) :
    Tendsto (fun n => ∫⁻ u, if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0 ∂markLaw)
      atTop (𝓝 0) := by
  have hmeas (n : ℕ) : Measurable (fun u =>
      if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) :=
    ((G.measurable_peakReturn x).comp (measurable_atParameter (q n))).ite
      (G.measurable_heavyFlag p x).setOf measurable_const
  have hbound (n : ℕ) : ∀ᵐ u ∂markLaw,
      (if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) ≤ (1:ℝ≥0∞) := by
    exact Eventually.of_forall (fun u => by split_ifs; exact G.peakReturn_le_one _ x; exact zero_le)
  have hae := G.marks_ae_of_law_ae p _ (G.no_heavy_finite_peaks_ae hc hl hq p)
  have ht : ∀ᵐ u ∂markLaw, Tendsto (fun n =>
      if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) atTop (𝓝 (0:ℝ≥0∞)) := by
    filter_upwards [hae] with u hu
    by_cases h : G.heavyFlag p u x
    · simp only [h,ite_true, if_true]
      apply G.tendsto_peakReturn_of_exhaustion _ _
        ((atParameter_mono u).comp hmono) (atParameter_iUnion p q hqp hlim u) x
      by_cases hp : G.clusterPeak (atParameter p u) x
      · right
        intro hf
        exact hu x hf.toFinset.card ⟨h,⟨hf.toFinset,le_rfl,fun _ hy => hf.mem_toFinset.mpr hy⟩,hp⟩
      · exact Or.inl hp
    · simp only [h,ite_false, if_false]
      exact tendsto_const_nhds
  simpa only [lintegral_zero] using
    tendsto_lintegral_of_dominated_convergence (μ := (markLaw : Measure (E → ℝ)))
      (fun _ => (1:ℝ≥0∞)) hmeas hbound (by simp) ht

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn_oai.{u_1, u_2}
