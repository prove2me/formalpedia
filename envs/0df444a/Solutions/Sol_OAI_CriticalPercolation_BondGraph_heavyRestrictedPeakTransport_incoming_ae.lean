-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:53.009849+00:00
-- url     : https://prove2.me/submissions/6fd5adc8-e974-42e2-ac34-d57a780b0866

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_incoming_finite_ae
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_clusterPeaks_finite_of_mass_ne_top
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

lemma peakRatioTransport_incoming (ω : Set E) (y : V) :
    (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
      if G.clusterPeak ω y ∧ G.modularMass y (G.cluster ω y) ≠ ∞ then
        ((G.clusterPeaks ω y).ncard : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hp : G.clusterPeak ω y
  · have heq : (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
        ((G.modularMass y (G.cluster ω y))⁻¹ * ((G.clusterPeaks ω y).ncard : ℝ≥0∞)⁻¹) *
          G.modularMass y (G.cluster ω y) := by
      conv_rhs => rhs; unfold modularMass
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      by_cases hx : x∈G.cluster ω y
      · rw [ite_eq_left hx,peakRatioTransport,ite_eq_left ⟨hx.symm,hp⟩,
          G.cluster_eq_of_reachable hx.symm,G.clusterPeaks_eq_of_reachable hx.symm]
      · have hnot : y∉G.clusterPeaks ω x := fun h => hx h.1.symm
        simp only [peakRatioTransport,ite_eq_right hnot,zero_mul,ite_eq_right hx,mul_zero]
    rw [heq]
    by_cases hm : G.modularMass y (G.cluster ω y) = ∞
    · simp [hp,hm]
    · rw [ite_eq_left ⟨hp,hm⟩,mul_right_comm,
        ENNReal.inv_mul_cancel (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω y))) hm,
        one_mul]
  · have hz : ∀ x, G.peakRatioTransport ω x y = 0 := by
      intro x
      exact ite_eq_right (fun h => hp h.2)
    simp only [hz,zero_mul,tsum_zero,hp,false_and,ite_false, if_false]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakReturn
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
variable {V E : Type*} (G : BondGraph V E)

lemma peakReturn_eq_inv_ncard (ω : Set E) (x : V) (hp : G.clusterPeak ω x)
    (hf : (G.clusterPeaks ω x).Finite) :
    G.peakReturn ω x = ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹ := by
  rw [peakReturn,ite_eq_left hp,hf.encard_eq_coe,ENat.toENNReal_coe]
  rfl

lemma peakRatioTransport_incoming_ae [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (y : V) :
    ∀ᵐ ω ∂G.law p, (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
      G.peakReturn ω y := by
  filter_upwards [G.no_heavy_finite_peaks_ae hc hl hq p] with ω hω
  rw [G.peakRatioTransport_incoming]
  by_cases hp : G.clusterPeak ω y
  · by_cases hm : G.modularMass y (G.cluster ω y) = ∞
    · have hi : (G.clusterPeaks ω y).Infinite := by
        intro hf
        exact hω y hf.toFinset.card ⟨hm,⟨hf.toFinset,le_rfl,fun _ hx => hf.mem_toFinset.mpr hx⟩,hp⟩
      simp [peakReturn,hp,hm,hi.encard_eq]
    · rw [ite_eq_left ⟨hp,hm⟩,G.peakReturn_eq_inv_ncard ω y hp
        (G.clusterPeaks_finite_of_mass_ne_top hc hl ω y hm)]
  · simp only [hp,false_and,ite_false, if_false,peakReturn]

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

omit [Countable V] [Countable E] in
lemma heavyFlag_iff_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {p q : unitInterval} (hqp : q≤p) (u : E → ℝ) {x y : V}
    (hxy : (G.openGraph (atParameter q u)).Reachable x y) :
    G.heavyFlag p u x ↔ G.heavyFlag p u y := by
  have hr := hxy.mono (G.openGraph_mono (atParameter_mono u hqp))
  unfold heavyFlag
  rw [G.cluster_eq_of_reachable hr,G.modularMass_eq_top_change_base hc hl x y]

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_swap (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {p q : unitInterval} (hqp : q≤p) (u : E → ℝ) (x y : V) :
    G.heavyRestrictedPeakTransport p q u x y =
    if G.heavyFlag p u y then G.peakRatioTransport (atParameter q u) x y else 0 := by
  by_cases hy : y∈G.clusterPeaks (atParameter q u) x
  · simp only [heavyRestrictedPeakTransport,G.heavyFlag_iff_of_reachable hc hl hqp u hy.1]
  · simp only [heavyRestrictedPeakTransport,peakRatioTransport,ite_eq_right hy,ite_self]

lemma heavyRestrictedPeakTransport_incoming_ae_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    {p q : unitInterval} (hqp : q≤p) (y : V) :
    ∀ᵐ u ∂markLaw, (∑' x, G.heavyRestrictedPeakTransport p q u x y * G.stabilizerWeight y x) =
      if G.heavyFlag p u y then G.peakReturn (atParameter q u) y else 0 := by
  have ha := G.marks_ae_of_law_ae q _ (G.peakRatioTransport_incoming_ae hc hl hq q y)
  filter_upwards [ha] with u hu
  simp only [G.heavyRestrictedPeakTransport_swap hc hl hqp]
  by_cases h : G.heavyFlag p u y
  · simpa only [h,ite_true, if_true] using hu
  · simp only [h,ite_false, if_false,zero_mul,tsum_zero]

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.heavyRestrictedPeakTransport_incoming_ae_oai.{u_1, u_2}
