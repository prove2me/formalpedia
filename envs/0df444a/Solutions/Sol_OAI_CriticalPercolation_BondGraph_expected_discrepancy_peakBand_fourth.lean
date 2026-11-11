-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:25:23.8902+00:00
-- url     : https://prove2.me/submissions/04f10b8d-c55a-43ae-9c2f-203526794297

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_normalizedClusterVolume_eq_at_peak
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_restriction_quadratic_real_le
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_pos
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_weighted_incidence_le
import Theorems.Thm_OAI_CriticalPercolation_FiniteClusters_restrict_cluster
import Theorems.Thm_OAI_CriticalPercolation_IncidenceSearch_compile_terminal
import Theorems.Thm_OAI_CriticalPercolation_SearchTree_restricted_weighted_event_fourth

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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ComponentSelf
attribute [-simp] _root_.OAI.CriticalPercolation.ClusterDeletion.component_bot _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}

lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]

end CriticalPercolation.ClusterDeletion

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FourthMomentFatou
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace CriticalPercolation
variable {X : Type*} [MeasurableSpace X]

lemma lintegral_fourth_bound_of_tendsto (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (g : X → ℝ≥0∞) (C : ℝ≥0∞) (hm : ∀ n, Measurable (f n))
    (ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hb : ∀ n, (∫⁻ x, f n x ∂μ)^4≤C) : (∫⁻ x, g x ∂μ)^4≤C := by
  have hroot (n : ℕ) : (∫⁻ x, f n x ∂μ) ≤ C^((4:ℝ)⁻¹) := by
    apply (ENNReal.le_rpow_inv_iff (by norm_num : (0:ℝ)<4)).mpr
    simpa only [ENNReal.rpow_ofNat] using hb n
  have hlim : (∫⁻ x, g x ∂μ) ≤ C^((4:ℝ)⁻¹) := by
    calc _ = ∫⁻ x, liminf (fun n => f n x) atTop ∂μ := by
               apply lintegral_congr
               intro x
               exact (ht x).liminf_eq.symm
         _ ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := lintegral_liminf_le hm
         _ ≤ C^((4:ℝ)⁻¹) :=
           liminf_le_of_frequently_le (Eventually.frequently (Eventually.of_forall hroot))
  have h := (ENNReal.le_rpow_inv_iff (by norm_num : (0:ℝ)<4)).mp hlim
  simpa only [ENNReal.rpow_ofNat] using h

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceSearch
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

namespace CriticalPercolation.IncidenceSearch

variable {V E : Type*} [DecidableEq E]

lemma compile_valid (G : BondGraph V E) (v : V) (n : ℕ) (st : State E) :
    (compile G v n st).Valid st.read := by
  induction n generalizing st with
  | zero => trivial
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · exact ⟨h.choose_spec.1,ih _,ih _⟩
    · trivial

lemma terminal_cluster (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (ht : ¬∃ e, Available G v st e) :
    G.cluster ω v = G.cluster (st.opened : Set E) v ∧
      (st.read : Set E) = G.incidentEdges (G.cluster ω v) := by
  have hread : ∀ e ∈ G.incidentEdges (G.cluster (st.opened : Set E) v), e ∈ st.read := by
    intro e he
    by_contra hh
    exact ht ⟨e,hh,he⟩
  have hc : G.cluster ω v = G.cluster (st.opened : Set E) v := by
    have hh := G.roots_eq_of_incident (S := {v}) (U := G.cluster (st.opened : Set E) v)
      (ω := (st.opened : Set E)) (ω' := ω)
      (by simp only [ClusterDeletion.roots_singleton,ClusterDeletion.component,BondGraph.cluster])
      (fun e he => hs.2.1 e (hread e he))
    simpa only [ClusterDeletion.roots_singleton,ClusterDeletion.component,BondGraph.cluster] using hh
  refine ⟨hc,?_⟩
  rw [hc]
  exact Set.Subset.antisymm hs.2.2 hread

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceIdentity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

variable [Fintype E]

lemma tree_valid (G : BondGraph V E) (v : V) : (tree G v).Valid ∅ :=
  compile_valid G v _ _

lemma tree_read (G : BondGraph V E) (v : V) (ω : Set E) :
    (((tree G v).run (fun e => decide (e∈ω))).read : Set E) =
      G.incidentEdges (G.cluster ω v) := by
  have hg : Good G v ω (⟨∅,∅⟩ : State E) := by simp [Good]
  have hh := compile_terminal G v ω (Fintype.card E+1) ⟨∅,∅⟩ hg (by simp)
  exact (terminal_cluster G v ω _ hh.1 hh.2).2

lemma tree_mem_read (G : BondGraph V E) (v : V) (ω : Set E) (e : E) :
    e ∈ ((tree G v).run (fun a => decide (a∈ω))).read ↔
      e ∈ G.incidentEdges (G.cluster ω v) := by
  exact Set.ext_iff.mp (tree_read G v ω) e

end CriticalPercolation.IncidenceSearch
end
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEvent
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
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma finite_subset_exhaustion {X : Type*} {U S : Set X}
    (K : Set.FiniteExhaustion U) (hS : S.Finite) (hSU : S ⊆ U) :
    ∃ n, S ⊆ K n := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x S hx hS ih =>
      obtain ⟨n, hn⟩ := ih (Set.Subset.trans (Set.subset_insert _ _) hSU)
      have hxU := hSU (Set.mem_insert x S)
      rw [← K.iUnion_eq, Set.mem_iUnion] at hxU
      obtain ⟨m, hm⟩ := hxU
      exact ⟨max m n, Set.insert_subset (K.mono (le_max_left _ _) hm)
        (Set.Subset.trans hn (K.mono (le_max_right _ _)))⟩

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

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

lemma measurable_peakRatioTransport [Countable V] [Countable E] (x y : V) :
    Measurable (fun ω : Set E => G.peakRatioTransport ω x y) := by
  apply Measurable.ite (G.measurable_mem_clusterPeaks x y).setOf _ measurable_const
  apply Measurable.mul (G.measurable_modularClusterMass y x).inv
  apply Measurable.inv
  apply Measurable.of_discrete.comp
  apply measurable_ncard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

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

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedPeakTransport
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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

lemma peakVolumeBand_le_one (T U : ℝ≥0∞) (ω : Set E) (x : V) : G.peakVolumeBand T U ω x≤1 := by
  unfold peakVolumeBand
  split_ifs
  · exact G.peakReturn_le_one ω x
  · exact zero_le

lemma peakVolumeBand_support (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) (h : G.peakVolumeBand T U ω x≠0) :
    G.clusterPeak ω x ∧ T≤G.modularMass x (G.cluster ω x) ∧
      G.modularMass x (G.cluster ω x)<U := by
  have hb : T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U := by
    by_contra hn
    exact h (ite_eq_right hn)
  have hp : G.clusterPeak ω x := by
    by_contra hn
    exact h (by simp only [peakVolumeBand,ite_eq_left hb,peakReturn,ite_eq_right hn])
  have hm : G.modularMass x (G.cluster ω x)≠∞ := by
    intro he
    have hz := G.clusterPeakRatio_eq_zero_of_heavy hc hl ω x he
    have hvol : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,hz]
    rw [hvol] at hb
    exact (not_le.mpr hT) hb.1
  rw [G.normalizedClusterVolume_eq_at_peak hc hl ω x hp hm] at hb
  exact ⟨hp,hb⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedDiscrepancy
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

lemma summable_weightedIncidence_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (ω : Set E) (x : V)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Summable (fun e => (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal) := by
  apply ENNReal.summable_toReal
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
    (G.weighted_incidence_le hc hl D K hD hK x _)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedIncidenceSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

lemma compile_weighted_trace (G : BondGraph V E) (v : V) (n : ℕ) (st : State E)
    (ω : Set E) (a : E → ℝ) (p : ℝ) :
    let t := compile G v n st
    let out := t.run (fun e => decide (e∈ω))
    t.weightedSum a p ω + weightedRead a p ω st = weightedRead a p ω out ∧
    t.quadraticCost a ω + quadraticRead a st = quadraticRead a out := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.weightedSum,SearchTree.quadraticCost]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : e∉st.read := h.choose_spec.1
      have hopen := ih (st.open e)
      have hclosed := ih (st.closed e)
      have hs : weightedRead a p ω (st.open e) =
          (if e∈ω then a e*(1-p) else -a e*p)+weightedRead a p ω st := by
        simp only [weightedRead,State.open,Finset.sum_insert he]
      have hs' : weightedRead a p ω (st.closed e) =
          (if e∈ω then a e*(1-p) else -a e*p)+weightedRead a p ω st := by
        simp only [weightedRead,State.closed,Finset.sum_insert he]
      have hq : quadraticRead a (st.open e) = (a e)^2+quadraticRead a st := by
        simp only [quadraticRead,State.open,Finset.sum_insert he]
      have hq' : quadraticRead a (st.closed e) = (a e)^2+quadraticRead a st := by
        simp only [quadraticRead,State.closed,Finset.sum_insert he]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        (if ω e then a e*(1-p)+(compile G v n (st.open e)).weightedSum a p ω else
          -a e*p+(compile G v n (st.closed e)).weightedSum a p ω) + weightedRead a p ω st =
          weightedRead a p ω out ∧
        ((a e)^2 + if ω e then (compile G v n (st.open e)).quadraticCost a ω else
          (compile G v n (st.closed e)).quadraticCost a ω) + quadraticRead a st = quadraticRead a out)
      by_cases hω : e∈ω
      · have hω' : ω e := hω
        simp only [hω,hω',decide_true,ite_true, if_true]
        dsimp only at hopen
        rw [hs,hq,ite_eq_left hω] at hopen
        constructor <;> linarith [hopen.1,hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,ite_false, if_false]
        dsimp only at hclosed
        rw [hs',hq',ite_eq_right hω] at hclosed
        constructor <;> linarith [hclosed.1,hclosed.2]
    · simp [SearchTree.run,SearchTree.weightedSum,SearchTree.quadraticCost]

variable [Fintype E]

lemma tree_weighted (G : BondGraph V E) (v : V) (ω : Set E) (a : E → ℝ) (p : ℝ) :
    (tree G v).weightedSum a p ω = ∑ e, if e∈G.incidentEdges (G.cluster ω v) then
      (if e∈ω then a e*(1-p) else -a e*p) else 0 := by
  have h := (compile_weighted_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω a p).1
  change (tree G v).weightedSum a p ω + weightedRead a p ω ⟨∅,∅⟩ =
    weightedRead a p ω ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [weightedRead,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then
        (if e∈ω then a e*(1-p) else -a e*p) else 0 := by
      simp only [←Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [tree_mem_read]

end CriticalPercolation.IncidenceSearch
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedDiscrepancyLimit
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

lemma restrictedWeightedDiscrepancy_eq_tree (s : Set E) [Fintype s]
    (p : ℝ) (ω : Set E) (x : V) :
    G.restrictedWeightedDiscrepancy s p ω x =
      (IncidenceSearch.tree (G.restrictEdges s) x).weightedSum
        (fun e : s => (G.bondWeight x e.val).toReal) p (Subtype.val ⁻¹' ω) := by
  rw [IncidenceSearch.tree_weighted]
  unfold restrictedWeightedDiscrepancy restrictedWeightedTerm
  have ht : (∑' e : E, if e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x) then
      (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0) =
      ∑' e : s, if e.val∈G.incidentEdges (G.cluster (s∩ω) x) then
        (G.bondWeight x e.val).toReal*centeredCoefficient p ω e.val else 0 := by
    rw [tsum_subtype s (fun e : E => if e∈G.incidentEdges (G.cluster (s∩ω) x) then
      (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0)]
    apply tsum_congr
    intro e
    by_cases he : e∈s <;> simp only [Set.indicator,he,ite_true, if_true,ite_false, if_false,true_and,false_and]
  rw [ht,tsum_fintype]
  apply Finset.sum_congr rfl
  intro e _
  have hi : e∈(G.restrictEdges s).incidentEdges ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) ↔
      e.val∈G.incidentEdges (G.cluster (s∩ω) x) := by
    rw [FiniteClusters.restrict_cluster]
    rfl
  rw [hi]
  unfold centeredCoefficient
  simp only [Set.mem_preimage]
  split_ifs <;> ring

lemma norm_restrictedWeightedTerm_le (s : Set E) (p : ℝ) (hp : p∈Icc 0 1)
    (ω : Set E) (x : V) (e : E) :
    ‖G.restrictedWeightedTerm s p ω x e‖ ≤
      (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
  unfold restrictedWeightedTerm
  by_cases he : e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x)
  · have hi : e∈G.incidentEdges (G.cluster ω x) := by
      obtain ⟨v,hv,hve⟩ := he.2
      exact ⟨v,G.cluster_mono Set.inter_subset_right x hv,hve⟩
    rw [ite_eq_left he,ite_eq_left hi,Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_centeredCoefficient_le_one p hp ω e)
  · rw [ite_eq_right he,norm_zero]
    exact ENNReal.toReal_nonneg

lemma eventually_restrictedWeightedTerm (K : Set.FiniteExhaustion (Set.univ : Set E))
    (p : ℝ) (ω : Set E) (x : V) (e : E) :
    ∀ᶠ n in atTop, G.restrictedWeightedTerm (K n) p ω x e=G.weightedIncidenceTerm p ω x e := by
  by_cases he : e∈G.incidentEdges (G.cluster ω x)
  · obtain ⟨v,hv,hve⟩ := he
    obtain ⟨s,hs,hsω,hvs⟩ := G.mem_cluster_finite_witness hv
    obtain ⟨n,hn⟩ := finite_subset_exhaustion K (hs.insert e) (Set.subset_univ _)
    apply eventually_atTop.mpr
    refine ⟨n,fun m hm => ?_⟩
    have heK : e∈K m := K.mono hm (hn (Set.mem_insert e s))
    have hsK : s⊆K m := fun a ha => K.mono hm (hn (Set.mem_insert_of_mem e ha))
    have hem : e∈G.incidentEdges (G.cluster (K m∩ω) x) :=
      ⟨v,G.cluster_mono (Set.subset_inter hsK hsω) x hvs,hve⟩
    have hefull : e∈G.incidentEdges (G.cluster ω x) := ⟨v,hv,hve⟩
    simp only [restrictedWeightedTerm,weightedIncidenceTerm,heK,hem,hefull,true_and,ite_true, if_true]
  · apply Eventually.of_forall
    intro n
    have hen : ¬(e∈K n ∧ e∈G.incidentEdges (G.cluster (K n∩ω) x)) := by
      rintro ⟨_,v,hv,hve⟩
      exact he ⟨v,G.cluster_mono Set.inter_subset_right x hv,hve⟩
    simp only [restrictedWeightedTerm,weightedIncidenceTerm,ite_eq_right hen,ite_eq_right he]

theorem tendsto_restrictedWeightedDiscrepancy (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1)
    (L : Set.FiniteExhaustion (Set.univ : Set E)) (ω : Set E) (x : V)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.restrictedWeightedDiscrepancy (L n) p ω x) atTop
      (𝓝 (G.weightedDiscrepancy p ω x)) := by
  apply tendsto_tsum_of_dominated_convergence
    (G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm)
  · intro e
    apply tendsto_const_nhds.congr'
    filter_upwards [G.eventually_restrictedWeightedTerm L p ω x e] with n hn
    exact hn.symm
  · exact Eventually.of_forall (fun n e => G.norm_restrictedWeightedTerm_le (L n) p hp ω x e)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedPeakBand
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
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] in
lemma measurable_restrictedWeightedDiscrepancy (s : Set E) [Fintype s] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.restrictedWeightedDiscrepancy s p ω x) := by
  simp only [G.restrictedWeightedDiscrepancy_eq_tree]
  exact (measurable_of_finite (fun η : Set s =>
    (IncidenceSearch.tree (G.restrictEdges s) x).weightedSum
      (fun e : s => (G.bondWeight x e.val).toReal) p η)).comp
    (Measurable.of_eval (fun edge : s => measurable_set_mem edge.val))

theorem expected_discrepancy_peakBand_fourth_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval)
    (T U : ℝ) (hT : 0<T) (hU : 0≤U) (x : V) :
    (∫⁻ ω, ENNReal.ofReal |G.weightedDiscrepancy p ω x| *
      G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p)^4 ≤
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*U)^2)*
        (∫⁻ ω, G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p)^3 := by
  classical
  let L := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let (n : ℕ) : Fintype (L n) := (L.finite n).fintype
  let h : Set E → ℝ≥0∞ := fun ω => G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x
  have hsupport (ω : Set E) (hh : h ω≠0) :=
    G.peakVolumeBand_support hc hl (ENNReal.ofReal T) (ENNReal.ofReal U)
      (ENNReal.ofReal_pos.mpr hT) ω x hh
  have hcost (n : ℕ) (ω : Set E) (hh : h ω≠0) :
      (IncidenceSearch.tree (G.restrictEdges (L n)) x).quadraticCost
        (fun e : L n => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω) ≤ (D*(2*K)^2 : ℕ)*U := by
    let := (L.finite n).fintype
    exact G.restriction_quadratic_real_le hc hl D K hD hK (L n) ω x
      (hsupport ω hh).1 U hU (hsupport ω hh).2.2.le
  let f : ℕ → Set E → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal |G.restrictedWeightedDiscrepancy (L n) p ω x| * h ω
  apply lintegral_fourth_bound_of_tendsto (G.law p) f
    (fun ω => ENNReal.ofReal |G.weightedDiscrepancy p ω x| * h ω) _
  · intro n
    let := (L.finite n).fintype
    exact (G.measurable_restrictedWeightedDiscrepancy (L n) p x).norm.ennreal_ofReal.mul
      (G.measurable_peakVolumeBand _ _ x)
  · intro ω
    by_cases hh : h ω=0
    · simpa only [f,hh,mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
    · have hm : G.modularMass x (G.cluster ω x)≠∞ :=
        ne_top_of_lt ((hsupport ω hh).2.2.trans_le (le_top))
      exact ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal
        ((G.tendsto_restrictedWeightedDiscrepancy hc hl D K hD hK p p.2 L ω x hm).abs))
        (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top (G.peakVolumeBand_le_one _ _ ω x)))
  · intro n
    let := (L.finite n).fintype
    have hn := @SearchTree.restricted_weighted_event_fourth E (IncidenceSearch.State (L n)) (L n) _ (Classical.decEq _)
      (fun e : L n => (G.bondWeight x e.val).toReal)
      (IncidenceSearch.tree (G.restrictEdges (L n)) x) (IncidenceSearch.tree_valid _ _) p
      ((D*(2*K)^2 : ℕ)*U) (by positivity) h (G.measurable_peakVolumeBand _ _ x)
      (fun ω => G.peakVolumeBand_le_one _ _ ω x) (hcost n)
    simpa only [f,G.restrictedWeightedDiscrepancy_eq_tree,BernoulliProduct.law_const,BondGraph.law] using hn

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth_oai.{u_1, u_2}
