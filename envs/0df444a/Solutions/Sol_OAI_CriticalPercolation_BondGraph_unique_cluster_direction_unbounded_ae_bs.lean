-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:58:22.857792+00:00
-- url     : https://prove2.me/submissions/5c7990fa-3916-48d7-b053-bdf68ba1f788

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_subexponential_adjacent_bound_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_uniform_rooted_probability_bs

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)

lemma measurable_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact Measurable.of_eval fun vertex => G.measurable_reachable v vertex

lemma measurable_infinite_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => (G.cluster ω v).Infinite) := by
  simp_rw [← Set.encard_eq_top_iff]
  exact (measurable_encard.comp (G.measurable_cluster v)).eq_const ⊤

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

lemma bitMeasure_real_singleton (p : unitInterval) (b : Prop) :
    (bitMeasure p).real {b} = bitWeight p b := by
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma measurableSet_infiniteEvent [Countable V] [Countable E] (o : V) :
    MeasurableSet (G.infiniteEvent o) := (G.measurable_infinite_cluster o).setOf

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infiniteEvent_subset_clusterTail (o : V) (n : ℕ) :
    G.infiniteEvent o ⊆ G.clusterTail o n := by
  intro ω hω
  obtain ⟨K, hKω, hK, hn⟩ := hω.exists_subset_ncard_eq n
  exact ⟨K, hK, hKω, hn.ge⟩

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_WitnessEvents
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma twoClusterEvent_comm (u v : V) (s : ℕ) :
    G.twoClusterEvent u v s = G.twoClusterEvent v u s := by
  ext ω
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h,hu⟩,hv⟩
    exact ⟨⟨fun hc => h hc.symm,hv⟩,hu⟩
  · rintro ⟨⟨h,hv⟩,hu⟩
    exact ⟨⟨fun hc => h hc.symm,hu⟩,hv⟩

lemma twoClusterEvent_sym2 {u v x y : V} (h : s(u,v)=s(x,y)) (s : ℕ) :
    G.twoClusterEvent u v s = G.twoClusterEvent x y s := by
  rcases Sym2.eq_iff.mp h with h | h
  · rcases h with ⟨rfl,rfl⟩; rfl
  · rcases h with ⟨rfl,rfl⟩; exact G.twoClusterEvent_comm _ _ _

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_InfiniteUniquenessGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_distinctInfiniteEvent [Countable V] [Countable E] (x y : V) :
    MeasurableSet (G.distinctInfiniteEvent x y) :=
  ((G.measurable_infinite_cluster x).and
    ((G.measurable_infinite_cluster y).and (G.measurable_reachable x y).not)).setOf

lemma distinctInfiniteEvent_subset_twoClusterEvent (x y : V) (s : ℕ) :
    G.distinctInfiniteEvent x y ⊆ G.twoClusterEvent x y s := by
  rintro ω ⟨hx,hy,hxy⟩
  exact ⟨⟨hxy,G.infiniteEvent_subset_clusterTail x s hx⟩,
    G.infiniteEvent_subset_clusterTail y s hy⟩

lemma cluster_insert_edge_unchanged (ω : Set E) (e : E) (o : V)
    (hends : ∀ v ∈ G.ends e, v ∉ G.cluster ω o) :
    G.cluster (insert e ω) o = G.cluster ω o := by
  apply Set.Subset.antisymm
  · intro y hy
    have hr := ((G.openGraph (insert e ω)).reachable_iff_reflTransGen o y).mp hy
    clear hy
    induction hr with
    | refl => exact .refl _
    | @tail x y hr hxy ih =>
      obtain ⟨⟨f,hf,hfe⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
      rcases hf with rfl | hf
      · exact False.elim (hends x (by simp [hfe]) ih)
      · have hadj : (G.openGraph ω).Adj x y :=
          (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨f,hf,hfe⟩,hne⟩
        exact ih.trans hadj.reachable
  · exact G.cluster_mono (Set.subset_insert e ω) o

lemma distinctInfinite_force_adjacent_length (n : ℕ) :
    ∀ (ω : Set E) (x y : V), lengthReach G.fullGraph n x y →
      ω ∈ G.distinctInfiniteEvent x y →
      ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
        S ∪ ω ∈ G.distinctInfiniteEvent a b := by
  induction n with
  | zero =>
    intro ω x y hxy h
    exact False.elim (h.2.2 (hxy ▸ SimpleGraph.Reachable.refl x))
  | succ n ih =>
    rintro ω x y ⟨u,hxu,huy⟩ ⟨hx,hy,hxy⟩
    by_cases hxuω : (G.openGraph ω).Reachable x u
    · refine ⟨∅,Set.finite_empty,u,y,huy,?_⟩
      rw [Set.empty_union]
      refine ⟨?_,hy,fun huy => hxy (hxuω.trans huy)⟩
      rwa [← G.cluster_eq_of_reachable hxuω]
    · obtain ⟨⟨e,_,he⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huy
      have hends : ∀ v ∈ G.ends e, v ∉ G.cluster ω x := by
        intro v hv
        rw [he,Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact hxuω
        · exact hxy
      have hc := G.cluster_insert_edge_unchanged ω e x hends
      have hnewx : (G.cluster (insert e ω) x).Infinite := hc ▸ hx
      have hay : (G.openGraph (insert e ω)).Adj u y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_insert e ω,he⟩,hne⟩
      have hnewu : (G.cluster (insert e ω) u).Infinite := by
        have hh := hy.mono (G.cluster_mono (Set.subset_insert e ω) y)
        rwa [← G.cluster_eq_of_reachable hay.reachable] at hh
      have hnot : ¬ (G.openGraph (insert e ω)).Reachable x u := by
        change u ∉ G.cluster (insert e ω) x
        rwa [hc]
      obtain ⟨S,hS,a,b,hab,hhab⟩ := ih (insert e ω) x u hxu ⟨hnewx,hnewu,hnot⟩
      refine ⟨insert e S,hS.insert e,a,b,hab,?_⟩
      simpa only [Set.insert_union,Set.union_insert] using hhab

lemma distinctInfinite_force_adjacent (hconnected : G.fullGraph.Connected)
    (ω : Set E) (x y : V) (h : ω ∈ G.distinctInfiniteEvent x y) :
    ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
      S ∪ ω ∈ G.distinctInfiniteEvent a b := by
  obtain ⟨n,hn⟩ := (reachable_iff_exists_lengthReach G.fullGraph x y).mp (hconnected x y)
  exact G.distinctInfinite_force_adjacent_length n ω x y hn h

theorem adjacent_distinctInfinite_null [Countable V] [Countable E]
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hg : G.SubexponentialGrowth)
    (p : unitInterval) (hp : (p:ℝ) ∈ Set.Ioo 0 1) (x y : V)
    (hxy : G.fullGraph.Adj x y) : G.law p (G.distinctInfiniteEvent x y) = 0 := by
  obtain ⟨A,_,hA⟩ := G.subexponential_adjacent_bound_bs hconnected hlocal hquasi hg
  obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  have hbound : ∀ K : ℕ, (G.law p).real (G.distinctInfiniteEvent x y) ≤
      A/((p:ℝ)*(2:ℝ)^K) := by
    intro K
    have hsub := measureReal_mono (G.distinctInfiniteEvent_subset_twoClusterEvent x y (4^K))
      (μ := G.law p)
    have heq : s(x,y) = s((G.ends e).out.1,(G.ends e).out.2) := by
      exact he.symm.trans (G.ends e).out_eq.symm
    rw [G.twoClusterEvent_sym2 heq (4^K)] at hsub
    exact hsub.trans (hA p hp e K)
  have ht : Tendsto (fun K : ℕ => A/((p:ℝ)*(2:ℝ)^K)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop hp.1)
  have hz : (G.law p).real (G.distinctInfiniteEvent x y) = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hbound)) measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_TailProduct
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_eq_infinitePi (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id

lemma independent_coordinates (q : E → unitInterval) :
    iIndep coordinateSigma (law q) := by
  rw [law_eq_infinitePi]
  exact iIndepFun_infinitePi (X := fun _ (b : Prop) => b) (fun _ => measurable_id)

lemma independent_blocks (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl coordinateSigma_le (independent_coordinates q) S

theorem zero_one_of_finite_erasure_invariant (q : E → unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinvariant : ∀ (S : Set E), S.Finite → ∀ ω,
      forceOn S ∅ ω ∈ A ↔ ω ∈ A) : law q A = 0 ∨ law q A = 1 := by
  let mA : MeasurableSpace (Set E) := MeasurableSpace.generateFrom {A}
  have hmA : mA ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) := MeasurableSpace.generateFrom_singleton_le hA
  have hi : ∀ S : Finset E, Indep (blockSigma (S : Set E)) mA (law q) := by
    intro S
    have htail : MeasurableSet[blockSigma (S : Set E)ᶜ] A := by
      have hh := hA.preimage (measurable_forceOn_block (S : Set E) ∅)
      have heq : forceOn (S : Set E) ∅ ⁻¹' A = A := by
        ext ω
        exact hinvariant _ S.finite_toSet ω
      rwa [heq] at hh
    exact indep_of_indep_of_le_right (independent_blocks q (S : Set E))
      (MeasurableSpace.generateFrom_singleton_le htail)
  have hd : Directed (· ≤ ·) (fun S : Finset E => blockSigma (S : Set E)) := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩ <;> apply iSup₂_le <;> intro e he
    · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_union_left T he) le_rfl)
    · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_union_right S he) le_rfl)
  have hall : (⨆ S : Finset E, blockSigma (S : Set E)) =
      (Set.instMeasurableSpace : MeasurableSpace (Set E)) := by
    apply le_antisymm (iSup_le fun S => blockSigma_le _)
    change (⨆ e, coordinateSigma e) ≤ _
    apply iSup_le
    intro e
    exact le_iSup_of_le {e} (le_iSup_of_le e
      (le_iSup_of_le (Finset.mem_singleton_self e) le_rfl))
  have h := indep_iSup_of_directed_le hi (fun S => blockSigma_le (S : Set E)) hmA hd
  rw [hall] at h
  exact measure_eq_zero_or_one_of_indepSet_self
    (h.indepSet_of_measurableSet hA (MeasurableSpace.measurableSet_generateFrom (by simp)))

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteEnergy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_coordinate (q : E → unitInterval) (e : E) (b : Prop) :
    law q {ω : Set E | (e ∈ ω) = b} = bitMeasure (q e) {b} := by
  rw [law_eq_infinitePi]
  have h := congrArg (fun μ : Measure Prop => μ {b})
    (Measure.infinitePi_map_eval (fun e => bitMeasure (q e)) e)
  rw [Measure.map_apply (measurable_pi_apply e) (MeasurableSet.singleton b)] at h
  exact h

lemma force_singleton_preimage_null (q : E → unitInterval) (e : E) (σ : Set E)
    (hb : bitMeasure (q e) {e ∈ σ} ≠ 0)
    (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q (forceOn {e} σ ⁻¹' A) = 0 := by
  let B := forceOn {e} σ ⁻¹' A
  let C := {ω : Set E | (e ∈ ω) = (e ∈ σ)}
  have hmC : MeasurableSet[blockSigma {e}] C := by
    have hc : MeasurableSet[coordinateSigma e] C :=
      ⟨{e ∈ σ}, MeasurableSet.singleton _, rfl⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Set.mem_singleton e) le_rfl) :
      coordinateSigma e ≤ blockSigma {e}) _ hc
  have hmB : MeasurableSet[blockSigma ({e} : Set E)ᶜ] B :=
    hA.preimage (measurable_forceOn_block {e} σ)
  have hmul := ((independent_blocks q {e}).indepSet_of_measurableSet hmC hmB).measure_inter_eq_mul
  have hsub : C ∩ B ⊆ A := by
    intro ω hω
    have heq : forceOn {e} σ ω = ω := by
      ext f
      change (if f ∈ ({e} : Set E) then f ∈ σ else f ∈ ω) ↔ f ∈ ω
      by_cases hf : f = e
      · subst f
        simpa only [Set.mem_singleton_iff, ↓reduceIte] using (Iff.of_eq hω.1.symm)
      · simp only [Set.mem_singleton_iff, ite_eq_right hf]
    have hh : forceOn {e} σ ω ∈ A := hω.2
    rwa [heq] at hh
  have hz : law q (C ∩ B) = 0 := measure_mono_null hsub hnull
  rw [hz, law_coordinate] at hmul
  exact (mul_eq_zero.mp hmul.symm).resolve_left hb

lemma bitMeasure_true_ne_zero (p : unitInterval) (hp : (0:ℝ) < p) :
    bitMeasure p {True} ≠ 0 := by
  have hh := bitMeasure_real_singleton p True
  simp only [bitWeight, if_true] at hh
  intro hz
  have : (bitMeasure p).real {True} = 0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  rw [hh] at this
  exact (ne_of_gt hp) this

lemma insert_preimage_null (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (e : E) (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q ((fun ω => insert e ω) ⁻¹' A) = 0 := by
  have hh := force_singleton_preimage_null q e Set.univ (bitMeasure_true_ne_zero (q e) (hq e))
    A hA hnull
  have heq : forceOn {e} Set.univ = (fun ω : Set E => insert e ω) := by
    funext ω
    ext f
    change (if f ∈ ({e} : Set E) then True else f ∈ ω) ↔ (f = e ∨ f ∈ ω)
    simp only [Set.mem_singleton_iff]
    split_ifs <;> tauto
  rwa [heq] at hh

lemma measurable_union_left (S : Set E) : Measurable (fun ω : Set E => S ∪ ω) :=
  Measurable.of_eval (fun edge => measurable_const.or (measurable_set_mem edge))

lemma finite_union_preimage_null (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (S : Set E) (hS : S.Finite) (A : Set (Set E)) (hA : MeasurableSet A)
    (hnull : law q A = 0) : law q ((fun ω => S ∪ ω) ⁻¹' A) = 0 := by
  induction S,hS using Set.Finite.induction_on generalizing A with
  | empty =>
    have hh : (fun ω : Set E => (∅ : Set E) ∪ ω) = id := funext (fun _ => Set.empty_union _)
    rw [hh,Set.preimage_id_eq]
    exact hnull
  | @insert e S he hS ih =>
    have hi := insert_preimage_null q hq e A hA hnull
    have hm : Measurable (fun ω : Set E => insert e ω) := by
      simpa only [Set.singleton_union] using measurable_union_left ({e} : Set E)
    have hh := ih ((fun ω => insert e ω) ⁻¹' A) (hA.preimage hm) hi
    simpa only [Set.preimage_preimage,Function.comp_def,Set.insert_union] using hh

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_InfiniteUniqueness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem atMostOneInfinite_ae (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p:ℝ) ∈ Set.Ioo 0 1) : ∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite := by
  have hn : ∀ (S : Finset E) (x y : V), ∀ᵐ ω ∂G.law p,
      G.fullGraph.Adj x y → (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
    intro S x y
    by_cases hxy : G.fullGraph.Adj x y
    · have hz := BernoulliProduct.finite_union_preimage_null (fun _ : E => p)
        (fun _ => hp.1) (S : Set E) S.finite_toSet (G.distinctInfiniteEvent x y)
        (G.measurableSet_distinctInfiniteEvent x y)
        (by rw [BernoulliProduct.law_const];
            exact G.adjacent_distinctInfinite_null hconnected hlocal hquasi hg p hp x y hxy)
      rw [BernoulliProduct.law_const] at hz
      have hh : ∀ᵐ ω ∂G.law p, (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
        rw [ae_iff]
        simp only [not_not]
        exact hz
      exact hh.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hxy h))
  have hall := ae_all_iff.mpr (fun S => ae_all_iff.mpr (fun x => ae_all_iff.mpr (hn S x)))
  filter_upwards [hall] with ω hω
  intro x y hx hy
  by_contra hxy
  obtain ⟨S,hS,a,b,hab,hh⟩ := G.distinctInfinite_force_adjacent hconnected ω x y ⟨hx,hy,hxy⟩
  have hnot := hω hS.toFinset a b hab
  exact hnot (by simpa only [Set.Finite.coe_toFinset] using hh)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DirectionalTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infiniteVertices_mono {ω τ : Set E} (h : ω⊆τ) :
    G.infiniteVertices ω⊆G.infiniteVertices τ := fun v hv => hv.mono (G.cluster_mono h v)

lemma cluster_union_unchanged (ω S : Set E) (o : V)
    (hends : ∀ e∈S, ∀ v∈G.ends e, v∉G.cluster ω o) :
    G.cluster (ω∪S) o=G.cluster ω o := by
  apply Set.Subset.antisymm
  · intro z hz
    have hr := ((G.openGraph (ω∪S)).reachable_iff_reflTransGen o z).mp hz
    clear hz
    induction hr with
    | refl => exact .refl _
    | @tail x y hr hxy ih =>
      obtain ⟨⟨e,he,hend⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
      rcases he with he|he
      · have hadj : (G.openGraph ω).Adj x y :=
          (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,hend⟩,hne⟩
        exact ih.trans hadj.reachable
      · exact False.elim (hends e he x (by simp [hend]) ih)
  · exact G.cluster_mono Set.subset_union_left o

lemma infiniteVertices_union_finite_error (ω S : Set E) (hS : S.Finite) :
    (G.infiniteVertices (ω∪S)\G.infiniteVertices ω).Finite := by
  let K := ⋃ e∈S, ⋃ v∈(G.ends e).toFinset,
    {x | x∈G.cluster ω v ∧ (G.cluster ω v).Finite}
  have hK : K.Finite := hS.biUnion fun e _ => (G.ends e).toFinset.finite_toSet.biUnion fun v _ => by
    by_cases hv : (G.cluster ω v).Finite
    · exact hv.subset (fun _ h => h.1)
    · have heq : {x | x∈G.cluster ω v ∧ (G.cluster ω v).Finite}=(∅ : Set V) := by
        ext x
        simp [hv]
      rw [heq]
      exact Set.finite_empty
  apply hK.subset
  intro x hx
  have hfin : (G.cluster ω x).Finite := Set.not_infinite.mp hx.2
  by_contra hn
  have hends : ∀ e∈S, ∀ v∈G.ends e, v∉G.cluster ω x := by
    intro e he v hv hvc
    apply hn
    refine Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr ⟨v,?_,hvc.symm,?_⟩⟩
    · simpa only [Sym2.mem_toFinset] using hv
    · rwa [← G.cluster_eq_of_reachable hvc]
  exact hx.1 (by rwa [G.cluster_union_unchanged ω S x hends])

lemma directionUnbounded_mono (f : V → ℝ) : IsUpperSet (G.directionUnbounded f) := by
  intro ω τ h hω n
  obtain ⟨v,hv,hv'⟩ := hω n
  exact ⟨v,hv,G.infiniteVertices_mono h hv'⟩

lemma directionUnbounded_union_finite_iff (f : V → ℝ) (ω S : Set E) (hS : S.Finite) :
    ω∪S∈G.directionUnbounded f ↔ ω∈G.directionUnbounded f := by
  constructor
  · intro h n
    have hK := (G.infiniteVertices_union_finite_error ω S hS).image f
    obtain ⟨M,hM⟩ := hK.bddAbove
    obtain ⟨N,hN⟩ := exists_nat_gt (max M n)
    obtain ⟨v,hv,hinf⟩ := h N
    refine ⟨v,lt_trans (lt_of_le_of_lt (le_max_right M n) hN) hv,?_⟩
    by_contra hnot
    have hfM := hM (Set.mem_image_of_mem f ⟨hinf,hnot⟩)
    have : M<(N : ℝ) := lt_of_le_of_lt (le_max_left M n) hN
    linarith
  · exact G.directionUnbounded_mono f Set.subset_union_left

lemma directionUnbounded_diff_finite_iff (f : V → ℝ) (ω S : Set E) (hS : S.Finite) :
    ω\S∈G.directionUnbounded f ↔ ω∈G.directionUnbounded f := by
  constructor
  · exact G.directionUnbounded_mono f Set.sdiff_subset
  · intro h
    have hs : ω⊆(ω\S)∪S := fun e he => by
      by_cases hh : e∈S
      · exact Or.inr hh
      · exact Or.inl ⟨he,hh⟩
    exact (G.directionUnbounded_union_finite_iff f (ω\S) S hS).mp
      (G.directionUnbounded_mono f hs h)

lemma directionUnbounded_measurable [Countable V] [Countable E] (f : V → ℝ) :
    MeasurableSet (G.directionUnbounded f) := by
  have heq : G.directionUnbounded f=⋂ n : ℕ, ⋃ v∈{v | (n : ℝ)<f v}, G.infiniteEvent v := by
    ext ω
    simp only [directionUnbounded,infiniteVertices,infiniteEvent,Set.mem_ofPred_eq,
      Set.mem_iInter,Set.mem_iUnion,exists_prop]
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.biUnion (Set.to_countable _) fun v _ =>
    G.measurableSet_infiniteEvent v

lemma directionUnbounded_zero_one [Countable V] [Countable E]
    (q : E → unitInterval) (f : V → ℝ) :
    BernoulliProduct.law q (G.directionUnbounded f)=0 ∨
      BernoulliProduct.law q (G.directionUnbounded f)=1 := by
  apply BernoulliProduct.zero_one_of_finite_erasure_invariant q _ (G.directionUnbounded_measurable f)
  intro S hS ω
  have heq : BernoulliProduct.forceOn S ∅ ω=ω\S := by
    ext e
    change (if e∈S then False else e∈ω) ↔ e∈ω ∧ e∉S
    split_ifs <;> tauto
  rw [heq]
  exact G.directionUnbounded_diff_finite_iff f ω S hS

lemma directionUnbounded_positive [Countable V] [Countable E]
    (p : unitInterval) (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v)
    (theta : ℝ) (htheta : 0<theta)
    (hroot : ∀ v, theta≤(G.law p).real (G.infiniteEvent v)) :
    0<G.law p (G.directionUnbounded f) := by
  let A := fun n : ℕ => ⋃ v∈{v | (n : ℝ)<f v}, G.infiniteEvent v
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.biUnion (Set.to_countable _) fun v _ => G.measurableSet_infiniteEvent v
  have hanti : Antitone A := by
    intro n m hnm ω hω
    obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp hω
    exact Set.mem_iUnion₂.mpr ⟨v,(show (n : ℝ)<f v from lt_of_le_of_lt (Nat.cast_le.mpr hnm) hv),hh⟩
  have heq : (⋂ n, A n)=G.directionUnbounded f := by
    ext ω
    simp only [A,directionUnbounded,infiniteVertices,infiniteEvent,Set.mem_ofPred_eq,
      Set.mem_iInter,Set.mem_iUnion,exists_prop]
  have ht := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0,measure_ne_top _ _⟩
  rw [heq] at ht
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  have hbound : ∀ n, theta≤(G.law p).real (A n) := by
    intro n
    obtain ⟨v,hv⟩ := hf n
    have hs : G.infiniteEvent v⊆A n := fun ω hω => Set.mem_iUnion₂.mpr ⟨v,hv,hω⟩
    exact (hroot v).trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hs))
  have hp : 0<(G.law p).real (G.directionUnbounded f) :=
    htheta.trans_le (ge_of_tendsto hreal (Eventually.of_forall hbound))
  exact ENNReal.toReal_pos_iff.mp hp |>.1

theorem directionUnbounded_one [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hpositive : 0<G.law p G.percolates)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    G.law p (G.directionUnbounded f)=1 := by
  obtain ⟨theta,htheta,hroot⟩ := G.uniform_rooted_probability_bs hc hl hq p hpositive
  have hp := G.directionUnbounded_positive p f hf theta htheta hroot
  have hz := G.directionUnbounded_zero_one (fun _ => p) f
  rw [BernoulliProduct.law_const] at hz
  exact hz.resolve_left (ne_of_gt hp)

theorem unique_cluster_direction_unbounded_ae_bs_oai [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p : ℝ)∈Set.Ioo 0 1) (hpositive : 0<G.law p G.percolates)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    ∀ᵐ ω ∂G.law p, ∀ v, (G.cluster ω v).Infinite →
      ∀ n : ℕ, ∃ w∈G.cluster ω v, (n : ℝ)<f w := by
  have hu : ∀ᵐ ω ∂G.law p, ω∈G.directionUnbounded f := by
    rw [ae_iff]
    change G.law p (G.directionUnbounded f)ᶜ=0
    rw [measure_compl (G.directionUnbounded_measurable f) (measure_ne_top _ _),
      G.directionUnbounded_one hc hl hq p hpositive f hf,measure_univ,tsub_self]
  filter_upwards [hu,G.atMostOneInfinite_ae hc hl hq hg p hp] with ω hω huniq
  intro v hv n
  obtain ⟨w,hw,hwinf⟩ := hω n
  exact ⟨w,huniq v w hv hwinf,hw⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs_oai.{u_1, u_2}
