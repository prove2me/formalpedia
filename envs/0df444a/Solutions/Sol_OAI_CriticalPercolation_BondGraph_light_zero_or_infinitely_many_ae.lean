-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:54.43479+00:00
-- url     : https://prove2.me/submissions/99819405-8e38-408c-8af4-9e130db0db13

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_clusterPeaks_finite_of_mass_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_finite_clusterUpperSet_has_peak
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_finite_clusterUpperSet_of_mass_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_pos

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

theorem countable_vertices (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable V := by
  obtain ⟨o⟩ := hconnected.nonempty
  have hc : (⋃ n : ℕ, G.vertexBall o n).Countable :=
    Set.countable_iUnion fun n => (G.vertexBall_finite hlocal o n).countable
  have heq : (⋃ n : ℕ, G.vertexBall o n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n, hn⟩ := G.reachable_mem_vertexBall (hconnected o v)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

theorem countable_bonds (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable E := by
  let := G.countable_vertices hconnected hlocal
  have hc : (⋃ v : V, {e : E | v ∈ G.ends e}).Countable :=
    Set.countable_iUnion fun v => (hlocal v).countable
  have heq : (⋃ v : V, {e : E | v ∈ G.ends e}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    exact Set.mem_iUnion.mpr ⟨(G.ends e).out.1, Sym2.out_fst_mem _⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_image_equiv (e : E ≃ E) :
    Measurable (fun ω : Set E => e '' ω) := by
  have he : (fun ω : Set E => e '' ω) = (fun ω => e.symm ⁻¹' ω) := by
    funext ω
    ext i
    simp
  rw [he]
  exact Measurable.of_eval (fun index => measurable_set_mem (e.symm index))

lemma law_map_equiv (p : unitInterval) (e : E ≃ E) :
    (law (fun _ : E => p)).map (fun ω : Set E => e '' ω) = law (fun _ : E => p) := by
  unfold law
  rw [Measure.map_map (measurable_image_equiv e) MeasurableEquiv.setOfPred.measurable]
  have he : (fun ω : Set E => e '' ω) ∘ MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ MeasurableEquiv.piCongrLeft (fun _ : E => Prop) e := by
    funext ω
    ext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_piCongrLeft (fun _ : E => bitMeasure p) e]

end CriticalPercolation.BernoulliProduct
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

lemma law_map_aut (p : unitInterval) (φ : G.Aut) :
    (G.law p).map (fun ω : Set E => φ.edge '' ω) = G.law p := by
  simpa only [BernoulliProduct.law_const, law] using
    BernoulliProduct.law_map_equiv p φ.edge

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphBalls
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
variable {V E : Type*} (G : BondGraph V E)

lemma orbit_density_radius (hconnected : G.fullGraph.Connected)
    (hquasi : G.QuasiTransitive) (u : V) :
    ∃ C : ℕ, ∀ v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  have hpath : ∀ z : S, ∃ n, u ∈ G.vertexBall z.val n :=
    fun z => G.reachable_mem_vertexBall (hconnected z u)
  choose n hn using hpath
  let := hS.fintype
  let C := ∑ z : S, n z
  refine ⟨C,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  refine ⟨φ,(Aut.vertexBall_mem G φ z u C).mpr ?_⟩
  exact G.vertexBall_mono z (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨z,hz⟩ : S))) (hn ⟨z,hz⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_AutDisplacement
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma aut_moves_vertex_outside_ball [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (R : ℕ) :
    ∃ φ : G.Aut, φ.vertex o ∉ G.vertexBall o R := by
  obtain ⟨C,hC⟩ := G.orbit_density_radius hc hq o
  obtain ⟨v,hv⟩ := (G.vertexBall_finite hl o (R+C)).exists_notMem
  obtain ⟨φ,hφ⟩ := hC v
  refine ⟨φ,fun h => hv ?_⟩
  exact G.vertexBall_add h C (G.vertexBall_comm.mp hφ)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_InvariantFiniteSets
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma vertex_aut_orbit_infinite [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (v : V) :
    (Set.range (fun φ : G.Aut => φ.vertex v)).Infinite := by
  intro hf
  obtain ⟨R,hR⟩ := G.finite_subset_vertexBall hc v hf
  obtain ⟨φ,hφ⟩ := G.aut_moves_vertex_outside_ball hc hl hq v R
  exact hφ (hR ⟨φ,rfl⟩)

lemma bounded_invariant_marks_null [Infinite V] [Countable V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (M : Set E → V → Prop)
    (hm : ∀ v, Measurable (fun ω => M ω v))
    (ha : ∀ (φ : G.Aut) ω v, M (φ.edge '' ω) (φ.vertex v) ↔ M ω v)
    (N : ℕ) (hb : ∀ ω, ∃ S : Finset V, S.card≤N ∧ ∀ v, M ω v → v∈S) (v : V) :
    G.law p {ω | M ω v}=0 := by
  have hmeas (x : V) : Measurable (fun ω => if M ω x then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite (hm x).setOf measurable_const
  have he (x : V) : (∫⁻ ω, if M ω x then (1:ℝ≥0∞) else 0 ∂G.law p) =
      G.law p {ω | M ω x} := by
    simpa only [Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
      (lintegral_indicator_one (μ := G.law p) (hm x).setOf)
  have hpoint (ω : Set E) : (∑' x, if M ω x then (1:ℝ≥0∞) else 0) ≤ N := by
    obtain ⟨S,hS,hcover⟩ := hb ω
    calc
      _ ≤ ∑' x, if x∈S then (1:ℝ≥0∞) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro x
        split_ifs with hx hs
        · rfl
        · exact False.elim (hs (hcover x hx))
        · exact zero_le
        · rfl
      _ = (S.card:ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun x hx => ite_eq_right hx)]
        simp
      _ ≤ N := by exact_mod_cast hS
  have hsum : (∑' x, G.law p {ω | M ω x}) ≤ N := by
    calc
      _ = ∫⁻ ω, ∑' x, if M ω x then (1:ℝ≥0∞) else 0 ∂G.law p := by
        rw [lintegral_tsum (fun x => (hmeas x).aemeasurable)]
        simp only [he]
      _ ≤ ∫⁻ _ : Set E, (N:ℝ≥0∞) ∂G.law p := lintegral_mono hpoint
      _ = N := by simp
  have hinv (φ : G.Aut) : G.law p {ω | M ω (φ.vertex v)} = G.law p {ω | M ω v} := by
    conv_lhs => rw [←G.law_map_aut p φ]
    rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge) (hm _).setOf]
    congr 1
    ext ω
    exact ha φ ω v
  by_contra hn
  have hf := ENNReal.finite_const_le_of_tsum_ne_top
    ((hsum.trans_lt (ENNReal.natCast_lt_top N)).ne) hn
  apply G.vertex_aut_orbit_infinite hc hl hq v
  apply hf.subset
  rintro x ⟨φ,rfl⟩
  change G.law p {ω | M ω v} ≤ G.law p {ω | M ω (φ.vertex v)}
  rw [hinv]

lemma measurable_vertexSetBound [Countable V] (A : Set E → Set V)
    (hm : ∀ v, Measurable (fun ω => v∈A ω)) (N : ℕ) :
    Measurable (G.vertexSetBound A N) := by
  exact .exists fun S : Finset V => measurable_const.and
    (.forall fun v => (hm v).imp measurable_const)

lemma vertexSetBound_aut (A : Set E → Set V)
    (ha : ∀ (φ : G.Aut) ω, A (φ.edge '' ω)=φ.vertex '' A ω)
    (N : ℕ) (φ : G.Aut) (ω : Set E) :
    G.vertexSetBound A N (φ.edge '' ω) ↔ G.vertexSetBound A N ω := by
  change (∃ S : Finset V, S.card≤N ∧ A (φ.edge '' ω)⊆S) ↔ _
  rw [ha]
  constructor
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex.symm,Finset.card_image_le.trans hS,?_⟩
    intro x hx
    exact Finset.mem_image.mpr ⟨φ.vertex x,h ⟨x,hx,rfl⟩,φ.vertex.symm_apply_apply x⟩
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex,Finset.card_image_le.trans hS,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact Finset.mem_image.mpr ⟨x,h hx,rfl⟩

theorem invariant_finite_vertex_set_empty_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (A : Set E → Set V)
    (hm : ∀ v, Measurable (fun ω => v∈A ω))
    (ha : ∀ (φ : G.Aut) ω, A (φ.edge '' ω)=φ.vertex '' A ω) :
    ∀ᵐ ω ∂G.law p, (A ω).Finite → A ω=∅ := by
  let := G.countable_vertices hc hl
  have hn (N : ℕ) (v : V) : ∀ᵐ ω ∂G.law p, ¬(G.vertexSetBound A N ω ∧ v∈A ω) := by
    rw [ae_iff]
    simp only [not_not]
    apply G.bounded_invariant_marks_null hc hl hq p
      (fun ω v => G.vertexSetBound A N ω ∧ v∈A ω)
      (fun v => (G.measurable_vertexSetBound A hm N).and (hm v))
      (fun φ ω v => by
        rw [G.vertexSetBound_aut A ha N φ ω,ha]
        simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]) N
    intro ω
    by_cases hh : G.vertexSetBound A N ω
    · obtain ⟨S,hS,hcover⟩ := hh
      exact ⟨S,hS,fun x hx => hcover hx.2⟩
    · exact ⟨∅,Nat.zero_le N,fun x hx => (hh hx.1).elim⟩
  have hall : ∀ᵐ ω ∂G.law p, ∀ N : ℕ, ∀ v : V,
      ¬(G.vertexSetBound A N ω ∧ v∈A ω) :=
    ae_all_iff.mpr (fun N => ae_all_iff.mpr (hn N))
  filter_upwards [hall] with ω hω hf
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact hω hf.toFinset.card v ⟨⟨hf.toFinset,le_rfl,fun _ hx => hf.mem_toFinset.mpr hx⟩,hv⟩

end CriticalPercolation.BondGraph
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

lemma measurableSet_lightInfiniteEvent [Countable V] [Countable E] (o v : V) :
    MeasurableSet (G.lightInfiniteEvent o v) := by
  exact (G.measurable_infinite_cluster v).setOf.inter
    (measurableSet_lt (G.measurable_modularClusterMass o v) measurable_const)

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

lemma measurable_clusterPeak [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeak ω x) := by
  exact .forall (fun z => (G.measurable_reachable x z).imp measurable_const)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularSuperlevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma clusterPeaks_nonempty_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hm : G.modularMass v (G.cluster ω v) ≠ ∞) :
    (G.clusterPeaks ω v).Nonempty := by
  obtain ⟨y,hy,hp,_⟩ := G.finite_clusterUpperSet_has_peak hc hl ω v
    (G.finite_clusterUpperSet_of_mass_ne_top hm)
  exact ⟨y,hy,hp⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_LightClusterNumber
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma lightInfiniteEvent_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {ω : Set E} {v x : V} (hx : (G.openGraph ω).Reachable v x)
    (hv : ω∈G.lightInfiniteEvent v v) : ω∈G.lightInfiniteEvent x x := by
  change (G.cluster ω x).Infinite ∧ G.modularMass x (G.cluster ω x)<∞
  have he := G.cluster_eq_of_reachable hx
  rw [←he]
  refine ⟨hv.1,?_⟩
  rw [lt_top_iff_ne_top]
  intro h
  exact hv.2.ne ((G.modularMass_eq_top_change_base hc hl v x _).mpr h)

lemma Aut.lightInfiniteEvent_self_iff (φ : G.Aut) (ω : Set E) (v : V) :
    φ.edge '' ω∈G.lightInfiniteEvent (φ.vertex v) (φ.vertex v) ↔
      ω∈G.lightInfiniteEvent v v := by
  change (_ ∧ _<∞) ↔ (_ ∧ _<∞)
  rw [←φ.cluster_image,φ.modularMass_image]
  exact and_congr (Set.infinite_image_iff φ.vertex.injective.injOn) Iff.rfl

lemma measurable_lightInfinitePeaks [Countable V] [Countable E] (v : V) :
    Measurable (fun ω => v∈G.lightInfinitePeaks ω) :=
  (G.measurableSet_lightInfiniteEvent v v).mem.and (G.measurable_clusterPeak v)

lemma lightInfinitePeaks_aut (φ : G.Aut) (ω : Set E) :
    G.lightInfinitePeaks (φ.edge '' ω)=φ.vertex '' G.lightInfinitePeaks ω := by
  ext y
  obtain ⟨v,rfl⟩ := φ.vertex.surjective y
  simp only [lightInfinitePeaks,Set.mem_ofPred_eq,φ.lightInfiniteEvent_self_iff,
    φ.clusterPeak_iff,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

lemma lightInfinitePeaks_finite_of_cover (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (S : Set V) (hS : S.Finite) (hcover : G.lightClusterCover ω S) :
    (G.lightInfinitePeaks ω).Finite := by
  let T := {s∈S | ω∈G.lightInfiniteEvent s s}
  have hT : T.Finite := hS.subset (fun _ hx => hx.1)
  refine (hT.biUnion (fun s hs => G.clusterPeaks_finite_of_mass_ne_top hc hl ω s hs.2.2.ne)).subset ?_
  intro v hv
  obtain ⟨s,hs,hvs⟩ := hcover v hv.1
  exact Set.mem_iUnion₂.mpr ⟨s,⟨hs,G.lightInfiniteEvent_of_reachable hc hl hvs hv.1⟩,hvs.symm,hv.2⟩

lemma lightInfinitePeaks_nonempty (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hv : ω∈G.lightInfiniteEvent v v) :
    (G.lightInfinitePeaks ω).Nonempty := by
  obtain ⟨x,hx,hpeak⟩ := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω v hv.2.ne
  exact ⟨x,G.lightInfiniteEvent_of_reachable hc hl hx hv,hpeak⟩

lemma infinitelyManyLightClusters_iff_no_finite_cover (ω : Set E) :
    G.infinitelyManyLightClusters ω ↔ ∀ S : Finset V, ¬G.lightClusterCover ω (S : Set V) := by
  simp only [infinitelyManyLightClusters,lightClusterCover]
  push Not
  rfl

theorem light_zero_or_infinitely_many_ae_oai [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    ∀ᵐ ω ∂G.law p, (∃ v, ω∈G.lightInfiniteEvent v v) → G.infinitelyManyLightClusters ω := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hh := G.invariant_finite_vertex_set_empty_ae hc hl hq p G.lightInfinitePeaks
    G.measurable_lightInfinitePeaks G.lightInfinitePeaks_aut
  filter_upwards [hh] with ω hω ⟨v,hv⟩
  rw [G.infinitelyManyLightClusters_iff_no_finite_cover]
  intro S hS
  have hf := G.lightInfinitePeaks_finite_of_cover hc hl ω (S : Set V) S.finite_toSet hS
  have hn := G.lightInfinitePeaks_nonempty hc hl ω v hv
  rw [hω hf] at hn
  exact Set.not_nonempty_empty hn

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.light_zero_or_infinitely_many_ae_oai.{u_1, u_2}
