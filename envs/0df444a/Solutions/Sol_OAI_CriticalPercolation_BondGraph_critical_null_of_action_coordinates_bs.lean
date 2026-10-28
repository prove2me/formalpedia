-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:47:09.200393+00:00
-- url     : https://prove2.me/submissions/8f169136-7651-455d-bfff-8a167f3ff89d

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_critical_strip_null_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_ellipse_critical_contradiction_bs

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

theorem percolates_mono {ω ω' : Set E} (h : ω ⊆ ω')
    (hω : ω ∈ G.percolates) : ω' ∈ G.percolates := by
  obtain ⟨v, hv⟩ := hω
  exact ⟨v, hv.mono (G.cluster_mono h v)⟩

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

theorem measurableSet_percolates [Countable V] [Countable E] :
    MeasurableSet G.percolates := by
  exact (Measurable.exists fun v => G.measurable_infinite_cluster v).setOf

theorem percolates_null_iff [Countable V] (μ : Measure (Set E)) :
    μ G.percolates = 0 ↔ ∀ v, μ {ω | (G.cluster ω v).Infinite} = 0 := by
  have heq : G.percolates = ⋃ v, {ω | (G.cluster ω v).Infinite} := by
    ext ω
    simp [percolates]
  rw [heq, measure_iUnion_null_iff]

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

lemma finite_subset_cluster_finite_witness {ω : Set E} {v : V} {K : Set V}
    (hK : K.Finite) (hKv : K ⊆ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ K ⊆ G.cluster s v := by
  classical
  have h : ∀ w ∈ K, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v :=
    fun w hw => G.mem_cluster_finite_witness (hKv hw)
  choose s hs hsω hws using h
  let := hK.fintype
  refine ⟨⋃ w : K, s w w.property, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun w => hs w w.property
  · exact Set.iUnion_subset fun w => hsω w w.property
  · intro w hw
    exact G.cluster_mono (Set.subset_iUnion (fun w : K => s w w.property) ⟨w, hw⟩)
      v (hws w hw)

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype A] in
lemma density_nonneg {w : E → A → ℝ} (h : ∀ e a, 0 ≤ w e a) (ω : E → A) :
    0 ≤ density w ω := Finset.prod_nonneg fun e _ => h e (ω e)

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

lemma expect_mono {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f g : (E → A) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g := by
  classical
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (density_nonneg hw ω)

lemma expect_mul_const (w : E → A → ℝ) (f : (E → A) → ℝ) (c : ℝ) :
    expect w (fun ω => f ω * c) = expect w f * c := by
  classical
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  ring

end CriticalPercolation.FiniteProduct

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

lemma bitWeight_sum (p : unitInterval) : ∑ b, bitWeight p b = 1 := by
  simp [bitWeight]

lemma bitWeight_nonneg (p : unitInterval) (b : Prop) : 0 ≤ bitWeight p b := by
  unfold bitWeight
  split_ifs
  · exact p.property.1
  · exact sub_nonneg.mpr p.property.2

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

lemma integral_bits_eq_expect [Fintype E] (q : E → unitInterval) (f : (E → Prop) → ℝ) :
    (∫ ω, f ω ∂(Measure.infinitePi fun e => bitMeasure (q e))) =
      FiniteProduct.expect (fun e => bitWeight (q e)) f := by
  rw [Measure.infinitePi_eq_pi, integral_fintype Integrable.of_finite]
  unfold FiniteProduct.expect FiniteProduct.density
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_eq_mul]
  congr 1
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun e _ => bitMeasure_real_singleton (q e) (ω e))

lemma integral_law_eq_expect [Fintype E] (q : E → unitInterval) (f : Set E → ℝ) :
    (∫ ω, f ω ∂law q) =
      FiniteProduct.expect (fun e => bitWeight (q e)) (fun ω => f {e | ω e}) := by
  rw [law, integral_map MeasurableEquiv.setOfPred.measurable.aemeasurable
    Integrable.of_finite.aestronglyMeasurable, integral_bits_eq_expect]
  rfl

lemma law_map_restrict (q : E → unitInterval) (s : Set E) :
    (law q).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) =
      law (fun e : s => q e) := by
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_set_iff.mpr (fun bond => measurable_set_mem bond.val)
  unfold law
  rw [Measure.map_map hmeas MeasurableEquiv.setOfPred.measurable]
  have hcomp : (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) ∘
      MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ s.domRestrict := rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_restrict']

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphBalls
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma Aut.incident_singleton_image (φ : G.Aut) (v : V) :
    φ.edge '' G.incidentEdges {v} = G.incidentEdges {φ.vertex v} := by
  ext e
  obtain ⟨f,rfl⟩ := φ.edge.surjective e
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,incidentEdges,
    Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left,φ.preserves]
  simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]

lemma uniform_incident_bound (hquasi : G.QuasiTransitive) :
    ∃ D : ℕ, 1≤D ∧ ∀ v, (G.incidentEdges {v}).ncard ≤ D := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  let D := 1 + ∑ v ∈ hS.toFinset, (G.incidentEdges {v}).ncard
  refine ⟨D,by dsimp [D]; omega,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [← Aut.incident_singleton_image G φ,Set.ncard_image_of_injective _ φ.edge.injective]
  exact (Finset.single_le_sum (f := fun v => (G.incidentEdges {v}).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)).trans (Nat.le_add_left _ _)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_ActionCoordinates
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V]
variable (α : Λ → G.Aut) (hα : ∀ g x, (α g).vertex x=g • x)

include α hα in
lemma action_orbit_dense (hc : G.fullGraph.Connected) (S : Set V) (hS : S.Finite)
    (hcover : ∀ x, ∃ s∈S, ∃ g : Λ, g • s=x) (o : V) :
    ∃ c : ℕ, ∀ y, ∃ g : Λ, g • o∈G.vertexBall y c := by
  obtain ⟨c,hc'⟩ := G.finite_subset_vertexBall hc o hS
  refine ⟨c,?_⟩
  intro y
  obtain ⟨s,hs,g,rfl⟩ := hcover y
  refine ⟨g,?_⟩
  rw [←hα g o,←hα g s,Aut.vertexBall_mem]
  exact G.vertexBall_comm.mp (hc' hs)

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_PercolationTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_union_subset (ω S : Set E) (o : V) :
    G.cluster (ω ∪ S) o ⊆ G.cluster ω o ∪
      ⋃ e ∈ S, ⋃ v ∈ (G.ends e).toFinset, G.cluster ω v := by
  intro z hz
  have hr := ((G.openGraph (ω ∪ S)).reachable_iff_reflTransGen o z).mp hz
  clear hz
  induction hr with
  | refl => exact Or.inl (.refl _)
  | @tail x y hr hxy ih =>
    obtain ⟨⟨e, he, heq⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    rcases he with he | he
    · have hadj : (G.openGraph ω).Adj x y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩
      rcases ih with ho | h
      · exact Or.inl (ho.trans hadj.reachable)
      · obtain ⟨f,hf,h⟩ := Set.mem_iUnion₂.mp h
        obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp h
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,Set.mem_iUnion₂.mpr
          ⟨v,hv,hh.trans hadj.reachable⟩⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr
        ⟨y,by simp [heq], .refl _⟩⟩)

lemma percolates_union_finite_iff (ω S : Set E) (hS : S.Finite) :
    ω ∪ S ∈ G.percolates ↔ ω ∈ G.percolates := by
  constructor
  · rintro ⟨o,ho⟩
    by_contra hω
    have hfinite : ∀ v, (G.cluster ω v).Finite :=
      fun v => Set.not_infinite.mp (fun hv => hω ⟨v,hv⟩)
    exact ho (((hfinite o).union (hS.biUnion fun e _ =>
      (G.ends e).toFinset.finite_toSet.biUnion fun v _ => hfinite v)).subset
        (G.cluster_union_subset ω S o))
  · exact G.percolates_mono Set.subset_union_left

lemma percolates_diff_finite_iff (ω S : Set E) (hS : S.Finite) :
    ω \ S ∈ G.percolates ↔ ω ∈ G.percolates := by
  constructor
  · exact G.percolates_mono Set.sdiff_subset
  · intro hω
    have hh := G.percolates_mono (show ω ⊆ (ω \ S) ∪ S from
      fun e he => by by_cases hs : e ∈ S; exact Or.inr hs; exact Or.inl ⟨he,hs⟩) hω
    exact (G.percolates_union_finite_iff (ω \ S) S hS).mp hh

theorem percolates_zero_one [Countable V] [Countable E] (q : E → unitInterval) :
    BernoulliProduct.law q G.percolates = 0 ∨
      BernoulliProduct.law q G.percolates = 1 := by
  apply BernoulliProduct.zero_one_of_finite_erasure_invariant q G.percolates
    G.measurableSet_percolates
  intro S hS ω
  have heq : BernoulliProduct.forceOn S ∅ ω = ω \ S := by
    ext e
    change (if e ∈ S then False else e ∈ ω) ↔ (e ∈ ω ∧ e ∉ S)
    split_ifs <;> tauto
  rw [heq]
  exact G.percolates_diff_finite_iff ω S hS

lemma percolates_probability_one [Countable V] [Countable E] (p : unitInterval)
    (h : 0 < G.law p G.percolates) : G.law p G.percolates = 1 := by
  have hh := G.percolates_zero_one (fun _ => p)
  rw [BernoulliProduct.law_const] at hh
  exact hh.resolve_left (ne_of_gt h)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteProductPin
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j

omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]

lemma expect_mask_pin (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [ite_eq_left h,ite_eq_left h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Distribution
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_zero (w : E → A → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]

lemma expect_nonneg {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect w f := by
  rw [← expect_zero w]
  exact expect_mono hw hf

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_const_mul (w : E → A → ℝ) (c : ℝ) (f : (E → A) → ℝ) :
    expect w (fun ω => c * f ω) = c * expect w f := by
  simp only [mul_comm c]
  exact expect_mul_const w f c
end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Potential
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_prop_mask_pin (w : E → Prop → ℝ) (e : E) (b : Prop) (f : (E → Prop) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  convert expect_mask_pin w e b f using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  by_cases h : ω e = b <;> simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ComponentSelf
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_HitEvent
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteInduced
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
variable {V E : Type*} (G : BondGraph V E)

lemma induced_adj_mem (S : Set V) (ω : Set (G.inducedEdges S)) {u v : V}
    (h : (G.openGraph (Subtype.val '' ω)).Adj u v) : u∈S ∧ v∈S := by
  obtain ⟨⟨e,⟨a,ha,rfl⟩,he⟩,_⟩ := h
  constructor
  · exact a.property u (by rw [he]; simp)
  · exact a.property v (by rw [he]; simp)

lemma induce_reachable (S : Set V) (ω : Set (G.inducedEdges S)) (u v : S) :
    ((G.induce S).openGraph ω).Reachable u v ↔
      (G.openGraph (Subtype.val '' ω)).Reachable u.val v.val := by
  constructor
  · intro h
    exact h.map ⟨Subtype.val, fun {a b} hab => (G.induce_adj S ω a b).mp hab⟩
  · intro h
    have H : ∀ w, (G.openGraph (Subtype.val '' ω)).Reachable u.val w →
        ∀ hw : w∈S, ((G.induce S).openGraph ω).Reachable u ⟨w,hw⟩ := by
      intro w hh
      rw [SimpleGraph.reachable_iff_reflTransGen] at hh
      induction hh with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | @tail w z _ hz ih =>
        intro hmem
        have hw := (G.induced_adj_mem S ω hz).1
        exact (ih hw).trans ((G.induce_adj S ω ⟨w,hw⟩ ⟨z,hmem⟩).mpr hz).reachable
    exact H v.val h v.property

lemma induced_cluster_subset (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) :
    G.cluster (Subtype.val '' ω) u.val ⊆ S := by
  intro v hv
  rw [cluster,Set.mem_ofPred_eq,SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl => exact u.property
  | tail _ hadj _ => exact (G.induced_adj_mem S ω hadj).2

lemma induce_cluster_image (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) :
    Subtype.val '' ((G.induce S).cluster ω u) = G.cluster (Subtype.val '' ω) u.val := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (G.induce_reachable S ω u a).mp ha
  · intro hv
    have hmem := G.induced_cluster_subset S ω u hv
    exact ⟨⟨v,hmem⟩,(G.induce_reachable S ω u ⟨v,hmem⟩).mpr hv,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorGraph
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma inducedEdges_mono {S T : Set V} (h : S⊆T) :
    G.inducedEdges S⊆G.inducedEdges T := by
  intro e he v hv
  exact h (he v hv)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteOpenWitness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma real_law_restrict (p : unitInterval) (s : Set E) (hs : s.Finite)
    (A : Set (Set E)) :
    (law (fun _ : E => p)).real {ω | s ∩ ω ∈ A} =
      (law (fun _ : s => p)).real {ω | Subtype.val '' ω ∈ A} := by
  let := hs.fintype
  have hi (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
    ext e
    simp
  rw [← law_map_restrict (fun _ : E => p) s]
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [Measure.real]
  rw [Measure.map_apply hf (.of_discrete)]
  simp only [Set.preimage_ofPred_eq, hi]

lemma finiteWitness_exhaustion (A : Set (Set E)) (hmono : IsUpperSet A)
    (hw : HasFiniteOpenWitness A) (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    (⋃ n, {ω | K n ∩ ω ∈ A}) = A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact hmono Set.inter_subset_right hn
  · intro h
    obtain ⟨s, hs, hsω, hsA⟩ := hw ω h
    obtain ⟨n, hn⟩ := BondGraph.finite_subset_exhaustion K hs (Set.subset_univ _)
    exact Set.mem_iUnion.mpr ⟨n, hmono (Set.subset_inter hn hsω) hsA⟩

lemma finiteWitness_exhaustion_mono (A : Set (Set E)) (hmono : IsUpperSet A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Monotone (fun n => {ω | K n ∩ ω ∈ A}) := by
  intro m n h ω hω
  exact hmono (Set.inter_subset_inter_left _ (K.mono h)) hω

lemma tendsto_real_finiteWitness (p : unitInterval) (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A})
      atTop (𝓝 ((law (fun _ : E => p)).real A)) := by
  have h := tendsto_measure_iUnion_atTop (μ := law (fun _ : E => p))
    (finiteWitness_exhaustion_mono A hmono K)
  rw [finiteWitness_exhaustion A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_MonotoneIndicatorUpper
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma real_eq_expect_indicator [Fintype E] (q : E → unitInterval) (A : Set (Set E)) :
    (law q).real A = FiniteProduct.expect (fun e => bitWeight (q e))
      (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  rw [← integral_law_eq_expect]
  exact (integral_indicator_one (.of_discrete)).symm

end CriticalPercolation.BernoulliProduct
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

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

lemma clusterTail_isUpperSet (o : V) (n : ℕ) : IsUpperSet (G.clusterTail o n) := by
  rintro ω ω' h ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω.trans (G.cluster_mono h o), hn⟩

lemma clusterTail_hasFiniteOpenWitness (o : V) (n : ℕ) :
    BernoulliProduct.HasFiniteOpenWitness (G.clusterTail o n) := by
  rintro ω ⟨K, hK, hKω, hn⟩
  obtain ⟨s, hs, hsω, hKs⟩ := G.finite_subset_cluster_finite_witness hK hKω
  exact ⟨s, hs, hsω, K, hK, hKs, hn⟩

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_OpenRay
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma openWalk_getVert_ball {ω : Set E} {a b : V} (w : (G.openGraph ω).Walk a b) :
    ∀ n≤w.length, w.getVert n∈G.vertexBall a n := by
  intro n
  induction n with
  | zero => intro _; simpa using G.mem_vertexBall_self a 0
  | succ n ih =>
    intro hn
    exact G.vertexBall_step (ih (by omega))
      (G.openGraph_mono (Set.subset_univ _) (w.adj_getVert_succ (by omega)))

lemma rayPrefix_nonempty (hl : G.LocallyFinite) {ω : Set E} {o : V}
    (hi : (G.cluster ω o).Infinite) (n : ℕ) : Nonempty (G.RayPrefix ω o n) := by
  have hn : ¬G.cluster ω o⊆G.vertexBall o n := fun h => hi ((G.vertexBall_finite hl o n).subset h)
  obtain ⟨b,hb,hbn⟩ := Set.not_subset.mp hn
  obtain ⟨w⟩ := hb
  let p := w.toPath
  have hlen : n<p.val.length := by
    by_contra hn
    have h := G.openWalk_getVert_ball p.val p.val.length le_rfl
    rw [SimpleGraph.Walk.getVert_length] at h
    exact hbn (G.vertexBall_mono o (by omega) h)
  refine ⟨{ vertex := fun i => p.val.getVert i.val
            start := p.val.getVert_zero
            adjacent := ?_
            injective := ?_
            ball := ?_ }⟩
  · intro i
    exact p.val.adj_getVert_succ (by omega)
  · intro i j hij
    apply Fin.ext
    exact p.property.getVert_injOn (by change i.val≤p.val.length; omega)
      (by change j.val≤p.val.length; omega) hij
  · intro i
    exact G.openWalk_getVert_ball p.val i.val (by omega)

lemma rayPrefix_finite (hl : G.LocallyFinite) (ω : Set E) (o : V) (n : ℕ) :
    Finite (G.RayPrefix ω o n) := by
  let := (G.vertexBall_finite hl o n).to_subtype
  let f : G.RayPrefix ω o n → (Fin (n+1) → G.vertexBall o n) := fun p i =>
    ⟨p.vertex i,G.vertexBall_mono o (by omega) (p.ball i)⟩
  apply Finite.of_injective f
  intro p q hpq
  apply RayPrefix.ext
  funext i
  exact congrArg Subtype.val (congrFun hpq i)

lemma RayPrefix.restrict_refl {ω : Set E} {o : V} {i : ℕ} (p : G.RayPrefix ω o i) :
    p.restrict G le_rfl=p := by ext k; rfl

lemma RayPrefix.restrict_trans {ω : Set E} {o : V} {i j k : ℕ}
    (hij : i≤j) (hjk : j≤k) (p : G.RayPrefix ω o k) :
    (p.restrict G hjk).restrict G hij=p.restrict G (hij.trans hjk) := by ext k; rfl

theorem infinite_cluster_openRay (hl : G.LocallyFinite) {ω : Set E} {o : V}
    (hi : (G.cluster ω o).Infinite) : ∃ r : G.OpenRay ω, r.vertex 0=o := by
  let : ∀ n, Finite (G.RayPrefix ω o n) := G.rayPrefix_finite hl ω o
  let : ∀ n, Nonempty (G.RayPrefix ω o n) := G.rayPrefix_nonempty hl hi
  obtain ⟨f,hf⟩ := exists_seq_forall_proj_of_forall_finite (α := fun n => G.RayPrefix ω o n)
    (fun {i j} h p => RayPrefix.restrict G (i := i) (j := j) h p)
    (fun {_} p => p.restrict_refl G) (fun {_ _ _} hij hjk p => p.restrict_trans G hij hjk)
    (fun _ _ => Set.toFinite _)
  let r : ℕ → V := fun n => (f n).vertex ⟨n,Nat.lt_succ_self n⟩
  have hcoh : ∀ i j (h : i≤j), (f j).vertex ⟨i,by omega⟩=r i := by
    intro i j hij
    have h := congrArg (fun p : G.RayPrefix ω o i => p.vertex ⟨i,Nat.lt_succ_self i⟩) (hf hij)
    exact h
  have hinj : Function.Injective r := by
    intro i j hij
    have hh : (f (max i j)).vertex ⟨i,by omega⟩=(f (max i j)).vertex ⟨j,by omega⟩ := by
      rw [hcoh i _ (le_max_left _ _),hcoh j _ (le_max_right _ _),hij]
    exact congrArg Fin.val ((f (max i j)).injective hh)
  have hadj : ∀ n, (G.openGraph ω).Adj (r n) (r (n+1)) := by
    intro n
    have h := (f (n+1)).adjacent ⟨n,Nat.lt_succ_self n⟩
    change (G.openGraph ω).Adj ((f (n+1)).vertex ⟨n,by omega⟩)
      ((f (n+1)).vertex ⟨n+1,by omega⟩) at h
    simpa only [hcoh n (n+1) (Nat.le_succ n),hcoh (n+1) (n+1) le_rfl] using h
  exact ⟨⟨r,hinj,hadj⟩,(f 0).start⟩

theorem infinite_induced_openRay (hl : G.LocallyFinite) (ω : Set E) (S : Set V) (o : V)
    (hi : (G.cluster (ω∩G.inducedEdges S) o).Infinite) :
    ∃ r : G.OpenRay ω, r.vertex 0=o ∧ ∀ n, r.vertex n∈S := by
  obtain ⟨r,hr⟩ := G.infinite_cluster_openRay hl hi
  refine ⟨⟨r.vertex,r.injective,fun n => G.openGraph_mono Set.inter_subset_left (r.adjacent n)⟩,
    hr,?_⟩
  intro n
  exact ((G.open_induced_adj S ω _ _).mp (r.adjacent n)).2.1

lemma no_bounded_ray_rectangles (hl : G.LocallyFinite) (u v : V → ℝ) (ω : Set E)
    (h : ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
      ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ∀ U W : ℝ, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite := by
  intro U W a
  by_contra hi
  obtain ⟨r,_hr,hS⟩ := G.infinite_induced_openRay hl ω _ a hi
  exact h ⟨r,U,W,hS⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_MovingStrips
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma unit_pair_bounds {a b : ℝ} (h : a^2+b^2=1) :
    -1≤a ∧ a≤1 ∧ -1≤b ∧ b≤1 := by
  have ha : a^2≤1 := by nlinarith [sq_nonneg b]
  have hb : b^2≤1 := by nlinarith [sq_nonneg a]
  constructor
  · nlinarith [sq_nonneg (a+1)]
  constructor
  · nlinarith [sq_nonneg (a-1)]
  constructor <;> nlinarith [sq_nonneg (b+1),sq_nonneg (b-1)]

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CoordinateRotation
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exists_int_coefficient_gt (a r : ℝ) (ha : a≠0) : ∃ m : ℤ, r<a*m := by
  rcases lt_or_gt_of_ne ha with ha|ha
  · obtain ⟨m,hm⟩ := exists_int_lt (r/a)
    exact ⟨m,by have := (lt_div_iff_of_neg ha).mp hm; nlinarith only [this]⟩
  · obtain ⟨m,hm⟩ := exists_int_gt (r/a)
    exact ⟨m,by have := (div_lt_iff₀ ha).mp hm; nlinarith only [this]⟩

lemma integer_coordinates_direction_unbounded (pi : V → ℂ)
    (honto : ∀ m n : ℤ, ∃ x, (pi x).re=m ∧ (pi x).im=n)
    (a b : ℝ) (hab : a^2+b^2=1) :
    ∀ r : ℕ, ∃ x, (r : ℝ)<normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b x := by
  intro r
  by_cases ha : a=0
  · have hb : -b≠0 := by intro hh; have : b=0 := neg_eq_zero.mp hh; simp [ha,this] at hab
    obtain ⟨m,hm⟩ := exists_int_coefficient_gt (-b) r hb
    obtain ⟨x,hx,hy⟩ := honto m 0
    exact ⟨x,by simpa [normalCoordinate,hx,hy] using hm⟩
  · obtain ⟨n,hn⟩ := exists_int_coefficient_gt a r ha
    obtain ⟨x,hx,hy⟩ := honto 0 n
    exact ⟨x,by simpa [normalCoordinate,hx,hy] using hn⟩

lemma rotated_coordinate_inverse (u v : V → ℝ) (a b : ℝ) (hab : a^2+b^2=1) (x : V) :
    u x=a*parallelCoordinate u v a b x-b*normalCoordinate u v a b x ∧
    v x=b*parallelCoordinate u v a b x+a*normalCoordinate u v a b x := by
  constructor <;> dsimp [parallelCoordinate,normalCoordinate] <;>
    nlinarith [congrArg (fun t => t*u x) hab,congrArg (fun t => t*v x) hab]

lemma rotated_box_bound (u v : V → ℝ) (a b U W : ℝ) (hab : a^2+b^2=1) (x : V)
    (hx : |parallelCoordinate u v a b x|≤U) (hy : |normalCoordinate u v a b x|≤W) :
    |u x|≤|a| *U+|b| *W ∧ |v x|≤|b| *U+|a| *W := by
  obtain ⟨he,hf⟩ := rotated_coordinate_inverse u v a b hab x
  constructor
  · rw [he]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg a))
      (mul_le_mul_of_nonneg_left hy (abs_nonneg b))
  · rw [hf]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg b))
      (mul_le_mul_of_nonneg_left hy (abs_nonneg a))

lemma rotated_no_bounded_ray (u v : V → ℝ) (a b : ℝ) (hab : a^2+b^2=1) (ω : Set E)
    (h : ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n,
      |parallelCoordinate u v a b (r.vertex n)|≤U ∧ |normalCoordinate u v a b (r.vertex n)|≤W := by
  rintro ⟨r,U,W,hr⟩
  exact h ⟨r,|a| *U+|b| *W,|b| *U+|a| *W,fun n => rotated_box_bound u v a b U W hab _ (hr n).1 (hr n).2⟩

lemma coordinate_linear_difference (u v : V → ℝ) (a b : ℝ) (x y : V) :
    parallelCoordinate u v a b x-parallelCoordinate u v a b y=a*(u x-u y)+b*(v x-v y) ∧
    normalCoordinate u v a b x-normalCoordinate u v a b y= -b*(u x-u y)+a*(v x-v y) := by
  constructor <;> dsimp [parallelCoordinate,normalCoordinate] <;> ring

lemma rotated_coordinate_increments (u v : V → ℝ) (a b D : ℝ) (hab : a^2+b^2=1) (hD : 0≤D)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D) :
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |parallelCoordinate u v a b x-parallelCoordinate u v a b y|≤2*D) ∧
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |normalCoordinate u v a b x-normalCoordinate u v a b y|≤2*D) := by
  obtain ⟨ha,ha',hb,hb'⟩ := unit_pair_bounds hab
  have haa : |a|≤1 := abs_le.mpr ⟨ha,ha'⟩
  have hbb : |b|≤1 := abs_le.mpr ⟨hb,hb'⟩
  have bound : ∀ A B : ℝ, |A|≤1 → |B|≤1 → ∀ x y, G.fullGraph.Adj x y →
      |A*(u x-u y)+B*(v x-v y)|≤2*D := by
    intro A B hA hB x y hxy
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    have hu' := mul_le_mul_of_nonneg_left (hu hxy) (abs_nonneg A)
    have hv' := mul_le_mul_of_nonneg_left (hv hxy) (abs_nonneg B)
    nlinarith [mul_le_mul_of_nonneg_right hA hD,mul_le_mul_of_nonneg_right hB hD]
  constructor
  · intro x y hxy
    rw [(coordinate_linear_difference u v a b x y).1]
    exact bound a b haa hbb x y hxy
  · intro x y hxy
    rw [(coordinate_linear_difference u v a b x y).2]
    exact bound (-b) a (by simpa only [abs_neg] using hbb) haa x y hxy

lemma rotated_aut_differences (u v : V → ℝ) (a b : ℝ) (phi : G.Aut)
    (hu : ∀ x y, u (phi.vertex x)-u (phi.vertex y)=u x-u y)
    (hv : ∀ x y, v (phi.vertex x)-v (phi.vertex y)=v x-v y) :
    (∀ x y, parallelCoordinate u v a b (phi.vertex x)-parallelCoordinate u v a b (phi.vertex y)=
      parallelCoordinate u v a b x-parallelCoordinate u v a b y) ∧
    (∀ x y, normalCoordinate u v a b (phi.vertex x)-normalCoordinate u v a b (phi.vertex y)=
      normalCoordinate u v a b x-normalCoordinate u v a b y) := by
  constructor
  · intro x y
    rw [(coordinate_linear_difference u v a b _ _).1,(coordinate_linear_difference u v a b x y).1,hu,hv]
  · intro x y
    rw [(coordinate_linear_difference u v a b _ _).2,(coordinate_linear_difference u v a b x y).2,hu,hv]

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterObject
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

lemma incidentEdges_mono {S T : Set V} (h : S ⊆ T) : G.incidentEdges S ⊆ G.incidentEdges T := by
  rintro e ⟨v, hv, he⟩
  exact ⟨v, h hv, he⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma expect_prop_ite (w : E → Prop → ℝ) (e : E) (f g : Set E → ℝ) :
    expect w (fun ω => if ω e then f ω else g ω) =
      w e True*expect (pin w e True) f+w e False*expect (pin w e False) g := by
  calc
    _ = expect w (fun ω => (if ω e = True then f ω else 0) +
        (if ω e = False then g ω else 0)) := by
      congr 1
      funext ω
      by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert expect_prop_mask_pin w e True f using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert expect_prop_mask_pin w e False g using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]

end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dite_eq_right hje]
  exact hf j hj'.2

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedFresh
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
lemma expect_square_add_const (v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (a : ℝ) (f : (E → Prop) → ℝ) :
    expect v (fun ω => (a+f ω)^2) = a^2+2*a*expect v f+expect v (fun ω => (f ω)^2) := by
  have heq : (fun ω => (a+f ω)^2) = (fun ω => a^2+2*a*f ω+(f ω)^2) := by
    funext ω; ring
  rw [heq,expect_add,expect_add,expect_const v hv,expect_const_mul]

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteInterpolationMeasure
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

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*} [Fintype E]

lemma prob_eq_real (q : E → unitInterval) (A : Set (Set E)) :
    FiniteProduct.prob (fun e => bitWeight (q e)) (fun ω => ω ∈ A) = (law q).real A := by
  rw [real_eq_expect_indicator]
  unfold FiniteProduct.prob
  rfl

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma clusterTail_iff_card [Fintype V] (ω : Set E) (u : V) (s : ℕ) :
    ω ∈ G.clusterTail u s ↔ s ≤ (G.cluster ω u).toFinset.card := by
  constructor
  · rintro ⟨K,hK,hsub,hs⟩
    exact hs.trans (by simpa only [Set.ncard_eq_toFinset_card'] using Set.ncard_le_ncard hsub)
  · intro hs
    exact ⟨G.cluster ω u, Set.toFinite _, Set.Subset.rfl, by simpa only [Set.ncard_eq_toFinset_card'] using hs⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceDegree
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
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma incident_card_le (S : Set V) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D) :
    (G.incidentEdges S).toFinset.card ≤ S.toFinset.card * D := by
  have he : (G.incidentEdges S).toFinset =
      S.toFinset.biUnion (fun v => (G.incidentEdges {v}).toFinset) := by
    ext e
    constructor
    · intro hh
      obtain ⟨v,hv,hev⟩ := Set.mem_toFinset.mp hh
      exact Finset.mem_biUnion.mpr ⟨v,Set.mem_toFinset.mpr hv,
        Set.mem_toFinset.mpr ⟨v,Set.mem_singleton v,hev⟩⟩
    · intro hh
      obtain ⟨v,hv,hev⟩ := Finset.mem_biUnion.mp hh
      obtain ⟨z,hz,he⟩ := Set.mem_toFinset.mp hev
      have hzv : z=v := Set.mem_singleton_iff.mp hz
      subst z
      exact Set.mem_toFinset.mpr ⟨v,Set.mem_toFinset.mp hv,he⟩
  rw [he]
  calc _ ≤ ∑ v ∈ S.toFinset, (G.incidentEdges {v}).toFinset.card := Finset.card_biUnion_le
       _ ≤ ∑ _v ∈ S.toFinset, D := Finset.sum_le_sum (fun v _ => hD v)
       _ = _ := by simp

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceSearch
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

lemma good_closed (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∉ ω) :
    Good G v ω (st.closed e) := by
  refine ⟨fun a ha => Finset.mem_insert_of_mem (hs.1 ha),?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_false (fun h => he.1 (hs.1 h)) hω
    · exact hs.2.1 a ha
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha

lemma good_open (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∈ ω) :
    Good G v ω (st.open e) := by
  refine ⟨Finset.insert_subset_insert e hs.1,?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_true (Finset.mem_insert_self _ _) hω
    · have hae : a≠e := fun hh => he.1 (hh ▸ ha)
      simpa only [State.open,Finset.mem_insert,hae,false_or] using hs.2.1 a ha
  · intro a ha
    change a ∈ G.incidentEdges (G.cluster ((insert e st.opened : Finset E) : Set E) v)
    rw [Finset.coe_insert]
    apply G.incidentEdges_mono (G.cluster_mono (Set.subset_insert e (st.opened : Set E)) v)
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha

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

variable [Fintype E]

lemma compile_terminal (G : BondGraph V E) (v : V) (ω : Set E) (n : ℕ) (st : State E)
    (hs : Good G v ω st) (hn : Fintype.card E - st.read.card < n) :
    let out := (compile G v n st).run (fun e => decide (e∈ω))
    Good G v ω out ∧ ¬∃ e, Available G v out e := by
  induction n generalizing st with
  | zero => omega
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : Available G v st e := h.choose_spec
      have hc : (insert e st.read).card = st.read.card+1 := Finset.card_insert_of_notMem he.1
      have hle : st.read.card < Fintype.card E := by
        have hh := Finset.card_le_univ (s := insert e st.read)
        rw [hc] at hh
        omega
      have hn' : Fintype.card E - (insert e st.read).card < n := by rw [hc]; omega
      simp only [SearchTree.run]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        Good G v ω out ∧ ¬∃ a, Available G v out a)
      by_cases hω : e∈ω
      · simp only [hω,decide_true,if_true]
        exact ih (st.open e) (good_open G v ω st hs e he hω) hn'
      · simp only [hω,decide_false,Bool.false_eq_true,if_false]
        exact ih (st.closed e) (good_closed G v ω st hs e he hω) hn'
    · exact ⟨hs,h⟩

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_QueryMartingale
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

variable [Fintype E] [DecidableEq E]

lemma centeredSum_moments (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hf : LazyDFS.Fresh w p used) :
    expect w (t.centeredSum p) = 0 ∧
      expect w (fun ω => (t.centeredSum p ω)^2) =
        p*(1-p)*expect w (fun ω => (t.queryCount ω : ℝ)) := by
  induction t generalizing used w with
  | done r => simp [centeredSum,queryCount,expect_const w hw]
  | ask e l r hl hr =>
    have h0 := hl (insert e used) ht.2.1 (pin w e False)
      (pin_normalized w hw e False) (LazyDFS.fresh_pin w p used hf e False)
    have h1 := hr (insert e used) ht.2.2 (pin w e True)
      (pin_normalized w hw e True) (LazyDFS.fresh_pin w p used hf e True)
    have he := hf e ht.1
    constructor
    · simp only [centeredSum]
      erw [expect_prop_ite]
      simp only [expect_add, expect_const _ (pin_normalized w hw e False),
        expect_const _ (pin_normalized w hw e True),h0.1,h1.1,he.1,he.2]
      ring
    · have hx : (fun ω => ((.ask e l r : SearchTree E R).centeredSum p ω)^2) =
          (fun ω => if ω e then ((1-p)+r.centeredSum p ω)^2
            else (-p+l.centeredSum p ω)^2) := by funext ω; simp only [centeredSum]; split_ifs <;> rfl
      rw [hx]
      erw [expect_prop_ite,
        expect_square_add_const _ (pin_normalized w hw e False),
        expect_square_add_const _ (pin_normalized w hw e True),h0.1,h1.1,h0.2,h1.2,he.1,he.2]
      have hc : (fun ω => ((.ask e l r : SearchTree E R).queryCount ω : ℝ)) =
          (fun ω => 1+(if ω e then (r.queryCount ω : ℝ) else (l.queryCount ω : ℝ))) := by
        funext ω; simp only [queryCount]; split_ifs <;> simp
      rw [hc,expect_add]
      erw [expect_prop_ite,expect_const w hw,he.1,he.2]
      ring

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceIdentity
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

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

lemma compile_trace (G : BondGraph V E) (v : V) (n : ℕ) (st : State E)
    (ω : Set E) (p : ℝ) :
    let t := compile G v n st
    let out := t.run (fun e => decide (e∈ω))
    t.queryCount ω + st.read.card = out.read.card ∧
      t.centeredSum p ω + readSum p ω st = readSum p ω out := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.queryCount,SearchTree.centeredSum]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : e∉st.read := h.choose_spec.1
      have hopen := ih (st.open e)
      have hclosed := ih (st.closed e)
      have hcard : (insert e st.read).card = st.read.card + 1 := Finset.card_insert_of_notMem he
      have hsum : readSum p ω (st.open e) =
          (if e∈ω then 1-p else -p)+readSum p ω st := by
        simp only [readSum,State.open,Finset.sum_insert he]
      have hsum' : readSum p ω (st.closed e) =
          (if e∈ω then 1-p else -p)+readSum p ω st := by
        simp only [readSum,State.closed,Finset.sum_insert he]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        (1 + if ω e then (compile G v n (st.open e)).queryCount ω else
          (compile G v n (st.closed e)).queryCount ω) + st.read.card = out.read.card ∧
        (if ω e then (1-p)+(compile G v n (st.open e)).centeredSum p ω else
          -p+(compile G v n (st.closed e)).centeredSum p ω) + readSum p ω st = readSum p ω out)
      by_cases hω : e∈ω
      · have hω' : ω e := hω
        simp only [hω,hω',decide_true,if_true]
        dsimp only at hopen
        constructor
        · have hh := hopen.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum,ite_eq_left hω] at hopen
          linarith [hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,if_false]
        dsimp only at hclosed
        constructor
        · have hh := hclosed.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum',ite_eq_right hω] at hclosed
          linarith [hclosed.2]
    · simp [SearchTree.run,SearchTree.queryCount,SearchTree.centeredSum]

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

lemma tree_count (G : BondGraph V E) (v : V) (ω : Set E) :
    (tree G v).queryCount ω = (G.incidentEdges (G.cluster ω v)).toFinset.card := by
  have h := (compile_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω (0:ℝ)).1
  change (tree G v).queryCount ω + (∅ : Finset E).card =
    ((tree G v).run (fun e => decide (e∈ω))).read.card at h
  simp only [Finset.card_empty,add_zero] at h
  refine h.trans (congrArg Finset.card ?_)
  ext e
  rw [Set.mem_toFinset]
  exact tree_mem_read G v ω e

lemma tree_centered (G : BondGraph V E) (v : V) (ω : Set E) (p : ℝ) :
    (tree G v).centeredSum p ω = ∑ e,
      if e∈G.incidentEdges (G.cluster ω v) then (if e∈ω then 1-p else -p) else 0 := by
  have h := (compile_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω p).2
  change (tree G v).centeredSum p ω + readSum p ω ⟨∅,∅⟩ =
    readSum p ω ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [readSum,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then
        (if e∈ω then 1-p else -p) else 0 := by
      simp only [← Finset.sum_filter]
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
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_FiniteClusterTransport
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

namespace CriticalPercolation

lemma finite_subset_size_image {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (S : Set α) (n : ℕ) :
    (∃ K : Set β, K.Finite ∧ K ⊆ f '' S ∧ n≤K.ncard) ↔
      ∃ K : Set α, K.Finite ∧ K ⊆ S ∧ n≤K.ncard := by
  constructor
  · rintro ⟨K,hK,hKS,hn⟩
    refine ⟨f ⁻¹' K,hK.preimage hf.injOn,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,heq⟩ := hKS ha
      exact hf heq ▸ hb
    · rwa [Set.ncard_preimage_of_injective_subset_range hf
        (hKS.trans (Set.image_subset_range _ _))]
  · rintro ⟨K,hK,hKS,hn⟩
    exact ⟨f '' K,hK.image f,Set.image_mono hKS,
      (Set.ncard_image_of_injective K hf) ▸ hn⟩

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma induce_clusterTail (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) (n : ℕ) :
    ω ∈ (G.induce S).clusterTail u n ↔
      Subtype.val '' ω ∈ G.clusterTail u.val n := by
  change _ ↔ ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster (Subtype.val '' ω) u.val ∧ n≤K.ncard
  rw [← G.induce_cluster_image]
  exact (finite_subset_size_image Subtype.val Subtype.val_injective _ n).symm

lemma induce_law_event (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (A : Set (Set E)) :
    ((G.induce S).law p).real {ω | Subtype.val '' ω ∈ A} =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ A} := by
  simpa only [law,← BernoulliProduct.law_const] using
    (BernoulliProduct.real_law_restrict p (G.inducedEdges S) hS A).symm

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteAdjacentMeasure
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
variable {V E : Type*} (G : BondGraph V E)

lemma induce_incident_image_subset (S : Set V) (v : S) :
    Subtype.val '' ((G.induce S).incidentEdges {v}) ⊆ G.incidentEdges {v.val} := by
  rintro e ⟨a,ha,rfl⟩
  simp only [incidentEdges,Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left] at ha ⊢
  rw [← G.induce_ends_map S a]
  exact Sym2.mem_map.mpr ⟨v,ha,rfl⟩

lemma induce_incident_bound (hlocal : G.LocallyFinite) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (S : Set V) (v : S) :
    ((G.induce S).incidentEdges {v}).ncard ≤ D := by
  calc
    _ = (Subtype.val '' ((G.induce S).incidentEdges {v})).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.incidentEdges {v.val}).ncard := Set.ncard_le_ncard
      (G.induce_incident_image_subset S v) (G.finite_incident hlocal (Set.finite_singleton _))
    _ ≤ D := hD v.val

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteSusceptibility
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

namespace CriticalPercolation
open FiniteProduct

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_subset_endpoint_union (ω : Set E) (v : V) :
    G.cluster ω v ⊆ {v} ∪ ((fun e => (G.ends e).out.1) '' G.openIncident ω v ∪
      (fun e => (G.ends e).out.2) '' G.openIncident ω v) := by
  intro z hz
  change (G.openGraph ω).Reachable v z at hz
  rw [SimpleGraph.reachable_iff_reflTransGen] at hz
  induction hz with
  | refl => exact Or.inl rfl
  | @tail u z hv hu _ =>
    obtain ⟨⟨e,he,heq⟩,_⟩ := hu
    have hzmem : z ∈ G.ends e := by rw [heq]; simp
    have heI : e ∈ G.openIncident ω v := by
      exact ⟨⟨u,(SimpleGraph.reachable_iff_reflTransGen _ _).mpr hv,
        by rw [heq]; simp⟩,he⟩
    have hout : G.ends e = s((G.ends e).out.1,(G.ends e).out.2) :=
      (G.ends e).out_eq.symm
    rw [hout,Sym2.mem_iff] at hzmem
    exact Or.inr (hzmem.elim (fun h => Or.inl ⟨e,heI,h.symm⟩)
      (fun h => Or.inr ⟨e,heI,h.symm⟩))

lemma cluster_card_le_open_incident [Fintype V] [Fintype E] (ω : Set E) (v : V) :
    G.clusterSize ω v ≤ 1 + 2*(G.openIncident ω v).ncard := by
  calc
    _ ≤ ({v} ∪ ((fun e => (G.ends e).out.1) '' G.openIncident ω v ∪
      (fun e => (G.ends e).out.2) '' G.openIncident ω v)).ncard := by
      simpa only [clusterSize,← Set.ncard_eq_toFinset_card'] using
        Set.ncard_le_ncard (G.cluster_subset_endpoint_union ω v)
    _ ≤ ({v} : Set V).ncard + (((fun e => (G.ends e).out.1) '' G.openIncident ω v).ncard +
      ((fun e => (G.ends e).out.2) '' G.openIncident ω v).ncard) :=
      (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_union_le _ _) _)
    _ ≤ _ := by
      have h1 := Set.ncard_image_le (s := G.openIncident ω v) (f := fun e => (G.ends e).out.1)
      have h2 := Set.ncard_image_le (s := G.openIncident ω v) (f := fun e => (G.ends e).out.2)
      simp only [Set.ncard_singleton]
      omega

lemma openIncident_card_centered [Fintype E] (p : ℝ) (ω : Set E) (v : V) :
    ((G.openIncident ω v).ncard : ℝ) = (IncidenceSearch.tree G v).centeredSum p ω +
      p*((IncidenceSearch.tree G v).queryCount ω : ℝ) := by
  rw [IncidenceSearch.tree_centered,IncidenceSearch.tree_count]
  simp only [Set.ncard_eq_toFinset_card']
  have ha : ((G.openIncident ω v).toFinset.card : ℝ) =
      ∑ e : E, if e ∈ G.openIncident ω v then (1:ℝ) else 0 := by simp
  have hb : ((G.incidentEdges (G.cluster ω v)).toFinset.card : ℝ) =
      ∑ e : E, if e ∈ G.incidentEdges (G.cluster ω v) then (1:ℝ) else 0 := by simp
  rw [ha,hb,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : e∈G.incidentEdges (G.cluster ω v) <;> by_cases ho : e∈ω <;>
    simp [openIncident,hi,ho]

lemma finite_susceptibility_bound [Fintype V] [Fintype E]
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (h0 : ∀ e, w e False=1-p) (h1 : ∀ e, w e True=p)
    (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D)
    (hpD : 4*p*D ≤ 1) (v : V) :
    expect w (fun ω => (G.clusterSize {e | ω e} v : ℝ)) ≤ 2 := by
  let t := IncidenceSearch.tree G v
  let a := expect w (fun ω => (G.clusterSize {e | ω e} v : ℝ))
  have hmean := (t.centeredSum_moments ∅ (IncidenceSearch.tree_valid G v) p w hw
    (fun e _ => ⟨h0 e,h1 e⟩)).1
  have hquery : expect w (fun ω => (t.queryCount ω : ℝ)) ≤ D*a := by
    calc
      _ ≤ expect w (fun ω => (D:ℝ)*(G.clusterSize {e | ω e} v : ℝ)) := by
        apply expect_mono hn
        intro ω
        have hcount : t.queryCount ω = (G.incidentEdges (G.cluster {e | ω e} v)).toFinset.card :=
          IncidenceSearch.tree_count G v {e | ω e}
        rw [hcount]
        exact_mod_cast (by simpa only [clusterSize,mul_comm] using
          G.incident_card_le (G.cluster {e | ω e} v) D hD)
      _ = _ := expect_const_mul _ _ _
  have hcluster : a ≤ 1+2*p*(D*a) := by
    calc
      _ ≤ expect w (fun ω => 1+2*((G.openIncident {e | ω e} v).ncard : ℝ)) := by
        apply expect_mono hn
        intro ω
        exact_mod_cast G.cluster_card_le_open_incident {e | ω e} v
      _ = 1+2*p*expect w (fun ω => (t.queryCount ω : ℝ)) := by
        have hopen (ω : E → Prop) : ((G.openIncident {e | ω e} v).ncard : ℝ) =
            t.centeredSum p ω + p*(t.queryCount ω : ℝ) :=
          G.openIncident_card_centered p {e | ω e} v
        simp_rw [hopen]
        rw [expect_add,expect_const w hw,expect_const_mul,expect_add,hmean,
          expect_const_mul]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hquery (mul_nonneg (by norm_num) hp.1 : 0≤2*p)
        linarith
  have ha : 0≤a := expect_nonneg hn (fun _ => Nat.cast_nonneg _)
  nlinarith

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_SusceptibilityMeasure
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
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma finite_clusterTail_measure_bound [Fintype V] [Fintype E]
    (p : unitInterval) (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hpD : 4*(p:ℝ)*D≤1) (u : V) (s : ℕ) :
    (s:ℝ)*(G.law p).real (G.clusterTail u s) ≤ 2 := by
  let w := fun _ : E => BernoulliProduct.bitWeight p
  have hn : ∀ e b, 0≤w e b := fun _ => BernoulliProduct.bitWeight_nonneg p
  have ht := G.finite_susceptibility_bound p p.property w
    (fun _ => BernoulliProduct.bitWeight_sum p) hn
    (fun _ => by simp only [w,BernoulliProduct.bitWeight,if_false])
    (fun _ => by simp only [w,BernoulliProduct.bitWeight,if_true]) D
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v) hpD u
  have hprob : (G.law p).real (G.clusterTail u s) = prob w (fun ω => ω∈G.clusterTail u s) := by
    simpa only [law,← BernoulliProduct.law_const,w] using
      (BernoulliProduct.prob_eq_real (fun _ : E => p) (G.clusterTail u s)).symm
  rw [hprob,prob,← expect_const_mul]
  refine le_trans (expect_mono hn ?_) ht
  intro ω
  change (s:ℝ)*(if {e | ω e}∈G.clusterTail u s then 1 else 0) ≤
    (G.clusterSize {e | ω e} u : ℝ)
  by_cases hh : {e | ω e} ∈ G.clusterTail u s
  · simp only [ite_eq_left hh,mul_one]
    exact_mod_cast (G.clusterTail_iff_card {e | ω e} u s).mp hh
  · simp only [ite_eq_right hh,mul_zero]
    exact Nat.cast_nonneg _

lemma induce_clusterTail_real (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (u : S) (s : ℕ) :
    ((G.induce S).law p).real ((G.induce S).clusterTail u s) =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.clusterTail u.val s} := by
  have he : (G.induce S).clusterTail u s =
      {ω | Subtype.val '' ω ∈ G.clusterTail u.val s} := by
    ext ω
    exact G.induce_clusterTail S ω u s
  rw [he,G.induce_law_event S hS]

lemma induced_clusterTail_measure_bound (hlocal : G.LocallyFinite)
    (p : unitInterval) (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hpD : 4*(p:ℝ)*D≤1) (S : Set V) (hS : S.Finite) (u : S) (s : ℕ) :
    (s:ℝ)*(G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.clusterTail u.val s} ≤ 2 := by
  let := hS.fintype
  let := (G.finite_inducedEdges hlocal hS).fintype
  have h := (G.induce S).finite_clusterTail_measure_bound p D
    (G.induce_incident_bound hlocal D hD S) hpD u s
  rwa [G.induce_clusterTail_real S (G.finite_inducedEdges hlocal hS)] at h

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_PositiveCritical
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

lemma small_parameter_tail_bound (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1)
    (u : V) (s : ℕ) : (s:ℝ)*(G.law p).real (G.clusterTail u s) ≤ 2 := by
  let K := G.inducedBallExhaustion hconnected hlocal u
  have ht := BernoulliProduct.tendsto_real_finiteWitness p (G.clusterTail u s)
    (G.clusterTail_isUpperSet u s) (G.clusterTail_hasFiniteOpenWitness u s) K
  have ht' : Tendsto (fun n => (s:ℝ)*(G.law p).real {ω | K n ∩ ω ∈ G.clusterTail u s})
      atTop (𝓝 ((s:ℝ)*(G.law p).real (G.clusterTail u s))) := by
    simpa only [law,← BernoulliProduct.law_const] using ht.const_mul (s:ℝ)
  apply le_of_tendsto ht'
  exact Filter.Eventually.of_forall (fun n => G.induced_clusterTail_measure_bound hlocal p D hD hpD
    (G.vertexBall u n) (G.vertexBall_finite hlocal u n) ⟨u,G.mem_vertexBall_self u n⟩ s)

lemma small_parameter_infinite_null (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1) (u : V) :
    G.law p (G.infiniteEvent u) = 0 := by
  have hreal : (G.law p).real (G.infiniteEvent u) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! hp
    obtain ⟨n,hn⟩ := exists_nat_gt (2/(G.law p).real (G.infiniteEvent u))
    have hh : (n:ℝ)*(G.law p).real (G.infiniteEvent u) ≤ 2 := by
      calc
        _ ≤ (n:ℝ)*(G.law p).real (G.clusterTail u n) :=
          mul_le_mul_of_nonneg_left (measureReal_mono (G.infiniteEvent_subset_clusterTail u n))
            (Nat.cast_nonneg _)
        _ ≤ 2 := G.small_parameter_tail_bound hconnected hlocal p D hD hpD u n
    have hlt := (div_lt_iff₀ hp).mp hn
    linarith
  have hh := (ENNReal.toReal_eq_zero_iff _).mp hreal
  exact hh.resolve_right (measure_ne_top _ _)

lemma small_parameter_percolates_null (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1) :
    G.law p G.percolates = 0 := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  apply (G.percolates_null_iff (G.law p)).mpr
  exact G.small_parameter_infinite_null hconnected hlocal p D hD hpD

theorem criticalProbability_pos (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive) :
    (0:ℝ)<G.criticalProbability := by
  obtain ⟨D,_,hD⟩ := G.uniform_incident_bound hquasi
  have hd : (0:ℝ)<4*(D:ℝ)+1 := by positivity
  let p₀ : unitInterval := ⟨1/(4*(D:ℝ)+1), by
    constructor
    · positivity
    · exact (div_le_one hd).mpr (by
        have hh : (0:ℝ) ≤ 4 * (D:ℝ) := by positivity
        linarith)⟩
  have he : (p₀:ℝ)*(4*(D:ℝ)+1)=1 := div_mul_cancel₀ _ hd.ne'
  have hp₀ : (0:ℝ)<p₀ := one_div_pos.mpr hd
  have hsmall : ∀ p : unitInterval, p≤p₀ → 4*(p:ℝ)*D≤1 := by
    intro p hp
    have hn : (0:ℝ)≤D := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (show (p:ℝ)≤p₀ from hp) hn
    nlinarith [p₀.property.1]
  have hle : p₀≤G.criticalProbability := by
    apply le_sInf
    intro p hp
    by_contra h
    have hpp : p≤p₀ := (not_le.mp h).le
    have hz := G.small_parameter_percolates_null hconnected hlocal p D hD (hsmall p hpp)
    exact (ne_of_gt hp) hz
  exact hp₀.trans_le hle

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CriticalCoordinates
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
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stripPercolates_subset_some (v : V → ℝ) (w : ℝ) :
    G.stripPercolates v w⊆G.someStripPercolates v := by
  obtain ⟨n,hn⟩ := exists_nat_ge w
  rintro ω ⟨a,ha⟩
  apply Set.mem_iUnion.mpr
  exact ⟨n,a,ha.mono (G.cluster_mono (Set.inter_subset_inter_right _
    (G.inducedEdges_mono (fun _ hx => hx.trans hn))) a)⟩

theorem critical_null_of_unbounded_projection
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (hpc1 : G.criticalProbability<1)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ) (hD : 0≤D) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (honto : ∀ m n : ℤ, ∃ x, (pi x).re=m ∧ (pi x).im=n)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
        ∀ n, |(pi (r.vertex n)).re|≤U ∧ |(pi (r.vertex n)).im|≤W) :
    G.law G.criticalProbability G.percolates=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hpc := G.criticalProbability_pos hc hl hq
  have hur : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |(pi x).re-(pi y).re|≤D :=
    fun {_ _} h => (Complex.abs_re_le_norm _).trans (hpi h)
  have hvi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |(pi x).im-(pi y).im|≤D :=
    fun {_ _} h => (Complex.abs_im_le_norm _).trans (hpi h)
  have hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => G.criticalProbability)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0 := by
    intro a b hab w
    let u := parallelCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b
    let v := normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b
    have huo : u o=0 := by simp [u,parallelCoordinate,hpo]
    have hvo : v o=0 := by simp [v,normalCoordinate,hpo]
    have hsteps := G.rotated_coordinate_increments (fun x => (pi x).re) (fun x => (pi x).im) a b D hab hD hur hvi
    have hdense' : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
        (∀ x y, u (phi.vertex x)-u (phi.vertex y)=u x-u y) ∧
        (∀ x y, v (phi.vertex x)-v (phi.vertex y)=v x-v y) := by
      intro y
      obtain ⟨phi,hphi,hP⟩ := hdense y
      have hpr : ∀ x y, (pi (phi.vertex x)).re-(pi (phi.vertex y)).re=(pi x).re-(pi y).re :=
        fun x y => congrArg Complex.re (hP x y)
      have hpi' : ∀ x y, (pi (phi.vertex x)).im-(pi (phi.vertex y)).im=(pi x).im-(pi y).im :=
        fun x y => congrArg Complex.im (hP x y)
      exact ⟨phi,hphi,G.rotated_aut_differences _ _ a b phi hpr hpi'⟩
    have hn : ∀ᵐ ω ∂G.law G.criticalProbability,
        ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W := by
      filter_upwards [hnoray] with ω hω
      exact G.rotated_no_bounded_ray _ _ a b hab ω hω
    have hs := G.critical_strip_null_bs hc hl hq hg hpc1 u v o c (2*D) (by positivity) huo hvo hsteps.1 hsteps.2
      (integer_coordinates_direction_unbounded pi honto a b hab) hdense' hn
    have hm := measure_mono (μ := G.law G.criticalProbability) (G.stripPercolates_subset_some v w)
    rw [hs] at hm
    simpa only [law,BernoulliProduct.law_const] using le_antisymm hm (bot_le)
  by_contra hne
  have hpos := pos_iff_ne_zero.mpr hne
  have hone : BernoulliProduct.law (fun _ : E => G.criticalProbability) G.percolates=1 := by
    simpa only [law,BernoulliProduct.law_const] using G.percolates_probability_one G.criticalProbability hpos
  have hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite := by
    intro U W
    have hh := hnoray.mono (fun ω hω => G.no_bounded_ray_rectangles hl (fun x => (pi x).re) (fun x => (pi x).im) ω hω U W)
    simpa only [law,BernoulliProduct.law_const] using hh
  exact G.ellipse_critical_contradiction_bs hc hl hq pi o c D hD hpc hpc1 hpo hpi hdense hone hbox hnull

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphActionCoordinates
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]

lemma quasiTransitive_of_action (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) :
    G.QuasiTransitive := by
  refine ⟨S,hS,?_⟩
  intro v
  obtain ⟨s,hs,g,hg⟩ := hcover v
  exact ⟨s,hs,G.smulAut h g,hg⟩

lemma bounded_coordinate_jumps {A : Type*} [NormedAddCommGroup A]
    (hl : G.LocallyFinite) (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (a : Λ → A) (π : V → A) (hπ : ∀ g v, π (g • v)=a g+π v) :
    ∃ D : ℝ, 0≤D ∧ ∀ e x y, G.ends e=s(x,y) → ‖π x-π y‖≤D := by
  let F : Set (V×V) := ⋃ s∈S, (fun w => (s,w)) '' G.fullGraph.neighborSet s
  have hF : F.Finite := hS.biUnion fun s _ => (G.finite_neighbors hl s).image _
  obtain ⟨D,hD⟩ := (hF.image (fun z => ‖π z.1-π z.2‖)).bddAbove
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro e x y he
  by_cases hxy : x=y
  · subst y
    simpa only [sub_self,norm_zero] using le_max_right D 0
  · have hadj : G.fullGraph.Adj x y := (SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e,Set.mem_univ _,he⟩,hxy⟩
    obtain ⟨s,hs,g,hgx⟩ := hcover x
    change g • s=x at hgx
    let w := g⁻¹ • y
    have hgw : g • w=y := smul_inv_smul g y
    have hsw : G.fullGraph.Adj s w := by
      apply (Aut.fullGraph_adj G (G.smulAut h g) s w).mp
      change G.fullGraph.Adj (g • s) (g • w)
      rwa [hgx,hgw]
    have hf : (s,w)∈F := Set.mem_iUnion₂.mpr ⟨s,hs,w,hsw,rfl⟩
    have hd : ‖π s-π w‖≤D := hD ⟨(s,w),hf,rfl⟩
    have hdiff : π x-π y=π s-π w := by
      rw [← hgx,← hgw,hπ,hπ]
      abel
    rw [hdiff]
    exact hd.trans (le_max_left _ _)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_StructuredCoordinates
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E Λ N : Type*} (G : BondGraph V E)
  [Group Λ] [Group N] [MulAction Λ V] [MulAction Λ E]

lemma integerPairComplex_add (a b : ℤ×ℤ) :
    integerPairComplex (a+b)=integerPairComplex a+integerPairComplex b := by
  simp only [integerPairComplex,Prod.fst_add,Prod.snd_add,Int.cast_add]
  ring

lemma integerPairComplex_re (z : ℤ×ℤ) : (integerPairComplex z).re=z.1 := by
  simp [integerPairComplex]

lemma integerPairComplex_im (z : ℤ×ℤ) : (integerPairComplex z).im=z.2 := by
  simp [integerPairComplex]

lemma integer_pair_coordinate_geometry
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (a : Λ → ℤ×ℤ) (z : V → ℤ×ℤ) (honto : Surjective z)
    (hz : ∀ g v, z (g • v)=a g+z v) :
    ∃ (o : V) (c : ℕ) (D : ℝ), 0≤D ∧ integerPairComplex (z o)=0 ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        ‖integerPairComplex (z x)-integerPairComplex (z y)‖≤D) ∧
      (∀ m n : ℤ, ∃ x, (integerPairComplex (z x)).re=m ∧
        (integerPairComplex (z x)).im=n) ∧
      (∀ y, ∃ psi : G.Aut, psi.vertex o∈G.vertexBall y c ∧
        ∀ x y, integerPairComplex (z (psi.vertex x))-integerPairComplex (z (psi.vertex y))=
          integerPairComplex (z x)-integerPairComplex (z y)) := by
  let pi : V → ℂ := fun v => integerPairComplex (z v)
  have hpi : ∀ g v, pi (g • v)=integerPairComplex (a g)+pi v := by
    intro g v
    exact (congrArg integerPairComplex (hz g v)).trans (integerPairComplex_add _ _)
  obtain ⟨o,ho⟩ := honto 0
  obtain ⟨c,hc'⟩ := G.action_orbit_dense (fun g => G.smulAut ha g) (fun _ _ => rfl)
    hc S hS hcover o
  obtain ⟨D,hD,hj⟩ := G.bounded_coordinate_jumps hl ha S hS hcover
    (fun g => integerPairComplex (a g)) pi hpi
  refine ⟨o,c,D,hD,?_,?_,?_,?_⟩
  · simp [ho,integerPairComplex]
  · intro x y hxy
    obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    exact hj e x y he
  · intro m n
    obtain ⟨x,hx⟩ := honto (m,n)
    exact ⟨x,by rw [hx,integerPairComplex_re],by rw [hx,integerPairComplex_im]⟩
  · intro y
    obtain ⟨g,hg⟩ := hc' y
    refine ⟨G.smulAut ha g,hg,?_⟩
    intro x y
    change pi (g • x)-pi (g • y)=pi x-pi y
    rw [hpi,hpi]
    abel

theorem critical_null_of_action_coordinates_bs_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (hg : G.SubexponentialGrowth) (hpc : G.criticalProbability<1)
    (a : Λ → ℤ×ℤ) (z : V → ℤ×ℤ) (honto : Surjective z)
    (hz : ∀ g v, z (g • v)=a g+z v)
    (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n,
        |(z (r.vertex n)).1|≤U ∧ |(z (r.vertex n)).2|≤W) :
    G.law G.criticalProbability G.percolates=0 := by
  obtain ⟨o,c,D,hD,ho,hjump,honto',hdense⟩ :=
    G.integer_pair_coordinate_geometry hc hl ha S hS hcover a z honto hz
  apply G.critical_null_of_unbounded_projection hc hl
    (G.quasiTransitive_of_action ha S hS hcover) hg hpc
    (fun v => integerPairComplex (z v)) o c D hD ho hjump honto' hdense
  simpa only [integerPairComplex_re,integerPairComplex_im,Int.cast_abs] using hnoray

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates_bs_oai.{u_1, u_2, u_3} := @OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates_bs_oai.{u_1, u_2, u_3}
