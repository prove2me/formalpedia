-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:20:15.484646+00:00
-- url     : https://prove2.me/submissions/253024a0-878d-4b99-abb1-9ac8f4c03c7e

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_approximate_moves_contradiction
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_criticalProbability_pos
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_critical_strip_null

section
-- module Solutions.Q228_CP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

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

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

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

lemma criticalProbability_le_of_pos {p : unitInterval}
    (hp : 0 < G.law p G.percolates) : G.criticalProbability ≤ p :=
  sInf_le hp

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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_CutEdges
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

namespace CriticalPercolation.BondGraph
open scoped Classical

variable {V E : Type*}

lemma not_reachable_of_cut_closed (G : BondGraph V E) (O : Set V) (ω : Set E)
    (hc : ∀ e ∈ G.cutEdges O, ¬ω e) {a b : V} (ha : a ∉ O) (hb : b ∈ O) :
    ¬(G.openGraph ω).Reachable a b := by
  intro hab
  have hclosed : ∀ ⦃v z⦄, v ∈ Oᶜ → (G.openGraph ω).Adj v z → z ∈ Oᶜ := by
    intro v z hv hvz hz
    obtain ⟨⟨e,he,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvz
    exact hc e ⟨v,z,heq,hv,hz⟩ he
  exact (ClusterDeletion.reachable_mem_of_closed hclosed ha hab) hb

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteInduced
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_HeightCuts
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_height_interval (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite)
    (a b : ℤ) : (π ⁻¹' Set.Icc a b).Finite := by
  have hh := (Set.finite_Icc a b).biUnion (fun t _ => hπ t)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp

lemma finite_heightCut (hlocal : G.LocallyFinite) (π : V → ℤ)
    (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ)) (t : ℤ) :
    (G.heightCut π t).Finite := by
  apply (G.finite_incident hlocal (finite_height_interval π hπ (t-J) t)).subset
  rintro e ⟨x,y,he,hx,hy⟩
  have hxy := (abs_le.mp (hJ e x y he)).1
  refine ⟨x,?_,?_⟩
  · change t-(J:ℤ) ≤ π x ∧ π x ≤ t
    change ¬t<π x at hx
    change t<π y at hy
    omega
  · simp [he]

lemma heightCut_disjoint (π : V → ℤ) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (t u : ℤ) (htu : (J:ℤ) ≤ |t-u|) :
    Disjoint (G.heightCut π t) (G.heightCut π u) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨x,y,he,hx,hy⟩ ⟨a,b,hef,ha,hb⟩
  change ¬t<π x at hx
  change t<π y at hy
  change ¬u<π a at ha
  change u<π b at hb
  have hj := abs_le.mp (hJ e x y he)
  rcases Sym2.eq_iff.mp (he.symm.trans hef) with ⟨hxa,hyb⟩|⟨hxb,hya⟩
  · subst a; subst b
    rcases le_total t u with hl|hl
    · rw [abs_of_nonpos (sub_nonpos.mpr hl)] at htu
      omega
    · rw [abs_of_nonneg (sub_nonneg.mpr hl)] at htu
      omega
  · subst b; subst a
    omega

lemma heightCut_translate (π : V → ℤ) (φ : G.Aut) (a : ℤ)
    (hφ : ∀ v, π (φ.vertex v)=π v+a) (t : ℤ) :
    φ.edge '' G.heightCut π t = G.heightCut π (t+a) := by
  ext e
  constructor
  · rintro ⟨f,⟨x,y,hf,hx,hy⟩,rfl⟩
    refine ⟨φ.vertex x,φ.vertex y,?_,?_,?_⟩
    · rw [φ.preserves,hf,Sym2.map_mk]
    · change ¬t+a<π (φ.vertex x)
      rw [hφ]
      change ¬t<π x at hx
      omega
    · change t+a<π (φ.vertex y)
      rw [hφ]
      change t<π y at hy
      omega
  · rintro ⟨x,y,he,hx,hy⟩
    refine ⟨φ.edge.symm e,?_,φ.edge.apply_symm_apply e⟩
    refine ⟨φ.vertex.symm x,φ.vertex.symm y,?_,?_,?_⟩
    · have hh := (Aut.symm G φ).preserves e
      change G.ends (φ.edge.symm e) = s(φ.vertex.symm x,φ.vertex.symm y)
      change G.ends (φ.edge.symm e) = Sym2.map φ.vertex.symm (G.ends e) at hh
      rw [hh,he,Sym2.map_mk]
    · have hh := hφ (φ.vertex.symm x)
      simp only [Equiv.apply_symm_apply] at hh
      change ¬t<π (φ.vertex.symm x)
      change ¬t+a<π x at hx
      omega
    · have hh := hφ (φ.vertex.symm y)
      simp only [Equiv.apply_symm_apply] at hh
      change t<π (φ.vertex.symm y)
      change t+a<π y at hy
      omega

lemma heightCut_ncard (π : V → ℤ)
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t) (t : ℤ) :
    (G.heightCut π t).ncard = (G.heightCut π 0).ncard := by
  obtain ⟨φ,hφ⟩ := htrans t
  have he := G.heightCut_translate π φ t hφ 0
  simp only [zero_add] at he
  rw [← he,Set.ncard_image_of_injective _ φ.edge.injective]

lemma cluster_bounded_by_closed_cuts (π : V → ℤ) (ω : Set E) (a b : ℤ)
    (ha : Disjoint (G.heightCut π a) ω) (hb : Disjoint (G.heightCut π b) ω)
    (o : V) (hoa : a<π o) (hob : π o≤b) :
    G.cluster ω o ⊆ π ⁻¹' Set.Icc (a+1) b := by
  intro v hv
  constructor
  · by_contra h
    have hva : ¬a<π v := by change ¬a+1≤π v at h; omega
    exact G.not_reachable_of_cut_closed {v | a<π v} ω
      (fun e he => Set.disjoint_left.mp ha he) hva hoa hv.symm
  · by_contra h
    have hvb : b<π v := lt_of_not_ge h
    exact G.not_reachable_of_cut_closed {v | b<π v} ω
      (fun e he => Set.disjoint_left.mp hb he) (not_lt.mpr hob) hvb hv

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_TailProduct
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BernoulliProduct.mem_forceOn
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteEnergy
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BlockIndependence
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
variable {E I : Type*}

lemma blockSigma_mono {S T : Set E} (h : S ⊆ T) : blockSigma S ≤ blockSigma T := by
  apply iSup₂_le
  intro e he
  exact le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)

lemma independent_disjoint_blocks (q : E → unitInterval) (S T : Set E)
    (h : Disjoint S T) : Indep (blockSigma S) (blockSigma T) (law q) :=
  indep_iSup_of_disjoint coordinateSigma_le (independent_coordinates q) h

theorem independent_block_family (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndep (fun i => blockSigma (S i)) (law q) := by
  apply (iIndep_iff _ _).mpr
  intro t
  induction t using Finset.induction_on with
  | empty => intro f hf; simp
  | @insert i t hi ih =>
    intro f hf
    let T := ⋃ j ∈ t, S j
    have hj : ∀ j ∈ t, blockSigma (S j) ≤ blockSigma T := by
      intro j hj
      exact blockSigma_mono (fun e he => Set.mem_iUnion₂.mpr ⟨j,hj,he⟩)
    have hm : MeasurableSet[blockSigma T] (⋂ j ∈ t, f j) := by
      apply MeasurableSet.biInter t.finite_toSet.countable
      intro j hjt
      exact hj j hjt _ (hf j (Finset.mem_insert_of_mem hjt))
    have hdis : Disjoint (S i) T := by
      apply Set.disjoint_left.mpr
      intro e hei heT
      obtain ⟨j,hjt,hje⟩ := Set.mem_iUnion₂.mp heT
      exact Set.disjoint_left.mp (hS (by intro h; subst j; exact hi hjt)) hei hje
    have hmuli := ((independent_disjoint_blocks q (S i) T hdis).indepSet_of_measurableSet
      (hf i (Finset.mem_insert_self i t)) hm).measure_inter_eq_mul
    rw [Finset.set_biInter_insert,Finset.prod_insert hi,hmuli]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma independent_block_events (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (A : I → Set (Set E))
    (hA : ∀ i, MeasurableSet[blockSigma (S i)] (A i)) : iIndepSet A (law q) :=
  (independent_block_family q S hS).iIndepSets'.iIndepSet_of_mem hA
    (fun i => blockSigma_le (S i) _ (hA i))

lemma measurableSet_closed_coordinate (e : E) :
    MeasurableSet[coordinateSigma e] {ω : Set E | e ∉ ω} := by
  refine ⟨{False},MeasurableSet.singleton _,?_⟩
  ext ω
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq]
  constructor
  · intro h hp
    exact Eq.mp h hp
  · intro h
    exact propext (iff_false_intro h)

lemma measurableSet_closedBlock (S : Set E) (hS : S.Countable) :
    MeasurableSet[blockSigma S] (closedBlock S) := by
  have heq : closedBlock S = ⋂ e ∈ S, {ω : Set E | e ∉ ω} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left]
  rw [heq]
  apply MeasurableSet.biInter hS
  intro e he
  exact (le_iSup_of_le e (le_iSup_of_le he le_rfl) : coordinateSigma e ≤ blockSigma S)
    _ (measurableSet_closed_coordinate e)

lemma law_closedBlock (q : E → unitInterval) (S : Set E) (hS : S.Finite) :
    law q (closedBlock S) = ∏ e ∈ hS.toFinset, bitMeasure (q e) {False} := by
  have heq : closedBlock S = ⋂ e ∈ hS.toFinset, {ω : Set E | (e ∈ ω) = False} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left,
      Set.Finite.mem_toFinset]
    constructor
    · intro h e he
      exact propext (iff_false_intro (h he))
    · intro h e he hp
      exact Eq.mp (h e he) hp
  rw [heq,(independent_coordinates q).meas_biInter]
  · exact Finset.prod_congr rfl (fun e _ => law_coordinate q e False)
  · intro e _
    exact ⟨{False},MeasurableSet.singleton _,rfl⟩

lemma law_closedBlock_const (p : unitInterval) (S : Set E) (hS : S.Finite) :
    law (fun _ : E => p) (closedBlock S) =
      (bitMeasure p {False}) ^ S.ncard := by
  rw [law_closedBlock (fun _ : E => p) S hS,Finset.prod_const]
  rw [Set.ncard_eq_toFinset_card S hS]

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ClosedCutProbability
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma bitMeasure_false_ne_zero (p : unitInterval) (hp : (p:ℝ)<1) :
    bitMeasure p {False} ≠ 0 := by
  have hh := bitMeasure_real_singleton p False
  simp only [bitWeight,ite_false, if_false] at hh
  intro hz
  have : (bitMeasure p).real {False}=0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  linarith

theorem frequently_closedBlock_ae (p : unitInterval) (hp : (p:ℝ)<1)
    (S : ℕ → Set E) (hS : ∀ n, (S n).Finite)
    (hdis : Pairwise (fun n m => Disjoint (S n) (S m))) (N : ℕ)
    (hN : ∀ n, (S n).ncard=N) :
    ∀ᵐ ω ∂law (fun _ : E => p), ∃ᶠ n in atTop, ω ∈ closedBlock (S n) := by
  let A := fun n => closedBlock (S n)
  have hm' : ∀ n, MeasurableSet[blockSigma (S n)] (A n) :=
    fun n => measurableSet_closedBlock (S n) (hS n).countable
  have hm : ∀ n, MeasurableSet (A n) := fun n => blockSigma_le (S n) _ (hm' n)
  have hi := independent_block_events (fun _ : E => p) S hdis A hm'
  have hprob : ∀ n, law (fun _ : E => p) (A n) = (bitMeasure p {False})^N := by
    intro n
    rw [law_closedBlock_const p (S n) (hS n),hN]
  have hsum : (∑' n, law (fun _ : E => p) (A n)) = ∞ := by
    simp_rw [hprob]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (pow_ne_zero _ (bitMeasure_false_ne_zero p hp))
  have hlim := measure_limsup_eq_one hm hi hsum
  have hl : ∀ᵐ ω ∂law (fun _ : E => p), ω ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hm)).mpr hlim
  exact hl.mono (fun _ h => Filter.mem_limsup_iff_frequently_mem.mp h)

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_OneDimensionalCritical
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma spaced_integer_levels (J n m : ℕ) (hnm : n≠m) :
    (J:ℤ) ≤ |(n:ℤ)*(J+1)-(m:ℤ)*(J+1)| := by
  have hne : (n:ℤ)-(m:ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hpos : 1 ≤ |(n:ℤ)-(m:ℤ)| := Int.add_one_le_iff.mpr (abs_pos.mpr hne)
  rw [← sub_mul,abs_mul,abs_of_nonneg (by omega : (0:ℤ)≤(J:ℤ)+1)]
  nlinarith [Int.natCast_nonneg J]

theorem proper_integer_height_percolates_null (hlocal : G.LocallyFinite)
    (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t)
    (p : unitInterval) (hp : (p:ℝ)<1) : G.law p G.percolates = 0 := by
  let Cpos : ℕ → Set E := fun n => G.heightCut π ((n:ℤ)*(J+1))
  let Cneg : ℕ → Set E := fun n => G.heightCut π (-((n:ℤ)*(J+1)))
  have hpdis : Pairwise (fun n m => Disjoint (Cpos n) (Cpos m)) := by
    intro n m hnm
    exact G.heightCut_disjoint π J hJ _ _ (spaced_integer_levels J n m hnm)
  have hmdis : Pairwise (fun n m => Disjoint (Cneg n) (Cneg m)) := by
    intro n m hnm
    apply G.heightCut_disjoint π J hJ
    rw [neg_sub_neg,abs_sub_comm]
    exact spaced_integer_levels J n m hnm
  have hplus := BernoulliProduct.frequently_closedBlock_ae p hp Cpos
    (fun n => G.finite_heightCut hlocal π hπ J hJ _) hpdis (G.heightCut π 0).ncard
    (fun n => G.heightCut_ncard π htrans _)
  have hminus := BernoulliProduct.frequently_closedBlock_ae p hp Cneg
    (fun n => G.finite_heightCut hlocal π hπ J hJ _) hmdis (G.heightCut π 0).ncard
    (fun n => G.heightCut_ncard π htrans _)
  rw [BernoulliProduct.law_const] at hplus hminus
  have hno : ∀ᵐ ω ∂G.law p, ω ∉ G.percolates := by
    filter_upwards [hplus,hminus] with ω hpω hmω
    rintro ⟨o,ho⟩
    obtain ⟨n,hn,hncut⟩ := Filter.frequently_atTop.mp hpω ((π o).natAbs+1)
    obtain ⟨m,hm,hmcut⟩ := Filter.frequently_atTop.mp hmω ((π o).natAbs+1)
    have hno : π o ≤ (n:ℤ)*(J+1) := by
      have habs : π o ≤ ((π o).natAbs : ℤ) := Int.le_natAbs
      have hh : (π o).natAbs+1 ≤ (n:ℤ) := by exact_mod_cast hn
      have hprod : (n:ℤ) ≤ (n:ℤ)*(J+1) := by nlinarith [Int.natCast_nonneg n,Int.natCast_nonneg J]
      omega
    have hmo : -((m:ℤ)*(J+1)) < π o := by
      have habs : -((π o).natAbs : ℤ) ≤ π o := by
        simpa only [Int.natCast_natAbs] using neg_abs_le (π o)
      have hh : (π o).natAbs+1 ≤ (m:ℤ) := by exact_mod_cast hm
      have hprod : (m:ℤ) ≤ (m:ℤ)*(J+1) := by nlinarith [Int.natCast_nonneg m,Int.natCast_nonneg J]
      omega
    exact ho ((finite_height_interval π hπ _ _).subset
      (G.cluster_bounded_by_closed_cuts π ω _ _ hmcut hncut o hmo hno))
  rw [ae_iff] at hno
  simpa only [not_not,Set.ofPred_mem_eq] using hno

theorem proper_integer_height_critical_one (hlocal : G.LocallyFinite)
    (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t) :
    G.criticalProbability=1 := by
  apply le_antisymm le_top
  apply le_sInf
  intro p hp
  by_contra h
  have hlt : (p:ℝ)<1 := lt_of_not_ge h
  have hz := G.proper_integer_height_percolates_null hlocal π hπ J hJ htrans p hlt
  exact (ne_of_gt hp) hz

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EquivariantCoordinates
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

namespace CriticalPercolation.EquivariantCoordinates
variable {Λ N T V : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]

lemma hom_eq_of_smul_eq (a : Λ →* T)
    (hstab : ∀ (g : Λ) (v : V), g • v=v → a g=1) (g h : Λ) (v : V)
    (heq : g • v=h • v) : a g=a h := by
  have hs : (g⁻¹*h) • v=v := by rw [mul_smul,← heq,inv_smul_smul]
  have hh := hstab (g⁻¹*h) v hs
  rw [map_mul,map_inv,inv_mul_eq_one] at hh
  exact hh

lemma stabilizer_killed [IsMulTorsionFree T] (ρ : Λ →* N) (φ : N →* T)
    (hfinite : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) :
    ∀ (g : Λ) (v : V), g • v=v → (φ.comp ρ) g=1 := by
  intro g v hg
  let H := (MulAction.stabilizer Λ v).map ρ
  have hmem : ρ g ∈ H := ⟨g,hg,rfl⟩
  let : Finite H := (hfinite v).to_subtype
  have hh := isOfFinOrder_of_finite (⟨ρ g,hmem⟩ : H)
  have hm := ((φ.comp H.subtype).isOfFinOrder hh).eq_one'
  exact hm

theorem exists_equivariant (a : Λ →* T)
    (hstab : ∀ (g : Λ) (v : V), g • v=v → a g=1) :
    ∃ π : V → T, ∀ g v, π (g • v)=a g*π v := by
  let q : V → MulAction.orbitRel.Quotient Λ V := Quotient.mk''
  let r : V → V := fun v => (q v).out
  have hex : ∀ v, ∃ g : Λ, g • r v=v := by
    intro v
    exact Quotient.exact (Quotient.out_eq' (q v)).symm
  choose b hb using hex
  let π : V → T := fun v => a (b v)
  refine ⟨π,?_⟩
  intro g v
  have hr : r (g • v)=r v := by
    apply congrArg Quotient.out
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  have hh : b (g • v) • r v=(g*b v) • r v := by
    rw [mul_smul,hb,← hr,hb]
  exact (hom_eq_of_smul_eq a hstab _ _ _ hh).trans (map_mul a g (b v))

lemma surjective_of_equivariant [Nonempty V] (a : Λ →* T)
    (ha : Function.Surjective a) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v) : Function.Surjective π := by
  intro t
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨g,hg⟩ := ha (t*(π v)⁻¹)
  exact ⟨g • v,by rw [hπ,hg,inv_mul_cancel_right]⟩

lemma same_level_kernel_orbit (a : Λ →* T) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v) (x y : V)
    (hxy : y ∈ MulAction.orbit Λ x) (heq : π y=π x) :
    y ∈ MulAction.orbit a.ker x := by
  obtain ⟨g,hg⟩ := hxy
  change g • x=y at hg
  have hga : a g=1 := by
    have hh := hπ g x
    rw [hg,heq] at hh
    have hmul : a g*π x=1*π x := by simpa only [one_mul] using hh.symm
    exact mul_right_cancel hmul
  exact ⟨⟨g,hga⟩,hg⟩

theorem finite_fibers (a : Λ →* T) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v)
    (hker : ∀ v : V, (MulAction.orbit a.ker v).Finite)
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (t : T) : (π ⁻¹' {t}).Finite := by
  have hf : ∀ s : V, {v | π v=t ∧ v∈MulAction.orbit Λ s}.Finite := by
    intro s
    by_cases he : ∃ y, π y=t ∧ y∈MulAction.orbit Λ s
    · obtain ⟨y,hyt,hys⟩ := he
      apply (hker y).subset
      rintro v ⟨hvt,hvs⟩
      apply same_level_kernel_orbit a π hπ y v _ (hvt.trans hyt.symm)
      rw [MulAction.orbit_eq_iff.mpr hys]
      exact hvs
    · convert Set.finite_empty using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun h => he ⟨v,h⟩
  apply (hS.biUnion fun s _ => hf s).subset
  intro v hv
  obtain ⟨s,hs,hvs⟩ := hcover v
  exact Set.mem_iUnion₂.mpr ⟨s,hs,hv,hvs⟩

end CriticalPercolation.EquivariantCoordinates
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteKernelOrbits
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

namespace CriticalPercolation.EquivariantCoordinates
variable {Λ N T V : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]

theorem finite_orbit_of_finite_image (ρ : Λ →* N) (L : Subgroup Λ)
    (hfin : (L.map ρ : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite) (v : V) :
    (MulAction.orbit L v).Finite := by
  have hex : ∀ a : L.map ρ, ∃ g : Λ, g∈L ∧ ρ g=a := by
    intro a
    exact a.property
  choose r hr using hex
  let : Finite (L.map ρ) := hfin.to_subtype
  have hset : (⋃ a : L.map ρ, (fun x : V => r a • x) '' MulAction.orbit ρ.ker v).Finite :=
    Set.finite_iUnion (fun a => (hker v).image _)
  apply hset.subset
  rintro w ⟨g,hg⟩
  change (g : Λ) • v=w at hg
  let a : L.map ρ := ⟨ρ g,⟨g,g.property,rfl⟩⟩
  have hk : (r a)⁻¹*(g : Λ)∈ρ.ker := by
    change ρ ((r a)⁻¹*(g : Λ))=1
    rw [map_mul,map_inv,(hr a).2]
    exact inv_mul_cancel (ρ g)
  apply Set.mem_iUnion.mpr
  refine ⟨a,((r a)⁻¹*(g : Λ)) • v,?_,?_⟩
  · exact ⟨⟨(r a)⁻¹*(g : Λ),hk⟩,rfl⟩
  · change r a • (((r a)⁻¹*(g : Λ)) • v)=w
    rw [← mul_smul,mul_inv_cancel_left,hg]

lemma finite_composite_kernel_orbits (ρ : Λ →* N) (φ : N →* T)
    (hφ : (φ.ker : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite) (v : V) :
    (MulAction.orbit (φ.comp ρ).ker v).Finite := by
  apply finite_orbit_of_finite_image ρ _ _ hker v
  apply hφ.subset
  rintro n ⟨g,hg,rfl⟩
  exact hg

lemma finite_vertices_of_finite_quotient (ρ : Λ →* N) [Finite N]
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) :
    (Set.univ : Set V).Finite := by
  have hf : ∀ s : V, (MulAction.orbit Λ s).Finite := by
    intro s
    have hh := finite_orbit_of_finite_image ρ ⊤ (Set.toFinite _) hker s
    apply hh.subset
    rintro v ⟨g,hg⟩
    exact ⟨⟨g,Subgroup.mem_top g⟩,hg⟩
  apply (hS.biUnion fun s _ => hf s).subset
  intro v _
  obtain ⟨s,hs,hvs⟩ := hcover v
  exact Set.mem_iUnion₂.mpr ⟨s,hs,hvs⟩

end CriticalPercolation.EquivariantCoordinates
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphActionCoordinates
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

theorem finite_by_integer_critical_one {N : Type*} [Group N]
    (hl : G.LocallyFinite) (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* N) (hρ : Function.Surjective ρ)
    (φ : N →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (hf : (φ.ker : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) :
    G.criticalProbability=1 := by
  let a := φ.comp ρ
  obtain ⟨π,hπ⟩ := EquivariantCoordinates.exists_equivariant a
    (EquivariantCoordinates.stabilizer_killed ρ φ hstab)
  let πa : V → ℤ := fun v => (π v).toAdd
  have hπa : ∀ (g : Λ) (v : V), πa (g • v)=(a g).toAdd+πa v := by
    intro g v
    exact congrArg Multiplicative.toAdd (hπ g v)
  have hfib : ∀ t : ℤ, (πa ⁻¹' {t}).Finite := by
    intro t
    exact EquivariantCoordinates.finite_fibers a π hπ
      (EquivariantCoordinates.finite_composite_kernel_orbits ρ φ hf hker)
      S hS hcover (Multiplicative.ofAdd t)
  have htrans : ∀ t : ℤ, ∃ ψ : G.Aut, ∀ v, πa (ψ.vertex v)=πa v+t := by
    intro t
    obtain ⟨g,hg⟩ := hφ.comp hρ (Multiplicative.ofAdd t)
    refine ⟨G.smulAut h g,?_⟩
    intro v
    change πa (g • v)=πa v+t
    rw [hπa]
    rw [show a g=Multiplicative.ofAdd t from hg]
    exact add_comm _ _
  obtain ⟨D,hD,hjump⟩ := G.bounded_coordinate_jumps hl h S hS hcover
    (fun g => (a g).toAdd) πa hπa
  obtain ⟨J,hJ⟩ := exists_nat_gt D
  apply G.proper_integer_height_critical_one hl πa hfib J _ htrans
  intro e x y he
  have hh := (hjump e x y he).trans hJ.le
  rw [Int.norm_eq_abs,← Int.cast_abs] at hh
  exact_mod_cast hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_DensityModular
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
open scoped Classical

variable {E : Type*} [Fintype E]

lemma density_modular (w : E → Prop → ℝ) (x y : E → Prop) :
    density w x * density w y = density w (x ⊓ y) * density w (x ⊔ y) := by
  unfold density
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  simp only [Pi.inf_apply, Pi.sup_apply]
  by_cases hx : x e <;> by_cases hy : y e <;> simp [hx, hy, mul_comm]

lemma expect_mul_ge (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (f g : (E → Prop) → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hf : Monotone f) (hg : Monotone g) :
    expect w f * expect w g ≤ expect w (fun ω => f ω * g ω) := by
  have h := fkg f g (density w) (fun ω => density_nonneg hpos ω) hf0 hg0 hf hg
    (fun x y => le_of_eq (density_modular w x y))
  simpa only [expect, sum_density w hw, one_mul] using h

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ContinuousExpectWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation.FiniteProduct
variable {E B : Type*} [Fintype E] [Fintype B]

lemma continuous_expect_weights (f : (E → B) → ℝ) :
    Continuous (fun w : E → B → ℝ => expect w f) := by
  classical
  unfold expect density
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  exact (continuous_apply (ω e)).comp (continuous_apply e)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

lemma hitEvent_mono_edges (o : V) (A : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    ω ∈ G.hitEvent o A → ω' ∈ G.hitEvent o A :=
  fun hω => hω.mono (Set.inter_subset_inter_left A (G.cluster_mono h o))

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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ConditionalGluing
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma seedHitEvent_upper (B T : Set V) : IsUpperSet (G.seedHitEvent B T) := by
  intro ω τ hωτ hω
  obtain ⟨b,hb,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨b,hb,G.hitEvent_mono_edges b T hωτ hω⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorGraph
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma coordinate_ball_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    {v w : V} {n : ℕ} (hw : w∈G.vertexBall v n) : |f w-f v|≤n*ρ := by
  induction n generalizing w with
  | zero =>
    have he : w=v := hw
    subst w
    simp
  | succ n ih =>
    rcases hw with hw|hw
    · exact (ih hw).trans (by push_cast <;> nlinarith)
    · obtain ⟨u,hu,huw⟩ := Set.mem_iUnion₂.mp hw
      calc
        |f w-f v| ≤ |f w-f u|+|f u-f v| := abs_sub_le _ _ _
        _ ≤ ρ+n*ρ := add_le_add (hf huw.symm) (ih hu)
        _ = _ := by push_cast <;> ring

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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayMoves
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma walk_reachable_induced (S : Set V) (ω : Set E) {a b : V}
    (w : (G.openGraph ω).Walk a b) (hw : ∀ x∈w.support,x∈S) :
    (G.openGraph (ω∩G.inducedEdges S)).Reachable a b := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac w ih =>
    have hc : c∈S := hw c (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr w.start_mem_support)
    have ha : a∈S := hw a (by simp)
    exact ((G.open_induced_adj S ω a c).mpr ⟨hac,ha,hc⟩).reachable.trans
      (ih (fun x hx => hw x (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx)))

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_OpenRay
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_InducedCritical
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma induce_locallyFinite (hl : G.LocallyFinite) (S : Set V) : (G.induce S).LocallyFinite := by
  intro v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hl v.val)).subset
  intro e he
  have hh : v.val∈Sym2.map Subtype.val ((G.induce S).ends e) := Sym2.mem_map.mpr ⟨v,he,rfl⟩
  rwa [G.induce_ends_map] at hh

lemma induce_fullGraph_adj (S : Set V) (x y : S) :
    (G.induce S).fullGraph.Adj x y → G.fullGraph.Adj x.val y.val := by
  intro h
  exact G.openGraph_mono (Set.subset_univ _) ((G.induce_adj S Set.univ x y).mp h)

lemma induce_vertexBall_subset (S : Set V) (o : S) (n : ℕ) :
    Subtype.val '' (G.induce S).vertexBall o n ⊆ G.vertexBall o.val n := by
  induction n with
  | zero => rintro x ⟨y,rfl,rfl⟩; rfl
  | succ n ih =>
    rintro x ⟨y,hy,rfl⟩
    rcases hy with hy|hy
    · exact G.vertexBall_mono o.val (Nat.le_succ n) (ih ⟨y,hy,rfl⟩)
    · obtain ⟨z,hz,hzy⟩ := Set.mem_iUnion₂.mp hy
      exact G.vertexBall_step (ih ⟨z,hz,rfl⟩) (G.induce_fullGraph_adj S z y hzy)

lemma induce_subexponential (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth) (S : Set V) :
    (G.induce S).SubexponentialGrowth := by
  intro o ε hε
  obtain ⟨N,hN⟩ := hg o.val ε hε
  refine ⟨N,fun n hn => ?_⟩
  have hcard : ((G.induce S).vertexBall o n).ncard ≤ (G.vertexBall o.val n).ncard := by
    rw [←Set.ncard_image_of_injective _ Subtype.val_injective]
    exact Set.ncard_le_ncard (G.induce_vertexBall_subset S o n) (G.vertexBall_finite hl o.val n)
  have hpositive : 0<(((G.induce S).vertexBall o n).ncard : ℝ) := by
    exact_mod_cast (Set.ncard_pos ((G.induce S).vertexBall_finite (G.induce_locallyFinite hl S) o n)).mpr
      ⟨o,(G.induce S).mem_vertexBall_self o n⟩
  exact (Real.log_le_log hpositive (by exact_mod_cast hcard)).trans (hN n hn)

lemma induce_percolates_subset (S : Set V) :
    (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (G.inducedEdges S)) ⁻¹' (G.induce S).percolates
      ⊆G.percolates := by
  rintro ω ⟨o,ho⟩
  refine ⟨o.val,?_⟩
  have hi := ho.image Subtype.val_injective.injOn
  rw [G.induce_cluster_image] at hi
  exact hi.mono (G.cluster_mono (by rintro e ⟨a,ha,rfl⟩; exact ha) o.val)

lemma law_induce [Countable V] [Countable E] (S : Set V) (p : unitInterval) :
    (G.law p).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (G.inducedEdges S)) =
      (G.induce S).law p := by
  simpa only [law,BernoulliProduct.law_const] using
    BernoulliProduct.law_map_restrict (fun _ : E => p) (G.inducedEdges S)

lemma law_induce_percolates_le [Countable V] [Countable E] (S : Set V) (p : unitInterval) :
    (G.induce S).law p (G.induce S).percolates ≤ G.law p G.percolates := by
  rw [←G.law_induce S p,Measure.map_apply]
  · exact measure_mono (G.induce_percolates_subset S)
  · exact Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  · exact (G.induce S).measurableSet_percolates

lemma criticalProbability_le_induce [Countable V] [Countable E] (S : Set V) :
    G.criticalProbability≤(G.induce S).criticalProbability := by
  apply le_sInf
  intro p hp
  exact G.criticalProbability_le_of_pos (hp.trans_le (G.law_induce_percolates_le S p))

lemma induce_criticalProbability_eq_of_pos [Countable V] [Countable E] (S : Set V)
    (hpos : 0<(G.induce S).law G.criticalProbability (G.induce S).percolates) :
    (G.induce S).criticalProbability=G.criticalProbability :=
  le_antisymm ((G.induce S).criticalProbability_le_of_pos hpos) (G.criticalProbability_le_induce S)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ComponentCritical
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma domainComponent_subset {S : Set V} {o : V} (ho : o∈S) :
    G.domainComponent S o⊆S := by
  have h := G.induced_cluster_subset S Set.univ (⟨o,ho⟩ : S)
  simpa only [Set.image_univ,Subtype.range_coe,domainComponent] using h

lemma domainComponent_self (S : Set V) (o : V) : o∈G.domainComponent S o :=
  SimpleGraph.Reachable.refl o

lemma domainComponent_closed (S : Set V) (o : V) {x y : V}
    (hx : x∈G.domainComponent S o) (hxy : (G.openGraph (G.inducedEdges S)).Adj x y) :
    y∈G.domainComponent S o := hx.trans hxy.reachable

lemma domainComponent_connected (S : Set V) (o : V) :
    (G.induce (G.domainComponent S o)).fullGraph.Connected := by
  let C := G.domainComponent S o
  let a : C := ⟨o,G.domainComponent_self S o⟩
  have hreach : ∀ x : C, ((G.induce C).fullGraph).Reachable a x := by
    intro x
    apply (G.induce_reachable C Set.univ a x).mpr
    rw [Set.image_univ,Subtype.range_coe]
    have h : (G.openGraph (G.inducedEdges S)).Reachable o x.val := x.property
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    have H : ∀ y, Relation.ReflTransGen (G.openGraph (G.inducedEdges S)).Adj o y →
        Relation.ReflTransGen (G.openGraph (G.inducedEdges C)).Adj o y := by
      intro y hy
      induction hy with
      | refl => exact .refl
      | @tail b c hr hadj ih =>
        have hb : b∈C := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hr
        have hc : c∈C := G.domainComponent_closed S o hb hadj
        obtain ⟨⟨e,he,hend⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hadj
        have hC : e∈G.inducedEdges C := by
          intro v hv
          rw [hend] at hv
          rcases Sym2.mem_iff.mp hv with rfl|rfl
          · exact hb
          · exact hc
        exact ih.tail ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,hC,hend⟩,hne⟩)
    exact H _ h
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨a,hreach⟩

lemma OpenRay.reachable_start {ω : Set E} (r : G.OpenRay ω) (n : ℕ) :
    (G.openGraph ω).Reachable (r.vertex 0) (r.vertex n) := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact ih.trans (r.adjacent n).reachable

lemma OpenRay.percolates {ω : Set E} (r : G.OpenRay ω) : ω∈G.percolates := by
  refine ⟨r.vertex 0,?_⟩
  exact (Set.infinite_range_of_injective r.injective).mono (by
    rintro x ⟨n,rfl⟩
    exact r.reachable_start G n)

lemma OpenRay.mem_domainComponent {ω : Set E} (r : G.OpenRay ω) (S : Set V)
    (hS : ∀ n, r.vertex n∈S) (n : ℕ) :
    r.vertex n∈G.domainComponent S (r.vertex 0) := by
  induction n with
  | zero => exact G.domainComponent_self S _
  | succ n ih =>
    apply G.domainComponent_closed S _ ih
    apply G.openGraph_mono Set.inter_subset_right
    exact (G.open_induced_adj S ω _ _).mpr ⟨r.adjacent n,hS n,hS (n+1)⟩

lemma ae_restriction_not_percolates [Countable V] [Countable E]
    (S : Set V) (p : unitInterval) (h : (G.induce S).law p (G.induce S).percolates=0) :
    ∀ᵐ ω ∂G.law p, Subtype.val ⁻¹' ω∉(G.induce S).percolates := by
  rw [←G.law_induce S p,Measure.map_apply] at h
  · apply ae_iff.mpr
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,not_not]
  · exact Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  · exact (G.induce S).measurableSet_percolates

theorem bounded_ray_critical_component [Countable V] [Countable E]
    (u v : V → ℝ)
    (hbad : ¬∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
        ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ∃ (k : ℕ) (o : V),
      let S := {x | |u x|≤(k:ℝ) ∧ |v x|≤(k:ℝ)}
      o∈S ∧
      let H := G.induce (G.domainComponent S o)
      H.criticalProbability=G.criticalProbability ∧
      0<H.law H.criticalProbability H.percolates := by
  let S : ℕ → Set V := fun k => {x | |u x|≤(k:ℝ) ∧ |v x|≤(k:ℝ)}
  have hex : ∃ (k : ℕ) (o : V), o∈S k ∧
      0<(G.induce (G.domainComponent (S k) o)).law G.criticalProbability
        (G.induce (G.domainComponent (S k) o)).percolates := by
    by_contra hh
    push Not at hh
    have ha : ∀ k o, ∀ᵐ ω ∂G.law G.criticalProbability,
        o∈S k → Subtype.val ⁻¹' ω∉(G.induce (G.domainComponent (S k) o)).percolates := by
      intro k o
      by_cases ho : o∈S k
      · exact (G.ae_restriction_not_percolates _ _ (le_antisymm (hh k o ho) bot_le)).mono
          (fun _ h _ => h)
      · exact Filter.Eventually.of_forall (fun _ h => (ho h).elim)
    have hall : ∀ᵐ ω ∂G.law G.criticalProbability, ∀ k o,
        o∈S k → Subtype.val ⁻¹' ω∉(G.induce (G.domainComponent (S k) o)).percolates :=
      (ae_all_iff.mpr fun k => ae_all_iff.mpr (ha k))
    apply hbad
    filter_upwards [hall] with ω hω
    rintro ⟨r,U,W,hr⟩
    obtain ⟨k,hk⟩ := exists_nat_ge (max U W)
    have hrS : ∀ n, r.vertex n∈S k := fun n =>
      ⟨(hr n).1.trans ((le_max_left _ _).trans hk),
       (hr n).2.trans ((le_max_right _ _).trans hk)⟩
    exact hω k (r.vertex 0) (hrS 0)
      ((r.induce G _ (r.mem_domainComponent G _ hrS)).percolates _)
  obtain ⟨k,o,ho,hp⟩ := hex
  have heq := G.induce_criticalProbability_eq_of_pos (G.domainComponent (S k) o) hp
  exact ⟨k,o,ho,heq,by rwa [heq]⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_InducedAutomorphism
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

lemma Aut.inducedEdges_image (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) :
    phi.edge '' G.inducedEdges S=G.inducedEdges S := by
  ext e
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (Aut.inducedEdges_mem G phi S hS a).mpr ha
  · intro he
    exact ⟨phi.edge.symm e,(Aut.inducedEdges_mem G phi S hS (phi.edge.symm e)).mp
      (by simpa only [Equiv.apply_symm_apply] using he),phi.edge.apply_symm_apply e⟩

lemma Aut.domainComponent_image (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (o : V) :
    phi.vertex '' G.domainComponent S o=G.domainComponent S (phi.vertex o) := by
  change phi.vertex '' G.cluster (G.inducedEdges S) o=G.cluster (G.inducedEdges S) (phi.vertex o)
  rw [Aut.cluster_image,Aut.inducedEdges_image G phi S hS]

lemma domainComponent_eq_of_mem (S : Set V) {o x : V} (hx : x∈G.domainComponent S o) :
    G.domainComponent S x=G.domainComponent S o := by
  ext y
  exact ⟨fun h => hx.trans h,fun h => hx.symm.trans h⟩

lemma Aut.preserves_domainComponent (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (o x : V)
    (hx : x∈G.domainComponent S o) (hpx : phi.vertex x∈G.domainComponent S o) :
    ∀ y, phi.vertex y∈G.domainComponent S o ↔ y∈G.domainComponent S o := by
  have heq : phi.vertex '' G.domainComponent S o=G.domainComponent S o := calc
    phi.vertex '' G.domainComponent S o=phi.vertex '' G.domainComponent S x :=
      congrArg (Set.image phi.vertex) (G.domainComponent_eq_of_mem S hx).symm
    _=G.domainComponent S (phi.vertex x) := Aut.domainComponent_image G phi S hS x
    _=G.domainComponent S o := G.domainComponent_eq_of_mem S hpx
  intro y
  constructor
  · intro hy
    have him : phi.vertex y∈phi.vertex '' G.domainComponent S o := by rwa [heq]
    obtain ⟨z,hz,hzy⟩ := him
    exact phi.vertex.injective hzy ▸ hz
  · intro hy
    rw [←heq]
    exact ⟨y,hy,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_RestrictedAction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]

lemma restricted_preservesEnds (ha : G.PreservesEnds (Λ := Λ))
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    let _ := G.restrictedEdgeAction ha C L hL
    (G.induce C).PreservesEnds (Λ := L) := by
  intro _ _ g e
  exact (Aut.restrict G (G.smulAut ha g.val) C (hL g.property)).preserves e

lemma restricted_kernel_orbits {N : Type*} [Group N]
    (ρ : Λ →* N) (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    ∀ v : C, (MulAction.orbit (ρ.comp L.subtype).ker v).Finite := by
  intro _ v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hker v.val)).subset
  rintro w ⟨g,hg⟩
  refine ⟨⟨(g.val : Λ),g.property⟩,?_⟩
  exact congrArg Subtype.val hg

lemma restricted_stabilizer_images {N : Type*} [Group N]
    (ρ : Λ →* N)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    ∀ v : C, ((MulAction.stabilizer L v).map (ρ.comp L.subtype) : Set N).Finite := by
  intro _ v
  apply (hstab v.val).subset
  rintro n ⟨g,hg,rfl⟩
  exact ⟨g.val,congrArg Subtype.val hg,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ComponentAction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
variable {V E Λ T : Type*} (G : BondGraph V E)
  [Group Λ] [Group T] [MulAction Λ V] [MulAction Λ E]

lemma componentKernel_same_level
    (ha : G.PreservesEnds (Λ := Λ)) (a : Λ →* T) (z : V → T)
    (hz : ∀ g v, z (g • v)=a g*z v)
    (Q : Set T) (o : V) (x y : G.domainComponent (z ⁻¹' Q) o)
    (horbit : y.val∈MulAction.orbit Λ x.val) (hlevel : z y.val=z x.val) :
    ∃ g : componentKernel a (G.domainComponent (z ⁻¹' Q) o),
      (g.val : Λ) • x.val=y.val := by
  obtain ⟨g,hg⟩ := EquivariantCoordinates.same_level_kernel_orbit a z hz x.val y.val horbit hlevel
  change g.val • x.val=y.val at hg
  have hS : ∀ v, (G.smulAut ha g.val).vertex v∈z ⁻¹' Q ↔ v∈z ⁻¹' Q := by
    intro v
    change z (g.val • v)∈Q ↔ z v∈Q
    rw [hz,g.property,one_mul]
  have hp := Aut.preserves_domainComponent G (G.smulAut ha g.val) (z ⁻¹' Q)
    hS o x.val x.property (by change g.val • x.val∈_; rw [hg]; exact y.property)
  exact ⟨⟨g.val,g.property,hp⟩,hg⟩

theorem componentKernel_finite_orbits
    (ha : G.PreservesEnds (Λ := Λ))
    (R : Set V) (hR : R.Finite) (hcover : ∀ v, ∃ s∈R, v∈MulAction.orbit Λ s)
    (a : Λ →* T) (z : V → T) (hz : ∀ g v, z (g • v)=a g*z v)
    (Q : Set T) (hQ : Q.Finite) (o : V) (ho : z o∈Q) :
    let C := G.domainComponent (z ⁻¹' Q) o
    let L := componentKernel a C
    let _ := restrictedVertexAction C L (componentKernel_le a C)
    ∃ S : Set C, S.Finite ∧ ∀ v : C, ∃ s∈S, v∈MulAction.orbit L s := by
  let C := G.domainComponent (z ⁻¹' Q) o
  let L := componentKernel a C
  let _ := restrictedVertexAction C L (componentKernel_le a C)
  let I : Set (V×T) := {q | q.1∈R ∧ q.2∈Q ∧ ∃ x : C,
    x.val∈MulAction.orbit Λ q.1 ∧ z x.val=q.2}
  have hI : I.Finite := (hR.prod hQ).subset (fun _ h => ⟨h.1,h.2.1⟩)
  let _ := hI.to_subtype
  have hex : ∀ q : I, ∃ x : C, x.val∈MulAction.orbit Λ q.val.1 ∧ z x.val=q.val.2 :=
    fun q => q.property.2.2
  choose r hr using hex
  refine ⟨Set.range r,Set.finite_range r,?_⟩
  intro y
  obtain ⟨s,hs,hys⟩ := hcover y.val
  have hyQ : z y.val∈Q := G.domainComponent_subset ho y.property
  let q : I := ⟨(s,z y.val),hs,hyQ,y,hys,rfl⟩
  refine ⟨r q,⟨q,rfl⟩,?_⟩
  have hyorbit : y.val∈MulAction.orbit Λ (r q).val := by
    rw [MulAction.orbit_eq_iff.mpr (hr q).1]
    exact hys
  obtain ⟨g,hg⟩ := G.componentKernel_same_level ha a z hz Q o (r q) y hyorbit (hr q).2.symm
  exact ⟨g,Subtype.ext hg⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Classification_RestrictedQuotient
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
variable {V Λ N T : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]

lemma rangeRestrict_kernel_orbits (f : Λ →* N)
    (hf : ∀ v : V, (MulAction.orbit f.ker v).Finite) :
    ∀ v : V, (MulAction.orbit f.rangeRestrict.ker v).Finite := by
  intro v
  apply (hf v).subset
  rintro w ⟨g,hg⟩
  have hgm : f g.val=1 := congrArg Subtype.val g.property
  exact ⟨⟨g.val,hgm⟩,hg⟩

lemma rangeRestrict_stabilizer_images (f : Λ →* N)
    (hf : ∀ v : V, ((MulAction.stabilizer Λ v).map f : Set N).Finite) :
    ∀ v : V, ((MulAction.stabilizer Λ v).map f.rangeRestrict : Set f.range).Finite := by
  intro v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hf v)).subset
  rintro n ⟨g,hg,rfl⟩
  exact ⟨g,hg,rfl⟩

lemma component_quotient_le_kernel (ρ : Λ →* N) (φ : N →* T) (C : Set V) :
    (ρ.comp (componentKernel (φ.comp ρ) C).subtype).range≤φ.ker := by
  rintro n ⟨g,rfl⟩
  exact g.property.1

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ActionCoordinates
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_PercolationTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteOpenWitness
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

lemma continuous_bitWeight (b : Prop) : Continuous (fun p : unitInterval => bitWeight p b) := by
  by_cases hb : b
  · simpa [bitWeight, hb] using (continuous_subtype_val : Continuous (fun p : unitInterval => (p : ℝ)))
  · simp only [bitWeight, ite_eq_right hb]
    fun_prop

lemma continuous_real_law_finite [Fintype E] (A : Set (Set E)) :
    Continuous (fun p : unitInterval => (law (fun _ : E => p)).real A) := by
  have h (p : unitInterval) : (law (fun _ : E => p)).real A =
      FiniteProduct.expect (fun _ : E => bitWeight p)
        (fun ω : E → Prop => A.indicator (fun _ => (1 : ℝ)) {e | ω e}) := by
    rw [← integral_law_eq_expect]
    exact (integral_indicator_one (.of_discrete) :
      (∫ ω, A.indicator (1 : Set E → ℝ) ω ∂law (fun _ : E => p)) = _).symm
  simp_rw [h]
  apply (FiniteProduct.continuous_expect_weights _).comp
  exact continuous_pi fun _ => continuous_pi fun b => continuous_bitWeight b

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

lemma continuous_real_law_restrict (s : Set E) (hs : s.Finite) (A : Set (Set E)) :
    Continuous (fun p : unitInterval => (law (fun _ : E => p)).real
      {ω | s ∩ ω ∈ A}) := by
  let := hs.fintype
  simp_rw [real_law_restrict _ s hs A]
  exact continuous_real_law_finite _

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

lemma lowerSemicontinuous_real_finiteWitness [Countable E] (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A) :
    LowerSemicontinuous (fun p : unitInterval => (law (fun _ : E => p)).real A) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  intro p a ha
  have ht := (tendsto_real_finiteWitness p A hmono hw K).eventually (lt_mem_nhds ha)
  obtain ⟨n, hn⟩ := ht.exists
  have hc := (continuous_real_law_restrict (K n) (K.finite n) A).continuousAt (x := p)
  filter_upwards [hc.eventually (lt_mem_nhds hn)] with q hq
  exact lt_of_lt_of_le hq (measureReal_mono (fun ω hω => hmono Set.inter_subset_right hω))

lemma exists_lower_parameter [Countable E] {I : Type*} [Finite I]
    (A : I → Set (Set E)) (hmono : ∀ i, IsUpperSet (A i))
    (hw : ∀ i, HasFiniteOpenWitness (A i)) (p : unitInterval) (hp : 0 < p)
    (a : I → ℝ) (ha : ∀ i, a i < (law (fun _ : E => p)).real (A i)) :
    ∃ q : unitInterval, (p : ℝ) / 2 ≤ q ∧ q < p ∧
      ∀ i, a i < (law (fun _ : E => q)).real (A i) := by
  have hall : ∀ᶠ q in 𝓝 p, ∀ i, a i < (law (fun _ : E => q)).real (A i) :=
    Filter.eventually_all.mpr fun i =>
      lowerSemicontinuous_real_finiteWitness (A i) (hmono i) (hw i) p (a i) (ha i)
  have hp' : (0 : ℝ) < p := hp
  have hhalf : ∀ᶠ q : unitInterval in 𝓝 p, (p : ℝ) / 2 < q :=
    continuous_subtype_val.continuousAt.eventually (lt_mem_nhds (by linarith : (p : ℝ) / 2 < p))
  have : NeBot (𝓝[<] p) := nhdsLT_neBot_of_exists_lt ⟨0, hp⟩
  obtain ⟨q, hq, hqp, hqA⟩ :=
    ((hhalf.filter_mono nhdsWithin_le_nhds).and
      ((show ∀ᶠ q in 𝓝[<] p, q < p from self_mem_nhdsWithin).and
        (hall.filter_mono nhdsWithin_le_nhds))).exists
  exact ⟨q, le_of_lt hq, hqp, hqA⟩

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_MoveWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma walk_induced_support {S : Set V} {ω : Set E} {a b : V}
    (w : (G.openGraph (ω∩G.inducedEdges S)).Walk a b) (hb : b∈S) :
    ∀ x∈w.support, x∈S := by
  induction w with
  | nil =>
    intro x hx
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
    subst x
    exact hb
  | @cons a c b hac w ih =>
    intro x hx
    rcases (List.mem_cons.mp hx) with hxa|hx
    · rw [hxa]
      exact ((G.open_induced_adj S ω a c).mp hac).2.1
    · exact ih hb x hx

lemma boxMove_eq_restrictedSeed (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    G.boxMove t z m q B y s=G.restrictedSeed (G.vertexBall y m)
      {b | (|t b-(t y+1)|≤q ∧ |z b-(z y+s)|≤q) ∧ |t b-t y|≤B ∧ |z b-z y|≤B}
      (G.inducedEdges {x | |t x-t y|≤B ∧ |z x-z y|≤B}) := by
  ext ω
  constructor
  · rintro ⟨a,ha,b,w,hw,ht,hz⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,b,G.walk_reachable_induced _ ω w hw,⟨ht,hz⟩,hw b w.end_mem_support⟩
  · intro h
    obtain ⟨a,ha,b,⟨w⟩,hb⟩ := Set.mem_iUnion₂.mp h
    let w' := w.mapLe (G.openGraph_mono Set.inter_subset_left)
    refine ⟨a,ha,b,w',?_,hb.1.1,hb.1.2⟩
    intro x hx
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
    exact G.walk_induced_support w hb.2 x hx

lemma restrictedSeed_upper (A T : Set V) (S : Set E) : IsUpperSet (G.restrictedSeed A T S) := by
  intro ω τ h hω
  exact G.seedHitEvent_upper A T (Set.inter_subset_inter_left S h) hω

lemma restrictedSeed_finiteWitness (A T : Set V) (S : Set E) :
    BernoulliProduct.HasFiniteOpenWitness (G.restrictedSeed A T S) := by
  intro ω hω
  obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hω
  obtain ⟨K,hK,hKsub,hKr⟩ := G.mem_cluster_finite_witness hr
  refine ⟨K,hK,fun _ he => (hKsub he).1,?_⟩
  change K∩S∈G.seedHitEvent A T
  rw [Set.inter_eq_left.mpr (fun _ he => (hKsub he).2)]
  exact Set.mem_iUnion₂.mpr ⟨a,ha,b,hKr,hb⟩

lemma boxMove_upper (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    IsUpperSet (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_upper _ _ _

lemma boxMove_finiteWitness (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    BernoulliProduct.HasFiniteOpenWitness (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_finiteWitness _ _ _

lemma boxMove_measurable [Countable V] [Countable E]
    (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    MeasurableSet (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_measurable _ _ _

lemma lower_two_boxMoves [Countable E] (t z : V → ℝ) (m : ℕ) (q B : ℝ)
    (o : V) (pc : unitInterval) (hpc : 0<pc) (eta : ℝ)
    (hm : ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.boxMove t z m q B o (Corridor.sign b))) :
    ∃ p : unitInterval, (pc : ℝ)/2≤p ∧ p<pc ∧ ∀ b : Bool,
      1-eta<(BernoulliProduct.law (fun _ : E => p)).real
        (G.boxMove t z m q B o (Corridor.sign b)) :=
  BernoulliProduct.exists_lower_parameter _ (fun _ => G.boxMove_upper _ _ _ _ _ _ _)
    (fun _ => G.boxMove_finiteWitness _ _ _ _ _ _ _) pc hpc (fun _ => 1-eta) hm

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_MeasurableSetRestrict
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

lemma measurableSet_restrict (s : Set E) (hs : s.Finite) (A : Set (Set E)) :
    MeasurableSet {ω | s ∩ ω ∈ A} := by
  let := hs.fintype
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have he : {ω : Set E | s ∩ ω ∈ A} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        {u : Set s | Subtype.val '' u ∈ A} := by
    ext ω
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
      ext e
      simp
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hi]
  rw [he]
  exact hf (.of_discrete)

lemma measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A) : MeasurableSet A := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  rw [← finiteWitness_exhaustion A hmono hw K]
  exact MeasurableSet.iUnion fun n => measurableSet_restrict (K n) (K.finite n) A

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_MonotoneIndicatorUpper
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

lemma monotone_indicator_upper (A : Set (Set E)) (hA : IsUpperSet A) :
    Monotone (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  intro ω ω' h
  change (if {e | ω e} ∈ A then (1 : ℝ) else 0) ≤
    (if {e | ω' e} ∈ A then (1 : ℝ) else 0)
  split_ifs with ha hb
  · rfl
  · exact (hb (hA h ha)).elim
  · norm_num
  · rfl

lemma real_eq_expect_indicator [Fintype E] (q : E → unitInterval) (A : Set (Set E)) :
    (law q).real A = FiniteProduct.expect (fun e => bitWeight (q e))
      (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  rw [← integral_law_eq_expect]
  exact (integral_indicator_one (.of_discrete)).symm

lemma finite_harris [Fintype E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) := by
  simp_rw [real_eq_expect_indicator]
  have he : (fun ω : E → Prop => (A ∩ B).indicator (1 : Set E → ℝ) {e | ω e}) =
      (fun ω => A.indicator (1 : Set E → ℝ) {e | ω e} *
        B.indicator (1 : Set E → ℝ) {e | ω e}) := by
    funext ω
    by_cases ha : {e | ω e} ∈ A <;> by_cases hb : {e | ω e} ∈ B <;> simp [ha, hb]
  rw [he]
  exact FiniteProduct.expect_mul_ge _ (fun e => bitWeight_sum (q e))
    (fun e b => bitWeight_nonneg (q e) b) _ _
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (monotone_indicator_upper A hA) (monotone_indicator_upper B hB)

lemma real_law_restrict_general (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (A : Set (Set E)) :
    (law q).real {ω | s ∩ ω ∈ A} =
      (law (fun e : s => q e)).real {ω | Subtype.val '' ω ∈ A} := by
  let := hs.fintype
  have hi (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
    ext e
    simp
  rw [← law_map_restrict q s]
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [Measure.real]
  rw [Measure.map_apply hf (.of_discrete)]
  simp only [Set.preimage_ofPred_eq, hi]

lemma finite_restriction_harris (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law q).real {ω | s ∩ ω ∈ A} * (law q).real {ω | s ∩ ω ∈ B} ≤
      (law q).real {ω | s ∩ ω ∈ A ∩ B} := by
  let := hs.fintype
  simp_rw [real_law_restrict_general _ s hs]
  exact finite_harris _ _ _ (fun _ _ h => hA (Set.image_mono h))
    (fun _ _ h => hB (Set.image_mono h))

lemma HasFiniteOpenWitness.inter {A B : Set (Set E)}
    (hA : HasFiniteOpenWitness A) (hB : HasFiniteOpenWitness B)
    (hAm : IsUpperSet A) (hBm : IsUpperSet B) : HasFiniteOpenWitness (A ∩ B) := by
  rintro ω ⟨hωA, hωB⟩
  obtain ⟨s, hs, hsω, hsA⟩ := hA ω hωA
  obtain ⟨t, ht, htω, htB⟩ := hB ω hωB
  exact ⟨s ∪ t, hs.union ht, Set.union_subset hsω htω,
    hAm Set.subset_union_left hsA, hBm Set.subset_union_right htB⟩

lemma tendsto_real_finiteWitness_general (q : E → unitInterval) (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law q).real {ω | K n ∩ ω ∈ A})
      atTop (𝓝 ((law q).real A)) := by
  have h := tendsto_measure_iUnion_atTop (μ := law q)
    (finiteWitness_exhaustion_mono A hmono K)
  rw [finiteWitness_exhaustion A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

theorem harris_finiteWitness [Countable E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : HasFiniteOpenWitness A) (hwB : HasFiniteOpenWitness B) :
    (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  exact le_of_tendsto_of_tendsto
    ((tendsto_real_finiteWitness_general q A hA hwA K).mul
      (tendsto_real_finiteWitness_general q B hB hwB K))
    (tendsto_real_finiteWitness_general q (A ∩ B) (hA.inter hB)
      (hwA.inter hwB hA hB) K)
    (Eventually.of_forall fun n => finite_restriction_harris q (K n) (K.finite n) A B hA hB)

end CriticalPercolation.BernoulliProduct
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_MoveExit
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

namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}

lemma bounded_first_crossing (f : V → ℝ) (D T : ℝ) (hD : 0≤D)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y|≤D)
    {a b : V} (w : H.Walk a b) (ha : f a<T) (hb : T≤f b) :
    ∃ x, ∃ p : H.Walk a x, p.support⊆w.support ∧
      (∀ v∈p.support, f v≤T+D) ∧ T≤f x := by
  induction w with
  | nil => exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T≤f c
    · refine ⟨c,hac.toWalk,?_,?_,hc⟩
      · intro v hv
        simp only [SimpleGraph.Adj.support_toWalk,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl
        · exact (_root_.SimpleGraph.Walk.cons hac w).start_mem_support
        · exact List.mem_cons_of_mem a w.start_mem_support
      · intro v hv
        simp only [SimpleGraph.Adj.support_toWalk,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl
        · linarith
        · have hh := (abs_le.mp (hf hac)).1
          linarith
    · obtain ⟨x,p,hp,hpb,hpx⟩ := ih (lt_of_not_ge hc) hb
      refine ⟨x,_root_.SimpleGraph.Walk.cons hac p,?_,?_,hpx⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hv|hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · exact List.mem_cons.mpr (Or.inr (hp hv))
      · intro v hv
        rcases List.mem_cons.mp hv with hv|hv
        · rw [hv]
          linarith
        · exact hpb v hv

end SimpleGraph.Walk
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterTail
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

lemma measurableSet_clusterTail [Countable E] (o : V) (n : ℕ) :
    MeasurableSet (G.clusterTail o n) :=
  BernoulliProduct.measurableSet_finiteWitness _ (G.clusterTail_isUpperSet o n)
    (G.clusterTail_hasFiniteOpenWitness o n)

lemma clusterTail_antitone (o : V) : Antitone (G.clusterTail o) := by
  rintro m n h ω ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω, h.trans hn⟩

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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripCompactness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma seedDomainTail_measurable [Countable V] [Countable E] (A S : Set V) (n : ℕ) :
    MeasurableSet (G.seedDomainTail A S n) := by
  have hm : Measurable (fun ω : Set E => ω∩G.inducedEdges S) :=
    (BernoulliProduct.measurable_inter_block _).mono (BernoulliProduct.blockSigma_le _) le_rfl
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (G.measurableSet_clusterTail a n).preimage hm

lemma seedDomainTail_antitone (A S : Set V) : Antitone (G.seedDomainTail A S) := by
  intro n m hnm ω hω
  obtain ⟨a,ha,ht⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨a,ha,G.clusterTail_antitone a hnm ht⟩

lemma seedDomainInfinite_eq_iInter (A S : Set V) (hA : A.Finite) :
    G.seedDomainInfinite A S=⋂ n, G.seedDomainTail A S n := by
  ext ω
  constructor
  · rintro ⟨a,ha,hi⟩
    exact Set.mem_iInter.mpr fun n => Set.mem_iUnion₂.mpr
      ⟨a,ha,G.infiniteEvent_subset_clusterTail a n hi⟩
  · intro hω
    by_contra hn
    have hf : ∀ a∈A, (G.cluster (ω∩G.inducedEdges S) a).Finite := by
      intro a ha
      by_contra hi
      exact hn ⟨a,ha,hi⟩
    let K := ⋃ a∈A, G.cluster (ω∩G.inducedEdges S) a
    have hK : K.Finite := hA.biUnion hf
    obtain ⟨a,ha,L,hL,hLa,hLn⟩ := Set.mem_iUnion₂.mp
      (Set.mem_iInter.mp hω (K.ncard+1))
    have hs : L⊆K := fun x hx => Set.mem_iUnion₂.mpr ⟨a,ha,hLa hx⟩
    have hc := Set.ncard_le_ncard hs hK
    omega

lemma seedDomainInfinite_probability [Countable V] [Countable E]
    (μ : Measure (Set E)) [IsFiniteMeasure μ] (A S : Set V) (hA : A.Finite)
    (r : ℝ) (h : ∀ n, r≤μ.real (G.seedDomainTail A S n)) :
    r≤μ.real (G.seedDomainInfinite A S) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (G.seedDomainTail_measurable A S n).nullMeasurableSet)
    (G.seedDomainTail_antitone A S) ⟨0,measure_ne_top _ _⟩
  rw [←G.seedDomainInfinite_eq_iInter A S hA] at ht
  exact ge_of_tendsto ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht)
    (Filter.Eventually.of_forall h)

lemma RayPrefix.reachable {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n)
    (i : Fin (n+1)) : (G.openGraph ω).Reachable a (p.vertex i) := by
  suffices hh : ∀ k, ∀ hk : k<n+1, (G.openGraph ω).Reachable a (p.vertex ⟨k,hk⟩) from
    hh i.val i.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    have he : (⟨0,hk⟩ : Fin (n+1))=0 := by ext; simp
    rw [he,p.start]
  | succ k ih =>
    intro hk
    exact (ih (by omega)).trans (p.adjacent ⟨k,by omega⟩).reachable

lemma RayPrefix.clusterTail {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n) :
    ω∈G.clusterTail a (n+1) := by
  refine ⟨Set.range p.vertex,Set.finite_range _,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact p.reachable G i
  · rw [Set.ncard_range_of_injective p.injective,Nat.card_fin]

lemma exit_gives_prefix (A S K : Set V) (n : ℕ)
    (hK : ∀ a∈A, G.vertexBall a n⊆K) {ω : Set E}
    (hω : ω∈G.restrictedSeed A (S\K) (G.inducedEdges S)) :
    ∃ a∈A, ∃ p : G.RayPrefix ω a n, ∀ i, p.vertex i∈S∩K := by
  obtain ⟨a,ha,b,⟨w⟩,hb⟩ := Set.mem_iUnion₂.mp hω
  let p := w.toPath
  let q := p.val.mapLe (G.openGraph_mono Set.inter_subset_left)
  have hlen : n<q.length := by
    by_contra hn
    have h := G.openWalk_getVert_ball q q.length le_rfl
    rw [SimpleGraph.Walk.getVert_length] at h
    exact hb.2 (hK a ha (G.vertexBall_mono a (by omega) h))
  let r : G.RayPrefix ω a n := {
    vertex := fun i => q.getVert i.val
    start := q.getVert_zero
    adjacent := fun i => q.adj_getVert_succ (by omega)
    injective := by
      intro i j hij
      apply Fin.ext
      have hpath : q.IsPath := p.property.mapLe _
      exact hpath.getVert_injOn (by change i.val≤q.length; omega)
        (by change j.val≤q.length; omega) hij
    ball := fun i => G.openWalk_getVert_ball q i.val (by omega) }
  refine ⟨a,ha,r,?_⟩
  intro i
  refine ⟨?_,hK a ha (G.vertexBall_mono a (by omega) (r.ball i))⟩
  have hs := G.walk_induced_support p.val hb.1 (p.val.getVert i.val)
    (p.val.getVert_mem_support i.val)
  simpa only [r,q,SimpleGraph.Walk.mapLe,SimpleGraph.Walk.getVert_map,SimpleGraph.Hom.ofLE_apply] using hs

theorem local_domain_exit_compactness [Countable V] [Countable E]
    (hl : G.LocallyFinite) (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (A S : Set V) (hA : A.Finite) (Sj Tj : ℕ → Set V) (r : ℝ)
    (hlocal : ∀ K : Set V, K.Finite → ∀ᶠ j in atTop, Sj j∩K⊆S)
    (hescape : ∀ K : Set V, K.Finite → ∀ᶠ j in atTop, Disjoint (Tj j) K)
    (hprob : ∀ j, r≤μ.real (G.restrictedSeed A (Sj j∩Tj j) (G.inducedEdges (Sj j)))) :
    r≤μ.real (G.seedDomainInfinite A S) := by
  apply G.seedDomainInfinite_probability μ A S hA r
  intro n
  let K := ⋃ a∈A, G.vertexBall a n
  have hK : K.Finite := hA.biUnion (fun a _ => G.vertexBall_finite hl a n)
  obtain ⟨j,hj,hj'⟩ := ((hlocal K hK).and (hescape K hK)).exists
  apply (hprob j).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have hout : ω∈G.restrictedSeed A (Sj j\K) (G.inducedEdges (Sj j)) := by
    obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hω
    exact Set.mem_iUnion₂.mpr ⟨a,ha,b,hr,hb.1,fun hk => Set.disjoint_left.mp hj' hb.2 hk⟩
  obtain ⟨a,ha,p,hp⟩ := G.exit_gives_prefix A (Sj j) K n
    (fun a ha x hx => Set.mem_iUnion₂.mpr ⟨a,ha,hx⟩) hout
  have ht := (G.prefix_inside_domain p S (fun i => hj (hp i))).clusterTail G
  exact Set.mem_iUnion₂.mpr ⟨a,ha,G.clusterTail_antitone a (Nat.le_succ n) ht⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_MovingStrips
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

theorem uniform_long_strip_exits [Countable V] [Countable E]
    (hl : G.LocallyFinite) (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (u v : V → ℝ) (A : Set V) (hA : A.Finite) (W r : ℝ)
    (hW : 0<W) (hr : 0 < r)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 →
      μ (G.stripPercolates (normalCoordinate u v a b) (2*W))=0) :
    ∃ N : ℕ, ∀ L : ℝ, (N : ℝ)≤L → ∀ a b : ℝ, a^2+b^2=1 →
      μ.real (G.longStripExit u v A W L a b) < r := by
  by_contra hn
  push Not at hn
  choose L hL a b hab hprob using hn
  have hseq : ∀ n, (a n,b n)∈Set.Icc ((-1 : ℝ),(-1 : ℝ)) (1,1) := by
    intro n
    have h := unit_pair_bounds (hab n)
    exact ⟨⟨h.1,h.2.2.1⟩,h.2.1,h.2.2.2⟩
  obtain ⟨c,_hc,φ,hφ,hc⟩ := isCompact_Icc.tendsto_subseq hseq
  have ha : Tendsto (fun n => a (φ n)) atTop (𝓝 c.1) := (continuous_fst.tendsto c).comp hc
  have hb : Tendsto (fun n => b (φ n)) atTop (𝓝 c.2) := (continuous_snd.tendsto c).comp hc
  have hunit : c.1^2+c.2^2=1 := by
    apply tendsto_nhds_unique ((ha.pow 2).add (hb.pow 2))
    simpa only [hab] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hpar : ∀ x, Tendsto (fun n => parallelCoordinate u v (a (φ n)) (b (φ n)) x)
      atTop (𝓝 (parallelCoordinate u v c.1 c.2 x)) := fun x =>
    (ha.mul_const (u x)).add (hb.mul_const (v x))
  have hnorm : ∀ x, Tendsto (fun n => normalCoordinate u v (a (φ n)) (b (φ n)) x)
      atTop (𝓝 (normalCoordinate u v c.1 c.2 x)) := fun x =>
    (hb.neg.mul_const (u x)).add (ha.mul_const (v x))
  have hLtop : Tendsto (fun n => L (φ n)) atTop atTop :=
    tendsto_atTop_mono (fun n => hL (φ n))
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  let Sj := fun n => {x | |normalCoordinate u v (a (φ n)) (b (φ n)) x|≤W}
  let Tj := fun n => {x | L (φ n)≤|parallelCoordinate u v (a (φ n)) (b (φ n)) x|}
  let S := {x | |normalCoordinate u v c.1 c.2 x|≤2*W}
  have hlocal : ∀ K : Set V, K.Finite → ∀ᶠ n in atTop, Sj n∩K⊆S := by
    intro K hK
    have he : ∀ᶠ n in atTop, ∀ x∈K,
        |normalCoordinate u v (a (φ n)) (b (φ n)) x|≤W → x∈S := by
      apply hK.eventually_all.mpr
      intro x _hx
      by_cases hx : x∈S
      · exact Eventually.of_forall (fun _ _ => hx)
      · have hh : W < |normalCoordinate u v c.1 c.2 x| := by
          change ¬|normalCoordinate u v c.1 c.2 x|≤2*W at hx
          linarith
        filter_upwards [(hnorm x).abs.eventually (lt_mem_nhds hh)] with n hn
        exact fun hnx => False.elim (not_lt_of_ge hnx hn)
    exact he.mono fun n hn x hx => hn x hx.2 hx.1
  have hescape : ∀ K : Set V, K.Finite → ∀ᶠ n in atTop, Disjoint (Tj n) K := by
    intro K hK
    have he : ∀ᶠ n in atTop, ∀ x∈K,
        |parallelCoordinate u v (a (φ n)) (b (φ n)) x|<L (φ n) := by
      apply hK.eventually_all.mpr
      intro x _hx
      let M := |parallelCoordinate u v c.1 c.2 x|+1
      have hm : |parallelCoordinate u v c.1 c.2 x|<M := by dsimp [M]; linarith
      filter_upwards [(hpar x).abs.eventually (gt_mem_nhds hm),
        (tendsto_atTop.mp hLtop M)] with n hn hn'
      exact hn.trans_le hn'
    exact he.mono fun n hn => Set.disjoint_left.mpr (fun x hx hk =>
      not_lt_of_ge hx (hn x hk))
  have hmass := G.local_domain_exit_compactness hl μ A S hA Sj Tj r hlocal hescape
    (fun n => hprob (φ n))
  have hf : μ (G.seedDomainInfinite A S)=0 := measure_mono_null
    (fun ω hω => by obtain ⟨x,_hx,hx⟩ := hω; exact ⟨x,hx⟩) (hnull c.1 c.2 hunit)
  rw [measureReal_def,hf,ENNReal.toReal_zero] at hmass
  exact not_le_of_gt hr hmass

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_CoordinateRotation
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseExit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

namespace CriticalPercolation.EuclideanEllipse

lemma finite_circle_cover (zeta : ℝ) (hzeta : 0<zeta) :
    ∃ S : Finset Circle, ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta := by
  obtain ⟨S,_hS,hSf,hcover⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circle)).finite_cover_balls hzeta
  refine ⟨hSf.toFinset,?_⟩
  intro c
  obtain ⟨d,hd,hcd⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ c))
  change dist (c : ℂ) (d : ℂ)<zeta at hcd
  exact ⟨d,hSf.mem_toFinset.mpr hd,by simpa only [dist_eq_norm] using hcd⟩

lemma exists_radial_circle (z : ℂ) (hz : z≠0) :
    ∃ c : Circle, z=‖z‖•(c : ℂ) := by
  let c : Circle := ⟨‖z‖⁻¹•z,by
    apply mem_sphere_zero_iff_norm.mpr
    exact norm_smul_inv_norm (𝕜 := ℝ) hz⟩
  refine ⟨c,?_⟩
  change z=‖z‖•(‖z‖⁻¹•z)
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]

lemma annulus_covered (S : Finset Circle) (zeta : ℝ)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (z : ℂ) (hlo : 1≤‖z‖) (hhi : ‖z‖≤1+zeta) :
    ∃ d∈S, ‖z-(d : ℂ)‖≤2*zeta := by
  have hz : z≠0 := by intro h; subst z; norm_num at hlo
  obtain ⟨c,hc⟩ := exists_radial_circle z hz
  obtain ⟨d,hd,hcd⟩ := hcover c
  have he : z-(c : ℂ)=(‖z‖-1)•(c : ℂ) := by rw [sub_smul,one_smul,←hc]
  have hdiff : ‖z-(c : ℂ)‖=‖z‖-1 := by
    rw [he,norm_smul,Real.norm_eq_abs,Circle.norm_coe,mul_one,abs_of_nonneg (by linarith)]
  refine ⟨d,hd,?_⟩
  have htri : ‖z-(d : ℂ)‖≤‖z-(c : ℂ)‖+‖(c : ℂ)-(d : ℂ)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (z-(c : ℂ)) ((c : ℂ)-(d : ℂ))
  linarith

end CriticalPercolation.EuclideanEllipse
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma ellipseExit_iff (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) (ω : Set E) :
    ω∈G.ellipseExit Psi A zeta c ↔ ∃ a∈A, ∃ x, ∃ w : (G.openGraph ω).Walk a x,
      (∀ v∈w.support, ‖Psi v‖≤1+zeta) ∧ ‖Psi x-(c : ℂ)‖≤2*zeta := by
  constructor
  · intro h
    obtain ⟨a,ha,x,⟨w⟩,hx⟩ := Set.mem_iUnion₂.mp h
    refine ⟨a,ha,x,w.mapLe (G.openGraph_mono Set.inter_subset_left),?_,hx.1⟩
    intro v hv
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact G.walk_induced_support w hx.2 v hv
  · rintro ⟨a,ha,x,w,hw,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,x,G.walk_reachable_induced _ ω w hw,hx,hw x w.end_mem_support⟩

lemma ellipseExit_upper (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) :
    IsUpperSet (G.ellipseExit Psi A zeta c) := G.restrictedSeed_upper _ _ _
lemma ellipseExit_finiteWitness (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) :
    BernoulliProduct.HasFiniteOpenWitness (G.ellipseExit Psi A zeta c) := G.restrictedSeed_finiteWitness _ _ _

lemma full_infinite_cluster_exit (Psi : V → ℂ) (ω : Set E) (a : V)
    (hi : (G.cluster ω a).Infinite)
    (hbound : (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) a).Finite) :
    ∃ b∈G.cluster ω a, 1<‖Psi b‖ := by
  by_contra hn
  push Not at hn
  apply hi
  apply hbound.subset
  rintro b ⟨w⟩
  apply G.walk_reachable_induced _ ω w
  intro x hx
  exact hn x (w.takeUntil x hx).reachable

theorem infinite_cluster_ellipseExit (Psi : V → ℂ) (A : Set V) (zeta D : ℝ)
    (hD : 0≤D) (hDz : D≤zeta)
    (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D)
    (hseed : ∀ a∈A, ‖Psi a‖<1) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    {ω : Set E} (hi : ∃ a∈A, (G.cluster ω a).Infinite)
    (hbound : ∀ a∈A, (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) a).Finite) :
    ω∈⋃ c∈S, G.ellipseExit Psi A zeta c := by
  obtain ⟨a,ha,hi⟩ := hi
  obtain ⟨b,⟨w⟩,hb⟩ := G.full_infinite_cluster_exit Psi ω a hi (hbound a ha)
  have hstep : ∀ ⦃x y⦄, (G.openGraph ω).Adj x y → |‖Psi x‖-‖Psi y‖|≤D := by
    intro x y hxy
    exact (abs_norm_sub_norm_le _ _).trans (hPsi (G.openGraph_mono (Set.subset_univ _) hxy))
  obtain ⟨x,p,_hp,hpb,hpx⟩ := _root_.OAI.SimpleGraph.Walk.bounded_first_crossing (fun x => ‖Psi x‖) D 1 hD hstep w (hseed a ha) hb.le
  obtain ⟨c,hc,hcx⟩ := EuclideanEllipse.annulus_covered S zeta hcover (Psi x) hpx (by linarith [hpb x p.end_mem_support])
  apply Set.mem_iUnion₂.mpr
  refine ⟨c,hc,(G.ellipseExit_iff Psi A zeta c ω).mpr ⟨a,ha,x,p,?_,hcx⟩⟩
  intro v hv
  linarith [hpb v hv]

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DiskWinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.DiskWinding

lemma increment_add_of_short {a b c : Real.Angle}
    (hab : |increment a b|<Real.pi/4) (hbc : |increment b c|<Real.pi/4)
    (hac : |increment a c|<Real.pi/4) :
    increment a b+increment b c=increment a c := by
  let z := increment a b+increment b c-increment a c
  have hco : (z : Real.Angle)=0 := by
    simp only [z,increment,Real.Angle.coe_sub,Real.Angle.coe_add,Real.Angle.coe_toReal]
    abel
  have hbounded : -Real.pi<z ∧ z≤Real.pi := by
    obtain ⟨habl,habu⟩ := abs_lt.mp hab
    obtain ⟨hbcl,hbcu⟩ := abs_lt.mp hbc
    obtain ⟨hacl,hacu⟩ := abs_lt.mp hac
    dsimp [z]
    constructor <;> linarith [Real.pi_pos]
  have hz := Real.Angle.toReal_coe_eq_self_iff.mpr hbounded
  rw [hco,Real.Angle.toReal_zero] at hz
  dsimp [z] at hz
  linarith

lemma sum_successive_sub (f : ℕ → ℝ) (K : ℕ) :
    ∑ k∈Finset.range K, (f (k+1)-f k)=f K-f 0 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; ring

lemma cell_balance {a b c d : Real.Angle}
    (hab : |increment a b|<Real.pi/4) (hbc : |increment b c|<Real.pi/4)
    (hac : |increment a c|<Real.pi/4) (had : |increment a d|<Real.pi/4)
    (hdc : |increment d c|<Real.pi/4) :
    increment a b+increment b c=increment a d+increment d c :=
  (increment_add_of_short hab hbc hac).trans (increment_add_of_short had hdc hac).symm

theorem boundary_sum_zero (F : ℕ → ℕ → Real.Angle) (N K : ℕ)
    (hcenter : ∀ k≤K, F 0 k=F 0 0)
    (hseam : ∀ i≤N, F i K=F i 0)
    (hhoriz : ∀ i≤N, ∀ k<K, |increment (F i k) (F i (k+1))|<Real.pi/4)
    (hvert : ∀ i<N, ∀ k≤K, |increment (F i k) (F (i+1) k)|<Real.pi/4)
    (hdiag : ∀ i<N, ∀ k<K, |increment (F i k) (F (i+1) (k+1))|<Real.pi/4) :
    ∑ k∈Finset.range K, increment (F N k) (F N (k+1))=0 := by
  have step : ∀ i<N,
      (∑ k∈Finset.range K, increment (F (i+1) k) (F (i+1) (k+1)))=
      ∑ k∈Finset.range K, increment (F i k) (F i (k+1)) := by
    intro i hi
    let v : ℕ → ℝ := fun k => increment (F i k) (F (i+1) k)
    have hver : ∑ k∈Finset.range K, (v (k+1)-v k)=0 := by
      rw [sum_successive_sub]
      dsimp [v]
      rw [hseam i (by omega),hseam (i+1) (by omega),sub_self]
    have heach : ∀ k∈Finset.range K,
        increment (F (i+1) k) (F (i+1) (k+1))=
        increment (F i k) (F i (k+1))+(v (k+1)-v k) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h := cell_balance (hhoriz i (by omega) k hk')
        (hvert i hi (k+1) (by omega)) (hdiag i hi k hk')
        (hvert i hi k (by omega)) (hhoriz (i+1) (by omega) k hk')
      dsimp [v]
      linarith
    rw [Finset.sum_congr rfl heach,Finset.sum_add_distrib,hver,add_zero]
  have all : ∀ i≤N, ∑ k∈Finset.range K, increment (F i k) (F i (k+1))=0 := by
    intro i
    induction i with
    | zero =>
      intro _
      apply Finset.sum_eq_zero
      intro k hk
      rw [hcenter k (by have := Finset.mem_range.mp hk; omega),
        hcenter (k+1) (by have := Finset.mem_range.mp hk; omega)]
      simp [increment]
    | succ i ih =>
      intro hi
      rw [step i (by omega),ih (by omega)]
  exact all N le_rfl

lemma boundary_sum_lift (F : ℕ → Real.Angle) (b : ℕ → ℝ) (K : ℕ)
    (hlift : ∀ k≤K, F k=(b k : Real.Angle))
    (hstep : ∀ k<K, |b (k+1)-b k|<Real.pi) :
    ∑ k∈Finset.range K, increment (F k) (F (k+1))=b K-b 0 := by
  rw [←sum_successive_sub b K]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [increment,hlift k (by omega),hlift (k+1) (by omega),←Real.Angle.coe_sub]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨(abs_lt.mp (hstep k hk')).1,
    (abs_lt.mp (hstep k hk')).2.le⟩

theorem exists_large_edge (F : ℕ → ℕ → Real.Angle) (N K : ℕ) (b : ℕ → ℝ)
    (hcenter : ∀ k≤K, F 0 k=F 0 0)
    (hseam : ∀ i≤N, F i K=F i 0)
    (hlift : ∀ k≤K, F N k=(b k : Real.Angle))
    (hstep : ∀ k<K, |b (k+1)-b k|<Real.pi)
    (hturn : b K-b 0=2*Real.pi) :
    (∃ i≤N, ∃ k<K, Real.pi/4≤|increment (F i k) (F i (k+1))|) ∨
    (∃ i<N, ∃ k≤K, Real.pi/4≤|increment (F i k) (F (i+1) k)|) ∨
    (∃ i<N, ∃ k<K, Real.pi/4≤|increment (F i k) (F (i+1) (k+1))|) := by
  by_contra hn
  push Not at hn
  have hz := boundary_sum_zero F N K hcenter hseam hn.1 hn.2.1 hn.2.2
  have ht := boundary_sum_lift (F N) b K hlift hstep
  rw [hz,hturn] at ht
  linarith [Real.pi_pos]

lemma boundary_mesh_lifts (φ e : ℕ → ℝ) (K : ℕ)
    (hmesh : ∀ k<K, |φ (k+1)-φ k|<Real.pi/32)
    (herr : ∀ k≤K, |e k|<Real.pi/8) :
    ∀ k<K, |(2*φ (k+1)+Real.pi+e (k+1))-(2*φ k+Real.pi+e k)|<Real.pi := by
  intro k hk
  obtain ⟨hma,hmb⟩ := abs_lt.mp (hmesh k hk)
  obtain ⟨hea,heb⟩ := abs_lt.mp (herr k (by omega))
  obtain ⟨hfa,hfb⟩ := abs_lt.mp (herr (k+1) (by omega))
  apply abs_lt.mpr
  constructor <;> linarith [Real.pi_pos]

end CriticalPercolation.DiskWinding
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open LinearMap

namespace CriticalPercolation.EllipseLinear

lemma center_left (a b c d : ℝ) (h : det a b c d≠0) :
    time a b c d a b=1 ∧ height a b c d a b=1 := by
  constructor <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring

lemma center_right (a b c d : ℝ) (h : det a b c d≠0) :
    time a b c d c d=1 ∧ height a b c d c d= -1 := by
  constructor <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring

lemma det_lower_of_separation (θ ψ : ℝ)
    (hsep : Real.pi/4≤|DiskWinding.increment ((2*θ : ℝ) : Real.Angle)
      ((2*ψ : ℝ) : Real.Angle)|) :
    (1 : ℝ)/4≤|det (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)| := by
  let t : Real.Angle := ((2*ψ : ℝ) : Real.Angle)-((2*θ : ℝ) : Real.Angle)
  have ht : t=((2*(ψ-θ) : ℝ) : Real.Angle) := by
    dsimp [t]
    rw [←Real.Angle.coe_sub]
    congr 1
    ring
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0≤Real.pi/4) (Real.Angle.abs_toReal_le_pi t) hsep
  rw [Real.cos_abs,Real.Angle.cos_toReal,ht,Real.Angle.cos_coe,
    Real.cos_two_mul,Real.cos_pi_div_four] at hcos
  have hsqrt : Real.sqrt 2≤(7 : ℝ)/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg 2]
  have hsq := Real.sin_sq_add_cos_sq (ψ-θ)
  have hsin : (1 : ℝ)/4≤|Real.sin (ψ-θ)| := by
    nlinarith [sq_abs (Real.sin (ψ-θ)),abs_nonneg (Real.sin (ψ-θ))]
  have heq : det (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)=
      Real.sin (ψ-θ) := by rw [Real.sin_sub]; unfold det; ring
  rwa [heq]

lemma row_bound {a b c d : ℝ} (ha : |a|≤1) (hb : |b|≤1)
    (hc : |c|≤1) (hd : |d|≤1) (hdet : (1 : ℝ)/4≤|det a b c d|)
    (x y q : ℝ) (hq : 0≤q) (hx : |x|≤q) (hy : |y|≤q) :
    |time a b c d x y|≤16*q ∧ |height a b c d x y|≤16*q := by
  have hpos : 0 < |det a b c d| := by linarith
  have hdb : |d-b|≤2 := (abs_sub d b).trans (by linarith)
  have hac : |a-c|≤2 := (abs_sub a c).trans (by linarith)
  have hdb' : |d+b|≤2 := (abs_add_le d b).trans (by linarith)
  have hca : |c+a|≤2 := (abs_add_le c a).trans (by linarith)
  have hprod : ∀ z w : ℝ, |z|≤2 → |w|≤q → |z*w|≤2*q := by
    intro z w hz hw
    rw [abs_mul]
    exact mul_le_mul hz hw (abs_nonneg _) (by norm_num)
  constructor
  · unfold time
    rw [abs_div]
    apply (div_le_iff₀ hpos).mpr
    calc
      |(d-b)*x+(a-c)*y|≤|(d-b)*x|+|(a-c)*y| := abs_add_le _ _
      _ ≤4*q := by linarith [hprod (d-b) x hdb hx,hprod (a-c) y hac hy]
      _ ≤16*q*|det a b c d| := by nlinarith
  · unfold height
    rw [abs_div]
    apply (div_le_iff₀ hpos).mpr
    calc
      |(d+b)*x-(c+a)*y|≤|(d+b)*x|+|(c+a)*y| := abs_sub _ _
      _ ≤4*q := by linarith [hprod (d+b) x hdb' hx,hprod (c+a) y hca hy]
      _ ≤16*q*|det a b c d| := by nlinarith

lemma time_sub (a b c d x y x' y' : ℝ) :
    time a b c d x y-time a b c d x' y'=time a b c d (x-x') (y-y') := by
  unfold time; ring
lemma height_sub (a b c d x y x' y' : ℝ) :
    height a b c d x y-height a b c d x' y'=height a b c d (x-x') (y-y') := by
  unfold height; ring

lemma source_budgets {eps : ℝ} (heps : 0<eps) (heps' : eps<1/10) :
    16*(4*(eps/1000))<eps/8 ∧
    16*((1+eps/1000)^2)<30 := by constructor <;> nlinarith

end CriticalPercolation.EllipseLinear
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_EllipseMoves
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma circle_component_bounds (c : Circle) : |(c : ℂ).re|≤1 ∧ |(c : ℂ).im|≤1 := by
  constructor
  · exact (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe c)
  · exact (Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe c)

lemma ellipse_coordinates_norm_bound (Psi : V → ℂ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (x : V) : |ellipseTime Psi c d x|≤16*‖Psi x‖ ∧ |ellipseHeight Psi c d x|≤16*‖Psi x‖ := by
  exact EllipseLinear.row_bound (circle_component_bounds c).1 (circle_component_bounds c).2
    (circle_component_bounds d).1 (circle_component_bounds d).2 hdet (Psi x).re (Psi x).im
    ‖Psi x‖ (norm_nonneg _) (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

lemma ellipse_coordinates_sub (Psi : V → ℂ) (c d : Circle) (x y : V) :
    ellipseTime Psi c d x-ellipseTime Psi c d y=
      ellipseTime (fun v => Psi v-Psi y) c d x ∧
    ellipseHeight Psi c d x-ellipseHeight Psi c d y=
      ellipseHeight (fun v => Psi v-Psi y) c d x := by
  constructor
  · exact EllipseLinear.time_sub _ _ _ _ _ _ _ _
  · exact EllipseLinear.height_sub _ _ _ _ _ _ _ _

lemma ellipse_coordinates_step (Psi : V → ℂ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (D : ℝ) (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D) :
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |ellipseTime Psi c d x-ellipseTime Psi c d y|≤16*D) ∧
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |ellipseHeight Psi c d x-ellipseHeight Psi c d y|≤16*D) := by
  constructor
  · intro x y hxy
    rw [(ellipse_coordinates_sub Psi c d x y).1]
    exact (ellipse_coordinates_norm_bound (fun v => Psi v-Psi y) c d hdet x).1.trans (by nlinarith [hPsi hxy])
  · intro x y hxy
    rw [(ellipse_coordinates_sub Psi c d x y).2]
    exact (ellipse_coordinates_norm_bound (fun v => Psi v-Psi y) c d hdet x).2.trans (by nlinarith [hPsi hxy])

theorem ellipseExit_boxMove (Psi Psi' : V → ℂ) (o : V) (m : ℕ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (eps : ℝ) (heps : 0<eps) (heps' : eps<1/10) (ho : Psi o=0)
    (hpert : ∀ x, ‖Psi x-Psi' x‖≤(eps/1000)*‖Psi' x‖) (b : Bool) :
    G.ellipseExit Psi' (G.vertexBall o m) (eps/1000) (if b then c else d) ⊆
      G.boxMove (ellipseTime Psi c d) (ellipseHeight Psi c d) m (eps/8) 30 o (Corridor.sign b) := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.ellipseExit_iff _ _ _ _ ω).mp hω
  have hzeta : 0<eps/1000 := by positivity
  have hzeta' : eps/1000<1/10000 := by linarith
  have hdet' : EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im≠0 := by
    intro he
    rw [he,abs_zero] at hdet
    norm_num at hdet
  have hto : ellipseTime Psi c d o=0 := by simp [ellipseTime,ho,EllipseLinear.time]
  have hzo : ellipseHeight Psi c d o=0 := by simp [ellipseHeight,ho,EllipseLinear.height]
  have hpath : ∀ y∈w.support, ‖Psi y‖≤(1+eps/1000)^2 := by
    intro y hy
    have htri : ‖Psi y‖≤‖Psi y-Psi' y‖+‖Psi' y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Psi y-Psi' y) (Psi' y)
    nlinarith [hpert y,hw y hy]
  have hterminal : ‖Psi x-((if b then c else d) : Circle)‖≤4*(eps/1000) := by
    have htri : ‖Psi x-((if b then c else d) : Circle)‖≤
        ‖Psi x-Psi' x‖+‖Psi' x-((if b then c else d) : Circle)‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (Psi x-Psi' x)
        (Psi' x-((if b then c else d) : Circle))
    nlinarith [hpert x,hw x w.end_mem_support,mul_pos hzeta (by linarith : 0<1-eps/1000)]
  have hcenter : EllipseLinear.time (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im
      (((if b then c else d) : Circle) : ℂ).re (((if b then c else d) : Circle) : ℂ).im=1 ∧
      EllipseLinear.height (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im
      (((if b then c else d) : Circle) : ℂ).re (((if b then c else d) : Circle) : ℂ).im=Corridor.sign b := by
    cases b
    · exact EllipseLinear.center_right _ _ _ _ hdet'
    · exact EllipseLinear.center_left _ _ _ _ hdet'
  have hend := ellipse_coordinates_norm_bound (fun v => Psi v-((if b then c else d) : Circle)) c d hdet x
  have htend : |ellipseTime Psi c d x-1|≤eps/8 := by
    rw [←hcenter.1,ellipseTime,EllipseLinear.time_sub]
    exact hend.1.trans ((mul_le_mul_of_nonneg_left hterminal (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').1.le)
  have hzend : |ellipseHeight Psi c d x-Corridor.sign b|≤eps/8 := by
    rw [←hcenter.2,ellipseHeight,EllipseLinear.height_sub]
    exact hend.2.trans ((mul_le_mul_of_nonneg_left hterminal (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').1.le)
  refine ⟨a,ha,x,w,?_,?_,?_⟩
  · intro y hy
    rw [hto,hzo,sub_zero,sub_zero]
    have hnorm := ellipse_coordinates_norm_bound Psi c d hdet y
    have hbudget : 16*‖Psi y‖≤30 := (mul_le_mul_of_nonneg_left (hpath y hy) (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').2.le
    exact ⟨hnorm.1.trans hbudget,hnorm.2.trans hbudget⟩
  · simpa only [hto,zero_add] using htend
  · simpa only [hzo,zero_add] using hzend

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FavoredFinite
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma upper_biUnion (A : I → Set (Set E)) (s : Finset I)
    (hA : ∀ i∈s, IsUpperSet (A i)) : IsUpperSet (⋃ i∈s, A i) := by
  intro ω τ h hω
  obtain ⟨i,hi,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨i,hi,hA i hi h hω⟩

lemma finiteWitness_biUnion (A : I → Set (Set E)) (s : Finset I)
    (hA : ∀ i∈s, HasFiniteOpenWitness (A i)) :
    HasFiniteOpenWitness (⋃ i∈s, A i) := by
  intro ω hω
  obtain ⟨i,hi,hω⟩ := Set.mem_iUnion₂.mp hω
  obtain ⟨K,hK,hKs,hKA⟩ := hA i hi ω hω
  exact ⟨K,hK,hKs,Set.mem_iUnion₂.mpr ⟨i,hi,hKA⟩⟩

theorem finite_miss_product [Countable E] (q : E → unitInterval) (A : I → Set (Set E))
    (s : Finset I) (hA : ∀ i∈s, IsUpperSet (A i))
    (hw : ∀ i∈s, HasFiniteOpenWitness (A i)) :
    ∏ i∈s, (1-(law q).real (A i)) ≤ 1-(law q).real (⋃ i∈s, A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hm := hA i (Finset.mem_insert_self i s)
    have hw' := hw i (Finset.mem_insert_self i s)
    have hs : ∀ j∈s, IsUpperSet (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hsw : ∀ j∈s, HasFiniteOpenWitness (A j) := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hind := ih hs hsw
    let B := ⋃ j∈s, A j
    have hBm := upper_biUnion A s hs
    have hBw := finiteWitness_biUnion A s hsw
    have hH := harris_finiteWitness q (A i) B hm hBm hw' hBw
    have hu := measureReal_union_add_inter (s := A i)
      (measurableSet_finiteWitness B hBm hBw) (μ := law q)
      (measure_ne_top _ _) (measure_ne_top _ _)
    have hb : (law q).real (A i)≤1 := measureReal_le_one
    have hp := mul_le_mul_of_nonneg_left hind (by linarith : 0≤1-(law q).real (A i))
    rw [Finset.prod_insert hi]
    rw [Finset.set_biUnion_insert]
    change (1-(law q).real (A i))*(∏ j∈s, (1-(law q).real (A j)))≤
      1-(law q).real (A i∪B)
    change _≤1-(law q).real B at hind
    change _≤(1-(law q).real (A i))*(1-(law q).real B) at hp
    nlinarith

theorem exists_favored_finite [Countable E] (q : E → unitInterval) (A : I → Set (Set E))
    (s : Finset I) (hA : ∀ i∈s, IsUpperSet (A i))
    (hw : ∀ i∈s, HasFiniteOpenWitness (A i)) (a : ℝ) (ha : 0≤a)
    (hu : 1-a^s.card<(law q).real (⋃ i∈s, A i)) :
    ∃ i∈s, 1-a<(law q).real (A i) := by
  by_contra hn
  push Not at hn
  have hp : a^s.card≤∏ i∈s, (1-(law q).real (A i)) := by
    rw [←Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => ha)
    intro i hi
    linarith [hn i hi]
  have hH := finite_miss_product q A s hA hw
  linarith

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseSeed
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma seedInfiniteEvent_mono {A B : Set V} (hAB : A⊆B) :
    G.seedInfiniteEvent A⊆G.seedInfiniteEvent B := by
  rintro ω ⟨a,ha,hi⟩
  exact ⟨a,hAB ha,hi⟩

theorem exists_seed_infinite_probability [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (o : V) (q : E → unitInterval)
    (hone : BernoulliProduct.law q G.percolates=1) (eps : ℝ) (heps : 0<eps) :
    ∃ m : ℕ, 1-eps<(BernoulliProduct.law q).real (G.seedInfiniteEvent (G.vertexBall o m)) := by
  let A : ℕ → Set (Set E) := fun n => G.seedInfiniteEvent (G.vertexBall o n)
  have hmono : Monotone A := fun _ _ h => G.seedInfiniteEvent_mono (G.vertexBall_mono o h)
  have heq : (⋃ n, A n)=G.percolates := by
    ext ω
    constructor
    · intro h
      obtain ⟨n,a,_ha,hi⟩ := Set.mem_iUnion.mp h
      exact ⟨a,hi⟩
    · rintro ⟨a,hi⟩
      obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc o a)
      exact Set.mem_iUnion.mpr ⟨n,a,hn,hi⟩
  have ht := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
  rw [heq,hone] at ht
  have hreal := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞)≠⊤)).comp ht
  have hnear : ∀ᶠ n in atTop, 1-eps<(BernoulliProduct.law q).real (A n) :=
    hreal.eventually (lt_mem_nhds (by simpa using heps : 1-eps<ENNReal.toReal 1))
  exact hnear.exists

theorem exists_favored_ellipse [Countable E]
    (Psi : V → ℂ) (A : Set V) (zeta D : ℝ) (hD : 0≤D) (hDz : D≤zeta)
    (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D)
    (hseed : ∀ a∈A, ‖Psi a‖<1) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (q : E → unitInterval) (a : ℝ) (ha : 0≤a)
    (hi : 1-a^S.card<(BernoulliProduct.law q).real (G.seedInfiniteEvent A))
    (hbound : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x∈A,
      (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) x).Finite) :
    ∃ c∈S, 1-a<(BernoulliProduct.law q).real (G.ellipseExit Psi A zeta c) := by
  have hsub : G.seedInfiniteEvent A ≤ᵐ[BernoulliProduct.law q] ⋃ c∈S, G.ellipseExit Psi A zeta c := by
    filter_upwards [hbound] with ω hω
    exact fun hi => G.infinite_cluster_ellipseExit Psi A zeta D hD hDz hPsi hseed S hcover hi hω
  have hprob := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact BernoulliProduct.exists_favored_finite q (fun c => G.ellipseExit Psi A zeta c) S
    (fun c _ => G.ellipseExit_upper Psi A zeta c) (fun c _ => G.ellipseExit_finiteWitness Psi A zeta c)
    a ha (hi.trans_le hprob)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EuclideanEllipse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

lemma diagonal_add (a b : ℝ) (z w : ℂ) :
    diagonal a b (z+w)=diagonal a b z+diagonal a b w := by
  apply Complex.ext <;> simp [diagonal,mul_add]
lemma diagonal_sub (a b : ℝ) (z w : ℂ) :
    diagonal a b (z-w)=diagonal a b z-diagonal a b w := by
  apply Complex.ext <;> simp [diagonal,mul_sub]
lemma diagonal_comp (a b c d : ℝ) (z : ℂ) :
    diagonal a b (diagonal c d z)=diagonal (a*c) (b*d) z := by
  apply Complex.ext <;> simp [diagonal,mul_assoc]
lemma diagonal_one (z : ℂ) : diagonal 1 1 z=z := by apply Complex.ext <;> simp [diagonal]
lemma diagonal_neg (a b : ℝ) (z : ℂ) : diagonal a b (-z)= -diagonal a b z := by
  apply Complex.ext <;> simp [diagonal]

lemma diagonal_norm_le (a b M : ℝ) (hM : 0≤M) (ha : |a|≤M) (hb : |b|≤M) (z : ℂ) :
    ‖diagonal a b z‖≤M*‖z‖ := by
  have ha2 : a^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr ha
  have hb2 : b^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hb
  have hsq : ‖diagonal a b z‖^2≤(M*‖z‖)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,mul_pow,Complex.sq_norm,Complex.normSq_apply]
    dsimp [diagonal]
    nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg z.re),
      mul_le_mul_of_nonneg_right hb2 (sq_nonneg z.im)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hsq

lemma normalize_sub (R W : ℝ) (c : Circle) (z w : ℂ) :
    normalize R W c (z-w)=normalize R W c z-normalize R W c w := by
  simp only [normalize,mul_sub,diagonal_sub]

lemma expand_normalize (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    expand R W c (normalize R W c z)=z := by
  simp only [normalize,expand,←mul_assoc,inv_mul_cancel₀ c.coe_ne_zero,one_mul,
    diagonal_comp,mul_one_div_cancel hR,mul_one_div_cancel hW,diagonal_one]
  rw [mul_assoc,mul_inv_cancel_left₀ c.coe_ne_zero]

lemma normalize_expand (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    normalize R W c (expand R W c z)=z := by
  simp only [normalize,expand,←mul_assoc,inv_mul_cancel₀ c.coe_ne_zero,one_mul,
    diagonal_comp,one_div_mul_cancel hR,one_div_mul_cancel hW,diagonal_one]
  rw [mul_assoc,mul_inv_cancel_left₀ c.coe_ne_zero]

lemma normalize_norm_le (R W : ℝ) (hW : 0<W) (hWR : W≤R) (c : Circle) (z : ℂ) :
    ‖normalize R W c z‖≤‖z‖/W := by
  have hR : 0<R := hW.trans_le hWR
  have h1 : |1/R|≤1/W := by rw [abs_of_pos (one_div_pos.mpr hR)]; exact one_div_le_one_div_of_le hW hWR
  have h2 : |1/W|≤1/W := (abs_of_pos (one_div_pos.mpr hW)).le
  have h := diagonal_norm_le (1/R) (1/W) (1/W) (by positivity) h1 h2 ((c : ℂ)⁻¹*z)
  simpa [normalize,norm_mul,Circle.norm_coe,div_eq_mul_inv,mul_comm]
    using h

lemma expand_norm_le (R W : ℝ) (hW : 0≤W) (hWR : W≤R) (c : Circle) (z : ℂ) :
    ‖expand R W c z‖≤R*‖z‖ := by
  have hR := hW.trans hWR
  have h := diagonal_norm_le R W R hR (by simp [abs_of_nonneg hR])
    (by simpa [abs_of_nonneg hW] using hWR) ((c : ℂ)⁻¹*z)
  simpa only [expand,norm_mul,Circle.norm_coe,norm_inv,inv_one,one_mul] using h

lemma normalize_center (W : ℝ) (c : Circle) (z : ℂ) :
    normalize W W c z=(1/W : ℝ)•z := by
  have he : ∀ w : ℂ, diagonal (1/W) (1/W) w=(1/W : ℝ)•w := by intro w; apply Complex.ext <;> simp [diagonal]
  rw [normalize,he,mul_smul_comm,←mul_assoc,mul_inv_cancel₀ c.coe_ne_zero,one_mul]

lemma normalize_neg (R W : ℝ) (c : Circle) (z : ℂ) :
    normalize R W (-c) z=normalize R W c z := by
  simp only [normalize,Circle.coe_neg,inv_neg,neg_mul,diagonal_neg,mul_neg,neg_neg]

lemma normalize_components (R W : ℝ) (c : Circle) (z : ℂ) :
    (((c : ℂ)⁻¹*normalize R W c z).re=(1/R)*((c : ℂ)⁻¹*z).re) ∧
    (((c : ℂ)⁻¹*normalize R W c z).im=(1/W)*((c : ℂ)⁻¹*z).im) := by
  simp [normalize,diagonal]

lemma normalize_origin (R W : ℝ) (c : Circle) : normalize R W c 0=0 := by
  simp [normalize,diagonal,Complex.ext_iff]

lemma normalize_real_linear (R W : ℝ) (c : Circle) (z w : ℂ) (a b : ℝ) :
    normalize R W c (a•z+b•w)=a•normalize R W c z+b•normalize R W c w := by
  have hd : ∀ q : ℂ, ∀ t : ℝ, diagonal (1/R) (1/W) (t•q)=t•diagonal (1/R) (1/W) q := by
    intro q t
    apply Complex.ext <;> simp [diagonal,Complex.mul_re,Complex.mul_im] <;> ring
  simp only [normalize,mul_add,mul_smul_comm,diagonal_add,hd]

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

namespace CriticalPercolation.EuclideanEllipse

lemma rotated_re (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).re=(c : ℂ).re*z.re+(c : ℂ).im*z.im := by
  rw [←Circle.coe_inv,Circle.coe_inv_eq_conj]
  simp [Complex.mul_re]
lemma rotated_im (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).im= -(c : ℂ).im*z.re+(c : ℂ).re*z.im := by
  rw [←Circle.coe_inv,Circle.coe_inv_eq_conj]
  simp [Complex.mul_im,add_comm]
lemma norm_rotated (c : Circle) (z : ℂ) : ‖(c : ℂ)⁻¹*z‖=‖z‖ := by
  rw [norm_mul,norm_inv,Circle.norm_coe,inv_one,one_mul]

lemma original_components (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).re=R*((c : ℂ)⁻¹*normalize R W c z).re ∧
    ((c : ℂ)⁻¹*z).im=W*((c : ℂ)⁻¹*normalize R W c z).im := by
  obtain ⟨hre,him⟩ := normalize_components R W c z
  rw [hre,him]
  constructor <;> field_simp

lemma normalize_transverse_le (R W zeta : ℝ) (hR : R≠0) (hW : 0<W)
    (c : Circle) (z : ℂ) (hz : ‖normalize R W c z‖≤1+zeta) :
    |((c : ℂ)⁻¹*z).im|≤W*(1+zeta) := by
  rw [(original_components R W hR hW.ne' c z).2,abs_mul,abs_of_pos hW]
  apply mul_le_mul_of_nonneg_left _ hW.le
  exact ((Complex.abs_im_le_norm _).trans_eq (norm_rotated c _)).trans hz

lemma normalized_far_major (R W zeta : ℝ) (hR : 0<R) (hW : W≠0)
    (hzeta : zeta≤1/10000) (c d : Circle)
    (hd : (1 : ℝ)/8≤|((c : ℂ)⁻¹*(d : ℂ)).re|)
    (z : ℂ) (hz : ‖normalize R W c z-(d : ℂ)‖≤2*zeta) :
    R/10≤|((c : ℂ)⁻¹*z).re| := by
  have hdiff : |((c : ℂ)⁻¹*normalize R W c z).re-((c : ℂ)⁻¹*(d : ℂ)).re|≤2*zeta := by
    calc
      _ = |((c : ℂ)⁻¹*(normalize R W c z-(d : ℂ))).re| := by rw [mul_sub,Complex.sub_re]
      _ ≤ ‖(c : ℂ)⁻¹*(normalize R W c z-(d : ℂ))‖ := Complex.abs_re_le_norm _
      _ = ‖normalize R W c z-(d : ℂ)‖ := norm_rotated c _
      _ ≤ 2*zeta := hz
  have ha := abs_sub_abs_le_abs_sub (((c : ℂ)⁻¹*(d : ℂ)).re)
    (((c : ℂ)⁻¹*normalize R W c z).re)
  rw [abs_sub_comm] at ha
  have hmajor : (1 : ℝ)/10≤|((c : ℂ)⁻¹*normalize R W c z).re| := by linarith
  rw [(original_components R W hR.ne' hW c z).1,abs_mul,abs_of_pos hR]
  nlinarith

lemma doubled_angle_le_sine (theta : ℝ) :
    |((2*theta : ℝ) : Real.Angle).toReal|≤Real.pi*|Real.sin theta| := by
  let t : Real.Angle := ((2*theta : ℝ) : Real.Angle)
  have ht : |t.toReal/2|≤Real.pi/2 := by rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]; exact div_le_div_of_nonneg_right (Real.Angle.abs_toReal_le_pi t) (by norm_num)
  have heq : 2•((t.toReal/2 : ℝ) : Real.Angle)=2•((theta : ℝ) : Real.Angle) := by
    rw [Real.Angle.two_nsmul_coe_div_two,Real.Angle.coe_toReal]
    dsimp [t]
    rw [←Real.Angle.coe_nsmul]
    congr 1
    simp only [two_smul]
    ring
  have hs := Real.Angle.abs_sin_eq_of_two_nsmul_eq heq
  simp only [Real.Angle.sin_coe] at hs
  have hj := Real.mul_abs_le_abs_sin ht
  rw [hs,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hj
  have hp := Real.pi_pos
  have hm := mul_le_mul_of_nonneg_left hj hp.le
  field_simp at hm
  dsimp [t] at hm
  nlinarith

end CriticalPercolation.EuclideanEllipse
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma ellipseExit_subset_longStrip (pi : V → ℂ) (A : Set V) (R W zeta : ℝ)
    (hR : 0<R) (hW : 0<W) (hzeta : zeta≤1/10000) (c d : Circle)
    (hd : (1 : ℝ)/8≤|((c : ℂ)⁻¹*(d : ℂ)).re|) :
    G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d ⊆
      G.longStripExit (fun x => (pi x).re) (fun x => (pi x).im) A
        (W*(1+zeta)) (R/10) (c : ℂ).re (c : ℂ).im := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.ellipseExit_iff _ A zeta d ω).mp hω
  have hpath : ∀ y∈w.support, |normalCoordinate (fun x => (pi x).re)
      (fun x => (pi x).im) (c : ℂ).re (c : ℂ).im y|≤W*(1+zeta) := by
    intro y hy
    change |-(c : ℂ).im*(pi y).re+(c : ℂ).re*(pi y).im|≤_
    rw [←EuclideanEllipse.rotated_im]
    exact EuclideanEllipse.normalize_transverse_le R W zeta hR.ne' hW c (pi y) (hw y hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,G.walk_reachable_induced _ ω w hpath,hpath x w.end_mem_support,?_⟩
  change R/10≤|(c : ℂ).re*(pi x).re+(c : ℂ).im*(pi x).im|
  rw [←EuclideanEllipse.rotated_re]
  exact EuclideanEllipse.normalized_far_major R W zeta hR hW.ne' hzeta c d hd (pi x) hx

theorem favored_boundary_major_small [Countable V] [Countable E]
    (hl : G.LocallyFinite) (mu : Measure (Set E)) [IsFiniteMeasure mu]
    (pi : V → ℂ) (A : Set V) (hA : A.Finite) (W zeta r : ℝ)
    (hW : 0<W) (hzeta : 0≤zeta) (hzeta' : zeta≤1/10000) (hr : 0 < r)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      mu (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0) :
    ∃ N : ℕ, ∀ R : ℝ, 0<R → 10*(N : ℝ)≤R → ∀ c d : Circle,
      r ≤ mu.real (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d) →
      |((c : ℂ)⁻¹*(d : ℂ)).re|<1/8 := by
  obtain ⟨N,hN⟩ := G.uniform_long_strip_exits hl mu (fun x => (pi x).re)
    (fun x => (pi x).im) A hA (W*(1+zeta)) r (by positivity) hr
    (fun a b hab => hnull a b hab _)
  refine ⟨N,?_⟩
  intro R hR hRN c d hprob
  by_contra hn
  have hunit : (c : ℂ).re^2+(c : ℂ).im^2=1 := by
    have h := Circle.normSq_coe c
    simpa [Complex.normSq_apply,pow_two] using h
  have hsmall := hN (R/10) (by linarith) (c : ℂ).re (c : ℂ).im hunit
  have hmono := ENNReal.toReal_mono (measure_ne_top mu _)
    (measure_mono (G.ellipseExit_subset_longStrip pi A R W zeta hR hW hzeta' c d (le_of_not_gt hn)))
  exact (not_lt_of_ge (hprob.trans hmono) hsmall).elim

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseMesh
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

lemma normalize_basis (R W : ℝ) (c : Circle) (z : ℂ) :
    normalize R W c z=z.re•normalize R W c 1+z.im•normalize R W c Complex.I := by
  have hz : z=z.re•(1 : ℂ)+z.im•Complex.I := by
    apply Complex.ext <;> simp
  rw [hz,normalize_real_linear]
  simp

lemma basis_difference_bound (R W R' W' : ℝ) (c d : Circle) (q : ℝ) (hq : 0≤q)
    (h1 : ‖normalize R W c 1-normalize R' W' d 1‖≤q)
    (hI : ‖normalize R W c Complex.I-normalize R' W' d Complex.I‖≤q) (z : ℂ) :
    ‖normalize R W c z-normalize R' W' d z‖≤2*q*‖z‖ := by
  have he : normalize R W c z-normalize R' W' d z=
      z.re•(normalize R W c 1-normalize R' W' d 1)+
      z.im•(normalize R W c Complex.I-normalize R' W' d Complex.I) := by
    rw [normalize_basis R W c z,normalize_basis R' W' d z]
    simp only [smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖z.re•(normalize R W c 1-normalize R' W' d 1)‖+
      ‖z.im•(normalize R W c Complex.I-normalize R' W' d Complex.I)‖ := norm_add_le _ _
    _ = |z.re| * ‖normalize R W c 1-normalize R' W' d 1‖+
      |z.im| * ‖normalize R W c Complex.I-normalize R' W' d Complex.I‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ |z.re| * q+|z.im| * q := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hI (abs_nonneg _))
    _ ≤ 2*q*‖z‖ := by nlinarith [mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) hq,
      mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) hq]

lemma diskRadius_bounds (W U : ℝ) (hWU : W≤U) {p : ℝ×ℝ} (hp : p∈parameterDisk) :
    W≤diskRadius W U p ∧ diskRadius W U p≤U := by
  obtain ⟨⟨hs,_hφ⟩,hs',_hφ'⟩ := hp
  dsimp [diskRadius]
  constructor <;> nlinarith

lemma diskNormalize_continuousOn (W U : ℝ) (hW : 0<W) (hWU : W≤U) (z : ℂ) :
    ContinuousOn (fun p => diskNormalize W U p z) parameterDisk := by
  have hR : ∀ p∈parameterDisk, diskRadius W U p≠0 := fun p hp =>
    ne_of_gt (hW.trans_le (diskRadius_bounds W U hWU hp).1)
  have hc : Continuous (fun p : ℝ×ℝ => (Circle.exp p.2 : ℂ)) := by
    simp only [Circle.coe_exp]
    fun_prop
  have hcinv : Continuous (fun p : ℝ×ℝ => (Circle.exp p.2 : ℂ)⁻¹) :=
    hc.inv₀ (fun p => (Circle.exp p.2).coe_ne_zero)
  have hRd : ContinuousOn (fun p => 1/diskRadius W U p) parameterDisk := by
    apply continuousOn_const.div
    · unfold diskRadius
      fun_prop
    · exact hR
  unfold diskNormalize normalize diagonal
  apply hc.continuousOn.mul
  have hre := hRd.mul (Complex.continuous_re.comp (hcinv.mul (continuous_const : Continuous (fun _ : ℝ×ℝ => z)))).continuousOn
  have him := (continuousOn_const : ContinuousOn (fun _ : ℝ×ℝ => 1/W) parameterDisk).mul
    (Complex.continuous_im.comp (hcinv.mul (continuous_const : Continuous (fun _ : ℝ×ℝ => z)))).continuousOn
  have hd := (Complex.continuous_ofReal.comp_continuousOn hre).add
    ((Complex.continuous_ofReal.comp_continuousOn him).mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ×ℝ => Complex.I) parameterDisk))
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  apply Complex.ext <;> simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add,sub_zero]

theorem diskNormalize_uniform_comparison (W U zeta : ℝ)
    (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta) :
    ∃ delta : ℝ, 0<delta ∧ ∀ p∈parameterDisk, ∀ q∈parameterDisk,
      dist p q<delta → ∀ z : ℂ,
        ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖ := by
  let F : (ℝ×ℝ) → (ℂ × ℂ) := fun p => (diskNormalize W U p 1,diskNormalize W U p Complex.I)
  have hc : ContinuousOn F parameterDisk := (diskNormalize_continuousOn W U hW hWU 1).prodMk
    (diskNormalize_continuousOn W U hW hWU Complex.I)
  have hcompact : IsCompact parameterDisk := isCompact_Icc
  have hu := hcompact.uniformContinuousOn_of_continuous hc
  have hU : 0<U := hW.trans_le hWU
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (zeta/(2*U)) (by positivity)
  refine ⟨delta,hdelta,?_⟩
  intro p hp q hq hpq z
  have h := hclose p hp q hq hpq
  rw [Prod.dist_eq] at h
  have h1 : ‖diskNormalize W U p 1-diskNormalize W U q 1‖≤zeta/(2*U) := by
    have hh := (lt_of_le_of_lt (le_max_left _ _) h).le
    simpa only [F,dist_eq_norm] using hh
  have hI : ‖diskNormalize W U p Complex.I-diskNormalize W U q Complex.I‖≤zeta/(2*U) := by
    have hh := (lt_of_le_of_lt (le_max_right _ _) h).le
    simpa only [F,dist_eq_norm] using hh
  have hnorm := basis_difference_bound (diskRadius W U p) W (diskRadius W U q) W
    (Circle.exp p.2) (Circle.exp q.2) (zeta/(2*U)) (by positivity) h1 hI (diskExpand W U q z)
  have hqR := diskRadius_bounds W U hWU hq
  have hexpand : ‖diskExpand W U q z‖≤U*‖z‖ :=
    (expand_norm_le (diskRadius W U q) W hW.le hqR.1 (Circle.exp q.2) z).trans
      (mul_le_mul_of_nonneg_right hqR.2 (norm_nonneg _))
  have hcancel : diskNormalize W U q (diskExpand W U q z)=z :=
    normalize_expand _ W (ne_of_gt (hW.trans_le hqR.1)) hW.ne' _ z
  change ‖diskNormalize W U p (diskExpand W U q z)-diskNormalize W U q (diskExpand W U q z)‖≤_ at hnorm
  rw [hcancel] at hnorm
  apply hnorm.trans
  have hmul := mul_le_mul_of_nonneg_left hexpand (by positivity : 0≤2*(zeta/(2*U)))
  convert hmul using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseAngles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

lemma circle_arg_re (c : Circle) : Real.cos (c : ℂ).arg=(c : ℂ).re := by
  simpa only [Circle.norm_coe,div_one] using Complex.cos_arg c.coe_ne_zero

lemma circle_arg_im (c : Circle) : Real.sin (c : ℂ).arg=(c : ℂ).im := by
  simpa only [Circle.norm_coe,div_one] using Complex.sin_arg (c : ℂ)

lemma circle_exp_re (phi : ℝ) : (Circle.exp phi : ℂ).re=Real.cos phi := by
  simp only [Circle.coe_exp,Complex.exp_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,one_mul,Complex.mul_im,
    mul_one,add_zero]

lemma circle_exp_im (phi : ℝ) : (Circle.exp phi : ℂ).im=Real.sin phi := by
  simp only [Circle.coe_exp,Complex.exp_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,one_mul,Complex.mul_im,
    mul_one,add_zero]

lemma rotated_major_cos (phi : ℝ) (c : Circle) :
    ((Circle.exp phi : ℂ)⁻¹*(c : ℂ)).re=Real.cos ((c : ℂ).arg-phi) := by
  rw [rotated_re,circle_exp_re,circle_exp_im,Real.cos_sub,circle_arg_re,circle_arg_im]
  ring

lemma boundary_error_lt (phi : ℝ) (c : Circle)
    (hc : |((Circle.exp phi : ℂ)⁻¹*(c : ℂ)).re|<1/8) :
    |boundaryError phi c|<Real.pi/8 := by
  have he : lineAngle c-((2*phi+Real.pi : ℝ) : Real.Angle)=
      ((2*((c : ℂ).arg-phi-Real.pi/2) : ℝ) : Real.Angle) := by
    rw [lineAngle,←Real.Angle.coe_sub]
    congr 1
    ring
  have hs : |Real.sin ((c : ℂ).arg-phi-Real.pi/2)|<1/8 := by
    rw [Real.sin_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_sub,abs_neg]
    rwa [rotated_major_cos] at hc
  have hh := doubled_angle_le_sine ((c : ℂ).arg-phi-Real.pi/2)
  rw [boundaryError,he]
  exact hh.trans_lt (by nlinarith [Real.pi_pos])

lemma boundary_lift (phi : ℝ) (c : Circle) :
    lineAngle c=((2*phi+Real.pi+boundaryError phi c : ℝ) : Real.Angle) := by
  simp only [Real.Angle.coe_add,boundaryError,Real.Angle.coe_toReal]
  abel

lemma boundary_error_seam (c : Circle) : boundaryError Real.pi c=boundaryError 0 c := by
  unfold boundaryError
  congr 1
  have he : ((2*Real.pi+Real.pi : ℝ) : Real.Angle)=((Real.pi : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add,Real.Angle.coe_two_pi,zero_add]
  simp [he]

lemma circle_exp_pi : Circle.exp Real.pi= -(Circle.exp 0) := by
  apply Subtype.ext
  apply Complex.ext
  · simp only [circle_exp_re,Circle.coe_neg,Complex.neg_re,Real.cos_pi,Real.cos_zero]
  · simp only [circle_exp_im,Circle.coe_neg,Complex.neg_im,Real.sin_pi,Real.sin_zero,neg_zero]

lemma diskNormalize_seam (W U s : ℝ) : diskNormalize W U (s,Real.pi)=diskNormalize W U (s,0) := by
  funext z
  change normalize _ W (Circle.exp Real.pi) z=normalize _ W (Circle.exp 0) z
  rw [circle_exp_pi,normalize_neg]
  rfl

lemma diskNormalize_center (W U phi : ℝ) : diskNormalize W U (0,phi)=diskNormalize W U (0,0) := by
  funext z
  simp only [diskNormalize,diskRadius,mul_zero,add_zero,normalize_center]

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

lemma gridPoint_mem {N K i k : ℕ} (hN : 0<N) (hK : 0<K) (hi : i≤N) (hk : k≤K) :
    gridPoint N K i k∈parameterDisk := by
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K : ℝ) := Nat.cast_pos.mpr hK
  have hir : (i : ℝ)≤N := Nat.cast_le.mpr hi
  have hkr : (k : ℝ)≤K := Nat.cast_le.mpr hk
  change (0≤(i : ℝ)/N ∧ 0≤(k : ℝ)*Real.pi/K) ∧ (i : ℝ)/N≤1 ∧ (k : ℝ)*Real.pi/K≤Real.pi
  exact ⟨⟨by positivity,by positivity⟩,(div_le_one hNr).mpr hir,
    (div_le_iff₀ hKr).mpr (by nlinarith [Real.pi_pos])⟩

lemma gridPoint_dist {N K : ℕ} (hN : 0<N) (hK : 0<K) (i k : ℕ) (a b : ℕ)
    (ha : a≤1) (hb : b≤1) :
    dist (gridPoint N K i k) (gridPoint N K (i+a) (k+b)) ≤ max (1/(N : ℝ)) (Real.pi/K) := by
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K : ℝ) := Nat.cast_pos.mpr hK
  rw [Prod.dist_eq]
  have hfirst : dist (gridPoint N K i k).1 (gridPoint N K (i+a) (k+b)).1≤1/(N : ℝ) := by
    change |(i : ℝ)/N-(i+a : ℕ)/N|≤_
    rw [Nat.cast_add]
    have he : (i : ℝ)/N-((i : ℝ)+a)/N= -(a : ℝ)/N := by ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg a),abs_of_pos hNr]
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha) hNr.le
  have hsecond : dist (gridPoint N K i k).2 (gridPoint N K (i+a) (k+b)).2≤Real.pi/K := by
    change |(k : ℝ)*Real.pi/K-(k+b : ℕ)*Real.pi/K|≤_
    rw [Nat.cast_add]
    have he : (k : ℝ)*Real.pi/K-((k : ℝ)+b)*Real.pi/K= -((b : ℝ)*Real.pi)/K := by ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (by positivity : 0≤(b : ℝ)*Real.pi),abs_of_pos hKr]
    apply div_le_div_of_nonneg_right _ hKr.le
    have hb' : (b : ℝ)≤1 := by exact_mod_cast hb
    nlinarith [Real.pi_pos]
  exact max_le_max hfirst hsecond

lemma exists_grid_mesh (delta : ℝ) (hdelta : 0<delta) :
    ∃ N K : ℕ, 0<N ∧ 0<K ∧ max (1/(N : ℝ)) (Real.pi/K)<delta ∧ Real.pi/K<Real.pi/32 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/delta)
  obtain ⟨K,hK⟩ := exists_nat_gt (max (Real.pi/delta) 32)
  have hNr : 0<(N : ℝ) := lt_trans (by positivity) hN
  have hKr : 0<(K : ℝ) := lt_trans (by norm_num : (0 : ℝ)<32) ((le_max_right _ _).trans_lt hK)
  have hNm : 1/(N : ℝ)<delta := (div_lt_iff₀ hNr).mpr (by
    have := (div_lt_iff₀ hdelta).mp hN
    nlinarith)
  have hKm : Real.pi/(K : ℝ)<delta := (div_lt_iff₀ hKr).mpr (by
    have := (div_lt_iff₀ hdelta).mp ((le_max_left _ _).trans_lt hK)
    nlinarith)
  have hK32 : Real.pi/(K : ℝ)<Real.pi/32 := div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    ((le_max_right _ _).trans_lt hK)
  exact ⟨N,K,Nat.cast_pos.mp hNr,Nat.cast_pos.mp hKr,max_lt hNm hKm,hK32⟩

lemma gridPoint_angular_step (N K k : ℕ) (hK : 0<K) :
    |(gridPoint N K (0 : ℕ) (k+1)).2-(gridPoint N K 0 k).2|=Real.pi/K := by
  change |((k+1 : ℕ) : ℝ)*Real.pi/K-(k : ℝ)*Real.pi/K|=_
  rw [Nat.cast_add,Nat.cast_one]
  have he : ((k : ℝ)+1)*Real.pi/K-(k : ℝ)*Real.pi/K=Real.pi/K := by ring
  rw [he,abs_of_nonneg (by positivity)]

theorem exists_grid_comparison (W U zeta : ℝ) (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta) :
    ∃ N K : ℕ, 0<N ∧ 0<K ∧ Real.pi/K<Real.pi/32 ∧
      ∀ i≤N, ∀ k≤K, ∀ a≤1, ∀ b≤1, i+a≤N → k+b≤K → ∀ z : ℂ,
        ‖diskNormalize W U (gridPoint N K i k) (diskExpand W U (gridPoint N K (i+a) (k+b)) z)-z‖≤zeta*‖z‖ := by
  obtain ⟨delta,hd,hcomp⟩ := diskNormalize_uniform_comparison W U zeta hW hWU hzeta
  obtain ⟨N,K,hN,hK,hm,hangle⟩ := exists_grid_mesh delta hd
  refine ⟨N,K,hN,hK,hangle,?_⟩
  intro i hi k hk a ha b hb hia hkb z
  exact hcomp _ (gridPoint_mem hN hK hi hk) _ (gridPoint_mem hN hK hia hkb)
    ((gridPoint_dist hN hK i k a b ha hb).trans_lt hm) z

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

theorem separated_neighboring_ellipses (W U zeta : ℝ)
    (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta)
    (chooseCenter : (ℂ → ℂ) → Circle)
    (hboundary : ∀ phi : ℝ,
      |((Circle.exp phi : ℂ)⁻¹*(chooseCenter (normalize U W (Circle.exp phi)) : ℂ)).re|<1/8) :
    ∃ p∈parameterDisk, ∃ q∈parameterDisk,
      (∀ z : ℂ, ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖) ∧
      (1 : ℝ)/4≤|EllipseLinear.det
        (chooseCenter (diskNormalize W U p) : ℂ).re (chooseCenter (diskNormalize W U p) : ℂ).im
        (chooseCenter (diskNormalize W U q) : ℂ).re (chooseCenter (diskNormalize W U q) : ℂ).im| := by
  obtain ⟨N,K,hN,hK,hangle,hcomp⟩ := exists_grid_comparison W U zeta hW hWU hzeta
  have hNr : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hKr : (K : ℝ)≠0 := (Nat.cast_pos.mpr hK).ne'
  let phi : ℕ → ℝ := fun k => (k : ℝ)*Real.pi/K
  let centers : ℕ → ℕ → Circle := fun i k => chooseCenter (diskNormalize W U (gridPoint N K i k))
  let F : ℕ → ℕ → Real.Angle := fun i k => lineAngle (centers i k)
  have hp0 : phi 0=0 := by simp [phi]
  have hpK : phi K=Real.pi := by dsimp [phi]; field_simp
  have hn : ∀ k, diskNormalize W U (gridPoint N K N k)=normalize U W (Circle.exp (phi k)) := by
    intro k
    simp only [diskNormalize,gridPoint,div_self hNr,diskRadius,mul_one,add_sub_cancel,phi]
  have hc : ∀ k≤K, F 0 k=F 0 0 := by
    intro k _hk
    dsimp [F,centers,gridPoint]
    simp only [Nat.cast_zero,zero_div,zero_mul]
    rw [diskNormalize_center W U ((k : ℝ)*Real.pi/K)]
  have hs : ∀ i≤N, F i K=F i 0 := by
    intro i _hi
    have he : gridPoint N K i K=((i : ℝ)/N,Real.pi) := by
      simp only [gridPoint]
      congr 1
    have he0 : gridPoint N K i 0=((i : ℝ)/N,0) := by simp [gridPoint]
    dsimp [F,centers]
    rw [he,he0,diskNormalize_seam]
  let err : ℕ → ℝ := fun k => boundaryError (phi k) (centers N k)
  let b : ℕ → ℝ := fun k => 2*phi k+Real.pi+err k
  have herr : ∀ k≤K, |err k|<Real.pi/8 := by
    intro k _hk
    apply boundary_error_lt
    simpa only [centers,hn] using hboundary (phi k)
  have hlift : ∀ k≤K, F N k=(b k : Real.Angle) := by
    intro k _hk
    exact boundary_lift (phi k) (centers N k)
  have hmesh : ∀ k<K, |phi (k+1)-phi k|<Real.pi/32 := by
    intro k _hk
    have he := gridPoint_angular_step N K k hK
    exact he.trans_lt hangle
  have hstep := DiskWinding.boundary_mesh_lifts phi err K hmesh herr
  have hturn : b K-b 0=2*Real.pi := by
    have hcseam : centers N K=centers N 0 := by
      dsimp [centers]
      rw [hn,hn,hpK,hp0,circle_exp_pi]
      congr 1
      funext z
      exact normalize_neg U W (Circle.exp 0) z
    have heseam : err K=err 0 := by
      dsimp [err]
      rw [hpK,hp0,hcseam,boundary_error_seam]
    dsimp [b]
    rw [hpK,hp0,heseam]
    ring
  have hex := DiskWinding.exists_large_edge F N K b hc hs hlift hstep hturn
  have edge : ∀ i≤N, ∀ k≤K, ∀ a≤1, ∀ b≤1, i+a≤N → k+b≤K →
      Real.pi/4≤|DiskWinding.increment (F i k) (F (i+a) (k+b))| →
      ∃ p∈parameterDisk, ∃ q∈parameterDisk,
        (∀ z : ℂ, ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖) ∧
        (1 : ℝ)/4≤|EllipseLinear.det
          (chooseCenter (diskNormalize W U p) : ℂ).re (chooseCenter (diskNormalize W U p) : ℂ).im
          (chooseCenter (diskNormalize W U q) : ℂ).re (chooseCenter (diskNormalize W U q) : ℂ).im| := by
    intro i hi k hk a ha b hb hia hkb hsep
    refine ⟨gridPoint N K i k,gridPoint_mem hN hK hi hk,
      gridPoint N K (i+a) (k+b),gridPoint_mem hN hK hia hkb,hcomp i hi k hk a ha b hb hia hkb,?_⟩
    have hd := EllipseLinear.det_lower_of_separation (centers i k : ℂ).arg (centers (i+a) (k+b) : ℂ).arg hsep
    simpa only [circle_arg_re,circle_arg_im] using hd
  rcases hex with ⟨i,hi,k,hk,hik⟩ | ⟨i,hi,k,hk,hik⟩ | ⟨i,hi,k,hk,hik⟩
  · exact edge i hi k (by omega) 0 (by omega) 1 (by omega) (by omega) (by omega) (by simpa using hik)
  · exact edge i (by omega) k hk 1 (by omega) 0 (by omega) (by omega) (by omega) (by simpa using hik)
  · exact edge i (by omega) k (by omega) 1 (by omega) 1 (by omega) (by omega) (by omega) hik

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripOrigin
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

lemma exists_strip_scale (B K d : ℝ) (hd : 0<d) :
    ∃ U : ℝ, 0<U ∧ B<U ∧ K/U<d := by
  obtain ⟨U,hU⟩ := exists_gt (max 0 (max B (K/d)))
  have hU0 : 0<U := (le_max_left _ _).trans_lt hU
  have hBU : B<U := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hU
  have hKU : K/d<U := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hU
  exact ⟨U,hU0,hBU,(div_lt_iff₀ hU0).mpr (by nlinarith [(div_lt_iff₀ hd).mp hKU])⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_EllipseProbability
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma normalized_edge_bound (pi : V → ℂ) (R W D : ℝ) (hW : 0<W) (hWR : W≤R)
    (c : Circle) (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D) :
    ∀ ⦃x y⦄, G.fullGraph.Adj x y →
      ‖EuclideanEllipse.normalize R W c (pi x)-EuclideanEllipse.normalize R W c (pi y)‖≤D/W := by
  intro x y hxy
  rw [←EuclideanEllipse.normalize_sub]
  exact (EuclideanEllipse.normalize_norm_le R W hW hWR c _).trans
    (div_le_div_of_nonneg_right (hpi hxy) hW.le)

lemma normalized_clusters_finite (pi : V → ℂ) (R W : ℝ) (hW : 0<W) (hWR : W≤R)
    (c : Circle) (mu : Measure (Set E))
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂mu, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) a).Finite) :
    ∀ᵐ ω ∂mu, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}) a).Finite := by
  have hR : 0<R := hW.trans_le hWR
  have hsub : {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}⊆
      {x | |(pi x).re|≤R ∧ |(pi x).im|≤R} := by
    intro x hx
    change ‖EuclideanEllipse.normalize R W c (pi x)‖≤1 at hx
    have hn : ‖pi x‖≤R := by
      calc
        _ = ‖EuclideanEllipse.expand R W c (EuclideanEllipse.normalize R W c (pi x))‖ := by
          rw [EuclideanEllipse.expand_normalize R W hR.ne' hW.ne']
        _ ≤ R*‖EuclideanEllipse.normalize R W c (pi x)‖ := EuclideanEllipse.expand_norm_le R W hW.le hWR c _
        _ ≤ R := by nlinarith
    exact ⟨(Complex.abs_re_le_norm _).trans hn,(Complex.abs_im_le_norm _).trans hn⟩
  filter_upwards [hbox R R] with ω hω a
  exact (hω a).subset (G.cluster_mono (Set.inter_subset_inter_right _ (G.inducedEdges_mono hsub)) a)

theorem all_ellipses_favored [Countable E]
    (pi : V → ℂ) (A : Set V) (W B D zeta : ℝ) (hD : 0≤D) (hW : 0<W)
    (hBW : B<W) (hDz : D/W≤zeta)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hA : ∀ a∈A, ‖pi a‖≤B) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (q : E → unitInterval) (a : ℝ) (ha : 0≤a)
    (hi : 1-a^S.card<(BernoulliProduct.law q).real (G.seedInfiniteEvent A))
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite) :
    ∀ R : ℝ, W≤R → ∀ c : Circle, ∃ d∈S,
      1-a<(BernoulliProduct.law q).real (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d) := by
  intro R hWR c
  have hseed : ∀ x∈A, ‖EuclideanEllipse.normalize R W c (pi x)‖<1 := by
    intro x hx
    exact (EuclideanEllipse.normalize_norm_le R W hW hWR c (pi x)).trans_lt
      ((div_lt_one hW).mpr ((hA x hx).trans_lt hBW))
  have hbound : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x∈A,
      (G.cluster (ω∩G.inducedEdges {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}) x).Finite := by
    filter_upwards [G.normalized_clusters_finite pi R W hW hWR c (BernoulliProduct.law q) hbox] with ω hω x _hx
    exact hω x
  exact G.exists_favored_ellipse _ A zeta (D/W) (by positivity) hDz
    (G.normalized_edge_bound pi R W D hW hWR c hpi) hseed S hcover q a ha hi hbound

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseOrigin
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

theorem ellipse_origin_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (pi : V → ℂ) (o : V) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hone : BernoulliProduct.law (fun _ : E => pc) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => pc)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ R W : ℝ, ∃ c d e : Circle,
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e x-
          ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e y| ≤ rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e x-
          ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e y| ≤ rho) ∧
      ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
        (G.boxMove (ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e)
          (ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e) m (eps/8) 30 o (Corridor.sign b)) := by
  let zeta := eps/1000
  have hzeta : 0<zeta := by dsimp [zeta] <;> positivity
  have hzeta' : zeta≤1/10000 := by dsimp [zeta] <;> linarith
  let a := min (eta/2) (1/2)
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have haeta : a<eta := (min_le_left _ _).trans_lt (by linarith)
  have haone : a<1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨S,hS⟩ := EuclideanEllipse.finite_circle_cover zeta hzeta
  obtain ⟨m,hm⟩ := G.exists_seed_infinite_probability hc o (fun _ : E => pc) hone (a^S.card) (pow_pos ha _)
  have hAfin := G.vertexBall_finite hl o m
  obtain ⟨B,hB⟩ := (hAfin.image (fun x => ‖pi x‖)).bddAbove
  have hAB : ∀ x∈G.vertexBall o m, ‖pi x‖≤B := fun x hx => hB ⟨x,hx,rfl⟩
  refine ⟨m,?_⟩
  intro rho hrho
  obtain ⟨W,hW,hBW,hmesh⟩ := exists_strip_scale B D (min zeta (rho/16)) (lt_min hzeta (by positivity))
  have hDz : D/W≤zeta := hmesh.le.trans (min_le_left _ _)
  have hDrho : 16*(D/W) ≤ rho := by have := hmesh.trans_le (min_le_right _ _); linarith
  have hfav := G.all_ellipses_favored pi (G.vertexBall o m) W B D zeta hD hW hBW hDz hpi hAB
    S hS (fun _ : E => pc) a ha.le hm hbox
  let chooseCenter : (ℂ → ℂ) → Circle := fun f => Classical.epsilon
    (fun c => c∈S ∧ 1-a<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.ellipseExit (f ∘ pi) (G.vertexBall o m) zeta c))
  have hselect : ∀ R : ℝ, W≤R → ∀ c : Circle,
      1-a<(BernoulliProduct.law (fun _ : E => pc)).real
        (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) (G.vertexBall o m) zeta
          (chooseCenter (EuclideanEllipse.normalize R W c))) := by
    intro R hWR c
    exact (Classical.epsilon_spec (hfav R hWR c)).2
  obtain ⟨N,hN⟩ := G.favored_boundary_major_small hl (BernoulliProduct.law (fun _ : E => pc))
    pi (G.vertexBall o m) hAfin W zeta (1-a) hW hzeta.le hzeta' (by linarith) hnull
  let U := max W (10*(N : ℝ))
  have hWU : W≤U := le_max_left _ _
  have hU : 0<U := hW.trans_le hWU
  have hboundary : ∀ phi : ℝ,
      |((Circle.exp phi : ℂ)⁻¹*(chooseCenter (EuclideanEllipse.normalize U W (Circle.exp phi)) : ℂ)).re|<1/8 := by
    intro phi
    exact hN U hU (le_max_right _ _) _ _ (hselect U hWU _).le
  obtain ⟨p,hp,q,hq,hcomp,hdet⟩ := EuclideanEllipse.separated_neighboring_ellipses W U zeta hW hWU hzeta chooseCenter hboundary
  have hpR := EuclideanEllipse.diskRadius_bounds W U hWU hp
  have hqR := EuclideanEllipse.diskRadius_bounds W U hWU hq
  let R := EuclideanEllipse.diskRadius W U p
  let c := Circle.exp p.2
  let Psi := EuclideanEllipse.diskNormalize W U p ∘ pi
  let Psi' := EuclideanEllipse.diskNormalize W U q ∘ pi
  let d := chooseCenter (EuclideanEllipse.diskNormalize W U p)
  let e := chooseCenter (EuclideanEllipse.diskNormalize W U q)
  have hstep := G.ellipse_coordinates_step Psi d e hdet (D/W)
    (G.normalized_edge_bound pi R W D hW hpR.1 c hpi)
  have hpert : ∀ x, ‖Psi x-Psi' x‖≤zeta*‖Psi' x‖ := by
    intro x
    have hh := hcomp (Psi' x)
    have he : EuclideanEllipse.diskExpand W U q (Psi' x)=pi x :=
      EuclideanEllipse.expand_normalize _ W (ne_of_gt (hW.trans_le hqR.1)) hW.ne' _ (pi x)
    rwa [he] at hh
  have hPsi0 : Psi o=0 := by
    change EuclideanEllipse.normalize R W c (pi o)=0
    rw [hpo,EuclideanEllipse.normalize_origin]
  refine ⟨R,W,c,d,e,(fun {_ _} h => (hstep.1 h).trans hDrho),
    (fun {_ _} h => (hstep.2 h).trans hDrho),?_⟩
  intro b
  cases b
  · have hfavored := hselect (EuclideanEllipse.diskRadius W U q) hqR.1 (Circle.exp q.2)
    have hmono := ENNReal.toReal_mono (measure_ne_top (BernoulliProduct.law (fun _ : E => pc)) _)
      (measure_mono (G.ellipseExit_boxMove Psi Psi' o m d e hdet eps heps heps' hPsi0 hpert false))
    exact (by linarith : 1-eta<1-a).trans (hfavored.trans_le hmono)
  · have hfavored := hselect (EuclideanEllipse.diskRadius W U p) hpR.1 (Circle.exp p.2)
    have hsame : ∀ x, ‖Psi x-Psi x‖≤(eps/1000)*‖Psi x‖ := by intro x; simp only [sub_self,norm_zero] <;> positivity
    have hmono := ENNReal.toReal_mono (measure_ne_top (BernoulliProduct.law (fun _ : E => pc)) _)
      (measure_mono (G.ellipseExit_boxMove Psi Psi o m d e hdet eps heps heps' hPsi0 hsame true))
    exact (by linarith : 1-eta<1-a).trans (hfavored.trans_le hmono)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_MoveTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma boxMove_aut_subset (t z : V → ℝ) (m : ℕ) (q B : ℝ) (o : V) (s : ℝ)
    (φ : G.Aut) (ht : ∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y)
    (hz : ∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y) :
    G.boxMove t z m q B o s ⊆ (fun ω => φ.edge '' ω) ⁻¹'
      G.boxMove t z m q B (φ.vertex o) s := by
  rintro ω ⟨a,ha,b,w,hw,hbt,hbz⟩
  let w' := w.map (Aut.openGraphIso G φ ω).toHom
  refine ⟨φ.vertex a,(Aut.vertexBall_mem G φ o a m).mpr ha,φ.vertex b,w',?_,?_,?_⟩
  · intro x hx
    change x∈(w.map (Aut.openGraphIso G φ ω).toHom).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    change |t (φ.vertex v)-t (φ.vertex o)|≤B ∧ |z (φ.vertex v)-z (φ.vertex o)|≤B
    rw [ht,hz]
    exact hw v hv
  · have h : t (φ.vertex b)-(t (φ.vertex o)+1)=t b-(t o+1) := by linarith [ht b o]
    rwa [h]
  · have h : z (φ.vertex b)-(z (φ.vertex o)+s)=z b-(z o+s) := by linarith [hz b o]
    rwa [h]

lemma boxMove_aut_probability [Countable V] [Countable E]
    (t z : V → ℝ) (m : ℕ) (q B : ℝ) (o : V) (s : ℝ) (p : unitInterval)
    (φ : G.Aut) (ht : ∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y)
    (hz : ∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y) :
    (G.law p).real (G.boxMove t z m q B o s) ≤
      (G.law p).real (G.boxMove t z m q B (φ.vertex o) s) := by
  have hm : G.law p (G.boxMove t z m q B o s) ≤
      G.law p (G.boxMove t z m q B (φ.vertex o) s) := by
    conv_rhs => rw [← G.law_map_aut p φ]
    rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
      (G.boxMove_measurable _ _ _ _ _ _ _)]
    exact measure_mono (G.boxMove_aut_subset t z m q B o s φ ht hz)
  exact ENNReal.toReal_mono (measure_ne_top _ _) hm

lemma boxMove_close_center (t z : V → ℝ) (m c : ℕ) (e s : ℝ) (he : e<1/10)
    {x y : V} (hxy : x∈G.vertexBall y c)
    (ht : |t x-t y|≤e/8) (hz : |z x-z y|≤e/8) :
    G.boxMove t z m (e/8) 30 x s ⊆ G.coordinateMove t z (m+c) e y s := by
  rintro ω ⟨a,ha,b,w,hw,hbt,hbz⟩
  refine ⟨a,?_,b,w,?_,?_,?_⟩
  · simpa only [Nat.add_comm c m] using G.vertexBall_add hxy m ha
  · intro v hv
    have hvb := hw v hv
    constructor
    · have := abs_sub_le (t v) (t x) (t y)
      linarith [hvb.1]
    · have := abs_sub_le (z v) (z x) (z y)
      linarith [hvb.2]
  · have hh := abs_sub_le (t b) (t x+1) (t y+1)
    rw [add_sub_add_right_eq_sub] at hh
    linarith
  · have hh := abs_sub_le (z b) (z x+s) (z y+s)
    rw [add_sub_add_right_eq_sub] at hh
    linarith

theorem uniform_moves_of_origin [Countable V] [Countable E]
    (t z : V → ℝ) (o : V) (m c : ℕ) (e eta rho : ℝ)
    (he : e<1/10) (hrho : 0 ≤ rho) (hmesh : c*rho≤e/8)
    (ht : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |t x-t y| ≤ rho)
    (hz : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |z x-z y| ≤ rho)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y) ∧
      (∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y))
    (pc : unitInterval) (hpc : 0<pc)
    (horigin : ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.boxMove t z m (e/8) 30 o (Corridor.sign b))) :
    ∃ p : unitInterval, (pc : ℝ)/2≤p ∧ p<pc ∧ ∀ y s, |s|=1 →
      1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
        (G.coordinateMove t z (m+c) e y s) := by
  obtain ⟨p,hpl,hpu,hp⟩ := G.lower_two_boxMoves t z m (e/8) 30 o pc hpc eta horigin
  refine ⟨p,hpl,hpu,?_⟩
  intro y s hs
  obtain ⟨b,hb⟩ : ∃ b : Bool, Corridor.sign b=s := by
    rcases (abs_eq (by norm_num : (0 : ℝ)≤1)).mp hs with h|h
    · exact ⟨true,by simpa [Corridor.sign] using h.symm⟩
    · exact ⟨false,by simpa [Corridor.sign] using h.symm⟩
  obtain ⟨φ,hφ,hφt,hφz⟩ := hdense y
  have htt := (G.coordinate_ball_bound t rho hrho ht hφ).trans hmesh
  have hzz := (G.coordinate_ball_bound z rho hrho hz hφ).trans hmesh
  have hsub := G.boxMove_close_center t z m c e s he hφ htt hzz
  have hm : (G.law p).real (G.boxMove t z m (e/8) 30 (φ.vertex o) s)≤
      (G.law p).real (G.coordinateMove t z (m+c) e y s) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hp' := hp b
  rw [hb] at hp'
  have hp'' : 1-eta≤(G.law p).real (G.boxMove t z m (e/8) 30 o s) := by
    simpa only [law,BernoulliProduct.law_const] using hp'.le
  simpa only [law,BernoulliProduct.law_const] using
    hp''.trans ((G.boxMove_aut_probability t z m (e/8) 30 o s p φ hφt hφz).trans hm)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseUniform
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma ellipse_aut_differences (pi : V → ℂ) (R W : ℝ) (c d e : Circle) (phi : G.Aut)
    (hphi : ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y) :
    (∀ x y, ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex x)-
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex y)=
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e x-
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e y) ∧
    (∀ x y, ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex x)-
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex y)=
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e x-
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e y) := by
  have hPsi : ∀ x y,
      EuclideanEllipse.normalize R W c (pi (phi.vertex x))-EuclideanEllipse.normalize R W c (pi (phi.vertex y))=
      EuclideanEllipse.normalize R W c (pi x)-EuclideanEllipse.normalize R W c (pi y) := by
    intro x y
    rw [←EuclideanEllipse.normalize_sub,←EuclideanEllipse.normalize_sub,hphi]
  constructor
  · intro x y
    rw [(ellipse_coordinates_sub _ d e (phi.vertex x) (phi.vertex y)).1,
      (ellipse_coordinates_sub _ d e x y).1]
    exact congrArg (fun z : ℂ => EllipseLinear.time (d : ℂ).re (d : ℂ).im (e : ℂ).re (e : ℂ).im z.re z.im) (hPsi x y)
  · intro x y
    rw [(ellipse_coordinates_sub _ d e (phi.vertex x) (phi.vertex y)).2,
      (ellipse_coordinates_sub _ d e x y).2]
    exact congrArg (fun z : ℂ => EllipseLinear.height (d : ℂ).re (d : ℂ).im (e : ℂ).re (e : ℂ).im z.re z.im) (hPsi x y)

theorem ellipse_uniform_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpc : 0<pc) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hone : BernoulliProduct.law (fun _ : E => pc) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => pc)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
      (pc : ℝ)/2≤p ∧ p<pc ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |t x-t y| ≤ rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |z x-z y| ≤ rho) ∧
      ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
        (G.coordinateMove t z m eps y s) := by
  obtain ⟨m,hm⟩ := G.ellipse_origin_moves hc hl pi o D pc hD hpo hpi hone hbox hnull eps eta heps heps' heta
  refine ⟨m+c,?_⟩
  intro rho hrho
  let r := min rho (eps/(8*((c : ℝ)+1)))
  have hr : 0 < r := lt_min hrho (div_pos heps (by positivity))
  have hrrho : r ≤ rho := min_le_left _ _
  have hrs : r≤eps/(8*((c : ℝ)+1)) := min_le_right _ _
  have hmesh : (c : ℝ)*r≤eps/8 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*((c : ℝ)+1))).mp hrs
    nlinarith
  obtain ⟨R,W,a,b,d,ht,hz,hmoves⟩ := hm r hr
  let t := ellipseTime (EuclideanEllipse.normalize R W a ∘ pi) b d
  let z := ellipseHeight (EuclideanEllipse.normalize R W a ∘ pi) b d
  have htdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      (∀ x y, t (phi.vertex x)-t (phi.vertex y)=t x-t y) ∧
      (∀ x y, z (phi.vertex x)-z (phi.vertex y)=z x-z y) := by
    intro y
    obtain ⟨phi,hphi,hphiP⟩ := hdense y
    exact ⟨phi,hphi,G.ellipse_aut_differences pi R W a b d phi hphiP⟩
  obtain ⟨p,hpl,hpu,hp⟩ := G.uniform_moves_of_origin t z o m c eps eta r heps' hr.le hmesh ht hz htdense pc hpc hmoves
  exact ⟨t,z,p,hpl,hpu,fun {_ _} h => (ht h).trans hrrho,fun {_ _} h => (hz h).trans hrrho,hp⟩

theorem ellipse_critical_contradiction [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (hpc : 0<(G.criticalProbability : ℝ)) (hpc1 : (G.criticalProbability : ℝ)<1)
    (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hone : BernoulliProduct.law (fun _ : E => G.criticalProbability) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => G.criticalProbability)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0) : False := by
  apply G.approximate_moves_contradiction hc hl hq hpc hpc1
  intro eps eta he he' heta _heta'
  exact G.ellipse_uniform_moves hc hl pi o c D G.criticalProbability hD hpc hpo hpi hdense hone hbox hnull eps eta he he' heta

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_CriticalCoordinates
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
    have hs := G.critical_strip_null hc hl hq hg hpc1 u v o c (2*D) (by positivity) huo hvo hsteps.1 hsteps.2
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
  exact G.ellipse_critical_contradiction hc hl hq pi o c D hD hpc hpc1 hpo hpi hdense hone hbox hnull

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Classification_StructuredCoordinates
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

theorem exists_integer_pair_coordinates
    (ρ : Λ →* N) (hρ : Surjective ρ)
    (φ : N →* Multiplicative (ℤ×ℤ)) (hφ : Surjective φ)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    [Nonempty V] :
    ∃ z : V → ℤ×ℤ, Surjective z ∧
      ∀ g v, z (g • v)=(φ (ρ g)).toAdd+z v := by
  obtain ⟨π,hπ⟩ := EquivariantCoordinates.exists_equivariant (φ.comp ρ)
    (EquivariantCoordinates.stabilizer_killed ρ φ hstab)
  refine ⟨fun v => (π v).toAdd,?_,?_⟩
  · intro t
    obtain ⟨v,hv⟩ := EquivariantCoordinates.surjective_of_equivariant
      (φ.comp ρ) (hφ.comp hρ) π hπ (Multiplicative.ofAdd t)
    exact ⟨v,congrArg Multiplicative.toAdd hv⟩
  · intro g v
    exact congrArg Multiplicative.toAdd (hπ g v)

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

theorem critical_null_of_action_coordinates
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

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CentralCommutatorGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G : Type*} [Group G]

private lemma central_conjugation {z : G} (hz : z∈Subgroup.center G) (a : G) :
    a*z*a⁻¹=z := by
  rw [Subgroup.mem_center_iff.mp hz a,mul_assoc,mul_inv_cancel,mul_one]

private lemma central_comm_inv_left {a b : G} (h : ⁅a,b⁆∈Subgroup.center G) :
    ⁅a⁻¹,b⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_left,←commutatorElement_inv]
  simpa using central_conjugation ((Subgroup.center G).inv_mem h) a⁻¹

private lemma central_comm_inv_right {a b : G} (h : ⁅a,b⁆∈Subgroup.center G) :
    ⁅a,b⁻¹⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_right,←commutatorElement_inv]
  simpa using central_conjugation ((Subgroup.center G).inv_mem h) b⁻¹

theorem central_commutator_generated (S T : Set G)
    (hc : ⁅Subgroup.closure S,Subgroup.closure T⁆≤Subgroup.center G) :
    ⁅Subgroup.closure S,Subgroup.closure T⁆=
      Subgroup.closure (Set.image2 (fun a b : G => ⁅a,b⁆) S T) := by
  let K := Subgroup.closure (Set.image2 (fun a b : G => ⁅a,b⁆) S T)
  have hz {a b : G} (ha : a∈Subgroup.closure S) (hb : b∈Subgroup.closure T) :
      ⁅a,b⁆∈Subgroup.center G := hc (Subgroup.commutator_mem_commutator ha hb)
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      intro b hb
      induction hb using Subgroup.closure_induction with
      | mem b hb => exact Subgroup.subset_closure (Set.mem_image2.mpr ⟨a,ha,b,hb,rfl⟩)
      | one => simp
      | mul b c hb hc' ihb ihc =>
        rw [commutatorElement_mul_right_eq_mul_conj]
        have he : ⁅a,b⁆*b*⁅a,c⁆*b⁻¹=⁅a,b⁆*(b*⁅a,c⁆*b⁻¹) := by group
        rw [he,central_conjugation (hz (Subgroup.subset_closure ha) hc') b]
        exact K.mul_mem ihb ihc
      | inv b hb ih =>
        rw [central_comm_inv_right (hz (Subgroup.subset_closure ha) hb)]
        exact K.inv_mem ih
    | one => intro b _; simp
    | mul a c ha hc' iha ihc =>
      intro b hb
      rw [commutatorElement_mul_left_eq_conj_mul,
        central_conjugation (hz hc' hb) a]
      exact K.mul_mem (ihc b hb) (iha b hb)
    | inv a ha ih =>
      intro b hb
      rw [central_comm_inv_left (hz ha hb)]
      exact K.inv_mem (ih b hb)
  · apply (Subgroup.closure_le _).mpr
    rintro z ⟨a,ha,b,hb,rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure ha)
      (Subgroup.subset_closure hb)

theorem central_commutator_fg (H J : Subgroup G) (hH : H.FG) (hJ : J.FG)
    (hc : ⁅H,J⁆≤Subgroup.center G) : ⁅H,J⁆.FG := by
  obtain ⟨S,hS,hfinS⟩ := Subgroup.fg_iff H |>.mp hH
  obtain ⟨T,hT,hfinT⟩ := Subgroup.fg_iff J |>.mp hJ
  apply (Subgroup.fg_iff _).mpr
  refine ⟨Set.image2 (fun a b : G => ⁅a,b⁆) S T,?_,hfinS.image2 _ hfinT⟩
  rw [←central_commutator_generated S T (by rwa [hS,hT]),hS,hT]

theorem class_two_commutator_fg [Group.FG G]
    (hc : commutator G≤Subgroup.center G) : Group.FG (commutator G) := by
  apply (Group.fg_iff_subgroup_fg _).mpr
  exact central_commutator_fg ⊤ ⊤ (Group.fg_def.mp inferInstance)
    (Group.fg_def.mp inferInstance) hc

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ClassTwoRankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G A : Type*} [Group G] [Group A]

theorem class_two_commutator_finite_of_cyclic_mod_torsion [Group.FG G]
    (hc : commutator G≤Subgroup.center G) (ρ : G →* A)
    (hker : ρ.ker≤Subgroup.center G) (g : G)
    (hcyc : ∀ a : G, ∃ k : ℤ, IsOfFinOrder (ρ (a*g^(-k)))) :
    (commutator G : Set G).Finite := by
  let C := commutator G
  let _ : CommGroup C := {
    (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a.val) }
  let _ : Group.FG C := class_two_commutator_fg hc
  let t := centralCommHom hc
  have ht (a b : G) (hb : IsOfFinOrder (ρ b)) : IsOfFinOrder (t a b) := by
    obtain ⟨m,hm,he⟩ := hb.exists_pow_eq_one
    have hpow : b^m∈ρ.ker := by change ρ (b^m)=1; rwa [map_pow]
    have hz := hker hpow
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    rw [←map_pow]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz a)
  have hself : t g g=1 := by apply Subtype.ext; simp [t,centralCommHom,commutatorElement_def]
  have hga (a : G) : IsOfFinOrder (t g a) := by
    obtain ⟨k,hk⟩ := hcyc a
    have h := ht g (a*g^(-k)) hk
    simpa only [map_mul,map_zpow,hself,one_zpow,mul_one] using h
  have hag (a : G) : IsOfFinOrder (t a g) := by
    have he : t a g=(t g a)⁻¹ := by
      apply Subtype.ext
      exact (commutatorElement_inv g a).symm
    rw [he]
    exact (hga a).inv
  have hab (a b : G) : IsOfFinOrder (t a b) := by
    obtain ⟨k,hk⟩ := hcyc b
    have hw := ht a (b*g^(-k)) hk
    have hg : (t a g)^k∈CommGroup.torsion C :=
      (CommGroup.torsion C).zpow_mem (hag a) k
    have hh := (CommGroup.torsion C).mul_mem hw hg
    have he : t a (b*g^(-k))*(t a g)^k=t a b := by
      rw [map_mul,map_zpow,zpow_neg]
      group
    rw [he] at hh
    exact hh
  have hsub : C≤(CommGroup.torsion C).map C.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact ⟨t a b,hab a b,rfl⟩
  let _ : Finite C := CommGroup.finite_of_fg_isMulTorsion C (fun c => by
    obtain ⟨d,hd,he⟩ := hsub c.property
    change IsOfFinOrder d at hd
    exact (show d=c from Subtype.ext he) ▸ hd)
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_IntegerBoxes
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

lemma integerPairBox_finite (k : ℕ) : (integerPairBox k).Finite := by
  have hh := ((Set.finite_Icc (-(k:ℤ)) (k:ℤ)).prod
    (Set.finite_Icc (-(k:ℤ)) (k:ℤ))).image (Multiplicative.ofAdd : ℤ×ℤ → _)
  apply hh.subset
  intro t ht
  refine ⟨t.toAdd,?_,rfl⟩
  have h₁ := abs_le.mp ht.1
  have h₂ := abs_le.mp ht.2
  exact ⟨⟨by exact_mod_cast h₁.1,by exact_mod_cast h₁.2⟩,
    ⟨by exact_mod_cast h₂.1,by exact_mod_cast h₂.2⟩⟩

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DescentCritical
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

universe groupUniverse vertexUniverse edgeUniverse actionUniverse

theorem critical_null_of_algebraic_descent {N : Type groupUniverse} [Group N]
    (hN : AlgebraicDescent N) :
    ∀ {V : Type vertexUniverse} {E : Type edgeUniverse} {Λ : Type actionUniverse}
      [Group Λ] [MulAction Λ V] [MulAction Λ E]
      (G : BondGraph V E),
      G.fullGraph.Connected → G.LocallyFinite → G.SubexponentialGrowth →
      G.PreservesEnds (Λ := Λ) →
      ∀ (S : Set V), S.Finite → (∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) →
      ∀ (ρ : Λ →* N), Surjective ρ →
      (∀ v : V, (MulAction.orbit ρ.ker v).Finite) →
      (∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) →
      G.criticalProbability<1 → G.law G.criticalProbability G.percolates=0 := by
  induction hN with
  | @finite N _ _ =>
    intro V E Λ _ _ _ G _ _ _ _ S hS hcover ρ _ hker _ _
    have hV := EquivariantCoordinates.finite_vertices_of_finite_quotient ρ hker S hS hcover
    have hempty : G.percolates=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨v,hv⟩
      exact hv (hV.subset (Set.subset_univ _))
    rw [hempty,measure_empty]
  | @cyclic N _ φ hφ hf =>
    intro V E Λ _ _ _ G _ hl _ ha S hS hcover ρ hρ hker hstab hpc
    have heq := G.finite_by_integer_critical_one hl ha S hS hcover ρ hρ φ hφ hf hker hstab
    exact False.elim ((ne_of_lt hpc) heq)
  | @plane N _ φ hφ lower ih =>
    intro V E Λ _ _ _ G hc hl hg ha S hS hcover ρ hρ hker hstab hpc
    let _ := hc.nonempty
    let _ := G.countable_vertices hc hl
    let _ := G.countable_bonds hc hl
    obtain ⟨z,hzonto,hz⟩ := exists_integer_pair_coordinates ρ hρ φ hφ hstab
    apply G.critical_null_of_action_coordinates hc hl ha S hS hcover hg hpc
      (fun g => (φ (ρ g)).toAdd) z hzonto hz
    by_contra hbad
    obtain ⟨k,o,ho,hcrit,hpos⟩ := G.bounded_ray_critical_component
      (fun v => ((z v).1 : ℝ)) (fun v => ((z v).2 : ℝ)) (by simpa only [Int.cast_abs] using hbad)
    let zM : V → Multiplicative (ℤ×ℤ) := fun v => Multiplicative.ofAdd (z v)
    let Q := integerPairBox k
    let C := G.domainComponent (zM ⁻¹' Q) o
    let L := componentKernel (φ.comp ρ) C
    let H := G.induce C
    let _ := restrictedVertexAction C L (componentKernel_le (φ.comp ρ) C)
    let _ := G.restrictedEdgeAction ha C L (componentKernel_le (φ.comp ρ) C)
    have hzm : ∀ g v, zM (g • v)=(φ.comp ρ) g*zM v :=
      fun g v => congrArg Multiplicative.ofAdd (hz g v)
    obtain ⟨R,hR,hRcover⟩ := G.componentKernel_finite_orbits ha S hS hcover
      (φ.comp ρ) zM hzm Q (integerPairBox_finite k) o ho
    let f := ρ.comp L.subtype
    have hfker : ∀ v : C, (MulAction.orbit f.rangeRestrict.ker v).Finite :=
      rangeRestrict_kernel_orbits f
        (restricted_kernel_orbits ρ hker C L (componentKernel_le (φ.comp ρ) C))
    have hfstab : ∀ v : C,
        ((MulAction.stabilizer L v).map f.rangeRestrict : Set f.range).Finite :=
      rangeRestrict_stabilizer_images f
        (restricted_stabilizer_images ρ hstab C L (componentKernel_le (φ.comp ρ) C))
    have hle : f.range≤φ.ker := component_quotient_le_kernel ρ φ C
    have hnull := ih f.range hle H
      (G.domainComponent_connected (zM ⁻¹' Q) o) (G.induce_locallyFinite hl C)
      (G.induce_subexponential hl hg C)
      (G.restricted_preservesEnds ha C L (componentKernel_le (φ.comp ρ) C))
      R hR hRcover f.rangeRestrict f.rangeRestrict_surjective hfker hfstab
      (by change H.criticalProbability=G.criticalProbability at hcrit
          rw [hcrit]; exact hpc)
    exact (ne_of_gt hpos) hnull

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_SubgroupFiniteIndexExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation

theorem subgroup_finiteIndex_of_image_and_kernel {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Surjective f) (J : Subgroup G)
    [(J.map f).FiniteIndex] [(J.subgroupOf f.ker).FiniteIndex] : J.FiniteIndex := by
  let S := J ⊔ f.ker
  have hS : S.FiniteIndex := by
    constructor
    have hn := (inferInstance : (J.map f).FiniteIndex).index_ne_zero
    rw [Subgroup.index_map,f.range_eq_top_of_surjective hf,Subgroup.index_top,mul_one] at hn
    exact hn
  let _ := hS
  let inc : f.ker →* S := {
    toFun := fun x => ⟨x.val,(le_sup_right : f.ker≤J⊔f.ker) x.property⟩
    map_one' := rfl
    map_mul' := by intros; rfl }
  let F : (f.ker ⧸ J.subgroupOf f.ker) → (S ⧸ J.subgroupOf S) :=
    Quotient.map inc (by
      intro a b hab
      apply (QuotientGroup.leftRel_apply (s := J.subgroupOf S)).mpr
      exact (QuotientGroup.leftRel_apply (s := J.subgroupOf f.ker)).mp hab)
  have hF : Surjective F := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x.val∈(f.ker : Set G)*(J : Set G) := by
      rw [←Subgroup.normal_mul, sup_comm]
      exact x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    refine ⟨QuotientGroup.mk ⟨a,ha⟩,?_⟩
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply (s := J.subgroupOf S)).mpr
    change a⁻¹*x.val∈J
    rw [←he,inv_mul_cancel_left]
    exact hb
  let _ : Finite (S ⧸ J.subgroupOf S) := Finite.of_surjective F hF
  apply Subgroup.finiteIndex_iff_finite_quotient.mpr
  exact Finite.of_equiv _ (Subgroup.quotientEquivProdOfLE (le_sup_left : J≤S)).symm

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteIndexAction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
variable {V E Λ Q : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

lemma finite_orbit_quotient_of_representatives (S : Set V) (hS : S.Finite)
    (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) :
    Finite (MulAction.orbitRel.Quotient Λ V) := by
  let : Setoid V := MulAction.orbitRel Λ V
  let _ := hS.to_subtype
  apply Finite.of_surjective (fun s : S => Quotient.mk' s.val)
  intro q
  induction q using Quotient.inductionOn with
  | h v =>
    obtain ⟨s,hs,hvs⟩ := hcover v
    exact ⟨⟨s,hs⟩,Quotient.sound ((MulAction.orbitRel Λ V).symm (MulAction.orbitRel_apply.mpr hvs))⟩

lemma finite_representatives_of_orbit_quotient
    [Finite (MulAction.orbitRel.Quotient Λ V)] :
    ∃ S : Set V, S.Finite ∧ (∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) := by
  let : Setoid V := MulAction.orbitRel Λ V
  let S := Set.range (Quotient.out : MulAction.orbitRel.Quotient Λ V → V)
  refine ⟨S,Set.finite_range _,?_⟩
  intro v
  refine ⟨Quotient.out (Quotient.mk' v),⟨Quotient.mk' v,rfl⟩,?_⟩
  apply MulAction.orbitRel_apply.mp
  exact Quotient.exact' (Quotient.out_eq' (Quotient.mk' v)).symm

lemma finiteIndex_action_representatives (S : Set V) (hS : S.Finite)
    (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (L : Subgroup Λ) (hL : L.index≠0) :
    ∃ R : Set V, R.Finite ∧ (∀ v, ∃ r∈R, v∈MulAction.orbit L r) := by
  let _ := finite_orbit_quotient_of_representatives S hS hcover
  let _ := L.finite_quotient_of_finite_quotient_of_index_ne_zero (X := V) hL
  exact finite_representatives_of_orbit_quotient

lemma quotientSubgroupMap_surjective (ρ : Λ →* Q) (hρ : Surjective ρ)
    (N : Subgroup Q) : Surjective (quotientSubgroupMap ρ N) := by
  intro n
  obtain ⟨g,hg⟩ := hρ n.val
  exact ⟨⟨g,by change ρ g∈N; rw [hg]; exact n.property⟩,Subtype.ext hg⟩

lemma quotientSubgroupMap_kernel_orbits (ρ : Λ →* Q) (N : Subgroup Q)
    (hf : ∀ v : V, (MulAction.orbit ρ.ker v).Finite) :
    ∀ v : V, (MulAction.orbit (quotientSubgroupMap ρ N).ker v).Finite := by
  intro v
  apply (hf v).subset
  rintro w ⟨g,hg⟩
  exact ⟨⟨g.val.val,congrArg Subtype.val g.property⟩,hg⟩

lemma quotientSubgroupMap_stabilizer_images (ρ : Λ →* Q) (N : Subgroup Q)
    (hf : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set Q).Finite) :
    ∀ v : V, ((MulAction.stabilizer (N.comap ρ) v).map
      (quotientSubgroupMap ρ N) : Set N).Finite := by
  intro v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hf v)).subset
  rintro n ⟨g,hg,rfl⟩
  exact ⟨g.val,hg,rfl⟩

lemma subgroup_preservesEnds (ha : G.PreservesEnds (Λ := Λ)) (L : Subgroup Λ) :
    G.PreservesEnds (Λ := L) := fun g e => ha g.val e

lemma finiteIndex_quotient_transfer
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* Q) (hρ : Surjective ρ)
    (hf : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hs : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set Q).Finite)
    (N : Subgroup Q) (hN : N.index≠0) :
    G.PreservesEnds (Λ := N.comap ρ) ∧
      (∃ R : Set V, R.Finite ∧ ∀ v, ∃ r∈R, v∈MulAction.orbit (N.comap ρ) r) ∧
      Surjective (quotientSubgroupMap ρ N) ∧
      (∀ v : V, (MulAction.orbit (quotientSubgroupMap ρ N).ker v).Finite) ∧
      (∀ v : V, ((MulAction.stabilizer (N.comap ρ) v).map
        (quotientSubgroupMap ρ N) : Set N).Finite) := by
  refine ⟨G.subgroup_preservesEnds ha (N.comap ρ),?_,
    quotientSubgroupMap_surjective ρ hρ N,
    quotientSubgroupMap_kernel_orbits ρ N hf,
    quotientSubgroupMap_stabilizer_images ρ N hs⟩
  exact finiteIndex_action_representatives S hS hcover (N.comap ρ)
    (by rwa [Subgroup.index_comap_of_surjective _ hρ])

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteKernelDescent
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

namespace CriticalPercolation

universe u v

lemma hom_finite_preimage_of_finite_kernel {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hk : (f.ker : Set G).Finite) (S : Set H) (hS : S.Finite) :
    (f ⁻¹' S).Finite := by
  let _ := hk.to_subtype
  have hfib : ∀ a : H, (f ⁻¹' {a}).Finite := by
    intro a
    by_cases ha : (f ⁻¹' {a}).Nonempty
    · obtain ⟨x,hx⟩ := ha
      change f x=a at hx
      rw [←hx]
      let _ := Finite.of_equiv _ (f.fiberEquivKer x).symm
      exact Set.toFinite _
    · rw [Set.not_nonempty_iff_eq_empty.mp ha]
      exact Set.finite_empty
  apply (hS.biUnion (fun a _ => hfib a)).subset
  exact fun x hx => Set.mem_iUnion₂.mpr ⟨f x,hx,rfl⟩

lemma hom_finite_composite_kernel {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K)
    (hf : (f.ker : Set G).Finite) (hg : (g.ker : Set H).Finite) :
    ((g.comp f).ker : Set G).Finite :=
  hom_finite_preimage_of_finite_kernel f hf g.ker hg

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitQuotientTransfer
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
variable {V E Λ Q Y : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

lemma finite_kernel_orbits_from_one_vertex
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ)) (ρ : Λ →* Q) (o : V)
    (ho : (MulAction.orbit ρ.ker o).Finite) :
    ∀ v : V, (MulAction.orbit ρ.ker v).Finite := by
  intro v
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc o v)
  have hfin := ho.biUnion (fun w _ => G.vertexBall_finite hl w n)
  apply hfin.subset
  rintro w ⟨g,rfl⟩
  refine Set.mem_iUnion₂.mpr ⟨g.val • o,⟨g,rfl⟩,?_⟩
  exact (Aut.vertexBall_mem G (G.smulAut ha g.val) o v n).mpr hn

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitalPower
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

lemma powerOn_finite_neighbors (hl : G.LocallyFinite) (O : Set V) (L : ℕ) (u : O) :
    ((G.powerOn O L).neighborSet u).Finite := by
  apply (Set.Finite.preimage Subtype.val_injective.injOn (G.vertexBall_finite hl u.val L)).subset
  exact fun _ h => h.2

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_GraphAutomorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

lemma continuous_variable_eval : Continuous (fun p : (X → X) × X => p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr fun x => continuous_apply x

variable (Γ : SimpleGraph X)

attribute [local instance] OAI.CriticalPercolation.GraphTopology.instTopologicalSpaceIso_solutions
omit [DiscreteTopology X] in
lemma coordinates_embedding : IsEmbedding (coordinates Γ) where
  eq_induced := rfl
  injective := by
    intro g h he
    apply RelIso.ext
    intro x
    exact congrFun (congrArg Prod.fst he) x

omit [DiscreteTopology X] in
lemma continuous_eval (x : X) : Continuous (fun g : Γ ≃g Γ => g x) :=
  (continuous_apply x).comp (continuous_fst.comp (coordinates_embedding Γ).continuous)

omit [DiscreteTopology X] in
lemma continuous_inv_eval (x : X) : Continuous (fun g : Γ ≃g Γ => g.symm x) :=
  (continuous_apply x).comp (continuous_snd.comp (coordinates_embedding Γ).continuous)

omit [TopologicalSpace X] [DiscreteTopology X] in
lemma coordinates_range : Set.range (coordinates Γ) =
    {p : (X → X) × (X → X) |
      (∀ x, p.2 (p.1 x)=x) ∧ (∀ x, p.1 (p.2 x)=x) ∧
      (∀ x y, Γ.Adj (p.1 x) (p.1 y) ↔ Γ.Adj x y)} := by
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g.symm_apply_apply,g.apply_symm_apply,fun _ _ => g.map_adj_iff⟩
  · rintro ⟨hleft,hright,hadj⟩
    refine ⟨{toEquiv := ⟨p.1,p.2,hleft,hright⟩,map_rel_iff' := fun {x y} => hadj x y},?_⟩
    exact Prod.eta p

lemma coordinates_closed : IsClosed (Set.range (coordinates Γ)) := by
  rw [coordinates_range]
  simp only [Set.ofPred_and,Set.ofPred_forall]
  refine (isClosed_iInter fun x => ?_).inter ((isClosed_iInter fun x => ?_).inter
    (isClosed_iInter fun x => isClosed_iInter fun y => ?_))
  · change IsClosed {p : (X → X) × (X → X) | p.2 (p.1 x)=x}
    exact isClosed_eq ((continuous_variable_eval (X := X)).comp (continuous_snd.prodMk
      ((continuous_apply x).comp continuous_fst))) continuous_const
  · change IsClosed {p : (X → X) × (X → X) | p.1 (p.2 x)=x}
    exact isClosed_eq ((continuous_variable_eval (X := X)).comp (continuous_fst.prodMk
      ((continuous_apply x).comp continuous_snd))) continuous_const
  · change IsClosed {p : (X → X) × (X → X) | Γ.Adj (p.1 x) (p.1 y) ↔ Γ.Adj x y}
    exact (isClosed_discrete {p : X × X | Γ.Adj p.1 p.2 ↔ Γ.Adj x y}).preimage
      (show Continuous (fun p : (X → X) × (X → X) => (p.1 x,p.1 y)) from
        ((continuous_apply x).comp continuous_fst).prodMk
          ((continuous_apply y).comp continuous_fst))

lemma coordinates_closedEmbedding : IsClosedEmbedding (coordinates Γ) :=
  ⟨coordinates_embedding Γ,coordinates_closed Γ⟩

instance aut_t2 : T2Space (Γ ≃g Γ) := (coordinates_embedding Γ).t2Space

instance aut_topologicalGroup : IsTopologicalGroup (Γ ≃g Γ) where
  continuous_mul := by
    apply (coordinates_embedding Γ).continuous_iff.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro x
      exact continuous_variable_eval.comp
        (((continuous_fst.comp (coordinates_embedding Γ).continuous).comp continuous_fst).prodMk
          ((continuous_eval Γ x).comp continuous_snd))
    · apply continuous_pi
      intro x
      exact continuous_variable_eval.comp
        (((continuous_snd.comp (coordinates_embedding Γ).continuous).comp continuous_snd).prodMk
          ((continuous_inv_eval Γ x).comp continuous_fst))
  continuous_inv := by
    apply (coordinates_embedding Γ).continuous_iff.mpr
    exact (continuous_snd.comp (coordinates_embedding Γ).continuous).prodMk
      (continuous_fst.comp (coordinates_embedding Γ).continuous)

lemma compact_coordinate_bounds (F : X → Set X) (hF : ∀ x, (F x).Finite) :
    IsCompact {g : Γ ≃g Γ | (∀ x, g x∈F x) ∧ (∀ x, g.symm x∈F x)} := by
  have hK : IsCompact {f : X → X | ∀ x, f x∈F x} :=
    isCompact_pi_infinite fun x => (hF x).isCompact
  exact (coordinates_closedEmbedding Γ).isCompact_preimage (hK.prod hK)

lemma isClosed_eval_mem (x : X) (S : Set X) :
    IsClosed {g : Γ ≃g Γ | g x∈S} :=
  (isClosed_discrete S).preimage (continuous_eval Γ x)

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.mem_around
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma reachBall_self (o : X) (r : ℕ) : o∈reachBall Γ o r :=
  ⟨SimpleGraph.Walk.nil,Nat.zero_le _⟩

lemma reachBall_symm {o x : X} {r : ℕ} (h : x∈reachBall Γ o r) :
    o∈reachBall Γ x r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.reverse,by simpa using hp⟩

lemma inverse_displacement {o : X} {r : ℕ} (g : Γ ≃g Γ)
    (h : g o∈reachBall Γ o r) : g.symm o∈reachBall Γ o r := by
  have hh := reachBall_symm Γ (iso_reachBall Γ g.symm h)
  simpa using hh

variable [TopologicalSpace X] [DiscreteTopology X]

attribute [local instance] OAI.CriticalPercolation.GraphTopology.instTopologicalSpaceIso_solutions_1
lemma compact_displacement (hc : Γ.Connected)
    (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (r : ℕ) :
    IsCompact {g : Γ ≃g Γ | g o∈reachBall Γ o r} := by
  have hp : ∀ x, ∃ p : Γ.Walk o x, True := fun x => by
    obtain ⟨p⟩ := hc o x
    exact ⟨p,trivial⟩
  choose p _ using hp
  let F : X → Set X := fun x => reachBall Γ o (r+(p x).length)
  have hfb : ∀ (g : Γ ≃g Γ), g o∈reachBall Γ o r → ∀ x, g x∈F x := by
    intro g hg x
    exact reachBall_add Γ hg (iso_reachBall Γ g ⟨p x,le_rfl⟩)
  apply (compact_coordinate_bounds Γ F (fun x => reachBall_finite Γ hl o _)).of_isClosed_subset
    (isClosed_eval_mem Γ o _)
  intro g hg
  exact ⟨hfb g hg,hfb g.symm (inverse_displacement Γ g hg)⟩

lemma compact_stabilizer (hc : Γ.Connected)
    (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) :
    IsCompact {g : Γ ≃g Γ | g o=o} := by
  apply (compact_displacement Γ hc hl o 0).of_isClosed_subset
    (isClosed_eq (continuous_eval Γ o) continuous_const)
  intro g hg
  change g o∈reachBall Γ o 0
  rw [hg]
  exact reachBall_self Γ o 0

instance aut_totallyDisconnected : TotallyDisconnectedSpace (Γ ≃g Γ) :=
  (coordinates_embedding Γ).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

lemma compact_finite_vertex_images (K : Set (Γ ≃g Γ)) (hK : IsCompact K) (o : X) :
    ((fun g : Γ ≃g Γ => g o) '' K).Finite :=
  isCompact_iff_finite.mp (hK.image (continuous_eval Γ o))

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularLevelGeometry
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

attribute [local instance] OAI.CriticalPercolation.BondGraph.instMulActionAut_1
lemma aut_preservesEnds : G.PreservesEnds (Λ := G.Aut) := fun φ => φ.preserves

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CyclicSubgroupIndex
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

namespace CriticalPercolation

theorem cyclic_infinite_subgroup_finiteIndex {G : Type*} [Group G]
    (e : G ≃* Multiplicative ℤ) (J : Subgroup G) [Infinite J] : J.FiniteIndex := by
  let a : Additive G ≃+ ℤ := e.toAdditive.trans (AddEquiv.additiveMultiplicative ℤ)
  let K := J.toAddSubgroup.map a.toAddMonoidHom
  obtain ⟨j,hj⟩ := exists_ne (1 : J)
  let z := a (Additive.ofMul j.val)
  have hz : z≠0 := by
    intro h
    have he : Additive.ofMul j.val=0 := a.injective (h.trans a.map_zero.symm)
    apply hj
    exact Subtype.ext he
  have hmem : z∈K := ⟨Additive.ofMul j.val,j.property,rfl⟩
  have hZ : (AddSubgroup.zmultiples z).FiniteIndex := by
    constructor
    rw [Int.index_zmultiples]
    exact Int.natAbs_ne_zero.mpr hz
  let _ := hZ
  have hK : K.FiniteIndex := AddSubgroup.finiteIndex_of_le (AddSubgroup.zmultiples_le.mpr hmem)
  constructor
  have hn := hK.index_ne_zero
  have he : K.index=J.index := by
    exact (AddSubgroup.index_map_equiv J.toAddSubgroup a).trans J.index_toAddSubgroup
  rwa [he] at hn

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_FiniteCyclicConstruction
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

lemma FiniteCyclicConstruction.of_finite_kernel {G Q : Type u} [Group G] [Group Q]
    {n : ℕ} (hQ : FiniteCyclicConstruction Q n) (f : G →* Q)
    (hf : Surjective f) [Finite f.ker] : FiniteCyclicConstruction G n := by
  simpa using FiniteCyclicConstruction.extension f hf (.finite f.ker) hQ

lemma FiniteCyclicConstruction.of_equiv {G Q : Type u} [Group G] [Group Q]
    {n : ℕ} (hQ : FiniteCyclicConstruction Q n) (e : G ≃* Q) :
    FiniteCyclicConstruction G n := by
  have he : e.toMonoidHom.ker=⊥ := e.toMonoidHom.ker_eq_bot e.injective
  let _ : Finite e.toMonoidHom.ker := he.symm ▸ (inferInstance : Finite (⊥ : Subgroup G))
  exact hQ.of_finite_kernel e.toMonoidHom e.surjective

private lemma free_finite_cyclic_construction_rank (n : ℕ) :
    ∀ (A : Type u) [AddCommGroup A] [Module.Free ℤ A] [Module.Finite ℤ A],
      Module.finrank ℤ A=n → ∃ k≤n, FiniteCyclicConstruction (Multiplicative A) k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ _ hrank
    let b : Module.Basis (Fin n) ℤ A := hrank ▸ Module.finBasis ℤ A
    let e := b.equivFun
    cases n with
    | zero =>
      let _ : Subsingleton A := ⟨fun x y => e.injective (funext fun i => Fin.elim0 i)⟩
      exact ⟨0,le_rfl,.finite _⟩
    | succ n =>
      let f : A →+ ULift.{u} ℤ := {
        toFun := fun a => ⟨e a 0⟩
        map_zero' := by apply ULift.ext; simp
        map_add' := by intros; apply ULift.ext; simp }
      have hf : Surjective f := by
        intro z
        exact ⟨e.symm (fun _ => z.down),by apply ULift.ext; simp [f]⟩
      let K := f.ker.toIntSubmodule
      have hzero (a : K) : e a.val 0=0 := congrArg ULift.down a.property
      let d : K →ₗ[ℤ] (Fin n → ℤ) := {
        toFun := fun a i => e a.val i.succ
        map_add' := by intros; ext i; simp
        map_smul' := by intros; ext i; simp }
      have hd : Injective d := by
        intro a a' haa
        apply Subtype.ext
        apply e.injective
        funext i
        exact Fin.cases ((hzero a).trans (hzero a').symm) (fun j => congrFun haa j) i
      have hr : Module.finrank ℤ K≤n := by
        simpa using d.finrank_le_finrank_of_injective hd
      obtain ⟨k,hk,hC⟩ := ih (Module.finrank ℤ K) (by omega) K rfl
      let ek : f.toMultiplicative.ker ≃* Multiplicative K := {
        toFun := fun a => Multiplicative.ofAdd ⟨a.val.toAdd,a.property⟩
        invFun := fun a => ⟨Multiplicative.ofAdd a.toAdd.val,a.toAdd.property⟩
        left_inv := by intro a; rfl
        right_inv := by intro a; rfl
        map_mul' := by intros; rfl }
      refine ⟨k+1,by omega,?_⟩
      exact FiniteCyclicConstruction.extension f.toMultiplicative (fun z => hf z.toAdd)
        (hC.of_equiv ek) (.cyclic _ AddEquiv.ulift.toMultiplicative)

theorem free_finite_cyclic_construction (A : Type u) [AddCommGroup A]
    [Module.Free ℤ A] [Module.Finite ℤ A] :
    ∃ n, FiniteCyclicConstruction (Multiplicative A) n := by
  obtain ⟨n,_,hn⟩ := free_finite_cyclic_construction_rank (Module.finrank ℤ A) A rfl
  exact ⟨n,hn⟩

theorem abelian_finite_cyclic_construction (A : Type u) [CommGroup A] [Group.FG A] :
    ∃ n, FiniteCyclicConstruction A n := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive A)
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let φ₀ := (AddMonoidHom.fst (Fin n →₀ ℤ) T).comp f.toAddMonoidHom
  let φ : Additive A →+ ULift.{u} (Fin n →₀ ℤ) := AddEquiv.ulift.symm.toAddMonoidHom.comp φ₀
  have hs : Surjective φ := by
    intro z
    refine ⟨f.symm (z.down,0),?_⟩
    change ULift.up (φ₀ (f.symm (z.down,0)))=z
    apply ULift.ext
    change φ₀ (f.symm (z.down,0))=z.down
    simp [φ₀]
  have hk : (φ.toMultiplicativeRight.ker : Set A).Finite := by
    apply ((Set.finite_singleton (0 : Fin n →₀ ℤ)).prod
      (Set.toFinite (Set.univ : Set T))).preimage f.injective.injOn |>.subset
    intro x hx
    exact ⟨congrArg (fun z : Multiplicative (ULift (Fin n →₀ ℤ)) => z.toAdd.down) hx,
      Set.mem_univ _⟩
  let _ := hk.to_subtype
  obtain ⟨k,hk⟩ := free_finite_cyclic_construction (ULift.{u} (Fin n →₀ ℤ))
  exact ⟨k,hk.of_finite_kernel φ.toMultiplicativeRight (fun z => hs z.toAdd)⟩

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_FiniteCyclicInheritance
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe groupUniverse

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem FiniteCyclicConstruction.subgroup {G : Type groupUniverse} [Group G] {n : ℕ}
    (hG : FiniteCyclicConstruction G n) :
    ∀ J : Subgroup G, ∃ m≤n, FiniteCyclicConstruction J m ∧ (m=n → J.FiniteIndex) := by
  induction hG with
  | @finite G _ _ =>
    intro J
    exact ⟨0,le_rfl,.finite _,fun _ => inferInstance⟩
  | @cyclic G _ e =>
    intro J
    cases finite_or_infinite J with
    | inl h =>
      let _ := h
      exact ⟨0,by omega,.finite _,by omega⟩
    | inr h =>
      let _ := h
      let _ : IsCyclic G := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      exact ⟨1,le_rfl,.cyclic _ (intCyclicMulEquiv.symm),
        fun _ => cyclic_infinite_subgroup_finiteIndex e J⟩
  | @extension G Q _ _ f hf n m hker hquot ihker ihquot =>
    intro J
    obtain ⟨k,hk,hK,hki⟩ := ihker (J.subgroupOf f.ker)
    obtain ⟨l,hl,hL,hli⟩ := ihquot (J.map f)
    let g : J →* J.map f := {
      toFun := fun j => ⟨f j.val,⟨j.val,j.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact f.map_one
      map_mul' := by intros; apply Subtype.ext; exact f.map_mul _ _ }
    have hg : Surjective g := by
      rintro ⟨q,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    let e : g.ker ≃* J.subgroupOf f.ker := {
      toFun := fun a => ⟨⟨a.val.val,congrArg Subtype.val a.property⟩,a.val.property⟩
      invFun := fun a => ⟨⟨a.val.val,a.property⟩,Subtype.ext a.val.property⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl
      map_mul' := by intros; rfl }
    refine ⟨k+l,by omega,FiniteCyclicConstruction.extension g hg (hK.of_equiv e) hL,?_⟩
    intro he
    let _ := hki (by omega)
    let _ := hli (by omega)
    exact subgroup_finiteIndex_of_image_and_kernel f hf J

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_AbelianAlternatives
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

theorem additive_abelian_alternatives (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    Finite A ∨
      (∃ φ : A →+ ℤ, Surjective φ ∧ (φ.ker : Set A).Finite) ∨
      (∃ φ : A →+ (ℤ×ℤ), Surjective φ) := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  cases n with
  | zero =>
    exact Or.inl (Finite.of_equiv _ f.symm.toEquiv)
  | succ n =>
    cases n with
    | zero =>
      let φ := (Finsupp.applyAddHom (0 : Fin 1)).comp
        ((AddMonoidHom.fst (Fin 1 →₀ ℤ) T).comp f.toAddMonoidHom)
      have hs : Surjective φ := by
        intro z
        refine ⟨f.symm (Finsupp.single 0 z,0),?_⟩
        simp [φ]
      have hk : (φ.ker : Set A).Finite := by
        apply (Set.finite_singleton (0 : Fin 1 →₀ ℤ)).prod (Set.toFinite (Set.univ : Set T)) |>.preimage f.injective.injOn |>.subset
        intro x hx
        change (f x).1∈({0} : Set (Fin 1 →₀ ℤ)) ∧ (f x).2∈(Set.univ : Set T)
        refine ⟨?_,Set.mem_univ _⟩
        apply Finsupp.ext
        intro i
        have hi : i=(0 : Fin 1) := Fin.ext (by omega)
        subst i
        exact hx
      exact Or.inr (Or.inl ⟨φ,hs,hk⟩)
    | succ n =>
      let ev : (Fin (n+2) →₀ ℤ) →+ (ℤ×ℤ) :=
        (Finsupp.applyAddHom ⟨0,by omega⟩).prod (Finsupp.applyAddHom ⟨1,by omega⟩)
      let φ := ev.comp ((AddMonoidHom.fst (Fin (n+2) →₀ ℤ) T).comp f.toAddMonoidHom)
      refine Or.inr (Or.inr ⟨φ,?_⟩)
      intro z
      refine ⟨f.symm (Finsupp.single ⟨0,by omega⟩ z.1 +
        Finsupp.single ⟨1,by omega⟩ z.2,0),?_⟩
      simp [φ,ev]

theorem abelian_alternatives (A : Type*) [CommGroup A] [Group.FG A] :
    Finite A ∨
      (∃ φ : A →* Multiplicative ℤ, Surjective φ ∧ (φ.ker : Set A).Finite) ∨
      (∃ φ : A →* Multiplicative (ℤ×ℤ), Surjective φ) := by
  rcases additive_abelian_alternatives (Additive A) with h | ⟨φ,hs,hk⟩ | ⟨φ,hs⟩
  · let _ := h
    exact Or.inl (Finite.of_equiv _ Additive.toMul)
  · refine Or.inr (Or.inl ⟨φ.toMultiplicativeRight,?_,?_⟩)
    · exact fun z => hs z.toAdd
    · exact hk
  · refine Or.inr (Or.inr ⟨φ.toMultiplicativeRight,?_⟩)
    exact fun z => hs z.toAdd

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CentralCommutatorQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G Q : Type*} [Group G] [Group Q]

lemma finite_generating_lifts [Group.FG Q] {H : Type*} [Group H]
    (f : H →* Q) (hf : Surjective f) :
    ∃ S : Set H, S.Finite ∧ (Subgroup.closure S).map f=⊤ := by
  obtain ⟨T,hT,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG Q)
  choose s hs using hf
  refine ⟨s '' T,hfin.image s,?_⟩
  rw [MonoidHom.map_closure,Set.image_image]
  have he : (fun x => f (s x))=id := funext hs
  rw [he,Set.image_id,hT]

theorem central_commutator_fg_of_quotient [Group.FG G] [Group.FG Q]
    (H : Subgroup G) (f : H →* Q) (hf : Surjective f)
    (hker : f.ker.map H.subtype≤Subgroup.center G)
    (hcentral : ⁅(⊤ : Subgroup G),H⁆≤Subgroup.center G) :
    ⁅(⊤ : Subgroup G),H⁆.FG := by
  obtain ⟨S,hS,himage⟩ := finite_generating_lifts f hf
  let L := Subgroup.closure S
  let M := L.map H.subtype
  have hM : M.FG := by
    apply (Subgroup.fg_iff M).mpr
    refine ⟨H.subtype '' S,?_,hS.image H.subtype⟩
    exact (MonoidHom.map_closure H.subtype S).symm
  have hMH : M≤H := by
    rintro x ⟨y,_,rfl⟩
    exact y.property
  suffices he : ⁅(⊤ : Subgroup G),H⁆=⁅(⊤ : Subgroup G),M⁆ by
    rw [he]
    exact central_commutator_fg ⊤ M (Group.fg_def.mp inferInstance) hM
      ((Subgroup.commutator_mono le_rfl hMH).trans hcentral)
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro g _ h hh
    have him : f ⟨h,hh⟩∈L.map f := by rw [himage]; trivial
    obtain ⟨l,hl,he⟩ := him
    let z : H := l⁻¹*⟨h,hh⟩
    have hzker : z∈f.ker := by
      change f (l⁻¹*⟨h,hh⟩)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hz : (z:G)∈Subgroup.center G := hker ⟨z,hzker,rfl⟩
    have hgz : ⁅g,(z:G)⁆=1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz g)
    have hdecomp : h=(l:G)*(z:G) := by simp [z]
    rw [hdecomp,commutatorElement_mul_right_eq_mul_conj,hgz]
    simpa using (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
      (H₂ := M) (by trivial) (show (l:G)∈M from ⟨l,hl,rfl⟩) : ⁅g,(l:G)⁆∈⁅⊤,M⁆)
  · exact Subgroup.commutator_mono le_rfl hMH

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CentralCommutatorFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G Q : Type*} [Group G] [Group Q]

theorem central_commutator_finite_of_quotient [Group.FG G] [Finite Q]
    (H : Subgroup G) (f : H →* Q) (hf : Surjective f)
    (hker : f.ker.map H.subtype≤Subgroup.center G)
    (hc : ⁅(⊤ : Subgroup G),H⁆≤Subgroup.center G) :
    ((⁅(⊤ : Subgroup G),H⁆ : Subgroup G) : Set G).Finite := by
  let C := ⁅(⊤ : Subgroup G),H⁆
  let _ : CommGroup C := {
    (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a.val) }
  let _ : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr
    (central_commutator_fg_of_quotient H f hf hker hc)
  have hpair (a : G) (b : H) : IsOfFinOrder (⁅a,(b:G)⁆) := by
    let t : H →* G := {
      toFun := fun b => ⁅a,(b:G)⁆
      map_one' := by simp
      map_mul' := by
        intro b d
        change ⁅a,(b:G)*(d:G)⁆=⁅a,(b:G)⁆*⁅a,(d:G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hd := hc (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
          (by trivial) d.property : ⁅a,(d:G)⁆∈C)
        calc
          ⁅a,(b:G)⁆*(b:G)*⁅a,(d:G)⁆*(b:G)⁻¹ =
            ⁅a,(b:G)⁆*((b:G)*⁅a,(d:G)⁆)*(b:G)⁻¹ := by group
          _ = ⁅a,(b:G)⁆*(⁅a,(d:G)⁆*(b:G))*(b:G)⁻¹ := by
            rw [Subgroup.mem_center_iff.mp hd (b:G)]
          _ = _ := by group }
    obtain ⟨m,hm,he⟩ := (isOfFinOrder_of_finite (f b)).exists_pow_eq_one
    have hb : b^m∈f.ker := by change f (b^m)=1; rwa [map_pow]
    have hz : ((b^m:H):G)∈Subgroup.center G := hker ⟨b^m,hb,rfl⟩
    have heq : t (b^m)=1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz a)
    rw [map_pow] at heq
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,heq⟩
  have ht : C≤(CommGroup.torsion C).map C.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b hb
    let c : C := ⟨⁅a,b⁆,Subgroup.commutator_mem_commutator (by trivial) hb⟩
    refine ⟨c,?_,rfl⟩
    change IsOfFinOrder c
    obtain ⟨m,hm,he⟩ := (hpair a ⟨b,hb⟩).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,Subtype.ext he⟩
  let _ : Finite C := CommGroup.finite_of_fg_isMulTorsion C (fun c => by
    obtain ⟨d,hd,he⟩ := ht c.property
    have hcd : d=c := Subtype.ext he
    change IsOfFinOrder d at hd
    exact hcd ▸ hd)
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_LowerCentralFG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable (G : Type*) [Group G]

lemma lowerFactor_central (n : ℕ) : lowerFactor G n≤
    Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (n+1)) := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  let f := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
  have hf : (⊤ : Subgroup G).map f=⊤ :=
    Subgroup.map_top_of_surjective f QuotientGroup.mk_surjective
  change ⁅((⊤ : Subgroup G).lowerCentralSeries n).map f,⊤⁆=⊥
  rw [←hf,←Subgroup.map_commutator,←Subgroup.lowerCentralSeries_succ]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']

theorem lowerFactor_fg [Group.FG G] (n : ℕ) : Group.FG (lowerFactor G n) := by
  induction n with
  | zero =>
    unfold lowerFactor
    rw [Subgroup.lowerCentralSeries_zero,←MonoidHom.range_eq_map]
    infer_instance
  | succ n ih =>
    let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
    let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
    let π := QuotientGroup.mk' M
    let σ := QuotientGroup.mk' N
    have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
    let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
      rw [QuotientGroup.ker_mk']; exact hMN)
    have hq (g : G) : q (π g)=σ g := rfl
    let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
    let f : H →* lowerFactor G n := {
      toFun := fun h => ⟨q h.val,by
        obtain ⟨g,hg,he⟩ := h.property
        exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hf : Surjective f := by
      rintro ⟨x,g,hg,rfl⟩
      exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
    have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
      rintro x ⟨h,hh,rfl⟩
      obtain ⟨g,hg,he⟩ := h.property
      apply lowerFactor_central G (n+1)
      refine ⟨g,?_,he⟩
      have heq : σ g=1 := by
        rw [←hq,he]
        exact congrArg Subtype.val hh
      change g∈N
      rw [←QuotientGroup.ker_mk' N]
      exact heq
    have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
      have hπ : (⊤ : Subgroup G).map π=⊤ :=
        Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
      change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
        ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
      rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
        ←Subgroup.lowerCentralSeries_succ]
    let _ := ih
    have hfg := central_commutator_fg_of_quotient H f hf hker
      (hcomm ▸ lowerFactor_central G (n+1))
    apply (Group.fg_iff_subgroup_fg _).mpr
    rwa [hcomm] at hfg

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_LowerCentralFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable (G : Type*) [Group G]

theorem lowerFactor_finite [Group.FG G] [Finite (lowerFactor G 0)] (n : ℕ) :
    Finite (lowerFactor G n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
    let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
    let π := QuotientGroup.mk' M
    let σ := QuotientGroup.mk' N
    have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
    let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
      rw [QuotientGroup.ker_mk']; exact hMN)
    have hq (g : G) : q (π g)=σ g := rfl
    let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
    let f : H →* lowerFactor G n := {
      toFun := fun h => ⟨q h.val,by
        obtain ⟨g,hg,he⟩ := h.property
        exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hf : Surjective f := by
      rintro ⟨x,g,hg,rfl⟩
      exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
    have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
      rintro x ⟨h,hh,rfl⟩
      obtain ⟨g,hg,he⟩ := h.property
      apply lowerFactor_central G (n+1)
      refine ⟨g,?_,he⟩
      have heq : σ g=1 := by
        rw [←hq,he]
        exact congrArg Subtype.val hh
      change g∈N
      rw [←QuotientGroup.ker_mk' N]
      exact heq
    have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
      have hπ : (⊤ : Subgroup G).map π=⊤ :=
        Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
      change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
        ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
      rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
        ←Subgroup.lowerCentralSeries_succ]
    let _ := ih
    have hfin := central_commutator_finite_of_quotient H f hf hker
      (hcomm ▸ lowerFactor_central G (n+1))
    rw [hcomm] at hfin
    exact hfin.to_subtype

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_NilpotentFinite
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

namespace CriticalPercolation

theorem nilpotent_finite_of_finite_factors (G : Type*) [Group G]
    [Group.IsNilpotent G] (hfin : ∀ n, Finite (lowerFactor G n)) : Finite G := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Finite (L (n+1))) : Finite (L n) := by
    let F := lowerFactor G n
    let _ : Finite F := hfin n
    let q := QuotientGroup.mk' (L (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hemem (x : L n) : x∈f.ker ↔ x.val∈L (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃ f.ker := {
      toFun := fun x => ⟨⟨x.val,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property⟩,
        (hemem _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val,(hemem _).mp x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    let _ : Finite f.ker := Finite.of_equiv _ e
    exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance,inferInstance⟩
  have base : Finite (L c) := by
    change Finite ((⊤ : Subgroup G).lowerCentralSeries c)
    rw [hc]
    infer_instance
  have hall : ∀ k, Finite (L (c-k)) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k < c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · simpa [Nat.sub_eq_zero_of_le (by omega : c≤k),
          Nat.sub_eq_zero_of_le (by omega : c≤k+1)] using ih
  have h : Finite (⊤ : Subgroup G) := by simpa [L] using hall c
  let _ := h
  exact Finite.of_equiv _ (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv

theorem nilpotent_finite_of_finite_abelianization (G : Type*) [Group G]
    [Group.FG G] [Group.IsNilpotent G] [Finite (Abelianization G)] : Finite G := by
  have he : (⊤ : Subgroup G).lowerCentralSeries 1=commutator G :=
    Subgroup.top_lowerCentralSeries_one
  let _ : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1) := by
    rw [he]
    exact (inferInstance : Finite (Abelianization G))
  let _ : Finite (lowerFactor G 0) := inferInstance
  exact nilpotent_finite_of_finite_factors G (lowerFactor_finite G)

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CyclicModTorsion
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

namespace CriticalPercolation

lemma cyclic_mod_torsion_of_finite_kernel {G A : Type*} [Group G] [Group A]
    (ρ : G →* A) (hρ : Surjective ρ) (φ : A →* Multiplicative ℤ)
    (hφ : Surjective φ) (hk : (φ.ker : Set A).Finite) :
    ∃ g : G, ∀ a : G, ∃ k : ℤ, IsOfFinOrder (ρ (a*g^(-k))) := by
  obtain ⟨g,hg⟩ := hφ.comp hρ (Multiplicative.ofAdd (1 : ℤ))
  change φ (ρ g)=Multiplicative.ofAdd (1 : ℤ) at hg
  let _ := hk.to_subtype
  refine ⟨g,fun a => ?_⟩
  let k := (φ (ρ a)).toAdd
  refine ⟨k,?_⟩
  have he : ρ (a*g^(-k))∈φ.ker := by
    change φ (ρ (a*g^(-k)))=1
    rw [map_mul,map_zpow,map_mul,map_zpow,hg]
    change (φ (ρ a)).toAdd+(-k) • (1 : ℤ)=0
    simp [k]
  obtain ⟨m,hm,heq⟩ :=
    (isOfFinOrder_of_finite (⟨ρ (a*g^(-k)),he⟩ : φ.ker)).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,congrArg Subtype.val heq⟩

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_LowerCentralTailFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation

lemma lowerFactor_finite_step (G : Type*) [Group G] [Group.FG G] (n : ℕ)
    [Finite (lowerFactor G n)] : Finite (lowerFactor G (n+1)) := by
  let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
  let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
  let π := QuotientGroup.mk' M
  let σ := QuotientGroup.mk' N
  have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
    rw [QuotientGroup.ker_mk']; exact hMN)
  have hq (g : G) : q (π g)=σ g := rfl
  let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
  let f : H →* lowerFactor G n := {
    toFun := fun h => ⟨q h.val,by
      obtain ⟨g,hg,he⟩ := h.property
      exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
    map_one' := by apply Subtype.ext; exact q.map_one
    map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
  have hf : Surjective f := by
    rintro ⟨x,g,hg,rfl⟩
    exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
  have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
    rintro x ⟨h,hh,rfl⟩
    obtain ⟨g,hg,he⟩ := h.property
    apply lowerFactor_central G (n+1)
    refine ⟨g,?_,he⟩
    have heq : σ g=1 := by
      rw [←hq,he]
      exact congrArg Subtype.val hh
    change g∈N
    rw [←QuotientGroup.ker_mk' N]
    exact heq
  have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
    have hπ : (⊤ : Subgroup G).map π=⊤ :=
      Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
    change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
      ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
    rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
      ←Subgroup.lowerCentralSeries_succ]
  have hfin := central_commutator_finite_of_quotient H f hf hker
    (hcomm ▸ lowerFactor_central G (n+1))
  rw [hcomm] at hfin
  exact hfin.to_subtype

theorem nilpotent_lower_finite_of_tail (G : Type*) [Group G]
    [Group.IsNilpotent G] (start : ℕ)
    (hfin : ∀ n, start≤n → Finite (lowerFactor G n)) :
    Finite ((⊤ : Subgroup G).lowerCentralSeries start) := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hsn : start≤n) (hn : Finite (L (n+1))) : Finite (L n) := by
    let F := lowerFactor G n
    let _ : Finite F := hfin n hsn
    let q := QuotientGroup.mk' (L (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hemem (x : L n) : x∈f.ker ↔ x.val∈L (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃ f.ker := {
      toFun := fun x => ⟨⟨x.val,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property⟩,
        (hemem _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val,(hemem _).mp x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    let _ : Finite f.ker := Finite.of_equiv _ e
    exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance,inferInstance⟩

  have hall : ∀ k n, c≤n+k → start≤n → Finite (L n) := by
    intro k
    induction k with
    | zero =>
      intro n hcn _
      have hn : L n=⊥ := by
        apply le_antisymm ?_ bot_le
        calc
          L n ≤ L c := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
          _ = ⊥ := hc
      rw [hn]
      infer_instance
    | succ k ih =>
      intro n hcn hsn
      exact step n hsn (ih (n+1) (by omega) (by omega))
  exact hall c start (by omega) le_rfl

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_NilpotentRankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation

theorem first_commutator_factor_finite (G : Type*) [Group G] [Group.FG G]
    (φ : Abelianization G →* Multiplicative ℤ) (hφ : Surjective φ)
    (hk : (φ.ker : Set (Abelianization G)).Finite) : Finite (lowerFactor G 1) := by
  let M := (⊤ : Subgroup G).lowerCentralSeries 2
  let p := QuotientGroup.mk' M
  have hM : M ≤ commutator G := by
    rw [←Subgroup.top_lowerCentralSeries_one]
    exact (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  let ρ : (G ⧸ M) →* Abelianization G := QuotientGroup.lift M (Abelianization.of : G →* Abelianization G) (by
    rw [Abelianization.ker_of]; exact hM)
  have hρ : Surjective ρ := by
    intro a
    obtain ⟨g,rfl⟩ := (QuotientGroup.mk_surjective (s := commutator G)) a
    exact ⟨p g,rfl⟩
  have hcomm : commutator (G ⧸ M)=lowerFactor G 1 := by
    have hp : (⊤ : Subgroup G).map p=⊤ :=
      Subgroup.map_top_of_surjective p QuotientGroup.mk_surjective
    change ⁅⊤,⊤⁆=((⊤ : Subgroup G).lowerCentralSeries 1).map p
    rw [Subgroup.top_lowerCentralSeries_one,commutator,Subgroup.map_commutator,hp]
  have hc : commutator (G ⧸ M)≤Subgroup.center (G ⧸ M) := by
    rw [hcomm]
    exact lowerFactor_central G 1
  have hker : ρ.ker≤Subgroup.center (G ⧸ M) := by
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g∈commutator G := by
      change Abelianization.of g=1 at hx
      exact (QuotientGroup.eq_one_iff g).mp hx
    apply lowerFactor_central G 1
    exact ⟨g,hg,rfl⟩
  obtain ⟨g,hg⟩ := cyclic_mod_torsion_of_finite_kernel ρ hρ φ hφ hk
  have hf := class_two_commutator_finite_of_cyclic_mod_torsion hc ρ hker g hg
  rw [hcomm] at hf
  exact hf.to_subtype

theorem nilpotent_commutator_finite_of_cyclic_abelianization (G : Type*)
    [Group G] [Group.FG G] [Group.IsNilpotent G]
    (φ : Abelianization G →* Multiplicative ℤ) (hφ : Surjective φ)
    (hk : (φ.ker : Set (Abelianization G)).Finite) :
    (commutator G : Set G).Finite := by
  have hfirst := first_commutator_factor_finite G φ hφ hk
  have htail : ∀ n, 1≤n → Finite (lowerFactor G n) := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => exact hfirst
    | succ n hn ih =>
      let _ := ih
      exact lowerFactor_finite_step G n
  have hf := nilpotent_lower_finite_of_tail G 1 htail
  rw [Subgroup.top_lowerCentralSeries_one] at hf
  let _ := hf
  exact Set.toFinite _

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_NilpotentAlternatives
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

namespace CriticalPercolation

theorem nilpotent_alternatives (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] :
    Finite G ∨
      (∃ φ : G →* Multiplicative ℤ, Surjective φ ∧ (φ.ker : Set G).Finite) ∨
      (∃ φ : G →* Multiplicative (ℤ×ℤ), Surjective φ) := by
  let q : G →* Abelianization G := Abelianization.of
  have hq : Surjective q := QuotientGroup.mk_surjective
  let _ : Group.FG (Abelianization G) := Group.fg_of_surjective hq
  rcases abelian_alternatives (Abelianization G) with h | ⟨φ,hφ,hk⟩ | ⟨φ,hφ⟩
  · let _ := h
    exact Or.inl (nilpotent_finite_of_finite_abelianization G)
  · refine Or.inr (Or.inl ⟨φ.comp q,hφ.comp hq,?_⟩)
    apply hom_finite_composite_kernel q φ ?_ hk
    have hf := nilpotent_commutator_finite_of_cyclic_abelianization G φ hφ hk
    simpa only [q,Abelianization.ker_of] using hf
  · exact Or.inr (Or.inr ⟨φ.comp q,hφ.comp hq⟩)

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_FGExtensions
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

namespace CriticalPercolation

theorem fg_of_kernel_quotient {G Q : Type*} [Group G] [Group Q] [Group.FG Q]
    (f : G →* Q) (hf : Surjective f) [Group.FG f.ker] : Group.FG G := by
  obtain ⟨S,hS,himage⟩ := finite_generating_lifts f hf
  obtain ⟨T,hT,hfinT⟩ := Group.fg_iff.mp (inferInstance : Group.FG f.ker)
  let U := S ∪ f.ker.subtype '' T
  let L := Subgroup.closure U
  have hSle : Subgroup.closure S≤L := Subgroup.closure_mono Set.subset_union_left
  have hker : f.ker≤L := by
    have he : (Subgroup.closure T).map f.ker.subtype=f.ker := by
      rw [hT,←MonoidHom.range_eq_map,Subgroup.subtype_range]
    rw [←he,MonoidHom.map_closure]
    exact Subgroup.closure_mono Set.subset_union_right
  have htop : L=⊤ := by
    apply top_unique
    intro g _
    have hg : f g∈(Subgroup.closure S).map f := by rw [himage]; trivial
    obtain ⟨a,ha,he⟩ := hg
    have hz : a⁻¹*g∈f.ker := by
      change f (a⁻¹*g)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    simpa using L.mul_mem (hSle ha) (hker hz)
  exact Group.fg_iff.mpr ⟨U,htop,hS.union (hfinT.image _)⟩

theorem abelian_subgroup_fg {A : Type*} [CommGroup A] [Group.FG A]
    (H : Subgroup A) : Group.FG H := by
  let K := H.toAddSubgroup.toIntSubmodule
  let _ : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let _ : AddGroup.FG K := Module.Finite.iff_addGroup_fg.mp inferInstance
  let e : Multiplicative K ≃* H := {
    toFun := fun a => ⟨a.toAdd.val.toMul,a.toAdd.property⟩
    invFun := fun h => Multiplicative.ofAdd ⟨Additive.ofMul h.val,h.property⟩
    left_inv := by intro a; rfl
    right_inv := by intro h; rfl
    map_mul' := by intros; rfl }
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_NilpotentCyclicConstruction
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

namespace CriticalPercolation

theorem nilpotent_subgroup_finite_cyclic_construction (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : ∃ k, FiniteCyclicConstruction J k := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : ∃ k, FiniteCyclicConstruction (L (n+1)) k) :
      ∃ k, FiniteCyclicConstruction (L n) k := by
    let F := lowerFactor G n
    let _ : CommGroup F := {
      (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp (lowerFactor_central G n b.property) a.val) }
    let _ : Group.FG F := lowerFactor_fg G n
    let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property.2,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    let _ : Group.FG f.range := abelian_subgroup_fg f.range
    obtain ⟨k,hk⟩ := hn
    have hemem (x : L n) : x∈f.ker ↔ x.val∈(⊤ : Subgroup G).lowerCentralSeries (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val,⟨x.property.1,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property.2⟩⟩,
        (hemem _).mpr x.property.2⟩
      invFun := fun x => ⟨x.val.val,⟨x.val.property.1,(hemem _).mp x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intros; rfl }
    have hker := hk.of_equiv e.symm
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    have hker' : FiniteCyclicConstruction f.rangeRestrict.ker k := he.symm ▸ hker
    obtain ⟨m,hm⟩ := abelian_finite_cyclic_construction f.range
    exact ⟨k+m,FiniteCyclicConstruction.extension f.rangeRestrict
      f.rangeRestrict_surjective hker' hm⟩
  have base : ∃ k, FiniteCyclicConstruction (L c) k := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    exact ⟨0,.finite _⟩
  have hall : ∀ k, ∃ m, FiniteCyclicConstruction (L (c-k)) m := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k < c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · have he : c-k=c-(k+1) := by omega
        exact he ▸ ih
  have h := hall c
  have he : L (c-c)=J := by simp [L]
  exact he ▸ h

theorem nilpotent_finite_cyclic_construction (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] : ∃ k, FiniteCyclicConstruction G k := by
  obtain ⟨k,hk⟩ := nilpotent_subgroup_finite_cyclic_construction G ⊤
  exact ⟨k,hk.of_equiv Subgroup.topEquiv.symm⟩

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_NilpotentSubgroupFG
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

namespace CriticalPercolation

theorem nilpotent_subgroup_fg (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : Group.FG J := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Group.FG (L (n+1))) : Group.FG (L n) := by
    let F := lowerFactor G n
    let _ : CommGroup F := {
      (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp (lowerFactor_central G n b.property) a.val) }
    let _ : Group.FG F := lowerFactor_fg G n
    let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property.2,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    let _ : Group.FG f.range := abelian_subgroup_fg f.range
    let _ : Group.FG (L (n+1)) := hn
    have hemem (x : L n) : x∈f.ker ↔ x.val∈(⊤ : Subgroup G).lowerCentralSeries (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val,⟨x.property.1,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property.2⟩⟩,
        (hemem _).mpr x.property.2⟩
      invFun := fun x => ⟨x.val.val,⟨x.val.property.1,(hemem _).mp x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intros; rfl }
    let _ : Group.FG f.ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    let _ : Group.FG f.rangeRestrict.ker := he.symm ▸ (inferInstance : Group.FG f.ker)
    exact fg_of_kernel_quotient f.rangeRestrict f.rangeRestrict_surjective
  have base : Group.FG (L c) := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    infer_instance
  have hall : ∀ k, Group.FG (L (c-k)) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k < c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · simpa [Nat.sub_eq_zero_of_le (by omega : c≤k),
          Nat.sub_eq_zero_of_le (by omega : c≤k+1)] using ih
  have h := hall c
  simpa [L] using h

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_NilpotentDescent
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

namespace CriticalPercolation

private theorem nilpotent_descent_by_construction (n : ℕ) :
    ∀ (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G],
      FiniteCyclicConstruction G n → AlgebraicDescent G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ hG
    rcases nilpotent_alternatives G with h | ⟨φ,hφ,hk⟩ | ⟨φ,hφ⟩
    · let _ := h
      exact .finite G
    · exact .cyclic G φ hφ hk
    · apply AlgebraicDescent.plane G φ hφ
      intro J hJ
      obtain ⟨m,hm,hC,hi⟩ := hG.subgroup J
      have hlt : m<n := by
        by_contra! hge
        have he : m=n := by omega
        let _ := hi he
        have hker : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hJ
        apply hker.index_ne_zero
        rw [Subgroup.index_ker,φ.range_eq_top_of_surjective hφ]
        rw [Nat.card_congr (Subgroup.topEquiv :
          (⊤ : Subgroup (Multiplicative (ℤ×ℤ))) ≃* Multiplicative (ℤ×ℤ)).toEquiv]
        exact Nat.card_eq_zero_of_infinite
      let _ : Group.FG J := nilpotent_subgroup_fg G J
      exact ih m hlt J hC

theorem nilpotent_descent (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G] :
    AlgebraicDescent G := by
  obtain ⟨n,hn⟩ := nilpotent_finite_cyclic_construction G
  exact nilpotent_descent_by_construction n G hn

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_StructuredNilpotent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

theorem critical_null_of_nilpotent_quotient {V E Λ N : Type*}
    [Group Λ] [MulAction Λ V] [MulAction Λ E] [Group N] [Group.FG N] [Group.IsNilpotent N]
    (G : BondGraph V E) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* N) (hρ : Surjective ρ)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 :=
  critical_null_of_algebraic_descent (nilpotent_descent N) G hc hl hg ha S hS hcover
    ρ hρ hker hstab hpc

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_StructuredVirtuallyNilpotent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

theorem critical_null_of_virtually_nilpotent_quotient {V E Λ Q : Type*}
    [Group Λ] [MulAction Λ V] [MulAction Λ E] [Group Q] [Group.FG Q]
    (G : BondGraph V E) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* Q) (hρ : Surjective ρ)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set Q).Finite)
    (N : Subgroup Q) [Group.IsNilpotent N] (hN : N.index≠0)
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 := by
  let _ : N.FiniteIndex := ⟨hN⟩
  obtain ⟨ha',⟨R,hR,hRcover⟩,hsur,hfinite,hst⟩ :=
    G.finiteIndex_quotient_transfer ha S hS hcover ρ hρ hker hstab N hN
  exact critical_null_of_nilpotent_quotient G hc hl hg ha' R hR hRcover
    (quotientSubgroupMap ρ N) hsur hfinite hst hpc

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FullOrbitalStructureTransfer
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal

namespace CriticalPercolation
namespace StructurePullback
variable {A B : Type*} [Group A] [Group B]

lemma nilpotent_comap_of_injective (f : A →* B) (hf : Injective f)
    (N : Subgroup B) [Group.IsNilpotent N] : Group.IsNilpotent (N.comap f) := by
  let F : N.comap f →* N :=
    {toFun := fun g => ⟨f g.val,g.property⟩
     map_one' := Subtype.ext (map_one f)
     map_mul' := fun g h => Subtype.ext (map_mul f g.val h.val)}
  have hF : Injective F := by
    intro g h he
    apply Subtype.ext
    exact hf (congrArg Subtype.val he)
  apply Subgroup.isNilpotent_of_ker_le_center F
  rw [(MonoidHom.ker_eq_bot_iff F).mpr hF]
  exact bot_le

lemma finiteIndex_comap (f : A →* B) (N : Subgroup B) (hN : N.index≠0) :
    (N.comap f).index≠0 := by
  rw [Subgroup.index_comap]
  intro h
  exact hN (Subgroup.index_eq_zero_of_relIndex_eq_zero h)

end StructurePullback
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_stabilizer_images_from_one_vertex
    {A B : Type*} [Group A] [Group B] [MulAction A V] [MulAction A E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := A)) (ρ : A →* B) (o : V)
    (ho : ((MulAction.stabilizer A o).map ρ : Set B).Finite) :
    ∀ v : V, ((MulAction.stabilizer A v).map ρ : Set B).Finite := by
  let a : V → A := fun w => if h : ∃ g : A, g • o=w then h.choose else 1
  have ha' : ∀ {w : V}, (∃ g : A, g • o=w) → a w • o=w := by
    intro w hw
    simp only [a, dite_eq_left hw]
    exact hw.choose_spec
  intro v
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc v o)
  apply ((G.vertexBall_finite hl v n).biUnion
    (fun w _ => ho.image (fun b => ρ (a w)*b))).subset
  rintro b ⟨g,hg,rfl⟩
  have hgo : g • o∈G.vertexBall v n := by
    have hh := (Aut.vertexBall_mem G (G.smulAut ha g) v o n).mpr hn
    change g • o∈G.vertexBall (g • v) n at hh
    exact hg ▸ hh
  refine Set.mem_iUnion₂.mpr ⟨g • o,hgo,ρ ((a (g • o))⁻¹*g),?_,?_⟩
  · refine ⟨(a (g • o))⁻¹*g,?_,rfl⟩
    change ((a (g • o))⁻¹*g) • o=o
    rw [mul_smul]
    calc
      (a (g • o))⁻¹ • (g • o) = (a (g • o))⁻¹ • (a (g • o) • o) :=
        congrArg (fun x => (a (g • o))⁻¹ • x) (ha' ⟨g,rfl⟩).symm
      _ = o := inv_smul_smul _ _
  · simp only [map_mul, map_inv, mul_inv_cancel_left]

lemma fullOrbital_finite_kernel_orbits (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal]
    (hH : ((fun g : G.orbitPower o L ≃g G.orbitPower o L =>
      g (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o)) '' (H : Set _)).Finite) :
    ∀ v : V, (MulAction.orbit (G.fullOrbitalQuotientHom o L Λ H).rangeRestrict.ker v).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.finite_kernel_orbits_from_one_vertex hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) _ o
  apply (hH.image Subtype.val).subset
  rintro v ⟨g,rfl⟩
  have he := congrArg Subtype.val g.property
  have hg : G.orbitPowerHom o L g.val.val∈H := (QuotientGroup.eq_one_iff _).mp he
  exact ⟨⟨g • o,⟨g.val.val,rfl⟩⟩,⟨G.orbitPowerHom o L g.val.val,hg,rfl⟩,rfl⟩

lemma fullOrbital_finite_stabilizer_images (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal]
    (hstab : (((QuotientGroup.mk' H) : (G.orbitPower o L ≃g G.orbitPower o L) → _)
      '' {g | g (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o)=
        ⟨o,MulAction.mem_orbit_self o⟩}).Finite) :
    ∀ v : V, ((MulAction.stabilizer Λ v).map
      (G.fullOrbitalQuotientHom o L Λ H).rangeRestrict :
      Set (G.fullOrbitalQuotientHom o L Λ H).range).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.finite_stabilizer_images_from_one_vertex hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) _ o
  apply (hstab.preimage Subtype.val_injective.injOn).subset
  rintro g ⟨a,ha,rfl⟩
  refine ⟨G.orbitPowerHom o L a.val,?_,rfl⟩
  apply Subtype.ext
  exact ha

theorem critical_null_of_compact_open_orbital_quotient_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth)
    (o : V) (L : ℕ) (hconn : (G.orbitPower o L).Connected)
    (Λ : Subgroup G.Aut) [Group.FG Λ]
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal]
    (N : Subgroup ((G.orbitPower o L ≃g G.orbitPower o L) ⧸ H)) [Group.IsNilpotent N]
    (hN : N.index≠0)
    (hH : let _ : TopologicalSpace (MulAction.orbit G.Aut o) := ⊥
      let _ : TopologicalSpace (G.orbitPower o L ≃g G.orbitPower o L) :=
        GraphTopology.autTopology (G.orbitPower o L)
      IsCompact (H : Set (G.orbitPower o L ≃g G.orbitPower o L)) ∧
      IsOpen (H : Set (G.orbitPower o L ≃g G.orbitPower o L)))
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 := by
  let _ : TopologicalSpace (MulAction.orbit G.Aut o) := ⊥
  let _ : DiscreteTopology (MulAction.orbit G.Aut o) := ⟨rfl⟩
  let _ : TopologicalSpace (G.orbitPower o L ≃g G.orbitPower o L) :=
    GraphTopology.autTopology (G.orbitPower o L)
  let _ : DiscreteTopology ((G.orbitPower o L ≃g G.orbitPower o L) ⧸ H) :=
    QuotientGroup.discreteTopology hH.2
  let o' : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
  have hstab : (((QuotientGroup.mk' H) : (G.orbitPower o L ≃g G.orbitPower o L) → _)
      '' {g | g o'=o'}).Finite := by
    apply isCompact_iff_finite.mp
    apply (GraphTopology.compact_stabilizer (G.orbitPower o L) hconn
      (G.powerOn_finite_neighbors hl _ _) o').image
    exact QuotientGroup.continuous_mk
  let f := G.fullOrbitalQuotientHom o L Λ H
  let M := N.comap f.range.subtype
  let _ : Group.IsNilpotent M := StructurePullback.nilpotent_comap_of_injective
    f.range.subtype Subtype.val_injective N
  let _ : MulAction G.Aut E := G.autEdgeAction
  exact G.critical_null_of_virtually_nilpotent_quotient hc hl hg
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) S hS hcover
    f.rangeRestrict (MonoidHom.rangeRestrict_surjective f)
    (G.fullOrbital_finite_kernel_orbits hc hl o L Λ H
      (GraphTopology.compact_finite_vertex_images _ _ hH.1 o'))
    (G.fullOrbital_finite_stabilizer_images hc hl o L Λ H hstab) M
    (StructurePullback.finiteIndex_comap f.range.subtype N hN) hpc

end BondGraph
end CriticalPercolation
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_oai.{u_1, u_2}
