-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:47:10.41807+00:00
-- url     : https://prove2.me/submissions/4928293a-f357-4e1b-9ee7-3e474ae2ffad

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_critical_null_of_action_coordinates_bs
import Theorems.Thm_OAI_CriticalPercolation_nilpotent_descent_bs

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

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CutEdges
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_HeightCuts
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

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BlockIndependence
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ClosedCutProbability
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
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma bitMeasure_false_ne_zero (p : unitInterval) (hp : (p:ℝ)<1) :
    bitMeasure p {False} ≠ 0 := by
  have hh := bitMeasure_real_singleton p False
  simp only [bitWeight,if_false] at hh
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_OneDimensionalCritical
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EquivariantCoordinates
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteKernelOrbits
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_InducedCritical
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ComponentCritical
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_InducedAutomorphism
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_RestrictedAction
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_ComponentAction
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_RestrictedQuotient
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_StructuredCoordinates
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_IntegerBoxes
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DescentCritical
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
    apply G.critical_null_of_action_coordinates_bs hc hl ha S hS hcover hg hpc
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteIndexAction
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitQuotientTransfer
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitalPower
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphAutomorphismTopology
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularLevelGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_StructuredNilpotent
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

theorem critical_null_of_nilpotent_quotient {V E Λ N : Type*}
    [Group Λ] [MulAction Λ V] [MulAction Λ E] [Group N] [Group.FG N] [Group.IsNilpotent N]
    (G : BondGraph V E) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* N) (hρ : Surjective ρ)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 :=
  critical_null_of_algebraic_descent (nilpotent_descent_bs N) G hc hl hg ha S hS hcover
    ρ hρ hker hstab hpc

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_StructuredVirtuallyNilpotent
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FullOrbitalStructureTransfer
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

theorem critical_null_of_compact_open_orbital_quotient_bs_oai
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

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs_oai.{u_1, u_2}
