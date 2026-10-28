-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:27:44.155759+00:00
-- url     : https://prove2.me/submissions/434b0c61-6f04-47fc-b0c9-12d13113723d

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

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

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BlockExposure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E B : Type*}

lemma measurable_block_of_dependsOn {A : Type*} [MeasurableSpace A]
    {f : Set E → A} (hf : Measurable f) (S : Set E) (hdep : DependsOn f S) :
    @Measurable (Set E) A (blockSigma S) inferInstance f := by
  have hm := hf.comp (measurable_forceOn_block Sᶜ (∅ : Set E))
  rw [compl_compl] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  apply hdep
  intro e he
  simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he),
    Set.mem_empty_iff_false]
  rfl

lemma lintegral_indicator_fresh (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hdep : DependsOn (fun ω => ω ∈ A) S)
    (g : Set E → ℝ≥0∞) (hg : Measurable g) (hgdep : DependsOn g Sᶜ) :
    (∫⁻ ω, A.indicator g ω ∂law q) = law q A * ∫⁻ ω, g ω ∂law q := by
  have hAb : MeasurableSet[blockSigma S] A := by
    have hm := hA.preimage (measurable_forceOn_block Sᶜ (∅ : Set E))
    rw [compl_compl] at hm
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    apply Iff.of_eq
    apply hdep
    intro e he
    simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he)]
    rfl
  have hgb := measurable_block_of_dependsOn hg Sᶜ hgdep
  have hi := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (blockSigma_le S) (blockSigma_le Sᶜ)
    (independent_blocks q S)
    ((measurable_const : @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance
      (fun _ => 1)).indicator hAb) hgb
  have heq : (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω * g ω) = A.indicator g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  have hone := lintegral_indicator_const (μ := law q) hA (1 : ℝ≥0∞)
  simp only [one_mul] at hone
  rw [heq, hone] at hi
  exact hi

end CriticalPercolation.BernoulliProduct

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ClusterExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exactCluster_dependsOn (x : V) (S : Set V) :
    DependsOn (fun ω : Set E => G.cluster ω x = S) (G.incidentEdges S) := by
  intro ω η hω
  apply propext
  have hforward (ω η : Set E) (hωη : ∀ e ∈ G.incidentEdges S, e ∈ ω ↔ e ∈ η)
      (hS : G.cluster ω x = S) : G.cluster η x = S := by
    have hr : ClusterDeletion.roots (G.openGraph ω) {x} = S := by
      simpa only [ClusterDeletion.roots_singleton, ClusterDeletion.component, cluster] using hS
    have hr' := G.roots_eq_of_incident hr hωη
    simpa only [ClusterDeletion.roots_singleton, ClusterDeletion.component, cluster] using hr'
  exact ⟨hforward ω η (fun e he => (hω e he).to_iff),
    hforward η ω (fun e he => (hω e he).symm.to_iff)⟩

lemma measurableSet_exactCluster [Countable V] [Countable E] (x : V) (S : Set V) :
    MeasurableSet {ω | G.cluster ω x = S} := by
  have heq : {ω | G.cluster ω x = S} =
      ⋂ y : V, {ω | (G.openGraph ω).Reachable x y ↔ y ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Set.ext_iff
  rw [heq]
  exact MeasurableSet.iInter fun y => ((G.measurable_reachable x y).iff measurable_const).setOf

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Basic
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}



section Deterministic
variable (G : BondGraph V E) (ω : Set E)

theorem conn_univ_of_connected (h : Connected G) (x y : V) : Conn G Set.univ x y := by
  apply Relation.ReflTransGen.mono (r := Adj G) ?_ x y (h x y)
  rintro a b ⟨e, he⟩
  exact ⟨e, Set.mem_univ _, he⟩

end Deterministic

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Restriction

theorem measurable_set_restrict (s : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply e.val).comp MeasurableEquiv.setOfPred.symm.measurable))

 
theorem law_map_restrict (p : unitInterval) (s : Set E) :
    (law p : Measure (Set E)).map (fun ω => (Subtype.val ⁻¹' ω : Set s)) = law p := by
  have hm := measurable_set_restrict s
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ∘
      (fun f : E → Prop => {e | f e}) =
      (fun f : s → Prop => {e | f e}) ∘ s.domRestrict := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop),
    Measure.infinitePi_map_restrict', setBernoulli_eq_map]
  simp only [Set.mem_univ]

end Restriction

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Paths
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section DegreeBound
attribute [local instance] Classical.propDecidable

 theorem finite_steps (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Set.Finite {ey : E × V | G ey.1 = s(x,ey.2)} := by
  apply ((hloc x).prod (finite_neighbors hloc x)).subset
  rintro ⟨e,y⟩ he
  change G e = s(x,y) at he
  exact ⟨by change x ∈ G e; rw [he]; simp, e, he⟩

end DegreeBound

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Goodness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section GoodnessLaw
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incident_filter_card_le_degree (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (x : V) : (Q.filter fun e => x ∈ G e).card ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  have hex (e : {e // e ∈ Q.filter fun e => x ∈ G e}) : ∃ y, G e.val = s(x,y) :=
    Sym2.mem_iff_exists.mp (Finset.mem_filter.mp e.property).2
  let f : {e // e ∈ Q.filter fun e => x ∈ G e} → Step G x :=
    fun e => ⟨(e.val,(hex e).choose),(hex e).choose_spec⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : Step G x => z.val.1) hab)
  simpa only [degree,Nat.card_eq_fintype_card,Fintype.card_coe] using Fintype.card_le_of_injective f hf



end GoodnessLaw

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_LargeContacts
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large Contacts for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformLargeContacts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incident_ncard_le_degree (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    {e | x ∈ G e}.ncard ≤ degree G x := by
  have he : ((hloc x).toFinset.filter fun e => x ∈ G e) = (hloc x).toFinset := by
    ext e
    simp only [Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,and_self]
  simpa only [he,←Set.ncard_eq_toFinset_card] using incident_filter_card_le_degree G hloc (hloc x).toFinset x

end UniformLargeContacts
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Derivatives
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSizeBounds
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incidentSupport_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (W : Finset V) :
    (incidentSupport G hloc W).card ≤ W.card*d := by
  apply Finset.card_biUnion_le_card_mul
  intro x _
  rw [←Set.ncard_eq_toFinset_card _ (hloc x)]
  exact (incident_ncard_le_degree G hloc x).trans (hd x)

end CorridorSizeBounds
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PhaseInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_openGraph (G : BondGraph V E) (ω : Set E) :
    (criticalModel G).openGraph ω = openSimpleGraph G ω := by
  ext x y
  simp only [CriticalPercolation.BondGraph.openGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_image, openSimpleGraph, criticalModel]
  tauto

theorem criticalModel_cluster (G : BondGraph V E) (ω : Set E) (x : V) :
    (criticalModel G).cluster ω x = cluster G ω x := by
  ext y
  simp only [CriticalPercolation.BondGraph.cluster, criticalModel_openGraph,
    Set.mem_ofPred_eq, cluster]
  exact (conn_iff_reachable G ω x y).symm

theorem criticalModel_connected [Nonempty V] (G : BondGraph V E) (hconn : Connected G) :
    (criticalModel G).fullGraph.Connected := by
  rw [CriticalPercolation.BondGraph.fullGraph, criticalModel_openGraph]
  exact ⟨fun x y => (conn_iff_reachable G Set.univ x y).mp (conn_univ_of_connected G hconn x y)⟩

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RelativeModular
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace Subgroup
open scoped _root_.Subgroup
variable {Γ : Type*} [Group Γ]

lemma relativeMass_self (A : Subgroup Γ) : relativeMass A A = 1 := by
  simp [relativeMass]

end Subgroup
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_GraphModular
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

lemma modularRatio_self (x : V) : G.modularRatio x x = 1 := by
  rw [modularRatio_eq_relativeMass,Subgroup.relativeMass_self]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularClusterMass
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

@[simp] lemma stabilizerWeight_self (o : V) : G.stabilizerWeight o o = 1 := by
  simp [stabilizerWeight,modularRatio_self]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedMassTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma suborbitCard_mul_modularRatio (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (x y : V) :
    (G.suborbitCard y x : ℝ) * G.modularRatio x y = G.suborbitCard x y := by
  unfold modularRatio
  have hn : (G.suborbitCard y x : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x))
  field_simp

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma tilted_massTransport (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (hrow : ∀ x, (Function.support (F x)).Finite)
    (hcol : ∀ y, (Function.support (fun x => F x y)).Finite) :
    (∑ x ∈ R.roots, ∑' y, F x y) =
      ∑ y ∈ R.roots, ∑' x, F x y * G.modularRatio x y := by
  let F' := fun x y => F y x * G.modularRatio y x
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := by
    simp only [F',hF,Aut.modularRatio]
  have hc' (x : V) : (Function.support (F' x)).Finite := by
    apply (hcol x).subset
    intro y hy
    exact fun hz => hy (by simp only [F',hz,zero_mul])
  have hs : Summable (weightedRow G R (fun _ => 1) F) :=
    summable_of_hasFiniteSupport (weightedRow_finite G R _ F hrow)
  have ht : Summable (weightedRow G R (fun _ => 1) F') :=
    summable_of_hasFiniteSupport (weightedRow_finite G R _ F' hc')
  have heq : (∑' p, weightedRow G R (fun _ => 1) F p) =
      ∑' p, weightedRow G R (fun _ => 1) F' p := by
    calc
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q},
          weightedRow G R (fun _ => 1) F p :=
        (hs.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq.symm
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          weightedRow G R (fun _ => 1) F' p := by
        apply tsum_congr
        intro q
        induction q using Quotient.inductionOn' with
        | h p =>
          change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2},
            weightedRow G R (fun _ => 1) F z) =
              ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1},
                weightedRow G R (fun _ => 1) F' z
          rw [fiber_sum G R hc hl _ (fun _ _ => rfl) F hF,
            fiber_sum G R hc hl _ (fun _ _ => rfl) F' hF']
          simp only [one_mul,F']
          rw [mul_left_comm,suborbitCard_mul_modularRatio G hc hl,mul_comm]
      _ = ∑' p, weightedRow G R (fun _ => 1) F' p := by
        exact (G.swapPairOrbit.tsum_eq (fun q =>
          ∑' p : (pairMap G R) ⁻¹' {q}, weightedRow G R (fun _ => 1) F' p)).trans
            (ht.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq
  rw [tsum_weightedRow G R _ F hrow,tsum_weightedRow G R _ F' hc'] at heq
  simpa only [one_mul,F'] using heq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularCharacter
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

lemma modularRatio_aut_translate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio o (φ.vertex x) =
      G.modularRatio o (φ.vertex o) * G.modularRatio o x := by
  rw [←G.modularRatio_cocycle hc hl o (φ.vertex o) (φ.vertex x),Aut.modularRatio]

lemma modularRatio_aut_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio x (φ.vertex x) = G.modularRatio o (φ.vertex o) := by
  have h1 := G.modularRatio_cocycle hc hl o x (φ.vertex x)
  rw [G.modularRatio_aut_translate hc hl o x φ] at h1
  exact (mul_left_cancel₀ (ne_of_gt (G.modularRatio_pos hc hl o x)))
    (h1.trans (mul_comm _ _))

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ModularSlabs
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma modularLogHeight_self (x : V) : G.modularLogHeight x x = 0 := by
  simp only [modularLogHeight,G.modularRatio_self,Real.log_one]

lemma modularLogHeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x v y : V) : G.modularLogHeight x y = G.modularLogHeight x v + G.modularLogHeight v y := by
  unfold modularLogHeight
  rw [← Real.log_mul (G.modularRatio_pos hc hl v x).ne' (G.modularRatio_pos hc hl y v).ne']
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

lemma Aut.modularLogHeight (φ : G.Aut) (x y : V) :
    G.modularLogHeight (φ.vertex x) (φ.vertex y) = G.modularLogHeight x y := by
  simp only [CriticalPercolation.BondGraph.modularLogHeight,Aut.modularRatio]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitHeightComparison
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma orbitAdjustedHeight_self (a : V → ℝ) (x : V) :
    G.orbitAdjustedHeight a x x = 0 := by simp [orbitAdjustedHeight]

lemma orbitAdjustedHeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (x v y : V) :
    G.orbitAdjustedHeight a x y = G.orbitAdjustedHeight a x v + G.orbitAdjustedHeight a v y := by
  simp only [orbitAdjustedHeight,G.modularLogHeight_change_base hc hl x v y]
  ring

lemma orbitAdjustedHeight_aut (a : V → ℝ) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x)
    (φ : G.Aut) (x y : V) :
    G.orbitAdjustedHeight a (φ.vertex x) (φ.vertex y) = G.orbitAdjustedHeight a x y := by
  simp only [orbitAdjustedHeight,Aut.modularLogHeight,ha]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ConsistentLayers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma adjustedLayerIndex_self (a : V → ℝ) (R u : ℝ) (x : V) :
    G.adjustedLayerIndex a R u x x=0 := by simp [adjustedLayerIndex]

lemma adjustedLayerIndex_height_bounds (a : V → ℝ) (R u : ℝ) (hR : 0 < R) (x y : V) :
    R*((G.adjustedLayerIndex a R u x y : ℝ)-1) < G.orbitAdjustedHeight a x y ∧
      G.orbitAdjustedHeight a x y < R*((G.adjustedLayerIndex a R u x y : ℝ)+1) := by
  have h₁ := Int.floor_le (G.orbitAdjustedHeight a x y/R+u)
  have h₂ := Int.lt_floor_add_one (G.orbitAdjustedHeight a x y/R+u)
  have h₃ := Int.floor_le u
  have h₄ := Int.lt_floor_add_one u
  have he : (G.adjustedLayerIndex a R u x y : ℝ) =
      (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ) := by
    simp only [adjustedLayerIndex,Int.cast_sub]
  rw [he]
  constructor
  · have hh : (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ)-1 <
        G.orbitAdjustedHeight a x y/R := by linarith
    have hm := (lt_div_iff₀ hR).mp hh
    nlinarith
  · have hh : G.orbitAdjustedHeight a x y/R <
        (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ)+1 := by linarith
    have hm := (div_lt_iff₀ hR).mp hh
    nlinarith

lemma adjustedLayerIndex_edge_jump (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R u : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight a v w| ≤ R)
    (x v w : V) (e : E) (hv : v ∈ G.ends e) (hw : w ∈ G.ends e) :
    G.adjustedLayerIndex a R u x v-1 ≤ G.adjustedLayerIndex a R u x w ∧
      G.adjustedLayerIndex a R u x w ≤ G.adjustedLayerIndex a R u x v+1 := by
  have hh := abs_le.mp (hjump e v w hv hw)
  have hcoc := G.orbitAdjustedHeight_change_base hc hl a x v w
  have hdiv : G.orbitAdjustedHeight a x v/R-1 ≤ G.orbitAdjustedHeight a x w/R ∧
      G.orbitAdjustedHeight a x w/R ≤ G.orbitAdjustedHeight a x v/R+1 := by
    constructor
    · apply (le_div_iff₀ hR).mpr
      have he : (G.orbitAdjustedHeight a x v/R-1)*R = G.orbitAdjustedHeight a x v-R := by
        field_simp
      rw [he]
      linarith
    · apply (div_le_iff₀ hR).mpr
      have he : (G.orbitAdjustedHeight a x v/R+1)*R = G.orbitAdjustedHeight a x v+R := by
        field_simp
      rw [he]
      linarith
  have hlo := Int.floor_mono (add_le_add hdiv.1 (le_refl u))
  have hhi := Int.floor_mono (add_le_add hdiv.2 (le_refl u))
  have helo : G.orbitAdjustedHeight a x v/R-1+u = G.orbitAdjustedHeight a x v/R+u-1 := by ring
  have hehi : G.orbitAdjustedHeight a x v/R+1+u = G.orbitAdjustedHeight a x v/R+u+1 := by ring
  rw [helo,Int.floor_sub_one] at hlo
  rw [hehi,Int.floor_add_one] at hhi
  unfold adjustedLayerIndex
  omega

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FreshSlabCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma conn_internalEdges_end_mem (ω : Set E) (D : Set V) {x y : V}
    (hx : x ∈ D) (hconn : Conn G (ω ∩ internalEdges G D) x y) : y ∈ D := by
  induction hconn with
  | refl => exact hx
  | @tail z y _ hy _ =>
    obtain ⟨e,he,heq⟩ := hy
    exact he.2 y (by rw [heq]; simp)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitNeighborChain
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma orbit_out_aut (x : V) : ∃ φ : G.Aut, φ.vertex (G.vertexOrbit x).out = x := by
  have he : (Quotient.mk'' (G.vertexOrbit x).out : G.VertexOrbit) = Quotient.mk'' x :=
    (G.vertexOrbit x).out_eq'
  exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp (Quotient.exact he))

lemma modularWalkDegree_pos [Nontrivial V] (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x : V) : 0 < G.modularWalkDegree x := by
  apply (Set.ncard_pos (G.finite_neighbors hl x)).mpr
  have h := hc.preconnected.not_isIsolated x
  unfold SimpleGraph.IsIsolated at h
  push Not at h
  exact h

lemma modularWalkDegree_aut (φ : G.Aut) (x : V) :
    G.modularWalkDegree (φ.vertex x) = G.modularWalkDegree x := by
  have he : φ.vertex '' G.fullGraph.neighborSet x = G.fullGraph.neighborSet (φ.vertex x) := by
    ext y
    obtain ⟨z,rfl⟩ := φ.vertex.surjective y
    simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,SimpleGraph.mem_neighborSet,
      Aut.fullGraph_adj]
  unfold modularWalkDegree
  rw [← he,Set.ncard_image_of_injective _ φ.vertex.injective]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitNormalization
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stationaryOrbitWeight_pos [Nontrivial V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) (x : V) :
    0 < G.stationaryOrbitWeight μ x :=
  div_pos (hμ _) (Nat.cast_pos.mpr (G.modularWalkDegree_pos hc hl x))

lemma stationaryOrbitWeight_aut (μ : G.VertexOrbit → ℝ) (φ : G.Aut) (x : V) :
    G.stationaryOrbitWeight μ (φ.vertex x) = G.stationaryOrbitWeight μ x := by
  simp only [stationaryOrbitWeight,G.vertexOrbit_aut,G.modularWalkDegree_aut]

lemma stationaryOrbitWeight_out (μ : G.VertexOrbit → ℝ) (x : V) :
    G.stationaryOrbitWeight μ x = G.stationaryOrbitWeight μ (G.vertexOrbit x).out := by
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  simpa only [hφ] using G.stationaryOrbitWeight_aut μ φ (G.vertexOrbit x).out

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma sum_roots_eq_orbitSum [Fintype G.VertexOrbit] (f : G.VertexOrbit → ℝ) :
    ∑ x ∈ R.roots, f (G.vertexOrbit x) = ∑ i, f i := by
  rw [← Finset.sum_coe_sort R.roots (fun x => f (G.vertexOrbit x))]
  exact (R.orbitEquiv G).sum_comp f

end OrbitRepresentatives

lemma orbitNeighborCount_eq_at_vertex (hl : G.LocallyFinite) (x : V) (i : G.VertexOrbit) :
    G.orbitNeighborCount hl (G.vertexOrbit x) i =
      (((G.finite_neighbors hl x).toFinset).filter fun y => G.vertexOrbit y = i).card := by
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  have himage :
      ((((G.finite_neighbors hl (G.vertexOrbit x).out).toFinset).filter
        fun y => G.vertexOrbit y = i).image φ.vertex) =
      (((G.finite_neighbors hl x).toFinset).filter fun y => G.vertexOrbit y = i) := by
    ext y
    constructor
    · rintro h
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hz,ho⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨(G.finite_neighbors hl x).mem_toFinset.mpr ?_,?_⟩
      · rw [← hφ]
        exact (Aut.fullGraph_adj G φ _ _).mpr ((G.finite_neighbors hl _).mem_toFinset.mp hz)
      · simpa only [G.vertexOrbit_aut] using ho
    · intro hy
      obtain ⟨hy,ho⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_image.mpr ⟨φ.vertex.symm y,Finset.mem_filter.mpr ⟨?_,?_⟩,
        Equiv.apply_symm_apply _ _⟩
      · apply (G.finite_neighbors hl _).mem_toFinset.mpr
        apply (Aut.fullGraph_adj G φ _ _).mp
        have hy' : G.fullGraph.Adj x y := (G.finite_neighbors hl x).mem_toFinset.mp hy
        simpa only [hφ,Equiv.apply_symm_apply] using hy'
      · have he : G.vertexOrbit (φ.vertex.symm y) = G.vertexOrbit y := by
          simpa only [Equiv.apply_symm_apply] using (G.vertexOrbit_aut φ (φ.vertex.symm y)).symm
        exact he.trans ho
  rw [← himage,Finset.card_image_of_injective _ φ.vertex.injective]
  rfl

lemma orbitNeighborTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) (i : G.VertexOrbit) (φ : G.Aut) (x y : V) :
    G.orbitNeighborTransport a i (φ.vertex x) (φ.vertex y) =
      G.orbitNeighborTransport a i x y := by
  simp only [orbitNeighborTransport,G.vertexOrbit_aut,Aut.fullGraph_adj,ha]

lemma orbitNeighborTransport_row_finite (hl : G.LocallyFinite) (a : V → ℝ)
    (i : G.VertexOrbit) (x : V) : (Function.support (G.orbitNeighborTransport a i x)).Finite := by
  apply (G.finite_neighbors hl x).subset
  intro y hy
  by_contra h
  exact hy (ite_eq_right (by simpa only [SimpleGraph.mem_neighborSet] using not_and_of_not_right _ h))

lemma orbitNeighborTransport_col_finite (hl : G.LocallyFinite) (a : V → ℝ)
    (i : G.VertexOrbit) (y : V) : (Function.support (fun x => G.orbitNeighborTransport a i x y)).Finite := by
  apply (G.finite_neighbors hl y).subset
  intro x hx
  by_contra h
  apply hx
  apply ite_eq_right
  exact not_and_of_not_right _ (fun hxy => h hxy.symm)

lemma orbitNeighborTransport_row (hl : G.LocallyFinite) (a : V → ℝ)
    (i : G.VertexOrbit) (x : V) :
    ∑' y, G.orbitNeighborTransport a i x y =
      a x * G.orbitNeighborCount hl (G.vertexOrbit x) i := by
  unfold orbitNeighborTransport
  rw [tsum_eq_sum (f := fun y => if G.vertexOrbit y = i ∧ G.fullGraph.Adj x y then a x else 0)
    (s := (G.finite_neighbors hl x).toFinset) (fun y hy => ite_eq_right (by
      intro h
      exact hy ((G.finite_neighbors hl x).mem_toFinset.mpr h.2)))]
  rw [G.orbitNeighborCount_eq_at_vertex hl x i]
  have he : (∑ y ∈ (G.finite_neighbors hl x).toFinset,
      if G.vertexOrbit y = i ∧ G.fullGraph.Adj x y then a x else 0) =
    ∑ y ∈ ((G.finite_neighbors hl x).toFinset).filter (fun y => G.vertexOrbit y = i), a x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    have hxy : G.fullGraph.Adj x y := (G.finite_neighbors hl x).mem_toFinset.mp hy
    simp only [hxy,and_true]
  rw [he,Finset.sum_const,nsmul_eq_mul,mul_comm]

lemma weightedNeighborIncoming_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) (φ : G.Aut) (y : V) :
    G.weightedNeighborIncoming a (φ.vertex y) = G.weightedNeighborIncoming a y := by
  unfold weightedNeighborIncoming
  rw [← φ.vertex.tsum_eq (fun x =>
    if G.fullGraph.Adj x (φ.vertex y) then a x * G.modularRatio x (φ.vertex y) else 0)]
  apply tsum_congr
  intro x
  simp only [Aut.fullGraph_adj,ha,Aut.modularRatio]

lemma orbitNeighborTransport_incoming (a : V → ℝ) (i : G.VertexOrbit) (y : V) :
    (∑' x, G.orbitNeighborTransport a i x y * G.modularRatio x y) =
      if G.vertexOrbit y = i then G.weightedNeighborIncoming a y else 0 := by
  by_cases hy : G.vertexOrbit y = i
  · simp only [orbitNeighborTransport,hy,true_and,if_true,weightedNeighborIncoming]
    apply tsum_congr
    intro x
    split_ifs <;> simp only [zero_mul]
  · simp only [orbitNeighborTransport,hy,false_and,if_false,zero_mul,tsum_zero]

theorem weightedNeighborIncoming_stationary [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ) (y : V) :
    G.weightedNeighborIncoming (G.stationaryOrbitWeight μ) y = μ (G.vertexOrbit y) := by
  let R := G.orbitRepresentatives hq
  let a := G.stationaryOrbitWeight μ
  have ha := G.stationaryOrbitWeight_aut μ
  have hout (i : G.VertexOrbit) :
      (∑ x ∈ R.roots, ∑' z, G.orbitNeighborTransport a i x z) = μ i := by
    calc
      _ = ∑ x ∈ R.roots, a x * G.orbitNeighborCount hl (G.vertexOrbit x) i := by
        apply Finset.sum_congr rfl
        intro x _
        exact G.orbitNeighborTransport_row hl a i x
      _ = ∑ j, (μ j / G.modularWalkDegree j.out) * G.orbitNeighborCount hl j i := by
        rw [← R.sum_roots_eq_orbitSum G]
        apply Finset.sum_congr rfl
        intro x _
        rw [show a x = a (G.vertexOrbit x).out from G.stationaryOrbitWeight_out μ x]
        simp only [a,stationaryOrbitWeight,vertexOrbit,Quotient.out_eq']
      _ = Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ i := by
        unfold Percolation.BenjaminiSchramm.orbitChainStep orbitWalkKernel
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = μ i := congrFun hstat i
  have hin (i : G.VertexOrbit) :
      (∑ z ∈ R.roots, ∑' x, G.orbitNeighborTransport a i x z * G.modularRatio x z) =
        G.weightedNeighborIncoming a i.out := by
    calc
      _ = ∑ z ∈ R.roots, if G.vertexOrbit z = i then
          G.weightedNeighborIncoming a (G.vertexOrbit z).out else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        rw [G.orbitNeighborTransport_incoming]
        obtain ⟨φ,hφ⟩ := G.orbit_out_aut z
        by_cases hz : G.vertexOrbit z = i
        · simp only [hz,if_true]
          have he := G.weightedNeighborIncoming_aut a ha φ (G.vertexOrbit z).out
          rw [hφ] at he
          simpa only [hz] using he
        · simp only [hz,if_false]
      _ = ∑ j : G.VertexOrbit, if j = i then G.weightedNeighborIncoming a j.out else 0 :=
        R.sum_roots_eq_orbitSum G (fun j => if j = i then G.weightedNeighborIncoming a j.out else 0)
      _ = _ := by simp
  have hi (i : G.VertexOrbit) : G.weightedNeighborIncoming a i.out = μ i := by
    rw [← hin i,← R.tilted_massTransport G hc hl _
      (G.orbitNeighborTransport_aut a ha i) (G.orbitNeighborTransport_row_finite hl a i)
      (G.orbitNeighborTransport_col_finite hl a i)]
    exact hout i
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut y
  calc
    _ = G.weightedNeighborIncoming a (G.vertexOrbit y).out := by
      simpa only [hφ] using G.weightedNeighborIncoming_aut a ha φ (G.vertexOrbit y).out
    _ = _ := hi (G.vertexOrbit y)

theorem stationaryOrbitWeight_neighbor_sum [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ) (x : V) :
    (∑ y ∈ (G.finite_neighbors hl x).toFinset,
      G.stationaryOrbitWeight μ y * G.modularRatio y x) =
        G.stationaryOrbitWeight μ x * G.modularWalkDegree x := by
  have he : G.weightedNeighborIncoming (G.stationaryOrbitWeight μ) x =
      ∑ y ∈ (G.finite_neighbors hl x).toFinset,
        G.stationaryOrbitWeight μ y * G.modularRatio y x := by
    unfold weightedNeighborIncoming
    rw [tsum_eq_sum (s := (G.finite_neighbors hl x).toFinset)
      (fun y hy => ite_eq_right (fun hxy => hy ((G.finite_neighbors hl x).mem_toFinset.mpr hxy.symm)))]
    apply Finset.sum_congr rfl
    intro y hy
    exact ite_eq_left ((G.finite_neighbors hl x).mem_toFinset.mp hy).symm
  rw [← he,G.weightedNeighborIncoming_stationary hc hl hq μ hstat]
  unfold stationaryOrbitWeight
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (G.modularWalkDegree_pos hc hl x).ne')]

theorem stationaryOrbitHeight_harmonic [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ) (x : V) :
    (∑ y ∈ (G.finite_neighbors hl x).toFinset,
      Real.exp (G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y)) =
        G.modularWalkDegree x := by
  have he (y : V) :
      Real.exp (G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y) =
        (G.stationaryOrbitWeight μ y * G.modularRatio y x) / G.stationaryOrbitWeight μ x := by
    rw [orbitAdjustedHeight,modularLogHeight,Real.exp_sub,Real.exp_add,
      Real.exp_log (G.modularRatio_pos hc hl y x),
      Real.exp_log (G.stationaryOrbitWeight_pos hc hl μ hμ y),
      Real.exp_log (G.stationaryOrbitWeight_pos hc hl μ hμ x)]
    ring
  simp_rw [he]
  rw [← Finset.sum_div,G.stationaryOrbitWeight_neighbor_sum hc hl hq μ hstat]
  exact mul_div_cancel_left₀ _ (G.stationaryOrbitWeight_pos hc hl μ hμ x).ne'

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HarmonicHeightAscent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma height_harmonic_flat_or_rise (hl : G.LocallyFinite) (f : V → ℝ)
    (hf : ∀ x, (∑ y ∈ (G.finite_neighbors hl x).toFinset, Real.exp (f y-f x)) =
      G.modularWalkDegree x) (x : V) :
    (∃ y, G.fullGraph.Adj x y ∧ f x < f y) ∨
      (∀ y, G.fullGraph.Adj x y → f y = f x) := by
  by_cases hu : ∃ y, G.fullGraph.Adj x y ∧ f x < f y
  · exact Or.inl hu
  right
  have hle (y : V) (hy : y ∈ (G.finite_neighbors hl x).toFinset) :
      Real.exp (f y-f x) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact sub_nonpos.mpr (le_of_not_gt (fun h => hu ⟨y,(G.finite_neighbors hl x).mem_toFinset.mp hy,h⟩))
  have hs : (∑ y ∈ (G.finite_neighbors hl x).toFinset, Real.exp (f y-f x)) =
      ∑ _y ∈ (G.finite_neighbors hl x).toFinset, (1 : ℝ) := by
    rw [hf,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp only [modularWalkDegree,Set.ncard_eq_toFinset_card _ (G.finite_neighbors hl x)]
  intro y hxy
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp hs y ((G.finite_neighbors hl x).mem_toFinset.mpr hxy)
  exact sub_eq_zero.mp (Real.exp_injective (by simpa only [Real.exp_zero] using he))

lemma harmonic_ascent_walk (f : V → ℝ)
    (hf : ∀ x, (∃ y, G.fullGraph.Adj x y ∧ f x < f y) ∨
      (∀ y, G.fullGraph.Adj x y → f y = f x)) {x y : V}
    (w : G.fullGraph.Walk x y) (hxy : f y ≠ f x) :
    ∃ z, ∃ q : G.fullGraph.Walk x z, (∀ v ∈ q.support, f x ≤ f v) ∧ f x < f z := by
  induction w with
  | nil => exact False.elim (hxy rfl)
  | @cons x u y hxu w ih =>
    rcases hf x with ⟨z,hxz,hz⟩ | hflat
    · refine ⟨z,.cons hxz .nil,?_,hz⟩
      intro v hv
      simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,List.mem_cons,
        List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl
      · exact le_rfl
      · exact hz.le
    · have hux := hflat u hxu
      obtain ⟨z,q,hq,hz⟩ := ih (by simpa only [hux] using hxy)
      refine ⟨z,.cons hxu q,?_,by simpa only [hux] using hz⟩
      intro v hv
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact le_rfl
      · simpa only [hux] using hq v hv

lemma orbitAdjustedHeight_nonconstant (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x)
    (hu : ¬ G.CombinatoriallyUnimodular) (x : V) :
    ∃ y, G.orbitAdjustedHeight a x y ≠ 0 := by
  by_contra h
  push Not at h
  apply hu
  intro φ y
  have hx := h (φ.vertex x)
  simp only [orbitAdjustedHeight,ha,add_sub_cancel_right] at hx
  have he : G.modularRatio (φ.vertex x) x = 1 := by
    rw [← Real.exp_log (G.modularRatio_pos hc hl (φ.vertex x) x)]
    rw [show Real.log (G.modularRatio (φ.vertex x) x) = 0 from hx,Real.exp_zero]
  have he' : G.modularRatio x (φ.vertex x) = 1 := by
    have hcoc := G.modularRatio_cocycle hc hl x (φ.vertex x) x
    rw [he,mul_one,G.modularRatio_self] at hcoc
    exact hcoc
  rw [← G.modularRatio_aut_base hc hl x y φ] at he'
  unfold modularRatio at he'
  have hcard := (div_eq_one_iff_eq
    (Nat.cast_ne_zero.mpr (G.suborbitCard_pos hc hl (φ.vertex y) y).ne')).mp he'
  exact_mod_cast hcard

theorem stationaryOrbitHeight_ascent [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) (x : V) :
    ∃ y, ∃ w : G.fullGraph.Walk x y,
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
        0 < G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  let f := G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x
  have hself : f x = 0 := G.orbitAdjustedHeight_self _ x
  obtain ⟨y,hy⟩ := G.orbitAdjustedHeight_nonconstant hc hl _
    (G.stationaryOrbitWeight_aut μ) hu x
  have hhar (v : V) : (∑ y ∈ (G.finite_neighbors hl v).toFinset, Real.exp (f y-f v)) =
      G.modularWalkDegree v := by
    have he (y : V) : f y-f v = G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v y := by
      dsimp [f]
      rw [G.orbitAdjustedHeight_change_base hc hl _ x v y,add_sub_cancel_left]
    simp_rw [he]
    exact G.stationaryOrbitHeight_harmonic hc hl hq μ hμ hstat v
  obtain ⟨z,w,hw,hz⟩ := G.harmonic_ascent_walk f (G.height_harmonic_flat_or_rise hl f hhar)
    (hc x y).some (by simpa only [hself] using hy)
  refine ⟨z,w,?_,?_⟩
  · intro v hv
    simpa only [hself] using hw v hv
  · simpa only [hself] using hz

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_UniformHeightAscent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_uniform_ascent [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L : ℕ, ∀ x, ∃ y, ∃ w : G.fullGraph.Walk x y,
      w.length ≤ L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
      ε ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  let : Nonempty G.VertexOrbit := ⟨G.vertexOrbit (Classical.arbitrary V)⟩
  choose y w hw hr using fun i : G.VertexOrbit =>
    G.stationaryOrbitHeight_ascent hc hl hq μ hμ hstat hu i.out
  let a := G.stationaryOrbitWeight μ
  let rise : G.VertexOrbit → ℝ := fun i => G.orbitAdjustedHeight a i.out (y i)
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ rise Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ
    (fun k : G.VertexOrbit => (w k).length) Finset.univ_nonempty
  refine ⟨rise i,hr i,(w j).length,fun x => ?_⟩
  let k := G.vertexOrbit x
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  let f : G.fullGraph →g G.fullGraph :=
    ⟨φ.vertex,fun {_ _} h => (Aut.fullGraph_adj G φ _ _).mpr h⟩
  refine ⟨φ.vertex (y k),((w k).map f).copy hφ rfl,?_,?_,?_⟩
  · simpa only [SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map] using
      hj k (Finset.mem_univ _)
  · intro v hv
    simp only [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨z,hz,rfl⟩ := hv
    change 0 ≤ G.orbitAdjustedHeight a x (φ.vertex z)
    rw [← hφ,G.orbitAdjustedHeight_aut a (G.stationaryOrbitWeight_aut μ)]
    exact hw k z hz
  · change rise i ≤ G.orbitAdjustedHeight a x (φ.vertex (y k))
    rw [← hφ,G.orbitAdjustedHeight_aut a (G.stationaryOrbitWeight_aut μ)]
    exact hi k (Finset.mem_univ _)

lemma height_ascent_iterate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (L : ℕ)
    (hstep : ∀ x, ∃ y, ∃ w : G.fullGraph.Walk x y, w.length ≤ L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v) ∧ ε ≤ G.orbitAdjustedHeight a x y)
    (n : ℕ) (x : V) :
    ∃ y, ∃ w : G.fullGraph.Walk x y, w.length ≤ n*L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v) ∧
      n*ε ≤ G.orbitAdjustedHeight a x y := by
  induction n with
  | zero =>
    refine ⟨x,.nil,by simp,?_,by simp⟩
    intro v hv
    have he : v = x := List.mem_singleton.mp hv
    rw [he,G.orbitAdjustedHeight_self]
  | succ n ih =>
    obtain ⟨y,w,hlen,hw,hr⟩ := ih
    obtain ⟨z,q,hqlen,hq,hqr⟩ := hstep y
    refine ⟨z,w.append q,?_,?_,?_⟩
    · rw [SimpleGraph.Walk.length_append]
      exact (Nat.add_le_add hlen hqlen).trans_eq (Nat.succ_mul n L).symm
    · intro v hv
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
      · exact hw v hv
      · rw [G.orbitAdjustedHeight_change_base hc hl a x y v]
        exact add_nonneg ((mul_nonneg (Nat.cast_nonneg n) hε).trans hr) (hq v hv)
    · rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
      push_cast
      nlinarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HeightOrbitConnection
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem height_uniform_orbit_connection_abs [Fintype G.VertexOrbit]
    (hc : G.fullGraph.Connected) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) :
    ∃ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x (j : G.VertexOrbit), ∃ y,
      ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y = j ∧ w.length ≤ N ∧
        ∀ v ∈ w.support, |G.orbitAdjustedHeight a x v| ≤ D := by
  let w : (i j : G.VertexOrbit) → G.fullGraph.Walk i.out j.out := fun i j => (hc i.out j.out).some
  let N : ℕ := ∑ i : G.VertexOrbit, ∑ j : G.VertexOrbit, (w i j).length
  let b : G.VertexOrbit → G.VertexOrbit → ℝ := fun i j =>
    ∑ v ∈ (w i j).support.toFinset, |G.orbitAdjustedHeight a i.out v|
  let D : ℝ := ∑ i : G.VertexOrbit, ∑ j : G.VertexOrbit, b i j
  have hb (i j : G.VertexOrbit) : 0 ≤ b i j := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hb i j
  have hlen (i j : G.VertexOrbit) : (w i j).length ≤ N :=
    (Finset.single_le_sum (f := fun k => (w i k).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k => ∑ j, (w k j).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hd (i j : G.VertexOrbit) (v : V) (hv : v ∈ (w i j).support) :
      |G.orbitAdjustedHeight a i.out v| ≤ D :=
    (Finset.single_le_sum (fun _ _ => abs_nonneg _) (List.mem_toFinset.mpr hv)).trans
      ((Finset.single_le_sum (fun j _ => hb i j) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hb i j) (Finset.mem_univ i)))
  refine ⟨N,D,hD,fun x j => ?_⟩
  let i := G.vertexOrbit x
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  let f : G.fullGraph →g G.fullGraph :=
    ⟨φ.vertex,fun {_ _} h => (Aut.fullGraph_adj G φ _ _).mpr h⟩
  refine ⟨φ.vertex j.out,((w i j).map f).copy hφ rfl,?_,?_,?_⟩
  · rw [G.vertexOrbit_aut]
    exact j.out_eq'
  · simpa only [SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map] using hlen i j
  · intro v hv
    simp only [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨z,hz,rfl⟩ := hv
    change |G.orbitAdjustedHeight a x (φ.vertex z)| ≤ D
    rw [← hφ,G.orbitAdjustedHeight_aut a ha]
    exact hd i j z hz

theorem height_uniform_orbit_connection [Fintype G.VertexOrbit]
    (hc : G.fullGraph.Connected) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) :
    ∃ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x (j : G.VertexOrbit), ∃ y,
      ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y = j ∧ w.length ≤ N ∧
        ∀ v ∈ w.support, -D ≤ G.orbitAdjustedHeight a x v := by
  obtain ⟨N,D,hD,h⟩ := G.height_uniform_orbit_connection_abs hc a ha
  refine ⟨N,D,hD,fun x j => ?_⟩
  obtain ⟨y,w,hy,hw,hh⟩ := h x j
  exact ⟨y,w,hy,hw,fun v hv => (abs_le.mp (hh v hv)).1⟩

theorem stationaryOrbitHeight_orbit_above [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → ∀ x (j : G.VertexOrbit),
      ∃ y, ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y = j ∧
        (w.length : ℝ) ≤ A*r+B ∧
        (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
        r ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_ascent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  obtain ⟨N,D,hD,hconn⟩ := G.height_uniform_orbit_connection hc a (G.stationaryOrbitWeight_aut μ)
  let A : ℝ := (L : ℝ)/ε+1
  let B : ℝ := (D/ε+1)*L+N
  refine ⟨A,B,by dsimp [A]; positivity,by dsimp [B]; positivity,fun r hr x j => ?_⟩
  let n : ℕ := ⌈(r+D)/ε⌉₊
  have hn : r+D ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil ((r+D)/ε))
  have hn' : (n : ℝ) ≤ (r+D)/ε+1 :=
    (Nat.ceil_lt_add_one (div_nonneg (add_nonneg hr hD) hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_ascent_iterate hc hl a ε hε.le L hstep n x
  obtain ⟨z,q,hqorb,hqlen,hq⟩ := hconn y j
  refine ⟨z,w.append q,hqorb,?_,?_,?_⟩
  · rw [SimpleGraph.Walk.length_append,Nat.cast_add]
    have hwl : (w.length : ℝ) ≤ (n : ℝ)*L := by exact_mod_cast hwlen
    have hql : (q.length : ℝ) ≤ N := by exact_mod_cast hqlen
    have hm := mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    have he : (((r+D)/ε+1)*L+(N : ℝ)) = (L:ℝ)/ε*r+B := by dsimp [B]; ring
    calc
      _ ≤ (n : ℝ)*L+(N : ℝ) := add_le_add hwl hql
      _ ≤ ((r+D)/ε+1)*L+(N : ℝ) := add_le_add hm le_rfl
      _ = (L : ℝ)/ε*r+B := he
      _ ≤ A*r+B := by dsimp [A]; nlinarith
  · intro v hv
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · exact hw v hv
    · rw [G.orbitAdjustedHeight_change_base hc hl a x y v]
      have hv' := hq v hv
      linarith
  · rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
    have hz := hq z q.end_mem_support
    linarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma openFrontier_dependsOn (S : Set V) :
    DependsOn (fun ω => openFrontier G ω S) (ballIncidentEdges G S) := by
  intro ω η hωη
  ext z
  constructor
  · rintro ⟨hz,u,hu,e,he,heq⟩
    exact ⟨hz,u,hu,e,(Iff.of_eq (hωη e ⟨u,hu,by rw [heq]; simp⟩)).mp he,heq⟩
  · rintro ⟨hz,u,hu,e,he,heq⟩
    exact ⟨hz,u,hu,e,(Iff.of_eq (hωη e ⟨u,hu,by rw [heq]; simp⟩)).mpr he,heq⟩

lemma measurable_mem_openFrontier [Countable V] [Countable E] (S : Set V) (z : V) :
    Measurable (fun ω => z ∈ openFrontier G ω S) := by
  exact measurable_const.and (Measurable.exists fun u => measurable_const.and
    (Measurable.exists fun e => (measurable_set_mem e).and measurable_const))

lemma measurableSet_openFrontier_eq [Countable V] [Countable E] (S F : Set V) :
    MeasurableSet {ω | openFrontier G ω S = F} := by
  have he : {ω | openFrontier G ω S = F} =
      ⋂ z : V, {ω | (z ∈ openFrontier G ω S) ↔ z ∈ F} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact Set.ext_iff
  rw [he]
  exact MeasurableSet.iInter fun z =>
    ((measurable_mem_openFrontier G S z).iff measurable_const).setOf

lemma restricted_exactCluster_dependsOn (I : Set E) (x : V) (S : Set V) :
    DependsOn (fun ω => cluster G (ω ∩ I) x = S) (ballIncidentEdges G S) := by
  intro ω η hωη
  have ha : ∀ e ∈ (criticalModel G).incidentEdges S,
      (e ∈ Set.inter ω I) = (e ∈ Set.inter η I) := by
    intro e he
    exact congrArg (fun p : Prop => p ∧ e ∈ I) (hωη e he)
  have hh := (criticalModel G).exactCluster_dependsOn x S ha
  change ((criticalModel G).cluster (Set.inter ω I) x = S) =
    ((criticalModel G).cluster (Set.inter η I) x = S) at hh
  rw [criticalModel_cluster,criticalModel_cluster] at hh
  exact hh

lemma measurableSet_restricted_exactCluster [Countable V] [Countable E]
    (I : Set E) (x : V) (S : Set V) :
    MeasurableSet {ω | cluster G (ω ∩ I) x = S} := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  simpa only [criticalModel_cluster,Set.preimage_ofPred_eq] using
    ((criticalModel G).measurableSet_exactCluster x S).preimage hm

lemma lowerFrontierCell_dependsOn (I J : Set E) (x : V) (S F : Set V) :
    DependsOn (fun ω => ω ∈ lowerFrontierCell G I J x S F) (ballIncidentEdges G S) := by
  intro ω η hωη
  have hc := restricted_exactCluster_dependsOn G I x S hωη
  change (cluster G (Set.inter ω I) x = S) =
    (cluster G (Set.inter η I) x = S) at hc
  have ha : ∀ e ∈ ballIncidentEdges G S,
      (e ∈ Set.inter ω J) = (e ∈ Set.inter η J) := by
    intro e he
    exact congrArg (fun p : Prop => p ∧ e ∈ J) (hωη e he)
  have hf := openFrontier_dependsOn G S ha
  change openFrontier G (Set.inter ω J) S = openFrontier G (Set.inter η J) S at hf
  change (cluster G (Set.inter ω I) x = S ∧ openFrontier G (Set.inter ω J) S = F) =
    (cluster G (Set.inter η I) x = S ∧ openFrontier G (Set.inter η J) S = F)
  rw [hc,hf]

lemma measurableSet_lowerFrontierCell [Countable V] [Countable E]
    (I J : Set E) (x : V) (S F : Set V) :
    MeasurableSet (lowerFrontierCell G I J x S F) := by
  have hm : Measurable (fun ω : Set E => ω ∩ J) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (measurableSet_restricted_exactCluster G I x S).inter
    ((measurableSet_openFrontier_eq G S F).preimage hm)

lemma openFrontier_lowerCluster_outside (ω : Set E) (D : Set V) (x : V)
    (hx : x ∈ D) {z : V}
    (hz : z ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G D) x)) : z ∉ D := by
  rintro hzD
  obtain ⟨hz,u,hu,e,he,heq⟩ := hz
  have huD := conn_internalEdges_end_mem G ω D hx hu
  apply hz
  exact hu.tail ⟨e,⟨he,(mem_internalEdges_of_ends G D e u z heq).mpr ⟨huD,hzD⟩⟩,heq⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabFirstVisit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma walk_endpoint_height_bound {V : Type*} {H : SimpleGraph V}
    (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ {u v}, H.Adj u v → |f v-f u| ≤ R)
    {x y : V} (p : H.Walk x y) (hx : f x < b)
    (hbelow : ∀ v ∈ p.support, v ≠ y → f v < b) : f y ≤ b+R := by
  induction p with
  | nil => linarith
  | @cons x v y hxv p ih =>
    by_cases hv : v = y
    · subst v
      have hh := (abs_le.mp (hjump hxv)).2
      linarith
    · exact ih (hbelow v (by simp) hv)
        (fun w hw hwy => hbelow w (List.mem_cons_of_mem _ hw) hwy)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSurgeryGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace Percolation.BenjaminiSchramm

lemma walk_first_strict_height_peak {V : Type*} {H : SimpleGraph V}
    (f : V → ℝ) {x y : V} (p : H.Walk x y) (t : ℝ)
    (hy : t ≤ f y) :
    ∃ z, t ≤ f z ∧ ∃ q : H.Walk x z, q.length ≤ p.length ∧
      (∀ v ∈ q.support, v ∈ p.support) ∧
      ∀ v ∈ q.support, v ≠ z → f v < f z := by
  let S := p.support.toFinset.filter fun v => t ≤ f v
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support,hy⟩
  obtain ⟨z,hzS,hzp,hfirst⟩ := p.exists_mem_support_forall_mem_support_imp_eq S
    ⟨y,Finset.mem_filter.mpr ⟨hyS,p.end_mem_support⟩⟩
  have hz : t ≤ f z := (Finset.mem_filter.mp hzS).2
  refine ⟨z,hz,p.takeUntil z hzp,p.length_takeUntil_le_length hzp,
    fun v hv => p.support_takeUntil_subset_support hzp hv,?_⟩
  intro v hv hvz
  have hlt : f v < t := by
    by_contra hn
    have hvS : v ∈ S := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (p.support_takeUntil_subset_support hzp hv),le_of_not_gt hn⟩
    exact hvz (hfirst v hvS hv)
  exact hlt.trans_le hz

variable {V E : Type*} (G : BondGraph V E)

lemma conn_mem_of_open_closed (η : Set E) (U : Set V) (x : V) (hx : x ∈ U)
    (hclosed : ∀ e ∈ η, ∀ v ∈ G e, v ∈ U → ∀ w ∈ G e, w ∈ U) :
    ∀ y, Conn G η x y → y ∈ U := by
  intro y hy
  induction hy with
  | refl => exact hx
  | @tail v w hconn hstep ih =>
    obtain ⟨e,he,heq⟩ := hstep
    exact hclosed e he v (by rw [heq]; simp) ih w (by rw [heq]; simp)

lemma openFrontier_reachable (ω : Set E) (I : Set E) (x : V) {u : V}
    (hu : u ∈ openFrontier G ω (cluster G (ω ∩ I) x)) : Conn G ω x u := by
  obtain ⟨_,v,hv,e,he,heq⟩ := hu
  exact (conn_mono G Set.inter_subset_left hv).tail ⟨e,he,heq⟩

theorem strict_peak_of_lower_frontier_surgery
    (ω η : Set E) (D S F P : Set V) (x u z : V) (f : V → ℝ)
    (hS : cluster G (ω ∩ internalEdges G D) x=S)
    (hF : openFrontier G ω S=F) (hu : u ∈ F)
    (hagree : ∀ e ∈ ballIncidentEdges G S, (e ∈ ω)=(e ∈ η))
    (hpath : Conn G η u z)
    (hclosed : ∀ e ∈ η, ∀ v ∈ G e, v ∈ F ∪ P →
      ∀ w ∈ G e, w ∈ S ∪ F ∪ P)
    (hbelow : ∀ v ∈ S ∪ F, f v < f z)
    (hpeak : ∀ v ∈ P, v ≠ z → f v < f z) :
    Conn G η x z ∧ ∀ y, Conn G η z y → y ≠ z → f y < f z := by
  have hSη : cluster G (η ∩ internalEdges G D) x=S := by
    have hh := restricted_exactCluster_dependsOn G (internalEdges G D) x S hagree
    exact (Iff.of_eq hh).mp hS
  have hFη : openFrontier G η S=F := by
    have hh := openFrontier_dependsOn G S hagree
    exact hh.symm.trans hF
  have huη : u ∈ openFrontier G η (cluster G (η ∩ internalEdges G D) x) := by
    rwa [hSη,hFη]
  have hxz : Conn G η x z := (openFrontier_reachable G η _ x huη).trans hpath
  have hxU : x ∈ S ∪ F ∪ P := Or.inl (Or.inl (hSη ▸ mem_cluster_self G _ x))
  have hclose : ∀ e ∈ η, ∀ v ∈ G e, v ∈ S ∪ F ∪ P →
      ∀ w ∈ G e, w ∈ S ∪ F ∪ P := by
    intro e he v hv hvU w hw
    rcases hvU with (hvS | hvF) | hvP
    · by_cases hwS : w ∈ S
      · exact Or.inl (Or.inl hwS)
      · have hwF : w ∈ F := by
          rw [←hFη]
          have hne : v ≠ w := fun hvw => hwS (hvw ▸ hvS)
          exact ⟨hwS,v,hvS,e,he,(Sym2.mem_and_mem_iff hne).mp ⟨hv,hw⟩⟩
        exact Or.inl (Or.inr hwF)
    · exact hclosed e he v hv (Or.inl hvF) w hw
    · exact hclosed e he v hv (Or.inr hvP) w hw
  refine ⟨hxz,?_⟩
  intro y hzy hyz
  have hyU := conn_mem_of_open_closed G η (S ∪ F ∪ P) x hxU hclose y (hxz.trans hzy)
  rcases hyU with hy | hy
  · exact hbelow y hy
  · exact hpeak y hy hyz

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_peak_extension [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R) :
    ∃ L : ℕ, ∀ x, ∃ z, ∃ w : G.fullGraph.Walk x z,
      w.length ≤ L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
      2*R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z ∧
      ∀ v ∈ w.support, v ≠ z →
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v <
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z := by
  obtain ⟨A,B,_hA,_hB,hpath⟩ := G.stationaryOrbitHeight_orbit_above hc hl hq μ hμ hstat hu
  obtain ⟨L,hL⟩ := exists_nat_ge (A*(2*R)+B)
  refine ⟨L,fun x => ?_⟩
  obtain ⟨y,p,_horb,hlen,hmin,hy⟩ := hpath (2*R) (by positivity) x (G.vertexOrbit x)
  obtain ⟨z,hz,w,hwlen,hsub,hpeak⟩ := walk_first_strict_height_peak
    (G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x) p (2*R) hy
  refine ⟨z,w,?_,fun v hv => hmin v (hsub v hv),hz,hpeak⟩
  have hpL : p.length ≤ L := by exact_mod_cast hlen.trans hL
  exact hwlen.trans hpL

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace Percolation.BenjaminiSchramm

lemma walk_first_height_prefix {V : Type*} {H : SimpleGraph V}
    (f : V → ℝ) {x y : V} (p : H.Walk x y) (t : ℝ) (hy : t ≤ f y) :
    ∃ z, t ≤ f z ∧ ∃ q : H.Walk x z, q.length ≤ p.length ∧
      (∀ v ∈ q.support, v ∈ p.support) ∧
      ∀ v ∈ q.support, v ≠ z → f v < t := by
  let S := p.support.toFinset.filter fun v => t ≤ f v
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support,hy⟩
  obtain ⟨z,hzS,hzp,hfirst⟩ := p.exists_mem_support_forall_mem_support_imp_eq S
    ⟨y,Finset.mem_filter.mpr ⟨hyS,p.end_mem_support⟩⟩
  have hz : t ≤ f z := (Finset.mem_filter.mp hzS).2
  refine ⟨z,hz,p.takeUntil z hzp,p.length_takeUntil_le_length hzp,
    fun v hv => p.support_takeUntil_subset_support hzp hv,?_⟩
  intro v hv hvz
  by_contra hn
  have hvS : v ∈ S := Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr (p.support_takeUntil_subset_support hzp hv),le_of_not_gt hn⟩
  exact hvz (hfirst v hvS hv)

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_bounded_peak_extension [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ L : ℕ, ∀ x, ∃ z, ∃ w : G.fullGraph.Walk x z,
      w.length ≤ L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
      (2*R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z ≤ 3*R) ∧
      ∀ v ∈ w.support, v ≠ z →
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v <
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x z := by
  obtain ⟨L,hpath⟩ := G.stationaryOrbitHeight_peak_extension hc hl hq μ hμ hstat hu R hR
  refine ⟨L,fun x => ?_⟩
  obtain ⟨y,p,hlen,hmin,hy,_hpeak⟩ := hpath x
  let f := G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x
  obtain ⟨z,hz,w,hwlen,hsub,hbelow⟩ := walk_first_height_prefix f p (2*R) hy
  have hj {v v' : V} (hv : G.fullGraph.Adj v v') : |f v'-f v| ≤ R := by
    obtain ⟨⟨e,_he,heq⟩,_hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hv
    have hh := hjump e v v' (by rw [heq]; simp) (by rw [heq]; simp)
    have he : f v'-f v=G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v v' := by
      dsimp [f]
      rw [G.orbitAdjustedHeight_change_base hc hl _ x v v',add_sub_cancel_left]
    rwa [he]
  have hzupper : f z ≤ 2*R+R := walk_endpoint_height_bound f R (2*R) hR.le hj w
    (by simp only [f,G.orbitAdjustedHeight_self]; positivity) hbelow
  refine ⟨z,w,hwlen.trans hlen,fun v hv => hmin v (hsub v hv),⟨hz,by linarith⟩,?_⟩
  intro v hv hvz
  exact (hbelow v hv hvz).trans_le hz

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntegerFrontierCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma integer_lower_frontier_level (f : V → ℤ) (n : ℤ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1)
    (ω : Set E) (x : V) (hx : f x < n) {u : V}
    (hu : u ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G {v | f v < n}) x)) : f u=n := by
  have hout := openFrontier_lowerCluster_outside G ω {v | f v < n} x hx hu
  obtain ⟨_,v,hv,e,_he,heq⟩ := hu
  have hvn := conn_internalEdges_end_mem G ω {v | f v < n} hx hv
  have hj := hjump e v u (by rw [heq]; simp) (by rw [heq]; simp)
  change ¬f u < n at hout
  change f v < n at hvn
  omega

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakFiniteEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {E : Type*}

lemma finiteBondPattern_dependsOn (F : Finset E) (σ : Set E) :
    DependsOn (fun ω => ω ∈ finiteBondPattern F σ) (F : Set E) := by
  intro ω η h
  apply propext
  constructor
  · intro hω e he
    exact (h e he).symm.trans (hω e he)
  · intro hη e he
    exact (h e he).trans (hη e he)

lemma measurableSet_finiteBondPattern [Countable E] (F : Finset E) (σ : Set E) :
    MeasurableSet (finiteBondPattern F σ) :=
  (Measurable.forall fun e => measurable_const.imp
    ((measurable_set_mem e).eq_const (e ∈ σ))).setOf

lemma finiteBondPattern_probability_lower (p : unitInterval) (F : Finset E) (σ : Set E) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) ≤ law p (finiteBondPattern F σ) := by
  let T : Set (F : Set E) := Subtype.val ⁻¹' σ
  have he : finiteBondPattern F σ =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (F : Set E))) ⁻¹' {T} := by
    ext ω
    change (∀ e ∈ F, (e ∈ ω)=(e ∈ σ)) ↔ Subtype.val ⁻¹' ω=T
    constructor
    · intro h
      ext e
      exact Iff.of_eq (h e e.property)
    · intro h e he
      exact propext (show (⟨e,he⟩ : (F : Set E)) ∈ Subtype.val ⁻¹' ω ↔
        (⟨e,he⟩ : (F : Set E)) ∈ T from by rw [h])
  have hprob : (law p).real (finiteBondPattern F σ) =
      (p : ℝ)^T.ncard*(1-p : ℝ)^Tᶜ.ncard := by
    unfold Measure.real
    rw [he,←Measure.map_apply (measurable_set_restrict _) (MeasurableSet.singleton T),law_map_restrict]
    change (ProbabilityTheory.setBernoulli Set.univ p).real {T}=_
    simpa only [←Set.compl_eq_univ_sdiff] using ProbabilityTheory.setBernoulli_real_singleton p
      (Set.subset_univ T) (Set.toFinite Set.univ)
  have hcard : T.ncard+Tᶜ.ncard=F.card := by
    calc
      _ = Nat.card (F : Set E) := Set.ncard_add_ncard_compl T
      _ = F.card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe F
  have hmin : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hb : (min (p : ℝ) (1-p))^F.card ≤ (p : ℝ)^T.ncard*(1-p : ℝ)^Tᶜ.ncard := by
    rw [←hcard,pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hmin (min_le_left _ _) _)
      (pow_le_pow_left₀ hmin (min_le_right _ _) _) (pow_nonneg hmin _) (pow_nonneg p.2.1 _)
  exact ENNReal.ofReal_le_of_le_toReal (hb.trans_eq hprob.symm)

lemma fresh_finiteBondPattern_cell_lower [Countable E]
    (p : unitInterval) (Q : Set E) (A : Set (Set E)) (hA : MeasurableSet A)
    (hdep : DependsOn (fun ω => ω ∈ A) Q)
    (F : Finset E) (hF : (F : Set E) ⊆ Qᶜ) (σ : Set E) :
    law p A*ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) ≤
      law p (A ∩ finiteBondPattern F σ) := by
  let B := finiteBondPattern F σ
  have hB : MeasurableSet B := measurableSet_finiteBondPattern F σ
  have hg : Measurable (B.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hB
  have hd : DependsOn (B.indicator (fun _ => (1 : ℝ≥0∞))) Qᶜ := by
    change ∀ (ω η : Set E), (∀ e ∈ Qᶜ, (e ∈ ω)=(e ∈ η)) →
      B.indicator (fun _ => (1 : ℝ≥0∞)) ω = B.indicator (fun _ => (1 : ℝ≥0∞)) η
    intro ω η h
    have he := finiteBondPattern_dependsOn F σ (fun e he => h e (hF he))
    change (ω ∈ B)=(η ∈ B) at he
    by_cases hω : ω ∈ B
    · have hη : η ∈ B := (Iff.of_eq he).mp hω
      simp only [Set.indicator_of_mem hω,Set.indicator_of_mem hη]
    · have hη : η ∉ B := fun hη => hω ((Iff.of_eq he).mpr hη)
      simp only [Set.indicator_of_notMem hω,Set.indicator_of_notMem hη]
  have hi := CriticalPercolation.BernoulliProduct.lintegral_indicator_fresh
    (fun _ : E => p) Q A hA hdep _ hg hd
  rw [CriticalPercolation.BernoulliProduct.law_const] at hi
  have he : A.indicator (B.indicator (fun _ => (1 : ℝ≥0∞))) =
      (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [Set.indicator,ha,hb]
  rw [he,lintegral_indicator_fun_one (hA.inter hB),lintegral_indicator_fun_one hB] at hi
  exact (mul_le_mul' le_rfl (finiteBondPattern_probability_lower p F σ)).trans_eq hi.symm

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSurgeryProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem lowerFrontierCell_strict_peak_probability [Countable V] [Countable E]
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ v, degree G v ≤ d)
    (p : unitInterval) (D S : Set V) (F : Finset V) (x u z : V)
    (f : V → ℝ) (hu : u ∈ F) (w : (openSimpleGraph G Set.univ).Walk u z)
    (havoid : ∀ v ∈ w.support, v ∉ S)
    (hbelow : ∀ v ∈ S ∪ (F : Set V), f v < f z)
    (hpeak : ∀ v ∈ w.support, v ≠ z → f v < f z) :
    law p (lowerFrontierCell G (internalEdges G D) Set.univ x S (F : Set V))*
      ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(F.card+w.length+1))) ≤
        law p (lowerFrontierCell G (internalEdges G D) Set.univ x S (F : Set V) ∩
          strictHeightPeakConnection G f x z) := by
  let A := lowerFrontierCell G (internalEdges G D) Set.univ x S (F : Set V)
  let Q := ballIncidentEdges G S
  let P := w.support.toFinset
  let W := F ∪ P
  let J := (incidentSupport G hloc W).filter fun e => e ∉ Q
  obtain ⟨l,hl,he,_ho⟩ := walk_lift_bonds G Set.univ w
  let σ : Set E := (l.toFinset : Set E)
  have hends (e : E) (he' : e ∈ l) (v : V) (hv : v ∈ G e) : v ∈ P :=
    List.mem_toFinset.mpr (SimpleGraph.Walk.mem_support_of_mem_edges
      (he ▸ List.mem_map_of_mem he') hv)
  have hmem (e : E) (he' : e ∈ l) : e ∈ J := by
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_incidentSupport G hloc W e).mpr
        ⟨(G e).out.1,Finset.mem_union_right F (hends e he' _ (Sym2.out_fst_mem _)),Sym2.out_fst_mem _⟩
    · rintro ⟨v,hv,hve⟩
      exact havoid v (List.mem_toFinset.mp (hends e he' v hve)) hv
  have hJ : (J : Set E) ⊆ Qᶜ := fun e he => (Finset.mem_filter.mp he).2
  have hJcard : J.card ≤ d*(F.card+w.length+1) := by
    have hP : P.card ≤ w.length+1 := by
      exact (List.toFinset_card_le w.support).trans_eq w.length_support
    calc
      _ ≤ (incidentSupport G hloc W).card := Finset.card_filter_le _ _
      _ ≤ W.card*d := incidentSupport_card_le G hloc d hd W
      _ ≤ (F.card+P.card)*d := Nat.mul_le_mul_right d (Finset.card_union_le F P)
      _ ≤ (F.card+(w.length+1))*d := Nat.mul_le_mul_right d (Nat.add_le_add_left hP F.card)
      _ = _ := by ring
  have hsub : A ∩ finiteBondPattern J σ ⊆ A ∩ strictHeightPeakConnection G f x z := by
    rintro η ⟨hη,hpat⟩
    have hSη : cluster G (η ∩ internalEdges G D) x=S := hη.1
    have hFη : openFrontier G η S=(F : Set V) := by
      simpa only [Set.inter_univ] using hη.2
    have hpath : Conn G η u z := hl.conn (fun e he' =>
      (Iff.of_eq (hpat e (hmem e he'))).mpr (List.mem_toFinset.mpr he'))
    have hclosed : ∀ e ∈ η, ∀ v ∈ G e, v ∈ (F : Set V) ∪ (P : Set V) →
        ∀ v' ∈ G e, v' ∈ S ∪ (F : Set V) ∪ (P : Set V) := by
      intro e heη v hv hvW v' hv'
      by_cases heQ : e ∈ Q
      · obtain ⟨a,ha,hae⟩ := heQ
        by_cases hvS : v' ∈ S
        · exact Or.inl (Or.inl hvS)
        · have hne : a ≠ v' := fun hh => hvS (hh ▸ ha)
          have hvF : v' ∈ openFrontier G η S :=
            ⟨hvS,a,ha,e,heη,(Sym2.mem_and_mem_iff hne).mp ⟨hae,hv'⟩⟩
          exact Or.inl (Or.inr (hFη ▸ hvF))
      · have heJ : e ∈ J := Finset.mem_filter.mpr
          ⟨(mem_incidentSupport G hloc W e).mpr
            ⟨v,Finset.mem_union.mpr hvW,hv⟩,heQ⟩
        have heσ : e ∈ σ := (Iff.of_eq (hpat e heJ)).mp heη
        exact Or.inr (hends e (List.mem_toFinset.mp heσ) v' hv')
    refine ⟨hη,?_⟩
    exact strict_peak_of_lower_frontier_surgery G η η D S (F : Set V) (P : Set V)
      x u z f hSη hFη hu (fun _ _ => rfl) hpath hclosed hbelow
        (fun v hv hvz => hpeak v (List.mem_toFinset.mp hv) hvz)
  have hδ : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hδ1 : min (p : ℝ) (1-p) ≤ 1 := (min_le_left _ _).trans p.2.2
  calc
    _ ≤ law p A*ENNReal.ofReal ((min (p : ℝ) (1-p))^J.card) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ hδ1 hJcard))
    _ ≤ law p (A ∩ finiteBondPattern J σ) := fresh_finiteBondPattern_cell_lower p Q A
      (measurableSet_lowerFrontierCell G _ _ x S _) (lowerFrontierCell_dependsOn G _ _ x S _) J hJ σ
    _ ≤ _ := measure_mono hsub

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NormalizedPeakSurgery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem normalized_peak_surgery_bs_oai
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ L : ℕ, ∀ (p : unitInterval) (d : ℕ), (∀ v, degree G v ≤ d) →
      ∀ (n : ℕ), 0 < n → ∀ (x : V) (u : ℝ) (S F : Finset V),
      (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V)).Nonempty →
      F.Nonempty →
      law p (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V))*
        ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(F.card+L+1))) ≤
      law p (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V) ∩
        {ω | ∃ z, R*((n : ℝ)+1) < (criticalModel G).orbitAdjustedHeight
            ((criticalModel G).stationaryOrbitWeight μ) x z ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ R*((n : ℝ)+4) ∧
          ω ∈ strictHeightPeakConnection G
            ((criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x) x z}) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨L,hpath⟩ := H.stationaryOrbitHeight_bounded_peak_extension hHc hl hHq μ hμ hstat hu R hR hjump
  refine ⟨L,fun p d hd n hn x offset S F hcell hF => ?_⟩
  let f := H.adjustedLayerIndex a R offset x
  let h := H.orbitAdjustedHeight a x
  have hfx : f x < (n : ℤ) := by
    simp only [f,H.adjustedLayerIndex_self]
    exact_mod_cast hn
  have hfj : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1 := by
    intro e v w hv hw
    exact (H.adjustedLayerIndex_edge_jump hHc hl a R offset hR hjump x v w e hv hw).2
  obtain ⟨η,hη⟩ := hcell
  have hSlevel (v : V) (hv : v ∈ S) : f v < (n : ℤ) := by
    apply conn_internalEdges_end_mem G η {v | f v < (n : ℤ)} hfx
    change v ∈ cluster G (η ∩ internalEdges G {v | f v < (n : ℤ)}) x
    rw [hη.1]
    exact hv
  have hFlevel (v : V) (hv : v ∈ F) : f v=(n : ℤ) := by
    apply integer_lower_frontier_level G f (n : ℤ) hfj η x hfx
    have hfront : openFrontier G η (cluster G (η ∩ internalEdges G {v | f v < (n : ℤ)}) x)=(F : Set V) := by
      rw [hη.1]
      simpa only [Set.inter_univ] using hη.2
    rwa [hfront]
  obtain ⟨v,hv⟩ := hF
  obtain ⟨z,w,hwlen,hwmin,hwheight,hwpeak⟩ := hpath v
  have hvheight := H.adjustedLayerIndex_height_bounds a R offset hR x v
  change R*((f v : ℝ)-1) < h v ∧ h v < R*((f v : ℝ)+1) at hvheight
  rw [hFlevel v hv] at hvheight
  simp only [Int.cast_natCast] at hvheight
  have hzadd : h z=h v+H.orbitAdjustedHeight a v z := H.orbitAdjustedHeight_change_base hHc hl a x v z
  have hzband : R*((n : ℝ)+1) < h z ∧ h z ≤ R*((n : ℝ)+4) := by
    change R*((n : ℝ)-1) < h v ∧ h v < R*((n : ℝ)+1) at hvheight
    constructor <;> nlinarith [hwheight.1,hwheight.2]
  have hbelow : ∀ v' ∈ (S : Set V) ∪ (F : Set V), h v' < h z := by
    intro v' hv'
    have hh := (H.adjustedLayerIndex_height_bounds a R offset hR x v').2
    change h v' < R*((f v' : ℝ)+1) at hh
    rcases hv' with hvS | hvF
    · have hi : (f v' : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (show f v'+1 ≤ (n : ℤ) by have := hSlevel v' hvS; omega)
      nlinarith [hzband.1]
    · rw [hFlevel v' hvF] at hh
      simp only [Int.cast_natCast] at hh
      exact hh.trans hzband.1
  have havoid : ∀ v' ∈ w.support, v' ∉ (S : Set V) := by
    intro v' hv' hvS
    have hh := hwmin v' hv'
    have hheight : h v ≤ h v' := by
      have he := H.orbitAdjustedHeight_change_base hHc hl a x v v'
      change h v'=h v+H.orbitAdjustedHeight a v v' at he
      linarith
    have hidx : f v ≤ f v' := by
      unfold f CriticalPercolation.BondGraph.adjustedLayerIndex
      apply sub_le_sub_right
      apply Int.floor_mono
      have hh := div_le_div_of_nonneg_right hheight hR.le
      change h v/R+offset ≤ h v'/R+offset
      linarith
    rw [hFlevel v hv] at hidx
    have := hSlevel v' hvS
    omega
  have hpeak : ∀ v' ∈ w.support, v' ≠ z → h v' < h z := by
    intro v' hv' hvz
    have hh := hwpeak v' hv' hvz
    change H.orbitAdjustedHeight a x v' < H.orbitAdjustedHeight a x z
    rw [H.orbitAdjustedHeight_change_base hHc hl a x v v',
      H.orbitAdjustedHeight_change_base hHc hl a x v z]
    change H.orbitAdjustedHeight a v v' < H.orbitAdjustedHeight a v z at hh
    linarith
  have hg : H.fullGraph=openSimpleGraph G Set.univ := criticalModel_openGraph G Set.univ
  let ι : H.fullGraph →g openSimpleGraph G Set.univ := ⟨id,fun {_ _} h => by simpa only [←hg,id_eq] using h⟩
  have hsupport (v' : V) : v' ∈ (w.map ι).support ↔ v' ∈ w.support := by
    simp only [SimpleGraph.Walk.support_map]
    change v' ∈ w.support.map id ↔ _
    simp only [List.map_id_fun,id_eq]
  have hb := lowerFrontierCell_strict_peak_probability G hl d hd p {v | f v < (n : ℤ)}
    (S : Set V) F x v z h hv (w.map ι)
      (fun v' hv' => havoid v' ((hsupport v').mp hv')) hbelow
      (fun v' hv' => hpeak v' ((hsupport v').mp hv'))
  have hδ : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hδ1 : min (p : ℝ) (1-p) ≤ 1 := (min_le_left _ _).trans p.2.2
  apply le_trans _ (hb.trans (measure_mono ?_))
  · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ hδ1
      (Nat.mul_le_mul_left d (by simpa only [SimpleGraph.Walk.length_map] using Nat.add_le_add_right (Nat.add_le_add_left hwlen F.card) 1))))
  · rintro ω ⟨hc',hp'⟩
    exact ⟨hc',z,hzband.1,hzband.2,hp'⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery_bs_oai.{u_1, u_2} := @OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery_bs_oai.{u_1, u_2}
