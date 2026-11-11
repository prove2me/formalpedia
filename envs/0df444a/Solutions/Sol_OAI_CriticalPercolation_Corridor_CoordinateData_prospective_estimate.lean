-- Prove2me | solution 1 for OAI.CriticalPercolation.Corridor.CoordinateData.prospective_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:21.567671+00:00
-- url     : https://prove2.me/submissions/c705b27e-4e20-4fca-b6bf-3fa00fedcf49

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_fresh_collar_transfer

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_TailProduct
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ProductConditioning
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
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma forceOn_map_law (q : E → unitInterval) (S σ : Set E) :
    (law q).map (forceOn S σ)=law (pinnedParameters q S σ) := by
  simp only [law_eq_infinitePi]
  have hm (e : E) : Measurable (fun b : Prop => if e∈S then e∈σ else b) := .of_discrete
  have h := Measure.infinitePi_map_pi (fun e => bitMeasure (q e)) hm
  change (Measure.infinitePi (fun e => bitMeasure (q e))).map
    (fun (ω : E → Prop) e => if e∈S then e∈σ else ω e)=
    Measure.infinitePi (fun e => bitMeasure (pinnedParameters q S σ e))
  rw [h]
  congr 1
  funext e
  by_cases he : e∈S
  · simp only [ite_eq_left he,Measure.map_const,measure_univ,one_smul]
    by_cases hs : e∈σ <;> simp [pinnedParameters,he,hs,bitMeasure]
  · simp [pinnedParameters,he]

end CriticalPercolation.BernoulliProduct
end
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

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_RestrictedSeed
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma restrictedSeed_mono (A T : Set V) {S U : Set E} (h : S⊆U) :
    G.restrictedSeed A T S⊆G.restrictedSeed A T U := by
  intro ω hω
  exact G.seedHitEvent_upper A T (Set.inter_subset_inter_right _ h) hω

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorSeparation
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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

namespace CriticalPercolation.Corridor

lemma int_eq_of_close (a b : ℤ) (h1 : (a : ℝ)-b<1) (h2 : (b : ℝ)-a<1) : a=b := by
  have h1' : a-b<1 := by exact_mod_cast h1
  have h2' : b-a<1 := by exact_mod_cast h2
  omega

lemma int_endpoint_interval (a b : ℤ) (h1 : (a : ℝ)-b<1) (h2 : (b : ℝ)-a<2) :
    b=a ∨ b=a+1 := by
  have h1' : a-b<1 := by exact_mod_cast h1
  have h2' : b-a<2 := by exact_mod_cast h2
  omega

lemma box_disjoint (j h : ℝ) (hs : 2*j+h<1) {v w : Site} (hv : v≠w) :
    Disjoint (box j h v) (box j h w) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hx1,hx2⟩ := hx
  obtain ⟨hy1,hy2⟩ := hy
  rw [abs_le] at hx1 hx2 hy1 hy2
  apply hv
  apply Prod.ext
  · apply int_eq_of_close <;> linarith
  · apply int_eq_of_close <;> linarith

lemma box_tube_endpoint (j h : ℝ) (hs : j+h<1) (hj : j<1)
    {v : Site} {e : Edge} {x : Point} (hx : x∈box j h v) (hy : x∈tube h e) :
    v=source e ∨ v=target e := by
  obtain ⟨a,b⟩ := v
  obtain ⟨⟨c,d⟩,s⟩ := e
  obtain ⟨hx1,hx2⟩ := hx
  rw [abs_le] at hx1 hx2
  cases s with
  | true =>
    change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(x.1-2*(d : ℝ))|≤h at hy
    rw [abs_le] at hy
    have hb : b=d := int_eq_of_close _ _ (by linarith) (by linarith)
    subst d
    have ha : a=c ∨ a=c+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
    rcases ha with rfl|rfl <;> simp [source,target]
  | false =>
    change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
    rw [abs_le] at hy
    have ha : a=c := int_eq_of_close _ _ (by linarith) (by linarith)
    subst c
    have hb : b=d ∨ b=d+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
    rcases hb with rfl|rfl <;> simp [source,target]

lemma tubes_opposite (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) {x : Point} (hx : x∈tube h ((a,b),true))
    (hy : x∈tube h ((c,d),false)) :
    ∃ v, v∈endpoints ((a,b),true) ∧ v∈endpoints ((c,d),false) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(x.1-2*(b : ℝ))|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
  rw [abs_le] at hx hy
  have hac : c=a ∨ c=a+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
  have hdb : b=d ∨ b=d+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
  refine ⟨(c,b),?_,?_,?_⟩
  · rcases hac with rfl|rfl <;> simp [endpoints,source,target]
  · rcases hdb with rfl|rfl <;> simp [endpoints,source,target]
  · constructor <;> rw [abs_le] <;> constructor <;> dsimp <;> linarith

lemma tubes_parallel_true (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) (hne : (a,b)≠(c,d)) {x : Point}
    (hx : x∈tube h ((a,b),true)) (hy : x∈tube h ((c,d),true)) :
    ∃ v, v∈endpoints ((a,b),true) ∧ v∈endpoints ((c,d),true) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(x.1-2*(b : ℝ))|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(x.1-2*(d : ℝ))|≤h at hy
  rw [abs_le] at hx hy
  have hb : b=d := int_eq_of_close _ _ (by linarith) (by linarith)
  subst d
  have ha : a≠c := by intro h; subst c; exact hne rfl
  have hab : a=c+1 ∨ c=a+1 := by
    have h1 : a ≤ c+1 := by exact_mod_cast (show (a : ℝ) ≤ c+1 by linarith)
    have h2 : c≤a+1 := by exact_mod_cast (show (c : ℝ)≤a+1 by linarith)
    omega
  rcases hab with rfl|rfl
  · refine ⟨(c+1,b),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  · refine ⟨(a+1,b),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith

lemma tubes_parallel_false (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) (hne : (a,b)≠(c,d)) {x : Point}
    (hx : x∈tube h ((a,b),false)) (hy : x∈tube h ((c,d),false)) :
    ∃ v, v∈endpoints ((a,b),false) ∧ v∈endpoints ((c,d),false) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(2*(a : ℝ)-x.1)|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
  rw [abs_le] at hx hy
  have ha : a=c := int_eq_of_close _ _ (by linarith) (by linarith)
  subst c
  have hb : b≠d := by intro h; subst d; exact hne rfl
  have hbd : b=d+1 ∨ d=b+1 := by
    have h1 : b≤d+1 := by exact_mod_cast (show (b : ℝ)≤d+1 by linarith)
    have h2 : d≤b+1 := by exact_mod_cast (show (d : ℝ)≤b+1 by linarith)
    omega
  rcases hbd with rfl|rfl
  · refine ⟨(a,d+1),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  · refine ⟨(a,b+1),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith

lemma distinct_tubes_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    {e f : Edge} (hne : e≠f) {x : Point} (hx : x∈tube h e) (hy : x∈tube h f) :
    ∃ v, v∈endpoints e ∧ v∈endpoints f ∧ x∈box j h v := by
  obtain ⟨⟨a,b⟩,s⟩ := e
  obtain ⟨⟨c,d⟩,t⟩ := f
  cases s <;> cases t
  · exact tubes_parallel_false j h hh hhj hh1 a b c d (by intro he; exact hne (congrArg (fun z => (z,false)) he)) hx hy
  · obtain ⟨v,hv,hv',hb⟩ := tubes_opposite j h hh hhj hh1 c d a b hy hx
    exact ⟨v,hv',hv,hb⟩
  · exact tubes_opposite j h hh hhj hh1 a b c d hx hy
  · exact tubes_parallel_true j h hh hhj hh1 a b c d (by intro he; exact hne (congrArg (fun z => (z,true)) he)) hx hy

lemma box_domain_endpoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {v : Site} {e : Edge} {x : Point} (hx : x∈box j h v) (hy : x∈domain j h e) :
    v∈endpoints e := by
  rcases hy with (hy|hy)|hy
  · have he : v=source e := by
      by_contra he
      exact Set.disjoint_left.mp (box_disjoint j h hs he) hx hy
    simp [endpoints,he]
  · have he : v=target e := by
      by_contra he
      exact Set.disjoint_left.mp (box_disjoint j h hs he) hx hy
    simp [endpoints,he]
  · exact (box_tube_endpoint j h (by linarith) (by linarith) hx hy)

theorem distinct_domains_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hne : e≠f) {x : Point} (hx : x∈domain j h e) (hy : x∈domain j h f) :
    ∃ v, v∈endpoints e ∧ v∈endpoints f ∧ x∈box j h v := by
  rcases hx with (hx|hx)|hx
  · exact ⟨source e,by simp [endpoints],box_domain_endpoint j h hh hhj hs hx hy,hx⟩
  · exact ⟨target e,by simp [endpoints],box_domain_endpoint j h hh hhj hs hx hy,hx⟩
  · rcases hy with (hy|hy)|hy
    · exact ⟨source f,box_domain_endpoint j h hh hhj hs hy (Or.inr hx),by simp [endpoints],hy⟩
    · exact ⟨target f,box_domain_endpoint j h hh hhj hs hy (Or.inr hx),by simp [endpoints],hy⟩
    · exact distinct_tubes_intersection j h hh hhj (by linarith) hne hx hy

lemma nonincident_domains_disjoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (he : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (domain j h e) (domain j h f) := by
  have hne : e≠f := by
    intro hh
    subst f
    exact Set.disjoint_left.mp he (show source e∈endpoints e by simp [endpoints])
      (by simp [endpoints])
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v,hv,hv',_⟩ := distinct_domains_intersection j h hh hhj hs hne hx hy
  exact Set.disjoint_left.mp he hv hv'

lemma nonendpoint_domain_box_disjoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e : Edge} {v : Site} (hv : v∉endpoints e) : Disjoint (box j h v) (domain j h e) := by
  exact Set.disjoint_left.mpr fun _ hx hy => hv (box_domain_endpoint j h hh hhj hs hx hy)

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_OpenTrialBound
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
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma inducedEdges_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (G.inducedEdges S) (G.inducedEdges T) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
  have hx : x∈G.ends e := by rw [← hxy]; simp
  exact Set.disjoint_left.mp h (he x hx) (he' x hx)

end BondGraph
end CriticalPercolation
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

lemma coordinate_collar_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    (B : Set V) (c r : ℝ) (hB : ∀ v∈B, |f v-c| ≤ r)
    {w : V} {n : ℕ} (hw : w∈G.vertexCollar B n) : |f w-c| ≤ r+n*ρ := by
  obtain ⟨v,hv,hw⟩ := Set.mem_iUnion₂.mp hw
  calc
    |f w-c| ≤ |f w-f v|+|f v-c| := abs_sub_le _ _ _
    _ ≤ n*ρ+r := add_le_add (G.coordinate_ball_bound f ρ hρ hf hw) (hB v hv)
    _ = _ := add_comm _ _

lemma inducedEdges_mono {S T : Set V} (h : S⊆T) :
    G.inducedEdges S⊆G.inducedEdges T := by
  intro e he v hv
  exact h (he v hv)

end CriticalPercolation.BondGraph
namespace CriticalPercolation.Corridor
open BondGraph

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

lemma graph_nonincident_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hef : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (graphDomain ξ j h e) (graphDomain ξ j h f) :=
  (nonincident_domains_disjoint j h hh hhj hs hef).preimage ξ

lemma edge_nonincident_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hef : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (corridorEdges G ξ j h e) (corridorEdges G ξ j h f) :=
  G.inducedEdges_disjoint (graph_nonincident_disjoint ξ j h hh hhj hs hef)

lemma edge_box_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e : Edge} {v : Site} (hv : v∉endpoints e) :
    Disjoint (boxEdges G ξ j h v) (corridorEdges G ξ j h e) :=
  G.inducedEdges_disjoint
    ((nonendpoint_domain_box_disjoint j h hh hhj hs hv).preimage ξ)

lemma history_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    (H : Set Edge) {e : Edge} (he : ∀ f∈H, Disjoint (endpoints f) (endpoints e)) :
    Disjoint (⋃ f∈H, corridorEdges G ξ j h f) (corridorEdges G ξ j h e) := by
  apply Set.disjoint_left.mpr
  intro b hb he'
  obtain ⟨f,hf,hb⟩ := Set.mem_iUnion₂.mp hb
  exact Set.disjoint_left.mp (edge_nonincident_disjoint G ξ j h hh hhj hs (he f hf)) hb he'

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SlotContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.Boundary

lemma gridSlot_east (v : Grid) (hv : quadrant v) : gridSlot v<gridSlot (v+(1,0)) := by
  change Nat.pair v.1.toNat v.2.toNat<Nat.pair (v.1+1).toNat (v.2+0).toNat
  rw [add_zero]
  exact Nat.pair_lt_pair_left _ (by dsimp [quadrant] at hv; omega)

lemma gridSlot_north (v : Grid) (hv : quadrant v) : gridSlot v<gridSlot (v+(0,1)) := by
  change Nat.pair v.1.toNat v.2.toNat<Nat.pair (v.1+0).toNat (v.2+1).toNat
  rw [add_zero]
  exact Nat.pair_lt_pair_right _ (by dsimp [quadrant] at hv; omega)

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_LatticeGrowth
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

namespace CriticalPercolation.Corridor
open Boundary

lemma slotSite_quadrant (n : ℕ) : quadrant (slotSite n) := by
  exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _⟩

lemma gridSlot_slotSite (n : ℕ) : gridSlot (slotSite n)=n := by
  simp [gridSlot,slotSite]

lemma parent_slot_lt (e : Edge) (h : quadrant (source e)) :
    gridSlot (source e)<gridSlot (target e) := by
  obtain ⟨v,b⟩ := e
  cases b with
  | true => exact gridSlot_east v h
  | false => exact gridSlot_north v h

lemma incoming_source {n : ℕ} {S : Finset Site} {e : Edge}
    (h : incoming n S=some e) : source e∈S := by
  unfold incoming at h
  split_ifs at h with hw hn
  · have he := Option.some.inj h
    subst e
    exact hw
  · have he := Option.some.inj h
    subst e
    exact hn

lemma incoming_target {n : ℕ} {S : Finset Site} {e : Edge}
    (h : incoming n S=some e) : target e=slotSite n := by
  unfold incoming at h
  split_ifs at h with hw hn
  · have he := Option.some.inj h
    subst e
    simp [target]
  · have he := Option.some.inj h
    subst e
    simp [target]

lemma GrowthState.outgoing_nonincident (n : ℕ) (S : GrowthState) (h : S.Valid n)
    {e : Edge} (he : source e=slotSite n) {f : Edge} (hf : f∈S.seen) :
    Disjoint (endpoints f) (endpoints e) := by
  have hq := (h.2.1 _ (h.2.2 f hf).1).1
  have hf1 := parent_slot_lt f hq
  have hf2 := (h.2.2 f hf).2
  have he1 := parent_slot_lt e (he ▸ slotSite_quadrant n)
  have he2 : gridSlot (source e)=n := by rw [he,gridSlot_slotSite]
  apply Set.disjoint_left.mpr
  intro v hv hw
  rcases hv with hv|hv <;> rcases hw with hw|hw
  · have hh : source f=source e := hv.symm.trans hw
    rw [hh,he2] at hf1
    omega
  · have hh : source f=target e := hv.symm.trans hw
    rw [hh] at hf1
    omega
  · have hh : target f=source e := hv.symm.trans hw
    rw [hh,he2] at hf2
    omega
  · have hh : target f=target e := hv.symm.trans hw
    rw [hh] at hf2
    omega

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_GrowthHistoryGeometry
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

namespace CriticalPercolation.Corridor
open BondGraph Boundary

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

lemma outgoing_unrevealed (hh : 0≤h) (hhj : h≤j) (hsep : 2*j+h<1)
    (n : ℕ) (S : GrowthState) (hv : S.Valid n) (hn : 0<n)
    {e : Edge} (he : source e=slotSite n) :
    Disjoint (revealed G ξ j h S) (corridorEdges G ξ j h e) := by
  apply Disjoint.sup_left
  · apply edge_box_disjoint G ξ j h hh hhj hsep
    intro hroot
    have he1 := parent_slot_lt e (he ▸ slotSite_quadrant n)
    have he2 : gridSlot (source e)=n := by rw [he,gridSlot_slotSite]
    rcases hroot with hh|hh
    · have he0 : gridSlot (source e)=0 := by rw [← hh]; rfl
      omega
    · have he0 : gridSlot (target e)=0 := by rw [← hh]; rfl
      omega
  · exact history_disjoint G ξ j h hh hhj hsep (↑S.seen)
      (fun f hf => S.outgoing_nonincident n hv he hf)

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_PinnedTest
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
variable {E : Type*}

lemma blockProbability_eq_pinnedLaw (q : E → unitInterval) (I σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    blockProbability q I A σ=law (pinnedParameters q I σ) A := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn I σ) hA]
  rfl

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ProductEmbedding
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
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {A E : Type*}

lemma law_map_preimage (q : E → unitInterval) (i : A → E) (hi : Injective i) :
    (law q).map (fun ω : Set E => i ⁻¹' ω)=law (q∘i) := by
  have hind : iIndepFun (fun a (ω : Set E) => i a∈ω) (law q) :=
    iIndepFun.precomp hi (independent_coordinates q)
  have hh := hind.map_fun_eq_infinitePi_map (fun a => measurable_set_mem (i a))
  change (law q).map (fun ω : Set E => i ⁻¹' ω)=_ at hh
  rw [hh]
  rw [law_eq_infinitePi (q∘i)]
  apply congrArg Measure.infinitePi
  funext a
  rw [law_eq_infinitePi]
  exact Measure.infinitePi_map_eval _ (i a)

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SourceGraph
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
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma withSource_original_adj (A : Set V) (ω : Set (E⊕A)) {v w : V}
    (h : (G.openGraph (Sum.inl ⁻¹' ω)).Adj v w) :
    ((G.withSource A).openGraph ω).Adj (some v) (some w) := by
  obtain ⟨⟨e,he,hend⟩,hne⟩ := h
  exact ⟨⟨Sum.inl e,he,by simp [withSource,hend]⟩,fun h => hne (Option.some.inj h)⟩

lemma withSource_original_reachable (A : Set V) (ω : Set (E⊕A)) {v w : V}
    (h : (G.openGraph (Sum.inl ⁻¹' ω)).Reachable v w) :
    ((G.withSource A).openGraph ω).Reachable (some v) (some w) :=
  h.map ⟨Option.some,fun hvw => G.withSource_original_adj A ω hvw⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SourceLift
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
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma withSource_edge_cases (A : Set V) (e : E⊕A) (v w : Option V)
    (he : (G.withSource A).ends e=s(v,w)) :
    (∃ b x y, e=Sum.inl b ∧ v=some x ∧ w=some y ∧ G.ends b=s(x,y)) ∨
    (∃ a : A, e=Sum.inr a ∧ ((v=none ∧ w=some a.val) ∨ (w=none ∧ v=some a.val))) := by
  cases e with
  | inl e =>
    obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
    change s(x,y)=G.ends e at hxy
    have hh : s(some x,some y)=s(v,w) := by simpa [withSource,← hxy] using he
    rcases Sym2.eq_iff.mp hh with hh|hh
    · exact Or.inl ⟨e,x,y,rfl,hh.1.symm,hh.2.symm,hxy.symm⟩
    · exact Or.inl ⟨e,y,x,rfl,hh.2.symm,hh.1.symm,by simpa only [Sym2.eq_swap] using hxy.symm⟩
  | inr a =>
    right
    refine ⟨a,rfl,?_⟩
    have hh : s(none,some a.val)=s(v,w) := he
    rcases Sym2.eq_iff.mp hh with hh|hh
    · exact Or.inl ⟨hh.1.symm,hh.2.symm⟩
    · exact Or.inr ⟨hh.1.symm,hh.2.symm⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayGeometry
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

namespace CriticalPercolation.Relay

lemma width_lower (i : ℕ) : 2 ≤ width i := le_max_left _ _
lemma width_upper (i : ℕ) : width i ≤ 210 := by
  apply max_le (by norm_num)
  linarith [Nat.cast_nonneg (α := ℝ) i]
lemma width_next (i : ℕ) : width i ≤ width (i+1)+1/2 := by
  have h1 := width_lower (i+1)
  have h2 : 210-((i+1 : ℕ) : ℝ)/2 ≤ width (i+1) := le_max_right _ _
  unfold width at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  exact max_le (by linarith) (by linarith)
lemma width_last (L : ℕ) (hL : 416 ≤ L) : width L=2 := by
  apply max_eq_left
  have : (416 : ℝ) ≤ L := by exact_mod_cast hL
  linarith

lemma selectedSign_cases (u : ℝ) : selectedSign u=-1 ∨ selectedSign u=1 := by
  unfold selectedSign
  split  <;>  simp

lemma selectedSign_abs (u : ℝ) : |selectedSign u|=1 := by
  rcases selectedSign_cases u with h|h  <;>  rw [h]  <;>  norm_num

lemma move_towards_axis (u b : ℝ) (hu : |u| ≤ b) :
    |u+selectedSign u| ≤ max 1 (b-1) := by
  rw [abs_le] at hu ⊢
  have h1 : 1 ≤ max 1 (b-1) := le_max_left _ _
  have h2 : b-1 ≤ max 1 (b-1) := le_max_right _ _
  unfold selectedSign
  split  <;>  constructor  <;>  linarith

lemma full_step_height (i : ℕ) (u σ d e ε : ℝ) (hσ : |σ|=1)
    (hu : |u| ≤ width i+d) (hd₀ : 0 ≤ d) (hd : d+e/4 ≤ 1/4)
    (hε : |ε| ≤ e/4) :
    |u+selectedSign u-σ/4+ε| ≤ width (i+1) := by
  have h1 := width_lower (i+1)
  have h2 := width_next i
  have hs : |σ/4|=1/4 := by rw [abs_div,hσ]; norm_num
  calc
    _  ≤  |u+selectedSign u|+|σ/4|+|ε| :=
      by linarith [abs_add_le (u+selectedSign u-σ/4) ε, abs_sub (u+selectedSign u) (σ/4)]
    _  ≤  max 1 (width i+d-1)+1/4+e/4 := by
      rw [hs]
      linarith [move_towards_axis u (width i+d) hu]
    _  ≤  width (i+1) := by
      rcases le_total 1 (width i+d-1) with hh|hh
      · rw [max_eq_right hh]; linarith
      · rw [max_eq_left hh]; linarith

lemma full_step_time (i : ℕ) (y z d e : ℝ)
    (hy : |y-(i : ℝ)| ≤ (i+1)*e+d) (hz : |z-(y+1)| ≤ e/4)
    (hde : d+e/4 ≤ e) : |z-((i+1 : ℕ) : ℝ)| ≤ (i+2)*e := by
  rw [abs_le] at hy hz ⊢
  push_cast
  constructor  <;>  nlinarith

lemma path_axis_bound (L i : ℕ) (hi : i ≤ L) (y x : ℝ×ℝ) (d e σ : ℝ)
    (hσ : |σ|=1) (he : 0 ≤ e)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    |x.2-σ*x.1/4| ≤ 210+d+100+((L+1)*e+d+100)/4 := by
  have ht : |x.1-(i : ℝ)| ≤ (L+1)*e+d+100 := by
    have hc : (i : ℝ) ≤ L := by exact_mod_cast hi
    calc
      _  ≤  |x.1-y.1|+|y.1-(i : ℝ)| := abs_sub_le _ _ _
      _  ≤  100+((i+1)*e+d) := add_le_add hxt hyt
      _  ≤  _ := by nlinarith
  have hsame : σ*(i : ℝ)/4-σ*x.1/4=σ*((i : ℝ)-x.1)/4 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(i : ℝ)/4|+|σ*(i : ℝ)/4-σ*x.1/4| := by
      linarith [abs_sub_le x.2 (σ*(i : ℝ)/4) (σ*x.1/4),
        abs_sub_le x.2 y.2 (σ*(i : ℝ)/4)]
    _  ≤  100+(width i+d)+((L+1)*e+d+100)/4 := by
      rw [hsame,abs_div,abs_mul,hσ,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4),abs_sub_comm (i : ℝ)]
      exact add_le_add (add_le_add hxz hyz) (div_le_div_of_nonneg_right ht (by norm_num))
    _  ≤  _ := by linarith [width_upper i]

lemma band_mem_domain (J T σ : ℝ) (hσ : |σ|=1)
    (x : ℝ×ℝ) (ht : -J ≤ x.1 ∧ x.1 ≤ T+J)
    (hz : |x.2-σ*x.1/4| ≤ 630) : x∈domain J T σ := by
  have ha : |σ|=1 := hσ
  by_cases h0 : x.1 < 0
  · apply Or.inl; apply Or.inl
    have hx : |x.1| ≤ J := by rw [abs_of_neg h0]; linarith [ht.1]
    refine ⟨hx,?_⟩
    calc
      |x.2|  ≤  |x.2-σ*x.1/4|+|σ*x.1/4| := by simpa using abs_sub_le x.2 (σ*x.1/4) 0
      _  ≤  630+J/4 := by
        rw [abs_div,abs_mul,ha,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4)]
        exact add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
      _ = _ := add_comm _ _
  · by_cases h1 : T < x.1
    · apply Or.inl; apply Or.inr
      have hx : |x.1-T| ≤ J := by rw [abs_of_pos (by linarith)]; linarith [ht.2]
      refine ⟨hx,?_⟩
      calc
        _  ≤  |x.2-σ*x.1/4|+|σ*x.1/4-σ*T/4| := abs_sub_le _ _ _
        _ = |x.2-σ*x.1/4|+|x.1-T|/4 := by
          rw [show σ*x.1/4-σ*T/4=σ*(x.1-T)/4 by ring,abs_div,abs_mul,ha,one_mul]
          norm_num
        _  ≤  630+J/4 := add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
        _ = _ := add_comm _ _
    · exact Or.inr ⟨by linarith,by linarith,hz⟩

lemma move_path_contained (J : ℝ) (L i : ℕ) (hi : i ≤ L) (hJ : 26200 < J)
    (y x : ℝ×ℝ) (d e σ : ℝ) (hσ : |σ|=1) (he : 0 ≤ e)
    (hsmall : (L+1)*e+d < 1)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    x∈domain J (L+1/2) σ := by
  have hi' : (i : ℝ) ≤ L := by exact_mod_cast hi
  have hi₀ : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have heL : 0 ≤ (L+1)*e := mul_nonneg (by positivity) he
  apply band_mem_domain J (L+1/2) σ hσ x
  · rw [abs_le] at hyt hxt
    constructor  <;>  nlinarith
  · exact (path_axis_bound L i hi y x d e σ hσ he hyt hyz hxt hxz).trans (by linarith)

lemma last_crossing_height (L : ℕ) (y x : ℝ×ℝ) (d σ : ℝ) (hσ : |σ|=1)
    (hy : |y.2-σ*(L : ℝ)/4| ≤ 2+d) (hx : |x.2-y.2| ≤ 100) (hd : d < 1) :
    |x.2-σ*(L+1/2)/4| < 210 := by
  have he : σ*(L : ℝ)/4-σ*(L+1/2)/4=-σ/8 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(L : ℝ)/4|+|σ*(L : ℝ)/4-σ*(L+1/2)/4| :=
      by linarith [abs_sub_le x.2 (σ*(L : ℝ)/4) (σ*(L+1/2)/4),
        abs_sub_le x.2 y.2 (σ*(L : ℝ)/4)]
    _  ≤  100+(2+d)+1/8 := by
      rw [he,abs_div,abs_neg,hσ]
      norm_num
      linarith
    _  <  _ := by linarith

end CriticalPercolation.Relay
namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}

lemma exists_first_crossing (f : V → ℝ) (ρ T : ℝ)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y| ≤ ρ)
    {a b : V} (w : H.Walk a b) (ha : f a < T) (hb : T ≤ f b) :
    ∃ x∈w.support, T ≤ f x ∧ f x ≤ T+ρ := by
  induction w with
  | nil =>  exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T ≤ f c
    · refine ⟨c,?_,hc,?_⟩
      · simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]
        exact Or.inr w.start_mem_support
      · have hh := hf hac
        rw [abs_le] at hh
        linarith
    · obtain ⟨x,hx,h1,h2⟩ := ih (lt_of_not_ge hc) hb
      exact ⟨x,by simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx,h1,h2⟩
end SimpleGraph.Walk
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

lemma relay_collar_bounds (t z : V → ℝ) (σ e ρ : ℝ) (hρ : 0 ≤ ρ)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (R i : ℕ) {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    |t y-(i : ℝ)| ≤ (i+1)*e+R*ρ ∧ |z y-σ*(i : ℝ)/4| ≤ Relay.width i+R*ρ := by
  exact ⟨G.coordinate_collar_bound t ρ hρ ht _ _ _ (fun _ h => h.1) hy,
    G.coordinate_collar_bound z ρ hρ hz _ _ _ (fun _ h => h.2) hy⟩

lemma full_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i<L) (hsmall : (L+1)*e+R*ρ<1)
    (hheight : R*ρ+e/4 ≤ 1/4) (htime : R*ρ+e/4 ≤ e)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    coordinateMove G t z m e y (Relay.selectedSign (z y-σ*(i : ℝ)/4)) ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1))} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,hbz⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  have hb : b∈relayRegion t z σ e (i+1) := by
    refine ⟨?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
        Relay.full_step_time i (t y) (t b) (R*ρ) e hy'.1 hbt htime
    have hh := Relay.full_step_height i (z y-σ*(i : ℝ)/4) σ (R*ρ) e
      (z b-(z y+Relay.selectedSign (z y-σ*(i : ℝ)/4))) hσ hy'.2
      (mul_nonneg (Nat.cast_nonneg _) hρ) hheight hbz
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring_nf
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,b,G.walk_reachable_induced _ ω w ?_,hb⟩
  intro x hx
  exact Relay.move_path_contained J L i hi.le hJ (t y,z y) (t x,z x)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 (hw x hx).1 (hw x hx).2

lemma last_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hL : 416 ≤ L) (hsmall : (L+1)*e+(R+m)*ρ+e/4<1/2)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e L) R) (s : ℝ) :
    coordinateMove G t z m e y s ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ)} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,_⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R L hy
  have hma : |t a-t y| ≤ m*ρ := G.coordinate_ball_bound t ρ hρ ht ha
  have hnR : 0 ≤ (R : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnm : 0 ≤ (m : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnL : 0 ≤ (L+1 : ℝ)*e := mul_nonneg (by positivity) he
  have hyt := abs_le.mp hy'.1
  have hbt' := abs_le.mp hbt
  have hma' := abs_le.mp hma
  have haT : t a<L+1/2 := by linarith
  have hbT : (L : ℝ)+1/2 ≤ t b := by linarith
  have hadj : ∀ ⦃u v⦄, (G.openGraph ω).Adj u v → |t u-t v| ≤ ρ :=
    fun _ _ h => ht (G.openGraph_mono (Set.subset_univ _) h)
  obtain ⟨x,hx,hx₁,hx₂⟩ := _root_.OAI.SimpleGraph.Walk.exists_first_crossing t ρ (L+1/2) hadj w haT hbT
  have hxz : |z x-σ*(L+1/2)/4|<210 := by
    apply Relay.last_crossing_height L (t y,z y) (t x,z x) (R*ρ) σ hσ
    · simpa only [Relay.width_last L hL] using hy'.2
    · exact (hw x hx).2
    · linarith
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,?_,⟨hx₁,hx₂,hxz.le⟩⟩
  apply G.walk_reachable_induced _ ω (w.takeUntil x hx)
  intro v hv
  have hv' : v∈w.support := (w.isSubwalk_takeUntil hx).support_subset hv
  apply Relay.move_path_contained J L L le_rfl hJ (t y,z y) (t v,z v)
    (R*ρ) e σ hσ he _ hy'.1 hy'.2 (hw v hv').1 (hw v hv').2
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayScales
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

lemma vertexCollar_mono {S T : Set V} (hST : S⊆T) (R : ℕ) :
    G.vertexCollar S R⊆G.vertexCollar T R := by
  intro y hy
  obtain ⟨v,hv,hy⟩ := Set.mem_iUnion₂.mp hy
  exact Set.mem_iUnion₂.mpr ⟨v,hST hv,hy⟩

lemma initial_mark_subset_relay (t z : V → ℝ) (σ e ρ : ℝ) (hρ : ρ ≤ e) :
    relayMark t z 0 σ ρ⊆relayRegion t z σ e 0 := by
  intro v hv
  obtain ⟨ht₀,ht₁,hz⟩ := hv
  change |t v-(0:ℕ)| ≤ ((0:ℕ)+1)*e ∧ |z v-σ*(0:ℕ)/4| ≤ Relay.width 0
  norm_num [Relay.width] at ht₀ ht₁ hz ⊢
  exact ⟨by rw [abs_of_nonneg ht₀]; linarith,hz⟩

lemma relay_coordinate_scale (L R m : ℕ) (e ρ : ℝ) (he : 0<e) (hρ : 0 ≤ ρ)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) :
    ρ ≤ e ∧ (L+1)*e+R*ρ<1 ∧ R*ρ+e/4 ≤ 1/4 ∧ R*ρ+e/4 ≤ e ∧
      (L+1)*e+(R+m)*ρ+e/4<1/2 := by
  have hR : 0 ≤ (R:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hm : 0 ≤ (m:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hL : 0 ≤ (L:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he.le
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma relay_collar_in_domain (t z : V → ℝ) (σ e ρ J : ℝ) (L R i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i ≤ L) (hsmall : (L+1)*e+R*ρ<1)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ) :
    G.vertexCollar (relayRegion t z σ e i) R⊆relayDomain t z J (L+1/2) σ := by
  intro y hy
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  apply Relay.move_path_contained J L i hi hJ (t y,z y) (t y,z y)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 <;> norm_num

lemma forceOutside_induced (S : Set V) (ω : Set E) :
    BernoulliProduct.forceOn (G.inducedEdges S)ᶜ ∅ ω=ω∩G.inducedEdges S := by
  ext b
  by_cases hb : b∈G.inducedEdges S <;> simp [hb]

lemma corridorRelay_subset (t z : V → ℝ) (σ e ρ : ℝ) (hρe : ρ ≤ e)
    (L i : ℕ) (hi : i ≤ L) : corridorRelay t z σ e ρ L i⊆relayRegion t z σ e i := by
  by_cases h0 : i=0
  · subst i
    simpa [corridorRelay] using initial_mark_subset_relay t z σ e ρ hρe
  · simp only [corridorRelay,ite_eq_right h0,ite_eq_left hi,Subset.rfl]

theorem coordinate_moves_relay_estimates (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (p : unitInterval) (η : ℝ)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
      (G.coordinateMove t z m e y s)) :
    ∀ i ≤ L,
      G.vertexCollar (corridorRelay t z σ e ρ L i) R⊆relayDomain t z J (L+1/2) σ ∧
      ∀ y∈G.vertexCollar (corridorRelay t z σ e ρ L i) R,
        1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
          ((BernoulliProduct.forceOn (G.inducedEdges (relayDomain t z J (L+1/2) σ))ᶜ ∅) ⁻¹'
            G.seedHitEvent (G.vertexBall y m) (corridorRelay t z σ e ρ L (i+1))) := by
  obtain ⟨hρe,hsmall,hheight,htime,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  intro i hi
  have hsub := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R
  refine ⟨hsub.trans (G.relay_collar_in_domain t z σ e ρ J L R i hσ he.le hρ hJ hi hsmall ht hz),?_⟩
  intro y hy
  apply (hmove y (Relay.selectedSign (z y-σ*(i:ℝ)/4)) (Relay.selectedSign_abs _)).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  rw [Set.mem_preimage,G.forceOutside_induced]
  by_cases hiL : i<L
  · have hh := G.full_relay_move t z σ e ρ J L R m i hσ he.le hρ hJ hiL hsmall
      hheight htime ht hz (hsub hy) hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1)) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,ite_false, if_false,ite_eq_left (by omega : i+1 ≤ L)] using hh
  · have hiEq : i=L := by omega
    subst i
    have hh := G.last_relay_move t z σ e ρ J L R m hσ he.le hρ hJ hL hlast ht hz
      (hsub hy) _ hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,ite_false, if_false,ite_eq_right (by omega : ¬L+1 ≤ L)] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SourceRelaySeparation
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma source_outside_relay_collar (t z : V → ℝ) (σ e ρ P : ℝ) (L R m i : ℕ)
    (he : 0<e) (hρ : 0 ≤ ρ) (hi : i ≤ L) (hPi : 1 ≤ P+i)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {a : V} (ha : t a ≤ m*ρ-P) :
    a∉G.vertexCollar (corridorRelay t z σ e ρ L i) R := by
  intro hin
  obtain ⟨hρe,_,_,_,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  have hs := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R hin
  have hb := (G.relay_collar_bounds t z σ e ρ hρ ht hz R i hs).1
  have hi' : (i:ℝ) ≤ L := by exact_mod_cast hi
  have hile : (i+1)*e ≤ (L+1)*e := mul_le_mul_of_nonneg_right (by linarith) he.le
  have hb' := (abs_le.mp hb).1
  nlinarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_RelayProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation
variable {Ω : Type*} [MeasurableSpace Ω]

lemma relay_failure_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (κ : ℝ) (N : ℕ)
    (h : ∀ i<N, μ.real (A i\A (i+1)) ≤ κ) :
    μ.real (A 0\A N) ≤ N*κ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsub : A 0\A (N+1) ⊆ (A 0\A N)∪(A N\A (N+1)) := by
      intro ω hω
      by_cases hn : ω∈A N
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    calc
      _ ≤ μ.real ((A 0\A N)∪(A N\A (N+1))) := measureReal_mono hsub
      _ ≤ μ.real (A 0\A N)+μ.real (A N\A (N+1)) := measureReal_union_le _ _
      _ ≤ N*κ+κ := add_le_add (ih (fun i hi => h i (by omega))) (h N (by omega))
      _ = _ := by push_cast <;> ring

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_FreshCorridor
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem coordinate_corridor_failure (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (t z : V → ℝ) (σ e ρ J P : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (hP : 1 ≤ P) (hsource : ∀ a∈A, t a ≤ m*ρ-P)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q (Sum.inl b)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law q).real
      ((G.withSource A).hitEvent none (some '' relayMark t z 0 σ ρ)\
        (G.withSource A).hitEvent none (some '' relayMark t z (L+1/2) σ ρ)) ≤ (L+1)*κ := by
  let H : ℕ → Set (Set (E⊕A)) := fun i =>
    (G.withSource A).hitEvent none (some '' corridorRelay t z σ e ρ L i)
  have hh := relay_failure_bound (BernoulliProduct.law q) H κ (L+1) (by
    intro i hi
    have hiL : i ≤ L := by omega
    obtain ⟨hcoll,hmean⟩ := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
      hσ he hρ hJ hL heL hr ht hz p' η hmove i hiL
    apply G.fresh_collar_transfer hc hl A _ _ hA q m R hcR
      (G.inducedEdges (relayDomain t z J (L+1/2) σ))
      (fun a ha => G.source_outside_relay_collar t z σ e ρ P L R m i he hρ hiL
        (by linarith [Nat.cast_nonneg (α := ℝ) i]) heL hr ht hz (hsource a ha))
      (G.inducedEdges_mono hcoll) pc p' hpc₀ hpc hpp hppc hq D k M VM hD hM hMbound hVM
      κ η hκ hκ1 hη₀ hη hk hR hmean)
  simpa [H,corridorRelay,show ¬L+1 ≤ L by omega] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SourceConnectivity
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
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma withSource_reachable_from_seed (A : Set V) (ω : Set (E⊕A))
    (hw : ∀ a : A, Sum.inr a∈ω) {v : V}
    (hv : ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v) :
    ((G.withSource A).openGraph ω).Reachable none (some v) := by
  obtain ⟨a,ha,hav⟩ := hv
  have hh : ((G.withSource A).openGraph ω).Adj none (some a) :=
    ⟨⟨Sum.inr ⟨a,ha⟩,hw ⟨a,ha⟩,rfl⟩,by simp⟩
  exact hh.reachable.trans (G.withSource_original_reachable A ω hav)

lemma withSource_reachable_to_seed (A : Set V) (ω : Set (E⊕A)) {v : V}
    (hv : ((G.withSource A).openGraph ω).Reachable none (some v)) :
    ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v := by
  have hi : ∀ w, ((G.withSource A).openGraph ω).Reachable none w →
      Option.elim' True (fun v => ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v) w := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => trivial
    | @tail u w hr huw ih =>
      obtain ⟨⟨b,hb,hend⟩,hne⟩ := huw
      cases w with
      | none => trivial
      | some w =>
        rcases G.withSource_edge_cases A b u (some w) hend with
          ⟨b,v,w',rfl,rfl,hw',hb'⟩|⟨a,rfl,hh⟩
        · have he : w'=w := Option.some.inj hw'.symm
          subst w'
          obtain ⟨a,ha,hav⟩ := ih
          refine ⟨a,ha,hav.trans ?_⟩
          exact (show (G.openGraph (Sum.inl ⁻¹' ω)).Adj v w from
            ⟨⟨b,hb,hb'⟩,fun h => hne (congrArg some h)⟩).reachable
        · rcases hh with ⟨rfl,hh⟩|⟨hh,_⟩
          · have he : w=a.val := Option.some.inj hh
            exact ⟨a.val,a.property,he.symm ▸ SimpleGraph.Reachable.refl _⟩
          · simp at hh
  exact hi (some v) hv

lemma source_hit_iff_seedHit (A T : Set V) (ω : Set (E⊕A))
    (hw : ∀ a : A, Sum.inr a∈ω) :
    ω∈(G.withSource A).hitEvent none (some '' T) ↔
      Sum.inl ⁻¹' ω∈G.seedHitEvent A T := by
  constructor
  · rintro ⟨w,hr,v,hv,rfl⟩
    obtain ⟨a,ha,hav⟩ := G.withSource_reachable_to_seed A ω hr
    exact Set.mem_iUnion₂.mpr ⟨a,ha,v,hav,hv⟩
  · intro h
    obtain ⟨a,ha,v,hav,hv⟩ := Set.mem_iUnion₂.mp h
    exact ⟨some v,G.withSource_reachable_from_seed A ω hw ⟨a,ha,hav⟩,v,hv,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_SourceEventLaw
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
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
lemma source_hit_ae_seed (A T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    (G.withSource A).hitEvent none (some '' T) =ᵐ[BernoulliProduct.law q]
      ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent A T) := by
  have ha (a : A) : ∀ᵐ ω ∂BernoulliProduct.law q, Sum.inr a∈ω := by
    rw [ae_iff]
    have he : {ω : Set (E⊕A) | ¬Sum.inr a∈ω}={ω | (Sum.inr a∈ω)=False} := by
      ext ω; simp
    rw [he,law_coordinate,hq a]
    simp [bitMeasure]
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  exact propext (G.source_hit_iff_seedHit A T ω hω)

lemma source_hit_diff_probability (A B T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' B)\
      (G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law (fun b => q (Sum.inl b)) (G.seedHitEvent A B\G.seedHitEvent A T) := by
  have heq : BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' B)\
      (G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law q ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹'
        (G.seedHitEvent A B\G.seedHitEvent A T)) := by
    apply measure_congr
    filter_upwards [G.source_hit_ae_seed A B q hq,G.source_hit_ae_seed A T q hq] with ω hB hT
    exact propext (and_congr (eq_iff_iff.mp hB) (not_congr (eq_iff_iff.mp hT)))
  rw [heq]
  change BernoulliProduct.law q ((fun ω : Set (E⊕A) => fun b => Sum.inl b∈ω) ⁻¹' _)=_
  rw [← Measure.map_apply (Measurable.of_eval (fun bond => measurable_set_mem (Sum.inl bond)))
    ((G.measurableSet_seedHitEvent A B).diff (G.measurableSet_seedHitEvent A T))]
  change (Measure.map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) (BernoulliProduct.law q)) _=_
  rw [law_map_preimage q Sum.inl Sum.inl_injective]
  rfl

lemma restricted_seed_diff_probability (A B T : Set V) (q : E → unitInterval) (R : Set E) :
    BernoulliProduct.law q (G.restrictedSeed A B R\G.restrictedSeed A T R)=
      BernoulliProduct.law (pinnedParameters q Rᶜ ∅) (G.seedHitEvent A B\G.seedHitEvent A T) := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn _ _)
    ((G.measurableSet_seedHitEvent A B).diff (G.measurableSet_seedHitEvent A T))]
  congr 1
  have he (ω : Set E) : forceOn Rᶜ ∅ ω=ω∩R := by
    ext e
    by_cases he : e∈R <;> simp [he]
  ext ω
  simp only [Set.mem_sdiff,Set.mem_preimage,restrictedSeed,Set.mem_ofPred_eq,he]

lemma restricted_seed_diff_le_source (A B T : Set V) (q : E → unitInterval)
    (I F R σ : Set E) (hFR : F⊆R) :
    (blockProbability q I (G.restrictedSeed A B F\G.restrictedSeed A T R) σ).toReal ≤
      (BernoulliProduct.law (Sum.elim (pinnedParameters (pinnedParameters q I σ) Rᶜ ∅)
        (fun _ : A => 1))).real
        ((G.withSource A).hitEvent none (some '' B)\(G.withSource A).hitEvent none (some '' T)) := by
  rw [blockProbability_eq_pinnedLaw q I σ _
    ((G.restrictedSeed_measurable _ _ _).diff (G.restrictedSeed_measurable _ _ _))]
  rw [measureReal_def,G.source_hit_diff_probability A B T _ (fun _ => rfl)]
  change (BernoulliProduct.law (pinnedParameters q I σ)).real _ ≤
    (BernoulliProduct.law (pinnedParameters (pinnedParameters q I σ) Rᶜ ∅)).real _
  rw [measureReal_def,measureReal_def,← G.restricted_seed_diff_probability]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  exact Set.sdiff_subset_sdiff_left (G.restrictedSeed_mono A B hFR)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ProspectiveCorridor
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
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem coordinate_pinned_corridor_failure (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A : Set V) (hA : A.Finite) (q : E → unitInterval)
    (I F U ω : Set E) (hFU : F⊆U)
    (t z : V → ℝ) (σ e ρ J P : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (hP : 1 ≤ P) (hsource : ∀ a∈A, t a ≤ m*ρ-P)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q b=p')
    (hDU : G.inducedEdges (relayDomain t z J (L+1/2) σ)⊆U)
    (hfresh : Disjoint I (G.inducedEdges (relayDomain t z J (L+1/2) σ)))
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.blockProbability q I
      (G.restrictedSeed A (relayMark t z 0 σ ρ) F\
        G.restrictedSeed A (relayMark t z (L+1/2) σ ρ) U) ω).toReal ≤ (L+1)*κ := by
  let r : E → unitInterval := pinnedParameters (pinnedParameters q I ω) Uᶜ ∅
  let q' : (E⊕A) → unitInterval := Sum.elim r (fun _ => 1)
  have hq' : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q' (Sum.inl b)=p' := by
    intro b hb
    have hbU := hDU hb
    have hbI : b∉I := fun hi => Set.disjoint_left.mp hfresh hi hb
    simpa [q',r,pinnedParameters,hbU,hbI] using hq b hb
  exact (G.restricted_seed_diff_le_source A _ _ q I F U ω hFU).trans
    (G.coordinate_corridor_failure hc hl A hA q' t z σ e ρ J P L R m
      hσ he hρ hJ hL heL hr hP hsource ht hz hcR pc p' hpc₀ hpc hpp hppc hq'
      D k M VM hD hM hMbound hVM κ η hκ hκ1 hη₀ hη hk hR hmove)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorNormalization
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

namespace CriticalPercolation.Corridor
open BondGraph

variable {V : Type*}

lemma sign_abs (b : Bool) : |sign b|=1 := by cases b <;> norm_num [sign]

lemma timeCenter_target (T : ℝ) (v : Site) (b : Bool) :
    timeCenter T (target (v,b))=timeCenter T v+T := by
  cases b <;> simp [target,timeCenter] <;> ring

lemma heightCenter_target (T : ℝ) (v : Site) (b : Bool) :
    heightCenter T (target (v,b))=heightCenter T v+sign b*T/4 := by
  cases b <;> simp [target,heightCenter,sign] <;> ring

lemma normalized_box (t z : V → ℝ) (T J : ℝ) (hT : 0<T) (v : Site) :
    graphBox (normalized t z T) (J/T) (2520/T) v=
      {x | |localTime t T v x|≤J ∧ |localHeight z T v x|≤J/4+630} := by
  ext x
  change (|t x/T-((v.1 : ℝ)+v.2)|≤J/T ∧
    |4*z x/T-((v.1 : ℝ)-v.2)|≤J/T+2520/T) ↔ _
  have ht : t x/T-((v.1 : ℝ)+v.2)=localTime t T v x/T := by
    dsimp [localTime,timeCenter]; field_simp
  have hz : 4*z x/T-((v.1 : ℝ)-v.2)=4*localHeight z T v x/T := by
    dsimp [localHeight,heightCenter]; field_simp
  rw [ht,hz,abs_div,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
    show J/T+2520/T=(J+2520)/T by ring,div_le_div_iff_of_pos_right hT,
    abs_mul,show |(4 : ℝ)|=4 by norm_num]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨ht,hz⟩ <;> exact ⟨ht,by linarith⟩

lemma normalized_tube (t z : V → ℝ) (T : ℝ) (hT : 0<T) (v : Site) (b : Bool) :
    (normalized t z T) ⁻¹' tube (2520/T) (v,b)=
      {x | 0≤localTime t T v x ∧ localTime t T v x≤T ∧
        |localHeight z T v x-sign b*localTime t T v x/4|≤630} := by
  ext x
  have ht : ((v.1 : ℝ)+v.2≤t x/T) ↔ 0≤localTime t T v x := by
    rw [le_div_iff₀ hT]; dsimp [localTime,timeCenter]; constructor <;> intro h <;> linarith
  have ht' : (t x/T≤(v.1 : ℝ)+v.2+1) ↔ localTime t T v x≤T := by
    rw [div_le_iff₀ hT]; dsimp [localTime,timeCenter]; constructor <;> intro h <;> nlinarith
  cases b with
  | true =>
    change (((v.1 : ℝ)+v.2≤t x/T) ∧ (t x/T≤(v.1 : ℝ)+v.2+1) ∧
      |4*z x/T-(t x/T-2*(v.2 : ℝ))|≤2520/T) ↔ _
    have he : 4*z x/T-(t x/T-2*(v.2 : ℝ))=
        4*(localHeight z T v x-sign true*localTime t T v x/4)/T := by
      dsimp [localHeight,heightCenter,localTime,timeCenter,sign]; field_simp <;> ring
    rw [ht,ht',he,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
      abs_mul,show |(4 : ℝ)|=4 by norm_num]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨ha,hb,by linarith⟩
  | false =>
    change (((v.1 : ℝ)+v.2≤t x/T) ∧ (t x/T≤(v.1 : ℝ)+v.2+1) ∧
      |4*z x/T-(2*(v.1 : ℝ)-t x/T)|≤2520/T) ↔ _
    have he : 4*z x/T-(2*(v.1 : ℝ)-t x/T)=
        4*(localHeight z T v x-sign false*localTime t T v x/4)/T := by
      dsimp [localHeight,heightCenter,localTime,timeCenter,sign]; field_simp <;> ring
    rw [ht,ht',he,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
      abs_mul,show |(4 : ℝ)|=4 by norm_num]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨ha,hb,by linarith⟩

lemma normalized_domain (t z : V → ℝ) (T J : ℝ) (hT : 0<T) (v : Site) (b : Bool) :
    graphDomain (normalized t z T) (J/T) (2520/T) (v,b)=
      relayDomain (localTime t T v) (localHeight z T v) J T (sign b) := by
  change (normalized t z T) ⁻¹' (box _ _ v∪box _ _ (target (v,b))∪tube _ (v,b))=_
  rw [Set.preimage_union,Set.preimage_union]
  change graphBox _ _ _ v∪graphBox _ _ _ (target (v,b))∪_=_
  rw [normalized_box t z T J hT,normalized_box t z T J hT,normalized_tube t z T hT]
  ext x
  change ((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _)
  simp only [localTime,localHeight,timeCenter_target,heightCenter_target,sub_add_eq_sub_sub]

lemma mark_initial (t z : V → ℝ) (T ρ : ℝ) (v : Site) (b : Bool) :
    relayMark (localTime t T v) (localHeight z T v) 0 (sign b) ρ=mark t z T ρ v := by
  ext x
  simp only [relayMark,mark,Set.mem_ofPred_eq,mul_zero,zero_div,sub_zero,zero_add]

lemma mark_target (t z : V → ℝ) (T ρ : ℝ) (v : Site) (b : Bool) :
    relayMark (localTime t T v) (localHeight z T v) T (sign b) ρ=mark t z T ρ (target (v,b)) := by
  ext x
  change (T≤localTime t T v x ∧ localTime t T v x≤T+ρ ∧
    |localHeight z T v x-sign b*T/4|≤210) ↔ _
  change _ ↔ (0≤localTime t T (target (v,b)) x ∧ localTime t T (target (v,b)) x≤ρ ∧
    |localHeight z T (target (v,b)) x|≤210)
  simp only [localTime,localHeight,timeCenter_target,heightCenter_target]
  have he : z x-heightCenter T v-sign b*T/4=z x-(heightCenter T v+sign b*T/4) := by ring
  rw [he]
  constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨by linarith,by linarith,hc⟩

lemma coordinateMove_translate {E : Type*} (G : BondGraph V E) (t z : V → ℝ)
    (T : ℝ) (v : Site) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) :
    G.coordinateMove (localTime t T v) (localHeight z T v) m e y s=
      G.coordinateMove t z m e y s := by
  unfold coordinateMove localTime localHeight
  simp only [sub_sub_sub_cancel_right]
  have ht : ∀ b, t b-timeCenter T v-(t y-timeCenter T v+1)=t b-(t y+1) := by intro b; ring
  have hz : ∀ b, z b-heightCenter T v-(z y-heightCenter T v+s)=z b-(z y+s) := by intro b; ring
  simp only [ht,hz]

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_CoordinateScheme
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

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

namespace CoordinateData
variable {V E : Type*} (C : CoordinateData V E)

lemma T_pos : 0<C.T := by unfold T; positivity

lemma L_large (h : C.Bounds) : 416≤C.L := by
  have : (416 : ℝ)≤C.L := by linarith [h.J_lower,h.L_lower]
  exact_mod_cast this

lemma layout (h : C.Bounds) :
    0≤C.scheme.h ∧ C.scheme.h≤C.scheme.j ∧ 2*C.scheme.j+C.scheme.h<1 := by
  change 0≤2520/C.T ∧ 2520/C.T≤C.J/C.T ∧ 2*(C.J/C.T)+2520/C.T<1
  refine ⟨div_nonneg (by norm_num) C.T_pos.le, (div_le_div_iff_of_pos_right C.T_pos).mpr (by linarith [h.J_lower]),?_⟩
  rw [show 2*(C.J/C.T)+2520/C.T=(2*C.J+2520)/C.T by ring,div_lt_one C.T_pos]
  dsimp [T]
  linarith [h.J_lower,h.L_lower]

lemma domain_eq (v : Site) (b : Bool) : C.scheme.edgeDomain (v,b)=
    C.graph.inducedEdges (relayDomain (localTime C.time C.T v) (localHeight C.height C.T v)
      C.J C.T (sign b)) := by
  change C.graph.inducedEdges (graphDomain (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T) (v,b))=_
  rw [normalized_domain C.time C.height C.T C.J C.T_pos]

lemma local_time_step (h : C.Bounds) (v : Site) {u w : V} (huw : C.graph.fullGraph.Adj u w) :
    |localTime C.time C.T v u-localTime C.time C.T v w|≤C.rho := by
  simpa only [localTime,sub_sub_sub_cancel_right] using h.time_step huw

lemma local_height_step (h : C.Bounds) (v : Site) {u w : V} (huw : C.graph.fullGraph.Adj u w) :
    |localHeight C.height C.T v u-localHeight C.height C.T v w|≤C.rho := by
  simpa only [localHeight,sub_sub_sub_cancel_right] using h.height_step huw

lemma source_behind (h : C.Bounds) (n : ℕ) (hn : 0<n) :
    ∀ a∈C.scheme.seed, localTime C.time C.T (slotSite n) a≤C.m*C.rho-C.T := by
  intro a ha
  have ht := (abs_le.mp (C.graph.coordinate_ball_bound C.time C.rho h.rho_nonneg h.time_step ha)).2
  rw [h.time_origin,sub_zero] at ht
  have hv := slotSite_quadrant n
  have hnz : slotSite n≠(0,0) := by
    intro he
    have he' := congrArg gridSlot he
    rw [gridSlot_slotSite] at he'
    change n=0 at he'
    omega
  have hsumInt : 1≤(slotSite n).1+(slotSite n).2 := by
    by_contra hs
    have hx : (slotSite n).1=0 := by dsimp [quadrant] at hv; omega
    have hy : (slotSite n).2=0 := by dsimp [quadrant] at hv; omega
    exact hnz (Prod.ext hx hy)
  have hsum : (1 : ℝ)≤((slotSite n).1 : ℝ)+(slotSite n).2 := by exact_mod_cast hsumInt
  have hmul := mul_le_mul_of_nonneg_right hsum C.T_pos.le
  change C.time a-(((slotSite n).1 : ℝ)+(slotSite n).2)*C.T≤_
  linarith

end CoordinateData
end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CoordinateProspective
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val
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

namespace CriticalPercolation.Corridor.CoordinateData
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (C : CoordinateData V E)

lemma active_slot_positive (n : ℕ) (S : GrowthState) (hv : S.Valid n)
    (ha : (incoming n S.good).isSome) : 0<n := by
  obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha
  have ht := parent_slot_lt e (hv.2.1 _ (incoming_source he)).1
  rw [incoming_target he,gridSlot_slotSite] at ht
  omega

theorem prospective_estimate_oai (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s))
    (n : ℕ) (S : GrowthState) (hv : S.Valid n) (_hc : S.Covered)
    (ha : (incoming n S.good).isSome) (ω : Set E) (b : Bool) :
    (blockProbability C.scheme.parameter (C.scheme.block S)
      (C.scheme.incomingHit n S\C.scheme.nextHit n S b) ω).toReal≤(C.L+1)*C.kappa := by
  let v := slotSite n
  let F := C.scheme.enlarged n S
  let U := F∪C.scheme.edgeDomain (v,b)
  have hdom := C.domain_eq v b
  have hDU : C.graph.inducedEdges (relayDomain (localTime C.time C.T v)
      (localHeight C.height C.T v) C.J C.T (sign b))⊆U := by
    rw [← hdom]
    exact Set.subset_union_right
  have hfresh : Disjoint (C.scheme.block S)
      (C.graph.inducedEdges (relayDomain (localTime C.time C.T v)
        (localHeight C.height C.T v) C.J C.T (sign b))) := by
    rw [← hdom]
    exact outgoing_unrevealed C.graph (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T)
      (C.layout h).1 (C.layout h).2.1 (C.layout h).2.2 n S hv (active_slot_positive n S hv ha) rfl
  have hmoves : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove (localTime C.time C.T v) (localHeight C.height C.T v)
        C.m C.e y s) := by
    intro y s hs
    rw [coordinateMove_translate]
    exact hmove y s hs
  have hP : 1≤C.T := by
    have hh : (416 : ℝ)≤C.L := by exact_mod_cast C.L_large h
    dsimp [T] <;> linarith
  have hh := C.graph.coordinate_pinned_corridor_failure h.connected h.locallyFinite
    C.scheme.seed (C.graph.vertexBall_finite h.locallyFinite C.origin C.m) C.scheme.parameter
    (C.scheme.block S) F U ω Set.subset_union_left
    (localTime C.time C.T v) (localHeight C.height C.T v) (sign b) C.e C.rho C.J C.T
    C.L C.R C.m (sign_abs b) h.e_pos h.rho_nonneg h.J_lower (C.L_large h) h.e_small h.rho_small
    hP (C.source_behind h n (active_slot_positive n S hv ha))
    (fun {_ _} hh => C.local_time_step h v hh) (fun {_ _} hh => C.local_height_step h v hh) h.R_gt C.pc C.p h.pc_pos h.pc_lt
    h.p_lower h.p_upper (fun _ _ => rfl) hDU hfresh C.D C.k C.M C.VM h.degree h.M_pos
    h.M_bound h.VM_bound C.kappa C.eta h.kappa_pos h.kappa_le h.eta_nonneg h.eta_small
    h.k_large h.R_large hmoves
  change (blockProbability C.scheme.parameter (C.scheme.block S)
    (C.graph.restrictedSeed C.scheme.seed (relayMark (localTime C.time C.T v) (localHeight C.height C.T v) 0 (sign b) C.rho) F\
      C.graph.restrictedSeed C.scheme.seed (relayMark (localTime C.time C.T v) (localHeight C.height C.T v) C.T (sign b) C.rho) U) ω).toReal≤_ at hh
  rw [mark_initial,mark_target] at hh
  exact hh

end CriticalPercolation.Corridor.CoordinateData
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.Corridor.CoordinateData.prospective_estimate_oai.{u_1, u_2} := @OAI.CriticalPercolation.Corridor.CoordinateData.prospective_estimate_oai.{u_1, u_2}
