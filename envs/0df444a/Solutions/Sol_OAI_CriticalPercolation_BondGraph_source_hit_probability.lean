-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.source_hit_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:11.915076+00:00
-- url     : https://prove2.me/submissions/01eb6ab4-119c-4bd0-ad01-273398760a6b

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001

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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SourceConnectivity
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

lemma source_hit_probability_oai [Countable V] [Countable E] (A T : Set V)
    (q : (E⊕A) → unitInterval) (hq : ∀ a : A, q (Sum.inr a)=1) :
    BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law (fun b => q (Sum.inl b)) (G.seedHitEvent A T) := by
  have ha (a : A) : ∀ᵐ ω ∂BernoulliProduct.law q, Sum.inr a∈ω := by
    rw [ae_iff]
    have he : {ω : Set (E⊕A) | ¬Sum.inr a∈ω}={ω | (Sum.inr a∈ω)=False} := by
      ext ω; simp
    rw [he,BernoulliProduct.law_coordinate,hq a]
    simp [BernoulliProduct.bitMeasure]
  have hall : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ a : A, Sum.inr a∈ω := ae_all_iff.mpr ha
  have heq : BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law q ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent A T) := by
    apply measure_congr
    filter_upwards [hall] with ω hω
    exact propext (G.source_hit_iff_seedHit A T ω hω)
  rw [heq]
  change BernoulliProduct.law q ((fun ω : Set (E⊕A) => fun b => Sum.inl b∈ω) ⁻¹' G.seedHitEvent A T)=_
  rw [← Measure.map_apply
    (Measurable.of_eval (fun bond => measurable_set_mem (Sum.inl bond)))
    (G.measurableSet_seedHitEvent A T)]
  change (Measure.map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) (BernoulliProduct.law q)) (G.seedHitEvent A T)=_
  rw [BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective]
  rfl

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.source_hit_probability_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.source_hit_probability_oai.{u_1, u_2}
