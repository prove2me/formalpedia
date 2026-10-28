-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:53:27.664166+00:00
-- url     : https://prove2.me/submissions/9aa42406-cd05-4383-8622-06247ae46861

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology


private theorem subset_edgeExhaustion [Encodable E] (s : Finset E) :
    ∃ n, s ⊆ edgeExhaustion n := by
  refine ⟨s.sup Encodable.encode + 1, ?_⟩
  intro e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup he)

 theorem witness_eq_union [Encodable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hf : FiniteWitness A) :
    A = ⋃ n, {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hω
    obtain ⟨s, hs, hsa⟩ := hf ω hω
    obtain ⟨n, hn⟩ := subset_edgeExhaustion s
    exact ⟨n, hA (fun _ he => ⟨hs he, hn he⟩) hsa⟩
  · rintro ⟨n, hn⟩
    exact hA Set.inter_subset_left hn



end WitnessAssociation

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hfA : FiniteWitness A) : MeasurableSet A := by
  let := Encodable.ofCountable E
  rw [witness_eq_union A hA hfA]
  apply MeasurableSet.iUnion
  intro n
  let s := edgeExhaustion (E := E) n
  have he : {ω : Set E | ω ∩ (s : Set E) ∈ A} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ A} := by
    ext ω
    change ω ∩ (s : Set E) ∈ A ↔ Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) ∈ A
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) = ω ∩ (s : Set E) := by
      ext e
      simp [and_comm]
    rw [hi]
  change MeasurableSet {ω : Set E | ω ∩ (s : Set E) ∈ A}
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem finiteWitness_conn (G : BondGraph V E) (x y : V) :
    FiniteWitness {ω | Conn G ω x y} := by
  intro ω h
  induction h with
  | refl => exact ⟨∅, by simp, by simp⟩
  | @tail b c hab hbc ih =>
    obtain ⟨s, hs, hconn⟩ := ih
    obtain ⟨e, he, hGe⟩ := hbc
    refine ⟨insert e s, ?_, ?_⟩
    · simpa only [Finset.coe_insert] using Set.insert_subset he hs
    · exact (conn_mono G (by simp) hconn).tail ⟨e, by simp, hGe⟩

end ClusterEvents

section Automorphisms
attribute [local instance] Classical.propDecidable


theorem finite_open_probability (p : unitInterval) (s : Finset E) :
    (law p).real {ω | (s : Set E) ⊆ ω} = (p : ℝ) ^ s.card := by
  have he : {ω : Set E | (s : Set E) ⊆ ω} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹' {Set.univ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => Set.eq_univ_of_forall fun e => h e.property,
      fun h e he => show (⟨e, he⟩ : (s : Set E)) ∈ (Subtype.val ⁻¹' ω) from
        h.symm ▸ Set.mem_univ _⟩
  unfold Measure.real
  rw [he, ← Measure.map_apply (measurable_set_restrict _) (by measurability),
    law_map_restrict]
  change (law p : Measure (Set (s : Set E))).real {Set.univ} = _
  simp [law, setBernoulli_real_singleton p (Set.Subset.refl _) (Set.toFinite _)]

end Automorphisms

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Sharpness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq


theorem internalEdges_mono (G : BondGraph V E) {S T : Set V} (h : S ⊆ T) :
    internalEdges G S ⊆ internalEdges G T := fun _ he x hx => h (he x hx)

end SharpnessSusceptibility

end Percolation

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

lemma Aut.vertexBall_image (φ : G.Aut) (o : V) (n : ℕ) :
    φ.vertex '' G.vertexBall o n = G.vertexBall (φ.vertex o) n := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using
    (Aut.vertexBall_mem G φ o w n).symm

lemma Aut.vertexBall_ncard (φ : G.Aut) (o : V) (n : ℕ) :
    (G.vertexBall (φ.vertex o) n).ncard = (G.vertexBall o n).ncard := by
  rw [← Aut.vertexBall_image G φ,Set.ncard_image_of_injective _ φ.vertex.injective]

lemma uniform_ball_bound (hquasi : G.QuasiTransitive) (n : ℕ) :
    ∃ M : ℕ, ∀ v, (G.vertexBall v n).ncard ≤ M := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  refine ⟨∑ v ∈ hS.toFinset, (G.vertexBall v n).ncard,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [Aut.vertexBall_ncard G φ]
  exact Finset.single_le_sum (f := fun v => (G.vertexBall v n).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ContinuousExpectWeights
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

lemma stabilizerWeight_ne_top (o x : V) : G.stabilizerWeight o x ≠ ∞ :=
  ENNReal.ofReal_ne_top

lemma stabilizerWeight_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : 0 < G.stabilizerWeight o x :=
  ENNReal.ofReal_pos.mpr (G.modularRatio_pos hc hl x o)

@[simp] lemma stabilizerWeight_self (o : V) : G.stabilizerWeight o o = 1 := by
  simp [stabilizerWeight,modularRatio_self]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularIncidence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma incidence_stabilizerOrbit_subset_ball (v w : V) (n : ℕ) (hw : w∈G.vertexBall v n) :
    G.stabilizerOrbit v w ⊆ G.vertexBall v n := by
  intro z hz
  obtain ⟨φ,hv,hwz⟩ := G.mem_stabilizerOrbit.mp hz
  have h := (Aut.vertexBall_mem G φ v w n).mpr hw
  simpa only [hv,hwz] using h

lemma stabilizerWeight_le_ball_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) {v w : V}
    (_hw : w∈G.vertexBall v 1) (hv : v∈G.vertexBall w 1) :
    G.stabilizerWeight v w ≤ K := by
  unfold stabilizerWeight modularRatio
  apply ENNReal.ofReal_le_of_le_toReal
  simp only [ENNReal.toReal_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl v w))).mpr
  have hnum : G.suborbitCard w v ≤ K :=
    (Set.ncard_le_ncard (G.incidence_stabilizerOrbit_subset_ball w v 1 hv)
      (G.vertexBall_finite hl w 1)).trans (hK w)
  have hden : (1:ℝ)≤G.suborbitCard v w := by exact_mod_cast G.suborbitCard_pos hc hl v w
  exact (Nat.cast_le.mpr hnum).trans (by nlinarith [show (0:ℝ)≤K by positivity])

lemma common_bond_ball_one {v w : V} {e : E} (hv : v∈G.ends e) (hw : w∈G.ends e) :
    w∈G.vertexBall v 1 := by
  by_cases he : v=w
  · subst w
    exact G.mem_vertexBall_self v 1
  · apply G.vertexBall_step (G.mem_vertexBall_self v 0)
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨?_,he⟩
    refine ⟨e,Set.mem_univ e,?_⟩
    exact (Sym2.mem_and_mem_iff he).mp ⟨hv,hw⟩

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

lemma modularLogHeight_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : G.modularLogHeight y x = -G.modularLogHeight x y := by
  have h := G.modularLogHeight_change_base hc hl x y x
  rw [G.modularLogHeight_self] at h
  linarith

lemma Aut.modularLogHeight (φ : G.Aut) (x y : V) :
    G.modularLogHeight (φ.vertex x) (φ.vertex y) = G.modularLogHeight x y := by
  simp only [CriticalPercolation.BondGraph.modularLogHeight,Aut.modularRatio]

lemma modularLogHeight_eq_log_weight (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : G.modularLogHeight x y = Real.log (G.stabilizerWeight x y).toReal := by
  rw [stabilizerWeight,ENNReal.toReal_ofReal (G.modularRatio_pos hc hl y x).le]
  rfl

lemma modularLogHeight_le_log_ball_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) (x y : V)
    (hxy : y ∈ G.vertexBall x 1) (hyx : x ∈ G.vertexBall y 1) :
    G.modularLogHeight x y ≤ Real.log (K : ℝ) := by
  rw [G.modularLogHeight_eq_log_weight hc hl]
  apply Real.log_le_log (ENNReal.toReal_pos (G.stabilizerWeight_pos hc hl x y).ne'
    (G.stabilizerWeight_ne_top x y))
  simpa only [ENNReal.toReal_natCast,ENNReal.coe_toReal,NNReal.coe_natCast] using ENNReal.toReal_mono ENNReal.coe_ne_top
    (G.stabilizerWeight_le_ball_bound hc hl K hK hxy hyx)

lemma modularLogHeight_edge_jump (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) (o x y : V) (e : E)
    (hx : x ∈ G.ends e) (hy : y ∈ G.ends e) :
    |G.modularLogHeight o y - G.modularLogHeight o x| ≤ Real.log (K : ℝ) := by
  rw [G.modularLogHeight_change_base hc hl o x y,add_sub_cancel_left,abs_le]
  constructor
  · have h := G.modularLogHeight_le_log_ball_bound hc hl K hK y x
      (G.common_bond_ball_one hy hx) (G.common_bond_ball_one hx hy)
    rw [G.modularLogHeight_reverse hc hl] at h
    linarith
  · exact G.modularLogHeight_le_log_ball_bound hc hl K hK x y
      (G.common_bond_ball_one hx hy) (G.common_bond_ball_one hy hx)

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

lemma orbitAdjustedHeight_sub_bound (a : V → ℝ) (m M : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x ∧ a x ≤ M) (x y : V) :
    |G.orbitAdjustedHeight a x y - G.modularLogHeight x y| ≤ Real.log M - Real.log m := by
  have hxlo := Real.log_le_log hm (ha x).1
  have hylo := Real.log_le_log hm (ha y).1
  have hxhi := Real.log_le_log (hm.trans_le (ha x).1) (ha x).2
  have hyhi := Real.log_le_log (hm.trans_le (ha y).1) (ha y).2
  have he : G.orbitAdjustedHeight a x y-G.modularLogHeight x y = Real.log (a y)-Real.log (a x) := by
    unfold orbitAdjustedHeight
    ring
  rw [he,abs_le]
  constructor <;> linarith

end CriticalPercolation.BondGraph

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

theorem stationaryOrbitWeight_uniform_bounds [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ G.stationaryOrbitWeight μ x ∧
      G.stationaryOrbitWeight μ x ≤ M := by
  let : Nonempty G.VertexOrbit := ⟨G.vertexOrbit (Classical.arbitrary V)⟩
  let w : G.VertexOrbit → ℝ := fun i => G.stationaryOrbitWeight μ i.out
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ
    (show G.VertexOrbit → OrderDual ℝ from w) Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  refine ⟨w i,w j,G.stationaryOrbitWeight_pos hc hl μ hμ i.out,fun x => ?_⟩
  rw [G.stationaryOrbitWeight_out μ x]
  exact ⟨hi (G.vertexOrbit x) (Finset.mem_univ _),hj (G.vertexOrbit x) (Finset.mem_univ _)⟩

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFreshSelection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E ι : Type*}

lemma measure_inter_of_separate_blocks (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hdA : DependsOn (fun ω => ω ∈ A) S)
    (hdB : DependsOn (fun ω => ω ∈ B) Sᶜ) :
    law q (A ∩ B) = law q A * law q B := by
  have hBg : DependsOn (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) Sᶜ := by
    intro ω η hωη
    have h := hdB hωη
    change (ω ∈ B) = (η ∈ B) at h
    change (if ω ∈ B then (1 : ℝ≥0∞) else 0) =
      (if η ∈ B then (1 : ℝ≥0∞) else 0)
    exact congrArg (fun p : Prop => if p then (1 : ℝ≥0∞) else 0) h
  have h := lintegral_indicator_fresh q S A hA hdA
    (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) (measurable_const.indicator hB) hBg
  have heq : A.indicator (B.indicator (fun _ : Set E => (1 : ℝ≥0∞))) =
      (A ∩ B).indicator (fun _ : Set E => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [Set.indicator,ha,hb]
  have hAB : (∫⁻ ω, (A ∩ B).indicator (fun _ : Set E => (1 : ℝ≥0∞)) ω ∂law q) =
      law q (A ∩ B) := lintegral_indicator_one (hA.inter hB)
  have hB' : (∫⁻ ω, B.indicator (fun _ : Set E => (1 : ℝ≥0∞)) ω ∂law q) =
      law q B := lintegral_indicator_one hB
  rw [heq,hAB,hB'] at h
  exact h

theorem selected_fresh_continuation_lower [Countable ι]
    (q : E → unitInterval) (S : Set E) (A B : ι → Set (Set E))
    (hmA : ∀ i, MeasurableSet (A i)) (hmB : ∀ i, MeasurableSet (B i))
    (hdA : ∀ i, DependsOn (fun ω => ω ∈ A i) S)
    (hdB : ∀ i, DependsOn (fun ω => ω ∈ B i) Sᶜ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (c : ℝ≥0∞) (hc : ∀ i, c ≤ law q (B i)) :
    law q (⋃ i, A i) * c ≤ law q (⋃ i, A i ∩ B i) := by
  have hdisj' : Pairwise (fun i j => Disjoint (A i ∩ B i) (A j ∩ B j)) := by
    intro i j hij
    exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  rw [measure_iUnion hdisj hmA,measure_iUnion hdisj' (fun i => (hmA i).inter (hmB i)),
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [measure_inter_of_separate_blocks q S _ _ (hmA i) (hmB i) (hdA i) (hdB i)]
  exact mul_le_mul' le_rfl (hc i)

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SelectedLayerVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] (G : BondGraph V E)

lemma firstLayerHitAt_pairwise (I : Set E) (x : V) (A : Set V) :
    Pairwise (fun u v => Disjoint (firstLayerHitAt G I x A u) (firstLayerHitAt G I x A v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  rintro ω hu hv
  exact huv (Encodable.encode_injective (le_antisymm (hu.2.2 v hv.2.1 hv.1)
    (hv.2.2 u hu.2.1 hu.1)))

lemma iUnion_firstLayerHitAt (I : Set E) (x : V) (A : Set V) :
    (⋃ z, firstLayerHitAt G I x A z) = {ω | ∃ z ∈ A, Conn G (ω ∩ I) x z} := by
  ext ω
  constructor
  · intro h
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp h
    exact ⟨z,hz.2.1,hz.1⟩
  · rintro ⟨z,hz,hconn⟩
    have hex : ∃ n : ℕ, ∃ w : V, Encodable.encode w = n ∧ w ∈ A ∧ Conn G (ω ∩ I) x w :=
      ⟨Encodable.encode z,z,rfl,hz,hconn⟩
    obtain ⟨w,hwn,hw,hwconn⟩ := Nat.find_spec hex
    apply Set.mem_iUnion.mpr
    refine ⟨w,hwconn,hw,?_⟩
    intro v hv hvconn
    rw [hwn]
    exact Nat.find_min' hex ⟨v,rfl,hv,hvconn⟩

lemma firstLayerHitAt_dependsOn (I : Set E) (x : V) (A : Set V) (z : V) :
    DependsOn (fun ω => ω ∈ firstLayerHitAt G I x A z) I := by
  intro ω η hωη
  have he : Set.inter ω I = Set.inter η I := by
    ext e
    change (ω e ∧ e ∈ I) ↔ (η e ∧ e ∈ I)
    by_cases hi : e ∈ I
    · simp only [hi,and_true]
      exact Iff.of_eq (hωη e hi)
    · simp only [hi,and_false]
  change (Conn G (Set.inter ω I) x z ∧ z ∈ A ∧ ∀ w ∈ A,
      Conn G (Set.inter ω I) x w → Encodable.encode z ≤ Encodable.encode w) =
    (Conn G (Set.inter η I) x z ∧ z ∈ A ∧ ∀ w ∈ A,
      Conn G (Set.inter η I) x w → Encodable.encode z ≤ Encodable.encode w)
  rw [he]

lemma measurableSet_firstLayerHitAt [Countable E] (I : Set E) (x : V) (A : Set V) (z : V) :
    MeasurableSet (firstLayerHitAt G I x A z) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  have hc (y : V) : Measurable (fun ω : Set E => Conn G (ω ∩ I) x y) :=
    (measurableSet_conn G x y).mem.comp hm
  exact ((hc z).and (measurable_const.and (Measurable.forall fun w =>
    measurable_const.imp ((hc w).imp measurable_const)))).setOf

end Percolation.BenjaminiSchramm

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

lemma lowerCrossingBlock_disjoint_upper (f : V → ℝ) (a b R : ℝ) :
    Disjoint (lowerCrossingBlock G f a b R) (internalEdges G {v | b ≤ f v}) := by
  exact Set.disjoint_left.mpr fun _ h₁ h₂ => h₁.2 h₂

lemma first_height_crossing_unexposed (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) {x y : V} (p : (openSimpleGraph G ω).Walk x y) (a b : ℝ) :
    a ≤ f x → f x < b → b ≤ f y → (∀ z ∈ p.support, a ≤ f z) →
      ∃ z, b ≤ f z ∧ f z ≤ b+R ∧
        Conn G (ω ∩ lowerCrossingBlock G f a b R) x z := by
  induction p with
  | @nil u =>
    intro _ hu hv _
    exact (not_lt_of_ge hv hu).elim
  | @cons x v y huv p ih =>
    intro ha hb hend hlow
    have hav : a ≤ f v := hlow v (by simp)
    obtain ⟨e,he,heq⟩ := huv.2
    have hxe : x ∈ G e := by rw [heq]; simp
    have hve : v ∈ G e := by rw [heq]; simp
    have hj := (abs_le.mp (hjump e x v hxe hve)).2
    by_cases hv : b ≤ f v
    · have hvR : f v ≤ b+R := by linarith
      refine ⟨v,hv,hvR,Relation.ReflTransGen.single ⟨e,⟨he,?_,?_⟩,heq⟩⟩
      · rw [mem_internalEdges_of_ends G _ e x v heq]
        exact ⟨⟨ha,by linarith⟩,hav,hvR⟩
      · intro he'
        exact (not_le_of_gt hb) (he' x hxe)
    · obtain ⟨z,hz,hzR,hconn⟩ := ih hav (lt_of_not_ge hv) hend
        (fun w hw => hlow w (List.mem_cons_of_mem _ hw))
      refine ⟨z,hz,hzR,(Relation.ReflTransGen.single ⟨e,⟨he,?_,?_⟩,heq⟩).trans hconn⟩
      · rw [mem_internalEdges_of_ends G _ e x v heq]
        exact ⟨⟨ha,by linarith⟩,hav,by linarith⟩
      · intro he'
        exact (not_le_of_gt hb) (he' x hxe)

theorem conn_above_lower_first_crossing (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (x y : V) (a b : ℝ) (hx : a ≤ f x) (hxb : f x < b)
    (hy : b ≤ f y) (hc : Conn G (ω ∩ internalEdges G {v | a ≤ f v}) x y) :
    ∃ z, b ≤ f z ∧ f z ≤ b+R ∧
      Conn G (ω ∩ lowerCrossingBlock G f a b R) x z := by
  obtain ⟨p⟩ := (conn_iff_reachable G _ x y).mp hc
  have hlow : ∀ z ∈ p.support, a ≤ f z := by
    intro z hz
    have hconn : Conn G (ω ∩ internalEdges G {v | a ≤ f v}) x z :=
      (conn_iff_reachable G _ x z).mpr ⟨p.takeUntil z hz⟩
    exact conn_internalEdges_end_mem G ω _ hx hconn
  obtain ⟨z,hz,hzR,hconn⟩ := first_height_crossing_unexposed G f R hR hjump
    (ω ∩ internalEdges G {v | a ≤ f v}) p a b hx hxb hy hlow
  refine ⟨z,hz,hzR,conn_mono G ?_ hconn⟩
  intro e he
  exact ⟨he.1.1,he.2⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FreshSlabConcatenation
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

lemma measurableSet_restrictedHit [Countable V] [Countable E]
    (I : Set E) (x : V) (A : Set V) : MeasurableSet (restrictedHit G I x A) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (Measurable.exists fun y => measurable_const.and
    ((measurableSet_conn G x y).mem.comp hm)).setOf

lemma restrictedHit_dependsOn (I : Set E) (x : V) (A : Set V) :
    DependsOn (fun ω => ω ∈ restrictedHit G I x A) I := by
  intro ω η hωη
  have he : Set.inter ω I = Set.inter η I := by
    ext e
    change (ω e ∧ e ∈ I) ↔ (η e ∧ e ∈ I)
    by_cases hi : e ∈ I
    · simp only [hi,and_true]
      exact Iff.of_eq (hωη e hi)
    · simp only [hi,and_false]
  change (∃ y ∈ A, Conn G (Set.inter ω I) x y) =
    (∃ y ∈ A, Conn G (Set.inter η I) x y)
  rw [he]

theorem restrictedHit_fresh_concatenation [Encodable V] [Countable E]
    (q : E → unitInterval) (I J : Set E) (hIJ : Disjoint I J)
    (x : V) (A B : Set V) (c : ℝ≥0∞)
    (hc : ∀ z ∈ A, c ≤ CriticalPercolation.BernoulliProduct.law q (restrictedHit G J z B)) :
    CriticalPercolation.BernoulliProduct.law q (restrictedHit G I x A) * c ≤
      CriticalPercolation.BernoulliProduct.law q (restrictedHit G (I ∪ J) x B) := by
  let SA : A → Set (Set E) := fun z => firstLayerHitAt G I x A z
  let SB : A → Set (Set E) := fun z => restrictedHit G J z B
  have hdisj : Pairwise (fun z w => Disjoint (SA z) (SA w)) := by
    intro z w hzw
    exact firstLayerHitAt_pairwise G I x A (fun h => hzw (Subtype.ext h))
  have hsub : J ⊆ Iᶜ := Set.disjoint_left.mp hIJ.symm
  have hprob := CriticalPercolation.BernoulliProduct.selected_fresh_continuation_lower
    q I SA SB (fun z => measurableSet_firstLayerHitAt G I x A z)
    (fun z => measurableSet_restrictedHit G J z B)
    (fun z => firstLayerHitAt_dependsOn G I x A z)
    (fun z => DependsOn.mono hsub (restrictedHit_dependsOn G J z B))
    hdisj c (fun z => hc z z.property)
  have hsel : (⋃ z, SA z) = restrictedHit G I x A := by
    ext ω
    constructor
    · intro h
      obtain ⟨z,hz⟩ := Set.mem_iUnion.mp h
      exact ⟨z,z.property,hz.1⟩
    · intro h
      have h' : ω ∈ ⋃ z, firstLayerHitAt G I x A z := by
        rw [iUnion_firstLayerHitAt]
        exact h
      obtain ⟨z,hz⟩ := Set.mem_iUnion.mp h'
      exact Set.mem_iUnion.mpr ⟨⟨z,hz.2.1⟩,hz⟩
  rw [hsel] at hprob
  refine hprob.trans (measure_mono ?_)
  intro ω hω
  obtain ⟨z,hz,hcont⟩ := Set.mem_iUnion.mp hω
  obtain ⟨y,hy,hzy⟩ := hcont
  refine ⟨y,hy,(conn_mono G (Set.inter_subset_inter_right _ Set.subset_union_left) hz.1).trans ?_⟩
  exact conn_mono G (Set.inter_subset_inter_right _ Set.subset_union_right) hzy

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HalfspaceConcatenation
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

theorem halfspace_crossing_fresh_product [Encodable V] [Countable E]
    (q : E → unitInterval) (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (x : V) (a b t : ℝ) (hx : a ≤ f x) (hxb : f x < b) (κ : ℝ≥0∞)
    (hκ : ∀ z, b ≤ f z → f z ≤ b+R →
      κ ≤ CriticalPercolation.BernoulliProduct.law q
        (restrictedHit G (internalEdges G {v | b ≤ f v}) z {v | t ≤ f v})) :
    CriticalPercolation.BernoulliProduct.law q
      (restrictedHit G (internalEdges G {v | a ≤ f v}) x {v | b ≤ f v}) * κ ≤
      CriticalPercolation.BernoulliProduct.law q
        (restrictedHit G (internalEdges G {v | a ≤ f v}) x {v | t ≤ f v}) := by
  let I := lowerCrossingBlock G f a b R
  let J := internalEdges G {v | b ≤ f v}
  let A := {v | b ≤ f v ∧ f v ≤ b+R}
  let B := {v | t ≤ f v}
  have hstart : restrictedHit G (internalEdges G {v | a ≤ f v}) x {v | b ≤ f v} ⊆
      restrictedHit G I x A := by
    intro ω hω
    obtain ⟨y,hy,hxy⟩ := hω
    obtain ⟨z,hz,hzR,hzconn⟩ :=
      conn_above_lower_first_crossing G f R hR hjump ω x y a b hx hxb hy hxy
    exact ⟨z,⟨hz,hzR⟩,hzconn⟩
  have hfinish : I ∪ J ⊆ internalEdges G {v | a ≤ f v} := by
    intro e he
    rcases he with he | he
    · exact internalEdges_mono G (fun _ h => h.1) he.1
    · exact internalEdges_mono G (show {v | b ≤ f v} ⊆ {v | a ≤ f v}
        from fun _ h => (hx.trans hxb.le).trans h) he
  calc
    _ ≤ CriticalPercolation.BernoulliProduct.law q (restrictedHit G I x A) * κ :=
      mul_le_mul' (measure_mono hstart) le_rfl
    _ ≤ CriticalPercolation.BernoulliProduct.law q (restrictedHit G (I ∪ J) x B) :=
      restrictedHit_fresh_concatenation G q I J
        (lowerCrossingBlock_disjoint_upper G f a b R) x A B κ
        (fun z hz => hκ z hz.1 hz.2)
    _ ≤ _ := by
      apply measure_mono
      intro ω hω
      obtain ⟨y,hy,hxy⟩ := hω
      exact ⟨y,hy,conn_mono G (Set.inter_subset_inter_right _ hfinish) hxy⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NormalizedHalfspace
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
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedHalfspaceHit_zero (a : V → ℝ) (x : V) :
    G.adjustedHalfspaceHit a x 0 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  exact ⟨x,by simp,Percolation.conn_refl G.ends _ x⟩

@[simp] lemma infimalAdjustedCrossing_zero [Nonempty V] (a : V → ℝ) (p : unitInterval) :
    G.infimalAdjustedCrossing a p 0 = 1 := by
  simp only [infimalAdjustedCrossing,G.adjustedHalfspaceHit_zero,measure_univ,ciInf_const]

lemma adjustedHalfspaceHit_upper (a : V → ℝ) (x : V) (b t : ℝ) :
    IsUpperSet (G.adjustedHalfspaceHit a x b t) := by
  rintro ω η hωη ⟨y,hy,hxy⟩
  exact ⟨y,hy,Percolation.conn_mono G.ends (Set.inter_subset_inter_left _ hωη) hxy⟩

lemma adjustedHalfspaceHit_finiteWitness (a : V → ℝ) (x : V) (b t : ℝ) :
    Percolation.FiniteWitness (G.adjustedHalfspaceHit a x b t) := by
  rintro ω ⟨y,hy,hxy⟩
  obtain ⟨s,hs,hconn⟩ := Percolation.finiteWitness_conn G.ends x y _ hxy
  refine ⟨s,fun _ he => (hs he).1,y,hy,?_⟩
  exact Percolation.conn_mono G.ends (show (s : Set E) ⊆ (s : Set E) ∩
    Percolation.internalEdges G.ends {v | b ≤ G.orbitAdjustedHeight a x v}
      from fun _ he => ⟨he,(hs he).2⟩) hconn

lemma adjustedHalfspaceHit_hasFiniteOpenWitness (a : V → ℝ) (x : V) (b t : ℝ) :
    BernoulliProduct.HasFiniteOpenWitness (G.adjustedHalfspaceHit a x b t) := by
  intro ω hω
  obtain ⟨s,hs,hsa⟩ := G.adjustedHalfspaceHit_finiteWitness a x b t ω hω
  exact ⟨s,s.finite_toSet,hs,hsa⟩

lemma measurableSet_adjustedHalfspaceHit [Countable E] (a : V → ℝ) (x : V) (b t : ℝ) :
    MeasurableSet (G.adjustedHalfspaceHit a x b t) :=
  Percolation.measurableSet_finiteWitness _ (G.adjustedHalfspaceHit_upper a x b t)
    (G.adjustedHalfspaceHit_finiteWitness a x b t)

lemma Aut.adjustedHalfspaceHit_preimage (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) (φ : G.Aut) (x : V) (b t : ℝ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.adjustedHalfspaceHit a (φ.vertex x) b t =
      G.adjustedHalfspaceHit a x b t := by
  have hD : φ.vertex ⁻¹' {v | b ≤ G.orbitAdjustedHeight a (φ.vertex x) v} =
      {v | b ≤ G.orbitAdjustedHeight a x v} := by
    ext v
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
  ext ω
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {v | b ≤ G.orbitAdjustedHeight a (φ.vertex x) v}) =
      ω ∩ Percolation.internalEdges G.ends {v | b ≤ G.orbitAdjustedHeight a x v} := by
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ← Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  have hconn (y : V) :
      Percolation.Conn G.ends (φ.edge '' ω ∩ Percolation.internalEdges G.ends
        {v | b ≤ G.orbitAdjustedHeight a (φ.vertex x) v}) (φ.vertex x) (φ.vertex y) ↔
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | b ≤ G.orbitAdjustedHeight a x v}) x y := by
    rw [← Percolation.conn_aut_iff G.ends φ.preserves,hmask]
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨z,rfl⟩ := φ.vertex.surjective y
    exact ⟨z,by simpa only [Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha] using hy,(hconn z).mp hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨φ.vertex y,by simpa only [Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha] using hy,
      (hconn y).mpr hxy⟩

lemma Aut.adjustedHalfspaceHit_measure [Countable E] (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) (φ : G.Aut) (p : unitInterval)
    (x : V) (b t : ℝ) :
    G.law p (G.adjustedHalfspaceHit a (φ.vertex x) b t) = G.law p (G.adjustedHalfspaceHit a x b t) := by
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_adjustedHalfspaceHit _ _ _ _),Aut.adjustedHalfspaceHit_preimage G a ha φ]

lemma infimalAdjustedCrossing_le_one [Nonempty V] (a : V → ℝ) (p : unitInterval) (t : ℝ) :
    G.infimalAdjustedCrossing a p t ≤ 1 :=
  (iInf_le (fun x => G.law p (G.adjustedHalfspaceHit a x 0 t)) (Classical.arbitrary V)).trans prob_le_one

theorem infimalAdjustedCrossing_supermultiplicative [Encodable V] [Countable E] [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (a : V → ℝ) (m M : ℝ) (hm : 0 < m) (ha : ∀ x, m ≤ a x ∧ a x ≤ M)
    (p : unitInterval) {s t : ℝ} (hs : 0 ≤ s) (_ht : 0 ≤ t) :
    G.infimalAdjustedCrossing a p s * G.infimalAdjustedCrossing a p t ≤
      G.infimalAdjustedCrossing a p (s+t) := by
  by_cases hs0 : s = 0
  · simp only [hs0,zero_add,G.infimalAdjustedCrossing_zero,one_mul,le_refl]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  obtain ⟨K,hK⟩ := G.uniform_ball_bound hq 1
  let D := Real.log M-Real.log m
  have hD : 0 ≤ D := sub_nonneg.mpr (Real.log_le_log hm
    ((ha (Classical.arbitrary V)).1.trans (ha (Classical.arbitrary V)).2))
  let R := D+max 0 (Real.log (K : ℝ))
  have hR : 0 ≤ R := add_nonneg hD (le_max_left _ _)
  apply le_iInf
  intro x
  have hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
    intro e u v hu hv
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v,add_sub_cancel_left]
    have hr := G.modularLogHeight_edge_jump hc hl K hK u u v e hu hv
    rw [G.modularLogHeight_self,sub_zero] at hr
    have ht := abs_add_le (G.orbitAdjustedHeight a u v-G.modularLogHeight u v) (G.modularLogHeight u v)
    rw [sub_add_cancel] at ht
    exact ht.trans (add_le_add (G.orbitAdjustedHeight_sub_bound a m M hm ha u v)
      (hr.trans (le_max_right _ _)))
  have hcont (z : V) (hz : s ≤ G.orbitAdjustedHeight a x z)
      (_hzR : G.orbitAdjustedHeight a x z ≤ s+R) :
      G.infimalAdjustedCrossing a p t ≤ BernoulliProduct.law (fun _ : E => p)
        (restrictedHit G.ends (Percolation.internalEdges G.ends {v | s ≤ G.orbitAdjustedHeight a x v})
          z {v | s+t ≤ G.orbitAdjustedHeight a x v}) := by
    apply (iInf_le (fun y => G.law p (G.adjustedHalfspaceHit a y 0 t)) z).trans
    rw [BernoulliProduct.law_const]
    apply measure_mono
    rintro ω ⟨y,hy,hzy⟩
    change t ≤ G.orbitAdjustedHeight a z y at hy
    refine ⟨y,?_,Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
      (Percolation.internalEdges_mono G.ends ?_)) hzy⟩
    · change s+t ≤ G.orbitAdjustedHeight a x y
      rw [G.orbitAdjustedHeight_change_base hc hl a x z y]
      linarith
    · intro v hv
      change 0 ≤ G.orbitAdjustedHeight a z v at hv
      change s ≤ G.orbitAdjustedHeight a x v
      rw [G.orbitAdjustedHeight_change_base hc hl a x z v]
      linarith
  have hprod := halfspace_crossing_fresh_product G.ends (fun _ : E => p)
    (G.orbitAdjustedHeight a x) R hR hjump x 0 s (s+t) (by simp) (by simpa using hspos)
    (G.infimalAdjustedCrossing a p t) hcont
  simp only [BernoulliProduct.law_const] at hprod
  exact (mul_le_mul' (iInf_le (fun y => G.law p (G.adjustedHalfspaceHit a y 0 s)) x) le_rfl).trans hprod

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HalfspaceRootComparison
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

lemma walk_finite_open_restriction {x y : V} (w : (openSimpleGraph G Set.univ).Walk x y)
    (D : Set V) (hD : ∀ v ∈ w.support, v ∈ D) :
    ∃ s : Finset E, s.card ≤ w.length ∧ ∀ ω : Set E, (s : Set E) ⊆ ω →
      Conn G (ω ∩ internalEdges G D) x y := by
  obtain ⟨l,hl,he,_ho⟩ := walk_lift_bonds G Set.univ w
  have hlen : l.length = w.length := by
    simpa only [List.length_map,SimpleGraph.Walk.length_edges] using congrArg List.length he
  refine ⟨l.toFinset,(List.toFinset_card_le l).trans_eq hlen,fun ω hω => ?_⟩
  apply hl.conn
  intro e he'
  refine ⟨hω (List.mem_toFinset.mpr he'),?_⟩
  intro v hv
  exact hD v (SimpleGraph.Walk.mem_support_of_mem_edges (he ▸ List.mem_map_of_mem he') hv)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CrossingExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology BigOperators

namespace Percolation.BenjaminiSchramm

theorem positive_crossing_exponent (P : ℕ → ℝ) (hP : ∀ n, 0 < P n)
    (hP1 : ∀ n, P n ≤ 1) (hP0 : P 0 = 1)
    (hmul : ∀ m n, P m*P n ≤ P (m+n)) :
    ∃ α : ℝ, 0 ≤ α ∧
      (∀ n : ℕ, P n ≤ Real.exp (-α*n)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(α+ε)*n) ≤ P n) ∧
      Tendsto (fun n : ℕ => -Real.log (P n)/n) atTop (𝓝 α) := by
  let u : ℕ → ℝ := fun n => -Real.log (P n)
  have hu : Subadditive u := by
    intro m n
    have h := Real.log_le_log (mul_pos (hP m) (hP n)) (hmul m n)
    rw [Real.log_mul (hP m).ne' (hP n).ne'] at h
    dsimp [u]
    linarith
  have hun (n : ℕ) : 0 ≤ u n := neg_nonneg.mpr (Real.log_nonpos (hP n).le (hP1 n))
  have hbdd : BddBelow (Set.range fun n : ℕ => u n/n) :=
    ⟨0,by rintro _ ⟨n,rfl⟩; exact div_nonneg (hun n) (Nat.cast_nonneg n)⟩
  let α := hu.lim
  have hlim : Tendsto (fun n : ℕ => u n/n) atTop (𝓝 α) := hu.tendsto_lim hbdd
  have hα : 0 ≤ α := ge_of_tendsto hlim (Filter.Eventually.of_forall
    (fun n => div_nonneg (hun n) (Nat.cast_nonneg n)))
  refine ⟨α,hα,?_,?_,hlim⟩
  · intro n
    by_cases hn : n = 0
    · simp only [hn,hP0,Nat.cast_zero,mul_zero,Real.exp_zero,le_refl]
    have hr := (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn) : (0 : ℝ) < n)).mp
      (hu.lim_le_div hbdd hn)
    have he := Real.exp_le_exp.mpr (show Real.log (P n) ≤ -α*n by dsimp [u] at hr; nlinarith)
    rwa [Real.exp_log (hP n)] at he
  · intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right α hε)))
    let f : ℕ → ℝ := fun n => P n*Real.exp ((α+ε)*n)
    obtain ⟨i,hi,himin⟩ := Finset.exists_min_image (Finset.range (N+1)) f
      ⟨0,Finset.mem_range.mpr (Nat.succ_pos N)⟩
    let c := min 1 (f i)
    have hc : 0 < c := lt_min (by norm_num) (mul_pos (hP i) (Real.exp_pos _))
    refine ⟨c,hc,fun n => ?_⟩
    by_cases hn : n < N+1
    · have hcf : c ≤ f n := (min_le_right _ _).trans (himin n (Finset.mem_range.mpr hn))
      have hh := mul_le_mul_of_nonneg_right hcf (Real.exp_pos (-(α+ε)*n)).le
      have he : Real.exp ((α+ε)*n)*Real.exp (-(α+ε)*n) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
      dsimp [f] at hh
      rwa [mul_assoc,he,mul_one] at hh
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hr := (div_lt_iff₀ hnpos).mp (hN n (by omega))
      have hh : -(α+ε)*(n : ℝ) ≤ Real.log (P n) := by dsimp [u] at hr; linarith
      have he := Real.exp_le_exp.mpr hh
      rw [Real.exp_log (hP n)] at he
      exact (mul_le_of_le_one_left (Real.exp_nonneg _) (min_le_left _ _)).trans he

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CrossingPositivity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem adjustedHalfspaceHit_walk_lower [Countable E] (a : V → ℝ) (p : unitInterval)
    {x y : V} (w : G.fullGraph.Walk x y) (t : ℝ)
    (hw : ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v)
    (hy : t ≤ G.orbitAdjustedHeight a x y) :
    (p : ℝ)^w.length ≤ (G.law p).real (G.adjustedHalfspaceHit a x 0 t) := by
  have hg : G.fullGraph = Percolation.openSimpleGraph G.ends Set.univ :=
    criticalModel_openGraph G.ends Set.univ
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by simpa only [← hg,id_eq] using h⟩
  obtain ⟨s,hs,hconn⟩ := walk_finite_open_restriction G.ends (w.map f)
    {v | 0 ≤ G.orbitAdjustedHeight a x v} (by
      intro v hv
      rw [SimpleGraph.Walk.support_map] at hv
      change v ∈ w.support.map id at hv
      exact hw v (by simpa only [List.map_id_fun,id_eq] using hv))
  have hslen : s.card ≤ w.length := by simpa only [SimpleGraph.Walk.length_map] using hs
  have hsub : {ω : Set E | (s : Set E) ⊆ ω} ⊆ G.adjustedHalfspaceHit a x 0 t :=
    fun ω hω => ⟨y,hy,hconn ω hω⟩
  calc
    _ ≤ (p : ℝ)^s.card := pow_le_pow_of_le_one p.2.1 p.2.2 hslen
    _ = (G.law p).real {ω : Set E | (s : Set E) ⊆ ω} :=
      (Percolation.finite_open_probability p s).symm
    _ ≤ _ := measureReal_mono hsub

theorem infimalAdjustedCrossing_finite_energy [Fintype G.VertexOrbit] [Nontrivial V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ = μ) (hu : ¬ G.CombinatoriallyUnimodular)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      (p : ℝ)^(A*t+B) ≤ (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p t).toReal := by
  obtain ⟨A,B,hA,hB,hpath⟩ := G.stationaryOrbitHeight_orbit_above hc hl hq μ hμ hstat hu
  refine ⟨A,B,hA,hB,fun t ht => ?_⟩
  have hroot (x : V) : (p : ℝ)^(A*t+B) ≤
      (G.law p).real (G.adjustedHalfspaceHit (G.stationaryOrbitWeight μ) x 0 t) := by
    obtain ⟨y,w,_horb,hlen,hw,hy⟩ := hpath t ht x (G.vertexOrbit x)
    have hc := G.adjustedHalfspaceHit_walk_lower (G.stationaryOrbitWeight μ) p w t hw hy
    have hcoeff : (p : ℝ)^(A*t+B) ≤ (p : ℝ)^w.length := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hp p.2.2 hlen
    exact hcoeff.trans hc
  have he : ENNReal.ofReal ((p : ℝ)^(A*t+B)) ≤
      G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p t :=
    le_iInf fun x => ENNReal.ofReal_le_of_le_toReal (hroot x)
  have hf := ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (G.infimalAdjustedCrossing_le_one _ p t)) he
  rwa [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hp _).le] at hf

theorem normalized_crossing_exponent [Fintype G.VertexOrbit] [Nontrivial V]
    [Encodable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ = μ) (hu : ¬ G.CombinatoriallyUnimodular)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∃ α : ℝ, 0 ≤ α ∧
      (∀ n : ℕ, (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal ≤ Real.exp (-α*n)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(α+ε)*n) ≤ (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal) ∧
      Tendsto (fun n : ℕ => -Real.log
        (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal/n) atTop (𝓝 α) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,_hA,_hB,hbound⟩ := G.infimalAdjustedCrossing_finite_energy hc hl hq μ hμ hstat hu p hp
  obtain ⟨m,M,hm,ha⟩ := G.stationaryOrbitWeight_uniform_bounds hc hl μ hμ
  have hne (t : ℝ) : G.infimalAdjustedCrossing a p t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (G.infimalAdjustedCrossing_le_one a p t)
  apply positive_crossing_exponent (fun n : ℕ => (G.infimalAdjustedCrossing a p n).toReal)
  · intro n
    exact (Real.rpow_pos_of_pos hp _).trans_le (hbound n (Nat.cast_nonneg n))
  · intro n
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (G.infimalAdjustedCrossing_le_one a p n)).trans_eq
      ENNReal.toReal_one
  · simp
  · intro n k
    have hh := ENNReal.toReal_mono (hne (n+k))
      (G.infimalAdjustedCrossing_supermultiplicative hc hl hq a m M hm ha p
        (Nat.cast_nonneg n) (Nat.cast_nonneg k))
    simpa only [ENNReal.toReal_mul,Nat.cast_add] using hh

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CrossingExponentContinuity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma infimalAdjustedCrossing_lower_parameter [Countable E] [Nonempty V]
    (hq : G.QuasiTransitive) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x)
    (p : unitInterval) (hp : 0 < p) (t c : ℝ) (hc : 0 ≤ c)
    (hlt : c < (G.infimalAdjustedCrossing a p t).toReal) :
    ∃ q : unitInterval, (p : ℝ)/2 ≤ q ∧ q < p ∧ c < (G.infimalAdjustedCrossing a q t).toReal := by
  let d := (c+(G.infimalAdjustedCrossing a p t).toReal)/2
  have hcd : c < d := by dsimp [d]; linarith
  have hdp : d < (G.infimalAdjustedCrossing a p t).toReal := by dsimp [d]; linarith
  obtain ⟨S,hS,hcover⟩ := hq
  let : Finite S := hS.to_subtype
  have hroot (x : V) : d < (G.law p).real (G.adjustedHalfspaceHit a x 0 t) :=
    hdp.trans_le (ENNReal.toReal_mono (measure_ne_top _ _)
      (iInf_le (fun y => G.law p (G.adjustedHalfspaceHit a y 0 t)) x))
  obtain ⟨q,hhalf,hqp,hqroot⟩ := BernoulliProduct.exists_lower_parameter
    (fun x : S => G.adjustedHalfspaceHit a x 0 t) (fun x => G.adjustedHalfspaceHit_upper a x 0 t)
    (fun x => G.adjustedHalfspaceHit_hasFiniteOpenWitness a x 0 t) p hp (fun _ => d)
    (fun x => by simpa only [BernoulliProduct.law_const,law] using hroot x)
  refine ⟨q,hhalf,hqp,hcd.trans_le ?_⟩
  have he : ENNReal.ofReal d ≤ G.infimalAdjustedCrossing a q t := by
    apply le_iInf
    intro x
    obtain ⟨o,ho,φ,rfl⟩ := hcover x
    rw [Aut.adjustedHalfspaceHit_measure G a ha φ]
    have hr := hqroot ⟨o,ho⟩
    rw [BernoulliProduct.law_const] at hr
    exact ENNReal.ofReal_le_of_le_toReal hr.le
  have hf := ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (G.infimalAdjustedCrossing_le_one a q t)) he
  rwa [ENNReal.toReal_ofReal (hc.trans hcd.le)] at hf

theorem normalized_crossing_exponent_approximation_bs_oai [Fintype G.VertexOrbit] [Nontrivial V]
    [Encodable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ = μ) (hu : ¬ G.CombinatoriallyUnimodular)
    (p : unitInterval) (hp : 0 < p) (α : ℝ)
    (hlim : Tendsto (fun n : ℕ => -Real.log
      (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal/n) atTop (𝓝 α))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : unitInterval, (p : ℝ)/2 ≤ q ∧ q < p ∧ ∃ β : ℝ, 0 ≤ β ∧ β < α+ε ∧
      (∀ n : ℕ, (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) q n).toReal ≤ Real.exp (-β*n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(β+δ)*n) ≤ (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) q n).toReal) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,_hA,_hB,hpos⟩ := G.infimalAdjustedCrossing_finite_energy hc hl hq μ hμ hstat hu p hp
  obtain ⟨n,hn,hsl⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right α hε)))).exists
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hPn : 0 < (G.infimalAdjustedCrossing a p n).toReal :=
    (Real.rpow_pos_of_pos hp _).trans_le (hpos n (Nat.cast_nonneg n))
  have hlog : -(α+ε)*(n : ℝ) < Real.log (G.infimalAdjustedCrossing a p n).toReal := by
    have hh := (div_lt_iff₀ hnpos).mp hsl
    linarith
  have he := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hPn] at he
  obtain ⟨q,hhalf,hqp,hqprob⟩ := G.infimalAdjustedCrossing_lower_parameter hq a
    (G.stationaryOrbitWeight_aut μ) p hp n (Real.exp (-(α+ε)*n)) (Real.exp_pos _).le he
  have hqpos : (0 : ℝ) < q := (half_pos (show (0 : ℝ) < p from hp)).trans_le hhalf
  obtain ⟨β,hβ,hβupper,hβlower,_hβlim⟩ := G.normalized_crossing_exponent hc hl hq μ hμ hstat hu q hqpos
  refine ⟨q,hhalf,hqp,β,hβ,?_,hβupper,hβlower⟩
  have hle := Real.exp_lt_exp.mp (hqprob.trans_le (hβupper n))
  nlinarith

end CriticalPercolation.BondGraph

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation_bs_oai.{u_1, u_2}
