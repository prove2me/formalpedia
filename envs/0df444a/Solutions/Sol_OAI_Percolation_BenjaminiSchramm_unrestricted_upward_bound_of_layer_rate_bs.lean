-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.unrestricted_upward_bound_of_layer_rate_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:32:13.953913+00:00
-- url     : https://prove2.me/submissions/427add88-f87d-4a52-92f8-70f9561b6fea

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Bounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Coupling

theorem measurable_threshold (p : unitInterval) :
    Measurable (fun t : unitInterval => t ≤ p) :=
  measurableSet_setOfPred.mp measurableSet_Iic

 
theorem map_threshold (p : unitInterval) :
    (volume : Measure unitInterval).map (fun t => t ≤ p) =
      unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Iic p) = _
    rw [unitInterval.volume_Iic, ← unitInterval.coe_toNNReal p,
      ENNReal.ofReal_coe_nnreal]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Ioi p) = _
    rw [unitInterval.volume_Ioi, ← unitInterval.coe_symm_eq,
      ← unitInterval.coe_toNNReal (unitInterval.symm p), ENNReal.ofReal_coe_nnreal]


end Coupling

end Percolation

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

section FiniteAssociation
attribute [local instance] Classical.propDecidable
variable [Fintype E]

private theorem bernoulli_atom_product (p : unitInterval) (ω : Set E) :
    (law p).real {ω} = ∏ e : E, if e ∈ ω then (p : ℝ) else 1 - p := by
  rw [law, setBernoulli_real_singleton p (Set.subset_univ ω) (Set.finite_univ)]
  simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.sdiff_eq]
  exact Or.inl rfl

private theorem bernoulli_atom_modular (p : unitInterval) (a b : Set E) :
    (law p).real {a} * (law p).real {b} =
      (law p).real {a ∩ b} * (law p).real {a ∪ b} := by
  simp only [bernoulli_atom_product, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases ha : e ∈ a <;> by_cases hb : e ∈ b <;> simp [ha, hb, mul_comm]

 

theorem association_finite (p : unitInterval) (f g : Set E → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f ω ∂law p) * (∫ ω, g ω ∂law p) ≤ ∫ ω, f ω * g ω ∂law p := by
  have h := fkg f g (fun ω : Set E => (law p).real {ω})
    (fun _ => measureReal_nonneg) hf0 hg0 hf hg
    (fun a b => (bernoulli_atom_modular p a b).le)
  have hsum : (∑ ω : Set E, (law p).real {ω}) = 1 := by
    simp
  rw [hsum, one_mul] at h
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul] using h

 
theorem association_events_finite (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real A * (law p).real B ≤ (law p).real (A ∩ B) := by
  have hm (S : Set (Set E)) (hS : IsUpperSet S) :
      Monotone (S.indicator (fun _ => (1 : ℝ))) := by
    intro a b hab
    by_cases ha : a ∈ S
    · simp [ha, hS hab ha]
    · simp only [Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have he : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
      B.indicator (fun _ => (1 : ℝ)) ω) = (A ∩ B).indicator (fun _ => 1) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha, hb]
  have h := association_finite p _ _ (hm A hA) (hm B hB)
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
  rw [he] at h
  simpa only [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet B),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet (A ∩ B)),
    smul_eq_mul, mul_one] using h

end FiniteAssociation

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


theorem association_restricted (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A ∩ B} := by
  let A' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ A}
  let B' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ B}
  have hA' : IsUpperSet A' := fun _ _ h ha => hA (Set.image_mono h) ha
  have hB' : IsUpperSet B' := fun _ _ h hb => hB (Set.image_mono h) hb
  have he (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) =
      ω ∩ (s : Set E) := by
    ext e
    simp [and_comm]
  have hl (C : Set (Set E)) :
      (law p : Measure (Set (s : Set E))).real {η | Subtype.val '' η ∈ C} =
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} := by
    rw [← law_map_restrict p (s : Set E), measureReal_def,
      Measure.map_apply (measurable_set_restrict _) .of_discrete]
    simp only [Set.preimage_ofPred_eq, he, measureReal_def]
  have ht := association_events_finite p A' B' hA' hB'
  change (law p).real {η | Subtype.val '' η ∈ A} *
    (law p).real {η | Subtype.val '' η ∈ B} ≤
    (law p).real {η | Subtype.val '' η ∈ A ∩ B} at ht
  simpa only [hl] using ht

 theorem edgeExhaustion_mono [Encodable E] :
    Monotone (edgeExhaustion : ℕ → Finset E) := by
  intro m n h e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range] at he ⊢
  exact he.trans_le h

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

 

theorem association_finiteWitness [Countable E] (p : unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real A * (law p).real B ≤ (law p).real (A ∩ B) := by
  let := Encodable.ofCountable E
  have hfAB : FiniteWitness (A ∩ B) := by
    intro ω hω
    obtain ⟨s, hs, hsa⟩ := hfA ω hω.1
    obtain ⟨t, ht, htb⟩ := hfB ω hω.2
    refine ⟨s ∪ t, ?_, hA ?_ hsa, hB ?_ htb⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs ht
    · simp only [Finset.coe_union]; exact Set.subset_union_left
    · simp only [Finset.coe_union]; exact Set.subset_union_right
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto
    ((hlim A hA hfA).mul (hlim B hB hfB)) (hlim (A ∩ B) (hA.inter hB) hfAB)
    (Filter.Eventually.of_forall fun n => association_restricted p A B hA hB (edgeExhaustion n))

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

section DisjointWitness
attribute [local instance] Classical.propDecidable


theorem disjointOccurrence_upper (A B : Set (Set E)) : IsUpperSet (DisjointOccurrence A B) := by
  rintro ω η h ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs.trans h, ht.trans h, hd, ha, hb⟩

theorem finiteWitness_disjointOccurrence (A B : Set (Set E)) :
    FiniteWitness (DisjointOccurrence A B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  refine ⟨s ∪ t, ?_, s, t, ?_, ?_, hd, ha, hb⟩
  · simpa only [Finset.coe_union] using Set.union_subset hs ht
  · simp
  · simp

theorem disjointOccurrence_mono {A A' B B' : Set (Set E)}
    (hA : A ⊆ A') (hB : B ⊆ B') : DisjointOccurrence A B ⊆ DisjointOccurrence A' B' := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs, ht, hd, hA ha, hB hb⟩


theorem openSection_upper {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    IsUpperSet (openSection A e) :=
  fun _ _ h hω => hA (Set.insert_subset_insert h) hω

theorem subset_openSection {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    A ⊆ openSection A e := fun ω hω => hA (Set.subset_insert e ω) hω

 
theorem openSection_disjointOccurrence (A B : Set (Set E)) (_hA : IsUpperSet A)
    (hB : IsUpperSet B) (e : E) :
    openSection (DisjointOccurrence A B) e ⊆
      DisjointOccurrence (openSection A e) B ∪ DisjointOccurrence A (openSection B e) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  by_cases he : e ∈ s
  · left
    have het : e ∉ t := fun h => Finset.disjoint_left.mp hd he h
    refine ⟨s.erase e, t, ?_, ?_, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd, ?_, hb⟩
    · intro z hz
      exact (hs (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · intro z hz
      rcases ht hz with rfl | hz'
      · exact (het hz).elim
      · exact hz'
    · change insert e (↑(s.erase e) : Set E) ∈ A
      simpa only [← Finset.coe_insert, Finset.insert_erase he] using ha
  · right
    refine ⟨s, t.erase e, ?_, ?_, Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd, ha, ?_⟩
    · intro z hz
      rcases hs hz with rfl | hz'
      · exact (he hz).elim
      · exact hz'
    · intro z hz
      exact (ht (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · apply hB ?_ hb
      intro z hz
      by_cases hze : z = e
      · exact Or.inl hze
      · exact Or.inr (Finset.mem_erase.mpr ⟨hze, hz⟩)



theorem finiteProbability_mono (p : unitInterval) (s : Finset E)
    {A B : Set (Set E)} (h : A ⊆ B) : finiteProbability p s A ≤ finiteProbability p s B := by
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ha hb hb
  · exact le_rfl
  · exact (hb (h ha)).elim
  · exact mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  · exact le_rfl

theorem finiteProbability_union_add_inter (p : unitInterval) (s : Finset E)
    (A B : Set (Set E)) :
    finiteProbability p s (A ∪ B) + finiteProbability p s (A ∩ B) =
      finiteProbability p s A + finiteProbability p s B := by
  simp only [finiteProbability, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ha : (t : Set E) ∈ A <;> by_cases hb : (t : Set E) ∈ B <;> simp [ha, hb]

theorem finiteProbability_insert (p : unitInterval) (s : Finset E) (e : E) (he : e ∉ s)
    (A : Set (Set E)) :
    finiteProbability p (insert e s) A =
      (1 - p : ℝ) * finiteProbability p s A + (p : ℝ) * finiteProbability p s (openSection A e) := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  simp only [finiteProbability, Finset.powerset_insert, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum, Finset.card_insert_of_notMem he]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp ht)
    have hexp : s.card + 1 - t.card = (s.card - t.card) + 1 := by omega
    rw [hexp, pow_succ]
    split_ifs <;> simp_all [mul_comm, mul_left_comm]
  · apply Finset.sum_congr rfl
    intro t ht
    have het : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    simp only [Finset.card_insert_of_notMem het, Nat.add_sub_add_right, pow_succ,
      Finset.coe_insert, openSection, Set.mem_ofPred_eq]
    split_ifs <;> simp_all [mul_assoc, mul_comm]

end DisjointWitness

section FiniteBK
attribute [local instance] Classical.propDecidable



theorem finiteProbability_disjointOccurrence_le_half (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (s : Finset E) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteProbability p s (DisjointOccurrence A B) ≤
      finiteProbability p s A * finiteProbability p s B := by
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    simp only [finiteProbability_empty, empty_mem_disjointOccurrence]
    by_cases ha : (∅ : Set E) ∈ A <;> by_cases hb : (∅ : Set E) ∈ B <;> simp [ha, hb]
  | @insert e s he ih =>
    let A1 := openSection A e
    let B1 := openSection B e
    let D00 := DisjointOccurrence A B
    let D10 := DisjointOccurrence A1 B
    let D01 := DisjointOccurrence A B1
    have hD : D00 ⊆ D10 ∩ D01 := by
      intro ω hω
      exact ⟨disjointOccurrence_mono (subset_openSection hA e) (Set.Subset.refl _) hω,
        disjointOccurrence_mono (Set.Subset.refl _) (subset_openSection hB e) hω⟩
    have hsec : finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s D10 + finiteProbability p s D01 - finiteProbability p s D00 := by
      have h1 := finiteProbability_mono p s (openSection_disjointOccurrence A B hA hB e)
      have h2 := finiteProbability_mono p s hD
      have h3 := finiteProbability_union_add_inter p s D10 D01
      change finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s (D10 ∪ D01) at h1
      linarith
    have h00 := ih A B hA hB
    have h10 := ih A1 B (openSection_upper hA e) hB
    have h01 := ih A B1 hA (openSection_upper hB e)
    have ha := finiteProbability_mono p s (subset_openSection hA e)
    have hb := finiteProbability_mono p s (subset_openSection hB e)
    have hcoef : 0 ≤ 1 - 2 * (p : ℝ) := by linarith
    have hdif : 0 ≤ ((p : ℝ) ^ 2) *
        (finiteProbability p s A1 - finiteProbability p s A) *
        (finiteProbability p s B1 - finiteProbability p s B) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ha)) (sub_nonneg.mpr hb)
    rw [finiteProbability_insert p s e he, finiteProbability_insert p s e he,
      finiteProbability_insert p s e he]
    have hm := mul_le_mul_of_nonneg_left hsec p.2.1
    have hm00 := mul_le_mul_of_nonneg_left h00 hcoef
    have hm10 := mul_le_mul_of_nonneg_left h10 p.2.1
    have hm01 := mul_le_mul_of_nonneg_left h01 p.2.1
    change (1 - (p : ℝ)) * finiteProbability p s D00 +
      (p : ℝ) * finiteProbability p s (openSection D00 e) ≤
      ((1 - (p : ℝ)) * finiteProbability p s A + (p : ℝ) * finiteProbability p s A1) *
      ((1 - (p : ℝ)) * finiteProbability p s B + (p : ℝ) * finiteProbability p s B1)
    nlinarith

end FiniteBK

section BKMeasure
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem finiteProbability_univ [Fintype E] (p : unitInterval) (A : Set (Set E)) :
    finiteProbability p Finset.univ A = (law p).real A := by
  have he : (law p).real A = ∑ ω : Set E, if ω ∈ A then (law p).real {ω} else 0 := by
    have h := integral_fintype (μ := law p) (f := A.indicator (fun _ => (1 : ℝ)))
      Integrable.of_finite
    rw [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A)] at h
    simpa [smul_eq_mul, mul_ite, Set.indicator_apply] using h
  rw [he, finiteProbability]
  apply Finset.sum_bij (fun (t : Finset E) _ => (t : Set E))
  · simp
  · intro a _ b _ h
    exact Finset.coe_injective h
  · intro ω _
    exact ⟨ω.toFinset, by simp, by simp⟩
  · intro t _
    rw [law, setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ]
    simp [Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card]

theorem disjointOccurrence_image {F : Type*} (f : F ↪ E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B =
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  ext ω
  constructor
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    let s' := s.preimage f f.injective.injOn
    let t' := t.preimage f f.injective.injOn
    have hs' : (s' : Set F) = f ⁻¹' (s : Set E) := by simp [s']
    have ht' : (t' : Set F) = f ⁻¹' (t : Set E) := by simp [t']
    have hsI : f '' (s' : Set F) = (s : Set E) := by
      rw [hs', Set.image_preimage_eq_of_subset]
      exact hs.trans (Set.image_subset_range _ _)
    have htI : f '' (t' : Set F) = (t : Set E) := by
      rw [ht', Set.image_preimage_eq_of_subset]
      exact ht.trans (Set.image_subset_range _ _)
    refine ⟨s', t', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs']
      exact (Set.preimage_mono hs).trans (by rw [Set.preimage_image_eq _ f.injective])
    · rw [ht']
      exact (Set.preimage_mono ht).trans (by rw [Set.preimage_image_eq _ f.injective])
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      exact Finset.disjoint_left.mp hd (by simpa [s'] using hx) (by simpa [t'] using hy)
    · change f '' (s' : Set F) ∈ A
      rwa [hsI]
    · change f '' (t' : Set F) ∈ B
      rwa [htI]
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    refine ⟨s.map f, t.map f, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_map] using Set.image_mono hs
    · simpa only [Finset.coe_map] using Set.image_mono ht
    · exact (Finset.disjoint_map f).mpr hd
    · simpa only [Finset.coe_map, Set.mem_preimage] using ha
    · simpa only [Finset.coe_map, Set.mem_preimage] using hb

theorem bk_finite_half [Fintype E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  simpa only [finiteProbability_univ] using
    finiteProbability_disjointOccurrence_le_half p hp Finset.univ A B hA hB

theorem bk_restricted_half (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ DisjointOccurrence A B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} := by
  let f : (s : Set E) ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  have hreal (C : Set (Set E)) :
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} =
        (law p).real {η : Set (s : Set E) | f '' η ∈ C} := by
    rw [← law_map_restrict p (s : Set E)]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_set_restrict _) MeasurableSet.of_discrete]
    congr 2
    ext ω
    change ω ∩ (s : Set E) ∈ C ↔ f '' (Subtype.val ⁻¹' ω) ∈ C
    have he : f '' (Subtype.val ⁻¹' ω) = ω ∩ (s : Set E) := by
      ext e
      simp [f, and_comm]
    rw [he]
  rw [hreal, hreal, hreal]
  have hh := bk_finite_half p hp ((fun ω => f '' ω) ⁻¹' A)
    ((fun ω => f '' ω) ⁻¹' B)
    (fun _ _ h hω => hA (Set.image_mono h) hω)
    (fun _ _ h hω => hB (Set.image_mono h) hω)
  rw [← disjointOccurrence_image] at hh
  exact hh

 
theorem bk_finiteWitness_half [Countable E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  let := Encodable.ofCountable E
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  apply le_of_tendsto_of_tendsto
    (hlim _ (disjointOccurrence_upper A B) (finiteWitness_disjointOccurrence A B))
    ((hlim A hA hfA).mul (hlim B hB hfB))
  exact Filter.Eventually.of_forall fun n => bk_restricted_half p hp A B hA hB (edgeExhaustion n)

end BKMeasure

section ORLift
attribute [local instance] Classical.propDecidable

instance bitLaw_isProbabilityMeasure (q : unitInterval) : IsProbabilityMeasure (bitLaw q) := by
  rw [bitLaw, ← map_threshold q]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

 
theorem map_nonempty (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set F)).map Set.Nonempty = bitLaw (orParameter q (Fintype.card F)) := by
  let μ := (law q : Measure (Set F)).map Set.Nonempty
  have hm : Measurable (Set.Nonempty : Set F → Prop) := .of_discrete
  have : IsProbabilityMeasure μ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hfalse : μ.real {False} = (1 - (q : ℝ)) ^ Fintype.card F := by
    change ((law q).map Set.Nonempty).real {False} = _
    simp only [Measure.real, Measure.map_apply hm (measurableSet_singleton _)]
    have he : Set.Nonempty ⁻¹' ({False} : Set Prop) = ({∅} : Set (Set F)) := by
      ext ω
      simp [Set.not_nonempty_iff_eq_empty]
    rw [he]
    change (law q).real {∅} = _
    rw [law, setBernoulli_real_singleton q (Set.empty_subset _) Set.finite_univ]
    simp [Set.ncard_univ, Nat.card_eq_fintype_card]
  have htrue : μ.real {True} = 1 - (1 - (q : ℝ)) ^ Fintype.card F := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext b; simp
    rw [he, measureReal_compl (measurableSet_singleton _), probReal_univ, hfalse]
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (orParameter q (Fintype.card F))).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [htrue]
    simp [bitLaw, Measure.real, orParameter]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hfalse]
    simp [bitLaw, Measure.real, orParameter]

 
theorem finite_image_lift {F : Type*} (f : F → E) {ω : Set F} (s : Finset E)
    (hs : (s : Set E) ⊆ f '' ω) :
    ∃ t : Finset F, (t : Set F) ⊆ ω ∧ f '' (t : Set F) = (s : Set E) := by
  have hex : ∃ t ⊆ f '' ω, t.Finite ∧ t = (s : Set E) :=
    ⟨s, hs, s.finite_toSet, rfl⟩
  obtain ⟨t, ht, htf, hti⟩ := Set.exists_subset_image_finite_and.mp hex
  exact ⟨htf.toFinset, by simpa using ht, by simpa using hti⟩

theorem finiteWitness_image_preimage {F : Type*} (f : F → E) (A : Set (Set E))
    (hA : FiniteWitness A) : FiniteWitness ((fun ω => f '' ω) ⁻¹' A) := by
  intro ω hω
  obtain ⟨s, hs, ha⟩ := hA (f '' ω) hω
  obtain ⟨t, ht, htI⟩ := finite_image_lift f s hs
  exact ⟨t, ht, by simpa only [Set.mem_preimage, htI] using ha⟩

theorem image_preimage_disjointOccurrence {F : Type*} (f : F → E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B ⊆
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  obtain ⟨s', hs', hsI⟩ := finite_image_lift f s hs
  obtain ⟨t', ht', htI⟩ := finite_image_lift f t ht
  refine ⟨s', t', hs', ht', ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxs : f x ∈ (s : Set E) := hsI ▸ Set.mem_image_of_mem f hx
    have hxt : f x ∈ (t : Set E) := htI ▸ Set.mem_image_of_mem f hy
    exact Finset.disjoint_left.mp hd hxs hxt
  · simpa only [Set.mem_preimage, hsI] using ha
  · simpa only [Set.mem_preimage, htI] using hb

end ORLift

section ORLaw
attribute [local instance] Classical.propDecidable

theorem map_exists_bitLaw (q : unitInterval) (F : Type*) [Fintype F] :
    (Measure.infinitePi (fun _ : F => bitLaw q)).map (fun f : F → Prop => ∃ j, f j) =
      bitLaw (orParameter q (Fintype.card F)) := by
  have h := map_nonempty q F
  unfold law at h
  rw [setBernoulli_eq_map, Measure.map_map (Measurable.of_discrete) measurable_setOfPred] at h
  simpa only [Set.mem_univ, Function.comp_def, Set.Nonempty, Set.mem_ofPred_eq,
    bernoulliMeasure_def, bitLaw] using h

theorem measurable_image_fst (F : Type*) [Fintype F] :
    Measurable (fun ω : Set (E × F) => Prod.fst '' ω) := by
  have hm : Measurable (fun ω : Set (E × F) => fun e => ∃ j : F, (e,j) ∈ ω) := by
    apply Measurable.of_eval
    intro e
    apply measurableSet_setOfPred.mp
    have he : {ω : Set (E × F) | ∃ j : F, (e,j) ∈ ω} =
        ⋃ j : F, {ω : Set (E × F) | (e,j) ∈ ω} := by ext ω; simp
    rw [he]
    exact MeasurableSet.iUnion fun j => measurableSet_setOfPred.mpr
      ((measurable_pi_apply (e,j)).comp MeasurableEquiv.setOfPred.symm.measurable)
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) =
      (fun f : E → Prop => {e | f e}) ∘ (fun ω e => ∃ j : F, (e,j) ∈ ω) := by
    funext ω
    ext e
    simp [Prod.exists]
  rw [he]
  exact measurable_setOfPred.comp hm

 
theorem law_map_image_fst (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set (E × F))).map (fun ω => Prod.fst '' ω) =
      law (orParameter q (Fintype.card F)) := by
  let c := MeasurableEquiv.curry E F Prop
  let b := fun f : E → F → Prop => fun e => ∃ j, f e j
  have hb : Measurable b := Measurable.of_eval
    (fun e => (Measurable.of_discrete : Measurable (fun f : F → Prop => ∃j, f j)).comp
      (measurable_pi_apply e))
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map (measurable_image_fst F) measurable_setOfPred]
  simp only [Set.mem_univ]
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) ∘ (fun f => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘ b ∘ c := by
    funext f
    ext e
    simp [b, c, Function.comp_def, Prod.exists]
  rw [he, ← Measure.map_map measurable_setOfPred (hb.comp c.measurable),
    ← Measure.map_map hb c.measurable]
  change ((Measure.infinitePi (fun _ : E × F => bitLaw q)).map c |>.map b |>.map
    (fun f : E → Prop => {e | f e})) = _
  rw [Measure.infinitePi_map_curry (fun (_ : E) (_ : F) => bitLaw q)]
  dsimp only [b]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  rw [map_exists_bitLaw q F]
  rw [setBernoulli_eq_map]
  rfl

 
theorem exists_orParameter (p : unitInterval) (hp : p < 1) :
    ∃ m : ℕ, ∃ q : unitInterval, (q : ℝ) ≤ 1 / 2 ∧ orParameter q m = p := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - (p : ℝ) by exact sub_pos.mpr hp)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let f := fun x : ℝ => 1 - (1-x)^m
  have hf : Continuous f := by fun_prop
  have h0 : f 0 = 0 := by simp [f]
  have hp' : (p : ℝ) ∈ Set.Icc (f 0) (f (1/2)) := by
    rw [h0]
    refine ⟨p.2.1, ?_⟩
    dsimp [f]
    norm_num at hm ⊢
    linarith
  obtain ⟨q, hq, hqp⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1/2)
    hf.continuousOn hp'
  refine ⟨m, ⟨q, hq.1, hq.2.trans (by norm_num)⟩, hq.2, ?_⟩
  apply Subtype.ext
  exact hqp

end ORLaw

section BK
attribute [local instance] Classical.propDecidable

theorem disjointOccurrence_subset_inter (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) : DisjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨s,t,hs,ht,_,ha,hb⟩
  exact ⟨hA hs ha, hB ht hb⟩

 

theorem bk [Countable E] (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  by_cases hp : p = 1
  · subst p
    by_cases hu : Set.univ ∈ DisjointOccurrence A B
    · have ha := (disjointOccurrence_subset_inter A B hA hB hu).1
      have hb := (disjointOccurrence_subset_inter A B hA hB hu).2
      simp [law, Measure.real, hu, ha, hb]
    · simp [law, Measure.real, hu]
      positivity
  · have hp' : p < 1 := lt_of_le_of_ne p.2.2 hp
    obtain ⟨m, q, hq, hqp⟩ := exists_orParameter p hp'
    let f : E × Fin m → E := Prod.fst
    let A' := (fun ω => f '' ω) ⁻¹' A
    let B' := (fun ω => f '' ω) ⁻¹' B
    have hreal (C : Set (Set E)) (hC : MeasurableSet C) :
        (law p).real C = (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' C) := by
      have hh := law_map_image_fst (E := E) q (Fin m)
      simp only [Fintype.card_fin, hqp] at hh
      rw [← hh]
      simp only [Measure.real, Measure.map_apply (measurable_image_fst (Fin m)) hC]
      rfl
    calc
      (law p).real (DisjointOccurrence A B) =
          (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' DisjointOccurrence A B) :=
        hreal _ (measurableSet_finiteWitness _ (disjointOccurrence_upper A B)
          (finiteWitness_disjointOccurrence A B))
      _ ≤ (law q).real (DisjointOccurrence A' B') :=
        measureReal_mono (image_preimage_disjointOccurrence f A B)
      _ ≤ (law q).real A' * (law q).real B' := bk_finiteWitness_half q hq A' B'
        (fun _ _ h hω => hA (Set.image_mono h) hω)
        (fun _ _ h hω => hB (Set.image_mono h) hω)
        (finiteWitness_image_preimage f A hfA) (finiteWitness_image_preimage f B hfB)
      _ = (law p).real A * (law p).real B := by
        rw [hreal A (measurableSet_finiteWitness A hA hfA),
          hreal B (measurableSet_finiteWitness B hB hfB)]

end BK

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_KernelMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ThreeArmProbability
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem bk_ennreal [Countable E] (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    law p (DisjointOccurrence A B) ≤ law p A * law p B := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  exact bk p A B hA hB hfA hfB



end ThreeArmProbability
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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabSecondMoment
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

lemma finiteWitness_conn_restricted (I : Set E) (x y : V) :
    FiniteWitness {ω | Conn G (ω ∩ I) x y} := by
  intro ω hω
  obtain ⟨s,hs,hconn⟩ := finiteWitness_conn G x y (ω ∩ I) hω
  refine ⟨s,fun e he => (hs he).1,?_⟩
  have hsub : (s : Set E) ⊆ (s : Set E) ∩ I := fun e he => ⟨he,(hs he).2⟩
  exact conn_mono G hsub hconn

lemma lintegral_restrictedLayerCount [Countable V] [Countable E]
    (I : Set E) (A : Set V) (p : unitInterval) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) =
      ∑' y, if y ∈ A then law p {ω | Conn G (ω ∩ I) x y} else 0 := by
  unfold restrictedLayerCount
  have hm (y : V) : Measurable (fun ω : Set E =>
      if y ∈ A ∧ Conn G (ω ∩ I) x y then (1 : ℝ≥0∞) else 0) := by
    have hi : Measurable (fun ω : Set E => ω ∩ I) :=
      measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
    exact Measurable.ite (measurable_const.and
      ((measurableSet_conn G x y).mem.comp hi)).setOf measurable_const measurable_const
  rw [lintegral_tsum (fun y => (hm y).aemeasurable)]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ A
  · simp only [hy,true_and,if_true]
    have hi : Measurable (fun ω : Set E => ω ∩ I) :=
      measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
    have hset : MeasurableSet {ω : Set E | Conn G (ω ∩ I) x y} :=
      (measurableSet_conn G x y).preimage hi
    simpa only [Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
      lintegral_indicator_one (μ := law p) hset
  · simp only [hy,false_and,if_false,lintegral_zero]

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

variable {V E : Type*} (G : BondGraph V E)

lemma conn_first_height_disjoint (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (I : Set E) (ω : Set E) (x y : V) (hx : f x < b) (hy : b ≤ f y)
    (hconn : Conn G (ω ∩ I) x y) :
    ∃ z, b ≤ f z ∧ f z ≤ b+R ∧ ω ∈ DisjointOccurrence
      {η | Conn G (η ∩ (I ∩ internalEdges G {v | f v ≤ b+R})) x z}
      {η | Conn G (η ∩ I) z y} := by
  obtain ⟨p₀⟩ := (conn_iff_reachable G (ω ∩ I) x y).mp hconn
  let p := p₀.toPath.val
  let S := p.support.toFinset.filter fun v => b ≤ f v
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support,hy⟩
  obtain ⟨z,hzS,hzp,hfirst⟩ := p.exists_mem_support_forall_mem_support_imp_eq S
    ⟨y,Finset.mem_filter.mpr ⟨hyS,p.end_mem_support⟩⟩
  have hz : b ≤ f z := (Finset.mem_filter.mp hzS).2
  have hbelow (v : V) (hv : v ∈ (p.takeUntil z hzp).support) (hvz : v ≠ z) : f v < b := by
    by_contra hn
    have hvS : v ∈ S := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (p.support_takeUntil_subset_support hzp hv),le_of_not_gt hn⟩
    exact hvz (hfirst v hvS hv)
  have hj {u v : V} (huv : (openSimpleGraph G (ω ∩ I)).Adj u v) : |f v-f u| ≤ R := by
    obtain ⟨e,_he,heq⟩ := huv.2
    exact hjump e u v (by rw [heq]; simp) (by rw [heq]; simp)
  have hzR : f z ≤ b+R := walk_endpoint_height_bound f R b hR hj (p.takeUntil z hzp) hx hbelow
  have hupper (v : V) (hv : v ∈ (p.takeUntil z hzp).support) : f v ≤ b+R := by
    by_cases hvz : v=z
    · simpa only [hvz] using hzR
    · have hh := hbelow v hv hvz
      linarith
  obtain ⟨a,ha,hea,hoa⟩ := walk_lift_bonds G (ω ∩ I) (p.takeUntil z hzp)
  obtain ⟨c,hc,hec,hoc⟩ := walk_lift_bonds G (ω ∩ I) (p.dropUntil z hzp)
  have hain (e : E) (he : e ∈ a) : e ∈ internalEdges G {v | f v ≤ b+R} := by
    intro v hv
    have hGe : G e ∈ (p.takeUntil z hzp).edges := hea ▸ List.mem_map_of_mem he
    exact hupper v (SimpleGraph.Walk.mem_support_of_mem_edges hGe hv)
  have haI : (a.toFinset : Set E) ⊆ I ∩ internalEdges G {v | f v ≤ b+R} := by
    intro e he
    exact ⟨(hoa e (List.mem_toFinset.mp he)).2,hain e (List.mem_toFinset.mp he)⟩
  have hcI : (c.toFinset : Set E) ⊆ I := fun e he => (hoc e (List.mem_toFinset.mp he)).2
  refine ⟨z,hz,hzR,a.toFinset,c.toFinset,?_,?_,?_,?_,?_⟩
  · intro e he
    exact (hoa e (List.mem_toFinset.mp he)).1
  · intro e he
    exact (hoc e (List.mem_toFinset.mp he)).1
  · apply Finset.disjoint_left.mpr
    intro e heA heC
    exact List.disjoint_left.mp (p₀.toPath.property.isTrail.disjoint_edges_takeUntil_dropUntil hzp)
      (hea ▸ List.mem_map_of_mem (List.mem_toFinset.mp heA))
      (hec ▸ List.mem_map_of_mem (List.mem_toFinset.mp heC))
  · have hh := ha.conn (fun e he => List.mem_toFinset.mpr he)
    have hsub : (a.toFinset : Set E) ⊆ (a.toFinset : Set E) ∩
        (I ∩ internalEdges G {v | f v ≤ b+R}) := fun e he => ⟨he,haI he⟩
    exact conn_mono G hsub hh
  · have hh := hc.conn (fun e he => List.mem_toFinset.mpr he)
    have hsub : (c.toFinset : Set E) ⊆ (c.toFinset : Set E) ∩ I := fun e he => ⟨he,hcI he⟩
    exact conn_mono G hsub hh

theorem first_height_connection_bound [Countable V] [Countable E]
    (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (I : Set E) (p : unitInterval) (x y : V) (hx : f x < b) (hy : b ≤ f y) :
    law p {ω | Conn G (ω ∩ I) x y} ≤
      ∑' z, if b ≤ f z ∧ f z ≤ b+R then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ b+R})) x z} *
          law p {ω | Conn G (ω ∩ I) z y} else 0 := by
  let J := I ∩ internalEdges G {v | f v ≤ b+R}
  let C := fun z => if b ≤ f z ∧ f z ≤ b+R then
    DisjointOccurrence {ω | Conn G (ω ∩ J) x z} {ω | Conn G (ω ∩ I) z y} else ∅
  have hsub : {ω | Conn G (ω ∩ I) x y} ⊆ ⋃ z, C z := by
    intro ω hω
    obtain ⟨z,hz,hzR,hd⟩ := conn_first_height_disjoint G f R b hR hjump I ω x y hx hy hω
    have hband : b ≤ f z ∧ f z ≤ b+R := ⟨hz,hzR⟩
    exact Set.mem_iUnion.mpr ⟨z,by simpa only [C,ite_eq_left hband] using hd⟩
  calc
    _ ≤ law p (⋃ z, C z) := measure_mono hsub
    _ ≤ ∑' z, law p (C z) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : b ≤ f z ∧ f z ≤ b+R
      · simp only [C,ite_eq_left hz]
        exact bk_ennreal p _ _
          (fun _ _ h hconn => conn_mono G (Set.inter_subset_inter_left _ h) hconn)
          (fun _ _ h hconn => conn_mono G (Set.inter_subset_inter_left _ h) hconn)
          (finiteWitness_conn_restricted G J x z) (finiteWitness_conn_restricted G I z y)
      · simp only [C,ite_eq_right hz,measure_empty,le_refl]

theorem first_height_layer_moment_bound [Countable V] [Countable E]
    (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (I : Set E) (A : Set V) (p : unitInterval) (x : V)
    (hx : f x < b) (hA : ∀ y ∈ A, b ≤ f y) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) ≤
      ∑' z, (if b ≤ f z ∧ f z ≤ b+R then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ b+R})) x z} else 0) *
          (∫⁻ ω, restrictedLayerCount G I A ω z ∂law p) := by
  simp_rw [lintegral_restrictedLayerCount]
  calc
    _ ≤ ∑' y, ∑' z, (if b ≤ f z ∧ f z ≤ b+R then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ b+R})) x z} else 0) *
          (if y ∈ A then law p {ω | Conn G (ω ∩ I) z y} else 0) := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : y ∈ A
      · simp only [ite_eq_left hy]
        have hh := first_height_connection_bound G f R b hR hjump I p x y hx (hA y hy)
        refine hh.trans_eq (tsum_congr fun z => ?_)
        by_cases hz : b ≤ f z ∧ f z ≤ b+R
        · rw [ite_eq_left hz,ite_eq_left hz]
        · rw [ite_eq_right hz,ite_eq_right hz,zero_mul]
      · simp only [ite_eq_right hy]
        exact bot_le
    _ = _ := by
      rw [ENNReal.tsum_comm]
      congr 1
      funext z
      exact ENNReal.tsum_mul_left

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntegerLayerFirstVisit
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

lemma integer_half_band (k m : ℤ) :
    ((m : ℝ)-1/2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ (m : ℝ)-1/2+1) ↔ k=m := by
  constructor
  · rintro ⟨hlo,hhi⟩
    have h₁ : (m : ℝ)-1 < k := by linarith
    have h₂ : (k : ℝ) < (m : ℝ)+1 := by linarith
    have h₁' : m-1 < k := by exact_mod_cast h₁
    have h₂' : k < m+1 := by exact_mod_cast h₂
    omega
  · rintro rfl
    constructor <;> linarith

lemma integer_half_ceiling (k m : ℤ) :
    ((k : ℝ) ≤ (m : ℝ)-1/2+1) ↔ k ≤ m := by
  constructor
  · intro h
    have hh : (k : ℝ) < (m : ℝ)+1 := by linarith
    have hh' : k < m+1 := by exact_mod_cast hh
    omega
  · intro h
    have hh : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    linarith

theorem integer_first_layer_moment_bound [Countable V] [Countable E]
    (f : V → ℤ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → f v ≤ f u+1 ∧ f u ≤ f v+1)
    (I : Set E) (A : Set V) (p : unitInterval) (x : V) (m : ℤ)
    (hx : f x < m) (hA : ∀ y ∈ A, m ≤ f y) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) ≤
      ∑' z, (if f z=m then
        law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ m})) x z} else 0) *
          (∫⁻ ω, restrictedLayerCount G I A ω z ∂law p) := by
  have hj : ∀ e u v, u ∈ G e → v ∈ G e → |(f v : ℝ)-(f u : ℝ)| ≤ 1 := by
    intro e u v hu hv
    obtain ⟨h₁,h₂⟩ := hjump e u v hu hv
    have h₁' : (f v : ℝ) ≤ (f u : ℝ)+1 := by exact_mod_cast h₁
    have h₂' : (f u : ℝ) ≤ (f v : ℝ)+1 := by exact_mod_cast h₂
    rw [abs_le]
    constructor <;> linarith
  have hx' : (f x : ℝ) < (m : ℝ)-1/2 := by
    have hh : f x ≤ m-1 := by omega
    have hh' : (f x : ℝ) ≤ (m : ℝ)-1 := by exact_mod_cast hh
    linarith
  have hA' : ∀ y ∈ A, (m : ℝ)-1/2 ≤ (f y : ℝ) := by
    intro y hy
    have hh : (m : ℝ) ≤ (f y : ℝ) := by exact_mod_cast hA y hy
    linarith
  have hh := first_height_layer_moment_bound G (fun v => (f v : ℝ)) 1 ((m : ℝ)-1/2)
    (by norm_num) hj I A p x hx' hA'
  have hD : {v : V | (f v : ℝ) ≤ (m : ℝ)-1/2+1} = {v | f v ≤ m} := by
    ext v
    exact integer_half_ceiling (f v) m
  simpa only [hD,integer_half_band] using hh

end Percolation.BenjaminiSchramm

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabLastMaximum
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

lemma conn_max_height_disjoint (f : V → ℝ) (I : Set E) (ω : Set E)
    (x y : V) (hconn : Conn G (ω ∩ I) x y) :
    ∃ z, f x ≤ f z ∧ f y ≤ f z ∧ ω ∈ DisjointOccurrence
      {η | Conn G (η ∩ (I ∩ internalEdges G {v | f v ≤ f z})) x z}
      {η | Conn G (η ∩ (I ∩ internalEdges G {v | f v ≤ f z})) z y} := by
  obtain ⟨p₀⟩ := (conn_iff_reachable G (ω ∩ I) x y).mp hconn
  let p := p₀.toPath.val
  obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image p.support.toFinset f
    ⟨x,List.mem_toFinset.mpr p.start_mem_support⟩
  have hzp : z ∈ p.support := List.mem_toFinset.mp hz
  have hu (v : V) (hv : v ∈ p.support) : f v ≤ f z := hmax v (List.mem_toFinset.mpr hv)
  obtain ⟨a,ha,hea,hoa⟩ := walk_lift_bonds G (ω ∩ I) (p.takeUntil z hzp)
  obtain ⟨c,hc,hec,hoc⟩ := walk_lift_bonds G (ω ∩ I) (p.dropUntil z hzp)
  have haI : (a.toFinset : Set E) ⊆ I ∩ internalEdges G {v | f v ≤ f z} := by
    intro e he
    refine ⟨(hoa e (List.mem_toFinset.mp he)).2,fun v hv => ?_⟩
    have hGe : G e ∈ (p.takeUntil z hzp).edges := hea ▸ List.mem_map_of_mem (List.mem_toFinset.mp he)
    exact hu v (p.support_takeUntil_subset_support hzp (SimpleGraph.Walk.mem_support_of_mem_edges hGe hv))
  have hcI : (c.toFinset : Set E) ⊆ I ∩ internalEdges G {v | f v ≤ f z} := by
    intro e he
    refine ⟨(hoc e (List.mem_toFinset.mp he)).2,fun v hv => ?_⟩
    have hGe : G e ∈ (p.dropUntil z hzp).edges := hec ▸ List.mem_map_of_mem (List.mem_toFinset.mp he)
    exact hu v (p.support_dropUntil_subset_support hzp (SimpleGraph.Walk.mem_support_of_mem_edges hGe hv))
  refine ⟨z,hu x p.start_mem_support,hu y p.end_mem_support,a.toFinset,c.toFinset,?_,?_,?_,?_,?_⟩
  · intro e he
    exact (hoa e (List.mem_toFinset.mp he)).1
  · intro e he
    exact (hoc e (List.mem_toFinset.mp he)).1
  · apply Finset.disjoint_left.mpr
    intro e heA heC
    exact List.disjoint_left.mp (p₀.toPath.property.isTrail.disjoint_edges_takeUntil_dropUntil hzp)
      (hea ▸ List.mem_map_of_mem (List.mem_toFinset.mp heA))
      (hec ▸ List.mem_map_of_mem (List.mem_toFinset.mp heC))
  · have hh := ha.conn (fun e he => List.mem_toFinset.mpr he)
    have hsub : (a.toFinset : Set E) ⊆ (a.toFinset : Set E) ∩
        (I ∩ internalEdges G {v | f v ≤ f z}) := fun e he => ⟨he,haI he⟩
    exact conn_mono G hsub hh
  · have hh := hc.conn (fun e he => List.mem_toFinset.mpr he)
    have hsub : (c.toFinset : Set E) ⊆ (c.toFinset : Set E) ∩
        (I ∩ internalEdges G {v | f v ≤ f z}) := fun e he => ⟨he,hcI he⟩
    exact conn_mono G hsub hh

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFirstMoments
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

lemma adjustedUpLayerMoment_le_sup (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (n : ℕ) (x : V) (u : ℝ) :
    G.adjustedUpLayerMoment a R p n x u ≤ G.supAdjustedUpLayerMoment a R p n :=
  le_iSup_of_le x (le_iSup_of_le u le_rfl)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BoundedLayerShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma restrictedLayerCount_expectation_le_row_bound (p : unitInterval)
    (C : ℝ≥0∞) (hrow : ∀ z, (∑' y, law p {ω | Conn G ω z y}) ≤ C)
    (I : Set E) (A : Set V) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) ≤ C := by
  rw [lintegral_restrictedLayerCount]
  apply le_trans _ (hrow x)
  apply ENNReal.tsum_le_tsum
  intro y
  split_ifs
  · exact measure_mono fun ω hω => conn_mono G Set.inter_subset_left hω
  · exact bot_le

theorem first_layer_moment_bound_with_row (p : unitInterval)
    (C : ℝ≥0∞) (hrow : ∀ z, (∑' y, law p {ω | Conn G ω z y}) ≤ C)
    (f : V → ℤ) (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      f w ≤ f v+1 ∧ f v ≤ f w+1)
    (I : Set E) (A : Set V) (x : V) (n : ℤ)
    (hx : f x < n) (hA : ∀ y ∈ A, n ≤ f y) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p) ≤
      (∫⁻ ω, restrictedLayerCount G (internalEdges G {v | f v ≤ n})
        {v | f v=n} ω x ∂law p)*C := by
  have hfirst := integer_first_layer_moment_bound G f hjump I A p x n hx hA
  have hprefix (z : V) :
      law p {ω | Conn G (ω ∩ (I ∩ internalEdges G {v | f v ≤ n})) x z} ≤
      law p {ω | Conn G (ω ∩ internalEdges G {v | f v ≤ n}) x z} :=
    measure_mono (fun ω hω => conn_mono G
      (Set.inter_subset_inter_right _ Set.inter_subset_right) hω)
  calc
    _ ≤ ∑' z, (if f z=n then
        law p {ω | Conn G (ω ∩ internalEdges G {v | f v ≤ n}) x z} else 0)*C := by
      apply hfirst.trans
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z=n
      · simp only [ite_eq_left hz]
        exact mul_le_mul' (hprefix z)
          (restrictedLayerCount_expectation_le_row_bound G p C hrow I A z)
      · simp only [ite_eq_right hz,zero_mul,le_refl]
    _ = _ := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      rw [lintegral_restrictedLayerCount]
      apply tsum_congr
      intro z
      by_cases hz : f z=n <;> simp [hz]

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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
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

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem adjustedHalfspaceHit_path_comparison [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) {x y : V} (w : G.fullGraph.Walk x y) (r t : ℝ) (hr : 0 ≤ r)
    (hw : ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v)
    (hxy : r ≤ G.orbitAdjustedHeight a x y) :
    (p : ℝ)^w.length * (G.law p).real (G.adjustedHalfspaceHit a y (-r) t) ≤
      (G.law p).real (G.adjustedHalfspaceHit a x 0 t) := by
  have hg : G.fullGraph = Percolation.openSimpleGraph G.ends Set.univ :=
    criticalModel_openGraph G.ends Set.univ
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by simpa only [← hg,id_eq] using h⟩
  obtain ⟨s,hs,hconn⟩ := walk_finite_open_restriction G.ends (w.map f)
    {v | 0 ≤ G.orbitAdjustedHeight a x v} (by
      intro v hv
      have hv' : v ∈ w.support := by
        rw [SimpleGraph.Walk.support_map] at hv
        change v ∈ w.support.map id at hv
        simpa only [List.map_id_fun,id_eq] using hv
      exact hw v hv')
  have hslen : s.card ≤ w.length := by simpa only [SimpleGraph.Walk.length_map] using hs
  let F : Set (Set E) := {ω | (s : Set E) ⊆ ω}
  let B := G.adjustedHalfspaceHit a y (-r) t
  have hF : IsUpperSet F := fun _ _ hωη hω => hω.trans hωη
  have hfF : Percolation.FiniteWitness F := fun _ hω => ⟨s,hω,Set.Subset.rfl⟩
  have hsub : F ∩ B ⊆ G.adjustedHalfspaceHit a x 0 t := by
    rintro ω ⟨hω,⟨z,hz,hyz⟩⟩
    have hyz' : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | 0 ≤ G.orbitAdjustedHeight a x v}) y z := by
      apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
        (Percolation.internalEdges_mono G.ends ?_)) hyz
      intro v hv
      change -r ≤ G.orbitAdjustedHeight a y v at hv
      change 0 ≤ G.orbitAdjustedHeight a x v
      rw [G.orbitAdjustedHeight_change_base hc hl a x y v]
      linarith
    refine ⟨z,?_,(hconn ω hω).trans hyz'⟩
    change t ≤ G.orbitAdjustedHeight a x z
    change t ≤ G.orbitAdjustedHeight a y z at hz
    rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
    linarith
  have hassoc := Percolation.association_finiteWitness p F B hF
    (G.adjustedHalfspaceHit_upper a y (-r) t) hfF
    (G.adjustedHalfspaceHit_finiteWitness a y (-r) t)
  have hprob : (G.law p).real F = (p : ℝ)^s.card := Percolation.finite_open_probability p s
  rw [show Percolation.law p = G.law p from rfl, hprob] at hassoc
  apply (le_trans ?_ hassoc).trans (measureReal_mono hsub)
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  exact pow_le_pow_of_le_one p.2.1 p.2.2 hslen

end CriticalPercolation.BondGraph

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NormalizedExponentComparison
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace Percolation.BenjaminiSchramm

lemma supermultiplicative_exp_rate_bound (P : ℝ → ℝ) (hP : ∀ t, 0 ≤ P t)
    (hzero : P 0 = 1) (hmul : ∀ s t, 0 ≤ s → 0 ≤ t → P s*P t ≤ P (s+t))
    (β C : ℝ) (hbound : ∀ t, 0 ≤ t → P t ≤ C*Real.exp (-β*t))
    (t : ℝ) (ht : 0 ≤ t) : P t ≤ Real.exp (-β*t) := by
  have hpow (n : ℕ) : P t^n ≤ P ((n : ℝ)*t) := by
    induction n with
    | zero => simp only [pow_zero,Nat.cast_zero,zero_mul,hzero,le_refl]
    | succ n ih =>
      calc
        _ = P t^n*P t := pow_succ _ _
        _ ≤ P ((n : ℝ)*t)*P t := mul_le_mul_of_nonneg_right ih (hP t)
        _ ≤ P ((n : ℝ)*t+t) := hmul _ _ (mul_nonneg (Nat.cast_nonneg n) ht) ht
        _ = _ := by congr 1; push_cast; ring
  by_contra hn
  have hlt : Real.exp (-β*t) < P t := lt_of_not_ge hn
  have hone : 1 < P t*Real.exp (β*t) := by
    have hh := mul_lt_mul_of_pos_right hlt (Real.exp_pos (β*t))
    have he : Real.exp (-β*t)*Real.exp (β*t)=1 := by
      rw [←Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rwa [he] at hh
  obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hone).eventually
    (eventually_gt_atTop C)).exists
  have hh := mul_le_mul_of_nonneg_right
    ((hpow n).trans (hbound _ (mul_nonneg (Nat.cast_nonneg n) ht)))
    (pow_nonneg (Real.exp_pos (β*t)).le n)
  have he : Real.exp (-β*((n : ℝ)*t))*Real.exp (β*t)^n=1 := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [←mul_pow,mul_assoc,he,mul_one] at hh
  exact hn.not_ge hh

variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

omit [Encodable V] in
theorem normalized_halfspace_uniform_of_infimal_bound
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hu : ¬ (criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ = μ)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (β : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) p t).toReal ≤ Real.exp (-β*t)) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → ∀ (x : V) (t : ℝ), 0 ≤ t →
      (law p).real ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤
        (p : ℝ)^(-(A*r+B)) * Real.exp (-β*t) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨A,B,hA,hB,hpath⟩ := H.stationaryOrbitHeight_orbit_above hHc hl hHq μ hμ hstat hu
  have hauto := H.stationaryOrbitWeight_aut μ
  refine ⟨A,B,hA,hB,fun r hr x t ht => ?_⟩
  let α : ℝ := (p : ℝ)^(A*r+B)
  have hα : 0 < α := Real.rpow_pos_of_pos hp _
  have hroot (u : V) :
      α*(law p).real (H.adjustedHalfspaceHit a x (-r) t) ≤
        (law p).real (H.adjustedHalfspaceHit a u 0 t) := by
    obtain ⟨y,w,horb,hlen,hw,hy⟩ := hpath r hr u (H.vertexOrbit x)
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact horb)
    change φ.vertex x = y at hφ
    have hcomp := H.adjustedHalfspaceHit_path_comparison hHc hl a p w r t hr hw hy
    have he := CriticalPercolation.BondGraph.Aut.adjustedHalfspaceHit_measure H a hauto φ p x (-r) t
    rw [hφ] at he
    have her := congrArg ENNReal.toReal he
    change (H.law p).real (H.adjustedHalfspaceHit a y (-r) t) =
      (H.law p).real (H.adjustedHalfspaceHit a x (-r) t) at her
    rw [her] at hcomp
    have hcoeff : α ≤ (p : ℝ)^w.length := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_ge hp p.2.2 hlen
    exact (mul_le_mul_of_nonneg_right hcoeff ENNReal.toReal_nonneg).trans hcomp
  have hmin : α*(law p).real (H.adjustedHalfspaceHit a x (-r) t) ≤
      (H.infimalAdjustedCrossing a p t).toReal := by
    have he : ENNReal.ofReal (α*(law p).real (H.adjustedHalfspaceHit a x (-r) t)) ≤
        H.infimalAdjustedCrossing a p t := by
      apply le_iInf
      intro u
      exact ENNReal.ofReal_le_of_le_toReal (hroot u)
    have hf := ENNReal.toReal_mono
      (ne_top_of_le_ne_top ENNReal.one_ne_top (H.infimalAdjustedCrossing_le_one a p t)) he
    have hnonneg : 0 ≤ α*(law p).real (H.adjustedHalfspaceHit a x (-r) t) :=
      mul_nonneg hα.le measureReal_nonneg
    rwa [ENNReal.toReal_ofReal hnonneg] at hf
  have hh := hmin.trans (hbound t ht)
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hα.le)
  rw [← mul_assoc,inv_mul_cancel₀ hα.ne',one_mul] at hh'
  have he : α⁻¹ = (p : ℝ)^(-(A*r+B)) := by
    exact (Real.rpow_neg p.2.1 _).symm
  rwa [he] at hh'

theorem normalized_crossing_real_bound
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (p : unitInterval) (β : ℝ) (hβ : 0 ≤ β)
    (hbound : ∀ n : ℕ,
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) p n).toReal ≤ Real.exp (-β*n)) :
    ∀ t : ℝ, 0 ≤ t → ((criticalModel G).infimalAdjustedCrossing
      ((criticalModel G).stationaryOrbitWeight μ) p t).toReal ≤ Real.exp (-β*t) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  obtain ⟨m,M,hm,hbounds⟩ := H.stationaryOrbitWeight_uniform_bounds
    (criticalModel_connected G hc) hl μ hμ
  have hne (t : ℝ) : H.infimalAdjustedCrossing a p t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (H.infimalAdjustedCrossing_le_one a p t)
  have hmul (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      (H.infimalAdjustedCrossing a p s).toReal*(H.infimalAdjustedCrossing a p t).toReal ≤
        (H.infimalAdjustedCrossing a p (s+t)).toReal := by
    simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono (hne (s+t))
      (H.infimalAdjustedCrossing_supermultiplicative (criticalModel_connected G hc) hl
        (criticalModel_quasiTransitive G hq) a m M hm hbounds p hs ht)
  apply supermultiplicative_exp_rate_bound _ (fun _ => ENNReal.toReal_nonneg)
    (by simp only [H.infimalAdjustedCrossing_zero,ENNReal.toReal_one]) hmul β (Real.exp β)
  intro t ht
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have hmono : H.infimalAdjustedCrossing a p t ≤ H.infimalAdjustedCrossing a p ⌊t⌋₊ := by
    apply iInf_mono
    intro x
    apply measure_mono
    rintro ω ⟨y,hy,hxy⟩
    exact ⟨y,hfloor.trans hy,hxy⟩
  calc
    _ ≤ (H.infimalAdjustedCrossing a p ⌊t⌋₊).toReal := ENNReal.toReal_mono (hne _) hmono
    _ ≤ Real.exp (-β*(⌊t⌋₊ : ℝ)) := hbound _
    _ ≤ Real.exp β*Real.exp (-β*t) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := Nat.lt_floor_add_one t
      nlinarith

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerCrossingComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace Percolation.BenjaminiSchramm

lemma exponential_rate_le_of_bound (a b c C : ℝ) (hc : 0 < c)
    (h : ∀ n : ℕ, 0 < n → c*Real.exp (-a*n) ≤ C*Real.exp (-b*n)) : b ≤ a := by
  have hC : 0 < C := by
    have hh := h 1 (by norm_num)
    have hp : 0 < c*Real.exp (-a*(1 : ℕ)) := mul_pos hc (Real.exp_pos _)
    exact pos_of_mul_pos_left (hp.trans_le hh) (Real.exp_nonneg _)
  by_contra hn
  have hab : 0 < b-a := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨N,hN⟩ := exists_nat_gt ((Real.log C-Real.log c)/(b-a))
  let n := N+1
  have hh := Real.log_le_log (mul_pos hc (Real.exp_pos _)) (h n (Nat.succ_pos N))
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_mul hC.ne' (Real.exp_pos _).ne',
    Real.log_exp,Real.log_exp] at hh
  have hnn : (Real.log C-Real.log c)/(b-a) < (n : ℝ) :=
    hN.trans (by dsimp [n]; push_cast; linarith)
  have hn' := (div_lt_iff₀ hab).mp hnn
  linarith

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem adjustedHalfspaceHit_le_upLayerMoment
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (hn : 0 < n) (x : V) :
    G.law p (G.adjustedHalfspaceHit a x 0 (R*n)) ≤ G.supAdjustedUpLayerMoment a R p n*C := by
  let f := G.adjustedLayerIndex a R 0 x
  let I := Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight a x v}
  let A := {v | R*n ≤ G.orbitAdjustedHeight a x v}
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R 0 hR hjump x v w e hv hw
    change f v-1 ≤ f w ∧ f w ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by
    simp only [f,G.adjustedLayerIndex_self]
    exact_mod_cast hn
  have hA : ∀ y ∈ A, (n : ℤ) ≤ f y := by
    intro y hy
    change R*n ≤ G.orbitAdjustedHeight a x y at hy
    simp only [f,adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero]
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hR).mpr
    push_cast
    nlinarith
  have hindicator (ω : Set E) :
      (G.adjustedHalfspaceHit a x 0 (R*n)).indicator (fun _ => (1 : ℝ≥0∞)) ω ≤
        restrictedLayerCount G.ends I A ω x := by
    by_cases hω : ω ∈ G.adjustedHalfspaceHit a x 0 (R*n)
    · rw [Set.indicator_of_mem hω]
      obtain ⟨y,hy,hxy⟩ := hω
      apply le_trans _ (ENNReal.le_tsum y)
      exact (ite_eq_left ⟨hy,hxy⟩).symm.le
    · rw [Set.indicator_of_notMem hω]
      exact bot_le
  calc
    _ = ∫⁻ ω, (G.adjustedHalfspaceHit a x 0 (R*n)).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂G.law p :=
      (lintegral_indicator_one (G.measurableSet_adjustedHalfspaceHit _ _ _ _)).symm
    _ ≤ ∫⁻ ω, restrictedLayerCount G.ends I A ω x ∂G.law p := lintegral_mono hindicator
    _ ≤ _ := (first_layer_moment_bound_with_row G.ends p C hrow f hj I A x n hx hA).trans
      (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p n x 0) le_rfl)

theorem crossing_rate_ge_layer_rate [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞) (hC : C < ⊤)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (α β : ℝ) (hα : 0 ≤ α)
    (hlower : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
      c*Real.exp (-(α+ε)*m) ≤ (G.infimalAdjustedCrossing a p m).toReal)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      G.supAdjustedUpLayerMoment a R p n ≤ ENNReal.ofReal (K*Real.exp (-(β-ε)*n))) :
    β ≤ α*R := by
  have hcompare (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) : β-ε ≤ (α+δ)*R := by
    obtain ⟨c,hcpos,hcbd⟩ := hlower δ hδ
    obtain ⟨K,hK,hKbd⟩ := hupper ε hε
    have hc' : 0 < c*Real.exp (-(α+δ)) := mul_pos hcpos (Real.exp_pos _)
    apply exponential_rate_le_of_bound ((α+δ)*R) (β-ε)
      (c*Real.exp (-(α+δ))) (C.toReal*K) hc'
    intro n hn
    let m := ⌈R*(n : ℝ)⌉₊
    have hmlo : R*(n : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
    have hmhi : (m : ℝ) ≤ R*(n : ℝ)+1 := (Nat.ceil_lt_add_one (mul_nonneg hR.le (Nat.cast_nonneg n))).le
    have hmin : G.infimalAdjustedCrossing a p m ≤
        G.law p (G.adjustedHalfspaceHit a (Classical.arbitrary V) 0 (R*n)) := by
      apply (iInf_le _ (Classical.arbitrary V)).trans
      apply measure_mono
      rintro ω ⟨y,hy,hxy⟩
      exact ⟨y,hmlo.trans hy,hxy⟩
    have he : ENNReal.ofReal (c*Real.exp (-(α+δ)*m)) ≤
        C*ENNReal.ofReal (K*Real.exp (-(β-ε)*n)) := by
      calc
        _ ≤ G.infimalAdjustedCrossing a p m := ENNReal.ofReal_le_of_le_toReal (hcbd m)
        _ ≤ G.supAdjustedUpLayerMoment a R p n*C := hmin.trans
          (G.adjustedHalfspaceHit_le_upLayerMoment hc hl a R hR hjump p C hrow n hn _)
        _ ≤ ENNReal.ofReal (K*Real.exp (-(β-ε)*n))*C := mul_le_mul' (hKbd n) le_rfl
        _ = _ := mul_comm _ _
    have her := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hC.ne ENNReal.ofReal_ne_top) he
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg hK.le (Real.exp_nonneg _)),
      ENNReal.toReal_ofReal (mul_nonneg hcpos.le (Real.exp_nonneg _))] at her
    have hexp : Real.exp (-((α+δ)*R)*(n : ℝ)-(α+δ)) ≤ Real.exp (-(α+δ)*(m : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ = c*Real.exp (-((α+δ)*R)*(n : ℝ)-(α+δ)) := by rw [mul_assoc,←Real.exp_add]; congr 2; ring
      _ ≤ c*Real.exp (-(α+δ)*(m : ℝ)) := mul_le_mul_of_nonneg_left hexp hcpos.le
      _ ≤ _ := her.trans_eq (by ring)
  by_contra hn
  have hd : 0 < β-α*R := sub_pos.mpr (lt_of_not_ge hn)
  let ε := (β-α*R)/(2*(R+1))
  have hε : 0 < ε := div_pos hd (by positivity)
  have hh := hcompare ε ε hε hε
  have he : ε*(2*(R+1))=β-α*R := div_mul_cancel₀ _ (by positivity)
  nlinarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_MinimumHeightHit
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

lemma restrictedHit_upper (I : Set E) (x : V) (A : Set V) :
    IsUpperSet (restrictedHit G I x A) := by
  rintro ω η hωη ⟨y,hy,hxy⟩
  exact ⟨y,hy,conn_mono G (Set.inter_subset_inter_left _ hωη) hxy⟩

lemma restrictedHit_finiteWitness (I : Set E) (x : V) (A : Set V) :
    FiniteWitness (restrictedHit G I x A) := by
  rintro ω ⟨y,hy,hxy⟩
  obtain ⟨s,hs,hconn⟩ := finiteWitness_conn G x y _ hxy
  refine ⟨s,fun e he => (hs he).1,y,hy,?_⟩
  exact conn_mono G (show (s : Set E) ⊆ (s : Set E) ∩ I from fun e he => ⟨he,(hs he).2⟩) hconn

lemma unrestricted_hit_minimum_disjoint (f : V → ℝ) (x : V) (A : Set V)
    (ω : Set E) (hω : ω ∈ restrictedHit G Set.univ x A) :
    ∃ z, f z ≤ f x ∧ ω ∈ DisjointOccurrence {η | Conn G η x z}
      (restrictedHit G (internalEdges G {v | f z ≤ f v}) z A) := by
  obtain ⟨y,hy,hxy⟩ := hω
  obtain ⟨z,hzx,_hzy,s,t,hs,ht,hd,hxs,hyt⟩ :=
    conn_max_height_disjoint G (fun v => -f v) Set.univ ω x y hxy
  have hD : {v : V | -f v ≤ -f z}={v | f z ≤ f v} := by ext v; simp
  rw [Set.univ_inter,hD] at hxs hyt
  refine ⟨z,neg_le_neg_iff.mp hzx,s,t,hs,ht,hd,conn_mono G Set.inter_subset_left hxs,y,hy,hyt⟩

theorem unrestricted_hit_minimum_bound [Countable V] [Countable E]
    (f : V → ℝ) (p : unitInterval) (x : V) (A : Set V) :
    law p (restrictedHit G Set.univ x A) ≤
      ∑' z, if f z ≤ f x then law p {ω | Conn G ω x z} *
        law p (restrictedHit G (internalEdges G {v | f z ≤ f v}) z A) else 0 := by
  let B (z : V) := restrictedHit G (internalEdges G {v | f z ≤ f v}) z A
  let D (z : V) := if f z ≤ f x then DisjointOccurrence {ω | Conn G ω x z} (B z) else ∅
  have hs : restrictedHit G Set.univ x A ⊆ ⋃ z, D z := by
    intro ω hω
    obtain ⟨z,hz,hdis⟩ := unrestricted_hit_minimum_disjoint G f x A ω hω
    exact Set.mem_iUnion.mpr ⟨z,by simpa only [D,ite_eq_left hz] using hdis⟩
  calc
    _ ≤ law p (⋃ z, D z) := measure_mono hs
    _ ≤ ∑' z, law p (D z) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z ≤ f x
      · simp only [D,ite_eq_left hz]
        exact bk_ennreal p _ _ (fun _ _ h hc => conn_mono G h hc)
          (restrictedHit_upper G _ _ _) (finiteWitness_conn G x z)
            (restrictedHit_finiteWitness G _ _ _)
      · simp only [D,ite_eq_right hz,measure_empty,le_refl]

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem unrestricted_adjusted_upward_hit_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (C κ : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (t : ℝ) (hκ : ∀ z, G.law p (G.adjustedHalfspaceHit a z 0 t) ≤ κ) (x : V) :
    G.law p (restrictedHit G.ends Set.univ x {v | t ≤ G.orbitAdjustedHeight a x v}) ≤ C*κ := by
  let f := G.orbitAdjustedHeight a x
  let A := {v | t ≤ f v}
  have hcont (z : V) (hz : f z ≤ f x) :
      G.law p (restrictedHit G.ends (Percolation.internalEdges G.ends {v | f z ≤ f v}) z A) ≤ κ := by
    apply le_trans (measure_mono ?_) (hκ z)
    rintro ω ⟨y,hy,hzy⟩
    have hz0 : f z ≤ 0 := by simpa only [f,G.orbitAdjustedHeight_self] using hz
    have hdom : {v : V | f z ≤ f v} ⊆ {v | 0 ≤ G.orbitAdjustedHeight a z v} := by
      intro v hv
      change 0 ≤ G.orbitAdjustedHeight a z v
      have hh := G.orbitAdjustedHeight_change_base hc hl a x z v
      change f z ≤ f v at hv
      dsimp only [f] at hv
      linarith
    refine ⟨y,?_,Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
      (Percolation.internalEdges_mono G.ends hdom)) hzy⟩
    change t ≤ G.orbitAdjustedHeight a z y
    have hh := G.orbitAdjustedHeight_change_base hc hl a x z y
    change t ≤ f y at hy
    dsimp only [f] at hy hz0
    linarith
  calc
    _ ≤ ∑' z, if f z ≤ f x then G.law p {ω | Percolation.Conn G.ends ω x z} *
        G.law p (restrictedHit G.ends (Percolation.internalEdges G.ends {v | f z ≤ f v}) z A) else 0 :=
      unrestricted_hit_minimum_bound G.ends f p x A
    _ ≤ ∑' z, G.law p {ω | Percolation.Conn G.ends ω x z}*κ := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z ≤ f x
      · rw [ite_eq_left hz]
        exact mul_le_mul' le_rfl (hcont z hz)
      · rw [ite_eq_right hz]
        exact bot_le
    _ ≤ C*κ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul' (hrow x) le_rfl

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SubcriticalCrossingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem unrestricted_upward_bound_of_layer_rate_bs_oai
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (C : ℝ≥0∞) (hC : C < ⊤)
    (hrow : ∀ z, (∑' y, law p {ω | Conn G ω z y}) ≤ C)
    (β : ℝ)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      (criticalModel G).supAdjustedUpLayerMoment ((criticalModel G).stationaryOrbitWeight μ) R p n ≤
        ENNReal.ofReal (K*Real.exp (-(β-ε)*n))) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (x : V),
      law p (restrictedHit G Set.univ x
        {y | R*((n : ℝ)-1) ≤ (criticalModel G).orbitAdjustedHeight
          ((criticalModel G).stationaryOrbitWeight μ) x y}) ≤ ENNReal.ofReal (B*Real.exp (-β*n)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨α,hα,hαupper,hαlower,_hαlim⟩ := H.normalized_crossing_exponent hHc hl hHq μ hμ hstat hu p hp
  have hβα := H.crossing_rate_ge_layer_rate hHc hl a R hR hjump p C hC hrow α β hα hαlower hupper
  have hreal := normalized_crossing_real_bound G hc hl hq μ hμ p α hα hαupper
  obtain ⟨A,D,_hA,_hD,hroot⟩ := normalized_halfspace_uniform_of_infimal_bound G hc hl hq hu μ hμ hstat p hp α hreal
  let K : ℝ := (p : ℝ)^(-D)
  have hK : 0 < K := Real.rpow_pos_of_pos hp _
  let B := 1+C.toReal*K*Real.exp (α*R)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,fun n x => ?_⟩
  by_cases hn : n=0
  · subst n
    have hB1 : (1 : ℝ) ≤ B := by dsimp [B]; exact le_add_of_nonneg_right (by positivity)
    simpa only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using
      (prob_le_one (μ := law p)).trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hB1)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have ht : 0 ≤ R*((n : ℝ)-1) := mul_nonneg hR.le (by linarith)
  have hκ (z : V) : H.law p (H.adjustedHalfspaceHit a z 0 (R*((n : ℝ)-1))) ≤
      ENNReal.ofReal (K*Real.exp (-α*(R*((n : ℝ)-1)))) := by
    have hh := hroot 0 (le_refl 0) z (R*((n : ℝ)-1)) ht
    simp only [mul_zero,zero_add,neg_zero] at hh
    have he := ENNReal.ofReal_le_ofReal hh
    change ENNReal.ofReal ((H.law p (H.adjustedHalfspaceHit a z 0 (R*((n : ℝ)-1)))).toReal) ≤
      ENNReal.ofReal (K*Real.exp (-α*(R*((n : ℝ)-1)))) at he
    rwa [ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  have hh := H.unrestricted_adjusted_upward_hit_bound hHc hl a p C _ hrow _ hκ x
  have hexp : Real.exp (-α*(R*((n : ℝ)-1))) ≤ Real.exp (α*R)*Real.exp (-β*n) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc
    _ ≤ C*ENNReal.ofReal (K*Real.exp (-α*(R*((n : ℝ)-1)))) := hh
    _ = ENNReal.ofReal (C.toReal*K*Real.exp (-α*(R*((n : ℝ)-1)))) := by
      calc
        _ = ENNReal.ofReal C.toReal*ENNReal.ofReal (K*Real.exp (-α*(R*((n : ℝ)-1)))) := by
          rw [ENNReal.ofReal_toReal hC.ne]
        _ = _ := by rw [←ENNReal.ofReal_mul ENNReal.toReal_nonneg]; congr 1; ring
    _ ≤ ENNReal.ofReal ((C.toReal*K*Real.exp (α*R))*Real.exp (-β*n)) := by
      apply ENNReal.ofReal_le_ofReal
      have he := mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ C.toReal*K from mul_nonneg ENNReal.toReal_nonneg hK.le)
      simpa only [mul_assoc] using he
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      dsimp [B]
      linarith

end Percolation.BenjaminiSchramm

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Percolation.BenjaminiSchramm.unrestricted_upward_bound_of_layer_rate_bs_oai.{u_1, u_2} := @OAI.Percolation.BenjaminiSchramm.unrestricted_upward_bound_of_layer_rate_bs_oai.{u_1, u_2}
