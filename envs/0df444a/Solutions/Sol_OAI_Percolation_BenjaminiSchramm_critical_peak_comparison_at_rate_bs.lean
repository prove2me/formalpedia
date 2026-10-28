-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:22:07.903992+00:00
-- url     : https://prove2.me/submissions/46a72a56-a594-4e61-ba92-469cc1e8b3b7

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_finite_general_bs

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_Uniqueness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster events, invariant covers and uniqueness thresholds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section PercolationZeroOne
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] [Countable E] in
theorem infiniteClusters_nonempty_iff (G : BondGraph V E) (ω : Set E) :
    (infiniteClusters G ω).Nonempty ↔ ∃ x, (cluster G ω x).Infinite := by
  constructor
  · rintro ⟨C, hC, x, rfl⟩
    exact ⟨x, hC⟩
  · rintro ⟨x, hx⟩
    exact ⟨cluster G ω x, hx, x, rfl⟩

end PercolationZeroOne

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

 theorem degree_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (x : V) : degree G (a x) = degree G x :=
  (Nat.card_congr (stepEquiv G h x)).symm

 theorem exists_degree_bound (G : BondGraph V E) (hqt : QuasiTransitive G) :
    ∃ D : ℕ, 0 < D ∧ ∀ x, degree G x ≤ D := by
  obtain ⟨F, hF⟩ := hqt
  refine ⟨(∑ x ∈ F, degree G x) + 1, Nat.zero_lt_succ _, ?_⟩
  intro x
  obtain ⟨o, ho, a, b, hab, rfl⟩ := hF x
  rw [degree_aut G hab]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ho).trans (Nat.le_succ _)

end DegreeBound

section SmallParameter
attribute [local instance] Classical.propDecidable

theorem trailLength_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (TrailLength G x n) := by
  rintro ω η h ⟨y,l,hl,hn,hlen,ho⟩
  exact ⟨y,l,hl,hn,hlen,fun e he => h (ho e he)⟩

theorem finiteWitness_trailLength (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (TrailLength G x n) := by
  rintro ω ⟨y,l,hl,hn,hlen,ho⟩
  exact ⟨l.toFinset, fun e he => ho e (List.mem_toFinset.mp he),
    y,l,hl,hn,hlen, fun e he => List.mem_toFinset.mpr he⟩

theorem finiteWitness_edge (e : E) : FiniteWitness {ω : Set E | e ∈ ω} := by
  intro ω he
  exact ⟨{e}, by simpa using he, by simp⟩

theorem trailLength_succ_subset (G : BondGraph V E) (x : V) (n : ℕ) :
    TrailLength G x (n+1) ⊆ ⋃ d : Step G x,
      DisjointOccurrence {ω | d.val.1 ∈ ω} (TrailLength G d.val.2 n) := by
  rintro ω ⟨y,l,hl,hn,hlen,ho⟩
  cases hl with
  | nil => simp at hlen
  | @cons x z y l e he tail =>
    refine Set.mem_iUnion.mpr ⟨⟨(e,z),he⟩, {e}, l.toFinset, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using ho e (by simp)
    · intro e' he'; exact ho e' (by simpa using Or.inr (List.mem_toFinset.mp he'))
    · simpa using (List.nodup_cons.mp hn).1
    · simp
    · exact ⟨y,l,tail,(List.nodup_cons.mp hn).2, by simpa using hlen,
        fun e' he' => List.mem_toFinset.mpr he'⟩

theorem trailLength_probability_le [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (x : V) (n : ℕ) :
    (law p).real (TrailLength G x n) ≤ ((D : ℝ) * p) ^ n := by
  induction n generalizing x with
  | zero => simpa only [pow_zero] using (measureReal_le_one (μ := law p) (s := TrailLength G x 0))
  | succ n ih =>
    let : Fintype (Step G x) := (finite_steps G hloc x).fintype
    let F := fun d : Step G x =>
      DisjointOccurrence {ω : Set E | d.val.1 ∈ ω} (TrailLength G d.val.2 n)
    calc
      (law p).real (TrailLength G x (n+1)) ≤ (law p).real (⋃ d, F d) :=
        measureReal_mono (trailLength_succ_subset G x n)
      _ ≤ ∑ d, (law p).real (F d) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _d : Step G x, (p : ℝ) * ((D : ℝ) * p) ^ n := by
        apply Finset.sum_le_sum
        intro d _
        have hb := bk p {ω : Set E | d.val.1 ∈ ω} (TrailLength G d.val.2 n)
          (fun _ _ hω he => hω he) (trailLength_upper G d.val.2 n)
          (finiteWitness_edge _) (finiteWitness_trailLength G d.val.2 n)
        have heq : (law p).real {ω : Set E | d.val.1 ∈ ω} = (p : ℝ) := by
          simpa using finite_open_probability p {d.val.1}
        rw [heq] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left (ih d.val.2) p.2.1)
      _ ≤ (D : ℝ) * ((p : ℝ) * ((D : ℝ) * p) ^ n) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg p.2.1 (pow_nonneg (mul_nonneg (Nat.cast_nonneg D) p.2.1) n))
        exact_mod_cast (show Fintype.card (Step G x) ≤ D by
          simpa only [degree, Nat.card_eq_fintype_card] using hD x)
      _ = ((D : ℝ) * p) ^ (n+1) := by ring

 theorem Along.take {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) (n : ℕ) : ∃ z, Along G x (l.take n) z := by
  induction h generalizing n with
  | @nil z => exact ⟨z, by simpa using (Along.nil (G := G) z)⟩
  | @cons x z y l e he ht ih =>
    cases n with
    | zero => exact ⟨x,.nil x⟩
    | succ n =>
      obtain ⟨v,hv⟩ := ih n
      exact ⟨v,.cons e he hv⟩

 theorem infinite_cluster_subset_trailLength (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (n : ℕ) : {ω | (cluster G ω x).Infinite} ⊆ TrailLength G x n := by
  intro ω hω
  obtain ⟨y,hy,hyball⟩ := hω.exists_notMem_finite (finite_reachBall hloc x n)
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G hy
  have hlen : n ≤ l.length := by
    by_contra h
    exact hyball ((reachBall_mono G x (le_of_lt (Nat.lt_of_not_ge h))) hl.mem_reachBall)
  obtain ⟨z,hz⟩ := hl.take n
  exact ⟨z,l.take n,hz,hn.take,List.length_take_of_le hlen,
    fun e he => ho e (List.mem_of_mem_take he)⟩

 theorem infinite_cluster_probability_eq_zero_of_small [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp : (D : ℝ) * p < 1) (x : V) :
    law p {ω | (cluster G ω x).Infinite} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg (Nat.cast_nonneg D) p.2.1) hp)
  filter_upwards [] with n
  exact (measureReal_mono (infinite_cluster_subset_trailLength G hloc x n)).trans
    (trailLength_probability_le G hloc D hD p x n)

 theorem exists_infinite_cluster_probability_eq_zero_of_small [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp : (D : ℝ) * p < 1) :
    law p {ω | (infiniteClusters G ω).Nonempty} = 0 := by
  have heq : {ω | (infiniteClusters G ω).Nonempty} =
      ⋃ x : V, {ω | (cluster G ω x).Infinite} := by
    ext ω
    simp only [Set.mem_ofPred_eq, infiniteClusters_nonempty_iff, Set.mem_iUnion]
  rw [heq, measure_iUnion_null_iff]
  exact infinite_cluster_probability_eq_zero_of_small G hloc D hD p hp

 theorem pc_pos [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) :
    0 < pc G := by
  obtain ⟨D, hDpos, hD⟩ := exists_degree_bound G hqt
  let t : unitInterval := ⟨1 / ((D : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) D]⟩
  have ht : (0 : unitInterval) < t := by
    change (0 : ℝ) < 1 / ((D : ℝ) + 1)
    positivity
  apply ht.trans_le
  apply le_sInf
  intro p hp
  by_contra h
  have hp' : (p : ℝ) < 1 / ((D : ℝ) + 1) := lt_of_not_ge h
  have hsmall : (D : ℝ) * p < 1 := by
    have hmul := (lt_div_iff₀ (show (0 : ℝ) < D + 1 by positivity)).mp hp'
    nlinarith [p.2.1]
  have hz := exists_infinite_cluster_probability_eq_zero_of_small G hloc D hD p hsmall
  exact (ne_of_gt hp) hz

end SmallParameter

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_ClusterProducts
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster Products for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


theorem walk_conn_restrict_vertices (G : BondGraph V E) (S : Set E) {x y : V}
    (q : (openSimpleGraph G S).Walk x y) (D : Set V)
    (hD : ∀ z ∈ q.support, z ∈ D) : Conn G (S ∩ internalEdges G D) x y := by
  obtain ⟨l,hl,hm,ho⟩ := walk_lift_bonds G S q
  apply hl.conn
  intro e he
  refine ⟨ho e he,?_⟩
  intro z hz
  exact hD z (SimpleGraph.Walk.mem_support_of_mem_edges (hm ▸ List.mem_map_of_mem he) hz)

theorem conn_restrict_of_no_simpleVisit (G : BondGraph V E) (S : Set E)
    (A : Set V) (x y : V) (hc : Conn G S x y) (hn : ¬SimpleVisit G S A x y) :
    Conn G (S ∩ internalEdges G Aᶜ) x y := by
  obtain ⟨q⟩ := (conn_iff_reachable G S x y).mp hc
  exact walk_conn_restrict_vertices G S q.bypass Aᶜ
    (fun z hz ha => hn ⟨q.bypass,q.bypass_isPath,z,hz,ha⟩)

end DeletionGeometry
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExteriorCorridorGeometry
attribute [local instance] Classical.propDecidable Classical.decEq



theorem conn_restrict_away_from_cluster (G : BondGraph V E) (ω S : Set E)
    (hS : S ⊆ ω) (u x y : V) (hx : x ∉ cluster G ω u) (hc : Conn G S x y) :
    Conn G (S ∩ internalEdges G (cluster G ω u)ᶜ) x y := by
  apply conn_restrict_of_no_simpleVisit G S (cluster G ω u) x y hc
  rintro ⟨q,_,z,hz,hzu⟩
  have hxz : Conn G ω x z := conn_mono G hS
    ((conn_iff_reachable G S x z).mpr ⟨q.takeUntil z hz⟩)
  exact hx (hzu.trans (conn_symm G ω hxz))

end ExteriorCorridorGeometry
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

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedTransportENNReal
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
namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma enn_fiber_sum_root (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x : {x // x∈R.roots}) (y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  let := (G.stabilizerOrbit_finite hc hl x y).fintype
  rw [← (fiberEquiv G R x y).symm.tsum_eq]
  have hv (z : G.stabilizerOrbit x y) :
      ennRow G R F ((fiberEquiv G R x y).symm z) = F x y := by
    change F x z = F x y
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp z.property
    have hh := hF φ x y
    rwa [hx,hy] at hh
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (G.stabilizerOrbit x y) = G.suborbitCard x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]

lemma enn_fiber_sum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) (x y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ.vertex.symm y
  have hy : φ.vertex v = y := φ.vertex.apply_symm_apply y
  have hq : G.pairOrbit (φ.vertex u) y = G.pairOrbit u v := by
    rw [←hy,Aut.pairOrbit]
  rw [hq,enn_fiber_sum_root G R hc hl F hF ⟨u,hu⟩ v]
  change (G.suborbitCard u v : ℝ≥0∞) * F u v = _
  rw [←hy,Aut.suborbitCard,hF]

lemma tsum_ennRow (F : V → V → ℝ≥0∞) :
    (∑' p, ennRow G R F p) = ∑ x ∈ R.roots, ∑' y, F x y := by
  change (∑' p : {x // x∈R.roots} × V, F p.1 p.2) = _
  rw [ENNReal.tsum_prod (f := fun (x : {x // x∈R.roots}) y => F x y)]
  simp only [tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => ∑' y, F x y)

lemma tilted_massTransport_ennreal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) :
    (∑ x ∈ R.roots, ∑' y, F x y) =
      ∑ y ∈ R.roots, ∑' x, F x y * G.stabilizerWeight y x := by
  let F' := fun x y => F y x * G.stabilizerWeight x y
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := by
    simp only [F',hF,Aut.stabilizerWeight]
  have heq : (∑' p, ennRow G R F p) = (∑' p, ennRow G R F' p) := by
    calc
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q}, ennRow G R F p :=
        (ENNReal.tsum_fiberwise _ _).symm
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          ennRow G R F' p := by
        apply tsum_congr
        intro q
        induction q using Quotient.inductionOn' with
        | h p =>
          change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2}, ennRow G R F z) =
            ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1}, ennRow G R F' z
          rw [enn_fiber_sum G R hc hl F hF,enn_fiber_sum G R hc hl F' hF']
          have hbal : (G.suborbitCard p.2 p.1 : ℝ≥0∞) * G.stabilizerWeight p.2 p.1 =
              (G.suborbitCard p.1 p.2 : ℝ≥0∞) := by
            unfold stabilizerWeight
            rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _),
              G.suborbitCard_mul_modularRatio hc hl,ENNReal.ofReal_natCast]
          simp only [F']
          rw [mul_left_comm, hbal, mul_comm]
      _ = ∑' p, ennRow G R F' p :=
        (G.swapPairOrbit.tsum_eq _).trans (ENNReal.tsum_fiberwise _ _)
  rw [tsum_ennRow G R F,tsum_ennRow G R F'] at heq
  exact heq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RandomTiltedTransport
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
variable {V E : Type*} [Countable V] (G : BondGraph V E)

omit [Countable V] in
lemma expected_enn_transport_aut (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (φ : G.Aut) (x y : V) :
    (∫⁻ ω, F ω (φ.vertex x) (φ.vertex y) ∂G.law p) = ∫⁻ ω, F ω x y ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [lintegral_map (hm _ _) (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [ha]

lemma OrbitRepresentatives.random_tilted_transport (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y) :
    (∑ x ∈ R.roots, ∫⁻ ω, ∑' y, F ω x y ∂G.law p) =
      ∑ y ∈ R.roots, ∫⁻ ω, ∑' x, F ω x y * G.stabilizerWeight y x ∂G.law p := by
  simp_rw [lintegral_tsum (fun y => (hm _ y).aemeasurable),
    lintegral_tsum (fun x => ((hm x _).mul_const _).aemeasurable),
    lintegral_mul_const _ (hm _ _)]
  exact OrbitRepresentatives.tilted_massTransport_ennreal G R hc hl _ (G.expected_enn_transport_aut p F hm ha)

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HarmonicHeightDescent
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

lemma height_harmonic_flat_or_fall (hl : G.LocallyFinite) (f : V → ℝ)
    (hf : ∀ x, (∑ y ∈ (G.finite_neighbors hl x).toFinset, Real.exp (f y-f x)) =
      G.modularWalkDegree x) (x : V) :
    (∃ y, G.fullGraph.Adj x y ∧ f y < f x) ∨
      (∀ y, G.fullGraph.Adj x y → f y=f x) := by
  by_cases hd : ∃ y, G.fullGraph.Adj x y ∧ f y < f x
  · exact Or.inl hd
  right
  have hle (y : V) (hy : y ∈ (G.finite_neighbors hl x).toFinset) :
      1 ≤ Real.exp (f y-f x) := by
    apply Real.one_le_exp_iff.mpr
    exact sub_nonneg.mpr (le_of_not_gt
      (fun h => hd ⟨y,(G.finite_neighbors hl x).mem_toFinset.mp hy,h⟩))
  have hs : (∑ _y ∈ (G.finite_neighbors hl x).toFinset, (1 : ℝ)) =
      ∑ y ∈ (G.finite_neighbors hl x).toFinset, Real.exp (f y-f x) := by
    rw [hf,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp only [modularWalkDegree,Set.ncard_eq_toFinset_card _ (G.finite_neighbors hl x)]
  intro y hxy
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp hs y
    ((G.finite_neighbors hl x).mem_toFinset.mpr hxy)
  exact sub_eq_zero.mp (Real.exp_injective (by simpa only [Real.exp_zero] using he.symm))

theorem stationaryOrbitHeight_descent [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (x : V) :
    ∃ y, ∃ w : G.fullGraph.Walk x y,
      (∀ v ∈ w.support, G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0) ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y < 0 := by
  let f := G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x
  have hself : f x=0 := G.orbitAdjustedHeight_self _ x
  obtain ⟨y,hy⟩ := G.orbitAdjustedHeight_nonconstant hc hl _ (G.stationaryOrbitWeight_aut μ) hu x
  have hhar (v : V) : (∑ y ∈ (G.finite_neighbors hl v).toFinset, Real.exp (f y-f v)) =
      G.modularWalkDegree v := by
    have he (y : V) : f y-f v=G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v y := by
      dsimp [f]
      rw [G.orbitAdjustedHeight_change_base hc hl _ x v y,add_sub_cancel_left]
    simp_rw [he]
    exact G.stationaryOrbitHeight_harmonic hc hl hq μ hμ hstat v
  have hfall (v : V) : (∃ z, G.fullGraph.Adj v z ∧ -f v < -f z) ∨
      (∀ z, G.fullGraph.Adj v z → -f z= -f v) := by
    rcases G.height_harmonic_flat_or_fall hl f hhar v with ⟨z,hvz,hz⟩ | hflat
    · exact Or.inl ⟨z,hvz,by linarith⟩
    · exact Or.inr fun z hz => congrArg Neg.neg (hflat z hz)
  have hy' : f y ≠ f x := by simpa only [hself] using hy
  obtain ⟨z,w,hw,hz⟩ := G.harmonic_ascent_walk (fun v => -f v) hfall
    (hc x y).some (fun he => hy' (neg_injective he))
  refine ⟨z,w,?_,?_⟩
  · intro v hv
    have hh := hw v hv
    rw [hself] at hh
    change f v ≤ 0
    linarith
  · rw [hself] at hz
    change f z < 0
    linarith

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_UniformHeightDescent
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

theorem stationaryOrbitHeight_uniform_descent [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L : ℕ, ∀ x, ∃ y, ∃ w : G.fullGraph.Walk x y,
      w.length ≤ L ∧
      (∀ v ∈ w.support, G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0) ∧
      G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ -ε := by
  let : Nonempty G.VertexOrbit := ⟨G.vertexOrbit (Classical.arbitrary V)⟩
  choose y w hw hr using fun i : G.VertexOrbit =>
    G.stationaryOrbitHeight_descent hc hl hq μ hμ hstat hu i.out
  let a := G.stationaryOrbitWeight μ
  let fall : G.VertexOrbit → ℝ := fun i => -G.orbitAdjustedHeight a i.out (y i)
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ fall Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ
    (fun k : G.VertexOrbit => (w k).length) Finset.univ_nonempty
  refine ⟨fall i,neg_pos.mpr (hr i),(w j).length,fun x => ?_⟩
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
    change G.orbitAdjustedHeight a x (φ.vertex z) ≤ 0
    rw [← hφ,G.orbitAdjustedHeight_aut a (G.stationaryOrbitWeight_aut μ)]
    exact hw k z hz
  · change G.orbitAdjustedHeight a x (φ.vertex (y k)) ≤ -fall i
    rw [← hφ,G.orbitAdjustedHeight_aut a (G.stationaryOrbitWeight_aut μ)]
    have hh := hi k (Finset.mem_univ _)
    dsimp [fall] at hh ⊢
    linarith

lemma height_descent_iterate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (L : ℕ)
    (hstep : ∀ x, ∃ y, ∃ w : G.fullGraph.Walk x y, w.length ≤ L ∧
      (∀ v ∈ w.support, G.orbitAdjustedHeight a x v ≤ 0) ∧ G.orbitAdjustedHeight a x y ≤ -ε)
    (n : ℕ) (x : V) :
    ∃ y, ∃ w : G.fullGraph.Walk x y, w.length ≤ n*L ∧
      (∀ v ∈ w.support, G.orbitAdjustedHeight a x v ≤ 0) ∧
      G.orbitAdjustedHeight a x y ≤ -(n*ε) := by
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
        exact add_nonpos (hr.trans (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) hε))) (hq v hv)
    · rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
      push_cast
      nlinarith

theorem stationaryOrbitHeight_orbit_below [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → ∀ x (j : G.VertexOrbit),
      ∃ y, ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y = j ∧
        (w.length : ℝ) ≤ A*r+B ∧
        (∀ v ∈ w.support, G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0) ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ -r := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_descent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  obtain ⟨N,D,hD,hconn⟩ := G.height_uniform_orbit_connection_abs hc a (G.stationaryOrbitWeight_aut μ)
  let A : ℝ := (L : ℝ)/ε+1
  let B : ℝ := (D/ε+1)*L+N
  refine ⟨A,B,by dsimp [A]; positivity,by dsimp [B]; positivity,fun r hr x j => ?_⟩
  let n : ℕ := ⌈(r+D)/ε⌉₊
  have hn : r+D ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil ((r+D)/ε))
  have hn' : (n : ℝ) ≤ (r+D)/ε+1 :=
    (Nat.ceil_lt_add_one (div_nonneg (add_nonneg hr hD) hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_descent_iterate hc hl a ε hε.le L hstep n x
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
      have hv' := (abs_le.mp (hq v hv)).2
      linarith
  · rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
    have hz := (abs_le.mp (hq z q.end_mem_support)).2
    linarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BoundedOrbitDescent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace Percolation.BenjaminiSchramm

lemma walk_height_support_bound {V : Type*} {H : SimpleGraph V}
    (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hj : ∀ {v w}, H.Adj v w → |f w-f v| ≤ R)
    {x y : V} (p : H.Walk x y) :
    ∀ v ∈ p.support, |f v-f x| ≤ (p.length : ℝ)*R := by
  induction p with
  | @nil u =>
    intro v hv
    have he : v=u := List.mem_singleton.mp hv
    simp only [he,sub_self,abs_zero,SimpleGraph.Walk.length_nil,Nat.cast_zero,zero_mul,le_refl]
  | @cons x z y hxy p ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simp only [sub_self,abs_zero,SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
      positivity
    · calc
        _ = |(f v-f z)+(f z-f x)| := by congr 1; ring
        _ ≤ |f v-f z|+|f z-f x| := abs_add_le _ _
        _ ≤ (p.length : ℝ)*R+R := add_le_add (ih v hv) (hj hxy)
        _ = _ := by rw [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]; ring

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_bounded_orbit_below [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ N : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ x (j : G.VertexOrbit), ∃ y,
      ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y=j ∧ w.length ≤ N ∧
        (∀ v ∈ w.support, -M ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0) ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ -R := by
  obtain ⟨A,B,hA,hB,hpath⟩ := G.stationaryOrbitHeight_orbit_below hc hl hq μ hμ hstat hu
  let N : ℕ := ⌈A*R+B⌉₊
  let M : ℝ := (N : ℝ)*R+R
  refine ⟨N,M,by dsimp [M]; positivity,fun x j => ?_⟩
  obtain ⟨y,w,hy,hlen,hw,hend⟩ := hpath R hR.le x j
  have hlenN : w.length ≤ N := by
    exact_mod_cast hlen.trans (Nat.le_ceil (A*R+B))
  let a := G.stationaryOrbitWeight μ
  let f := G.orbitAdjustedHeight a x
  have hj {v v' : V} (hv : G.fullGraph.Adj v v') : |f v'-f v| ≤ R := by
    obtain ⟨⟨e,_he,heq⟩,_hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hv
    have hh := hjump e v v' (by rw [heq]; simp) (by rw [heq]; simp)
    have he : f v'-f v=G.orbitAdjustedHeight a v v' := by
      dsimp [f]
      rw [G.orbitAdjustedHeight_change_base hc hl _ x v v',add_sub_cancel_left]
    rwa [he]
  refine ⟨y,w,hy,hlenN,fun v hv => ⟨?_,hw v hv⟩,hend⟩
  have hh := walk_height_support_bound f R hR.le hj w v hv
  have hf : f x=0 := G.orbitAdjustedHeight_self a x
  rw [hf,sub_zero] at hh
  have hN : (w.length : ℝ)*R ≤ (N : ℝ)*R :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlenN) hR.le
  have hv' := (abs_le.mp hh).1
  change -M ≤ f v
  dsimp [M]
  linarith

end CriticalPercolation.BondGraph

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

end CriticalPercolation.BernoulliProduct

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

end Percolation.BenjaminiSchramm

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

theorem conn_last_exit_frontier (ω : Set E) (S : Set V) {x y : V}
    (hx : x ∈ S) (hy : y ∉ S) (hc : Conn G ω x y) :
    ∃ z ∈ openFrontier G ω S, Conn G (ω \ ballIncidentEdges G S) z y := by
  revert hy
  induction hc with
  | refl => exact fun hy => (hy hx).elim
  | @tail a b hxa hab ih =>
    intro hy
    obtain ⟨e,he,heq⟩ := hab
    by_cases ha : a ∈ S
    · exact ⟨b,⟨hy,a,ha,e,he,heq⟩,conn_refl G _ b⟩
    · obtain ⟨z,hz,hza⟩ := ih ha
      refine ⟨z,hz,hza.tail ⟨e,⟨he,?_⟩,heq⟩⟩
      rintro ⟨u,hu,hue⟩
      rw [heq,Sym2.mem_iff] at hue
      rcases hue with rfl | rfl
      · exact ha hu
      · exact hy hu

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NormalizedLayerTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitAdjustedHeight_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (x y : V) :
    G.orbitAdjustedHeight a y x = -G.orbitAdjustedHeight a x y := by
  have hh := G.orbitAdjustedHeight_change_base hc hl a x y x
  rw [G.orbitAdjustedHeight_self] at hh
  linarith

lemma orbitAdjustedHeight_exp_balance (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ha : ∀ x, 0 < a x) (x y : V) :
    ENNReal.ofReal (a x)*G.stabilizerWeight y x =
      ENNReal.ofReal (a y)*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) := by
  rw [stabilizerWeight,←ENNReal.ofReal_mul (ha x).le,
    ←ENNReal.ofReal_mul (ha y).le]
  congr 1
  rw [orbitAdjustedHeight,modularLogHeight,Real.exp_sub,Real.exp_add,
    Real.exp_log (G.modularRatio_pos hc hl x y),Real.exp_log (ha x),Real.exp_log (ha y)]
  field_simp [(ha y).ne']

theorem OrbitRepresentatives.random_normalized_tilted_transport [Countable V]
    (R : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (hF : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y)=F ω x y) :
    (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, ∑' y, F ω x y ∂G.law p)) =
      ∑ y ∈ R.roots, ENNReal.ofReal (a y)*
        (∫⁻ ω, ∑' x, F ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ∂G.law p) := by
  have hh := OrbitRepresentatives.random_tilted_transport G R hc hl p
    (fun ω x y => ENNReal.ofReal (a x)*F ω x y)
    (fun x y => measurable_const.mul (hm x y))
    (fun φ ω x y => by rw [ha φ x,hF φ ω x y])
  have hin (ω : Set E) (y : V) :
      (∑' x, (ENNReal.ofReal (a x)*F ω x y)*G.stabilizerWeight y x) =
        ENNReal.ofReal (a y)*(∑' x, F ω x y*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) := by
    rw [←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro x
    calc
      _ = F ω x y*(ENNReal.ofReal (a x)*G.stabilizerWeight y x) := by ring
      _ = F ω x y*(ENNReal.ofReal (a y)*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) := by
        rw [G.orbitAdjustedHeight_exp_balance hc hl a hapos x y]
      _ = _ := by ring
  simp_rw [ENNReal.tsum_mul_left,hin,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hh
  exact hh

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakHalfspaceGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedStrictHalfspacePeak_unique
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (b : ℝ)
    (ω : Set E) (base x y : V)
    (hxy : G.adjustedHalfspaceConn a b ω base x y)
    (hx : G.adjustedStrictHalfspacePeak a b ω base x)
    (hy : G.adjustedStrictHalfspacePeak a b ω base y) : x=y := by
  by_contra hne
  have hh := hx y hxy (Ne.symm hne)
  have hh' := hy x (Percolation.conn_symm G.ends _ hxy) hne
  rw [G.orbitAdjustedHeight_reverse hc hl a x y] at hh'
  linarith

lemma strictPeakBandTransport_outgoing
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (y : V) :
    (∑' x, G.strictPeakBandTransport a r l u ω y x) ≤
      if ω ∈ restrictedHit G.ends (Percolation.internalEdges G.ends
        {z | -r ≤ G.orbitAdjustedHeight a y z}) y
          {z | -u ≤ G.orbitAdjustedHeight a y z} then 1 else 0 := by
  let P (x : V) := G.adjustedHalfspaceConn a (-r) ω y y x ∧
    G.adjustedStrictHalfspacePeak a (-r) ω y x ∧
      -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l
  by_cases hex : ∃ x, P x
  · obtain ⟨x,hx⟩ := hex
    have hhit : ω ∈ restrictedHit G.ends (Percolation.internalEdges G.ends
        {z | -r ≤ G.orbitAdjustedHeight a y z}) y {z | -u ≤ G.orbitAdjustedHeight a y z} :=
      ⟨x,hx.2.2.1,hx.1⟩
    rw [ite_eq_left hhit,tsum_eq_single x]
    · exact (ite_eq_left hx).le
    · intro z hzx
      apply ite_eq_right
      intro hz
      exact hzx (G.adjustedStrictHalfspacePeak_unique hc hl a (-r) ω y z x
        ((Percolation.conn_symm G.ends _ hz.1).trans hx.1) hz.2.1 hx.2.1)
  · have hz (x : V) : G.strictPeakBandTransport a r l u ω y x=0 :=
      ite_eq_right (fun h => hex ⟨x,h⟩)
    rw [ENNReal.tsum_eq_zero.mpr hz]
    exact bot_le

lemma strictPeakSlabBandTransport_incoming_lower
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (x y : V) :
    ENNReal.ofReal (Real.exp l)*G.strictPeakSlabBandTransport a r l u ω x y ≤
      G.strictPeakBandTransport a r l u ω y x *
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
  by_cases hp : G.adjustedStrictHalfspacePeak a (l-r) ω x x ∧
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | u-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ 0}) x y ∧
        l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u
  · have hconn : G.adjustedHalfspaceConn a (-r) ω y y x := by
      apply Percolation.conn_symm G.ends _
      apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
        (Percolation.internalEdges_mono G.ends ?_)) hp.2.1
      intro z hz
      have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
      change u-r ≤ G.orbitAdjustedHeight a x z ∧ _ at hz
      change -r ≤ G.orbitAdjustedHeight a y z
      linarith [hp.2.2.2,hz.1]
    have hpeak : G.adjustedStrictHalfspacePeak a (-r) ω y x := by
      intro z hz hzx
      apply hp.1 z _ hzx
      apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
        (Percolation.internalEdges_mono G.ends ?_)) hz
      intro v hv
      have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
      change -r ≤ G.orbitAdjustedHeight a y v at hv
      change l-r ≤ G.orbitAdjustedHeight a x v
      linarith [hp.2.2.1]
    have ht : G.adjustedHalfspaceConn a (-r) ω y y x ∧
        G.adjustedStrictHalfspacePeak a (-r) ω y x ∧
          -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l := by
      rw [G.orbitAdjustedHeight_reverse hc hl a x y]
      exact ⟨hconn,hpeak,by linarith [hp.2.2.2],by linarith [hp.2.2.1]⟩
    simp only [strictPeakSlabBandTransport,strictPeakBandTransport,ite_eq_left hp,
      ite_eq_left ht,mul_one,one_mul]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hp.2.2.1)
  · simp only [strictPeakSlabBandTransport,ite_eq_right hp,mul_zero]
    exact bot_le

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakHalfspaceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedHalfspaceConn_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (b : ℝ)
    (φ : G.Aut) (ω : Set E) (base x y : V) :
    G.adjustedHalfspaceConn a b (φ.edge '' ω) (φ.vertex base) (φ.vertex x) (φ.vertex y) ↔
      G.adjustedHalfspaceConn a b ω base x y := by
  have hD : φ.vertex ⁻¹' {z | b ≤ G.orbitAdjustedHeight a (φ.vertex base) z} =
      {z | b ≤ G.orbitAdjustedHeight a base z} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | b ≤ G.orbitAdjustedHeight a (φ.vertex base) z}) =
      ω ∩ Percolation.internalEdges G.ends {z | b ≤ G.orbitAdjustedHeight a base z} := by
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ←Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  unfold adjustedHalfspaceConn
  rw [←Percolation.conn_aut_iff G.ends φ.preserves,hmask]

lemma adjustedStrictHalfspacePeak_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (b : ℝ)
    (φ : G.Aut) (ω : Set E) (base x : V) :
    G.adjustedStrictHalfspacePeak a b (φ.edge '' ω) (φ.vertex base) (φ.vertex x) =
      G.adjustedStrictHalfspacePeak a b ω base x := by
  apply propext
  constructor
  · intro h z hz hzx
    have hh := h (φ.vertex z) ((G.adjustedHalfspaceConn_aut a ha b φ ω base x z).mpr hz)
      (fun he => hzx (φ.vertex.injective he))
    simpa only [G.orbitAdjustedHeight_aut a ha] using hh
  · intro h z hz hzx
    obtain ⟨z,rfl⟩ := φ.vertex.surjective z
    have hh := h z ((G.adjustedHalfspaceConn_aut a ha b φ ω base x z).mp hz)
      (fun he => hzx (congrArg φ.vertex he))
    simpa only [G.orbitAdjustedHeight_aut a ha] using hh

lemma strictPeakBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (r l u : ℝ)
    (φ : G.Aut) (ω : Set E) (y x : V) :
    G.strictPeakBandTransport a r l u (φ.edge '' ω) (φ.vertex y) (φ.vertex x) =
      G.strictPeakBandTransport a r l u ω y x := by
  simp only [strictPeakBandTransport,G.adjustedHalfspaceConn_aut a ha,
    G.adjustedStrictHalfspacePeak_aut a ha,G.orbitAdjustedHeight_aut a ha]

variable [Countable V] [Countable E]

lemma measurable_adjustedHalfspaceConn (a : V → ℝ) (b : ℝ) (base x y : V) :
    Measurable (fun ω => G.adjustedHalfspaceConn a b ω base x y) := by
  have hm : Measurable (fun ω : Set E => ω ∩ Percolation.internalEdges G.ends
      {z | b ≤ G.orbitAdjustedHeight a base z}) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (Percolation.measurableSet_conn G.ends x y).mem.comp hm

lemma measurable_adjustedStrictHalfspacePeak (a : V → ℝ) (b : ℝ) (base x : V) :
    Measurable (fun ω => G.adjustedStrictHalfspacePeak a b ω base x) := by
  exact Measurable.forall fun z => (G.measurable_adjustedHalfspaceConn a b base x z).imp
    (measurable_const.imp measurable_const)

lemma measurable_strictPeakBandTransport (a : V → ℝ) (r l u : ℝ) (y x : V) :
    Measurable (fun ω => G.strictPeakBandTransport a r l u ω y x) := by
  exact Measurable.ite (((G.measurable_adjustedHalfspaceConn a (-r) y y x).and
    ((G.measurable_adjustedStrictHalfspacePeak a (-r) y x).and measurable_const)).setOf)
      measurable_const measurable_const

lemma measurable_strictPeakSlabBandTransport (a : V → ℝ) (r l u : ℝ) (x y : V) :
    Measurable (fun ω => G.strictPeakSlabBandTransport a r l u ω x y) := by
  have hm : Measurable (fun ω : Set E => ω ∩ Percolation.internalEdges G.ends
      {z | u-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ 0}) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.ite (((G.measurable_adjustedStrictHalfspacePeak a (l-r) x x).and
    (((Percolation.measurableSet_conn G.ends x y).mem.comp hm).and measurable_const)).setOf)
      measurable_const measurable_const

lemma measurable_strictPeakSlabBandCount (a : V → ℝ) (r l u : ℝ) (x : V) :
    Measurable (fun ω => G.strictPeakSlabBandCount a r l u ω x) :=
  Measurable.tsum fun y => G.measurable_strictPeakSlabBandTransport a r l u x y

theorem expected_strictPeakSlabBandCount_bound
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval) (r l u : ℝ) :
    ENNReal.ofReal (Real.exp l)*
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, G.strictPeakSlabBandCount a r l u ω x ∂G.law p)) ≤
      ∑ y ∈ O.roots, ENNReal.ofReal (a y)*G.law p
        (restrictedHit G.ends (Percolation.internalEdges G.ends
          {z | -r ≤ G.orbitAdjustedHeight a y z}) y {z | -u ≤ G.orbitAdjustedHeight a y z}) := by
  have hin (ω : Set E) (x : V) :
      ENNReal.ofReal (Real.exp l)*G.strictPeakSlabBandCount a r l u ω x ≤
        ∑' y, G.strictPeakBandTransport a r l u ω y x*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
    rw [strictPeakSlabBandCount,←ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun y =>
      G.strictPeakSlabBandTransport_incoming_lower hc hl a r l u ω x y
  calc
    _ = ∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, ENNReal.ofReal (Real.exp l)*G.strictPeakSlabBandCount a r l u ω x ∂G.law p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [lintegral_const_mul _ (G.measurable_strictPeakSlabBandCount a r l u x)]
      ring
    _ ≤ ∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, ∑' y, G.strictPeakBandTransport a r l u ω y x*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) ∂G.law p) :=
      Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (lintegral_mono fun ω => hin ω x)
    _ = ∑ y ∈ O.roots, ENNReal.ofReal (a y)*
        (∫⁻ ω, ∑' x, G.strictPeakBandTransport a r l u ω y x ∂G.law p) :=
      (OrbitRepresentatives.random_normalized_tilted_transport G O hc hl a hapos ha p
        (G.strictPeakBandTransport a r l u) (G.measurable_strictPeakBandTransport a r l u)
          (G.strictPeakBandTransport_aut a ha r l u)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul' le_rfl
      apply (lintegral_mono fun ω => G.strictPeakBandTransport_outgoing hc hl a r l u ω y).trans_eq
      simpa only [Set.indicator,Pi.one_apply] using lintegral_indicator_one (μ := G.law p)
        (measurableSet_restrictedHit G.ends _ y _)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CriticalPeakBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

lemma critical_normalized_halfspace_exp_bound_at_rate (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t)) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ r, 0 ≤ r → ∀ x t, 0 ≤ t →
      law (pc G) ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤
          ENNReal.ofReal (C*Real.exp (L*r-α*t)) := by
  have hp : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  obtain ⟨A,B,hA,hB,hh⟩ := normalized_halfspace_uniform_of_infimal_bound G hc hl hq hu
    μ hμ hstat (pc G) hp α hcross
  let ell := -Real.log (pc G : ℝ)
  have hell : 0 ≤ ell := neg_nonneg.mpr (Real.log_nonpos hp.le (pc G).2.2)
  let C := Real.exp (ell*B)
  let L := ell*A+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C,L,Real.exp_pos _,hL,fun r hr x t ht => ?_⟩
  have hreal : (law (pc G)).real ((criticalModel G).adjustedHalfspaceHit
      ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤ C*Real.exp (L*r-α*t) := by
    apply (hh r hr x t ht).trans
    rw [Real.rpow_def_of_pos hp,←Real.exp_add]
    change Real.exp _ ≤ Real.exp (ell*B)*Real.exp (L*r-α*t)
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [ell,L]
    nlinarith
  calc
    _ = ENNReal.ofReal ((law (pc G)).real ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

theorem critical_peak_band_bound_at_rate (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t)) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ r, 0 ≤ r → ∀ l u, u ≤ 0 →
      (∑ x ∈ ((criticalModel G).orbitRepresentatives
          (criticalModel_quasiTransitive G hq)).roots,
        ENNReal.ofReal ((criticalModel G).stationaryOrbitWeight μ x)*
          (∫⁻ ω, (criticalModel G).strictPeakSlabBandCount
            ((criticalModel G).stationaryOrbitWeight μ) r l u ω x ∂law (pc G))) ≤
      (∑ x ∈ ((criticalModel G).orbitRepresentatives
          (criticalModel_quasiTransitive G hq)).roots,
        ENNReal.ofReal ((criticalModel G).stationaryOrbitWeight μ x))*
          ENNReal.ofReal (C*Real.exp (L*r+α*u-l)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let O := H.orbitRepresentatives (criticalModel_quasiTransitive G hq)
  have hHc := criticalModel_connected G hc
  obtain ⟨C,L,hC,hL,hup⟩ := critical_normalized_halfspace_exp_bound_at_rate G hc hl hq hu μ hμ hstat α hcross
  refine ⟨C,L,hC,hL,fun r hr l u hu0 => ?_⟩
  have hb := H.expected_strictPeakSlabBandCount_bound O hHc hl a
    (H.stationaryOrbitWeight_pos hHc hl μ hμ) (H.stationaryOrbitWeight_aut μ) (pc G) r l u
  have hs : (∑ y ∈ O.roots, ENNReal.ofReal (a y)*H.law (pc G)
      (restrictedHit G (internalEdges G {z | -r ≤ H.orbitAdjustedHeight a y z}) y
        {z | -u ≤ H.orbitAdjustedHeight a y z})) ≤
      (∑ y ∈ O.roots, ENNReal.ofReal (a y))*ENNReal.ofReal (C*Real.exp (L*r+α*u)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y _
    apply mul_le_mul' le_rfl
    change law (pc G) (H.adjustedHalfspaceHit a y (-r) (-u)) ≤ _
    simpa only [mul_neg,sub_neg_eq_add] using hup r hr y (-u) (neg_nonneg.mpr hu0)
  have he : ENNReal.ofReal (Real.exp (-l))*ENNReal.ofReal (Real.exp l)=1 := by
    rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
    simp only [neg_add_cancel,Real.exp_zero,ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal (Real.exp (-l))*(ENNReal.ofReal (Real.exp l)*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
          (∫⁻ ω, H.strictPeakSlabBandCount a r l u ω x ∂law (pc G)))) := by
      rw [←mul_assoc,he,one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-l))*
        ((∑ y ∈ O.roots, ENNReal.ofReal (a y))*ENNReal.ofReal (C*Real.exp (L*r+α*u))) :=
      mul_le_mul' le_rfl (hb.trans hs)
    _ = _ := by
      rw [mul_left_comm,←ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 2
      rw [mul_left_comm,←Real.exp_add]
      congr 2
      ring

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FiniteEnergyModification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma forceOn_finitePattern_eq (F : Finset E) (σ : Set (F : Set E)) (ω : Set E)
    (hω : ω ∈ finiteBondPattern F (Subtype.val '' σ)) :
    forceOn (F : Set E) (Subtype.val '' σ) ω=ω := by
  ext e
  rw [mem_forceOn]
  by_cases he : e ∈ (F : Set E)
  · simpa only [he,if_true] using (Iff.of_eq (hω e he)).symm
  · simp only [he,if_false]

lemma finiteBondPattern_pairwise (F : Finset E) :
    Pairwise (fun σ τ : Set (F : Set E) => Disjoint
      (finiteBondPattern F (Subtype.val '' σ)) (finiteBondPattern F (Subtype.val '' τ))) := by
  intro σ τ hστ
  apply Set.disjoint_left.mpr
  intro ω hσ hτ
  apply hστ
  ext e
  have hh := (hσ e e.property).symm.trans (hτ e e.property)
  simpa only [Set.mem_image,Subtype.val_injective.eq_iff,exists_eq_right] using Iff.of_eq hh

lemma iUnion_finiteBondPattern (F : Finset E) :
    (⋃ σ : Set (F : Set E), finiteBondPattern F (Subtype.val '' σ))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  refine Set.mem_iUnion.mpr ⟨Subtype.val ⁻¹' ω,?_⟩
  intro e he
  apply propext
  simp only [Set.mem_image,Set.mem_preimage]
  constructor
  · intro heω
    exact ⟨⟨e,he⟩,heω,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact hz

lemma forced_event_dependsOn_compl (F : Finset E) (σ : Set E) (B : Set (Set E)) :
    DependsOn (fun ω => forceOn (F : Set E) σ ω ∈ B) (F : Set E)ᶜ := by
  intro ω η hωη
  let ξ : Set E := {e | ω e}
  let ζ : Set E := {e | η e}
  have hh : forceOn (F : Set E) σ ξ=forceOn (F : Set E) σ ζ := by
    ext e
    rw [mem_forceOn,mem_forceOn]
    by_cases he : e ∈ (F : Set E)
    · simp only [he,if_true]
    · simp only [he,if_false]
      exact Iff.of_eq (hωη e he)
  exact congrArg (fun ξ : Set E => ξ ∈ B) hh

variable [Countable E]

lemma finiteModification_probability (p : unitInterval) (F : Finset E)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*law p (finiteModification F B) ≤ law p B := by
  let A (σ : Set (F : Set E)) := (forceOn (F : Set E) (Subtype.val '' σ)) ⁻¹' B
  let P (σ : Set (F : Set E)) := finiteBondPattern F (Subtype.val '' σ)
  have hmA (σ : Set (F : Set E)) : MeasurableSet (A σ) :=
    hB.preimage (measurable_forceOn _ _)
  have hcell (σ : Set (F : Set E)) :
      law p (A σ)*ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) ≤ law p (B ∩ P σ) := by
    have he : A σ ∩ P σ=B ∩ P σ := by
      ext ω
      constructor
      · rintro ⟨ha,hp⟩
        exact ⟨forceOn_finitePattern_eq F σ ω hp ▸ ha,hp⟩
      · rintro ⟨hb,hp⟩
        refine ⟨?_,hp⟩
        change forceOn (F : Set E) (Subtype.val '' σ) ω ∈ B
        rw [forceOn_finitePattern_eq F σ ω hp]
        exact hb
    have hh := fresh_finiteBondPattern_cell_lower p (F : Set E)ᶜ (A σ) (hmA σ)
      (forced_event_dependsOn_compl F _ B) F (by simp only [compl_compl]; exact Set.Subset.rfl)
        (Subtype.val '' σ)
    rwa [he] at hh
  have hd : Pairwise (fun σ τ : Set (F : Set E) => Disjoint (B ∩ P σ) (B ∩ P τ)) :=
    fun σ τ hστ => (finiteBondPattern_pairwise F hστ).mono Set.inter_subset_right Set.inter_subset_right
  have hp : (⋃ σ : Set (F : Set E), B ∩ P σ)=B := by
    rw [←Set.inter_iUnion,iUnion_finiteBondPattern,Set.inter_univ]
  calc
    _ ≤ ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*∑' σ : Set (F : Set E), law p (A σ) :=
      mul_le_mul' le_rfl (measure_iUnion_le A)
    _ = ∑' σ : Set (F : Set E), law p (A σ)*ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) := by
      rw [ENNReal.tsum_mul_right,mul_comm]
    _ ≤ ∑' σ : Set (F : Set E), law p (B ∩ P σ) := ENNReal.tsum_le_tsum hcell
    _ = _ := by rw [←measure_iUnion hd (fun σ => hB.inter (measurableSet_finiteBondPattern F _)),hp]

theorem finite_energy_modification_bound (p : unitInterval) (F : Finset E)
    (A B : Set (Set E)) (hB : MeasurableSet B)
    (hmod : ∀ ω ∈ A, ∃ η ∈ B, ∀ e ∉ F, (e ∈ ω)=(e ∈ η)) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*law p A ≤ law p B := by
  apply (mul_le_mul' le_rfl (measure_mono ?_)).trans (finiteModification_probability p F B hB)
  intro ω hω
  obtain ⟨η,hη,hagree⟩ := hmod ω hω
  let σ : Set (F : Set E) := Subtype.val ⁻¹' η
  refine Set.mem_iUnion.mpr ⟨σ,?_⟩
  have hh : forceOn (F : Set E) (Subtype.val '' σ) ω=η := by
    ext e
    rw [mem_forceOn]
    by_cases he : e ∈ (F : Set E)
    · simp only [he,if_true,Set.mem_image]
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact hz
      · intro heη
        exact ⟨⟨e,he⟩,heη,rfl⟩
    · simpa only [he,if_false] using Iff.of_eq (hagree e he)
  change forceOn (F : Set E) (Subtype.val '' σ) ω ∈ B
  rw [hh]
  exact hη

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakClusterCorrelation
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

lemma peakConnectionCell_iff (I J : Set E) (hJI : J ⊆ I) (u w : V) (S T : Set V)
    (ω : Set E) :
    ω ∈ peakConnectionCell G I J u w S T ↔
      cluster G (ω ∩ I) u=S ∧ Conn G (ω ∩ J) u w ∧ Disjoint S T := by
  constructor
  · rintro ⟨hc,hw,hd⟩
    exact ⟨hc,conn_mono G Set.inter_subset_left hw,hd⟩
  · rintro ⟨hc,hw,hd⟩
    have hh := conn_restrict_cluster_of_subset G (ω ∩ I) u
      (fun e he => ⟨he.1,hJI he.2⟩) (mem_cluster_self G _ u) hw
    rw [hc] at hh
    exact ⟨hc,hh,hd⟩

lemma masked_internal_configuration_dependsOn (J : Set E) (S : Set V) :
    DependsOn (fun ω : Set E => (ω ∩ J) ∩ internalEdges G S) (ballIncidentEdges G S) := by
  intro ω η hωη
  ext e
  change ((ω e ∧ e ∈ J) ∧ e ∈ internalEdges G S) ↔
    ((η e ∧ e ∈ J) ∧ e ∈ internalEdges G S)
  by_cases he : e ∈ internalEdges G S
  · have hi : e ∈ ballIncidentEdges G S :=
      ⟨(G e).out.1,he _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩
    rw [hωη e hi]
  · simp only [he,and_false]

lemma peakConnectionCell_dependsOn (I J : Set E) (u w : V) (S T : Set V) :
    DependsOn (fun ω => ω ∈ peakConnectionCell G I J u w S T) (ballIncidentEdges G S) := by
  intro ω η hωη
  have hc := restricted_exactCluster_dependsOn G I u S hωη
  have hm := masked_internal_configuration_dependsOn G J S hωη
  change (cluster G (Set.inter ω I) u=S) = (cluster G (Set.inter η I) u=S) at hc
  change (Set.inter (Set.inter ω J) (internalEdges G S)) =
    (Set.inter (Set.inter η J) (internalEdges G S)) at hm
  change (cluster G (Set.inter ω I) u=S ∧
    Conn G (Set.inter (Set.inter ω J) (internalEdges G S)) u w ∧ Disjoint S T) =
      (cluster G (Set.inter η I) u=S ∧
    Conn G (Set.inter (Set.inter η J) (internalEdges G S)) u w ∧ Disjoint S T)
  rw [hc,hm]

lemma masked_exterior_configuration_dependsOn (I : Set E) (S : Set V) :
    DependsOn (fun ω : Set E => (ω ∩ I) ∩ internalEdges G Sᶜ) (ballIncidentEdges G S)ᶜ := by
  intro ω η hωη
  ext e
  change ((ω e ∧ e ∈ I) ∧ e ∈ internalEdges G Sᶜ) ↔
    ((η e ∧ e ∈ I) ∧ e ∈ internalEdges G Sᶜ)
  by_cases he : e ∈ internalEdges G Sᶜ
  · have hi : e ∈ (ballIncidentEdges G S)ᶜ := by
      rintro ⟨v,hv,hve⟩
      exact (he v hve) hv
    rw [hωη e hi]
  · simp only [he,and_false]

lemma peakConnectionCell_inter_hit (I J : Set E) (u w : V) (S A T : Set V) :
    peakConnectionCell G I J u w S T ∩ restrictedSetHit G I A T =
      peakConnectionCell G I J u w S T ∩
        restrictedSetHit G (I ∩ internalEdges G Sᶜ) A T := by
  ext ω
  constructor
  · rintro ⟨hc,v,hv,t,ht,hvt⟩
    have htn : t ∉ cluster G (ω ∩ I) u := by
      rw [hc.1]
      exact fun h => Set.disjoint_left.mp hc.2.2 h ht
    have hh := conn_restrict_away_from_cluster G (ω ∩ I) (ω ∩ I) Set.Subset.rfl
      u t v htn (conn_symm G _ hvt)
    rw [hc.1] at hh
    refine ⟨hc,v,hv,t,ht,?_⟩
    simpa only [Set.inter_assoc] using conn_symm G _ hh
  · rintro ⟨hc,v,hv,t,ht,hvt⟩
    exact ⟨hc,v,hv,t,ht,conn_mono G
      (Set.inter_subset_inter_right _ Set.inter_subset_left) hvt⟩

variable [Countable V] [Countable E]

lemma measurableSet_restrictedSetHit (I : Set E) (A T : Set V) :
    MeasurableSet (restrictedSetHit G I A T) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (Measurable.exists fun v => measurable_const.and
    (Measurable.exists fun t => measurable_const.and
      ((measurableSet_conn G v t).mem.comp hm))).setOf

lemma measurableSet_peakConnectionCell (I J : Set E) (u w : V) (S T : Set V) :
    MeasurableSet (peakConnectionCell G I J u w S T) := by
  have hm : Measurable (fun ω : Set E => (ω ∩ J) ∩ internalEdges G S) :=
    measurable_set_iff.mpr fun e => ((measurable_set_mem e).and measurable_const).and measurable_const
  exact (measurableSet_restricted_exactCluster G I u S).inter
    ((((measurableSet_conn G u w).mem.comp hm).and measurable_const).setOf)

omit [Countable V] [Countable E] in
lemma restrictedSetHit_exterior_dependsOn (I : Set E) (A T S : Set V) :
    DependsOn (fun ω => ω ∈ restrictedSetHit G (I ∩ internalEdges G Sᶜ) A T)
      (ballIncidentEdges G S)ᶜ := by
  intro ω η hωη
  have hh := masked_exterior_configuration_dependsOn G I S hωη
  change Set.inter (Set.inter ω I) (internalEdges G Sᶜ) =
    Set.inter (Set.inter η I) (internalEdges G Sᶜ) at hh
  have hh' : Set.inter ω (Set.inter I (internalEdges G Sᶜ)) =
      Set.inter η (Set.inter I (internalEdges G Sᶜ)) :=
    (Set.inter_assoc ω I (internalEdges G Sᶜ)).symm.trans
      (hh.trans (Set.inter_assoc η I (internalEdges G Sᶜ)))
  exact congrArg (fun ξ : Set E => ∃ v ∈ A, ∃ t ∈ T, Conn G ξ v t) hh'

lemma peakConnectionCell_hit_probability (p : unitInterval)
    (I J : Set E) (u w : V) (S A T : Set V) :
    law p (peakConnectionCell G I J u w S T ∩ restrictedSetHit G I A T) ≤
      law p (peakConnectionCell G I J u w S T)*law p (restrictedSetHit G I A T) := by
  rw [peakConnectionCell_inter_hit]
  have hlaw : CriticalPercolation.BernoulliProduct.law (fun _ : E => p) = law p :=
    CriticalPercolation.BernoulliProduct.law_const p
  rw [←hlaw]
  rw [CriticalPercolation.BernoulliProduct.measure_inter_of_separate_blocks (fun _ : E => p)
    (ballIncidentEdges G S) _ _ (measurableSet_peakConnectionCell G I J u w S T)
      (measurableSet_restrictedSetHit G _ A T) (peakConnectionCell_dependsOn G I J u w S T)
        (restrictedSetHit_exterior_dependsOn G I A T S)]
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro ω ⟨v,hv,t,ht,hvt⟩
  exact ⟨v,hv,t,ht,conn_mono G (Set.inter_subset_inter_right _ Set.inter_subset_left) hvt⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakCorrelationAveraging
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

omit [Countable V] [Countable E] in
lemma connectionAvoidingHit_finite_cells (I J : Set E) (hJI : J ⊆ I)
    (u w : V) (T : Set V) (ω : Set E) (hf : (cluster G (ω ∩ I) u).Finite) :
    ω ∈ connectionAvoidingHit G I J u w T ↔
      ∃ S : Finset V, ω ∈ peakConnectionCell G I J u w (S : Set V) T := by
  constructor
  · rintro ⟨hw,havoid⟩
    let S := hf.toFinset
    have hs : cluster G (ω ∩ I) u=(S : Set V) := hf.coe_toFinset.symm
    apply Exists.intro S
    apply (peakConnectionCell_iff G I J hJI u w _ T ω).mpr
    refine ⟨hs,hw,Set.disjoint_left.mpr ?_⟩
    intro v hv hvT
    apply havoid
    refine ⟨v,hvT,?_⟩
    change v ∈ cluster G (ω ∩ I) u
    rwa [hs]
  · rintro ⟨S,hS⟩
    obtain ⟨hs,hw,hdis⟩ := (peakConnectionCell_iff G I J hJI u w _ T ω).mp hS
    refine ⟨hw,?_⟩
    rintro ⟨v,hvT,huv⟩
    apply Set.disjoint_left.mp hdis _ hvT
    rw [←hs]
    exact huv

lemma measure_peakConnectionCell_partition (p : unitInterval)
    (I J : Set E) (hJI : J ⊆ I) (u w : V) (T : Set V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) u).Finite)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    law p (connectionAvoidingHit G I J u w T ∩ B) =
      ∑' S : Finset V, law p (peakConnectionCell G I J u w (S : Set V) T ∩ B) := by
  have hdis : Pairwise (fun S U : Finset V => Disjoint
      (peakConnectionCell G I J u w (S : Set V) T ∩ B)
      (peakConnectionCell G I J u w (U : Set V) T ∩ B)) := by
    intro S U hne
    apply Set.disjoint_left.mpr
    rintro ω ⟨hS,_⟩ ⟨hU,_⟩
    exact hne (Finset.coe_injective (hS.1.symm.trans hU.1))
  calc
    _ = law p (⋃ S : Finset V, peakConnectionCell G I J u w (S : Set V) T ∩ B) := by
      apply measure_congr
      filter_upwards [hfin] with ω hω
      show (ω ∈ connectionAvoidingHit G I J u w T ∩ B) =
        (ω ∈ ⋃ S : Finset V, peakConnectionCell G I J u w (S : Set V) T ∩ B)
      simp only [Set.mem_inter_iff,Set.mem_iUnion]
      rw [connectionAvoidingHit_finite_cells G I J hJI u w T ω hω]
      exact propext exists_and_right.symm
    _ = _ := measure_iUnion hdis fun S =>
      (measurableSet_peakConnectionCell G I J u w (S : Set V) T).inter hB

theorem connection_avoiding_hit_negative_correlation (p : unitInterval)
    (I J : Set E) (hJI : J ⊆ I) (u w : V) (A T : Set V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) u).Finite) :
    law p (connectionAvoidingHit G I J u w T ∩ restrictedSetHit G I A T) ≤
      law p (connectionAvoidingHit G I J u w T)*law p (restrictedSetHit G I A T) := by
  have hpart : law p (connectionAvoidingHit G I J u w T) =
      ∑' S : Finset V, law p (peakConnectionCell G I J u w (S : Set V) T) := by
    simpa only [Set.inter_univ] using measure_peakConnectionCell_partition G p I J hJI u w T hfin
      Set.univ MeasurableSet.univ
  rw [measure_peakConnectionCell_partition G p I J hJI u w T hfin
    (restrictedSetHit G I A T) (measurableSet_restrictedSetHit G I A T),hpart,
      ←ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum fun S => peakConnectionCell_hit_probability G p I J u w _ A T

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakComplementCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma probability_complement_correlation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C B : Set Ω)
    (hB : MeasurableSet B) (hneg : μ (C ∩ B) ≤ μ C * μ B) :
    μ C * μ Bᶜ ≤ μ (C ∩ Bᶜ) := by
  apply ENNReal.le_of_add_le_add_left (measure_ne_top μ (C ∩ B))
  calc
    μ (C ∩ B) + μ C * μ Bᶜ ≤ μ C * μ B + μ C * μ Bᶜ :=
      add_le_add hneg le_rfl
    _ = μ C := by rw [←mul_add,prob_add_prob_compl hB,mul_one]
    _ = μ (C ∩ B) + μ (C ∩ Bᶜ) := by
      simpa only [Set.sdiff_eq] using (measure_inter_add_sdiff (μ := μ) C hB).symm

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem connection_avoiding_hit_complement_correlation (p : unitInterval)
    (I J : Set E) (hJI : J ⊆ I) (u w : V) (A T : Set V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) u).Finite) :
    law p (connectionAvoidingHit G I J u w T) * law p (restrictedSetHit G I A T)ᶜ ≤
      law p (connectionAvoidingHit G I J u w T ∩ (restrictedSetHit G I A T)ᶜ) :=
  probability_complement_correlation (law p) _ _
    (measurableSet_restrictedSetHit G I A T)
    (connection_avoiding_hit_negative_correlation G p I J hJI u w A T hfin)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakUpperExposure
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

lemma restricted_exactCluster_dependsOn_inter (K : Set E) (x : V) (A : Set V) :
    DependsOn (fun ω => cluster G (ω ∩ K) x=A) (K ∩ ballIncidentEdges G A) := by
  intro ω η hωη
  have hh : ∀ e ∈ ballIncidentEdges G A,
      (e ∈ Set.inter ω K)=(e ∈ Set.inter η K) := by
    intro e he
    change (ω e ∧ e ∈ K)=(η e ∧ e ∈ K)
    by_cases hk : e ∈ K
    · exact congrArg (fun P : Prop => P ∧ e ∈ K) (hωη e ⟨hk,he⟩)
    · simp only [hk,and_false]
  have h := (criticalModel G).exactCluster_dependsOn x A hh
  change ((criticalModel G).cluster (Set.inter ω K) x=A) =
    ((criticalModel G).cluster (Set.inter η K) x=A) at h
  rw [criticalModel_cluster,criticalModel_cluster] at h
  exact h

lemma restrictedSetHit_dependsOn (I : Set E) (A T : Set V) :
    DependsOn (fun ω => ω ∈ restrictedSetHit G I A T) I := by
  intro ω η hωη
  have he : Set.inter ω I=Set.inter η I := by
    ext e
    change (ω e ∧ e ∈ I) ↔ (η e ∧ e ∈ I)
    by_cases hi : e ∈ I
    · exact and_congr (Iff.of_eq (hωη e hi)) Iff.rfl
    · simp only [hi,and_false]
  exact congrArg (fun ξ : Set E => ∃ v ∈ A, ∃ t ∈ T, Conn G ξ v t) he

theorem upper_cluster_forbidden_hit_iff (ω : Set E) (D K : Set E) (hKD : K ⊆ D)
    (x : V) (A T : Set V) (hA : cluster G (ω ∩ K) x=A) (hAT : Disjoint A T) :
    ω ∈ restrictedHit G D x T ↔
      ω ∈ restrictedSetHit G (D \ (K ∩ ballIncidentEdges G A)) A T := by
  constructor
  · rintro ⟨t,ht,hxt⟩
    have hxA : x ∈ A := hA ▸ mem_cluster_self G _ x
    have htA : t ∉ A := fun h => Set.disjoint_left.mp hAT h ht
    obtain ⟨z,hz,hzt⟩ := conn_last_exit_frontier G (ω ∩ D) A hxA htA hxt
    obtain ⟨hzA,u,hu,e,he,heq⟩ := hz
    have hek : e ∉ K := by
      intro hk
      apply hzA
      rw [←hA]
      have hxu : Conn G (ω ∩ K) x u := by
        change u ∈ cluster G (ω ∩ K) x
        rwa [hA]
      exact hxu.tail ⟨e,⟨he.1,hk⟩,heq⟩
    have huz : Conn G (ω ∩ (D \ (K ∩ ballIncidentEdges G A))) u z :=
      (conn_refl G _ u).tail ⟨e,⟨he.1,he.2,fun h => hek h.1⟩,heq⟩
    refine ⟨u,hu,t,ht,huz.trans (conn_mono G ?_ hzt)⟩
    rintro e ⟨⟨he,heD⟩,heA⟩
    exact ⟨he,heD,fun h => heA h.2⟩
  · rintro ⟨u,hu,t,ht,hut⟩
    have hxu : Conn G (ω ∩ K) x u := by
      change u ∈ cluster G (ω ∩ K) x
      rwa [hA]
    refine ⟨t,ht,(conn_mono G (Set.inter_subset_inter_right _ hKD) hxu).trans ?_⟩
    exact conn_mono G (Set.inter_subset_inter_right _ Set.sdiff_subset) hut

variable [Countable V] [Countable E]

lemma upper_cluster_fresh_factor (p : unitInterval) (K I : Set E) (x : V) (A : Set V)
    (hfresh : I ⊆ (K ∩ ballIncidentEdges G A)ᶜ)
    (B : Set (Set E)) (hB : MeasurableSet B)
    (hdB : DependsOn (fun ω => ω ∈ B) I) :
    law p ({ω | cluster G (ω ∩ K) x=A} ∩ B) =
      law p {ω | cluster G (ω ∩ K) x=A} * law p B := by
  have hlaw : CriticalPercolation.BernoulliProduct.law (fun _ : E => p)=law p :=
    CriticalPercolation.BernoulliProduct.law_const p
  rw [←hlaw]
  exact CriticalPercolation.BernoulliProduct.measure_inter_of_separate_blocks
    (fun _ : E => p) (K ∩ ballIncidentEdges G A) _ B
    (measurableSet_restricted_exactCluster G K x A) hB
    (restricted_exactCluster_dependsOn_inter G K x A) (DependsOn.mono hfresh hdB)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakExposureComparison
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

lemma connectionAvoidingHit_dependsOn (I J : Set E) (hJI : J ⊆ I)
    (u w : V) (T : Set V) :
    DependsOn (fun ω => ω ∈ connectionAvoidingHit G I J u w T) I := by
  intro ω η hωη
  have hJ : Set.inter ω J=Set.inter η J := by
    ext e
    change (ω e ∧ e ∈ J) ↔ (η e ∧ e ∈ J)
    by_cases hj : e ∈ J
    · exact and_congr (Iff.of_eq (hωη e (hJI hj))) Iff.rfl
    · simp only [hj,and_false]
  have hT := restrictedHit_dependsOn G I u T hωη
  exact congrArg₂ And (congrArg (fun ξ : Set E => Conn G ξ u w) hJ)
    (congrArg Not hT)

variable [Countable V] [Countable E]

lemma measurableSet_connectionAvoidingHit (I J : Set E) (u w : V) (T : Set V) :
    MeasurableSet (connectionAvoidingHit G I J u w T) := by
  have hm : Measurable (fun ω : Set E => ω ∩ J) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (((measurableSet_conn G u w).mem.comp hm).setOf).inter
    (measurableSet_restrictedHit G I u T).compl

theorem upper_cluster_peak_connection_comparison_in_domain (p : unitInterval)
    (D D' K J : Set E) (hKD : K ⊆ D) (hKD' : K ⊆ D') (hJD' : J ⊆ D') (x u w : V) (A T : Set V)
    (hu : u ∈ A) (hAT : Disjoint A T)
    (hJI : J ⊆ D \ (K ∩ ballIncidentEdges G A))
    (hfin : ∀ᵐ ω ∂law p,
      (cluster G (ω ∩ (D \ (K ∩ ballIncidentEdges G A))) u).Finite) :
    law p ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) *
      law p (connectionAvoidingHit G D J u w T) ≤
    law p (({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) ∩
      {ω | Conn G (ω ∩ D') x w}) := by
  let C : Set (Set E) := {ω | cluster G (ω ∩ K) x=A}
  let I := D \ (K ∩ ballIncidentEdges G A)
  let B := restrictedSetHit G I A T
  let F := connectionAvoidingHit G I J u w T
  have hfresh : I ⊆ (K ∩ ballIncidentEdges G A)ᶜ := fun _ h => h.2
  have hCB : C ∩ (restrictedHit G D x T)ᶜ=C ∩ Bᶜ := by
    ext ω
    constructor
    · rintro ⟨hc,havoid⟩
      exact ⟨hc,fun hh => havoid ((upper_cluster_forbidden_hit_iff G ω D K hKD x A T hc hAT).mpr hh)⟩
    · rintro ⟨hc,havoid⟩
      exact ⟨hc,fun hh => havoid ((upper_cluster_forbidden_hit_iff G ω D K hKD x A T hc hAT).mp hh)⟩
  have hBc : MeasurableSet Bᶜ := (measurableSet_restrictedSetHit G I A T).compl
  have hdBc : DependsOn (fun ω => ω ∈ Bᶜ) I := by
    intro ω η hωη
    exact congrArg Not (restrictedSetHit_dependsOn G I A T hωη)
  have hFB : MeasurableSet (F ∩ Bᶜ) :=
    (measurableSet_connectionAvoidingHit G I J u w T).inter hBc
  have hdFB : DependsOn (fun ω => ω ∈ F ∩ Bᶜ) I := by
    intro ω η hωη
    exact congrArg₂ And (connectionAvoidingHit_dependsOn G I J hJI u w T hωη)
      (hdBc hωη)
  have hmon : law p (connectionAvoidingHit G D J u w T) ≤ law p F := by
    apply measure_mono
    rintro ω ⟨hc,havoid⟩
    refine ⟨hc,?_⟩
    rintro ⟨t,ht,hut⟩
    exact havoid ⟨t,ht,conn_mono G (Set.inter_subset_inter_right _ Set.sdiff_subset) hut⟩
  have hinc : C ∩ (F ∩ Bᶜ) ⊆
      (C ∩ (restrictedHit G D x T)ᶜ) ∩ {ω | Conn G (ω ∩ D') x w} := by
    rintro ω ⟨hc,hF,hB⟩
    have hp : ω ∈ C ∩ (restrictedHit G D x T)ᶜ := by
      rw [hCB]
      exact ⟨hc,hB⟩
    have hxu : Conn G (ω ∩ K) x u := by
      change u ∈ cluster G (ω ∩ K) x
      rwa [hc]
    exact ⟨hp,(conn_mono G (Set.inter_subset_inter_right _ hKD') hxu).trans
      (conn_mono G (Set.inter_subset_inter_right _ hJD') hF.1)⟩
  change law p (C ∩ (restrictedHit G D x T)ᶜ)*_ ≤ _
  conv_lhs => rw [hCB,upper_cluster_fresh_factor G p K I x A hfresh Bᶜ hBc hdBc]
  calc
    (law p C*law p Bᶜ)*law p (connectionAvoidingHit G D J u w T) ≤
        (law p C*law p Bᶜ)*law p F := mul_le_mul' le_rfl hmon
    _ = law p C*(law p F*law p Bᶜ) := by ring
    _ ≤ law p C*law p (F ∩ Bᶜ) := mul_le_mul' le_rfl
      (connection_avoiding_hit_complement_correlation G p I J hJI u w A T hfin)
    _ = law p (C ∩ (F ∩ Bᶜ)) :=
      (upper_cluster_fresh_factor G p K I x A hfresh (F ∩ Bᶜ) hFB hdFB).symm
    _ ≤ _ := measure_mono hinc

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_MixedRootSurgery
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

lemma mixed_root_surgery (D J γ : Set E) (P T : Set V)
    (hJD : J ⊆ D) (hγJ : γ ⊆ J) (hγP : γ ⊆ internalEdges G P)
    (hPT : Disjoint P T) (u v w : V) (huP : u ∈ P) (hγuv : Conn G γ u v)
    (ω : Set E) (hvw : Conn G (ω ∩ J) v w)
    (havoid : ω ∉ restrictedHit G D v T) :
    ∃ η : Set E, η ∈ connectionAvoidingHit G D J u w T ∧
      ∀ e ∉ ballIncidentEdges G P, (e ∈ ω)=(e ∈ η) := by
  let S := cluster G (ω ∩ D) v
  let Q := ballIncidentEdges G (P \ S)
  let η := (ω \ Q) ∪ γ
  have hvS : v ∈ S := mem_cluster_self G _ v
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro z hz hzT
    exact havoid ⟨z,hzT,hz⟩
  have hkeep : (ω ∩ J) ∩ internalEdges G S ⊆ η ∩ J := by
    rintro e ⟨⟨he,heJ⟩,heS⟩
    refine ⟨Or.inl ⟨he,?_⟩,heJ⟩
    rintro ⟨z,⟨_,hzS⟩,hze⟩
    exact hzS (heS z hze)
  have hvw' : Conn G (η ∩ J) v w := by
    have hh := conn_restrict_cluster_of_subset G (ω ∩ D) v
      (Set.inter_subset_inter_right _ hJD) (mem_cluster_self G _ v) hvw
    exact conn_mono G hkeep hh
  have hγsub : γ ⊆ η ∩ J := fun e he => ⟨Or.inr he,hγJ he⟩
  have huv : Conn G (η ∩ J) u v := conn_mono G hγsub hγuv
  have hclosed : ∀ e ∈ η ∩ D, ∀ z ∈ G e, z ∈ S ∪ P → ∀ z' ∈ G e, z' ∈ S ∪ P := by
    intro e he z hze hz z' hz'e
    rcases he.1 with heω | heγ
    · rcases hz with hzS | hzP
      · by_cases hzz' : z=z'
        · exact Or.inl (hzz' ▸ hzS)
        · have heq : G e=s(z,z') := (Sym2.mem_and_mem_iff hzz').mp ⟨hze,hz'e⟩
          exact Or.inl ((edge_cluster_sides G (ω ∩ D) v ⟨heω.1,he.2⟩ heq).mp hzS)
      · by_cases hzS : z ∈ S
        · by_cases hzz' : z=z'
          · exact Or.inl (hzz' ▸ hzS)
          · have heq : G e=s(z,z') := (Sym2.mem_and_mem_iff hzz').mp ⟨hze,hz'e⟩
            exact Or.inl ((edge_cluster_sides G (ω ∩ D) v ⟨heω.1,he.2⟩ heq).mp hzS)
        · exact (heω.2 ⟨z,⟨hzP,hzS⟩,hze⟩).elim
    · exact Or.inr (hγP heγ z' hz'e)
  have hηavoid : η ∉ restrictedHit G D u T := by
    rintro ⟨z,hzT,huz⟩
    have hz := conn_mem_of_open_closed G (η ∩ D) (S ∪ P) u (Or.inr huP) hclosed z huz
    rcases hz with hzS | hzP
    · exact Set.disjoint_left.mp hST hzS hzT
    · exact Set.disjoint_left.mp hPT hzP hzT
  refine ⟨η,⟨huv.trans hvw',hηavoid⟩,?_⟩
  intro e heP
  have heQ : e ∉ Q := fun ⟨z,hz,hze⟩ => heP ⟨z,hz.1,hze⟩
  have heγ : e ∉ γ := by
    intro he
    exact heP ⟨(G e).out.1,hγP he _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩
  apply propext
  change e ∈ ω ↔ (e ∈ ω ∧ e ∉ Q) ∨ e ∈ γ
  constructor
  · intro he
    exact Or.inl ⟨he,heQ⟩
  · rintro (⟨he,_⟩ | he)
    · exact he
    · exact (heγ he).elim

theorem mixed_root_connection_probability [Countable V] [Countable E]
    (hl : LocallyFinite G) (p : unitInterval) (D J γ : Set E) (P : Finset V) (T : Set V)
    (hJD : J ⊆ D) (hγJ : γ ⊆ J) (hγP : γ ⊆ internalEdges G (P : Set V))
    (hPT : Disjoint (P : Set V) T) (u v w : V) (huP : u ∈ P) (hγuv : Conn G γ u v) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^(incidentSupport G hl P).card)*
      law p (connectionAvoidingHit G D J v w T) ≤ law p (connectionAvoidingHit G D J u w T) := by
  apply finite_energy_modification_bound p (incidentSupport G hl P) _ _
    (measurableSet_connectionAvoidingHit G D J u w T)
  rintro ω ⟨hvw,havoid⟩
  obtain ⟨η,hη,hagree⟩ := mixed_root_surgery G D J γ (P : Set V) T hJD hγJ hγP hPT
    u v w huP hγuv ω hvw havoid
  refine ⟨η,hη,fun e he => hagree e ?_⟩
  exact fun hh => he ((mem_incidentSupport G hl P e).mpr hh)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_MixedRootPathComparison
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

omit [Countable V] [Countable E] in
lemma walk_internal_restriction {x y : V} (q : (openSimpleGraph G Set.univ).Walk x y)
    (P : Set V) (hP : ∀ v ∈ q.support, v ∈ P) :
    ∃ q' : (openSimpleGraph G (internalEdges G P)).Walk x y,
      q'.length=q.length ∧ q'.support=q.support := by
  induction q with
  | nil => exact ⟨.nil,rfl,rfl⟩
  | @cons x z y hxy q ih =>
    have htail : ∀ v ∈ q.support, v ∈ P :=
      fun v hv => hP v (List.mem_cons_of_mem x hv)
    obtain ⟨q',hlen,hsupp⟩ := ih htail
    obtain ⟨e,he,heq⟩ := hxy.2
    have heP : e ∈ internalEdges G P := by
      intro v hv
      rw [heq] at hv
      rcases Sym2.mem_iff.mp hv with hv | hv
      · subst v
        exact hP x (SimpleGraph.Walk.start_mem_support (.cons hxy q))
      · subst v
        exact hP z (List.mem_cons_of_mem x q.start_mem_support)
    refine ⟨.cons ⟨hxy.1,e,heP,heq⟩ q',?_,?_⟩
    · change q'.length+1=q.length+1
      rw [hlen]
    · change x::q'.support=x::q.support
      rw [hsupp]

theorem mixed_root_walk_probability (hl : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, degree G z ≤ d) (p : unitInterval) (D J : Set E) (hJD : J ⊆ D)
    (T : Set V) (u v w : V) (q : (openSimpleGraph G J).Walk u v)
    (hT : ∀ z ∈ q.support, z ∉ T) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(q.length+1)))*
      law p (connectionAvoidingHit G D J v w T) ≤ law p (connectionAvoidingHit G D J u w T) := by
  let P := q.support.toFinset
  obtain ⟨l,hlift,hends,hopen⟩ := walk_lift_bonds G J q
  let γ : Set E := (l.toFinset : Set E)
  have hγJ : γ ⊆ J := fun e he => hopen e (List.mem_toFinset.mp he)
  have hγP : γ ⊆ internalEdges G (P : Set V) := by
    intro e he z hze
    exact List.mem_toFinset.mpr (SimpleGraph.Walk.mem_support_of_mem_edges
      (hends ▸ List.mem_map_of_mem (List.mem_toFinset.mp he)) hze)
  have hPT : Disjoint (P : Set V) T := Set.disjoint_left.mpr
    fun z hz hzT => hT z (List.mem_toFinset.mp hz) hzT
  have hcard : (incidentSupport G hl P).card ≤ d*(q.length+1) := by
    calc
      _ ≤ P.card*d := incidentSupport_card_le G hl d hd P
      _ ≤ (q.length+1)*d := Nat.mul_le_mul_right d
        ((List.toFinset_card_le q.support).trans_eq q.length_support)
      _ = _ := by ring
  have hδ : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hδ1 : min (p : ℝ) (1-p) ≤ 1 := (min_le_left _ _).trans p.2.2
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (pow_le_pow_of_le_one hδ hδ1 hcard)) le_rfl).trans
      (mixed_root_connection_probability G hl p D J γ P T hJD hγJ hγP hPT u v w
        (List.mem_toFinset.mpr q.start_mem_support) (hlift.conn (fun e he => List.mem_toFinset.mpr he)))

theorem mixed_root_walk_layer_moment (hl : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, degree G z ≤ d) (p : unitInterval) (D J : Set E) (hJD : J ⊆ D)
    (T W : Set V) (u v : V) (q : (openSimpleGraph G J).Walk u v)
    (hT : ∀ z ∈ q.support, z ∉ T) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(q.length+1)))*
      (∑' w, if w ∈ W then law p (connectionAvoidingHit G D J v w T) else 0) ≤
      ∑' w, if w ∈ W then law p (connectionAvoidingHit G D J u w T) else 0 := by
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : w ∈ W
  · simp only [hw,if_true]
    exact mixed_root_walk_probability G hl d hd p D J hJD T u v w q hT
  · simp only [hw,if_false,mul_zero]
    exact le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_MixedHeightMoment
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

omit [Countable V] [Countable E] in
lemma connectionAvoidingHit_mono (D D' J J' : Set E) (T T' : Set V)
    (hD : D' ⊆ D) (hJ : J ⊆ J') (hT : T' ⊆ T) (x y : V) :
    connectionAvoidingHit G D J x y T ⊆ connectionAvoidingHit G D' J' x y T' := by
  rintro ω ⟨hxy,havoid⟩
  refine ⟨conn_mono G (Set.inter_subset_inter_right _ hJ) hxy,?_⟩
  rintro ⟨z,hz,hxz⟩
  exact havoid ⟨z,hT hz,conn_mono G (Set.inter_subset_inter_right _ hD) hxz⟩

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma mixedHeight_connection_event_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (d c ad t : ℝ) (φ : G.Aut) (ω : Set E) (x y : V) :
    φ.edge '' ω ∈ connectionAvoidingHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a (φ.vertex x) z})
      (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧
        G.orbitAdjustedHeight a (φ.vertex x) z ≤ c})
      (φ.vertex x) (φ.vertex y) {z | t ≤ G.orbitAdjustedHeight a (φ.vertex x) z} ↔
    ω ∈ connectionAvoidingHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a x z})
      (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
      x y {z | t ≤ G.orbitAdjustedHeight a x z} := by
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧ G.orbitAdjustedHeight a (φ.vertex x) z ≤ c}) =
      ω ∩ Percolation.internalEdges G.ends
        {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c} := by
    have hD : φ.vertex ⁻¹' {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧
        G.orbitAdjustedHeight a (φ.vertex x) z ≤ c} =
        {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c} := by
      ext z
      simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ←Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  have hconn : Percolation.Conn G.ends (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧ G.orbitAdjustedHeight a (φ.vertex x) z ≤ c})
      (φ.vertex x) (φ.vertex y) ↔
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) x y := by
    rw [←Percolation.conn_aut_iff G.ends φ.preserves,hmask]
  have hhit : φ.edge '' ω ∈ restrictedHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a (φ.vertex x) z})
      (φ.vertex x) {z | t ≤ G.orbitAdjustedHeight a (φ.vertex x) z} ↔
    ω ∈ restrictedHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a x z})
      x {z | t ≤ G.orbitAdjustedHeight a x z} := by
    constructor
    · rintro ⟨z,hz,hxz⟩
      obtain ⟨w,rfl⟩ := φ.vertex.surjective z
      refine ⟨w,?_,(G.adjustedHalfspaceConn_aut a ha ad φ ω x x w).mp hxz⟩
      simpa only [Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha] using hz
    · rintro ⟨z,hz,hxz⟩
      refine ⟨φ.vertex z,?_,(G.adjustedHalfspaceConn_aut a ha ad φ ω x x z).mpr hxz⟩
      simpa only [Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha] using hz
  exact and_congr hconn (not_congr hhit)

lemma mixedHeightLayerMoment_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (p : unitInterval) (d c l u ad t : ℝ) (φ : G.Aut) (x : V) :
    G.mixedHeightLayerMoment a p d c l u ad t (φ.vertex x) =
      G.mixedHeightLayerMoment a p d c l u ad t x := by
  unfold mixedHeightLayerMoment
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro y
  simp only [G.orbitAdjustedHeight_aut a ha]
  split_ifs
  · conv_lhs => rw [←G.law_map_aut p φ]
    rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
      (measurableSet_connectionAvoidingHit G.ends _ _ _ _ _)]
    congr 1
    ext ω
    exact G.mixedHeight_connection_event_aut a ha d c ad t φ ω x y
  · rfl

omit [Countable V] [Countable E] in
lemma mixedHeightLayerMoment_le_continuation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (R M k r ell : ℝ) (hR : 0 ≤ R) (_hM : 0 ≤ M)
    (x v : V)
    (hlo : -ell-R-M ≤ G.orbitAdjustedHeight a x v)
    (hhi : G.orbitAdjustedHeight a x v ≤ -ell-R) :
    G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v ≤
      ∑' w, if -ell-k-M-2*R ≤ G.orbitAdjustedHeight a x w ∧
          G.orbitAdjustedHeight a x w ≤ -ell-k then
        G.law p (connectionAvoidingHit G.ends
          (Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z})
          (Percolation.internalEdges G.ends {z | -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧
            G.orbitAdjustedHeight a x z ≤ -ell})
          v w {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z}) else 0 := by
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : -k-R ≤ G.orbitAdjustedHeight a v w ∧ G.orbitAdjustedHeight a v w ≤ -k+R
  · have hw' : -ell-k-M-2*R ≤ G.orbitAdjustedHeight a x w ∧
        G.orbitAdjustedHeight a x w ≤ -ell-k := by
      rw [G.orbitAdjustedHeight_change_base hc hl a x v w]
      constructor <;> linarith [hw.1,hw.2]
    simp only [hw,hw']
    apply measure_mono
    apply connectionAvoidingHit_mono G.ends
    · apply Percolation.internalEdges_mono G.ends
      intro z hz
      change -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z at hz
      change -k-r-2*M-2*R ≤ G.orbitAdjustedHeight a v z
      rw [G.orbitAdjustedHeight_change_base hc hl a x v z] at hz
      linarith
    · apply Percolation.internalEdges_mono G.ends
      intro z hz
      change -k-r ≤ G.orbitAdjustedHeight a v z ∧ G.orbitAdjustedHeight a v z ≤ 0 at hz
      change -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -ell
      rw [G.orbitAdjustedHeight_change_base hc hl a x v z]
      constructor <;> linarith [hz.1,hz.2]
    · intro z hz
      change z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z at hz
      change ell ≤ G.orbitAdjustedHeight a v z
      rw [G.orbitAdjustedHeight_change_base hc hl a x v z] at hz
      linarith [hz.2]
  · simp only [hw,if_false]
    exact bot_le

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakCountComparison
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

lemma lintegral_indicator_restrictedLayerCount (p : unitInterval)
    (P : Set (Set E)) (hP : MeasurableSet P) (I : Set E) (W : Set V) (x : V) :
    (∫⁻ ω, P.indicator (fun ω => restrictedLayerCount G I W ω x) ω ∂law p) =
      ∑' w, if w ∈ W then law p (P ∩ {ω | Conn G (ω ∩ I) x w}) else 0 := by
  have hm (w : V) : MeasurableSet (P ∩ {ω | Conn G (ω ∩ I) x w}) := by
    have hi : Measurable (fun ω : Set E => ω ∩ I) :=
      measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
    exact hP.inter ((measurableSet_conn G x w).preimage hi)
  have he (ω : Set E) : P.indicator (fun ω => restrictedLayerCount G I W ω x) ω =
      ∑' w, if w ∈ W then (P ∩ {ω | Conn G (ω ∩ I) x w}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω else 0 := by
    by_cases hp : ω ∈ P
    · rw [Set.indicator_of_mem hp]
      unfold restrictedLayerCount
      apply tsum_congr
      intro w
      by_cases hw : w ∈ W <;> by_cases hc : Conn G (ω ∩ I) x w <;>
        simp only [hw,hc,hp,Set.indicator,Set.mem_inter_iff,Set.mem_ofPred_eq,
          and_true,and_false,if_true,if_false]
    · rw [Set.indicator_of_notMem hp]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro w
      by_cases hw : w ∈ W <;>
        simp only [hw,hp,Set.indicator,Set.mem_inter_iff,false_and,if_true,if_false]
  simp_rw [he]
  rw [lintegral_tsum (fun w => (by
    by_cases hw : w ∈ W
    · simpa only [hw,if_true] using ((measurable_const.indicator (hm w)).aemeasurable)
    · simp only [hw,if_false]
      exact aemeasurable_const))]
  apply tsum_congr
  intro w
  by_cases hw : w ∈ W
  · simp only [hw,if_true]
    exact lintegral_indicator_one (hm w)
  · simp only [hw,if_false,lintegral_zero]

theorem upper_cluster_peak_layer_comparison_in_domain (p : unitInterval)
    (D D' K J : Set E) (hKD : K ⊆ D) (hKD' : K ⊆ D') (hJD' : J ⊆ D') (x u : V) (A T W : Set V)
    (hu : u ∈ A) (hAT : Disjoint A T)
    (hJI : J ⊆ D \ (K ∩ ballIncidentEdges G A))
    (hfin : ∀ᵐ ω ∂law p,
      (cluster G (ω ∩ (D \ (K ∩ ballIncidentEdges G A))) u).Finite) :
    law p ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) *
      (∑' w, if w ∈ W then law p (connectionAvoidingHit G D J u w T) else 0) ≤
    ∫⁻ ω, ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ).indicator
      (fun ω => restrictedLayerCount G D' W ω x) ω ∂law p := by
  rw [lintegral_indicator_restrictedLayerCount G p _
    ((measurableSet_restricted_exactCluster G K x A).inter
      (measurableSet_restrictedHit G D x T).compl),←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : w ∈ W
  · simp only [hw,if_true]
    exact upper_cluster_peak_connection_comparison_in_domain G p D D' K J hKD hKD' hJD' x u w A T hu hAT hJI hfin
  · simp only [hw,if_false,mul_zero]
    exact le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakComparisonAveraging
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

theorem peak_layer_comparison_averaged_in_domain (p : unitInterval)
    (D D' K J : Set E) (hKD : K ⊆ D) (hJD : J ⊆ D) (hJK : Disjoint J K)
    (hKD' : K ⊆ D') (hJD' : J ⊆ D')
    (x : V) (U T W : Set V) (b : ℝ≥0∞)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G (ω ∩ D) v).Finite)
    (hbound : ∀ u ∈ U, b ≤
      ∑' w, if w ∈ W then law p (connectionAvoidingHit G D J u w T) else 0) :
    law p ((restrictedHit G D x T)ᶜ ∩ restrictedHit G K x U)*b ≤
      ∫⁻ ω, (restrictedHit G D x T)ᶜ.indicator
        (fun ω => restrictedLayerCount G D' W ω x) ω ∂law p := by
  let P := (restrictedHit G D x T)ᶜ
  let ι := {A : Finset V // ((A : Set V) ∩ U).Nonempty ∧ Disjoint (A : Set V) T}
  let C (i : ι) : Set (Set E) := {ω | cluster G (ω ∩ K) x=(i.val : Set V)} ∩ P
  have hm (i : ι) : MeasurableSet (C i) :=
    (measurableSet_restricted_exactCluster G K x _).inter
      (measurableSet_restrictedHit G D x T).compl
  have hd : Pairwise (fun i j : ι => Disjoint (C i) (C j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro ω ⟨hi,_⟩ ⟨hj,_⟩
    exact hij (Subtype.ext (Finset.coe_injective (hi.symm.trans hj)))
  have hpart : law p (P ∩ restrictedHit G K x U)=∑' i : ι, law p (C i) := by
    calc
      _ = law p (⋃ i : ι, C i) := by
        apply measure_congr
        filter_upwards [hfin x] with ω hω
        apply propext
        constructor
        · rintro ⟨hp,u,hu,hxu⟩
          have hfK : (cluster G (ω ∩ K) x).Finite := hω.subset fun v hv =>
            conn_mono G (Set.inter_subset_inter_right _ hKD) hv
          let A := hfK.toFinset
          have hA : cluster G (ω ∩ K) x=(A : Set V) := hfK.coe_toFinset.symm
          have hU : ((A : Set V) ∩ U).Nonempty := ⟨u,hA ▸ hxu,hu⟩
          have hT : Disjoint (A : Set V) T := by
            apply Set.disjoint_left.mpr
            intro v hv hvT
            apply hp
            refine ⟨v,hvT,conn_mono G (Set.inter_subset_inter_right _ hKD) ?_⟩
            change v ∈ cluster G (ω ∩ K) x
            rwa [hA]
          exact Set.mem_iUnion.mpr ⟨⟨A,hU,hT⟩,hA,hp⟩
        · intro hh
          obtain ⟨i,hi,hp⟩ := Set.mem_iUnion.mp hh
          obtain ⟨u,hu,huU⟩ := i.property.1
          refine ⟨hp,u,huU,?_⟩
          change u ∈ cluster G (ω ∩ K) x
          rwa [hi]
      _ = _ := measure_iUnion hd hm
  have hcell (i : ι) : law p (C i)*b ≤
      ∫⁻ ω, (C i).indicator (fun ω => restrictedLayerCount G D' W ω x) ω ∂law p := by
    obtain ⟨u,hu,huU⟩ := i.property.1
    have hJI : J ⊆ D \ (K ∩ ballIncidentEdges G (i.val : Set V)) := by
      intro e he
      exact ⟨hJD he,fun h => Set.disjoint_left.mp hJK he h.1⟩
    have hf : ∀ᵐ ω ∂law p,
        (cluster G (ω ∩ (D \ (K ∩ ballIncidentEdges G (i.val : Set V)))) u).Finite := by
      filter_upwards [hfin u] with ω hω
      exact hω.subset fun v hv => conn_mono G
        (Set.inter_subset_inter_right _ Set.sdiff_subset) hv
    exact (mul_le_mul' le_rfl (hbound u huU)).trans
      (upper_cluster_peak_layer_comparison_in_domain G p D D' K J hKD hKD' hJD' x u _ T W hu i.property.2 hJI hf)
  calc
    _ = ∑' i : ι, law p (C i)*b := by rw [hpart,ENNReal.tsum_mul_right]
    _ ≤ ∑' i : ι, ∫⁻ ω, (C i).indicator
        (fun ω => restrictedLayerCount G D' W ω x) ω ∂law p := ENNReal.tsum_le_tsum hcell
    _ = ∫⁻ ω in ⋃ i : ι, C i, restrictedLayerCount G D' W ω x ∂law p := by
      simp_rw [lintegral_indicator (hm _)]
      exact (lintegral_iUnion hm hd _).symm
    _ ≤ ∫⁻ ω in P, restrictedLayerCount G D' W ω x ∂law p := by
      apply lintegral_mono_set
      intro ω hω
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hω
      exact hi.2
    _ = _ := (lintegral_indicator (measurableSet_restrictedHit G D x T).compl
      (fun ω => restrictedLayerCount G D' W ω x)).symm

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakExposureGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma upper_mask_lower_bound (f : V → ℝ) (R b d : ℝ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → |f w-f v| ≤ R)
    (D : Set E) (hd : d ≤ b-R) :
    D \ internalEdges G {z | f z ≤ b} ⊆ internalEdges G {z | d ≤ f z} := by
  intro e he v hve
  have hn : ¬∀ z ∈ G e, f z ≤ b := he.2
  push Not at hn
  obtain ⟨z,hze,hz⟩ := hn
  have hh := (abs_le.mp (hjump e z v hze hve)).1
  change d ≤ f v
  linarith

lemma upper_cluster_crossing_cover (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → |f w-f v| ≤ R)
    (D : Set E) (ω : Set E) (x y : V) (hx : b < f x) (hy : f y ≤ b)
    (hxy : Conn G (ω ∩ D) x y) :
    ∃ z, b-R ≤ f z ∧ f z ≤ b ∧
      Conn G (ω ∩ (D \ internalEdges G {z | f z ≤ b})) x z := by
  let K := D \ internalEdges G {z | f z ≤ b}
  have aux : ∀ z, Conn G (ω ∩ D) x z →
      (∃ v, b-R ≤ f v ∧ f v ≤ b ∧ Conn G (ω ∩ K) x v) ∨
        (b < f z ∧ Conn G (ω ∩ K) x z) := by
    intro z hz
    induction hz with
    | refl => exact Or.inr ⟨hx,conn_refl G _ x⟩
    | @tail v w hxv hvw ih =>
      rcases ih with ih | ⟨hv,hxv⟩
      · exact Or.inl ih
      · obtain ⟨e,he,heq⟩ := hvw
        have heK : e ∈ K := ⟨he.2,fun hh => (not_le_of_gt hv) (hh v (by rw [heq]; simp))⟩
        have hxw : Conn G (ω ∩ K) x w := hxv.tail ⟨e,⟨he.1,heK⟩,heq⟩
        by_cases hw : f w ≤ b
        · have hh := (abs_le.mp (hjump e v w (by rw [heq]; simp) (by rw [heq]; simp))).1
          exact Or.inl ⟨w,by linarith,hw,hxw⟩
        · exact Or.inr ⟨lt_of_not_ge hw,hxw⟩
  rcases aux y hxy with hh | hh
  · exact hh
  · exact ((not_lt_of_ge hy) hh.1).elim

lemma connection_restrict_below_peak (D J : Set E) (hJD : J ⊆ D)
    (f : V → ℝ) (c : ℝ) (ω : Set E) (x y : V)
    (hpeak : ∀ z, Conn G (ω ∩ D) x z → f z ≤ c)
    (hxy : Conn G (ω ∩ J) x y) :
    Conn G (ω ∩ (J ∩ internalEdges G {z | f z ≤ c})) x y := by
  have hh := conn_restrict_cluster_of_subset G (ω ∩ D) x
    (Set.inter_subset_inter_right _ hJD) (mem_cluster_self G _ x) hxy
  have hs : cluster G (ω ∩ D) x ⊆ {z | f z ≤ c} := hpeak
  simpa only [Set.inter_assoc] using conn_mono G
    (Set.inter_subset_inter_right _ (internalEdges_mono G hs)) hh

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedStrictHalfspacePeak_iff_avoid (a : V → ℝ) (d : ℝ) (ω : Set E) (x : V) :
    G.adjustedStrictHalfspacePeak a d ω x x ↔
      ω ∉ restrictedHit G.ends (Percolation.internalEdges G.ends
        {z | d ≤ G.orbitAdjustedHeight a x z}) x
          {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z} := by
  constructor
  · intro hp ⟨z,⟨hzx,hz⟩,hconn⟩
    exact (not_lt_of_ge hz) (hp z hconn hzx)
  · intro hp z hz hzx
    exact lt_of_not_ge fun hh => hp ⟨z,⟨hzx,hh⟩,hz⟩

lemma strict_peak_slab_band_count_eq (a : V → ℝ) (r l u : ℝ) (hlu : l ≤ u)
    (ω : Set E) (x : V) :
    G.strictPeakSlabBandCount a r l u ω x =
      (restrictedHit G.ends (Percolation.internalEdges G.ends
        {z | l-r ≤ G.orbitAdjustedHeight a x z}) x
          {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z})ᶜ.indicator
      (fun ω => restrictedLayerCount G.ends (Percolation.internalEdges G.ends
        {z | u-r ≤ G.orbitAdjustedHeight a x z})
          {z | l ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u} ω x) ω := by
  by_cases hp : G.adjustedStrictHalfspacePeak a (l-r) ω x x
  · have havoid := (G.adjustedStrictHalfspacePeak_iff_avoid a (l-r) ω x).mp hp
    rw [Set.indicator_of_mem havoid]
    apply tsum_congr
    intro y
    have hupper : ∀ z, Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | l-r ≤ G.orbitAdjustedHeight a x z}) x z → G.orbitAdjustedHeight a x z ≤ 0 := by
      intro z hz
      by_cases hzx : z=x
      · simp only [hzx,G.orbitAdjustedHeight_self,le_refl]
      · exact (hp z hz hzx).le
    have hc : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | u-r ≤ G.orbitAdjustedHeight a x z}) x y ↔
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | u-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ 0}) x y := by
      constructor
      · intro hh
        have hj : Percolation.internalEdges G.ends {z | u-r ≤ G.orbitAdjustedHeight a x z} ⊆
            Percolation.internalEdges G.ends {z | l-r ≤ G.orbitAdjustedHeight a x z} :=
          Percolation.internalEdges_mono G.ends (fun z hz => by
            change u-r ≤ G.orbitAdjustedHeight a x z at hz
            change l-r ≤ G.orbitAdjustedHeight a x z
            linarith)
        have h := connection_restrict_below_peak G.ends _ _ hj (G.orbitAdjustedHeight a x) 0 ω x y hupper hh
        apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _ ?_) h
        rintro e ⟨he,he'⟩ z hze
        exact ⟨he z hze,he' z hze⟩
      · exact Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
          (Percolation.internalEdges_mono G.ends (fun _ hz => hz.1)))
    unfold strictPeakSlabBandTransport
    simp only [hp,true_and,←hc,Set.mem_ofPred_eq,and_comm]
    split_ifs <;> rfl
  · have havoid := mt (G.adjustedStrictHalfspacePeak_iff_avoid a (l-r) ω x).mpr hp
    rw [Set.indicator_of_notMem havoid]
    apply ENNReal.tsum_eq_zero.mpr
    intro y
    simp only [strictPeakSlabBandTransport,hp,false_and,if_false]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakOrbitComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma mixedHeightLayerMoment_eq_of_orbit (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (p : unitInterval) (d c l u ad t : ℝ) {x y : V}
    (h : G.vertexOrbit x=G.vertexOrbit y) :
    G.mixedHeightLayerMoment a p d c l u ad t x =
      G.mixedHeightLayerMoment a p d c l u ad t y := by
  obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
  change φ.vertex y=x at hφ
  rw [←hφ,G.mixedHeightLayerMoment_aut a ha]

lemma mixedHeight_continuation_at_boundary
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (d N : ℕ) (hd : ∀ z, Percolation.degree G.ends z ≤ d)
    (p : unitInterval) (R M k r ell : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hell : 0 < ell) (x u v₀ : V)
    (hu : -ell-R ≤ G.orbitAdjustedHeight a x u ∧ G.orbitAdjustedHeight a x u ≤ -ell)
    (hpath : ∃ v, ∃ q : G.fullGraph.Walk u v,
      G.vertexOrbit v=G.vertexOrbit v₀ ∧ q.length ≤ N ∧
      (∀ z ∈ q.support, -M ≤ G.orbitAdjustedHeight a u z ∧ G.orbitAdjustedHeight a u z ≤ 0) ∧
      G.orbitAdjustedHeight a u v ≤ -R) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1)))*
      G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
      ∑' w, if -ell-k-M-2*R ≤ G.orbitAdjustedHeight a x w ∧
          G.orbitAdjustedHeight a x w ≤ -ell-k then
        G.law p (connectionAvoidingHit G.ends
          (Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z})
          (Percolation.internalEdges G.ends {z | -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧
            G.orbitAdjustedHeight a x z ≤ -ell})
          u w {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z}) else 0 := by
  obtain ⟨v,q,horb,hlen,hq,hend⟩ := hpath
  let P : Set V := {z | -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧
    G.orbitAdjustedHeight a x z ≤ -ell}
  let D := Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z}
  let J := Percolation.internalEdges G.ends P
  let T : Set V := {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z}
  let W : Set V := {z | -ell-k-M-2*R ≤ G.orbitAdjustedHeight a x z ∧
    G.orbitAdjustedHeight a x z ≤ -ell-k}
  have hsupp : ∀ z ∈ q.support, z ∈ P := by
    intro z hz
    change -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -ell
    rw [G.orbitAdjustedHeight_change_base hc hl a x u z]
    have hh := hq z hz
    constructor <;> linarith [hu.1,hu.2,hh.1,hh.2]
  have hg : G.fullGraph=Percolation.openSimpleGraph G.ends Set.univ :=
    criticalModel_openGraph G.ends Set.univ
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by simpa only [←hg,id_eq] using h⟩
  obtain ⟨q',hqlen,hqsupp⟩ := walk_internal_restriction G.ends (q.map f) P (by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    change z ∈ q.support.map id at hz
    exact hsupp z (by simpa only [List.map_id_fun,id_eq] using hz))
  have hlen' : q'.length ≤ N := by
    rw [hqlen,SimpleGraph.Walk.length_map]
    exact hlen
  have havoid : ∀ z ∈ q'.support, z ∉ T := by
    intro z hz hzt
    rw [hqsupp,SimpleGraph.Walk.support_map] at hz
    change z ∈ q.support.map id at hz
    have hzq : z ∈ q.support := by simpa only [List.map_id_fun,id_eq] using hz
    have hh := (hsupp z hzq).2
    exact (not_le_of_gt hell) (by linarith [hzt.2])
  have hJD : J ⊆ D := Percolation.internalEdges_mono G.ends (by
    intro z hz
    change -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -ell at hz
    change -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z
    linarith [hz.1])
  have hroot := mixed_root_walk_layer_moment G.ends hl d hd p D J hJD T W u v q' havoid
  have hδ : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hδ1 : min (p : ℝ) (1-p) ≤ 1 := (min_le_left _ _).trans p.2.2
  have hcost : ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1))) ≤
      ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(q'.length+1))) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ hδ1
      (Nat.mul_le_mul_left d (Nat.add_le_add_right hlen' 1)))
  have hvlo : -ell-R-M ≤ G.orbitAdjustedHeight a x v := by
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
    have hh := (hq v q.end_mem_support).1
    linarith [hu.1]
  have hvhi : G.orbitAdjustedHeight a x v ≤ -ell-R := by
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
    linarith [hu.2]
  rw [←G.mixedHeightLayerMoment_eq_of_orbit a ha p _ _ _ _ _ _ horb]
  have hroot' := hroot
  simp only [D,J,T,W,Set.mem_ofPred_eq] at hroot'
  exact (mul_le_mul' hcost
    (G.mixedHeightLayerMoment_le_continuation hc hl a p R M k r ell hR hM x v hvlo hvhi)).trans hroot'

omit [Countable V] [Countable E] in
lemma fullPeakDownHit_subset_exposed
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R M k r ell : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hell : 0 < ell)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (x : V) :
    G.fullPeakDownHit a ell x ⊆
      (restrictedHit G.ends
        (Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z})
        x {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z})ᶜ ∩
      restrictedHit G.ends
        ((Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z}) \
          Percolation.internalEdges G.ends {z | G.orbitAdjustedHeight a x z ≤ -ell})
        x {z | -ell-R ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -ell} := by
  rintro ω ⟨⟨_hxx,hpeak⟩,y,hy,hxy⟩
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight a x w-G.orbitAdjustedHeight a x v| ≤ R := by
    intro e v w hv hw
    rw [G.orbitAdjustedHeight_change_base hc hl a x v w,add_sub_cancel_left]
    exact hjump e v w hv hw
  obtain ⟨z,hzlo,hzhi,hxz⟩ := upper_cluster_crossing_cover G.ends (G.orbitAdjustedHeight a x)
    R (-ell) hj Set.univ ω x y (by rw [G.orbitAdjustedHeight_self]; linarith) hy hxy
  have hmask : Set.univ \ Percolation.internalEdges G.ends {z | G.orbitAdjustedHeight a x z ≤ -ell} ⊆
      Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z} :=
    upper_mask_lower_bound G.ends (G.orbitAdjustedHeight a x) R (-ell) _ hj Set.univ (by linarith)
  refine ⟨?_,z,⟨hzlo,hzhi⟩,?_⟩
  · rintro ⟨v,⟨hvx,hv⟩,hxv⟩
    have hh := hpeak v (Percolation.conn_mono G.ends Set.inter_subset_left hxv) hvx
    have hself := G.orbitAdjustedHeight_self a x
    linarith
  · apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _ ?_) hxz
    intro e he
    exact ⟨hmask he,he.2⟩

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSlabComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem full_peak_lower_slab_comparison
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (d N : ℕ) (hd : ∀ z, Percolation.degree G.ends z ≤ d)
    (p : unitInterval) (R M k r ell : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hell : 0 < ell)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (hpaths : ∀ u (j : G.VertexOrbit), ∃ v, ∃ q : G.fullGraph.Walk u v,
      G.vertexOrbit v=j ∧ q.length ≤ N ∧
      (∀ z ∈ q.support, -M ≤ G.orbitAdjustedHeight a u z ∧ G.orbitAdjustedHeight a u z ≤ 0) ∧
      G.orbitAdjustedHeight a u v ≤ -R)
    (hfin : ∀ v, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω v).Finite)
    (x v₀ : V) :
    (G.law p (G.fullPeakDownHit a ell x))*
      ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1)))*
        G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
      ∫⁻ ω, G.strictPeakSlabBandCount a (r+R+M) (-ell-k-M-2*R) (-ell-k) ω x ∂G.law p := by
  let f := G.orbitAdjustedHeight a x
  let D := Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ f z}
  let D' := Percolation.internalEdges G.ends {z | -ell-k-r-R-M ≤ f z}
  let K := D \ Percolation.internalEdges G.ends {z | f z ≤ -ell}
  let J := Percolation.internalEdges G.ends {z | -ell-k-r-R-M ≤ f z ∧ f z ≤ -ell}
  let U : Set V := {z | -ell-R ≤ f z ∧ f z ≤ -ell}
  let T : Set V := {z | z ≠ x ∧ 0 ≤ f z}
  let W : Set V := {z | -ell-k-M-2*R ≤ f z ∧ f z ≤ -ell-k}
  let b := ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1)))*
    G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |f w-f v| ≤ R := by
    intro e v w hv hw
    dsimp [f]
    rw [G.orbitAdjustedHeight_change_base hc hl a x v w,add_sub_cancel_left]
    exact hjump e v w hv hw
  have hD'D : D' ⊆ D := Percolation.internalEdges_mono G.ends (by
    intro z hz
    change -ell-k-r-R-M ≤ f z at hz
    change -ell-k-r-2*M-3*R ≤ f z
    linarith)
  have hJD' : J ⊆ D' := Percolation.internalEdges_mono G.ends (fun _ hz => hz.1)
  have hKD' : K ⊆ D' := upper_mask_lower_bound G.ends f R (-ell) _ hj D (by linarith)
  have hJK : Disjoint J K := Set.disjoint_left.mpr (by
    intro e heJ heK
    exact heK.2 (fun z hz => (heJ z hz).2))
  have hfinD : ∀ v, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends (ω ∩ D) v).Finite := by
    intro v
    filter_upwards [hfin v] with ω hω
    exact hω.subset fun z hz => Percolation.conn_mono G.ends Set.inter_subset_left hz
  have hbound : ∀ u ∈ U, b ≤
      ∑' w, if w ∈ W then G.law p (connectionAvoidingHit G.ends D J u w T) else 0 := by
    intro u hu
    exact G.mixedHeight_continuation_at_boundary hc hl a ha d N hd p R M k r ell hR hM
      hk hr hell x u v₀ hu (hpaths u (G.vertexOrbit v₀))
  have hcmp := peak_layer_comparison_averaged_in_domain G.ends p D D' K J
    Set.sdiff_subset (hJD'.trans hD'D) hJK hKD' hJD' x U T W b hfinD (by
      intro u hu
      refine (hbound u hu).trans_eq ?_
      apply tsum_congr
      intro w
      split_ifs <;> rfl)
  have hsub : G.fullPeakDownHit a ell x ⊆
      (restrictedHit G.ends D x T)ᶜ ∩ restrictedHit G.ends K x U :=
    G.fullPeakDownHit_subset_exposed hc hl a R M k r ell hR hM hk hr hell hjump x
  have hdEq : (-ell-k-M-2*R)-(r+R+M)= -ell-k-r-2*M-3*R := by ring
  have hcEq : (-ell-k)-(r+R+M)= -ell-k-r-R-M := by ring
  have heq (ω : Set E) : G.strictPeakSlabBandCount a (r+R+M) (-ell-k-M-2*R) (-ell-k) ω x =
      (restrictedHit G.ends D x T)ᶜ.indicator
        (fun ω => restrictedLayerCount G.ends D' W ω x) ω := by
    simpa only [hdEq,hcEq] using G.strict_peak_slab_band_count_eq a (r+R+M)
      (-ell-k-M-2*R) (-ell-k) (by linarith) ω x
  calc
    _ = G.law p (G.fullPeakDownHit a ell x)*b := by dsimp [b]; rw [mul_assoc]
    _ ≤ G.law p ((restrictedHit G.ends D x T)ᶜ ∩ restrictedHit G.ends K x U)*b :=
      mul_le_mul' (measure_mono hsub) le_rfl
    _ ≤ ∫⁻ ω, (restrictedHit G.ends D x T)ᶜ.indicator
        (fun ω => restrictedLayerCount G.ends D' W ω x) ω ∂G.law p := hcmp
    _ = _ := lintegral_congr fun ω => (heq ω).symm

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_WeightedPeakSlabComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem weighted_full_peak_lower_slab_comparison
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (d N : ℕ) (hd : ∀ z, Percolation.degree G.ends z ≤ d)
    (p : unitInterval) (R M k r ell : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hell : 0 < ell)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (hpaths : ∀ u (j : G.VertexOrbit), ∃ v, ∃ q : G.fullGraph.Walk u v,
      G.vertexOrbit v=j ∧ q.length ≤ N ∧
      (∀ z ∈ q.support, -M ≤ G.orbitAdjustedHeight a u z ∧ G.orbitAdjustedHeight a u z ≤ 0) ∧
      G.orbitAdjustedHeight a u v ≤ -R)
    (hfin : ∀ v, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω v).Finite) (v₀ : V) :
    G.fullPeakDownProbability O a p ell*
      ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1)))*
        G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*
        (∫⁻ ω, G.strictPeakSlabBandCount a (r+R+M) (-ell-k-M-2*R) (-ell-k) ω x ∂G.law p) := by
  unfold fullPeakDownProbability
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal (a x)))
    (G.full_peak_lower_slab_comparison hc hl a ha d N hd p R M k r ell hR hM hk hr hell
      hjump hpaths hfin x v₀)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CriticalPeakComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_peak_comparison_at_rate_bs_oai
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t))
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ M : ℝ, 0 < M ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧ ∃ L : ℝ, 0 < L ∧
      ∀ k, 0 ≤ k → ∀ r, 0 ≤ r → ∀ ell, 0 < ell → ∀ v₀,
      (criticalModel G).fullPeakDownProbability
        ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq))
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell*
      (criticalModel G).mixedHeightLayerMoment ((criticalModel G).stationaryOrbitWeight μ)
        (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
          K*ENNReal.ofReal (Real.exp (L*r-(α-1)*(ell+k))) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let O := H.orbitRepresentatives (criticalModel_quasiTransitive G hq)
  have hHc := criticalModel_connected G hc
  obtain ⟨N,M,hM,hpaths⟩ := H.stationaryOrbitHeight_bounded_orbit_below hHc hl
    (criticalModel_quasiTransitive G hq) μ hμ hstat hu R hR hjump
  obtain ⟨d,_hdpos,hd⟩ := exists_degree_bound G hq
  obtain ⟨C,L,hC,hL,hband⟩ := critical_peak_band_bound_at_rate G hc hl hq hu μ hμ hstat α hcross
  let cost := ENNReal.ofReal ((min (pc G : ℝ) (1-pc G))^(d*(N+1)))
  have hp0 : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  have hp1 : (pc G : ℝ) < 1 := by exact_mod_cast hpc1
  have hcost0 : cost ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact pow_pos (lt_min hp0 (sub_pos.mpr hp1)) _
  have hcosttop : cost ≠ ⊤ := ENNReal.ofReal_ne_top
  let W := ∑ x ∈ O.roots, ENNReal.ofReal (a x)
  let K := cost⁻¹*W*ENNReal.ofReal (C*Real.exp (L*(R+M)+M+2*R))
  have hW : W < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  have hK : K < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (bot_lt_iff_ne_bot.mpr hcost0)) hW) ENNReal.ofReal_lt_top
  refine ⟨M,hM,K,hK,L,hL,fun k hk r hr ell hell v₀ => ?_⟩
  have hcmp := H.weighted_full_peak_lower_slab_comparison O hHc hl a
    (H.stationaryOrbitWeight_aut μ) d N hd (pc G) R M k r ell hR.le hM.le hk hr hell
    hjump hpaths (critical_finite_general_bs G hc hl hq hpc1) v₀
  have hbound := hband (r+R+M) (by positivity) (-ell-k-M-2*R) (-ell-k) (by linarith)
  have hcancel : cost⁻¹*cost=1 := ENNReal.inv_mul_cancel hcost0 hcosttop
  calc
    _ = cost⁻¹*((H.fullPeakDownProbability O a (pc G) ell*cost)*
        H.mixedHeightLayerMoment a (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀) := by
      let P := H.fullPeakDownProbability O a (pc G) ell
      let X := H.mixedHeightLayerMoment a (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀
      change P*X=cost⁻¹*((P*cost)*X)
      calc
        _ = (cost⁻¹*cost)*(P*X) := by rw [hcancel,one_mul]
        _ = _ := by ac_rfl
    _ ≤ cost⁻¹*(W*ENNReal.ofReal (C*Real.exp (L*(r+R+M)+α*(-ell-k)-(-ell-k-M-2*R)))) :=
      mul_le_mul' le_rfl (hcmp.trans hbound)
    _ = K*ENNReal.ofReal (Real.exp (L*r-(α-1)*(ell+k))) := by
      have he : C*Real.exp (L*(r+R+M)+α*(-ell-k)-(-ell-k-M-2*R)) =
          (C*Real.exp (L*(R+M)+M+2*R))*Real.exp (L*r-(α-1)*(ell+k)) := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        ring
      rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ C*Real.exp (L*(R+M)+M+2*R))]
      dsimp [K]
      ac_rfl

end Percolation.BenjaminiSchramm

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate_bs_oai.{u_1, u_2} := @OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate_bs_oai.{u_1, u_2}
