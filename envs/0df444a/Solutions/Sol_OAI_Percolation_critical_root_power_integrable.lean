-- Prove2me | solution 1 for OAI.Percolation.critical_root_power_integrable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:02:49.562019+00:00
-- url     : https://prove2.me/submissions/3022681e-df62-425c-ace6-50722b70a5d4

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_EndpointProfile_eventually_neighborMoment_lower
import Theorems.Thm_OAI_Percolation_efficient_endpoint_profiles_of_divergent_moment

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Basic
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

section Countability


theorem exists_mem_reachBall {G : BondGraph V E} {x y : V}
    (h : Relation.ReflTransGen (Adj G) x y) : ∃ n, y ∈ reachBall G x n := by
  induction h with
  | refl => exact ⟨0, Set.mem_singleton _⟩
  | @tail y z _ hyz ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, Or.inr ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨y, hn, hyz⟩

end Countability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Bounds
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

 
theorem map_openEdges (p : unitInterval) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p) =
      law p := by
  unfold law
  rw [setBernoulli_eq_map]
  have hmeas : Measurable (fun labels : E → unitInterval => fun e => labels e ≤ p) :=
    Measurable.of_eval (fun e => (measurable_threshold p).comp (measurable_pi_apply e))
  have he : (fun labels : E → unitInterval => openEdges labels p) =
      (fun f : E → Prop => {e | f e}) ∘ (fun labels e => labels e ≤ p) := rfl
  rw [he, ← Measure.map_map measurable_setOfPred hmeas]
  unfold labelLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_threshold p)]
  simp only [map_threshold, Set.mem_univ, bernoulliMeasure_def]

end Coupling

section CouplingOrder
variable [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
theorem measurable_openEdges (p : unitInterval) :
    Measurable (fun labels : E → unitInterval => openEdges labels p) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_threshold p).comp (measurable_pi_apply e)))

theorem twoPoint_eq_labelLaw (p : unitInterval) (x y : V) :
    twoPoint G p x y =
      (labelLaw {labels : E → unitInterval | Conn G (openEdges labels p) x y}).toReal := by
  unfold twoPoint
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p)
    (measurableSet_conn G x y)]
  rfl

omit [Countable E] in
theorem openEdges_mono (labels : E → unitInterval) : Monotone (openEdges labels) := by
  intro p q hpq e he
  exact he.trans hpq

theorem twoPoint_mono (x y : V) : Monotone (fun p => twoPoint G p x y) := by
  intro p q hpq
  change twoPoint G p x y ≤ twoPoint G q x y
  rw [twoPoint_eq_labelLaw, twoPoint_eq_labelLaw]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro labels h
  exact conn_mono G (openEdges_mono labels hpq) h

end CouplingOrder

section CouplingLimits
open Filter Topology


theorem ae_labels_ne [Countable E] (q : unitInterval) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), ∀ e, labels e ≠ q := by
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  simp only [not_not]
  change labelLaw ((fun labels : E → unitInterval => labels e) ⁻¹' {q}) = 0
  rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton q)]
  change (Measure.infinitePi (fun _ : E => (volume : Measure unitInterval))).map
    (fun labels => labels e) {q} = 0
  rw [Measure.infinitePi_map_eval]
  simp

end CouplingLimits

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_ProductMeasure_Association
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
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

 
theorem map_nonempty (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set F)).map Set.Nonempty = bitLaw (orParameter q (Fintype.card F)) := by
  let μ := (law q : Measure (Set F)).map Set.Nonempty
  have hm : Measurable (Set.Nonempty : Set F → Prop) := .of_discrete
  have : IsProbabilityMeasure μ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
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
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Paths
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

theorem finiteWitness_edge (e : E) : FiniteWitness {ω : Set E | e ∈ ω} := by
  intro ω he
  exact ⟨{e}, by simpa using he, by simp⟩

end SmallParameter

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Sprinkling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SprinklingLaw
attribute [local instance] Classical.propDecidable

 theorem map_bool_or (p a : unitInterval) :
    (Measure.infinitePi (fun b : Bool => bitLaw (pairParameter p a b))).map
      (fun f : Bool → Prop => ∃ b, f b) = bitLaw (sprinkleParameter p a) := by
  let μ := (Measure.infinitePi (fun b : Bool => bitLaw (pairParameter p a b))).map
      (fun f : Bool → Prop => ∃ b, f b)
  have hm : Measurable (fun f : Bool → Prop => ∃ b, f b) := .of_discrete
  have : IsProbabilityMeasure μ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hf : μ.real {False} = (1-(p : ℝ)) * (1-(a : ℝ)) := by
    change ((Measure.infinitePi _).map _).real _ = _
    rw [Measure.real, Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun f : Bool → Prop => ∃ b, f b) ⁻¹' ({False} : Set Prop) =
        ((Finset.univ : Finset Bool) : Set Bool).pi (fun _ => ({False} : Set Prop)) := by
      ext f
      simp [and_comm]
    rw [he, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    simp [pairParameter, bitLaw, ENNReal.toReal_mul]
  have ht : μ.real {True} = (p : ℝ) + (1-p)*a := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext b; simp
    rw [he, measureReal_compl (measurableSet_singleton _), probReal_univ, hf]
    ring
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (sprinkleParameter p a)).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [ht]
    simp [bitLaw, Measure.real, sprinkleParameter]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hf]
    simp [bitLaw, Measure.real, sprinkleParameter]
    ring

 theorem measurable_fieldUnion : Measurable (fieldUnion : (Bool → Set E) → Set E) := by
  have hm (e : E) : Measurable (fun f : Bool → Set E => e ∈ fieldUnion f) := by
    apply measurableSet_setOfPred.mp
    change MeasurableSet ({f : Bool → Set E | e ∈ f true} ∪ {f | e ∈ f false})
    apply MeasurableSet.union <;> apply measurableSet_setOfPred.mpr
    · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp
        (measurable_pi_apply true)
    · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp
        (measurable_pi_apply false)
  exact measurable_setOfPred.comp (Measurable.of_eval hm)

 theorem map_fieldUnion (p a : unitInterval) :
    (fieldLaw p a).map (fieldUnion : (Bool → Set E) → Set E) = law (sprinkleParameter p a) := by
  let μ := fun b : Bool => bitLaw (pairParameter p a b)
  let s := fun f : Bool → E → Prop => fun b => {e | f b e}
  have hs : Measurable s := Measurable.of_eval
    (fun b => measurable_setOfPred.comp (measurable_pi_apply b))
  have hstart : (Measure.infinitePi (fun b : Bool => Measure.infinitePi (fun _ : E => μ b))).map s =
      fieldLaw p a := by
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_setOfPred)]
    congr 1
    funext b
    rw [law, setBernoulli_eq_map]
    rfl
  rw [← hstart, Measure.map_map measurable_fieldUnion hs]
  let f := (MeasurableEquiv.curry Bool E Prop).symm
  let swap := MeasurableEquiv.piCongrLeft (fun _ : E × Bool => Prop) (Equiv.prodComm Bool E)
  let c := MeasurableEquiv.curry E Bool Prop
  let b := fun g : E → Bool → Prop => fun e => ∃ j, g e j
  have hb : Measurable b := Measurable.of_eval
    (fun e => (Measurable.of_discrete : Measurable (fun f : Bool → Prop => ∃ j, f j)).comp
      (measurable_pi_apply e))
  have he : fieldUnion ∘ s = (fun g : E → Prop => {e | g e}) ∘ b ∘ c ∘ swap ∘ f := by
    funext g
    ext e
    simp [fieldUnion, s, b, c, swap, f, Function.comp_def, Bool.exists_bool, or_comm, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]
  rw [he, ← Measure.map_map measurable_setOfPred (hb.comp (c.measurable.comp (swap.measurable.comp f.measurable))),
    ← Measure.map_map hb (c.measurable.comp (swap.measurable.comp f.measurable))]
  rw [← Measure.map_map c.measurable (swap.measurable.comp f.measurable),
    ← Measure.map_map swap.measurable f.measurable]
  rw [Measure.infinitePi_map_curry_symm]
  rw [show (Measure.infinitePi (fun x : Bool × E => μ x.1)).map swap =
      Measure.infinitePi (fun x : E × Bool => μ x.2) from
    Measure.infinitePi_map_piCongrLeft (fun x : E × Bool => μ x.2) (Equiv.prodComm Bool E)]
  rw [Measure.infinitePi_map_curry (fun (_ : E) (j : Bool) => μ j)]
  dsimp only [b]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  have hm : (Measure.infinitePi (fun j : Bool => μ j)).map Exists =
      bitLaw (sprinkleParameter p a) := map_bool_or p a
  rw [hm, law, setBernoulli_eq_map]
  rfl

 theorem fieldLaw_map_pair (p a : unitInterval) :
    (fieldLaw p a).map (fun f : Bool → Set E => (f true, f false)) =
      (law p).prod (law a) := by
  simpa [fieldLaw, pairParameter] using
    (Measure.infinitePi_map_eval_prod (P := fun b : Bool => (law (pairParameter p a b) : Measure (Set E)))
    (by decide : true ≠ false))

 theorem law_map_union (p a : unitInterval) :
    ((law p : Measure (Set E)).prod (law a)).map (fun f => f.1 ∪ f.2) =
      law (sprinkleParameter p a) := by
  rw [← fieldLaw_map_pair p a, Measure.map_map]
  · exact map_fieldUnion p a
  · have h : Measurable (fun f : Set E × Set E => fun e => e ∈ f.1 ∪ f.2) := by
      apply Measurable.of_eval
      intro e
      apply measurableSet_setOfPred.mp
      change MeasurableSet ({f : Set E × Set E | e ∈ f.1} ∪ {f | e ∈ f.2})
      apply MeasurableSet.union <;> apply measurableSet_setOfPred.mpr
      · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_fst
      · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_snd
    exact measurable_setOfPred.comp h
  · exact (measurable_pi_apply true).prodMk (measurable_pi_apply false)

end SprinklingLaw

section SprinklingPaths
attribute [local instance] Classical.propDecidable

 
theorem Along.first_outside {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) (S : Set E) :
    (∀ e ∈ l, e ∈ S) ∨ ∃ a b e l₁ l₂,
      l = l₁ ++ e :: l₂ ∧ Along G x l₁ a ∧ G e = s(a,b) ∧
      Along G b l₂ y ∧ (∀ d ∈ l₁, d ∈ S) ∧ e ∉ S := by
  induction h with
  | nil => left; simp
  | @cons x z y l e he ht ih =>
    by_cases hes : e ∈ S
    · rcases ih with hall | ⟨a,b,d,l₁,l₂,hl,h₁,hd,h₂,hopen,hnot⟩
      · left
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hes hall
      · right
        refine ⟨a,b,d,e::l₁,l₂,by simp [hl], .cons e he h₁, hd, h₂, ?_, hnot⟩
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hes hopen
    · right
      exact ⟨x,z,e,[],l,rfl,.nil x,he,ht,by simp,hes⟩


end SprinklingPaths

section ColoredSprinkling
attribute [local instance] Classical.propDecidable

 theorem finiteWitness_inter (A : Set (Set E)) (hA : FiniteWitness A) (S : Set E) :
    FiniteWitness {ω | ω ∩ S ∈ A} := by
  intro ω h
  obtain ⟨s,hs,hsa⟩ := hA (ω ∩ S) h
  refine ⟨s,hs.trans Set.inter_subset_left,?_⟩
  have he : (s : Set E) ∩ S = s := Set.inter_eq_left.mpr (hs.trans Set.inter_subset_right)
  change (s : Set E) ∩ S ∈ A
  rwa [he]

end ColoredSprinkling

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Sharpness
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

section FiniteRusso
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem bernoulliPolynomial_congr (s : Finset E) {f g : Finset E → ℝ}
    (h : ∀ t ⊆ s, f t = g t) (p : ℝ) :
    bernoulliPolynomial s f p = bernoulliPolynomial s g p := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_powerset.mp ht)]

theorem bernoulliPolynomial_sub (s : Finset E) (f g : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => f t-g t) p =
      bernoulliPolynomial s f p - bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial, sub_mul, Finset.sum_sub_distrib]


theorem hasDerivAt_bernoulliPolynomial (s : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    HasDerivAt (bernoulliPolynomial s f)
      (∑ e ∈ s, bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p) p := by
  induction s using Finset.induction_on generalizing f with
  | empty =>
    convert hasDerivAt_const p (f ∅) using 1 <;> try rfl
    · funext q
      exact bernoulliPolynomial_empty f q
  | @insert e s he ih =>
    have hd := (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul (ih f)).add
      ((hasDerivAt_id p).mul (ih (fun t => f (insert e t))))
    have hf : bernoulliPolynomial (insert e s) f =
        fun q => (1-q)*bernoulliPolynomial s f q +
          q*bernoulliPolynomial s (fun t => f (insert e t)) q :=
      funext fun q => bernoulliPolynomial_insert s e he f q
    rw [hf]
    convert hd using 1 <;> try rfl
    have hs : ∑ a ∈ s, bernoulliPolynomial ((insert e s).erase a)
          (fun t => f (insert a t)-f t) p =
        (1-p)*(∑ a ∈ s, bernoulliPolynomial (s.erase a) (fun t => f (insert a t)-f t) p) +
        p*(∑ a ∈ s, bernoulliPolynomial (s.erase a)
          (fun t => f (insert e (insert a t))-f (insert e t)) p) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have hae : e ≠ a := (ne_of_mem_of_not_mem ha he).symm
      rw [Finset.erase_insert_of_ne hae, bernoulliPolynomial_insert _ e
        (fun hh => he (Finset.mem_of_mem_erase hh))]
      congr 2
      apply bernoulliPolynomial_congr
      intro t _
      rw [Finset.insert_comm e a]
    simp only [Finset.sum_insert he, Finset.erase_insert he, zero_sub, neg_one_mul,
      one_mul, Pi.sub_apply, id_eq]
    rw [hs, bernoulliPolynomial_sub]
    ring

theorem bernoulliPolynomial_nonneg (s : Finset E) (f : Finset E → ℝ) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hf : ∀ t ⊆ s, 0 ≤ f t) :
    0 ≤ bernoulliPolynomial s f p := by
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (mul_nonneg (hf t (Finset.mem_powerset.mp ht))
    (pow_nonneg hp.1 _)) (pow_nonneg (sub_nonneg.mpr hp.2) _)

theorem bernoulliPolynomial_mono (s : Finset E) (f g : Finset E → ℝ) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hfg : ∀ t ⊆ s, f t ≤ g t) :
    bernoulliPolynomial s f p ≤ bernoulliPolynomial s g p := by
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hfg t (Finset.mem_powerset.mp ht)) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

 
theorem bernoulliPolynomial_union (s t : Finset E) (hdis : Disjoint s t)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t) f p =
      bernoulliPolynomial s (fun a => bernoulliPolynomial t (fun b => f (a ∪ b)) p) p := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert e s he ih =>
    have hed : e ∉ t := (Finset.disjoint_insert_left.mp hdis).1
    have hst : Disjoint s t := (Finset.disjoint_insert_left.mp hdis).2
    rw [Finset.insert_union, bernoulliPolynomial_insert _ e (by simp [he, hed]),
      bernoulliPolynomial_insert s e he, ih hst, ih hst]
    congr 2
    apply bernoulliPolynomial_congr
    intro a _
    apply bernoulliPolynomial_congr
    intro b _
    rw [Finset.insert_union]

 

theorem bernoulliPolynomial_closed_difference (s : Finset E) (e : E) (he : e ∈ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => if e ∈ t then 0 else f (insert e t)-f t) p =
      (1-p)*bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
  have hes : e ∉ s.erase e := Finset.notMem_erase e s
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e hes]
  have hc : bernoulliPolynomial (s.erase e)
      (fun t => if e ∈ t then 0 else f (insert e t)-f t) p =
      bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
    apply bernoulliPolynomial_congr
    intro t ht
    simp [show e ∉ t from fun h => hes (ht h)]
  rw [hc]
  simp

theorem closed_difference_russo (s : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    (1-p)*deriv (bernoulliPolynomial s f) p =
      ∑ e ∈ s, bernoulliPolynomial s
        (fun t => if e ∈ t then 0 else f (insert e t)-f t) p := by
  rw [(hasDerivAt_bernoulliPolynomial s f p).deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact (bernoulliPolynomial_closed_difference s e he f p).symm


theorem finiteEventPolynomial_eq (s : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial s A (p : ℝ) = finiteProbability p s A := by
  unfold finiteEventPolynomial bernoulliPolynomial finiteProbability
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : (t : Set E) ∈ A <;> simp [ht]


theorem closedPivotal_difference (A : Set (Set E)) (hA : IsUpperSet A) (e : E)
    (t : Finset E) :
    (if (t : Set E) ∈ closedPivotal A e then (1:ℝ) else 0) =
    (if e ∈ t then 0 else
      (if ((insert e t : Finset E) : Set E) ∈ A then (1:ℝ) else 0) -
      (if (t : Set E) ∈ A then 1 else 0)) := by
  by_cases he : e ∈ t
  · simp [closedPivotal, he]
  · by_cases ha : (t : Set E) ∈ A
    · have hi : insert e (t : Set E) ∈ A := hA (Set.subset_insert e _) ha
      simp [closedPivotal, he, ha, hi]
    · by_cases hi : insert e (t : Set E) ∈ A <;> simp [closedPivotal, he, ha, hi]


end FiniteRusso

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem mem_unexposed_of_conn (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∈ unexposed G Λ ω) (hxy : Conn G ω x y) :
    y ∈ unexposed G Λ ω := by
  intro z hyz
  exact hx z (hxy.trans hyz)

 
theorem conn_restrict_unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∈ unexposed G Λ ω) (hxy : Conn G ω x y) :
    Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x y := by
  induction hxy with
  | refl => exact conn_refl _ _ _
  | @tail y z hxy hyz ih =>
    obtain ⟨e,he,hends⟩ := hyz
    have hy : y ∈ unexposed G Λ ω := mem_unexposed_of_conn G Λ ω hx hxy
    have hz : z ∈ unexposed G Λ ω := mem_unexposed_of_conn G Λ ω hy (.single ⟨e,he,hends⟩)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e y z hends).mpr ⟨hy,hz⟩⟩,hends⟩

 
theorem unexposed_boundary_closed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {e : E} {a b : V} (he : G e = s(a,b))
    (ha : a ∈ unexposed G Λ ω) (hb : b ∉ unexposed G Λ ω) : e ∉ ω := by
  intro ho
  exact hb (mem_unexposed_of_conn G Λ ω ha (.single ⟨e,ho,he⟩))

 

theorem unexposed_insert_crossing (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {e : E} {a b x : V} (he : G e = s(a,b))
    (hx : x ∈ unexposed G Λ ω) (_ha : a ∈ unexposed G Λ ω)
    (hb : b ∉ unexposed G Λ ω) :
    x ∉ unexposed G Λ (insert e ω) ↔
      Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x a := by
  classical
  constructor
  · intro hn
    obtain ⟨y,hxy,hy⟩ := by simpa [unexposed, not_forall, Classical.not_imp] using hn
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | h | h
    · exact (hy (hx y h)).elim
    · exact conn_restrict_unexposed G Λ ω hx h.1
    · exact (hb (mem_unexposed_of_conn G Λ ω hx h.1)).elim
  · intro hxa hn
    have hxa' : Conn G ω x a := conn_mono G Set.inter_subset_left hxa
    apply hb
    intro y hby
    exact hn y ((conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨hxa',hby⟩)))

 
theorem not_mem_unexposed_of_conn (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ unexposed G Λ ω) (hxy : Conn G ω x y) :
    y ∉ unexposed G Λ ω := by
  intro hy
  exact hx (mem_unexposed_of_conn G Λ ω hy (conn_symm G ω hxy))

 
theorem conn_sdiff_internal_unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ unexposed G Λ ω) (hxy : Conn G ω x y) :
    Conn G (ω \ internalEdges G (unexposed G Λ ω)) x y := by
  induction hxy with
  | refl => exact conn_refl _ _ _
  | @tail y z hxy hyz ih =>
    obtain ⟨e,he,hends⟩ := hyz
    have hy : y ∉ unexposed G Λ ω := not_mem_unexposed_of_conn G Λ ω hx hxy
    exact ih.tail ⟨e,⟨he,fun hi => hy ((mem_internalEdges_of_ends G _ e y z hends).mp hi).1⟩,hends⟩

 
theorem unexposed_sdiff_internal (G : BondGraph V E) (Λ : Set V) (ω : Set E) :
    unexposed G Λ (ω \ internalEdges G (unexposed G Λ ω)) = unexposed G Λ ω := by
  ext x
  constructor
  · intro hx
    by_contra hn
    apply hn
    intro y hxy
    exact hx y (conn_sdiff_internal_unexposed G Λ ω hn hxy)
  · intro hx y hxy
    exact hx y (conn_mono G Set.sdiff_subset hxy)

 
theorem unexposed_union_internal (G : BondGraph V E) (Λ : Set V) (ω η : Set E)
    (hη : η ⊆ internalEdges G (unexposed G Λ ω)) :
    unexposed G Λ (ω ∪ η) = unexposed G Λ ω := by
  ext x
  constructor
  · intro hx y hxy
    exact hx y (conn_mono G Set.subset_union_left hxy)
  · intro hx y hxy
    suffices hy : y ∈ unexposed G Λ ω from unexposed_subset G Λ ω hy
    induction hxy with
    | refl => exact hx
    | @tail y z hxy hyz ih =>
      obtain ⟨e,hωe,he⟩ := hyz
      rcases hωe with ho | hηe
      · exact mem_unexposed_of_conn G Λ ω ih (.single ⟨e,ho,he⟩)
      · exact ((mem_internalEdges_of_ends G _ e y z he).mp (hη hηe)).2

 
theorem unexposed_union_eq_iff (G : BondGraph V E) (Λ S : Set V) (a b : Set E)
    (ha : a ⊆ internalEdges G S) (hb : Disjoint b (internalEdges G S)) :
    unexposed G Λ (a ∪ b) = S ↔ unexposed G Λ b = S := by
  constructor
  · intro h
    have he : (a ∪ b) \ internalEdges G S = b := by
      ext e
      constructor
      · rintro ⟨he,hn⟩
        exact he.resolve_left (fun he => hn (ha he))
      · intro he
        exact ⟨Or.inr he,fun hi => Set.disjoint_left.mp hb he hi⟩
    simpa only [h, he] using unexposed_sdiff_internal G Λ (a ∪ b)
  · intro h
    have he := unexposed_union_internal G Λ b a (h ▸ ha)
    simpa only [Set.union_comm b a,h] using he


theorem escapeEvent_isUpperSet (G : BondGraph V E) (Λ : Set V) (x : V) :
    IsUpperSet (escapeEvent G Λ x) := by
  intro ω η hωη hx hη
  apply hx
  intro y hxy
  exact hη y (conn_mono G hωη hxy)

 
theorem escape_closed_pivotal_iff (G : BondGraph V E) (Λ : Set V)
    (ω : Set E) (x : V) (e : E) :
    (e ∉ ω ∧ ω ∉ escapeEvent G Λ x ∧ insert e ω ∈ escapeEvent G Λ x) ↔
      x ∈ unexposed G Λ ω ∧ ∃ a b,
        G e = s(a,b) ∧ a ∈ unexposed G Λ ω ∧ b ∉ unexposed G Λ ω ∧
        Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x a := by
  classical
  constructor
  · rintro ⟨_,hx,hn⟩
    have hx' : x ∈ unexposed G Λ ω := by simpa [escapeEvent] using hx
    refine ⟨hx',?_⟩
    obtain ⟨⟨a,b⟩,he'⟩ := Sym2.mk_surjective (G e)
    have he : G e = s(a,b) := he'.symm
    obtain ⟨y,hxy,hy⟩ := by simpa [escapeEvent,unexposed,not_forall,Classical.not_imp] using hn
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | h | h
    · exact (hy (hx' y h)).elim
    · exact ⟨a,b,he,mem_unexposed_of_conn G Λ ω hx' h.1,
        fun hb => hy (hb y h.2),conn_restrict_unexposed G Λ ω hx' h.1⟩
    · exact ⟨b,a,he.trans (Sym2.eq_swap ..),mem_unexposed_of_conn G Λ ω hx' h.1,
        fun ha => hy (ha y h.2),conn_restrict_unexposed G Λ ω hx' h.1⟩
  · rintro ⟨hx,a,b,he,ha,hb,hxa⟩
    exact ⟨unexposed_boundary_closed G Λ ω he ha hb,by simpa [escapeEvent] using hx,
      (unexposed_insert_crossing G Λ ω he hx ha hb).mpr hxa⟩

attribute [local instance] Classical.decEq

 theorem bernoulliPolynomial_mul_const (s : Finset E) (f : Finset E → ℝ) (c p : ℝ) :
    bernoulliPolynomial s (fun t => f t*c) p = bernoulliPolynomial s f p*c := by
  simp only [bernoulliPolynomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  ring

 theorem bernoulliPolynomial_const_mul (s : Finset E) (f : Finset E → ℝ) (c p : ℝ) :
    bernoulliPolynomial s (fun t => c*f t) p = c*bernoulliPolynomial s f p := by
  simpa only [mul_comm c] using bernoulliPolynomial_mul_const s f c p

 theorem bernoulliPolynomial_sum {ι : Type*} (s : Finset E) (I : Finset ι)
    (f : ι → Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => ∑ i ∈ I, f i t) p =
      ∑ i ∈ I, bernoulliPolynomial s (f i) p := by
  classical
  simp only [bernoulliPolynomial, Finset.sum_mul]
  exact Finset.sum_comm



theorem bernoulliPolynomial_exposure (G : BondGraph V E) (Λ S : Set V)
    (s t : Finset E) (hs : (s : Set E) ⊆ internalEdges G S)
    (ht : Disjoint (t : Set E) (internalEdges G S)) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t)
      (fun a => (if unexposed G Λ (a : Set E) = S then (1:ℝ) else 0) * f (a ∩ s)) p =
    bernoulliPolynomial t (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p *
      bernoulliPolynomial s f p := by
  have hdis : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp ht hf (hs he)
  rw [bernoulliPolynomial_union s t hdis]
  trans bernoulliPolynomial s (fun a =>
    bernoulliPolynomial t (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p * f a) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [← bernoulliPolynomial_mul_const]
    apply bernoulliPolynomial_congr
    intro b hb
    have hab : unexposed G Λ ((a ∪ b : Finset E) : Set E) = S ↔
        unexposed G Λ (b : Set E) = S := by
      rw [Finset.coe_union]
      exact unexposed_union_eq_iff G Λ S _ _ (fun _ he => hs (ha he))
        (ht.mono_left (by exact_mod_cast hb))
    have hbs : b ∩ s = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp (hdis.symm.mono_left hb)
    rw [Finset.union_inter_distrib_right,Finset.inter_eq_left.mpr ha,hbs,Finset.union_empty]
    simp only [hab]
  · exact bernoulliPolynomial_const_mul s f _ p


theorem unexposedRegion_subset (G : BondGraph V E) (Λ : Finset V) (ω : Set E) :
    unexposedRegion G Λ ω ⊆ Λ := by
  intro x hx
  apply unexposed_subset G (Λ : Set V) ω
  simpa only [← coe_unexposedRegion,Finset.mem_coe] using hx

 
theorem bernoulliPolynomial_partition_region (G : BondGraph V E) (Λ : Finset V)
    (F : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial F f p = ∑ S ∈ Λ.powerset,
      bernoulliPolynomial F
        (fun t => if unexposed G (Λ : Set V) (t : Set E) = (S : Set V) then f t else 0) p := by
  rw [← bernoulliPolynomial_sum]
  apply bernoulliPolynomial_congr
  intro t _
  symm
  rw [Finset.sum_eq_single (unexposedRegion G Λ (t : Set E))]
  · simp
  · intro S _ hne
    have hh : unexposed G (Λ : Set V) (t : Set E) ≠ (S : Set V) := by
      intro he
      apply hne
      apply Finset.coe_injective
      exact he.symm.trans (coe_unexposedRegion G Λ (t : Set E)).symm
    simp [hh]
  · intro hn
    exact (hn (Finset.mem_powerset.mpr (unexposedRegion_subset G Λ (t : Set E)))).elim


 theorem internalSupport_subset (G : BondGraph V E) (S : Set V) (F : Finset E) :
    internalSupport G S F ⊆ F := Finset.filter_subset _ _

 theorem internalSupport_union_sdiff (G : BondGraph V E) (S : Set V) (F : Finset E) :
    internalSupport G S F ∪ (F \ internalSupport G S F) = F :=
  Finset.union_sdiff_of_subset (internalSupport_subset G S F)

 theorem coe_inter_internalSupport (G : BondGraph V E) (S : Set V) (F t : Finset E)
    (ht : t ⊆ F) : ((t ∩ internalSupport G S F : Finset E) : Set E) =
      (t : Set E) ∩ internalEdges G S := by
  ext e
  simp only [Finset.mem_coe,Finset.mem_inter,internalSupport,Finset.mem_filter,Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,ht h.1,h.2⟩⟩


 theorem regionProbability_nonneg (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ regionProbability G Λ S F p := by
  apply bernoulliPolynomial_nonneg _ _ _ hp
  intro t _
  split_ifs <;> norm_num

 
theorem bernoulliPolynomial_exposure_factor (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial F
      (fun t => (if unexposed G Λ (t : Set E) = S then (1:ℝ) else 0) *
        f (t ∩ internalSupport G S F)) p =
      regionProbability G Λ S F p * bernoulliPolynomial (internalSupport G S F) f p := by
  let s := internalSupport G S F
  let t := F \ s
  have hs : (s : Set E) ⊆ internalEdges G S := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have ht : Disjoint (t : Set E) (internalEdges G S) := by
    apply Set.disjoint_left.mpr
    intro e he hi
    have he' := Finset.mem_sdiff.mp he
    exact he'.2 (Finset.mem_filter.mpr ⟨he'.1,hi⟩)
  have he : s ∪ t = F := internalSupport_union_sdiff G S F
  have hq : bernoulliPolynomial t
      (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p =
      regionProbability G Λ S F p := by
    simpa only [he,mul_one,bernoulliPolynomial_const,regionProbability] using
      (bernoulliPolynomial_exposure G Λ S s t hs ht (fun _ => 1) p).symm
  simpa only [he,hq] using bernoulliPolynomial_exposure G Λ S s t hs ht f p


theorem finite_escape_russo (G : BondGraph V E) (Λ : Set V) (x : V)
    (F : Finset E) (p : ℝ) :
    (1-p)*deriv (finiteEventPolynomial F (escapeEvent G Λ x)) p =
      bernoulliPolynomial F (fun t => closedEscapeCount G Λ x F (t : Set E)) p := by
  unfold finiteEventPolynomial
  rw [closed_difference_russo]
  unfold closedEscapeCount
  rw [bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply bernoulliPolynomial_congr
  intro t _
  exact (closedPivotal_difference _ (escapeEvent_isUpperSet G Λ x) e t).symm

 
theorem closedEscapeCount_expectation (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) :
    bernoulliPolynomial F (fun t => closedEscapeCount G Λ x F (t : Set E)) p =
      ∑ S ∈ Λ.powerset, if x ∈ S then
        regionProbability G Λ S F p * boundaryExpectation G S x F p else 0 := by
  rw [bernoulliPolynomial_partition_region G Λ F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    unfold boundaryExpectation
    rw [← bernoulliPolynomial_exposure_factor G Λ S F
      (fun t => crossingCount G S x F (t : Set E)) p]
    apply bernoulliPolynomial_congr
    intro t ht
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V)
    · simp only [hreg,ite_true,one_mul]
      apply Finset.sum_congr rfl
      intro e _
      have hc : (t : Set E) ∈ closedPivotal (escapeEvent G Λ x) e ↔
          crossingReach G S x ((t ∩ internalSupport G S F : Finset E) : Set E) e := by
        simpa only [closedPivotal,Set.mem_ofPred_eq,hreg,Finset.mem_coe,hx,true_and,
          coe_inter_internalSupport G S F t ht,crossingReach] using
          escape_closed_pivotal_iff G Λ (t : Set E) x e
      exact if_congr hc rfl rfl
    · simp [hreg]
  · rw [ite_eq_right hx,← bernoulliPolynomial_zero F p]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V)
    · simp only [hreg,ite_true]
      apply Finset.sum_eq_zero
      intro e _
      have hn : (t : Set E) ∉ closedPivotal (escapeEvent G Λ x) e := by
        intro he
        have hh := ((escape_closed_pivotal_iff G Λ (t : Set E) x e).mp he).1
        apply hx
        simpa only [hreg,Finset.mem_coe] using hh
      simp [hn]
    · simp [hreg]

 
theorem finite_escape_complement (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) :
    1-finiteEventPolynomial F (escapeEvent G Λ x) p =
      ∑ S ∈ Λ.powerset, if x ∈ S then regionProbability G Λ S F p else 0 := by
  have he : 1-finiteEventPolynomial F (escapeEvent G Λ x) p =
      bernoulliPolynomial F
        (fun t => if x ∈ unexposed G (Λ : Set V) (t : Set E) then (1:ℝ) else 0) p := by
    change 1-bernoulliPolynomial F (fun t => if (t : Set E) ∈ escapeEvent G Λ x then 1 else 0) p = _
    rw [show (1:ℝ) = bernoulliPolynomial F (fun _ => 1) p from (bernoulliPolynomial_const F 1 p).symm]
    rw [← bernoulliPolynomial_sub]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hx : x ∈ unexposed G (Λ : Set V) (t : Set E) <;> simp [escapeEvent,hx,bernoulliPolynomial_const]
  rw [he,bernoulliPolynomial_partition_region G Λ F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V) <;> simp [hreg,hx]
  · rw [ite_eq_right hx,← bernoulliPolynomial_zero F p]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V) <;> simp [hreg,hx]

 

theorem finite_escape_differential_lower (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hcost : ∀ S ⊆ Λ, x ∈ S → 1 ≤ p*boundaryExpectation G (S : Set V) x F p) :
    1-finiteEventPolynomial F (escapeEvent G Λ x) p ≤
      p*(1-p)*deriv (finiteEventPolynomial F (escapeEvent G Λ x)) p := by
  rw [mul_assoc,finite_escape_russo,closedEscapeCount_expectation,finite_escape_complement,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  by_cases hx : x ∈ S
  · simp only [ite_eq_left hx]
    have hq := regionProbability_nonneg G Λ S F p hp
    calc
      regionProbability G Λ S F p ≤
          regionProbability G Λ S F p * (p*boundaryExpectation G S x F p) :=
        le_mul_of_one_le_right hq (hcost S (Finset.mem_powerset.mp hS) hx)
      _ = p*(regionProbability G Λ S F p * boundaryExpectation G S x F p) := by ring
  · simp [hx]

 theorem bernoulliPolynomial_monotoneOn (F : Finset E) (f : Finset E → ℝ)
    (hf : ∀ a b, a ⊆ b → f a ≤ f b) :
    MonotoneOn (bernoulliPolynomial F f) (Set.Icc (0:ℝ) 1) := by
  have hd : Differentiable ℝ (bernoulliPolynomial F f) :=
    fun q => (hasDerivAt_bernoulliPolynomial F f q).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hd.continuous.continuousOn hd.differentiableOn
  intro q hq
  have hq' : q ∈ Set.Icc (0:ℝ) 1 := interior_subset hq
  rw [(hasDerivAt_bernoulliPolynomial F f q).deriv]
  apply Finset.sum_nonneg
  intro e _
  apply bernoulliPolynomial_nonneg _ _ _ hq'
  intro t _
  exact sub_nonneg.mpr (hf t (insert e t) (Finset.subset_insert e t))

 theorem crossingCount_mono (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) {ω η : Set E} (h : ω ⊆ η) :
    crossingCount G S x F ω ≤ crossingCount G S x F η := by
  apply Finset.sum_le_sum
  intro e _
  have hh : crossingReach G S x ω e → crossingReach G S x η e := by
    rintro ⟨a,b,he,ha,hb,hc⟩
    exact ⟨a,b,he,ha,hb,conn_mono G h hc⟩
  by_cases hω : crossingReach G S x ω e
  · simp [hω,hh hω]
  · simp only [ite_eq_right hω]
    split_ifs <;> norm_num

 theorem boundaryExpectation_nonneg (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ boundaryExpectation G S x F p := by
  apply bernoulliPolynomial_nonneg _ _ _ hp
  intro t _
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

 theorem boundaryExpectation_monotoneOn (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) : MonotoneOn (boundaryExpectation G S x F) (Set.Icc (0:ℝ) 1) := by
  apply bernoulliPolynomial_monotoneOn
  intro a b hab
  exact crossingCount_mono G S x F (by exact_mod_cast hab)

 theorem boundaryCost_monotoneOn (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) : MonotoneOn (fun p => p*boundaryExpectation G S x F p)
      (Set.Icc (0:ℝ) 1) := by
  intro p hp q hq hpq
  exact mul_le_mul hpq (boundaryExpectation_monotoneOn G S x F hp hq hpq)
    (boundaryExpectation_nonneg G S x F p hp) hq.1

 theorem finiteEventPolynomial_mem_Icc (F : Finset E) (A : Set (Set E))
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    finiteEventPolynomial F A p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply bernoulliPolynomial_nonneg _ _ _ hp
    intro t _
    split_ifs <;> norm_num
  · calc
      finiteEventPolynomial F A p ≤ bernoulliPolynomial F (fun _ => 1) p := by
        apply bernoulliPolynomial_mono _ _ _ _ hp
        intro t _
        split_ifs <;> norm_num
      _ = 1 := bernoulliPolynomial_const F 1 p

 

theorem differential_escape_growth {f : ℝ → ℝ} {r p : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (hp : p < 1)
    (hf : Differentiable ℝ f) (hbound : ∀ q ∈ Set.Icc r p, f q ∈ Set.Icc (0:ℝ) 1)
    (hineq : ∀ q ∈ Set.Icc r p, 1-f q ≤ q*(1-q)*deriv f q) :
    1-Real.exp (r-p) ≤ f p := by
  have hd (q : ℝ) : HasDerivAt (fun u => Real.exp u*(1-f u))
      (Real.exp q*(1-f q)+Real.exp q*(0-deriv f q)) q :=
    (Real.hasDerivAt_exp q).mul ((hasDerivAt_const q 1).sub (hf q).hasDerivAt)
  have hanti : AntitoneOn (fun q => Real.exp q*(1-f q)) (Set.Icc r p) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc r p)
      (Real.continuous_exp.mul (continuous_const.sub hf.continuous)).continuousOn
      (fun q _ => (hd q).hasDerivWithinAt)
    intro q hq
    have hqi : q ∈ Set.Icc r p := interior_subset hq
    have hq0 : 0 < q := hr.trans_le hqi.1
    have hq1 : q < 1 := hqi.2.trans_lt hp
    have hcoef : 0 < q*(1-q) := mul_pos hq0 (sub_pos.mpr hq1)
    have hder : 0 ≤ deriv f q := nonneg_of_mul_nonneg_right
      ((sub_nonneg.mpr (hbound q hqi).2).trans (hineq q hqi)) hcoef
    have hc : q*(1-q) ≤ 1 := by nlinarith [sq_nonneg q]
    have hsmall : 1-f q ≤ deriv f q := (hineq q hqi).trans
      (mul_le_of_le_one_left hder hc)
    have hn := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos q).le
      (show 1-f q-deriv f q ≤ 0 by linarith)
    nlinarith only [hn]
  have hle := hanti (show r ∈ Set.Icc r p from ⟨le_rfl,hrp⟩)
    (show p ∈ Set.Icc r p from ⟨hrp,le_rfl⟩) hrp
  have he : Real.exp p*(1-f p) ≤ Real.exp r := by
    calc
      Real.exp p*(1-f p) ≤ Real.exp r*(1-f r) := hle
      _ ≤ Real.exp r := mul_le_of_le_one_right (Real.exp_pos r).le
        (by linarith [(hbound r ⟨le_rfl,hrp⟩).1])
  have hfin : 1-f p ≤ Real.exp (r-p) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos p)).mpr
    simpa only [mul_comm] using he
  linarith

 

theorem finite_escape_probability_lower (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (r p : ℝ) (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S ⊆ Λ, x ∈ S → 1 ≤ r*boundaryExpectation G (S : Set V) x F r) :
    0 < 1-Real.exp (r-p) ∧
      1-Real.exp (r-p) ≤ finiteEventPolynomial F (escapeEvent G Λ x) p := by
  have hrI : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr.le,(hrp.trans hp).le⟩
  have hqI (q : ℝ) (hq : q ∈ Set.Icc r p) : q ∈ Set.Icc (0:ℝ) 1 :=
    ⟨hr.le.trans hq.1,hq.2.trans hp.le⟩
  refine ⟨sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hrp)),?_⟩
  apply differential_escape_growth hr hrp.le hp
  · intro q
    exact (hasDerivAt_bernoulliPolynomial F _ q).differentiableAt
  · intro q hq
    exact finiteEventPolynomial_mem_Icc F _ q (hqI q hq)
  · intro q hq
    apply finite_escape_differential_lower G Λ x F q (hqI q hq)
    intro S hS hx
    exact (hcost S hS hx).trans (boundaryCost_monotoneOn G S x F hrI (hqI q hq) hq.1)

end ExteriorExposure

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology

theorem bernoulliPolynomial_map {F : Type*} (f : E ↪ F) (s : Finset E)
    (h : Finset F → ℝ) (p : ℝ) :
    bernoulliPolynomial (s.map f) h p =
      bernoulliPolynomial s (fun t => h (t.map f)) p := by
  induction s using Finset.induction_on generalizing h with
  | empty => simp
  | @insert e s he ih =>
    rw [Finset.map_insert,bernoulliPolynomial_insert _ (f e) (by simpa using he),
      bernoulliPolynomial_insert s e he,ih,ih]
    simp only [Finset.map_insert]

theorem finiteEventPolynomial_restrict (F : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial F A (p : ℝ) = (law p).real {ω | ω ∩ (F : Set E) ∈ A} := by
  let f : (F : Set E) ↪ E := ⟨Subtype.val,Subtype.val_injective⟩
  have hm : (Finset.univ : Finset (F : Set E)).map f = F := by
    ext e
    simp [f]
  have he : finiteEventPolynomial F A (p : ℝ) =
      finiteEventPolynomial (Finset.univ : Finset (F : Set E))
        {η | f '' η ∈ A} (p : ℝ) := by
    unfold finiteEventPolynomial
    calc
      bernoulliPolynomial F (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ) =
        bernoulliPolynomial (Finset.univ.map f) (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ) :=
          congrArg (fun H => bernoulliPolynomial H (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ)) hm.symm
      _ = _ := by
        rw [bernoulliPolynomial_map]
        apply bernoulliPolynomial_congr
        intro t _
        simp only [Finset.coe_map]
        rfl
  rw [he,finiteEventPolynomial_eq,finiteProbability_univ,← law_map_restrict p (F : Set E),
    measureReal_def,Measure.map_apply (measurable_set_restrict _) .of_discrete]
  congr 2
  ext ω
  have hh : f '' (Subtype.val ⁻¹' ω : Set (F : Set E)) = ω ∩ (F : Set E) := by
    ext e
    simp [f,and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,hh]

theorem bernoulliPolynomial_restrict (F H : Finset E) (hFH : F ⊆ H)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial H (fun t => f (t ∩ F)) p = bernoulliPolynomial F f p := by
  rw [← Finset.union_sdiff_of_subset hFH,bernoulliPolynomial_union _ _ Finset.disjoint_sdiff]
  trans bernoulliPolynomial F (fun a => f a) p
  · apply bernoulliPolynomial_congr
    intro a ha
    trans bernoulliPolynomial (H \ F) (fun _ => f a) p
    · apply bernoulliPolynomial_congr
      intro b hb
      have hdis : Disjoint b F := (Finset.disjoint_sdiff.symm).mono_left hb
      rw [Finset.union_inter_distrib_right,Finset.inter_eq_left.mpr ha,
        Finset.disjoint_iff_inter_eq_empty.mp hdis,Finset.union_empty]
    · exact bernoulliPolynomial_const _ _ _
  · rfl


theorem escapeEvent_restrict_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) (ω : Set E) :
    ω ∩ (incidentSupport G hloc Λ : Set E) ∈ escapeEvent G Λ x ↔
      ω ∈ escapeEvent G Λ x := by
  constructor
  · exact escapeEvent_isUpperSet G Λ x Set.inter_subset_left
  · intro hx
    by_contra hn
    have hx' : x ∈ unexposed G Λ (ω ∩ (incidentSupport G hloc Λ : Set E)) := by
      simpa only [escapeEvent,Set.mem_ofPred_eq,not_not] using hn
    apply hx
    intro y hxy
    have hc : Conn G (ω ∩ (incidentSupport G hloc Λ : Set E)) x y := by
      induction hxy with
      | refl => exact conn_refl _ _ _
      | @tail a b hxa hab ih =>
        obtain ⟨e,he,heab⟩ := hab
        have ha : a ∈ Λ := hx' a ih
        have hF : e ∈ incidentSupport G hloc Λ :=
          (mem_incidentSupport G hloc Λ e).mpr ⟨a,ha,by simp [heab]⟩
        exact ih.tail ⟨e,⟨he,hF⟩,heab⟩
    exact hx' y hc

theorem finite_escape_eq_law (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) (p : unitInterval) :
    finiteEventPolynomial (incidentSupport G hloc Λ) (escapeEvent G Λ x) (p : ℝ) =
      (law p).real (escapeEvent G Λ x) := by
  rw [finiteEventPolynomial_restrict]
  congr 1
  ext ω
  exact escapeEvent_restrict_incident G hloc Λ x ω

theorem internal_edge_mem_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) {e : E} (he : e ∈ internalEdges G (S : Set V)) :
    e ∈ incidentSupport G hloc S := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G e)
  have ha : a ∈ G e := by rw [← hab]; simp
  exact (mem_incidentSupport G hloc S e).mpr ⟨a,he a ha,ha⟩

theorem internalSupport_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) :
    internalSupport G S F = internalSupport G S (incidentSupport G hloc S) := by
  ext e
  simp only [internalSupport,Finset.mem_filter]
  exact ⟨fun h => ⟨internal_edge_mem_incident G hloc S h.2,h.2⟩,
    fun h => ⟨hF h.1,h.2⟩⟩

theorem crossingCount_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) (ω : Set E) :
    crossingCount G S x F ω = crossingCount G S x (incidentSupport G hloc S) ω := by
  symm
  apply Finset.sum_subset hF
  intro e _ he
  have hn : ¬ crossingReach G S x ω e := by
    rintro ⟨a,b,hab,ha,_,_⟩
    exact he ((mem_incidentSupport G hloc S e).mpr ⟨a,ha,by simp [hab]⟩)
  simp [hn]

theorem boundaryExpectation_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) (p : ℝ) :
    boundaryExpectation G S x F p =
      boundaryExpectation G S x (incidentSupport G hloc S) p := by
  unfold boundaryExpectation
  rw [internalSupport_eq_of_incident_subset G hloc S F hF]
  apply bernoulliPolynomial_congr
  intro t _
  exact crossingCount_eq_of_incident_subset G hloc S x F hF t


theorem measurableSet_escapeEvent (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) : MeasurableSet (escapeEvent G Λ x) := by
  let F := incidentSupport G hloc Λ
  have he : escapeEvent G Λ x =
      (fun ω => (Subtype.val ⁻¹' ω : Set (F : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ escapeEvent G Λ x} := by
    ext ω
    have hh : Subtype.val '' (Subtype.val ⁻¹' ω : Set (F : Set E)) = ω ∩ (F : Set E) := by
      ext e
      simp [and_comm]
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hh]
    exact (escapeEvent_restrict_incident G hloc Λ x ω).symm
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem escapeEvent_antitone_domain (G : BondGraph V E) {S Λ : Set V} (hS : S ⊆ Λ)
    (x : V) : escapeEvent G Λ x ⊆ escapeEvent G S x := by
  intro ω hω hn
  apply hω
  intro y hxy
  exact hS (hn y hxy)

theorem vertexExhaustion_mono [Encodable V] :
    Monotone (vertexExhaustion : ℕ → Finset V) := by
  intro m n h x hx
  simp only [vertexExhaustion,Finset.mem_preimage,Finset.mem_range] at hx ⊢
  exact hx.trans_le h

theorem subset_vertexExhaustion [Encodable V] (S : Finset V) :
    ∃ n, S ⊆ vertexExhaustion n := by
  refine ⟨S.sup Encodable.encode+1,?_⟩
  intro x hx
  simp only [vertexExhaustion,Finset.mem_preimage,Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup hx)

theorem infinite_cluster_eq_iInter_escape [Encodable V] (G : BondGraph V E) (x : V) :
    {ω | (cluster G ω x).Infinite} = ⋂ n, escapeEvent G (vertexExhaustion (V := V) n : Set V) x := by
  ext ω
  simp only [Set.mem_ofPred_eq,Set.mem_iInter]
  constructor
  · intro hi n hn
    exact hi ((vertexExhaustion n).finite_toSet.subset (by
      intro y hy; exact hn y hy))
  · intro he hf
    obtain ⟨n,hn⟩ := subset_vertexExhaustion hf.toFinset
    apply he n
    intro y hy
    exact hn (hf.mem_toFinset.mpr hy)

 
theorem infinite_cluster_probability_ge_of_escape [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (p : unitInterval) (c : ℝ)
    (hc : ∀ Λ : Finset V, c ≤ (law p).real (escapeEvent G Λ x)) :
    c ≤ (law p).real {ω | (cluster G ω x).Infinite} := by
  let := Encodable.ofCountable V
  rw [infinite_cluster_eq_iInter_escape]
  have hm : Antitone (fun n => escapeEvent G (vertexExhaustion (V := V) n : Set V) x) := by
    intro m n h
    exact escapeEvent_antitone_domain G (by exact_mod_cast vertexExhaustion_mono h) x
  have ht := tendsto_measure_iInter_atTop (μ := law p)
    (fun n => (measurableSet_escapeEvent G hloc (vertexExhaustion n) x).nullMeasurableSet)
    hm ⟨0,measure_ne_top _ _⟩
  have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact ge_of_tendsto hr (Eventually.of_forall (fun n => hc (vertexExhaustion n)))

 

theorem infinite_cluster_probability_pos_of_bad_cost [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (r p : unitInterval)
    (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S : Finset V, x ∈ S → 1 ≤ boundaryCost G hloc S x (r : ℝ)) :
    0 < (law p).real {ω | (cluster G ω x).Infinite} := by
  have hc : 0 < 1-Real.exp ((r:ℝ)-(p:ℝ)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hrp))
  apply hc.trans_le
  apply infinite_cluster_probability_ge_of_escape G hloc x p
  intro Λ
  rw [← finite_escape_eq_law G hloc Λ x p]
  apply (finite_escape_probability_lower G Λ x (incidentSupport G hloc Λ)
    (r:ℝ) (p:ℝ) hr hrp hp ?_).2
  intro S hS hx
  rw [boundaryExpectation_eq_of_incident_subset G hloc S x _ (incidentSupport_mono G hloc hS)]
  exact hcost S hx

theorem pc_le_of_infinite_cluster_probability_pos (G : BondGraph V E)
    (x : V) (p : unitInterval) (hp : 0 < (law p).real {ω | (cluster G ω x).Infinite}) :
    pc G ≤ p := by
  apply sInf_le
  have hh : 0 < law p {ω | (cluster G ω x).Infinite} := (ENNReal.toReal_pos_iff.mp hp).1
  apply hh.trans_le
  apply measure_mono
  intro ω hω
  exact ⟨cluster G ω x,hω,x,rfl⟩

 
theorem exists_subcritical_testSet [Countable V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∃ S : Finset V, x ∈ S ∧ boundaryCost G hloc S x (p:ℝ) < 1 := by
  by_cases hz : p = 0
  · exact ⟨{x},by simp,by simp [hz,boundaryCost]⟩
  · have hp0 : 0 < p := bot_lt_iff_ne_bot.mpr hz
    by_contra! hn
    obtain ⟨q,hpq,hqc⟩ := exists_between hp
    have hq1 : q < 1 := hqc.trans_le (show pc G ≤ 1 from (pc G).2.2)
    have hs := infinite_cluster_probability_pos_of_bad_cost G hloc x p q hp0 hpq hq1 hn
    exact (not_le_of_gt hqc) (pc_le_of_infinite_cluster_probability_pos G x q hs)

theorem internalEdges_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (e : E) :
    b e ∈ internalEdges G (a '' S) ↔ e ∈ internalEdges G S := by
  constructor
  · intro he x hx
    have hh := he (a x) (by rw [h e]; exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩)
    simpa using hh
  · intro he y hy
    rw [h e,Sym2.mem_map] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact Set.mem_image_of_mem a (he x hx)

theorem crossingReach_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (ω : Set E) (e : E) :
    crossingReach G (a '' S) (a x) (b '' ω) (b e) ↔ crossingReach G S x ω e := by
  constructor
  · rintro ⟨c,d,he,hc,hd,hconn⟩
    have he' : G e = s(a.symm c,a.symm d) := by
      have hh := congrArg (Sym2.map a.symm) he
      rw [h e,Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id,Sym2.map_mk] at hh
      exact hh
    refine ⟨a.symm c,a.symm d,he',?_,?_,?_⟩
    · simpa using hc
    · simpa using hd
    · have hh := (conn_aut_iff G h (b '' ω) x (a.symm c)).mpr (by simpa using hconn)
      simpa only [Set.preimage_image_eq _ b.injective] using hh
  · rintro ⟨c,d,he,hc,hd,hconn⟩
    refine ⟨a c,a d,?_,by simpa using hc,by simpa using hd,conn_aut G h hconn⟩
    rw [h e,he,Sym2.map_mk]

theorem internalSupport_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (F : Finset E) :
    internalSupport G (a '' S) (F.map b.toEmbedding) =
      (internalSupport G S F).map b.toEmbedding := by
  ext e
  obtain ⟨d,rfl⟩ := b.surjective e
  simp [internalSupport,internalEdges_aut_iff G h]

theorem crossingCount_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (F : Finset E) (ω : Set E) :
    crossingCount G (a '' S) (a x) (F.map b.toEmbedding) (b '' ω) =
      crossingCount G S x F ω := by
  simp only [crossingCount,Finset.sum_map,Equiv.toEmbedding_apply,crossingReach_aut_iff G h]

theorem boundaryExpectation_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (F : Finset E) (p : ℝ) :
    boundaryExpectation G (a '' S) (a x) (F.map b.toEmbedding) p =
      boundaryExpectation G S x F p := by
  unfold boundaryExpectation
  rw [internalSupport_aut G h,bernoulliPolynomial_map]
  apply bernoulliPolynomial_congr
  intro t _
  simp only [Finset.coe_map,Equiv.coe_toEmbedding]
  exact crossingCount_aut G h S x F t

theorem boundaryCost_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (S : Finset V) (x : V) (p : ℝ) :
    boundaryCost G hloc (S.map a.toEmbedding) (a x) p = boundaryCost G hloc S x p := by
  unfold boundaryCost
  rw [incidentSupport_aut G hloc h,Finset.coe_map]
  exact congrArg (p*·) (boundaryExpectation_aut G h S x (incidentSupport G hloc S) p)

 

theorem exists_uniform_subcritical_testSets [Countable V] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) :
    ∃ (L : ℕ) (a : ℝ), 0 ≤ a ∧ a < 1 ∧ ∀ x, ∃ S : Finset V,
      x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p:ℝ) ≤ a := by
  obtain ⟨O,hO⟩ := hqt
  choose S hmem hcost using exists_subcritical_testSet G hloc p hp
  have hOn : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO (Classical.arbitrary V)
    exact ⟨o,ho⟩
  let L := O.sup (fun x => (S x).card)
  let a := max 0 (O.sup' hOn (fun x => boundaryCost G hloc (S x) x (p:ℝ)))
  refine ⟨L,a,le_max_left _ _,?_,?_⟩
  · apply max_lt zero_lt_one
    exact (Finset.sup'_lt_iff hOn).mpr (fun x _ => hcost x)
  · intro x
    obtain ⟨o,ho,α,β,hαβ,rfl⟩ := hO x
    refine ⟨(S o).map α.toEmbedding,?_,?_,?_⟩
    · simp only [Finset.mem_map,Equiv.toEmbedding_apply]
      exact ⟨o,hmem o,rfl⟩
    · simpa only [Finset.card_map] using Finset.le_sup (f := fun x => (S x).card) ho
    · rw [boundaryCost_aut G hloc hαβ]
      exact (Finset.le_sup' (f := fun x => boundaryCost G hloc (S x) x (p:ℝ)) ho).trans
        (le_max_right _ _)

end SharpnessBridge

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq


theorem cut_spec [Nonempty V] (G : BondGraph V E) (S : Set V) {e : E}
    (he : CutExists G S e) :
    G e = s(cutInside G S e,cutOutside G S e) ∧
      cutInside G S e ∈ S ∧ cutOutside G S e ∉ S := by
  simpa only [cutInside,cutOutside,dite_eq_left he] using he.choose_spec.choose_spec

theorem cut_unique [Nonempty V] (G : BondGraph V E) (S : Set V) {e : E} {a b : V}
    (he : G e = s(a,b)) (ha : a ∈ S) (hb : b ∉ S) :
    a = cutInside G S e ∧ b = cutOutside G S e := by
  have hc := cut_spec G S (e := e) ⟨a,b,he,ha,hb⟩
  have hh := Sym2.eq_iff.mp (he.symm.trans hc.1)
  rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨h₁,h₂⟩
  · exact (hc.2.2 (h₁ ▸ ha)).elim

theorem crossingReach_upper (G : BondGraph V E) (S : Set V) (x : V) (e : E) :
    IsUpperSet {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  rintro ω η h ⟨a,b,he,ha,hb,hconn⟩
  exact ⟨a,b,he,ha,hb,conn_mono G (Set.inter_subset_inter_left _ h) hconn⟩

theorem finiteWitness_crossingReach (G : BondGraph V E) (S : Set V) (x : V) (e : E) :
    FiniteWitness {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  rintro ω ⟨a,b,he,ha,hb,hconn⟩
  obtain ⟨t,ht,hc⟩ := finiteWitness_inter {η | Conn G η x a} (finiteWitness_conn G x a)
    (internalEdges G S) ω hconn
  exact ⟨t,ht,a,b,he,ha,hb,hc⟩

 
theorem conn_first_exit [Nonempty V] (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (U : Set E) {ω : Set E} {x y : V} (hx : x ∈ S)
    (hxy : Conn G (ω ∩ U) x y) :
    y ∈ S ∨ ∃ e ∈ incidentSupport G hloc S,
      ω ∈ DisjointOccurrence {η | crossingReach G S x (η ∩ internalEdges G S) e}
        (DisjointOccurrence {η | e ∈ η} {η | Conn G (η ∩ U) (cutOutside G S e) y}) := by
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G hxy
  rcases hl.first_outside (internalEdges G S) with hall |
      ⟨a,b,e,l₁,l₂,heq,h₁,he,h₂,hfirst,hnot⟩
  · exact Or.inl (conn_internal_endpoint G S hx (hl.conn fun e he => ⟨(ho e he).1,hall e he⟩))
  · subst l
    have hnod := List.nodup_append.mp hn
    have hen : e ∉ l₂ := (List.nodup_cons.mp hnod.2.1).1
    have ha : a ∈ S := conn_internal_endpoint G S hx
      (h₁.conn (ω := ω ∩ internalEdges G S) fun d hd =>
        ⟨(ho d (List.mem_append_left _ hd)).1,hfirst d hd⟩)
    have hb : b ∉ S := fun hb => hnot ((mem_internalEdges_of_ends G S e a b he).mpr ⟨ha,hb⟩)
    have hbe := (cut_unique G S he ha hb).2
    refine Or.inr ⟨e,(mem_incidentSupport G hloc S e).mpr ⟨a,ha,by simp [he]⟩,
      l₁.toFinset,(e::l₂).toFinset,?_,?_,?_,?_,?_⟩
    · intro d hd
      exact (ho d (List.mem_append_left _ (List.mem_toFinset.mp hd))).1
    · intro d hd
      exact (ho d (List.mem_append_right _ (List.mem_toFinset.mp hd))).1
    · apply Finset.disjoint_left.mpr
      intro d hd hd'
      exact hnod.2.2 d (List.mem_toFinset.mp hd) d (List.mem_toFinset.mp hd') rfl
    · exact ⟨a,b,he,ha,hb,h₁.conn (fun d hd => ⟨by simpa using hd,hfirst d hd⟩)⟩
    · refine ⟨{e},l₂.toFinset,by simp,by simp,by simpa using hen,by simp,?_⟩
      rw [← hbe]
      exact h₂.conn fun d hd => ⟨by simpa using hd,
        (ho d (List.mem_append_right _ (List.mem_cons_of_mem e hd))).2⟩

 
theorem boundaryExpectation_eq_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (p : unitInterval) :
    boundaryExpectation G S x (incidentSupport G hloc S) (p:ℝ) =
      ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  have hI : (internalSupport G S (incidentSupport G hloc S) : Set E) = internalEdges G S := by
    ext e
    simp only [Finset.mem_coe,internalSupport,Finset.mem_filter]
    exact ⟨And.right,fun he => ⟨internal_edge_mem_incident G hloc S he,he⟩⟩
  unfold boundaryExpectation crossingCount bernoulliPolynomial
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  change finiteEventPolynomial (internalSupport G S (incidentSupport G hloc S))
    {ω | crossingReach G S x ω e} (p:ℝ) = _
  rw [finiteEventPolynomial_restrict,hI]
  rfl

 
theorem domainTwoPoint_first_exit [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Finset V) (Λ : Set V) (p : unitInterval)
    (x y : V) (hx : x ∈ S) :
    domainTwoPoint G Λ p x y ≤ (if y ∈ S then (1:ℝ) else 0) +
      ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
          (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y := by
  by_cases hy : y ∈ S
  · have hnon : 0 ≤ ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
          (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y := by
      apply Finset.sum_nonneg
      intro e _
      exact mul_nonneg (mul_nonneg (measureReal_nonneg) p.2.1) measureReal_nonneg
    simpa only [ite_eq_left hy,domainTwoPoint] using (measureReal_le_one (μ := law p)
      (s := {ω | Conn G (ω ∩ internalEdges G Λ) x y})).trans (le_add_of_nonneg_right hnon)
  · simp only [ite_eq_right hy,zero_add]
    let A := fun e => {ω | crossingReach G S x (ω ∩ internalEdges G S) e}
    let B := fun e => {ω | Conn G (ω ∩ internalEdges G Λ) (cutOutside G S e) y}
    let F := incidentSupport G hloc S
    let C := fun e => DisjointOccurrence (A e) (DisjointOccurrence {ω | e ∈ ω} (B e))
    have hsub : {ω | Conn G (ω ∩ internalEdges G Λ) x y} ⊆ ⋃ e ∈ F, C e := by
      intro ω hω
      rcases conn_first_exit G hloc S (internalEdges G Λ) hx hω with h | ⟨e,he,h⟩
      · exact (hy h).elim
      · exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨he,h⟩⟩
    calc
      domainTwoPoint G Λ p x y ≤ (law p).real (⋃ e ∈ F, C e) := measureReal_mono (μ := law p) hsub (measure_ne_top _ _)
      _ ≤ ∑ e ∈ F, (law p).real (C e) := measureReal_biUnion_finset_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro e _
        have hB : IsUpperSet (B e) := fun _ _ h hc =>
          conn_mono G (Set.inter_subset_inter_left _ h) hc
        have hfB : FiniteWitness (B e) := finiteWitness_inter _
          (finiteWitness_conn G _ _) (internalEdges G Λ)
        have hb := bk p (A e) (DisjointOccurrence {ω | e ∈ ω} (B e))
          (crossingReach_upper G S x e) (disjointOccurrence_upper _ _)
          (finiteWitness_crossingReach G S x e) (finiteWitness_disjointOccurrence _ _)
        have hb' := bk p {ω | e ∈ ω} (B e) (fun _ _ h he => h he) hB (finiteWitness_edge e) hfB
        have heq : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
          simpa using finite_open_probability p {e}
        rw [heq] at hb'
        calc
          (law p).real (C e) ≤ (law p).real (A e) * (law p).real
              (DisjointOccurrence {ω | e ∈ ω} (B e)) := hb
          _ ≤ (law p).real (A e) * ((p:ℝ) * (law p).real (B e)) :=
            mul_le_mul_of_nonneg_left hb' measureReal_nonneg
          _ = _ := (mul_assoc _ _ _).symm

theorem conn_internal_eq_or_mem (G : BondGraph V E) (S : Set V) {ω : Set E} {x y : V}
    (h : Conn G (ω ∩ internalEdges G S) x y) : x = y ∨ x ∈ S ∧ y ∈ S := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    have he' := (mem_internalEdges_of_ends G S e a b heq).mp he.2
    right
    exact ⟨ih.elim (fun h => h.symm ▸ he'.1) And.left,he'.2⟩

theorem domainTwoPoint_zero_of_outside (G : BondGraph V E) (S : Set V) (p : unitInterval)
    {x y : V} (hx : x ∉ S) (hy : y ∈ S) : domainTwoPoint G S p x y = 0 := by
  have he : {ω | Conn G (ω ∩ internalEdges G S) x y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω h
    rcases conn_internal_eq_or_mem G S h with rfl | h
    · exact hx hy
    · exact hx h.1
  simp only [domainTwoPoint,he,measureReal_empty]

theorem domainRow_le_boundaryCost [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (S Λ : Finset V) (p : unitInterval) (x : V) (hx : x ∈ S)
    (H : ℝ) (hH : ∀ z, ∑ y ∈ Λ, domainTwoPoint G Λ p z y ≤ H) :
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤ S.card + boundaryCost G hloc S x (p:ℝ) * H := by
  have hind : (∑ y ∈ Λ, if y ∈ S then (1:ℝ) else 0) ≤ (S.card:ℝ) := by
    simp only [← Finset.sum_filter]
    simpa using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card
      (show Λ.filter (fun y => y ∈ S) ⊆ S from fun y hy => (Finset.mem_filter.mp hy).2))
  calc
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤
        ∑ y ∈ Λ, ((if y ∈ S then (1:ℝ) else 0) +
          ∑ e ∈ incidentSupport G hloc S,
            (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
              (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y) :=
      Finset.sum_le_sum fun y _ => domainTwoPoint_first_exit G hloc S Λ p x y hx
    _ = (∑ y ∈ Λ, if y ∈ S then (1:ℝ) else 0) +
        ∑ e ∈ incidentSupport G hloc S,
          (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
            (p:ℝ) * ∑ y ∈ Λ, domainTwoPoint G Λ p (cutOutside G S e) y := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [← Finset.mul_sum]
    _ ≤ S.card + ∑ e ∈ incidentSupport G hloc S,
          (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} * (p:ℝ) * H := by
      apply add_le_add hind
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (hH _) (mul_nonneg measureReal_nonneg p.2.1)
    _ = S.card + boundaryCost G hloc S x (p:ℝ) * H := by
      unfold boundaryCost
      rw [boundaryExpectation_eq_sum]
      simp only [← Finset.sum_mul]
      ring

theorem domainRow_uniform_bound [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (p : unitInterval) (L : ℕ) (a : ℝ) (ha : a < 1)
    (htest : ∀ x, ∃ S : Finset V, x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p:ℝ) ≤ a)
    (Λ : Finset V) (x : V) :
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤ (L:ℝ)/(1-a) := by
  by_cases hΛ : Λ.Nonempty
  · let row := fun z => ∑ y ∈ Λ, domainTwoPoint G Λ p z y
    obtain ⟨z,hz,hmax⟩ := Λ.exists_max_image row hΛ
    have hnon : 0 ≤ row z := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
    have hH : ∀ w, row w ≤ row z := by
      intro w
      by_cases hw : w ∈ Λ
      · exact hmax w hw
      · have he : row w = 0 := by
          apply Finset.sum_eq_zero
          intro y hy
          exact domainTwoPoint_zero_of_outside G Λ p hw hy
        rwa [he]
    obtain ⟨S,hS,hcard,hcost⟩ := htest z
    have h := domainRow_le_boundaryCost G hloc S Λ p z hS (row z) hH
    have hL : (S.card:ℝ) ≤ (L:ℝ) := Nat.cast_le.mpr hcard
    have hc := mul_le_mul_of_nonneg_right hcost hnon
    have hrow : row z ≤ (L:ℝ)/(1-a) := (le_div_iff₀ (sub_pos.mpr ha)).mpr (by nlinarith)
    exact (hH x).trans hrow
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hΛ,Finset.sum_empty]
    exact div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr ha).le

theorem internalEdges_mono (G : BondGraph V E) {S T : Set V} (h : S ⊆ T) :
    internalEdges G S ⊆ internalEdges G T := fun _ he x hx => h (he x hx)

theorem exists_internal_vertexExhaustion [Encodable V] (G : BondGraph V E) (e : E) :
    ∃ n, e ∈ internalEdges G (vertexExhaustion (V := V) n : Set V) := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G e)
  obtain ⟨n,hn⟩ := subset_vertexExhaustion ({a,b} : Finset V)
  refine ⟨n,?_⟩
  rw [mem_internalEdges_of_ends G _ e a b hab.symm]
  exact ⟨hn (by simp),hn (by simp)⟩

theorem conn_domain_exhaustion [Encodable V] (G : BondGraph V E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    ∃ n, Conn G (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y := by
  induction h with
  | refl => exact ⟨0,conn_refl _ _ _⟩
  | @tail a b hxa hab ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨e,he,heq⟩ := hab
    obtain ⟨m,hm⟩ := exists_internal_vertexExhaustion G e
    refine ⟨max n m,?_⟩
    have hnm := internalEdges_mono G (show (vertexExhaustion (V := V) n : Set V) ⊆
        (vertexExhaustion (V := V) (max n m) : Set V) from vertexExhaustion_mono (le_max_left n m))
    have hmm := internalEdges_mono G (show (vertexExhaustion (V := V) m : Set V) ⊆
        (vertexExhaustion (V := V) (max n m) : Set V) from vertexExhaustion_mono (le_max_right n m))
    exact (conn_mono G (Set.inter_subset_inter_right _ hnm) hn).tail ⟨e,⟨he,hmm hm⟩,heq⟩

theorem tendsto_domainTwoPoint [Encodable V] (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Tendsto (fun n => domainTwoPoint G (vertexExhaustion (V := V) n : Set V) p x y)
      atTop (𝓝 (twoPoint G p x y)) := by
  have hm : Monotone (fun n => {ω | Conn G
      (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y}) := by
    intro m n h ω hc
    exact conn_mono G (Set.inter_subset_inter_right _ (internalEdges_mono G
      (show (vertexExhaustion (V := V) m : Set V) ⊆ (vertexExhaustion (V := V) n : Set V) from
        vertexExhaustion_mono h))) hc
  have he : (⋃ n, {ω | Conn G (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y}) =
      {ω | Conn G ω x y} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,h⟩ => conn_mono G Set.inter_subset_left h,conn_domain_exhaustion G⟩
  have h := tendsto_measure_iUnion_atTop (μ := law p) hm
  rw [he] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

 
theorem subcritical_row_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x (F : Finset V), ∑ y ∈ F, twoPoint G p x y ≤ C := by
  let : Encodable V := Encodable.ofCountable V
  obtain ⟨L,a,_,ha,htest⟩ := exists_uniform_subcritical_testSets G hloc hqt p hp
  refine ⟨(L:ℝ)/(1-a),div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr ha).le,?_⟩
  intro x F
  apply le_of_tendsto (tendsto_finsetSum F (fun y _ => tendsto_domainTwoPoint G p x y))
  obtain ⟨N,hN⟩ := subset_vertexExhaustion F
  filter_upwards [eventually_ge_atTop N] with n hn
  have hFn : F ⊆ vertexExhaustion n := hN.trans (vertexExhaustion_mono hn)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hFn (fun _ _ _ => measureReal_nonneg)).trans
    (domainRow_uniform_bound G hloc p L a ha htest (vertexExhaustion n) x)


end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Marked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked decision trees, graph searches and pivotal geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedExploration

 
theorem centered_bernoulli_mgf_le (p : unitInterval) (lam : ℝ) :
    (1-(p:ℝ))*Real.exp (-lam*p) + p*Real.exp (lam*(1-p)) ≤ Real.exp (lam^2/8) := by
  let X : Bool → ℝ := fun b => if b then 1-(p:ℝ) else -(p:ℝ)
  have hb : ∀ᵐ b ∂bernoulliMeasure true false p, X b ∈ Set.Icc (-(p:ℝ)) (1-p) := by
    filter_upwards with b
    cases b <;> simp [X]
  have hc : ∫ b, X b ∂bernoulliMeasure true false p = 0 := by
    rw [integral_bernoulliMeasure]
    simp [X]
    ring
  have hg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := bernoulliMeasure true false p) (X := X)
    (Measurable.of_discrete.aemeasurable) hb hc
  have hh := hg.mgf_le lam
  simp only [mgf,integral_bernoulliMeasure] at hh
  norm_num [X,sub_neg_eq_add,sub_add_cancel,smul_eq_mul] at hh
  rw [show (1/4:ℝ)*lam^2/2 = lam^2/8 by ring] at hh
  simpa only [neg_mul,add_comm] using hh


namespace ProbeTree

lemma weight_nonneg (p h : unitInterval) (t : ProbeTree) (l : t.Leaf) :
    0 ≤ weight p h t l := by
  induction t with
  | done b => exact zero_le_one
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_nonneg (sub_nonneg.mpr p.2.2) (ih₀ l)
    | inr l => exact mul_nonneg p.2.1 (ih₁ l)
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_nonneg (sub_nonneg.mpr h.2.2) (ih₀ l)
    | inr l => exact mul_nonneg h.2.1 (ih₁ l)

lemma sum_weight (p h : ℝ) (t : ProbeTree) : ∑ l, weight p h t l = 1 := by
  induction t with
  | done b => change (∑ _ : Unit, (1:ℝ)) = 1; simp
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 1
    simp only [Fintype.sum_sum_type,weight,← Finset.mul_sum,ih₀,ih₁]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 1
    simp only [Fintype.sum_sum_type,weight,← Finset.mul_sum,ih₀,ih₁]
    ring

 
theorem score_mgf (p h : unitInterval) (lam : ℝ) (t : ProbeTree) :
    ∑ l, weight p h t l * Real.exp (lam*score p t l-lam^2*(queries t l : ℝ)/8) ≤ 1 := by
  induction t with
  | done b => change (∑ l : Unit, _) ≤ (1:ℝ); simp [weight,score,queries]
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) ≤ (1:ℝ)
    rw [Fintype.sum_sum_type]
    have h₀ (l : t₀.Leaf) :
        weight p h (.edge t₀ t₁) (.inl l) *
          Real.exp (lam*score p (.edge t₀ t₁) (.inl l)-lam^2*(queries (.edge t₀ t₁) (.inl l):ℝ)/8) =
        ((1-(p:ℝ))*Real.exp (-lam*p-lam^2/8)) *
          (weight p h t₀ l * Real.exp (lam*score p t₀ l-lam^2*(queries t₀ l:ℝ)/8)) := by
      simp only [weight,score,queries,Nat.cast_add,Nat.cast_one]
      rw [show lam*(score p t₀ l-p)-lam^2*((queries t₀ l:ℝ)+1)/8 =
        (-lam*p-lam^2/8)+(lam*score p t₀ l-lam^2*(queries t₀ l:ℝ)/8) by ring,Real.exp_add]
      ring
    have h₁ (l : t₁.Leaf) :
        weight p h (.edge t₀ t₁) (.inr l) *
          Real.exp (lam*score p (.edge t₀ t₁) (.inr l)-lam^2*(queries (.edge t₀ t₁) (.inr l):ℝ)/8) =
        ((p:ℝ)*Real.exp (lam*(1-p)-lam^2/8)) *
          (weight p h t₁ l * Real.exp (lam*score p t₁ l-lam^2*(queries t₁ l:ℝ)/8)) := by
      simp only [weight,score,queries,Nat.cast_add,Nat.cast_one]
      rw [show lam*(score p t₁ l+(1-p))-lam^2*((queries t₁ l:ℝ)+1)/8 =
        (lam*(1-p)-lam^2/8)+(lam*score p t₁ l-lam^2*(queries t₁ l:ℝ)/8) by ring,Real.exp_add]
      ring
    simp only [h₀,h₁,← Finset.mul_sum]
    have hc₀ : 0 ≤ (1-(p:ℝ))*Real.exp (-lam*p-lam^2/8) :=
      mul_nonneg (sub_nonneg.mpr p.2.2) (Real.exp_pos _).le
    have hc₁ : 0 ≤ (p:ℝ)*Real.exp (lam*(1-p)-lam^2/8) :=
      mul_nonneg p.2.1 (Real.exp_pos _).le
    calc
      _ ≤ (1-(p:ℝ))*Real.exp (-lam*p-lam^2/8) + p*Real.exp (lam*(1-p)-lam^2/8) := by
        simpa using add_le_add (mul_le_mul_of_nonneg_left ih₀ hc₀) (mul_le_mul_of_nonneg_left ih₁ hc₁)
      _ = ((1-(p:ℝ))*Real.exp (-lam*p)+p*Real.exp (lam*(1-p))) / Real.exp (lam^2/8) := by
        simp only [Real.exp_sub]; ring
      _ ≤ 1 := (div_le_one (Real.exp_pos _)).mpr (centered_bernoulli_mgf_le p lam)
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) ≤ (1:ℝ)
    simp only [Fintype.sum_sum_type,weight,score,queries,mul_assoc,← Finset.mul_sum]
    calc
      _ ≤ (1-(h:ℝ))*1+(h:ℝ)*1 :=
        add_le_add (mul_le_mul_of_nonneg_left ih₀ (sub_nonneg.mpr h.2.2))
          (mul_le_mul_of_nonneg_left ih₁ h.2.1)
      _ = 1 := by ring

lemma successWeight_nonneg (p h : unitInterval) (t : ProbeTree) (l : t.Leaf) :
    0 ≤ successWeight p h t l := by
  unfold successWeight
  split <;> simp_all [weight_nonneg]

lemma successWeight_le (p h : unitInterval) (t : ProbeTree) (l : t.Leaf) :
    successWeight p h t l ≤ weight p h t l := by
  unfold successWeight
  split
  · exact le_rfl
  · exact weight_nonneg p h t l

lemma successMass_nonneg (p h : unitInterval) (t : ProbeTree) : 0 ≤ successMass p h t :=
  Finset.sum_nonneg fun _ _ => successWeight_nonneg p h t _

lemma successMass_le_one (p h : unitInterval) (t : ProbeTree) : successMass p h t ≤ 1 := by
  rw [← sum_weight p h t]
  exact Finset.sum_le_sum fun _ _ => successWeight_le p h t _


theorem conditional_score_bound (p h : unitInterval) (t : ProbeTree)
    (hH : 0 < successMass p h t) (lam : ℝ) :
    lam*(successScore p h t / successMass p h t) ≤
      Real.log (1/successMass p h t) + lam^2/8*(successQueries p h t / successMass p h t) := by
  let H := successMass p h t
  let w : t.Leaf → ℝ := fun l => successWeight p h t l / H
  let X : t.Leaf → ℝ := fun l => lam*score p t l-lam^2*(queries t l : ℝ)/8
  have hw : ∀ l ∈ (Finset.univ : Finset t.Leaf), 0 ≤ w l :=
    fun l _ => div_nonneg (successWeight_nonneg p h t l) hH.le
  have hw1 : ∑ l, w l = 1 := by
    simp only [w,← Finset.sum_div]
    exact div_self hH.ne'
  have hJ := convexOn_exp.map_sum_le hw hw1 (fun _ _ => Set.mem_univ _ : ∀ l ∈
    (Finset.univ : Finset t.Leaf), X l ∈ Set.univ)
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ l, w l * X l = lam*(successScore p h t/H)-
      lam^2/8*(successQueries p h t/H) := by
    simp only [w,X,successScore,successQueries,Finset.sum_div,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have he : ∑ l, w l * Real.exp (X l) ≤ 1/H := by
    calc
      _ = (∑ l, successWeight p h t l * Real.exp (X l))/H := by
        simp only [Finset.sum_div,w]; apply Finset.sum_congr rfl; intro l _; ring
      _ ≤ (∑ l, weight p h t l * Real.exp (X l))/H := by
        apply div_le_div_of_nonneg_right _ hH.le
        exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (successWeight_le p h t l)
          (Real.exp_pos _).le
      _ ≤ 1/H := div_le_div_of_nonneg_right (score_mgf p h lam t) hH.le
  rw [hsum] at hJ
  have hb := (Real.le_log_iff_exp_le (one_div_pos.mpr hH)).mpr (hJ.trans he)
  linarith

lemma hasDerivAt_weight (p h : ℝ) (t : ProbeTree) (l : t.Leaf) :
    HasDerivAt (fun q => weight q h t l) (dweight p h t l) p := by
  induction t with
  | done b => exact hasDerivAt_const p 1
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => convert ((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul (ih₀ l) using 1 <;> try rfl
               simp [dweight]
    | inr l => convert (hasDerivAt_id p).mul (ih₁ l) using 1 <;> try rfl
               simp [dweight]
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact (ih₀ l).const_mul (1-h)
    | inr l => exact (ih₁ l).const_mul h

lemma score_eq_derivative (p h : ℝ) (t : ProbeTree) (l : t.Leaf) :
    p*(1-p)*dweight p h t l = weight p h t l * score p t l := by
  induction t with
  | done b => simp [dweight,weight,score]
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => dsimp [dweight,weight,score]; linear_combination (1-p)*(ih₀ l)
    | inr l => dsimp [dweight,weight,score]; linear_combination p*(ih₁ l)
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => dsimp [dweight,weight,score]; linear_combination (1-h)*(ih₀ l)
    | inr l => dsimp [dweight,weight,score]; linear_combination h*(ih₁ l)

 
theorem successScore_eq_deriv (p h : ℝ) (t : ProbeTree) :
    successScore p h t = p*(1-p)*deriv (fun q => successMass q h t) p := by
  have hd : HasDerivAt (fun q => successMass q h t)
      (∑ l, if outcome t l then dweight p h t l else 0) p := by
    have hh (l : t.Leaf) (_ : l ∈ (Finset.univ : Finset t.Leaf)) :
        HasDerivAt (fun q => successWeight q h t l) (if outcome t l then dweight p h t l else 0) p := by
      by_cases hl : outcome t l
      · simpa [successWeight,hl] using hasDerivAt_weight p h t l
      · simpa [successWeight,hl] using hasDerivAt_const p (0:ℝ)
    simpa only [successMass,Finset.sum_apply] using HasDerivAt.fun_sum hh
  rw [hd.deriv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : outcome t l
  · simpa [successWeight,hl] using (score_eq_derivative p h t l).symm
  · simp [successWeight,hl]


lemma successMass_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMass p h (.edge t₀ t₁) = (1-p)*successMass p h t₀+p*successMass p h t₁ := by
  simp only [successMass,Fintype.sum_sum_type,successWeight,outcome,weight,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split <;> simp

lemma successMass_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMass p h (.mark t₀ t₁) = (1-h)*successMass p h t₀+h*successMass p h t₁ := by
  simp only [successMass,Fintype.sum_sum_type,successWeight,outcome,weight,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split <;> simp

lemma successMarks_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMarks p h (.edge t₀ t₁) = (1-p)*successMarks p h t₀+p*successMarks p h t₁ := by
  simp only [successMarks,Fintype.sum_sum_type,successWeight,outcome,weight,marks,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split <;> simp [mul_assoc]

lemma successMarks_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMarks p h (.mark t₀ t₁) =
      (1-h)*(successMarks p h t₀+successMass p h t₀) +
        h*(successMarks p h t₁+successMass p h t₁) := by
  simp only [successMarks,successMass,Fintype.sum_sum_type,successWeight,outcome,weight,marks,
    Nat.cast_add,Nat.cast_one,← Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split_ifs <;> ring


theorem marks_times_parameter_le (p h : unitInterval) {t : ProbeTree} (ht : IsMarkSearch t) :
    (h:ℝ)*successMarks p h t ≤ successMass p h t := by
  induction ht with
  | fail => simp
  | @edge t₀ t₁ _ _ ih₀ ih₁ =>
    rw [successMarks_edge,successMass_edge]
    nlinarith [mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr ih₀),
      mul_nonneg p.2.1 (sub_nonneg.mpr ih₁)]
  | @mark t₀ _ ih =>
    rw [successMarks_mark,successMass_mark]
    simp only [successMarks_done,successMass_done,ite_true,zero_add,mul_one]
    have hn := mul_nonneg (mul_nonneg h.2.1 (sub_nonneg.mpr h.2.2))
      (sub_nonneg.mpr (successMass_le_one p h t₀))
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2.2) (sub_nonneg.mpr ih)]

theorem successQueries_times_parameter_le (p h : unitInterval) {t : ProbeTree}
    (ht : IsMarkSearch t) (d : ℕ) (hcost : ∀ l, queries t l ≤ d*marks t l) :
    (h:ℝ)*successQueries p h t ≤ d*successMass p h t := by
  have hs : successQueries p h t ≤ d*successMarks p h t := by
    simp only [successQueries,successMarks,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    calc
      _ ≤ successWeight p h t l * ((d:ℝ)*marks t l) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcost l) (successWeight_nonneg p h t l)
      _ = _ := by ring
  calc
    _ ≤ (h:ℝ)*(d*successMarks p h t) := mul_le_mul_of_nonneg_left hs h.2.1
    _ = d*((h:ℝ)*successMarks p h t) := by ring
    _ ≤ d*successMass p h t := mul_le_mul_of_nonneg_left (marks_times_parameter_le p h ht)
      (Nat.cast_nonneg _)

 
theorem marked_score_bound (p h : unitInterval) (hh : 0 < (h:ℝ))
    {t : ProbeTree} (ht : IsMarkSearch t) (d : ℕ)
    (hcost : ∀ l, queries t l ≤ d*marks t l) (hroot : (h:ℝ) ≤ successMass p h t)
    (lam : ℝ) :
    lam*(successScore p h t / successMass p h t) ≤
      Real.log (1/(h:ℝ)) + lam^2*(d:ℝ)/(8*h) := by
  have hH := hh.trans_le hroot
  have hlog : Real.log (1/successMass p h t) ≤ Real.log (1/(h:ℝ)) :=
    Real.log_le_log (one_div_pos.mpr hH) (one_div_le_one_div_of_le hh hroot)
  have hQ : successQueries p h t / successMass p h t ≤ (d:ℝ)/h := by
    apply (div_le_div_iff₀ hH hh).mpr
    simpa [mul_comm] using successQueries_times_parameter_le p h ht d hcost
  calc
    _ ≤ Real.log (1/successMass p h t)+lam^2/8*(successQueries p h t/successMass p h t) :=
      conditional_score_bound p h t hH lam
    _ ≤ Real.log (1/(h:ℝ))+lam^2/8*((d:ℝ)/h) :=
      add_le_add hlog (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = _ := by ring

end ProbeTree
end MarkedExploration

section LabelledExploration
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace LabelledTree

theorem eval_congr (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {ω ω' : Finset E} {m m' : Finset V}
    (hω : ∀ e ∈ Q, e ∈ ω ↔ e ∈ ω') (hm : ∀ v ∈ F, v ∈ m ↔ v ∈ m') :
    t.eval ω m = t.eval ω' m' := by
  induction t generalizing Q F with
  | done b => rfl
  | edge e t₀ t₁ ih₀ ih₁ =>
    obtain ⟨he,h₀,h₁⟩ := ht
    simp only [eval,hω e he]
    split
    · exact ih₁ h₁ (fun a ha => hω a (Finset.mem_of_mem_erase ha)) hm
    · exact ih₀ h₀ (fun a ha => hω a (Finset.mem_of_mem_erase ha)) hm
  | mark v t₀ t₁ ih₀ ih₁ =>
    obtain ⟨hv,h₀,h₁⟩ := ht
    simp only [eval,hm v hv]
    split
    · exact ih₁ h₁ hω (fun a ha => hm a (Finset.mem_of_mem_erase ha))
    · exact ih₀ h₀ hω (fun a ha => hm a (Finset.mem_of_mem_erase ha))

lemma eval_insert_edge (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {e : E} (he : e ∉ Q) (ω : Finset E) (m : Finset V) :
    t.eval (insert e ω) m = t.eval ω m := by
  apply eval_congr t ht
  · intro a ha
    simp [show a ≠ e from fun hh => he (hh ▸ ha)]
  · simp

lemma eval_insert_mark (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {v : V} (hv : v ∉ F) (ω : Finset E) (m : Finset V) :
    t.eval ω (insert v m) = t.eval ω m := by
  apply eval_congr t ht
  · simp
  · intro a ha
    simp [show a ≠ v from fun hh => hv (hh ▸ ha)]

end LabelledTree

theorem bernoulliPolynomial_affine (s : Finset E) (f g : Finset E → ℝ) (a b p : ℝ) :
    bernoulliPolynomial s (fun t => a*f t+b*g t) p =
      a*bernoulliPolynomial s f p+b*bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> ring

namespace LabelledTree

 
theorem expectation_eq (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) (p h : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial F
      (fun m => if t.eval ω m then 1 else 0) h) p =
      ProbeTree.successMass p h t.forget := by
  induction t generalizing Q F with
  | done b =>
    cases b <;> simp [eval,forget,ProbeTree.successMass_done,bernoulliPolynomial_const]
  | edge e t₀ t₁ ih₀ ih₁ =>
    obtain ⟨he,h₀,h₁⟩ := ht
    conv_lhs => rw [← Finset.insert_erase he]
    rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
    have hc : bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if (edge e t₀ t₁).eval ω m then 1 else 0) h) p =
        bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if t₀.eval ω m then 1 else 0) h) p := by
      apply bernoulliPolynomial_congr
      intro ω hω
      have heω : e ∉ ω := fun hh => Finset.notMem_erase e Q (hω hh)
      simp only [eval,heω,ite_false]
    have ho : bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if (edge e t₀ t₁).eval (insert e ω) m then 1 else 0) h) p =
        bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if t₁.eval ω m then 1 else 0) h) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      simp only [eval,Finset.mem_insert_self,ite_true]
      apply bernoulliPolynomial_congr
      intro m _
      rw [eval_insert_edge t₁ h₁ (Finset.notMem_erase e Q)]
    rw [hc,ho,ih₀ h₀,ih₁ h₁,forget,ProbeTree.successMass_edge]
  | mark v t₀ t₁ ih₀ ih₁ =>
    obtain ⟨hv,h₀,h₁⟩ := ht
    have hh : ∀ ω, bernoulliPolynomial F
        (fun m => if (mark v t₀ t₁).eval ω m then 1 else 0) h =
      (1-h)*bernoulliPolynomial (F.erase v) (fun m => if t₀.eval ω m then 1 else 0) h +
        h*bernoulliPolynomial (F.erase v) (fun m => if t₁.eval ω m then 1 else 0) h := by
      intro ω
      conv_lhs => rw [← Finset.insert_erase hv]
      rw [bernoulliPolynomial_insert _ v (Finset.notMem_erase v F)]
      congr 1
      · congr 1
        apply bernoulliPolynomial_congr
        intro m hm
        have hvm : v ∉ m := fun hh => Finset.notMem_erase v F (hm hh)
        simp only [eval,hvm,ite_false]
      · congr 1
        apply bernoulliPolynomial_congr
        intro m _
        simp only [eval,Finset.mem_insert_self,ite_true]
        rw [eval_insert_mark t₁ h₁ (Finset.notMem_erase v F)]
    simp_rw [hh]
    rw [bernoulliPolynomial_affine,ih₀ h₀,ih₁ h₁,forget,ProbeTree.successMass_mark]

end LabelledTree
end LabelledExploration

section GraphMarkedSearch
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem searchCrossing_spec (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : SearchCrossing G Q R) :
    (searchCrossing G Q R h).1 ∈ Q ∧ (searchCrossing G Q R h).2.1 ∈ R ∧
      (searchCrossing G Q R h).2.2 ∉ R ∧
      G (searchCrossing G Q R h).1 = s((searchCrossing G Q R h).2.1,(searchCrossing G Q R h).2.2) :=
  Classical.choose_spec h


lemma searchAvailable_erase (G : BondGraph V E) {Q : Finset E} {R F : Finset V}
    (h : SearchAvailable G Q R F) (e : E) : SearchAvailable G (Q.erase e) R F :=
  fun _ ha _ hv => h _ (Finset.mem_of_mem_erase ha) _ hv

lemma searchAvailable_discover (G : BondGraph V E) {Q : Finset E} {R F : Finset V}
    (h : SearchAvailable G Q R F) (e : E) (v : V) :
    SearchAvailable G (Q.erase e) (insert v R) (F.erase v) := by
  intro a ha b hb
  rcases h a (Finset.mem_of_mem_erase ha) b hb with hb | hb
  · exact Or.inl (Finset.mem_insert_of_mem hb)
  · by_cases hbe : b = v
    · exact Or.inl (by simp [hbe])
    · exact Or.inr (Finset.mem_erase.mpr ⟨hbe,hb⟩)

theorem clusterSearch_valid (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R F : Finset V)
    (ha : SearchAvailable G Q R F) : LabelledTree.Valid Q F (clusterSearch G n Q R) := by
  induction n generalizing Q R F with
  | zero => trivial
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      refine ⟨he,ih _ _ _ (searchAvailable_erase G ha _),?_,?_,trivial⟩
      · exact (ha _ he _ (by rw [hends]; simp)).resolve_left hw
      · exact ih _ _ _ (searchAvailable_discover G ha _ _)
    · trivial

theorem clusterSearch_markSearch (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V) :
    ProbeTree.IsMarkSearch (clusterSearch G n Q R).forget := by
  induction n generalizing Q R with
  | zero => exact .fail
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs
    · exact .edge (ih _ _) (.mark (ih _ _))
    · exact .fail


theorem seedMarked_insert_edge (G : BondGraph V E) (ω : Set E) (R m : Finset V)
    (e : E) (a b : V) (ha : a ∈ R) (he : G e = s(a,b)) :
    SeedMarked G (insert e ω) R m ↔ SeedMarked G ω (insert b R) m := by
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | ⟨_,h⟩ | ⟨_,h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hx,y,hy,h⟩
    · exact ⟨b,by simp,y,hy,h⟩
    · exact ⟨a,Finset.mem_insert_of_mem ha,y,hy,h⟩
  · rintro ⟨x,hx,y,hy,hxy⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · refine ⟨a,ha,y,hy,?_⟩
      exact (Relation.ReflTransGen.single ⟨e,Set.mem_insert e ω,he⟩).trans
        (conn_mono G (Set.subset_insert e ω) hxy)
    · exact ⟨x,hx,y,hy,conn_mono G (Set.subset_insert e ω) hxy⟩

theorem seedMarked_false_of_no_crossing (G : BondGraph V E) (Q : Finset E) (R m : Finset V)
    (hc : ¬ SearchCrossing G Q R) (hm : Disjoint R m) (ω : Finset E) (hω : ω ⊆ Q) :
    ¬ SeedMarked G (ω : Set E) R m := by
  rintro ⟨a,ha,b,hb,hab⟩
  have hclosed : ∀ x ∈ R, ∀ y, Conn G (ω : Set E) x y → y ∈ R := by
    intro x hx y hxy
    induction hxy with
    | refl => exact hx
    | @tail v w hv hw ih =>
      by_contra hn
      obtain ⟨e,he,hevw⟩ := hw
      exact hc ⟨(e,v,w),hω he,ih,hn,hevw⟩
  exact Finset.disjoint_left.mp hm (hclosed a ha b hab) hb

 
theorem clusterSearch_correct (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R F m : Finset V)
    (hn : Q.card ≤ n) (ha : SearchAvailable G Q R F) (hm : Disjoint R m)
    (ω : Finset E) (hω : ω ⊆ Q) :
    (clusterSearch G n Q R).eval ω m = true ↔ SeedMarked G (ω : Set E) R m := by
  induction n generalizing Q R F ω with
  | zero =>
    have hQ : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    have hωe : ω = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by simp_all)
    simp only [clusterSearch,LabelledTree.eval,Bool.false_eq_true,false_iff]
    exact seedMarked_false_of_no_crossing G Q R m (by simp [SearchCrossing,hQ]) hm ω hω
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      have hcard : (Q.erase (searchCrossing G Q R hc).1).card ≤ n := by
        rw [Finset.card_erase_of_mem he]; omega
      simp only [LabelledTree.eval]
      by_cases heω : (searchCrossing G Q R hc).1 ∈ ω
      · simp only [heω,ite_true]
        rw [← Finset.insert_erase heω,Finset.coe_insert,
          seedMarked_insert_edge G _ R m _ _ _ hv hends]
        by_cases hwm : (searchCrossing G Q R hc).2.2 ∈ m
        · simp only [hwm,ite_true,true_iff]
          exact ⟨_,by simp,_,hwm,conn_refl G _ _⟩
        · simp only [hwm,ite_false]
          rw [LabelledTree.eval_insert_edge _
            (clusterSearch_valid G n _ _ (F.erase (searchCrossing G Q R hc).2.2)
              (searchAvailable_discover G ha _ _)) (Finset.notMem_erase _ _)]
          exact ih _ _ _ hcard (searchAvailable_discover G ha _ _)
            (Finset.disjoint_insert_left.mpr ⟨hwm,hm⟩) (ω.erase (searchCrossing G Q R hc).1)
            (Finset.erase_subset_erase _ hω)
      · simp only [heω,ite_false]
        exact ih _ _ _ hcard (searchAvailable_erase G ha _ ) hm ω
          (fun e he => Finset.mem_erase.mpr ⟨fun heq => heω (heq ▸ he),hω he⟩)
    · simp only [false_iff]
      exact seedMarked_false_of_no_crossing G Q R m hc hm ω hω

end GraphMarkedSearch

section GraphSearchCost
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace ProbeTree

lemma budget_done (b : Bool) (K d : ℕ) : Budget (.done b) K d := by
  intro l
  simp [queries,marks]

lemma budget_mono {t : ProbeTree} {K L d : ℕ} (h : Budget t K d) (hKL : K ≤ L) :
    Budget t L d := fun l => (h l).trans (Nat.add_le_add_right hKL _)

lemma budget_edge {t₀ t₁ : ProbeTree} {K d : ℕ} (h₀ : Budget t₀ K d) (h₁ : Budget t₁ K d) :
    Budget (.edge t₀ t₁) (K+1) d := by
  intro l
  cases l with
  | inl l => simpa [queries,marks,Nat.add_right_comm] using Nat.add_le_add_right (h₀ l) 1
  | inr l => simpa [queries,marks,Nat.add_right_comm] using Nat.add_le_add_right (h₁ l) 1

lemma budget_mark {t₀ t₁ : ProbeTree} {K d : ℕ}
    (h₀ : Budget t₀ (K+d) d) (h₁ : Budget t₁ (K+d) d) :
    Budget (.mark t₀ t₁) K d := by
  intro l
  cases l with
  | inl l => simpa [queries,marks,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₀ l
  | inr l => simpa [queries,marks,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₁ l

end ProbeTree


lemma queryPotential_erase (G : BondGraph V E) (Q : Finset E) (R : Finset V) (e : E) :
    queryPotential G (Q.erase e) R = (queryPotential G Q R).erase e := by
  ext a
  simp [queryPotential,and_assoc]

lemma queryPotential_insert (G : BondGraph V E) (Q : Finset E) (R : Finset V) (v : V) :
    queryPotential G Q (insert v R) = queryPotential G Q R ∪ Q.filter (fun e => v ∈ G e) := by
  ext a
  simp [queryPotential,and_or_left,or_comm]

lemma filtered_degree_erase (G : BondGraph V E) (Q : Finset E) (d : ℕ)
    (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) (a : E) :
    ∀ v, ((Q.erase a).filter (fun e => v ∈ G e)).card ≤ d := by
  intro v
  apply (Finset.card_le_card ?_).trans (hd v)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_filter.mp he).1,
    (Finset.mem_filter.mp he).2⟩

lemma queryPotential_discover_card (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (e : E) (v : V) (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    (queryPotential G (Q.erase e) (insert v R)).card ≤
      ((queryPotential G Q R).erase e).card+d := by
  rw [queryPotential_insert,queryPotential_erase]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (filtered_degree_erase G Q d hd e v) _)

 
theorem clusterSearch_budget (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V)
    (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    ProbeTree.Budget (clusterSearch G n Q R).forget (queryPotential G Q R).card d := by
  induction n generalizing Q R with
  | zero => exact ProbeTree.budget_done _ _ _
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      have hpot : (searchCrossing G Q R hc).1 ∈ queryPotential G Q R := by
        exact Finset.mem_filter.mpr ⟨he,_,hv,by rw [hends]; simp⟩
      have hpos : 0 < (queryPotential G Q R).card := Finset.card_pos.mpr ⟨_,hpot⟩
      have hclosed := ih (Q.erase (searchCrossing G Q R hc).1) R
        (filtered_degree_erase G Q d hd _)
      have hopen := ih (Q.erase (searchCrossing G Q R hc).1)
        (insert (searchCrossing G Q R hc).2.2 R) (filtered_degree_erase G Q d hd _)
      rw [queryPotential_erase,Finset.card_erase_of_mem hpot] at hclosed
      have hnew := queryPotential_discover_card G Q R (searchCrossing G Q R hc).1
        (searchCrossing G Q R hc).2.2 d hd
      rw [Finset.card_erase_of_mem hpot] at hnew
      have hh := ProbeTree.budget_edge hclosed
        (ProbeTree.budget_mark (ProbeTree.budget_mono hopen hnew) (ProbeTree.budget_done true _ _))
      have hcadd : (queryPotential G Q R).card-1+1 = (queryPotential G Q R).card := by omega
      simpa only [LabelledTree.forget,hcadd] using hh
    · exact ProbeTree.budget_done _ _ _

lemma mem_searchVertices (G : BondGraph V E) {Q : Finset E} {e : E} (he : e ∈ Q)
    {v : V} (hv : v ∈ G e) : v ∈ searchVertices G Q :=
  Finset.mem_biUnion.mpr ⟨e,he,Sym2.mem_toFinset.mpr hv⟩

lemma markedClusterTree_available (G : BondGraph V E) (Q : Finset E) (x : V) :
    SearchAvailable G Q {x} ((insert x (searchVertices G Q)).erase x) := by
  intro e he v hv
  by_cases hx : v = x
  · exact Or.inl (by simpa using hx)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hx,Finset.mem_insert_of_mem (mem_searchVertices G he hv)⟩)

theorem markedClusterTree_valid (G : BondGraph V E) (Q : Finset E) (x : V) :
    LabelledTree.Valid Q (insert x (searchVertices G Q)) (markedClusterTree G Q x) :=
  ⟨by simp,clusterSearch_valid G _ _ _ _ (markedClusterTree_available G Q x),trivial⟩

theorem markedClusterTree_budget (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    ProbeTree.Budget (markedClusterTree G Q x).forget 0 d := by
  have hh := clusterSearch_budget G Q.card Q {x} d hd
  have hcost : (queryPotential G Q {x}).card ≤ 0+d := by simpa [queryPotential] using hd x
  exact ProbeTree.budget_mark (ProbeTree.budget_mono hh hcost) (ProbeTree.budget_done true _ _)

theorem markedClusterTree_correct (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (hω : ω ⊆ Q) (m : Finset V) :
    (markedClusterTree G Q x).eval ω m = true ↔ ∃ y ∈ m, Conn G (ω : Set E) x y := by
  simp only [markedClusterTree,LabelledTree.eval]
  by_cases hxm : x ∈ m
  · simp only [hxm,ite_true,true_iff]
    exact ⟨x,hxm,conn_refl G _ x⟩
  · simp only [hxm,ite_false]
    rw [clusterSearch_correct G Q.card Q {x} ((insert x (searchVertices G Q)).erase x) m
      le_rfl (markedClusterTree_available G Q x) (by simpa) ω hω]
    simp only [SeedMarked,Finset.mem_singleton,exists_eq_left]

end GraphSearchCost

section MarkedFirstMoment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem quadratic_test_bound {z L B : ℝ} (hL : 0 ≤ L) (hB : 0 < B)
    (h : ∀ lam : ℝ, lam*z ≤ L+lam^2*B) : z ≤ Real.sqrt (4*B*L) := by
  have hh := h (z/(2*B))
  have hid : z/(2*B)*z-(z/(2*B))^2*B = z^2/(4*B) := by
    field_simp
    ring
  have hs : z^2/(4*B) ≤ L := by rw [← hid]; linarith
  have hs' := (div_le_iff₀ (by positivity : 0 < 4*B)).mp hs
  have hn : 0 ≤ 4*B*L := by positivity
  have hsq := Real.sq_sqrt hn
  have hpos := Real.sqrt_nonneg (4*B*L)
  nlinarith


theorem markedConnectionPolynomial_eq_tree (G : BondGraph V E) (Q : Finset E)
    (x : V) (h p : ℝ) :
    markedConnectionPolynomial G Q x h p =
      ProbeTree.successMass p h (markedClusterTree G Q x).forget := by
  rw [← LabelledTree.expectation_eq _ (markedClusterTree_valid G Q x) p h]
  apply bernoulliPolynomial_congr
  intro ω hω
  apply bernoulliPolynomial_congr
  intro m _
  simp only [markedClusterTree_correct G Q x ω hω m]

theorem markedConnectionPolynomial_ge_mark (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) : (h:ℝ) ≤ markedConnectionPolynomial G Q x h p := by
  rw [markedConnectionPolynomial_eq_tree,markedClusterTree,LabelledTree.forget,
    ProbeTree.successMass_mark]
  simp only [LabelledTree.forget,ProbeTree.successMass_done,ite_true,mul_one]
  exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr h.2.2)
    (ProbeTree.successMass_nonneg p h _))

 
theorem markedConnection_derivative_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ))
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    (p:ℝ)*deriv (markedConnectionPolynomial G Q x h) p ≤
      (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)*
        markedConnectionPolynomial G Q x h p := by
  let t := (markedClusterTree G Q x).forget
  have ht : ProbeTree.IsMarkSearch t := .mark (clusterSearch_markSearch G _ _ _)
  have hcost : ∀ l, ProbeTree.queries t l ≤ d*ProbeTree.marks t l := by
    simpa only [ProbeTree.Budget,zero_add] using markedClusterTree_budget G Q x d hdeg
  have hroot : (h:ℝ) ≤ ProbeTree.successMass p h t := by
    simpa only [markedConnectionPolynomial_eq_tree] using markedConnectionPolynomial_ge_mark G Q x p h
  have hB : 0 < (d:ℝ)/(8*h) := div_pos (by exact_mod_cast hd) (by positivity)
  have hL : 0 ≤ Real.log (1/(h:ℝ)) := Real.log_nonneg ((one_le_div hh).mpr h.2.2)
  have htest (lam : ℝ) : lam*(ProbeTree.successScore p h t/ProbeTree.successMass p h t) ≤
      Real.log (1/(h:ℝ))+lam^2*((d:ℝ)/(8*h)) := by
    simpa only [mul_div_assoc] using ProbeTree.marked_score_bound p h hh ht d hcost hroot lam
  have hz := quadratic_test_bound hL hB htest
  have hsqrt : Real.sqrt (4*((d:ℝ)/(8*h))*Real.log (1/(h:ℝ))) =
      Real.sqrt ((d:ℝ)/2)*Real.sqrt (Real.log (1/(h:ℝ))/h) := by
    rw [show 4*((d:ℝ)/(8*h))*Real.log (1/(h:ℝ)) =
      ((d:ℝ)/2)*(Real.log (1/(h:ℝ))/h) by ring,Real.sqrt_mul (by positivity)]
  rw [hsqrt] at hz
  have hH : 0 < ProbeTree.successMass p h t := hh.trans_le hroot
  have hscore := (div_le_iff₀ hH).mp hz
  rw [ProbeTree.successScore_eq_deriv] at hscore
  have heq : markedConnectionPolynomial G Q x h = fun q => ProbeTree.successMass q h t :=
    funext fun q => markedConnectionPolynomial_eq_tree G Q x h q
  rw [heq]
  have hq : 0 < 1-(p:ℝ) := sub_pos.mpr hp
  calc
    _ = ((p:ℝ)*(1-p)*deriv (fun q => ProbeTree.successMass q h t) p)/(1-p) := by
      field_simp
    _ ≤ (Real.sqrt ((d:ℝ)/2)*Real.sqrt (Real.log (1/(h:ℝ))/h)*
        ProbeTree.successMass p h t)/(1-p) := div_le_div_of_nonneg_right hscore hq.le
    _ = _ := by ring

end MarkedFirstMoment

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive marked moments and exponential estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedRecursion
attribute [local instance] Classical.propDecidable Classical.decEq


theorem conn_mem_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    {ω : Set E} (hω : ω ⊆ Q) {y : V} (hxy : Conn G ω x y) :
    y ∈ insert x (searchVertices G Q) := by
  induction hxy with
  | refl => exact Finset.mem_insert_self _ _
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact Finset.mem_insert_of_mem (mem_searchVertices G (hω he) (by simp [heq]))

end MarkedRecursion

section CutFactor
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

omit [Nonempty V] in
 
theorem bernoulliPolynomial_empty_indicator (F : Finset V) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m = ∅ then (1:ℝ) else 0) h = (1-h)^F.card := by
  unfold bernoulliPolynomial
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro m hm hne
    simp [hne]
  · simp


end CutFactor

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

omit [Nonempty V] in
theorem finiteRootComponent_subset (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (ω : Finset E) (hω : ω ⊆ Q) (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteRootComponent G ω x ⊆ F := by
  intro y hy
  have hxy : Conn G (ω : Set E) x y := by
    change y ∈ (finiteRootComponent G ω x : Set V) at hy
    rwa [coe_finiteRootComponent] at hy
  exact hF (conn_mem_searchSupport G Q x (by exact_mod_cast hω) hxy)

end PointwiseRecursion

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Goodness
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

theorem measurableSet_finite_restriction (Q : Finset E) (A : Set (Set E)) :
    MeasurableSet {ω : Set E | ω ∩ (Q : Set E) ∈ A} := by
  have hm : MeasurableSet {η : Set (Q : Set E) | (Subtype.val '' η : Set E) ∈ A} := .of_discrete
  convert hm.preimage (measurable_set_restrict (Q : Set E)) using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  have he : (Subtype.val '' (Subtype.val ⁻¹' ω : Set (Q : Set E)) : Set E) = ω ∩ (Q : Set E) := by
    ext e
    simp [and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,he]

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
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_TrajectoryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem RootTransport.real (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (m : V → V → ℝ)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hc : ∀ y, Summable (fun x => m x y)) :
    (∑ i, weight i * ∑' y, m (root i) y) =
      (∑ i, weight i * ∑' x, m x (root i)) := by
  have ht := htr (fun x y => (m x y:ℂ))
    (fun a ha x y => congrArg Complex.ofReal (hi a ha x y))
    (fun x => Complex.summable_ofReal.mpr (hr x))
    (fun y => Complex.summable_ofReal.mpr (hc y))
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_tsum] using ht

 

theorem transported_column_le (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hcol : ∀ y, Summable (fun x => m x y))
    (B : ℝ) (hB : ∀ x, ∑' y, m x y ≤ B) (y : V) :
    (∑' x, m x y) ≤ c*B := by
  have ht := htr.real root weight Γ m hi hr hcol
  have hb : (∑ i, weight i * ∑' x, m x (root i)) ≤ B := by
    rw [← ht]
    calc
      _ ≤ ∑ i, weight i * B := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hB _) (hw i)
      _ = B := by rw [← Finset.sum_mul,hw1,one_mul]
  obtain ⟨i,a,ha,hay⟩ := hcov y
  have he : (∑' x, m x y) = ∑' x, m x (root i) := by
    rw [← hay,← a.tsum_eq (fun x => m x (a (root i)))]
    exact tsum_congr (fun x => hi a ha x (root i))
  have hn : 0 ≤ ∑' x, m x (root i) := tsum_nonneg (fun x => hm x _)
  have hs : weight i * ∑' x, m x (root i) ≤ ∑ j, weight j * ∑' x, m x (root j) :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (tsum_nonneg (fun x => hm x (root j))))
      (Finset.mem_univ i)
  rw [he]
  calc
    _ ≤ (c*weight i) * ∑' x, m x (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) hn
    _ = c * (weight i * ∑' x, m x (root i)) := by ring
    _ ≤ c * (∑ j, weight j * ∑' x, m x (root j)) := mul_le_mul_of_nonneg_left hs hc
    _ ≤ c*B := mul_le_mul_of_nonneg_left hb hc



end TrajectoryTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NonnegativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem transportCut_mono (G : BondGraph V E) {n m : ℕ} (h : n ≤ m)
    {x y : V} (hxy : transportCut G n x y) : transportCut G m x y :=
  ⟨reachBall_mono G x h hxy.1, reachBall_mono G y h hxy.2⟩

theorem transportCut_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (ha : IsAut G a b) (n : ℕ) (x y : V) :
    transportCut G n (a x) (a y) ↔ transportCut G n x y := by
  simp only [transportCut,mem_reachBall_aut_iff G ha]

theorem exists_transportCut (G : BondGraph V E) (hconn : Connected G)
    (y : V) (Z : Finset V) : ∃ n, ∀ x ∈ Z, transportCut G n x y := by
  induction Z using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x Z _ ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨r,hr⟩ := exists_mem_reachBall (hconn x y)
    obtain ⟨s,hs⟩ := exists_mem_reachBall (hconn y x)
    refine ⟨max n (max r s), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨reachBall_mono G z (le_trans (le_max_left r s) (le_max_right n _)) hr,
        reachBall_mono G y (le_trans (le_max_right r s) (le_max_right n _)) hs⟩
    · exact transportCut_mono G (le_max_left n _) (hn z hz)

 

theorem transported_column_of_row_bound (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (m : V → V → ℝ) (hm : ∀ x y, 0 ≤ m x y)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (B : ℝ) (hB : ∀ x, ∑' y, m x y ≤ B) :
    ∀ y, Summable (fun x => m x y) ∧ (∑' x, m x y) ≤ c*B := by
  let cut (n : ℕ) (x y : V) : ℝ := if transportCut G n x y then m x y else 0
  have hn (n : ℕ) (x y : V) : 0 ≤ cut n x y := by
    dsimp [cut]; split_ifs; exact hm x y; exact le_refl 0
  have hcRow (n : ℕ) (x : V) : Summable (cut n x) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x n).toFinset)
    intro y hy
    simp only [Set.Finite.mem_toFinset] at hy
    exact ite_eq_right (fun h => hy h.1)
  have hcCol (n : ℕ) (y : V) : Summable (fun x => cut n x y) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
    intro x hx
    simp only [Set.Finite.mem_toFinset] at hx
    exact ite_eq_right (fun h => hx h.2)
  have hcInv (n : ℕ) : ∀ a ∈ Γ, ∀ x y, cut n (a x) (a y) = cut n x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    simp only [cut,transportCut_aut G hb,hi a ha]
  have hcBound (n : ℕ) (x : V) : (∑' y, cut n x y) ≤ B := by
    apply le_trans ((hcRow n x).tsum_le_tsum (fun y => ?_) (hr x)) (hB x)
    dsimp [cut]; split_ifs; exact le_refl _; exact hm x y
  have hbound (y : V) (Z : Finset V) : (∑ x ∈ Z, m x y) ≤ c*B := by
    obtain ⟨n,hnZ⟩ := exists_transportCut G hconn y Z
    calc
      _ = ∑ x ∈ Z, cut n x y := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (ite_eq_left (hnZ x hx)).symm
      _ ≤ ∑' x, cut n x y := (hcCol n y).sum_le_tsum Z (fun x _ => hn n x y)
      _ ≤ c*B := transported_column_le root weight Γ htr hcov hw hw1 c hc hmin
        (cut n) (hn n) (hcInv n) (hcRow n) (hcCol n) B (hcBound n) y
  intro y
  exact ⟨summable_of_sum_le (fun x => hm x y) (hbound y),
    Real.tsum_le_of_sum_le (fun x => hm x y) (hbound y)⟩



end NonnegativeTransport

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_EndpointKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointRule
attribute [local instance] Classical.propDecidable Classical.decEq



namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem mass_le_one (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V) :
    q.mass ω x y ≤ 1 := by
  have h := (q.summable_mass ω x).sum_le_tsum ({y} : Finset V) (fun z _ => q.nonneg ω x z)
  simpa only [Finset.sum_singleton] using h.trans (q.row_le_one ω x)

 
theorem measurable_mass (q : LocalEndpointRule G hloc O M L) (x y : V) :
    Measurable (fun ω => q.mass ω x y) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset
  let f : Set (Q : Set E) → ℝ := fun η => q.mass (Subtype.val '' η) x y
  have hm : Measurable f := measurable_of_finite f
  have he : (fun ω => q.mass ω x y) = f ∘ (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (Q : Set E)) := by
    funext ω
    rw [q.locality ω x y]
    congr 1
    ext e
    simp [Q,and_comm]
  rw [he]
  exact hm.comp (measurable_set_restrict (Q : Set E))

theorem integrable_mass (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) :
    Integrable (fun ω => q.mass ω x y) (law p) := by
  apply Integrable.of_bound (q.measurable_mass x y).aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (q.nonneg ω x y)] using q.mass_le_one ω x y



theorem kernel_outside_ball_zero (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V)
    (hy : y ∉ reachBall G x M) : q.kernel p x y = 0 := by
  simp only [kernel,q.outside_ball_zero _ x y hy,integral_zero]



theorem kernel_row_integral (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∑' y, q.kernel p x y) = ∫ ω, (∑' y, q.mass ω x y) ∂law p := by
  let B := (finite_reachBall hloc x M).toFinset
  have h₁ : (∑' y, q.kernel p x y) = ∑ y ∈ B, q.kernel p x y :=
    tsum_eq_sum fun y hy => q.kernel_outside_ball_zero p x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  have h₂ (ω : Set E) : (∑' y, q.mass ω x y) = ∑ y ∈ B, q.mass ω x y :=
    tsum_eq_sum fun y hy => q.outside_ball_zero ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  rw [h₁]
  simp_rw [h₂]
  exact (integral_finsetSum B (fun y _ => q.integrable_mass p x y)).symm

theorem kernel_row_le_one (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∑' y, q.kernel p x y) ≤ 1 := by
  rw [q.kernel_row_integral p x]
  have hi : Integrable (fun ω => ∑' y, q.mass ω x y) (law p) := by
    let B := (finite_reachBall hloc x M).toFinset
    have he (ω : Set E) : (∑' y, q.mass ω x y) = ∑ y ∈ B, q.mass ω x y :=
      tsum_eq_sum fun y hy => q.outside_ball_zero ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
    simp_rw [he]
    exact integrable_finsetSum B (fun y _ => q.integrable_mass p x y)
  calc
    _ ≤ ∫ _, (1:ℝ) ∂law p := integral_mono hi (integrable_const _) (q.row_le_one · x)
    _ = 1 := by simp

end LocalEndpointRule
end LocalEndpointRule

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem successProbability_le_one (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    q.successProbability p x ≤ 1 := q.kernel_row_le_one p x

end LocalEndpointRule
end LocalEndpointKernel

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section FiniteLocalIntegral
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteFieldWeight_eq_atom (Q : Finset E) (p : unitInterval) (ω : FiniteField Q) :
    finiteFieldWeight Q p ω = (law p : Measure (Set (Q : Set E))).real {finiteFieldEquiv Q ω} := by
  have hn : (finiteFieldEquiv Q ω).ncard = ω.val.card := by
    rw [finiteFieldEquiv_apply,Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
    · exact Set.ncard_coe_finset _
    · intro e he
      exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,rfl⟩
  rw [law,setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ,hn]
  have hc : Fintype.card (Q : Set E) = Q.card := Fintype.card_coe Q
  simp only [finiteFieldWeight,bernoulliWeight,Set.ncard_univ,Nat.card_eq_fintype_card,hc]

 

theorem integral_finite_local (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) :
    (∫ ω, f ω ∂law p) = ∑ η : FiniteField Q, finiteFieldWeight Q p η * f (finiteFieldSet Q η) := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have hmap := integral_map (μ := law p) (measurable_set_restrict (Q : Set E)).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable
  rw [law_map_restrict p (Q : Set E)] at hmap
  have he (ω : Set E) : g (Subtype.val ⁻¹' ω) = f ω := by
    rw [hf ω]
    dsimp [g]
    congr 1
    ext e
    simp [and_comm]
  simp_rw [he] at hmap
  rw [← hmap,integral_fintype Integrable.of_finite]
  rw [← (finiteFieldEquiv Q).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  rw [← finiteFieldWeight_eq_atom]
  simp only [g,finiteFieldEquiv_image,smul_eq_mul]

end FiniteLocalIntegral

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedGoodLocality
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_finite_local (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Integrable f (law p) := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  have hi : Integrable g (Measure.map (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) (law p)) := by
    rw [law_map_restrict]
    exact Integrable.of_finite
  rw [he]
  exact hi.comp_measurable (measurable_set_restrict (Q : Set E))

end CappedGoodLocality

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Connections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connections for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterWindowLaw
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterWindow_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
    ClusterWindow G x lo hi ω ↔ ClusterWindow G x lo hi (ω ∩ (Q : Set E)) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  change ClusterWindow G x lo hi ω ↔ ClusterWindow G x lo hi (ω ∩ (Q : Set E))
  constructor
  · rintro ⟨hf,hl,hh⟩
    have hs : cluster G ω x ⊆ (finite_reachBall hloc x hi).toFinset := by
      simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hf hi hh.le
    have he := cluster_restrict_incident_of_full G hloc _ ω x hs
    change cluster G (ω ∩ (Q : Set E)) x = cluster G ω x at he
    exact ⟨he.symm ▸ hf,he.symm ▸ hl,he.symm ▸ hh⟩
  · rintro ⟨hf,hl,hh⟩
    have he := cluster_restrict_of_cap G hloc Q ω x hi (Finset.Subset.refl _) hf hh.le
    exact ⟨he ▸ hf,he ▸ hl,he ▸ hh⟩

theorem measurableSet_clusterWindow (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) : MeasurableSet {ω | ClusterWindow G x lo hi ω} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  have he : {ω | ClusterWindow G x lo hi ω} =
      {ω | ω ∩ (Q : Set E) ∈ {η | ClusterWindow G x lo hi η}} := by
    ext ω
    exact clusterWindow_local G hloc x lo hi ω
  rw [he]
  exact measurableSet_finite_restriction Q _

theorem clusterWindowProbability_nonneg (G : BondGraph V E) (p : unitInterval)
    (x : V) (lo hi : ℕ) : 0 ≤ clusterWindowProbability G p x lo hi := ENNReal.toReal_nonneg

end ClusterWindowLaw
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_ScaleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale Budget for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterSizeMomentIntegrable
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_cluster_ncard (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Measurable (fun ω : Set E => (cluster G ω x).ncard) := by
  have hm (k : ℕ) (hk : k ≠ 0) : MeasurableSet {ω : Set E | (cluster G ω x).ncard = k} := by
    have he : {ω : Set E | (cluster G ω x).ncard = k} = {ω | ClusterWindow G x k (k+1) ω} := by
      ext ω
      constructor
      · intro h
        have hf := Set.finite_of_ncard_ne_zero (by rw [h]; exact hk)
        exact ⟨hf,by rw [h],by rw [h]; omega⟩
      · rintro ⟨hf,hl,hu⟩
        exact le_antisymm (by omega) hl
    rw [he]
    exact measurableSet_clusterWindow G hloc x k (k+1)
  have hm0 : MeasurableSet {ω : Set E | (cluster G ω x).ncard = 0} := by
    have he : {ω : Set E | (cluster G ω x).ncard = 0} =
        (⋃ k : ℕ, {ω : Set E | (cluster G ω x).ncard = k+1})ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff,Set.mem_iUnion,Set.mem_ofPred_eq,not_exists]
      constructor
      · intro h k
        omega
      · intro h
        by_contra hz
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
        exact h k hk
    rw [he]
    exact (MeasurableSet.iUnion (fun k => hm (k+1) (by omega))).compl
  apply measurable_to_countable
  intro ω
  change MeasurableSet {ω' | (cluster G ω' x).ncard = (cluster G ω x).ncard}
  by_cases h : (cluster G ω x).ncard = 0
  · simpa only [h] using hm0
  · exact hm _ h

 

theorem integrable_cluster_power_of_dyadic (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) (α : ℝ) (hα : 0 < α)
    (hs : Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p x (2^j) (2^(j+1)))) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) := by
  let f := fun ω : Set E => ((cluster G ω x).ncard:ℝ)^α
  let F := fun j : ℕ => {ω | ClusterWindow G x (2^j) (2^(j+1)) ω}.indicator
    (fun _ => (2:ℝ)^(α*((j+1:ℕ):ℝ)))
  have hFm (j : ℕ) : Measurable (F j) :=
    measurable_const.indicator (measurableSet_clusterWindow G hloc x _ _)
  have hFi (j : ℕ) : Integrable (F j) (law p) :=
    (integrable_const _).indicator (measurableSet_clusterWindow G hloc x _ _)
  have hFn (j : ℕ) (ω : Set E) : 0 ≤ F j ω := by
    exact Set.indicator_nonneg (fun _ _ => (Real.rpow_pos_of_pos (by norm_num) _).le) _
  have hFe (j : ℕ) : (∫ ω, F j ω ∂law p) =
      (2:ℝ)^α * ((2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p x (2^j) (2^(j+1))) := by
    rw [integral_indicator_const _ (measurableSet_clusterWindow G hloc x _ _)]
    simp only [smul_eq_mul,clusterWindowProbability,Nat.cast_add,Nat.cast_one,mul_add,mul_one,
      Real.rpow_add (by norm_num : (0:ℝ)<2)]
    ring
  have hsum : Summable (fun j => ∫ ω, F j ω ∂law p) := by
    simp only [hFe]
    exact hs.mul_left _
  have hbound (ω : Set E) : ENNReal.ofReal (f ω) ≤ ∑' j, ENNReal.ofReal (F j ω) := by
    by_cases hz : (cluster G ω x).ncard = 0
    · simp only [f,hz,Nat.cast_zero,Real.zero_rpow hα.ne',ENNReal.ofReal_zero]
      exact bot_le
    · let j := Nat.log 2 (cluster G ω x).ncard
      have hl := Nat.pow_log_le_self 2 hz
      have hu := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (cluster G ω x).ncard
      have hb : ClusterWindow G x (2^j) (2^(j+1)) ω :=
        ⟨Set.finite_of_ncard_ne_zero hz,hl,hu⟩
      have hle : f ω ≤ (2:ℝ)^(α*((j+1:ℕ):ℝ)) := by
        have hcast : ((cluster G ω x).ncard:ℝ) ≤ ((2^(j+1):ℕ):ℝ) := by exact_mod_cast hu.le
        have h := Real.rpow_le_rpow (Nat.cast_nonneg _) hcast hα.le
        have he : (((2^(j+1):ℕ):ℝ)^α) = (2:ℝ)^(α*((j+1:ℕ):ℝ)) := by
          rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
          congr 1
          ring
        exact h.trans_eq he
      have he : F j ω = (2:ℝ)^(α*((j+1:ℕ):ℝ)) := Set.indicator_of_mem (show ω ∈ {ω | ClusterWindow G x (2^j) (2^(j+1)) ω} from hb) _
      exact (ENNReal.ofReal_le_ofReal (hle.trans_eq he.symm)).trans
        (ENNReal.le_tsum (f := fun scale => ENNReal.ofReal (F scale ω)) j)
  have hfn (ω : Set E) : 0 ≤ f ω := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨((measurable_of_countable (fun m : ℕ => (m:ℝ)^α)).comp (measurable_cluster_ncard G hloc x)).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfn)).mpr
  have hlin : (∫⁻ ω, ∑' j, ENNReal.ofReal (F j ω) ∂law p) < ⊤ := by
    rw [lintegral_tsum (fun j => (hFm j).ennreal_ofReal.aemeasurable)]
    simp_rw [←ofReal_integral_eq_lintegral_ofReal (hFi _) (Filter.Eventually.of_forall (hFn _))]
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hFn j)) hsum]
    exact ENNReal.ofReal_lt_top
  exact (lintegral_mono hbound).trans_lt hlin

end ClusterSizeMomentIntegrable

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_Resampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resampling for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicBall
attribute [local instance] Classical.propDecidable Classical.decEq


theorem integral_eq_bernoulliPolynomial (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q:Set E))) :
    (∫ ω, f ω ∂law p) = bernoulliPolynomial Q (fun η => f η) p := by
  rw [integral_finite_local Q p f hf]
  simp only [finiteFieldWeight,finiteFieldSet]
  rw [Finset.sum_coe_sort Q.powerset (fun η => bernoulliWeight Q η p * f η)]
  unfold bernoulliPolynomial
  apply Finset.sum_congr rfl
  intro η _
  unfold bernoulliWeight
  ring

end IntrinsicBall
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_KernelMoments
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
section ThreeArmGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem Along.first_entrance {G : BondGraph V E} {x y : V} {l : List E}
    (hl : Along G x l y) (D : Set V) (hy : y ∈ D) :
    ∃ z ∈ D, ∃ k : List E, Along G x k z ∧ k ⊆ l ∧ ∀ e ∈ k, e ∉ internalEdges G D := by
  induction hl with
  | nil => exact ⟨_,hy,[],.nil _,by simp,by simp⟩
  | @cons x z y l e he ht ih =>
    by_cases hx : x ∈ D
    · exact ⟨x,hx,[],.nil _,by simp,by simp⟩
    · obtain ⟨w,hw,k,hk,hsub,hout⟩ := ih hy
      refine ⟨w,hw,e::k,.cons e he hk,?_,?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub hd)
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · intro h
          exact hx ((mem_internalEdges_of_ends G D d x z he).mp h).1
        · exact hout d hd

 

theorem conn_three_disjoint_arms (G : BondGraph V E) (ω : Set E) (x y z : V)
    (hxy : Conn G ω x y) (hxz : Conn G ω x z) :
    ∃ w, ω ∈ DisjointOccurrence {η | Conn G η x w}
      (DisjointOccurrence {η | Conn G η w y} {η | Conn G η w z}) := by
  obtain ⟨p⟩ := (conn_iff_reachable G ω x y).mp hxy
  let t := p.toPath
  let D : Set V := {a | a ∈ t.val.support}
  obtain ⟨l,hl,_,ho⟩ := conn_exists_bond_trail G (conn_symm G ω hxz)
  obtain ⟨w,hw,k,hk,hsub,hout⟩ := hl.first_entrance D t.val.start_mem_support
  obtain ⟨l₁,h₁,he₁,ho₁⟩ := walk_lift_bonds G ω (t.val.takeUntil w hw)
  obtain ⟨l₂,h₂,he₂,ho₂⟩ := walk_lift_bonds G ω (t.val.dropUntil w hw)
  have h₁in (e : E) (he : e ∈ l₁) : e ∈ internalEdges G D := by
    have hh : G e ∈ (t.val.takeUntil w hw).edges := he₁ ▸ List.mem_map_of_mem he
    have hh' := t.val.edges_takeUntil_subset_edges hw hh
    intro a ha
    exact SimpleGraph.Walk.mem_support_of_mem_edges hh' ha
  have h₂in (e : E) (he : e ∈ l₂) : e ∈ internalEdges G D := by
    have hh : G e ∈ (t.val.dropUntil w hw).edges := he₂ ▸ List.mem_map_of_mem he
    have hh' := t.val.edges_dropUntil_subset_edges hw hh
    intro a ha
    exact SimpleGraph.Walk.mem_support_of_mem_edges hh' ha
  have h12 : Disjoint l₁.toFinset l₂.toFinset := by
    apply Finset.disjoint_left.mpr
    intro e he₁' he₂'
    have hp := t.property.isTrail.disjoint_edges_takeUntil_dropUntil hw
    exact List.disjoint_left.mp hp (he₁ ▸ List.mem_map_of_mem (List.mem_toFinset.mp he₁'))
      (he₂ ▸ List.mem_map_of_mem (List.mem_toFinset.mp he₂'))
  have h13 : Disjoint l₁.toFinset k.toFinset := by
    apply Finset.disjoint_left.mpr
    intro e he hk'
    exact hout e (List.mem_toFinset.mp hk') (h₁in e (List.mem_toFinset.mp he))
  have h23 : Disjoint l₂.toFinset k.toFinset := by
    apply Finset.disjoint_left.mpr
    intro e he hk'
    exact hout e (List.mem_toFinset.mp hk') (h₂in e (List.mem_toFinset.mp he))
  have hkopen (e : E) (he : e ∈ k) : e ∈ ω := ho e (hsub he)
  refine ⟨w,l₁.toFinset,l₂.toFinset ∪ k.toFinset,?_,?_,Finset.disjoint_union_right.mpr ⟨h12,h13⟩,?_,?_⟩
  · intro e he; exact ho₁ e (List.mem_toFinset.mp he)
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact ho₂ e (List.mem_toFinset.mp he)
    · exact hkopen e (List.mem_toFinset.mp he)
  · exact h₁.conn (fun e he => List.mem_toFinset.mpr he)
  · refine ⟨l₂.toFinset,k.toFinset,?_,?_,h23,?_,?_⟩
    · exact_mod_cast Finset.subset_union_left
    · exact_mod_cast Finset.subset_union_right
    · exact h₂.conn (fun e he => List.mem_toFinset.mpr he)
    · exact conn_symm G _ (hk.conn (fun e he => List.mem_toFinset.mpr he))

end ThreeArmGeometry
end Percolation

 
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

 

theorem three_arm_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y z : V) :
    law p {ω | Conn G ω x y ∧ Conn G ω x z} ≤
      ∑' w, law p {ω | Conn G ω x w} * law p {ω | Conn G ω w y} * law p {ω | Conn G ω w z} := by
  let C := fun a b : V => {ω : Set E | Conn G ω a b}
  have hup (a b : V) : IsUpperSet (C a b) := fun _ _ h hconn => conn_mono G h hconn
  have hf (a b : V) : FiniteWitness (C a b) := finiteWitness_conn G a b
  have hb (w : V) : law p (DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) ≤
      law p (C x w) * law p (C w y) * law p (C w z) := by
    calc
      _ ≤ law p (C x w) * law p (DisjointOccurrence (C w y) (C w z)) :=
        bk_ennreal p _ _ (hup x w) (disjointOccurrence_upper _ _) (hf x w) (finiteWitness_disjointOccurrence _ _)
      _ ≤ law p (C x w) * (law p (C w y)*law p (C w z)) :=
        mul_le_mul_right (bk_ennreal p _ _ (hup w y) (hup w z) (hf w y) (hf w z)) _
      _ = _ := (mul_assoc _ _ _).symm
  calc
    _ ≤ law p (⋃ w, DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) := by
      apply measure_mono
      intro ω h
      obtain ⟨w,hw⟩ := conn_three_disjoint_arms G ω x y z h.1 h.2
      exact Set.mem_iUnion.mpr ⟨w,hw⟩
    _ ≤ ∑' w, law p (DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum hb

 

theorem three_arm_double_sum_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ x, (∑' y, law p {ω | Conn G ω x y}) ≤ C) (x : V) :
    (∑' y, ∑' z, law p {ω | Conn G ω x y ∧ Conn G ω x z}) ≤ C^3 := by
  calc
    _ ≤ ∑' y, ∑' z, ∑' w, law p {ω | Conn G ω x w} * law p {ω | Conn G ω w y} * law p {ω | Conn G ω w z} :=
      ENNReal.tsum_le_tsum (fun y => ENNReal.tsum_le_tsum (fun z => three_arm_bound G p x y z))
    _ = ∑' w, law p {ω | Conn G ω x w} * (∑' y, law p {ω | Conn G ω w y}) *
        (∑' z, law p {ω | Conn G ω w z}) := by
      calc
        _ = ∑' y, ∑' w, ∑' z, law p {ω | Conn G ω x w} * law p {ω | Conn G ω w y} * law p {ω | Conn G ω w z} := by
          apply tsum_congr
          intro y
          exact ENNReal.tsum_comm
        _ = ∑' w, ∑' y, ∑' z, law p {ω | Conn G ω x w} * law p {ω | Conn G ω w y} * law p {ω | Conn G ω w z} := ENNReal.tsum_comm
        _ = _ := by simp_rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _ ≤ ∑' w, law p {ω | Conn G ω x w} * C * C :=
      ENNReal.tsum_le_tsum (fun w => mul_le_mul' (mul_le_mul_right (hC w) _) (hC w))
    _ = (∑' w, law p {ω | Conn G ω x w}) * C * C := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_right]
    _ ≤ C*C*C := mul_le_mul_left (mul_le_mul_left (hC x) C) C
    _ = C^3 := by ring

end ThreeArmProbability
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterMassMoments
attribute [local instance] Classical.propDecidable Classical.decEq


theorem clusterMass_eq_ncard (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : clusterMass G ω x = (cluster G ω x).ncard := by
  change (∑' y, if y ∈ cluster G ω x then (1:ℝ≥0∞) else 0) = _
  rw [tsum_eq_sum (s := hf.toFinset) (fun y hy => by
    simp only [Set.Finite.mem_toFinset] at hy
    simp only [ite_eq_right hy])]
  have he : (∑ y ∈ hf.toFinset, if y ∈ cluster G ω x then (1:ℝ≥0∞) else 0) = ∑ _y ∈ hf.toFinset, (1:ℝ≥0∞) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact ite_eq_left (hf.mem_toFinset.mp hy)
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hf]

theorem lintegral_clusterMass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V) :
    (∫⁻ ω, clusterMass G ω x ∂law p) = ∑' y, law p {ω | Conn G ω x y} := by
  unfold clusterMass
  rw [lintegral_tsum (fun y => (Measurable.ite (measurableSet_conn G x y) measurable_const measurable_const).aemeasurable)]
  apply tsum_congr
  intro y
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using (lintegral_indicator_one (μ := law p) (measurableSet_conn G x y))

theorem clusterMass_sq (G : BondGraph V E) (ω : Set E) (x : V) :
    clusterMass G ω x ^ 2 = ∑' y, ∑' z, if Conn G ω x y ∧ Conn G ω x z then (1:ℝ≥0∞) else 0 := by
  rw [pow_two,clusterMass]
  rw [←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro y
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  split_ifs <;> simp_all

theorem lintegral_clusterMass_sq [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V) :
    (∫⁻ ω, clusterMass G ω x ^ 2 ∂law p) =
      ∑' y, ∑' z, law p {ω | Conn G ω x y ∧ Conn G ω x z} := by
  have hm (y z : V) : Measurable (fun ω : Set E => if Conn G ω x y ∧ Conn G ω x z then (1:ℝ≥0∞) else 0) :=
    Measurable.ite ((measurableSet_conn G x y).inter (measurableSet_conn G x z)) measurable_const measurable_const
  simp_rw [clusterMass_sq]
  rw [lintegral_tsum (fun y => (Measurable.tsum (fun z => hm y z)).aemeasurable)]
  apply tsum_congr
  intro y
  rw [lintegral_tsum (fun z => (hm y z).aemeasurable)]
  apply tsum_congr
  intro z
  have hs : MeasurableSet {ω : Set E | Conn G ω x y ∧ Conn G ω x z} :=
    (measurableSet_conn G x y).inter (measurableSet_conn G x z)
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using (lintegral_indicator_one (μ := law p) hs)

 
theorem cluster_second_moment_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ x, (∑' y, law p {ω | Conn G ω x y}) ≤ C) (x : V) :
    (∫⁻ ω, clusterMass G ω x ^ 2 ∂law p) ≤ C^3 := by
  rw [lintegral_clusterMass_sq]
  exact three_arm_double_sum_bound G p C hC x

end ClusterMassMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SubcriticalMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem subcritical_cluster_finite_ae (G : BondGraph V E)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
  have hz : (law p).real {ω | (cluster G ω x).Infinite} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! h
    exact (not_le_of_gt hp) (pc_le_of_infinite_cluster_probability_pos G x p h)
  apply ae_iff.mpr
  change law p {ω | (cluster G ω x).Infinite} = 0
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)

theorem subcritical_ennreal_row_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (∑' y, law p {ω | Conn G ω x y}) ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  refine ⟨C,hC,fun x => ?_⟩
  have hs := summable_of_sum_le (twoPoint_nonneg G p x) (hrow x)
  have he : (∑' y, law p {ω | Conn G ω x y}) = ENNReal.ofReal (∑' y, twoPoint G p x y) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (twoPoint_nonneg G p x) hs]
    apply tsum_congr
    intro y
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [he]
  exact ENNReal.ofReal_le_ofReal (hs.tsum_le_of_sum_le (hrow x))

 

theorem subcritical_second_moment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p) ∧
      (∫ ω, ((cluster G ω x).ncard:ℝ)^2 ∂law p) ≤ C^3 := by
  obtain ⟨C,hC,hrow⟩ := subcritical_ennreal_row_bound G hloc hqt p hp
  refine ⟨C,hC,fun x => ?_⟩
  have hmeas : Measurable (fun ω : Set E => ((cluster G ω x).ncard:ℝ)^2) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ)^2)).comp (measurable_cluster_ncard G hloc x)
  have hn : 0 ≤ᵐ[law p] (fun ω => ((cluster G ω x).ncard:ℝ)^2) :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have he : (fun ω => ENNReal.ofReal (((cluster G ω x).ncard:ℝ)^2)) =ᵐ[law p]
      (fun ω => clusterMass G ω x ^ 2) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    rw [clusterMass_eq_ncard G ω x hω,ENNReal.ofReal_pow (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  have hbound : (∫⁻ ω, ENNReal.ofReal (((cluster G ω x).ncard:ℝ)^2) ∂law p) ≤ ENNReal.ofReal (C^3) := by
    rw [lintegral_congr_ae he,ENNReal.ofReal_pow hC]
    exact cluster_second_moment_bound G p _ hrow x
  have hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p) :=
    ⟨hmeas.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hn).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hmeas.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal (pow_nonneg hC _))

end SubcriticalMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SusceptibilityTypes
attribute [local instance] Classical.propDecidable Classical.decEq

theorem susceptibility_nonneg (G : BondGraph V E) (p : unitInterval) (x : V) :
    0 ≤ susceptibility G p x := tsum_nonneg (twoPoint_nonneg G p x)

theorem summable_twoPoint_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : Summable (twoPoint G p x) := by
  obtain ⟨_,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  exact summable_of_sum_le (twoPoint_nonneg G p x) (hrow x)

theorem ennreal_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    ENNReal.ofReal (susceptibility G p x) = ∑' y, law p {ω | Conn G ω x y} := by
  rw [susceptibility,ENNReal.ofReal_tsum_of_nonneg (twoPoint_nonneg G p x)
    (summable_twoPoint_subcritical G hloc hqt p hp x)]
  apply tsum_congr
  intro y
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem susceptibility_aut [Countable V] [Countable E] (G : BondGraph V E)
    (p : unitInterval) {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x : V) :
    susceptibility G p (a x) = susceptibility G p x := by
  unfold susceptibility
  rw [←a.tsum_eq]
  simp only [twoPoint_aut G p h]

theorem susceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ susceptibility G p x := by
  have hd : twoPoint G p x x = 1 := by
    have he : {ω : Set E | Conn G ω x x} = Set.univ := Set.eq_univ_of_forall (fun _ => conn_refl G _ x)
    simp only [twoPoint,he,measure_univ,ENNReal.toReal_one]
  rw [←hd]
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).le_tsum x (fun _ _ => twoPoint_nonneg G p _ _)

theorem susceptibility_le_rootSusceptibility [Countable V] [Countable E]
    (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i) (p : unitInterval) (x : V) :
    susceptibility G p x ≤ c*rootSusceptibility G root weight p := by
  obtain ⟨i,a,b,hab,hax⟩ := hcov x
  rw [←hax,susceptibility_aut G p hab]
  calc
    _ ≤ (c*weight i)*susceptibility G p (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) (susceptibility_nonneg G p _)
    _ = c*(weight i*susceptibility G p (root i)) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (susceptibility_nonneg G p _)) (Finset.mem_univ i)) hc

 
theorem susceptibility_eq_integral [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)) (law p) ∧
      susceptibility G p x = ∫ ω, ((cluster G ω x).ncard:ℝ) ∂law p := by
  have hm : Measurable (fun ω : Set E => ((cluster G ω x).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x)
  have hn : 0 ≤ᵐ[law p] (fun ω => ((cluster G ω x).ncard:ℝ)) := Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  have he : (fun ω => ENNReal.ofReal ((cluster G ω x).ncard:ℝ)) =ᵐ[law p] (fun ω => clusterMass G ω x) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    rw [clusterMass_eq_ncard G ω x hω,ENNReal.ofReal_natCast]
  have heq : (∫⁻ ω, ENNReal.ofReal ((cluster G ω x).ncard:ℝ) ∂law p) = ENNReal.ofReal (susceptibility G p x) := by
    rw [lintegral_congr_ae he,lintegral_clusterMass,ennreal_susceptibility G hloc hqt p hp]
  refine ⟨⟨hm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hn).mpr (by rw [heq]; exact ENNReal.ofReal_lt_top)⟩,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable,heq,ENNReal.toReal_ofReal (susceptibility_nonneg G p x)]

end SusceptibilityTypes
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_ExteriorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterAssociation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem association_finiteWitness_ennreal [Countable E] (p : unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    law p A * law p B ≤ law p (A ∩ B) := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) (measure_ne_top _ _)).mp
  rw [ENNReal.toReal_mul]
  exact association_finiteWitness p A B hA hB hfA hfB

theorem clusterMass_mul (G : BondGraph V E) (ω : Set E) (x y : V) :
    clusterMass G ω x * clusterMass G ω y =
      ∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b then (1:ℝ≥0∞) else 0 := by
  rw [clusterMass,clusterMass,←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  split_ifs <;> simp_all

theorem lintegral_clusterMass_mul [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (∫⁻ ω, clusterMass G ω x * clusterMass G ω y ∂law p) =
      ∑' a, ∑' b, law p {ω | Conn G ω x a ∧ Conn G ω y b} := by
  have hm (a b : V) : Measurable (fun ω : Set E => if Conn G ω x a ∧ Conn G ω y b then (1:ℝ≥0∞) else 0) :=
    Measurable.ite ((measurableSet_conn G x a).inter (measurableSet_conn G y b)) measurable_const measurable_const
  simp_rw [clusterMass_mul]
  rw [lintegral_tsum (fun a => (Measurable.tsum (fun b => hm a b)).aemeasurable)]
  apply tsum_congr
  intro a
  rw [lintegral_tsum (fun b => (hm a b).aemeasurable)]
  apply tsum_congr
  intro b
  have hs : MeasurableSet {ω : Set E | Conn G ω x a ∧ Conn G ω y b} :=
    (measurableSet_conn G x a).inter (measurableSet_conn G y b)
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using (lintegral_indicator_one (μ := law p) hs)

theorem clusterMass_association [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (∑' a, law p {ω | Conn G ω x a})*(∑' b, law p {ω | Conn G ω y b}) ≤
      ∫⁻ ω, clusterMass G ω x * clusterMass G ω y ∂law p := by
  rw [lintegral_clusterMass_mul,←ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro a
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro b
  exact association_finiteWitness_ennreal p _ _
    (fun _ _ hω hc => conn_mono G hω hc) (fun _ _ hω hc => conn_mono G hω hc)
    (finiteWitness_conn G x a) (finiteWitness_conn G y b)

 

theorem subcritical_cluster_association [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) (law p) ∧
    susceptibility G p x * susceptibility G p y ≤
      ∫ ω, ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) ∂law p := by
  have hm (z : V) : Measurable (fun ω : Set E => ((cluster G ω z).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc z)
  have hn (ω : Set E) : 0 ≤ ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨_,_,hsecond⟩ := subcritical_second_moment G hloc hqt p hp
  have hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) (law p) := by
    apply ((hsecond x).1.add (hsecond y).1).mono' ((hm x).mul (hm y)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only [Pi.mul_apply,Pi.add_apply]
      rw [Real.norm_of_nonneg (hn ω)]
      nlinarith [sq_nonneg (((cluster G ω x).ncard:ℝ)-((cluster G ω y).ncard:ℝ))])
  refine ⟨hi,?_⟩
  have he : (fun ω => ENNReal.ofReal (((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ))) =ᵐ[law p]
      (fun ω => clusterMass G ω x * clusterMass G ω y) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
    rw [clusterMass_eq_ncard G ω x hx,clusterMass_eq_ncard G ω y hy,ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  have hb : ENNReal.ofReal (susceptibility G p x * susceptibility G p y) ≤
      ∫⁻ ω, ENNReal.ofReal (((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) ∂law p := by
    rw [lintegral_congr_ae he,ENNReal.ofReal_mul (susceptibility_nonneg G p x),
      ennreal_susceptibility G hloc hqt p hp,ennreal_susceptibility G hloc hqt p hp]
    exact clusterMass_association G p x y
  have htop : (∫⁻ ω, ENNReal.ofReal (((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) ∂law p) ≠ ⊤ :=
    ne_of_lt ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)).mp hi.hasFiniteIntegral)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hi.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (susceptibility_nonneg G p x) (susceptibility_nonneg G p y))] using
    ENNReal.toReal_mono htop hb

end ClusterAssociation
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshExteriorMoment
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_distinct_cluster_product [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fun ω => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) (law p) := by
  have he : (fun ω : Set E => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) =
      {ω : Set E | Conn G ω x y}ᶜ.indicator
        (fun ω => ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) := by
    funext ω
    simp only [Set.indicator,Set.mem_compl_iff,Set.mem_ofPred_eq]
  rw [he]
  exact (subcritical_cluster_association G hloc hqt p hp x y).1.indicator
    (measurableSet_conn G x y).compl



end FreshExteriorMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctClusterMoments
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinctClusterMoment_nonneg (G : BondGraph V E) (p : unitInterval) (x y : V) :
    0 ≤ distinctClusterMoment G p x y := by
  apply integral_nonneg
  intro ω
  dsimp only [Pi.zero_apply]
  split_ifs <;> positivity

theorem cluster_ncard_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
  rw [←cluster_aut G hab,Set.ncard_image_of_injective _ a.injective]

theorem distinctClusterMoment_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) :
    distinctClusterMoment G p (a x) (a y) = distinctClusterMoment G p x y := by
  have hs (z : V) : Measurable (fun ω : Set E => ((cluster G ω z).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc z)
  have hm : Measurable (fun ω : Set E => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) :=
    Measurable.ite (measurableSet_conn G x y).compl ((hs x).mul (hs y)) measurable_const
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [distinctClusterMoment,conn_aut_iff G hab,cluster_ncard_covariant G hab] using h.symm

theorem neighborClusterMoment_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) : 0 ≤ neighborClusterMoment G hloc p x :=
  Finset.sum_nonneg (fun y _ => distinctClusterMoment_nonneg G p x y)

theorem neighbors_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    neighbors G hloc (a x) = (neighbors G hloc x).map a.toEmbedding := by
  ext y
  simp only [mem_neighbors,Finset.mem_map,Equiv.coe_toEmbedding]
  constructor
  · intro h
    refine ⟨a.symm y,?_,by simp⟩
    simpa only [a.symm_apply_apply] using adj_aut G (isAut_symm G hab) h
  · rintro ⟨z,hz,rfl⟩
    exact adj_aut G hab hz

theorem neighborClusterMoment_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    neighborClusterMoment G hloc p (a x) = neighborClusterMoment G hloc p x := by
  simp only [neighborClusterMoment,neighbors_covariant G hloc hab,Finset.sum_map,Equiv.coe_toEmbedding,
    distinctClusterMoment_covariant G hloc p hab]

theorem neighborMoment_le_rootMoment [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcov : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i) (p : unitInterval) (x : V) :
    neighborClusterMoment G hloc p x ≤ c*rootNeighborMoment G hloc root weight p := by
  obtain ⟨i,a,b,hab,hax⟩ := hcov x
  rw [←hax,neighborClusterMoment_covariant G hloc p hab]
  calc
    _ ≤ (c*weight i)*neighborClusterMoment G hloc p (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) (neighborClusterMoment_nonneg G hloc p _)
    _ = c*(weight i*neighborClusterMoment G hloc p (root i)) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (neighborClusterMoment_nonneg G hloc p _)) (Finset.mem_univ i)) hc

end DistinctClusterMoments
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_DistinctMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section MapScaleBudget
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

theorem geometricScale_two_le (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ)) :
    2 ≤ q.geometricScale := by
  have hu : 1 ≤ (q.rule.successProbability p₀ o)⁻¹ :=
    (one_le_inv₀ q.success_pos).mpr (q.rule.successProbability_le_one p₀ o)
  have hb : 0 ≤ (1-(p₀:ℝ))/p₀*q.cap :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr p₀.2.2) hp₀.le) (Nat.cast_nonneg _)
  dsimp [geometricScale,potentialScale]
  nlinarith

theorem log_geometricScale_le (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ))
    (hM : 1 ≤ q.cap) :
    Real.log q.geometricScale ≤ q.U+q.m+Real.log (2*(1+1/(p₀:ℝ))) := by
  have hM' : (1:ℝ) ≤ q.cap := by exact_mod_cast hM
  have hMp : (0:ℝ) < q.cap := zero_lt_one.trans_le hM'
  have hb : 1+(1-(p₀:ℝ))/p₀*q.cap ≤ (1+1/(p₀:ℝ))*q.cap := by
    apply (mul_le_mul_iff_of_pos_right hp₀).mp
    field_simp
    nlinarith
  have Hz : q.geometricScale ≤ (1/q.rule.successProbability p₀ o)*(q.cap:ℝ)*(2*(1+1/(p₀:ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (inv_nonneg.mpr q.success_pos.le))
    simpa only [geometricScale,potentialScale,one_div,mul_assoc,mul_comm,mul_left_comm] using h
  have hc : 0 < 2*(1+1/(p₀:ℝ)) := by positivity
  have h := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (q.geometricScale_two_le hp₀)) Hz
  rw [Real.log_mul (mul_ne_zero (one_div_ne_zero q.success_pos.ne') hMp.ne') hc.ne',
    Real.log_mul (one_div_ne_zero q.success_pos.ne') hMp.ne'] at h
  exact h

end EndpointProfile
end MapScaleBudget
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EfficientProfileMomentConsequence
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem neighborMoment_growth_of_divergent_moment
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (p₀ : unitInterval) (hp₀ : 0 < (p₀:ℝ)) (hp₁ : (p₀:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law p₀, (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p₀)) :
    ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ᶠ p in nhds p₀, p < pc G →
      b*(rootSusceptibility G root weight p)^(2-γ) ≤ rootNeighborMoment G hloc root weight p := by
  obtain ⟨i,heff⟩ := efficient_endpoint_profiles_of_divergent_moment G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 p₀ hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hw i)).le)
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  intro γ hγ
  let C := Real.log (2*(1+1/(p₀:ℝ)))
  have hC : 0 ≤ C := Real.log_nonneg (by
    have hinv : 0 ≤ 1/(p₀:ℝ) := (one_div_pos.mpr hp₀).le
    nlinarith)
  obtain ⟨q,hM,hH,hR,hcost⟩ := heff (γ/4) (by linarith) (2+4*C/γ)
  have hH2 : 2 < q.H := by
    have hn : 0 ≤ 4*C/γ := div_nonneg (mul_nonneg (by norm_num) hC) hγ.le
    linarith
  have hCsmall : C < γ*q.H/4 := by
    have hx : 4*C < (q.H-2)*γ := (div_lt_iff₀ hγ).mp (by linarith : 4*C/γ < q.H-2)
    nlinarith
  have hexp : Real.log q.geometricScale/(q.H-1) ≤ γ := by
    apply (div_le_iff₀ (by linarith : 0 < q.H-1)).mpr
    have hz := q.log_geometricScale_le hp₀ (by omega)
    have hm : γ*q.H/2 ≤ γ*(q.H-1) := by nlinarith
    dsimp [C] at hCsmall
    nlinarith only [hz,hcost,hCsmall,hm]
  obtain ⟨b,hb,hnear⟩ := q.eventually_neighborMoment_lower hconn hqt root weight Γ htr
    (fun a ha => hΓ ha) (fun i => (hw i).le) hw1 i (hw i) hcover c hc hmin hp₀ hH
  refine ⟨b,hb,?_⟩
  filter_upwards [hnear] with p hp
  intro hpc
  have hχ : 1 ≤ rootSusceptibility G root weight p := by
    calc
      1 = ∑ i, weight i*1 := by simp only [mul_one,hw1]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (susceptibility_one_le G hloc hqt p hpc (root i)) (hw i).le)
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hχ (by linarith :
    2-γ ≤ 2-Real.log q.geometricScale/(q.H-1))) hb.le).trans (hp hpc)

end EfficientProfileMomentConsequence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory Function
section PivotalSprinklingGain
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_set_union_pair : Measurable (fun f : Set E × Set E => f.1 ∪ f.2) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  apply measurableSet_setOfPred.mp
  change MeasurableSet ({f : Set E × Set E | e ∈ f.1} ∪ {f | e ∈ f.2})
  apply MeasurableSet.union <;> apply measurableSet_setOfPred.mpr
  · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_fst
  · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_snd

theorem measurable_set_insert (e : E) : Measurable (fun ω : Set E => insert e ω) := by
  have h : Measurable (fun ω : Set E => ({e}:Set E) ∪ ω) :=
    measurable_set_union_pair.comp (measurable_const.prodMk measurable_id)
  simpa only [Set.singleton_union] using (h : Measurable (fun ω : Set E => {e} ∪ ω))

theorem measurableSet_closedPivotal (A : Set (Set E)) (hA : MeasurableSet A) (e : E) :
    MeasurableSet (closedPivotal A e) := by
  exact (measurableSet_mem e).compl.inter (hA.compl.inter (hA.preimage (measurable_set_insert e)))

theorem measurableSet_singleSprinkle (Q : Finset E) (e : (Q : Set E)) :
    MeasurableSet (singleSprinkle Q e) :=
  (measurableSet_singleton _).preimage (measurable_set_restrict (Q:Set E))

theorem singleSprinkle_disjoint (Q : Finset E) :
    Pairwise (Disjoint on singleSprinkle Q) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro η ha hb
  apply hab
  have h : ({a} : Set (Q:Set E)) = {b} := ha.symm.trans hb
  simpa only [Set.singleton_eq_singleton_iff] using h

theorem singleSprinkle_mem (Q : Finset E) (e : (Q:Set E)) {η : Set E}
    (hη : η ∈ singleSprinkle Q e) : e.val ∈ η := by
  have h : e ∈ Subtype.val ⁻¹' η := by rw [hη]; exact Set.mem_singleton e
  exact h

theorem singleSprinkle_probability (Q : Finset E) (e : (Q:Set E)) (a : unitInterval) :
    (law a).real (singleSprinkle Q e) = (a:ℝ)*(1-(a:ℝ))^(Q.card-1) := by
  have h := congrArg (fun μ : Measure (Set (Q:Set E)) => μ.real {({e}:Set (Q:Set E))})
    (law_map_restrict a (Q:Set E))
  rw [Measure.real,Measure.map_apply (measurable_set_restrict _) (measurableSet_singleton _)] at h
  change (law a).real (singleSprinkle Q e) = _ at h
  rw [h,law,setBernoulli_real_singleton a (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ,Set.ncard_singleton]
  simp only [Set.ncard_univ,Nat.card_eq_fintype_card,pow_one]
  rw [show Fintype.card (Q:Set E) = Q.card from Fintype.card_coe Q]

 

theorem event_sprinkling_gain (p a : unitInterval) (Q : Finset E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hup : IsUpperSet A) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) * (∑ e ∈ Q, (law p).real (closedPivotal A e)) ≤
      (law (sprinkleParameter p a)).real A - (law p).real A := by
  let μ : Measure (Set E × Set E) := (law p).prod (law a)
  let B : Set (Set E × Set E) := {f | f.1 ∉ A ∧ f.1 ∪ f.2 ∈ A}
  let C (e : (Q:Set E)) := (closedPivotal A e.val) ×ˢ singleSprinkle Q e
  have hB : MeasurableSet B := (hA.compl.preimage measurable_fst).inter (hA.preimage measurable_set_union_pair)
  have hC (e : (Q:Set E)) : MeasurableSet (C e) :=
    (measurableSet_closedPivotal A hA e.val).prod (measurableSet_singleSprinkle Q e)
  have hd : Pairwise (Disjoint on C) := by
    intro e f hef
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact Set.disjoint_left.mp (singleSprinkle_disjoint Q hef) hz.2 hz'.2
  have hsub : (⋃ e, C e) ⊆ B := by
    intro z hz
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp hz
    refine ⟨he.1.2.1,?_⟩
    apply hup _ he.1.2.2
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact Or.inr (singleSprinkle_mem Q e he.2)
    · exact Or.inl hf
  have hgain : μ.real B = (law (sprinkleParameter p a)).real A - (law p).real A := by
    have he : (fun f : Set E × Set E => f.1 ∪ f.2) ⁻¹' A = (A ×ˢ Set.univ) ∪ B := by
      ext f
      simp only [Set.mem_preimage,Set.mem_union,Set.mem_prod,Set.mem_univ,and_true,B,Set.mem_ofPred_eq]
      exact ⟨fun h => by by_cases ha : f.1 ∈ A; exact Or.inl ha; exact Or.inr ⟨ha,h⟩,
        fun h => h.elim (fun ha => hup Set.subset_union_left ha) And.right⟩
    have hd : Disjoint (A ×ˢ (Set.univ : Set (Set E))) B := by
      apply Set.disjoint_left.mpr
      intro f hf hf'
      exact hf'.1 hf.1
    have hm := congrArg (fun ν : Measure (Set E) => ν.real A) (law_map_union p a)
    rw [Measure.real,Measure.map_apply measurable_set_union_pair hA] at hm
    change μ.real ((fun f : Set E × Set E => f.1 ∪ f.2) ⁻¹' A) = _ at hm
    rw [he,measureReal_union hd hB] at hm
    have hp : μ.real (A ×ˢ Set.univ) = (law p).real A := by
      rw [measureReal_prod_prod,probReal_univ,mul_one]
    rw [hp] at hm
    linarith
  have hs : μ.real (⋃ e, C e) =
      (a:ℝ)*(1-(a:ℝ))^(Q.card-1) * (∑ e ∈ Q, (law p).real (closedPivotal A e)) := by
    rw [measureReal_iUnion_fintype hd hC]
    simp only [C,μ,measureReal_prod_prod,singleSprinkle_probability]
    rw [←Finset.sum_mul,mul_comm]
    congr 1
    apply Finset.sum_bij (fun e _ => e.val)
    · intro e _; exact e.property
    · intro e _ f _ h; exact Subtype.ext h
    · intro e he; exact ⟨⟨e,he⟩,Finset.mem_univ _,rfl⟩
    · intro _ _; rfl
  rw [←hs,←hgain]
  exact measureReal_mono hsub

end PivotalSprinklingGain
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Susceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SusceptibilityPivotalGain
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sprinkleParameter_ge_left (p a : unitInterval) : p ≤ sprinkleParameter p a := by
  change (p:ℝ) ≤ (p:ℝ)+(1-(p:ℝ))*(a:ℝ)
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr p.2.2) a.2.1)

 

theorem susceptibility_sprinkling_gain [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p a : unitInterval) (hq : sprinkleParameter p a < pc G) (x : V)
    (Q : Finset E) (F : Finset V) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) *
      (∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω x y} e)) ≤
      susceptibility G (sprinkleParameter p a) x - susceptibility G p x := by
  have hpa := sprinkleParameter_ge_left p a
  have hp : p < pc G := lt_of_le_of_lt hpa hq
  have hsum := (summable_twoPoint_subcritical G hloc hqt (sprinkleParameter p a) hq x).sub
    (summable_twoPoint_subcritical G hloc hqt p hp x)
  calc
    _ = ∑ y ∈ F, (a:ℝ)*(1-(a:ℝ))^(Q.card-1)*
      (∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω x y} e)) := Finset.mul_sum _ _ _
    _ ≤ ∑ y ∈ F, (twoPoint G (sprinkleParameter p a) x y - twoPoint G p x y) := by
      apply Finset.sum_le_sum
      intro y _
      exact event_sprinkling_gain p a Q {ω | Conn G ω x y} (measurableSet_conn G x y)
        (fun _ _ h hc => conn_mono G h hc)
    _ ≤ ∑' y, (twoPoint G (sprinkleParameter p a) x y - twoPoint G p x y) :=
      hsum.sum_le_tsum F (fun y _ => sub_nonneg.mpr (twoPoint_mono G x y hpa))
    _ = _ := (summable_twoPoint_subcritical G hloc hqt (sprinkleParameter p a) hq x).tsum_sub
      (summable_twoPoint_subcritical G hloc hqt p hp x)

 
theorem rootSusceptibility_sprinkling_gain [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p a : unitInterval) (hq : sprinkleParameter p a < pc G)
    (Q : Finset E) (F : Finset V) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) *
      (∑ i, weight i*(∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω (root i) y} e))) ≤
      rootSusceptibility G root weight (sprinkleParameter p a) - rootSusceptibility G root weight p := by
  rw [rootSusceptibility,rootSusceptibility,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (susceptibility_sprinkling_gain G hloc hqt p a hq (root i) Q F) (hw i)
  convert h using 1 <;> ring

end SusceptibilityPivotalGain
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrientedPivotalConnections
attribute [local instance] Classical.propDecidable Classical.decEq



theorem measurableSet_orientedPivotalEvent [Countable V] [Countable E]
    (G : BondGraph V E) (x y a b : V) : MeasurableSet (orientedPivotalEvent G x y a b) :=
  (measurableSet_conn G x a).inter ((measurableSet_conn G b y).inter (measurableSet_conn G a b).compl)

theorem orientedPivotalEvent_disjoint (G : BondGraph V E) (x y a b : V) :
    Disjoint (orientedPivotalEvent G x y a b) (orientedPivotalEvent G x y b a) := by
  apply Set.disjoint_left.mpr
  intro ω h h'
  exact h.2.2 ((conn_symm G ω h.1).trans h'.1)

theorem closedPivotal_conn (G : BondGraph V E) (e : E) (a b x y : V)
    (he : G e = s(a,b)) :
    closedPivotal {ω | Conn G ω x y} e =
      orientedPivotalEvent G x y a b ∪ orientedPivotalEvent G x y b a := by
  ext ω
  constructor
  · rintro ⟨_,hn,hc⟩
    rcases (conn_insert_iff G ω e a b x y he).mp hc with h | h | h
    · exact (hn h).elim
    · exact Or.inl ⟨h.1,h.2,fun hab => hn (h.1.trans (hab.trans h.2))⟩
    · exact Or.inr ⟨h.1,h.2,fun hba => hn (h.1.trans (hba.trans h.2))⟩
  · intro h
    have hi : ∀ a b : V, G e = s(a,b) → ω ∈ orientedPivotalEvent G x y a b →
        ω ∈ closedPivotal {ω | Conn G ω x y} e := by
      intro a b he h
      refine ⟨?_,?_,?_⟩
      · intro heω
        exact h.2.2 (.single ⟨e,heω,he⟩)
      · intro hxy
        exact h.2.2 ((conn_symm G ω h.1).trans (hxy.trans (conn_symm G ω h.2.1)))
      · exact (conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨h.1,h.2.1⟩))
    exact h.elim (hi a b he) (hi b a (he.trans (Sym2.eq_swap ..)))

theorem closedPivotal_conn_probability [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (e : E) (a b x y : V) (he : G e = s(a,b)) :
    (law p).real (closedPivotal {ω | Conn G ω x y} e) =
      (law p).real (orientedPivotalEvent G x y a b) +
      (law p).real (orientedPivotalEvent G x y b a) := by
  rw [closedPivotal_conn G e a b x y he]
  exact measureReal_union (orientedPivotalEvent_disjoint G x y a b)
    (measurableSet_orientedPivotalEvent G x y b a)


end OrientedPivotalConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PivotalMomentIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem distinctClusterMass_eq_pivotal (G : BondGraph V E) (ω : Set E) (a b : V) :
    (if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) =
      ∑' x, ∑' y, if ω ∈ orientedPivotalEvent G x y a b then (1:ℝ≥0∞) else 0 := by
  by_cases hab : Conn G ω a b
  · simp only [hab,not_true_eq_false,ite_false,orientedPivotalEvent,Set.mem_ofPred_eq,
       and_false,ite_false,tsum_zero]
  · rw [ite_eq_left hab,clusterMass_mul]
    apply tsum_congr
    intro x
    apply tsum_congr
    intro y
    apply if_congr _ rfl rfl
    simp only [orientedPivotalEvent,Set.mem_ofPred_eq,hab,not_false_eq_true,and_true]
    exact and_congr (show Conn G ω a x ↔ Conn G ω x a from ⟨conn_symm G ω,conn_symm G ω⟩) Iff.rfl

theorem lintegral_distinctClusterMass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (a b : V) :
    (∫⁻ ω, (if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) ∂law p) =
      ∑' x, ∑' y, law p (orientedPivotalEvent G x y a b) := by
  have hm (x y : V) : Measurable (fun ω : Set E =>
      if ω ∈ orientedPivotalEvent G x y a b then (1:ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_orientedPivotalEvent G x y a b) measurable_const measurable_const
  simp_rw [distinctClusterMass_eq_pivotal]
  rw [lintegral_tsum (fun x => (Measurable.tsum (fun y => hm x y)).aemeasurable)]
  apply tsum_congr
  intro x
  rw [lintegral_tsum (fun y => (hm x y).aemeasurable)]
  apply tsum_congr
  intro y
  simpa only [Set.indicator,Pi.one_apply] using
    (lintegral_indicator_one (μ := law p) (measurableSet_orientedPivotalEvent G x y a b))

theorem ennreal_distinctClusterMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    ENNReal.ofReal (distinctClusterMoment G p a b) =
      ∑' x, ∑' y, law p (orientedPivotalEvent G x y a b) := by
  have hi := integrable_distinct_cluster_product G hloc hqt p hp a b
  have hn : 0 ≤ᵐ[law p] (fun ω => if ¬Conn G ω a b
      then ((cluster G ω a).ncard:ℝ)*((cluster G ω b).ncard:ℝ) else 0) := by
    exact Filter.Eventually.of_forall (fun ω => by dsimp only; split_ifs <;> positivity)
  have he : (fun ω => ENNReal.ofReal (if ¬Conn G ω a b
      then ((cluster G ω a).ncard:ℝ)*((cluster G ω b).ncard:ℝ) else 0)) =ᵐ[law p]
      (fun ω => if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp a,
      subcritical_cluster_finite_ae G p hp b] with ω ha hb
    by_cases hab : Conn G ω a b
    · simp only [hab,not_true_eq_false,ite_false,ENNReal.ofReal_zero]
    · simp only [hab,not_false_eq_true,ite_true]
      rw [clusterMass_eq_ncard G ω a ha,clusterMass_eq_ncard G ω b hb,
        ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp only [ENNReal.ofReal_natCast]
  rw [←lintegral_distinctClusterMass,←lintegral_congr_ae he]
  exact ofReal_integral_eq_lintegral_ofReal hi hn

theorem summable_orientedPivotal_pairs [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    Summable (fun xy : V × V => (law p).real (orientedPivotalEvent G xy.1 xy.2 a b)) := by
  apply ENNReal.summable_toReal
  rw [ENNReal.tsum_prod',←ennreal_distinctClusterMoment G hloc hqt p hp a b]
  exact ENNReal.ofReal_ne_top

theorem distinctClusterMoment_eq_pivotal [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    distinctClusterMoment G p a b =
      ∑' x, ∑' y, (law p).real (orientedPivotalEvent G x y a b) := by
  rw [←(summable_orientedPivotal_pairs G hloc hqt p hp a b).tsum_prod]
  change distinctClusterMoment G p a b =
    ∑' xy : V × V, (law p (orientedPivotalEvent G xy.1 xy.2 a b)).toReal
  rw [←ENNReal.tsum_toReal_eq (f := fun xy : V × V => law p (orientedPivotalEvent G xy.1 xy.2 a b))
    (fun _ => measure_ne_top _ _), ENNReal.tsum_prod',
    ←ennreal_distinctClusterMoment G hloc hqt p hp a b,
    ENNReal.toReal_ofReal (distinctClusterMoment_nonneg G p a b)]

end PivotalMomentIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PivotalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem orientedPivotal_probability_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x y z w : V) :
    (law p).real (orientedPivotalEvent G (a x) (a y) (a z) (a w)) =
      (law p).real (orientedPivotalEvent G x y z w) := by
  have he : orientedPivotalEvent G (a x) (a y) (a z) (a w) =
      (fun ω => b ⁻¹' ω) ⁻¹' orientedPivotalEvent G x y z w := by
    ext ω
    simp only [orientedPivotalEvent,Set.mem_ofPred_eq,Set.mem_preimage,conn_aut_iff G hab]
  unfold Measure.real
  rw [he,←Measure.map_apply (measurable_set_preimage b)
    (measurableSet_orientedPivotalEvent G x y z w),law_map_preimage_equiv]

theorem pivotalTransportMass_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x a : V) : 0 ≤ pivotalTransportMass G hloc p x a :=
  Finset.sum_nonneg (fun _ _ => tsum_nonneg (fun _ => measureReal_nonneg))

theorem pivotalTransportMass_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x z : V) :
    pivotalTransportMass G hloc p (a x) (a z) = pivotalTransportMass G hloc p x z := by
  simp only [pivotalTransportMass,neighbors_covariant G hloc hab,Finset.sum_map,Equiv.coe_toEmbedding]
  apply Finset.sum_congr rfl
  intro w _
  rw [←a.tsum_eq (fun y => (law p).real (orientedPivotalEvent G (a x) y (a z) (a w)))]
  exact tsum_congr (fun y => orientedPivotal_probability_covariant G p hab x y z w)

theorem pivotalTransportMass_incoming_summable [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a : V) :
    Summable (fun x => pivotalTransportMass G hloc p x a) := by
  apply summable_sum
  intro b _
  exact (summable_orientedPivotal_pairs G hloc hqt p hp a b).prod

theorem pivotalTransportMass_incoming [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a : V) :
    (∑' x, pivotalTransportMass G hloc p x a) = neighborClusterMoment G hloc p a := by
  unfold pivotalTransportMass neighborClusterMoment
  rw [Summable.tsum_finsetSum (fun b _ =>
    (summable_orientedPivotal_pairs G hloc hqt p hp a b).prod)]
  exact Finset.sum_congr rfl (fun b _ => (distinctClusterMoment_eq_pivotal G hloc hqt p hp a b).symm)

end PivotalTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PivotalTransportTotal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pivotalTransportMass_outgoing_summable
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (pivotalTransportMass G hloc p x) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  exact (transported_column_of_row_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (fun a x => pivotalTransportMass G hloc p x a)
    (fun a x => pivotalTransportMass_nonneg G hloc p x a)
    (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; exact pivotalTransportMass_covariant G hloc p hab y x)
    (pivotalTransportMass_incoming_summable G hloc hqt p hp)
    (c*rootNeighborMoment G hloc root weight p)
    (fun a => by
      rw [pivotalTransportMass_incoming G hloc hqt p hp]
      exact neighborMoment_le_rootMoment G hloc root weight hw hcover c hc hmin p a) x).1

 

theorem rootPivotalMass_eq_neighborMoment
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) :
    (∑ i, weight i * ∑' a, pivotalTransportMass G hloc p (root i) a) =
      rootNeighborMoment G hloc root weight p := by
  rw [htr.real root weight Γ (pivotalTransportMass G hloc p)
    (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; exact pivotalTransportMass_covariant G hloc p hab x y)
    (pivotalTransportMass_outgoing_summable G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp)
    (pivotalTransportMass_incoming_summable G hloc hqt p hp)]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun t => weight i*t)
    (pivotalTransportMass_incoming G hloc hqt p hp (root i)))

end PivotalTransportTotal
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FinitePivotalComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem orientedPivotal_probability_le_closed [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (e : E) (x y a b : V) (he : G e = s(a,b)) :
    (law p).real (orientedPivotalEvent G x y a b) ≤
      (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  rw [closedPivotal_conn_probability G p e a b x y he]
  exact le_add_of_nonneg_right measureReal_nonneg

 

theorem finite_neighbor_pivotal_le_incident [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y a : V) :
    (∑ b ∈ neighbors G hloc a, (law p).real (orientedPivotalEvent G x y a b)) ≤
      ∑ e ∈ (hloc a).toFinset, (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  let B := neighbors G hloc a
  have he (b : B) : ∃ e, G e = s(a,(b:V)) := (mem_neighbors G hloc a b).mp b.property
  choose edge hedge using he
  have hinj : Function.Injective edge := by
    intro b c h
    apply Subtype.ext
    have hh := (hedge b).symm.trans ((congrArg G h).trans (hedge c))
    rcases Sym2.eq_iff.mp hh with h | h
    · exact h.2
    · exact h.2.trans h.1
  calc
    _ = ∑ b : B, (law p).real (orientedPivotalEvent G x y a b) := (Finset.sum_coe_sort B _).symm
    _ ≤ ∑ b : B, (law p).real (closedPivotal {ω | Conn G ω x y} (edge b)) :=
      Finset.sum_le_sum (fun b _ => orientedPivotal_probability_le_closed G p (edge b) x y a b (hedge b))
    _ = ∑ e ∈ Finset.univ.image edge, (law p).real (closedPivotal {ω | Conn G ω x y} e) :=
      (Finset.sum_image (f := fun e => (law p).real (closedPivotal {ω | Conn G ω x y} e))
        (s := Finset.univ) (fun _ _ _ _ h => hinj h)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp he
        rw [Set.Finite.mem_toFinset]
        change a ∈ G (edge b)
        rw [hedge b]
        exact Sym2.mem_mk_left _ _
      · intro _ _ _
        exact measureReal_nonneg

theorem finite_incident_sum_le_twice (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (f : E → ℝ) (hf : ∀ e, 0 ≤ f e) :
    (∑ a ∈ A, ∑ e ∈ (hloc a).toFinset, f e) ≤ 2*∑ e ∈ incidentSupport G hloc A, f e := by
  let Q := incidentSupport G hloc A
  have heq (a : V) (ha : a ∈ A) :
      (∑ e ∈ (hloc a).toFinset, f e) = ∑ e ∈ Q, if a ∈ G e then f e else 0 := by
    rw [←Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext e
    simp only [Set.Finite.mem_toFinset,Finset.mem_filter]
    exact ⟨fun he => ⟨(mem_incidentSupport G hloc A e).mpr ⟨a,ha,he⟩,he⟩,fun h => h.2⟩
  calc
    _ = ∑ a ∈ A, ∑ e ∈ Q, if a ∈ G e then f e else 0 := Finset.sum_congr rfl heq
    _ = ∑ e ∈ Q, ∑ a ∈ A, if a ∈ G e then f e else 0 := Finset.sum_comm
    _ ≤ ∑ e ∈ Q, 2*f e := by
      apply Finset.sum_le_sum
      intro e _
      have hsub : A.filter (fun a => a ∈ G e) ⊆ (G e).toFinset := by
        intro a ha
        exact Sym2.mem_toFinset.mpr (Finset.mem_filter.mp ha).2
      rw [←Finset.sum_filter,Finset.sum_const, nsmul_eq_mul]
      have hc : (A.filter (fun a => a ∈ G e)).card ≤ 2 := (Finset.card_le_card hsub).trans (by
        rw [Sym2.card_toFinset]; split_ifs <;> omega)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf e)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_oriented_pivotal_sum_le [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) (A : Finset V) :
    (∑ a ∈ A, ∑ b ∈ neighbors G hloc a, (law p).real (orientedPivotalEvent G x y a b)) ≤
      2*∑ e ∈ incidentSupport G hloc A, (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  exact (Finset.sum_le_sum (fun a _ => finite_neighbor_pivotal_le_incident G hloc p x y a)).trans
    (finite_incident_sum_le_twice G hloc A _ (fun _ => measureReal_nonneg))

end FinitePivotalComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SubcriticalSusceptibilityContinuity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem eventually_cluster_eq_at_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (labels : E → unitInterval) (p : unitInterval) (x : V)
    (hneq : ∀ e, labels e ≠ p) (hfin : (cluster G (openEdges labels p) x).Finite) :
    ∀ᶠ q in nhds p, cluster G (openEdges labels q) x = cluster G (openEdges labels p) x := by
  let Q := incidentSupport G hloc hfin.toFinset
  have he (e : E) : ∀ᶠ q in nhds p, (e ∈ openEdges labels q ↔ e ∈ openEdges labels p) := by
    change ∀ᶠ q in nhds p, (labels e ≤ q ↔ labels e ≤ p)
    by_cases hp : labels e ≤ p
    · have hlt : labels e < p := lt_of_le_of_ne hp (hneq e)
      filter_upwards [eventually_gt_nhds hlt] with q hq
      exact iff_of_true hq.le hp
    · have hlt : p < labels e := lt_of_not_ge hp
      filter_upwards [eventually_lt_nhds hlt] with q hq
      exact iff_of_false (not_le.mpr hq) hp
  filter_upwards [(eventually_all_finset Q).mpr (fun e _ => he e)] with q hq
  apply cluster_eq_of_incident_agreement G
  intro e he
  apply (hq e _).symm
  obtain ⟨v,hv,hve⟩ := he
  exact (mem_incidentSupport G hloc hfin.toFinset e).mpr ⟨v,hfin.mem_toFinset.mpr hv,hve⟩

theorem label_cluster_finite_ae_subcritical [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), (cluster G (openEdges labels p) x).Finite := by
  apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
    (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges p).aemeasurable
  rw [map_openEdges]
  exact subcritical_cluster_finite_ae G p hp x

theorem susceptibility_eq_label_integral [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Integrable (fun labels : E → unitInterval => ((cluster G (openEdges labels p) x).ncard:ℝ)) labelLaw ∧
    susceptibility G p x = ∫ labels : E → unitInterval, ((cluster G (openEdges labels p) x).ncard:ℝ) ∂labelLaw := by
  obtain ⟨hi,he⟩ := susceptibility_eq_integral G hloc hqt p hp x
  have hi' : Integrable (fun ω : Set E => ((cluster G ω x).ncard:ℝ))
      ((labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p)) := by
    rwa [map_openEdges]
  refine ⟨hi'.comp_measurable (measurable_openEdges p),?_⟩
  rw [he,←integral_map (measurable_openEdges p).aemeasurable hi'.aestronglyMeasurable,map_openEdges]

 

theorem continuousAt_susceptibility_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : ContinuousAt (fun q => susceptibility G q x) p := by
  obtain ⟨r,hpr,hr⟩ := exists_between hp
  let F (q : unitInterval) (labels : E → unitInterval) : ℝ := ((cluster G (openEdges labels q) x).ncard:ℝ)
  have hm (q : unitInterval) : Measurable (F q) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      ((measurable_cluster_ncard G hloc x).comp (measurable_openEdges q))
  have hcont : ContinuousAt (fun q => ∫ labels, F q labels ∂labelLaw) p := by
    apply continuousAt_of_dominated
      (bound := F r) (Filter.Eventually.of_forall (fun q => (hm q).aestronglyMeasurable))
    · filter_upwards [eventually_lt_nhds hpr] with q hqr
      filter_upwards [label_cluster_finite_ae_subcritical G r hr x] with labels hfin
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      dsimp only [F]
      exact_mod_cast Set.ncard_le_ncard (show cluster G (openEdges labels q) x ⊆ cluster G (openEdges labels r) x from
        fun y hy => conn_mono G (openEdges_mono labels hqr.le) hy) hfin
    · exact (susceptibility_eq_label_integral G hloc hqt r hr x).1
    · filter_upwards [ae_labels_ne (E := E) p,label_cluster_finite_ae_subcritical G p hp x] with labels hneq hfin
      apply Filter.EventuallyEq.continuousAt
      filter_upwards [eventually_cluster_eq_at_finite G hloc labels p x hneq hfin] with q hq
      exact congrArg (fun S : Set V => (S.ncard:ℝ)) hq
  apply (continuousAt_congr _).mpr hcont
  filter_upwards [eventually_lt_nhds hp] with q hq
  exact (susceptibility_eq_label_integral G hloc hqt q hq x).2

theorem continuousAt_rootSusceptibility_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp : p < pc G) :
    ContinuousAt (rootSusceptibility G root weight) p := by
  exact tendsto_finsetSum Finset.univ (fun i _ => continuousAt_const.mul
    (continuousAt_susceptibility_subcritical G hloc hqt p hp (root i)))

end SubcriticalSusceptibilityContinuity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section FiniteRootPivotalApproximation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_orientedPivotal_targets [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    Summable (fun y => (law p).real (orientedPivotalEvent G x y a b)) := by
  apply (summable_twoPoint_subcritical G hloc hqt p hp b).of_nonneg_of_le
  · exact fun _ => measureReal_nonneg
  · intro y
    exact measureReal_mono (fun _ h => h.2.1)

theorem finiteRootPivotalMass_nonneg (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) (Q : Finset E) (F : Finset V) :
    0 ≤ finiteRootPivotalMass G root weight p Q F :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i)
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => measureReal_nonneg))))

 

theorem exists_finiteRootPivotalMass_gt
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (B : ℝ)
    (hB : B < rootNeighborMoment G hloc root weight p / 2) :
    ∃ Q : Finset E, ∃ F : Finset V, B < finiteRootPivotalMass G root weight p Q F := by
  have hs (x : V) := pivotalTransportMass_outgoing_summable G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp x
  let f (a : V) := ∑ i, weight i*pivotalTransportMass G hloc p (root i) a
  have hsf : Summable f := summable_sum (fun i _ => (hs (root i)).mul_left (weight i))
  have htf : (∑' a, f a) = rootNeighborMoment G hloc root weight p := by
    rw [Summable.tsum_finsetSum (fun i _ => (hs (root i)).mul_left (weight i))]
    simp_rw [tsum_mul_left]
    exact rootPivotalMass_eq_neighborMoment G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp
  have hB' : 2*B < ∑' a, f a := by rw [htf]; linarith
  obtain ⟨A,hA⟩ := ((tendsto_order.mp hsf.hasSum).1 (2*B) hB').exists
  let g (y : V) := ∑ i, weight i*(∑ a ∈ A, ∑ b ∈ neighbors G hloc a,
    (law p).real (orientedPivotalEvent G (root i) y a b))
  have hst (i : ι) (a b : V) := summable_orientedPivotal_targets G hloc hqt p hp (root i) a b
  have hsg : Summable g := summable_sum (fun i _ =>
    (summable_sum (fun a _ => summable_sum (fun b _ => hst i a b))).mul_left (weight i))
  have htg : (∑' y, g y) = ∑ a ∈ A, f a := by
    rw [Summable.tsum_finsetSum (fun i _ =>
      (summable_sum (fun a _ => summable_sum (fun b _ => hst i a b))).mul_left (weight i))]
    simp_rw [tsum_mul_left]
    simp_rw [Summable.tsum_finsetSum (fun a _ => summable_sum (fun b _ => hst _ a b))]
    simp_rw [Summable.tsum_finsetSum (fun b _ => hst _ _ b)]
    simp only [f,Finset.mul_sum,pivotalTransportMass]
    rw [Finset.sum_comm]
  obtain ⟨F,hF⟩ := ((tendsto_order.mp hsg.hasSum).1 (2*B) (by rwa [htg])).exists
  refine ⟨incidentSupport G hloc A,F,?_⟩
  have hb : (∑ y ∈ F, g y) ≤ 2*finiteRootPivotalMass G root weight p (incidentSupport G hloc A) F := by
    unfold g finiteRootPivotalMass
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.mul_sum, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (hw i)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun y _ => finite_oriented_pivotal_sum_le G hloc p (root i) y A)
  linarith

end FiniteRootPivotalApproximation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section VanishingSprinkles
attribute [local instance] Classical.propDecidable Classical.decEq

theorem vanishingSprinkle_pos (n : ℕ) : 0 < (vanishingSprinkle n : ℝ) := by
  dsimp [vanishingSprinkle]
  positivity

theorem tendsto_vanishingSprinkle :
    Tendsto (fun n => (vanishingSprinkle n:ℝ)) atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem sprinkle_sequence_gt (p : unitInterval) (hp : (p:ℝ) < 1) (n : ℕ) :
    p < sprinkleParameter p (vanishingSprinkle n) := by
  change (p:ℝ) < (p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)
  exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hp) (vanishingSprinkle_pos n))

theorem tendsto_sprinkle_sequence (p : unitInterval) :
    Tendsto (fun n => sprinkleParameter p (vanishingSprinkle n)) atTop (nhds p) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => (p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)) atTop (nhds (p:ℝ))
  convert tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_vanishingSprinkle) using 1; simp

theorem tendsto_sprinkle_sequence_right (p : unitInterval) (hp : (p:ℝ) < 1) :
    Tendsto (fun n => (sprinkleParameter p (vanishingSprinkle n):ℝ)) atTop (nhdsWithin (p:ℝ) (Set.Ioi (p:ℝ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨continuous_subtype_val.continuousAt.tendsto.comp (tendsto_sprinkle_sequence p),
    Eventually.of_forall (sprinkle_sequence_gt p hp)⟩

 

theorem rootSusceptibility_sequence_slope_lower
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) (hp : p < pc G) (Q : Finset E) (F : Finset V) (d : ℝ)
    (hd : d < finiteRootPivotalMass G root weight p Q F) :
    ∀ᶠ n in atTop,
      ((sprinkleParameter p (vanishingSprinkle n):ℝ)-(p:ℝ))*d ≤
      rootSusceptibility G root weight (sprinkleParameter p (vanishingSprinkle n)) -
      rootSusceptibility G root weight p := by
  have ht : Tendsto (fun n => (1-(vanishingSprinkle n:ℝ))^(Q.card-1) *
      finiteRootPivotalMass G root weight p Q F) atTop
      (nhds (finiteRootPivotalMass G root weight p Q F)) := by
    convert ((tendsto_const_nhds.sub tendsto_vanishingSprinkle).pow (Q.card-1)).mul tendsto_const_nhds using 1; simp
  have hnn := finiteRootPivotalMass_nonneg G root weight hw p Q F
  filter_upwards [(tendsto_sprinkle_sequence p).eventually (eventually_lt_nhds hp),
      ht.eventually (eventually_gt_nhds hd)] with n hn hdn
  have hgain := rootSusceptibility_sprinkling_gain G hloc hqt root weight hw
    p (vanishingSprinkle n) hn Q F
  change (vanishingSprinkle n:ℝ)*(1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
    finiteRootPivotalMass G root weight p Q F ≤ _ at hgain
  by_cases hd0 : 0 ≤ d
  · have hdp : (1-(p:ℝ))*d ≤ (1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
        finiteRootPivotalMass G root weight p Q F := by
      calc
        _ ≤ d := by nlinarith [p.2.1]
        _ ≤ _ := hdn.le
    have hm := mul_le_mul_of_nonneg_left hdp (vanishingSprinkle n).2.1
    calc
      _ = (vanishingSprinkle n:ℝ)*((1-(p:ℝ))*d) := by
        change ((p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)-(p:ℝ))*d = _
        ring
      _ ≤ (vanishingSprinkle n:ℝ)*((1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
          finiteRootPivotalMass G root weight p Q F) := hm
      _ ≤ _ := by simpa only [mul_assoc] using hgain
  · have hmono : 0 ≤ rootSusceptibility G root weight (sprinkleParameter p (vanishingSprinkle n)) - rootSusceptibility G root weight p :=
      (mul_nonneg (mul_nonneg (vanishingSprinkle n).2.1 (pow_nonneg (sub_nonneg.mpr (vanishingSprinkle n).2.2) _)) hnn).trans hgain
    have hdp : ((sprinkleParameter p (vanishingSprinkle n):ℝ)-(p:ℝ))*d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (sprinkleParameter_ge_left _ _)) (le_of_not_ge hd0)
    linarith

end VanishingSprinkles
end Percolation

 
namespace Percolation
open Filter
section NegativePowerRightSlopes

 

theorem frequently_rpow_slope_le_of_sequence
    (f : ℝ → ℝ) (x d e : ℝ) (hx : 0 < f x) (hd : 0 < d) (he : e < 0)
    (z : ℕ → ℝ) (hz : Tendsto z atTop (nhdsWithin x (Set.Ioi x)))
    (hgain : ∀ᶠ n in atTop, (z n-x)*d ≤ f (z n)-f x) :
    ∀ r, e*(f x)^(e-1)*d < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope (fun t => (f t)^e) x y < r := by
  let A (t : ℝ) := f x+(t-x)*d
  have hA : HasDerivAt A d x := by
    simpa only [zero_add, one_mul] using! (hasDerivAt_const x (f x)).add (((hasDerivAt_id x).sub_const x).mul_const d)
  have hAx : A x = f x := by simp [A]
  have hR : HasDerivAt (fun t => (A t)^e) (e*(f x)^(e-1)*d) x := by
    simpa only [hAx] using! (Real.hasDerivAt_rpow_const (p := e) (Or.inl (show A x ≠ 0 by rw [hAx]; exact hx.ne'))).comp x hA
  intro r hr
  have hlim := hR.tendsto_slope.comp (hz.mono_right (nhdsWithin_mono x (show Set.Ioi x ⊆ {x}ᶜ from fun y hy => by simpa using ne_of_gt hy)))
  have hright : ∀ᶠ n in atTop, x < z n := (tendsto_nhdsWithin_iff.mp hz).2
  apply hz.frequently
  apply Filter.Eventually.frequently
  filter_upwards [hgain, hright, hlim.eventually (eventually_lt_nhds hr)] with n hn hzn hnr
  have hApos : 0 < A (z n) := by dsimp [A]; positivity
  have hAr : A (z n) ≤ f (z n) := by dsimp [A]; linarith
  have hp := Real.rpow_le_rpow_of_nonpos hApos hAr he.le
  apply lt_of_le_of_lt _ hnr
  simp only [Function.comp_apply, slope_def_field, hAx]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hp _) (sub_pos.mpr hzn).le

end NegativePowerRightSlopes
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ActualSusceptibilityRightSlope
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootSusceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ rootSusceptibility G root weight p := by
  calc
    1 = ∑ i, weight i*1 := by simp only [mul_one, hw1]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (susceptibility_one_le G hloc hqt p hp (root i)) (hw i))

theorem continuousAt_realRootSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp : p < pc G) :
    ContinuousAt (realRootSusceptibility G root weight) (p:ℝ) := by
  apply ContinuousAt.comp (f := Set.projIcc 0 1 zero_le_one)
  · simpa only [Set.projIcc_val] using continuousAt_rootSusceptibility_subcritical G hloc hqt root weight p hp
  · exact continuous_projIcc.continuousAt

 

theorem rootSusceptibility_power_right_slope
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (b γ : ℝ) (hb : 0 < b) (hγ : γ < 1)
    (hD : b*(rootSusceptibility G root weight p)^(2-γ) ≤ rootNeighborMoment G hloc root weight p) :
    ∀ r, -(1-γ)*b/4 < r → ∃ᶠ y in nhdsWithin (p:ℝ) (Set.Ioi (p:ℝ)),
      slope (fun t => (realRootSusceptibility G root weight t)^(γ-1)) (p:ℝ) y < r := by
  let χ := rootSusceptibility G root weight p
  have hχ : 0 < χ := lt_of_lt_of_le zero_lt_one (rootSusceptibility_one_le G hloc hqt root weight hw hw1 p hp)
  let d := (b/4)*χ^(2-γ)
  have hd : 0 < d := mul_pos (by positivity) (Real.rpow_pos_of_pos hχ _)
  have hBd : d < rootNeighborMoment G hloc root weight p/2 := by
    dsimp [d, χ] at *
    nlinarith [Real.rpow_pos_of_pos hχ (2-γ)]
  obtain ⟨Q,F,hQ⟩ := exists_finiteRootPivotalMass_gt G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp d hBd
  have hg := rootSusceptibility_sequence_slope_lower G hloc hqt root weight hw p hp Q F d hQ
  have hp1 : (p:ℝ) < 1 := lt_of_lt_of_le hp (pc G).2.2
  have hsl := frequently_rpow_slope_le_of_sequence (realRootSusceptibility G root weight)
    (p:ℝ) d (γ-1) (by simpa only [realRootSusceptibility_coe] using hχ) hd (by linarith)
    (fun n => (sprinkleParameter p (vanishingSprinkle n):ℝ)) (tendsto_sprinkle_sequence_right p hp1)
    (by simpa only [realRootSusceptibility_coe] using hg)
  have heq : (γ-1)*(realRootSusceptibility G root weight (p:ℝ))^(γ-1-1)*d = -(1-γ)*b/4 := by
    rw [realRootSusceptibility_coe]
    change (γ-1)*χ^(γ-1-1)*((b/4)*χ^(2-γ)) = _
    rw [show γ-1-1 = γ-2 by ring]
    calc
      _ = ((γ-1)*b/4)*(χ^(γ-2)*χ^(2-γ)) := by ring
      _ = _ := by rw [←Real.rpow_add hχ, sub_add_sub_cancel, sub_self, Real.rpow_zero]; ring
  rwa [heq] at hsl

end ActualSusceptibilityRightSlope
end Percolation

 
namespace Percolation
open Filter
section IntegratedRightSlopes

 

theorem interval_decrease_of_right_slope (f : ℝ → ℝ) (a b k : ℝ)
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hs : ∀ x ∈ Set.Ico a b, ∀ r, -k < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope f x y < r) :
    k*(b-a) ≤ f a-f b := by
  let B (t : ℝ) := f a-k*(t-a)
  have hB : ContinuousOn B (Set.Icc a b) := by fun_prop
  have hB' (x : ℝ) : HasDerivAt B (-k) x := by
    simpa only [one_mul, sub_zero, mul_one, zero_sub] using!
      (hasDerivAt_const x (f a)).sub (((hasDerivAt_id x).sub_const a).const_mul k)
  have h := image_le_of_liminf_slope_right_le_deriv_boundary hf
    (show f a ≤ B a by simp [B]) hB (fun x _ => (hB' x).hasDerivWithinAt) hs ⟨hab,le_rfl⟩
  dsimp [B] at h
  linarith

 

theorem right_slope_distance_bound (f : ℝ → ℝ) (a b k : ℝ)
    (hab : a < b) (hk : 0 < k)
    (hpos : ∀ x ∈ Set.Ico a b, 0 ≤ f x)
    (hc : ContinuousOn f (Set.Ico a b))
    (hs : ∀ x ∈ Set.Ico a b, ∀ r, -k < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope f x y < r) :
    k*(b-a) ≤ f a := by
  have hbound (r : ℝ) (hr : r ∈ Set.Ico a b) : k*(r-a) ≤ f a := by
    have hsub : Set.Icc a r ⊆ Set.Ico a b := fun t ht => ⟨ht.1,lt_of_le_of_lt ht.2 hr.2⟩
    have h := interval_decrease_of_right_slope f a r k hr.1 (hc.mono hsub)
      (fun x hx => hs x ⟨hx.1,lt_trans hx.2 hr.2⟩)
    linarith [hpos r hr]
  by_contra h
  have hd : a+f a/k < b := by
    have hh : f a < k*(b-a) := lt_of_not_ge h
    have hv : f a/k < b-a := (div_lt_iff₀ hk).mpr (by nlinarith)
    linarith
  obtain ⟨r,hr1,hr2⟩ := exists_between hd
  have ha : a ≤ r := by
    have hf := hpos a ⟨le_rfl,hab⟩
    have hd0 := div_nonneg hf hk.le
    linarith
  have hb := hbound r ⟨ha,hr2⟩
  have hr : f a < (r-a)*k := (div_lt_iff₀ hk).mp (by linarith : f a/k < r-a)
  nlinarith

end IntegratedRightSlopes
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ActualIntegratedSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem susceptibility_bound_of_neighborMoment
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (b γ : ℝ) (hb : 0 < b) (hγ : γ < 1)
    (hD : ∀ q, p ≤ q → q < pc G → b*(rootSusceptibility G root weight q)^(2-γ) ≤
      rootNeighborMoment G hloc root weight q) :
    rootSusceptibility G root weight p ≤
      (((1-γ)*b/4)*((pc G:ℝ)-(p:ℝ)))^(-1/(1-γ)) := by
  let k := (1-γ)*b/4
  have hk : 0 < k := by dsimp [k]; positivity
  let f (t : ℝ) := (realRootSusceptibility G root weight t)^(γ-1)
  have hparam (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans p.2.1 ht.1, le_trans ht.2.le (pc G).2.2⟩
  have hcp (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :
      ContinuousAt (realRootSusceptibility G root weight) t :=
    continuousAt_realRootSusceptibility G hloc hqt root weight ⟨t,hparam t ht⟩ ht.2
  have hpos (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :
      0 < realRootSusceptibility G root weight t := by
    have hh := rootSusceptibility_one_le G hloc hqt root weight hw hw1 ⟨t,hparam t ht⟩ ht.2
    rw [←realRootSusceptibility_coe] at hh
    exact lt_of_lt_of_le zero_lt_one hh
  have hcont : ContinuousOn f (Set.Ico (p:ℝ) (pc G:ℝ)) := by
    intro t ht
    exact ((hcp t ht).rpow_const (Or.inl (hpos t ht).ne')).continuousWithinAt
  have hs (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :=
    rootSusceptibility_power_right_slope G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin
      ⟨t,hparam t ht⟩ ht.2 b γ hb hγ (hD ⟨t,hparam t ht⟩ ht.1 ht.2)
  have hdist : k*((pc G:ℝ)-(p:ℝ)) ≤ f (p:ℝ) := by
    apply right_slope_distance_bound f (p:ℝ) (pc G:ℝ) k hp hk
      (fun t ht => (Real.rpow_pos_of_pos (hpos t ht) _).le) hcont
    intro t ht r hr
    apply hs t ht r
    dsimp [k] at hr
    linarith
  have hχ := lt_of_lt_of_le zero_lt_one (rootSusceptibility_one_le G hloc hqt root weight hw hw1 p hp)
  have hd : 0 < k*((pc G:ℝ)-(p:ℝ)) := mul_pos hk (sub_pos.mpr hp)
  have he : -1/(1-γ) = 1/(γ-1) := by rw [show γ-1=-(1-γ) by ring, div_neg, neg_div]
  have he0 : 1/(γ-1) < 0 := one_div_neg.mpr (by linarith)
  have hinv := Real.rpow_le_rpow_of_nonpos hd hdist he0.le
  rw [he]
  apply le_trans _ hinv
  change rootSusceptibility G root weight p ≤
    ((realRootSusceptibility G root weight (p:ℝ))^(γ-1))^(1/(γ-1))
  rw [realRootSusceptibility_coe,←Real.rpow_mul hχ.le]
  rw [mul_one_div_cancel (by linarith : γ-1 ≠ 0),Real.rpow_one]

end ActualIntegratedSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SusceptibilityGrowthConsequence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem eventually_upper_interval_unit (p₀ : unitInterval) (P : unitInterval → Prop)
    (h : ∀ᶠ p in nhds p₀, P p) :
    ∀ᶠ p in nhds p₀, p < p₀ → ∀ q, p ≤ q → q < p₀ → P q := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp h
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨ε,hε,?_⟩
  intro p hp hpp q hpq hq
  apply hball
  have hd : dist q p₀ ≤ dist p p₀ := by
    change |(q:ℝ)-(p₀:ℝ)| ≤ |(p:ℝ)-(p₀:ℝ)|
    rw [abs_of_nonpos (sub_nonpos.mpr (show (q:ℝ) ≤ (p₀:ℝ) from hq.le)),abs_of_nonpos (sub_nonpos.mpr (show (p:ℝ) ≤ (p₀:ℝ) from hpp.le))]
    have hpqR : (p:ℝ) ≤ (q:ℝ) := hpq
    linarith
  exact lt_of_le_of_lt hd hp

 

theorem susceptibility_growth_of_divergent_moment
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G))) :
    ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in nhds (pc G), p < pc G →
      rootSusceptibility G root weight p ≤ C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ)) := by
  intro γ hγ hγ1
  obtain ⟨b,hb,hnear⟩ := neighborMoment_growth_of_divergent_moment G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 (pc G) hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv γ hγ
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hw i)).le)
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  let k := (1-γ)*b/4
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k^(-1/(1-γ)),Real.rpow_pos_of_pos hk _,?_⟩
  filter_upwards [eventually_upper_interval_unit (pc G) _ hnear] with p hp
  intro hpc
  have hD (q : unitInterval) (hpq : p ≤ q) (hq : q < pc G) := hp hpc q hpq hq hq
  have hs := susceptibility_bound_of_neighborMoment G hconn hloc hqt root weight Γ hΓ htr hcov
    (fun i => (hw i).le) hw1 c hc hmin p hpc b γ hb hγ1 hD
  rwa [Real.mul_rpow hk.le (sub_pos.mpr (show (p:ℝ) < (pc G:ℝ) from hpc)).le] at hs

end SusceptibilityGrowthConsequence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedSearchTransfer
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exponential_transfer_of_deriv_bound (H : ℝ → ℝ) (a b K : ℝ)
    (hH : Differentiable ℝ H) (hab : a ≤ b)
    (hb : ∀ t ∈ Set.Icc a b, deriv H t ≤ K*H t) :
    H b ≤ Real.exp (K*(b-a))*H a := by
  let F (t : ℝ) := Real.exp (-K*(t-a))*H t
  have hF (t : ℝ) : HasDerivAt F (Real.exp (-K*(t-a))*(deriv H t-K*H t)) t := by
    have he := (((hasDerivAt_id t).sub_const a).const_mul (-K)).exp
    convert! he.mul (hH t).hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    ring
  have hanti : AntitoneOn F (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hb t (interior_subset ht)))
  have h := hanti ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (K*(b-a))).le
  simpa only [F, sub_self,mul_zero,Real.exp_zero,one_mul,←mul_assoc,←Real.exp_add,
    neg_mul,add_neg_cancel,Real.exp_zero,one_mul,neg_zero,add_zero] using hm

 

theorem markedConnection_transfer (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (p q h : unitInterval) (hp : 0 < (p:ℝ)) (hpq : p ≤ q) (hq : (q:ℝ) < 1)
    (hh : 0 < (h:ℝ)) :
    markedConnectionPolynomial G Q x h q ≤
      Real.exp ((Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ)))) *
        Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*((q:ℝ)-(p:ℝ))) *
      markedConnectionPolynomial G Q x h p := by
  let H := markedConnectionPolynomial G Q x h
  have hdiff : Differentiable ℝ H := fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt
  apply exponential_transfer_of_deriv_bound H p q _ hdiff hpq
  intro t ht
  let r : unitInterval := ⟨t,⟨le_trans p.2.1 ht.1,le_trans ht.2 q.2.2⟩⟩
  have hr0 : 0 < t := lt_of_lt_of_le hp ht.1
  have hr1 : t < 1 := lt_of_le_of_lt ht.2 hq
  have HB := markedConnection_derivative_bound G Q x r h hr1 hh d hd hdeg
  have hH : 0 ≤ H t := by
    change 0 ≤ markedConnectionPolynomial G Q x h r
    rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg r h _
  have hs : 0 ≤ Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ)) := Real.sqrt_nonneg _
  have hden : (p:ℝ)*(1-(q:ℝ)) ≤ t*(1-t) := by
    exact mul_le_mul ht.1 (by linarith [ht.2]) (sub_pos.mpr hq).le (by positivity)
  have hratio : Real.sqrt ((d:ℝ)/2)/(t*(1-t)) ≤
      Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ))) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos hp (sub_pos.mpr hq)) hden
  have hle : deriv H t ≤ (Real.sqrt ((d:ℝ)/2)/(t*(1-t)))*
      Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*H t := by
    have HBr : deriv H t ≤ ((Real.sqrt ((d:ℝ)/2)/(1-t))*
        Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*H t)/t := by
      apply (le_div_iff₀ hr0).mpr
      simpa only [mul_comm (deriv H t) t] using HB
    convert HBr using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  exact hle.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hs) hH)

end MarkedSearchTransfer
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedComponentIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem markedConnection_component_polynomial (G : BondGraph V E)
    (Q : Finset E) (x : V) (h p : ℝ) :
    markedConnectionPolynomial G Q x h p =
      bernoulliPolynomial Q (fun ω => 1-(1-h)^(finiteRootComponent G ω x).card) p := by
  apply bernoulliPolynomial_congr
  intro ω hω
  let C := finiteRootComponent G ω x
  let F := insert x (searchVertices G Q)
  have hCF : C ⊆ F := finiteRootComponent_subset G Q F x ω hω le_rfl
  have he (m : Finset V) : (∃ y ∈ m, Conn G (ω:Set E) x y) ↔ m ∩ C ≠ ∅ := by
    rw [Finset.nonempty_iff_ne_empty.symm]
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,Finset.mem_inter.mpr ⟨hy,by change y ∈ (C:Set V); simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hxy⟩⟩
    · rintro ⟨y,hy⟩
      refine ⟨y,(Finset.mem_inter.mp hy).1,?_⟩
      have hm : y ∈ (C:Set V) := (Finset.mem_inter.mp hy).2
      simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hm
  have hid : bernoulliPolynomial F (fun m => if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0) h =
      1-bernoulliPolynomial F (fun m => if m ∩ C = ∅ then 1 else 0) h := by
    calc
      _ = bernoulliPolynomial F (fun m => 1-(if m ∩ C = ∅ then 1 else 0)) h := by
        apply bernoulliPolynomial_congr
        intro m _
        by_cases hm : m ∩ C = ∅
        · have hn : ¬∃ y ∈ m, Conn G (ω:Set E) x y := fun hc => (he m).mp hc hm
          simp only [hm,hn,ite_false,ite_true,sub_self]
        · have hy := (he m).mpr hm
          simp only [hm,hy,ite_false,ite_true,sub_zero]
      _ = _ := by rw [bernoulliPolynomial_sub,bernoulliPolynomial_const]
  rw [hid,bernoulliPolynomial_restrict C F hCF (fun m => if m = ∅ then 1 else 0) h,
    bernoulliPolynomial_empty_indicator]

theorem one_sub_pow_one_sub_le (h : unitInterval) (n : ℕ) :
    1-(1-(h:ℝ))^n ≤ (h:ℝ)*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr h.2.2)
    have hn : 0 ≤ (h:ℝ)^2*n := by positivity
    nlinarith

end MarkedComponentIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedConnectionLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem markedConnection_integral (G : BondGraph V E) (Q : Finset E) (x : V)
    (h p : unitInterval) :
    markedConnectionPolynomial G Q x h p =
      ∫ ω, (1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard) ∂law p := by
  rw [integral_eq_bernoulliPolynomial Q p _ (by intro ω; simp only [Set.inter_assoc,Set.inter_self]),
    markedConnection_component_polynomial]
  apply bernoulliPolynomial_congr
  intro ω hω
  rw [Set.inter_eq_left.mpr (show (ω:Set E) ⊆ Q from hω)]
  congr 2
  rw [←coe_finiteRootComponent,Set.ncard_coe_finset]

theorem markedConnection_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (Q : Finset E) (x : V) (h p : unitInterval) (hp : p < pc G) :
    markedConnectionPolynomial G Q x h p ≤ (h:ℝ)*susceptibility G p x := by
  obtain ⟨hi,he⟩ := susceptibility_eq_integral G hloc hqt p hp x
  rw [markedConnection_integral,he,←integral_const_mul]
  apply integral_mono_ae
  · exact integrable_finite_local Q p _ (by intro ω; simp only [Set.inter_assoc,Set.inter_self])
  · exact hi.const_mul _
  · filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    apply (one_sub_pow_one_sub_le h _).trans
    apply mul_le_mul_of_nonneg_left _ h.2.1
    exact_mod_cast Set.ncard_le_ncard (fun y hy => conn_mono G Set.inter_subset_left hy) hω

 

theorem one_sub_pow_one_sub_ge_half (h : unitInterval) (n : ℕ)
    (hn : 1 ≤ (h:ℝ)*n) : (1:ℝ)/2 ≤ 1-(1-(h:ℝ))^n := by
  have hb (m : ℕ) : (1+(h:ℝ)*m)*(1-(h:ℝ))^m ≤ 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hp : 0 ≤ (1-(h:ℝ))^m := pow_nonneg (sub_nonneg.mpr h.2.2) _
      have ha : (1+(h:ℝ)*(m+1))*(1-(h:ℝ)) ≤ 1+(h:ℝ)*m := by
        have hh : 0 ≤ (h:ℝ)^2*((m:ℝ)+1) := by positivity
        nlinarith
      have hm := mul_le_mul_of_nonneg_right ha hp
      rw [Nat.cast_succ,pow_succ]
      nlinarith
  have hp : 0 ≤ (1-(h:ℝ))^n := pow_nonneg (sub_nonneg.mpr h.2.2) _
  have hm := mul_le_mul_of_nonneg_right hn hp
  have hb' := hb n
  nlinarith

 

theorem clusterWindow_le_markedConnection (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) (p h : unitInterval) (hh : 1 ≤ (h:ℝ)*lo) :
    clusterWindowProbability G p x lo hi ≤ 2*markedConnectionPolynomial G
      (incidentSupport G hloc (finite_reachBall hloc x hi).toFinset) x h p := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  let f (ω : Set E) := 1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard
  let A := {ω | ClusterWindow G x lo hi ω}
  have hA : MeasurableSet A := measurableSet_clusterWindow G hloc x lo hi
  have hf : Integrable f (law p) := integrable_finite_local Q p _
    (by intro ω; simp only [f,Set.inter_assoc,Set.inter_self])
  have hnon (ω : Set E) : 0 ≤ f ω := by
    apply sub_nonneg.mpr
    exact pow_le_one₀ (sub_nonneg.mpr h.2.2) (by linarith [h.2.1])
  have hbound (ω : Set E) : A.indicator (fun _ => (1:ℝ)/2) ω ≤ f ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have hs : cluster G ω x ⊆ (finite_reachBall hloc x hi).toFinset := by
        simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hω.1 hi hω.2.2.le
      have he := cluster_restrict_incident_of_full G hloc _ ω x hs
      change 1/2 ≤ 1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard
      rw [he]
      apply one_sub_pow_one_sub_ge_half
      exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hω.2.1) h.2.1)
    · rw [Set.indicator_of_notMem hω]
      exact hnon ω
  have hib := integral_mono ((integrable_const _).indicator hA) hf hbound
  rw [integral_indicator_const _ hA] at hib
  have he := markedConnection_integral G Q x h p
  change markedConnectionPolynomial G Q x h p = ∫ ω, f ω ∂law p at he
  rw [←he] at hib
  change (law p).real A ≤ 2*markedConnectionPolynomial G Q x h p
  simp only [smul_eq_mul] at hib
  linarith

end MarkedConnectionLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_FractionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section GhostPowerTransfer
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem sqrt_log_power_bound (h : unitInterval) (hh : 0 < (h:ℝ))
    (a : ℝ) (ha : 1/2 < a) :
    Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a ≤ Real.sqrt (1/(2*a-1)) := by
  let ε := 2*a-1
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hpow := Real.rpow_pos_of_pos hh ε
  have hl := Real.log_le_rpow_div (show 0 ≤ 1/(h:ℝ) by positivity) hε
  rw [Real.div_rpow (by norm_num) hh.le,Real.one_rpow] at hl
  have hpowid : ((h:ℝ)^a)^2 = (h:ℝ)^ε*(h:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hh.le]
    have he : a*(2:ℝ) = ε+1 := by dsimp [ε]; ring
    norm_num only [Nat.cast_ofNat]
    rw [he,Real.rpow_add hh,Real.rpow_one]
  have hbase : (Real.log (1/(h:ℝ))/(h:ℝ))*((h:ℝ)^a)^2 ≤ 1/ε := by
    rw [hpowid]
    calc
      _ = Real.log (1/(h:ℝ))*(h:ℝ)^ε := by field_simp
      _ ≤ ((1/(h:ℝ)^ε)/ε)*(h:ℝ)^ε := mul_le_mul_of_nonneg_right hl hpow.le
      _ = 1/ε := by field_simp
  have hlog : 0 ≤ Real.log (1/(h:ℝ))/(h:ℝ) := div_nonneg
    (Real.log_nonneg ((one_le_div hh).mpr h.2.2)) hh.le
  have hsq := Real.sq_sqrt hlog
  have htarget := Real.sq_sqrt (one_div_pos.mpr hε).le
  have hn := Real.sqrt_nonneg (1/ε)
  change _ ≤ Real.sqrt (1/ε)
  nlinarith [sq_nonneg (Real.sqrt (1/ε)-Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a)]

 

theorem markedConnection_power_transfer (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (p q h : unitInterval) (hq0 : 0 < (q:ℝ)) (hq1 : (q:ℝ) < 1)
    (hp : (q:ℝ)/2 ≤ (p:ℝ)) (hh : 0 < (h:ℝ))
    (a : ℝ) (ha : 1/2 < a) (he : (q:ℝ)-(p:ℝ) = (h:ℝ)^a) :
    markedConnectionPolynomial G Q x h q ≤
      Real.exp ((Real.sqrt ((d:ℝ)/2)/(((q:ℝ)/2)*(1-(q:ℝ)))) *
        Real.sqrt (1/(2*a-1))) * markedConnectionPolynomial G Q x h p := by
  have hp0 : 0 < (p:ℝ) := lt_of_lt_of_le (half_pos hq0) hp
  have hpq : p ≤ q := by change (p:ℝ) ≤ (q:ℝ); linarith [Real.rpow_pos_of_pos hh a]
  have H := markedConnection_transfer G Q x d hd hdeg p q h hp0 hpq hq1 hh
  apply H.trans
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    rw [he]
    have hr : Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ))) ≤
        Real.sqrt ((d:ℝ)/2)/(((q:ℝ)/2)*(1-(q:ℝ))) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos (half_pos hq0) (sub_pos.mpr hq1))
        (mul_le_mul_of_nonneg_right hp (sub_pos.mpr hq1).le)
    calc
      _ = (Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ)))) *
        (Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a) := by ring
      _ ≤ _ := mul_le_mul hr (sqrt_log_power_bound h hh a ha)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg h.2.1 _)) (by positivity)
  · rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg p h _

end GhostPowerTransfer
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section DyadicGhostParameters
attribute [local instance] Classical.propDecidable Classical.decEq

theorem dyadicGhost_pos (j : ℕ) : 0 < (dyadicGhost j:ℝ) := pow_pos (by norm_num) _

theorem dyadicGhost_volume (j : ℕ) : (dyadicGhost j:ℝ)*(2^j:ℕ) = 1 := by
  simp only [dyadicGhost,Nat.cast_pow,Nat.cast_ofNat,←mul_pow]
  norm_num

theorem tendsto_dyadicGhost : Tendsto (fun j => (dyadicGhost j:ℝ)) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem dyadicGhost_rpow (j : ℕ) (t : ℝ) :
    (dyadicGhost j:ℝ)^t = (2:ℝ)^(-t*(j:ℝ)) := by
  change ((1/2:ℝ)^j)^t = _
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [show (1/2:ℝ) = (2:ℝ)^(-1:ℝ) by norm_num,
    ←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

 

theorem eventually_dyadic_backstep (q : unitInterval) (hq : 0 < (q:ℝ))
    (a : ℝ) (ha : 0 < a) (P : unitInterval → Prop) (hP : ∀ᶠ p in nhds q, P p) :
    ∀ᶠ j : ℕ in atTop, ∃ p : unitInterval,
      (q:ℝ)/2 ≤ (p:ℝ) ∧ p < q ∧ (q:ℝ)-(p:ℝ) = (dyadicGhost j:ℝ)^a ∧ P p := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hP
  have ht : Tendsto (fun j => (dyadicGhost j:ℝ)^a) atTop (nhds 0) := by
    simpa only [Real.zero_rpow ha.ne', Function.comp_apply] using!
      (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.comp tendsto_dyadicGhost
  filter_upwards [ht.eventually (eventually_lt_nhds (half_pos hq)),ht.eventually (eventually_lt_nhds hε)] with j hj hεj
  have hz := Real.rpow_pos_of_pos (dyadicGhost_pos j) a
  let p : unitInterval := ⟨(q:ℝ)-(dyadicGhost j:ℝ)^a,⟨by linarith,by linarith [q.2.2]⟩⟩
  refine ⟨p,by dsimp [p]; linarith,by change (q:ℝ)-(dyadicGhost j:ℝ)^a < (q:ℝ); linarith,
    by dsimp [p]; ring,?_⟩
  apply hball
  change |((q:ℝ)-(dyadicGhost j:ℝ)^a)-(q:ℝ)| < ε
  rw [show (q:ℝ)-(dyadicGhost j:ℝ)^a-(q:ℝ) = -(dyadicGhost j:ℝ)^a by ring,abs_neg,abs_of_pos hz]
  exact hεj

end DyadicGhostParameters
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section CriticalDyadicTail
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_dyadic_bound_of_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hq0 : 0 < (pc G:ℝ)) (hq1 : (pc G:ℝ) < 1)
    (C b a : ℝ) (hC : 0 < C) (ha : 1/2 < a)
    (hχ : ∀ᶠ p in nhds (pc G), p < pc G → ∀ x,
      susceptibility G p x ≤ C*((pc G:ℝ)-(p:ℝ))^(-b)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ j : ℕ in atTop, ∀ x,
      clusterWindowProbability G (pc G) x (2^j) (2^(j+1)) ≤
        K*(dyadicGhost j:ℝ)^(1-a*b) := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  let B := Real.exp ((Real.sqrt ((d:ℝ)/2)/(((pc G:ℝ)/2)*(1-(pc G:ℝ)))) * Real.sqrt (1/(2*a-1)))
  have hB : 0 < B := Real.exp_pos _
  refine ⟨2*B*C,by positivity,?_⟩
  filter_upwards [eventually_dyadic_backstep (pc G) hq0 a (by linarith) _ hχ] with j hj
  obtain ⟨p,hp,hpc,he,hχp⟩ := hj
  intro x
  let Q := incidentSupport G hloc (finite_reachBall hloc x (2^(j+1))).toFinset
  have hwin := clusterWindow_le_markedConnection G hloc x (2^j) (2^(j+1)) (pc G) (dyadicGhost j)
    (by rw [dyadicGhost_volume])
  have htra := markedConnection_power_transfer G Q x d hd
    (fun v => (incident_filter_card_le_degree G hloc Q v).trans (hdeg v)) p (pc G) (dyadicGhost j)
    hq0 hq1 hp (dyadicGhost_pos j) a ha he
  have hsub := markedConnection_le_susceptibility G hloc hqt Q x (dyadicGhost j) p hpc
  have hid : (dyadicGhost j:ℝ)*((dyadicGhost j:ℝ)^a)^(-b) = (dyadicGhost j:ℝ)^(1-a*b) := by
    rw [←Real.rpow_mul (dyadicGhost j).2.1]
    calc
      _ = (dyadicGhost j:ℝ)^1*(dyadicGhost j:ℝ)^(a*(-b)) := by rw [Real.rpow_one]
      _ = (dyadicGhost j:ℝ)^(1+a*(-b)) := (Real.rpow_add (dyadicGhost_pos j) _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ 2*markedConnectionPolynomial G Q x (dyadicGhost j) (pc G) := hwin
    _ ≤ 2*(B*markedConnectionPolynomial G Q x (dyadicGhost j) p) :=
      mul_le_mul_of_nonneg_left htra (by norm_num)
    _ ≤ 2*(B*((dyadicGhost j:ℝ)*susceptibility G p x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hB.le) (by norm_num)
    _ ≤ 2*(B*((dyadicGhost j:ℝ)*(C*((pc G:ℝ)-(p:ℝ))^(-b)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hχp hpc x) (dyadicGhost j).2.1) hB.le) (by norm_num)
    _ = 2*B*C*((dyadicGhost j:ℝ)*((dyadicGhost j:ℝ)^a)^(-b)) := by rw [he]; ring
    _ = _ := by rw [hid]

 

theorem critical_power_integrable_of_dyadic_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (α θ K : ℝ) (hα : 0 < α) (hθ : α < θ)
    (hbound : ∀ᶠ j : ℕ in atTop, ∀ x,
      clusterWindowProbability G p x (2^j) (2^(j+1)) ≤ K*(dyadicGhost j:ℝ)^θ) :
    ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) := by
  intro x
  apply integrable_cluster_power_of_dyadic G hloc p x α hα
  have hs : Summable (fun j : ℕ => K*((2:ℝ)^(α-θ))^j) := by
    apply Summable.mul_left
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hθ)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hbound] with j hj
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (clusterWindowProbability_nonneg G p x _ _))]
  calc
    _ ≤ (2:ℝ)^(α*(j:ℝ))*(K*(dyadicGhost j:ℝ)^θ) :=
      mul_le_mul_of_nonneg_left (hj x) (Real.rpow_nonneg (by norm_num) _)
    _ = K*((2:ℝ)^(α-θ))^j := by
      rw [dyadicGhost_rpow,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [show (α-θ)*(j:ℝ) = α*(j:ℝ)+(-θ*(j:ℝ)) by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
      ring

end CriticalDyadicTail
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MomentFromGrowth
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_moment_of_susceptibility_growth [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hq0 : 0 < (pc G:ℝ)) (hq1 : (pc G:ℝ) < 1)
    (hgrowth : ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ p in nhds (pc G), p < pc G → ∀ x,
        susceptibility G p x ≤ C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ)))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :
    ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law (pc G)) := by
  let γ := (1/2-α)/2
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  have hprod : (1/2:ℝ) < (1-γ)*(1-α) := by
    have : 0 < γ*α := mul_pos hγ hα
    dsimp [γ] at *
    nlinarith
  obtain ⟨a,ha,hap⟩ := exists_between hprod
  have hden : 0 < 1-γ := sub_pos.mpr hγ1
  obtain ⟨C,hC,hnear⟩ := hgrowth γ hγ hγ1
  have he : -(1/(1-γ)) = -1/(1-γ) := by ring
  obtain ⟨K,hK,hbound⟩ := critical_dyadic_bound_of_susceptibility G hloc hqt hq0 hq1
    C (1/(1-γ)) a hC ha (by simpa only [he] using hnear)
  apply critical_power_integrable_of_dyadic_bound G hloc (pc G) α (1-a*(1/(1-γ))) K hα _ hbound
  have : a*(1/(1-γ)) < 1-α := by
    rw [mul_one_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [hap]
  linarith

end MomentFromGrowth
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section CriticalRootMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_root_power_integrable_oai
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :
    ∀ i, Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G)) := by
  by_contra hbad
  have hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G)) :=
    not_forall.mp hbad
  obtain ⟨β,hαβ,hβ⟩ := exists_between hα1
  let ε := (1/2-β)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hε1 : ε < 1/2 := by dsimp [ε]; linarith
  have hsmall : β+(1/2+ε) < 1 := by dsimp [ε]; linarith
  have hg := susceptibility_growth_of_divergent_moment G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 < c := Finset.sum_pos (fun i _ => one_div_pos.mpr (hw i)) Finset.univ_nonempty
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  have hall := critical_moment_of_susceptibility_growth G hloc hqt hp₀ hp₁ (by
    intro γ hγ hγ1
    obtain ⟨C,hC,hnear⟩ := hg γ hγ hγ1
    refine ⟨c*C,mul_pos hc hC,?_⟩
    filter_upwards [hnear] with p hp
    intro hpc x
    calc
      _ ≤ c*rootSusceptibility G root weight p :=
        susceptibility_le_rootSusceptibility G root weight (fun i => (hw i).le) hcover c hc.le hmin p x
      _ ≤ c*(C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ))) := mul_le_mul_of_nonneg_left (hp hpc) hc.le
      _ = _ := by ring) α hα hα1
  obtain ⟨i,hi⟩ := hdiv
  exact hi (hall (root i))

end CriticalRootMoments
end Percolation


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.critical_root_power_integrable_oai.{u, v, u_1} := @OAI.Percolation.critical_root_power_integrable_oai.{u, v, u_1}
