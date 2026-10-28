-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.susceptibility_upper_of_critical_operator_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:06:37.180693+00:00
-- url     : https://prove2.me/submissions/95964c3b-a591-4e12-a7e8-334ef366dc43

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

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
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

section KernelLimits
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable


theorem finiteEmbedding_dense : DenseRange (finiteEmbedding (V := V)) := by
  intro f
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) f)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ y ∈ s, Finsupp.single y (f y), ?_⟩
  simp



end KernelLimits

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Sprinkling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

section Schur
attribute [local instance] Classical.propDecidable

 
theorem exists_operator_of_row_column_bound (U : V → V → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hU : ∀ x y, 0 ≤ U x y)
    (hrow : ∀ x (s : Finset V), ∑ y ∈ s, U x y ≤ D)
    (hcol : ∀ y (s : Finset V), ∑ x ∈ s, U x y ≤ D) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ D ∧
      ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ) := by
  have hentry (x y : V) : U x y ≤ D := by simpa using hrow x {y}
  have hcm (y : V) : Memℓp (fun x => (U x y : ℂ)) 2 := by
    apply (memℓp_gen_iff'' (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    refine ⟨D^2, sq_nonneg _, fun s => ?_⟩
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    calc
      ∑ x ∈ s, U x y ^ 2 ≤ ∑ x ∈ s, D * U x y := by
        apply Finset.sum_le_sum
        intro x _
        nlinarith [hentry x y, hU x y]
      _ = D * ∑ x ∈ s, U x y := by rw [Finset.mul_sum]
      _ ≤ D * D := mul_le_mul_of_nonneg_left (hcol y s) hD
      _ = D^2 := by ring
  let col (y : V) : Hilbert V := ⟨fun x => (U x y : ℂ), hcm y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hn (f : V →₀ ℂ) : ‖L f‖ ≤ D * ‖finiteEmbedding f‖ := by
    apply lp.norm_le_of_forall_sum_le (by norm_num)
      (mul_nonneg hD (norm_nonneg _))
    intro s
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hpoint (x : V) : ‖L f x‖^2 ≤ D * ∑ y ∈ f.support, ‖f y‖^2 * U x y := by
      have hn0 : 0 ≤ ∑ y ∈ f.support, ‖f y‖ * U x y :=
        Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (hU x y)
      have hn1 : ‖L f x‖ ≤ ∑ y ∈ f.support, ‖f y‖ * U x y := by
        simp only [L, Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum,
          Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro y _
        simp [col, abs_of_nonneg (hU x y)]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul f.support
        (f := fun y => U x y) (g := fun y => ‖f y‖^2 * U x y)
        (r := fun y => ‖f y‖ * U x y)
        (fun y _ => hU x y)
        (fun y _ => mul_nonneg (sq_nonneg _) (hU x y))
        (fun y _ => by nlinarith)
      exact (sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn1).trans
        (hcs.trans (mul_le_mul_of_nonneg_right (hrow x f.support)
          (Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hU x y))))
    calc
      ∑ x ∈ s, ‖L f x‖^2 ≤ ∑ x ∈ s, D * ∑ y ∈ f.support, ‖f y‖^2 * U x y :=
        Finset.sum_le_sum fun x _ => hpoint x
      _ = D * ∑ y ∈ f.support, ‖f y‖^2 * ∑ x ∈ s, U x y := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ ≤ D * ∑ y ∈ f.support, ‖f y‖^2 * D := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hcol y s) (sq_nonneg _)
      _ = D^2 * ∑ y ∈ f.support, ‖finiteEmbedding f y‖^2 := by
        simp only [finiteEmbedding_apply, ← Finset.sum_mul]
        ring
      _ ≤ D^2 * ‖finiteEmbedding f‖^2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
            (finiteEmbedding f) f.support)
      _ = (D * ‖finiteEmbedding f‖)^2 := by ring
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense hD hn, ?_⟩
  intro x y
  have he := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨D, hn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at he
  rw [he]
  simp [L, col]

end Schur

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
    · simp only [hreg,if_true,one_mul]
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
    · simp only [hreg,if_true]
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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Moments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

 
theorem cluster_union_external (G : BondGraph V E) (ω η : Set E) (x : V) (W : Set V)
    (hω : cluster G ω x ⊆ W) (hη : η ⊆ internalEdges G Wᶜ) :
    cluster G (ω ∪ η) x = cluster G ω x := by
  apply Set.Subset.antisymm
  · intro y hy
    induction hy with
    | refl => exact conn_refl G ω x
    | @tail a b hxa hab ih =>
      obtain ⟨e,he,heq⟩ := hab
      rcases he with he | he
      · exact ih.tail ⟨e,he,heq⟩
      · exact (((mem_internalEdges_of_ends G _ e a b heq).mp (hη he)).1 (hω ih)).elim
  · exact fun _ h => conn_mono G Set.subset_union_left h

 
theorem cluster_union_external_eq_iff (G : BondGraph V E) (ω η : Set E)
    (x : V) (W : Set V) (hη : η ⊆ internalEdges G Wᶜ) :
    cluster G (ω ∪ η) x = W ↔ cluster G ω x = W := by
  constructor
  · intro h
    have hω : cluster G ω x ⊆ W := fun y hy => h ▸ conn_mono G Set.subset_union_left hy
    rwa [cluster_union_external G ω η x W hω hη] at h
  · intro h
    rw [cluster_union_external G ω η x W (h ▸ Set.Subset.rfl) hη,h]


end MarkedRecursion

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

section GoodnessGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incidentBonds_card_le (G : BondGraph V E) (Q : Finset E) (W : Finset V) (d : ℕ)
    (hd : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    (incidentBonds G Q W).card ≤ d*W.card := by
  calc
    _ ≤ ∑ v ∈ W, (Q.filter fun e => v ∈ G e).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ W, d := Finset.sum_le_sum fun _ _ => hd _
    _ = _ := by simp [Nat.mul_comm]



end GoodnessGeometry

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Spectral
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


theorem levelIndicator_eq (a : ℝ) :
    levelIndicator a = Set.indicator (Set.Ico 0 a) (fun _ => (1:ℝ)) := by
  funext t
  simp [levelIndicator, Set.indicator_apply, Set.mem_Ico]

theorem integrable_levelIndicator (a : ℝ) : Integrable (levelIndicator a) := by
  rw [levelIndicator_eq]
  exact (integrableOn_const (isCompact_Icc.measure_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc 0 a)).mono_set
      Set.Ico_subset_Icc_self |>.integrable_indicator measurableSet_Ico

theorem integral_levelIndicator {a : ℝ} (ha : 0 ≤ a) :
    ∫ t, levelIndicator a t = a := by
  rw [levelIndicator_eq, integral_indicator measurableSet_Ico]
  simp [ha]

theorem abs_sub_levelIndicator {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun t => |levelIndicator a t - levelIndicator b t|) =
      Set.indicator (Set.Ico (min a b) (max a b)) (fun _ => (1:ℝ)) := by
  funext t
  rcases le_total a b with hab | hba
  · simp only [min_eq_left hab, max_eq_right hab, Set.indicator_apply, Set.mem_Ico,
      levelIndicator]
    by_cases ht : 0 ≤ t
    · by_cases hta : t < a
      · have htb : t < b := hta.trans_le hab
        have hna : ¬a ≤ t := not_le.mpr hta
        simp [ht,hta,htb,hna]
      · by_cases htb : t < b <;> simp [ht,hta,htb,le_of_not_gt hta]
    · have hna : ¬a ≤ t := fun h => ht (ha.trans h)
      simp [ht,hna]
  · simp only [min_eq_right hba, max_eq_left hba, Set.indicator_apply, Set.mem_Ico,
      levelIndicator]
    by_cases ht : 0 ≤ t
    · by_cases htb : t < b
      · have hta : t < a := htb.trans_le hba
        have hnb : ¬b ≤ t := not_le.mpr htb
        simp [ht,hta,htb,hnb]
      · by_cases hta : t < a <;> simp [ht,hta,htb,le_of_not_gt htb]
    · have hnb : ¬b ≤ t := fun h => ht (hb.trans h)
      simp [ht,hnb]

theorem integrable_abs_sub_levelIndicator (a b : ℝ) :
    Integrable (fun t => |levelIndicator a t - levelIndicator b t|) :=
  ((integrable_levelIndicator a).sub (integrable_levelIndicator b)).abs

theorem integral_abs_sub_levelIndicator {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ t, |levelIndicator a t - levelIndicator b t| = |a-b| := by
  rw [abs_sub_levelIndicator ha hb, integral_indicator measurableSet_Ico]
  simp only [setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Ico_of_le min_le_max]
  exact (max_sub_min_eq_abs a b).trans (abs_sub_comm _ _)

 
theorem finite_coarea_lower_bound {α : Type*} (S : Finset α) (P : Finset (α × α))
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (hout : ∀ x ∉ S, f x = 0) (h : ℝ)
    (hcut : ∀ A : Finset α, A ⊆ S →
      h * A.card ≤ ∑ e ∈ P,
        |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)|) :
    h * ∑ x ∈ S, f x ≤ ∑ e ∈ P, |f e.1 - f e.2| := by
  let F : ℝ → ℝ := fun t => h * ∑ x ∈ S, levelIndicator (f x) t
  let J : ℝ → ℝ := fun t => ∑ e ∈ P,
    |levelIndicator (f e.1) t - levelIndicator (f e.2) t|
  have hF : Integrable F :=
    (integrable_finsetSum S (fun x _ => integrable_levelIndicator (f x))).const_mul h
  have hJ : Integrable J :=
    integrable_finsetSum P (fun e _ => integrable_abs_sub_levelIndicator _ _)
  have hle : ∀ t, F t ≤ J t := by
    intro t
    let A := S.filter (fun x => 0 ≤ t ∧ t < f x)
    have hi (x : α) : levelIndicator (f x) t = if x ∈ A then (1:ℝ) else 0 := by
      by_cases hx : x ∈ S
      · simp [A,levelIndicator,hx]
      · rw [hout x hx]
        have hz : ¬(0 ≤ t ∧ t < 0) := fun ht => (not_lt_of_ge ht.1) ht.2
        simp [A,levelIndicator,hx,hz]
    have hc : ∑ x ∈ S, levelIndicator (f x) t = (A.card : ℝ) := by
      simp [levelIndicator,A,Finset.sum_boole]
    dsimp [F,J]
    rw [hc]
    simpa only [hi] using hcut A (Finset.filter_subset _ _)
  have H := integral_mono hF hJ hle
  dsimp [F,J] at H
  rw [integral_const_mul, integral_finsetSum _
    (fun x _ => integrable_levelIndicator (f x)), integral_finsetSum _
    (fun e _ => integrable_abs_sub_levelIndicator _ _)] at H
  simpa only [integral_levelIndicator (hf _),
    integral_abs_sub_levelIndicator (hf _) (hf _)] using H

theorem hV_mul_card_le (G : BondGraph V E) (A : Finset V) :
    hV G * A.card ≤ (vertexBoundary G A).ncard := by
  by_cases hA : A.Nonempty
  · have hb : BddBelow {r : ℝ | ∃ B : Finset V, B.Nonempty ∧
        r = (vertexBoundary G B).ncard / (B.card : ℝ)} := by
      refine ⟨0, ?_⟩
      rintro _ ⟨B,_,rfl⟩
      positivity
    have hh : hV G ≤ (vertexBoundary G A).ncard / (A.card : ℝ) :=
      csInf_le hb ⟨A,hA,rfl⟩
    exact (le_div_iff₀ (by exact_mod_cast hA.card_pos)).mp hh
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

theorem finite_vertexBoundary (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) : (vertexBoundary G A).Finite := by
  apply (A.finite_toSet.biUnion (fun x _ => finite_neighbors hloc x)).subset
  rintro y ⟨_,x,hx,hxy⟩
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,hxy⟩⟩

theorem subset_neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) : S ⊆ neighborClosure G hloc S := Finset.subset_union_left

theorem neighbor_mem_neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) {x y : V} (hx : x ∈ S) (hxy : Adj G x y) :
    y ∈ neighborClosure G hloc S := by
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,(mem_neighbors ..).mpr hxy⟩)

theorem sum_swap_finiteAdjPairs (G : BondGraph V E) (K : Finset V)
    (f : V × V → ℝ) :
    ∑ e ∈ finiteAdjPairs G K, f e.swap = ∑ e ∈ finiteAdjPairs G K, f e := by
  apply Finset.sum_bij (fun e _ => e.swap)
  · intro e he
    rw [mem_finiteAdjPairs] at he ⊢
    exact ⟨he.2.1,he.1,adj_symm G he.2.2⟩
  · intro a _ b _ h
    exact Prod.swap_injective h
  · intro b hb
    refine ⟨b.swap,?_,Prod.swap_swap b⟩
    rw [mem_finiteAdjPairs] at hb ⊢
    exact ⟨hb.2.1,hb.1,adj_symm G hb.2.2⟩
  · intros; rfl

 
theorem finiteAdjPairs_cut_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (S A : Finset V) (hAS : A ⊆ S) :
    (2 * hV G) * A.card ≤ ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S),
      |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| := by
  let K := neighborClosure G hloc S
  let P := finiteAdjPairs G K
  let R := P.filter (fun e => e.1 ∈ A ∧ e.2 ∉ A)
  have hs : (finite_vertexBoundary G hloc A).toFinset ⊆ R.image Prod.snd := by
    intro y hy
    have hy' : y ∈ vertexBoundary G A := by simpa using hy
    obtain ⟨hyA,x,hx,hxy⟩ := hy'
    apply Finset.mem_image.mpr
    refine ⟨(x,y),Finset.mem_filter.mpr ⟨?_,hx,hyA⟩,rfl⟩
    exact (mem_finiteAdjPairs G K (x,y)).mpr
      ⟨subset_neighborClosure G hloc S (hAS hx),
        neighbor_mem_neighborClosure G hloc S (hAS hx) hxy,hxy⟩
  have hc : (vertexBoundary G A).ncard ≤ R.card := by
    rw [Set.ncard_eq_toFinset_card (vertexBoundary G A) (finite_vertexBoundary G hloc A)]
    exact (Finset.card_le_card hs).trans (Finset.card_image_le)
  have hcross : hV G * A.card ≤ ∑ e ∈ P,
      if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0 := by
    rw [Finset.sum_boole]
    exact (hV_mul_card_le G A).trans (by exact_mod_cast hc)
  have hsplit : ∑ e ∈ P,
      |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| =
      2 * ∑ e ∈ P, if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0 := by
    have ht (e : V × V) :
        |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| =
        (if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0) +
        (if e.2 ∈ A ∧ e.1 ∉ A then (1:ℝ) else 0) := by
      by_cases h₁ : e.1 ∈ A <;> by_cases h₂ : e.2 ∈ A <;> simp [h₁,h₂]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    have he := sum_swap_finiteAdjPairs G K
      (fun e => if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0)
    change (∑ e ∈ P, if e.2 ∈ A ∧ e.1 ∉ A then (1:ℝ) else 0) = _ at he
    rw [he]
    ring
  change _ ≤ ∑ e ∈ P, _
  rw [hsplit]
  nlinarith

 
theorem bondGraph_coarea (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hout : ∀ x ∉ S, f x = 0) :
    (2 * hV G) * ∑ x ∈ S, f x ≤
      ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), |f e.1 - f e.2| :=
  finite_coarea_lower_bound S _ f hf hout _
    (fun A hAS => finiteAdjPairs_cut_bound G hloc S A hAS)

theorem neighbors_card_le_degree (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    (neighbors G hloc x).card ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  let p : Step G x → {y // y ∈ neighbors G hloc x} :=
    fun d => ⟨d.val.2, (mem_neighbors G hloc x d.val.2).mpr ⟨d.val.1,d.property⟩⟩
  have hp : Function.Surjective p := by
    intro y
    obtain ⟨e,he⟩ := (mem_neighbors G hloc x y.val).mp y.property
    exact ⟨⟨(e,y.val),he⟩,Subtype.ext rfl⟩
  simpa only [degree,Nat.card_eq_fintype_card,Fintype.card_coe] using
    Fintype.card_le_of_surjective p hp

theorem finiteAdjPairs_source_sum_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (K : Finset V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ e ∈ finiteAdjPairs G K, f e.1 ≤ (D:ℝ) * ∑ x ∈ K, f x := by
  rw [Finset.mul_sum]
  simp only [finiteAdjPairs,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_le_sum
  intro x _
  have hc : (K.filter (fun y => Adj G x y)).card ≤ D := by
    apply (Finset.card_le_card ?_).trans ((neighbors_card_le_degree G hloc x).trans (hD x))
    intro y hy
    exact (mem_neighbors G hloc x y).mpr (Finset.mem_filter.mp hy).2
  calc
    (∑ y ∈ K, if Adj G x y then f x else 0) =
        ((K.filter (fun y => Adj G x y)).card:ℝ) * f x := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (D:ℝ) * f x := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf x)

theorem finiteAdjPairs_square_sum_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (S : Finset V) (f : V → ℝ)
    (hout : ∀ x ∉ S, f x = 0) :
    ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1 + f e.2)^2 ≤
      4 * (D:ℝ) * ∑ x ∈ S, (f x)^2 := by
  let K := neighborClosure G hloc S
  let P := finiteAdjPairs G K
  have hs : ∑ x ∈ K, (f x)^2 = ∑ x ∈ S, (f x)^2 := by
    symm
    apply Finset.sum_subset (subset_neighborClosure G hloc S)
    intro x _ hx
    simp [hout x hx]
  have hfirst := finiteAdjPairs_source_sum_le G hloc D hD K (fun x => (f x)^2) (fun _ => sq_nonneg _)
  rw [hs] at hfirst
  have hsecond := sum_swap_finiteAdjPairs G K (fun e => (f e.1)^2)
  change (∑ e ∈ P, (f e.2)^2) = ∑ e ∈ P, (f e.1)^2 at hsecond
  calc
    (∑ e ∈ P, (f e.1 + f e.2)^2) ≤ ∑ e ∈ P, (2*(f e.1)^2+2*(f e.2)^2) := by
      apply Finset.sum_le_sum
      intro e _
      nlinarith [sq_nonneg (f e.1 - f e.2)]
    _ = 4 * ∑ e ∈ P, (f e.1)^2 := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hsecond]
      ring
    _ ≤ 4 * (D:ℝ) * ∑ x ∈ S, (f x)^2 := by
      nlinarith

 

theorem bondGraph_cheeger_energy (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (S : Finset V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hout : ∀ x ∉ S, f x = 0) :
    (hV G)^2 * ∑ x ∈ S, (f x)^2 ≤
      (D:ℝ) * ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 := by
  let P := finiteAdjPairs G (neighborClosure G hloc S)
  let N := ∑ x ∈ S, (f x)^2
  let E := ∑ e ∈ P, (f e.1-f e.2)^2
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := bondGraph_coarea G hloc S (fun x => (f x)^2)
    (fun _ => sq_nonneg _) (fun x hx => by rw [hout x hx]; norm_num)
  have ht (e : V × V) : |(f e.1)^2-(f e.2)^2| = |f e.1-f e.2| * (f e.1+f e.2) := by
    rw [show (f e.1)^2-(f e.2)^2 = (f e.1-f e.2)*(f e.1+f e.2) by ring,
      abs_mul,abs_of_nonneg (add_nonneg (hf _) (hf _))]
  simp_rw [ht] at hc
  have hc' : ((2*hV G)*N)^2 ≤
      (∑ e ∈ P, |f e.1-f e.2| * (f e.1+f e.2))^2 := by
    exact sq_le_sq₀ (by positivity) (Finset.sum_nonneg (fun e _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (hf _) (hf _)))) |>.mpr hc
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun e => |f e.1-f e.2|) (fun e => f e.1+f e.2)
  simp only [sq_abs] at hcs
  have hbound := finiteAdjPairs_square_sum_le G hloc D hD S f hout
  have hall : ((2*hV G)*N)^2 ≤ E*(4*(D:ℝ)*N) :=
    (hc'.trans hcs).trans (mul_le_mul_of_nonneg_left hbound hE)
  change (hV G)^2*N ≤ (D:ℝ)*E
  rcases hN.eq_or_lt with hzero | hpos
  · rw [←hzero,mul_zero]
    positivity
  · apply (mul_le_mul_iff_left₀ (by positivity : 0 < 4*N)).mp
    nlinarith [hall]

end IsoperimetricEnergy

section FiniteQuadraticForms
attribute [local instance] Classical.propDecidable

 theorem kernel_finiteEmbedding (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (f : V →₀ ℂ) (x : V) :
    A (finiteEmbedding f) x = ∑ y ∈ f.support, f y * (U x y : ℂ) := by
  simp only [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul]
  change (∑ y ∈ f.support, f y • A (lp.single 2 y (1 : ℂ))) x = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    hA, smul_eq_mul]

 theorem symmetric_of_symmetric_kernel (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (hU : ∀ x y, U x y = U y x) : A.toLinearMap.IsSymmetric := by
  apply finiteEmbedding_dense.induction_on₂
    (p := fun f g => inner ℂ (A f) g = inner ℂ f (A g))
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f g
    simp only [finiteEmbedding_inner_left, finiteEmbedding_inner_right,
      kernel_finiteEmbedding A U hA, map_sum, map_mul, RCLike.star_def,
      Complex.conj_ofReal]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hU y x]
    ring

 theorem norm_le_of_finite_quadratic (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : A.toLinearMap.IsSymmetric) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f : V →₀ ℂ,
      |(inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f)).re| ≤
        C * ‖finiteEmbedding f‖^2) : ‖A‖ ≤ C := by
  have hall (f : Hilbert V) : |(inner ℂ (A f) f).re| ≤ C * ‖f‖^2 := by
    exact finiteEmbedding_dense.induction_on f
      (p := fun g => |(inner ℂ (A g) g).re| ≤ C * ‖g‖^2)
      (isClosed_le (by fun_prop) (by fun_prop)) h
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  apply ciSup_le
  intro f
  by_cases hf : f = 0
  · simp [hf, hC]
  · rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_sq]
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mpr (hall f)

 theorem abs_inner_kernel_finite_le (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (hU : ∀ x y, 0 ≤ U x y) (f : V →₀ ℂ) :
    |(inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f)).re| ≤
      ∑ x ∈ f.support, ∑ y ∈ f.support, ‖f x‖ * ‖f y‖ * U x y := by
  change |RCLike.re (inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f))| ≤ _
  rw [inner_re_symm]
  apply (Complex.abs_re_le_norm _).trans
  rw [finiteEmbedding_inner_left]
  simp_rw [kernel_finiteEmbedding A U hA, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro y _
  simp [abs_of_nonneg (hU x y), mul_assoc]

end FiniteQuadraticForms

section SymmetricWalk
attribute [local instance] Classical.propDecidable



 theorem walkKernel_symmetric (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : walkKernel G hloc a x y = walkKernel G hloc a y x := by
  have ha : Adj G x y ↔ Adj G y x := ⟨adj_symm G,adj_symm G⟩
  by_cases h : x = y
  · subst y; rfl
  · simp [walkKernel,h,Ne.symm h,ha]

 theorem walkKernel_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (x y : V) : 0 ≤ walkKernel G hloc a x y := by
  have hn : ((neighbors G hloc x).card : ℝ) ≤ D := by
    exact_mod_cast (neighbors_card_le_degree G hloc x).trans (hD x)
  have hh : 0 ≤ 1-a*(neighbors G hloc x).card := by nlinarith
  unfold walkKernel
  split_ifs <;> positivity

 theorem walkKernel_row_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x : V) :
    ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y = 1 := by
  let N := neighbors G hloc x
  have hf : (insert x N).filter (fun y => Adj G x y) = N := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    rw [mem_neighbors]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr h,h⟩⟩
  simp only [walkKernel, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_insert_self,if_true]
  rw [← Finset.sum_filter,hf]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [N]
  ring

 theorem walkKernel_row_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (x : V) (S : Finset V) : ∑ y ∈ S, walkKernel G hloc a x y ≤ 1 := by
  let N := insert x (neighbors G hloc x)
  calc
    ∑ y ∈ S, walkKernel G hloc a x y ≤ ∑ y ∈ S ∪ N, walkKernel G hloc a x y :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun y _ _ => walkKernel_nonneg G hloc D hD a ha haD x y)
    _ = ∑ y ∈ N, walkKernel G hloc a x y := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro y _ hy
      have hxy : x ≠ y := by intro h; subst y; exact hy (by simp [N])
      have hna : ¬ Adj G x y := by intro h; exact hy (by simp [N,h])
      simp [walkKernel,hxy,hna]
    _ = 1 := walkKernel_row_sum G hloc a x

 theorem exists_walk_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1) :
    ∃ P : Hilbert V →L[ℂ] Hilbert V, ‖P‖ ≤ 1 ∧
      P.toLinearMap.IsSymmetric ∧
      ∀ x y, P (lp.single 2 y (1 : ℂ)) x = (walkKernel G hloc a x y : ℂ) := by
  obtain ⟨P,hP,hK⟩ := exists_operator_of_row_column_bound (walkKernel G hloc a) 1
    zero_le_one (walkKernel_nonneg G hloc D hD a ha haD)
    (walkKernel_row_bound G hloc D hD a ha haD) (by
      intro y S
      simp_rw [walkKernel_symmetric G hloc a]
      exact walkKernel_row_bound G hloc D hD a ha haD y S)
  exact ⟨P,hP,symmetric_of_symmetric_kernel P _ hK (walkKernel_symmetric G hloc a),hK⟩

 theorem finiteAdjPairs_sum (G : BondGraph V E) (K : Finset V) (f : V × V → ℝ) :
    (∑ e ∈ finiteAdjPairs G K, f e) =
      ∑ x ∈ K, ∑ y ∈ K, if Adj G x y then f (x,y) else 0 := by
  simp [finiteAdjPairs,Finset.sum_filter,Finset.sum_product]

 theorem finiteAdjPairs_source_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), f e.1) =
      ∑ x ∈ S, ((neighbors G hloc x).card : ℝ) * f x := by
  let K := neighborClosure G hloc S
  rw [finiteAdjPairs_sum]
  have he (x : V) (hx : x ∈ S) :
      K.filter (fun y => Adj G x y) = neighbors G hloc x := by
    ext y
    simp only [Finset.mem_filter,mem_neighbors]
    exact ⟨fun h => h.2,fun h => ⟨neighbor_mem_neighborClosure G hloc S hx h,h⟩⟩
  have hout' : ∀ x ∉ S, (∑ y ∈ K, if Adj G x y then f x else 0) = 0 := by
    intro x hx; simp [hout x hx]
  change (∑ x ∈ K, ∑ y ∈ K, if Adj G x y then f x else 0) = _
  rw [← Finset.sum_subset (subset_neighborClosure G hloc S)
    (fun x _ hx => hout' x hx)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter,he x hx]
  simp

 theorem finiteAdjPairs_product_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), f e.1 * f e.2) =
      ∑ x ∈ S, ∑ y ∈ S, if Adj G x y then f x*f y else 0 := by
  rw [finiteAdjPairs_sum]
  have hs := subset_neighborClosure G hloc S
  calc
    _ = ∑ x ∈ S, ∑ y ∈ neighborClosure G hloc S,
        if Adj G x y then f x*f y else 0 := by
      symm; apply Finset.sum_subset hs
      intro x _ hx; simp [hout x hx]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      symm; apply Finset.sum_subset hs
      intro y _ hy; simp [hout y hy]

 theorem walkKernel_energy (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ x ∈ S, ∑ y ∈ S, f x*f y*walkKernel G hloc a x y) =
      ∑ x ∈ S, (f x)^2 - a/2 *
        ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 := by
  let P := finiteAdjPairs G (neighborClosure G hloc S)
  have henergy : (∑ e ∈ P, (f e.1-f e.2)^2) =
      2*(∑ x ∈ S, (neighbors G hloc x).card * (f x)^2) -
      2*(∑ x ∈ S, ∑ y ∈ S, if Adj G x y then f x*f y else 0) := by
    have hs := sum_swap_finiteAdjPairs G (neighborClosure G hloc S)
      (fun e => (f e.1)^2)
    change (∑ e ∈ P,(f e.2)^2) = (∑ e ∈ P,(f e.1)^2) at hs
    have hfirst := finiteAdjPairs_source_sum G hloc S (fun x => (f x)^2)
      (fun x hx => by rw [hout x hx]; norm_num)
    calc
      _ = (∑ e ∈ P, (f e.1)^2) + (∑ e ∈ P,(f e.2)^2) -
          2*(∑ e ∈ P,f e.1*f e.2) := by
        simp_rw [sub_sq]
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
        simp_rw [mul_assoc,← Finset.mul_sum]
        ring
      _ = _ := by rw [hs,hfirst,finiteAdjPairs_product_sum G hloc S f hout]; ring
  rw [henergy]
  have hpoint (x : V) (hx : x ∈ S) :
      (∑ y ∈ S, f x*f y*walkKernel G hloc a x y) =
        (f x)^2 - a*((neighbors G hloc x).card*(f x)^2) +
         a*(∑ y ∈ S, if Adj G x y then f x*f y else 0) := by
    simp only [walkKernel,mul_add,Finset.sum_add_distrib]
    have hi : (∑ y ∈ S, f x*f y*(if x=y then 1-a*(neighbors G hloc x).card else 0)) =
        (f x)^2*(1-a*(neighbors G hloc x).card) := by
      simp_rw [mul_ite,mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [hx,if_true]
      ring
    rw [hi,Finset.mul_sum]
    have hj : (∑ y ∈ S, f x*f y*(if Adj G x y then a else 0)) =
        ∑ y ∈ S, a*(if Adj G x y then f x*f y else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> ring
    rw [hj]
    ring
  simp_rw [Finset.sum_congr rfl hpoint,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

 

theorem walkKernel_quadratic_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hDp : 0 < D) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 ≤ a) (S : Finset V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hout : ∀ x ∉ S, f x = 0) :
    (∑ x ∈ S, ∑ y ∈ S, f x*f y*walkKernel G hloc a x y) ≤
      (1 - a*(hV G)^2/(2*D)) * ∑ x ∈ S, (f x)^2 := by
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have hc := bondGraph_cheeger_energy G hloc hh D hD S f hf hout
  have he : ((hV G)^2 * ∑ x ∈ S, (f x)^2)/(D:ℝ) ≤
      ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 :=
    (div_le_iff₀ hDp').mpr (by simpa only [mul_comm] using hc)
  rw [walkKernel_energy G hloc a S f hout]
  calc
    _ ≤ (∑ x ∈ S, (f x)^2) - a/2 *
        (((hV G)^2 * ∑ x ∈ S, (f x)^2)/(D:ℝ)) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left he (by positivity)) _
    _ = _ := by ring

 

theorem walk_operator_norm_lt_one (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hDp : 0 < D) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 < a) (haD : a*D ≤ 1)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ)) :
    ‖P‖ < 1 := by
  let C := max 0 (1-a*(hV G)^2/(2*D))
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have hC : 0 ≤ C := le_max_left _ _
  have hC1 : C < 1 := by
    apply max_lt (by norm_num)
    have : 0 < a*(hV G)^2/(2*D) := by positivity
    linarith
  have hn : ‖P‖ ≤ C := by
    apply norm_le_of_finite_quadratic P
      (symmetric_of_symmetric_kernel P _ hP (walkKernel_symmetric G hloc a)) C hC
    intro f
    calc
      _ ≤ ∑ x ∈ f.support, ∑ y ∈ f.support, ‖f x‖*‖f y‖*walkKernel G hloc a x y :=
        abs_inner_kernel_finite_le P _ hP (walkKernel_nonneg G hloc D hD a ha.le haD) f
      _ ≤ (1-a*(hV G)^2/(2*D)) * ∑ x ∈ f.support, ‖f x‖^2 :=
        walkKernel_quadratic_bound G hloc hh D hDp hD a ha.le f.support
          (fun x => ‖f x‖) (fun _ => norm_nonneg _) (by
            intro x hx; simp [Finsupp.notMem_support_iff.mp hx])
      _ ≤ C * ∑ x ∈ f.support, ‖f x‖^2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      _ = C * ‖finiteEmbedding f‖^2 := by rw [finiteEmbedding_norm_sq]
  exact hn.trans_lt hC1

 

theorem exists_strict_walk_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) :
    ∃ (D : ℕ) (P : Hilbert V →L[ℂ] Hilbert V), 0 < D ∧
      (∀ x, degree G x ≤ D) ∧ ‖P‖ < 1 ∧ P.toLinearMap.IsSymmetric ∧
      ∀ x y, P (lp.single 2 y (1:ℂ)) x =
        (walkKernel G hloc (1/(2*(D:ℝ))) x y : ℂ) := by
  obtain ⟨D,hDp,hD⟩ := exists_degree_bound G hqt
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have ha : 0 < (1:ℝ)/(2*D) := by positivity
  have haD : (1:ℝ)/(2*D)*D ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  obtain ⟨P,_,hPs,hP⟩ := exists_walk_operator G hloc D hD _ ha.le haD
  exact ⟨D,P,hDp,hD,walk_operator_norm_lt_one G hloc hh D hDp hD _ ha haD P hP,hPs,hP⟩

end SymmetricWalk

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable

theorem operator_kernel_hasSum (A : Hilbert V →L[ℂ] Hilbert V) (f : Hilbert V) (x : V) :
    HasSum (fun y => matrixCoeff A x y * f y) (A f x) := by
  have h := ((lp.evalCLM ℂ (fun _ : V => ℂ) 2 x).comp A).hasSum
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) f)
  change HasSum (fun y => A (lp.single 2 y (f y)) x) (A f x) at h
  have heq : (fun y : V => A (lp.single 2 y (f y)) x) =
      (fun y => matrixCoeff A x y * f y) := by
    funext y
    have he : lp.single (E := fun _ : V => ℂ) 2 y (f y) =
        f y • lp.single 2 y (1:ℂ) := by
      rw [← lp.single_smul]; simp
    simp [he, matrixCoeff, mul_comm]
  rw [heq] at h
  exact h

@[simp] theorem matrixCoeff_mul (A B : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (A*B) x y = ∑' z, matrixCoeff A x z * matrixCoeff B z y := by
  exact (operator_kernel_hasSum A (B (lp.single 2 y (1:ℂ))) x).tsum_eq.symm

end InvariantOperatorTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_EndpointKernels
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

theorem measurable_finite_local (Q : Finset E) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Measurable f := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  rw [he]
  exact (measurable_of_finite g).comp (measurable_set_restrict (Q : Set E))

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Amplification
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePathOperator
attribute [local instance] Classical.propDecidable Classical.decEq


namespace PositiveRealMatrix
variable {A H : Hilbert V →L[ℂ] Hilbert V}

theorem mul_hasSum (hA : PositiveRealMatrix A) (H : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    HasSum (fun z => (matrixCoeff A x z).re * (matrixCoeff H z y).re)
      (matrixCoeff (A*H) x y).re := by
  have h := Complex.reCLM.hasSum (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x)
  change HasSum (fun z => (matrixCoeff A x z * matrixCoeff H z y).re)
    (matrixCoeff (A*H) x y).re at h
  simpa only [Complex.mul_re,(hA _ _).1,zero_mul,sub_zero] using h

theorem mul (hA : PositiveRealMatrix A) (hH : PositiveRealMatrix H) :
    PositiveRealMatrix (A*H) := by
  intro x y
  constructor
  · have hs := (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x).summable
    change Summable (fun z => matrixCoeff A x z * matrixCoeff H z y) at hs
    rw [matrixCoeff_mul,Complex.im_tsum hs]
    simp only [Complex.mul_im,(hA _ _).1,(hH _ _).1,mul_zero,zero_mul,add_zero,tsum_zero]
  · rw [← (hA.mul_hasSum H x y).tsum_eq]
    exact tsum_nonneg fun z => mul_nonneg (hA x z).2 (hH z y).2

theorem one : PositiveRealMatrix (1 : Hilbert V →L[ℂ] Hilbert V) := by
  intro x y
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply]
  split_ifs <;> norm_num

theorem pow (hA : PositiveRealMatrix A) (k : ℕ) : PositiveRealMatrix (A^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (one (V := V))
  | succ k ih => rw [pow_succ]; exact ih.mul hA

end PositiveRealMatrix



end PositivePathOperator

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Connections
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

end ClusterWindowLaw
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkPowerSupport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_zero_of_not_step (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) (hxy : x ≠ y) (hadj : ¬ Adj G x y) :
    walkKernel G hloc a x y = 0 := by simp only [walkKernel,ite_eq_right hxy,ite_eq_right hadj,zero_add]

theorem walkKernel_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ) (x : V) :
    HasSum (walkKernel G hloc a x) 1 := by
  rw [← walkKernel_row_sum G hloc a x]
  apply hasSum_sum_of_ne_finset_zero
  intro y hy
  simp only [Finset.mem_insert,mem_neighbors,not_or] at hy
  exact walkKernel_zero_of_not_step G hloc a x y (Ne.symm hy.1) hy.2

theorem walkPower_support (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x y : V) (hy : y ∉ reachBall G x k) : (matrixCoeff (P^k) x y).re = 0 := by
  induction k generalizing y with
  | zero =>
    have he : y ≠ x := by simpa only [reachBall,Set.mem_singleton_iff] using hy
    simp only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right (Ne.symm he),Complex.zero_re]
  | succ k ih =>
    rw [pow_succ,← ((hpos.pow k).mul_hasSum P x y).tsum_eq]
    rw [← tsum_zero]
    apply tsum_congr
    intro z
    by_cases hz : z ∈ reachBall G x k
    · have hzy : z ≠ y := by intro he; subst y; exact hy (Or.inl hz)
      have hadj : ¬ Adj G z y := by
        intro h
        apply hy
        apply Or.inr
        simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
        exact ⟨z,hz,h⟩
      rw [hP,walkKernel_zero_of_not_step G hloc a z y hzy hadj,Complex.ofReal_zero,Complex.zero_re,mul_zero]
    · rw [ih z hz,zero_mul]

theorem walkPower_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x : V) : HasSum (fun y => (matrixCoeff (P^k) x y).re) 1 := by
  induction k with
  | zero =>
    have h : HasSum (fun y : V => if x=y then (1:ℝ) else 0) 1 := by
      exact hasSum_ite_eq' x (1:ℝ)
    simpa only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,apply_ite,Complex.one_re,Complex.zero_re] using h
  | succ k ih =>
    let B := (finite_reachBall hloc x k).toFinset
    have he (y : V) : (matrixCoeff (P^(k+1)) x y).re =
        ∑ z ∈ B, (matrixCoeff (P^k) x z).re * walkKernel G hloc a z y := by
      rw [pow_succ,← ((hpos.pow k).mul_hasSum P x y).tsum_eq]
      simp only [hP,Complex.ofReal_re]
      apply tsum_eq_sum
      intro z hz
      rw [walkPower_support G hloc a P hpos hP k x z (by simpa only [B,Set.Finite.mem_toFinset] using hz),zero_mul]
    have hs := hasSum_sum (s := B) (fun z _ => (walkKernel_hasSum G hloc a z).mul_left (matrixCoeff (P^k) x z).re)
    simp only [mul_one] at hs
    have hr : (∑ z ∈ B, (matrixCoeff (P^k) x z).re) = 1 := by
      rw [← ih.tsum_eq]
      exact (tsum_eq_sum fun z hz => walkPower_support G hloc a P hpos hP k x z
        (by simpa only [B,Set.Finite.mem_toFinset] using hz)).symm
    simpa only [← he,hr] using hs

end WalkPowerSupport

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_ScaleBudget
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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



end ClusterSizeMomentIntegrable

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_Resampling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
open MeasureTheory Filter Topology
section RestrictedConnectionLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conn_finite_exhaustion (G : BondGraph V E) (S : Set E)
    (Q : ℕ → Finset E) (hQ : Monotone Q) (hcover : ∀ e ∈ S, ∃ n, e ∈ Q n)
    {ω : Set E} {x y : V} (h : Conn G (ω ∩ S) x y) :
    ∃ n, Conn G (ω ∩ (Q n : Set E)) x y := by
  induction h with
  | refl => exact ⟨0,conn_refl _ _ _⟩
  | @tail a b hxa hab ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨e,he,hab⟩ := hab
    obtain ⟨m,hm⟩ := hcover e he.2
    refine ⟨max n m,?_⟩
    exact (conn_mono G (Set.inter_subset_inter_right _
      (show (Q n:Set E) ⊆ (Q (max n m):Set E) from hQ (le_max_left n m))) hn).tail
      ⟨e,⟨he.1,hQ (le_max_right n m) hm⟩,hab⟩

theorem finite_connection_polynomial_tendsto (G : BondGraph V E) (S : Set E)
    (Q : ℕ → Finset E) (hQ : Monotone Q) (hsub : ∀ n, (Q n:Set E) ⊆ S)
    (hcover : ∀ e ∈ S, ∃ n, e ∈ Q n) (p : unitInterval) (x y : V) :
    Tendsto (fun n => bernoulliPolynomial (Q n) (fun ω => if Conn G ω x y then (1:ℝ) else 0) p)
      atTop (𝓝 ((law p).real {ω | Conn G (ω ∩ S) x y})) := by
  have he (n : ℕ) : bernoulliPolynomial (Q n) (fun ω => if Conn G ω x y then (1:ℝ) else 0) p =
      (law p).real {ω | Conn G (ω ∩ (Q n:Set E)) x y} :=
    finiteEventPolynomial_restrict (Q n) {ω | Conn G ω x y} p
  simp_rw [he]
  have hm : Monotone (fun n => {ω : Set E | Conn G (ω ∩ (Q n:Set E)) x y}) := by
    intro m n h ω hc
    exact conn_mono G (Set.inter_subset_inter_right _ (show (Q m:Set E) ⊆ (Q n:Set E) from hQ h)) hc
  have hu : (⋃ n, {ω : Set E | Conn G (ω ∩ (Q n:Set E)) x y}) =
      {ω : Set E | Conn G (ω ∩ S) x y} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,hn⟩ => conn_mono G (Set.inter_subset_inter_right _ (hsub n)) hn,
      conn_finite_exhaustion G S Q hQ hcover⟩
  have ht := tendsto_measure_iUnion_atTop (μ := law p) hm
  rw [hu] at ht
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht

theorem restrictedBondExhaustion_mono [Encodable E] (S : Set E) (K : Finset E) :
    Monotone (restrictedBondExhaustion S K) := by
  intro m n h
  exact Finset.union_subset_union (by rfl) (Finset.filter_subset_filter _ (vertexExhaustion_mono h))

theorem restrictedBondExhaustion_cover [Encodable E] (S : Set E) (K : Finset E)
    (e : E) (he : e ∈ S) : ∃ n, e ∈ restrictedBondExhaustion S K n := by
  obtain ⟨n,hn⟩ := subset_vertexExhaustion ({e}:Finset E)
  exact ⟨n,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn (by simp),he⟩)⟩

theorem restrictedBondExhaustion_subset [Encodable E] (S : Set E) (K : Finset E)
    (hK : (K:Set E) ⊆ S) (n : ℕ) : (restrictedBondExhaustion S K n:Set E) ⊆ S := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hK he
  · exact (Finset.mem_filter.mp he).2

end RestrictedConnectionLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedSelectorBound
attribute [local instance] Classical.propDecidable Classical.decEq



theorem restrictedTwoPoint_le (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x y : V) :
    (law p).real {ω | Conn G (ω ∩ S) x y} ≤ twoPoint G p x y := by
  exact measureReal_mono (fun _ h => conn_mono G Set.inter_subset_left h)

theorem summable_restrictedTwoPoint [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (S : Set E) (x : V) :
    Summable (fun y => (law p).real {ω | Conn G (ω ∩ S) x y}) := by
  obtain ⟨C,_,hC⟩ := subcritical_row_bound G hloc hqt p hp
  apply summable_of_sum_le (fun _ => measureReal_nonneg)
  intro F
  exact (Finset.sum_le_sum (fun y _ => restrictedTwoPoint_le G S p x y)).trans (hC x F)

end RestrictedSelectorBound
end Percolation


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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicMaximum
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicMaximizer_spec (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    intrinsicMaximizer G hloc ω x M f ∈ intrinsicBall G ω x M ∧
      ∀ y ∈ intrinsicBall G ω x M, f y ≤ f (intrinsicMaximizer G hloc ω x M f) :=
  Classical.choose_spec (intrinsicBall_exists_max G hloc ω x M f)

theorem intrinsicPotentialMax_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    intrinsicPotentialMax G ω x M f = f (intrinsicMaximizer G hloc ω x M f) := by
  have h := intrinsicMaximizer_spec G hloc ω x M f
  apply IsGreatest.csSup_eq
  exact ⟨⟨_,h.1,rfl⟩,fun _ ⟨y,hy,he⟩ => he ▸ h.2 y hy⟩

theorem le_intrinsicPotentialMax (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) (y : V) (hy : y ∈ intrinsicBall G ω x M) :
    f y ≤ intrinsicPotentialMax G ω x M f := by
  rw [intrinsicPotentialMax_eq G hloc]
  exact (intrinsicMaximizer_spec G hloc ω x M f).2 y hy

end IntrinsicMaximum
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section RestrictedPathPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem restrictedTwoPoint_adj_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) (x y z : V) (e : E)
    (he : G e = s(x,y)) (heS : e ∈ S) :
    (p:ℝ)*(law p).real {ω | Conn G (ω ∩ S) y z} ≤
      (law p).real {ω | Conn G (ω ∩ S) x z} := by
  have h := association_finiteWitness p {ω : Set E | e ∈ ω} {ω | Conn G (ω ∩ S) y z}
    (fun _ _ hω h => hω h)
    (fun _ _ hω h => conn_mono G (Set.inter_subset_inter_left _ hω) h)
    (finiteWitness_edge e) (finiteWitness_inter _ (finiteWitness_conn G y z) S)
  have hp : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
    simpa using finite_open_probability p {e}
  rw [hp] at h
  exact h.trans (measureReal_mono (fun ω hω =>
    conn_trans G _ (Relation.ReflTransGen.single ⟨e,⟨hω.1,heS⟩,he⟩) hω.2))

theorem restrictedTwoPoint_path_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S) (z : V) :
    (p:ℝ)^l.length*(law p).real {ω | Conn G (ω ∩ S) y z} ≤
      (law p).real {ω | Conn G (ω ∩ S) x z} := by
  induction hl with
  | nil => simp
  | @cons x a y l e he ht ih =>
    have hh := mul_le_mul_of_nonneg_left (ih (fun d hd => hS d (List.mem_cons_of_mem _ hd))) p.2.1
    have ha := restrictedTwoPoint_adj_lower G S p x a z e he (hS e (by simp))
    simpa only [List.length_cons,pow_succ',mul_assoc] using hh.trans ha

theorem restrictedSusceptibility_nonneg (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x : V) : 0 ≤ restrictedSusceptibility G S p x :=
  tsum_nonneg (fun _ => measureReal_nonneg)

theorem restrictedSusceptibility_path_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S)
    (hfin : ∀ a, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) a z})) :
    (p:ℝ)^l.length*restrictedSusceptibility G S p y ≤ restrictedSusceptibility G S p x := by
  unfold restrictedSusceptibility
  rw [←tsum_mul_left]
  exact ((hfin y).mul_left _).tsum_le_tsum (restrictedTwoPoint_path_lower G S p hl hS) (hfin x)

 

theorem restrictedSusceptibility_short_path_bound [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) (hp : 0 < (p:ℝ)) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S) (M : ℕ) (hlen : l.length ≤ M)
    (hfin : ∀ a, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) a z})) :
    restrictedSusceptibility G S p y ≤ (p:ℝ)^(-(M:ℤ))*restrictedSusceptibility G S p x := by
  have hh := restrictedSusceptibility_path_lower G S p hl hS hfin
  have hpow : (p:ℝ)^M ≤ (p:ℝ)^l.length :=
    pow_le_pow_of_le_one p.2.1 p.2.2 hlen
  have hbound := (mul_le_mul_of_nonneg_right hpow (restrictedSusceptibility_nonneg G S p y)).trans hh
  rw [zpow_neg,zpow_natCast,←div_eq_inv_mul]
  exact (le_div_iff₀ (pow_pos hp M)).mpr (by simpa only [mul_comm] using hbound)

end RestrictedPathPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortPathsDeletedDomain
attribute [local instance] Classical.propDecidable Classical.decEq



theorem Along.last_entrance {G : BondGraph V E} {x y : V} {l : List E}
    (hl : Along G x l y) (D : Set V) (hy : y ∈ D) :
    (x ∈ D ∧ ∀ e ∈ l, e ∈ internalEdges G D) ∨
      ∃ a b e l₁ l₂, l = l₁ ++ e::l₂ ∧ Along G x l₁ a ∧ G e = s(a,b) ∧
        a ∉ D ∧ b ∈ D ∧ Along G b l₂ y ∧ ∀ d ∈ l₂, d ∈ internalEdges G D := by
  induction hl with
  | nil => exact Or.inl ⟨hy,by simp⟩
  | @cons x z y l e he ht ih =>
    rcases ih hy with ⟨hz,hall⟩ | ⟨a,b,d,l₁,l₂,heq,h₁,hd,ha,hb,h₂,hs⟩
    · by_cases hx : x ∈ D
      · left
        refine ⟨hx,?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact (mem_internalEdges_of_ends G D d x z he).mpr ⟨hx,hz⟩
        · exact hall d hd
      · right
        exact ⟨x,z,e,[],l,rfl,.nil x,he,hx,hz,ht,hall⟩
    · right
      exact ⟨a,b,d,e::l₁,l₂,by simp [heq],.cons e he h₁,hd,ha,hb,h₂,hs⟩

end ShortPathsDeletedDomain
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_KernelMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
section DeletedDomainPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem inducedSusceptibility_nonneg (G : BondGraph V E) (D : Set V)
    (p : unitInterval) (x : V) : 0 ≤ inducedSusceptibility G D p x := by
  unfold inducedSusceptibility
  split_ifs
  · exact restrictedSusceptibility_nonneg G _ p x
  · rfl

theorem deletedBoundaryPotential_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) :
    0 ≤ deletedBoundaryPotential G hloc D p x M := by
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => inducedSusceptibility_nonneg G D p b))

theorem le_deletedBoundaryPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) (a b : V)
    (ha : a ∈ reachBall G x M) (haD : a ∉ D) (hab : Adj G a b) :
    inducedSusceptibility G D p b ≤ deletedBoundaryPotential G hloc D p x M := by
  apply le_trans (Finset.single_le_sum (fun z _ => inducedSusceptibility_nonneg G D p z)
    ((mem_neighbors G hloc a b).mpr hab))
  apply Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun y _ => inducedSusceptibility_nonneg G D p y))
  exact Finset.mem_filter.mpr ⟨(finite_reachBall hloc x M).mem_toFinset.mpr ha,haD⟩

theorem deletedLocalPotential_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (ω : Set E) (x : V) (M : ℕ) :
    0 ≤ deletedLocalPotential G D p ω x M := by
  unfold deletedLocalPotential
  split_ifs
  · rw [intrinsicPotentialMax_eq G hloc]
    exact inducedSusceptibility_nonneg G D p _
  · rfl

 

theorem short_path_deleted_potential_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : Set V)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (ω : Set E) (x y : V) (M : ℕ)
    (l : List E) (hl : Along G x l y) (hlen : l.length ≤ M) (ho : ∀ e ∈ l, e ∈ ω)
    (hfin : ∀ a, Summable (fun z => (law p).real {η | Conn G (η ∩ internalEdges G D) a z})) :
    inducedSusceptibility G D p y ≤ deletedLocalPotential G D p ω x M +
      (p:ℝ)^(-(M:ℤ))*deletedBoundaryPotential G hloc D p x M := by
  have hpM : 0 ≤ (p:ℝ)^(-(M:ℤ)) := zpow_nonneg p.2.1 _
  have hn := deletedLocalPotential_nonneg G hloc D p ω x M
  have hb := deletedBoundaryPotential_nonneg G hloc D p x M
  by_cases hy : y ∈ D
  · rcases hl.last_entrance D hy with ⟨hx,hall⟩ | ⟨a,b,e,l₁,l₂,heq,h₁,he,ha,hbD,h₂,hs⟩
    · have hreach : y ∈ intrinsicBall G (ω ∩ internalEdges G D) x M :=
        ⟨l,hl,hlen,fun e he => ⟨ho e he,hall e he⟩⟩
      have hh := le_intrinsicPotentialMax G hloc _ x M (inducedSusceptibility G D p) y hreach
      change _ ≤ (if x ∈ D then _ else 0) + _
      rw [ite_eq_left hx]
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg hpM hb))
    · have hlen₂ : l₂.length ≤ M := by subst l; simp only [List.length_append,List.length_cons] at hlen; omega
      have hpath := restrictedSusceptibility_short_path_bound G (internalEdges G D) p hp h₂ hs M hlen₂ hfin
      have hχ : inducedSusceptibility G D p y ≤ (p:ℝ)^(-(M:ℤ))*inducedSusceptibility G D p b := by
        simpa only [inducedSusceptibility,ite_eq_left hy,ite_eq_left hbD] using hpath
      have haBall : a ∈ reachBall G x M := reachBall_mono G x
        (show l₁.length ≤ M by subst l; simp only [List.length_append,List.length_cons] at hlen; omega) h₁.mem_reachBall
      exact hχ.trans ((mul_le_mul_of_nonneg_left
        (le_deletedBoundaryPotential G hloc D p x M a b haBall ha ⟨e,he⟩) hpM).trans
          (le_add_of_nonneg_left hn))
  · rw [inducedSusceptibility,ite_eq_right hy]
    exact add_nonneg hn (mul_nonneg hpM hb)

end DeletedDomainPotential
end Percolation


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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_ExteriorMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
section RootSusceptibilityLower
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_rootSusceptibility_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ a : ℝ, 0 < a ∧ ∀ (p : unitInterval), p₀ ≤ (p:ℝ) → p < pc G → ∀ x,
      a*rootSusceptibility G root weight p ≤ susceptibility G p x := by
  have hex (ij : ι × ι) : ∃ l : List E, Along G (root ij.1) l (root ij.2) := by
    obtain ⟨l,hl,_,_⟩ := conn_exists_bond_trail G (conn_univ_of_connected G hconn (root ij.1) (root ij.2))
    exact ⟨l,hl⟩
  choose path hpath using hex
  let N := ∑ ij : ι × ι, (path ij).length
  have hlen (i j : ι) : (path (i,j)).length ≤ N :=
    Finset.single_le_sum (f := fun ij : ι × ι => (path ij).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i,j))
  refine ⟨p₀^N,pow_pos hp₀ N,fun p hp hpcrit x => ?_⟩
  obtain ⟨j,a,b,hab,hax⟩ := hcover x
  have hfin (z : V) : Summable (fun y => (law p).real {ω | Conn G (ω ∩ Set.univ) z y}) := by
    simp only [Set.inter_univ]
    exact summable_twoPoint_subcritical G hloc hqt p hpcrit z
  have heq (z : V) : restrictedSusceptibility G Set.univ p z = susceptibility G p z := by
    simp only [restrictedSusceptibility,susceptibility,Set.inter_univ,twoPoint,Measure.real]
  have hb (i : ι) : p₀^N*susceptibility G p (root i) ≤ susceptibility G p (root j) := by
    have h := restrictedSusceptibility_path_lower G Set.univ p (hpath (j,i)) (fun _ _ => Set.mem_univ _) hfin
    rw [heq,heq] at h
    have hpow : p₀^N ≤ (p:ℝ)^(path (j,i)).length :=
      (pow_le_pow_left₀ hp₀.le hp N).trans (pow_le_pow_of_le_one p.2.1 p.2.2 (hlen j i))
    exact (mul_le_mul_of_nonneg_right hpow (susceptibility_nonneg G p _)).trans h
  rw [←hax,susceptibility_aut G p hab]
  calc
    _ = ∑ i, weight i*(p₀^N*susceptibility G p (root i)) := by
      simp only [rootSusceptibility,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, weight i*susceptibility G p (root j) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = susceptibility G p (root j) := by rw [←Finset.sum_mul,hw1,one_mul]

end RootSusceptibilityLower
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteLocalIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integral_mul_finite_local (I R : Finset E) (hdis : Disjoint I R)
    (p : unitInterval) (f g : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (I:Set E)))
    (hg : ∀ ω, g ω = g (ω ∩ (R:Set E))) :
    (∫ ω, f ω*g ω ∂law p) = (∫ ω, f ω ∂law p)*(∫ ω, g ω ∂law p) := by
  have hf' := finite_local_of_subset I (I∪R) Finset.subset_union_left f hf
  have hg' := finite_local_of_subset R (I∪R) Finset.subset_union_right g hg
  rw [integral_eq_bernoulliPolynomial (I∪R) p _ (fun ω => by rw [hf' ω,hg' ω]),
    integral_eq_bernoulliPolynomial I p f hf,integral_eq_bernoulliPolynomial R p g hg,
    bernoulliPolynomial_union I R hdis]
  have hi (a b : Finset E) (ha : a ⊆ I) (hb : b ⊆ R) :
      ((a ∪ b : Finset E):Set E) ∩ (I:Set E) = a := by
    ext e
    simp only [Finset.coe_union,Set.mem_inter_iff,Set.mem_union,Finset.mem_coe]
    constructor
    · rintro ⟨he,hI⟩
      rcases he with he | he
      · exact he
      · exact ((Finset.disjoint_left.mp hdis) hI (hb he)).elim
    · intro he
      exact ⟨Or.inl he,ha he⟩
  have hr (a b : Finset E) (ha : a ⊆ I) (hb : b ⊆ R) :
      ((a ∪ b : Finset E):Set E) ∩ (R:Set E) = b := by
    ext e
    simp only [Finset.coe_union,Set.mem_inter_iff,Set.mem_union,Finset.mem_coe]
    constructor
    · rintro ⟨he,hR⟩
      rcases he with he | he
      · exact ((Finset.disjoint_left.mp hdis) (ha he) hR).elim
      · exact he
    · intro he
      exact ⟨Or.inr he,hb he⟩
  trans bernoulliPolynomial I (fun a => f a*bernoulliPolynomial R (fun b => g b) p) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro b hb
    rw [hf ((a∪b : Finset E):Set E),hg ((a∪b : Finset E):Set E),hi a b ha hb,hr a b ha hb]
  · exact bernoulliPolynomial_mul_const I _ _ p

theorem complement_incidentSupport (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V) :
    ((incidentSupport G hloc W:Set E))ᶜ = internalEdges G (W:Set V)ᶜ := by
  ext e
  simp only [Set.mem_compl_iff,Finset.mem_coe,mem_incidentSupport,internalEdges,Set.mem_ofPred_eq]
  push Not
  constructor
  · intro h x hx hxW
    exact h x hxW hx
  · intro h x hxW hx
    exact h x hx hxW

 

theorem cluster_restrict_incident_eq_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (W : Finset V) (Q : Finset E) (hQ : incidentSupport G hloc W ⊆ Q)
    (ω : Set E) (x : V) :
    cluster G (ω ∩ (Q:Set E)) x = (W:Set V) ↔ cluster G ω x = W := by
  have ho : ω \ (Q:Set E) ⊆ internalEdges G (W:Set V)ᶜ := by
    rw [←complement_incidentSupport G hloc W]
    exact fun _ h => fun he => h.2 (hQ he)
  have h := cluster_union_external_eq_iff G (ω ∩ (Q:Set E)) (ω \ (Q:Set E)) x W ho
  simpa only [Set.inter_union_sdiff] using h.symm

theorem measurableSet_cluster_eq [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) (W : Set V) : MeasurableSet {ω : Set E | cluster G ω x = W} := by
  have he : {ω : Set E | cluster G ω x = W} = ⋂ y, {ω : Set E | Conn G ω x y ↔ y ∈ W} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.ext_iff,cluster]
  rw [he]
  apply MeasurableSet.iInter
  intro y
  by_cases hy : y ∈ W
  · simpa only [hy,iff_true] using measurableSet_conn G x y
  · simpa only [hy,iff_false,Set.compl_ofPred] using (measurableSet_conn G x y).compl

 

theorem cluster_cell_finite_exterior_independence [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V) (x : V)
    (R : Finset E) (hR : (R:Set E) ⊆ internalEdges G (W:Set V)ᶜ)
    (p : unitInterval) (f : Set E → ℝ) (hf : ∀ ω, f ω = f (ω ∩ (R:Set E))) :
    (∫ ω, (if cluster G ω x = (W:Set V) then (1:ℝ) else 0)*f ω ∂law p) =
      (law p).real {ω | cluster G ω x = (W:Set V)} * (∫ ω, f ω ∂law p) := by
  have hdis : Disjoint (incidentSupport G hloc W) R := by
    rw [←complement_incidentSupport G hloc W] at hR
    exact Finset.disjoint_left.mpr (fun e he h => hR h he)
  have hc (ω : Set E) :
      (if cluster G ω x = (W:Set V) then (1:ℝ) else 0) =
        (if cluster G (ω ∩ (incidentSupport G hloc W:Set E)) x = (W:Set V) then 1 else 0) := by
    simp only [cluster_restrict_incident_eq_iff G hloc W _ (by rfl)]
  rw [integral_mul_finite_local _ R hdis p _ f hc hf]
  congr 1
  have hm : MeasurableSet {ω : Set E | cluster G ω x = (W:Set V)} := measurableSet_cluster_eq G x W
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using integral_indicator_one hm

end FiniteLocalIndependence

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped Topology
section ExteriorConnectionIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_restrictedConn [Countable E] (G : BondGraph V E)
    (S : Set E) (x y : V) : MeasurableSet {ω : Set E | Conn G (ω ∩ S) x y} :=
  measurableSet_finiteWitness _
    (fun _ _ hω hc => conn_mono G (Set.inter_subset_inter_left _ hω) hc)
    (finiteWitness_inter _ (finiteWitness_conn G x y) S)

theorem integral_event_indicator (p : unitInterval) (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ ω, (if ω ∈ A then (1:ℝ) else 0) ∂law p) = (law p).real A := by
  simpa only [Set.indicator,Pi.one_apply] using (integral_indicator_one (μ := law p) hA)

 

theorem cluster_cell_exterior_connection_independent [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V)
    (x y z : V) (p : unitInterval) :
    (law p).real {ω | cluster G ω x = (W:Set V) ∧ Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} =
      (law p).real {ω | cluster G ω x = (W:Set V)} *
        (law p).real {ω | Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} := by
  let := Encodable.ofCountable E
  let S := internalEdges G (W:Set V)ᶜ
  let R := restrictedBondExhaustion S ∅
  have hmono : Monotone R := restrictedBondExhaustion_mono S ∅
  have hsub (n : ℕ) : (R n:Set E) ⊆ S := restrictedBondExhaustion_subset S ∅ (by simp) n
  have hcover (e : E) (he : e ∈ S) : ∃ n, e ∈ R n := restrictedBondExhaustion_cover S ∅ e he
  let A : Set (Set E) := {ω | cluster G ω x = (W:Set V)}
  let B (n : ℕ) : Set (Set E) := {ω | Conn G (ω ∩ (R n:Set E)) y z}
  let Btop : Set (Set E) := {ω | Conn G (ω ∩ S) y z}
  have hB : Monotone B := fun n m h ω hc =>
    conn_mono G (Set.inter_subset_inter_right _ (show (R n:Set E) ⊆ (R m:Set E) from hmono h)) hc
  have hu : (⋃ n, B n) = Btop := by
    ext ω
    simp only [B,Btop,Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,hn⟩ => conn_mono G (Set.inter_subset_inter_right _ (hsub n)) hn,
      conn_finite_exhaustion G S R hmono hcover⟩
  have huA : (⋃ n, A ∩ B n) = A ∩ Btop := by rw [←Set.inter_iUnion,hu]
  have htB := tendsto_measure_iUnion_atTop (μ := law p) hB
  have htA := tendsto_measure_iUnion_atTop (μ := law p)
    (show Monotone (fun n => A ∩ B n) from fun _ _ h => Set.inter_subset_inter_right _ (hB h))
  rw [hu] at htB
  rw [huA] at htA
  have htB' := (ENNReal.tendsto_toReal (measure_ne_top (law p) Btop)).comp htB
  have htA' := (ENNReal.tendsto_toReal (measure_ne_top (law p) (A∩Btop))).comp htA
  have he (n : ℕ) : (law p).real (A ∩ B n) = (law p).real A * (law p).real (B n) := by
    have h := cluster_cell_finite_exterior_independence G hloc W x (R n) (hsub n) p
      (fun ω => if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0)
      (fun ω => by rw [Set.inter_assoc,Set.inter_self])
    have hf : (∫ ω, (if cluster G ω x = (W:Set V) then (1:ℝ) else 0)*
        (if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0) ∂law p) = (law p).real (A ∩ B n) := by
      rw [←integral_event_indicator p (A∩B n)
        ((measurableSet_cluster_eq G x W).inter (measurableSet_restrictedConn G _ y z))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        dsimp only [A,B,Set.mem_inter_iff,Set.mem_ofPred_eq]
        split_ifs <;> simp_all)
    rw [hf] at h
    rw [show (∫ ω, (if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0) ∂law p) =
      (law p).real (B n) from integral_event_indicator p (B n) (measurableSet_restrictedConn G _ y z)] at h
    exact h
  exact tendsto_nhds_unique htA' ((tendsto_const_nhds.mul htB').congr (fun n => (he n).symm))

end ExteriorConnectionIndependence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExposedClusterGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_exterior_of_cluster_eq (G : BondGraph V E) (ω : Set E)
    (x y z : V) (W : Set V) (hW : cluster G ω x = W) (hy : y ∉ W) :
    Conn G (ω ∩ internalEdges G Wᶜ) y z ↔ Conn G ω y z := by
  refine ⟨conn_mono G Set.inter_subset_left,fun h => ?_⟩
  have hout (a : V) (ha : Conn G ω y a) : a ∉ W := by
    intro haW
    have hxa : Conn G ω x a := by change a ∈ cluster G ω x; rwa [hW]
    exact hy (hW ▸ (hxa.trans (conn_symm G _ ha) : y ∈ cluster G ω x))
  induction h with
  | refl => exact conn_refl G _ y
  | @tail a b hya hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G Wᶜ e a b heq).mpr
      ⟨hout a hya,hout b (hya.tail ⟨e,he,heq⟩)⟩⟩,heq⟩

theorem cluster_size_eq_tsum_real (G : BondGraph V E) (ω : Set E) (y : V)
    (hf : (cluster G ω y).Finite) :
    ((cluster G ω y).ncard:ℝ) = ∑' z, if Conn G ω y z then (1:ℝ) else 0 := by
  rw [tsum_eq_sum (s := hf.toFinset) (fun z hz => by
    exact ite_eq_right (fun hc => hz (hf.mem_toFinset.mpr hc)))]
  rw [show (∑ z ∈ hf.toFinset, if Conn G ω y z then (1:ℝ) else 0) =
      ∑ _z ∈ hf.toFinset, (1:ℝ) from Finset.sum_congr rfl (fun z hz => ite_eq_left (hf.mem_toFinset.mp hz))]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hf]

 

theorem integral_cluster_size_event [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (y : V) (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ ω, (if ω ∈ A then ((cluster G ω y).ncard:ℝ) else 0) ∂law p) =
      ∑' z, (law p).real {ω | ω ∈ A ∧ Conn G ω y z} := by
  let f (z : V) (ω : Set E) : ℝ := if ω ∈ A ∧ Conn G ω y z then 1 else 0
  have hm (z : V) : MeasurableSet {ω : Set E | ω ∈ A ∧ Conn G ω y z} :=
    hA.inter (measurableSet_conn G y z)
  have hf (z : V) : f z = {ω : Set E | ω ∈ A ∧ Conn G ω y z}.indicator (fun _ => (1:ℝ)) := by
    funext ω
    simp only [f,Set.indicator,Set.mem_ofPred_eq]
  have hi (z : V) : Integrable (f z) (law p) := by
    rw [hf]
    exact (integrable_const (1:ℝ)).indicator (hm z)
  have hn (z : V) (ω : Set E) : 0 ≤ f z ω := by unfold f; split_ifs <;> norm_num
  have he (z : V) : (∫ ω, f z ω ∂law p) = (law p).real {ω | ω ∈ A ∧ Conn G ω y z} := by
    rw [hf]
    exact integral_indicator_one (hm z)
  have hint : Summable (fun z => ∫ ω, ‖f z ω‖ ∂law p) := by
    simp_rw [Real.norm_of_nonneg (hn _ _),he]
    apply (summable_twoPoint_subcritical G hloc hqt p hp y).of_nonneg_of_le
    · exact fun _ => ENNReal.toReal_nonneg
    · intro z
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun ω h => h.2))
  calc
    _ = ∫ ω, ∑' z, f z ω ∂law p := by
      apply integral_congr_ae
      filter_upwards [subcritical_cluster_finite_ae G p hp y] with ω hω
      by_cases hωA : ω ∈ A
      · simp only [hωA,if_true,f,true_and]
        exact cluster_size_eq_tsum_real G ω y hω
      · simp only [hωA,if_false,f,false_and,tsum_zero]
    _ = ∑' z, ∫ ω, f z ω ∂law p := (integral_tsum_of_summable_integral_norm hi hint).symm
    _ = _ := tsum_congr he

end ExposedClusterGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorCellSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_cell_exterior_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (W : Finset V) (x y : V) :
    (∫ ω, (if cluster G ω x = (W:Set V) ∧ ¬Conn G ω x y
      then ((cluster G ω y).ncard:ℝ) else 0) ∂law p) =
      (law p).real {ω | cluster G ω x = (W:Set V)} *
        inducedSusceptibility G (W:Set V)ᶜ p y := by
  by_cases hy : y ∈ (W:Set V)
  · rw [inducedSusceptibility,ite_eq_right (fun h => h hy),mul_zero]
    calc
      _ = ∫ _ω : Set E, (0:ℝ) ∂law p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          split_ifs with h
          · have hc : Conn G ω x y := by change y ∈ cluster G ω x; rwa [h.1]
            exact (h.2 hc).elim
          · rfl)
      _ = 0 := integral_zero _ _
  · simp only [inducedSusceptibility,Set.mem_compl_iff,hy,not_false_eq_true,if_true]
    calc
      _ = ∫ ω, (if cluster G ω x = (W:Set V) then ((cluster G ω y).ncard:ℝ) else 0) ∂law p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          by_cases hc : cluster G ω x = (W:Set V)
          · have hnc : ¬Conn G ω x y := by intro h; exact hy (hc ▸ h)
            simp [hc,hnc]
          · simp only [hc,false_and,if_false])
      _ = ∑' z, (law p).real {ω | cluster G ω x = (W:Set V) ∧ Conn G ω y z} :=
        integral_cluster_size_event G hloc hqt p hp y _ (measurableSet_cluster_eq G x W)
      _ = ∑' z, (law p).real {ω | cluster G ω x = (W:Set V)} *
          (law p).real {ω | Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} := by
        apply tsum_congr
        intro z
        rw [show {ω : Set E | cluster G ω x = (W:Set V) ∧ Conn G ω y z} =
            {ω | cluster G ω x = (W:Set V) ∧ Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} from by
          ext ω
          exact ⟨fun h => ⟨h.1,(conn_exterior_of_cluster_eq G ω x y z W h.1 hy).mpr h.2⟩,
            fun h => ⟨h.1,conn_mono G Set.inter_subset_left h.2⟩⟩]
        exact cluster_cell_exterior_connection_independent G hloc W x y z p
      _ = _ := tsum_mul_left

theorem restrictedSusceptibility_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (S : Set E) (y : V) :
    restrictedSusceptibility G S p y ≤ susceptibility G p y := by
  apply Summable.tsum_le_tsum _ (summable_restrictedTwoPoint G hloc hqt p hp S y)
    (summable_twoPoint_subcritical G hloc hqt p hp y)
  exact fun z => ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun ω hc => conn_mono G Set.inter_subset_left hc))

theorem inducedSusceptibility_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Set V) (y : V) :
    inducedSusceptibility G D p y ≤ susceptibility G p y := by
  unfold inducedSusceptibility
  split_ifs
  · exact restrictedSusceptibility_le_susceptibility G hloc hqt p hp _ y
  · exact susceptibility_nonneg G p y

end ExteriorCellSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterPartition
attribute [local instance] Classical.propDecidable Classical.decEq

theorem tsum_cluster_cells (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) (a : ℝ) :
    (∑' W : Finset V, if cluster G ω x = (W:Set V) then a else 0) = a := by
  let W := hf.toFinset
  have hW : cluster G ω x = (W:Set V) := hf.coe_toFinset.symm
  rw [tsum_eq_single W (fun U hU => ite_eq_right (fun h => hU (Finset.coe_injective (h.symm.trans hW)))),ite_eq_left hW]

 

theorem integral_cluster_finite_partition [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V)
    (f : Set E → ℝ) (hf : Integrable f (law p)) :
    (∫ ω, f ω ∂law p) = ∑' W : Finset V,
      ∫ ω, (if cluster G ω x = (W:Set V) then f ω else 0) ∂law p := by
  let F (W : Finset V) (ω : Set E) := if cluster G ω x = (W:Set V) then f ω else 0
  have hi (W : Finset V) : Integrable (F W) (law p) := by
    have he : F W = {ω : Set E | cluster G ω x = (W:Set V)}.indicator f := by
      funext ω
      simp only [F,Set.indicator,Set.mem_ofPred_eq]
      split_ifs <;> rfl
    rw [he]
    exact hf.indicator (measurableSet_cluster_eq G x W)
  have hb (S : Finset (Finset V)) (ω : Set E) : (∑ W ∈ S, ‖F W ω‖) ≤ ‖f ω‖ := by
    by_cases hex : ∃ W ∈ S, cluster G ω x = (W:Set V)
    · obtain ⟨W,hWS,hW⟩ := hex
      rw [Finset.sum_eq_single W]
      · simp only [F,hW,if_true,le_refl]
      · intro U _ hU
        have hu : cluster G ω x ≠ (U:Set V) := fun h => hU (Finset.coe_injective (h.symm.trans hW))
        simp only [F,ite_eq_right hu,norm_zero]
      · exact fun h => (h hWS).elim
    · have he (W : Finset V) (hW : W ∈ S) : cluster G ω x ≠ (W:Set V) := fun h => hex ⟨W,hW,h⟩
      calc
        _ = 0 := Finset.sum_eq_zero (fun W hW => by simp only [F,ite_eq_right (he W hW),norm_zero])
        _ ≤ _ := norm_nonneg _
  have hn : Summable (fun W => ∫ ω, ‖F W ω‖ ∂law p) := by
    apply summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (c := ∫ ω, ‖f ω‖ ∂law p)
    intro S
    rw [←integral_finsetSum _ (fun W _ => (hi W).norm)]
    exact integral_mono (integrable_finsetSum _ (fun W _ => (hi W).norm)) hf.norm (hb S)
  calc
    _ = ∫ ω, ∑' W : Finset V, F W ω ∂law p := by
      apply integral_congr_ae
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      exact (tsum_cluster_cells G ω x hω (f ω)).symm
    _ = _ := (integral_tsum_of_summable_integral_norm hi hn).symm

end ClusterPartition
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshExteriorMoment
attribute [local instance] Classical.propDecidable Classical.decEq

theorem freshExteriorMoment_eq_tsum (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) :
    freshExteriorMoment G p x y ω = ∑' W : Finset V, if cluster G ω x = (W:Set V)
      then (W.card:ℝ)*inducedSusceptibility G (W:Set V)ᶜ p y else 0 := by
  by_cases hf : (cluster G ω x).Finite
  · let W := hf.toFinset
    have hW : cluster G ω x = (W:Set V) := hf.coe_toFinset.symm
    rw [tsum_eq_single W (fun U hU => ite_eq_right (fun h => hU (Finset.coe_injective (h.symm.trans hW)))),ite_eq_left hW]
    simp only [freshExteriorMoment,hW,Set.ncard_coe_finset]
  · have he (W : Finset V) : cluster G ω x ≠ (W:Set V) := fun h => hf (h ▸ W.finite_toSet)
    simp only [freshExteriorMoment,Set.Infinite.ncard hf,Nat.cast_zero,zero_mul,ite_eq_right (he _),tsum_zero]

theorem measurable_freshExteriorMoment [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) : Measurable (freshExteriorMoment G p x y) := by
  simp_rw [show freshExteriorMoment G p x y = (fun ω => ∑' W : Finset V, if cluster G ω x = (W:Set V)
      then (W.card:ℝ)*inducedSusceptibility G (W:Set V)ᶜ p y else 0) from funext (freshExteriorMoment_eq_tsum G p x y)]
  apply Measurable.tsum
  intro W
  exact Measurable.ite (measurableSet_cluster_eq G x W) measurable_const measurable_const

theorem freshExteriorMoment_nonneg (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : 0 ≤ freshExteriorMoment G p x y ω :=
  mul_nonneg (Nat.cast_nonneg _) (inducedSusceptibility_nonneg G _ p y)

end FreshExteriorMoment
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Susceptibility
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
open MeasureTheory Filter
section SubcriticalSusceptibilityContinuity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem label_cluster_finite_ae_subcritical [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), (cluster G (openEdges labels p) x).Finite := by
  apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
    (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges p).aemeasurable
  rw [map_openEdges]
  exact subcritical_cluster_finite_ae G p hp x

end SubcriticalSusceptibilityContinuity
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_TailBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ContactConcentration
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactBonds_comm (G : BondGraph V E) (Q : Finset E) (A B : Finset V) :
    contactBonds G Q A B = contactBonds G Q B A := by
  ext e
  simp only [contactBonds,Finset.mem_filter]
  constructor <;> rintro ⟨he,a,ha,b,hb,hab⟩
  · exact ⟨he,b,hb,a,ha,hab.trans (Sym2.eq_swap ..)⟩
  · exact ⟨he,b,hb,a,ha,hab.trans (Sym2.eq_swap ..)⟩



end ContactConcentration
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
section ContactBinFirstMoment
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactBonds_card_le (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d) (A B : Finset V) :
    (contactBonds G Q A B).card ≤ d*min A.card B.card := by
  have hh (A B : Finset V) : (contactBonds G Q A B).card ≤ d*A.card := by
    apply (Finset.card_le_card (t := incidentBonds G Q A) _).trans (incidentBonds_card_le G Q A d hd)
    intro e he
    obtain ⟨he,a,ha,b,_,hab⟩ := Finset.mem_filter.mp he
    exact (mem_incidentBonds G Q A e).mpr ⟨he,a,ha,by rw [hab]; simp⟩
  rcases le_total A.card B.card with h | h
  · rw [min_eq_left h]; exact hh A B
  · rw [min_eq_right h,contactBonds_comm G Q A B]; exact hh B A

end ContactBinFirstMoment
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContacts
attribute [local instance] Classical.propDecidable Classical.decEq


theorem contactSet_subset_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (B : Set V) : closedContactSet G (A:Set V) B ⊆ (incidentSupport G hloc A:Set E) := by
  rintro e ⟨a,ha,b,_,hab⟩
  exact (mem_incidentSupport G hloc A e).mpr ⟨a,ha,by rw [hab]; simp⟩

theorem coe_contactBonds_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (A B : Finset V) (hQ : incidentSupport G hloc A ⊆ Q) :
    (contactBonds G Q A B : Set E) = closedContactSet G A B := by
  ext e
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨hQ (contactSet_subset_incident G hloc A B h),h⟩

end InfiniteContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ContactMeasurability
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_clusterContactCount [Countable V] [Countable E]
    (G : BondGraph V E) (x v : V) : Measurable (fun ω : Set E => clusterContactCount G ω x v) := by
  apply measurable_ncard.comp
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  apply measurableSet_setOfPred.mp
  change MeasurableSet {ω : Set E | ∃ a, Conn G ω x a ∧ ∃ b, Conn G ω v b ∧ G e = s(a,b)}
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  have he : {ω : Set E | Conn G ω x a ∧ ∃ b, Conn G ω v b ∧ G e = s(a,b)} =
      {ω | Conn G ω x a} ∩ ⋃ b, {ω | Conn G ω v b ∧ G e = s(a,b)} := by ext ω; simp
  rw [he]
  apply (measurableSet_conn G x a).inter
  apply MeasurableSet.iUnion
  intro b
  by_cases h : G e = s(a,b)
  · simpa only [h,and_true] using measurableSet_conn G v b
  · simp only [h,and_false,Set.ofPred_false]; exact MeasurableSet.empty

theorem coe_domainBits (Q : Finset E) (ω : Set E) :
    (domainBits Q ω:Set E) = ω ∩ (Q:Set E) := by ext e; simp only [mem_domainBits,Set.mem_inter_iff,Finset.mem_coe,and_comm]

theorem domainBits_local (Q : Finset E) (ω : Set E) :
    domainBits Q (ω ∩ (Q:Set E)) = domainBits Q ω := by
  ext e
  simp only [mem_domainBits,Set.mem_inter_iff,Finset.mem_coe]
  tauto

theorem domainBits_of_subset (Q ω : Finset E) (hω : ω ⊆ Q) : domainBits Q (ω:Set E) = ω := by
  ext e
  simp only [mem_domainBits,Finset.mem_coe]
  exact ⟨fun h => h.2,fun h => ⟨hω h,h⟩⟩

theorem integral_domainBits (Q : Finset E) (p : unitInterval) (f : Finset E → ℝ) :
    (∫ ω, f (domainBits Q ω) ∂law p) = bernoulliPolynomial Q f p := by
  rw [integral_eq_bernoulliPolynomial Q p _ (fun ω => by rw [domainBits_local])]
  apply bernoulliPolynomial_congr
  intro ω hω
  rw [domainBits_of_subset Q ω hω]

end ContactMeasurability
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullLargeContacts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem fullLargeContact_nonneg (G : BondGraph V E) (x v : V) (L : ℕ) (ω : Set E) :
    0 ≤ fullLargeContact G x v L ω := by unfold fullLargeContact; split_ifs <;> positivity

theorem measurable_fullLargeContact [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x v : V) (L : ℕ) :
    Measurable (fullLargeContact G x v L) := by
  have hs : Measurable (fun ω : Set E => min (cluster G ω x).ncard (cluster G ω v).ncard) :=
    (measurable_cluster_ncard G hloc x).min (measurable_cluster_ncard G hloc v)
  exact ((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (measurable_clusterContactCount G x v)).ite
    (((measurableSet_conn G x v).compl).inter (measurableSet_le measurable_const hs)) measurable_const

end FullLargeContacts
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterAveraging
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_ncard_pos (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : 0 < (cluster G ω x).ncard :=
  (Set.ncard_pos hf).mpr ⟨x,mem_cluster_self G ω x⟩

end ClusterAveraging
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_ContactTrace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Trace for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section IndexedEdgeKernel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem enn_ncard_eq_tsum {α : Type*} (A : Set α) (hA : A.Finite) :
    (A.ncard:ℝ≥0∞) = ∑' a, if a ∈ A then (1:ℝ≥0∞) else 0 := by
  rw [tsum_eq_sum (s := hA.toFinset) (fun a ha => by
    simp only [Set.Finite.mem_toFinset] at ha
    exact ite_eq_right ha)]
  simp only [Set.ncard_eq_toFinset_card A hA]
  rw [Finset.sum_congr rfl (fun a ha => ite_eq_left ((Set.Finite.mem_toFinset _).mp ha))]
  simp



theorem indexedEdgeKernel_row (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    (∑' y, indexedEdgeKernel G x y) = (degree G x:ℝ≥0∞) := by
  change (∑' y, ∑' e, if G e = s(x,y) then (1:ℝ≥0∞) else 0) = _
  rw [ENNReal.tsum_comm,←ENNReal.tsum_prod]
  have hn := (enn_ncard_eq_tsum _ (finite_steps G hloc x)).symm
  have he : (∑' (p : E × V), if G p.1 = s(x,p.2) then (1:ℝ≥0∞) else 0) =
      (({ey : E × V | G ey.1 = s(x,ey.2)} : Set (E × V)).ncard:ℝ≥0∞) := by
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    apply tsum_congr
    intro ey
    by_cases h : G ey.1 = s(x,ey.2) <;> simp only [Set.mem_ofPred_eq,h,if_true,if_false]
  rw [he]
  change (({ey : E × V | G ey.1 = s(x,ey.2)} : Set (E × V)).ncard:ℝ≥0∞) = (Nat.card (Step G x):ℝ≥0∞)
  rw [←Nat.card_coe_set_eq]; rfl

end IndexedEdgeKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactKernelCounting
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contact_endpoints_unique (G : BondGraph V E) (ω : Set E) (x y : V)
    (hd : ¬Conn G ω x y) {e : E} {a b c d : V}
    (ha : Conn G ω x a) (_hb : Conn G ω y b)
    (_hc : Conn G ω x c) (he : Conn G ω y d)
    (hab : G e = s(a,b)) (hcd : G e = s(c,d)) : a = c ∧ b = d := by
  rcases Sym2.eq_iff.mp (hab.symm.trans hcd) with h | h
  · exact h
  · exfalso
    apply hd
    exact conn_trans G ω ha (by simpa only [h.1] using conn_symm G ω he)

theorem closedContactSet_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (A B : Set V) (hA : A.Finite) : (closedContactSet G A B).Finite := by
  have hs := contactSet_subset_incident G hloc hA.toFinset B
  rw [Set.Finite.coe_toFinset] at hs
  exact (incidentSupport G hloc hA.toFinset).finite_toSet.subset hs

theorem clusterPairKernel_edge (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x y : V) (hd : ¬Conn G ω x y) (hx : (cluster G ω x).Finite) :
    clusterPairKernel G ω (indexedEdgeKernel G) x y = (clusterContactCount G ω x y:ℝ≥0∞) := by
  have hed (e : E) :
      (∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0) =
      if e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) then 1 else 0 := by
    by_cases h : e ∈ closedContactSet G (cluster G ω x) (cluster G ω y)
    · obtain ⟨a,ha,b,hb,hab⟩ := h
      change Conn G ω x a at ha
      change Conn G ω y b at hb
      have hh : e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) := ⟨a,ha,b,hb,hab⟩
      rw [ite_eq_left hh,tsum_eq_single a]
      · rw [tsum_eq_single b]
        · exact ite_eq_left ⟨ha,hb,hab⟩
        · intro d hdb
          apply ite_eq_right
          intro hc
          exact hdb (contact_endpoints_unique G ω x y hd hc.1 hc.2.1 ha hb hc.2.2 hab).2
      · intro c hca
        apply ENNReal.tsum_eq_zero.mpr
        intro d
        apply ite_eq_right
        intro hc
        exact hca (contact_endpoints_unique G ω x y hd hc.1 hc.2.1 ha hb hc.2.2 hab).1
    · rw [ite_eq_right h]
      apply ENNReal.tsum_eq_zero.mpr
      intro a
      apply ENNReal.tsum_eq_zero.mpr
      intro b
      apply ite_eq_right
      intro hab
      exact h ⟨a,hab.1,b,hab.2.1,hab.2.2⟩
  have he (a b : V) : (if Conn G ω x a ∧ Conn G ω y b then indexedEdgeKernel G a b else 0) =
      ∑' e, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
    by_cases ha : Conn G ω x a <;> by_cases hb : Conn G ω y b <;>
      simp only [ha,hb,and_self,true_and,false_and,if_true,if_false,indexedEdgeKernel,tsum_zero]
  rw [clusterPairKernel]
  simp_rw [he]
  calc
    _ = ∑' e, ∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
      calc
        _ = ∑' a, ∑' e, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
          apply tsum_congr; intro a; exact ENNReal.tsum_comm
        _ = _ := ENNReal.tsum_comm
    _ = ∑' e, if e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) then (1:ℝ≥0∞) else 0 := tsum_congr hed
    _ = _ := (enn_ncard_eq_tsum _ (closedContactSet_finite G hloc _ _ hx)).symm

end ContactKernelCounting
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section DistinctClusterBK
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinct_cluster_disjoint_occurrence (G : BondGraph V E) (ω : Set E)
    (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) (hd : ¬Conn G ω x y) :
    ω ∈ DisjointOccurrence {η | Conn G η x a} {η | Conn G η y b} := by
  obtain ⟨s,hs,hsa⟩ := finiteWitness_conn G x a _ (conn_restrict_cluster G ω x (mem_cluster_self G ω x) hxa)
  obtain ⟨t,ht,htb⟩ := finiteWitness_conn G y b _ (conn_restrict_cluster_compl G ω x hd hyb)
  refine ⟨s,t,fun e he => (hs he).1,fun e he => (ht he).1,?_,hsa,htb⟩
  apply Finset.disjoint_left.mpr
  intro e he ht'
  obtain ⟨⟨z,w⟩,hr⟩ := Quot.exists_rep (G e)
  have hz : z ∈ G e := by rw [←hr]; exact Sym2.mem_mk_left z w
  exact (ht ht').2 z hz ((hs he).2 z hz)

theorem distinct_cluster_two_point_bound [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y a b : V) :
    law p {ω | Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y} ≤
      law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b} := by
  calc
    _ ≤ law p (DisjointOccurrence {ω | Conn G ω x a} {ω | Conn G ω y b}) :=
      measure_mono (fun ω h => distinct_cluster_disjoint_occurrence G ω x y a b h.1 h.2.1 h.2.2)
    _ ≤ _ := bk_ennreal p _ _ (fun _ _ h hc => conn_mono G h hc)
      (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x a) (finiteWitness_conn G y b)

end DistinctClusterBK
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairSquareDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairKernel_distinct_integral [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (J : V → V → ℝ≥0∞) (x y : V) :
    (∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p) =
      ∑' a, ∑' b, J a b * law p {ω | Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y} := by
  have he (ω : Set E) : (if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0) =
      ∑' a, ∑' b, J a b * (if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0) := by
    by_cases hd : Conn G ω x y
    · simp only [hd,not_true_eq_false,and_false,if_false,mul_zero,tsum_zero]
    · rw [ite_eq_left hd,clusterPairKernel]
      apply tsum_congr; intro a
      apply tsum_congr; intro b
      by_cases h : Conn G ω x a ∧ Conn G ω y b
      · simp only [h.1,h.2,hd,not_false_eq_true,and_self,if_true,mul_one]
      · have hn : ¬ (Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y) := fun h' => h ⟨h'.1,h'.2.1⟩
        simp only [ite_eq_right h,ite_eq_right hn,mul_zero]
  have hm (a b : V) : Measurable (fun ω => if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite ((measurableSet_conn G x a).inter ((measurableSet_conn G y b).inter (measurableSet_conn G x y).compl)) measurable_const
  have hm' (a b : V) : Measurable (fun ω : Set E => J a b * (if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0)) :=
    (measurable_const : Measurable (fun _ : Set E => J a b)).mul (hm a b)
  simp_rw [he]
  rw [lintegral_tsum (fun a => (Measurable.tsum (fun b => hm' a b)).aemeasurable)]
  apply tsum_congr; intro a
  rw [lintegral_tsum (fun b => (hm' a b).aemeasurable)]
  apply tsum_congr; intro b
  rw [lintegral_const_mul _ (hm a b)]
  congr 1
  convert
    (lintegral_indicator_one (μ := law p) ((measurableSet_conn G x a).inter ((measurableSet_conn G y b).inter (measurableSet_conn G x y).compl))) using 1
  · apply lintegral_congr
    intro ω
    simp only [Set.indicator,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_ofPred_eq,Pi.one_apply]
  · congr 1

theorem clusterPairKernel_distinct_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (J : V → V → ℝ≥0∞) (x y : V) :
    (∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p) ≤
      ∑' a, ∑' b, J a b * (law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b}) := by
  rw [clusterPairKernel_distinct_integral]
  exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
    mul_le_mul_right (distinct_cluster_two_point_bound G p x y a b) _))



end PairSquareDiagram
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section NonnegativeOperatorDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem ennMatrixCoeff_mul {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : PositiveRealMatrix A) (hB : PositiveRealMatrix B) (x y : V) :
    ennMatrixCoeff (A*B) x y = ∑' z, ennMatrixCoeff A x z * ennMatrixCoeff B z y := by
  unfold ennMatrixCoeff
  rw [←(hA.mul_hasSum B x y).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun z => mul_nonneg (hA x z).2 (hB z y).2) (hA.mul_hasSum B x y).summable]
  apply tsum_congr; intro z
  exact ENNReal.ofReal_mul (hA x z).2

theorem HasKernel.ennMatrixCoeff [Countable E] (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    ennMatrixCoeff T x y = law p {ω | Conn G ω x y} := by
  unfold Percolation.ennMatrixCoeff matrixCoeff
  rw [hT x y]
  simp only [Complex.ofReal_re,twoPoint,ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem HasKernel.positiveRealMatrix (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) : PositiveRealMatrix T := by
  intro x y
  change (T (lp.single 2 y (1:ℂ)) x).im = 0 ∧ 0 ≤ (T (lp.single 2 y (1:ℂ)) x).re
  rw [hT x y]
  exact ⟨rfl,twoPoint_nonneg G p x y⟩

end NonnegativeOperatorDiagram
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_RussoRows
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Russo Rows for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionRussoContacts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem closedPivotal_connection_iff (G : BondGraph V E) (ω : Set E) (x y : V) (e : E) :
    ω ∈ closedPivotal {η | Conn G η x y} e ↔
      ¬Conn G ω x y ∧ e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) := by
  constructor
  · rintro ⟨_,hxy,hins⟩
    refine ⟨hxy,?_⟩
    obtain ⟨⟨a,b⟩,hab⟩ := Quot.exists_rep (G e)
    have he : G e = s(a,b) := hab.symm
    rcases (conn_insert_iff G ω e a b x y he).mp hins with h | h | h
    · exact (hxy h).elim
    · exact ⟨a,h.1,b,conn_symm G ω h.2,he⟩
    · exact ⟨b,h.1,a,conn_symm G ω h.2,by rw [he,Sym2.eq_swap]⟩
  · rintro ⟨hxy,a,hxa,b,hyb,he⟩
    have hclosed : e ∉ ω := by
      intro heω
      exact hxy (hxa.trans ((Relation.ReflTransGen.single ⟨e,heω,he⟩).trans (conn_symm G ω hyb)))
    refine ⟨hclosed,hxy,?_⟩
    exact (conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨hxa,conn_symm G ω hyb⟩))

theorem finiteClosedContact_eq_sum (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) :
    finiteClosedContact G Q x y ω =
      ∑ e ∈ Q, if (ω:Set E) ∈ closedPivotal {η | Conn G η x y} e then (1:ℝ) else 0 := by
  have hm (z a : V) : a ∈ finiteRootComponent G ω z ↔ Conn G (ω:Set E) z a := by
    change a ∈ (finiteRootComponent G ω z:Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  simp only [closedPivotal_connection_iff,closedContactSet,Set.mem_ofPred_eq,finiteClosedContact]
  by_cases hxy : Conn G (ω:Set E) x y
  · simp only [hxy,not_true_eq_false,false_and,if_false,Finset.sum_const_zero]
  · rw [ite_eq_left hxy]
    simp only [hxy,not_false_eq_true,true_and,contactBonds,hm,cluster,Set.mem_ofPred_eq]
    rw [Finset.sum_boole]

theorem finite_connection_russo_contacts (G : BondGraph V E) (Q : Finset E)
    (x y : V) (p : ℝ) :
    (1-p)*deriv (finiteEventPolynomial Q {ω | Conn G ω x y}) p =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) p := by
  change (1-p)*deriv (bernoulliPolynomial Q (fun ω => if Conn G (ω:Set E) x y then 1 else 0)) p = _
  rw [closed_difference_russo]
  have he : finiteClosedContact G Q x y = fun (ω : Finset E) =>
      ∑ e ∈ Q, if (ω:Set E) ∈ closedPivotal {η | Conn G η x y} e then (1:ℝ) else 0 :=
    funext (finiteClosedContact_eq_sum G Q x y)
  rw [he,bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply bernoulliPolynomial_congr
  intro ω _
  exact (closedPivotal_difference {η | Conn G η x y}
    (fun _ _ h hc => conn_mono G h hc) e ω).symm

end ConnectionRussoContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactApproximation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClosedContact_eq_full (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x y : V) (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite)
    (Q : Finset E) (hQx : incidentSupport G hloc hx.toFinset ⊆ Q)
    (hQy : incidentSupport G hloc hy.toFinset ⊆ Q) :
    finiteClosedContact G Q x y (domainBits Q ω) = fullLargeContact G x y 0 ω := by
  have hcluster (z : V) (hz : (cluster G ω z).Finite) (hQ : incidentSupport G hloc hz.toFinset ⊆ Q) :
      cluster G (domainBits Q ω:Set E) z = cluster G ω z := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hz.toFinset Q hQ ω z).mpr
      (Set.Finite.coe_toFinset hz).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  have hcx := hcluster x hx hQx
  have hcy := hcluster y hy hQy
  have hFx : finiteRootComponent G (domainBits Q ω) x = hx.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcx,Set.Finite.coe_toFinset]
  have hFy : finiteRootComponent G (domainBits Q ω) y = hy.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcy,Set.Finite.coe_toFinset]
  have hconn : Conn G (domainBits Q ω:Set E) x y ↔ Conn G ω x y := by
    change y ∈ cluster G (domainBits Q ω:Set E) x ↔ y ∈ cluster G ω x
    rw [hcx]
  have hc : (contactBonds G Q hx.toFinset hy.toFinset).card = clusterContactCount G ω x y := by
    rw [←Set.ncard_coe_finset,coe_contactBonds_eq G hloc Q _ _ hQx]
    simp only [Set.Finite.coe_toFinset,clusterContactCount]
  simp only [finiteClosedContact,fullLargeContact,hconn,hFx,hFy,hc,Nat.zero_le,and_true]

theorem finiteClosedContact_nonneg (G : BondGraph V E) (Q : Finset E) (x y : V) (ω : Finset E) :
    0 ≤ finiteClosedContact G Q x y ω := by
  unfold finiteClosedContact
  split_ifs <;> positivity

theorem finiteClosedContact_le_size (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q η : Finset E) (ω : Set E)
    (hη : (η:Set E) ⊆ ω) (x y : V) (hfin : (cluster G ω x).Finite) :
    finiteClosedContact G Q x y η ≤ (d:ℝ)*(cluster G ω x).ncard := by
  have hdQ (z : V) : (Q.filter fun e => z ∈ G e).card ≤ d :=
    (incident_filter_card_le_degree G hloc Q z).trans (hd z)
  have hs : (finiteRootComponent G η x).card ≤ (cluster G ω x).ncard := by
    rw [←Set.ncard_coe_finset,coe_finiteRootComponent]
    exact Set.ncard_le_ncard (fun z hz => conn_mono G hη hz) hfin
  unfold finiteClosedContact
  split_ifs
  · positivity
  · exact_mod_cast (contactBonds_card_le G Q d hdQ _ _).trans
      (Nat.mul_le_mul_left d ((min_le_left _ _).trans hs))



end UniformContactApproximation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ContactRegularity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem fullLargeContact_zero_le_size (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (ω : Set E) (x y : V)
    (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite) :
    fullLargeContact G x y 0 ω ≤ (d:ℝ)*(cluster G ω x).ncard := by
  let Q := incidentSupport G hloc hx.toFinset ∪ incidentSupport G hloc hy.toFinset
  rw [←finiteClosedContact_eq_full G hloc ω x y hx hy Q Finset.subset_union_left Finset.subset_union_right]
  exact finiteClosedContact_le_size G hloc d hd Q (domainBits Q ω) ω
    (by rw [coe_domainBits]; exact Set.inter_subset_left) x y hx

theorem integrable_fullContact_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fullLargeContact G x y 0) (law p) := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  apply ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ)).mono'
    (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
  rw [Real.norm_of_nonneg (fullLargeContact_nonneg G x y 0 ω)]
  exact fullLargeContact_zero_le_size G hloc d hd ω x y hx hy

theorem fullContact_label_integral [Countable E] [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) :
    (∫ labels, fullLargeContact G x y 0 (openEdges labels p) ∂labelLaw) =
      ∫ ω, fullLargeContact G x y 0 ω ∂law p := by
  rw [←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable).symm

theorem fullContact_label_integrable [Countable E] [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) :
    Integrable (fun labels => fullLargeContact G x y 0 (openEdges labels p)) labelLaw ↔
      Integrable (fullLargeContact G x y 0) (law p) := by
  rw [←map_openEdges p]
  exact (integrable_map_measure (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable
    (measurable_openEdges p).aemeasurable).symm

end ContactRegularity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactError
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_clusterSupportIn [Countable V] [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) :
    MeasurableSet {ω : Set E | ClusterSupportIn G Q ω x} := by
  simp only [ClusterSupportIn,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  have he : {ω : Set E | Conn G ω x a → ∀ e, a ∈ G e → e ∈ Q} =
      {ω | ¬Conn G ω x a} ∪ {ω | ∀ e, a ∈ G e → e ∈ Q} := by ext ω; simp only [Set.mem_union,Set.mem_ofPred_eq]; tauto
  rw [he]
  apply (measurableSet_conn G x a).compl.union
  by_cases h : ∀ e, a ∈ G e → e ∈ Q
  · convert (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Set E))) using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    exact h
  · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Set E))) using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    exact h

theorem clusterSupportIn_of_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω : Set E) (x : V) (hx : (cluster G ω x).Finite)
    (hQ : incidentSupport G hloc hx.toFinset ⊆ Q) : ClusterSupportIn G Q ω x := by
  intro a ha e he
  exact hQ ((mem_incidentSupport G hloc hx.toFinset e).mpr ⟨a,hx.mem_toFinset.mpr ha,he⟩)

theorem finiteClosedContact_eq_full_of_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω η : Set E) (hη : η ⊆ ω) (x y : V)
    (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite)
    (hQx : ClusterSupportIn G Q ω x) (hQy : ClusterSupportIn G Q ω y) :
    finiteClosedContact G Q x y (domainBits Q η) = fullLargeContact G x y 0 η := by
  have hsub (z : V) : cluster G η z ⊆ cluster G ω z := fun a ha => conn_mono G hη ha
  have hfx := hx.subset (hsub x)
  have hfy := hy.subset (hsub y)
  apply finiteClosedContact_eq_full G hloc η x y hfx hfy
  · intro e he
    obtain ⟨a,ha,he⟩ := (mem_incidentSupport G hloc hfx.toFinset e).mp he
    exact hQx a (hsub x (hfx.mem_toFinset.mp ha)) e he
  · intro e he
    obtain ⟨a,ha,he⟩ := (mem_incidentSupport G hloc hfy.toFinset e).mp he
    exact hQy a (hsub y (hfy.mem_toFinset.mp ha)) e he

theorem measurable_contactApproxError [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (Q : Finset E) (d : ℕ) (x y : V) :
    Measurable (contactApproxError G Q d x y) := by
  exact measurable_const.ite ((measurableSet_clusterSupportIn G Q x).inter
    (measurableSet_clusterSupportIn G Q y))
    (measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x)))

theorem contactApproxError_nonneg (G : BondGraph V E) (Q : Finset E) (d : ℕ) (x y : V) (ω : Set E) :
    0 ≤ contactApproxError G Q d x y ω := by unfold contactApproxError; split_ifs <;> positivity

theorem contactApproxError_le (G : BondGraph V E) (Q : Finset E) (d : ℕ) (x y : V) (ω : Set E) :
    contactApproxError G Q d x y ω ≤ (d:ℝ)*(cluster G ω x).ncard := by
  unfold contactApproxError; split_ifs <;> first | positivity | exact le_rfl

theorem contact_uniform_error_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q : Finset E) (ω η : Set E)
    (hη : η ⊆ ω) (x y : V) (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite) :
    ‖finiteClosedContact G Q x y (domainBits Q η) - fullLargeContact G x y 0 η‖ ≤
      contactApproxError G Q d x y ω := by
  unfold contactApproxError
  split_ifs with h
  · rw [finiteClosedContact_eq_full_of_support G hloc Q ω η hη x y hx hy h.1 h.2,sub_self,norm_zero]
  · have hsub (z : V) : cluster G η z ⊆ cluster G ω z := fun a ha => conn_mono G hη ha
    have hf := finiteClosedContact_le_size G hloc d hd Q (domainBits Q η) ω
      (by rw [coe_domainBits]; exact Set.inter_subset_left.trans hη) x y hx
    have hg : fullLargeContact G x y 0 η ≤ (d:ℝ)*(cluster G ω x).ncard := by
      exact (fullLargeContact_zero_le_size G hloc d hd η x y (hx.subset (hsub x)) (hy.subset (hsub y))).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Set.ncard_le_ncard (hsub x) hx) (Nat.cast_nonneg _))
    rw [Real.norm_eq_abs,abs_sub_le_iff]
    have hfn := finiteClosedContact_nonneg G Q x y (domainBits Q η)
    have hgn := fullLargeContact_nonneg G x y 0 η
    constructor <;> linarith

end UniformContactError
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactExpectation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_contactApproxError [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (Q : Finset E) (d : ℕ) (x y : V) :
    Integrable (contactApproxError G Q d x y) (law p) := by
  apply ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ)).mono'
    (measurable_contactApproxError G hloc Q d x y).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (contactApproxError_nonneg G Q d x y ω)]; exact contactApproxError_le G Q d x y ω)

theorem contactApproxError_integral_tendsto_zero [Countable V] [Encodable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (d : ℕ) (x y : V) :
    Tendsto (fun n => ∫ ω, contactApproxError G (vertexExhaustion n) d x y ω ∂law p) atTop (nhds 0) := by
  have ht : ∀ᵐ ω ∂law p, Tendsto (fun n => contactApproxError G (vertexExhaustion n) d x y ω) atTop (nhds 0) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
    obtain ⟨nx,hnx⟩ := subset_vertexExhaustion (incidentSupport G hloc hx.toFinset)
    obtain ⟨ny,hny⟩ := subset_vertexExhaustion (incidentSupport G hloc hy.toFinset)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max nx ny)] with n hn
    exact (ite_eq_left ⟨clusterSupportIn_of_incident G hloc _ ω x hx
      (hnx.trans (vertexExhaustion_mono ((le_max_left nx ny).trans hn))),
      clusterSupportIn_of_incident G hloc _ ω y hy
      (hny.trans (vertexExhaustion_mono ((le_max_right nx ny).trans hn)))⟩).symm
  have hh := tendsto_integral_of_dominated_convergence (fun ω : Set E => (d:ℝ)*(cluster G ω x).ncard)
    (fun n => (measurable_contactApproxError G hloc (vertexExhaustion n) d x y).aestronglyMeasurable)
    ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ))
    (fun n => Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (contactApproxError_nonneg G _ d x y ω)]; exact contactApproxError_le G _ d x y ω)) ht
  simpa only [integral_zero] using hh

theorem finiteClosedContact_label_integral [Countable E] (G : BondGraph V E)
    (Q : Finset E) (p : unitInterval) (x y : V) :
    (∫ labels, finiteClosedContact G Q x y (domainBits Q (openEdges labels p)) ∂labelLaw) =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) p := by
  rw [←integral_domainBits Q p (finiteClosedContact G Q x y),←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_finite_local Q (fun ω => finiteClosedContact G Q x y (domainBits Q ω)) (fun ω => by rw [domainBits_local])).aestronglyMeasurable).symm

theorem contactApproxError_label_integral [Countable V] [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (Q : Finset E) (p : unitInterval) (d : ℕ) (x y : V) :
    (∫ labels, contactApproxError G Q d x y (openEdges labels p) ∂labelLaw) =
      ∫ ω, contactApproxError G Q d x y ω ∂law p := by
  rw [←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_contactApproxError G hloc Q d x y).aestronglyMeasurable).symm

theorem contact_expectation_uniform_error [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q : Finset E) (b q : unitInterval)
    (hb : b < pc G) (hq : q ≤ b) (x y : V) :
    ‖bernoulliPolynomial Q (finiteClosedContact G Q x y) q -
      ∫ ω, fullLargeContact G x y 0 ω ∂law q‖ ≤
      ∫ ω, contactApproxError G Q d x y ω ∂law b := by
  have hf : Integrable (fun labels => finiteClosedContact G Q x y (domainBits Q (openEdges labels q))) labelLaw := by
    have hi := integrable_finite_local Q q (fun ω => finiteClosedContact G Q x y (domainBits Q ω))
      (fun ω => by rw [domainBits_local])
    rw [←map_openEdges q] at hi
    exact hi.comp_measurable (measurable_openEdges q)
  have hg := (fullContact_label_integrable G hloc q x y).mpr
    (integrable_fullContact_subcritical G hloc hqt q (hq.trans_lt hb) x y)
  have hi : Integrable (fun labels => contactApproxError G Q d x y (openEdges labels b)) labelLaw := by
    have hh := integrable_contactApproxError G hloc hqt b hb Q d x y
    rw [←map_openEdges b] at hh
    exact hh.comp_measurable (measurable_openEdges b)
  rw [←finiteClosedContact_label_integral G Q q x y,←fullContact_label_integral G hloc q x y,
    ←integral_sub hf hg,←contactApproxError_label_integral G hloc Q b d x y]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hf.sub hg).norm hi
  filter_upwards [label_cluster_finite_ae_subcritical G b hb x,label_cluster_finite_ae_subcritical G b hb y] with labels hx hy
  exact contact_uniform_error_bound G hloc d hd Q _ _ (openEdges_mono labels hq) x y hx hy

end UniformContactExpectation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section PointwiseRussoLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_connection_deriv_eq (G : BondGraph V E) (Q : Finset E)
    (x y : V) (t : ℝ) (ht : t ≠ 1) :
    deriv (finiteEventPolynomial Q {ω | Conn G ω x y}) t =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) t / (1-t) := by
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm ht))).mpr
  rw [mul_comm]
  exact finite_connection_russo_contacts G Q x y t

theorem finite_connection_deriv_tendstoUniformlyOn [Countable V] [Encodable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x y : V) :
    TendstoUniformlyOn (fun n => deriv (finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y}))
      (fun t => realContactExpectation G x y t / (1-t)) atTop (Set.Icc 0 (b:ℝ)) := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  have hb1 : (b:ℝ) < 1 := lt_of_lt_of_le hb (pc G).2.2
  have hden : 0 < 1-(b:ℝ) := sub_pos.mpr hb1
  have ht := (contactApproxError_integral_tendsto_zero G hloc hqt b hb d x y).div_const (1-(b:ℝ))
  rw [zero_div] at ht
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with n hn t ht
  let q : unitInterval := ⟨t,ht.1,ht.2.trans b.2.2⟩
  have hqb : q ≤ b := ht.2
  have hqt1 : t < 1 := ht.2.trans_lt hb1
  have he := contact_expectation_uniform_error G hloc hqt d hd (vertexExhaustion n) b q hb hqb x y
  have hn0 : 0 ≤ ∫ ω, contactApproxError G (vertexExhaustion n) d x y ω ∂law b :=
    integral_nonneg (contactApproxError_nonneg G _ d x y)
  rw [dist_comm,Real.dist_eq,finite_connection_deriv_eq G _ x y t (ne_of_lt hqt1),←sub_div,abs_div,
    abs_of_pos (sub_pos.mpr hqt1)]
  change |bernoulliPolynomial _ _ (q:ℝ) - realContactExpectation G x y (q:ℝ)| / (1-t) < ε
  rw [realContactExpectation_coe]
  apply lt_of_le_of_lt _ hn
  exact div_le_div₀ hn0 (by simpa only [Real.norm_eq_abs] using he) hden (sub_le_sub_left ht.2 1)

theorem finite_connection_polynomial_tendsto_twoPoint [Encodable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Tendsto (fun n => finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y} p)
      atTop (nhds (twoPoint G p x y)) := by
  have ht := finite_connection_polynomial_tendsto G Set.univ (vertexExhaustion (V := E))
    vertexExhaustion_mono (fun _ => Set.subset_univ _) (fun e _ => by
      obtain ⟨n,hn⟩ := subset_vertexExhaustion ({e}:Finset E)
      exact ⟨n,hn (by simp)⟩) p x y
  simpa only [Set.inter_univ,finiteEventPolynomial,Set.mem_ofPred_eq,twoPoint,Measure.real] using ht

 

theorem hasDerivAt_realTwoPoint_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (x y : V) :
    HasDerivAt (realTwoPoint G x y)
      ((∫ ω, fullLargeContact G x y 0 ω ∂law p)/(1-(p:ℝ))) (p:ℝ) := by
  let : Encodable E := Encodable.ofCountable E
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  have hu := (finite_connection_deriv_tendstoUniformlyOn G hloc hqt b hb x y).mono
    (show Set.Ioo 0 (b:ℝ) ⊆ Set.Icc 0 (b:ℝ) from Set.Ioo_subset_Icc_self)
  have hh := hasDerivAt_of_tendstoUniformlyOn (f := fun n => finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y})
    (g := realTwoPoint G x y) (g' := fun t => realContactExpectation G x y t/(1-t)) isOpen_Ioo hu
    (Eventually.of_forall (fun n t _ => by
      change HasDerivAt (bernoulliPolynomial (vertexExhaustion n) (fun (ω : Finset E) => if Conn G (ω:Set E) x y then (1:ℝ) else 0)) _ t
      exact (hasDerivAt_bernoulliPolynomial (vertexExhaustion n)
        (fun (ω : Finset E) => if Conn G (ω:Set E) x y then (1:ℝ) else 0) t).differentiableAt.hasDerivAt))
    (fun t ht => by
      let q : unitInterval := ⟨t,ht.1.le,ht.2.le.trans b.2.2⟩
      simpa only [←realTwoPoint_coe G x y q] using finite_connection_polynomial_tendsto_twoPoint G q x y)
    (show (p:ℝ) ∈ Set.Ioo 0 (b:ℝ) from ⟨hp0,hpb⟩)
  simpa only [realContactExpectation_coe] using hh

end PointwiseRussoLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conn_probability_symm (G : BondGraph V E) (p : unitInterval) (x y : V) :
    law p {ω | Conn G ω x y} = law p {ω | Conn G ω y x} := by
  congr 1
  ext ω
  exact ⟨conn_symm G ω,conn_symm G ω⟩

theorem conn_probability_mono [Countable V] [Countable E] (G : BondGraph V E)
    (p q : unitInterval) (hpq : p ≤ q) (x y : V) :
    law p {ω | Conn G ω x y} ≤ law q {ω | Conn G ω x y} := by
  rw [←ENNReal.ofReal_toReal (measure_ne_top (law p) _),←ENNReal.ofReal_toReal (measure_ne_top (law q) _)]
  exact ENNReal.ofReal_le_ofReal (twoPoint_mono G x y hpq)

theorem fullContact_lintegral_eq_kernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    (∫⁻ ω, ENNReal.ofReal (fullLargeContact G x y 0 ω) ∂law p) =
      ∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω (indexedEdgeKernel G) x y else 0 ∂law p := by
  apply lintegral_congr_ae
  filter_upwards [hx] with ω hω
  by_cases hxy : Conn G ω x y
  · simp only [fullLargeContact,hxy,not_true_eq_false,false_and,if_false,ENNReal.ofReal_zero]
  · rw [ite_eq_left hxy,clusterPairKernel_edge G hloc ω x y hxy hω]
    simp only [fullLargeContact,hxy,Nat.zero_le,not_false_eq_true,and_self,if_true,ENNReal.ofReal_natCast]

theorem fullContact_expectation_le_diagram [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    ENNReal.ofReal (∫ ω, fullLargeContact G x y 0 ω ∂law p) ≤ russoDiagram G p x y := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_fullContact_subcritical G hloc hqt p hp x y)
    (Eventually.of_forall (fullLargeContact_nonneg G x y 0))]
  rw [fullContact_lintegral_eq_kernel G hloc p x y (subcritical_cluster_finite_ae G p hp x)]
  exact clusterPairKernel_distinct_bound G p (indexedEdgeKernel G) x y

theorem russoDiagram_mono [Countable V] [Countable E] (G : BondGraph V E)
    (p q : unitInterval) (hpq : p ≤ q) (x y : V) : russoDiagram G p x y ≤ russoDiagram G q x y := by
  exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
    mul_le_mul_right (mul_le_mul' (conn_probability_mono G p q hpq x a)
      (conn_probability_mono G p q hpq y b)) _))

theorem russoDiagram_row_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ x, ∑' y, law p {ω | Conn G ω x y} ≤ C) (x : V) :
    (∑' y, russoDiagram G p x y) ≤ (d:ℝ≥0∞)*C^2 := by
  unfold russoDiagram
  rw [ENNReal.tsum_comm]
  calc
    _ = ∑' a, ∑' b, indexedEdgeKernel G a b * law p {ω | Conn G ω x a} *
        ∑' y, law p {ω | Conn G ω b y} := by
      apply tsum_congr; intro a
      rw [ENNReal.tsum_comm]
      apply tsum_congr; intro b
      simp_rw [←mul_assoc,conn_probability_symm G p _ b]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' a, ∑' b, indexedEdgeKernel G a b * law p {ω | Conn G ω x a} * C := by
      exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b => mul_le_mul_right (hC b) _))
    _ = ∑' a, (degree G a:ℝ≥0∞) * law p {ω | Conn G ω x a} * C := by
      apply tsum_congr; intro a
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_right,indexedEdgeKernel_row G hloc a]
    _ ≤ ∑' a, (d:ℝ≥0∞) * law p {ω | Conn G ω x a} * C := by
      exact ENNReal.tsum_le_tsum (fun a => mul_le_mul_left (mul_le_mul_left (show (degree G a:ℝ≥0∞) ≤ (d:ℝ≥0∞) by exact_mod_cast hd a) _) _)
    _ = (d:ℝ≥0∞)*(∑' a, law p {ω | Conn G ω x a})*C := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _ ≤ (d:ℝ≥0∞)*C^2 := by
      rw [pow_two,←mul_assoc]
      exact mul_le_mul_left (mul_le_mul_right (hC x) _) _

end RussoDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoMajorant
attribute [local instance] Classical.propDecidable Classical.decEq

theorem russoDiagram_row_ne_top [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x : V) : (∑' y, russoDiagram G b x y) ≠ ⊤ := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  obtain ⟨C,_,hC⟩ := subcritical_ennreal_row_bound G hloc hqt b hb
  exact ne_top_of_le_ne_top (by finiteness) (russoDiagram_row_bound G hloc d hd b _ hC x)

theorem russoDiagram_ne_top [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x y : V) : russoDiagram G b x y ≠ ⊤ :=
  ne_top_of_le_ne_top (russoDiagram_row_ne_top G hloc hqt b hb x) (ENNReal.le_tsum y)

theorem summable_russoMajorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x : V) : Summable (russoMajorant G b x) :=
  (ENNReal.summable_toReal (russoDiagram_row_ne_top G hloc hqt b hb x)).div_const _

theorem russoSlope_nonneg (G : BondGraph V E) (x y : V) (t : ℝ) (ht : t ≤ 1) :
    0 ≤ russoSlope G x y t := by
  exact div_nonneg (integral_nonneg (fullLargeContact_nonneg G x y 0)) (sub_nonneg.mpr ht)

theorem russoSlope_le_majorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b p : unitInterval) (hb : b < pc G) (hp : p ≤ b) (x y : V) :
    russoSlope G x y (p:ℝ) ≤ russoMajorant G b x y := by
  have hp' := hp.trans_lt hb
  have he := (fullContact_expectation_le_diagram G hloc hqt p hp' x y).trans (russoDiagram_mono G p b hp x y)
  have hn : 0 ≤ ∫ ω, fullLargeContact G x y 0 ω ∂law p := integral_nonneg (fullLargeContact_nonneg G x y 0)
  have hc : (∫ ω, fullLargeContact G x y 0 ω ∂law p) ≤ (russoDiagram G b x y).toReal := by
    simpa only [ENNReal.toReal_ofReal hn] using ENNReal.toReal_mono (russoDiagram_ne_top G hloc hqt b hb x y) he
  simp only [russoSlope,realContactExpectation_coe,russoMajorant]
  exact div_le_div₀ ENNReal.toReal_nonneg hc (sub_pos.mpr ((show (b:ℝ) < (pc G:ℝ) from hb).trans_le (pc G).2.2)) (sub_le_sub_left (show (p:ℝ) ≤ (b:ℝ) from hp) 1)

theorem hasDerivAt_realTwoPoint_slope [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 (pc G:ℝ)) (x y : V) :
    HasDerivAt (realTwoPoint G x y) (russoSlope G x y t) t := by
  let p : unitInterval := ⟨t, ht.1.le,ht.2.le.trans (pc G).2.2⟩
  change HasDerivAt (realTwoPoint G x y) (russoSlope G x y (p:ℝ)) (p:ℝ)
  simpa only [russoSlope,realContactExpectation_coe] using hasDerivAt_realTwoPoint_subcritical G hloc hqt p ht.1 ht.2 x y

end RussoMajorant
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



theorem simplePath_disjoint_at (G : BondGraph V E) (S : Set E) {x y z : V}
    (q : (openSimpleGraph G S).Walk x y) (hq : q.IsPath) (hz : z ∈ q.support) :
    S ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} := by
  obtain ⟨a,ha,hea,hoa⟩ := walk_lift_bonds G S (q.takeUntil z hz)
  obtain ⟨b,hb,heb,hob⟩ := walk_lift_bonds G S (q.dropUntil z hz)
  refine ⟨a.toFinset,b.toFinset,?_,?_,?_,?_,?_⟩
  · intro e he; exact hoa e (List.mem_toFinset.mp he)
  · intro e he; exact hob e (List.mem_toFinset.mp he)
  · apply Finset.disjoint_left.mpr
    intro e hae hbe
    exact List.disjoint_left.mp (hq.isTrail.disjoint_edges_takeUntil_dropUntil hz)
      (hea ▸ List.mem_map_of_mem (List.mem_toFinset.mp hae))
      (heb ▸ List.mem_map_of_mem (List.mem_toFinset.mp hbe))
  · exact ha.conn (fun e he => List.mem_toFinset.mpr he)
  · exact hb.conn (fun e he => List.mem_toFinset.mpr he)

end DeletionGeometry
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

theorem reachBall_ncard_le_pow (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (x : V) (k : ℕ) :
    (reachBall G x k).ncard ≤ (d+1)^k := by
  induction k with
  | zero => simp only [reachBall,Set.ncard_singleton,pow_zero,le_refl]
  | succ k ih =>
    let W := (finite_reachBall hloc x k).toFinset
    have he : reachBall G x (k+1) = (W ∪ W.biUnion (neighbors G hloc) : Finset V) := by
      ext z
      simp only [reachBall,Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,Finset.mem_coe,
        Finset.mem_union,Finset.mem_biUnion,mem_neighbors,Set.Finite.mem_toFinset,W,Adj,exists_prop]
    rw [he,Set.ncard_coe_finset]
    have hb : (W.biUnion (neighbors G hloc)).card ≤ W.card*d :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun a _ => (neighbors_card_le_degree G hloc a).trans (hd a))
    have hi : W.card ≤ (d+1)^k := by simpa only [W,←Set.ncard_eq_toFinset_card] using ih
    calc
      _ ≤ W.card + (W.biUnion (neighbors G hloc)).card := Finset.card_union_le _ _
      _ ≤ W.card + W.card*d := Nat.add_le_add_left hb _
      _ = W.card*(d+1) := by ring
      _ ≤ (d+1)^k*(d+1) := Nat.mul_le_mul_right _ hi
      _ = _ := (pow_succ _ _).symm

end CorridorSizeBounds
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_CollisionTails
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePropagation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_exists_short_walk (G : BondGraph V E) (x : V) (k : ℕ) {y : V}
    (hy : y ∈ reachBall G x k) :
    ∃ q : (openSimpleGraph G Set.univ).Walk x y, q.length ≤ k := by
  induction k generalizing y with
  | zero =>
    have he : y = x := hy
    subst y
    exact ⟨.nil,by simp⟩
  | succ k ih =>
    rcases hy with hy | hy
    · obtain ⟨q,hq⟩ := ih hy
      exact ⟨q,hq.trans (Nat.le_succ _)⟩
    · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy
      obtain ⟨z,hz,hzy⟩ := hy
      obtain ⟨q,hq⟩ := ih hz
      by_cases he : z = y
      · subst z
        exact ⟨q,hq.trans (Nat.le_succ _)⟩
      · let h : (openSimpleGraph G Set.univ).Adj z y :=
          (openSimpleGraph_univ_adj G z y).mpr ⟨he,hzy⟩
        refine ⟨q.append (.cons h .nil),?_⟩
        simpa only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.length_nil,zero_add] using Nat.add_le_add_right hq 1

end FinitePropagation
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BoundaryMultiplicity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem mem_reachBall_symm (G : BondGraph V E) (x y : V) (M : ℕ)
    (hy : y ∈ reachBall G x M) : x ∈ reachBall G y M := by
  obtain ⟨q,hq⟩ := reachBall_exists_short_walk G x M hy
  obtain ⟨l,hl,he,_⟩ := walk_lift_bonds G Set.univ q.reverse
  have hlen : l.length ≤ M := by
    have hh := congrArg List.length he
    have hh' : l.length = q.length := by
      simpa only [List.length_map,SimpleGraph.Walk.length_edges,
        SimpleGraph.Walk.length_reverse] using hh
    exact hh'.le.trans hq
  exact reachBall_mono G y hlen hl.mem_reachBall

theorem ball_multiplicity_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (M : ℕ) (W : Finset V)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ a ∈ W, ∑ c ∈ W, if c ∈ reachBall G a M then f c else 0) ≤
      ((d+1)^M : ℕ) * ∑ c ∈ W, f c := by
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hs : W.filter (fun a => c ∈ reachBall G a M) ⊆
      (finite_reachBall hloc c M).toFinset := by
    intro a ha
    exact (finite_reachBall hloc c M).mem_toFinset.mpr
      (mem_reachBall_symm G a c M (Finset.mem_filter.mp ha).2)
  have hn : (W.filter (fun a => c ∈ reachBall G a M)).card ≤ (d+1)^M := by
    apply (Finset.card_le_card hs).trans
    simpa only [←Set.ncard_eq_toFinset_card] using
      reachBall_ncard_le_pow G hloc d hd c M
  calc
    _ = ((W.filter (fun a => c ∈ reachBall G a M)).card : ℝ) * f c := by
      rw [←Finset.sum_filter]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (hf c)

theorem deletedBoundaryPotential_sum_bound (G : BondGraph V E)
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (M : ℕ) (W : Finset V) (p : unitInterval) :
    (∑ a ∈ W, deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M) ≤
      ((d+1)^M : ℕ) *
        ∑ c ∈ W, ∑ b ∈ neighbors G hloc c,
          inducedSusceptibility G (W : Set V)ᶜ p b := by
  let f (c : V) := ∑ b ∈ neighbors G hloc c,
    inducedSusceptibility G (W : Set V)ᶜ p b
  have he (a : V) :
      deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M =
        ∑ c ∈ W, if c ∈ reachBall G a M then f c else 0 := by
    unfold deletedBoundaryPotential
    simp only [Set.mem_compl_iff,Finset.mem_coe,not_not]
    have hs : (finite_reachBall hloc a M).toFinset.filter (· ∈ W) =
        W.filter (fun c => c ∈ reachBall G a M) := by
      ext c
      simp only [Finset.mem_filter,Set.Finite.mem_toFinset]
      exact and_comm
    rw [hs,Finset.sum_filter]
  simp_rw [he]
  exact ball_multiplicity_bound G hloc d hd M W f
    (fun c => Finset.sum_nonneg (fun b _ => inducedSusceptibility_nonneg G _ p b))

theorem inducedSusceptibility_ball_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : Set V)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (a b : V) (M : ℕ)
    (ha : a ∉ D) (hb : b ∈ reachBall G a M)
    (hfin : ∀ c, Summable (fun z => (law p).real
      {η | Conn G (η ∩ internalEdges G D) c z})) :
    inducedSusceptibility G D p b ≤
      (p : ℝ)^(-(M : ℤ)) * deletedBoundaryPotential G hloc D p a M := by
  obtain ⟨q,hq⟩ := reachBall_exists_short_walk G a M hb
  obtain ⟨l,hl,he,ho⟩ := walk_lift_bonds G Set.univ q
  have hlen : l.length ≤ M := by
    have hh : l.length = q.length := by
      simpa only [List.length_map,SimpleGraph.Walk.length_edges] using congrArg List.length he
    exact hh.le.trans hq
  have hh := short_path_deleted_potential_bound G hloc D p hp Set.univ a b M
    l hl hlen ho hfin
  simpa only [deletedLocalPotential,ite_eq_right ha,zero_add] using hh

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SusceptibilityDerivative
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_russoSlope [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun y => russoSlope G x y (p : ℝ)) := by
  exact (summable_russoMajorant G hloc hqt p hp x).of_nonneg_of_le
    (fun y => russoSlope_nonneg G x y p p.2.2)
    (fun y => russoSlope_le_majorant G hloc hqt p p hp le_rfl x y)

theorem hasDerivAt_realSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (x : V) :
    HasDerivAt (realSusceptibility G x) (∑' y, russoSlope G x y (p : ℝ)) p := by
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  apply hasDerivAt_tsum_of_isPreconnected (summable_russoMajorant G hloc hqt b hb x)
    isOpen_Ioo isPreconnected_Ioo
    (fun y t ht => hasDerivAt_realTwoPoint_slope G hloc hqt t
      ⟨ht.1,lt_trans ht.2 hb⟩ x y)
    (fun y t ht => ?_) (show (p : ℝ) ∈ Set.Ioo 0 (b : ℝ) from ⟨hp0,hpb⟩)
    (by simpa only [realTwoPoint_coe] using summable_twoPoint_subcritical G hloc hqt p hp x)
    ⟨hp0,hpb⟩
  let q : unitInterval := ⟨t,ht.1.le,ht.2.le.trans b.2.2⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (russoSlope_nonneg G x y t q.2.2)]
  exact russoSlope_le_majorant G hloc hqt b q hb ht.2.le x y

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_DeletionBound
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem connection_or_first_deleted_vertex (G : BondGraph V E) (D : Set V)
    (ω : Set E) (x y : V) (hc : Conn G ω x y) :
    (x ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y) ∨
      ∃ z ∉ D, ω ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} := by
  obtain ⟨p₀⟩ := (conn_iff_reachable G ω x y).mp hc
  let p := p₀.toPath.val
  by_cases h : ∀ z ∈ p.support, z ∈ D
  · exact Or.inl ⟨h x p.start_mem_support,walk_conn_restrict_vertices G ω p D h⟩
  · push Not at h
    obtain ⟨z,hz,hzD⟩ := h
    exact Or.inr ⟨z,hzD,simplePath_disjoint_at G ω p p₀.toPath.property hz⟩

theorem first_hit_deletion_probability [Countable V] [Countable E]
    (G : BondGraph V E) (D : Set V) (p : unitInterval) (x y : V) :
    law p {ω | Conn G ω x y} ≤
      (if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0) +
      ∑' z, if z ∈ D then 0 else
        law p {ω | Conn G ω x z} * law p {ω | Conn G ω z y} := by
  let B : Set (Set E) := {ω | x ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y}
  let C (z : V) : Set (Set E) := if z ∈ D then ∅ else
    DisjointOccurrence {ω | Conn G ω x z} {ω | Conn G ω z y}
  have hc : {ω | Conn G ω x y} ⊆ B ∪ ⋃ z, C z := by
    intro ω hω
    rcases connection_or_first_deleted_vertex G D ω x y hω with hb | ⟨z,hz,hzω⟩
    · exact Or.inl hb
    · exact Or.inr (Set.mem_iUnion.mpr ⟨z,by simpa only [C,ite_eq_right hz] using hzω⟩)
  have hB : law p B = if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0 := by
    by_cases hx : x ∈ D <;> simp [B,hx]
  have hC (z : V) : law p (C z) ≤ if z ∈ D then 0 else
      law p {ω | Conn G ω x z} * law p {ω | Conn G ω z y} := by
    by_cases hz : z ∈ D
    · simp only [C,ite_eq_left hz,measure_empty,le_refl]
    · simp only [C,ite_eq_right hz]
      exact bk_ennreal p _ _
        (fun _ _ h hconn => conn_mono G h hconn)
        (fun _ _ h hconn => conn_mono G h hconn)
        (finiteWitness_conn G x z) (finiteWitness_conn G z y)
  calc
    _ ≤ law p B + law p (⋃ z, C z) := (measure_mono hc).trans (measure_union_le _ _)
    _ ≤ law p B + ∑' z, law p (C z) := add_le_add_right (measure_iUnion_le C) _
    _ ≤ _ := by rw [hB]; exact add_le_add_right (ENNReal.tsum_le_tsum hC) _

theorem ennreal_inducedSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Set V) (x : V) :
    ENNReal.ofReal (inducedSusceptibility G D p x) =
      ∑' y, if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0 := by
  by_cases hx : x ∈ D
  · simp only [inducedSusceptibility,ite_eq_left hx,restrictedSusceptibility]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg)
      (summable_restrictedTwoPoint G hloc hqt p hp _ x)]
    exact tsum_congr (fun _ => ENNReal.ofReal_toReal (measure_ne_top _ _))
  · simp only [inducedSusceptibility,ite_eq_right hx,ENNReal.ofReal_zero,tsum_zero]

theorem susceptibility_deletion_ennreal [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Set V) (C : ℝ≥0∞)
    (hC : ∀ z, ENNReal.ofReal (susceptibility G p z) ≤ C) (x : V) :
    ENNReal.ofReal (susceptibility G p x) ≤
      ENNReal.ofReal (inducedSusceptibility G D p x) +
        (∑' z, if z ∈ D then 0 else law p {ω | Conn G ω x z}) * C := by
  rw [ennreal_susceptibility G hloc hqt p hp x,
    ennreal_inducedSusceptibility G hloc hqt p hp D x]
  calc
    _ ≤ ∑' y, ((if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0) +
        ∑' z, if z ∈ D then 0 else law p {ω | Conn G ω x z} * law p {ω | Conn G ω z y}) :=
      ENNReal.tsum_le_tsum (first_hit_deletion_probability G D p x)
    _ = (∑' y, if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0) +
        ∑' z, (if z ∈ D then 0 else law p {ω | Conn G ω x z}) *
          (∑' y, law p {ω | Conn G ω z y}) := by
      rw [ENNReal.tsum_add,ENNReal.tsum_comm]
      congr 1
      apply tsum_congr
      intro z
      by_cases hz : z ∈ D
      · simp only [ite_eq_left hz,tsum_zero,zero_mul]
      · simp only [ite_eq_right hz,ENNReal.tsum_mul_left]
    _ ≤ _ := by
      apply add_le_add_right
      rw [←ENNReal.tsum_mul_right]
      apply ENNReal.tsum_le_tsum
      intro z
      rw [←ennreal_susceptibility G hloc hqt p hp z]
      exact mul_le_mul' le_rfl (hC z)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_DeletionLoss
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem connection_measure_symm (G : BondGraph V E) (p : unitInterval) (x y : V) :
    law p {ω | Conn G ω x y} = law p {ω | Conn G ω y x} := by
  congr 1
  ext ω
  exact ⟨conn_symm G ω,conn_symm G ω⟩

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_KernelDeletionDiagram
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem kernelDeletionDiagram_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (K : V → V → ℝ≥0∞)
    (ε : ℝ≥0∞) (hε : ∀ u, kernelTriangleDiagonal G p K u ≤ ε) (x : V) :
    kernelDeletionDiagram G p K x ≤ ε * ∑' u, law p {ω | Conn G ω x u} := by
  let f (a b z u : V) : ℝ≥0∞ := K a b * law p {ω | Conn G ω b z} *
    (law p {ω | Conn G ω x u} * law p {ω | Conn G ω u a} * law p {ω | Conn G ω u z})
  have hswap : (∑' a, ∑' b, ∑' z, ∑' u, f a b z u) =
      ∑' u, ∑' a, ∑' b, ∑' z, f a b z u := by
    calc
      _ = ∑' a, ∑' b, ∑' u, ∑' z, f a b z u :=
        tsum_congr (fun _ => tsum_congr (fun _ => ENNReal.tsum_comm))
      _ = ∑' a, ∑' u, ∑' b, ∑' z, f a b z u :=
        tsum_congr (fun _ => ENNReal.tsum_comm)
      _ = _ := ENNReal.tsum_comm
  calc
    _ ≤ ∑' a, ∑' b, ∑' z, K a b * law p {ω | Conn G ω b z} *
        (∑' u, law p {ω | Conn G ω x u} * law p {ω | Conn G ω u a} *
          law p {ω | Conn G ω u z}) :=
      ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
        ENNReal.tsum_le_tsum (fun z => mul_le_mul' le_rfl (three_arm_bound G p x a z))))
    _ = ∑' a, ∑' b, ∑' z, ∑' u, f a b z u := by
      simp only [f,ENNReal.tsum_mul_left]
    _ = ∑' u, ∑' a, ∑' b, ∑' z, f a b z u := hswap
    _ = ∑' u, law p {ω | Conn G ω x u} * kernelTriangleDiagonal G p K u := by
      apply tsum_congr
      intro u
      simp only [kernelTriangleDiagonal,←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro a
      apply tsum_congr
      intro b
      apply tsum_congr
      intro z
      dsimp only [f]
      ring
    _ ≤ ∑' u, law p {ω | Conn G ω x u} * ε :=
      ENNReal.tsum_le_tsum (fun u => mul_le_mul' le_rfl (hε u))
    _ = _ := by rw [ENNReal.tsum_mul_right,mul_comm]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_KernelDeletionOperator
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem kernelTriangleDiagonal_eq_matrix [Countable E]
    (G : BondGraph V E) (p : unitInterval)
    (T K : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (hK : PositiveRealMatrix K) (u : V) :
    kernelTriangleDiagonal G p (ennMatrixCoeff K) u =
      ennMatrixCoeff (T * (K * (T*T))) u u := by
  have ht := hT.positiveRealMatrix G p T
  rw [ennMatrixCoeff_mul ht (hK.mul (ht.mul ht))]
  apply tsum_congr
  intro a
  rw [ennMatrixCoeff_mul hK (ht.mul ht),←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  rw [ennMatrixCoeff_mul ht ht,←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  simp only [hT.ennMatrixCoeff G p T,connection_measure_symm G p u z]
  ring

theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  change ‖A (lp.single 2 y (1 : ℂ)) x‖ ≤ ‖A‖
  apply (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (A (lp.single 2 y (1 : ℂ))) x).trans
  simpa only [lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one,mul_one] using
    A.le_opNorm (lp.single 2 y (1 : ℂ))

theorem kernelTriangleDiagonal_norm_bound [Countable E]
    (G : BondGraph V E) (p : unitInterval)
    (T K : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (hK : PositiveRealMatrix K) (u : V) :
    kernelTriangleDiagonal G p (ennMatrixCoeff K) u ≤ ENNReal.ofReal (‖T‖ ^ 3 * ‖K‖) := by
  rw [kernelTriangleDiagonal_eq_matrix G p T K hT hK u]
  apply ENNReal.ofReal_le_ofReal
  apply (Complex.re_le_norm _).trans ((matrixCoeff_norm_le _ u u).trans _)
  calc
    ‖T * (K * (T*T))‖ ≤ ‖T‖ * ‖K * (T*T)‖ := norm_mul_le _ _
    _ ≤ ‖T‖ * (‖K‖ * ‖T*T‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖T‖ * (‖K‖ * (‖T‖ * ‖T‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem connection_measure_mono [Countable V] [Countable E] (G : BondGraph V E) (x y : V)
    {p q : unitInterval} (hpq : p ≤ q) :
    law p {ω | Conn G ω x y} ≤ law q {ω | Conn G ω x y} := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact twoPoint_mono G x y hpq

theorem kernelTriangleDiagonal_mono [Countable V] [Countable E] (G : BondGraph V E)
    (K : V → V → ℝ≥0∞) (u : V) {p q : unitInterval} (hpq : p ≤ q) :
    kernelTriangleDiagonal G p K u ≤ kernelTriangleDiagonal G q K u := by
  apply ENNReal.tsum_le_tsum
  intro a
  apply ENNReal.tsum_le_tsum
  intro b
  apply ENNReal.tsum_le_tsum
  intro z
  exact mul_le_mul' (mul_le_mul'
    (mul_le_mul' (connection_measure_mono G u a hpq) le_rfl)
    (connection_measure_mono G b z hpq)) (connection_measure_mono G u z hpq)

theorem kernelDeletionDiagram_le_critical_norm [Countable V] [Countable E]
    (G : BondGraph V E) (T K : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G (pc G) T) (hK : PositiveRealMatrix K)
    (p : unitInterval) (hp : p ≤ pc G) (x : V) :
    kernelDeletionDiagram G p (ennMatrixCoeff K) x ≤
      ENNReal.ofReal (‖T‖ ^ 3 * ‖K‖) * ∑' u, law p {ω | Conn G ω x u} := by
  apply kernelDeletionDiagram_bound
  intro u
  exact (kernelTriangleDiagonal_mono G (ennMatrixCoeff K) u hp).trans
    (kernelTriangleDiagonal_norm_bound G (pc G) T K hT hK u)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ExteriorConnection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_exteriorSusceptibility [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x b : V) :
    Measurable (exteriorSusceptibility G p x b) :=
  (measurable_freshExteriorMoment G p x b).div
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_cluster_ncard G hloc x))

theorem exteriorSusceptibility_nonneg (G : BondGraph V E) (p : unitInterval)
    (x b : V) (ω : Set E) : 0 ≤ exteriorSusceptibility G p x b ω :=
  div_nonneg (freshExteriorMoment_nonneg G p x b ω) (Nat.cast_nonneg _)

theorem exteriorSusceptibility_eq (G : BondGraph V E) (p : unitInterval)
    (x b : V) (ω : Set E) (hf : (cluster G ω x).Finite) :
    exteriorSusceptibility G p x b ω = inducedSusceptibility G (cluster G ω x)ᶜ p b := by
  have hn : ((cluster G ω x).ncard : ℝ) ≠ 0 := by
    exact_mod_cast (cluster_ncard_pos G ω x hf).ne'
  exact mul_div_cancel_left₀ _ hn

theorem connection_exterior_comparison [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (C : ℝ≥0∞)
    (hC : ∀ z, ENNReal.ofReal (susceptibility G p z) ≤ C) (x a b : V) :
    law p {ω | Conn G ω x a} * ENNReal.ofReal (susceptibility G p b) ≤
      exteriorConnectionMoment G p x a b + C *
        ∑' z, law p {ω | Conn G ω x a ∧ Conn G ω x z} *
          law p {ω | Conn G ω b z} := by
  let F (ω : Set E) : ℝ≥0∞ := if Conn G ω x a then
    ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0
  let H (z : V) (ω : Set E) : ℝ≥0∞ := if Conn G ω x a ∧ Conn G ω x z then
    law p {η | Conn G η b z} else 0
  have hF : Measurable F := Measurable.ite (measurableSet_conn G x a)
    (ENNReal.measurable_ofReal.comp (measurable_exteriorSusceptibility G hloc p x b))
    measurable_const
  have hH (z : V) : Measurable (H z) := Measurable.ite
    ((measurableSet_conn G x a).inter (measurableSet_conn G x z))
    measurable_const measurable_const
  have hd : (fun ω => if Conn G ω x a then ENNReal.ofReal (susceptibility G p b) else 0)
      ≤ᵐ[law p] fun ω => F ω + C * ∑' z, H z ω := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hf
    by_cases ha : Conn G ω x a
    · simp only [ite_eq_left ha,F]
      rw [exteriorSusceptibility_eq G p x b ω hf]
      have hh := susceptibility_deletion_ennreal G hloc hqt p hp (cluster G ω x)ᶜ C hC b
      simpa only [Set.mem_compl_iff,cluster,Set.mem_ofPred_eq,ite_not,H,
        ha,true_and,mul_comm] using hh
    · simp only [ite_eq_right ha,F,H,ha,false_and,if_false,tsum_zero,mul_zero,
        add_zero,le_refl]
  have hi := lintegral_mono_ae hd
  have hleft : (∫⁻ ω, if Conn G ω x a then ENNReal.ofReal (susceptibility G p b)
      else 0 ∂law p) = law p {ω | Conn G ω x a} * ENNReal.ofReal (susceptibility G p b) := by
    simpa only [Set.indicator,Set.mem_ofPred_eq,mul_comm] using
      lintegral_indicator_const (measurableSet_conn G x a) (ENNReal.ofReal (susceptibility G p b))
  have hr : (∫⁻ ω, F ω + C * ∑' z, H z ω ∂law p) =
      exteriorConnectionMoment G p x a b + C *
        ∑' z, law p {ω | Conn G ω x a ∧ Conn G ω x z} * law p {ω | Conn G ω b z} := by
    rw [lintegral_add_left hF,lintegral_const_mul _ (Measurable.tsum hH),
      lintegral_tsum (fun z => (hH z).aemeasurable)]
    congr 2
    apply tsum_congr
    intro z
    have hs : MeasurableSet {ω | Conn G ω x a ∧ Conn G ω x z} :=
      (measurableSet_conn G x a).inter (measurableSet_conn G x z)
    simpa only [H,Set.indicator,Set.mem_ofPred_eq,mul_comm] using
      lintegral_indicator_const hs (law p {ω | Conn G ω b z})
  rwa [hleft,hr] at hi

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_KernelExterior
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem kernelExteriorPotential_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (K : V → V → ℝ≥0∞)
    (hK : ∀ a, ∑' b, K a b = 1) (c C : ℝ≥0∞)
    (hc : ∀ b, c ≤ ENNReal.ofReal (susceptibility G p b))
    (hC : ∀ b, ENNReal.ofReal (susceptibility G p b) ≤ C) (x : V) :
    c * (∑' a, law p {ω | Conn G ω x a}) ≤
      kernelExteriorPotential G p K x + C * kernelDeletionDiagram G p K x := by
  calc
    _ = ∑' a, ∑' b, K a b *
        (law p {ω | Conn G ω x a} * c) := by
      simp only [ENNReal.tsum_mul_right,hK,one_mul,mul_comm c]
    _ ≤ ∑' a, ∑' b, K a b *
        (law p {ω | Conn G ω x a} * ENNReal.ofReal (susceptibility G p b)) :=
      ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hc b))))
    _ ≤ ∑' a, ∑' b, K a b *
        (exteriorConnectionMoment G p x a b + C *
          ∑' z, law p {ω | Conn G ω x a ∧ Conn G ω x z} * law p {ω | Conn G ω b z}) :=
      ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
        mul_le_mul' le_rfl (connection_exterior_comparison G hloc hqt p hp C hC x a b)))
    _ = _ := by
      simp only [mul_add,ENNReal.tsum_add,kernelExteriorPotential,kernelDeletionDiagram]
      congr 1
      simp only [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro a
      apply tsum_congr
      intro b
      apply tsum_congr
      intro z
      ring

theorem kernelExteriorPotential_lower_of_critical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T K : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G (pc G) T) (hK : PositiveRealMatrix K)
    (hrow : ∀ a, ∑' b, ennMatrixCoeff K a b = 1) (c C : ℝ≥0∞)
    (hc : ∀ b, c ≤ ENNReal.ofReal (susceptibility G p b))
    (hC : ∀ b, ENNReal.ofReal (susceptibility G p b) ≤ C) (x : V) :
    c * ENNReal.ofReal (susceptibility G p x) ≤
      kernelExteriorPotential G p (ennMatrixCoeff K) x +
        C * ENNReal.ofReal (‖T‖^3 * ‖K‖) * ENNReal.ofReal (susceptibility G p x) := by
  have hh := kernelExteriorPotential_lower G hloc hqt p hp (ennMatrixCoeff K) hrow c C hc hC x
  rw [←ennreal_susceptibility G hloc hqt p hp x] at hh
  apply hh.trans
  apply add_le_add_right
  have he := kernelDeletionDiagram_le_critical_norm G T K hT hK p hp.le x
  rw [←ennreal_susceptibility G hloc hqt p hp x] at he
  simpa only [mul_assoc] using mul_le_mul' (le_refl C) he

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ExteriorExposure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exteriorSusceptibility_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x b : V) (ω : Set E) :
    exteriorSusceptibility G p x b ω ≤ susceptibility G p b := by
  by_cases hf : (cluster G ω x).Finite
  · rw [exteriorSusceptibility_eq G p x b ω hf]
    exact inducedSusceptibility_le_susceptibility G hloc hqt p hp _ b
  · simp only [exteriorSusceptibility,Set.Infinite.ncard hf,Nat.cast_zero,div_zero]
    exact susceptibility_nonneg G p b

theorem integrable_exteriorSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x b : V) :
    Integrable (exteriorSusceptibility G p x b) (law p) := by
  apply (integrable_const (susceptibility G p b)).mono'
    (measurable_exteriorSusceptibility G hloc p x b).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_of_nonneg (exteriorSusceptibility_nonneg G p x b ω)]
    exact exteriorSusceptibility_le G hloc hqt p hp x b ω)

theorem integral_exterior_connection [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    (∫ ω, (if Conn G ω x a then exteriorSusceptibility G p x b ω else 0) ∂law p) =
      ∫ ω, (if Conn G ω x a ∧ ¬Conn G ω x b then
        ((cluster G ω b).ncard : ℝ) else 0) ∂law p := by
  have hl : Integrable (fun ω => if Conn G ω x a then
      exteriorSusceptibility G p x b ω else 0) (law p) :=
    (integrable_exteriorSusceptibility G hloc hqt p hp x b).indicator
      (measurableSet_conn G x a)
  have hr : Integrable (fun ω => if Conn G ω x a ∧ ¬Conn G ω x b then
      ((cluster G ω b).ncard : ℝ) else 0) (law p) := by
    have hs : MeasurableSet {ω | Conn G ω x a ∧ ¬Conn G ω x b} :=
      (measurableSet_conn G x a).inter (measurableSet_conn G x b).compl
    apply ((susceptibility_eq_integral G hloc hqt p hp b).1.indicator hs).congr
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases h : Conn G ω x a ∧ ¬Conn G ω x b <;> simp [h])
  rw [integral_cluster_finite_partition G p hp x _ hl,
    integral_cluster_finite_partition G p hp x _ hr]
  apply tsum_congr
  intro W
  by_cases ha : a ∈ W
  · have hleft : (∫ ω, (if cluster G ω x = (W : Set V) then
        (if Conn G ω x a then exteriorSusceptibility G p x b ω else 0) else 0) ∂law p) =
        inducedSusceptibility G (W : Set V)ᶜ p b *
          (law p).real {ω | cluster G ω x = (W : Set V)} := by
      rw [←integral_event_indicator p _ (measurableSet_cluster_eq G x W),
        ←integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hc : cluster G ω x = (W : Set V)
        · have hca : Conn G ω x a := by
            change a ∈ cluster G ω x
            rw [hc]
            exact ha
          have hf : (cluster G ω x).Finite := by rw [hc]; exact W.finite_toSet
          simp only [hc,if_true,hca,exteriorSusceptibility_eq G p x b ω hf,mul_one,
            Set.mem_ofPred_eq]
        · simp only [hc,if_false,Set.mem_ofPred_eq,mul_zero])
    have hright : (∫ ω, (if cluster G ω x = (W : Set V) then
        (if Conn G ω x a ∧ ¬Conn G ω x b then ((cluster G ω b).ncard : ℝ) else 0)
        else 0) ∂law p) =
        (law p).real {ω | cluster G ω x = (W : Set V)} *
          inducedSusceptibility G (W : Set V)ᶜ p b := by
      rw [←cluster_cell_exterior_susceptibility G hloc hqt p hp W x b]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hc : cluster G ω x = (W : Set V)
        · have hca : Conn G ω x a := by change a ∈ cluster G ω x; rwa [hc]
          simp only [hc,if_true,hca,true_and]
        · simp only [hc,if_false,false_and])
    rw [hleft,hright,mul_comm]
  · have hz (ω : Set E) (hc : cluster G ω x = (W : Set V)) : ¬Conn G ω x a := by
      intro h
      have hh : a ∈ cluster G ω x := h
      rw [hc] at hh
      exact ha hh
    have he : (fun ω => if cluster G ω x = (W : Set V) then
        (if Conn G ω x a then exteriorSusceptibility G p x b ω else 0) else 0) =
        fun _ => (0 : ℝ) := by
      funext ω
      by_cases hc : cluster G ω x = (W : Set V)
      · simp only [hc,if_true,ite_eq_right (hz ω hc)]
      · exact ite_eq_right hc
    rw [he,integral_zero]
    symm
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall (fun ω => by
      change (if cluster G ω x = (W : Set V) then
        (if Conn G ω x a ∧ ¬Conn G ω x b then ((cluster G ω b).ncard : ℝ) else 0)
        else 0) = 0
      by_cases hc : cluster G ω x = (W : Set V)
      · simp only [hc,if_true,hz ω hc,false_and,if_false]
      · exact ite_eq_right hc)

theorem exteriorConnectionMoment_eq_tsum [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    exteriorConnectionMoment G p x a b =
      ∑' y, law p {ω | (Conn G ω x a ∧ ¬Conn G ω x b) ∧ Conn G ω b y} := by
  have hi : Integrable (fun ω => if Conn G ω x a then
      exteriorSusceptibility G p x b ω else 0) (law p) :=
    (integrable_exteriorSusceptibility G hloc hqt p hp x b).indicator
      (measurableSet_conn G x a)
  have hn (ω : Set E) : 0 ≤ (if Conn G ω x a then
      exteriorSusceptibility G p x b ω else 0) := by
    split_ifs
    · exact exteriorSusceptibility_nonneg G p x b ω
    · rfl
  have he : exteriorConnectionMoment G p x a b = ENNReal.ofReal
      (∫ ω, (if Conn G ω x a then exteriorSusceptibility G p x b ω else 0) ∂law p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)]
    apply lintegral_congr
    intro ω
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  have hsEvent : MeasurableSet {ω | Conn G ω x a ∧ ¬Conn G ω x b} :=
    (measurableSet_conn G x a).inter (measurableSet_conn G x b).compl
  have hv := integral_cluster_size_event G hloc hqt p hp b _ hsEvent
  have hv' : (∫ ω, (if Conn G ω x a ∧ ¬Conn G ω x b then
      ((cluster G ω b).ncard : ℝ) else 0) ∂law p) =
      ∑' y, (law p).real {ω | (Conn G ω x a ∧ ¬Conn G ω x b) ∧ Conn G ω b y} := by
    convert hv using 1
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases h : Conn G ω x a ∧ ¬Conn G ω x b <;> simp [h])
    · rfl
  rw [he,integral_exterior_connection G hloc hqt p hp x a b,hv']
  have hs : Summable (fun y => (law p).real
      {ω | (Conn G ω x a ∧ ¬Conn G ω x b) ∧ Conn G ω b y}) := by
    apply (summable_twoPoint_subcritical G hloc hqt p hp b).of_nonneg_of_le
      (fun _ => measureReal_nonneg)
    intro y
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun _ h => h.2))
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs]
  exact tsum_congr (fun _ => ENNReal.ofReal_toReal (measure_ne_top _ _))

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ExteriorContact
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinct_exterior_event (G : BondGraph V E) (x a b y : V) :
    {ω | (Conn G ω x a ∧ ¬Conn G ω x b) ∧ Conn G ω b y} =
      {ω | ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b)} := by
  ext ω
  constructor
  · rintro ⟨⟨ha,hb⟩,hby⟩
    exact ⟨fun hxy => hb (conn_trans G ω hxy (conn_symm G ω hby)),
      ha,conn_symm G ω hby⟩
  · rintro ⟨hxy,ha,hyb⟩
    exact ⟨⟨ha,fun hb => hxy (conn_trans G ω hb (conn_symm G ω hyb))⟩,
      conn_symm G ω hyb⟩

theorem lintegral_distinctClusterPair [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (J : V → V → ℝ≥0∞) (x y : V) :
    (∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p) =
      ∑' a, ∑' b, J a b *
        law p {ω | ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b)} := by
  let F (a b : V) (ω : Set E) : ℝ≥0∞ :=
    if ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b) then J a b else 0
  have hF (a b : V) : Measurable (F a b) := Measurable.ite
    ((measurableSet_conn G x y).compl.inter
      ((measurableSet_conn G x a).inter (measurableSet_conn G y b)))
    measurable_const measurable_const
  have he (ω : Set E) : (if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0) =
      ∑' a, ∑' b, F a b ω := by
    by_cases hxy : Conn G ω x y
    · simp only [hxy,not_true_eq_false,if_false,F,false_and,tsum_zero]
    · simp only [hxy,not_false_eq_true,if_true,F,true_and,clusterPairKernel]
  simp_rw [he]
  rw [lintegral_tsum (fun a => (Measurable.tsum (hF a)).aemeasurable)]
  apply tsum_congr
  intro a
  rw [lintegral_tsum (fun b => (hF a b).aemeasurable)]
  apply tsum_congr
  intro b
  have hs : MeasurableSet {ω | ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b)} :=
    (measurableSet_conn G x y).compl.inter
      ((measurableSet_conn G x a).inter (measurableSet_conn G y b))
  simpa only [F,Set.indicator,Set.mem_ofPred_eq] using lintegral_indicator_const hs (J a b)

theorem kernelExteriorPotential_eq_distinctClusterPair [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (J : V → V → ℝ≥0∞) (x : V) :
    kernelExteriorPotential G p J x =
      ∑' y, ∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p := by
  unfold kernelExteriorPotential
  simp_rw [exteriorConnectionMoment_eq_tsum G hloc hqt p hp,
    distinct_exterior_event G,lintegral_distinctClusterPair G p J x,
    ←ENNReal.tsum_mul_left]
  calc
    _ = ∑' a, ∑' y, ∑' b, J a b *
        law p {ω | ¬Conn G ω x y ∧ (Conn G ω x a ∧ Conn G ω y b)} :=
      tsum_congr (fun _ => ENNReal.tsum_comm)
    _ = _ := ENNReal.tsum_comm

theorem kernelExteriorPotential_edge_eq_contact [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    kernelExteriorPotential G p (indexedEdgeKernel G) x =
      ∑' y, ENNReal.ofReal (∫ ω, fullLargeContact G x y 0 ω ∂law p) := by
  rw [kernelExteriorPotential_eq_distinctClusterPair G hloc hqt p hp]
  apply tsum_congr
  intro y
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_fullContact_subcritical G hloc hqt p hp x y)
    (Filter.Eventually.of_forall (fullLargeContact_nonneg G x y 0)),
    fullContact_lintegral_eq_kernel G hloc p x y (subcritical_cluster_finite_ae G p hp x)]

theorem kernelExteriorPotential_edge_eq_derivative [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (x : V) :
    kernelExteriorPotential G p (indexedEdgeKernel G) x =
      ENNReal.ofReal (1 - (p : ℝ)) * ENNReal.ofReal (deriv (realSusceptibility G x) p) := by
  rw [kernelExteriorPotential_edge_eq_contact G hloc hqt p hp,
    (hasDerivAt_realSusceptibility G hloc hqt p hp0 hp x).deriv,
    ENNReal.ofReal_tsum_of_nonneg (fun y => russoSlope_nonneg G x y p p.2.2)
      (summable_russoSlope G hloc hqt p hp x),←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro y
  have hp1 : 0 < 1 - (p : ℝ) := sub_pos.mpr ((show (p : ℝ) < (pc G : ℝ) from hp).trans_le (pc G).2.2)
  have he : (∫ ω, fullLargeContact G x y 0 ω ∂law p) =
      (1 - (p : ℝ)) * russoSlope G x y p := by
    rw [russoSlope,realContactExpectation_coe]
    field_simp
  rw [he,ENNReal.ofReal_mul hp1.le]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_KernelExteriorBound
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem adjacencyKernel_le_indexed (G : BondGraph V E) (a b : V) :
    (if Adj G a b then (1 : ℝ≥0∞) else 0) ≤ indexedEdgeKernel G a b := by
  by_cases h : Adj G a b
  · obtain ⟨e,he⟩ := h
    rw [ite_eq_left ⟨e,he⟩]
    change (1 : ℝ≥0∞) ≤ ∑' e, if G e = s(a,b) then 1 else 0
    simpa only [ite_eq_left he] using
      (ENNReal.le_tsum (f := fun e => if G e = s(a,b) then (1 : ℝ≥0∞) else 0) e)
  · simp only [ite_eq_right h,zero_le]

theorem neighborSusceptibility_le_edge_action (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (a : V) :
    ENNReal.ofReal (∑ b ∈ neighbors G hloc a, inducedSusceptibility G D p b) ≤
      ∑' b, indexedEdgeKernel G a b * ENNReal.ofReal (inducedSusceptibility G D p b) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => inducedSusceptibility_nonneg G D p b)]
  have he : (∑ b ∈ neighbors G hloc a, ENNReal.ofReal (inducedSusceptibility G D p b)) =
      ∑' b, (if Adj G a b then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (inducedSusceptibility G D p b) := by
    rw [tsum_eq_sum (s := neighbors G hloc a) (fun b hb => by
      rw [ite_eq_right (fun h => hb ((mem_neighbors G hloc a b).mpr h)),zero_mul])]
    apply Finset.sum_congr rfl
    intro b hb
    rw [ite_eq_left ((mem_neighbors G hloc a b).mp hb),one_mul]
  rw [he]
  exact ENNReal.tsum_le_tsum (fun b => mul_le_mul' (adjacencyKernel_le_indexed G a b) le_rfl)

theorem finite_kernel_exterior_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (d : ℕ) (hd : ∀ a, degree G a ≤ d) (M : ℕ) (K : V → V → ℝ≥0∞)
    (hrow : ∀ a, ∑' b, K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → K a b = 0)
    (W : Finset V) :
    (∑ a ∈ W, ∑' b, K a b * ENNReal.ofReal (inducedSusceptibility G (W : Set V)ᶜ p b)) ≤
      ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        ∑ a ∈ W, ∑' b, indexedEdgeKernel G a b *
          ENNReal.ofReal (inducedSusceptibility G (W : Set V)ᶜ p b) := by
  have hb (a : V) (ha : a ∈ W) :
      (∑' b, K a b * ENNReal.ofReal (inducedSusceptibility G (W : Set V)ᶜ p b)) ≤
        ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) *
          ENNReal.ofReal (deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M) := by
    calc
      _ ≤ ∑' b, K a b *
          (ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) *
            ENNReal.ofReal (deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M)) := by
        apply ENNReal.tsum_le_tsum
        intro b
        by_cases hball : b ∈ reachBall G a M
        · apply mul_le_mul' le_rfl
          rw [←ENNReal.ofReal_mul (zpow_nonneg p.2.1 _)]
          apply ENNReal.ofReal_le_ofReal
          exact inducedSusceptibility_ball_bound G hloc (W : Set V)ᶜ p hp0 a b M
            (by simpa only [Set.mem_compl_iff,Finset.mem_coe,not_not] using ha) hball
            (fun c => summable_restrictedTwoPoint G hloc hqt p hp _ c)
        · rw [hsupport a b hball,zero_mul,zero_mul]
      _ = _ := by rw [ENNReal.tsum_mul_right,hrow,one_mul]
  calc
    _ ≤ ∑ a ∈ W, ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) *
        ENNReal.ofReal (deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M) :=
      Finset.sum_le_sum hb
    _ = ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ENNReal.ofReal
        (∑ a ∈ W, deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M) := by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun a _ => deletedBoundaryPotential_nonneg G hloc _ p a M),Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ENNReal.ofReal
        (((d+1)^M : ℕ) * ∑ a ∈ W, ∑ b ∈ neighbors G hloc a,
          inducedSusceptibility G (W : Set V)ᶜ p b) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (deletedBoundaryPotential_sum_bound G hloc d hd M W p))
    _ = ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        ∑ a ∈ W, ENNReal.ofReal (∑ b ∈ neighbors G hloc a,
          inducedSusceptibility G (W : Set V)ᶜ p b) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg
          (fun b _ => inducedSusceptibility_nonneg G _ p b)),mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum (fun a _ =>
      neighborSusceptibility_le_edge_action G hloc _ p a))

theorem kernelExteriorPotential_eq_lintegral [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (K : V → V → ℝ≥0∞) (x : V) :
    kernelExteriorPotential G p K x =
      ∫⁻ ω, ∑' a, ∑' b, K a b *
        (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0) ∂law p := by
  have hm (a b : V) : Measurable (fun ω => K a b *
      (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0)) :=
    measurable_const.mul (Measurable.ite (measurableSet_conn G x a)
      (ENNReal.measurable_ofReal.comp (measurable_exteriorSusceptibility G hloc p x b))
      measurable_const)
  rw [lintegral_tsum (fun a => (Measurable.tsum (hm a)).aemeasurable)]
  apply tsum_congr
  intro a
  rw [lintegral_tsum (fun b => (hm a b).aemeasurable)]
  apply tsum_congr
  intro b
  exact (lintegral_const_mul _ (Measurable.ite (measurableSet_conn G x a)
    (ENNReal.measurable_ofReal.comp (measurable_exteriorSusceptibility G hloc p x b))
    measurable_const)).symm

theorem kernel_exterior_sample_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (d : ℕ) (hd : ∀ a, degree G a ≤ d) (M : ℕ) (K : V → V → ℝ≥0∞)
    (hrow : ∀ a, ∑' b, K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → K a b = 0)
    (x : V) (ω : Set E) (hf : (cluster G ω x).Finite) :
    (∑' a, ∑' b, K a b *
      (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0)) ≤
      ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        ∑' a, ∑' b, indexedEdgeKernel G a b *
          (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0) := by
  let W := hf.toFinset
  have hW : cluster G ω x = (W : Set V) := hf.coe_toFinset.symm
  have hc (a : V) : Conn G ω x a ↔ a ∈ W := by
    change a ∈ cluster G ω x ↔ a ∈ W
    rw [hW]
    rfl
  have he (J : V → V → ℝ≥0∞) :
      (∑' a, ∑' b, J a b *
        (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0)) =
        ∑ a ∈ W, ∑' b, J a b * ENNReal.ofReal (inducedSusceptibility G (W : Set V)ᶜ p b) := by
    rw [tsum_eq_sum (s := W) (fun a ha => by
      simp only [ite_eq_right (fun h => ha ((hc a).mp h)),mul_zero,tsum_zero])]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [ite_eq_left ((hc a).mpr ha),exteriorSusceptibility_eq G p x _ ω hf,hW]
  rw [he K,he (indexedEdgeKernel G)]
  exact finite_kernel_exterior_bound G hloc hqt p hp0 hp d hd M K hrow hsupport W

theorem kernelExteriorPotential_upper [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (d : ℕ) (hd : ∀ a, degree G a ≤ d) (M : ℕ) (K : V → V → ℝ≥0∞)
    (hrow : ∀ a, ∑' b, K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → K a b = 0) (x : V) :
    kernelExteriorPotential G p K x ≤
      ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        kernelExteriorPotential G p (indexedEdgeKernel G) x := by
  rw [kernelExteriorPotential_eq_lintegral G hloc p K x,
    kernelExteriorPotential_eq_lintegral G hloc p (indexedEdgeKernel G) x]
  have hm (a b : V) : Measurable (fun ω => indexedEdgeKernel G a b *
      (if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω) else 0)) :=
    measurable_const.mul (Measurable.ite (measurableSet_conn G x a)
      (ENNReal.measurable_ofReal.comp (measurable_exteriorSusceptibility G hloc p x b))
      measurable_const)
  rw [←lintegral_const_mul _ (Measurable.tsum (fun a => Measurable.tsum (hm a)))]
  apply lintegral_mono_ae
  filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hf
  exact kernel_exterior_sample_bound G hloc hqt p hp0 hp d hd M K hrow hsupport x ω hf

theorem kernelExteriorPotential_le_derivative [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (d : ℕ) (hd : ∀ a, degree G a ≤ d) (M : ℕ) (K : V → V → ℝ≥0∞)
    (hrow : ∀ a, ∑' b, K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → K a b = 0) (x : V) :
    kernelExteriorPotential G p K x ≤
      ENNReal.ofReal ((p : ℝ)^(-(M : ℤ))) * ((d+1)^M : ℕ) *
        (ENNReal.ofReal (1 - (p : ℝ)) * ENNReal.ofReal (deriv (realSusceptibility G x) p)) := by
  have hh := kernelExteriorPotential_upper G hloc hqt p hp0 hp d hd M K hrow hsupport x
  rwa [kernelExteriorPotential_edge_eq_derivative G hloc hqt p hp0 hp x] at hh

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ReciprocalDecay
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Percolation.BenjaminiSchramm

theorem reciprocal_upper_of_derivative_lower
    (f : ℝ → ℝ) (a b k : ℝ) (hk : 0 < k)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Ioo a b, k * (f x)^2 ≤ deriv f x)
    (x : ℝ) (hx : x ∈ Ioo a b) : f x ≤ 1 / (k * (b-x)) := by
  have hinv : k * (b-x) ≤ 1 / f x := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := min ((b-x)/2) (ε/(2*k))
    have hδ : 0 < δ := lt_min (div_pos (sub_pos.mpr hx.2) (by norm_num))
      (div_pos hε (by positivity))
    have hδx : δ ≤ (b-x)/2 := min_le_left _ _
    have hδε : δ ≤ ε/(2*k) := min_le_right _ _
    let y := b-δ
    have hxy : x < y := by dsimp [y]; linarith
    have hyb : y < b := by dsimp [y]; linarith
    have hsub : Icc x y ⊆ Ioo a b := fun z hz =>
      ⟨hx.1.trans_le hz.1,hz.2.trans_lt hyb⟩
    have hg (z : ℝ) (hz : z ∈ Icc x y) :
        HasDerivAt (fun t => -(1 / f t)) (deriv f z / (f z)^2) z := by
      have hh := ((hdiff z (hsub hz)).hasDerivAt.inv (hpos z (hsub hz)).ne').neg
      simpa only [one_div,Pi.inv_apply,Pi.neg_apply,neg_div,neg_neg] using! hh
    have hbound (z : ℝ) (hz : z ∈ interior (Icc x y)) :
        k ≤ deriv (fun t => -(1 / f t)) z := by
      rw [(hg z (interior_subset hz)).deriv]
      exact (le_div_iff₀ (sq_pos_of_pos (hpos z (hsub (interior_subset hz))))).mpr
        (hderiv z (hsub (interior_subset hz)))
    have hdist := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
      (fun z hz => (hg z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hg z (interior_subset hz)).differentiableAt.differentiableWithinAt)
      hbound x ⟨le_rfl,hxy.le⟩ y ⟨hxy.le,le_rfl⟩ hxy.le
    have hn : 0 ≤ 1 / f y := (div_pos zero_lt_one (hpos y (hsub ⟨hxy.le,le_rfl⟩))).le
    have he : 2*k*δ ≤ ε := by
      simpa only [mul_comm δ] using (le_div_iff₀ (by positivity : 0 < 2*k)).mp hδε
    dsimp only [y] at hdist
    nlinarith
  apply (le_div_iff₀ (mul_pos hk (sub_pos.mpr hx.2))).mpr
  have hh := (le_div_iff₀ (hpos x hx)).mp hinv
  nlinarith

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SmallWalkKernel
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped ENNReal Topology

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_small_walk_kernel (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (ε : ℝ) (hε : 0 < ε) :
    ∃ (d M : ℕ) (K : Hilbert V →L[ℂ] Hilbert V),
      (∀ a, degree G a ≤ d) ∧ PositiveRealMatrix K ∧ ‖K‖ < ε ∧
      (∀ a, ∑' b, ennMatrixCoeff K a b = 1) ∧
      (∀ a b, b ∉ reachBall G a M → ennMatrixCoeff K a b = 0) := by
  obtain ⟨d,P,hd,hdeg,hPn,_,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 ≤ (1 : ℝ)/(2*d) := by positivity
  have had : (1 : ℝ)/(2*d)*d ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*(d : ℝ))).mpr
    nlinarith
  have hpos : PositiveRealMatrix P := by
    intro a b
    change (P (lp.single 2 b (1 : ℂ)) a).im = 0 ∧
      0 ≤ (P (lp.single 2 b (1 : ℂ)) a).re
    rw [hP]
    exact ⟨Complex.ofReal_im _,walkKernel_nonneg G hloc d hdeg _ ha had a b⟩
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg P) hPn
  obtain ⟨M,hM,hMp⟩ := Filter.Eventually.exists
    ((ht.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 1))
  refine ⟨d,M,P^M,hdeg,hpos.pow M,
    (norm_pow_le' P (Nat.zero_lt_of_lt hMp)).trans_lt hM,?_,?_⟩
  · intro a
    change (∑' b, ENNReal.ofReal (matrixCoeff (P^M) a b).re) = 1
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun b => ((hpos.pow M) a b).2)
      (walkPower_hasSum G hloc _ P hpos hP M a).summable,
      (walkPower_hasSum G hloc _ P hpos hP M a).tsum_eq,ENNReal.ofReal_one]
  · intro a b hb
    change ENNReal.ofReal (matrixCoeff (P^M) a b).re = 0
    rw [walkPower_support G hloc _ P hpos hP M a b hb,ENNReal.ofReal_zero]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SusceptibilityDerivativeLower
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem susceptibility_derivative_nonneg [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (x : V) :
    0 ≤ deriv (realSusceptibility G x) p := by
  rw [(hasDerivAt_realSusceptibility G hloc hqt p hp0 hp x).deriv]
  exact tsum_nonneg (fun y => russoSlope_nonneg G x y p p.2.2)

theorem susceptibility_derivative_lower_of_kernel [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (T K : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T)
    (hK : PositiveRealMatrix K) (d M : ℕ) (hd : ∀ a, degree G a ≤ d)
    (hrow : ∀ a, ∑' b, ennMatrixCoeff K a b = 1)
    (hsupport : ∀ a b, b ∉ reachBall G a M → ennMatrixCoeff K a b = 0)
    (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) (x : V)
    (hmin : ∀ b, c * susceptibility G p x ≤ susceptibility G p b)
    (hmax : ∀ b, susceptibility G p b ≤ C * susceptibility G p x)
    (hsmall : C * (‖T‖^3 * ‖K‖) ≤ c/2) :
    (c/2) * (susceptibility G p x)^2 ≤
      (p : ℝ)^(-(M : ℤ)) * ((d+1)^M : ℕ) * (1 - (p : ℝ)) *
        deriv (realSusceptibility G x) p := by
  have hχ := susceptibility_nonneg G p x
  have hder := susceptibility_derivative_nonneg G hloc hqt p hp0 hp x
  have hl := kernelExteriorPotential_lower_of_critical G hloc hqt p hp T K hT hK hrow
    (ENNReal.ofReal (c * susceptibility G p x)) (ENNReal.ofReal (C * susceptibility G p x))
    (fun b => ENNReal.ofReal_le_ofReal (hmin b))
    (fun b => ENNReal.ofReal_le_ofReal (hmax b)) x
  have hu := kernelExteriorPotential_le_derivative G hloc hqt p hp0 hp d hd M
    (ennMatrixCoeff K) hrow hsupport x
  have hh := hl.trans (add_le_add hu le_rfl)
  have hr := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal
    (mul_nonneg hc hχ),ENNReal.toReal_ofReal (mul_nonneg hC hχ),
    ENNReal.toReal_ofReal hχ,ENNReal.toReal_ofReal (zpow_nonneg p.2.1 _),
    ENNReal.toReal_natCast,ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2),
    ENNReal.toReal_ofReal hder,ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg (norm_nonneg T) _) (norm_nonneg K))] at hr
  have he := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (susceptibility G p x))
  nlinarith

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SusceptibilityComparison
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_susceptibility_comparison [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (p : unitInterval), p₀ ≤ (p : ℝ) → p < pc G →
      ∀ x b, c * susceptibility G p x ≤ susceptibility G p b ∧
        susceptibility G p b ≤ C * susceptibility G p x := by
  obtain ⟨O,hO⟩ := hqt
  have hqt : QuasiTransitive G := ⟨O,hO⟩
  let ι := {o : V // o ∈ O}
  let : Fintype ι := inferInstance
  obtain ⟨o,ho,_⟩ := hO (Classical.arbitrary V)
  let : Nonempty ι := ⟨⟨o,ho⟩⟩
  let root : ι → V := Subtype.val
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos (α := ι)
  let weight : ι → ℝ := fun _ => N⁻¹
  have hw (i : ι) : 0 ≤ weight i := inv_nonneg.mpr hN.le
  have hw1 : ∑ i, weight i = 1 := by
    simp only [weight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  have hcover (x : V) : ∃ i, x ∈ vertexOrbit G (root i) := by
    obtain ⟨y,hy,a,b,hab,hax⟩ := hO x
    exact ⟨⟨y,hy⟩,a,b,hab,hax⟩
  obtain ⟨a,ha,hlo⟩ := exists_rootSusceptibility_lower G hconn hloc hqt root weight
    hw hw1 hcover p₀ hp₀
  have hupper (p : unitInterval) (x : V) :
      susceptibility G p x ≤ N * rootSusceptibility G root weight p :=
    susceptibility_le_rootSusceptibility G root weight hw hcover N hN.le
      (fun _ => by dsimp [weight]; rw [mul_inv_cancel₀ hN.ne']) p x
  let c := a/N
  have hc : 0 < c := div_pos ha hN
  have hcomp (p : unitInterval) (hp : p₀ ≤ (p : ℝ)) (hpp : p < pc G) (x b : V) :
      c * susceptibility G p x ≤ susceptibility G p b := by
    calc
      _ ≤ c * (N * rootSusceptibility G root weight p) :=
        mul_le_mul_of_nonneg_left (hupper p x) hc.le
      _ = a * rootSusceptibility G root weight p := by
        dsimp only [c]
        rw [←mul_assoc,div_mul_cancel₀ a hN.ne']
      _ ≤ _ := hlo p hp hpp b
  refine ⟨c,c⁻¹,hc,inv_pos.mpr hc,fun p hp hpp x b => ⟨hcomp p hp hpp x b,?_⟩⟩
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hcomp p hp hpp b x)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OperatorSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_uniform_susceptibility_derivative_lower
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T)
    (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ k : ℝ, 0 < k ∧ ∀ (p : unitInterval), p₀ ≤ (p : ℝ) → p < pc G → ∀ x,
      k * (susceptibility G p x)^2 ≤ deriv (realSusceptibility G x) p := by
  obtain ⟨c,C,hc,hC,hcomp⟩ := exists_susceptibility_comparison G hconn hloc hqt p₀ hp₀
  let ε := c / (2 * (C * ‖T‖^3 + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨d,M,K,hdeg,hK,hKn,hrow,hsupport⟩ := exists_small_walk_kernel G hloc hqt hh ε hε
  have hsmall : C * (‖T‖^3 * ‖K‖) ≤ c/2 := by
    have hd : 0 < 2 * (C * ‖T‖^3 + 1) := by positivity
    have hmul := (lt_div_iff₀ hd).mp hKn
    nlinarith [norm_nonneg K]
  let A : ℝ := p₀^(-(M : ℤ)) * ((d+1)^M : ℕ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(c/2)/A,div_pos (half_pos hc) hA,fun p hpp hp x => ?_⟩
  have hp0 : 0 < (p : ℝ) := hp₀.trans_le hpp
  have hlo := susceptibility_derivative_lower_of_kernel G hloc hqt p hp0 hp T K hT hK d M
    hdeg hrow hsupport c C hc.le hC.le x
    (fun b => (hcomp p hpp hp x b).1) (fun b => (hcomp p hpp hp x b).2) hsmall
  have hz : (p : ℝ)^(-(M : ℤ)) ≤ p₀^(-(M : ℤ)) := by
    simp only [zpow_neg,zpow_natCast]
    exact inv_anti₀ (pow_pos hp₀ M) (pow_le_pow_left₀ hp₀.le hpp M)
  have hcoef : (p : ℝ)^(-(M : ℤ)) * ((d+1)^M : ℕ) * (1-(p : ℝ)) ≤ A := by
    calc
      _ ≤ (p : ℝ)^(-(M : ℤ)) * ((d+1)^M : ℕ) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [p.2.1]) (by positivity)
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg ((d+1)^M))
  have hbound := hlo.trans (mul_le_mul_of_nonneg_right hcoef
    (susceptibility_derivative_nonneg G hloc hqt p hp0 hp x))
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hA).mpr
  simpa only [mul_comm A] using hbound

theorem susceptibility_upper_of_critical_operator_bs_oai
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : unitInterval), p < pc G → ∀ x,
      susceptibility G p x ≤ A / ((pc G : ℝ) - p) := by
  have hpc0 : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  let a : ℝ := (pc G : ℝ)/4
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨k,hk,hderiv⟩ := exists_uniform_susceptibility_derivative_lower G hconn hloc hqt hh T hT a ha
  have hnear (p : unitInterval) (hap : a < (p : ℝ)) (hp : p < pc G) (x : V) :
      susceptibility G p x ≤ 1 / (k * ((pc G : ℝ) - p)) := by
    rw [←realSusceptibility_coe G x p]
    apply reciprocal_upper_of_derivative_lower (realSusceptibility G x) a (pc G) k hk
      (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) p ⟨hap,hp⟩
    · let q : unitInterval := ⟨t,⟨ha.le.trans ht.1.le,ht.2.le.trans (pc G).2.2⟩⟩
      change 0 < realSusceptibility G x q
      rw [realSusceptibility_coe G x q]
      exact lt_of_lt_of_le zero_lt_one (susceptibility_one_le G hloc hqt q ht.2 x)
    · let q : unitInterval := ⟨t,⟨ha.le.trans ht.1.le,ht.2.le.trans (pc G).2.2⟩⟩
      exact (hasDerivAt_realSusceptibility G hloc hqt q (ha.trans ht.1) ht.2 x).differentiableAt
    · let q : unitInterval := ⟨t,⟨ha.le.trans ht.1.le,ht.2.le.trans (pc G).2.2⟩⟩
      change k * (realSusceptibility G x q)^2 ≤ deriv (realSusceptibility G x) q
      rw [realSusceptibility_coe G x q]
      exact hderiv q ht.1.le ht.2 x
  refine ⟨2/k,div_pos (by norm_num) hk,fun p hp x => ?_⟩
  have hgap : 0 < (pc G : ℝ) - p := sub_pos.mpr hp
  by_cases hap : a < (p : ℝ)
  · apply (hnear p hap hp x).trans
    have he : 1 / (k * ((pc G : ℝ)-p)) = (1/k) / ((pc G : ℝ)-p) := by
      simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hk.le) hgap.le
  · let q : unitInterval := ⟨(pc G : ℝ)/2,⟨by positivity,by linarith [(pc G).2.2]⟩⟩
    have hq : q < pc G := by change (pc G : ℝ)/2 < pc G; linarith
    have haq : a < (q : ℝ) := by dsimp [a,q]; linarith
    have hpq : p ≤ q := by change (p : ℝ) ≤ (pc G : ℝ)/2; dsimp [a] at hap; linarith
    have hm : susceptibility G p x ≤ susceptibility G q x :=
      (summable_twoPoint_subcritical G hloc hqt p hp x).tsum_le_tsum
        (fun y => twoPoint_mono G x y hpq)
        (summable_twoPoint_subcritical G hloc hqt q hq x)
    apply (hm.trans (hnear q haq hq x)).trans
    have he : 1 / (k * ((pc G : ℝ)-q)) = (2/k)/(pc G : ℝ) := by
      dsimp only [q]
      field_simp
      ring
    rw [he]
    exact div_le_div_of_nonneg_left (div_nonneg (by norm_num) hk.le) hgap (by linarith [p.2.1])

end Percolation.BenjaminiSchramm

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Percolation.BenjaminiSchramm.susceptibility_upper_of_critical_operator_bs_oai.{u, v} := @OAI.Percolation.BenjaminiSchramm.susceptibility_upper_of_critical_operator_bs_oai.{u, v}
