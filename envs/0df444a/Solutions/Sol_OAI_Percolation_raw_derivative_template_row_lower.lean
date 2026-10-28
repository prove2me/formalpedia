-- Prove2me | solution 1 for OAI.Percolation.raw_derivative_template_row_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:09:31.125722+00:00
-- url     : https://prove2.me/submissions/e9a1b224-9e01-49e3-aaf7-bcc913e9d604

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002

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

section Probability
variable (G : BondGraph V E)

theorem twoPoint_le_one (p : unitInterval) (x y : V) : twoPoint G p x y ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using
    (prob_le_one (μ := law p) (s := {ω | Conn G ω x y})))

theorem twoPoint_symm (p : unitInterval) (x y : V) : twoPoint G p x y = twoPoint G p y x := by
  have he : {ω | Conn G ω x y} = {ω | Conn G ω y x} := by
    ext ω
    exact ⟨conn_symm G ω, conn_symm G ω⟩
  simp only [twoPoint, he]

end Probability

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


end Coupling

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

end GoodnessLaw

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Spectral
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

end IsoperimetricEnergy

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


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Amplification
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

end RestrictedPathPotential
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

theorem susceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ susceptibility G p x := by
  have hd : twoPoint G p x x = 1 := by
    have he : {ω : Set E | Conn G ω x x} = Set.univ := Set.eq_univ_of_forall (fun _ => conn_refl G _ x)
    simp only [twoPoint,he,measure_univ,ENNReal.toReal_one]
  rw [←hd]
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).le_tsum x (fun _ _ => twoPoint_nonneg G p _ _)


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
section FiniteLocalIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

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



end ExteriorConnectionIndependence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExposedClusterGeometry
attribute [local instance] Classical.propDecidable Classical.decEq



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
      · simp only [hωA,ite_true,f,true_and]
        exact cluster_size_eq_tsum_real G ω y hω
      · simp only [hωA,ite_false,f,false_and,tsum_zero]
    _ = ∑' z, ∫ ω, f z ω ∂law p := (integral_tsum_of_summable_integral_norm hi hint).symm
    _ = _ := tsum_congr he

end ExposedClusterGeometry
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



end ClusterPartition
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
section OrientedPivotalConnections
attribute [local instance] Classical.propDecidable Classical.decEq



theorem measurableSet_orientedPivotalEvent [Countable V] [Countable E]
    (G : BondGraph V E) (x y a b : V) : MeasurableSet (orientedPivotalEvent G x y a b) :=
  (measurableSet_conn G x a).inter ((measurableSet_conn G b y).inter (measurableSet_conn G a b).compl)


theorem orientedPivotalEvent_subset_disjoint (G : BondGraph V E) (x y a b : V) :
    orientedPivotalEvent G x y a b ⊆
      DisjointOccurrence {ω | Conn G ω x a} {ω | Conn G ω b y} := by
  intro ω hω
  have hx : x ∈ cluster G ω a := conn_symm G ω hω.1
  have hb : b ∉ cluster G ω a := hω.2.2
  obtain ⟨Q,hQ,hQa⟩ := finiteWitness_conn G x a _ (conn_restrict_cluster G ω a hx hω.1)
  obtain ⟨R,hR,hRb⟩ := finiteWitness_conn G b y _ (conn_restrict_cluster_compl G ω a hb hω.2.1)
  refine ⟨Q,R,fun e he => (hQ he).1,fun e he => (hR he).1,?_,hQa,hRb⟩
  apply Finset.disjoint_left.mpr
  intro e heQ heR
  obtain ⟨⟨z,w⟩,he⟩ := Quot.exists_rep (G e)
  have hz : z ∈ G e := by rw [←he]; exact Sym2.mem_mk_left z w
  exact (hR heR).2 z hz ((hQ heQ).2 z hz)

end OrientedPivotalConnections
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_ContactTrace
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
section NonnegativeOperatorDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

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
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_RussoRows
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
open MeasureTheory Filter
open scoped ENNReal
section RussoRows
attribute [local instance] Classical.propDecidable Classical.decEq



theorem summable_kernel_pair (A B : V → V → ℝ)
    (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ x y, 0 ≤ B x y)
    (hsA : ∀ x, Summable (A x)) (hsB : ∀ x, Summable (B x))
    (C : ℝ) (hC : ∀ x, ∑' y, B x y ≤ C) (x : V) :
    Summable (fun ab : V×V => A x ab.1 * B ab.1 ab.2) := by
  apply (summable_prod_of_nonneg (f := fun ab : V×V => A x ab.1 * B ab.1 ab.2)
    (fun ab => mul_nonneg (hA x ab.1) (hB ab.1 ab.2))).mpr
  refine ⟨fun a => (hsB a).mul_left (A x a),?_⟩
  simp only [tsum_mul_left]
  exact Summable.of_nonneg_of_le (fun a => mul_nonneg (hA x a) (tsum_nonneg (hB a)))
    (fun a => mul_le_mul_of_nonneg_left (hC a) (hA x a)) ((hsA x).mul_right C)

theorem summable_twoPoint_pair [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab : V×V => twoPoint G p x ab.1 * twoPoint G p ab.1 ab.2) := by
  obtain ⟨C,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  have hs := summable_twoPoint_subcritical G hloc hqt p hp
  exact summable_kernel_pair (twoPoint G p) (twoPoint G p) (twoPoint_nonneg G p)
    (twoPoint_nonneg G p) hs hs C (fun x => (hs x).tsum_le_of_sum_le (hrow x)) x

end RussoRows
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section PositiveTriangleSeries
attribute [local instance] Classical.propDecidable Classical.decEq


theorem HasKernel.matrixCoeff_re (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    (matrixCoeff T x y).re = twoPoint G p x y := by
  change (T (lp.single 2 y (1:ℂ)) x).re = _
  rw [hT x y,Complex.ofReal_re]

end PositiveTriangleSeries
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormRatio
attribute [local instance] Classical.propDecidable Classical.decEq



theorem susceptibility_bddAbove [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : BddAbove (Set.range (susceptibility G p)) := by
  obtain ⟨C,_,hC⟩ := subcritical_row_bound G hloc hqt p hp
  refine ⟨C,?_⟩
  rintro _ ⟨x,rfl⟩
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).tsum_le_of_sum_le (hC x)

theorem susceptibility_le_max [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    susceptibility G p x ≤ maxSusceptibility G p :=
  le_csSup (susceptibility_bddAbove G hloc hqt p hp) (Set.mem_range_self x)

theorem maxSusceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ maxSusceptibility G p := by
  let x : V := Classical.choice inferInstance
  exact (susceptibility_one_le G hloc hqt p hp x).trans (susceptibility_le_max G hloc hqt p hp x)

end NormRatio
end Percolation


namespace Percolation
universe u
section ChronologicalErasure
open List
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq



namespace HoldingWalk
variable {H : SimpleGraph V} {k : ℕ} {x y : V}

theorem mass_nonneg (P : V → V → ℝ) (hP : ∀ a b, 0 ≤ P a b) (w : HoldingWalk H k x y) :
    0 ≤ w.mass P := by
  induction w with
  | nil => exact zero_le_one
  | hold w ih => exact mul_nonneg (hP _ _) ih
  | step h w ih => exact mul_nonneg (hP _ _) ih

theorem withoutHolds_length (w : HoldingWalk H k x y) : w.withoutHolds.length ≤ k := by
  induction w with
  | nil => simp [withoutHolds]
  | hold w ih => exact ih.trans (Nat.le_succ _)
  | step h w ih => simpa only [withoutHolds,SimpleGraph.Walk.length_cons] using Nat.succ_le_succ ih

theorem erase_isPath (w : HoldingWalk H k x y) : w.erase.IsPath :=
  w.withoutHolds.reverse.bypass_isPath.reverse

theorem erase_length (w : HoldingWalk H k x y) : w.erase.length ≤ k := by
  have hh := w.withoutHolds.reverse.length_bypass_le_length
  simpa only [erase,SimpleGraph.Walk.length_reverse] using hh.trans (by simpa using w.withoutHolds_length)

end HoldingWalk
end ChronologicalErasure
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorMonotonicity
attribute [local instance] Classical.propDecidable Classical.decEq



lemma pivotal_restrict_of_conn (G : BondGraph V E) {S T : Set E} (hST : S ⊆ T)
    {x y : V} (hc : Conn G S x y) (e : E) (hp : ¬Conn G (T \ {e}) x y) :
    e ∈ S ∧ ¬Conn G (S \ {e}) x y := by
  constructor
  · by_contra he
    apply hp
    apply conn_mono G ?_ hc
    intro d hd
    exact ⟨hST hd,fun hde => he ((Set.mem_singleton_iff.mp hde) ▸ hd)⟩
  · intro h
    exact hp (conn_mono G (Set.sdiff_subset_sdiff_left hST) h)

 

theorem corridorCounted_restrict (G : BondGraph V E) (retained blockers : Set E)
    {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω') (x y : V)
    (hc : Conn G (ω ∩ internalEdges G D) x y)
    (ht : corridorCounted G retained blockers D' ω' x y) :
    corridorCounted G retained blockers D ω x y := by
  have hs : ω ∩ internalEdges G D ⊆ ω' ∩ internalEdges G D' :=
    Set.inter_subset_inter hω (internalEdges_mono G hD)
  refine ⟨hc,fun e he => pivotal_restrict_of_conn G hs hc e (ht.2.1 e he).2,?_⟩
  exact ht.2.2.mono_right hs

lemma corridorCounted_symm (G : BondGraph V E) (retained blockers : Set E)
    (D : Set V) (ω : Set E) (x y : V) :
    corridorCounted G retained blockers D ω x y ↔ corridorCounted G retained blockers D ω y x := by
  constructor <;> rintro ⟨hc,hp,hb⟩
  · exact ⟨conn_symm G _ hc,fun e he => ⟨(hp e he).1,fun hc => (hp e he).2 (conn_symm G _ hc)⟩,hb⟩
  · exact ⟨conn_symm G _ hc,fun e he => ⟨(hp e he).1,fun hc => (hp e he).2 (conn_symm G _ hc)⟩,hb⟩

 

theorem measurableSet_corridorCounted [Countable E] (G : BondGraph V E)
    (retained blockers : Set E) (D : Set V) (x y : V) :
    MeasurableSet {ω | corridorCounted G retained blockers D ω x y} := by
  have hmem (e : E) : MeasurableSet {ω : Set E | e ∈ ω ∩ internalEdges G D} := by
    by_cases he : e ∈ internalEdges G D
    · simpa only [Set.mem_inter_iff,he,and_true] using measurableSet_mem e
    · simp only [Set.mem_inter_iff,he,and_false,Set.ofPred_false]; exact MeasurableSet.empty
  have hp (e : E) : MeasurableSet {ω : Set E | e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y} := by
    apply (hmem e).inter
    have heq (ω : Set E) : (ω ∩ internalEdges G D) \ {e} = ω ∩ (internalEdges G D \ {e}) := by
      ext d; simp only [Set.mem_inter_iff,Set.mem_sdiff]; tauto
    simp_rw [heq]
    exact (measurableSet_restrictedConn G _ x y).compl
  have hb : MeasurableSet {ω : Set E | Disjoint blockers (ω ∩ internalEdges G D)} := by
    simp only [Set.disjoint_left,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun (_ : e ∈ blockers) => (hmem e).compl))
  have hkeep : MeasurableSet {ω : Set E | ∀ e ∈ retained, e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun (_ : e ∈ retained) => hp e))
  exact (measurableSet_restrictedConn G _ x y).inter (hkeep.inter hb)

end CorridorMonotonicity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralCorridors
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem path_isPath (w : RawCorridor G k) : w.path.IsPath := w.2.2.erase_isPath

theorem path_length (w : RawCorridor G k) : w.path.length ≤ k := w.2.2.erase_length

theorem retained_disjoint_blockers (w : RawCorridor G k) : Disjoint w.retained w.blockers := by
  exact Set.disjoint_left.mpr (fun e he hb => hb.2 he)

theorem weight_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (w : RawCorridor G k) : 0 ≤ w.weight P p := by
  exact mul_nonneg (mul_nonneg (w.2.2.mass_nonneg P hP) (inv_nonneg.mpr (pow_nonneg p.2.1 _)))
    (inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr p.2.2) _))

end RawCorridor
end LiteralCorridors
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Corridors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorEligibility
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem edge_has_label (w : RawCorridor G k) (s : Sym2 V) (hs : s ∈ w.path.edges) :
    ∃ e ∈ w.retained, G e = s := by
  induction s using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨_,e,_,he⟩ := w.path.adj_of_mem_edges hs
    exact ⟨e,by simpa only [retained,Set.mem_ofPred_eq,he] using hs,he⟩

theorem image_retained (w : RawCorridor G k) : G '' w.retained = {s | s ∈ w.path.edges} := by
  ext s
  constructor
  · rintro ⟨e,he,rfl⟩; exact he
  · exact w.edge_has_label s

theorem retained_ncard (hG : Function.Injective G) (w : RawCorridor G k) :
    w.retained.ncard = w.path.length := by
  rw [←hG.injOn.ncard_image (s := w.retained),w.image_retained]
  have hh := List.toFinset_card_of_nodup w.path_isPath.isTrail.edges_nodup
  simpa only [←List.coe_toFinset,Set.ncard_coe_finset,SimpleGraph.Walk.length_edges] using hh

 

theorem support_subset_of_retained (w : RawCorridor G k) (hlen : 0 < w.path.length)
    (D : Set V) (he : w.retained ⊆ internalEdges G D) :
    ∀ z ∈ w.path.support, z ∈ D := by
  intro z hz
  obtain ⟨s,hs,hzs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hlen)).mp hz
  obtain ⟨e,he',hGe⟩ := w.edge_has_label s hs
  exact he he' z (hGe.symm ▸ hzs)

theorem retained_incident_interior (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (e : E) (he : e ∈ w.retained) : ∃ z ∈ w.interior, z ∈ G e := by
  change G e ∈ w.path.edges at he
  generalize hab : G e = s at he
  induction s using Sym2.inductionOn with
  | _ a b =>
    have hedge : s(a,b) ∈ w.path.edges := he
    have ha := w.path.fst_mem_support_of_mem_edges hedge
    have hb := w.path.snd_mem_support_of_mem_edges hedge
    have habne : a ≠ b := (w.path.adj_of_mem_edges hedge).1
    by_contra hn
    have hna : a ∉ w.interior := fun hi => hn ⟨a,hi,by simp⟩
    have hnb : b ∉ w.interior := fun hi => hn ⟨b,hi,by simp⟩
    have hax : a = w.base ∨ a = w.endpoint := by simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,ha,true_and,Finset.mem_insert,Finset.mem_singleton,not_not] using hna
    have hbx : b = w.base ∨ b = w.endpoint := by simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,hb,true_and,Finset.mem_insert,Finset.mem_singleton,not_not] using hnb
    have hedge' : s(w.base,w.endpoint) ∈ w.path.edges := by
      rcases hax with rfl | rfl <;> rcases hbx with rfl | rfl
      · exact (habne rfl).elim
      · exact hedge
      · simpa only [Sym2.eq_swap] using hedge
      · exact (habne rfl).elim
    have hh := w.path_isPath.length_eq_one_of_mem_edges hedge'
    omega

theorem specified_disjoint_exterior (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) :
    Disjoint (w.retained ∪ w.blockers) (internalEdges G (w.interior : Set V)ᶜ) := by
  apply Set.disjoint_left.mpr
  intro e he hx
  obtain ⟨z,hz,he⟩ := he.elim (w.retained_incident_interior hlen e) (fun hb => hb.1)
  exact hx z he hz

end RawCorridor
end CorridorEligibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactCorridorPattern
attribute [local instance] Classical.propDecidable Classical.decEq

theorem edgePattern_eq_restriction (A B : Finset E) (hAB : Disjoint A B) :
    edgePattern A B = {ω | ω ∩ ((A ∪ B : Finset E) : Set E) = (A : Set E)} := by
  ext ω
  constructor
  · rintro ⟨ha,hb⟩
    apply Set.Subset.antisymm
    · rintro e ⟨he,heQ⟩
      rcases Finset.mem_union.mp heQ with h | h
      · exact h
      · exact (Set.disjoint_left.mp hb h he).elim
    · intro e he
      exact ⟨ha he,Finset.mem_union_left _ he⟩
  · intro h
    constructor
    · intro e he
      exact ((Set.ext_iff.mp h e).mpr he).1
    · apply Set.disjoint_left.mpr
      intro e he hw
      have ha : e ∈ A := (Set.ext_iff.mp h e).mp ⟨hw,Finset.mem_union_right _ he⟩
      exact Finset.disjoint_left.mp hAB ha he

theorem measurableSet_edgePattern (A B : Finset E) (hAB : Disjoint A B) :
    MeasurableSet (edgePattern A B) := by
  rw [edgePattern_eq_restriction A B hAB]
  exact measurableSet_finite_restriction (A∪B) {(A:Set E)}

 
theorem edgePattern_probability (A B : Finset E) (hAB : Disjoint A B) (p : unitInterval) :
    (law p).real (edgePattern A B) = (p:ℝ)^A.card*(1-(p:ℝ))^B.card := by
  let f : Set E → ℝ := fun ω => if ω ∈ edgePattern A B then 1 else 0
  have hf (ω : Set E) : f ω = f (ω ∩ ((A∪B:Finset E):Set E)) := by
    simp only [f,edgePattern_eq_restriction A B hAB,Set.mem_ofPred_eq,Set.inter_assoc,Set.inter_self]
  rw [←integral_event_indicator p _ (measurableSet_edgePattern A B hAB)]
  change (∫ ω, f ω ∂law p) = _
  rw [integral_eq_bernoulliPolynomial (A∪B) p f hf]
  trans bernoulliPolynomial (A∪B) (fun η => if η=A then 1 else 0) p
  · apply bernoulliPolynomial_congr
    intro η hη
    have he : (η:Set E) ∩ ((A∪B:Finset E):Set E) = (η:Set E) :=
      Set.inter_eq_left.mpr hη
    simp only [f,edgePattern_eq_restriction A B hAB,Set.mem_ofPred_eq,he,Finset.coe_inj]
  · simp only [bernoulliPolynomial,ite_mul,zero_mul,one_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_powerset,Finset.subset_union_left,ite_true,Finset.card_union_of_disjoint hAB,
      Nat.add_sub_cancel_left]

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem calibrationEvent_eq (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) : w.calibrationEvent =
      edgePattern (w.retained_finite hG).toFinset (w.blockers_finite hloc).toFinset := by
  simp only [calibrationEvent,edgePattern,Set.Finite.coe_toFinset]

theorem calibration_probability (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (p : unitInterval) :
    (law p).real w.calibrationEvent = (p:ℝ)^w.path.length*(1-(p:ℝ))^w.blockers.ncard := by
  rw [w.calibrationEvent_eq hG hloc,edgePattern_probability]
  · rw [←Set.ncard_eq_toFinset_card w.retained (w.retained_finite hG),←Set.ncard_eq_toFinset_card w.blockers (w.blockers_finite hloc),w.retained_ncard hG]
  · apply Finset.disjoint_left.mpr
    intro e he hb
    exact Set.disjoint_left.mp w.retained_disjoint_blockers
      ((w.retained_finite hG).mem_toFinset.mp he) ((w.blockers_finite hloc).mem_toFinset.mp hb)

 

theorem calibration_identity (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (P : V → V → ℝ) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) :
    w.weight P p * (law p).real w.calibrationEvent = w.probability P := by
  rw [w.calibration_probability hG hloc p]
  unfold weight
  have h₁ := pow_ne_zero w.path.length hp.ne'
  have h₂ := pow_ne_zero w.blockers.ncard (sub_pos.mpr hp₁).ne'
  field_simp

end RawCorridor
end ExactCorridorPattern
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorTerminalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem path_internal_two_neighbors {H : SimpleGraph V} {u v z : V}
    (q : H.Walk u v) (hq : q.IsPath) (hz : z ∈ q.support) (hzu : z ≠ u) (hzv : z ≠ v) :
    ∃ a b : V, a ≠ b ∧ s(z,a) ∈ q.edges ∧ s(z,b) ∈ q.edges := by
  induction q with
  | nil => simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz; exact (hzu hz).elim
  | @cons u a v h q ih =>
    have htail : q.IsPath := hq.of_cons
    have huz : u ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hq).2
    have hzq : z ∈ q.support := (List.mem_cons.mp hz).resolve_left hzu
    by_cases hza : z = a
    · subst z
      cases q with
      | nil => exact (hzv rfl).elim
      | @cons a b v h' q =>
        refine ⟨u,b,?_,?_,?_⟩
        · intro hub
          apply huz
          subst b
          simp
        · simp only [SimpleGraph.Walk.edges_cons,List.mem_cons,Sym2.eq_swap]; exact Or.inl trivial
        · simp only [SimpleGraph.Walk.edges_cons,List.mem_cons]; exact Or.inr (Or.inl trivial)
    · obtain ⟨b,c,hbc,hb,hc⟩ := ih htail hzq hza hzv
      exact ⟨b,c,hbc,List.mem_cons_of_mem _ hb,List.mem_cons_of_mem _ hc⟩

 

theorem pivotal_image_mem_edges (G : BondGraph V E) (ω : Set E) {x y : V}
    (q : (openSimpleGraph G ω).Walk x y) (e : E)
    (hp : ¬Conn G (ω \ {e}) x y) : G e ∈ q.edges := by
  obtain ⟨l,hl,hmap,ho⟩ := walk_lift_bonds G ω q
  by_contra he
  apply hp
  apply hl.conn
  intro f hf
  refine ⟨ho f hf,?_⟩
  intro hfe
  have hfe' : f = e := Set.mem_singleton_iff.mp hfe
  subst f
  apply he
  rw [←hmap]
  exact List.mem_map_of_mem hf

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem counted_terminal_outside (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : corridorCounted G w.retained w.blockers D ω x y) : x ∉ w.interior ∧ y ∉ w.interior := by
  have hleft (x y : V) (hc : corridorCounted G w.retained w.blockers D ω x y) : x ∉ w.interior := by
    intro hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxs : x ∈ w.path.support := List.mem_toFinset.mp hx'.1
    have hxne : x ≠ w.base ∧ x ≠ w.endpoint := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hx'.2
    have hxu := hxne.1
    have hxv := hxne.2
    obtain ⟨a,b,hab,ha,hb⟩ := path_internal_two_neighbors w.path w.path_isPath hxs hxu hxv
    obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.1
    let qp := q.bypass
    have hqp : qp.IsPath := q.bypass_isPath
    obtain ⟨e,he,hGe⟩ := w.edge_has_label _ ha
    obtain ⟨f,hf,hGf⟩ := w.edge_has_label _ hb
    have hea := pivotal_image_mem_edges G _ qp e (hc.2.1 e he).2
    have heb := pivotal_image_mem_edges G _ qp f (hc.2.1 f hf).2
    rw [hGe] at hea
    rw [hGf] at heb
    exact hab ((hqp.eq_snd_of_mem_edges hea).trans (hqp.eq_snd_of_mem_edges heb).symm)
  exact ⟨hleft x y hc,hleft y x ((corridorCounted_symm G _ _ D ω x y).mp hc)⟩

end RawCorridor
end CorridorTerminalGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section CorridorIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_inter_const (S : Set E) : Measurable (fun ω : Set E => ω ∩ S) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).and measurable_const

 
theorem restriction_events_independent (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (law p) ((fun ω => ω ∩ S) ⁻¹' A ∩ (fun ω => ω ∩ T) ⁻¹' B) =
      (law p) ((fun ω => ω ∩ S) ⁻¹' A) * (law p) ((fun ω => ω ∩ T) ⁻¹' B) := by
  let μ : Measure (E → Prop) := Measure.infinitePi (fun _ => bitLaw p)
  let σ : E → MeasurableSpace (E → Prop) := fun e =>
    MeasurableSpace.comap (fun f : E → Prop => f e) inferInstance
  have hi : iIndep σ μ := iIndepFun_infinitePi (X := fun (_ : E) (b : Prop) => b)
    (fun _ => measurable_id)
  have hle (e : E) : σ e ≤ (inferInstance : MeasurableSpace (E → Prop)) :=
    (measurable_pi_apply e).comap_le
  have hr (S : Set E) : @Measurable (E → Prop) (Set E) (⨆ e ∈ S, σ e) inferInstance
      (fun f => {e | f e} ∩ S) := by
    let : MeasurableSpace (E → Prop) := ⨆ e ∈ S, σ e
    apply measurable_setOfPred.comp
    apply Measurable.of_eval
    intro e
    change @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun f => f e ∧ e ∈ S)
    by_cases he : e ∈ S
    · have hm : @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun f => f e) :=
        Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
      simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,he,and_true] using hm
    · simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,he,and_false] using
        (measurable_const : @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun _ => False))
  have hm : (law p : Measure (Set E)) = μ.map (fun f => {e | f e}) := by
    simp only [law,setBernoulli_eq_map,Set.mem_univ,μ,bitLaw,bernoulliMeasure_def]
  rw [hm,Measure.map_apply measurable_setOfPred ((hA.preimage (measurable_inter_const S)).inter
    (hB.preimage (measurable_inter_const T))),
    Measure.map_apply measurable_setOfPred (hA.preimage (measurable_inter_const S)),
    Measure.map_apply measurable_setOfPred (hB.preimage (measurable_inter_const T))]
  exact (Indep_iff _ _ _).mp (indep_iSup_of_disjoint hle hi hST) _ _
    (hA.preimage (hr S)) (hB.preimage (hr T))

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem calibration_restriction (w : RawCorridor G k) (ω : Set E) :
    ω ∈ w.calibrationEvent ↔ ω ∩ (w.retained ∪ w.blockers) ∈ w.calibrationEvent := by
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨fun e he => ⟨ha he,Or.inl he⟩,hb.mono_right Set.inter_subset_left⟩
  · rintro ⟨ha,hb⟩
    refine ⟨fun e he => (ha he).1,Set.disjoint_left.mpr ?_⟩
    intro e he hw
    exact Set.disjoint_left.mp hb he ⟨hw,Or.inr he⟩

 

theorem calibration_independent (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) (p : unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (law p) (w.calibrationEvent ∩ (fun ω => ω ∩ internalEdges G (w.interior : Set V)ᶜ) ⁻¹' A) =
      (law p) w.calibrationEvent *
        (law p) ((fun ω => ω ∩ internalEdges G (w.interior : Set V)ᶜ) ⁻¹' A) := by
  have hQ : MeasurableSet w.calibrationEvent := by
    rw [w.calibrationEvent_eq hG hloc]
    apply measurableSet_edgePattern
    apply Finset.disjoint_left.mpr
    intro e he hb
    exact Set.disjoint_left.mp w.retained_disjoint_blockers
      ((w.retained_finite hG).mem_toFinset.mp he) ((w.blockers_finite hloc).mem_toFinset.mp hb)
  have heq : (fun ω => ω ∩ (w.retained ∪ w.blockers)) ⁻¹' w.calibrationEvent = w.calibrationEvent := by
    ext ω; exact (w.calibration_restriction ω).symm
  have hh := restriction_events_independent p _ _ (w.specified_disjoint_exterior hlen)
    w.calibrationEvent A hQ hA
  simpa only [heq] using hh

end RawCorridor
end CorridorIndependence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorContraction
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_union_attachment (G : BondGraph V E) (S T : Set E) (A : Set V)
    (hclosed : ∀ a b, a ∈ A → Conn G S a b → b ∈ A)
    (hT : ∀ e ∈ T, ∀ z ∈ G e, z ∈ A) {x y : V} (hc : Conn G (S ∪ T) x y) :
    Conn G S x y ∨ x ∈ A ∧ y ∈ A := by
  induction hc with
  | refl => exact Or.inl (conn_refl G S x)
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    rcases he with he | he
    · have hab : Conn G S a b := Relation.ReflTransGen.single ⟨e,he,heq⟩
      exact ih.elim (fun h => Or.inl (conn_trans G S h hab))
        (fun h => Or.inr ⟨h.1,hclosed a b h.2 hab⟩)
    · have ha := hT e he a (heq.symm ▸ (by simp : a ∈ s(a,b)))
      have hb := hT e he b (heq.symm ▸ (by simp : b ∈ s(a,b)))
      exact Or.inr ⟨ih.elim (fun h => hclosed a x ha (conn_symm G S h)) And.left,hb⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem support_exterior_ports (w : RawCorridor G k) {z : V}
    (hz : z ∈ w.path.support) (ho : z ∉ w.interior) : z = w.base ∨ z = w.endpoint := by
  simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,hz,true_and,
    Finset.mem_insert,Finset.mem_singleton,not_not] using ho

theorem attachment_closed (w : RawCorridor G k) (ω : Set E) (a b : V)
    (ha : a ∈ w.attachment ω) (hc : Conn G (w.exterior ω) a b) : b ∈ w.attachment ω := by
  rcases ha with ha | ha | ha
  · rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hc with rfl | ho
    · exact Or.inl ha
    · rcases w.support_exterior_ports ha ho.1 with rfl | rfl
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · exact Or.inr (Or.inl (conn_trans G _ ha hc))
  · exact Or.inr (Or.inr (conn_trans G _ ha hc))

theorem open_subset_exterior_retained (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) : ω ⊆ w.exterior ω ∪ w.retained := by
  intro e he
  by_cases hr : e ∈ w.retained
  · exact Or.inr hr
  · left
    refine ⟨he,?_⟩
    intro z hz hi
    exact Set.disjoint_left.mp hq.2 ⟨⟨z,hi,hz⟩,hr⟩ he

theorem connection_exterior_or_attachment (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) {x y : V} (hc : Conn G ω x y) :
    Conn G (w.exterior ω) x y ∨ x ∈ w.attachment ω ∧ y ∈ w.attachment ω := by
  apply conn_union_attachment G _ w.retained (w.attachment ω) (w.attachment_closed ω)
    (fun e he z hz => Or.inl (SimpleGraph.Walk.mem_support_of_mem_edges he hz))
  exact conn_mono G (w.open_subset_exterior_retained ω hq) hc

theorem attachment_outside (w : RawCorridor G k) (ω : Set E) {z : V}
    (ha : z ∈ w.attachment ω) (hz : z ∉ w.interior) :
    Conn G (w.exterior ω) w.base z ∨ Conn G (w.exterior ω) w.endpoint z := by
  rcases ha with ha | ha | ha
  · rcases w.support_exterior_ports ha hz with rfl | rfl
    · exact Or.inl (conn_refl G _ _)
    · exact Or.inr (conn_refl G _ _)
  · exact Or.inl ha
  · exact Or.inr ha

 
theorem counted_exterior_orientation (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (ω : Set E) (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hc : corridorCounted G w.retained w.blockers Set.univ ω x y) :
    ¬Conn G (w.exterior ω) w.base w.endpoint ∧
      ((Conn G (w.exterior ω) w.base x ∧ Conn G (w.exterior ω) w.endpoint y) ∨
       (Conn G (w.exterior ω) w.endpoint x ∧ Conn G (w.exterior ω) w.base y)) := by
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  have hc' : Conn G ω x y := by simpa only [hi,Set.inter_univ] using hc.1
  have hs : w.retained.Nonempty := by
    have hp : w.path.edges ≠ [] := by
      intro he
      have hh := congrArg List.length he
      simp only [SimpleGraph.Walk.length_edges,List.length_nil] at hh
      omega
    obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hp
    obtain ⟨e,he,_⟩ := w.edge_has_label s hs
    exact ⟨e,he⟩
  have hnot : ¬Conn G (w.exterior ω) x y := by
    intro h
    obtain ⟨e,he⟩ := hs
    apply (hc.2.1 e he).2
    apply conn_mono G ?_ h
    intro f hf
    refine ⟨?_,?_⟩
    · simpa only [hi,Set.inter_univ] using hf.1
    · intro hfe
      have hfe' := Set.mem_singleton_iff.mp hfe
      subst f
      exact Set.disjoint_left.mp (w.specified_disjoint_exterior hlen) (Or.inl he) hf.2
  have hatt := (w.connection_exterior_or_attachment ω hq hc').resolve_left hnot
  have hout := w.counted_terminal_outside Set.univ ω x y hc
  have hx := w.attachment_outside ω hatt.1 hout.1
  have hy := w.attachment_outside ω hatt.2 hout.2
  have hne : ¬Conn G (w.exterior ω) w.base w.endpoint := by
    intro h
    apply hnot
    have hx' : Conn G (w.exterior ω) w.base x := hx.elim id (conn_trans G _ h)
    have hy' : Conn G (w.exterior ω) w.base y := hy.elim id (conn_trans G _ h)
    exact conn_trans G _ (conn_symm G _ hx') hy'
  refine ⟨hne,?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hnot (conn_trans G _ (conn_symm G _ hx) hy)).elim
  · exact Or.inl ⟨hx,hy⟩
  · exact Or.inr ⟨hx,hy⟩
  · exact (hnot (conn_trans G _ (conn_symm G _ hx) hy)).elim

end RawCorridor
end CorridorContraction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CorridorBKCalibration
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem measurableSet_exteriorOrientations (w : RawCorridor G k) (x y : V) :
    MeasurableSet (w.exteriorOrientations x y) :=
  (measurableSet_orientedPivotalEvent G x y w.base w.endpoint).union
    (measurableSet_orientedPivotalEvent G x y w.endpoint w.base)

omit [Countable V] [Countable E] in
theorem counted_subset_calibration_exterior (w : RawCorridor G k)
    (hlen : 3 ≤ w.path.length) (x y : V) :
    {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} ⊆
      w.calibrationEvent ∩ (w.exterior ⁻¹' w.exteriorOrientations x y) := by
  intro ω hc
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  have hq : ω ∈ w.calibrationEvent := by
    refine ⟨fun e he => ?_,?_⟩
    · simpa only [hi,Set.inter_univ] using (hc.2.1 e he).1
    · simpa only [hi,Set.inter_univ] using hc.2.2
  refine ⟨hq,?_⟩
  obtain ⟨hne,ho⟩ := w.counted_exterior_orientation hlen ω hq x y hc
  rcases ho with ho | ho
  · exact Or.inl ⟨conn_symm G _ ho.1,ho.2,hne⟩
  · exact Or.inr ⟨conn_symm G _ ho.1,ho.2,fun h => hne (conn_symm G _ h)⟩

omit [Countable V] in
theorem exterior_orientation_BK (w : RawCorridor G k) (p : unitInterval) (x y a b : V) :
    (law p).real (w.exterior ⁻¹' orientedPivotalEvent G x y a b) ≤
      twoPoint G p x a * twoPoint G p b y := by
  apply le_trans (measureReal_mono ?_) (bk p {ω | Conn G ω x a} {ω | Conn G ω b y}
    (fun _ _ h hc => conn_mono G h hc) (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x a) (finiteWitness_conn G b y))
  intro ω h
  exact disjointOccurrence_upper _ _ Set.inter_subset_left
    (orientedPivotalEvent_subset_disjoint G x y a b h)

 

theorem counted_weight_bound (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (x y : V) :
    w.weight P p * (law p).real {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} ≤
      w.probability P * (twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y) := by
  have hi := w.calibration_independent hG hloc hlen p (w.exteriorOrientations x y)
    (w.measurableSet_exteriorOrientations x y)
  have hir : (law p).real (w.calibrationEvent ∩ w.exterior ⁻¹' w.exteriorOrientations x y) =
      (law p).real w.calibrationEvent * (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) := by
    exact congrArg ENNReal.toReal hi |>.trans ENNReal.toReal_mul
  have hb : (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) ≤
      twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y := by
    apply le_trans (measureReal_union_le _ _)
    exact add_le_add (w.exterior_orientation_BK p x y w.base w.endpoint)
      (w.exterior_orientation_BK p x y w.endpoint w.base)
  calc
    _ ≤ w.weight P p * (law p).real (w.calibrationEvent ∩ w.exterior ⁻¹' w.exteriorOrientations x y) :=
      mul_le_mul_of_nonneg_left (measureReal_mono (w.counted_subset_calibration_exterior hlen x y))
        (w.weight_nonneg P hP p)
    _ = w.probability P * (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) := by
      rw [hir,←mul_assoc,w.calibration_identity hG hloc P p hp hp₁]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (w.2.2.mass_nonneg P hP)

end RawCorridor
end CorridorBKCalibration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathIntegration
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_openSimpleGraph_neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Finite ((openSimpleGraph G Set.univ).neighborSet x) := by
  apply Set.Finite.to_subtype
  apply (finite_neighbors hloc x).subset
  intro y hy
  obtain ⟨_,e,_,he⟩ := hy
  exact ⟨e,he⟩

end RawPathIntegration
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSum
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}



theorem counted_iff (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted D ω x y ↔ 3 ≤ w.path.length ∧ corridorCounted G w.retained w.blockers D ω x y := by
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · rintro ⟨hlen,hc⟩
    exact ⟨hlen,w.support_subset_of_retained (by omega) D (fun e he => (hc.2.1 e he).1.2),hc⟩

theorem counted_base_mem_walk (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : w.counted D ω x y) (q : (openSimpleGraph G (ω ∩ internalEdges G D)).Walk x y) :
    w.base ∈ q.support := by
  have hl : 0 < w.path.length := by have := hc.1; omega
  obtain ⟨s,hs,hbs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hl)).mp w.path.start_mem_support
  obtain ⟨e,he,hGe⟩ := w.edge_has_label s hs
  have heq := pivotal_image_mem_edges G _ q e (hc.2.2.2.1 e he).2
  exact SimpleGraph.Walk.mem_support_of_mem_edges heq (hGe.symm ▸ hbs)

theorem counted_symm (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted D ω x y ↔ w.counted D ω y x := by
  rw [counted_iff,counted_iff,corridorCounted_symm]

theorem measurableSet_counted [Countable E] (w : RawCorridor G k) (D : Set V) (x y : V) :
    MeasurableSet {ω | w.counted D ω x y} := by
  simp_rw [w.counted_iff]
  by_cases h : 3 ≤ w.path.length
  · simpa only [h,true_and] using measurableSet_corridorCounted G w.retained w.blockers D x y
  · simp only [h,false_and,Set.ofPred_false]; exact MeasurableSet.empty

end RawCorridor

 theorem finite_corridors_on_bases (G : BondGraph V E) (hloc : LocallyFinite G) (k : ℕ)
    (S : Set V) (hS : S.Finite) : {w : RawCorridor G k | w.base ∈ S}.Finite := by
  let (x : V) : Finite ((openSimpleGraph G Set.univ).neighborSet x) :=
    finite_openSimpleGraph_neighbors G hloc x
  let : Finite S := hS.to_subtype
  let f : (Σ x : S, RawFrom (openSimpleGraph G Set.univ) k x.val) → RawCorridor G k :=
    fun w => ⟨w.1.val,w.2⟩
  have hr : {w : RawCorridor G k | w.base ∈ S} = Set.range f := by
    ext w
    constructor
    · intro hw
      exact ⟨⟨⟨w.base,hw⟩,w.2⟩,rfl⟩
    · rintro ⟨w,rfl⟩
      exact w.1.property
  rw [hr]
  exact Set.finite_range f

 

theorem finite_counted_corridors (G : BondGraph V E) (hloc : LocallyFinite G) (k : ℕ)
    (D : Set V) (ω : Set E) (x y : V) : {w : RawCorridor G k | w.counted D ω x y}.Finite := by
  by_cases hc : Conn G (ω ∩ internalEdges G D) x y
  · obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc
    apply (finite_corridors_on_bases G hloc k {z | z ∈ q.support} (List.finite_toSet _)).subset
    exact fun w hw => w.counted_base_mem_walk D ω x y hw q
  · have he : {w : RawCorridor G k | w.counted D ω x y} = ∅ := by
      ext w
      exact ⟨fun h => hc h.2.2.1,False.elim⟩
    rw [he]
    exact Set.finite_empty

end CorridorSum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualCorridorPenalty
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenaltyTerm_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) {k : ℕ} (D : Set V)
    (ω : Set E) (x y : V) (w : RawCorridor G k) :
    0 ≤ corridorPenaltyTerm G P p D ω x y w := by
  unfold corridorPenaltyTerm
  split_ifs
  · exact w.weight_nonneg P hP p
  · exact le_rfl

theorem corridorPenalty_finite_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    (Function.support (corridorPenaltyTerm G P p (k := k) D ω x y)).Finite := by
  apply (finite_counted_corridors G hloc k D ω x y).subset
  intro w hw
  by_contra hn
  exact hw (ite_eq_right hn)

theorem corridorPenalty_summable (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    Summable (corridorPenaltyTerm G P p (k := k) D ω x y) :=
  summable_of_hasFiniteSupport (corridorPenalty_finite_support G hloc P p k D ω x y)

theorem corridorPenalty_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (D : Set V)
    (ω : Set E) (x y : V) : 0 ≤ corridorPenalty G P p k D ω x y :=
  tsum_nonneg (corridorPenaltyTerm_nonneg G P hP p D ω x y)

theorem corridorPenalty_symm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenalty G P p k D ω x y = corridorPenalty G P p k D ω y x := by
  unfold corridorPenalty
  apply tsum_congr
  intro w
  simp only [corridorPenaltyTerm,w.counted_symm D ω x y]

theorem corridorPenalty_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω')
    (x y : V) (hc : Conn G (ω ∩ internalEdges G D) x y) :
    corridorPenalty G P p k D' ω' x y ≤ corridorPenalty G P p k D ω x y := by
  apply (corridorPenalty_summable G hloc P p k D' ω' x y).tsum_le_tsum ?_
    (corridorPenalty_summable G hloc P p k D ω x y)
  intro w
  by_cases hn : w.counted D' ω' x y
  · have ho : w.counted D ω x y := (w.counted_iff D ω x y).mpr
      ⟨hn.1,corridorCounted_restrict G _ _ hD hω x y hc hn.2.2⟩
    simp only [corridorPenaltyTerm,hn,ho,ite_true,le_refl]
  · simpa only [corridorPenaltyTerm,hn,ite_false] using corridorPenaltyTerm_nonneg G P hP p D ω x y w

theorem measurable_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    Measurable (fun ω => corridorPenaltyTerm G P p D ω x y w) := by
  exact Measurable.ite (w.measurableSet_counted D x y) measurable_const measurable_const

theorem measurable_corridorPenalty [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (x y : V) :
    Measurable (fun ω => corridorPenalty G P p k D ω x y) := by
  exact Measurable.tsum (fun w => measurable_corridorPenaltyTerm G P p D x y w)

end ActualCorridorPenalty
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq



theorem deformedConnection_nonneg (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    0 ≤ deformedConnection G P p k t D ω x y := by
  unfold deformedConnection
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem deformedConnection_le_one (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x y : V) : deformedConnection G P p k t D ω x y ≤ 1 := by
  unfold deformedConnection
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (corridorPenalty_nonneg G P hP p k D ω x y)
  · exact zero_le_one

theorem deformedConnection_symm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t D ω x y = deformedConnection G P p k t D ω y x := by
  have hc : Conn G (ω ∩ internalEdges G D) x y ↔ Conn G (ω ∩ internalEdges G D) y x :=
    ⟨conn_symm G _,conn_symm G _⟩
  simp only [deformedConnection,corridorPenalty_symm G P p k D ω x y,hc]
  congr 1
  apply propext; tauto

theorem deformedConnection_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω')
    (x y : V) : deformedConnection G P p k t D ω x y ≤ deformedConnection G P p k t D' ω' x y := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · have hc' : x ∈ D' ∧ y ∈ D' ∧ Conn G (ω' ∩ internalEdges G D') x y :=
      ⟨hD hc.1,hD hc.2.1,conn_mono G (Set.inter_subset_inter hω (internalEdges_mono G hD)) hc.2.2⟩
    simp only [deformedConnection,hc,hc']
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (corridorPenalty_restrict G hloc P hP p k hD hω x y hc.2.2)
      (neg_nonpos.mpr ht)
  · simpa only [deformedConnection,hc,ite_false] using deformedConnection_nonneg G P p k t D' ω' x y

theorem measurable_deformedConnection [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ)
    (D : Set V) (x y : V) : Measurable (fun ω => deformedConnection G P p k t D ω x y) := by
  have hs : MeasurableSet {ω : Set E | x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y} := by
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
    · simpa only [hx,hy,true_and] using measurableSet_restrictedConn G (internalEdges G D) x y
    all_goals simp only [hx,hy,false_and,and_false,Set.ofPred_false]; exact MeasurableSet.empty
  exact Measurable.ite hs ((measurable_corridorPenalty G P p k D x y).const_mul (-t)).exp measurable_const

theorem integrable_deformedConnection [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (fun ω => deformedConnection G P p k t D ω x y) (law p) := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (measurable_deformedConnection G P p k t D x y).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (deformedConnection_nonneg G P p k t D ω x y)]
  exact deformedConnection_le_one G P hP p k t ht D ω x y

end ActualWeightedConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedConnectionEndpoints
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_zero (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k 0 D ω x y =
      if x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y then 1 else 0 := by
  simp only [deformedConnection,neg_zero,zero_mul,Real.exp_zero]

theorem deformedConnection_full_zero (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (ω : Set E) (x y : V) : deformedConnection G P p k 0 Set.univ ω x y =
      if Conn G ω x y then 1 else 0 := by
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  simp only [deformedConnection_zero,Set.mem_univ,true_and,hi,Set.inter_univ]

theorem deformedConnection_change (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x y : V) :
    0 ≤ deformedConnection G P p k 0 D ω x y - deformedConnection G P p k t D ω x y ∧
    deformedConnection G P p k 0 D ω x y - deformedConnection G P p k t D ω x y ≤
      t*corridorPenalty G P p k D ω x y := by
  have hN := corridorPenalty_nonneg G P hP p k D ω x y
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · simp only [deformedConnection,hc,ite_true,neg_zero,zero_mul,Real.exp_zero,and_self]
    constructor
    · exact sub_nonneg.mpr ((Real.exp_le_one_iff).mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hN))
    · have h := Real.one_sub_le_exp_neg (t*corridorPenalty G P p k D ω x y)
      rw [←neg_mul] at h
      linarith
  · simp only [deformedConnection,hc,ite_false,sub_self]
    exact ⟨le_rfl,mul_nonneg ht hN⟩

theorem deformedKernel_zero [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) (k : ℕ) (x y : V) :
    deformedKernel G P p k 0 Set.univ x y = twoPoint G p x y := by
  unfold deformedKernel
  simp_rw [deformedConnection_full_zero]
  have hi := integral_indicator_const (μ := law p) (1:ℝ) (measurableSet_conn G x y)
  simpa only [Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_one,Measure.real,twoPoint] using hi

end WeightedConnectionEndpoints
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PenaltyTermExpectation
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem integrable_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    Integrable (fun ω => corridorPenaltyTerm G P p D ω x y w) (law p) := by
  exact (integrable_const (w.weight P p)).indicator (w.measurableSet_counted D x y)

theorem integral_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    (∫ ω, corridorPenaltyTerm G P p D ω x y w ∂law p) =
      w.weight P p * (law p).real {ω | w.counted D ω x y} := by
  have h := integral_indicator_const (μ := law p) (w.weight P p) (w.measurableSet_counted D x y)
  simpa only [corridorPenaltyTerm,Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_comm] using h

 
theorem integral_corridorPenaltyTerm_le [Countable V] [Countable E]
    (G : BondGraph V E) (hG : Function.Injective G) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) {k : ℕ} (x y : V) (w : RawCorridor G k) :
    (∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w ∂law p) ≤
      w.probability P * (twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y) := by
  rw [integral_corridorPenaltyTerm]
  by_cases hl : 3 ≤ w.path.length
  · have he : {ω | w.counted Set.univ ω x y} =
        {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} := by
      ext ω
      simp only [Set.mem_ofPred_eq,w.counted_iff,hl,true_and]
    rw [he]
    exact w.counted_weight_bound hG hloc hl P hP p hp hp₁ x y
  · have he : {ω | w.counted Set.univ ω x y} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq,w.counted_iff,hl,false_and,Set.mem_empty_iff_false]
    rw [he,measureReal_empty,mul_zero]
    exact mul_nonneg (w.2.2.mass_nonneg P hP) (add_nonneg
      (mul_nonneg (twoPoint_nonneg G p x w.base) (twoPoint_nonneg G p w.endpoint y))
      (mul_nonneg (twoPoint_nonneg G p x w.endpoint) (twoPoint_nonneg G p w.base y)))

end PenaltyTermExpectation
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SmallDeformationEntrywise
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]



omit [Countable V] [Countable E] in
theorem deformedKernel_nonneg (G : BondGraph V E) (P : V → V → ℝ) (p : unitInterval)
    (k : ℕ) (t : ℝ) (D : Set V) (x y : V) : 0 ≤ deformedKernel G P p k t D x y :=
  integral_nonneg (fun ω => deformedConnection_nonneg G P p k t D ω x y)

end SmallDeformationEntrywise
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_ClusterProducts
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


theorem SimpleVisit.mono (G : BondGraph V E) {S T : Set E} {A B : Set V}
    (hST : S ⊆ T) (hAB : A ⊆ B) {x y : V} (h : SimpleVisit G S A x y) :
    SimpleVisit G T B x y := by
  obtain ⟨q,hq,z,hz,ha⟩ := h
  have hg : openSimpleGraph G S ≤ openSimpleGraph G T := by
    rintro a b ⟨hne,e,he,hGe⟩
    exact ⟨hne,e,hST he,hGe⟩
  exact ⟨q.mapLe hg,hq.mapLe hg,z,by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hz,hAB ha⟩

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

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem counted_support_subset_walk (w : RawCorridor G k) (D : Set V) (ω : Set E)
    (x y : V) (hc : w.counted D ω x y)
    (q : (openSimpleGraph G (ω ∩ internalEdges G D)).Walk x y) :
    ∀ z ∈ w.path.support, z ∈ q.support := by
  intro z hz
  have hl : 0 < w.path.length := by have := hc.1; omega
  obtain ⟨s,hs,hzs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hl)).mp hz
  obtain ⟨e,he,hGe⟩ := w.edge_has_label s hs
  exact SimpleGraph.Walk.mem_support_of_mem_edges
    (pivotal_image_mem_edges G _ q e (hc.2.2.2.1 e he).2) (hGe.symm ▸ hzs)

end RawCorridor

 

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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionCounted
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_delete_of_no_visit (G : BondGraph V E) (ω : Set E) (D A : Set V)
    (x y : V) (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y)
    (S : Set E) (hS : S ⊆ ω ∩ internalEdges G D) (hc : Conn G S x y) :
    Conn G (S ∩ internalEdges G (D \ A)) x y := by
  have hno : ¬SimpleVisit G S A x y := fun h => hn (h.mono G hS (fun _ => Or.inl))
  have h := conn_restrict_of_no_simpleVisit G S A x y hc hno
  apply conn_mono G ?_ h
  rintro e ⟨he,ha⟩
  exact ⟨he,fun z hz => ⟨(hS he).2 z hz,ha z hz⟩⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_before_deletion_of_no_visit (w : RawCorridor G k)
    (D A : Set V) (ω : Set E) (x y : V)
    (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y)
    (hc : w.counted (D \ A) ω x y) : w.counted D ω x y := by
  have hs : ω ∩ internalEdges G (D \ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.sdiff_subset)
  apply (w.counted_iff D ω x y).mpr
  refine ⟨hc.1,conn_mono G hs hc.2.2.1,?_,?_⟩
  · intro e he
    refine ⟨hs (hc.2.2.2.1 e he).1,?_⟩
    intro hbad
    have hd := conn_delete_of_no_visit G ω D A x y hn
      ((ω ∩ internalEdges G D) \ {e}) Set.sdiff_subset hbad
    apply (hc.2.2.2.1 e he).2
    apply conn_mono G ?_ hd
    rintro f ⟨⟨⟨hfω,hfD⟩,hfne⟩,hfnew⟩
    exact ⟨⟨hfω,hfnew⟩,hfne⟩
  · apply Set.disjoint_left.mpr
    intro e he ho
    have henew : e ∉ internalEdges G (D \ A) := fun he' =>
      Set.disjoint_left.mp hc.2.2.2.2 he ⟨ho.1,he'⟩
    obtain ⟨a,ha,hna⟩ : ∃ a ∈ G e, a ∉ D \ A := by
      change ¬(∀ a ∈ G e, a ∈ D \ A) at henew
      push Not at henew
      exact henew
    have haA : a ∈ A := by
      by_contra ha'
      exact hna ⟨ho.2 a ha,ha'⟩
    obtain ⟨z,hzi,hze⟩ := he.1
    obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2.1
    have hz : z ∈ q.bypass.support := w.counted_support_subset_walk (D \ A) ω x y hc q.bypass z
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hzi).1)
    have hv : SimpleVisit G (ω ∩ internalEdges G (D \ A)) (closedBondNeighborhood G A) x y :=
      ⟨q.bypass,q.bypass_isPath,z,hz,Or.inr ⟨e,hze,a,ha,haA⟩⟩
    exact hn (hv.mono G hs (Set.Subset.refl _))

end RawCorridor
end DeletionCounted
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionWeightedLoss
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem deformedConnection_no_visit (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (ω : Set E) (x y : V)
    (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y) :
    deformedConnection G P p k t D ω x y ≤ deformedConnection G P p k t (D \ A) ω x y := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2
    have hx : x ∉ A := fun ha => hn ⟨q.bypass,q.bypass_isPath,x,q.bypass.start_mem_support,Or.inl ha⟩
    have hy : y ∉ A := fun ha => hn ⟨q.bypass,q.bypass_isPath,y,q.bypass.end_mem_support,Or.inl ha⟩
    have hc' : x ∈ D \ A ∧ y ∈ D \ A ∧ Conn G (ω ∩ internalEdges G (D \ A)) x y := by
      refine ⟨⟨hc.1,hx⟩,⟨hc.2.1,hy⟩,?_⟩
      apply conn_mono G ?_ (conn_delete_of_no_visit G ω D A x y hn _ (Set.Subset.refl _) hc.2.2)
      rintro e ⟨⟨heω,heD⟩,henew⟩
      exact ⟨heω,henew⟩
    simp only [deformedConnection,hc,hc']
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left ?_ (neg_nonpos.mpr ht)
    apply (corridorPenalty_summable G hloc P p k (D \ A) ω x y).tsum_le_tsum ?_
      (corridorPenalty_summable G hloc P p k D ω x y)
    intro w
    by_cases hw : w.counted (D \ A) ω x y
    · have hw' := w.counted_before_deletion_of_no_visit D A ω x y hn hw
      simp only [corridorPenaltyTerm,hw,hw',ite_true,le_refl]
    · simpa only [corridorPenaltyTerm,hw,ite_false] using corridorPenaltyTerm_nonneg G P hP p D ω x y w
  · simpa only [deformedConnection,hc,ite_false] using deformedConnection_nonneg G P p k t (D \ A) ω x y

 

theorem deformedConnection_deletion_pointwise (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ≤
      if ∃ z ∈ closedBondNeighborhood G A,
        ω ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} then 1 else 0 := by
  split_ifs with h
  · linarith [deformedConnection_le_one G P hP p k t ht D ω x y,
      deformedConnection_nonneg G P p k t (D \ A) ω x y]
  · apply sub_nonpos.mpr
    apply deformedConnection_no_visit G hloc P hP p k t ht D A ω x y
    rintro ⟨q,hq,z,hz,hza⟩
    apply h
    exact ⟨z,hza,disjointOccurrence_upper _ _ Set.inter_subset_left (simplePath_disjoint_at G _ q hq hz)⟩

end DeletionWeightedLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeletionKernelBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem deformedKernel_deletion_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (x y : V)
    (hs : Summable (fun z : closedBondNeighborhood G A => twoPoint G p x z * twoPoint G p z y)) :
    deformedKernel G P p k t D x y - deformedKernel G P p k t (D \ A) x y ≤
      ∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y := by
  let B := fun z : closedBondNeighborhood G A =>
    DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y}
  let U := ⋃ z, B z
  have hBm (z : closedBondNeighborhood G A) : MeasurableSet (B z) :=
    measurableSet_finiteWitness _ (disjointOccurrence_upper _ _) (finiteWitness_disjointOccurrence _ _)
  have hUm : MeasurableSet U := MeasurableSet.iUnion hBm
  have hBn (z : closedBondNeighborhood G A) : 0 ≤ twoPoint G p x z * twoPoint G p z y :=
    mul_nonneg (twoPoint_nonneg G p x z) (twoPoint_nonneg G p z y)
  have hBK (z : closedBondNeighborhood G A) : law p (B z) ≤ ENNReal.ofReal (twoPoint G p x z * twoPoint G p z y) := by
    rw [←ENNReal.ofReal_toReal (measure_ne_top (law p) (B z))]
    exact ENNReal.ofReal_le_ofReal (bk p _ _ (fun _ _ h hc => conn_mono G h hc)
      (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x z) (finiteWitness_conn G z y))
  have hU : (law p).real U ≤ ∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y := by
    have hh : law p U ≤ ENNReal.ofReal (∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y) := by
      calc
        _ ≤ ∑' z, law p (B z) := measure_iUnion_le B
        _ ≤ ∑' z : closedBondNeighborhood G A, ENNReal.ofReal (twoPoint G p x z * twoPoint G p z y) := ENNReal.tsum_le_tsum hBK
        _ = _ := (ENNReal.ofReal_tsum_of_nonneg hBn hs).symm
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (tsum_nonneg hBn))
  have hUi : Integrable (U.indicator (fun _ : Set E => (1:ℝ))) (law p) := (integrable_const _).indicator hUm
  have hpoint (ω : Set E) : deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ≤
      U.indicator (fun _ : Set E => (1:ℝ)) ω := by
    have he : ω ∈ U ↔ ∃ z ∈ closedBondNeighborhood G A, ω ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} := by
      simp [U,B]
    simpa only [Set.indicator_apply,he] using deformedConnection_deletion_pointwise G hloc P hP p k t ht D A ω x y
  have hi := integrable_deformedConnection G P hP p k t ht D x y
  have hi' := integrable_deformedConnection G P hP p k t ht (D \ A) x y
  calc
    _ = ∫ ω, deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ∂law p := (integral_sub hi hi').symm
    _ ≤ ∫ ω, U.indicator (fun _ : Set E => (1:ℝ)) ω ∂law p := integral_mono (hi.sub hi') hUi hpoint
    _ = (law p).real U := integral_indicator_one hUm
    _ ≤ _ := hU

end DeletionKernelBound
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedKernel_le_twoPoint [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    deformedKernel G P p k t D x y ≤ twoPoint G p x y := by
  rw [←deformedKernel_zero G P p k x y]
  apply integral_mono (integrable_deformedConnection G P hP p k t ht D x y)
    (integrable_deformedConnection G P hP p k 0 (le_refl _) Set.univ x y)
  intro ω
  exact (deformedConnection_mono G hloc P hP p k t ht (Set.subset_univ D)
    (Set.Subset.refl _) x y).trans (sub_nonneg.mp (deformedConnection_change G P hP p k t ht Set.univ ω x y).1)

theorem summable_deformedKernel [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    Summable (deformedKernel G P p k t D x) :=
  Summable.of_nonneg_of_le (deformedKernel_nonneg G P p k t D x)
    (deformedKernel_le_twoPoint G hloc P hP p k t ht D x)
    (summable_twoPoint_subcritical G hloc hqt p hp x)

theorem deformedSusceptibility_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    deformedSusceptibility G P p k t D x ≤ susceptibility G p x :=
  (summable_deformedKernel G hloc hqt P hP p hp k t ht D x).tsum_le_tsum
    (deformedKernel_le_twoPoint G hloc P hP p k t ht D x)
    (summable_twoPoint_subcritical G hloc hqt p hp x)

end DeformedSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionSusceptibilityEstimate
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem summable_twoPoint_restricted_pair (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x : V) (N : Set V) :
    Summable (fun zy : N×V => twoPoint G p x zy.1 * twoPoint G p zy.1 zy.2) := by
  apply (summable_twoPoint_pair G hloc hqt p hp x).comp_injective (i := fun zy : N×V => (zy.1.val,zy.2))
  intro a b hab
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hab)) (congrArg (fun z : V×V => z.2) hab)

theorem twoPoint_double_restricted_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x : V) (N : Set V) :
    (∑' y : V, ∑' z : N, twoPoint G p x z * twoPoint G p z y) ≤
      maxSusceptibility G p * (∑' z : N, twoPoint G p x z) := by
  have hpairs := summable_twoPoint_restricted_pair G hloc hqt p hp x N
  have hcomm : (∑' y : V, ∑' z : N, twoPoint G p x z * twoPoint G p z y) =
      ∑' z : N, twoPoint G p x z * susceptibility G p z := by
    calc
      _ = ∑' z : N, ∑' y : V, twoPoint G p x z * twoPoint G p z y := hpairs.tsum_comm
      _ = _ := by simp only [tsum_mul_left, susceptibility]
  have hprod : Summable (fun z : N => twoPoint G p x z * susceptibility G p z) := by
    simpa only [tsum_mul_left, susceptibility] using hpairs.prod
  rw [hcomm]
  calc
    _ ≤ ∑' z : N, twoPoint G p x z * maxSusceptibility G p :=
      hprod.tsum_le_tsum
        (fun z => mul_le_mul_of_nonneg_left (susceptibility_le_max G hloc hqt p hp z) (twoPoint_nonneg G p x z))
        ((summable_twoPoint_subcritical G hloc hqt p hp x).subtype N |>.mul_right _)
    _ = _ := by rw [tsum_mul_right,mul_comm]

 

theorem deformedSusceptibility_deletion (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D A : Set V) (x : V) :
    deformedSusceptibility G P p k t D x -
      maxSusceptibility G p * (∑' z : closedBondNeighborhood G A, twoPoint G p x z) ≤
      deformedSusceptibility G P p k t (D \ A) x := by
  let N := closedBondNeighborhood G A
  have hpairs := summable_twoPoint_restricted_pair G hloc hqt p hp x N
  have hdiag (y : V) := hpairs.prod_symm.prod_factor y
  have hi := summable_deformedKernel G hloc hqt P hP p hp k t ht D x
  have hi' := summable_deformedKernel G hloc hqt P hP p hp k t ht (D \ A) x
  have hb := (hi.sub hi').tsum_le_tsum
    (fun y => deformedKernel_deletion_bound G hloc P hP p k t ht D A x y (hdiag y)) hpairs.prod_symm.prod
  rw [hi.tsum_sub hi'] at hb
  change deformedSusceptibility G P p k t D x - deformedSusceptibility G P p k t (D \ A) x ≤ _ at hb
  have herr := twoPoint_double_restricted_bound G hloc hqt p hp x N
  linarith

end DeletionSusceptibilityEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExteriorCorridorGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conn_of_open_incident (G : BondGraph V E) (ω : Set E) (e : E)
    (he : e ∈ ω) (a b : V) (ha : a ∈ G e) (hb : b ∈ G e) : Conn G ω a b := by
  obtain ⟨c,d,hcd⟩ : ∃ c d, G e = s(c,d) := by
    obtain ⟨⟨c,d⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨c,d,hh.symm⟩
  rw [hcd,Sym2.mem_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact conn_refl G ω _
  · exact .single ⟨e,he,hcd⟩
  · exact conn_symm G ω (.single ⟨e,he,hcd⟩)
  · exact conn_refl G ω _

 

theorem conn_restrict_away_from_cluster (G : BondGraph V E) (ω S : Set E)
    (hS : S ⊆ ω) (u x y : V) (hx : x ∉ cluster G ω u) (hc : Conn G S x y) :
    Conn G (S ∩ internalEdges G (cluster G ω u)ᶜ) x y := by
  apply conn_restrict_of_no_simpleVisit G S (cluster G ω u) x y hc
  rintro ⟨q,_,z,hz,hzu⟩
  have hxz : Conn G ω x z := conn_mono G hS
    ((conn_iff_reachable G S x z).mpr ⟨q.takeUntil z hz⟩)
  exact hx (hzu.trans (conn_symm G ω hxz))

theorem conn_delete_cluster (G : BondGraph V E) (D : Set V) (ω : Set E)
    (u x y : V) (hx : x ∉ cluster G (ω ∩ internalEdges G D) u)
    (S : Set E) (hS : S ⊆ ω ∩ internalEdges G D) (hc : Conn G S x y) :
    Conn G (S ∩ internalEdges G (D \ cluster G (ω ∩ internalEdges G D) u)) x y := by
  apply conn_mono G ?_ (conn_restrict_away_from_cluster G _ S hS u x y hx hc)
  rintro e ⟨he,heA⟩
  exact ⟨he,fun z hz => ⟨(hS he).2 z hz,heA z hz⟩⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_delete_other_cluster (w : RawCorridor G k) (D : Set V) (ω : Set E)
    (u x y : V) (hx : x ∉ cluster G (ω ∩ internalEdges G D) u) :
    w.counted (D \ cluster G (ω ∩ internalEdges G D) u) ω x y ↔ w.counted D ω x y := by
  let A := cluster G (ω ∩ internalEdges G D) u
  have hs : ω ∩ internalEdges G (D \ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.sdiff_subset)
  constructor
  · intro hc
    apply (w.counted_iff D ω x y).mpr
    refine ⟨hc.1,conn_mono G hs hc.2.2.1,?_,?_⟩
    · intro e he
      refine ⟨hs (hc.2.2.2.1 e he).1,?_⟩
      intro hbad
      have hd := conn_delete_cluster G D ω u x y hx
        ((ω ∩ internalEdges G D) \ {e}) Set.sdiff_subset hbad
      apply (hc.2.2.2.1 e he).2
      apply conn_mono G ?_ hd
      rintro f ⟨⟨⟨hfω,hfD⟩,hfne⟩,hfnew⟩
      exact ⟨⟨hfω,hfnew⟩,hfne⟩
    · apply Set.disjoint_left.mpr
      intro e he ho
      obtain ⟨z,hzi,hze⟩ := he.1
      obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2.1
      have hz : z ∈ q.support := w.counted_support_subset_walk (D \ A) ω x y hc q z
        (List.mem_toFinset.mp (Finset.mem_sdiff.mp hzi).1)
      have hxz : Conn G (ω ∩ internalEdges G D) x z := conn_mono G hs
        ((conn_iff_reachable G _ x z).mpr ⟨q.takeUntil z hz⟩)
      have heA : e ∈ internalEdges G (D \ A) := by
        intro a ha
        refine ⟨ho.2 a ha,?_⟩
        intro hau
        have hza := conn_of_open_incident G _ e ho z a hze ha
        exact hx (hau.trans (conn_symm G _ (hxz.trans hza)))
      exact Set.disjoint_left.mp hc.2.2.2.2 he ⟨ho.1,heA⟩
  · intro hc
    have hnew := conn_delete_cluster G D ω u x y hx _ (Set.Subset.refl _) hc.2.2.1
    have hc' : Conn G (ω ∩ internalEdges G (D \ A)) x y := by
      apply conn_mono G ?_ hnew
      rintro e ⟨⟨heω,_⟩,heA⟩
      exact ⟨heω,heA⟩
    exact (w.counted_iff _ ω x y).mpr ⟨hc.1,
      corridorCounted_restrict G _ _ Set.sdiff_subset (Set.Subset.refl _) x y hc' hc.2.2⟩

end RawCorridor
end ExteriorCorridorGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenalty_delete_other_cluster (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (u x y : V)
    (hx : x ∉ cluster G (ω ∩ internalEdges G D) u) :
    corridorPenalty G P p k (D \ cluster G (ω ∩ internalEdges G D) u) ω x y =
      corridorPenalty G P p k D ω x y := by
  unfold corridorPenalty
  apply tsum_congr
  intro w
  simp only [corridorPenaltyTerm,w.counted_delete_other_cluster D ω u x y hx]

 

theorem deformedConnection_delete_other_cluster (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (u x y : V)
    (hx : x ∉ cluster G (ω ∩ internalEdges G D) u) :
    deformedConnection G P p k t (D \ cluster G (ω ∩ internalEdges G D) u) ω x y =
      deformedConnection G P p k t D ω x y := by
  let A := cluster G (ω ∩ internalEdges G D) u
  have hs : ω ∩ internalEdges G (D \ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.sdiff_subset)
  have hg : (x ∈ D \ A ∧ y ∈ D \ A ∧ Conn G (ω ∩ internalEdges G (D \ A)) x y) ↔
      (x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y) := by
    constructor
    · exact fun h => ⟨h.1.1,h.2.1.1,conn_mono G hs h.2.2⟩
    · rintro ⟨hxD,hyD,hc⟩
      have hy : y ∉ A := fun hy => hx (hy.trans (conn_symm G _ hc))
      refine ⟨⟨hxD,hx⟩,⟨hyD,hy⟩,?_⟩
      apply conn_mono G ?_ (conn_delete_cluster G D ω u x y hx _ (Set.Subset.refl _) hc)
      rintro e ⟨⟨heω,_⟩,heA⟩
      exact ⟨heω,heA⟩
  dsimp only [A] at hg
  simp only [deformedConnection,hg,corridorPenalty_delete_other_cluster G P p k D ω u x y hx]

theorem deformedClusterMass_delete_other_cluster (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (u x : V)
    (hx : x ∉ cluster G (ω ∩ internalEdges G D) u) :
    deformedClusterMass G P p k t (D \ cluster G (ω ∩ internalEdges G D) u) ω x =
      deformedClusterMass G P p k t D ω x := by
  exact tsum_congr (fun y => deformedConnection_delete_other_cluster G P p k t D ω u x y hx)

theorem measurable_deformedClusterMass [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    Measurable (fun ω => deformedClusterMass G P p k t D ω x) :=
  Measurable.tsum (fun y => measurable_deformedConnection G P p k t D x y)

end ExteriorWeightedConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedMassIntegrals
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_finite_support (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) :
    (deformedConnection G P p k t D ω x).HasFiniteSupport := by
  apply hf.subset
  intro y hy
  by_contra hn
  have hnc : ¬Conn G (ω ∩ internalEdges G D) x y := fun h => hn (conn_mono G Set.inter_subset_left h)
  exact hy (by simp only [deformedConnection,hnc,and_false,ite_false])

theorem deformedClusterMass_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) :
    0 ≤ deformedClusterMass G P p k t D ω x :=
  tsum_nonneg (deformedConnection_nonneg G P p k t D ω x)

theorem deformedClusterMass_le_ncard (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    deformedClusterMass G P p k t D ω x ≤ ((cluster G ω x).ncard:ℝ) := by
  unfold deformedClusterMass
  rw [tsum_eq_sum (s := hf.toFinset) (fun y hy => by
    have hn : ¬Conn G ω x y := fun hc => hy (hf.mem_toFinset.mpr hc)
    have hn' : ¬Conn G (ω ∩ internalEdges G D) x y := fun hc => hn (conn_mono G Set.inter_subset_left hc)
    simp only [deformedConnection,hn',and_false,ite_false])]
  calc
    _ ≤ ∑ _y ∈ hf.toFinset, (1:ℝ) := Finset.sum_le_sum (fun y _ => deformedConnection_le_one G P hP p k t ht D ω x y)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hf]

theorem integrable_deformedClusterMass [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    Integrable (fun ω => deformedClusterMass G P p k t D ω x) (law p) := by
  apply Integrable.mono' (susceptibility_eq_integral G hloc hqt p hp x).1
    (measurable_deformedClusterMass G P p k t D x).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
  rw [Real.norm_of_nonneg (deformedClusterMass_nonneg G P p k t D ω x)]
  exact deformedClusterMass_le_ncard G P hP p k t ht D ω x hω

 

theorem deformedSusceptibility_eq_integral [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    deformedSusceptibility G P p k t D x = ∫ ω, deformedClusterMass G P p k t D ω x ∂law p := by
  have hi := integrable_deformedConnection G P hP p k t ht D x
  have hs : Summable (fun y => ∫ ω, ‖deformedConnection G P p k t D ω x y‖ ∂law p) := by
    simp only [Real.norm_of_nonneg (deformedConnection_nonneg G P p k t D _ x _)]
    exact summable_deformedKernel G hloc hqt P hP p hp k t ht D x
  exact integral_tsum_of_summable_integral_norm hi hs

end DeformedMassIntegrals
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExactComponentRestriction
attribute [local instance] Classical.propDecidable Classical.decEq


theorem openClosed_cluster (G : BondGraph V E) (ω : Set E) (x : V) :
    OpenClosed G ω (cluster G ω x) := by
  intro e he z hz hx a ha
  exact hx.trans (conn_of_open_incident G ω e he z a hz ha)

theorem conn_restrict_openClosed (G : BondGraph V E) (ω S : Set E) (hS : S ⊆ ω)
    (A : Set V) (hA : OpenClosed G ω A) (x y : V) (hx : x ∈ A) (hc : Conn G S x y) :
    y ∈ A ∧ Conn G (S ∩ internalEdges G A) x y := by
  induction hc with
  | refl => exact ⟨hx,conn_refl G _ x⟩
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    have ha : a ∈ G e := by simp [heq]
    have hb : b ∈ G e := by simp [heq]
    have hei : e ∈ internalEdges G A := hA e (hS he) a ha ih.1
    exact ⟨hei b hb,ih.2.tail ⟨e,⟨he,hei⟩,heq⟩⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_restrict_openClosed (w : RawCorridor G k) (D A : Set V) (ω : Set E)
    (hA : OpenClosed G (ω ∩ internalEdges G D) A) (x y : V) (hx : x ∈ A) :
    w.counted (D ∩ A) ω x y ↔ w.counted D ω x y := by
  have hs : ω ∩ internalEdges G (D ∩ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.inter_subset_left)
  have hrest (S : Set E) (hS : S ⊆ ω ∩ internalEdges G D) (hc : Conn G S x y) :
      Conn G (S ∩ internalEdges G (D ∩ A)) x y := by
    apply conn_mono G ?_ (conn_restrict_openClosed G _ S hS A hA x y hx hc).2
    rintro e ⟨he,heA⟩
    exact ⟨he,fun z hz => ⟨(hS he).2 z hz,heA z hz⟩⟩
  constructor
  · intro hc
    apply (w.counted_iff D ω x y).mpr
    refine ⟨hc.1,conn_mono G hs hc.2.2.1,?_,?_⟩
    · intro e he
      refine ⟨hs (hc.2.2.2.1 e he).1,?_⟩
      intro hbad
      apply (hc.2.2.2.1 e he).2
      apply conn_mono G ?_ (hrest _ Set.sdiff_subset hbad)
      rintro f ⟨⟨⟨hfω,_⟩,hfne⟩,hfnew⟩
      exact ⟨⟨hfω,hfnew⟩,hfne⟩
    · apply Set.disjoint_left.mpr
      intro e he ho
      obtain ⟨z,hzi,hze⟩ := he.1
      have hz : z ∈ A := (hc.2.1 z (List.mem_toFinset.mp (Finset.mem_sdiff.mp hzi).1)).2
      have heA : e ∈ internalEdges G (D ∩ A) := fun a ha => ⟨ho.2 a ha,hA e ho z hze hz a ha⟩
      exact Set.disjoint_left.mp hc.2.2.2.2 he ⟨ho.1,heA⟩
  · intro hc
    have hc' : Conn G (ω ∩ internalEdges G (D ∩ A)) x y := by
      apply conn_mono G ?_ (hrest _ (Set.Subset.refl _) hc.2.2.1)
      rintro e ⟨⟨heω,_⟩,heA⟩
      exact ⟨heω,heA⟩
    exact (w.counted_iff _ ω x y).mpr ⟨hc.1,
      corridorCounted_restrict G _ _ Set.inter_subset_left (Set.Subset.refl _) x y hc' hc.2.2⟩

end RawCorridor
end ExactComponentRestriction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section InternalWeightedRestriction
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenalty_restrict_openClosed (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (D A : Set V) (ω : Set E)
    (hA : OpenClosed G (ω ∩ internalEdges G D) A) (x y : V) (hx : x ∈ A) :
    corridorPenalty G P p k (D ∩ A) ω x y = corridorPenalty G P p k D ω x y := by
  unfold corridorPenalty
  apply tsum_congr
  intro w
  simp only [corridorPenaltyTerm,w.counted_restrict_openClosed D A ω hA x y hx]

theorem deformedConnection_restrict_openClosed (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D A : Set V) (ω : Set E)
    (hA : OpenClosed G (ω ∩ internalEdges G D) A) (x y : V) (hx : x ∈ A) :
    deformedConnection G P p k t (D ∩ A) ω x y = deformedConnection G P p k t D ω x y := by
  have hg : (x ∈ D ∩ A ∧ y ∈ D ∩ A ∧ Conn G (ω ∩ internalEdges G (D ∩ A)) x y) ↔
      (x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y) := by
    constructor
    · exact fun h => ⟨h.1.1,h.2.1.1,conn_mono G
        (Set.inter_subset_inter_right _ (internalEdges_mono G Set.inter_subset_left)) h.2.2⟩
    · rintro ⟨hxD,hyD,hc⟩
      have hh := conn_restrict_openClosed G _ _ (Set.Subset.refl _) A hA x y hx hc
      refine ⟨⟨hxD,hx⟩,⟨hyD,hh.1⟩,conn_mono G ?_ hh.2⟩
      rintro e ⟨⟨heω,heD⟩,heA⟩
      exact ⟨heω,fun z hz => ⟨heD z hz,heA z hz⟩⟩
  simp only [deformedConnection,hg,corridorPenalty_restrict_openClosed G P p k D A ω hA x y hx]

theorem deformedClusterMass_restrict_openClosed (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D A : Set V) (ω : Set E)
    (hA : OpenClosed G (ω ∩ internalEdges G D) A) (x : V) (hx : x ∈ A) :
    deformedClusterMass G P p k t (D ∩ A) ω x = deformedClusterMass G P p k t D ω x :=
  tsum_congr (fun y => deformedConnection_restrict_openClosed G P p k t D A ω hA x y hx)

 
theorem deformedClusterMass_restrict_config (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) (S : Set E)
    (hS : internalEdges G D ⊆ S) :
    deformedClusterMass G P p k t D (ω ∩ S) x = deformedClusterMass G P p k t D ω x := by
  have he : (ω ∩ S) ∩ internalEdges G D = ω ∩ internalEdges G D := by
    ext e
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hS h.2⟩,h.2⟩⟩
  apply tsum_congr
  intro y
  have hc (w : RawCorridor G k) : w.counted D (ω ∩ S) x y ↔ w.counted D ω x y := by
    simp only [RawCorridor.counted,corridorCounted,he]
  simp only [deformedConnection,corridorPenalty,corridorPenaltyTerm,hc,he]

end InternalWeightedRestriction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section DisjointCoordinateObservables
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem restriction_functions_independent (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (f g : Set E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ ω, f ω = f (ω ∩ S)) (hgT : ∀ ω, g ω = g (ω ∩ T)) :
    IndepFun f g (law p) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  have he (h : Set E → ℝ) (U : Set E) (hU : ∀ ω, h ω = h (ω ∩ U)) (C : Set ℝ) :
      (fun ω => ω ∩ U) ⁻¹' (h ⁻¹' C) = h ⁻¹' C := by
    ext ω
    simp only [Set.mem_preimage,←hU ω]
  simpa only [he f S hfS A,he g T hgT B] using
    restriction_events_independent p S T hST (f ⁻¹' A) (g ⁻¹' B)
      (hA.preimage hf) (hB.preimage hg)

theorem integral_mul_disjoint_coordinates (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (f g : Set E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ ω, f ω = f (ω ∩ S)) (hgT : ∀ ω, g ω = g (ω ∩ T)) :
    (∫ ω, f ω*g ω ∂law p) = (∫ ω, f ω ∂law p)*(∫ ω, g ω ∂law p) :=
  (restriction_functions_independent p S T hST f g hf hg hfS hgT).integral_mul_eq_mul_integral
    hf.aestronglyMeasurable hg.aestronglyMeasurable

end DisjointCoordinateObservables
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactWeightedClusterCell
attribute [local instance] Classical.propDecidable Classical.decEq

theorem induced_cluster_restrict_incident_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (W : Finset V) (D : Set V) (ω : Set E) (x : V) :
    cluster G ((ω ∩ (incidentSupport G hloc W:Set E)) ∩ internalEdges G D) x = (W:Set V) ↔
      cluster G (ω ∩ internalEdges G D) x = (W:Set V) := by
  rw [Set.inter_right_comm]
  exact cluster_restrict_incident_eq_iff G hloc W _ (Finset.Subset.refl _) _ x

theorem weighted_cluster_cell_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (W : Finset V) (x : V)
    (ω : Set E) :
    (if cluster G (ω ∩ internalEdges G D) x = (W:Set V)
      then deformedClusterMass G P p k t D ω x else 0) =
    (if cluster G ((ω ∩ (incidentSupport G hloc W:Set E)) ∩ internalEdges G D) x = (W:Set V)
      then deformedClusterMass G P p k t D (ω ∩ (incidentSupport G hloc W:Set E)) x else 0) := by
  simp only [induced_cluster_restrict_incident_iff]
  split_ifs with hW
  · have hx : x ∈ (W:Set V) := hW ▸ conn_refl G _ x
    have hA : OpenClosed G (ω ∩ internalEdges G D) (W:Set V) := hW ▸ openClosed_cluster G _ x
    have hW' := (induced_cluster_restrict_incident_iff G hloc W D ω x).mpr hW
    have hA' : OpenClosed G ((ω ∩ (incidentSupport G hloc W:Set E)) ∩ internalEdges G D) (W:Set V) :=
      hW' ▸ openClosed_cluster G _ x
    rw [←deformedClusterMass_restrict_openClosed G P p k t D W ω hA x hx,
      ←deformedClusterMass_restrict_openClosed G P p k t D W _ hA' x hx]
    symm
    apply deformedClusterMass_restrict_config
    intro e he
    exact (mem_incidentSupport G hloc W e).mpr
      ⟨(G e).out.1,(he _ (Sym2.out_fst_mem _)).2,Sym2.out_fst_mem _⟩
  · rfl

 

theorem weighted_cluster_cell_exposure [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (W : Finset V) (x y : V) :
    (∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V)
      then deformedClusterMass G P p k t D ω x else 0) *
        deformedClusterMass G P p k t (D \ (W:Set V)) ω y ∂law p) =
    (∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V)
      then deformedClusterMass G P p k t D ω x else 0) ∂law p) *
        deformedSusceptibility G P p k t (D \ (W:Set V)) y := by
  rw [deformedSusceptibility_eq_integral G hloc hqt P hP p hp k t ht]
  apply integral_mul_disjoint_coordinates p (incidentSupport G hloc W:Set E)
    (incidentSupport G hloc W:Set E)ᶜ disjoint_compl_right
  · exact Measurable.ite ((measurableSet_cluster_eq G x W).preimage (measurable_inter_const _))
      (measurable_deformedClusterMass G P p k t D x) measurable_const
  · exact measurable_deformedClusterMass G P p k t _ y
  · exact weighted_cluster_cell_local G hloc P p k t D W x
  · intro ω
    symm
    apply deformedClusterMass_restrict_config
    rw [complement_incidentSupport]
    exact fun e he z hz => (he z hz).2

end ExactWeightedClusterCell
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section InducedClusterPartition
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem integral_induced_cluster_finite_partition [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (D : Set V) (x : V)
    (f : Set E → ℝ) (hf : Integrable f (law p)) :
    (∫ ω, f ω ∂law p) = ∑' W : Finset V,
      ∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then f ω else 0) ∂law p := by
  let F (W : Finset V) (ω : Set E) := if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then f ω else 0
  have hi (W : Finset V) : Integrable (F W) (law p) := by
    have he : F W = {ω : Set E | cluster G (ω ∩ internalEdges G D) x = (W:Set V)}.indicator f := by
      funext ω
      simp only [F,Set.indicator,Set.mem_ofPred_eq]
      split_ifs <;> rfl
    rw [he]
    exact hf.indicator ((measurableSet_cluster_eq G x W).preimage (measurable_inter_const _))
  have hb (S : Finset (Finset V)) (ω : Set E) : (∑ W ∈ S, ‖F W ω‖) ≤ ‖f ω‖ := by
    by_cases hex : ∃ W ∈ S, cluster G (ω ∩ internalEdges G D) x = (W:Set V)
    · obtain ⟨W,hWS,hW⟩ := hex
      rw [Finset.sum_eq_single W]
      · simp only [F,hW,ite_true,le_refl]
      · intro U _ hU
        have hu : cluster G (ω ∩ internalEdges G D) x ≠ (U:Set V) := fun h => hU (Finset.coe_injective (h.symm.trans hW))
        simp only [F,ite_eq_right hu,norm_zero]
      · exact fun h => (h hWS).elim
    · have he (W : Finset V) (hW : W ∈ S) : cluster G (ω ∩ internalEdges G D) x ≠ (W:Set V) := fun h => hex ⟨W,hW,h⟩
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
      exact (tsum_cluster_cells G (ω ∩ internalEdges G D) x
        (hω.subset (fun _ h => conn_mono G Set.inter_subset_left h)) (f ω)).symm
    _ = _ := (integral_tsum_of_summable_integral_norm hi hn).symm

end InducedClusterPartition
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedClusterProducts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedClusterMass_eq_zero_of_not_mem (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) (hx : x ∉ D) :
    deformedClusterMass G P p k t D ω x = 0 := by
  simp only [deformedClusterMass,deformedConnection,hx,false_and,ite_false,tsum_zero]

theorem deformed_distinct_product_eq_exterior (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    (if ¬Conn G (ω ∩ internalEdges G D) x y then
      deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) =
    deformedClusterMass G P p k t D ω x *
      deformedClusterMass G P p k t (D \ cluster G (ω ∩ internalEdges G D) x) ω y := by
  by_cases hc : Conn G (ω ∩ internalEdges G D) x y
  · rw [ite_eq_right (not_not_intro hc),deformedClusterMass_eq_zero_of_not_mem G P p k t _ ω y
      (fun h => h.2 hc),mul_zero]
  · rw [ite_eq_left hc,deformedClusterMass_delete_other_cluster G P p k t D ω x y hc]

theorem integrable_deformed_product [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (fun ω => deformedClusterMass G P p k t D ω x *
      deformedClusterMass G P p k t D ω y) (law p) := by
  apply Integrable.mono' (subcritical_cluster_association G hloc hqt p hp x y).1
    ((measurable_deformedClusterMass G P p k t D x).mul
      (measurable_deformedClusterMass G P p k t D y)).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
  dsimp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (deformedClusterMass_nonneg G P p k t D ω x)
    (deformedClusterMass_nonneg G P p k t D ω y))]
  exact mul_le_mul (deformedClusterMass_le_ncard G P hP p k t ht D ω x hx)
    (deformedClusterMass_le_ncard G P hP p k t ht D ω y hy)
    (deformedClusterMass_nonneg G P p k t D ω y) (Nat.cast_nonneg _)

theorem integrable_distinct_deformed_product [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (fun ω => if ¬Conn G (ω ∩ internalEdges G D) x y then
      deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) (law p) := by
  have he : (fun ω => if ¬Conn G (ω ∩ internalEdges G D) x y then
      deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) =
      {ω | Conn G (ω ∩ internalEdges G D) x y}ᶜ.indicator
        (fun ω => deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y) := by
    funext ω
    simp only [Set.indicator,Set.mem_compl_iff,Set.mem_ofPred_eq]
  rw [he]
  exact (integrable_deformed_product G hloc hqt P hP p hp k t ht D x y).indicator
    (((measurableSet_conn G x y).preimage (measurable_inter_const (internalEdges G D))).compl)

end DeformedClusterProducts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshWeightedMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedSusceptibility_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    0 ≤ deformedSusceptibility G P p k t D x :=
  tsum_nonneg (deformedKernel_nonneg G P p k t D x)

theorem deformedFreshExteriorMoment_eq_tsum (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) (ω : Set E)
    (hf : (cluster G (ω ∩ internalEdges G D) x).Finite) :
    deformedFreshExteriorMoment G P p k t D x y ω = ∑' W : Finset V,
      if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then
        deformedClusterMass G P p k t D ω x * deformedSusceptibility G P p k t (D \ (W:Set V)) y else 0 := by
  rw [←tsum_cluster_cells G (ω ∩ internalEdges G D) x hf (deformedFreshExteriorMoment G P p k t D x y ω)]
  apply tsum_congr
  intro W
  split_ifs with hW
  · simp only [deformedFreshExteriorMoment,hW]
  · rfl

theorem integrable_deformedFreshExteriorMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (deformedFreshExteriorMoment G P p k t D x y) (law p) := by
  have hm : AEStronglyMeasurable (deformedFreshExteriorMoment G P p k t D x y) (law p) := by
    have hh : Measurable (fun ω => ∑' W : Finset V,
        if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then
          deformedClusterMass G P p k t D ω x * deformedSusceptibility G P p k t (D \ (W:Set V)) y else 0) := by
      apply Measurable.tsum
      intro W
      exact Measurable.ite ((measurableSet_cluster_eq G x W).preimage (measurable_inter_const _))
        ((measurable_deformedClusterMass G P p k t D x).mul_const _) measurable_const
    apply hh.aestronglyMeasurable.congr
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    exact (deformedFreshExteriorMoment_eq_tsum G P p k t D x y ω
      (hω.subset (fun _ h => conn_mono G Set.inter_subset_left h))).symm
  apply Integrable.mono' ((integrable_deformedClusterMass G hloc hqt P hP p hp k t ht D x).mul_const
    (susceptibility G p y)) hm
  exact Filter.Eventually.of_forall (fun ω => by
    dsimp only [deformedFreshExteriorMoment]
    rw [Real.norm_of_nonneg (mul_nonneg (deformedClusterMass_nonneg G P p k t D ω x)
      (deformedSusceptibility_nonneg G P p k t _ y))]
    exact mul_le_mul_of_nonneg_left (deformedSusceptibility_le G hloc hqt P hP p hp k t ht _ y)
      (deformedClusterMass_nonneg G P p k t D ω x))

end FreshWeightedMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedExposureIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem integral_deformedFreshExteriorMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    (∫ ω, deformedFreshExteriorMoment G P p k t D x y ω ∂law p) =
      ∫ ω, (if ¬Conn G (ω ∩ internalEdges G D) x y then
        deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) ∂law p := by
  rw [integral_induced_cluster_finite_partition G p hp D x _
      (integrable_deformedFreshExteriorMoment G hloc hqt P hP p hp k t ht D x y),
    integral_induced_cluster_finite_partition G p hp D x _
      (integrable_distinct_deformed_product G hloc hqt P hP p hp k t ht D x y)]
  apply tsum_congr
  intro W
  have hl : (∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then
      deformedFreshExteriorMoment G P p k t D x y ω else 0) ∂law p) =
      (∫ ω, (if cluster G (ω ∩ internalEdges G D) x = (W:Set V) then
        deformedClusterMass G P p k t D ω x else 0) ∂law p) *
      deformedSusceptibility G P p k t (D \ (W:Set V)) y := by
    rw [←integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hW : cluster G (ω ∩ internalEdges G D) x = (W:Set V)
      · simp only [hW,ite_true,deformedFreshExteriorMoment]
      · simp only [hW,ite_false,zero_mul])
  rw [hl,←weighted_cluster_cell_exposure G hloc hqt P hP p hp k t ht D W x y]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases hW : cluster G (ω ∩ internalEdges G D) x = (W:Set V)
    · simp only [hW,ite_true]
      rw [deformed_distinct_product_eq_exterior,hW]
    · simp only [hW,ite_false,zero_mul])

end WeightedExposureIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedThreeArmEstimate
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem summable_three_arm_pair (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x a : V) :
    Summable (fun bz : V×V => twoPoint G p x bz.1 * twoPoint G p bz.1 a * twoPoint G p bz.1 bz.2) := by
  apply (summable_twoPoint_pair G hloc hqt p hp x).of_nonneg_of_le
  · exact fun bz => mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _))
      (twoPoint_nonneg G p _ _)
  · intro bz
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (twoPoint_nonneg G p _ _) (twoPoint_le_one G p _ _))
      (twoPoint_nonneg G p _ _)

theorem three_arm_real_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x a z : V) :
    (law p).real {ω | Conn G ω x a ∧ Conn G ω x z} ≤
      ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p b z := by
  have hs := (summable_three_arm_pair G hloc hqt p hp x a).prod_symm.prod_factor z
  have hn (b : V) : 0 ≤ twoPoint G p x b * twoPoint G p b a * twoPoint G p b z :=
    mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_nonneg G p _ _)
  have he : (∑' b, law p {ω | Conn G ω x b} * law p {ω | Conn G ω b a} * law p {ω | Conn G ω b z}) =
      ENNReal.ofReal (∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p b z) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hn hs]
    apply tsum_congr
    intro b
    rw [ENNReal.ofReal_mul (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)),
      ENNReal.ofReal_mul (twoPoint_nonneg G p _ _)]
    simp only [twoPoint,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hh := (three_arm_bound G p x a z).trans_eq he
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (tsum_nonneg hn))

 

theorem integral_size_membership_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x a : V) :
    (∫ ω, (if Conn G ω x a then ((cluster G ω x).ncard:ℝ) else 0) ∂law p) ≤
      maxSusceptibility G p * (∑' b, twoPoint G p x b * twoPoint G p b a) := by
  have he := integral_cluster_size_event G hloc hqt p hp x _ (measurableSet_conn G x a)
  simp only [Set.mem_ofPred_eq] at he
  rw [he]
  have hs := summable_three_arm_pair G hloc hqt p hp x a
  have hl : Summable (fun z => (law p).real {ω | Conn G ω x a ∧ Conn G ω x z}) :=
    (summable_twoPoint_subcritical G hloc hqt p hp x).of_nonneg_of_le (fun _ => measureReal_nonneg)
      (fun _ => measureReal_mono (fun _ h => h.2))
  have hb : Summable (fun b => twoPoint G p x b * twoPoint G p b a) :=
    (summable_twoPoint_subcritical G hloc hqt p hp x).of_nonneg_of_le
      (fun b => mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _))
      (fun b => mul_le_of_le_one_right (twoPoint_nonneg G p _ _) (twoPoint_le_one G p _ _))
  have hj : Summable (fun b => twoPoint G p x b * twoPoint G p b a * susceptibility G p b) := by
    simpa only [tsum_mul_left,susceptibility] using hs.prod
  calc
    _ ≤ ∑' z, ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p b z :=
      hl.tsum_le_tsum (three_arm_real_bound G hloc hqt p hp x a) hs.prod_symm.prod
    _ = ∑' b, ∑' z, twoPoint G p x b * twoPoint G p b a * twoPoint G p b z := hs.tsum_comm
    _ = ∑' b, twoPoint G p x b * twoPoint G p b a * susceptibility G p b := by
      simp only [tsum_mul_left,susceptibility]
    _ ≤ ∑' b, twoPoint G p x b * twoPoint G p b a * maxSusceptibility G p := by
      apply hj.tsum_le_tsum
        (fun b => mul_le_mul_of_nonneg_left (susceptibility_le_max G hloc hqt p hp b)
          (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _))) (hb.mul_right _)
    _ = _ := by rw [tsum_mul_right,mul_comm]

end WeightedThreeArmEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteNeighborhoodMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finset_sum_union_le (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (S T : Finset V) :
    (∑ x ∈ S ∪ T, f x) ≤ (∑ x ∈ S, f x) + ∑ x ∈ T, f x := by
  have he := Finset.sum_union_inter (f := f) (s₁ := S) (s₂ := T)
  have hn := Finset.sum_nonneg (s := S ∩ T) (fun x _ => hf x)
  linarith

theorem finset_sum_biUnion_le (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (W : Finset V) (N : V → Finset V) :
    (∑ z ∈ W.biUnion N, f z) ≤ ∑ a ∈ W, ∑ z ∈ N a, f z := by
  induction W using Finset.induction_on with
  | empty => simp
  | @insert a W ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    exact (finset_sum_union_le f hf _ _).trans (add_le_add (le_refl _) ih)

theorem closedBondNeighborhood_finset (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V) :
    closedBondNeighborhood G (W:Set V) = (W ∪ W.biUnion (neighbors G hloc) : Finset V) := by
  ext z
  simp only [closedBondNeighborhood,Set.mem_ofPred_eq,Finset.mem_coe,Finset.mem_union,Finset.mem_biUnion]
  constructor
  · rintro (hz | ⟨e,hz,a,ha,haW⟩)
    · exact Or.inl hz
    · by_cases hza : a = z
      · exact Or.inl (hza ▸ haW)
      · exact Or.inr ⟨a,haW,(mem_neighbors G hloc a z).mpr
          ⟨e,(Sym2.mem_and_mem_iff hza).mp ⟨ha,hz⟩⟩⟩
  · rintro (hz | ⟨a,ha,haz⟩)
    · exact Or.inl hz
    · obtain ⟨e,he⟩ := (mem_neighbors G hloc a z).mp haz
      exact Or.inr ⟨e,he.symm ▸ Sym2.mem_mk_right a z,a,he.symm ▸ Sym2.mem_mk_left a z,ha⟩

theorem neighborhood_mass_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (W : Finset V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑' z : closedBondNeighborhood G (W:Set V), f z) ≤
      ∑ a ∈ W, (f a + ∑ z ∈ neighbors G hloc a, f z) := by
  rw [closedBondNeighborhood_finset G hloc W,Finset.tsum_subtype']
  exact (finset_sum_union_le f hf _ _).trans
    ((add_le_add (le_refl _) (finset_sum_biUnion_le f hf W (neighbors G hloc))).trans_eq
      (Finset.sum_add_distrib).symm)

end FiniteNeighborhoodMass
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Derivatives
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
open MeasureTheory
section WeightedNeighborhoodEstimate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem twoPoint_neighbor_div_bound [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (v a z : V) (hz : z ∈ neighbors G hloc a) :
    twoPoint G p v z ≤ twoPoint G p v a / (p:ℝ) := by
  obtain ⟨e,he⟩ := (mem_neighbors G hloc a z).mp hz
  have hh := restrictedTwoPoint_adj_lower G Set.univ p a z v e he (Set.mem_univ _)
  simp only [Set.inter_univ] at hh
  change (p:ℝ)*twoPoint G p z v ≤ twoPoint G p a v at hh
  rw [twoPoint_symm G p z v,twoPoint_symm G p a v] at hh
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)

 

theorem neighborhood_twoPoint_bound [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d) (p : unitInterval) (hp : 0 < (p:ℝ))
    (W : Finset V) (v : V) :
    (∑' z : closedBondNeighborhood G (W:Set V), twoPoint G p v z) ≤
      (1+(d:ℝ)/(p:ℝ)) * (∑ a ∈ W, twoPoint G p v a) := by
  apply (neighborhood_mass_le G hloc W (twoPoint G p v) (twoPoint_nonneg G p v)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hsum : (∑ z ∈ neighbors G hloc a, twoPoint G p v z) ≤
      (d:ℝ)*(twoPoint G p v a/(p:ℝ)) := by
    calc
      _ ≤ ∑ _z ∈ neighbors G hloc a, twoPoint G p v a/(p:ℝ) :=
        Finset.sum_le_sum (fun z hz => twoPoint_neighbor_div_bound G hloc p hp v a z hz)
      _ = ((neighbors G hloc a).card:ℝ)*(twoPoint G p v a/(p:ℝ)) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hd a)) (div_nonneg (twoPoint_nonneg G p _ _) hp.le)
  calc
    _ ≤ twoPoint G p v a + (d:ℝ)*(twoPoint G p v a/(p:ℝ)) := add_le_add (le_refl _) hsum
    _ = _ := by ring

end WeightedNeighborhoodEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SizeWeightedPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sizeMembership_nonneg (G : BondGraph V E) (x a : V) (ω : Set E) :
    0 ≤ sizeMembership G x a ω := by
  unfold sizeMembership
  split_ifs
  · exact Nat.cast_nonneg _
  · rfl

theorem sizeMembership_le (G : BondGraph V E) (x a : V) (ω : Set E) :
    sizeMembership G x a ω ≤ ((cluster G ω x).ncard:ℝ) := by
  unfold sizeMembership
  split_ifs
  · rfl
  · exact Nat.cast_nonneg _

theorem measurable_sizeMembership [Countable V] [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (x a : V) : Measurable (sizeMembership G x a) := by
  apply Measurable.ite (measurableSet_conn G x a)
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x)) measurable_const

theorem integrable_sizeMembership [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a : V) : Integrable (sizeMembership G x a) (law p) := by
  apply Integrable.mono' (susceptibility_eq_integral G hloc hqt p hp x).1
    (measurable_sizeMembership G hloc x a).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_of_nonneg (sizeMembership_nonneg G x a ω)]
    exact sizeMembership_le G x a ω)

theorem integral_sizeMembership_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a : V) :
    (∫ ω, sizeMembership G x a ω ∂law p) ≤ susceptibility G p x := by
  rw [(susceptibility_eq_integral G hloc hqt p hp x).2]
  exact integral_mono (integrable_sizeMembership G hloc hqt p hp x a)
    (susceptibility_eq_integral G hloc hqt p hp x).1 (sizeMembership_le G x a)

theorem sizeWeightedConnectionPotential_eq_finite (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) (hf : (cluster G ω x).Finite) :
    sizeWeightedConnectionPotential G p x y ω =
      ((cluster G ω x).ncard:ℝ) * ∑ a ∈ hf.toFinset, twoPoint G p y a := by
  unfold sizeWeightedConnectionPotential
  rw [tsum_eq_sum (s := hf.toFinset)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hc : Conn G ω x a := hf.mem_toFinset.mp ha
    simp only [sizeMembership,ite_eq_left hc]
  · intro a ha
    have hn : ¬Conn G ω x a := fun hc => ha (hf.mem_toFinset.mpr hc)
    simp only [sizeMembership,ite_eq_right hn,zero_mul]

end SizeWeightedPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SizePotentialIntegral
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem summable_sizePotential_integral_norm (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x y : V) :
    Summable (fun a => ∫ ω, ‖sizeMembership G x a ω * twoPoint G p y a‖ ∂law p) := by
  apply ((summable_twoPoint_subcritical G hloc hqt p hp y).mul_left (susceptibility G p x)).of_nonneg_of_le
  · exact fun a => integral_nonneg (fun _ => norm_nonneg _)
  · intro a
    simp only [Real.norm_of_nonneg (mul_nonneg (sizeMembership_nonneg G x a _) (twoPoint_nonneg G p y a)),
      integral_mul_const]
    exact mul_le_mul_of_nonneg_right (integral_sizeMembership_le_susceptibility G hloc hqt p hp x a)
      (twoPoint_nonneg G p y a)

theorem integrable_sizeWeightedConnectionPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (sizeWeightedConnectionPotential G p x y) (law p) := by
  apply Integrable.mono' ((susceptibility_eq_integral G hloc hqt p hp x).1.mul_const
    (susceptibility G p y))
    (Measurable.tsum (fun a => (measurable_sizeMembership G hloc x a).mul_const (twoPoint G p y a))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    have hb (a : V) : sizeMembership G x a ω * twoPoint G p y a ≤
        ((cluster G ω x).ncard:ℝ)*twoPoint G p y a :=
      mul_le_mul_of_nonneg_right (sizeMembership_le G x a ω) (twoPoint_nonneg G p y a)
    have hn (a : V) : 0 ≤ sizeMembership G x a ω * twoPoint G p y a :=
      mul_nonneg (sizeMembership_nonneg G x a ω) (twoPoint_nonneg G p y a)
    have hs := (summable_twoPoint_subcritical G hloc hqt p hp y).mul_left ((cluster G ω x).ncard:ℝ)
    change ‖∑' a, sizeMembership G x a ω * twoPoint G p y a‖ ≤ _
    rw [Real.norm_of_nonneg (tsum_nonneg hn)]
    exact ((hs.of_nonneg_of_le hn hb).tsum_le_tsum hb hs).trans_eq (tsum_mul_left))

theorem summable_twoPoint_cube_pair (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x y : V) :
    Summable (fun ba : V×V => twoPoint G p x ba.1 * twoPoint G p ba.1 ba.2 * twoPoint G p y ba.2) := by
  exact (summable_twoPoint_pair G hloc hqt p hp x).of_nonneg_of_le
    (fun ba => mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _))
      (twoPoint_nonneg G p _ _))
    (fun ba => mul_le_of_le_one_right
      (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_le_one G p _ _))

 
theorem integral_sizeWeightedConnectionPotential_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x y : V) :
    (∫ ω, sizeWeightedConnectionPotential G p x y ω ∂law p) ≤
      maxSusceptibility G p * (∑' a, ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p y a) := by
  have hi (a : V) := (integrable_sizeMembership G hloc hqt p hp x a).mul_const (twoPoint G p y a)
  have hs := summable_sizePotential_integral_norm G hloc hqt p hp x y
  have hc : Summable (fun a => ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p y a) :=
    (summable_twoPoint_cube_pair G hloc hqt p hp x y).prod_symm.prod
  change (∫ ω, ∑' a, sizeMembership G x a ω * twoPoint G p y a ∂law p) ≤ _
  rw [←integral_tsum_of_summable_integral_norm hi hs,←tsum_mul_left]
  have hs' : Summable (fun a => ∫ ω, sizeMembership G x a ω * twoPoint G p y a ∂law p) := by
    simpa only [Real.norm_of_nonneg (mul_nonneg (sizeMembership_nonneg G x _ _) (twoPoint_nonneg G p y _))] using hs
  apply hs'.tsum_le_tsum (fun a => ?_) (hc.mul_left _)
  rw [integral_mul_const,tsum_mul_right]
  calc
    _ ≤ (maxSusceptibility G p * (∑' b, twoPoint G p x b * twoPoint G p b a)) * twoPoint G p y a :=
      mul_le_mul_of_nonneg_right (integral_size_membership_le G hloc hqt p hp x a) (twoPoint_nonneg G p y a)
    _ = _ := mul_assoc _ _ _

end SizePotentialIntegral
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedCorrelationPointwise
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem deformedFreshExteriorMoment_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : p < pc G) (hp₀ : 0 < (p:ℝ)) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (x y : V) (ω : Set E) (hf : (cluster G ω x).Finite) :
    deformedClusterMass G P p k t D ω x * deformedSusceptibility G P p k t D y -
      (1+(d:ℝ)/(p:ℝ))*maxSusceptibility G p * sizeWeightedConnectionPotential G p x y ω ≤
      deformedFreshExteriorMoment G P p k t D x y ω := by
  let A := cluster G (ω ∩ internalEdges G D) x
  have hsub : A ⊆ cluster G ω x := fun _ h => conn_mono G Set.inter_subset_left h
  have hA : A.Finite := hf.subset hsub
  have hn : (∑' z : closedBondNeighborhood G A, twoPoint G p y z) ≤
      (1+(d:ℝ)/(p:ℝ))*(∑ a ∈ hf.toFinset, twoPoint G p y a) := by
    have hh := neighborhood_twoPoint_bound G hloc d hd p hp₀ hA.toFinset y
    rw [hA.coe_toFinset] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg
        (fun a ha => hf.mem_toFinset.mpr (hsub (hA.mem_toFinset.mp ha)))
        (fun a _ _ => twoPoint_nonneg G p y a))
      (add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) hp₀.le)))
  have hm := deformedClusterMass_le_ncard G P hP p k t ht D ω x hf
  have hm₀ := deformedClusterMass_nonneg G P p k t D ω x
  have hχ : 0 ≤ maxSusceptibility G p := zero_le_one.trans (maxSusceptibility_one_le G hloc hqt p hp)
  have hh := mul_le_mul_of_nonneg_left
    (deformedSusceptibility_deletion G hloc hqt P hP p hp k t ht D A y) hm₀
  have hsum : 0 ≤ ∑ a ∈ hf.toFinset, twoPoint G p y a :=
    Finset.sum_nonneg (fun a _ => twoPoint_nonneg G p y a)
  have hC : 0 ≤ 1+(d:ℝ)/(p:ℝ) := add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) hp₀.le)
  have herr : deformedClusterMass G P p k t D ω x *
      (maxSusceptibility G p * (∑' z : closedBondNeighborhood G A, twoPoint G p y z)) ≤
      (1+(d:ℝ)/(p:ℝ))*maxSusceptibility G p * sizeWeightedConnectionPotential G p x y ω := by
    calc
      _ ≤ deformedClusterMass G P p k t D ω x *
          (maxSusceptibility G p * ((1+(d:ℝ)/(p:ℝ))*(∑ a ∈ hf.toFinset, twoPoint G p y a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hχ) hm₀
      _ ≤ ((cluster G ω x).ncard:ℝ)*
          (maxSusceptibility G p * ((1+(d:ℝ)/(p:ℝ))*(∑ a ∈ hf.toFinset, twoPoint G p y a))) :=
        mul_le_mul_of_nonneg_right hm (mul_nonneg hχ (mul_nonneg hC hsum))
      _ = _ := by rw [sizeWeightedConnectionPotential_eq_finite G p x y ω hf]; ring
  dsimp only [deformedFreshExteriorMoment]
  dsimp only [A] at hh
  nlinarith

end WeightedCorrelationPointwise
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedCorrelationIntegral
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem deformed_distinct_correlation (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : p < pc G) (hp₀ : 0 < (p:ℝ)) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (x y : V) :
    deformedSusceptibility G P p k t D x * deformedSusceptibility G P p k t D y -
      (1+(d:ℝ)/(p:ℝ))*(maxSusceptibility G p)^2 *
        (∑' a, ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p y a) ≤
      ∫ ω, (if ¬Conn G (ω ∩ internalEdges G D) x y then
        deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) ∂law p := by
  rw [←integral_deformedFreshExteriorMoment G hloc hqt P hP p hp k t ht D x y]
  have hi := integrable_deformedClusterMass G hloc hqt P hP p hp k t ht D x
  have hj := integrable_sizeWeightedConnectionPotential G hloc hqt p hp x y
  have hb := integral_mono_ae
    ((hi.mul_const (deformedSusceptibility G P p k t D y)).sub
      (hj.const_mul ((1+(d:ℝ)/(p:ℝ))*maxSusceptibility G p)))
    (integrable_deformedFreshExteriorMoment G hloc hqt P hP p hp k t ht D x y)
    (by
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      exact deformedFreshExteriorMoment_lower G hloc hqt d hd P hP p hp hp₀ k t ht D x y ω hω)
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (hi.mul_const _) (hj.const_mul _),integral_mul_const,integral_const_mul,
    ←deformedSusceptibility_eq_integral G hloc hqt P hP p hp k t ht D x] at hb
  have hC : 0 ≤ (1+(d:ℝ)/(p:ℝ))*maxSusceptibility G p :=
    mul_nonneg (add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) hp₀.le))
      (zero_le_one.trans (maxSusceptibility_one_le G hloc hqt p hp))
  have herr := mul_le_mul_of_nonneg_left
    (integral_sizeWeightedConnectionPotential_le G hloc hqt p hp x y) hC
  nlinarith

end WeightedCorrelationIntegral
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExactCubeKernel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem HasKernel.square_real_kernel (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    (∑' b, twoPoint G p x b * twoPoint G p b y) = (matrixCoeff (T^2) x y).re := by
  have hh := ((hT.positiveRealMatrix G p T).mul_hasSum T x y).tsum_eq
  simpa only [hT.matrixCoeff_re G p T,pow_two] using hh

theorem HasKernel.cube_real_kernel (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    (∑' a, ∑' b, twoPoint G p x b * twoPoint G p b a * twoPoint G p y a) =
      (matrixCoeff (T^3) x y).re := by
  have hh := (((hT.positiveRealMatrix G p T).pow 2).mul_hasSum T x y).tsum_eq
  calc
    _ = ∑' a, (matrixCoeff (T^2) x a).re * (matrixCoeff T a y).re := by
      apply tsum_congr
      intro a
      rw [tsum_mul_right,hT.square_real_kernel G p T x a,hT.matrixCoeff_re G p T a y,twoPoint_symm G p y a]
    _ = _ := by simpa only [show T^2*T = T^3 by rw [←pow_succ]] using hh

end ExactCubeKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformWeightedCorrelation
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem deformed_distinct_correlation_uniform (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    deformedSusceptibility G P p k t D x * deformedSusceptibility G P p k t D y -
      (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 * (matrixCoeff (T^3) x y).re ≤
      ∫ ω, (if ¬Conn G (ω ∩ internalEdges G D) x y then
        deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) ∂law p := by
  have hp₀ : 0 < (p:ℝ) := (half_pos hpcrit).trans_le hpnear
  have hb := deformed_distinct_correlation G hloc hqt d hd P hP p hp hp₀ k t ht D x y
  rw [hT.cube_real_kernel G p T x y] at hb
  have hc : (d:ℝ)/(p:ℝ) ≤ 2*(d:ℝ)/(pc G:ℝ) := by
    apply (div_le_div_iff₀ hp₀ hpcrit).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have he := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1:ℝ)) hc)
    (mul_nonneg (sq_nonneg (maxSusceptibility G p)) (((hT.positiveRealMatrix G p T).pow 3) x y).2)
  nlinarith

end UniformWeightedCorrelation
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkFiniteBases
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem base_mem_reachBall_of_retained (w : RawCorridor G k) (e : E)
    (he : e ∈ w.retained) (z : V) (hz : z ∈ G e) : w.base ∈ reachBall G z k := by
  have hs : z ∈ w.path.support := SimpleGraph.Walk.mem_support_of_mem_edges he hz
  let q := (w.path.takeUntil z hs).reverse
  have hq : q.length ≤ k := by
    change (w.path.takeUntil z hs).reverse.length ≤ k
    rw [SimpleGraph.Walk.length_reverse]
    exact (w.path.length_takeUntil_le_length hs).trans w.path_length
  have hh := walk_mem_reachBall G Set.univ (x := z) q 0 (by simp only [reachBall,Set.mem_singleton_iff])
  simp only [Nat.zero_add] at hh
  exact reachBall_mono_local G z hq hh

end RawCorridor
end RawWalkFiniteBases
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformPenaltyDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_raw_selection (G : BondGraph V E) (hloc : LocallyFinite G)
    (k : ℕ) (S : Set V) (hS : S.Finite) (Q : RawCorridor G k → Prop)
    (hQ : ∀ w, Q w → w.base ∈ S) (f : RawCorridor G k → ℝ) :
    Summable (fun w => if Q w then f w else 0) := by
  apply summable_of_hasFiniteSupport
  apply (finite_corridors_on_bases G hloc k S hS).subset
  intro w hw
  by_contra hn
  exact hw (ite_eq_right (fun h => hn (hQ w h)))

end UniformPenaltyDomination
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalMovePenalty
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_raw_edge_weights (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (e : E) :
    Summable (fun w : RawCorridor G k => if e ∈ w.retained then w.weight P p else 0) := by
  obtain ⟨z,z',hzz⟩ : ∃ z z', G e = s(z,z') := by
    obtain ⟨⟨z,z'⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨z,z',hh.symm⟩
  have he : z ∈ G e := hzz.symm ▸ Sym2.mem_mk_left z z'
  exact summable_raw_selection G hloc k (reachBall G z k) (finite_reachBall hloc z k)
    (fun w => e ∈ w.retained) (fun w hw => w.base_mem_reachBall_of_retained e hw z he)
    (fun w => w.weight P p)



end TerminalMovePenalty
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Calibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PivotalLegGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pivotal_endpoint_connected (G : BondGraph V E) (S : Set E) (x y : V)
    (hc : Conn G S x y) (e : E) (hp : ¬Conn G (S \ {e}) x y) (z : V) (hz : z ∈ G e) :
    Conn G S x z := by
  obtain ⟨q⟩ := (conn_iff_reachable G S x y).mp hc
  have hzs : z ∈ q.support := SimpleGraph.Walk.mem_support_of_mem_edges
    (pivotal_image_mem_edges G S q e hp) hz
  exact (conn_iff_reachable G S x z).mpr ⟨q.takeUntil z hzs⟩

theorem conn_delete_of_unconnected_endpoint (G : BondGraph V E) (S : Set E) (x y z : V)
    (hc : Conn G S x y) (e : E) (hz : z ∈ G e) (hn : ¬Conn G S x z) :
    Conn G (S \ {e}) x y := by
  by_contra hh
  exact hn (pivotal_endpoint_connected G S x y hc e hh z hz)

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem retained_conn_base (w : RawCorridor G k) (z : V) (hz : z ∈ w.path.support) :
    Conn G w.retained w.base z := by
  obtain ⟨l,hl,hm,_⟩ := walk_lift_bonds G Set.univ (w.path.takeUntil z hz)
  apply hl.conn
  intro e he
  exact w.path.edges_takeUntil_subset_edges hz (hm ▸ List.mem_map_of_mem he)

theorem retained_conn (w : RawCorridor G k) : Conn G w.retained w.base w.endpoint :=
  w.retained_conn_base w.endpoint w.path.end_mem_support

theorem retained_connects_support (w : RawCorridor G k) (x y : V)
    (hx : x ∈ w.path.support) (hy : y ∈ w.path.support) : Conn G w.retained x y :=
  conn_trans G _ (conn_symm G _ (w.retained_conn_base x hx)) (w.retained_conn_base y hy)

theorem retained_nonempty (w : RawCorridor G k) (hl : 0 < w.path.length) : w.retained.Nonempty := by
  have hp : w.path.edges ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [SimpleGraph.Walk.length_edges,List.length_nil] at hh
    omega
  obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hp
  obtain ⟨e,he,_⟩ := w.edge_has_label s hs
  exact ⟨e,he⟩

end RawCorridor
end PivotalLegGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OneLegGeometry
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_one_leg (r : RawCorridor G k) (D : Set V) (ω B : Set E)
    (x y u v : V) (hc : r.counted Set.univ ω x y)
    (hr : r.retained ⊆ ω ∩ internalEdges G D) (hB : B ⊆ ω)
    (hd : Disjoint B r.retained) (huv : Conn G B u v)
    (hxu : Conn G (ω ∩ internalEdges G D) x u)
    (hvy : Conn G (ω ∩ internalEdges G D) v y)
    (hne : ¬Conn G (ω ∩ internalEdges G D) u v)
    (e : E) (he : e ∈ r.retained)
    (hep : ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x u) : r.counted D ω x u := by
  let S := ω ∩ internalEdges G D
  have huniv : ω ∩ internalEdges G Set.univ = ω := by
    apply Set.Subset.antisymm Set.inter_subset_left
    exact fun _ he => ⟨he,fun _ _ => trivial⟩
  obtain ⟨z,z',hzz⟩ : ∃ z z', G e = s(z,z') := by
    obtain ⟨⟨z,z'⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨z,z',hh.symm⟩
  have hz : z ∈ G e := hzz.symm ▸ Sym2.mem_mk_left z z'
  have hxz : Conn G S x z := pivotal_endpoint_connected G S x u hxu e hep z hz
  have hzsupport : z ∈ r.path.support := SimpleGraph.Walk.mem_support_of_mem_edges he hz
  apply (r.counted_iff D ω x u).mpr
  refine ⟨hc.1,hxu,?_,hc.2.2.2.2.mono_right ?_⟩
  · intro f hf
    refine ⟨hr hf,?_⟩
    intro hxf
    obtain ⟨a,b,hab⟩ : ∃ a b, G f = s(a,b) := by
      obtain ⟨⟨a,b⟩,hh⟩ := Quot.exists_rep (G f)
      exact ⟨a,b,hh.symm⟩
    have ha : a ∈ G f := hab.symm ▸ Sym2.mem_mk_left a b
    have haz : Conn G S z a := conn_mono G hr (r.retained_connects_support z a hzsupport
      (SimpleGraph.Walk.mem_support_of_mem_edges hf ha))
    have hua : Conn G S u a := conn_trans G S (conn_symm G S hxu) (conn_trans G S hxz haz)
    have hvf : Conn G (S \ {f}) v y := conn_delete_of_unconnected_endpoint G S v y a hvy f ha
      (fun hva => hne (conn_trans G S hua (conn_symm G S hva)))
    have hBf : Conn G (ω \ {f}) u v := conn_mono G (show B ⊆ ω \ {f} from fun g hg => ⟨hB hg,fun hgf =>
      Set.disjoint_left.mp hd hg ((Set.mem_singleton_iff.mp hgf).symm ▸ hf)⟩) huv
    apply (hc.2.2.2.1 f hf).2
    rw [huniv]
    exact conn_trans G _ (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) hxf)
      (conn_trans G _ hBf (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) hvf))
  · rw [huniv]
    exact Set.inter_subset_left

end RawCorridor
end OneLegGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TwoLegGeometry
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem counted_split_legs (r : RawCorridor G k) (D : Set V) (ω B : Set E)
    (x y u v : V) (hc : r.counted Set.univ ω x y)
    (hr : r.retained ⊆ ω ∩ internalEdges G D) (hB : B ⊆ ω)
    (hd : Disjoint B r.retained) (huv : Conn G B u v)
    (hxu : Conn G (ω ∩ internalEdges G D) x u)
    (hvy : Conn G (ω ∩ internalEdges G D) v y)
    (hne : ¬Conn G (ω ∩ internalEdges G D) u v) :
    r.counted D ω x u ∨ r.counted D ω v y := by
  obtain ⟨e,he⟩ := r.retained_nonempty (by have := hc.1; omega)
  by_cases hp : ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x u
  · exact Or.inl (r.counted_one_leg D ω B x y u v hc hr hB hd huv hxu hvy hne e he hp)
  · have hxu' : Conn G ((ω ∩ internalEdges G D) \ {e}) x u := not_not.mp hp
    have hp' : ¬Conn G ((ω ∩ internalEdges G D) \ {e}) y v := by
      intro hyv
      apply (hc.2.2.2.1 e he).2
      have huniv : ω ∩ internalEdges G Set.univ = ω := by
        apply Set.Subset.antisymm Set.inter_subset_left
        exact fun _ he => ⟨he,fun _ _ => trivial⟩
      rw [huniv]
      have hB' : Conn G (ω \ {e}) u v := conn_mono G (show B ⊆ ω \ {e} from fun f hf => ⟨hB hf,fun hfe =>
        Set.disjoint_left.mp hd hf ((Set.mem_singleton_iff.mp hfe).symm ▸ he)⟩) huv
      exact conn_trans G _ (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) hxu')
        (conn_trans G _ hB' (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) (conn_symm G _ hyv)))
    exact Or.inr ((r.counted_symm D ω y v).mp (r.counted_one_leg D ω B y x v u
      ((r.counted_symm Set.univ ω x y).mp hc) hr hB hd (conn_symm G B huv)
      (conn_symm G _ hvy) (conn_symm G _ hxu) (fun h => hne (conn_symm G _ h)) e he hp'))

 
theorem counted_legs_of_disjoint (w r : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base)
    (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint)
    (hc : r.counted Set.univ ω x y) (hd : Disjoint w.retained r.retained) :
    r.counted (w.interior : Set V)ᶜ ω x w.base ∨ r.counted (w.interior : Set V)ᶜ ω w.endpoint y := by
  apply r.counted_split_legs (w.interior : Set V)ᶜ ω w.retained x y w.base w.endpoint
    hc ?_ hq.1 hd w.retained_conn hxu hvy hne
  intro e he
  have heω := (hc.2.2.2.1 e he).1.1
  exact (w.open_subset_exterior_retained ω hq heω).resolve_right
    (fun hw => Set.disjoint_left.mp hd hw he)

end RawCorridor
end TwoLegGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TwoLegPenaltyTerms
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenaltyTerm_legs (G : BondGraph V E) (hG : Function.Injective G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    (w r : RawCorridor G k) (ω : Set E) (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base) (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint) :
    corridorPenaltyTerm G P p Set.univ ω x y r ≤
      (∑ e ∈ (w.retained_finite hG).toFinset, if e ∈ r.retained then r.weight P p else 0) +
        corridorPenaltyTerm G P p (w.interior : Set V)ᶜ ω x w.base r +
        corridorPenaltyTerm G P p (w.interior : Set V)ᶜ ω w.endpoint y r := by
  have hr := r.weight_nonneg P hP p
  have hs : 0 ≤ ∑ e ∈ (w.retained_finite hG).toFinset, if e ∈ r.retained then r.weight P p else 0 :=
    Finset.sum_nonneg (fun _ _ => ite_nonneg hr (le_refl _))
  have hl := corridorPenaltyTerm_nonneg G P hP p (w.interior : Set V)ᶜ ω x w.base r
  have ht := corridorPenaltyTerm_nonneg G P hP p (w.interior : Set V)ᶜ ω w.endpoint y r
  by_cases hc : r.counted Set.univ ω x y
  · rw [corridorPenaltyTerm,ite_eq_left hc]
    by_cases hd : Disjoint w.retained r.retained
    · rcases w.counted_legs_of_disjoint r ω hq x y hxu hvy hne hc hd with hh | hh
      · have he : corridorPenaltyTerm G P p (w.interior : Set V)ᶜ ω x w.base r = r.weight P p := ite_eq_left hh
        linarith
      · have he : corridorPenaltyTerm G P p (w.interior : Set V)ᶜ ω w.endpoint y r = r.weight P p := ite_eq_left hh
        linarith
    · obtain ⟨e,hew,her⟩ := Set.not_disjoint_iff.mp hd
      have he := Finset.single_le_sum (f := fun e => if e ∈ r.retained then r.weight P p else 0)
        (s := (w.retained_finite hG).toFinset) (fun _ _ => ite_nonneg hr (le_refl _))
        ((w.retained_finite hG).mem_toFinset.mpr hew)
      rw [ite_eq_left her] at he
      linarith
  · rw [corridorPenaltyTerm,ite_eq_right hc]
    linarith

 

theorem corridorPenalty_legs (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base) (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint) :
    corridorPenalty G P p k Set.univ ω x y ≤
      (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) +
      corridorPenalty G P p k (w.interior : Set V)ᶜ ω x w.base +
      corridorPenalty G P p k (w.interior : Set V)ᶜ ω w.endpoint y := by
  have hs : Summable (fun r : RawCorridor G k => ∑ e ∈ (w.retained_finite hG).toFinset,
      if e ∈ r.retained then r.weight P p else 0) :=
    (hasSum_sum (fun e (_ : e ∈ (w.retained_finite hG).toFinset) =>
      (summable_raw_edge_weights G hloc P p k e).hasSum)).summable
  have hl := corridorPenalty_summable G hloc P p k (w.interior : Set V)ᶜ ω x w.base
  have hr := corridorPenalty_summable G hloc P p k (w.interior : Set V)ᶜ ω w.endpoint y
  have hh := (corridorPenalty_summable G hloc P p k Set.univ ω x y).tsum_le_tsum
    (fun r => corridorPenaltyTerm_legs G hG P hP p k w r ω hq x y hxu hvy hne) ((hs.add hl).add hr)
  rw [(hs.add hl).tsum_add hr,hs.tsum_add hl,
    Summable.tsum_finsetSum (fun e _ => summable_raw_edge_weights G hloc P p k e)] at hh
  exact hh

end TwoLegPenaltyTerms
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedLegComparison
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}
theorem base_not_interior (w : RawCorridor G k) : w.base ∉ w.interior := by
  simp only [interior,Finset.mem_sdiff,Finset.mem_insert,true_or,not_true_eq_false,and_false,not_false_eq_true]
theorem endpoint_not_interior (w : RawCorridor G k) : w.endpoint ∉ w.interior := by
  simp only [interior,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,or_true,not_true_eq_false,and_false,not_false_eq_true]
end RawCorridor

 
theorem deformedConnection_legs_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base) (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint) (c : ℝ)
    (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t*c) * deformedConnection G P p k t (w.interior : Set V)ᶜ ω x w.base *
      deformedConnection G P p k t (w.interior : Set V)ᶜ ω w.endpoint y ≤
        deformedConnection G P p k t Set.univ ω x y := by
  have hx : x ∈ (w.interior : Set V)ᶜ := by
    rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hxu with h | h
    · rw [h]; exact w.base_not_interior
    · exact h.1
  have hy : y ∈ (w.interior : Set V)ᶜ := by
    rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hvy with h | h
    · rw [←h]; exact w.endpoint_not_interior
    · exact h.2
  have hxy : Conn G (ω ∩ internalEdges G Set.univ) x y := by
    apply conn_mono G (show ω ⊆ ω ∩ internalEdges G Set.univ from fun _ h => ⟨h,fun _ _ => trivial⟩)
    exact conn_trans G ω (conn_mono G Set.inter_subset_left hxu)
      (conn_trans G ω (conn_mono G hq.1 w.retained_conn) (conn_mono G Set.inter_subset_left hvy))
  have hleft : x ∈ (w.interior : Set V)ᶜ ∧ w.base ∈ (w.interior : Set V)ᶜ ∧
      Conn G (ω ∩ internalEdges G (w.interior : Set V)ᶜ) x w.base := ⟨hx,w.base_not_interior,hxu⟩
  have hright : w.endpoint ∈ (w.interior : Set V)ᶜ ∧ y ∈ (w.interior : Set V)ᶜ ∧
      Conn G (ω ∩ internalEdges G (w.interior : Set V)ᶜ) w.endpoint y := ⟨w.endpoint_not_interior,hy,hvy⟩
  simp only [deformedConnection,ite_eq_left hleft,ite_eq_left hright,Set.mem_univ,hxy,and_self,ite_true]
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := (corridorPenalty_legs G hG hloc P hP p k w ω hq x y hxu hvy hne).trans
    (add_le_add (add_le_add hc le_rfl) le_rfl)
  simpa only [mul_add] using mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr ht)

end WeightedLegComparison
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SimplePathCuts
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem simplePath_edge_cut {H : SimpleGraph V} {u v : V} (q : H.Walk u v)
    (hq : q.IsPath) (e : Sym2 V) (he : e ∈ q.edges) :
    ∃ A : Set V, u ∈ A ∧ v ∉ A ∧ (∀ z ∈ A, z ∈ q.support) ∧
      ∀ f ∈ q.edges, f ≠ e → ∀ a ∈ f, ∀ b ∈ f, a ∈ A ↔ b ∈ A := by
  induction q with
  | nil => simp only [SimpleGraph.Walk.edges_nil,List.not_mem_nil] at he
  | @cons u a v h q ih =>
    have hu : u ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hq).2
    have huv : v ≠ u := fun hvu => hu (hvu ▸ q.end_mem_support)
    by_cases hh : e = s(u,a)
    · refine ⟨{u},rfl,huv,?_,?_⟩
      · intro z hz; rw [Set.mem_singleton_iff] at hz; subst z; simp
      · intro f hf hfe x hx y hy
        have hfq : f ∈ q.edges := (List.mem_cons.mp hf).resolve_left (fun h' => hfe (h'.trans hh.symm))
        have hxu : x ≠ u := fun hxu => hu (hxu ▸ SimpleGraph.Walk.mem_support_of_mem_edges hfq hx)
        have hyu : y ≠ u := fun hyu => hu (hyu ▸ SimpleGraph.Walk.mem_support_of_mem_edges hfq hy)
        simp only [Set.mem_singleton_iff,hxu,hyu]
    · have heq : e ∈ q.edges := (List.mem_cons.mp he).resolve_left hh
      obtain ⟨A,ha,hv,hA,hcut⟩ := ih hq.of_cons heq
      refine ⟨insert u A,Set.mem_insert u A,?_,?_,?_⟩
      · intro hvA
        rcases hvA with h' | h'
        · exact huv h'
        · exact hv h'
      · intro z hz
        rcases hz with rfl | hz
        · simp
        · exact List.mem_cons_of_mem u (hA z hz)
      · intro f hf hfe x hx y hy
        rcases List.mem_cons.mp hf with rfl | hf
        · have hx' : x = u ∨ x = a := by simpa only [SimpleGraph.Dart.edge,Sym2.mem_iff] using hx
          have hy' : y = u ∨ y = a := by simpa only [SimpleGraph.Dart.edge,Sym2.mem_iff] using hy
          have hxm : x ∈ insert u A := hx'.elim (fun h' => h' ▸ Set.mem_insert u A)
            (fun h' => h' ▸ Set.mem_insert_of_mem u ha)
          have hym : y ∈ insert u A := hy'.elim (fun h' => h' ▸ Set.mem_insert u A)
            (fun h' => h' ▸ Set.mem_insert_of_mem u ha)
          exact iff_of_true hxm hym
        · have hxu : x ≠ u := fun hxu => hu (hxu ▸ SimpleGraph.Walk.mem_support_of_mem_edges hf hx)
          have hyu : y ≠ u := fun hyu => hu (hyu ▸ SimpleGraph.Walk.mem_support_of_mem_edges hf hy)
          simpa only [Set.mem_insert_iff,hxu,hyu,false_or] using hcut f hf hfe x hx y hy

theorem conn_closed_vertex_set (G : BondGraph V E) (S : Set E) (A : Set V)
    (hA : ∀ e ∈ S, ∀ a ∈ G e, ∀ b ∈ G e, a ∈ A → b ∈ A)
    {x y : V} (hc : Conn G S x y) (hx : x ∈ A) : y ∈ A := by
  induction hc with
  | refl => exact hx
  | @tail a b _ hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact hA e he a (heq.symm ▸ Sym2.mem_mk_left a b) b (heq.symm ▸ Sym2.mem_mk_right a b) ih

end SimplePathCuts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CalibratedCut
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conn_edge_members (G : BondGraph V E) (S : Set E) (e : E) (he : e ∈ S)
    (a b : V) (ha : a ∈ G e) (hb : b ∈ G e) : Conn G S a b := by
  obtain ⟨x,y,hxy⟩ : ∃ x y, G e = s(x,y) := by
    obtain ⟨⟨x,y⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨x,y,hh.symm⟩
  rw [hxy,Sym2.mem_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact conn_refl G S _
  · exact Relation.ReflTransGen.single ⟨e,he,hxy⟩
  · exact conn_symm G S (Relation.ReflTransGen.single ⟨e,he,hxy⟩)
  · exact conn_refl G S _

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem calibration_pivotal_ports (hG : Function.Injective G) (w : RawCorridor G k)
    (ω : Set E) (hq : ω ∈ w.calibrationEvent)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint)
    (e : E) (he : e ∈ w.retained) : ¬Conn G (ω \ {e}) w.base w.endpoint := by
  obtain ⟨A,hu,hv,hA,hcut⟩ := simplePath_edge_cut w.path w.path_isPath (G e) he
  let B := A ∪ {z | Conn G (w.exterior ω) w.base z}
  have hAport (z : V) (hz : z ∈ A) (ho : z ∉ w.interior) : z = w.base := by
    rcases w.support_exterior_ports (hA z hz) ho with h | h
    · exact h
    · exact (hv (h ▸ hz)).elim
  have hConnOut (z : V) (hz : Conn G (w.exterior ω) w.base z) : z ∉ w.interior := by
    rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hz with h | h
    · rw [←h]; exact w.base_not_interior
    · exact h.2
  have hBclosed : ∀ f ∈ ω \ {e}, ∀ a ∈ G f, ∀ b ∈ G f, a ∈ B → b ∈ B := by
    intro f hf a ha b hb hba
    rcases w.open_subset_exterior_retained ω hq hf.1 with hfs | hfr
    · have hab := conn_edge_members G (w.exterior ω) f hfs a b ha hb
      rcases hba with haa | hua
      · have hau : a = w.base := hAport a haa (hfs.2 a ha)
        exact Or.inr (hau ▸ hab)
      · exact Or.inr (conn_trans G _ hua hab)
    · have hfe : G f ≠ G e := fun h => hf.2 (hG h)
      have haa : a ∈ A := by
        rcases hba with h | h
        · exact h
        · rcases w.support_exterior_ports (SimpleGraph.Walk.mem_support_of_mem_edges hfr ha)
            (hConnOut a h) with hau | hav
          · exact hau ▸ hu
          · exact (hne (hav ▸ h)).elim
      exact Or.inl ((hcut (G f) hfr hfe a ha b hb).mp haa)
  intro hc
  have hh := conn_closed_vertex_set G (ω \ {e}) B hBclosed hc (Or.inl hu)
  exact hh.elim hv hne

end RawCorridor
end CalibratedCut
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ReverseCalibration
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem calibration_counted_of_orientation (hG : Function.Injective G) (w : RawCorridor G k)
    (hlen : 3 ≤ w.path.length) (ω : Set E) (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base) (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint) : w.counted Set.univ ω x y := by
  have huniv : ω ∩ internalEdges G Set.univ = ω := by
    apply Set.Subset.antisymm Set.inter_subset_left
    exact fun _ he => ⟨he,fun _ _ => trivial⟩
  apply (w.counted_iff Set.univ ω x y).mpr
  refine ⟨hlen,?_⟩
  unfold corridorCounted
  rw [huniv]
  refine ⟨conn_trans G ω (conn_mono G Set.inter_subset_left hxu)
    (conn_trans G ω (conn_mono G hq.1 w.retained_conn) (conn_mono G Set.inter_subset_left hvy)),?_,hq.2⟩
  intro e he
  refine ⟨hq.1 he,?_⟩
  intro hxy
  have hS : w.exterior ω ⊆ ω \ {e} := by
    intro f hf
    refine ⟨hf.1,?_⟩
    intro hfe
    have hfe' : f = e := hfe
    subst f
    exact Set.disjoint_left.mp (w.specified_disjoint_exterior hlen) (Or.inl he) hf.2
  exact w.calibration_pivotal_ports hG ω hq hne e he
    (conn_trans G _ (conn_mono G hS (conn_symm G _ hxu))
      (conn_trans G _ hxy (conn_mono G hS (conn_symm G _ hvy))))



end RawCorridor
end ReverseCalibration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorLegObservable
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_restrict_config (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t D (ω ∩ internalEdges G D) x y =
      deformedConnection G P p k t D ω x y := by
  have he : (ω ∩ internalEdges G D) ∩ internalEdges G D = ω ∩ internalEdges G D :=
    Set.inter_assoc _ _ _ |>.trans (congrArg (ω ∩ ·) (Set.inter_self _))
  have hc (w : RawCorridor G k) : w.counted D (ω ∩ internalEdges G D) x y ↔ w.counted D ω x y := by
    simp only [RawCorridor.counted,corridorCounted,he]
  simp only [deformedConnection,corridorPenalty,corridorPenaltyTerm,hc,he]

theorem exteriorLegProduct_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E) (x y : V) :
    0 ≤ exteriorLegProduct G P p t w ω x y := by
  unfold exteriorLegProduct
  by_cases h : ¬Conn G (w.exterior ω) w.base w.endpoint
  · rw [ite_eq_left h]
    exact mul_nonneg (deformedConnection_nonneg _ _ _ _ _ _ _ _ _)
      (deformedConnection_nonneg _ _ _ _ _ _ _ _ _)
  · rw [ite_eq_right h]

theorem exteriorLegProduct_le_one (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) {k : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (w : RawCorridor G k) (ω : Set E) (x y : V) :
    exteriorLegProduct G P p t w ω x y ≤ 1 := by
  unfold exteriorLegProduct
  by_cases h : ¬Conn G (w.exterior ω) w.base w.endpoint
  · rw [ite_eq_left h]
    exact (mul_le_of_le_one_left (deformedConnection_nonneg _ _ _ _ _ _ _ _ _)
      (deformedConnection_le_one G P hP p k t ht _ _ _ _)).trans
      (deformedConnection_le_one G P hP p k t ht _ _ _ _)
  · rw [ite_eq_right h]
    exact zero_le_one

theorem measurable_exteriorLegProduct [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ) {k : ℕ} (t : ℝ)
    (w : RawCorridor G k) (x y : V) :
    Measurable (fun ω => exteriorLegProduct G P p t w ω x y) := by
  apply Measurable.ite
    ((measurableSet_restrictedConn G (internalEdges G (w.interior:Set V)ᶜ) w.base w.endpoint).compl)
  · exact (measurable_deformedConnection G P p k t _ x w.base).mul
      (measurable_deformedConnection G P p k t _ w.endpoint y)
  · exact measurable_const

theorem exteriorLegProduct_restrict (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E) (x y : V) :
    exteriorLegProduct G P p t w ω x y =
      exteriorLegProduct G P p t w (ω ∩ internalEdges G (w.interior:Set V)ᶜ) x y := by
  simp only [exteriorLegProduct,RawCorridor.exterior,Set.inter_assoc,Set.inter_self,
    deformedConnection_restrict_config]
  rfl

end ExteriorLegObservable
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CalibrationFactor
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem measurableSet_calibration (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) : MeasurableSet w.calibrationEvent := by
  rw [w.calibrationEvent_eq hG hloc]
  apply measurableSet_edgePattern
  apply Finset.disjoint_left.mpr
  intro e he hb
  exact Set.disjoint_left.mp w.retained_disjoint_blockers
    ((w.retained_finite hG).mem_toFinset.mp he) ((w.blockers_finite hloc).mem_toFinset.mp hb)

 

theorem calibration_integral (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) (p : unitInterval)
    (f : Set E → ℝ) (hf : Measurable f)
    (hfr : ∀ ω, f ω = f (ω ∩ internalEdges G (w.interior:Set V)ᶜ)) :
    (∫ ω, if ω ∈ w.calibrationEvent then f ω else 0 ∂law p) =
      (law p).real w.calibrationEvent * ∫ ω, f ω ∂law p := by
  have hh := integral_mul_disjoint_coordinates p _ _ (w.specified_disjoint_exterior hlen)
    (fun ω => if ω ∈ w.calibrationEvent then (1:ℝ) else 0) f
    (Measurable.ite (w.measurableSet_calibration hG hloc) measurable_const measurable_const) hf
    (fun ω => by rw [w.calibration_restriction ω]) hfr
  simpa only [ite_mul,one_mul,zero_mul,integral_event_indicator p _ (w.measurableSet_calibration hG hloc)] using hh

theorem calibration_weighted_integral (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) (P : V → V → ℝ)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1)
    (f : Set E → ℝ) (hf : Measurable f)
    (hfr : ∀ ω, f ω = f (ω ∩ internalEdges G (w.interior:Set V)ᶜ)) :
    (∫ ω, if ω ∈ w.calibrationEvent then w.weight P p * f ω else 0 ∂law p) =
      w.probability P * ∫ ω, f ω ∂law p := by
  have he : (fun ω => if ω ∈ w.calibrationEvent then w.weight P p * f ω else 0) =
      (fun ω => w.weight P p * (if ω ∈ w.calibrationEvent then f ω else 0)) := by
    funext ω
    by_cases h : ω ∈ w.calibrationEvent <;> simp only [h,ite_true,ite_false,mul_zero]
  rw [he,integral_const_mul,w.calibration_integral hG hloc hlen p f hf hfr,
    ←mul_assoc,w.calibration_identity hG hloc P p hp hp₁]

end RawCorridor
end CalibrationFactor
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CalibratedDerivativeTerm
attribute [local instance] Classical.propDecidable Classical.decEq

theorem calibrated_leg_product_le_term (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) (ω : Set E) (x y : V) :
    (if ω ∈ w.calibrationEvent then w.weight P p * (Real.exp (-t*c) *
      exteriorLegProduct G P p t w ω x y) else 0) ≤
        corridorPenaltyTerm G P p Set.univ ω x y w * deformedConnection G P p k t Set.univ ω x y := by
  have hr : 0 ≤ corridorPenaltyTerm G P p Set.univ ω x y w * deformedConnection G P p k t Set.univ ω x y :=
    mul_nonneg (corridorPenaltyTerm_nonneg G P hP p Set.univ ω x y w)
      (deformedConnection_nonneg G P p k t Set.univ ω x y)
  by_cases hq : ω ∈ w.calibrationEvent
  · rw [ite_eq_left hq]
    by_cases hn : ¬Conn G (w.exterior ω) w.base w.endpoint
    · rw [exteriorLegProduct,ite_eq_left hn]
      by_cases hx : Conn G (w.exterior ω) x w.base
      · by_cases hy : Conn G (w.exterior ω) w.endpoint y
        · have hj := w.calibration_counted_of_orientation hG hlen ω hq x y hx hy hn
          rw [corridorPenaltyTerm,ite_eq_left hj]
          have hh := mul_le_mul_of_nonneg_left
            (deformedConnection_legs_lower G hG hloc P hP p k w ω hq x y hx hy hn c hc t ht)
            (w.weight_nonneg P hP p)
          simpa only [mul_assoc] using hh
        · have hz : deformedConnection G P p k t (w.interior:Set V)ᶜ ω w.endpoint y = 0 := by
            simp only [deformedConnection,show ¬Conn G (ω ∩ internalEdges G (w.interior:Set V)ᶜ) w.endpoint y from hy,and_false,ite_false]
          simpa only [hz,mul_zero] using hr
      · have hz : deformedConnection G P p k t (w.interior:Set V)ᶜ ω x w.base = 0 := by
          simp only [deformedConnection,show ¬Conn G (ω ∩ internalEdges G (w.interior:Set V)ᶜ) x w.base from hx,and_false,ite_false]
        simpa only [hz,zero_mul,mul_zero] using hr
    · simpa only [exteriorLegProduct,ite_eq_right hn,mul_zero] using hr
  · simpa only [ite_eq_right hq] using hr

theorem integrable_corridorDerivativeTerm [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V)
    (w : RawCorridor G k) :
    Integrable (fun ω => corridorPenaltyTerm G P p D ω x y w *
      deformedConnection G P p k t D ω x y) (law p) := by
  have hh := ((integrable_deformedConnection G P hP p k t ht D x y).const_mul
    (w.weight P p)).indicator (w.measurableSet_counted D x y)
  have he : (fun ω => corridorPenaltyTerm G P p D ω x y w *
      deformedConnection G P p k t D ω x y) =
      {ω | w.counted D ω x y}.indicator (fun ω => w.weight P p * deformedConnection G P p k t D ω x y) := by
    funext ω
    simp only [Set.indicator,Set.mem_ofPred_eq,corridorPenaltyTerm,ite_mul,zero_mul]
  rw [he]
  exact hh

end CalibratedDerivativeTerm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CalibratedDecreaseKernel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_exteriorLegProduct [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : RawCorridor G k) (x y : V) :
    Integrable (fun ω => exteriorLegProduct G P p t w ω x y) (law p) := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (measurable_exteriorLegProduct G P p t w x y).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_of_nonneg (exteriorLegProduct_nonneg G P p t w ω x y)]
  exact exteriorLegProduct_le_one G P hP p t ht w ω x y

 

theorem calibrated_derivative_kernel_lower [Countable V] [Countable E]
    (G : BondGraph V E) (hG : Function.Injective G) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1)
    (k : ℕ) (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) (x y : V) :
    w.probability P * Real.exp (-t*c) * (∫ ω, exteriorLegProduct G P p t w ω x y ∂law p) ≤
      ∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
        deformedConnection G P p k t Set.univ ω x y ∂law p := by
  have hf := integrable_exteriorLegProduct G P hP p t ht w x y
  have hi : Integrable (fun ω => if ω ∈ w.calibrationEvent then w.weight P p *
      (Real.exp (-t*c) * exteriorLegProduct G P p t w ω x y) else 0) (law p) :=
    ((hf.const_mul (Real.exp (-t*c))).const_mul (w.weight P p)).indicator
      (w.measurableSet_calibration hG hloc)
  have hh := integral_mono hi (integrable_corridorDerivativeTerm G P hP p k t ht Set.univ x y w)
    (fun ω => calibrated_leg_product_le_term G hG hloc P hP p k w hlen c hc t ht ω x y)
  rw [w.calibration_weighted_integral hG hloc hlen P p hp hp₁
    (fun ω => Real.exp (-t*c)*exteriorLegProduct G P p t w ω x y)
    ((measurable_exteriorLegProduct G P p t w x y).const_mul _)
    (fun ω => congrArg (Real.exp (-t*c)*·) (exteriorLegProduct_restrict G P p t w ω x y)),
    integral_const_mul] at hh
  simpa only [mul_assoc] using hh

end CalibratedDecreaseKernel
end Percolation

 
namespace Percolation
open MeasureTheory
section NonnegativeRealTonelli
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem real_tonelli_of_integrable_sum {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (F : I → Ω → ℝ) (hF : ∀ i, Integrable (F i) μ)
    (hn : ∀ i ω, 0 ≤ F i ω) (hs : ∀ᵐ ω ∂μ, Summable (fun i => F i ω))
    (hi : Integrable (fun ω => ∑' i, F i ω) μ) :
    Summable (fun i => ∫ ω, F i ω ∂μ) ∧
      (∑' i, ∫ ω, F i ω ∂μ) = ∫ ω, ∑' i, F i ω ∂μ := by
  have he : (∑' i, ENNReal.ofReal (∫ ω, F i ω ∂μ)) =
      ∫⁻ ω, ENNReal.ofReal (∑' i, F i ω) ∂μ := by
    simp_rw [ofReal_integral_eq_lintegral_ofReal (hF _) (Filter.Eventually.of_forall (hn _))]
    rw [←lintegral_tsum (fun i => (hF i).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    apply lintegral_congr_ae
    filter_upwards [hs] with ω hω
    exact (ENNReal.ofReal_tsum_of_nonneg (fun i => hn i ω) hω).symm
  have ht : (∑' i, ENNReal.ofReal (∫ ω, F i ω ∂μ)) ≠ ⊤ := by
    rw [he,←ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun i => hn i ω)))]
    exact ENNReal.ofReal_ne_top
  have hh : Summable (fun i => ∫ ω, F i ω ∂μ) := by
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hn _))] using ENNReal.summable_toReal ht
  refine ⟨hh,?_⟩
  apply integral_tsum_of_summable_integral_norm hF
  simpa only [Real.norm_of_nonneg (hn _ _)] using hh

end NonnegativeRealTonelli
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TotalExteriorLegs
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exteriorLegProduct_sum (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E)
    (hu : (cluster G ω w.base).Finite) (hv : (cluster G ω w.endpoint).Finite) :
    Summable (fun xy : V × V => exteriorLegProduct G P p t w ω xy.1 xy.2) ∧
    (∑' xy : V × V, exteriorLegProduct G P p t w ω xy.1 xy.2) =
      if ¬Conn G (w.exterior ω) w.base w.endpoint then
        deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.base *
          deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.endpoint else 0 := by
  by_cases hn : ¬Conn G (w.exterior ω) w.base w.endpoint
  · have hsu : Summable (deformedConnection G P p k t (w.interior:Set V)ᶜ ω w.base) :=
      summable_of_hasFiniteSupport (deformedConnection_finite_support G P p k t (w.interior:Set V)ᶜ ω w.base hu)
    have hsv : Summable (deformedConnection G P p k t (w.interior:Set V)ᶜ ω w.endpoint) :=
      summable_of_hasFiniteSupport (deformedConnection_finite_support G P p k t (w.interior:Set V)ᶜ ω w.endpoint hv)
    have hsx : Summable (fun x => deformedConnection G P p k t (w.interior:Set V)ᶜ ω x w.base) := by
      simpa only [deformedConnection_symm G P p k t (w.interior:Set V)ᶜ ω _ w.base] using hsu
    have hs := hsx.mul_of_nonneg hsv
      (fun x => deformedConnection_nonneg G P p k t _ ω x w.base)
      (fun y => deformedConnection_nonneg G P p k t _ ω w.endpoint y)
    simp only [exteriorLegProduct,ite_eq_left hn]
    refine ⟨hs,?_⟩
    rw [←hsx.tsum_mul_tsum hsv hs]
    simp only [deformedClusterMass,deformedConnection_symm G P p k t (w.interior:Set V)ᶜ ω _ w.base]
  · simp only [exteriorLegProduct,ite_eq_right hn,summable_zero,tsum_zero,and_self]

 

theorem exteriorLegProduct_integral_sum [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : RawCorridor G k) :
    Summable (fun xy : V × V => ∫ ω, exteriorLegProduct G P p t w ω xy.1 xy.2 ∂law p) ∧
    (∑' xy : V × V, ∫ ω, exteriorLegProduct G P p t w ω xy.1 xy.2 ∂law p) =
      ∫ ω, (if ¬Conn G (w.exterior ω) w.base w.endpoint then
        deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.base *
          deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.endpoint else 0) ∂law p := by
  have hae : ∀ᵐ ω ∂law p, Summable (fun xy : V × V => exteriorLegProduct G P p t w ω xy.1 xy.2) ∧
    (∑' xy : V × V, exteriorLegProduct G P p t w ω xy.1 xy.2) =
      if ¬Conn G (w.exterior ω) w.base w.endpoint then
        deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.base *
          deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.endpoint else 0 := by
    filter_upwards [subcritical_cluster_finite_ae G p hp w.base,
      subcritical_cluster_finite_ae G p hp w.endpoint] with ω hu hv
    exact exteriorLegProduct_sum G P p t w ω hu hv
  have hi := (integrable_distinct_deformed_product G hloc hqt P hP p hp k t ht
    (w.interior:Set V)ᶜ w.base w.endpoint).congr (hae.mono (fun _ h => h.2.symm))
  obtain ⟨hs,he⟩ := real_tonelli_of_integrable_sum (law p)
    (fun xy : V × V => fun ω => exteriorLegProduct G P p t w ω xy.1 xy.2)
    (fun xy => integrable_exteriorLegProduct G P hP p t ht w xy.1 xy.2)
    (fun xy ω => exteriorLegProduct_nonneg G P p t w ω xy.1 xy.2)
    (hae.mono (fun _ h => h.1)) hi
  exact ⟨hs,he.trans (integral_congr_ae (hae.mono (fun _ h => h.2)))⟩

end TotalExteriorLegs
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SummableDerivativeTerm
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

omit [Nonempty V] in
theorem integral_corridorDerivativeTerm_le (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : RawCorridor G k) (x y : V) :
    (∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
      deformedConnection G P p k t Set.univ ω x y ∂law p) ≤
      w.probability P * (twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y) := by
  apply le_trans (integral_mono (integrable_corridorDerivativeTerm G P hP p k t ht Set.univ x y w)
    (integrable_corridorPenaltyTerm G P p Set.univ x y w) (fun ω =>
      mul_le_of_le_one_right (corridorPenaltyTerm_nonneg G P hP p Set.univ ω x y w)
        (deformedConnection_le_one G P hP p k t ht Set.univ ω x y)))
  exact integral_corridorPenaltyTerm_le G hG hloc P hP p hp0 hp1 x y w

theorem summable_twoPoint_pairs (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (p : unitInterval)
    (hp : p < pc G) (u v : V) :
    Summable (fun xy : V × V => twoPoint G p xy.1 u * twoPoint G p v xy.2) := by
  have hs : Summable (fun x => twoPoint G p x u) := by
    simpa only [twoPoint_symm G p _ u] using summable_twoPoint_subcritical G hloc hqt p hp u
  exact hs.mul_of_nonneg (summable_twoPoint_subcritical G hloc hqt p hp v)
    (fun x => twoPoint_nonneg G p x u) (fun y => twoPoint_nonneg G p v y)

omit [Nonempty V] [Countable V] [Countable E] in
 theorem integral_corridorDerivativeTerm_nonneg (G : BondGraph V E)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    (t : ℝ) (w : RawCorridor G k) (x y : V) :
    0 ≤ ∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
      deformedConnection G P p k t Set.univ ω x y ∂law p :=
  integral_nonneg (fun ω => mul_nonneg (corridorPenaltyTerm_nonneg G P hP p Set.univ ω x y w)
    (deformedConnection_nonneg G P p k t Set.univ ω x y))

theorem summable_corridorDerivativeTerm_pairs (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : RawCorridor G k) :
    Summable (fun xy : V × V => ∫ ω, corridorPenaltyTerm G P p Set.univ ω xy.1 xy.2 w *
      deformedConnection G P p k t Set.univ ω xy.1 xy.2 ∂law p) := by
  have hs : Summable (fun xy : V × V => w.probability P *
      (twoPoint G p xy.1 w.base * twoPoint G p w.endpoint xy.2 +
       twoPoint G p xy.1 w.endpoint * twoPoint G p w.base xy.2)) :=
    ((summable_twoPoint_pairs G hloc hqt p hp w.base w.endpoint).add
      (summable_twoPoint_pairs G hloc hqt p hp w.endpoint w.base)).mul_left (w.probability P)
  exact Summable.of_nonneg_of_le
    (fun (xy : V × V) => integral_corridorDerivativeTerm_nonneg G P hP p k t w xy.1 xy.2)
    (fun (xy : V × V) => integral_corridorDerivativeTerm_le G hG hloc P hP p hp0
      ((show (p:ℝ)<(pc G:ℝ) from hp).trans_le (pc G).2.2) t ht w xy.1 xy.2) hs

end SummableDerivativeTerm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SingleTemplateDecrease
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem calibrated_derivative_template_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (k : ℕ) (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    w.probability P * Real.exp (-t*c) *
      (∫ ω, (if ¬Conn G (w.exterior ω) w.base w.endpoint then
        deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.base *
          deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.endpoint else 0) ∂law p) ≤
      ∑' xy : V × V, ∫ ω, corridorPenaltyTerm G P p Set.univ ω xy.1 xy.2 w *
        deformedConnection G P p k t Set.univ ω xy.1 xy.2 ∂law p := by
  obtain ⟨hs,he⟩ := exteriorLegProduct_integral_sum G hloc hqt P hP p hp t ht w
  have hh := (hs.mul_left (w.probability P * Real.exp (-t*c))).tsum_le_tsum
    (fun (xy : V × V) => calibrated_derivative_kernel_lower G hG hloc P hP p hp0
      ((show (p:ℝ)<(pc G:ℝ) from hp).trans_le (pc G).2.2) k w hlen c hc t ht xy.1 xy.2)
    (summable_corridorDerivativeTerm_pairs G hG hloc hqt P hP p hp0 hp t ht w)
  rwa [tsum_mul_left,he] at hh

 

theorem calibrated_derivative_template_row_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    w.probability P * Real.exp (-t*c) *
      (deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.base *
        deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.endpoint -
        (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2*(matrixCoeff (T^3) w.base w.endpoint).re) ≤
      ∑' xy : V × V, ∫ ω, corridorPenaltyTerm G P p Set.univ ω xy.1 xy.2 w *
        deformedConnection G P p k t Set.univ ω xy.1 xy.2 ∂law p := by
  have hm := deformed_distinct_correlation_uniform G hloc hqt d hd P hP hpcrit p hp hpnear T hT
    k t ht (w.interior:Set V)ᶜ w.base w.endpoint
  exact (mul_le_mul_of_nonneg_left hm (mul_nonneg (w.2.2.mass_nonneg P hP) (Real.exp_pos _).le)).trans
    (calibrated_derivative_template_lower G hG hloc hqt P hP p ((half_pos hpcrit).trans_le hpnear)
      hp k w hlen c hc t ht)

end SingleTemplateDecrease
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_AveragedDecrease
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorDerivativeContribution_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (x y : V) :
    0 ≤ corridorDerivativeContribution G P p t w x y :=
  integral_corridorDerivativeTerm_nonneg G P hP p k t w x y

end DeformationCovariance
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedCalibratedDecrease
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

theorem raw_derivative_template_row_lower_oai (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (w : RawCorridor G k)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t*c) * (w.probability P *
      (retainedSusceptibilityProduct G P p t w -
        (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2*(matrixCoeff (T^3) w.base w.endpoint).re)) ≤
      ∑' xy : V × V, corridorDerivativeContribution G P p t w xy.1 xy.2 := by
  by_cases hlen : 3 ≤ w.path.length
  · have hh := calibrated_derivative_template_row_lower G hG hloc hqt d
      (fun x => (neighbors_card_le_degree G hloc x).trans (hd x)) P hP hpcrit p hp hpnear T hT k w hlen c hc t ht
    simpa only [retainedSusceptibilityProduct,hlen,ite_true,corridorDerivativeContribution,
      mul_assoc,mul_left_comm (Real.exp (-t*c))] using hh
  · have hC : 0 ≤ 1+2*(d:ℝ)/(pc G:ℝ) := by positivity
    have hA := (((hT.positiveRealMatrix G p T).pow 3) w.base w.endpoint).2
    have hpr := w.2.2.mass_nonneg P hP
    have hr : 0 ≤ ∑' xy : V × V, corridorDerivativeContribution G P p t w xy.1 xy.2 :=
      tsum_nonneg (fun xy => corridorDerivativeContribution_nonneg G P hP p t w xy.1 xy.2)
    apply le_trans _ hr
    simp only [retainedSusceptibilityProduct,hlen,ite_false,zero_sub,mul_neg]
    exact neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le (mul_nonneg hpr
      (mul_nonneg (mul_nonneg hC (sq_nonneg _)) hA)))


end AveragedCalibratedDecrease
end Percolation


end OAI
end

theorem solution.{u, v} : type_of% @OAI.Percolation.raw_derivative_template_row_lower_oai.{u, v} := @OAI.Percolation.raw_derivative_template_row_lower_oai.{u, v}
