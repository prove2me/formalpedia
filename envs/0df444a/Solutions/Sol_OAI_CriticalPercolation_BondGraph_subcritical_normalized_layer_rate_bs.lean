-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:55:40.99061+00:00
-- url     : https://prove2.me/submissions/32c3bbbd-a0e1-4852-ad35-4a44efedb58d

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Paths
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SubcriticalMoments
attribute [local instance] Classical.propDecidable Classical.decEq


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

lemma adjustedLayerIndex_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R u : ℝ) (x y z : V) :
    G.adjustedLayerIndex a R u x z = G.adjustedLayerIndex a R u x y+
      G.adjustedLayerIndex a R (G.orbitAdjustedHeight a x y/R+u) y z := by
  unfold adjustedLayerIndex
  rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
  have he : (G.orbitAdjustedHeight a x y+G.orbitAdjustedHeight a y z)/R+u =
      G.orbitAdjustedHeight a y z/R+(G.orbitAdjustedHeight a x y/R+u) := by ring
  rw [he]
  ring

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

lemma adjustedUpLayerMoment_zero_ge_one [Countable V] [Countable E]
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (x : V) (u : ℝ) :
    1 ≤ G.adjustedUpLayerMoment a R p 0 x u := by
  have hh (ω : Set E) : (1 : ℝ≥0∞) ≤ restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ (0 : ℤ)})
      {v | G.adjustedLayerIndex a R u x v = (0 : ℤ)} ω x := by
    apply le_trans _ (ENNReal.le_tsum x)
    simp only [G.adjustedLayerIndex_self,Set.mem_ofPred_eq,
      Percolation.conn_refl,true_and,if_true,le_refl]
  exact (show (1 : ℝ≥0∞) = ∫⁻ _ω : Set E, (1 : ℝ≥0∞) ∂G.law p by simp).le.trans
    (lintegral_mono hh)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFirstMomentPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma integer_first_layer_walk {V : Type*} {H : SimpleGraph V}
    (f : V → ℤ) (hjump : ∀ {v w}, H.Adj v w → f w ≤ f v+1 ∧ f v ≤ f w+1)
    {x y : V} (p : H.Walk x y) (m : ℤ) (hx : f x < m) (hy : m ≤ f y) :
    ∃ z, f z=m ∧ ∃ q : H.Walk x z, q.length ≤ p.length ∧
      ∀ v ∈ q.support, f v ≤ m := by
  let S := p.support.toFinset.filter fun v => m ≤ f v
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support,hy⟩
  obtain ⟨z,hzS,hzp,hfirst⟩ := p.exists_mem_support_forall_mem_support_imp_eq S
    ⟨y,Finset.mem_filter.mpr ⟨hyS,p.end_mem_support⟩⟩
  have hz : m ≤ f z := (Finset.mem_filter.mp hzS).2
  have hbelow (v : V) (hv : v ∈ (p.takeUntil z hzp).support) (hvz : v ≠ z) : f v < m := by
    by_contra hn
    have hvS : v ∈ S := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (p.support_takeUntil_subset_support hzp hv),le_of_not_gt hn⟩
    exact hvz (hfirst v hvS hv)
  have hj {v w : V} (hvw : H.Adj v w) : |(f w : ℝ)-(f v : ℝ)| ≤ 1 := by
    obtain ⟨h₁,h₂⟩ := hjump hvw
    have h₁' : (f w : ℝ) ≤ (f v : ℝ)+1 := by exact_mod_cast h₁
    have h₂' : (f v : ℝ) ≤ (f w : ℝ)+1 := by exact_mod_cast h₂
    rw [abs_le]
    constructor <;> linarith
  have hx' : (f x : ℝ) < (m : ℝ)-1/2 := by
    have hh : f x ≤ m-1 := by omega
    have hh' : (f x : ℝ) ≤ (m : ℝ)-1 := by exact_mod_cast hh
    linarith
  have hbl : ∀ v ∈ (p.takeUntil z hzp).support, v ≠ z → (f v : ℝ) < (m : ℝ)-1/2 := by
    intro v hv hvz
    have hh : f v ≤ m-1 := by have := hbelow v hv hvz; omega
    have hh' : (f v : ℝ) ≤ (m : ℝ)-1 := by exact_mod_cast hh
    linarith
  have hzhi := walk_endpoint_height_bound (fun v => (f v : ℝ)) 1 ((m : ℝ)-1/2)
    (by norm_num) hj (p.takeUntil z hzp) hx' hbl
  have hzm : f z=m := by
    have hh : f z ≤ m := (integer_half_ceiling _ _).mp hzhi
    omega
  refine ⟨z,hzm,p.takeUntil z hzp,p.length_takeUntil_le_length hzp,fun v hv => ?_⟩
  by_cases hvz : v=z
  · simp only [hvz,hzm,le_refl]
  · exact (hbelow v hv hvz).le

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] in
lemma adjustedUpLayerMoment_walk_lower (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R u : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (n : ℕ) (hn : 0 < n) {x y : V}
    (w : G.fullGraph.Walk x y) (hy : (n : ℤ) ≤ G.adjustedLayerIndex a R u x y) :
    ENNReal.ofReal ((p : ℝ)^w.length) ≤ G.adjustedUpLayerMoment a R p n x u := by
  let f := G.adjustedLayerIndex a R u x
  have hj {v z : V} (hvz : G.fullGraph.Adj v z) : f z ≤ f v+1 ∧ f v ≤ f z+1 := by
    obtain ⟨⟨e,_he,heq⟩,_hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvz
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R u hR hjump x v z e
      (by rw [heq]; simp) (by rw [heq]; simp)
    change f v-1 ≤ f z ∧ f z ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by simp only [f,G.adjustedLayerIndex_self]; exact_mod_cast hn
  obtain ⟨z,hz,q,hqlen,hq⟩ := integer_first_layer_walk f hj w n hx hy
  have hg : G.fullGraph = Percolation.openSimpleGraph G.ends Set.univ :=
    criticalModel_openGraph G.ends Set.univ
  let ι : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by simpa only [←hg,id_eq] using h⟩
  obtain ⟨s,hs,hconn⟩ := walk_finite_open_restriction G.ends (q.map ι)
    {v | f v ≤ (n : ℤ)} (by
      intro v hv
      rw [SimpleGraph.Walk.support_map] at hv
      change v ∈ q.support.map id at hv
      exact hq v (by simpa only [List.map_id_fun,id_eq] using hv))
  have hslen0 : s.card ≤ q.length := by simpa only [SimpleGraph.Walk.length_map] using hs
  have hslen : s.card ≤ w.length := hslen0.trans hqlen
  let F : Set (Set E) := {ω | (s : Set E) ⊆ ω}
  have hF : MeasurableSet F := Percolation.measurableSet_finiteWitness F
    (fun _ _ h hs => hs.trans h) (fun _ hs => ⟨s,hs,Set.Subset.rfl⟩)
  have hmeasure : G.law p F = ENNReal.ofReal ((p : ℝ)^s.card) := by
    rw [←Percolation.finite_open_probability p s]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  calc
    _ ≤ ENNReal.ofReal ((p : ℝ)^s.card) := ENNReal.ofReal_le_ofReal
      (pow_le_pow_of_le_one p.2.1 p.2.2 hslen)
    _ = G.law p F := hmeasure.symm
    _ = ∫⁻ ω, F.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂G.law p :=
      (lintegral_indicator_one hF).symm
    _ ≤ _ := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ F
      · rw [Set.indicator_of_mem hω]
        apply le_trans _ (ENNReal.le_tsum z)
        exact (ite_eq_left ⟨hz,hconn ω hω⟩).symm.le
      · rw [Set.indicator_of_notMem hω]
        exact bot_le

theorem adjustedUpLayerMoment_finite_energy [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ) (hu : ¬G.CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (n : ℕ) (x : V) (u : ℝ),
      ENNReal.ofReal ((p : ℝ)^(A*n+B)) ≤
        G.adjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n x u := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpath⟩ := G.stationaryOrbitHeight_orbit_above hc hl hq μ hμ hstat hu
  refine ⟨A*R,A*R+B,mul_pos hA hR,add_nonneg (mul_pos hA hR).le hB,fun n x u => ?_⟩
  by_cases hn : n=0
  · subst n
    have hb : (p : ℝ)^(A*R+B) ≤ 1 := Real.rpow_le_one p.2.1 p.2.2 (add_nonneg (mul_pos hA hR).le hB)
    have hz := G.adjustedUpLayerMoment_zero_ge_one a R p x u
    rw [←ENNReal.ofReal_one] at hz
    simpa only [Nat.cast_zero,mul_zero,zero_add,a] using
      (ENNReal.ofReal_le_ofReal hb).trans hz
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨y,w,_horb,hlen,_hlow,hy⟩ := hpath (((n : ℝ)+1)*R)
    (mul_nonneg (by positivity) hR.le) x (G.vertexOrbit x)
  have hend : (n : ℤ) ≤ G.adjustedLayerIndex a R u x y := by
    have hh := (G.adjustedLayerIndex_height_bounds a R u hR x y).2
    by_contra hf
    have hi : G.adjustedLayerIndex a R u x y ≤ (n : ℤ)-1 := by omega
    have hir : (G.adjustedLayerIndex a R u x y : ℝ) ≤ (n : ℝ)-1 := by exact_mod_cast hi
    nlinarith
  have hlen' : (w.length : ℝ) ≤ A*R*(n : ℝ)+(A*R+B) := by nlinarith [hlen]
  have hpow := Real.rpow_le_rpow_of_exponent_ge hp p.2.2 hlen'
  rw [Real.rpow_natCast] at hpow
  exact (ENNReal.ofReal_le_ofReal hpow).trans
    (G.adjustedUpLayerMoment_walk_lower hc hl a R u hR hjump p n hnpos w hend)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFirstMomentSubmultiplicative
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma adjustedUpLayerMoment_first_visit (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (m n : ℕ) (hm : 0 < m) (x : V) (u : ℝ) :
    G.adjustedUpLayerMoment a R p (m+n) x u ≤
      G.adjustedUpLayerMoment a R p m x u * G.supAdjustedUpLayerMoment a R p n := by
  let f := G.adjustedLayerIndex a R u x
  let I := Percolation.internalEdges G.ends {v | f v ≤ (m+n : ℕ)}
  let A := {v | f v = (m+n : ℕ)}
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R u hR hjump x v w e hv hw
    change f v-1 ≤ f w ∧ f w ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (m : ℤ) := by simp only [f,G.adjustedLayerIndex_self]; exact_mod_cast hm
  have hA : ∀ y ∈ A, (m : ℤ) ≤ f y := by
    intro y hy
    change f y = (m+n : ℕ) at hy
    rw [hy]
    exact_mod_cast Nat.le_add_right m n
  have hfirst := integer_first_layer_moment_bound G.ends f hj I A p x m hx hA
  have hI : I ∩ Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)} =
      Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)} := by
    apply Set.inter_eq_right.mpr
    apply Percolation.internalEdges_mono G.ends
    intro v hv
    change f v ≤ (m : ℤ) at hv
    change f v ≤ (m+n : ℕ)
    exact hv.trans (by exact_mod_cast Nat.le_add_right m n)
  rw [hI] at hfirst
  have hcont (z : V) (hz : f z=(m : ℤ)) :
      (∫⁻ ω, restrictedLayerCount G.ends I A ω z ∂G.law p) ≤ G.supAdjustedUpLayerMoment a R p n := by
    let v := G.orbitAdjustedHeight a x z/R+u
    have hidx (y : V) : f y = (m : ℤ)+G.adjustedLayerIndex a R v z y := by
      simpa only [f,hz] using G.adjustedLayerIndex_change_base hc hl a R u x z y
    have hDom : {y : V | f y ≤ (m+n : ℕ)} =
        {y | G.adjustedLayerIndex a R v z y ≤ (n : ℤ)} := by
      ext y
      change f y ≤ (m+n : ℕ) ↔ G.adjustedLayerIndex a R v z y ≤ (n : ℤ)
      rw [hidx]
      push_cast
      omega
    have hTar : A = {y | G.adjustedLayerIndex a R v z y=(n : ℤ)} := by
      ext y
      change f y = (m+n : ℕ) ↔ G.adjustedLayerIndex a R v z y=(n : ℤ)
      rw [hidx]
      push_cast
      omega
    change (∫⁻ ω, restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {y | f y ≤ (m+n : ℕ)}) A ω z ∂G.law p) ≤ _
    rw [hDom,hTar]
    exact G.adjustedUpLayerMoment_le_sup a R p n z v
  calc
    _ ≤ ∑' z, (if f z=(m : ℤ) then G.law p
        {ω | Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)}) x z} else 0) *
          (∫⁻ ω, restrictedLayerCount G.ends I A ω z ∂G.law p) := hfirst
    _ ≤ ∑' z, (if f z=(m : ℤ) then G.law p
        {ω | Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)}) x z} else 0) *
          G.supAdjustedUpLayerMoment a R p n := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z=(m : ℤ)
      · exact mul_le_mul' le_rfl (hcont z hz)
      · simp only [ite_eq_right hz,zero_mul,le_refl]
    _ = _ := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      rw [adjustedUpLayerMoment]
      change _ = ∫⁻ ω, restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)}) {v | f v=(m : ℤ)} ω x ∂Percolation.law p
      rw [lintegral_restrictedLayerCount]
      apply tsum_congr
      intro z
      by_cases hz : f z=(m : ℤ) <;>
        simp only [Set.mem_ofPred_eq,hz,if_true,if_false,law,Percolation.law]

theorem supAdjustedUpLayerMoment_submultiplicative [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (m n : ℕ) :
    G.supAdjustedUpLayerMoment a R p (m+n) ≤
      G.supAdjustedUpLayerMoment a R p m*G.supAdjustedUpLayerMoment a R p n := by
  have hzero : (1 : ℝ≥0∞) ≤ G.supAdjustedUpLayerMoment a R p 0 :=
    (G.adjustedUpLayerMoment_zero_ge_one a R p (Classical.arbitrary V) 0).trans
      (G.adjustedUpLayerMoment_le_sup a R p 0 _ 0)
  by_cases hm : m=0
  · rw [hm,zero_add]
    exact (one_mul _).symm.le.trans (mul_le_mul' hzero le_rfl)
  · apply iSup_le
    intro x
    apply iSup_le
    intro u
    exact (G.adjustedUpLayerMoment_first_visit hc hl a R hR hjump p m n
      (Nat.pos_of_ne_zero hm) x u).trans (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p m x u) le_rfl)

theorem subcritical_supAdjustedUpLayerMoment_bound [Nonempty V]
    (hl : Percolation.LocallyFinite G.ends) (hq : Percolation.QuasiTransitive G.ends)
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (hp : p < Percolation.pc G.ends) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, G.supAdjustedUpLayerMoment a R p n ≤ C := by
  obtain ⟨C,_hC,hrow⟩ := Percolation.subcritical_ennreal_row_bound G.ends hl hq p hp
  refine ⟨ENNReal.ofReal C,ENNReal.ofReal_lt_top,fun n => ?_⟩
  apply iSup_le
  intro x
  apply iSup_le
  intro u
  apply le_trans _ (hrow x)
  rw [adjustedUpLayerMoment]
  change (∫⁻ ω, restrictedLayerCount G.ends _ _ ω x ∂Percolation.law p) ≤ _
  rw [lintegral_restrictedLayerCount]
  apply ENNReal.tsum_le_tsum
  intro y
  split_ifs
  · exact measure_mono (fun ω hω => Percolation.conn_mono G.ends Set.inter_subset_left hω)
  · exact bot_le

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerMomentFekete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology

namespace Percolation.BenjaminiSchramm

theorem positive_layer_moment_rate (P : ℕ → ℝ) (hP : ∀ n, 0 < P n)
    (hP0 : 1 ≤ P 0) (hmul : ∀ m n, P (m+n) ≤ P m*P n)
    (C : ℝ) (hbound : ∀ n, P n ≤ C)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlower : ∀ n : ℕ, Real.exp (-A*n-B) ≤ P n) :
    ∃ β : ℝ, 0 ≤ β ∧
      (∀ n : ℕ, Real.exp (-β*n) ≤ P n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
        P n ≤ K*Real.exp (-(β-ε)*n)) ∧
      Tendsto (fun n : ℕ => -Real.log (P n)/n) atTop (𝓝 β) := by
  let u : ℕ → ℝ := fun n => Real.log (P n)
  have hu : Subadditive u := by
    intro m n
    have hh := Real.log_le_log (hP (m+n)) (hmul m n)
    rw [Real.log_mul (hP m).ne' (hP n).ne'] at hh
    exact hh
  have hlo (n : ℕ) : -A*n-B ≤ u n := by
    have hh := Real.log_le_log (Real.exp_pos _) (hlower n)
    rwa [Real.log_exp] at hh
  have hbdd : BddBelow (Set.range fun n : ℕ => u n/n) := by
    refine ⟨-A-B,?_⟩
    rintro _ ⟨n,rfl⟩
    by_cases hn : n=0
    · simp only [hn,Nat.cast_zero,div_zero]
      linarith
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      apply (le_div_iff₀ hnpos).mpr
      nlinarith [hlo n]
  let β := -hu.lim
  have hlim0 : Tendsto (fun n : ℕ => u n/n) atTop (𝓝 hu.lim) := hu.tendsto_lim hbdd
  have hlim : Tendsto (fun n : ℕ => -Real.log (P n)/n) atTop (𝓝 β) := by
    simpa only [neg_div,u] using hlim0.neg
  have hlog (n : ℕ) : u n ≤ Real.log C := Real.log_le_log (hP n) (hbound n)
  have hzero : Tendsto (fun n : ℕ => Real.log C/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlimle : hu.lim ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlim0 hzero
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (hlog n) (Nat.cast_nonneg n)
  have hβ : 0 ≤ β := neg_nonneg.mpr hlimle
  refine ⟨β,hβ,?_,?_,hlim⟩
  · intro n
    by_cases hn : n=0
    · simpa only [hn,Nat.cast_zero,mul_zero,Real.exp_zero] using hP0
    have hr := (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn) : (0 : ℝ) < n)).mp
      (hu.lim_le_div hbdd hn)
    have hh : -β*(n : ℝ) ≤ Real.log (P n) := by simpa only [β,u,neg_neg] using hr
    have he := Real.exp_le_exp.mpr hh
    rwa [Real.exp_log (hP n)] at he
  · intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp
      (hlim.eventually (lt_mem_nhds (sub_lt_self β hε)))
    let f : ℕ → ℝ := fun n => P n*Real.exp ((β-ε)*n)
    obtain ⟨i,hi,himax⟩ := Finset.exists_max_image (Finset.range (N+1)) f
      ⟨0,Finset.mem_range.mpr (Nat.succ_pos N)⟩
    let K := max 1 (f i)
    refine ⟨K,lt_of_lt_of_le (by norm_num) (le_max_left _ _),fun n => ?_⟩
    by_cases hn : n < N+1
    · have hK : f n ≤ K := (himax n (Finset.mem_range.mpr hn)).trans (le_max_right _ _)
      have hh := mul_le_mul_of_nonneg_right hK (Real.exp_pos (-(β-ε)*n)).le
      have he : Real.exp ((β-ε)*n)*Real.exp (-(β-ε)*n)=1 := by
        rw [←Real.exp_add]
        ring_nf
        exact Real.exp_zero
      dsimp [f] at hh
      rwa [mul_assoc,he,mul_one] at hh
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hh := (lt_div_iff₀ hnpos).mp (hN n (by omega))
      have he := Real.exp_le_exp.mpr (show Real.log (P n) ≤ -(β-ε)*(n : ℝ) by linarith)
      rw [Real.exp_log (hP n)] at he
      exact he.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _))

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFirstMomentRate
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
variable {V E : Type*} [Countable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype G.VertexOrbit]

theorem subcritical_normalized_layer_rate_bs_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hql : Percolation.QuasiTransitive G.ends)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ) (hu : ¬G.CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < Percolation.pc G.ends) :
    ∃ β : ℝ, 0 ≤ β ∧
      (∀ n : ℕ, Real.exp (-β*n) ≤
        (G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n).toReal) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
        G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n ≤
          ENNReal.ofReal (K*Real.exp (-(β-ε)*n))) ∧
      Tendsto (fun n : ℕ => -Real.log
        (G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n).toReal/n) atTop (𝓝 β) := by
  let a := G.stationaryOrbitWeight μ
  let S := G.supAdjustedUpLayerMoment a R p
  let P : ℕ → ℝ := fun n => (S n).toReal
  obtain ⟨C,hC,hbound⟩ := G.subcritical_supAdjustedUpLayerMoment_bound hl hql a R p hpc
  have hne (n : ℕ) : S n ≠ ⊤ := (lt_of_le_of_lt (hbound n) hC).ne
  obtain ⟨A,B,hA,hB,hlower⟩ := G.adjustedUpLayerMoment_finite_energy hc hl hq μ hμ hstat hu R hR hjump p hp
  have hlow (n : ℕ) : (p : ℝ)^(A*n+B) ≤ P n := by
    have hh := ENNReal.toReal_mono (hne n)
      ((hlower n (Classical.arbitrary V) 0).trans (G.adjustedUpLayerMoment_le_sup a R p n _ 0))
    rwa [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hp _).le] at hh
  have hP (n : ℕ) : 0 < P n := (Real.rpow_pos_of_pos hp _).trans_le (hlow n)
  have hP0 : 1 ≤ P 0 := by
    have hh := ENNReal.toReal_mono (hne 0)
      ((G.adjustedUpLayerMoment_zero_ge_one a R p (Classical.arbitrary V) 0).trans
        (G.adjustedUpLayerMoment_le_sup a R p 0 _ 0))
    simpa only [ENNReal.toReal_one] using hh
  have hmul (m n : ℕ) : P (m+n) ≤ P m*P n := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (hne m) (hne n))
      (G.supAdjustedUpLayerMoment_submultiplicative hc hl a R hR hjump p m n)
    simpa only [ENNReal.toReal_mul] using hh
  have hboundr (n : ℕ) : P n ≤ C.toReal := ENNReal.toReal_mono hC.ne (hbound n)
  have hlog : Real.log (p : ℝ) ≤ 0 := Real.log_nonpos hp.le p.2.2
  have hexp (n : ℕ) : Real.exp (-(-A*Real.log (p : ℝ))*n-(-B*Real.log (p : ℝ))) ≤ P n := by
    have hh := hlow n
    rw [Real.rpow_def_of_pos hp] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  obtain ⟨β,hβ,hlo,hupp,hlim⟩ := positive_layer_moment_rate P hP hP0 hmul C.toReal hboundr
    (-A*Real.log (p : ℝ)) (-B*Real.log (p : ℝ))
    (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hA.le) hlog)
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hB) hlog) hexp
  refine ⟨β,hβ,hlo,?_,hlim⟩
  intro ε hε
  obtain ⟨K,hK,hKbound⟩ := hupp ε hε
  refine ⟨K,hK,fun n => ?_⟩
  have hh := ENNReal.ofReal_le_ofReal (hKbound n)
  rwa [ENNReal.ofReal_toReal (hne n)] at hh

end CriticalPercolation.BondGraph

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate_bs_oai.{u_1, u_2}
