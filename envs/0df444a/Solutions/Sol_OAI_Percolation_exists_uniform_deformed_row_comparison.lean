-- Prove2me | solution 1 for OAI.Percolation.exists_uniform_deformed_row_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:09:08.506172+00:00
-- url     : https://prove2.me/submissions/469a147a-29af-4495-8d53-33f8638d2a01

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

section SymmetricWalk
attribute [local instance] Classical.propDecidable



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
  simp only [Finset.mem_insert_self,ite_true]
  rw [← Finset.sum_filter,hf]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [N]
  ring

end SymmetricWalk

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
section WalkPowerSupport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_zero_of_not_step (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) (hxy : x ≠ y) (hadj : ¬ Adj G x y) :
    walkKernel G hloc a x y = 0 := by simp only [walkKernel,ite_eq_right hxy,ite_eq_right hadj,zero_add]

end WalkPowerSupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem neighbors_aut_card (G : BondGraph V E) (hloc : LocallyFinite G)
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) (x : V) :
    (neighbors G hloc (g x)).card = (neighbors G hloc x).card := by
  have he : neighbors G hloc (g x) = (neighbors G hloc x).map g.toEmbedding := by
    ext y
    simp only [mem_neighbors,Finset.mem_map,Equiv.coe_toEmbedding]
    constructor
    · intro h
      refine ⟨g.symm y,?_,by simp⟩
      simpa only [g.symm_apply_apply] using adj_aut G (isAut_symm G hg) h
    · rintro ⟨z,hz,rfl⟩
      exact adj_aut G hg hz
  rw [he,Finset.card_map]

theorem walkKernel_covariant (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) (x y : V) :
    walkKernel G hloc a (g x) (g y) = walkKernel G hloc a x y := by
  have hadj : Adj G (g x) (g y) ↔ Adj G x y :=
    ⟨fun h => by simpa using adj_aut G (isAut_symm G hg) h,adj_aut G hg⟩
  simp only [walkKernel,g.apply_eq_iff_eq,neighbors_aut_card G hloc hg,hadj]

end WalkCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

lemma finiteKernel_summable_mul (K : V → V → ℝ)
    (hf : ∀ x, (Function.support (K x)).Finite) (x : V) (f : V → ℝ) :
    Summable (fun y => K x y * f y) := by
  apply summable_of_ne_finset_zero (s := (hf x).toFinset)
  intro y hy
  have hd : K x y = 0 := by simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hy
  rw [hd,zero_mul]



end OrbitReturn
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
open MeasureTheory
open scoped ENNReal
section SusceptibilityTypes
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_twoPoint_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : Summable (twoPoint G p x) := by
  obtain ⟨_,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  exact summable_of_sum_le (twoPoint_nonneg G p x) (hrow x)

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
open MeasureTheory Filter
open scoped Topology
section ExteriorConnectionIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_restrictedConn [Countable E] (G : BondGraph V E)
    (S : Set E) (x y : V) : MeasurableSet {ω : Set E | Conn G (ω ∩ S) x y} :=
  measurableSet_finiteWitness _
    (fun _ _ hω hc => conn_mono G (Set.inter_subset_inter_left _ hω) hc)
    (finiteWitness_inter _ (finiteWitness_conn G x y) S)

end ExteriorConnectionIndependence
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_LargeContacts
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



theorem support_subset_of_retained (w : RawCorridor G k) (hlen : 0 < w.path.length)
    (D : Set V) (he : w.retained ⊆ internalEdges G D) :
    ∀ z ∈ w.path.support, z ∈ D := by
  intro z hz
  obtain ⟨s,hs,hzs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hlen)).mp hz
  obtain ⟨e,he',hGe⟩ := w.edge_has_label s hs
  exact he he' z (hGe.symm ▸ hzs)

end RawCorridor
end CorridorEligibility
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorTerminalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq



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

end CorridorIndependence
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathIntegration
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawFrom
variable {H : SimpleGraph V}

theorem integral_zero (P : V → V → ℝ) (x : V) (f : V → ℝ) :
    integral (H := H) P 0 x f = f x := by
  unfold integral
  rw [←(zeroEquiv x).symm.tsum_eq]
  simp only [zeroEquiv,Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,one_mul,tsum_fintype,Fintype.sum_unique]

theorem integral_succ [∀ x, Finite (H.neighborSet x)] (P : V → V → ℝ)
    (k : ℕ) (x : V) (f : V → ℝ) :
    integral (H := H) P (k+1) x f =
      P x x * integral (H := H) P k x f +
        ∑' z : H.neighborSet x, P x z * integral (H := H) P k z f := by
  unfold integral
  rw [←(succEquiv k x).symm.tsum_eq]
  let := Fintype.ofFinite (RawFrom H k x)
  let := Fintype.ofFinite (H.neighborSet x)
  let (z : H.neighborSet x) := Fintype.ofFinite (RawFrom H k z)
  simp only [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,succEquiv,
    Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,mul_assoc,Finset.mul_sum]

end RawFrom

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
section RawPathOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem sum_step_decomposition (H : SimpleGraph V) (P : V → V → ℝ)
    (hs : ∀ x, (Function.support (P x)).Finite)
    (hstep : ∀ x y, x ≠ y → ¬H.Adj x y → P x y = 0) (x : V) (f : V → ℝ) :
    (∑' y, P x y * f y) = P x x * f x + ∑' y : H.neighborSet x, P x y * f y := by
  rw [(finiteKernel_summable_mul P hs x f).tsum_eq_add_tsum_ite x]
  congr 1
  have he : (∑' y : H.neighborSet x, if (y:V) = x then (0:ℝ) else P x y * f y) =
      ∑' y, if y = x then (0:ℝ) else P x y * f y := by
    apply tsum_subtype_eq_of_support_subset (f := fun y : V => if y = x then (0:ℝ) else P x y * f y)
    intro y hy
    by_contra hn
    apply hy
    by_cases h : y = x
    · simp only [h,ite_true]
    · simp only [ite_eq_right h,hstep x y (Ne.symm h) hn,zero_mul]
  rw [←he]
  apply tsum_congr
  intro y
  have hn : (y:V) ≠ x := by
    intro h
    have hy : H.Adj x y := y.property
    rw [h] at hy
    exact H.loopless.irrefl x hy
  rw [ite_eq_right hn]

end RawPathOperator
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

end DeformedSusceptibility
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
section FreshWeightedMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedSusceptibility_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    0 ≤ deformedSusceptibility G P p k t D x :=
  tsum_nonneg (deformedKernel_nonneg G P p k t D x)

end FreshWeightedMass
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
section CorridorSizeBounds
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incidentSupport_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (W : Finset V) :
    (incidentSupport G hloc W).card ≤ W.card*d := by
  apply Finset.card_biUnion_le_card_mul
  intro x _
  rw [←Set.ncard_eq_toFinset_card _ (hloc x)]
  exact (incident_ncard_le_degree G hloc x).trans (hd x)

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

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem interior_card_le (w : RawCorridor G k) : w.interior.card ≤ w.path.length := by
  have hs : w.interior ⊂ w.path.support.toFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset,?_⟩
    intro he
    have hb : w.base ∈ w.path.support.toFinset := List.mem_toFinset.mpr w.path.start_mem_support
    rw [←he] at hb
    have hn : w.base ∉ w.interior := by simp only [interior,Finset.mem_sdiff,Finset.mem_insert,
      true_or,not_true_eq_false,and_false,not_false_eq_true]
    exact hn hb
  have hh := Finset.card_lt_card hs
  rw [List.toFinset_card_of_nodup w.path_isPath.support_nodup,SimpleGraph.Walk.length_support] at hh
  omega

theorem blockers_ncard_le (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (w : RawCorridor G k) : w.blockers.ncard ≤ d*k := by
  have hs : w.blockers ⊆ (incidentSupport G hloc w.interior : Set E) :=
    fun e he => (mem_incidentSupport G hloc w.interior e).mpr he.1
  calc
    _ ≤ (incidentSupport G hloc w.interior : Set E).ncard := Set.ncard_le_ncard hs (Finset.finite_toSet _)
    _ = (incidentSupport G hloc w.interior).card := Set.ncard_coe_finset _
    _ ≤ w.interior.card*d := incidentSupport_card_le G hloc d hd _
    _ ≤ k*d := Nat.mul_le_mul_right _ (w.interior_card_le.trans w.path_length)
    _ = _ := Nat.mul_comm _ _

end RawCorridor
end CorridorSizeBounds
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkTotalMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_finite_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x : V) : (Function.support (walkKernel G hloc a x)).Finite := by
  apply (Finset.finite_toSet (insert x (neighbors G hloc x))).subset
  intro y hy
  by_contra hn
  have hn' : y ≠ x ∧ ¬Adj G x y := by simpa only [Finset.mem_coe,Finset.mem_insert,mem_neighbors,not_or] using hn
  exact hy (by simp only [walkKernel,ite_eq_right hn'.1.symm,ite_eq_right hn'.2,add_zero])

theorem walkKernel_tsum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ) (x : V) :
    (∑' y, walkKernel G hloc a x y) = 1 := by
  rw [tsum_eq_sum (s := insert x (neighbors G hloc x))]
  · exact walkKernel_row_sum G hloc a x
  · intro y hy
    have hn : y ≠ x ∧ ¬Adj G x y := by simpa only [Finset.mem_insert,mem_neighbors,not_or] using hy
    simp only [walkKernel,ite_eq_right hn.1.symm,ite_eq_right hn.2,add_zero]

theorem raw_integral_one (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (k : ℕ) (x : V) :
    RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k x (fun _ => 1) = 1 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  induction k generalizing x with
  | zero => exact RawFrom.integral_zero _ _ _
  | succ k ih =>
    rw [RawFrom.integral_succ]
    simp only [ih,mul_one]
    have he := sum_step_decomposition (openSimpleGraph G Set.univ) (walkKernel G hloc a)
      (walkKernel_finite_support G hloc a) (fun x y hxy hn => by
        apply walkKernel_zero_of_not_step G hloc a x y hxy
        intro h
        obtain ⟨e,he⟩ := h
        exact hn ⟨hxy,e,Set.mem_univ e,he⟩) x (fun _ => 1)
    simpa only [mul_one,walkKernel_tsum G hloc a] using he.symm

 
theorem rawFrom_probability_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (k : ℕ) (x : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) k x, w.2.mass (walkKernel G hloc a)) = 1 := by
  simpa only [RawFrom.integral,mul_one] using raw_integral_one G hloc a k x

end RawWalkTotalMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkFiniteBases
attribute [local instance] Classical.propDecidable Classical.decEq

theorem raw_probability_on_bases_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (k : ℕ) (S : Set V) (hS : S.Finite) :
    (∑' w : RawCorridor G k, if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) = (S.ncard:ℝ) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  have hs : Summable (fun w : RawCorridor G k => if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (finite_corridors_on_bases G hloc k S hS).subset
    intro w hw
    by_contra hn
    exact hw (ite_eq_right hn)
  rw [hs.tsum_sigma]
  have he (x : V) : (∑' w : RawFrom (openSimpleGraph G Set.univ) k x,
      if (RawCorridor.base ⟨x,w⟩) ∈ S then (RawCorridor.probability (walkKernel G hloc a) ⟨x,w⟩) else 0) =
      if x ∈ S then 1 else 0 := by
    by_cases hx : x ∈ S
    · simp only [RawCorridor.base,RawCorridor.probability,hx,ite_true,rawFrom_probability_sum G hloc a k x]
    · simp only [RawCorridor.base,hx,ite_false,tsum_zero]
  simp only [he]
  rw [tsum_eq_sum (s := hS.toFinset)]
  · rw [Finset.sum_congr rfl (fun x hx => ite_eq_left (hS.mem_toFinset.mp hx))]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [←Set.ncard_eq_toFinset_card _ hS]
  · intro x hx
    exact ite_eq_right (fun h => hx (hS.mem_toFinset.mpr h))

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
section UniformRawWeight
attribute [local instance] Classical.propDecidable Classical.decEq


theorem rawWeightBase_one_le {r q : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hq : 0 < q) (hq₁ : q ≤ 1) (d : ℕ) : 1 ≤ rawWeightBase r q d := by
  exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ hr).mpr hr₁)
    (one_le_pow₀ ((one_le_inv₀ hq).mpr hq₁))

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem weight_le_uniform (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (w : RawCorridor G k) : w.weight P p ≤ w.probability P * (rawWeightBase r q d)^k := by
  have hp₀ : 0 < (p:ℝ) := hr.trans_le hrp
  have hp₁ : 0 < 1-(p:ℝ) := hq.trans_le hqp
  have hr₁ : r ≤ 1 := hrp.trans p.2.2
  have hq₁ : q ≤ 1 := hqp.trans (sub_le_self _ p.2.1)
  have hi : (p:ℝ)⁻¹ ≤ r⁻¹ := inv_anti₀ hr hrp
  have hj : (1-(p:ℝ))⁻¹ ≤ q⁻¹ := inv_anti₀ hq hqp
  have hL : ((p:ℝ)^w.path.length)⁻¹ ≤ (r⁻¹)^k := by
    simp only [←inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr p.2.1) hi _).trans
      (pow_le_pow_right₀ ((one_le_inv₀ hr).mpr hr₁) w.path_length)
  have hB : ((1-(p:ℝ))^w.blockers.ncard)⁻¹ ≤ ((q⁻¹)^d)^k := by
    simp only [←inv_pow,←pow_mul]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hp₁.le) hj _).trans
      (pow_le_pow_right₀ ((one_le_inv₀ hq).mpr hq₁) (w.blockers_ncard_le hloc d hd))
  unfold weight
  calc
    _ = w.probability P * (((p:ℝ)^w.path.length)⁻¹ * ((1-(p:ℝ))^w.blockers.ncard)⁻¹) := mul_assoc _ _ _
    _ ≤ w.probability P * ((r⁻¹)^k * ((q⁻¹)^d)^k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hL hB
        (inv_nonneg.mpr (pow_nonneg hp₁.le _)) (pow_nonneg (inv_nonneg.mpr hr.le) _))
        (w.2.2.mass_nonneg P hP)
    _ = _ := by rw [rawWeightBase,mul_pow]

end RawCorridor
end UniformRawWeight
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

theorem mask_le_mask_mul {U W : Prop} [Decidable U] [Decidable W] (hUW : U → W)
    {f g B : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hfg : f ≤ g*B) :
    (if U then f else 0) ≤ (if W then g else 0)*B := by
  by_cases hU : U
  · simp only [hU,hUW hU,ite_true]; exact hfg
  · rw [ite_eq_right hU]
    by_cases hW : W
    · rw [ite_eq_left hW]; exact mul_nonneg hg hB
    · rw [ite_eq_right hW,zero_mul]

theorem raw_weight_sum_le_on_bases (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (S : Set V) (hS : S.Finite) (Q : RawCorridor G k → Prop)
    (hQ : ∀ w, Q w → w.base ∈ S) :
    (∑' w : RawCorridor G k, if Q w then w.weight (walkKernel G hloc a) p else 0) ≤
      (S.ncard:ℝ)*(rawWeightBase r q d)^k := by
  have hf := summable_raw_selection G hloc k S hS Q hQ
    (fun w => w.weight (walkKernel G hloc a) p)
  have hg := summable_raw_selection G hloc k S hS (fun w => w.base ∈ S)
    (fun _ h => h) (fun w => w.probability (walkKernel G hloc a))
  have hB : 0 ≤ (rawWeightBase r q d)^k := pow_nonneg
    (zero_le_one.trans (rawWeightBase_one_le hr (hrp.trans p.2.2) hq (hqp.trans (sub_le_self _ p.2.1)) d)) _
  have hpoint (w : RawCorridor G k) :
      (if Q w then w.weight (walkKernel G hloc a) p else 0) ≤
        (if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) * (rawWeightBase r q d)^k :=
    mask_le_mask_mul (hQ w) (w.2.2.mass_nonneg _ hP) hB
      (w.weight_le_uniform hloc d hd (walkKernel G hloc a) hP p hr hq hrp hqp)
  have hb := hf.tsum_le_tsum hpoint (hg.mul_right ((rawWeightBase r q d)^k))
  rw [tsum_mul_right,raw_probability_on_bases_sum G hloc a k S hS] at hb
  exact hb



theorem raw_edge_weight_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (e : E) (z : V) (hz : z ∈ G e) :
    (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤
      (((d:ℝ)+1)*rawWeightBase r q d)^k := by
  have hb := raw_weight_sum_le_on_bases G hloc d hd a hP p hr hq hrp hqp k
    (reachBall G z k) (finite_reachBall hloc z k) (fun w => e ∈ w.retained)
    (fun w hw => w.base_mem_reachBall_of_retained e hw z hz)
  have hcard : ((reachBall G z k).ncard:ℝ) ≤ ((d:ℝ)+1)^k := by
    exact_mod_cast reachBall_ncard_le_pow G hloc d hd z k
  have hB : 0 ≤ (rawWeightBase r q d)^k := pow_nonneg
    (zero_le_one.trans (rawWeightBase_one_le hr (hrp.trans p.2.2) hq (hqp.trans (sub_le_self _ p.2.1)) d)) _
  exact hb.trans ((mul_le_mul_of_nonneg_right hcard hB).trans_eq (mul_pow _ _ _).symm)

end UniformPenaltyDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExponentialCorridorCost
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pow_le_exp_div_self {B : ℝ} (hB : 1 ≤ B) {k : ℕ} (hk : 0 < k) :
    B^k ≤ Real.exp ((Real.log B + 1)*(k:ℝ))/(k:ℝ) := by
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  apply (le_div_iff₀ (Nat.cast_pos.mpr hk)).mpr
  have hh : (k:ℝ) ≤ Real.exp (k:ℝ) := by linarith [Real.add_one_le_exp (k:ℝ)]
  calc
    _ ≤ B^k * Real.exp (k:ℝ) := mul_le_mul_of_nonneg_left hh (pow_nonneg hB₀.le _)
    _ = Real.exp ((k:ℝ)*Real.log B) * Real.exp (k:ℝ) := by rw [Real.exp_nat_mul,Real.exp_log hB₀]
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

 

theorem exists_uniform_corridor_edge_cost (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (k : ℕ), 3 ≤ k → ∀ e : E,
      (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤
        Real.exp (C*(k:ℝ))/(k:ℝ) := by
  let B := ((d:ℝ)+1)*rawWeightBase ((pc G:ℝ)/2) (1-(pc G:ℝ)) d
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    (rawWeightBase_one_le (half_pos hpcrit) (by have := (pc G).2.2; linarith)
      (sub_pos.mpr hpcrit₁) (sub_le_self _ (pc G).2.1) d)
  refine ⟨Real.log B + 1,by linarith [Real.log_nonneg hB],?_⟩
  intro p hpnear hp k hk e
  obtain ⟨z,z',hzz⟩ : ∃ z z', G e = s(z,z') := by
    obtain ⟨⟨z,z'⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨z,z',hh.symm⟩
  have he : z ∈ G e := hzz.symm ▸ Sym2.mem_mk_left z z'
  have hq : 1-(pc G:ℝ) ≤ 1-(p:ℝ) := sub_le_sub_left (show (p:ℝ) ≤ (pc G:ℝ) from hp.le) (1:ℝ)
  exact (raw_edge_weight_bound G hloc d hd a hP p (half_pos hpcrit)
    (sub_pos.mpr hpcrit₁) hpnear hq k e z he).trans (pow_le_exp_div_self hB (by omega))

end ExponentialCorridorCost
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalMoveGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_move_terminal (w : RawCorridor G k) (D : Set V) (ω : Set E)
    (F : Set E) (hF : F ⊆ ω ∩ internalEdges G D) (b z y : V)
    (hbz : Conn G F b z) (hc : w.counted D ω b y) (hdis : Disjoint F w.retained) :
    w.counted D ω z y := by
  apply (w.counted_iff D ω z y).mpr
  refine ⟨hc.1,conn_trans G _ (conn_symm G _ (conn_mono G hF hbz)) hc.2.2.1,?_,hc.2.2.2.2⟩
  intro e he
  refine ⟨(hc.2.2.2.1 e he).1,?_⟩
  intro hzy
  apply (hc.2.2.2.1 e he).2
  apply conn_trans G _ (conn_mono G ?_ hbz) hzy
  intro f hf
  refine ⟨hF hf,?_⟩
  intro hfe
  have hh : f = e := Set.mem_singleton_iff.mp hfe
  exact Set.disjoint_left.mp hdis hf (hh.symm ▸ he)

end RawCorridor

 

theorem corridorPenaltyTerm_move_bound (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (D : Set V) (ω : Set E)
    (F : Finset E) (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V)
    (hbz : Conn G (F:Set E) b z) (w : RawCorridor G k) :
    corridorPenaltyTerm G P p D ω b y w ≤
      (∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0) + corridorPenaltyTerm G P p D ω z y w := by
  have hn := w.weight_nonneg P hP p
  have hs : 0 ≤ ∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0 :=
    Finset.sum_nonneg (fun e _ => by split_ifs; exact hn; exact le_rfl)
  by_cases hc : w.counted D ω b y
  · rw [corridorPenaltyTerm,ite_eq_left hc]
    by_cases hd : Disjoint (F:Set E) w.retained
    · have hc' := w.counted_move_terminal D ω F hF b z y hbz hc hd
      simpa only [corridorPenaltyTerm,hc',ite_true] using le_add_of_nonneg_left hs
    · obtain ⟨e,he,hew⟩ := Set.not_disjoint_iff.mp hd
      have he' : (if e ∈ w.retained then w.weight P p else 0) ≤
          ∑ f ∈ F, if f ∈ w.retained then w.weight P p else 0 :=
        Finset.single_le_sum (f := fun f => if f ∈ w.retained then w.weight P p else 0) (fun f _ => by split_ifs; exact hn; exact le_rfl) he
      rw [ite_eq_left hew] at he'
      exact he'.trans (le_add_of_nonneg_right (corridorPenaltyTerm_nonneg G P hP p D ω z y w))
  · rw [corridorPenaltyTerm,ite_eq_right hc]
    exact add_nonneg hs (corridorPenaltyTerm_nonneg G P hP p D ω z y w)

end TerminalMoveGeometry
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

 

theorem corridorPenalty_move_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V) (hbz : Conn G (F:Set E) b z) :
    corridorPenalty G P p k D ω b y ≤
      (∑ e ∈ F, ∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) +
        corridorPenalty G P p k D ω z y := by
  have hs : Summable (fun w : RawCorridor G k => ∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0) :=
    (hasSum_sum (fun e (_ : e ∈ F) => (summable_raw_edge_weights G hloc P p k e).hasSum)).summable
  have hr := corridorPenalty_summable G hloc P p k D ω z y
  have hl := (corridorPenalty_summable G hloc P p k D ω b y).tsum_le_tsum
    (corridorPenaltyTerm_move_bound G P hP p k D ω F hF b z y hbz) (hs.add hr)
  rw [hs.tsum_add hr,Summable.tsum_finsetSum (fun e _ => summable_raw_edge_weights G hloc P p k e)] at hl
  exact hl

end TerminalMovePenalty
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteOpeningAssociation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_union_const (S : Set E) : Measurable (fun ω : Set E => ω ∪ S) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).or measurable_const

theorem measurableSet_finite_open (F : Finset E) : MeasurableSet {ω : Set E | (F:Set E) ⊆ ω} := by
  have he : {ω : Set E | (F:Set E) ⊆ ω} = ⋂ e ∈ F, {ω : Set E | e ∈ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Finset.mem_coe,Set.subset_def]
  rw [he]
  exact F.measurableSet_biInter (fun e _ => measurableSet_setOfPred.mpr ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable))

 

theorem finite_open_integral_lower (p : unitInterval) (F : Finset E) (f : Set E → ℝ)
    (hf : Measurable f) (hn : ∀ ω, 0 ≤ f ω) (hb : ∀ ω, f ω ≤ 1)
    (hm : Monotone f) :
    (p:ℝ)^F.card*(∫ ω, f ω ∂law p) ≤ ∫ ω, if (F:Set E) ⊆ ω then f ω else 0 ∂law p := by
  let J : Set E → ℝ := fun ω => if (F:Set E) ⊆ ω then 1 else 0
  let g : Set E → ℝ := fun ω => f (ω ∪ (F:Set E))
  have hJ : Measurable J := Measurable.ite (measurableSet_finite_open F) measurable_const measurable_const
  have hg : Measurable g := hf.comp (measurable_union_const (F:Set E))
  have hi (f : Set E → ℝ) (hfm : Measurable f) (hfn : ∀ ω, 0 ≤ f ω) (hfb : ∀ ω, f ω ≤ 1) : Integrable f (law p) := by
    exact Integrable.mono' (integrable_const (1:ℝ)) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (hfn ω)]; exact hfb ω))
  have hfi := hi f hf hn hb
  have hgi := hi g hg (fun ω => hn _) (fun ω => hb _)
  have hJint : (∫ ω, J ω ∂law p) = (p:ℝ)^F.card := by
    have hh := integral_indicator_const (μ := law p) (1:ℝ) (measurableSet_finite_open F)
    simpa only [Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_one,finite_open_probability,J] using hh
  have he := integral_mul_disjoint_coordinates p (F:Set E) (F:Set E)ᶜ disjoint_compl_right J g hJ hg
    (fun ω => by simp only [J,Set.subset_inter_iff,Set.Subset.refl,and_true])
    (fun ω => by
      dsimp only [g]
      congr 1
      ext e
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
      tauto)
  calc
    _ ≤ (p:ℝ)^F.card*(∫ ω, g ω ∂law p) := mul_le_mul_of_nonneg_left
      (integral_mono hfi hgi (fun ω => hm Set.subset_union_left)) (pow_nonneg p.2.1 _)
    _ = (∫ ω, J ω ∂law p)*(∫ ω, g ω ∂law p) := by rw [hJint]
    _ = ∫ ω, J ω*g ω ∂law p := he.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hF : (F:Set E) ⊆ ω
        · simp only [J,g,hF,ite_true,one_mul,Set.union_eq_left.mpr hF]
        · simp only [J,hF,ite_false,zero_mul])

end FiniteOpeningAssociation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalConnectionComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenalty_move_edge_cost (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V) (hbz : Conn G (F:Set E) b z)
    (c : ℝ) (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    corridorPenalty G P p k D ω b y ≤ (F.card:ℝ)*c+corridorPenalty G P p k D ω z y := by
  apply (corridorPenalty_move_bound G hloc P hP p k D ω F hF b z y hbz).trans
  apply add_le_add _ le_rfl
  exact (Finset.sum_le_sum (fun e _ => hc e)).trans_eq (by simp only [Finset.sum_const,nsmul_eq_mul])

 

theorem deformedConnection_move_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z y : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (if (F:Set E) ⊆ ω then deformedConnection G P p k t D ω z y else 0) ≤
      deformedConnection G P p k t D ω b y := by
  by_cases ho : (F:Set E) ⊆ ω
  · rw [ite_eq_left ho]
    by_cases hz : z ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) z y
    · have hFa : (F:Set E) ⊆ ω ∩ internalEdges G D := fun e he => ⟨ho he,hF he⟩
      have hb' : b ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) b y :=
        ⟨hb,hz.2.1,conn_trans G _ (conn_mono G hFa hbz) hz.2.2⟩
      simp only [deformedConnection,hz,hb',and_self,ite_true]
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonpos_left
        (corridorPenalty_move_edge_cost G hloc P hP p k D ω F hFa b z y hbz c hc) (neg_nonpos.mpr ht)
      simpa only [mul_add] using hh
    · rw [deformedConnection,ite_eq_right hz,mul_zero]
      exact deformedConnection_nonneg G P p k t D ω b y
  · rw [ite_eq_right ho,mul_zero]
    exact deformedConnection_nonneg G P p k t D ω b y

end TerminalConnectionComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section EndpointSusceptibilityComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedKernel_move_lower [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z y : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card * deformedKernel G P p k t D z y ≤
      deformedKernel G P p k t D b y := by
  have hi := integrable_deformedConnection G P hP p k t ht D z y
  have hIi := hi.indicator (measurableSet_finite_open F)
  have has := finite_open_integral_lower p F (fun ω => deformedConnection G P p k t D ω z y)
    (measurable_deformedConnection G P p k t D z y)
    (fun ω => deformedConnection_nonneg G P p k t D ω z y)
    (fun ω => deformedConnection_le_one G P hP p k t ht D ω z y)
    (fun _ _ hω => deformedConnection_mono G hloc P hP p k t ht (Set.Subset.refl _) hω z y)
  have hb' := integral_mono (hIi.const_mul (Real.exp (-t*((F.card:ℝ)*c))))
    (integrable_deformedConnection G P hP p k t ht D b y)
    (fun ω => deformedConnection_move_lower G hloc P hP p k t ht D ω F hF b z y hb hbz c hc)
  simp only [Set.indicator,Set.mem_ofPred_eq,integral_const_mul] at hb'
  have hh := mul_le_mul_of_nonneg_left has (Real.exp_pos (-t*((F.card:ℝ)*c))).le
  simp only [mul_assoc] at hh ⊢
  exact hh.trans hb'

 
theorem deformedSusceptibility_move_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card * deformedSusceptibility G P p k t D z ≤
      deformedSusceptibility G P p k t D b := by
  simpa only [deformedSusceptibility,tsum_mul_left] using
    ((summable_deformedKernel G hloc hqt P hP p hp k t ht D z).mul_left
      (Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card)).tsum_le_tsum
      (fun y => deformedKernel_move_lower G hloc P hP p k t ht D F hF b z y hb hbz c hc)
      (summable_deformedKernel G hloc hqt P hP p hp k t ht D b)

end EndpointSusceptibilityComparison
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
section UniformDeformedEndpoint
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_uniform_deformed_endpoint_comparison [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (k : ℕ), 3 ≤ k → ∀ (t : ℝ), 0 ≤ t → ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b := by
  obtain ⟨C,hC,hcost⟩ := exists_uniform_corridor_edge_cost G hloc d hd a hP hpcrit hpcrit₁
  refine ⟨C,hC,?_⟩
  intro p hpnear hp k hk t ht D b z l hb hl hD
  have hc : ∀ e, (∑' w : RawCorridor G k,
      if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤ Real.exp (C*(k:ℝ)) := by
    intro e
    exact (hcost p hpnear hp k hk e).trans (div_le_self (Real.exp_pos _).le (by exact_mod_cast (show 1 ≤ k by omega)))
  have hh := deformedSusceptibility_move_lower G hloc hqt (walkKernel G hloc a) hP p hp k t ht D
    l.toFinset (fun e he => hD e (List.mem_toFinset.mp he)) b z hb
    (hl.conn (fun e he => List.mem_toFinset.mpr he)) (Real.exp (C*(k:ℝ))) hc
  have hcard : (l.toFinset.card:ℝ) ≤ (l.length:ℝ) := Nat.cast_le.mpr l.toFinset_card_le
  have he : Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) ≤
      Real.exp (-t*((l.toFinset.card:ℝ)*Real.exp (C*(k:ℝ)))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le) (neg_nonpos.mpr ht)
  have hpw : (p:ℝ)^l.length ≤ (p:ℝ)^l.toFinset.card :=
    pow_le_pow_of_le_one p.2.1 p.2.2 l.toFinset_card_le
  exact (mul_le_mul_of_nonneg_right (mul_le_mul he hpw (pow_nonneg p.2.1 _) (Real.exp_pos _).le)
    (tsum_nonneg (deformedKernel_nonneg G (walkKernel G hloc a) p k t D z))).trans hh

end UniformDeformedEndpoint
end Percolation


namespace Percolation
universe u u' v
section ErasureNaturality
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {H : SimpleGraph V} {H' : SimpleGraph V'}

theorem walk_map_dropUntil (f : H →g H') (hf : Function.Injective f)
    {x y : V} (w : H.Walk x y) (z : V) (hz : z ∈ w.support) :
    (w.dropUntil z hz).map f = (w.map f).dropUntil (f z)
      (by simpa only [SimpleGraph.Walk.support_map] using List.mem_map_of_mem hz) := by
  induction w with
  | @nil x =>
    have he : z = x := by simpa using hz
    subst z
    rfl
  | @cons x a y h w ih =>
    by_cases he : x = z
    · subst z
      simp only [SimpleGraph.Walk.dropUntil_first]
    · have hfe : f x ≠ f z := fun h => he (hf h)
      simp only [SimpleGraph.Walk.dropUntil,he,hfe,SimpleGraph.Walk.map_cons]
      exact ih _

 

theorem walk_map_bypass (f : H →g H') (hf : Function.Injective f)
    {x y : V} (w : H.Walk x y) : w.bypass.map f = (w.map f).bypass := by
  induction w with
  | nil => rfl
  | @cons x a y h w ih =>
    have hm : f x ∈ (w.map f).bypass.support ↔ x ∈ w.bypass.support := by
      rw [←ih,SimpleGraph.Walk.support_map]
      exact List.mem_map_of_injective hf
    by_cases hx : x ∈ w.bypass.support
    · have hfx := hm.mpr hx
      simp only [SimpleGraph.Walk.bypass,SimpleGraph.Walk.map_cons,dite_eq_left hx,dite_eq_left hfx]
      simp only [walk_map_dropUntil f hf,ih]
    · have hfx := mt hm.mp hx
      simp only [SimpleGraph.Walk.bypass,SimpleGraph.Walk.map_cons,dite_eq_right hx,dite_eq_right hfx,ih]

namespace HoldingWalk

theorem map_withoutHolds (f : H →g H') {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).withoutHolds = w.withoutHolds.map f := by
  induction w with
  | nil => rfl
  | hold w ih => exact ih
  | step h w ih => simp only [map,withoutHolds,SimpleGraph.Walk.map_cons,ih]

theorem map_erase (f : H →g H') (hf : Function.Injective f)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).erase = w.erase.map f := by
  simp only [erase,map_withoutHolds,SimpleGraph.Walk.reverse_map,
    ←walk_map_bypass f hf]

end HoldingWalk
end ErasureNaturality
end Percolation

 
namespace Percolation
universe u u' u'' v
section RawWalkMaps
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {V'' : Type u''}
  {H : SimpleGraph V} {H' : SimpleGraph V'} {H'' : SimpleGraph V''}
namespace HoldingWalk

theorem mass_map (f : H →g H') (P : V → V → ℝ) (Q : V' → V' → ℝ)
    (hPQ : ∀ x y, Q (f x) (f y) = P x y)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : (w.map f).mass Q = w.mass P := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [map,mass,hPQ,ih]
  | step h w ih => simp only [map,mass,hPQ,ih]
end HoldingWalk

end RawWalkMaps
section GraphAutWalks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {E : Type v}

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem aut_path {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path = w.path.map (autSimpleGraph G hab).toHom :=
  w.2.2.map_erase _ a.injective

theorem aut_path_length {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.length = w.path.length := by
  have hh := congrArg (fun q => q.length) (aut_path hab w)
  exact hh.trans (SimpleGraph.Walk.length_map _ _)

end RawCorridor
end GraphAutWalks
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TemplateCovariance
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem aut_base {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).base = a w.base := rfl

theorem aut_endpoint {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).endpoint = a w.endpoint := rfl

theorem aut_support {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.support = w.path.support.map a := by
  exact (congrArg (fun q => q.support) (aut_path hab w)).trans
    (SimpleGraph.Walk.support_map _ _)

theorem aut_edges {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.edges = w.path.edges.map (Sym2.map a) := by
  exact (congrArg (fun q => q.edges) (aut_path hab w)).trans
    (SimpleGraph.Walk.edges_map _ _)

theorem aut_interior {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (z : V) :
    a z ∈ (autEquiv hab w).interior ↔ z ∈ w.interior := by
  simp only [interior,Finset.mem_sdiff,List.mem_toFinset]
  rw [aut_support hab w]
  simp only [aut_base,aut_endpoint,Finset.mem_insert,Finset.mem_singleton,
    List.mem_map_of_injective a.injective,a.injective.eq_iff]

theorem aut_retained {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (e : E) :
    b e ∈ (autEquiv hab w).retained ↔ e ∈ w.retained := by
  simp only [retained,Set.mem_ofPred_eq,aut_edges hab w,hab e]
  exact List.mem_map_of_injective (Sym2.map.injective a.injective)

theorem aut_blockers {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (e : E) :
    b e ∈ (autEquiv hab w).blockers ↔ e ∈ w.blockers := by
  simp only [blockers,Set.mem_sdiff,Set.mem_ofPred_eq,aut_retained]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨z,hz,he⟩
    rw [hab e] at he
    obtain ⟨y,hy,rfl⟩ := Sym2.mem_map.mp he
    exact ⟨y,(aut_interior hab w y).mp hz,hy⟩
  · rintro ⟨z,hz,he⟩
    refine ⟨a z,(aut_interior hab w z).mpr hz,?_⟩
    rw [hab e]
    exact Sym2.mem_map.mpr ⟨z,he,rfl⟩

theorem aut_blockers_ncard {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).blockers.ncard = w.blockers.ncard := by
  have he : w.blockers = b ⁻¹' (autEquiv hab w).blockers := by
    ext e
    exact (aut_blockers hab w e).symm
  rw [he,Set.ncard_preimage_of_injective_subset_range b.injective]
  exact fun e _ => b.surjective e

theorem aut_probability {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y) (w : RawCorridor G k) :
    (autEquiv hab w).probability P = w.probability P :=
  w.2.2.mass_map (autSimpleGraph G hab).toHom P P hP

theorem aut_weight {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y) (p : ℝ) (w : RawCorridor G k) :
    (autEquiv hab w).weight P p = w.weight P p := by
  simp only [weight,aut_probability hab P hP,aut_path_length,aut_blockers_ncard]

end RawCorridor
end TemplateCovariance
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
section CountedCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem preimage_diff_singleton (b : E ≃ E) (ω : Set E) (e : E) :
    (b ⁻¹' ω) \ {e} = b ⁻¹' (ω \ {b e}) := by
  ext f
  simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]

theorem corridorCounted_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set E) (D : Set V) (ω : Set E) (x y : V) :
    corridorCounted G (b ⁻¹' S) (b ⁻¹' B) (a ⁻¹' D) (b ⁻¹' ω) x y ↔
      corridorCounted G S B D ω (a x) (a y) := by
  have he : (b ⁻¹' ω) ∩ internalEdges G (a ⁻¹' D) = b ⁻¹' (ω ∩ internalEdges G D) := by
    rw [internalEdges_aut_preimage G hab,Set.preimage_inter]
  simp only [corridorCounted,he,conn_aut_iff G hab,preimage_diff_singleton,
    Set.mem_preimage]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨hp,hB⟩
    constructor
    · intro e he
      obtain ⟨f,rfl⟩ := b.surjective e
      exact hp f he
    · apply Set.disjoint_left.mpr
      intro e he hw
      obtain ⟨f,rfl⟩ := b.surjective e
      exact Set.disjoint_left.mp hB he hw
  · rintro ⟨hp,hB⟩
    exact ⟨fun e he => hp (b e) he,Set.disjoint_left.mpr (fun e he hw => Set.disjoint_left.mp hB he hw)⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem aut_counted {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted (a ⁻¹' D) (b ⁻¹' ω) x y ↔ (autEquiv hab w).counted D ω (a x) (a y) := by
  have hr : w.retained = b ⁻¹' (autEquiv hab w).retained := by
    ext e
    exact (aut_retained hab w e).symm
  have hb : w.blockers = b ⁻¹' (autEquiv hab w).blockers := by
    ext e
    exact (aut_blockers hab w e).symm
  rw [counted_iff,counted_iff,aut_path_length,hr,hb,corridorCounted_aut G hab]

end RawCorridor

theorem corridorPenaltyTerm_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) {k : ℕ} (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenaltyTerm G P p (a ⁻¹' D) (b ⁻¹' ω) x y w =
      corridorPenaltyTerm G P p D ω (a x) (a y) (RawCorridor.autEquiv hab w) := by
  simp only [corridorPenaltyTerm,w.aut_counted hab D ω x y,RawCorridor.aut_weight hab P hP]

theorem corridorPenalty_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenalty G P p k (a ⁻¹' D) (b ⁻¹' ω) x y =
      corridorPenalty G P p k D ω (a x) (a y) := by
  unfold corridorPenalty
  rw [←(RawCorridor.autEquiv hab).tsum_eq (corridorPenaltyTerm G P p D ω (a x) (a y))]
  exact tsum_congr (fun w => corridorPenaltyTerm_aut G hab P hP p w D ω x y)

end CountedCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t (a ⁻¹' D) (b ⁻¹' ω) x y =
      deformedConnection G P p k t D ω (a x) (a y) := by
  simp only [deformedConnection,corridorPenalty_aut G hab P hP,Set.mem_preimage,
    internalEdges_aut_preimage G hab,←Set.preimage_inter,conn_aut_iff G hab]

theorem deformedKernel_aut [Countable V] [Countable E]
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) :
    deformedKernel G P p k t D (a x) (a y) = deformedKernel G P p k t (a ⁻¹' D) x y := by
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable
    (measurable_deformedConnection G P p k t (a ⁻¹' D) x y).aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [deformedKernel,deformedConnection_aut G hab P hP] using h.symm

theorem deformedSusceptibility_aut [Countable V] [Countable E]
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    deformedSusceptibility G P p k t D (a x) = deformedSusceptibility G P p k t (a ⁻¹' D) x := by
  unfold deformedSusceptibility
  rw [←a.tsum_eq (deformedKernel G P p k t D (a x))]
  exact tsum_congr (fun y => deformedKernel_aut G hab P hP p k t D x y)



end DeformationCovariance
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeformedRowComparison
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

 

theorem exists_uniform_deformed_row_comparison_oai (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C cf : ℝ, 0 < C ∧ 0 < cf ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G → ∀ (k : ℕ), 3 ≤ k → ∀ (t : ℝ),
      0 ≤ t → t*Real.exp (C*(k:ℝ)) ≤ 1 → ∀ x,
      cf*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x := by
  obtain ⟨C,hC,hmove⟩ := exists_uniform_deformed_endpoint_comparison G hloc hqt d hd a hP hpcrit hpcrit₁
  have hex (ij : ι × ι) : ∃ l : List E, Along G (root ij.1) l (root ij.2) := by
    obtain ⟨l,hl,_,_⟩ := conn_exists_bond_trail G (conn_univ_of_connected G hconn (root ij.1) (root ij.2))
    exact ⟨l,hl⟩
  choose path hpath using hex
  let N := ∑ ij : ι × ι, (path ij).length
  have hlen (i j : ι) : (path (i,j)).length ≤ N :=
    Finset.single_le_sum (f := fun ij : ι × ι => (path ij).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i,j))
  refine ⟨C,Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N,hC,mul_pos (Real.exp_pos _) (pow_pos (half_pos hpcrit) N),?_⟩
  intro p hpnear hp k hk t ht htc x
  obtain ⟨j,g,b,hgb,hgx⟩ := hcover x
  have hb (i : ι) : (Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N)*
      deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root i) ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root j) := by
    have hh := hmove p hpnear hp k hk t ht Set.univ (root j) (root i) (path (j,i))
      (Set.mem_univ _) (hpath (j,i)) (fun _ _ _ _ => Set.mem_univ _)
    have hpow : ((pc G:ℝ)/2)^N ≤ (p:ℝ)^(path (j,i)).length :=
      (pow_le_pow_left₀ (half_pos hpcrit).le hpnear N).trans
        (pow_le_pow_of_le_one p.2.1 p.2.2 (hlen j i))
    have he : Real.exp (-(N:ℝ)) ≤ Real.exp (-t*((path (j,i)).length*Real.exp (C*(k:ℝ)))) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right htc (Nat.cast_nonneg (path (j,i)).length : (0:ℝ) ≤ _)
      have hn : ((path (j,i)).length:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr (hlen j i)
      nlinarith
    exact (mul_le_mul_of_nonneg_right (mul_le_mul he hpow (pow_nonneg (half_pos hpcrit).le _) (Real.exp_pos _).le)
      (deformedSusceptibility_nonneg G _ p k t Set.univ (root i))).trans hh
  rw [←hgx,deformedSusceptibility_aut G hgb _ (walkKernel_covariant G hloc a hgb)]
  simp only [Set.preimage_univ]
  calc
    _ = ∑ i, weight i*((Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N)*
        deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root i)) := by
      simp only [averagedDeformedSusceptibility,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ ∑ i, weight i*deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root j) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = _ := by rw [←Finset.sum_mul,hw1,one_mul]

end DeformedRowComparison
end Percolation


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.exists_uniform_deformed_row_comparison_oai.{u, v, u_1} := @OAI.Percolation.exists_uniform_deformed_row_comparison_oai.{u, v, u_1}
