-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:30:32.41159+00:00
-- url     : https://prove2.me/submissions/f24aa523-d50f-497e-85f0-f5441bd1e79b

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_subcritical_peak_band_probability_bs

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

lemma Aut.cluster_image (φ : G.Aut) (ω : Set E) (o : V) :
    φ.vertex '' G.cluster ω o = G.cluster (φ.edge '' ω) (φ.vertex o) := by
  ext v
  obtain ⟨w, rfl⟩ := φ.vertex.surjective v
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]
  change (G.openGraph ω).Reachable o w ↔
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex o) (φ.vertex w)
  exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := o) (v := w)).symm

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

lemma measurable_restrictedLayerCount [Countable V] [Countable E]
    (I : Set E) (A : Set V) (x : V) : Measurable (fun ω => restrictedLayerCount G I A ω x) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.tsum fun y => Measurable.ite
    (measurable_const.and ((measurableSet_conn G x y).mem.comp hm)).setOf
    measurable_const measurable_const

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

end CriticalPercolation.BondGraph

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

lemma measurable_adjustedBandTransport [Countable V] [Countable E] (a : V → ℝ) (l u : ℝ) (x y : V) :
    Measurable (fun ω => G.adjustedBandTransport a l u ω x y) := by
  exact Measurable.ite ((G.measurable_reachable x y).and measurable_const).setOf
    measurable_const measurable_const

lemma adjustedBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.adjustedBandTransport a l u (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.adjustedBandTransport a l u ω x y := by
  simp only [adjustedBandTransport,G.orbitAdjustedHeight_aut a ha,
    ←Aut.cluster_image,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

lemma adjustedBandTransport_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (l u : ℝ) (ω : Set E) (x y : V) :
    G.adjustedBandTransport a l u ω x y = G.adjustedBandTransport a (-u) (-l) ω y x := by
  unfold adjustedBandTransport
  rw [G.orbitAdjustedHeight_reverse hc hl a x y]
  congr 1
  apply propext
  constructor
  · rintro ⟨h,hlo,hhi⟩
    exact ⟨h.symm,by linarith,by linarith⟩
  · rintro ⟨h,hlo,hhi⟩
    exact ⟨h.symm,by linarith,by linarith⟩

lemma adjustedBandTransport_weight_bounds (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (l u : ℝ) (ω : Set E) (x y : V) :
    ENNReal.ofReal (Real.exp (-u))*G.adjustedBandTransport a (-u) (-l) ω y x ≤
      G.adjustedBandTransport a l u ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ∧
    G.adjustedBandTransport a l u ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ≤
      ENNReal.ofReal (Real.exp (-l))*G.adjustedBandTransport a (-u) (-l) ω y x := by
  rw [G.adjustedBandTransport_reverse hc hl a l u ω x y]
  unfold adjustedBandTransport
  split_ifs with h
  · simp only [mul_one,one_mul]
    constructor <;> apply ENNReal.ofReal_le_ofReal <;> apply Real.exp_le_exp.mpr
    · exact h.2.1
    · exact h.2.2
  · simp only [mul_zero,zero_mul,le_refl,and_self]

theorem expected_adjustedBandCount_reciprocity [Countable V] [Countable E]
    (R : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval) (l u : ℝ) :
    ENNReal.ofReal (Real.exp (-u))*
      (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a (-u) (-l) ω x ∂G.law p)) ≤
      (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p)) ∧
    (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p)) ≤
      ENNReal.ofReal (Real.exp (-l))*
        (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a (-u) (-l) ω x ∂G.law p)) := by
  have he := OrbitRepresentatives.random_normalized_tilted_transport G R hc hl a hapos ha p
    (G.adjustedBandTransport a l u) (G.measurable_adjustedBandTransport a l u)
    (G.adjustedBandTransport_aut a ha l u)
  change (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p)) = _ at he
  rw [he]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _hy
    have hb (ω : Set E) : ENNReal.ofReal (Real.exp (-u))*G.adjustedBandCount a (-u) (-l) ω y ≤
        ∑' x, G.adjustedBandTransport a l u ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) := by
      rw [adjustedBandCount,←ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum (fun x => (G.adjustedBandTransport_weight_bounds hc hl a l u ω x y).1)
    calc
      _ = ENNReal.ofReal (a y)*(∫⁻ ω, ENNReal.ofReal (Real.exp (-u))*
          G.adjustedBandCount a (-u) (-l) ω y ∂G.law p) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono hb)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _hy
    have hb (ω : Set E) :
        (∑' x, G.adjustedBandTransport a l u ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) ≤
          ENNReal.ofReal (Real.exp (-l))*G.adjustedBandCount a (-u) (-l) ω y := by
      rw [adjustedBandCount,←ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum (fun x => (G.adjustedBandTransport_weight_bounds hc hl a l u ω x y).2)
    calc
      _ ≤ ENNReal.ofReal (a y)*(∫⁻ ω, ENNReal.ofReal (Real.exp (-l))*
          G.adjustedBandCount a (-u) (-l) ω y ∂G.law p) := mul_le_mul' le_rfl (lintegral_mono hb)
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; ring

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

lemma disjointOccurrence_restrict (I : Set E) (A B : Set (Set E)) :
    (fun ω : Set E => ω ∩ I) ⁻¹' DisjointOccurrence A B ⊆
      DisjointOccurrence ((fun ω : Set E => ω ∩ I) ⁻¹' A)
        ((fun ω : Set E => ω ∩ I) ⁻¹' B) := by
  rintro ω ⟨s,t,hs,ht,hd,ha,hb⟩
  have hsI : (s : Set E) ⊆ I := fun e he => (hs he).2
  have htI : (t : Set E) ⊆ I := fun e he => (ht he).2
  refine ⟨s,t,fun e he => (hs he).1,fun e he => (ht he).1,hd,?_,?_⟩
  · change (s : Set E) ∩ I ∈ A
    rwa [Set.inter_eq_self_of_subset_left hsI]
  · change (t : Set E) ∩ I ∈ B
    rwa [Set.inter_eq_self_of_subset_left htI]

lemma conn_restricted_three_disjoint_arms (I : Set E) (ω : Set E) (x y z : V)
    (hxy : Conn G (ω ∩ I) x y) (hxz : Conn G (ω ∩ I) x z) :
    ∃ w, ω ∈ DisjointOccurrence {η | Conn G (η ∩ I) x w}
      (DisjointOccurrence {η | Conn G (η ∩ I) w y} {η | Conn G (η ∩ I) w z}) := by
  obtain ⟨w,hw⟩ := conn_three_disjoint_arms G (ω ∩ I) x y z hxy hxz
  refine ⟨w,?_⟩
  have hh := disjointOccurrence_restrict I {η | Conn G η x w}
    (DisjointOccurrence {η | Conn G η w y} {η | Conn G η w z}) hw
  exact disjointOccurrence_mono (Set.Subset.refl _)
    (disjointOccurrence_restrict I _ _) hh

lemma finiteWitness_conn_restricted (I : Set E) (x y : V) :
    FiniteWitness {ω | Conn G (ω ∩ I) x y} := by
  intro ω hω
  obtain ⟨s,hs,hconn⟩ := finiteWitness_conn G x y (ω ∩ I) hω
  refine ⟨s,fun e he => (hs he).1,?_⟩
  have hsub : (s : Set E) ⊆ (s : Set E) ∩ I := fun e he => ⟨he,(hs he).2⟩
  exact conn_mono G hsub hconn

lemma restricted_three_arm_bound [Countable V] [Countable E]
    (I : Set E) (p : unitInterval) (x y z : V) :
    law p {ω | Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ I) x z} ≤
      ∑' w, law p {ω | Conn G (ω ∩ I) x w} *
        law p {ω | Conn G (ω ∩ I) w y} * law p {ω | Conn G (ω ∩ I) w z} := by
  let C := fun a b : V => {ω : Set E | Conn G (ω ∩ I) a b}
  have hup (a b : V) : IsUpperSet (C a b) :=
    fun _ _ h hconn => conn_mono G (Set.inter_subset_inter_left _ h) hconn
  have hf (a b : V) : FiniteWitness (C a b) := finiteWitness_conn_restricted G I a b
  have hb (w : V) : law p (DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) ≤
      law p (C x w)*law p (C w y)*law p (C w z) := by
    calc
      _ ≤ law p (C x w)*law p (DisjointOccurrence (C w y) (C w z)) :=
        bk_ennreal p _ _ (hup x w) (disjointOccurrence_upper _ _) (hf x w)
          (finiteWitness_disjointOccurrence _ _)
      _ ≤ law p (C x w)*(law p (C w y)*law p (C w z)) :=
        mul_le_mul' le_rfl (bk_ennreal p _ _ (hup w y) (hup w z) (hf w y) (hf w z))
      _ = _ := (mul_assoc _ _ _).symm
  calc
    _ ≤ law p (⋃ w, DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) := by
      apply measure_mono
      intro ω hω
      obtain ⟨w,hw⟩ := conn_restricted_three_disjoint_arms G I ω x y z hω.1 hω.2
      exact Set.mem_iUnion.mpr ⟨w,hw⟩
    _ ≤ ∑' w, law p (DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) :=
      measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum hb

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

lemma restrictedLayerCount_mul (I : Set E) (A B : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G I A ω x * restrictedLayerCount G I B ω x =
      ∑' y, ∑' z, if y ∈ A ∧ z ∈ B ∧ Conn G (ω ∩ I) x y ∧
        Conn G (ω ∩ I) x z then (1 : ℝ≥0∞) else 0 := by
  unfold restrictedLayerCount
  rw [←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro y
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  split_ifs <;> simp_all

lemma lintegral_restrictedLayerCount_mul [Countable V] [Countable E]
    (I : Set E) (A B : Set V) (p : unitInterval) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x*restrictedLayerCount G I B ω x ∂law p) =
      ∑' y, ∑' z, if y ∈ A ∧ z ∈ B then law p
        {ω | Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ I) x z} else 0 := by
  have hi : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  have hset (y z : V) : MeasurableSet
      {ω : Set E | Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ I) x z} :=
    ((measurableSet_conn G x y).preimage hi).inter ((measurableSet_conn G x z).preimage hi)
  have hm (y z : V) : Measurable (fun ω : Set E =>
      if y ∈ A ∧ z ∈ B ∧ Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ I) x z
      then (1 : ℝ≥0∞) else 0) := by
    by_cases h : y ∈ A ∧ z ∈ B
    · simpa only [←and_assoc,h,true_and] using
        Measurable.ite (hset y z) measurable_const measurable_const
    · have he : (fun ω : Set E => if y ∈ A ∧ z ∈ B ∧ Conn G (ω ∩ I) x y ∧
          Conn G (ω ∩ I) x z then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
        funext ω
        exact ite_eq_right (by tauto)
      rw [he]
      exact measurable_const
  simp_rw [restrictedLayerCount_mul]
  rw [lintegral_tsum (fun y => (Measurable.tsum (hm y)).aemeasurable)]
  apply tsum_congr
  intro y
  rw [lintegral_tsum (fun z => (hm y z).aemeasurable)]
  apply tsum_congr
  intro z
  by_cases h : y ∈ A ∧ z ∈ B
  · simp only [←and_assoc,h,true_and,if_true]
    simpa only [Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
      lintegral_indicator_one (μ := law p) (hset y z)
  · simp only [ite_eq_right h]
    have he : (fun ω : Set E => if y ∈ A ∧ z ∈ B ∧ Conn G (ω ∩ I) x y ∧
        Conn G (ω ∩ I) x z then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
      funext ω
      exact ite_eq_right (by tauto)
    rw [he,lintegral_zero]

theorem restricted_layer_second_moment [Countable V] [Countable E]
    (I : Set E) (A B : Set V) (p : unitInterval) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x*restrictedLayerCount G I B ω x ∂law p) ≤
      ∑' w, law p {ω | Conn G (ω ∩ I) x w} *
        (∫⁻ ω, restrictedLayerCount G I A ω w ∂law p) *
          (∫⁻ ω, restrictedLayerCount G I B ω w ∂law p) := by
  simp_rw [lintegral_restrictedLayerCount_mul,lintegral_restrictedLayerCount]
  calc
    _ ≤ ∑' y, ∑' z, ∑' w, law p {ω | Conn G (ω ∩ I) x w} *
        (if y ∈ A then law p {ω | Conn G (ω ∩ I) w y} else 0) *
        (if z ∈ B then law p {ω | Conn G (ω ∩ I) w z} else 0) := by
      apply ENNReal.tsum_le_tsum
      intro y
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases h : y ∈ A ∧ z ∈ B
      · simp only [ite_eq_left h,ite_eq_left h.1,ite_eq_left h.2]
        exact restricted_three_arm_bound G I p x y z
      · simp only [ite_eq_right h]
        exact bot_le
    _ = ∑' w, ∑' y, ∑' z, law p {ω | Conn G (ω ∩ I) x w} *
        (if y ∈ A then law p {ω | Conn G (ω ∩ I) w y} else 0) *
        (if z ∈ B then law p {ω | Conn G (ω ∩ I) w z} else 0) := by
      rw [show (∑' y, ∑' z, ∑' w, law p {ω | Conn G (ω ∩ I) x w} *
          (if y ∈ A then law p {ω | Conn G (ω ∩ I) w y} else 0) *
          (if z ∈ B then law p {ω | Conn G (ω ∩ I) w z} else 0)) =
        ∑' y, ∑' w, ∑' z, law p {ω | Conn G (ω ∩ I) x w} *
          (if y ∈ A then law p {ω | Conn G (ω ∩ I) w y} else 0) *
          (if z ∈ B then law p {ω | Conn G (ω ∩ I) w z} else 0) from
          tsum_congr (fun _ => ENNReal.tsum_comm),ENNReal.tsum_comm]
    _ = _ := by simp_rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BandMomentSummability
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

lemma adjustedBandCount_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x : V) :
    G.adjustedBandCount a l u (φ.edge '' ω) (φ.vertex x) =
      G.adjustedBandCount a l u ω x := by
  unfold adjustedBandCount
  rw [←φ.vertex.tsum_eq]
  simp only [G.adjustedBandTransport_aut a ha l u]

variable [Countable V] [Countable E]

lemma measurable_adjustedBandCount (a : V → ℝ) (l u : ℝ) (x : V) :
    Measurable (fun ω => G.adjustedBandCount a l u ω x) :=
  Measurable.tsum fun y => G.measurable_adjustedBandTransport a l u x y

lemma expected_adjustedBandCount_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (p : unitInterval) (x : V) :
    (∫⁻ ω, G.adjustedBandCount a l u ω (φ.vertex x) ∂G.law p) =
      ∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [lintegral_map (G.measurable_adjustedBandCount a l u _)
    (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [G.adjustedBandCount_aut a ha l u]

lemma expected_band_le_weighted_roots (O : G.OrbitRepresentatives)
    (a : V → ℝ) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (p : unitInterval) (l u : ℝ) (x : V) :
    (∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p) ≤
      (ENNReal.ofReal m)⁻¹ * ∑ r ∈ O.roots, ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedBandCount a l u ω r ∂G.law p) := by
  have hh : ENNReal.ofReal m*(∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p) ≤
      ∑ r ∈ O.roots, ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedBandCount a l u ω r ∂G.law p) := by
    obtain ⟨r,hr,φ,rfl⟩ := O.cover x
    rw [G.expected_adjustedBandCount_aut a ha l u φ p r]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (ham r)) le_rfl).trans
      (Finset.single_le_sum (f := fun r => ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedBandCount a l u ω r ∂G.law p)) (fun _ _ => bot_le) hr)
  calc
    _ = (ENNReal.ofReal m)⁻¹*(ENNReal.ofReal m*
        (∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p)) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hm))
        ENNReal.ofReal_ne_top,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hh

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerMaximumDecomposition
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

omit [Countable V] [Countable E] in
lemma adjustedFullLayerMoment_le_sup (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (i : ℤ) (x : V) (u : ℝ) :
    G.adjustedFullLayerMoment a R p i x u ≤ G.supAdjustedFullLayerMoment a R p i :=
  le_iSup_of_le x (le_iSup_of_le u le_rfl)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FullLayerProfile
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

theorem supAdjustedFullLayerMoment_le_row_bound
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C) (i : ℤ) :
    G.supAdjustedFullLayerMoment a R p i ≤ C := by
  apply iSup_le
  intro x
  apply iSup_le
  intro u
  exact restrictedLayerCount_expectation_le_row_bound G.ends p C hrow _ _ x

theorem adjustedFullLayerMoment_up_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (x : V) (u : ℝ) :
    G.adjustedFullLayerMoment a R p (n : ℤ) x u ≤ G.supAdjustedUpLayerMoment a R p n*C := by
  by_cases hn : n=0
  · subst n
    have hz : (1 : ℝ≥0∞) ≤ G.supAdjustedUpLayerMoment a R p 0 :=
      (G.adjustedUpLayerMoment_zero_ge_one a R p x u).trans (G.adjustedUpLayerMoment_le_sup a R p 0 x u)
    exact ((G.adjustedFullLayerMoment_le_sup a R p 0 x u).trans
      (G.supAdjustedFullLayerMoment_le_row_bound a R p C hrow 0)).trans
        ((one_mul C).symm.le.trans (mul_le_mul' hz le_rfl))
  let f := G.adjustedLayerIndex a R u x
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R u hR hjump x v w e hv hw
    change f v-1 ≤ f w ∧ f w ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by
    simp only [f,G.adjustedLayerIndex_self]
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hA : ∀ y ∈ {v | f v=(n : ℤ)}, (n : ℤ) ≤ f y := fun _ h => h.ge
  exact (first_layer_moment_bound_with_row G.ends p C hrow f hj Set.univ _ x n hx hA).trans
    (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p n x u) le_rfl)

theorem supAdjustedFullLayerMoment_up_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C) (n : ℕ) :
    G.supAdjustedFullLayerMoment a R p (n : ℤ) ≤ G.supAdjustedUpLayerMoment a R p n*C := by
  apply iSup_le
  intro x
  apply iSup_le
  intro u
  exact G.adjustedFullLayerMoment_up_bound hc hl a R hR hjump p C hrow n x u

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FullNegativeLayerProfile
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

lemma fullLayerCount_le_bandCount (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (i : ℤ) (x : V) (u : ℝ) (ω : Set E) :
    restrictedLayerCount G.ends Set.univ {y | G.adjustedLayerIndex a R u x y=i} ω x ≤
      G.adjustedBandCount a (R*((i : ℝ)-1)) (R*((i : ℝ)+1)) ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : G.adjustedLayerIndex a R u x y=i ∧ Percolation.Conn G.ends (ω ∩ Set.univ) x y
  · have hh := G.adjustedLayerIndex_height_bounds a R u hR x y
    rw [hy.1] at hh
    have hc : y ∈ G.cluster ω x := by
      change y ∈ (criticalModel G.ends).cluster ω x
      rw [criticalModel_cluster]
      exact Percolation.conn_mono G.ends Set.inter_subset_left hy.2
    have ht : y ∈ G.cluster ω x ∧
        R*((i : ℝ)-1) ≤ G.orbitAdjustedHeight a x y ∧
          G.orbitAdjustedHeight a x y ≤ R*((i : ℝ)+1) :=
      ⟨hc,hh.1.le,hh.2.le⟩
    simp only [Set.mem_ofPred_eq,ite_eq_left hy,adjustedBandTransport,ite_eq_left ht,le_refl]
  · simp only [Set.mem_ofPred_eq,ite_eq_right hy]
    exact bot_le

variable [Countable V] [Countable E]

lemma expected_bandCount_le_intermediate_upLayerMoment
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (hn : 0 < n) (x : V) (l u : ℝ) (hlower : R*n ≤ l) :
    (∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p) ≤ G.adjustedUpLayerMoment a R p n x 0*C := by
  have he (ω : Set E) : G.adjustedBandCount a l u ω x =
      restrictedLayerCount G.ends Set.univ
        {y | l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u} ω x := by
    apply tsum_congr
    intro y
    have hc : y ∈ G.cluster ω x ↔ Percolation.Conn G.ends ω x y := by
      change y ∈ (criticalModel G.ends).cluster ω x ↔ _
      rw [criticalModel_cluster]
      rfl
    simp only [adjustedBandTransport,Set.inter_univ,Set.mem_ofPred_eq,hc]
    congr 1
    apply propext
    tauto
  simp_rw [he]
  let f := G.adjustedLayerIndex a R 0 x
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R 0 hR hjump x v w e hv hw
    change f v-1 ≤ f w ∧ f w ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by simp only [f,G.adjustedLayerIndex_self]; exact_mod_cast hn
  have hA : ∀ y ∈ {v | l ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ u},
      (n : ℤ) ≤ f y := by
    intro y hy
    simp only [f,adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero]
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hR).mpr
    push_cast
    nlinarith [hy.1]
  exact first_layer_moment_bound_with_row G.ends p C hrow f hj Set.univ _ x n hx hA

theorem adjustedFullLayerMoment_negative_bound
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (hn : 3 ≤ n) (x : V) (u : ℝ) :
    G.adjustedFullLayerMoment a R p (-(n : ℤ)) x u ≤
      ((ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r)))*
        ENNReal.ofReal (Real.exp (R*((n : ℝ)+1)))*(G.supAdjustedUpLayerMoment a R p (n-2)*C) := by
  let l := -(R*((n : ℝ)+1))
  let v := -(R*((n : ℝ)-1))
  have hmin : R*(n-2 : ℕ) ≤ -v := by
    dsimp [v]
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    nlinarith
  have hroot (r : V) : (∫⁻ ω, G.adjustedBandCount a (-v) (-l) ω r ∂G.law p) ≤
      G.supAdjustedUpLayerMoment a R p (n-2)*C :=
    (G.expected_bandCount_le_intermediate_upLayerMoment hc hl a R hR hjump p C hrow
      (n-2) (by omega) r (-v) (-l) hmin).trans
        (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p (n-2) r 0) le_rfl)
  have hsum : (∑ r ∈ O.roots, ENNReal.ofReal (a r)*
      (∫⁻ ω, G.adjustedBandCount a (-v) (-l) ω r ∂G.law p)) ≤
        (∑ r ∈ O.roots, ENNReal.ofReal (a r))*(G.supAdjustedUpLayerMoment a R p (n-2)*C) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun r _ => mul_le_mul' le_rfl (hroot r)
  calc
    _ ≤ ∫⁻ ω, G.adjustedBandCount a l v ω x ∂G.law p := by
      have hleft : R*(((-(n : ℤ)) : ℝ)-1)=l := by
        dsimp [l]
        push_cast
        ring
      have hright : R*(((-(n : ℤ)) : ℝ)+1)=v := by
        dsimp [v]
        push_cast
        ring
      unfold adjustedFullLayerMoment
      apply lintegral_mono
      intro ω
      have hh := G.fullLayerCount_le_bandCount a R hR (-(n : ℤ)) x u ω
      simp only [Int.cast_neg] at hh
      rw [hleft,hright] at hh
      exact hh
    _ ≤ (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedBandCount a l v ω r ∂G.law p)) :=
      G.expected_band_le_weighted_roots O a ha m hm ham p l v x
    _ ≤ (ENNReal.ofReal m)⁻¹*(ENNReal.ofReal (Real.exp (-l))*
        ((∑ r ∈ O.roots, ENNReal.ofReal (a r))*(G.supAdjustedUpLayerMoment a R p (n-2)*C))) :=
      mul_le_mul' le_rfl (((G.expected_adjustedBandCount_reciprocity O hc hl a hapos ha p l v).2).trans
        (mul_le_mul' le_rfl hsum))
    _ = _ := by dsimp only [l]; rw [neg_neg]; ring

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerSecondMomentDecomposition
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

theorem adjusted_full_layer_second_moment_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (x : V) (u : ℝ) (k l : ℤ) :
    (∫⁻ ω, restrictedLayerCount G.ends Set.univ
        {y | G.adjustedLayerIndex a R u x y=k} ω x *
      restrictedLayerCount G.ends Set.univ
        {y | G.adjustedLayerIndex a R u x y=l} ω x ∂G.law p) ≤
      ∑' i : ℤ, G.supAdjustedFullLayerMoment a R p i *
        G.supAdjustedFullLayerMoment a R p (k-i) * G.supAdjustedFullLayerMoment a R p (l-i) := by
  let f := G.adjustedLayerIndex a R u x
  let T (z : V) := G.law p {ω | Percolation.Conn G.ends (ω ∩ Set.univ) x z}
  have hcont (z : V) (j : ℤ) :
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=j} ω z ∂G.law p) ≤
        G.supAdjustedFullLayerMoment a R p (j-f z) := by
    let v := G.orbitAdjustedHeight a x z/R+u
    have hidx (y : V) : f y=f z+G.adjustedLayerIndex a R v z y :=
      G.adjustedLayerIndex_change_base hc hl a R u x z y
    have htar : {y : V | f y=j}={y | G.adjustedLayerIndex a R v z y=j-f z} := by
      ext y
      change f y=j ↔ G.adjustedLayerIndex a R v z y=j-f z
      rw [hidx]
      omega
    rw [htar]
    exact G.adjustedFullLayerMoment_le_sup a R p _ z v
  have hrow (i : ℤ) : (∑' z, if f z=i then T z else 0) ≤ G.supAdjustedFullLayerMoment a R p i := by
    apply le_trans _ (G.adjustedFullLayerMoment_le_sup a R p i x u)
    rw [adjustedFullLayerMoment]
    change _ ≤ ∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=i} ω x ∂Percolation.law p
    rw [lintegral_restrictedLayerCount]
    apply ENNReal.tsum_le_tsum
    intro z
    by_cases hz : f z=i <;>
      simp only [Set.mem_ofPred_eq,hz,if_true,if_false,T,law,Percolation.law,le_refl]
  calc
    _ ≤ ∑' z, T z *
        (∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=k} ω z ∂G.law p) *
          (∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=l} ω z ∂G.law p) :=
      restricted_layer_second_moment G.ends Set.univ _ _ p x
    _ ≤ ∑' z, T z*G.supAdjustedFullLayerMoment a R p (k-f z)*
        G.supAdjustedFullLayerMoment a R p (l-f z) := by
      apply ENNReal.tsum_le_tsum
      intro z
      exact mul_le_mul' (mul_le_mul' le_rfl (hcont z k)) (hcont z l)
    _ ≤ ∑' z, ∑' i : ℤ, if f z=i then
        T z*G.supAdjustedFullLayerMoment a R p (k-i)*G.supAdjustedFullLayerMoment a R p (l-i)
        else 0 := by
      apply ENNReal.tsum_le_tsum
      intro z
      have ht := ENNReal.le_tsum (f := fun i : ℤ => if f z=i then
        T z*G.supAdjustedFullLayerMoment a R p (k-i)*G.supAdjustedFullLayerMoment a R p (l-i)
        else 0) (f z)
      rwa [ite_eq_left (rfl : f z=f z)] at ht
    _ = ∑' i : ℤ, (∑' z, if f z=i then T z else 0)*
        G.supAdjustedFullLayerMoment a R p (k-i)*G.supAdjustedFullLayerMoment a R p (l-i) := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro i
      rw [←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_right]
      apply tsum_congr
      intro z
      by_cases hz : f z=i <;> simp only [hz,if_true,if_false,zero_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact mul_le_mul' (mul_le_mul' (hrow i) le_rfl) le_rfl

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerMomentCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma lintegral_support_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f)
    (A : Set Ω) (hA : MeasurableSet A) (hzero : ∀ ω, ω ∉ A → f ω=0) :
    (∫⁻ ω, f ω ∂μ)^2 ≤ μ A*(∫⁻ ω, (f ω)^2 ∂μ) := by
  let g := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hg : Measurable g := measurable_const.indicator hA
  have hfg : (fun ω => f ω*g ω)=f := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [g,Set.indicator_of_mem hω,mul_one]
    · simp only [g,Set.indicator_of_notMem hω,mul_zero,hzero ω hω]
  have hgg : (fun ω => (g ω)^2)=g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [g,hω]
  have hgm : (∫⁻ ω, g ω ∂μ)=μ A := lintegral_indicator_one hA
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf.aemeasurable hg.aemeasurable
  simp only [Pi.mul_apply,hfg,ENNReal.rpow_two,hgg,hgm] at hh
  have hsqrt (z : ℝ≥0∞) : (z^((1 : ℝ)/2))^2=z := by
    rw [←ENNReal.rpow_two,←ENNReal.rpow_mul]
    norm_num
  have hh2 := pow_le_pow_left' hh 2
  rw [mul_pow,hsqrt,hsqrt,mul_comm] at hh2
  exact hh2

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SubcriticalFullLayerProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma symmetric_exponential_profile (F : ℤ → ℝ≥0∞) (χ K D R β : ℝ)
    (hχ : 0 ≤ χ) (hK : 0 ≤ K) (hD : 0 ≤ D) (hR : 0 < R) (hβ : R < β)
    (hbase : ∀ i, F i ≤ ENNReal.ofReal χ)
    (hup : ∀ n : ℕ, F n ≤ ENNReal.ofReal (K*χ*Real.exp (-β*n)))
    (hdown : ∀ n : ℕ, 3 ≤ n → F (-(n : ℤ)) ≤
      ENNReal.ofReal (D*K*χ*Real.exp (R+2*β)*Real.exp (-(β-R)*n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℤ,
      F i ≤ ENNReal.ofReal (C*Real.exp (-(β-R)*|(i : ℝ)|)) := by
  let a := β-R
  have ha : 0 < a := sub_pos.mpr hβ
  let M := χ+K*χ+D*K*χ*Real.exp (R+2*β)+1
  have hprod : 0 ≤ D*K*χ*Real.exp (R+2*β) := by positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hχM : χ ≤ M := by dsimp [M]; nlinarith [mul_nonneg hK hχ]
  have hKM : K*χ ≤ M := by dsimp [M]; linarith
  have hDM : D*K*χ*Real.exp (R+2*β) ≤ M := by
    dsimp [M]
    linarith [mul_nonneg hK hχ]
  have hexp : (1 : ℝ) ≤ Real.exp (2*a) := Real.one_le_exp_iff.mpr (by positivity)
  have hMC : M ≤ M*Real.exp (2*a) := by nlinarith
  have hpos (n : ℕ) : F (n : ℤ) ≤
      ENNReal.ofReal (M*Real.exp (2*a)*Real.exp (-a*n)) := by
    apply (hup n).trans
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-β*n) ≤ Real.exp (-a*n) := by
      apply Real.exp_le_exp.mpr
      dsimp [a]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact (mul_le_mul (hKM.trans hMC) he (Real.exp_nonneg _) (by positivity))
  have hneg (n : ℕ) : F (-(n : ℤ)) ≤
      ENNReal.ofReal (M*Real.exp (2*a)*Real.exp (-a*n)) := by
    by_cases hn : 3 ≤ n
    · exact (hdown n hn).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hDM.trans hMC) (Real.exp_nonneg _)))
    · apply (hbase _).trans
      apply ENNReal.ofReal_le_ofReal
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
      have he : (1 : ℝ) ≤ Real.exp (2*a-a*n) :=
        Real.one_le_exp_iff.mpr (by nlinarith)
      rw [mul_assoc,←Real.exp_add]
      have heq : 2*a + -a*(n : ℝ)=2*a-a*n := by ring
      rw [heq]
      exact hχM.trans (by nlinarith)
  refine ⟨M*Real.exp (2*a),by positivity,?_⟩
  intro i
  cases i with
  | ofNat n =>
    change F (n : ℤ) ≤ ENNReal.ofReal (M*Real.exp (2*a)*Real.exp (-a*|(n : ℝ)|))
    simpa only [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hpos n
  | negSucc n =>
    have hi : Int.negSucc n = -((n+1 : ℕ) : ℤ) := rfl
    simpa only [hi,Int.cast_neg,Int.cast_natCast,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (n+1) : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))] using hneg (n+1)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SubcriticalLayerConvolution
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

theorem expAbsLayerKernel_tsum_lt_top {a : ℝ} (ha : 0 < a) :
    (∑' i : ℤ, expAbsLayerKernel a i) < ⊤ := by
  have hn : Summable (fun n : ℕ => Real.exp ((n : ℝ)*(-a))) :=
    Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha)
  have hs : Summable (fun i : ℤ => Real.exp (-a*|(i : ℝ)|)) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor
    · convert hn using 1
      all_goals try with_reducible_and_instances rfl
      funext n
      simp only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      congr 1
      ring
    · convert hn using 1
      all_goals try with_reducible_and_instances rfl
      funext n
      simp only [Int.cast_neg,Int.cast_natCast,abs_neg,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      congr 1
      ring
  exact hs.tsum_ofReal_lt_top

lemma three_layer_abs_bound (k l : ℕ) (i : ℝ) :
    ((max k l : ℕ) : ℝ)+|i+(min k l : ℕ)| ≤ |i|+|-(k : ℝ)-i|+|-(l : ℝ)-i| := by
  have hneg (r : ℕ) : |-(r : ℝ)-i| = |i+r| := by
    rw [show -(r : ℝ)-i = -(i+r) by ring,abs_neg]
  rw [hneg k,hneg l]
  have htriangle (r : ℕ) : (r : ℝ) ≤ |i|+|i+r| := by
    have hh := abs_add_le (-i) (i+(r : ℝ))
    rw [show -i+(i+(r : ℝ)) = (r : ℝ) by ring,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] at hh
    exact hh
  by_cases hkl : k ≤ l
  · rw [max_eq_right hkl,min_eq_left hkl]
    linarith [htriangle l]
  · rw [max_eq_left (le_of_not_ge hkl),min_eq_right (le_of_not_ge hkl)]
    linarith [htriangle k]

theorem expAbsLayerKernel_triple_bound {a : ℝ} (ha : 0 ≤ a)
    (k l : ℕ) (i : ℤ) :
    expAbsLayerKernel a i * expAbsLayerKernel a (-(k : ℤ)-i) *
        expAbsLayerKernel a (-(l : ℤ)-i) ≤
      ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ))) *
        expAbsLayerKernel a (i+(min k l : ℕ)) := by
  unfold expAbsLayerKernel
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←ENNReal.ofReal_mul (mul_nonneg
    (Real.exp_nonneg _) (Real.exp_nonneg _)),←ENNReal.ofReal_mul (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Int.cast_sub,Int.cast_neg,Int.cast_natCast,Int.cast_add]
  have hh := mul_le_mul_of_nonneg_left (three_layer_abs_bound k l (i : ℝ)) ha
  linarith

theorem expAbsLayerKernel_triple_sum_bound {a : ℝ} (ha : 0 ≤ a) (k l : ℕ) :
    (∑' i : ℤ, expAbsLayerKernel a i * expAbsLayerKernel a (-(k : ℤ)-i) *
      expAbsLayerKernel a (-(l : ℤ)-i)) ≤
      ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ))) * ∑' i : ℤ, expAbsLayerKernel a i := by
  apply (ENNReal.tsum_le_tsum (expAbsLayerKernel_triple_bound ha k l)).trans_eq
  rw [ENNReal.tsum_mul_left]
  congr 1
  exact (Equiv.addRight ((min k l : ℕ) : ℤ)).tsum_eq (expAbsLayerKernel a)

theorem subcritical_three_profile_convolution {a : ℝ} (ha : 0 ≤ a)
    (C : ℝ≥0∞) (f g h : ℤ → ℝ≥0∞)
    (hf : ∀ i, f i ≤ C*expAbsLayerKernel a i)
    (hg : ∀ i, g i ≤ C*expAbsLayerKernel a i)
    (hh : ∀ i, h i ≤ C*expAbsLayerKernel a i) (k l : ℕ) :
    (∑' i : ℤ, f i*g (-(k : ℤ)-i)*h (-(l : ℤ)-i)) ≤
      C^3*ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ))) *
        ∑' i : ℤ, expAbsLayerKernel a i := by
  calc
    _ ≤ ∑' i : ℤ, C^3*(expAbsLayerKernel a i * expAbsLayerKernel a (-(k : ℤ)-i) *
        expAbsLayerKernel a (-(l : ℤ)-i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      calc
        _ ≤ (C*expAbsLayerKernel a i)*(C*expAbsLayerKernel a (-(k : ℤ)-i))*
            (C*expAbsLayerKernel a (-(l : ℤ)-i)) :=
          mul_le_mul' (mul_le_mul' (hf i) (hg _)) (hh _)
        _ = _ := by ring
    _ ≤ C^3*(ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ)))*
        ∑' i : ℤ, expAbsLayerKernel a i) := by
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul' le_rfl (expAbsLayerKernel_triple_sum_bound ha k l)
    _ = _ := (mul_assoc _ _ _).symm

theorem subcritical_three_profile_uniform_bound {a : ℝ} (ha : 0 < a)
    (C : ℝ≥0∞) (hC : C < ⊤) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (f g h : ℤ → ℝ≥0∞),
      (∀ i, f i ≤ C*expAbsLayerKernel a i) →
      (∀ i, g i ≤ C*expAbsLayerKernel a i) →
      (∀ i, h i ≤ C*expAbsLayerKernel a i) → ∀ k l : ℕ,
      (∑' i : ℤ, f i*g (-(k : ℤ)-i)*h (-(l : ℤ)-i)) ≤
        K*ENNReal.ofReal (Real.exp (-a*((max k l : ℕ) : ℝ))) := by
  refine ⟨C^3*(∑' i : ℤ, expAbsLayerKernel a i),?_,?_⟩
  · apply ENNReal.mul_lt_top _ (expAbsLayerKernel_tsum_lt_top ha)
    simpa only [pow_succ,pow_zero,one_mul] using
      ENNReal.mul_lt_top (ENNReal.mul_lt_top hC hC) hC
  · intro f g h hf hg hh k l
    exact (subcritical_three_profile_convolution ha.le C f g h hf hg hh k l).trans_eq
      (by ring)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerProfileAtRate
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

theorem subcritical_full_layer_profile_at_rate
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hpc : p < pc G) (β K : ℝ) (hβ : R < β) (hK : 0 < K)
    (hup : ∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
      ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℤ,
      (criticalModel G).supAdjustedFullLayerMoment ((criticalModel G).stationaryOrbitWeight μ) R p i ≤
        ENNReal.ofReal (C*Real.exp (-(β-R)*|(i : ℝ)|)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq p hpc
  obtain ⟨m,M,hm,hweights⟩ := H.stationaryOrbitWeight_uniform_bounds hHc hl μ hμ
  let O := H.orbitRepresentatives hHq
  let D : ℝ≥0∞ := (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hm))
    (ENNReal.sum_ne_top.mpr fun r _ => ENNReal.ofReal_ne_top)
  have hDEq : ENNReal.ofReal D.toReal=D := ENNReal.ofReal_toReal hD
  have hbase (i : ℤ) : H.supAdjustedFullLayerMoment a R p i ≤ ENNReal.ofReal χ :=
    H.supAdjustedFullLayerMoment_le_row_bound a R p _ hrow i
  have hpositive (n : ℕ) : H.supAdjustedFullLayerMoment a R p n ≤
      ENNReal.ofReal (K*χ*Real.exp (-β*n)) := by
    apply (H.supAdjustedFullLayerMoment_up_bound hHc hl a R hR hjump p _ hrow n).trans
    apply (mul_le_mul' (hup n) le_rfl).trans_eq
    rw [←ENNReal.ofReal_mul (mul_nonneg hK.le (Real.exp_nonneg _))]
    congr 1
    ring
  have hnegative (n : ℕ) (hn : 3 ≤ n) : H.supAdjustedFullLayerMoment a R p (-(n : ℤ)) ≤
      ENNReal.ofReal (D.toReal*K*χ*Real.exp (R+2*β)*Real.exp (-(β-R)*n)) := by
    have hb : H.supAdjustedFullLayerMoment a R p (-(n : ℤ)) ≤
        D*ENNReal.ofReal (Real.exp (R*((n : ℝ)+1)))*
          (H.supAdjustedUpLayerMoment a R p (n-2)*ENNReal.ofReal χ) := by
      apply iSup_le
      intro x
      apply iSup_le
      intro u
      exact H.adjustedFullLayerMoment_negative_bound O hHc hl a
        (H.stationaryOrbitWeight_pos hHc hl μ hμ) (H.stationaryOrbitWeight_aut μ)
        m hm (fun x => (hweights x).1) R hR hjump p _ hrow n hn x u
    apply hb.trans
    apply (mul_le_mul' le_rfl (mul_le_mul' (hup (n-2)) le_rfl)).trans_eq
    nth_rw 1 [←hDEq]
    rw [←ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ←ENNReal.ofReal_mul (mul_nonneg hK.le (Real.exp_nonneg _)),
      ←ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _))]
    congr 1
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    rw [show D.toReal*Real.exp (R*((n : ℝ)+1))*(K*Real.exp (-β*((n : ℝ)-2))*χ) =
      D.toReal*K*χ*(Real.exp (R*((n : ℝ)+1))*Real.exp (-β*((n : ℝ)-2))) by ring,
      ←Real.exp_add,show R*((n : ℝ)+1)+ -β*((n : ℝ)-2) = R+2*β + (-(β-R)*(n : ℝ)) by ring,
      Real.exp_add]
    ring
  obtain ⟨C,hC,hprof⟩ := symmetric_exponential_profile
    (H.supAdjustedFullLayerMoment a R p) χ K D.toReal R β hχ hK.le ENNReal.toReal_nonneg
      hR hβ hbase hpositive hnegative
  exact ⟨C,hC,hprof⟩

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem adjusted_downward_layer_second_moment_at_rate
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (R : ℝ)
    (p : unitInterval) (β C : ℝ) (hβ : R < β) (hC : 0 < C)
    (hprofile : ∀ i : ℤ, G.supAdjustedFullLayerMoment a R p i ≤
      ENNReal.ofReal (C*Real.exp (-(β-R)*|(i : ℝ)|))) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (k l : ℕ) (x : V) (u : ℝ),
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R u x y = -(k : ℤ)} ω x *
        restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R u x y = -(l : ℤ)} ω x ∂G.law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ))) := by
  have hprof (i : ℤ) : G.supAdjustedFullLayerMoment a R p i ≤
      ENNReal.ofReal C*expAbsLayerKernel (β-R) i := by
    simpa only [expAbsLayerKernel,ENNReal.ofReal_mul hC.le] using hprofile i
  obtain ⟨K,hK,hconv⟩ := subcritical_three_profile_uniform_bound (sub_pos.mpr hβ)
    (ENNReal.ofReal C) ENNReal.ofReal_lt_top
  refine ⟨K,hK,fun k l x u => ?_⟩
  exact (G.adjusted_full_layer_second_moment_bound hc hl a R p x u
    (-(k : ℤ)) (-(l : ℤ))).trans
      (hconv (G.supAdjustedFullLayerMoment a R p) (G.supAdjustedFullLayerMoment a R p)
        (G.supAdjustedFullLayerMoment a R p) hprof hprof hprof k l)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSurgeryProbability
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

lemma measurableSet_strictHeightPeakConnection [Countable V] [Countable E]
    (f : V → ℝ) (x z : V) : MeasurableSet (strictHeightPeakConnection G f x z) := by
  exact ((measurableSet_conn G x z).mem.and (Measurable.forall fun y =>
    (measurableSet_conn G z y).mem.imp (measurable_const.imp measurable_const))).setOf

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakBandProbability
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

lemma strictPeakBandEvent_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x : V) :
    φ.edge '' ω ∈ G.strictPeakBandEvent a l u (φ.vertex x) ↔
      ω ∈ G.strictPeakBandEvent a l u x := by
  have hconn (v w : V) : Percolation.Conn G.ends (φ.edge '' ω) (φ.vertex v) (φ.vertex w) ↔
      Percolation.Conn G.ends ω v w := by
    rw [←Percolation.conn_aut_iff G.ends φ.preserves,
      Set.preimage_image_eq _ φ.edge.injective]
  have hpeak (z : V) : φ.edge '' ω ∈ strictHeightPeakConnection G.ends
      (G.orbitAdjustedHeight a (φ.vertex x)) (φ.vertex x) (φ.vertex z) ↔
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a x) x z := by
    constructor
    · rintro ⟨h,hp⟩
      refine ⟨(hconn x z).mp h,fun y hy hyz => ?_⟩
      have hh := hp (φ.vertex y) ((hconn z y).mpr hy) (fun he => hyz (φ.vertex.injective he))
      simpa only [G.orbitAdjustedHeight_aut a ha] using hh
    · rintro ⟨h,hp⟩
      refine ⟨(hconn x z).mpr h,?_⟩
      intro y hy hyz
      obtain ⟨v,rfl⟩ := φ.vertex.surjective y
      have hh := hp v ((hconn z v).mp hy) (fun he => hyz (congrArg φ.vertex he))
      simpa only [G.orbitAdjustedHeight_aut a ha] using hh
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨v,rfl⟩ := φ.vertex.surjective z
    refine ⟨v,?_⟩
    simpa only [G.orbitAdjustedHeight_aut a ha,hpeak] using hz
  · rintro ⟨z,hz⟩
    refine ⟨φ.vertex z,?_⟩
    simpa only [G.orbitAdjustedHeight_aut a ha,hpeak] using hz

variable [Countable V] [Countable E]

lemma measurableSet_strictPeakBandEvent (a : V → ℝ) (l u : ℝ) (x : V) :
    MeasurableSet (G.strictPeakBandEvent a l u x) := by
  exact (Measurable.exists fun z => measurable_const.and
    (measurable_const.and (measurableSet_strictHeightPeakConnection G.ends _ x z).mem)).setOf

lemma strictPeakBandEvent_probability_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (p : unitInterval) (x : V) :
    G.law p (G.strictPeakBandEvent a l u (φ.vertex x)) =
      G.law p (G.strictPeakBandEvent a l u x) := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_strictPeakBandEvent a l u _)]
  congr 1
  ext ω
  exact G.strictPeakBandEvent_aut a ha l u φ ω x

lemma strictPeakBandEvent_probability_le_weighted_roots
    (O : G.OrbitRepresentatives) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (ham : ∀ x, m ≤ a x) (p : unitInterval) (l u : ℝ) (x : V) :
    ENNReal.ofReal m*G.law p (G.strictPeakBandEvent a l u x) ≤
      ∑ r ∈ O.roots, ENNReal.ofReal (a r)*G.law p (G.strictPeakBandEvent a l u r) := by
  obtain ⟨r,hr,φ,rfl⟩ := O.cover x
  rw [G.strictPeakBandEvent_probability_aut a ha l u φ p r]
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (ham r)) le_rfl).trans
    (Finset.single_le_sum (f := fun r => ENNReal.ofReal (a r)*G.law p (G.strictPeakBandEvent a l u r))
      (fun _ _ => bot_le) hr)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakBandTransport
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

lemma peakUpBandTransport_outgoing (a : V → ℝ) (l u : ℝ) (ω : Set E) (y : V) :
    (∑' x, G.peakUpBandTransport a l u ω y x) =
      (G.strictPeakBandEvent a l u y).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases he : ω ∈ G.strictPeakBandEvent a l u y
  · obtain ⟨z,hz⟩ := he
    rw [Set.indicator_of_mem (show ω ∈ G.strictPeakBandEvent a l u y from ⟨z,hz⟩),
      tsum_eq_single z]
    · exact ite_eq_left hz
    · intro x hxz
      apply ite_eq_right
      rintro ⟨_,_,hxy,hpeak⟩
      have hzx := Percolation.conn_trans G.ends ω (Percolation.conn_symm G.ends ω hz.2.2.1) hxy
      have hlt := hz.2.2.2 x hzx hxz
      have hlt' := hpeak z (Percolation.conn_symm G.ends ω hzx) (Ne.symm hxz)
      linarith
  · rw [Set.indicator_of_notMem he]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    exact ite_eq_right (fun hx => he ⟨x,hx⟩)

lemma peakUpBandTransport_incoming_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (l u : ℝ) (ω : Set E) (x y : V) :
    G.peakUpBandTransport a l u ω y x*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) ≤
      ENNReal.ofReal (Real.exp (-l))*G.peakUpBandTransport a l u ω y x := by
  by_cases h : l < G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ u ∧
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x
  · simp only [peakUpBandTransport,ite_eq_left h,one_mul,mul_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [G.orbitAdjustedHeight_reverse hc hl a y x]
    linarith [h.1]
  · simp only [peakUpBandTransport,ite_eq_right h,zero_mul,mul_zero,le_refl]

variable [Countable V] [Countable E]

lemma measurable_peakUpBandTransport (a : V → ℝ) (l u : ℝ) (y x : V) :
    Measurable (fun ω => G.peakUpBandTransport a l u ω y x) := by
  exact Measurable.ite (measurable_const.and (measurable_const.and
    (measurableSet_strictHeightPeakConnection G.ends _ y x).mem)).setOf
      measurable_const measurable_const

lemma measurable_peakDownBandCount (a : V → ℝ) (l u : ℝ) (x : V) :
    Measurable (fun ω => G.peakDownBandCount a l u ω x) :=
  Measurable.tsum fun y => G.measurable_peakUpBandTransport a l u y x

omit [Countable V] [Countable E] in
lemma peakUpBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (ω : Set E) (y x : V) :
    G.peakUpBandTransport a l u (φ.edge '' ω) (φ.vertex y) (φ.vertex x)=
      G.peakUpBandTransport a l u ω y x := by
  have hpeak : φ.edge '' ω ∈ strictHeightPeakConnection G.ends
      (G.orbitAdjustedHeight a (φ.vertex y)) (φ.vertex y) (φ.vertex x) ↔
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x := by
    have hconn (v w : V) : Percolation.Conn G.ends (φ.edge '' ω) (φ.vertex v) (φ.vertex w) ↔
        Percolation.Conn G.ends ω v w := by
      rw [←Percolation.conn_aut_iff G.ends φ.preserves,
        Set.preimage_image_eq _ φ.edge.injective]
    constructor
    · rintro ⟨h,hp⟩
      refine ⟨(hconn y x).mp h,fun z hz hzx => ?_⟩
      have hh := hp (φ.vertex z) ((hconn x z).mpr hz) (fun he => hzx (φ.vertex.injective he))
      simpa only [G.orbitAdjustedHeight_aut a ha] using hh
    · rintro ⟨h,hp⟩
      refine ⟨(hconn y x).mpr h,?_⟩
      intro z hz hzx
      obtain ⟨v,rfl⟩ := φ.vertex.surjective z
      have hh := hp v ((hconn x v).mp hz) (fun he => hzx (congrArg φ.vertex he))
      simpa only [G.orbitAdjustedHeight_aut a ha] using hh
  simp only [peakUpBandTransport,G.orbitAdjustedHeight_aut a ha,hpeak]

theorem expected_peakDownBandCount_lower
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval) (l u : ℝ) :
    (∑ y ∈ O.roots, ENNReal.ofReal (a y)*G.law p (G.strictPeakBandEvent a l u y)) ≤
      ENNReal.ofReal (Real.exp (-l))*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
          (∫⁻ ω, G.peakDownBandCount a l u ω x ∂G.law p)) := by
  have he := OrbitRepresentatives.random_normalized_tilted_transport G O hc hl a hapos ha p
    (G.peakUpBandTransport a l u) (G.measurable_peakUpBandTransport a l u)
      (G.peakUpBandTransport_aut a ha l u)
  simp_rw [G.peakUpBandTransport_outgoing,
    lintegral_indicator_fun_one (G.measurableSet_strictPeakBandEvent a l u _)] at he
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _hx
  calc
    _ ≤ ENNReal.ofReal (a x)*(∫⁻ ω,
        ENNReal.ofReal (Real.exp (-l))*G.peakDownBandCount a l u ω x ∂G.law p) := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro ω
      change (∑' y, G.peakUpBandTransport a l u ω y x*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y))) ≤
        ENNReal.ofReal (Real.exp (-l))*(∑' y, G.peakUpBandTransport a l u ω y x)
      rw [←ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun y => G.peakUpBandTransport_incoming_bound hc hl a l u ω x y
    _ = _ := by
      rw [lintegral_const_mul _ (G.measurable_peakDownBandCount a l u x)]
      ring

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakBandSecondMoment
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

lemma peakDownBandCount_le_four_layers (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (n : ℕ) (ω : Set E) (x : V) :
    G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x ≤
      ∑ j ∈ Finset.range 4, restrictedLayerCount G.ends Set.univ
        {y | G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ)} ω x := by
  unfold peakDownBandCount restrictedLayerCount
  simp only [Set.mem_ofPred_eq]
  rw [←Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases h : R*((n : ℝ)+1) < G.orbitAdjustedHeight a y x ∧
      G.orbitAdjustedHeight a y x ≤ R*((n : ℝ)+4) ∧
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x
  · have hhlo : -R*((n : ℝ)+4) ≤ G.orbitAdjustedHeight a x y := by
      rw [G.orbitAdjustedHeight_reverse hc hl a y x]
      linarith [h.2.1]
    have hhhi : G.orbitAdjustedHeight a x y < -R*((n : ℝ)+1) := by
      rw [G.orbitAdjustedHeight_reverse hc hl a y x]
      linarith [h.1]
    have hidx : -((n : ℤ)+4) ≤ G.adjustedLayerIndex a R 0 x y ∧
        G.adjustedLayerIndex a R 0 x y < -((n : ℤ)+1) := by
      simp only [adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero]
      constructor
      · apply Int.le_floor.mpr
        apply (le_div_iff₀ hR).mpr
        push_cast
        nlinarith
      · apply Int.floor_lt.mpr
        apply (div_lt_iff₀ hR).mpr
        push_cast
        nlinarith
    let j : ℕ := (-G.adjustedLayerIndex a R 0 x y-(n : ℤ)-1).toNat
    have hj : j ∈ Finset.range 4 := by
      simp only [Finset.mem_range,j]
      omega
    have he : G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ) := by
      dsimp [j]
      omega
    have hconn : Percolation.Conn G.ends (ω ∩ Set.univ) x y := by
      simpa only [Set.inter_univ] using Percolation.conn_symm G.ends ω h.2.2.1
    unfold peakUpBandTransport
    rw [ite_eq_left h]
    have hb := Finset.single_le_sum (s := Finset.range 4) (a := j)
      (f := fun k => if G.adjustedLayerIndex a R 0 x y = -((n+k+1 : ℕ) : ℤ) ∧
        Percolation.Conn G.ends (ω ∩ Set.univ) x y then (1 : ℝ≥0∞) else 0)
      (fun _ _ => bot_le) hj
    rw [ite_eq_left (show G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ) ∧
      Percolation.Conn G.ends (ω ∩ Set.univ) x y from ⟨he,hconn⟩)] at hb
    apply hb.trans_eq
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hh : G.adjustedLayerIndex a R 0 x y = -((n+k+1 : ℕ) : ℤ) ∧
      Percolation.Conn G.ends (ω ∩ Set.univ) x y
    · simp only [ite_eq_left hh]
    · simp only [ite_eq_right hh]
  · rw [peakUpBandTransport,ite_eq_right h]
    exact bot_le

variable [Countable V] [Countable E]

theorem peakDownBandCount_second_moment_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval) (β : ℝ) (hβ : R < β)
    (K : ℝ≥0∞)
    (hsecond : ∀ (k l : ℕ) (x : V),
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(k : ℤ)} ω x *
        restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} ω x ∂G.law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ)))) (n : ℕ) (x : V) :
    (∫⁻ ω, (G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x)^2 ∂G.law p) ≤
      16*K*ENNReal.ofReal (Real.exp (-(β-R)*n)) := by
  let N (j : ℕ) (ω : Set E) := restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ)} ω x
  have hmeas (j : ℕ) : Measurable (N j) := measurable_restrictedLayerCount G.ends _ _ x
  calc
    _ ≤ ∫⁻ ω, (∑ j ∈ Finset.range 4, N j ω)^2 ∂G.law p :=
      lintegral_mono fun ω => pow_le_pow_left' (G.peakDownBandCount_le_four_layers hc hl a R hR n ω x) 2
    _ = ∑ j ∈ Finset.range 4, ∑ k ∈ Finset.range 4, ∫⁻ ω, N j ω*N k ω ∂G.law p := by
      simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
      rw [lintegral_finsetSum (f := fun j ω => ∑ k ∈ Finset.range 4, N j ω*N k ω)
        (Finset.range 4) (fun j _ => Finset.measurable_sum _ (fun k _ => (hmeas j).mul (hmeas k)))]
      apply Finset.sum_congr rfl
      intro j _
      exact lintegral_finsetSum (f := fun k ω => N j ω*N k ω) _ (fun k _ => (hmeas j).mul (hmeas k))
    _ ≤ ∑ _j ∈ Finset.range 4, ∑ _k ∈ Finset.range 4,
        K*ENNReal.ofReal (Real.exp (-(β-R)*n)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply (hsecond (n+j+1) (n+k+1) x).trans
      apply mul_le_mul' le_rfl
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hm : (n : ℝ) ≤ ((max (n+j+1) (n+k+1) : ℕ) : ℝ) := by
        exact_mod_cast (show n ≤ max (n+j+1) (n+k+1) by omega)
      nlinarith
    _ = _ := by norm_num [Finset.sum_const,nsmul_eq_mul]; ring

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_WeightedMomentCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_finset_cauchy {ι : Type*} (s : Finset ι) (r f g : ι → ℝ≥0∞)
    (hr : ∀ i ∈ s, r i ≠ ⊤) (hf : ∀ i ∈ s, f i ≠ ⊤) (hg : ∀ i ∈ s, g i ≠ ⊤)
    (ht : ∀ i ∈ s, (r i)^2 ≤ f i*g i) :
    (∑ i ∈ s, r i)^2 ≤ (∑ i ∈ s, f i)*(∑ i ∈ s, g i) := by
  apply (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top (ENNReal.sum_ne_top.mpr hr))
    (ENNReal.mul_ne_top (ENNReal.sum_ne_top.mpr hf) (ENNReal.sum_ne_top.mpr hg))).mp
  rw [ENNReal.toReal_pow,ENNReal.toReal_sum hr,ENNReal.toReal_mul,
    ENNReal.toReal_sum hf,ENNReal.toReal_sum hg]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
  intro i hi
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (hf i hi) (hg i hi)) (ht i hi)
  simpa only [ENNReal.toReal_pow,ENNReal.toReal_mul] using hh

lemma weighted_lintegral_support_cauchy {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (w : ι → ℝ≥0∞)
    (f : ι → Ω → ℝ≥0∞) (A : ι → Set Ω)
    (hw : ∀ i ∈ s, w i ≠ ⊤) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hf : ∀ i ∈ s, Measurable (f i)) (hzero : ∀ i ∈ s, ∀ ω, ω ∉ A i → f i ω=0)
    (hmass : ∀ i ∈ s, μ (A i) ≠ ⊤)
    (hfirst : ∀ i ∈ s, (∫⁻ ω, f i ω ∂μ) ≠ ⊤)
    (hsecond : ∀ i ∈ s, (∫⁻ ω, (f i ω)^2 ∂μ) ≠ ⊤) :
    (∑ i ∈ s, w i*(∫⁻ ω, f i ω ∂μ))^2 ≤
      (∑ i ∈ s, w i*μ (A i))*(∑ i ∈ s, w i*(∫⁻ ω, (f i ω)^2 ∂μ)) := by
  apply ennreal_finset_cauchy s _ _ _
    (fun i hi => ENNReal.mul_ne_top (hw i hi) (hfirst i hi))
    (fun i hi => ENNReal.mul_ne_top (hw i hi) (hmass i hi))
    (fun i hi => ENNReal.mul_ne_top (hw i hi) (hsecond i hi))
  intro i hi
  calc
    _ = (w i)^2*(∫⁻ ω, f i ω ∂μ)^2 := mul_pow _ _ _
    _ ≤ (w i)^2*(μ (A i)*(∫⁻ ω, (f i ω)^2 ∂μ)) :=
      mul_le_mul' le_rfl (lintegral_support_cauchy μ (f i) (hf i hi) (A i) (hA i hi) (hzero i hi))
    _ = _ := by ring

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSurvivalCauchy
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

lemma peakDownBandCount_le_full_count (a : V → ℝ) (l u : ℝ) (ω : Set E) (x : V) :
    G.peakDownBandCount a l u ω x ≤
      restrictedLayerCount G.ends Set.univ Set.univ ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases h : l < G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ u ∧
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x
  · have hc := Percolation.conn_symm G.ends ω h.2.2.1
    simp only [peakUpBandTransport,ite_eq_left h,Set.mem_univ,true_and,Set.inter_univ,
      ite_eq_left hc,le_refl]
  · rw [peakUpBandTransport,ite_eq_right h]
    exact bot_le

variable [Countable V] [Countable E]

theorem weighted_peakDownBandCount_cauchy
    (O : G.OrbitRepresentatives) (a : V → ℝ) (l u : ℝ) (p : unitInterval)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hrow : ∀ x, (∑' y, G.law p {ω | Percolation.Conn G.ends ω x y}) ≤ C)
    (hsecond : ∀ x ∈ O.roots, (∫⁻ ω, (G.peakDownBandCount a l u ω x)^2 ∂G.law p) ≠ ⊤) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.peakDownBandCount a l u ω x ∂G.law p))^2 ≤
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law p {ω | 0 < G.peakDownBandCount a l u ω x})*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, (G.peakDownBandCount a l u ω x)^2 ∂G.law p)) := by
  apply weighted_lintegral_support_cauchy (G.law p) O.roots _ _ _
    (fun _ _ => ENNReal.ofReal_ne_top)
    (fun x _ => measurableSet_lt measurable_const (G.measurable_peakDownBandCount a l u x))
    (fun x _ => G.measurable_peakDownBandCount a l u x)
    (fun x _ ω hω => le_antisymm (le_of_not_gt hω) bot_le)
    (fun _ _ => measure_ne_top _ _) _ hsecond
  intro x _
  apply ne_top_of_le_ne_top hC
  exact (lintegral_mono fun ω => G.peakDownBandCount_le_full_count a l u ω x).trans
    (restrictedLayerCount_expectation_le_row_bound G.ends p C hrow _ _ x)

theorem peakDownBandCount_probability_lower_of_moments
    (O : G.OrbitRepresentatives) (a : V → ℝ) (l u : ℝ) (p : unitInterval)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hrow : ∀ x, (∑' y, G.law p {ω | Percolation.Conn G.ends ω x y}) ≤ C)
    (c D t : ℝ) (hc : 0 < c) (hD : 0 < D) (ht : 0 < t)
    (hlower : ENNReal.ofReal (c*t) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.peakDownBandCount a l u ω x ∂G.law p))
    (hsecond : ∀ x ∈ O.roots, (∫⁻ ω, (G.peakDownBandCount a l u ω x)^2 ∂G.law p) ≠ ⊤)
    (hupper : (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
      (∫⁻ ω, (G.peakDownBandCount a l u ω x)^2 ∂G.law p)) ≤ ENNReal.ofReal (D*t)) :
    ENNReal.ofReal (c^2/D*t) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law p {ω | 0 < G.peakDownBandCount a l u ω x} := by
  let Q := ∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law p {ω | 0 < G.peakDownBandCount a l u ω x}
  have hQ : Q ≠ ⊤ := ENNReal.sum_ne_top.mpr fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hh := (pow_le_pow_left' hlower 2).trans
    ((G.weighted_peakDownBandCount_cauchy O a l u p C hC hrow hsecond).trans (mul_le_mul' le_rfl hupper))
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hQ ENNReal.ofReal_ne_top) hh
  rw [ENNReal.toReal_pow,ENNReal.toReal_ofReal (mul_nonneg hc.le ht.le),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg hD.le ht.le)] at hreal
  have he : c^2*t ≤ Q.toReal*D := (mul_le_mul_iff_right₀ ht).mp (by nlinarith)
  apply ENNReal.ofReal_le_of_le_toReal
  calc
    c^2/D*t = (c^2*t)/D := by ring
    _ ≤ Q.toReal := (div_le_iff₀ hD).mpr he

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SubcriticalPeakSurvival
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

theorem subcritical_weighted_peak_survival
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G)
    (O : (criticalModel G).OrbitRepresentatives) :
    ∃ β : ℝ, R < β ∧ ∃ K : ℝ, 0 < K ∧
      (∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
        ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
        ENNReal.ofReal (c*Real.exp (-(β-R)*n)) ≤
          ∑ x ∈ O.roots, ENNReal.ofReal ((criticalModel G).stationaryOrbitWeight μ x)*
            (criticalModel G).law p {ω | 0 < (criticalModel G).peakDownBandCount
              ((criticalModel G).stationaryOrbitWeight μ) (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x} := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hapos := H.stationaryOrbitWeight_pos hHc hl μ hμ
  have ha := H.stationaryOrbitWeight_aut μ
  obtain ⟨β,hβR,K,hK,hup,c,hcpos,hpeak⟩ := subcritical_peak_band_probability_bs G hc hl hq
    μ hμ hstat hu R hR hjump p hp hpc
  obtain ⟨m,_M,hm,hweights⟩ := H.stationaryOrbitWeight_uniform_bounds hHc hl μ hμ
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq p hpc
  obtain ⟨C,hC,hprofile⟩ := subcritical_full_layer_profile_at_rate G hc hl hq μ hμ
    R hR hjump p hpc β K hβR hK hup
  obtain ⟨K₂,hK₂,hsecond⟩ := H.adjusted_downward_layer_second_moment_at_rate hHc hl a R p β C hβR hC hprofile
  let c₁ := m*c*Real.exp R
  have hc₁ : 0 < c₁ := mul_pos (mul_pos hm hcpos) (Real.exp_pos _)
  let B : ℝ≥0∞ := (∑ x ∈ O.roots, ENNReal.ofReal (a x))*(16*K₂)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by norm_num) hK₂.ne)
  let D := B.toReal+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : B ≤ ENNReal.ofReal D := by
    rw [←ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (by dsimp [D]; linarith)
  refine ⟨β,hβR,K,hK,hup,c₁^2/D,div_pos (sq_pos_of_pos hc₁) hD,?_⟩
  intro n hn
  let l := R*((n : ℝ)+1)
  let u := R*((n : ℝ)+4)
  let t := Real.exp (-(β-R)*n)
  have ht : 0 < t := Real.exp_pos _
  have hpweighted : ENNReal.ofReal (m*c*Real.exp (-β*n)) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*H.law p (H.strictPeakBandEvent a l u x) := by
    obtain ⟨x,hx⟩ := hpeak n hn
    calc
      _ = ENNReal.ofReal m*ENNReal.ofReal (c*Real.exp (-β*n)) := by
        rw [←ENNReal.ofReal_mul hm.le]
        congr 1
        ring
      _ ≤ ENNReal.ofReal m*H.law p (H.strictPeakBandEvent a l u x) := mul_le_mul' le_rfl hx
      _ ≤ _ := H.strictPeakBandEvent_probability_le_weighted_roots O a ha m
        (fun x => (hweights x).1) p l u x
  have hfirst : ENNReal.ofReal (c₁*t) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, H.peakDownBandCount a l u ω x ∂H.law p) := by
    have heq : ENNReal.ofReal (c₁*t)=
        ENNReal.ofReal (Real.exp l)*ENNReal.ofReal (m*c*Real.exp (-β*n)) := by
      rw [←ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      change m*c*Real.exp R*Real.exp (-(β-R)*(n : ℝ))=
        Real.exp (R*((n : ℝ)+1))*(m*c*Real.exp (-β*n))
      calc
        _ = m*c*(Real.exp R*Real.exp (-(β-R)*(n : ℝ))) := by ring
        _ = m*c*Real.exp (R+ -(β-R)*(n : ℝ)) := by rw [Real.exp_add]
        _ = _ := by
          rw [show R+ -(β-R)*(n : ℝ)=R*((n : ℝ)+1)+ -β*n by ring,Real.exp_add]
          ring
    rw [heq]
    apply (mul_le_mul' le_rfl (hpweighted.trans
      (H.expected_peakDownBandCount_lower O hHc hl a hapos ha p l u))).trans_eq
    rw [←mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add,
      add_neg_cancel,Real.exp_zero,ENNReal.ofReal_one,one_mul]
  have hsec (x : V) : (∫⁻ ω, (H.peakDownBandCount a l u ω x)^2 ∂H.law p) ≤ (16*K₂)*ENNReal.ofReal t := by
    exact H.peakDownBandCount_second_moment_bound hHc hl a R hR p β hβR K₂
      (fun k j x => hsecond k j x 0) n x
  have hsecfin (x : V) : (∫⁻ ω, (H.peakDownBandCount a l u ω x)^2 ∂H.law p) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hK₂.ne)
      ENNReal.ofReal_ne_top) (hsec x)
  have hsectotal : (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
      (∫⁻ ω, (H.peakDownBandCount a l u ω x)^2 ∂H.law p)) ≤ ENNReal.ofReal (D*t) := by
    calc
      _ ≤ ∑ x ∈ O.roots, ENNReal.ofReal (a x)*((16*K₂)*ENNReal.ofReal t) :=
        Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (hsec x)
      _ = B*ENNReal.ofReal t := by rw [←Finset.sum_mul]; dsimp [B]; ring
      _ ≤ ENNReal.ofReal D*ENNReal.ofReal t := mul_le_mul' hBD le_rfl
      _ = _ := (ENNReal.ofReal_mul hD.le).symm
  exact H.peakDownBandCount_probability_lower_of_moments O a l u p _ ENNReal.ofReal_ne_top
    hrow c₁ D t hc₁ hD ht hfirst (fun x _ => hsecfin x) hsectotal

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakConditionalLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma one_le_tsum_of_zero_or_one {ι : Type*} (f : ι → ℝ≥0∞)
    (hf : ∀ i, f i=0 ∨ f i=1) (h : 0 < ∑' i, f i) : 1 ≤ ∑' i, f i := by
  have he : ∃ i, f i ≠ 0 := by
    by_contra! hn
    rw [ENNReal.tsum_eq_zero.mpr hn] at h
    exact lt_irrefl _ h
  obtain ⟨i,hi⟩ := he
  have hh := ENNReal.le_tsum (f := f) i
  rwa [(hf i).resolve_left hi] at hh

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

variable [Countable V] [Countable E]

theorem peak_survival_layer_moment_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval) (β : ℝ) (hβ : R < β)
    (K : ℝ≥0∞)
    (hsecond : ∀ (k l : ℕ) (x : V),
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(k : ℤ)} ω x *
        restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} ω x ∂G.law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ)))) (n l : ℕ) (x : V) :
    (∫⁻ ω,
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => restrictedLayerCount G.ends Set.univ {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} η x) ω ∂G.law p) ≤
      4*K*ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) := by
  let F (ω : Set E) := restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} ω x
  let N (j : ℕ) (ω : Set E) := restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ)} ω x
  have hmF : Measurable F := measurable_restrictedLayerCount G.ends _ _ x
  have hmN (j : ℕ) : Measurable (N j) := measurable_restrictedLayerCount G.ends _ _ x
  have hpoint (ω : Set E) :
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator F ω ≤
        F ω*(∑ j ∈ Finset.range 4, N j ω) := by
    by_cases hω : 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x
    · rw [Set.indicator_of_mem (show ω ∈ {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x} from hω)]
      have hone : 1 ≤ G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x :=
        by
          unfold peakDownBandCount peakUpBandTransport at hω ⊢
          exact one_le_tsum_of_zero_or_one _ (fun y => by split_ifs <;> simp) hω
      exact (show F ω ≤ F ω*G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x by
        simpa only [mul_one] using mul_le_mul' (le_refl (F ω)) hone).trans
          (mul_le_mul' le_rfl (G.peakDownBandCount_le_four_layers hc hl a R hR n ω x))
    · rw [Set.indicator_of_notMem (show ω ∉ {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x} from hω)]
      exact bot_le
  calc
    _ ≤ ∫⁻ ω, F ω*(∑ j ∈ Finset.range 4, N j ω) ∂G.law p := lintegral_mono hpoint
    _ = ∑ j ∈ Finset.range 4, ∫⁻ ω, F ω*N j ω ∂G.law p := by
      simp_rw [Finset.mul_sum]
      exact lintegral_finsetSum (f := fun j ω => F ω*N j ω) _ (fun j _ => hmF.mul (hmN j))
    _ ≤ ∑ _j ∈ Finset.range 4, K*ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro j _
      apply (hsecond l (n+j+1) x).trans
      apply mul_le_mul' le_rfl
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hh : ((max n l : ℕ) : ℝ) ≤ ((max l (n+j+1) : ℕ) : ℝ) := by
        exact_mod_cast (show max n l ≤ max l (n+j+1) by omega)
      nlinarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

theorem peakSurvivalLayerMoment_bound
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval) (β : ℝ) (hβ : R < β)
    (K : ℝ≥0∞)
    (hsecond : ∀ (k l : ℕ) (x : V),
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(k : ℤ)} ω x *
        restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} ω x ∂G.law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ)))) (n l : ℕ) :
    G.peakSurvivalLayerMoment O a R p n l ≤
      (∑ x ∈ O.roots, ENNReal.ofReal (a x))*(4*K)*
        ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) := by
  apply (Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl
    (G.peak_survival_layer_moment_bound hc hl a R hR p β hβ K hsecond n l x)).trans_eq
  rw [←Finset.sum_mul]
  ring

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SubcriticalPeakConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma exponential_max_factorization (a c D n l : ℝ) (hc : c ≠ 0) :
    D*Real.exp (-a*max n l)=
      (c*Real.exp (-a*n))*((D/c)*Real.exp (-a*max (l-n) 0)) := by
  have hm : max n l=n+max (l-n) 0 := by
    rcases le_total n l with h | h
    · rw [max_eq_right h,max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [max_eq_left h,max_eq_right (sub_nonpos.mpr h)]
      ring
  rw [hm]
  calc
    _ = D*(Real.exp (-a*n)*Real.exp (-a*max (l-n) 0)) := by
      rw [←Real.exp_add]
      congr 2
      ring
    _ = _ := by field_simp

variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_weighted_peak_conditional_layers_bs_oai
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G)
    (O : (criticalModel G).OrbitRepresentatives) :
    ∃ β : ℝ, R < β ∧ ∃ K : ℝ, 0 < K ∧
      (∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
        ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        ENNReal.ofReal (c*Real.exp (-(β-R)*n)) ≤
          (criticalModel G).peakSurvivalProbability O ((criticalModel G).stationaryOrbitWeight μ) R p n ∧
        ∀ l : ℕ, (criticalModel G).peakSurvivalLayerMoment O
          ((criticalModel G).stationaryOrbitWeight μ) R p n l ≤
          (criticalModel G).peakSurvivalProbability O ((criticalModel G).stationaryOrbitWeight μ) R p n *
            ENNReal.ofReal (C*Real.exp (-(β-R)*max ((l : ℝ)-n) 0)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  obtain ⟨β,hβR,K,hK,hup,c,hcpos,hsurv⟩ := subcritical_weighted_peak_survival G hc hl hq
    μ hμ hstat hu R hR hjump p hp hpc O
  obtain ⟨C₀,hC₀,hprofile⟩ := subcritical_full_layer_profile_at_rate G hc hl hq μ hμ
    R hR hjump p hpc β K hβR hK hup
  obtain ⟨K₂,hK₂,hsecond⟩ := H.adjusted_downward_layer_second_moment_at_rate
    hHc hl a R p β C₀ hβR hC₀ hprofile
  let B : ℝ≥0∞ := (∑ x ∈ O.roots, ENNReal.ofReal (a x))*(4*K₂)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by norm_num) hK₂.ne)
  let D := B.toReal+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : B ≤ ENNReal.ofReal D := by
    rw [←ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (by dsimp [D]; linarith)
  refine ⟨β,hβR,K,hK,hup,c,hcpos,D/c,div_pos hD hcpos,?_⟩
  intro n hn
  refine ⟨hsurv n hn,?_⟩
  intro l
  calc
    _ ≤ B*ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) :=
      H.peakSurvivalLayerMoment_bound O hHc hl a R hR p β hβR K₂
        (fun k j x => hsecond k j x 0) n l
    _ ≤ ENNReal.ofReal D*ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) :=
      mul_le_mul' hBD le_rfl
    _ = ENNReal.ofReal (c*Real.exp (-(β-R)*n))*
        ENNReal.ofReal ((D/c)*Real.exp (-(β-R)*max ((l : ℝ)-n) 0)) := by
      rw [←ENNReal.ofReal_mul hD.le,←ENNReal.ofReal_mul
        (mul_nonneg hcpos.le (Real.exp_nonneg _))]
      congr 1
      rw [Nat.cast_max]
      exact exponential_max_factorization (β-R) c D n l hcpos.ne'
    _ ≤ _ := mul_le_mul' (hsurv n hn) le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers_bs_oai.{u_1, u_2} := @OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers_bs_oai.{u_1, u_2}
