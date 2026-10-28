-- Prove2me | solution 1 for OAI.Percolation.exists_selected_path_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:06:34.790842+00:00
-- url     : https://prove2.me/submissions/f0ae105a-dd2c-4c9d-bffa-b09016c22fb4

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_rooted_selected_label_mass_lower

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

section Probability
variable (G : BondGraph V E)

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

 
theorem operatorBounded_of_lt_pc [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : OperatorBounded G p := by
  obtain ⟨C,hC,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  obtain ⟨A,_,hA⟩ := exists_operator_of_row_column_bound (twoPoint G p) C hC
    (twoPoint_nonneg G p) hrow (fun y F => by
      simpa only [twoPoint_symm G p] using hrow y F)
  exact ⟨A,hA⟩

end SharpnessSusceptibility

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


theorem adj_symm (G : BondGraph V E) {x y : V} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,he.trans (Sym2.eq_swap)⟩

end IsoperimetricEnergy

section SymmetricWalk
attribute [local instance] Classical.propDecidable



 theorem walkKernel_symmetric (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : walkKernel G hloc a x y = walkKernel G hloc a y x := by
  have ha : Adj G x y ↔ Adj G y x := ⟨adj_symm G,adj_symm G⟩
  by_cases h : x = y
  · subst y; rfl
  · simp [walkKernel,h,Ne.symm h,ha]

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

 theorem matrixCoeff_mul_invariant (a : V ≃ V) (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y)
    (hB : ∀ x y, matrixCoeff B (a x) (a y) = matrixCoeff B x y) :
    ∀ x y, matrixCoeff (A*B) (a x) (a y) = matrixCoeff (A*B) x y := by
  intro x y
  simp only [matrixCoeff_mul]
  rw [← a.tsum_eq (fun z => matrixCoeff A (a x) z * matrixCoeff B z (a y))]
  simp only [hA,hB]

section RootTrace
variable {ι : Type*} [Fintype ι]
variable (root : ι → V) (weight : ι → ℝ)

theorem KernelInvariant.mul {Γ : Set (V ≃ V)}
    {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B) :
    KernelInvariant Γ (A*B) := by
  intro a ha
  exact matrixCoeff_mul_invariant a A B (hA a ha) (hB a ha)

end RootTrace

end InvariantOperatorTrace

section InvariantPercolationOperators
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable


theorem KernelInvariant.one (Γ : Set (V ≃ V)) :
    KernelInvariant Γ (1 : Hilbert V →L[ℂ] Hilbert V) := by
  intro a _ x y
  simp only [matrixCoeff, one_apply_eq_self, lp.coeFn_single]
  simp [Pi.single_apply, a.injective.eq_iff]

theorem KernelInvariant.pow {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) (n : ℕ) :
    KernelInvariant Γ (A^n) := by
  induction n with
  | zero => simpa only [pow_zero] using KernelInvariant.one Γ
  | succ n ih => simpa only [pow_succ] using ih.mul hA



end InvariantPercolationOperators

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



end TrajectoryTransport

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

 

theorem orbit_two_step_return_lower (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (K : V → V → ℝ)
    (hfin : ∀ x, (Function.support (K x)).Finite)
    (hrow : ∀ x, HasSum (K x) 1) (hsym : ∀ x y, K x y = K y x)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y) :
    (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' z, K (root i₀) z * ∑' y, if y ∈ vertexOrbit G (root i₀) then K z y else 0 := by
  let O := vertexOrbit G (root i₀)
  let I : V → ℝ := fun x => if x ∈ O then 1 else 0
  let f : V → ℝ := fun x => ∑' y, K x y * I y
  let g : V → ℝ := fun x => ∑' y, K x y * f y
  let σ := ∑ i, weight i * I (root i)
  have hI (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : I (a x) = I x := by
    simp only [I,O,mem_vertexOrbit_aut_iff G (root i₀) hab]
  have hf (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : f (a x) = f x := by
    dsimp only [f]
    rw [←a.tsum_eq (fun y => K (a x) y*I y)]
    simp only [hcov a b hab,hI a b hab]
  have hg (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : g (a x) = g x := by
    dsimp only [g]
    rw [←a.tsum_eq (fun y => K (a x) y*f y)]
    simp only [hcov a b hab,hf a b hab]
  have hgO (x : V) (hx : x ∈ O) : g x = g (root i₀) := by
    obtain ⟨a,b,hab,rfl⟩ := hx
    exact hg a b hab _
  have hmean : ∑ i, weight i*f (root i) = σ := by
    have ht := htr.real root weight Γ (fun x y => K x y*I y)
      (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; rw [hcov a b hab,hI a b hab])
      (fun x => finiteKernel_summable_mul K hfin x I)
      (fun y => by simpa only [hsym, mul_comm] using (hrow y).summable.mul_left (I y))
    calc
      _ = ∑ i, weight i * ∑' x, K x (root i)*I (root i) := ht
      _ = σ := by simp only [tsum_mul_right,show ∀ y, ∑' x, K x y = 1 from fun y => by simpa only [hsym] using (hrow y).tsum_eq,one_mul,σ]
  have hsecond : σ*g (root i₀) = ∑ i, weight i*f (root i)^2 := by
    have ht := htr.real root weight Γ (fun x y => I x*K x y*f y)
      (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; rw [hcov a b hab,hI a b hab,hf a b hab])
      (fun x => by simpa only [mul_assoc] using (finiteKernel_summable_mul K hfin x f).mul_left (I x))
      (fun y => by simpa only [hsym,mul_comm,mul_left_comm,mul_assoc] using (finiteKernel_summable_mul K hfin y I).mul_right (f y))
    have hr (i : ι) : I (root i)*g (root i) = I (root i)*g (root i₀) := by
      by_cases hi : root i ∈ O
      · rw [hgO _ hi]
      · simp only [I,ite_eq_right hi,zero_mul]
    calc
      _ = ∑ i, weight i*(I (root i)*g (root i)) := by
        simp only [hr,σ,Finset.sum_mul,mul_assoc]
      _ = ∑ i, weight i*∑' x, I x*K x (root i)*f (root i) := by
        simpa only [mul_assoc,tsum_mul_left,g] using ht
      _ = ∑ i, weight i*f (root i)^2 := by
        simp only [tsum_mul_right]
        congr 1
        ext i
        congr 1
        rw [show (∑' x, I x*K x (root i)) = f (root i) by simp only [f,hsym,mul_comm]]
        ring
  have hvariance : 0 ≤ ∑ i, weight i*(f (root i)-σ)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have he : (∑ i, weight i*(f (root i)-σ)^2) = (∑ i, weight i*f (root i)^2)-σ^2 := by
    simp_rw [sub_sq,mul_add,mul_sub]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hc : (∑ i, weight i*(2*f (root i)*σ)) = 2*σ*(∑ i, weight i*f (root i)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    rw [hc,hmean,←Finset.sum_mul,hw1,one_mul]
    ring
  rw [he,←hsecond] at hvariance
  have hσ : 0 < σ := by
    have hx : root i₀ ∈ O := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
    have hIn (x : V) : 0 ≤ I x := by dsimp [I]; split_ifs <;> norm_num
    have hb := Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (hIn (root i))) (Finset.mem_univ i₀)
    have he₀ : weight i₀*I (root i₀) = weight i₀ := by simp only [I,ite_eq_left hx,mul_one]
    rw [he₀] at hb
    exact hw₀.trans_le hb
  have hbound : σ ≤ g (root i₀) := by nlinarith only [hvariance,hσ]
  simpa only [σ,g,f,I,mul_ite,mul_one,mul_zero,zero_mul] using hbound

end OrbitReturn
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem matrixCoeff_real_symm (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : IsSelfAdjoint A) (x y : V) : (matrixCoeff A x y).re = (matrixCoeff A y x).re := by
  have h := congrArg Complex.re (matrixCoeff_adjoint A x y)
  simpa only [hA.star_eq,Complex.star_def,Complex.conj_re] using h

theorem finite_positive_square_row (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (hfin : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (A*A) x y).re*f y) =
      ∑' z, (matrixCoeff A x z).re*∑' y, (matrixCoeff A z y).re*f y := by
  let K := fun x y => (matrixCoeff A x y).re
  let B := (hfin x).toFinset
  have hz (z : V) (hz : z ∉ B) : K x z = 0 := by
    simpa only [B,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
  have he (y : V) : (matrixCoeff (A*A) x y).re*f y = ∑ z ∈ B, K x z*(K z y*f y) := by
    rw [←(hA.mul_hasSum A x y).tsum_eq,tsum_eq_sum (s := B) (fun z h => by change K x z*K z y = 0; rw [hz z h,zero_mul]),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z h
    exact mul_assoc _ _ _
  have hs := hasSum_sum (s := B) (fun z _ =>
    (finiteKernel_summable_mul K hfin z f).hasSum.mul_left (K x z))
  have hr : (∑' z, K x z*∑' y, K z y*f y) = ∑ z ∈ B, K x z*∑' y, K z y*f y :=
    tsum_eq_sum (fun z h => by rw [hz z h,zero_mul])
  simpa only [←he,←hr] using hs.tsum_eq

theorem walkPower_finite_support (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) (x : V) :
    (Function.support (fun y => (matrixCoeff (P^k) x y).re)).Finite := by
  apply (finite_reachBall hloc x k).subset
  intro y hy
  by_contra hn
  exact hy (walkPower_support G hloc a P hpos hP k x y hn)

theorem walkPower_invariant (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) :
    KernelInvariant (vertexAut G) (P^k) := by
  apply KernelInvariant.pow
  intro g hg x y
  obtain ⟨b,hb⟩ := hg
  simp only [hP,walkKernel_covariant G hloc a hb]

 

theorem walkPower_even_orbit_return (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) :
    (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' y, if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^(2*k)) (root i₀) y).re else 0 := by
  have h := orbit_two_step_return_lower G root weight Γ hΓ htr hw hw1 i₀ hw₀
    (fun x y => (matrixCoeff (P^k) x y).re)
    (walkPower_finite_support G hloc a P hpos hP k)
    (walkPower_hasSum G hloc a P hpos hP k)
    (matrixCoeff_real_symm (P^k) (hsym.pow k))
    (fun g b hb x y => congrArg Complex.re (walkPower_invariant G hloc a P hP k g ⟨b,hb⟩ x y))
  have he := finite_positive_square_row (P^k) (hpos.pow k)
    (walkPower_finite_support G hloc a P hpos hP k)
    (fun y => if y ∈ vertexOrbit G (root i₀) then 1 else 0) (root i₀)
  simp only [mul_ite,mul_one,mul_zero] at he
  rw [←he] at h
  simpa only [←pow_add,←two_mul] using h

end WalkOrbitReturn
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteOrbitPartition
attribute [local instance] Classical.propDecidable Classical.decEq



theorem vertexOrbit_eq_of_mem (G : BondGraph V E) (o x : V) (hx : x ∈ vertexOrbit G o) :
    vertexOrbit G x = vertexOrbit G o := by
  obtain ⟨a,b,hab,rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.trans c,b.trans d,isAut_trans G hab hcd,hc⟩
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.symm.trans c,b.symm.trans d,isAut_trans G (isAut_symm G hab) hcd,by simpa using hc⟩



end FiniteOrbitPartition
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
section FinitePositiveOperatorPowers
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_positive_product_support (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hb : ∀ x, (Function.support (fun y => (matrixCoeff B x y).re)).Finite) (x : V) :
    (Function.support (fun y => (matrixCoeff (A*B) x y).re)).Finite := by
  let S := (ha x).toFinset
  let T := S.biUnion (fun z => (hb z).toFinset)
  apply T.finite_toSet.subset
  intro y hy
  by_contra hn
  apply hy
  change (matrixCoeff (A*B) x y).re = 0
  rw [←(hA.mul_hasSum B x y).tsum_eq]
  rw [←tsum_zero]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ S
  · have hzy : (matrixCoeff B z y).re = 0 := by
      by_contra hh
      apply hn
      exact Finset.mem_biUnion.mpr ⟨z,hz,by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using hh⟩
    rw [hzy,mul_zero]
  · have hzx : (matrixCoeff A x z).re = 0 := by
      simpa only [S,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
    rw [hzx,zero_mul]

theorem finite_positive_product_action (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hb : ∀ x, (Function.support (fun y => (matrixCoeff B x y).re)).Finite)
    (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (A*B) x y).re*f y) =
      ∑' z, (matrixCoeff A x z).re*∑' y, (matrixCoeff B z y).re*f y := by
  let K := fun x y => (matrixCoeff A x y).re
  let J := fun x y => (matrixCoeff B x y).re
  let S := (ha x).toFinset
  have hz (z : V) (hz : z ∉ S) : K x z = 0 := by
    simpa only [S,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
  have he (y : V) : (matrixCoeff (A*B) x y).re*f y = ∑ z ∈ S, K x z*(J z y*f y) := by
    rw [←(hA.mul_hasSum B x y).tsum_eq,tsum_eq_sum (s := S)
      (fun z h => by change K x z*J z y = 0; rw [hz z h,zero_mul]),Finset.sum_mul]
    exact Finset.sum_congr rfl (fun z _ => mul_assoc _ _ _)
  have hs := hasSum_sum (s := S) (fun z _ =>
    (finiteKernel_summable_mul J hb z f).hasSum.mul_left (K x z))
  have hr : (∑' z, K x z*∑' y, J z y*f y) = ∑ z ∈ S, K x z*∑' y, J z y*f y :=
    tsum_eq_sum (fun z h => by rw [hz z h,zero_mul])
  simpa only [←he,←hr] using hs.tsum_eq

theorem finite_positive_pow_support (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (j : ℕ) (x : V) : (Function.support (fun y => (matrixCoeff (A^j) x y).re)).Finite := by
  induction j generalizing x with
  | zero =>
      apply (Set.finite_singleton x).subset
      intro y hy
      by_contra hn
      apply hy
      have he : x ≠ y := fun h => hn (by simp only [Set.mem_singleton_iff]; exact h.symm)
      simp only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right he,Complex.zero_re]
  | succ j ih =>
      rw [pow_succ']
      exact finite_positive_product_support A (A^j) hA ha ih x

theorem positive_identity_action (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (1 : Hilbert V →L[ℂ] Hilbert V) x y).re*f y) = f x := by
  rw [tsum_eq_single x (fun y hy => by
    simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right (Ne.symm hy),Complex.zero_re,zero_mul])]
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_true,Complex.one_re,one_mul]

end FinitePositiveOperatorPowers
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

end HoldingWalk
end ChronologicalErasure
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

 theorem raw_integral_operator (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x : V) (f : V → ℝ) :
    RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k x f =
      ∑' y, (matrixCoeff (P^k) x y).re * f y := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) :=
    finite_openSimpleGraph_neighbors G hloc z
  have hs (x : V) : (Function.support (walkKernel G hloc a x)).Finite := by
    simpa only [pow_one,hP,Complex.ofReal_re] using walkPower_finite_support G hloc a P hpos hP 1 x
  have hsP (x : V) : (Function.support (fun y => (matrixCoeff P x y).re)).Finite := by
    simpa only [hP,Complex.ofReal_re] using hs x
  induction k generalizing x with
  | zero => rw [RawFrom.integral_zero,pow_zero,positive_identity_action]
  | succ k ih =>
    rw [RawFrom.integral_succ,pow_succ',finite_positive_product_action P (P^k) hpos hsP
      (finite_positive_pow_support P hpos hsP k)]
    simp only [hP,Complex.ofReal_re]
    rw [sum_step_decomposition (openSimpleGraph G Set.univ) (walkKernel G hloc a) hs]
    · simp only [ih]
    · intro u v huv hn
      apply walkKernel_zero_of_not_step G hloc a u v huv
      intro ha
      apply hn
      obtain ⟨e,he⟩ := ha
      exact ⟨huv,e,Set.mem_univ e,he⟩

end RawPathOperator
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
section AnchoredSegments
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]


theorem segmentAnchors_nonempty_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    (segmentAnchors G hloc γ n hdiam i x).Nonempty ↔ x ∈ vertexOrbit G (γ i) := by
  constructor
  · rintro ⟨s,hs⟩
    obtain ⟨⟨a,b,h,rfl⟩,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
    exact ⟨a,b,h,hx⟩
  · rintro ⟨a,b,h,hx⟩
    exact ⟨a ∘ γ,(mem_segmentAnchors G hloc γ n hdiam i x _).mpr ⟨⟨a,b,h,rfl⟩,hx⟩⟩

end AnchoredSegments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionKernels
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem segmentAnchors_map (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    segmentAnchors G hloc γ n hdiam i (a x) =
      (segmentAnchors G hloc γ n hdiam i x).map (segmentAut a).toEmbedding := by
  ext s
  rw [Finset.mem_map,mem_segmentAnchors]
  constructor
  · rintro ⟨hs,hx⟩
    refine ⟨a.symm ∘ s,(mem_segmentAnchors G hloc γ n hdiam i x _).mpr ⟨?_,?_⟩,?_⟩
    · exact (segmentOrbit_aut_iff G γ s (isAut_symm G h)).mpr hs
    · simp only [Function.comp_apply,hx,Equiv.symm_apply_apply]
    · funext j; exact a.apply_symm_apply (s j)
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨ht,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x t).mp ht
    exact ⟨(segmentOrbit_aut_iff G γ t h).mpr ht,congrArg a hx⟩

theorem segmentAnchors_card_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    (segmentAnchors G hloc γ n hdiam i (a x)).card = (segmentAnchors G hloc γ n hdiam i x).card := by
  rw [segmentAnchors_map G hloc γ n hdiam i x h,Finset.card_map]



end AnchoredPositionKernels
end Percolation


namespace Percolation
universe u
variable {V : Type u}
section RawReversal
namespace HoldingWalk
variable {H : SimpleGraph V}


theorem mass_snocHold (P : V → V → ℝ) {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.mass P = w.mass P * P y y := by
  induction w with
  | nil => simp only [snocHold,mass,mul_one,one_mul]
  | hold w ih => simp only [snocHold,mass,ih,mul_assoc]
  | step h w ih => simp only [snocHold,mass,ih,mul_assoc]

theorem mass_snocStep (P : V → V → ℝ) {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).mass P = w.mass P * P y z := by
  induction w with
  | nil => simp only [snocStep,mass,mul_one,one_mul]
  | hold w ih => simp only [snocStep,mass,ih,mul_assoc]
  | step h' w ih => simp only [snocStep,mass,ih,mul_assoc]

theorem mass_reverse (P : V → V → ℝ) (hP : ∀ x y, P x y = P y x)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.reverse.mass P = w.mass P := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,mass_snocHold,mass,ih,mul_comm]
  | step h w ih => simp only [reverse,mass_snocStep,mass,ih,hP,mul_comm]

end HoldingWalk
end RawReversal
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FiniteRootedLabels
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

instance finite_rootedLabelCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    Finite (RootedLabelCode G hloc γ n hdiam center ep neg L m x) := by
  let (z : V) := finite_openSimpleGraph_neighbors G hloc z
  unfold RootedLabelCode
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem finite_rootedEscapeLabels (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    Finite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} :=
  Finite.of_equiv _ (rootedLabelEquiv G hloc γ n hdiam center ep neg L m x).symm

end FiniteRootedLabels
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem segmentAnchors_card_on_orbit (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    (hx : x ∈ vertexOrbit G (γ i)) :
    (segmentAnchors G hloc γ n hdiam i x).card = (segmentAnchors G hloc γ n hdiam i (γ i)).card := by
  obtain ⟨a,b,h,rfl⟩ := hx
  exact segmentAnchors_card_aut G hloc γ n hdiam i (γ i) h

theorem segmentAnchors_card_eq_indicator (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    ((segmentAnchors G hloc γ n hdiam i x).card : ℝ) =
      if x ∈ vertexOrbit G (γ i) then (segmentAnchors G hloc γ n hdiam i (γ i)).card else 0 := by
  split_ifs with hx
  · exact congrArg Nat.cast (segmentAnchors_card_on_orbit G hloc γ n hdiam i x hx)
  · have hh := (segmentAnchors_nonempty_iff G hloc γ n hdiam i x).not.mpr hx
    rw [Finset.not_nonempty_iff_eq_empty.mp hh]
    rfl

theorem labelFromCode_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (P : V → V → ℝ)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.mass P =
      c.2.1.2.mass P * c.2.2.2.1.2.mass P * c.2.2.2.2.2.mass P := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl



end LabeledMass
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledNormalization
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

omit [Fintype I] in
theorem segmentReturnMass_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) :
    segmentReturnMass G hloc a γ ep L x =
      ∑' y, if y ∈ vertexOrbit G (γ ep) then (matrixCoeff (P^L) x y).re else 0 := by
  have hh := raw_integral_operator G hloc a P hpos hP L x
    (fun y => if y ∈ vertexOrbit G (γ ep) then 1 else 0)
  simpa only [RawFrom.integral,mul_ite,mul_one,mul_zero,segmentReturnMass] using hh

omit [Fintype I] in
theorem segmentReturnMass_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) :
    segmentReturnMass G hloc a γ ep L (g x) = segmentReturnMass G hloc a γ ep L x := by
  rw [segmentReturnMass_operator G hloc a γ ep L (g x) P hpos hP,
    segmentReturnMass_operator G hloc a γ ep L x P hpos hP,←g.tsum_eq]
  apply tsum_congr
  intro y
  rw [mem_vertexOrbit_aut_iff G (γ ep) hg]
  have hh := walkPower_invariant G hloc a P hP L g ⟨b,hg⟩ x y
  rw [hh]

end LabeledNormalization
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LazyOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem positive_lazy_power_step (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (k : ℕ) (x y : V) :
    (1/2) * (matrixCoeff (P^k) x y).re ≤ (matrixCoeff (P^(k+1)) x y).re := by
  have hs := hpos.mul_hasSum (P^k) x y
  have hh := hs.summable.sum_le_tsum ({x} : Finset V)
    (fun z _ => mul_nonneg (hpos x z).2 ((hpos.pow k) z y).2)
  simp only [Finset.sum_singleton,hs.tsum_eq,←pow_succ'] at hh
  exact (mul_le_mul_of_nonneg_right (hdiag x) ((hpos.pow k) x y).2).trans hh

 

theorem walkPower_orbit_return_lower (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (L : ℕ) :
    (1/2) * (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' y, if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^L) (root i₀) y).re else 0 := by
  have hsum (k : ℕ) : Summable (fun y =>
      if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^k) (root i₀) y).re else 0) := by
    simpa only [mul_ite,mul_one,mul_zero] using finiteKernel_summable_mul
      (fun x y => (matrixCoeff (P^k) x y).re) (walkPower_finite_support G hloc a P hpos hP k)
      (root i₀) (fun y => if y ∈ vertexOrbit G (root i₀) then 1 else 0)
  obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' L
  · rw [hk]
    have hh := walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k
    have hn : 0 ≤ ∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0 :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hw i | rfl)
    linarith
  · rw [hk]
    have hh := mul_le_mul_of_nonneg_left
      (walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k)
      (show (0:ℝ) ≤ 1/2 by norm_num)
    apply hh.trans
    rw [←tsum_mul_left]
    apply ((hsum (2*k)).mul_left (1/2)).tsum_le_tsum _ (hsum (2*k+1))
    intro y
    split_ifs
    · exact positive_lazy_power_step P hpos hdiag (2*k) (root i₀) y
    · simp only [mul_zero,le_refl]

end LazyOrbitReturn
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section UniformLabeledLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

omit [Fintype I] in
 

theorem segmentReturnMass_uniform_lower (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (γ : I → V) (ep : I) (L : ℕ) :
    1/(2*c) ≤ segmentReturnMass G hloc a γ ep L (γ ep) := by
  obtain ⟨i,g,hg,hx⟩ := hcov (γ ep)
  obtain ⟨b,hb⟩ := hΓ hg
  have hO := vertexOrbit_eq_of_mem G (root i) (γ ep) ⟨g,b,hb,hx⟩
  rw [←hx,segmentReturnMass_aut G hloc a γ ep L (root i) P hpos hP hb]
  rw [segmentReturnMass_operator G hloc a γ ep L (root i) P hpos hP]
  rw [hO]
  have hh := walkPower_orbit_return_lower G hloc a root weight Γ hΓ htr
    (fun i => (hw i).le) hw1 i (hw i) P hpos hsym hP hdiag L
  have hi : weight i ≤ ∑ r, if root r ∈ vertexOrbit G (root i) then weight r else 0 := by
    have hx' : root i ∈ vertexOrbit G (root i) := ⟨Equiv.refl _,Equiv.refl _,isAut_refl G,rfl⟩
    simpa only [ite_eq_left hx'] using Finset.single_le_sum
      (f := fun r => if root r ∈ vertexOrbit G (root i) then weight r else 0)
      (fun r _ => by split_ifs <;> first | exact (hw r).le | rfl) (Finset.mem_univ i)
  apply le_trans _ hh
  have hct : 0 < 2*c := mul_pos (by norm_num) hc
  apply (div_le_iff₀ hct).mpr
  have hh' := mul_le_mul_of_nonneg_left hi hc.le
  nlinarith [hmin i]



end UniformLabeledLaw
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LongGeodesics
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_geodesic_length (G : BondGraph V E) [Infinite V]
    (hloc : LocallyFinite G) (hconn : Connected G) (x : V) (N : ℕ) :
    ∃ y : V, ∃ q : (openSimpleGraph G Set.univ).Walk x y,
      q.length = N ∧ q.length = (openSimpleGraph G Set.univ).dist x y := by
  obtain ⟨z,hz⟩ := (finite_reachBall hloc x N).exists_notMem
  have hc := (conn_iff_reachable G Set.univ x z).mp (conn_univ_of_connected G hconn x z)
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist
  have hN : N < q.length := by
    by_contra hh
    have hm := walk_mem_reachBall G Set.univ q 0 (show x ∈ reachBall G x 0 from rfl)
    have hm' : z ∈ reachBall G x q.length := by simpa only [Nat.zero_add] using hm
    exact hz (reachBall_mono_local G x (Nat.le_of_not_gt hh) hm')
  refine ⟨q.getVert N,q.take N,?_,?_⟩
  · simp only [SimpleGraph.Walk.take_length,inf_eq_left.mpr hN.le]
  · exact SimpleGraph.length_eq_dist_of_subwalk hq (q.isSubwalk_take N)

 

theorem geodesic_getVert_dist (H : SimpleGraph V) {x y : V} (q : H.Walk x y)
    (hq : q.length = H.dist x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ q.length) :
    H.dist (q.getVert i) (q.getVert j) = j-i := by
  have hs := SimpleGraph.length_eq_dist_of_subwalk hq
    (((q.drop i).isSubwalk_take (j-i)).trans (q.isSubwalk_drop i))
  have he : (q.drop i).getVert (j-i) = q.getVert j := by
    rw [SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hij]
  rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,he,
    min_eq_left (Nat.sub_le_sub_right hj i)] at hs
  exact hs.symm

end LongGeodesics
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
namespace HoldingWalk
variable {H : SimpleGraph V}



theorem mass_append (P : V → V → ℝ) {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) :
    (w.append v).mass P = w.mass P*v.mass P := by
  induction w with
  | nil => simp only [append,mass,one_mul]
  | hold w ih => simp only [append,mass,ih,mul_assoc]
  | step h w ih => simp only [append,mass,ih,mul_assoc]

end HoldingWalk
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GeodesicSegments
attribute [local instance] Classical.propDecidable Classical.decEq



theorem geodesicSegment_adj (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N)
    (i : ℕ) (hi : i < N) :
    (openSimpleGraph G Set.univ).Adj
      (geodesicSegment G q N ⟨i,by omega⟩) (geodesicSegment G q N ⟨i+1,by omega⟩) := by
  change (openSimpleGraph G Set.univ).Adj (q.getVert i) (q.getVert (i+1))
  exact q.adj_getVert_succ (by omega)

theorem geodesicSegment_injective (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N)
    (hq : q.length = (openSimpleGraph G Set.univ).dist x y) :
    Function.Injective (geodesicSegment G q N) := by
  intro i j hh
  apply Fin.ext
  exact (q.isPath_of_length_eq_dist hq).getVert_injOn
    (by change i.val ≤ q.length; omega) (by change j.val ≤ q.length; omega) hh

theorem geodesicSegment_diameter (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N) :
    ∀ i j, geodesicSegment G q N j ∈ reachBall G (geodesicSegment G q N i) N := by
  intro i j
  have hc : (openSimpleGraph G Set.univ).Reachable (q.getVert i) (q.getVert j) :=
    (q.take i).reachable.symm.trans (q.take j).reachable
  obtain ⟨r,hr⟩ := hc.exists_walk_length_eq_dist
  have hd : (openSimpleGraph G Set.univ).dist (q.getVert i) (q.getVert j) ≤ N := by
    rcases le_total i.val j.val with hij | hji
    · have hle := SimpleGraph.dist_le ((q.drop i).take (j-i))
      rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
        SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hij] at hle
      exact hle.trans (by omega)
    · have hle := SimpleGraph.dist_le ((q.drop j).take (i-j))
      rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
        SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hji] at hle
      rw [SimpleGraph.dist_comm] at hle
      exact hle.trans (by omega)
  have hm := walk_mem_reachBall G Set.univ r 0 (show q.getVert i ∈ reachBall G (q.getVert i) 0 from rfl)
  apply reachBall_mono_local G (q.getVert i) (a := r.length) (by omega)
  simpa only [Nat.zero_add, geodesicSegment] using hm

theorem walkKernel_step (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {x y : V} (h : (openSimpleGraph G Set.univ).Adj x y) : walkKernel G hloc a x y = a := by
  have hh := (openSimpleGraph_univ_adj G x y).mp h
  simp only [walkKernel,ite_eq_right hh.1,ite_eq_left hh.2,zero_add]

end GeodesicSegments
end Percolation


namespace Percolation
section LogarithmicTailLength

 

theorem logarithmic_tail_power (ρ X : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hX : 0 < X) :
    ρ ^ ⌈(2/(-Real.log ρ))*Real.log X⌉₊ ≤ X^(-2:ℝ) := by
  have hl : Real.log ρ ≠ 0 := ne_of_lt (Real.log_neg hρ hρ1)
  calc
    _ = ρ ^ (⌈(2/(-Real.log ρ))*Real.log X⌉₊ : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ρ ^ ((2/(-Real.log ρ))*Real.log X) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1.le (Nat.le_ceil _)
    _ = X^(-2:ℝ) := by
      rw [Real.rpow_def_of_pos hρ,Real.rpow_def_of_pos hX]
      congr 1
      field_simp [hl]

 

theorem exists_uniform_logarithmic_tail_cutoff (ρ A : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (kmin : ℕ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ 1 < (-Real.log ρ)*C₁ ∧
      ∃ k₀ : ℕ, kmin ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        A*((k:ℝ)+1)*R*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊ ≤ 1/4 := by
  have hlambda : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  refine ⟨2/(-Real.log ρ),div_pos (by norm_num) hlambda,?_,max kmin ⌈4*A⌉₊,le_max_left _ _,?_⟩
  · rw [mul_div_cancel₀ _ (ne_of_gt hlambda)]
    norm_num
  · intro k hk R hR
    have hk' : ⌈4*A⌉₊ ≤ k := (le_max_right _ _).trans hk
    have hAk : 4*A ≤ (k:ℝ) := (Nat.le_ceil (4*A)).trans (by exact_mod_cast hk')
    have hkpos : 0 < (k:ℝ)+1 := by positivity
    have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
    let X : ℝ := ((k:ℝ)+1)*R
    have hX : 0 < X := mul_pos hkpos hRp
    have hXk : (k:ℝ)+1 ≤ X := by dsimp [X]; exact le_mul_of_one_le_right hkpos.le hR
    have hp := logarithmic_tail_power ρ X hρ hρ1 hX
    have hneg : X^(-2:ℝ) = (X^2)⁻¹ := by rw [Real.rpow_neg,show (2:ℝ) = (2:ℕ) by norm_num,Real.rpow_natCast]; exact hX.le
    calc
      _ = A*X*ρ^⌈(2/(-Real.log ρ))*Real.log X⌉₊ := by dsimp [X]; ring
      _ ≤ A*X*X^(-2:ℝ) := mul_le_mul_of_nonneg_left hp (mul_nonneg hA hX.le)
      _ = A/X := by rw [hneg]; field_simp [ne_of_gt hX]
      _ ≤ 1/4 := (div_le_iff₀ hX).mpr (by linarith)

end LogarithmicTailLength
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_CollisionTails
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
section IndependentRawCollisions
attribute [local instance] Classical.propDecidable Classical.decEq



theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  apply (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (A (lp.single 2 y (1:ℂ))) x).trans
  simpa using A.le_opNorm (lp.single 2 y (1:ℂ))

end IndependentRawCollisions
end Percolation


namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}



theorem mass_fromPositions (P : V → V → ℝ) (a : ℝ)
    (hP : ∀ x y, H.Adj x y → P x y = a)
    (k : ℕ) (f : Fin (k+1) → V) (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) :
    (fromPositions k f h).mass P = a^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change P (f 0) (f 1) * (fromPositions k (fun i => f i.succ) (fun i => h i.succ)).mass P = a^(k+1)
    have he : P (f 0) (f 1) = a := by simpa using hP _ _ (h 0)
    rw [he,ih,pow_succ']

end HoldingWalk
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

theorem position_append_left {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) (i : ℕ) (hi : i ≤ k) :
    (w.append v).position i = w.position i := by
  induction w generalizing i with
  | nil =>
    obtain rfl : i = 0 := by omega
    exact v.position_zero
  | hold w ih => cases i with
    | zero => rfl
    | succ i => exact ih v i (by omega)
  | step h w ih => cases i with
    | zero => rfl
    | succ i => exact ih v i (by omega)

theorem position_append_right {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) (i : ℕ) :
    (w.append v).position (k+i) = v.position i := by
  induction w with
  | nil => simp only [Nat.zero_add,append]
  | hold w ih => simpa only [Nat.succ_add,append,position] using ih v
  | step h w ih => simpa only [Nat.succ_add,append,position] using ih v

 

theorem ext_positions {k : ℕ} {x y : V} (w v : HoldingWalk H k x y)
    (h : ∀ i : ℕ, i ≤ k → w.position i = v.position i) : w = v := by
  induction k generalizing x y with
  | zero => cases w; cases v; rfl
  | succ k ih =>
    cases w with
    | hold w =>
      cases v with
      | hold v =>
        congr 1
        exact ih w v (fun i hi => h (i+1) (Nat.succ_le_succ hi))
      | step hv v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        exact (hv.ne he).elim
    | step hw w =>
      cases v with
      | hold v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        exact (hw.ne he.symm).elim
      | step hv v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        cases he
        congr 1
        exact ih w v (fun i hi => h (i+1) (Nat.succ_le_succ hi))

end HoldingWalk
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IntrinsicVisibleBlocks
attribute [local instance] Classical.propDecidable Classical.decEq

theorem positiveStem_mass (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ))
    (P : V → V → ℝ) (a : ℝ) (hP : ∀ x y, H.Adj x y → P x y = a) :
    (positiveStem H J s hs).mass P = a^J :=
  HoldingWalk.mass_fromPositions P a hP J _ _

theorem escapeLabelRaw_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    (escapeLabelRaw G J L m γ hγ ξ).mass (walkKernel G hloc a) =
      a^(J+J)*ξ.middle.mass (walkKernel G hloc a) := by
  simp only [escapeLabelRaw,HoldingWalk.mass_append,HoldingWalk.mass_reverse _ (walkKernel_symmetric G hloc a),
    positiveStem_mass _ _ _ _ _ a (fun _ _ h => walkKernel_step G hloc a h),pow_add]
  ring

theorem escapeLabelRaw_middle_position (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (i : ℕ) (hi : i ≤ L) :
    (escapeLabelRaw G J L m γ hγ ξ).position (J+i) = ξ.middle.position i := by
  rw [escapeLabelRaw,HoldingWalk.position_append_right,HoldingWalk.position_append_left _ _ i hi]

end IntrinsicVisibleBlocks
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace RawFrom
variable {H : SimpleGraph V}

 
theorem ext_positions {k : ℕ} {x : V} (w v : RawFrom H k x)
    (h : ∀ i : ℕ, i ≤ k → w.2.position i = v.2.position i) : w = v := by
  rcases w with ⟨y,w⟩
  rcases v with ⟨z,v⟩
  have he : y = z := by simpa only [HoldingWalk.position_length] using h k le_rfl
  subst z
  exact Sigma.ext rfl (heq_of_eq (HoldingWalk.ext_positions w v h))

end RawFrom



end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RootedRawProjection
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootedEscapeLabelRaw_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    (rootedEscapeLabelRaw G J L m γ hγ x ξ).2.mass (walkKernel G hloc a) =
      a^(J+J)*ξ.1.middle.mass (walkKernel G hloc a) := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact escapeLabelRaw_mass G hloc a J L m γ hγ ξ

theorem rootedEscapeLabelRaw_middle_position (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (i : ℕ) (hi : i ≤ L) :
    (rootedEscapeLabelRaw G J L m γ hγ x ξ).2.position (J+i) = ξ.1.middle.position i := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact escapeLabelRaw_middle_position G J L m γ hγ ξ i hi

theorem rootedEscapeLabelRaw_fiber_middle_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (ha : 0 < a) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x)
    (hw : rootedEscapeLabelRaw G J L m γ hγ x ξ = w) :
    ξ.1.middle.mass (walkKernel G hloc a) = w.2.mass (walkKernel G hloc a)/a^(J+J) := by
  apply (eq_div_iff (ne_of_gt (pow_pos ha _))).mpr
  rw [mul_comm,←rootedEscapeLabelRaw_mass G hloc a J L m γ hγ x ξ,hw]

theorem rootedEscapeLabelRaw_fiber_middle_positions (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x)
    (hw : rootedEscapeLabelRaw G J L m γ hγ x ξ = w) :
    ∀ i : ℕ, i ≤ L → ξ.1.middle.position i = w.2.position (J+i) := by
  intro i hi
  rw [←rootedEscapeLabelRaw_middle_position G J L m γ hγ x ξ i hi,hw]

end RootedRawProjection
end Percolation

 
namespace Percolation
section FiniteFiberDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_auxiliary_event_bound {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hs : ∑ a, μ a = 1)
    (B : α → Prop) (c : ℝ) (hc : 0 ≤ c) :
    (∑ a, if B a then c*μ a else 0) ≤ c := by
  calc
    _ ≤ ∑ a, c*μ a := Finset.sum_le_sum (fun a _ => by
      split_ifs; exact le_rfl; exact mul_nonneg hc (hμ a))
    _ = c := by rw [←Finset.mul_sum,hs,mul_one]

 

theorem finite_nested_unique_fiber_bound {β : Type*} [Fintype β]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    {T : (b : β) → γ b → Type*} [∀ b c, Fintype (T b c)]
    (μ : β → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (ν : (b : β) → (c : γ b) → T b c → ℝ) (hν : ∀ b c t, 0 ≤ ν b c t)
    (hs : ∀ b c, ∑ t, ν b c t = 1)
    (B : (b : β) → (c : γ b) → T b c → Prop)
    (N C : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hcard : ∀ b, (Fintype.card (γ b) : ℝ) ≤ N)
    (hunique : ∀ b c t b' c' t', B b c t → B b' c' t' → b = b')
    (hbound : ∀ b c t, B b c t → μ b ≤ C) :
    (∑ b, ∑ c, ∑ t, if B b c t then μ b*ν b c t else 0) ≤ N*C := by
  by_cases hh : ∃ b c t, B b c t
  · obtain ⟨b,c,t,hb⟩ := hh
    have he : (∑ b', ∑ c', ∑ t', if B b' c' t' then μ b'*ν b' c' t' else 0) =
        ∑ c', ∑ t', if B b c' t' then μ b*ν b c' t' else 0 := by
      apply Finset.sum_eq_single b
      · intro b' _ hne
        apply Finset.sum_eq_zero
        intro c' _
        apply Finset.sum_eq_zero
        intro t' _
        exact ite_eq_right (fun hb' => hne (hunique b' c' t' b c t hb' hb))
      · simp
    rw [he]
    calc
      _ ≤ ∑ _c : γ b, μ b := Finset.sum_le_sum (fun c' _ =>
        finite_auxiliary_event_bound (ν b c') (hν b c') (hs b c') (B b c') (μ b) (hμ b))
      _ = (Fintype.card (γ b) : ℝ)*μ b := by simp
      _ ≤ N*C := mul_le_mul (hcard b) (hbound b c t hb) (hμ b) hN
  · have hz : ∀ b c t, ¬B b c t := by simpa only [not_exists] using hh
    simp only [hz,ite_false,Finset.sum_const_zero]
    exact mul_nonneg hN hC

end FiniteFiberDomination
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CodeMiddleIdentities
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem labelFromCode_middle_position (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) (i : ℕ) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.middle.position i =
      c.2.1.2.position i := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

theorem labelFromCode_middle_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (P : V → V → ℝ)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.middle.mass P =
      c.2.1.2.mass P := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

end CodeMiddleIdentities
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralFiberEstimate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rooted_code_single_anchor_fiber_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (s : segmentAnchors G hloc γ n hdiam (segmentCenter J) x)
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val (Fin.last (J+J))),
      ∑' h : segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) mid.1,
        ∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val 0) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val 0),
          if rootedEscapeLabelRaw G J L m γ hγ x
              (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
                ⟨s,mid,h,tails⟩) = w then
            mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
              tails.2.2.mass (walkKernel G hloc a) else 0) ≤
      ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
        (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  simp only [tsum_fintype,mul_assoc]
  convert finite_nested_unique_fiber_bound
    (β := RawFrom (openSimpleGraph G Set.univ) L (s.val (Fin.last (J+J))))
    (γ := fun mid => segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) mid.1)
    (T := fun _ h => RawFrom (openSimpleGraph G Set.univ) m (s.val 0) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val 0))
    (fun mid => mid.2.mass (walkKernel G hloc a))
    (fun mid => mid.2.mass_nonneg _ hK)
    (fun _ _ tails => tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a))
    (fun _ _ tails => mul_nonneg (tails.1.2.mass_nonneg _ hK) (tails.2.2.mass_nonneg _ hK)) ?_
    (fun mid h tails => rootedEscapeLabelRaw G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) = w)
    (((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ))
    (w.2.mass (walkKernel G hloc a)/a^(J+J)) ?_ ?_ ?_ ?_ ?_ using 1
  · apply Finset.sum_congr rfl
    intro mid _
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro tails _
    split_ifs <;> rfl
  · intro mid h
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    simpa only [tsum_fintype,mul_one] using congrArg₂ (fun r s : ℝ => r*s)
      (rawFrom_probability_sum G hloc a m (s.val 0))
      (rawFrom_probability_sum G hloc a m (h.val 0))
  · positivity
  · exact div_nonneg (w.2.mass_nonneg _ hK) (pow_nonneg ha.le _)
  · intro mid
    rw [Fintype.card_coe,segmentAnchors_card_eq_indicator G hloc γ n hdiam (Fin.last (J+J)) mid.1]
    split_ifs
    · exact le_rfl
    · exact_mod_cast Nat.zero_le _
  · intro mid h tails mid' h' tails' hh hh'
    apply RawFrom.ext_positions
    intro i hi
    have he := rootedEscapeLabelRaw_fiber_middle_positions G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) w hh i hi
    have he' := rootedEscapeLabelRaw_fiber_middle_positions G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid',h',tails'⟩) w hh' i hi
    have hm := labelFromCode_middle_position G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩ i
    have hm' := labelFromCode_middle_position G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid',h',tails'⟩ i
    exact hm.symm.trans (he.trans (he'.symm.trans hm'))
  · intro mid h tails hh
    have he := rootedEscapeLabelRaw_fiber_middle_mass G hloc a ha J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) w hh
    have hm := labelFromCode_middle_mass G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x (walkKernel G hloc a) ⟨s,mid,h,tails⟩
    exact (hm.symm.trans he).le

end LiteralFiberEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralProjectionDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem rooted_label_raw_fiber_mass_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if rootedEscapeLabelRaw G J L m γ hγ x ξ = w then ξ.1.mass (walkKernel G hloc a) else 0) ≤
      ((segmentAnchors G hloc γ n hdiam (segmentCenter J) x).card : ℝ) *
      ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
        (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let R := rootedLabelEquiv G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  calc
    _ ≤ ∑' _s : segmentAnchors G hloc γ n hdiam (segmentCenter J) x,
        ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
          (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
      apply (summable_of_hasFiniteSupport (Set.toFinite _)).tsum_le_tsum _
        (summable_of_hasFiniteSupport (Set.toFinite _))
      intro s
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      conv_lhs => arg 1; ext mid; rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      exact rooted_code_single_anchor_fiber_bound G hloc a ha hK J L m γ hγ n hdiam x s w
    _ = _ := by
      simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring

end LiteralProjectionDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedProjection
attribute [local instance] Classical.propDecidable Classical.decEq

theorem tsum_indicator_div {α : Type*} (f : α → ℝ) (B : α → Prop) [DecidablePred B] (d : ℝ) :
    (∑' a, if B a then f a/d else 0) = (∑' a, if B a then f a else 0)/d := by
  rw [←tsum_div_const]
  apply tsum_congr
  intro a
  split_ifs <;> simp

theorem rooted_label_raw_projection_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if rootedEscapeLabelRaw G J L m γ hγ x ξ = w then
        escapeLabelProbability G hloc a γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) ≤
      w.2.mass (walkKernel G hloc a)/(a^(J+J)*q) := by
  have hN (i : Fin (J+J+1)) : 0 < ((segmentAnchors G hloc γ n hdiam i (γ i)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i (γ i)).mpr
      (by exact ⟨Equiv.refl V,Equiv.refl E,(fun e => by simp),rfl⟩))
  have hQ := hq.trans_le hqle
  have hA := pow_pos ha (J+J)
  have hm := w.2.mass_nonneg (walkKernel G hloc a) hK
  simp only [escapeLabelProbability,tsum_indicator_div]
  have hb := rooted_label_raw_fiber_mass_bound G hloc a ha hK J L m γ hγ n hdiam x w
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam (segmentCenter J) x hx] at hb
  apply (div_le_div_of_nonneg_right hb (mul_nonneg (mul_nonneg (hN (segmentCenter J)).le (hN (Fin.last (J+J))).le) hQ.le)).trans
  calc
    _ = w.2.mass (walkKernel G hloc a)/
        (a^(J+J)*segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J)))) := by
      field_simp [(hN (segmentCenter J)).ne', (hN (Fin.last (J+J))).ne']
    _ ≤ _ := div_le_div_of_nonneg_left hm (mul_pos hA hq) (mul_le_mul_of_nonneg_left hqle hA.le)

end NormalizedProjection
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PositiveEscapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Escapes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
section QuantitativeEarlyCutoff



theorem earlyCollisionCost_tendsto (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Filter.Tendsto (earlyCollisionCost ρ) Filter.atTop (nhds 0) := by
  have hn : ‖ρ‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hρ] using hρ1
  have ht : Filter.Tendsto (fun J : ℕ => (J:ℝ)*ρ^J) Filter.atTop (nhds 0) := by
    simpa only [pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1 hn).tendsto_atTop_zero
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1
  have hh := (((ht.add hp).const_mul 2).div_const (1-ρ)).add ((hp.const_mul 2).div_const ((1-ρ)^2))
  have he : earlyCollisionCost ρ = (fun J : ℕ => 2*((J:ℝ)*ρ^J+ρ^J)/(1-ρ)+2*ρ^J/(1-ρ)^2) := by
    funext J
    unfold earlyCollisionCost
    ring
  rw [he]
  simpa only [zero_add,mul_zero,zero_div] using hh

theorem exists_earlyCollisionCutoff (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → earlyCollisionCost ρ J < ε := by
  exact Filter.eventually_atTop.mp ((earlyCollisionCost_tendsto ρ hρ hρ1).eventually (gt_mem_nhds hε))

end QuantitativeEarlyCutoff
end Percolation


namespace Percolation
section FirstEscapeChoiceOrder

 

theorem exists_first_escape_uniform_cutoffs (ρ c ε : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      2*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L) < ε := by
  have hδ : 0 < ε/(4*c) := div_pos hε (by positivity)
  obtain ⟨J₀,hJ₀⟩ := exists_earlyCollisionCutoff ρ hρ hρ1 (ε/(4*c)) hδ
  let J := max J₀ 1
  have hJ : 0 < J := lt_of_lt_of_le (by omega : 0 < 1) (le_max_right _ _)
  have he : earlyCollisionCost ρ J < ε/(4*c) := hJ₀ J (le_max_left _ _)
  have hel : 2*c*earlyCollisionCost ρ J < ε := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*c)).mp he
    nlinarith
  have ht : Filter.Tendsto
      (fun L : ℕ => 2*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L))
      Filter.atTop (nhds (2*c*earlyCollisionCost ρ J)) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul
      (suffixCollisionCost ρ c J)).const_add (earlyCollisionCost ρ J)
    have hh' := hh.const_mul (2*c)
    simpa only [mul_zero,add_zero] using hh'
  obtain ⟨L₀,hL₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hel))
  exact ⟨J,hJ,L₀,hL₀⟩

end FirstEscapeChoiceOrder
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralGeodesicSeparation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem graph_dist_aut (G : BondGraph V E) (hconn : Connected G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) :
    (openSimpleGraph G Set.univ).dist (a x) (a y) =
      (openSimpleGraph G Set.univ).dist x y := by
  have hreach (x y : V) : (openSimpleGraph G Set.univ).Reachable x y :=
    (conn_iff_reachable G Set.univ x y).mp (conn_univ_of_connected G hconn x y)
  obtain ⟨q,hq⟩ := (hreach x y).exists_walk_length_eq_dist
  obtain ⟨r,hr⟩ := (hreach (a x) (a y)).exists_walk_length_eq_dist
  have hq' := SimpleGraph.dist_le (q.map (autSimpleGraph G hab).toHom)
  have hr' := SimpleGraph.dist_le (r.map (autSimpleGraph G (isAut_symm G hab)).toHom)
  simp only [SimpleGraph.Walk.length_map,hq] at hq'
  change (openSimpleGraph G Set.univ).dist (a.symm (a x)) (a.symm (a y)) ≤ _ at hr'
  simp only [a.symm_apply_apply,SimpleGraph.Walk.length_map,hr] at hr'
  exact le_antisymm hq' hr'



end LiteralGeodesicSeparation
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ProjectionEvents
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_event_fiber_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (μ : α → ℝ) (B : β → Prop) [DecidablePred B] :
    (∑ a, if B (f a) then μ a else 0) =
      ∑ b, if B b then ∑ a, if f a = b then μ a else 0 else 0 := by
  calc
    _ = ∑ a, ∑ b, if B b then (if f a = b then μ a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      have hf : (fun b => if B b then (if f a = b then μ a else 0) else 0) =
          fun b => if f a = b then (if B (f a) then μ a else 0) else 0 := by
        funext b
        by_cases h : f a = b
        · subst b
          simp
        · simp [h]
      rw [hf]
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : B b <;> simp [h]

 

theorem rooted_label_raw_event_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (B : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x → Prop) [DecidablePred B] :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if B (rootedEscapeLabelRaw G J L m γ hγ x ξ) then
        escapeLabelProbability G hloc a γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) ≤
      (∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x,
        if B w then w.2.mass (walkKernel G hloc a) else 0)/(a^(J+J)*q) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let : Fintype {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} := Fintype.ofFinite _
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) := Fintype.ofFinite _
  rw [←tsum_indicator_div]
  simp only [tsum_fintype]
  rw [finite_event_fiber_sum]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : B w
  · simp only [hw,ite_true]
    simpa only [tsum_fintype] using
      rooted_label_raw_projection_bound G hloc a ha hK J L m γ hγ n hdiam x hx q hq hqle w
  · simp only [hw,ite_false,le_refl]

end ProjectionEvents
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_SelectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
section BothEscapeChoiceOrder

 

theorem exists_both_escape_uniform_cutoffs (ρ c ε : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L) < ε := by
  obtain ⟨J,hJ,L₀,hL₀⟩ := exists_first_escape_uniform_cutoffs ρ c (ε/2) hρ hρ1 hc (by positivity)
  refine ⟨J,hJ,L₀,fun L hL => ?_⟩
  have hh := hL₀ L hL
  linarith

end BothEscapeChoiceOrder
end Percolation


namespace Percolation
section JointSelectionChoiceOrder

 

theorem exists_joint_collision_potential_cutoffs (ρ c d τ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hd : 0 ≤ d) (hτ : 0 < τ) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∃ C₁ : ℝ, 0 < C₁ ∧ 1 < (-Real.log ρ)*C₁ ∧
      ∃ k₀ : ℕ, J+J+L₀ ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^(k-(J+J))) +
          2*((d+1)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) ≤ 3/8 := by
  obtain ⟨J,hJ,L₀,hL₀⟩ := exists_both_escape_uniform_cutoffs ρ c (1/8) hρ.le hρ1 hc (by norm_num)
  let A : ℝ := 2*(d+1)*Real.sqrt c/τ
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.sqrt_nonneg _)) hτ.le
  obtain ⟨C₁,hC₁,hlam,k₀,hk₀,hk⟩ := exists_uniform_logarithmic_tail_cutoff ρ A hρ hρ1 hA (J+J+L₀)
  refine ⟨J,hJ,L₀,C₁,hC₁,hlam,k₀,hk₀,fun k hk' R hR => ?_⟩
  have hL : L₀ ≤ k-(J+J) := by omega
  have hb := hL₀ (k-(J+J)) hL
  have hp := hk k hk' R hR
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have he : 2*((d+1)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) =
      A*((k:ℝ)+1)*R*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊ := by
    dsimp only [A]
    field_simp [hτ.ne',hRp.ne']
  rw [he]
  linarith

end JointSelectionChoiceOrder
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PathSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SelectedRawMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootedEscapeLabelRaw_corridor (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    (⟨x,rootedEscapeLabelRaw G J L m γ hγ x ξ⟩ : RawCorridor G ((J+L)+J)) =
      labelCorridor G J L m γ hγ ξ.1 := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  rfl

 

theorem selected_raw_mass_of_label_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) (J+J)) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (p : unitInterval) (t b : ℝ)
    (hb : b ≤ ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if (labelCorridor G J L m γ hγ ξ.1).Selected hloc p (J+m) t then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) :
    b*(a^(J+J)*q) ≤ ∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x,
      if RawCorridor.Selected hloc p (J+m) t (⟨x,w⟩ : RawCorridor G ((J+L)+J)) then
        w.2.mass (walkKernel G hloc a) else 0 := by
  have hh := rooted_label_raw_event_bound G hloc a ha hK J L m γ hγ (J+J) hdiam x hx
    q hq hqle (fun w => RawCorridor.Selected hloc p (J+m) t (⟨x,w⟩ : RawCorridor G ((J+L)+J)))
  simp only [rootedEscapeLabelRaw_corridor] at hh
  exact (le_div_iff₀ (mul_pos (pow_pos ha _) hq)).mp (hb.trans hh)

end SelectedRawMass

section FullSelectionCutoffs
 

theorem exists_full_selection_cutoffs (ρ c d τ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hd : 0 ≤ d) (hτ : 0 < τ) :
    ∃ J : ℕ, 0 < J ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ k₀ : ℕ, J+J ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^(k-(J+J))) +
          2*((3*d+3)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) +
          2*c*(d+1)^2*Real.sqrt c*ρ^(k-(J+J)) ≤ 1/2 := by
  obtain ⟨J,hJ,L₀,C₁,hC₁,_,k₀,hk₀,hk⟩ :=
    exists_joint_collision_potential_cutoffs ρ c (3*d+2) τ hρ hρ1 hc (by linarith) hτ
  have ht : Filter.Tendsto (fun L : ℕ => 2*c*(d+1)^2*Real.sqrt c*ρ^L) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul
      (2*c*(d+1)^2*Real.sqrt c)
  obtain ⟨L₁,hL₁⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1/8 by norm_num)))
  refine ⟨J,hJ,C₁,hC₁,max k₀ (J+J+L₁),by omega,fun k hk' R hR => ?_⟩
  have h₁ := hk k (le_trans (le_max_left _ _) hk') R hR
  have h₂ := hL₁ (k-(J+J)) (by omega)
  have he : 3*d+2+1 = 3*d+3 := by ring
  rw [he] at h₁
  linarith
end FullSelectionCutoffs
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FullPathSelection
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem exists_selected_path_mass_oai [Countable V] [Countable E] [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (τ : ℝ) (hτ : 0 < τ) :
    ∃ J : ℕ, ∃ C₁ : ℝ, ∃ k₀ : ℕ, ∃ b : ℝ,
      0 < J ∧ 0 < C₁ ∧ 3 ≤ k₀ ∧ 0 < b ∧
      ∀ p : unitInterval, (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        b ≤ rawPathAverage G (walkKernel G hloc a) k root weight
          (fun w => if w.Selected hloc p (J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊) (τ/R) then 1 else 0) := by
  let x₀ : V := Classical.arbitrary V
  have hρpos : 0 < ‖P‖ := by
    have hh := (hdiag x₀).trans ((Complex.re_le_norm _).trans (matrixCoeff_norm_le P x₀ x₀))
    linarith
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  obtain ⟨J,hJ,C₁,hC₁,k₀,hJk,hcut⟩ := exists_full_selection_cutoffs ‖P‖ c d τ hρpos hρ hc (Nat.cast_nonneg d) hτ
  obtain ⟨y,q,hqN,hq⟩ := exists_geodesic_length G hloc hconn x₀ (J+J)
  let γ := geodesicSegment G q (J+J)
  have hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ) :=
    fun i => geodesicSegment_adj G q (J+J) hqN i.val i.isLt
  have hinj : Function.Injective γ := geodesicSegment_injective G q (J+J) hqN hq
  have hdiam := geodesicSegment_diameter G q (J+J) hqN
  have hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (segmentPositiveIndex J i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s (Fin.last (J+J))) (s (segmentNegativeIndex J i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (Fin.last (J+J))) := by
    rintro s ⟨g,e,hge,rfl⟩
    constructor
    · intro i
      change J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert 0)) (g (q.getVert (J+i.val)))
      rw [graph_dist_aut G hconn hge,geodesic_getVert_dist _ q hq 0 (J+i.val) (by omega) (by omega)]
      omega
    constructor
    · intro i
      change J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert (J+J))) (g (q.getVert i.val))
      rw [graph_dist_aut G hconn hge,SimpleGraph.dist_comm,
        geodesic_getVert_dist _ q hq i.val (J+J) (by omega) (by omega)]
      omega
    · change 2*J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert 0)) (g (q.getVert (J+J)))
      rw [graph_dist_aut G hconn hge,geodesic_getVert_dist _ q hq 0 (J+J) (by omega) (by omega)]
      omega
  obtain ⟨i,g,hg,hgx⟩ := hcov (γ (segmentCenter J))
  obtain ⟨e,he⟩ := hg
  have hx : root i ∈ vertexOrbit G (γ (segmentCenter J)) :=
    ⟨g.symm,e.symm,isAut_symm G he,by rw [←hgx,g.symm_apply_apply]⟩
  let b : ℝ := weight i * ((1/2)*(a^(J+J)*(1/(2*c))))
  have hb : 0 < b := mul_pos (hw i) (mul_pos (by norm_num)
    (mul_pos (pow_pos ha _) (by positivity)))
  refine ⟨J,C₁,max k₀ 3,b,hJ,hC₁,le_max_right _ _,hb,?_⟩
  intro p _hpnear hp k hk R hR
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hJk' : J+J ≤ k := hJk.trans hk₀
  obtain ⟨L,rfl⟩ : ∃ L : ℕ, (J+L)+J = k := ⟨k-(J+J),by omega⟩
  let m' := ⌈C₁*Real.log ((((((J+L)+J):ℕ):ℝ)+1)*R)⌉₊
  obtain ⟨A,hA⟩ := operatorBounded_of_lt_pc G hloc hqt p hp
  have hcost := hcut ((J+L)+J) hk₀ R hR
  have hL : (J+L)+J-(J+J) = L := by omega
  rw [hL] at hcost
  have hcost' :
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
      2*((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)*Real.sqrt c*‖P‖^m')/(τ/R) +
      2*c*(((d+1)^2:ℕ):ℝ)*Real.sqrt c*‖P‖^L ≤ 1/2 := by
    simpa only [m',Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hcost
  have hl := rooted_selected_label_mass_lower G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA J L m' γ hinj hγ hdiam (root i) hx hρ hsep d hd (τ/R)
    (div_pos hτ (lt_of_lt_of_le zero_lt_one hR))
  have hhalf : (1/2:ℝ) ≤ ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m' // ξ.first (segmentCenter J) = root i},
      if (labelCorridor G J L m' γ hγ ξ.1).Selected hloc p (J+m') (τ/R) then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m' ξ.1 else 0 := by
    linarith
  have hqreturn := segmentReturnMass_uniform_lower G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ (Fin.last (J+J)) L
  have hmraw := selected_raw_mass_of_label_mass G hloc a ha hK J L m' γ hγ hdiam (root i) hx
    (1/(2*c)) (by positivity) hqreturn p (τ/R) (1/2) hhalf
  have hroot := mul_le_mul_of_nonneg_left hmraw (hw i).le
  apply hroot.trans
  unfold rawPathAverage
  have hall (r : ι) : 0 ≤ weight r * ∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) (root r),
      w.2.mass (walkKernel G hloc a) *
        (if RawCorridor.Selected hloc p (J+m') (τ/R) ⟨root r,w⟩ then 1 else 0) := by
    apply mul_nonneg (hw r).le
    apply tsum_nonneg
    intro w
    apply mul_nonneg (w.2.mass_nonneg _ hK)
    split_ifs <;> norm_num
  have hi := Finset.single_le_sum (s := Finset.univ) (fun r _ => hall r) (Finset.mem_univ i)
  simpa only [mul_ite,mul_one,mul_zero] using hi

end FullPathSelection
end Percolation

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.exists_selected_path_mass_oai.{u, v, u_1} := @OAI.Percolation.exists_selected_path_mass_oai.{u, v, u_1}
