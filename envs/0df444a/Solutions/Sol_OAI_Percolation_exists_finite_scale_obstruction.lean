-- Prove2me | solution 1 for OAI.Percolation.exists_finite_scale_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:05:49.950258+00:00
-- url     : https://prove2.me/submissions/7e71b93c-b58d-4e8d-9a7c-0158fad1673f

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_deformed_root_sum_retained
import Theorems.Thm_OAI_Percolation_exists_selected_path_mass
import Theorems.Thm_OAI_Percolation_exists_uniform_averaged_decrease
import Theorems.Thm_OAI_Percolation_exists_uniform_deformed_row_comparison

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

section Kernel
attribute [local instance] Classical.propDecidable

 
theorem kernel_extension_unique {K : V → V → ℂ}
    {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : ∀ x y, (A (lp.single 2 y (1 : ℂ))) x = K x y)
    (hB : ∀ x y, (B (lp.single 2 y (1 : ℂ))) x = K x y) : A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro y
  apply ContinuousLinearMap.ext
  intro z
  apply lp.ext
  funext x
  have hz : lp.single (E := fun _ : V => ℂ) 2 y z =
      z • lp.single (E := fun _ : V => ℂ) 2 y (1 : ℂ) := by
    simpa using (lp.single_smul (E := fun _ : V => ℂ) 2 y z (1 : ℂ))
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    lp.singleContinuousLinearMap_apply, hz, map_smul, lp.coeFn_smul, Pi.smul_apply,
    hA, hB]

theorem HasKernel.unique {G : BondGraph V E} {p : unitInterval}
    {A B : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G p A) (hB : HasKernel G p B) :
    A = B := kernel_extension_unique hA hB


end Kernel

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


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section TriangleDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_realTriangleTerm [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab => realTriangleTerm G x ab (p:ℝ)) := by
  simp only [realTriangleTerm,realTwoPoint_coe]
  apply (summable_twoPoint_pair G hloc hqt p hp x).of_nonneg_of_le
  · intro ab
    exact mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_nonneg G p _ _)
  · intro ab
    exact mul_le_of_le_one_right (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_le_one G p _ _)

end TriangleDerivative
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

 
theorem PositiveRealMatrix.triple_hasSum
    {A B C : Hilbert V →L[ℂ] Hilbert V}
    (hA : PositiveRealMatrix A) (hB : PositiveRealMatrix B) (hC : PositiveRealMatrix C)
    (x y : V) :
    HasSum (fun ab : V×V => (matrixCoeff A x ab.1).re * (matrixCoeff B ab.1 ab.2).re *
      (matrixCoeff C ab.2 y).re) (matrixCoeff (A*B*C) x y).re := by
  have hi (a : V) : HasSum (fun b => (matrixCoeff A x a).re * (matrixCoeff B a b).re * (matrixCoeff C b y).re)
      ((matrixCoeff A x a).re * (matrixCoeff (B*C) a y).re) := by
    simpa only [mul_assoc] using (hB.mul_hasSum C a y).mul_left (matrixCoeff A x a).re
  have ho := hA.mul_hasSum (B*C) x y
  have hs : Summable (fun ab : V×V => (matrixCoeff A x ab.1).re * (matrixCoeff B ab.1 ab.2).re * (matrixCoeff C ab.2 y).re) := by
    apply (summable_prod_of_nonneg (f := fun ab : V×V => (matrixCoeff A x ab.1).re * (matrixCoeff B ab.1 ab.2).re * (matrixCoeff C ab.2 y).re)
      (fun ab => mul_nonneg (mul_nonneg (hA _ _).2 (hB _ _).2) (hC _ _).2)).mpr
    refine ⟨fun a => (hi a).summable,?_⟩
    simp only [(hi _).tsum_eq]
    exact ho.summable
  have he : (∑' ab : V×V, (matrixCoeff A x ab.1).re * (matrixCoeff B ab.1 ab.2).re * (matrixCoeff C ab.2 y).re) =
      (matrixCoeff (A*B*C) x y).re := by
    rw [hs.tsum_prod]
    simp only [(hi _).tsum_eq]
    rw [ho.tsum_eq,mul_assoc]
  exact he ▸ hs.hasSum

theorem HasKernel.matrixCoeff_re (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    (matrixCoeff T x y).re = twoPoint G p x y := by
  change (T (lp.single 2 y (1:ℂ)) x).re = _
  rw [hT x y,Complex.ofReal_re]

theorem realTriangle_eq_matrixCoeff (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x : V) :
    realTriangle G x (p:ℝ) = (matrixCoeff (T^3) x x).re := by
  have ht := hT.positiveRealMatrix G p T
  have hs := ht.triple_hasSum ht ht x x
  rw [show T*T*T = T^3 by simp only [pow_succ,pow_zero,one_mul]] at hs
  simpa only [HasKernel.matrixCoeff_re G p T hT,realTriangle,realTriangleTerm,realTwoPoint_coe] using hs.tsum_eq

theorem rootTriangle_eq_trace (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) :
    rootTriangle G root weight (p:ℝ) = (rootTrace root weight (T^3)).re := by
  simp only [rootTriangle,realTriangle_eq_matrixCoeff G p T hT,rootTrace,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end PositiveTriangleSeries
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RootTriangleRusso
attribute [local instance] Classical.propDecidable Classical.decEq


theorem realTriangle_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ realTriangle G x (p:ℝ) := by
  have hh := (summable_realTriangleTerm G hloc hqt p hp x).le_tsum (x,x)
    (fun ab _ => by
      simp only [realTriangleTerm,realTwoPoint_coe]
      exact mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_nonneg G p _ _))
  simpa only [realTriangleTerm,realTwoPoint_coe,twoPoint_self,mul_one,realTriangle] using hh

theorem rootTriangle_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ rootTriangle G root weight (p:ℝ) := by
  calc
    1 = ∑ i, weight i * 1 := by simpa using hw1.symm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (realTriangle_one_le G hloc hqt p hp (root i)) (hw i))

end RootTriangleRusso
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceNumerics
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem HasKernel.norm_le_susceptibility_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, susceptibility G p x ≤ C) :
    ‖T‖ ≤ C := by
  have hr (x : V) (s : Finset V) : ∑ y ∈ s, twoPoint G p x y ≤ C :=
    ((summable_twoPoint_subcritical G hloc hqt p hp x).sum_le_tsum s
      (fun y _ => twoPoint_nonneg G p x y)).trans (hb x)
  obtain ⟨S,hS,hK⟩ := exists_operator_of_row_column_bound (twoPoint G p) C hC (twoPoint_nonneg G p)
    hr (fun y s => by simpa only [twoPoint_symm G p] using hr y s)
  rwa [hT.unique hK]

end TraceNumerics
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

theorem HasKernel.norm_le_maxSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : ‖T‖ ≤ maxSusceptibility G p :=
  hT.norm_le_susceptibility_bound G hloc hqt p hp T _
    (le_trans zero_le_one (maxSusceptibility_one_le G hloc hqt p hp))
    (susceptibility_le_max G hloc hqt p hp)

theorem HasKernel.norm_one_le [Countable E] [Nonempty V]
    (G : BondGraph V E) (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : 1 ≤ ‖T‖ := by
  let x : V := Classical.choice inferInstance
  have hd : twoPoint G p x x = 1 := twoPoint_self G p x
  have hh := (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (T (lp.single 2 x (1:ℂ))) x).trans (T.le_opNorm (lp.single 2 x (1:ℂ)))
  simpa [hT x x,hd,lp.norm_single] using hh

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
open MeasureTheory
section ExteriorWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

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


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteNeighborhoodMass
attribute [local instance] Classical.propDecidable Classical.decEq

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

theorem counted_base_mem_cluster (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : w.counted D ω x y) : w.base ∈ cluster G ω x := by
  obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2.1
  have hm := w.counted_base_mem_walk D ω x y hc q
  exact conn_mono G Set.inter_subset_left ((conn_iff_reachable G _ x w.base).mpr ⟨q.takeUntil w.base hm⟩)

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

 

theorem corridorPenalty_le_cluster (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) (hf : (cluster G ω x).Finite) :
    corridorPenalty G (walkKernel G hloc a) p k D ω x y ≤
      ((cluster G ω x).ncard:ℝ)*(rawWeightBase r q d)^k := by
  exact raw_weight_sum_le_on_bases G hloc d hd a hP p hr hq hrp hqp k _ hf
    (fun w => w.counted D ω x y) (fun w hw => w.counted_base_mem_cluster D ω x y hw)

 

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
open MeasureTheory
section LiteralDeformationDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_eq_zero_of_not_conn (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) (hn : ¬Conn G ω x y) :
    deformedConnection G P p k t D ω x y = 0 := by
  have hnc : ¬Conn G (ω ∩ internalEdges G D) x y := fun h => hn (conn_mono G Set.inter_subset_left h)
  simp only [deformedConnection,hnc,and_false,ite_false]

theorem deformedClusterMass_eq_sum (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : deformedClusterMass G P p k t D ω x =
      ∑ y ∈ hf.toFinset, deformedConnection G P p k t D ω x y := by
  apply tsum_eq_sum
  intro y hy
  exact deformedConnection_eq_zero_of_not_conn G P p k t D ω x y (fun h => hy (hf.mem_toFinset.mpr h))

theorem deformedDerivativeMass_eq_sum (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : deformedDerivativeMass G P p k t D ω x =
      ∑ y ∈ hf.toFinset, corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y := by
  apply tsum_eq_sum
  intro y hy
  rw [deformedConnection_eq_zero_of_not_conn G P p k t D ω x y (fun h => hy (hf.mem_toFinset.mpr h)),mul_zero]

theorem measurable_deformedDerivativeMass [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    Measurable (fun ω => deformedDerivativeMass G P p k t D ω x) :=
  Measurable.tsum (fun y => (measurable_corridorPenalty G P p k D x y).mul
    (measurable_deformedConnection G P p k t D x y))

theorem deformedDerivativeMass_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ)
    (D : Set V) (ω : Set E) (x : V) : 0 ≤ deformedDerivativeMass G P p k t D ω x :=
  tsum_nonneg (fun y => mul_nonneg (corridorPenalty_nonneg G P hP p k D ω x y)
    (deformedConnection_nonneg G P p k t D ω x y))

theorem hasDerivAt_deformedConnection (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    HasDerivAt (fun s => deformedConnection G P p k s D ω x y)
      (-(corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y)) t := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · simp only [deformedConnection,hc,and_self,ite_true]
    simpa only [Pi.neg_apply,id_eq,neg_mul,one_mul,mul_neg,mul_comm] using
      (((hasDerivAt_id t).neg.mul_const (corridorPenalty G P p k D ω x y)).exp)
  · simpa only [deformedConnection,hc,ite_false,mul_zero,neg_zero] using hasDerivAt_const t (0:ℝ)

 

theorem hasDerivAt_deformedClusterMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) :
    HasDerivAt (fun s => deformedClusterMass G P p k s D ω x)
      (-deformedDerivativeMass G P p k t D ω x) t := by
  have hh := HasDerivAt.fun_sum (u := hf.toFinset) (fun y _ => hasDerivAt_deformedConnection G P p k t D ω x y)
  simpa only [deformedClusterMass_eq_sum G P p k _ D ω x hf,
    deformedDerivativeMass_eq_sum G P p k t D ω x hf,Finset.sum_neg_distrib] using hh

end LiteralDeformationDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationDerivativeDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedDerivativeMass_le_square (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    deformedDerivativeMass G (walkKernel G hloc a) p k t D ω x ≤
      ((cluster G ω x).ncard:ℝ)^2 * (rawWeightBase p (1-(p:ℝ)) d)^k := by
  rw [deformedDerivativeMass_eq_sum G (walkKernel G hloc a) p k t D ω x hf]
  calc
    _ ≤ ∑ _y ∈ hf.toFinset, ((cluster G ω x).ncard:ℝ)*(rawWeightBase p (1-(p:ℝ)) d)^k := by
      apply Finset.sum_le_sum
      intro y _
      have hn := corridorPenalty_nonneg G (walkKernel G hloc a) hP p k D ω x y
      exact (mul_le_of_le_one_right hn (deformedConnection_le_one G (walkKernel G hloc a) hP p k t ht D ω x y)).trans
        (corridorPenalty_le_cluster G hloc d hd a hP p hp0 (sub_pos.mpr hp1) le_rfl le_rfl k D ω x y hf)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
      ring

end DeformationDerivativeDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section DeformationDifferentiation
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem hasDerivAt_deformedSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 < t)
    (D : Set V) (x : V) :
    HasDerivAt (fun s => deformedSusceptibility G (walkKernel G hloc a) p k s D x)
      (-(∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t D ω x ∂law p)) t := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  have hp1 : (p:ℝ) < 1 := (show (p:ℝ) < (pc G:ℝ) from hp).trans_le (pc G).2.2
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := law p) (s := Set.Ioi 0) (x₀ := t)
    (F := fun s ω => deformedClusterMass G (walkKernel G hloc a) p k s D ω x)
    (F' := fun s ω => -deformedDerivativeMass G (walkKernel G hloc a) p k s D ω x)
    (bound := fun ω => ((cluster G ω x).ncard:ℝ)^2*(rawWeightBase p (1-(p:ℝ)) d)^k)
    (Ioi_mem_nhds ht)
    (Filter.Eventually.of_forall (fun s => (measurable_deformedClusterMass G (walkKernel G hloc a) p k s D x).aestronglyMeasurable))
    (integrable_deformedClusterMass G hloc hqt (walkKernel G hloc a) hP p hp k t ht.le D x)
    (measurable_deformedDerivativeMass G (walkKernel G hloc a) p k t D x).neg.aestronglyMeasurable
    (by
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      intro s hs
      rw [norm_neg,Real.norm_of_nonneg (deformedDerivativeMass_nonneg G (walkKernel G hloc a) hP p k s D ω x)]
      exact deformedDerivativeMass_le_square G hloc d hd a hP p hp0 hp1 k s hs.le D ω x hω)
    ((hs x).1.mul_const _)
    (by
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      intro s _
      exact hasDerivAt_deformedClusterMass G (walkKernel G hloc a) p k s D ω x hω)
  rw [integral_neg] at hder
  apply hder.2.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact deformedSusceptibility_eq_integral G hloc hqt (walkKernel G hloc a) hP p hp k s hs.le D x

end DeformationDifferentiation
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
section AveragedDerivative
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]



theorem hasDerivAt_averagedDeformedSusceptibility (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight)
      (-(∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p)) t := by
  have he : -(∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p) =
      ∑ i, weight i * (-(∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p)) := by
    simp only [mul_neg,Finset.sum_neg_distrib]
  rw [he]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_deformedSusceptibility G hloc hqt d hd a hP p hp0 hp k t ht Set.univ (root i)).const_mul (weight i))

end AveragedDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PathAverage
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem rawPathAverage_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (f g : RawCorridor G k → ℝ) (hfg : ∀ w, f w ≤ g w) :
    rawPathAverage G P k root weight f ≤ rawPathAverage G P k root weight g := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  unfold rawPathAverage
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) k (root i))
  simp only [tsum_fintype]
  exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hfg _) (w.2.mass_nonneg P hP))

theorem rawPathAverage_const_mul (G : BondGraph V E) (P : V → V → ℝ) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (c : ℝ) (f : RawCorridor G k → ℝ) :
    rawPathAverage G P k root weight (fun w => c*f w) = c*rawPathAverage G P k root weight f := by
  unfold rawPathAverage
  simp only [←mul_left_comm c,tsum_mul_left,Finset.mul_sum]

end PathAverage
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

end FiniteRootedLabels
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

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem coe_neighborhood (hloc : LocallyFinite G) (w : RawCorridor G k) :
    (w.neighborhood hloc : Set V) = closedBondNeighborhood G (w.interior : Set V) :=
  (closedBondNeighborhood_finset G hloc w.interior).symm


end RawCorridor



end EscapeGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_FiniteScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deformed susceptibility, finite-scale estimates and the Riccati contradiction. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section EscapeSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

omit [Countable V] [Countable E] [Nonempty V] in
 

theorem deformed_move_of_walk (G : BondGraph V E) (hloc : LocallyFinite G)
    (a C : ℝ) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmove : ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b)
    (D : Set V) (b z : V) (q : (openSimpleGraph G Set.univ).Walk b z)
    (j : ℕ) (hj : q.length ≤ j) (hD : ∀ x ∈ q.support, x ∈ D) :
    Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^j *
      deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t D b := by
  obtain ⟨l,hl,he,_⟩ := walk_lift_bonds G Set.univ q
  have hlen : l.length = q.length := by
    have hh := congrArg List.length he
    simpa only [List.length_map,SimpleGraph.Walk.length_edges] using hh
  have hle : l.length ≤ j := hlen.trans_le hj
  have hcomp := hmove D b z l (hD b q.start_mem_support) hl (by
    intro e hel x hxe
    exact hD x (SimpleGraph.Walk.mem_support_of_mem_edges
      (he ▸ List.mem_map_of_mem hel) hxe))
  have he' : Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ)))) ≤
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (Real.exp_pos _).le) (neg_nonpos.mpr ht)
  have hpw : (p:ℝ)^j ≤ (p:ℝ)^l.length := pow_le_pow_of_le_one p.2.1 p.2.2 hle
  exact (mul_le_mul_of_nonneg_right (mul_le_mul he' hpw (pow_nonneg p.2.1 _) (Real.exp_pos _).le)
    (deformedSusceptibility_nonneg G _ p k t D z)).trans hcomp

 
theorem deformedSusceptibility_delete_interior (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (w : RawCorridor G k) (x : V) :
    deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x -
      maxSusceptibility G p * (∑ z ∈ w.neighborhood hloc, twoPoint G p x z) ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ x := by
  have hh := deformedSusceptibility_deletion G hloc hqt _ hP p hp k t ht Set.univ (w.interior : Set V) x
  rw [←w.coe_neighborhood hloc,Finset.tsum_subtype'] at hh
  have he : Set.univ \ (w.interior : Set V) = (w.interior : Set V)ᶜ := by ext z; simp
  rw [he] at hh
  exact hh

 

theorem selected_retained_product_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (j : ℕ) (s C cf χ : ℝ) (hcf : 0 ≤ cf) (hχ : 0 ≤ χ)
    (hrow : ∀ x, cf*χ ≤ deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x)
    (hcost : maxSusceptibility G p*s ≤ (cf/2)*χ)
    (hmove : ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b)
    (w : RawCorridor G k) (hw : w.Selected hloc p j s) :
    Real.exp (-2*t*(j:ℝ)*Real.exp (C*(k:ℝ))) * (p:ℝ)^(2*j) * ((cf/2)*χ)^2 ≤
      retainedSusceptibilityProduct G (walkKernel G hloc a) p t w := by
  have hx (x : V) (he : w.HasEscape hloc p j s x) :
      Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ))))*(p:ℝ)^j*((cf/2)*χ) ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ x := by
    obtain ⟨z,q,_hq,hj,havoid,hs⟩ := he
    have hd := deformedSusceptibility_delete_interior G hloc hqt a hP p hp k t ht w z
    have hδ : (cf/2)*χ ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ z := by
      have hb := mul_le_mul_of_nonneg_left hs (zero_le_one.trans (maxSusceptibility_one_le G hloc hqt p hp))
      have hr := hrow z
      linarith
    exact (mul_le_mul_of_nonneg_left hδ
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg p.2.1 _))).trans
        (deformed_move_of_walk G hloc a C p k t ht hmove (w.interior : Set V)ᶜ x z q j hj havoid)
  have h₁ := hx w.base hw.2.1
  have h₂ := hx w.endpoint hw.2.2
  have hfactor : 0 ≤ Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ))))*(p:ℝ)^j*((cf/2)*χ) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg p.2.1 _))
      (mul_nonneg (div_nonneg hcf (by norm_num)) hχ)
  have hh := mul_le_mul h₁ h₂ hfactor
    (deformedSusceptibility_nonneg G _ p k t (w.interior : Set V)ᶜ w.base)
  rw [retainedSusceptibilityProduct,ite_eq_left hw.1]
  apply le_trans (le_of_eq ?_) hh
  have he : -2*t*(j:ℝ)*Real.exp (C*(k:ℝ)) =
      -t*((j:ℝ)*Real.exp (C*(k:ℝ))) + -t*((j:ℝ)*Real.exp (C*(k:ℝ))) := by ring
  rw [he,Real.exp_add,show 2*j=j+j by omega,pow_add]
  ring

end EscapeSusceptibility
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedRetention
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

omit [Countable V] [Countable E] [Nonempty V] in
theorem averagedDeformedSusceptibility_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (t : ℝ) :
    0 ≤ averagedDeformedSusceptibility G P p k root weight t :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (deformedSusceptibility_nonneg G P p k t Set.univ (root i)))

end AveragedRetention
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AveragePositiveTerm
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

omit [Countable V] [Countable E] [Nonempty V] in
 
theorem selected_average_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (j : ℕ) (s b F : ℝ) (hF : 0 ≤ F)
    (hm : b ≤ rawPathAverage G P k root weight
      (fun w => if w.Selected hloc p j s then 1 else 0))
    (hgood : ∀ w : RawCorridor G k, w.Selected hloc p j s →
      F ≤ retainedSusceptibilityProduct G P p t w) :
    F*b ≤ rawPathAverage G P k root weight (retainedSusceptibilityProduct G P p t) := by
  have hh := rawPathAverage_mono G hloc P hP k root weight hw
    (fun w => F*(if w.Selected hloc p j s then 1 else 0))
    (retainedSusceptibilityProduct G P p t) (by
      intro w
      by_cases hs : w.Selected hloc p j s
      · simpa only [hs,ite_true,mul_one] using hgood w hs
      · simp only [hs,ite_false,mul_zero,retainedSusceptibilityProduct]
        split_ifs
        · exact mul_nonneg (deformedSusceptibility_nonneg G P p k t _ w.base)
            (deformedSusceptibility_nonneg G P p k t _ w.endpoint)
        · exact le_rfl)
  rw [rawPathAverage_const_mul] at hh
  exact (mul_le_mul_of_nonneg_left hm hF).trans hh
end AveragePositiveTerm

section RiccatiContradiction
 

theorem riccati_retention_bound (χ D : ℝ → ℝ) (T m c h : ℝ)
    (hT : 0 < T) (hm : 0 < m) (hc : 0 < c) (_hh : 0 ≤ h)
    (hret : ∀ t ∈ Set.Icc (T/2) T, m/(2*c) ≤ χ t)
    (hder : ∀ t ∈ Set.Icc (T/2) T, HasDerivAt χ (-D t) t)
    (hdec : ∀ t ∈ Set.Icc (T/2) T, h*(χ t)^2 ≤ D t) :
    h*T*m ≤ 4*c := by
  have hpos (t) (ht : t ∈ Set.Icc (T/2) T) : 0 < χ t :=
    (div_pos hm (by positivity)).trans_le (hret t ht)
  have hd (t) (ht : t ∈ Set.Icc (T/2) T) :
      HasDerivAt (fun s => (χ s)⁻¹) (D t/(χ t)^2) t := by
    convert! (hder t ht).inv (hpos t ht).ne' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [neg_neg]
  have hcχ : ContinuousOn (fun s => (χ s)⁻¹) (Set.Icc (T/2) T) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => (χ s)⁻¹) (interior (Set.Icc (T/2) T)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hdl (t) (ht : t ∈ interior (Set.Icc (T/2) T)) :
      h ≤ deriv (fun s => (χ s)⁻¹) t := by
    rw [(hd t (interior_subset ht)).deriv]
    exact (le_div_iff₀ (sq_pos_of_pos (hpos t (interior_subset ht)))).mpr (hdec t (interior_subset ht))
  have hs := (convex_Icc (T/2) T).mul_sub_le_image_sub_of_le_deriv hcχ hdiff hdl
    (T/2) ⟨le_rfl,by linarith⟩ T ⟨by linarith,le_rfl⟩ (by linarith)
  have hstart : 0 ≤ (χ (T/2))⁻¹ := (inv_pos.mpr (hpos _ ⟨le_rfl,by linarith⟩)).le
  have hend : (χ T)⁻¹ ≤ 2*c/m := by
    have hb := one_div_le_one_div_of_le (div_pos hm (by positivity)) (hret T ⟨by linarith,le_rfl⟩)
    simpa only [one_div,inv_div] using hb
  have hs' : h*(T/2) ≤ 2*c/m := by linarith
  have hs'' := (le_div_iff₀ hm).mp hs'
  nlinarith
end RiccatiContradiction
end Percolation

 

 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteScale
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Infinite V]
variable {ι : Type*} [Fintype ι]

 

theorem exists_finite_scale_obstruction_oai
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, 0 < J ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (A : Hilbert V →L[ℂ] Hilbert V), HasKernel G p A →
      ∀ k : ℕ, k₀ ≤ k → ∀ B : ℝ, 0 < B →
      let R := maxSusceptibility G p/‖A‖
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊
      B*‖P‖^k ≤ 1/4 →
      B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ ‖A‖ →
      R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k ≤ ε*((pc G:ℝ)/2)^(2*j) →
      M < B*((pc G:ℝ)/2)^(2*j) → False := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hw₀ (i) := (hw i).le
  obtain ⟨Cr,cf,hCr,hcf,hrow⟩ := exists_uniform_deformed_row_comparison G hconn hloc hqt
    root weight hw₀ hw1 (fun x => by
      obtain ⟨i,g,⟨e,he⟩,hx⟩ := hcov x
      exact ⟨i,g,e,he,hx⟩) d hd a hK hpcrit hpcrit₁
  obtain ⟨Cm,hCm,hmove⟩ := exists_uniform_deformed_endpoint_comparison G hloc hqt d hd a hK hpcrit hpcrit₁
  obtain ⟨Cd,hCd,hdecrease⟩ := exists_uniform_averaged_decrease G hG hloc hqt
    root weight hw₀ (vertexAut G) (Set.Subset.refl _) htr d hd a hK hpcrit hpcrit₁ P hpos hP hsym
  let τ := cf/(8*c)
  have hτ : 0 < τ := div_pos hcf (by positivity)
  obtain ⟨J,C₁,k₀,b,hJ,hC₁,hk₀,hb,hselected⟩ := exists_selected_path_mass G hconn hloc hqt
    a ha root weight htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag hρ d hd τ hτ
  let C := Cr+Cm+Cd
  let q := b*Real.exp (-2)*(cf/2)^2
  let H := (1+2*(d:ℝ)/(pc G:ℝ))*(2*c)^2
  let ε := q/(2*H)
  let h₀ := Real.exp (-1)*q/2
  let M := 4*c/h₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hε : 0 < ε := div_pos hq (by positivity)
  have hh₀ : 0 < h₀ := by dsimp [h₀]; positivity
  have hM : 0 < M := div_pos (by positivity) hh₀
  refine ⟨C,by dsimp [C]; positivity,J,hJ,C₁,hC₁,k₀,hk₀,ε,M,hε,hM,?_⟩
  intro p hpnear hp A hA k hk B hB
  dsimp only
  let m := ‖A‖
  let R := maxSusceptibility G p/m
  let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊
  let β := ((pc G:ℝ)/2)^(2*j)
  let T := B/m
  let χ := averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight
  let D := fun t => ∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p
  change B*‖P‖^k ≤ 1/4 → B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m →
    R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k ≤ ε*β → M < B*β → False
  intro hsmall htime herrscale hlarge
  have hm : 0 < m := zero_lt_one.trans_le (hA.norm_one_le G p A)
  have hR : 1 ≤ R := (one_le_div hm).mpr (hA.norm_le_maxSusceptibility G hloc hqt p hp A)
  have hβ : 0 < β := pow_pos (half_pos hpcrit) _
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjr : (1:ℝ) ≤ (j:ℝ) := Nat.one_le_cast.mpr hj
  have hk3 : 3 ≤ k := hk₀.trans hk
  have hpzero : 0 < (p:ℝ) := (half_pos hpcrit).trans_le hpnear
  have hT : 0 < T := div_pos hB hm
  have hTb (t : ℝ) (ht : t ≤ T) : t*m ≤ B := (le_div_iff₀ hm).mp ht
  have htim (t : ℝ) (ht : t ≤ T) : t*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ 1 := by
    have hm' := mul_le_mul_of_nonneg_right (hTb t ht)
      (mul_nonneg (Nat.cast_nonneg j) (Real.exp_pos (C*(k:ℝ))).le)
    nlinarith only [hm',htime,hm]
  have hCbound (C' : ℝ) (hC' : C' ≤ C) : Real.exp (C'*(k:ℝ)) ≤ Real.exp (C*(k:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC' (Nat.cast_nonneg k))
  have htim' (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (C' : ℝ) (hC' : C' ≤ C) :
      t*Real.exp (C'*(k:ℝ)) ≤ 1 := by
    have he := mul_le_mul_of_nonneg_left (hCbound C' hC') ht
    have hj' := mul_le_mul_of_nonneg_left hjr (mul_nonneg ht (Real.exp_pos (C*(k:ℝ))).le)
    nlinarith only [he,hj',htim t htT]
  have hret (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) : m/(2*c) ≤ χ t :=
    deformed_root_sum_retained G hG hloc hqt a p hpzero hp root weight hw₀ hcov c hc hmin
      P A hpos hsym hP hA k t B ht (hTb t htT) hsmall
  have hdec (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) : (h₀*β)*(χ t)^2 ≤ D t := by
    have hχ : 0 ≤ χ t := averagedDeformedSusceptibility_nonneg G _ p k root weight hw₀ t
    have hret' := (div_le_iff₀ (by positivity : 0 < 2*c)).mp (hret t ht htT)
    have hrow' := hrow p hpnear hp k hk3 t ht (htim' t ht htT Cr (by dsimp [C]; linarith only [hCr,hCm,hCd]))
    have hcost : maxSusceptibility G p*(τ/R) ≤ (cf/2)*χ t := by
      have hmax : maxSusceptibility G p ≠ 0 :=
        (zero_lt_one.trans_le (maxSusceptibility_one_le G hloc hqt p hp)).ne'
      have he : maxSusceptibility G p*(τ/R) = τ*m := by dsimp [R]; field_simp [hmax]
      rw [he]
      have hh := mul_le_mul_of_nonneg_left hret' hτ.le
      have hτcf : τ*(2*c) = cf/4 := by dsimp [τ]; field_simp; ring
      rw [mul_left_comm τ (χ t) (2*c),hτcf,mul_comm (χ t)] at hh
      nlinarith only [hh,hcf,hχ]
    have hprod (w : RawCorridor G k) (hwsel : w.Selected hloc p j (τ/R)) :
        Real.exp (-2)*β*((cf/2)*χ t)^2 ≤ retainedSusceptibilityProduct G (walkKernel G hloc a) p t w := by
      have hbnd := selected_retained_product_lower G hloc hqt a hK p hp k t ht j (τ/R) Cm cf (χ t)
        hcf.le hχ hrow' hcost (hmove p hpnear hp k hk3 t ht) w hwsel
      have he : Real.exp (-2) ≤ Real.exp (-2*t*(j:ℝ)*Real.exp (Cm*(k:ℝ))) := by
        apply Real.exp_le_exp.mpr
        have he' := mul_le_mul_of_nonneg_left (hCbound Cm (by dsimp [C]; linarith only [hCr,hCm,hCd]))
          (mul_nonneg ht (Nat.cast_nonneg j))
        linarith only [he',htim t htT]
      have hpw : β ≤ (p:ℝ)^(2*j) := pow_le_pow_left₀ (half_pos hpcrit).le hpnear _
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul he hpw hβ.le (Real.exp_pos _).le) (sq_nonneg _)).trans hbnd
    have hsel := hselected p hpnear hp k hk R hR
    have hpositive := selected_average_lower G hloc _ hK p k t root weight hw₀ j (τ/R) b
      (Real.exp (-2)*β*((cf/2)*χ t)^2) (by positivity) hsel hprod
    have hpositive' : q*β*(χ t)^2 ≤ rawPathAverage G (walkKernel G hloc a) k root weight
        (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) := by
      convert hpositive using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [q]
      ring
    have ha₃ : 0 ≤ rootTriangle G root weight (p:ℝ) :=
      zero_le_one.trans (rootTriangle_one_le G hloc hqt root weight hw₀ hw1 p hp)
    have herror : (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
        (‖P‖^k*(rootTrace root weight (A^3)).re) ≤ (q/2)*β*(χ t)^2 := by
      rw [←rootTriangle_eq_trace G p root weight A hA]
      have hx : maxSusceptibility G p = R*m := by dsimp [R]; field_simp
      rw [hx]
      have hcoeff : 0 ≤ (1+2*(d:ℝ)/(pc G:ℝ)) := by positivity
      have hm2 : m^2 ≤ (2*c)^2*(χ t)^2 := by
        calc
          m^2 ≤ (χ t*(2*c))^2 := pow_le_pow_left₀ hm.le hret' 2
          _ = _ := by ring
      have h₁ := mul_le_mul_of_nonneg_left hm2
        (mul_nonneg (mul_nonneg hcoeff (sq_nonneg R)) (mul_nonneg ha₃ (pow_nonneg (norm_nonneg P) k)))
      have h₂ := mul_le_mul_of_nonneg_left herrscale (mul_nonneg hH.le (sq_nonneg (χ t)))
      have he : H*ε = q/2 := by dsimp [ε]; field_simp
      calc
        _ ≤ H*(R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k)*(χ t)^2 := by dsimp [H]; nlinarith only [h₁]
        _ ≤ H*(ε*β)*(χ t)^2 := by nlinarith only [h₂]
        _ = _ := by rw [←mul_assoc H ε β,he]
    have hdiff : (q/2)*β*(χ t)^2 ≤
        rawPathAverage G (walkKernel G hloc a) k root weight
          (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) -
        (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
          (‖P‖^k*(rootTrace root weight (A^3)).re) := by linarith only [hpositive',herror]
    have hexp : Real.exp (-1) ≤ Real.exp (-t*Real.exp (Cd*(k:ℝ))) :=
      Real.exp_le_exp.mpr (by linarith only [htim' t ht htT Cd (by dsimp [C]; linarith only [hCr,hCm]) ])
    have hh := mul_le_mul hexp hdiff (by positivity) (Real.exp_pos _).le
    have hdecr := hdecrease p hpnear hp A hA k hk3 t ht
    apply le_trans _ hdecr
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [h₀]
    ring
  have hb := riccati_retention_bound χ D T m c (h₀*β) hT hm hc (mul_pos hh₀ hβ).le
    (fun t ht => hret t (by linarith only [ht.1,hT]) ht.2)
    (fun t ht => hasDerivAt_averagedDeformedSusceptibility G hloc hqt root weight d hd a hK p hpzero hp k t
      (by linarith only [ht.1,hT]))
    (fun t ht => hdec t (by linarith only [ht.1,hT]) ht.2)
  have he : h₀*β*T*m = h₀*(B*β) := by dsimp [T]; field_simp
  rw [he] at hb
  have hg := (div_lt_iff₀ hh₀).mp hlarge
  nlinarith only [hg,hb]

end FiniteScale
end Percolation

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.exists_finite_scale_obstruction_oai.{u, v, u_1} := @OAI.Percolation.exists_finite_scale_obstruction_oai.{u, v, u_1}
