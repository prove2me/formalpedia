-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.critical_fullspace_threeQuarter_profiles_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:19:14.62521+00:00
-- url     : https://prove2.me/submissions/d18e2c57-5b06-4d1a-8d4c-156dfaf63b04

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_endpoint_fractional_profiles_bs
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_finite_general_bs
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_halfspace_fractional_profiles_bs

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

section CouplingLimits
open Filter Topology

theorem conn_iUnion_iff (G : BondGraph V E) (ω : ℕ → Set E) (hω : Monotone ω)
    (x y : V) : Conn G (⋃ n, ω n) x y ↔ ∃ n, Conn G (ω n) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, conn_refl G _ _⟩
    | @tail y z _ hyz ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨e, he, heq⟩ := hyz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
      exact ⟨max m n, (conn_mono G (hω (le_max_left _ _)) hm).tail
        ⟨e, hω (le_max_right _ _) hn, heq⟩⟩
  · rintro ⟨n, hn⟩
    exact conn_mono G (Set.subset_iUnion ω n) hn


end CouplingLimits

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FirstHeightPeakWalk
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V : Type*} {H : SimpleGraph V}

lemma first_height_peak_walk (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ {u v}, H.Adj u v → |f v-f u| ≤ R)
    {x y : V} (p : H.Walk x y) (a b : ℝ)
    (ha : a ≤ f x) (hb : f x ≤ b) (hend : b ≤ f y)
    (hlow : ∀ z ∈ p.support, a ≤ f z) :
    ∃ z, ∃ q : H.Walk x z, q.length ≤ p.length ∧
      b ≤ f z ∧ f z ≤ b+R ∧ ∀ v ∈ q.support, a ≤ f v ∧ f v ≤ f z := by
  induction p with
  | @nil u =>
    refine ⟨u,.nil,le_rfl,hend,by linarith,?_⟩
    intro v hv
    have hv' : v=u := List.mem_singleton.mp hv
    subst v
    exact ⟨ha,le_rfl⟩
  | @cons x v y huv p ih =>
    by_cases hx : b ≤ f x
    · refine ⟨x,.nil,Nat.zero_le _,hx,by linarith,?_⟩
      intro z hz
      have hz' : z=x := List.mem_singleton.mp hz
      subst z
      exact ⟨ha,le_rfl⟩
    have hav : a ≤ f v := hlow v (by simp)
    by_cases hv : b ≤ f v
    · have hvu := (abs_le.mp (hjump huv)).2
      refine ⟨v,.cons huv .nil,by simp,hv,by linarith,?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
        List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨ha,by linarith⟩
      · exact ⟨hav,le_rfl⟩
    · obtain ⟨z,q,hq,hz,hzR,hbound⟩ := ih hav (le_of_not_ge hv) hend
        (fun z hz => hlow z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz))
      refine ⟨z,.cons huv q,Nat.succ_le_succ hq,hz,hzR,?_⟩
      intro w hw
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨ha,by linarith⟩
      · exact hbound w hw

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_bounded_ascent_to_level
    [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ c : ℝ, 0 ≤ c → ∀ x,
      ∃ y, ∃ w : G.fullGraph.Walk x y, (w.length : ℝ) ≤ A*c+B ∧
        c ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ c+R ∧
        ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤
            G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_ascent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  refine ⟨(L : ℝ)/ε+1,L,by positivity,Nat.cast_nonneg _,fun c hc0 x => ?_⟩
  let n := ⌈c/ε⌉₊
  have hn : c ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil (c/ε))
  have hn' : (n : ℝ) ≤ c/ε+1 := (Nat.ceil_lt_add_one (div_nonneg hc0 hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_ascent_iterate hc hl a ε hε.le L hstep n x
  have hj : ∀ {u v}, G.fullGraph.Adj u v →
      |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
    intro u v huv
    have huv' : (Percolation.openSimpleGraph G.ends Set.univ).Adj u v := by
      rw [←criticalModel_openGraph G.ends Set.univ]
      exact huv
    obtain ⟨e,_he,he⟩ := huv'.2
    have hv := hjump e u v (by rw [he]; simp) (by rw [he]; simp)
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
    simpa only [add_sub_cancel_left] using hv
  obtain ⟨z,q,hq,hz,hzR,hbound⟩ := first_height_peak_walk
    (G.orbitAdjustedHeight a x) R hR hj w 0 c (by simp) (by simpa using hc0) (hn.trans hwy) hw
  refine ⟨z,q,?_,hz,hzR,hbound⟩
  have hqn : q.length ≤ n*L := hq.trans hwlen
  have hqn' : (q.length : ℝ) ≤ (n : ℝ)*L := by exact_mod_cast hqn
  have hm := mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  calc
    _ ≤ (n : ℝ)*L := hqn'
    _ ≤ (c/ε+1)*L := hm
    _ = ((L : ℝ)/ε+1)*c+L-c := by ring
    _ ≤ ((L : ℝ)/ε+1)*c+L := by linarith

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

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerMomentDecomposition
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_lintegral_rpow_le_rpow_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    (∫⁻ ω, f ω ^ b ∂μ) ≤ (∫⁻ ω, f ω ∂μ)^b := by
  by_cases he : b = 1
  · simp only [he,ENNReal.rpow_one,le_refl]
  have hblt : b < 1 := lt_of_le_of_ne hb1 he
  have hc := Real.holderConjugate_one_div hb (sub_pos.mpr hblt) (by ring : b+(1-b)=1)
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
    ((hf.pow_const b).aemeasurable) (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) μ)
  have hcancel : b*(1/b)=1 := by field_simp
  have hinv : 1/(1/b)=b := by field_simp
  simpa only [Pi.mul_apply,mul_one,ENNReal.one_rpow,←ENNReal.rpow_mul,hcancel,ENNReal.rpow_one,
    lintegral_const,measure_univ,one_mul,hinv] using hh

lemma ennreal_fractional_finset_sum {ι : Type*} (F : Finset ι) (f : ι → ℝ≥0∞)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑ z ∈ F, f z)^a ≤ ∑ z ∈ F, f z^a := by
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,ENNReal.zero_rpow_of_pos ha,le_refl]
  | @insert z F hz ih =>
    simp only [Finset.sum_insert hz]
    exact (ENNReal.rpow_add_le_add_rpow _ _ ha.le ha1).trans (add_le_add le_rfl ih)

theorem fractional_frontier_continuations
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Finset ι) (f : ι → Ω → ℝ≥0∞) (hf : ∀ z ∈ F, Measurable (f z))
    (g : Ω → ℝ≥0∞) (hcover : ∀ ω, g ω ≤ ∑ z ∈ F, f z ω)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (L : ℝ≥0∞) (hL : ∀ z ∈ F, (∫⁻ ω, f z ω^a ∂μ) ≤ L) :
    (∫⁻ ω, g ω^(a*b) ∂μ) ≤ (F.card : ℝ≥0∞)^b*L^b := by
  have hm : Measurable (fun ω => ∑ z ∈ F, f z ω^a) :=
    Finset.measurable_sum F (fun z hz => (hf z hz).pow_const a)
  calc
    _ ≤ ∫⁻ ω, (∑ z ∈ F, f z ω^a)^b ∂μ := by
      apply lintegral_mono
      intro ω
      change g ω^(a*b) ≤ (∑ z ∈ F, f z ω^a)^b
      rw [ENNReal.rpow_mul]
      exact ENNReal.rpow_le_rpow
        ((ENNReal.rpow_le_rpow (hcover ω) ha.le).trans
          (ennreal_fractional_finset_sum F (fun z => f z ω) ha ha1)) hb.le
    _ ≤ (∫⁻ ω, ∑ z ∈ F, f z ω^a ∂μ)^b :=
      ennreal_lintegral_rpow_le_rpow_lintegral μ _ hm hb hb1
    _ = (∑ z ∈ F, ∫⁻ ω, f z ω^a ∂μ)^b := by
      rw [lintegral_finsetSum F (fun z hz => (hf z hz).pow_const a)]
    _ ≤ ((F.card : ℝ≥0∞)*L)^b := by
      apply ENNReal.rpow_le_rpow _ hb.le
      calc
        _ ≤ ∑ _z ∈ F, L := Finset.sum_le_sum hL
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hb.le

theorem exposed_frontier_fractional_bound {E ι : Type*}
    (q : E → unitInterval) (Q : Set E) (A : Set (Set E))
    (hA : MeasurableSet A) (hAdep : DependsOn (fun ω => ω ∈ A) Q)
    (F : Finset ι) (f : ι → Set E → ℝ≥0∞) (hf : ∀ z ∈ F, Measurable (f z))
    (g : Set E → ℝ≥0∞) (hg : Measurable g) (hgdep : DependsOn g Qᶜ)
    (hcover : ∀ ω, g ω ≤ ∑ z ∈ F, f z ω)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (L : ℝ≥0∞) (hL : ∀ z ∈ F,
      (∫⁻ ω, f z ω^a ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, A.indicator (fun ω => g ω^(a*b)) ω ∂CriticalPercolation.BernoulliProduct.law q) ≤
      CriticalPercolation.BernoulliProduct.law q A * (F.card : ℝ≥0∞)^b*L^b := by
  rw [CriticalPercolation.BernoulliProduct.lintegral_indicator_fresh q Q A hA hAdep _
    (hg.pow_const (a*b)) (fun ω η h => congrArg (fun x : ℝ≥0∞ => x^(a*b)) (hgdep h))]
  exact (mul_le_mul' le_rfl (fractional_frontier_continuations
    (CriticalPercolation.BernoulliProduct.law q) F f hf g hcover ha ha1 hb hb1 L hL)).trans_eq
      (mul_assoc _ _ _).symm

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

lemma openFrontier_dependsOn (S : Set V) :
    DependsOn (fun ω => openFrontier G ω S) (ballIncidentEdges G S) := by
  intro ω η hωη
  ext z
  constructor
  · rintro ⟨hz,u,hu,e,he,heq⟩
    exact ⟨hz,u,hu,e,(Iff.of_eq (hωη e ⟨u,hu,by rw [heq]; simp⟩)).mp he,heq⟩
  · rintro ⟨hz,u,hu,e,he,heq⟩
    exact ⟨hz,u,hu,e,(Iff.of_eq (hωη e ⟨u,hu,by rw [heq]; simp⟩)).mpr he,heq⟩

lemma openFrontier_finite (hloc : LocallyFinite G) (ω : Set E)
    {S : Set V} (hS : S.Finite) : (openFrontier G ω S).Finite := by
  apply (hS.biUnion (fun u _ => finite_neighbors hloc u)).subset
  rintro z ⟨_,u,hu,e,_,heq⟩
  exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,e,heq⟩⟩

lemma measurable_mem_openFrontier [Countable V] [Countable E] (S : Set V) (z : V) :
    Measurable (fun ω => z ∈ openFrontier G ω S) := by
  exact measurable_const.and (Measurable.exists fun u => measurable_const.and
    (Measurable.exists fun e => (measurable_set_mem e).and measurable_const))

lemma measurableSet_openFrontier_eq [Countable V] [Countable E] (S F : Set V) :
    MeasurableSet {ω | openFrontier G ω S = F} := by
  have he : {ω | openFrontier G ω S = F} =
      ⋂ z : V, {ω | (z ∈ openFrontier G ω S) ↔ z ∈ F} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact Set.ext_iff
  rw [he]
  exact MeasurableSet.iInter fun z =>
    ((measurable_mem_openFrontier G S z).iff measurable_const).setOf

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

lemma lowerFrontierCell_dependsOn (I J : Set E) (x : V) (S F : Set V) :
    DependsOn (fun ω => ω ∈ lowerFrontierCell G I J x S F) (ballIncidentEdges G S) := by
  intro ω η hωη
  have hc := restricted_exactCluster_dependsOn G I x S hωη
  change (cluster G (Set.inter ω I) x = S) =
    (cluster G (Set.inter η I) x = S) at hc
  have ha : ∀ e ∈ ballIncidentEdges G S,
      (e ∈ Set.inter ω J) = (e ∈ Set.inter η J) := by
    intro e he
    exact congrArg (fun p : Prop => p ∧ e ∈ J) (hωη e he)
  have hf := openFrontier_dependsOn G S ha
  change openFrontier G (Set.inter ω J) S = openFrontier G (Set.inter η J) S at hf
  change (cluster G (Set.inter ω I) x = S ∧ openFrontier G (Set.inter ω J) S = F) =
    (cluster G (Set.inter η I) x = S ∧ openFrontier G (Set.inter η J) S = F)
  rw [hc,hf]

lemma measurableSet_lowerFrontierCell [Countable V] [Countable E]
    (I J : Set E) (x : V) (S F : Set V) :
    MeasurableSet (lowerFrontierCell G I J x S F) := by
  have hm : Measurable (fun ω : Set E => ω ∩ J) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (measurableSet_restricted_exactCluster G I x S).inter
    ((measurableSet_openFrontier_eq G S F).preimage hm)

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

lemma openFrontier_lowerCluster_outside (ω : Set E) (D : Set V) (x : V)
    (hx : x ∈ D) {z : V}
    (hz : z ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G D) x)) : z ∉ D := by
  rintro hzD
  obtain ⟨hz,u,hu,e,he,heq⟩ := hz
  have huD := conn_internalEdges_end_mem G ω D hx hu
  apply hz
  exact hu.tail ⟨e,⟨he,(mem_internalEdges_of_ends G D e u z heq).mpr ⟨huD,hzD⟩⟩,heq⟩

lemma measurable_restrictedLayerCount [Countable V] [Countable E]
    (I : Set E) (A : Set V) (x : V) : Measurable (fun ω => restrictedLayerCount G I A ω x) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.tsum fun y => Measurable.ite
    (measurable_const.and ((measurableSet_conn G x y).mem.comp hm)).setOf
    measurable_const measurable_const

lemma restrictedLayerCount_dependsOn (I : Set E) (A : Set V) (x : V) :
    DependsOn (fun ω => restrictedLayerCount G I A ω x) I := by
  intro ω η hωη
  have he : Set.inter ω I = Set.inter η I := by
    ext e
    change (ω e ∧ e ∈ I) ↔ (η e ∧ e ∈ I)
    by_cases hi : e ∈ I
    · simp only [hi,and_true]
      exact Iff.of_eq (hωη e hi)
    · simp only [hi,and_false]
  change (∑' y, if y ∈ A ∧ Conn G (Set.inter ω I) x y then (1 : ℝ≥0∞) else 0) =
    (∑' y, if y ∈ A ∧ Conn G (Set.inter η I) x y then (1 : ℝ≥0∞) else 0)
  rw [he]

lemma restrictedLayerCount_mono_edges {I J : Set E} (hIJ : I ⊆ J)
    (A : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G I A ω x ≤ restrictedLayerCount G J A ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ A ∧ Conn G (ω ∩ I) x y
  · rw [ite_eq_left hy,ite_eq_left
      ⟨hy.1,conn_mono G (Set.inter_subset_inter_right _ hIJ) hy.2⟩]
  · rw [ite_eq_right hy]
    exact bot_le

theorem layerCount_le_frontier_sum (ω : Set E) (I J : Set E)
    (x : V) (S : Set V) (F : Finset V) (A : Set V)
    (hcell : ω ∈ lowerFrontierCell G I J x S (F : Set V)) :
    restrictedLayerCount G J (A \ S) ω x ≤
      ∑ z ∈ F, restrictedLayerCount G (J \ ballIncidentEdges G S) A ω z := by
  rw [show (∑ z ∈ F, restrictedLayerCount G (J \ ballIncidentEdges G S) A ω z) =
      ∑' y, ∑ z ∈ F, if y ∈ A ∧
        Conn G (ω ∩ (J \ ballIncidentEdges G S)) z y then (1 : ℝ≥0∞) else 0 by
    exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ A \ S ∧ Conn G (ω ∩ J) x y
  · rw [ite_eq_left hy]
    obtain ⟨z,hz,hzy⟩ := conn_last_exit_frontier G (ω ∩ J) S
      (hcell.1 ▸ mem_cluster_self G (ω ∩ I) x) hy.1.2 hy.2
    have hzF : z ∈ F := by
      change z ∈ (F : Set V)
      rwa [←hcell.2]
    have he : Set.inter ω (Set.diff J (ballIncidentEdges G S)) =
        Set.diff (Set.inter ω J) (ballIncidentEdges G S) := by
      ext e
      exact and_assoc.symm
    have hzterm : (if y ∈ A ∧ Conn G (ω ∩ (J \ ballIncidentEdges G S)) z y
        then (1 : ℝ≥0∞) else 0) = 1 := by
      have hc' : Conn G (ω ∩ (J \ ballIncidentEdges G S)) z y := by
        change Conn G (Set.inter ω (Set.diff J (ballIncidentEdges G S))) z y
        rw [he]
        exact hzy
      rw [ite_eq_left ⟨hy.1.1,hc'⟩]
    exact hzterm.symm.le.trans (Finset.single_le_sum
      (f := fun z => if y ∈ A ∧ Conn G (ω ∩ (J \ ballIncidentEdges G S)) z y
        then (1 : ℝ≥0∞) else 0) (fun _ _ => bot_le) hzF)
  · rw [ite_eq_right hy]
    exact bot_le

theorem lowerFrontierCell_fractional_bound [Countable V] [Countable E]
    (q : E → unitInterval) (I J : Set E) (x : V) (S : Set V)
    (F : Finset V) (A : Set V) {a b : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (L : ℝ≥0∞) (hL : ∀ z ∈ F,
      (∫⁻ ω, restrictedLayerCount G J A ω z^a
        ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, (lowerFrontierCell G I J x S (F : Set V)).indicator
      (fun ω => restrictedLayerCount G J (A \ S) ω x^(a*b)) ω
        ∂CriticalPercolation.BernoulliProduct.law q) ≤
      CriticalPercolation.BernoulliProduct.law q
        (lowerFrontierCell G I J x S (F : Set V)) * (F.card : ℝ≥0∞)^b*L^b := by
  let Q := ballIncidentEdges G S
  let f : V → Set E → ℝ≥0∞ := fun z ω => restrictedLayerCount G (J \ Q) A ω z
  let g : Set E → ℝ≥0∞ := fun ω => ∑ z ∈ F, f z ω
  have hf (z : V) : Measurable (f z) := measurable_restrictedLayerCount G _ A z
  have hg : Measurable g := Finset.measurable_sum F (fun z _ => hf z)
  have hd : DependsOn g Qᶜ := by
    intro ω η hωη
    apply Finset.sum_congr rfl
    intro z _
    exact restrictedLayerCount_dependsOn G (J \ Q) A z (fun e he => hωη e he.2)
  have hLf (z : V) (hz : z ∈ F) :
      (∫⁻ ω, f z ω^a ∂CriticalPercolation.BernoulliProduct.law q) ≤ L := by
    exact le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (restrictedLayerCount_mono_edges G (I := J \ Q) (J := J)
        Set.sdiff_subset A ω z) ha.le) (hL z hz)
  have hbound := exposed_frontier_fractional_bound q Q
    (lowerFrontierCell G I J x S (F : Set V))
    (measurableSet_lowerFrontierCell G I J x S _) (lowerFrontierCell_dependsOn G I J x S _)
    F f (fun z _ => hf z) g hg hd (fun _ => le_rfl) ha ha1 hb hb1 L hLf
  apply le_trans (lintegral_mono ?_) hbound
  intro ω
  by_cases hω : ω ∈ lowerFrontierCell G I J x S (F : Set V)
  · simp only [Set.indicator_of_mem hω]
    exact ENNReal.rpow_le_rpow (layerCount_le_frontier_sum G ω I J x S F A hω)
      (mul_nonneg ha.le hb.le)
  · simp only [Set.indicator_of_notMem hω,le_refl]

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

end CriticalPercolation.BondGraph

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
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FiniteEnergyObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct

variable {E : Type*} [Countable E]

lemma finite_forcing_measure_bound (p : unitInterval) (F : Finset E) (σ : Set E) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) •
      (law p).map (forceOn (F : Set E) σ) ≤ law p := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.smul_apply,Measure.map_apply (measurable_forceOn _ _) hB,smul_eq_mul]
  apply finite_energy_modification_bound p F _ B hB
  intro ω hω
  refine ⟨forceOn (F : Set E) σ ω,hω,?_⟩
  intro e he
  rw [mem_forceOn]
  simp only [Finset.mem_coe,he,if_false]

lemma lintegral_finite_forcing_bound (p : unitInterval) (F : Finset E) (σ : Set E)
    (X : Set E → ℝ≥0∞) (hX : Measurable X) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*
      (∫⁻ ω, X (forceOn (F : Set E) σ ω) ∂law p) ≤ ∫⁻ ω, X ω ∂law p := by
  have hh := lintegral_mono' (finite_forcing_measure_bound p F σ) (le_refl X)
  rwa [lintegral_smul_measure,lintegral_map hX (measurable_forceOn _ _),smul_eq_mul] at hh

variable {V : Type*} [Countable V] (G : BondGraph V E)

omit [Countable E] [Countable V] in
lemma rooted_forced_layer_count_le (F : Finset E) (I J : Set E) (W Z : Set V)
    (hIJ : I ⊆ J) (hWZ : W ⊆ Z) (x y : V)
    (hpath : ∀ η : Set E, (F : Set E) ⊆ η → Conn G (η ∩ J) x y)
    (ω : Set E) :
    restrictedLayerCount G I W ω y ≤
      restrictedLayerCount G J Z (forceOn (F : Set E) Set.univ ω) x := by
  let η := forceOn (F : Set E) Set.univ ω
  have hωη : ω ⊆ η := by
    intro e he
    rw [mem_forceOn]
    by_cases heF : e ∈ (F : Set E)
    · simp only [heF,if_true,Set.mem_univ]
    · simpa only [heF,if_false] using he
  have hFη : (F : Set E) ⊆ η := by
    intro e he
    rw [mem_forceOn,ite_eq_left he]
    exact Set.mem_univ e
  have hxy := hpath η hFη
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ W ∧ Conn G (ω ∩ I) y z
  · have hconn := hxy.trans (conn_mono G (Set.inter_subset_inter hωη hIJ) hz.2)
    have ht : z ∈ Z ∧ Conn G (η ∩ J) x z := ⟨hWZ hz.1,hconn⟩
    rw [ite_eq_left hz,ite_eq_left ht]
  · rw [ite_eq_right hz]
    exact bot_le

theorem forced_path_fractional_layer_comparison
    (p : unitInterval) (F : Finset E) (I J : Set E) (W Z : Set V)
    (hIJ : I ⊆ J) (hWZ : W ⊆ Z) (x y : V)
    (hpath : ∀ η : Set E, (F : Set E) ⊆ η → Conn G (η ∩ J) x y)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*
      (∫⁻ ω, (restrictedLayerCount G I W ω y)^q ∂law p) ≤
        ∫⁻ ω, (restrictedLayerCount G J Z ω x)^q ∂law p := by
  apply (mul_le_mul' le_rfl (lintegral_mono (fun ω =>
    ENNReal.rpow_le_rpow (rooted_forced_layer_count_le G F I J W Z hIJ hWZ x y hpath ω) hq))).trans
  exact lintegral_finite_forcing_bound p F Set.univ _
    ((measurable_restrictedLayerCount G J Z x).pow_const q)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabFractionalProfileShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma finite_energy_cancel_length (X Y : ℝ≥0∞) (δ A B c : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlen : (N : ℝ) ≤ A*c+B)
    (hXY : ENNReal.ofReal (δ^N)*X ≤ Y) :
    X ≤ ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)))*Y := by
  have he : Real.exp (-Real.log δ*(N : ℝ))*δ^N=1 := by
    rw [←Real.exp_log hδ,←Real.exp_nat_mul,←Real.exp_add,Real.log_exp]
    rw [show -Real.log δ*(N : ℝ)+(N : ℝ)*Real.log δ=0 by ring,Real.exp_zero]
  have hc : ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*ENNReal.ofReal (δ^N)=1 := by
    rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),he,ENNReal.ofReal_one]
  have hs : 0 ≤ -Real.log δ := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  calc
    _ = ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*(ENNReal.ofReal (δ^N)*X) := by
      rw [←mul_assoc,hc,one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*Y := mul_le_mul' le_rfl hXY
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hlen hs))) le_rfl

end Percolation.BenjaminiSchramm

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

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CeilingDownCrudeProfile
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

theorem stationaryOrbitHeight_bounded_descent_to_level
    [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ k : ℝ, 0 ≤ k → ∀ x,
      ∃ y, ∃ w : G.fullGraph.Walk x y, (w.length : ℝ) ≤ A*k+B ∧
        -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ -k ∧
        ∀ v ∈ w.support, G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0 := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_descent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  refine ⟨(L : ℝ)/ε+1,L,by positivity,Nat.cast_nonneg _,fun k hk x => ?_⟩
  let n := ⌈k/ε⌉₊
  have hn : k ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil (k/ε))
  have hn' : (n : ℝ) ≤ k/ε+1 := (Nat.ceil_lt_add_one (div_nonneg hk hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_descent_iterate hc hl a ε hε.le L hstep n x
  let f := fun v => -G.orbitAdjustedHeight a x v
  have hj : ∀ {u v}, G.fullGraph.Adj u v → |f v-f u| ≤ R := by
    intro u v huv
    have huv' : (Percolation.openSimpleGraph G.ends Set.univ).Adj u v := by
      rw [←criticalModel_openGraph G.ends Set.univ]
      exact huv
    obtain ⟨e,_he,he⟩ := huv'.2
    have hv := hjump e u v (by rw [he]; simp) (by rw [he]; simp)
    have hh : |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
      rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
      simpa only [add_sub_cancel_left] using hv
    simpa only [f,neg_sub_neg,abs_sub_comm] using hh
  obtain ⟨z,q,hqlen,hz,hzR,hbound⟩ := first_height_peak_walk f R hR hj w 0 k
    (by simp [f]) (by simpa [f] using hk) (by dsimp [f]; linarith)
    (fun v hv => by dsimp [f]; exact neg_nonneg.mpr (hw v hv))
  refine ⟨z,q,?_,by dsimp [f] at hzR; linarith,by dsimp [f] at hz; linarith,?_⟩
  · have hqn : q.length ≤ n*L := hqlen.trans hwlen
    have hqn' : (q.length : ℝ) ≤ (n : ℝ)*L := by exact_mod_cast hqn
    have hm := mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    calc
      _ ≤ (n : ℝ)*L := hqn'
      _ ≤ (k/ε+1)*L := hm
      _ = ((L : ℝ)/ε+1)*k+L-k := by ring
      _ ≤ ((L : ℝ)/ε+1)*k+L := by linarith
  · intro v hv
    have hh := hbound v hv
    dsimp [f] at hh
    exact ⟨by linarith [hh.2],by linarith [hh.1]⟩

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TruncatedFractionalSummation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_exp_rpow (t a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (Real.exp t)^a=ENNReal.ofReal (Real.exp (t*a)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) ha,←Real.exp_mul]

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierExpectation
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

lemma measurable_newLayerCount (I J : Set E) (A : Set V) (x : V) :
    Measurable (fun ω => newLayerCount G I J A ω x) := by
  have hm (Q : Set E) : Measurable (fun ω : Set E => ω ∩ Q) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.tsum fun y => Measurable.ite
    (measurable_const.and (((measurableSet_conn G x y).mem.comp (hm I)).not.and
      ((measurableSet_conn G x y).mem.comp (hm J)))).setOf
    measurable_const measurable_const

lemma measurable_frontierCount (I J : Set E) (x : V) :
    Measurable (fun ω => frontierCount G I J ω x) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  have hc (y : V) : Measurable (fun ω => Conn G (ω ∩ I) x y) :=
    (measurableSet_conn G x y).mem.comp hm
  exact Measurable.tsum fun z => Measurable.ite
    ((hc z).not.and (Measurable.exists fun u => (hc u).and
      (Measurable.exists fun e => ((measurable_set_mem e).and measurable_const).and
        measurable_const))).setOf measurable_const measurable_const

omit [Countable V] [Countable E] in
lemma newLayerCount_eq_on_cell (I J : Set E) (x : V) (S F A : Set V)
    {ω : Set E} (hω : ω ∈ lowerFrontierCell G I J x S F) :
    newLayerCount G I J A ω x = restrictedLayerCount G J (A \ S) ω x := by
  apply tsum_congr
  intro y
  have he : Conn G (ω ∩ I) x y ↔ y ∈ S := by
    change y ∈ cluster G (ω ∩ I) x ↔ y ∈ S
    rw [hω.1]
  simp only [Set.mem_sdiff,he,and_assoc]

omit [Countable V] [Countable E] in
lemma frontierCount_eq_card_on_cell (I J : Set E) (x : V) (S : Set V)
    (F : Finset V) {ω : Set E}
    (hω : ω ∈ lowerFrontierCell G I J x S (F : Set V)) :
    frontierCount G I J ω x = F.card := by
  unfold frontierCount
  rw [hω.1,hω.2]
  simp only [Finset.mem_coe]
  rw [tsum_eq_sum (s := F) (fun z hz => ite_eq_right hz)]
  calc
    _ = ∑ _z ∈ F, (1 : ℝ≥0∞) := Finset.sum_congr rfl (fun _ hz => ite_eq_left hz)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]

theorem lintegral_lowerFrontier_partition
    (hloc : LocallyFinite G) (q : E → unitInterval) (I J : Set E) (x : V)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ I) x).Finite)
    (g : Set E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, g ω ∂CriticalPercolation.BernoulliProduct.law q) =
      ∑' B : Finset V × Finset V, ∫⁻ ω,
        (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator g ω
          ∂CriticalPercolation.BernoulliProduct.law q := by
  have heq : g =ᵐ[CriticalPercolation.BernoulliProduct.law q]
      (fun ω => ∑' B : Finset V × Finset V,
        (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator g ω) := by
    filter_upwards [hfin] with ω hω
    let S := hω.toFinset
    have hF := openFrontier_finite G hloc (ω ∩ J) hω
    let F := hF.toFinset
    have hS : (S : Set V) = cluster G (ω ∩ I) x := hω.coe_toFinset
    have hFF : (F : Set V) = openFrontier G (ω ∩ J) (cluster G (ω ∩ I) x) :=
      hF.coe_toFinset
    have hmem : ω ∈ lowerFrontierCell G I J x (S : Set V) (F : Set V) := by
      exact ⟨hS.symm,by rw [hS,hFF]⟩
    have huniq (B : Finset V × Finset V)
        (hB : ω ∈ lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)) : B = (S,F) := by
      have hs : B.1 = S := Finset.coe_injective (hB.1.symm.trans hS.symm)
      have hf : B.2 = F := Finset.coe_injective (by
        rw [←hB.2,←hB.1,hFF])
      exact Prod.ext hs hf
    rw [tsum_eq_single (S,F) (fun B hB => Set.indicator_of_notMem
      (fun hm => hB (huniq B hm)) g)]
    exact (Set.indicator_of_mem hmem g).symm
  rw [lintegral_congr_ae heq,lintegral_tsum]
  intro B
  exact (hg.indicator (measurableSet_lowerFrontierCell G I J x _ _)).aemeasurable

theorem newLayerCount_fractional_bound_on_frontier
    (hloc : LocallyFinite G) (q : E → unitInterval) (I J : Set E) (x : V)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ I) x).Finite)
    (A : Set V) {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (L : ℝ≥0∞)
    (Z : Set V) (hZ : ∀ ω, openFrontier G (ω ∩ J) (cluster G (ω ∩ I) x) ⊆ Z)
    (hL : ∀ z ∈ Z, (∫⁻ ω, restrictedLayerCount G J A ω z^a
      ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, newLayerCount G I J A ω x^(a*b)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (∫⁻ ω, frontierCount G I J ω x^b
        ∂CriticalPercolation.BernoulliProduct.law q)*L^b := by
  let μ := CriticalPercolation.BernoulliProduct.law q
  rw [lintegral_lowerFrontier_partition G hloc q I J x hfin _
    ((measurable_newLayerCount G I J A x).pow_const (a*b))]
  have hbound (B : Finset V × Finset V) :
      (∫⁻ ω, (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
        (fun ω => newLayerCount G I J A ω x^(a*b)) ω ∂μ) ≤
      μ (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)) *
        (B.2.card : ℝ≥0∞)^b*L^b := by
    have he : (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
        (fun ω => newLayerCount G I J A ω x^(a*b)) =
        (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
          (fun ω => restrictedLayerCount G J (A \ (B.1 : Set V)) ω x^(a*b)) := by
      apply Set.indicator_congr
      intro ω hω
      exact congrArg (fun t : ℝ≥0∞ => t^(a*b))
        (newLayerCount_eq_on_cell G I J x _ _ A hω)
    rw [he]
    by_cases hcell : (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).Nonempty
    · obtain ⟨η,hη⟩ := hcell
      exact lowerFrontierCell_fractional_bound G q I J x _ _ A ha ha1 hb hb1 L
        (fun z hz => hL z (hZ η (by
          rw [hη.1,hη.2]
          exact hz)))
    · rw [Set.not_nonempty_iff_eq_empty.mp hcell]
      simp only [Set.indicator_empty,lintegral_zero,measure_empty,zero_mul,le_refl]
  apply (ENNReal.tsum_le_tsum hbound).trans_eq
  rw [ENNReal.tsum_mul_right]
  congr 1
  rw [lintegral_lowerFrontier_partition G hloc q I J x hfin _
    ((measurable_frontierCount G I J x).pow_const b)]
  apply tsum_congr
  intro B
  have he : (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
      (fun ω => frontierCount G I J ω x^b) =
      (lowerFrontierCell G I J x (B.1 : Set V) (B.2 : Set V)).indicator
        (fun _ => (B.2.card : ℝ≥0∞)^b) := by
    apply Set.indicator_congr
    intro ω hω
    exact congrArg (fun t : ℝ≥0∞ => t^b)
      (frontierCount_eq_card_on_cell G I J x _ _ hω)
  rw [he,lintegral_indicator_const (measurableSet_lowerFrontierCell G I J x _ _),mul_comm]

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierLocalization
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

lemma restrictedLayerCount_eq_card (I : Set E) (A : Set V) (ω : Set E) (x : V)
    (F : Finset V) (hF : ∀ y, y ∈ F ↔ y ∈ A ∧ Conn G (ω ∩ I) x y) :
    restrictedLayerCount G I A ω x = F.card := by
  unfold restrictedLayerCount
  rw [tsum_eq_sum (s := F) (fun y hy => ite_eq_right (fun hh => hy ((hF y).mpr hh)))]
  calc
    _ = ∑ _y ∈ F, (1 : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun y hy => ite_eq_left ((hF y).mp hy))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]

theorem frontierCount_le_boundary_layer (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (I J : Set E) (ω : Set E) (x : V) (A : Set V)
    (hfin : (cluster G (ω ∩ I) x).Finite)
    (hA : ∀ u ∈ cluster G (ω ∩ I) x, ∀ z ∉ cluster G (ω ∩ I) x,
      ∀ e ∈ ω ∩ J, G e = s(u,z) → u ∈ A) :
    frontierCount G I J ω x ≤ (d : ℝ≥0∞)*restrictedLayerCount G I A ω x := by
  let C := cluster G (ω ∩ I) x
  have hCA : (C ∩ A).Finite := hfin.inter_of_left A
  let S := hCA.toFinset
  have hF := openFrontier_finite G hloc (ω ∩ J) hfin
  let F := hF.toFinset
  have hcover : F ⊆ S.biUnion (fun u => (finite_neighbors hloc u).toFinset) := by
    intro z hz
    obtain ⟨hz,u,hu,e,he,heq⟩ := hF.mem_toFinset.mp hz
    exact Finset.mem_biUnion.mpr ⟨u,hCA.mem_toFinset.mpr ⟨hu,hA u hu z hz e he heq⟩,
      (finite_neighbors hloc u).mem_toFinset.mpr ⟨e,heq⟩⟩
  have hcard : F.card ≤ S.card*d :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum (fun u _ => hd u)).trans_eq (by simp)))
  have hcount : restrictedLayerCount G I A ω x = S.card :=
    restrictedLayerCount_eq_card G I A ω x S (fun y => by
      rw [hCA.mem_toFinset]
      exact and_comm)
  have hfcount : frontierCount G I J ω x = F.card :=
    frontierCount_eq_card_on_cell G I J x C F
      ⟨rfl,hF.coe_toFinset.symm⟩
  rw [hfcount,hcount,mul_comm]
  exact_mod_cast hcard

theorem lower_halfspace_frontier_incident_top_band
    (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (J : Set E) (x : V) (hx : f x ≤ b)
    {u z : V} (hu : u ∈ cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x)
    (hz : z ∉ cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x)
    {e : E} (he : e ∈ ω ∩ J) (heq : G e = s(u,z)) :
    b-R ≤ f u ∧ f u ≤ b := by
  have hub := conn_internalEdges_end_mem G ω {v | f v ≤ b} hx hu
  have hzb : ¬f z ≤ b := openFrontier_lowerCluster_outside G ω
    {v | f v ≤ b} x hx ⟨hz,u,hu,e,he.1,heq⟩
  have hj := (abs_le.mp (hjump e u z (by rw [heq]; simp) (by rw [heq]; simp))).2
  exact ⟨by linarith,hub⟩

theorem lower_halfspace_frontierCount_le_top_band
    (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (J : Set E) (x : V) (hx : f x ≤ b)
    (hfin : (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x).Finite) :
    frontierCount G (internalEdges G {v | f v ≤ b}) J ω x ≤
      (d : ℝ≥0∞)*restrictedLayerCount G (internalEdges G {v | f v ≤ b})
        {u | b-R ≤ f u ∧ f u ≤ b} ω x := by
  exact frontierCount_le_boundary_layer G hloc d hd _ J ω x _ hfin
    (fun _ hu _ hz _ he heq =>
      lower_halfspace_frontier_incident_top_band G f R b hjump ω J x hx hu hz he heq)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabCountBasic
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

lemma restrictedLayerCount_zero_or_one_le (I : Set E) (W : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G I W ω x=0 ∨ 1 ≤ restrictedLayerCount G I W ω x := by
  by_cases hex : ∃ y, y ∈ W ∧ Conn G (ω ∩ I) x y
  · obtain ⟨y,hy⟩ := hex
    apply Or.inr
    unfold restrictedLayerCount
    exact ((show (1 : ℝ≥0∞)=(if y ∈ W ∧ Conn G (ω ∩ I) x y then 1 else 0) from
      (ite_eq_left hy).symm).le.trans (ENNReal.le_tsum
        (f := fun z => if z ∈ W ∧ Conn G (ω ∩ I) x z then 1 else 0) y))
  · exact Or.inl (ENNReal.tsum_eq_zero.mpr fun y => ite_eq_right (fun h => hex ⟨y,h⟩))

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GeometricIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal BigOperators
namespace Percolation.BenjaminiSchramm

lemma geometric_increment_factored (F : ℕ → ℝ≥0∞) (B K W : ℝ≥0∞) (s : ℝ)
    (h0 : F 0 ≤ B*W)
    (hstep : ∀ n, F (n+1) ≤ F n+K*W*ENNReal.ofReal (Real.exp (-s*n))) :
    ∀ n, F n ≤ (B+K*(∑' i : ℕ, ENNReal.ofReal (Real.exp (-s*i))))*W := by
  have hb : ∀ n, F n ≤ (B+K*∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (-s*i)))*W := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      calc
        _ ≤ F n+K*W*ENNReal.ofReal (Real.exp (-s*n)) := hstep n
        _ ≤ (B+K*∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (-s*i)))*W+
            K*W*ENNReal.ofReal (Real.exp (-s*n)) := add_le_add ih le_rfl
        _ = _ := by
          rw [Finset.sum_range_succ]
          simp only [mul_add,add_mul]
          ac_rfl
  intro n
  exact (hb n).trans (mul_le_mul' (add_le_add le_rfl
    (mul_le_mul' le_rfl (ENNReal.sum_le_tsum _))) le_rfl)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerMonotoneLimit
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

lemma restrictedLayerCount_mono_vertices {A B : Set V} (hAB : A ⊆ B)
    (I : Set E) (ω : Set E) (x : V) :
    restrictedLayerCount G I A ω x ≤ restrictedLayerCount G I B ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ A ∧ Conn G (ω ∩ I) x y
  · rw [ite_eq_left hy,ite_eq_left ⟨hAB hy.1,hy.2⟩]
  · rw [ite_eq_right hy]
    exact bot_le

variable [Countable V] [Countable E]

omit [Countable E] in
lemma restrictedLayerCount_iUnion (I : ℕ → Set E) (hI : Monotone I)
    (A : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G (⋃ n, I n) A ω x = ⨆ n, restrictedLayerCount G (I n) A ω x := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  let f (n : ℕ) (y : V) : ℝ≥0∞ := if y ∈ A ∧ Conn G (ω ∩ I n) x y then 1 else 0
  have hf : ∀ n, Measurable (f n) := fun _ => measurable_of_countable _
  have hmono : Monotone f := by
    intro n m hnm y
    by_cases hy : y ∈ A ∧ Conn G (ω ∩ I n) x y
    · have hym : y ∈ A ∧ Conn G (ω ∩ I m) x y :=
        ⟨hy.1,conn_mono G (inter_subset_inter_right ω (hI hnm)) hy.2⟩
      simp only [f,ite_eq_left hy,ite_eq_left hym,le_refl]
    · simp only [f,ite_eq_right hy]
      exact bot_le
  have hpoint (y : V) : (if y ∈ A ∧ Conn G (ω ∩ ⋃ n, I n) x y then (1 : ℝ≥0∞) else 0)=
      ⨆ n, f n y := by
    by_cases hy : y ∈ A ∧ Conn G (ω ∩ ⋃ n, I n) x y
    · rw [ite_eq_left hy]
      have he : ω ∩ ⋃ n, I n=⋃ n, ω ∩ I n := inter_iUnion ω I
      obtain ⟨n,hn⟩ := (conn_iUnion_iff G (fun n => ω ∩ I n)
        (fun _ _ h => inter_subset_inter_right ω (hI h)) x y).mp (he ▸ hy.2)
      apply le_antisymm
      · exact le_iSup_of_le n (by
          dsimp [f]
          rw [ite_eq_left (show y ∈ A ∧ Conn G (ω ∩ I n) x y from ⟨hy.1,hn⟩)])
      · exact iSup_le fun n => by dsimp [f]; split_ifs <;> simp
    · rw [ite_eq_right hy]
      apply le_antisymm bot_le
      apply iSup_le
      intro n
      have hn : ¬(y ∈ A ∧ Conn G (ω ∩ I n) x y) := fun hh =>
        hy ⟨hh.1,conn_mono G (inter_subset_inter_right ω (subset_iUnion I n)) hh.2⟩
      simp [f,hn]
  unfold restrictedLayerCount
  simp_rw [hpoint]
  rw [←lintegral_count (fun y => ⨆ n, f n y),lintegral_iSup hf hmono]
  simp_rw [lintegral_count]
  rfl

theorem restrictedLayerMoment_iUnion (I : ℕ → Set E) (hI : Monotone I)
    (A : Set V) (x : V) (p : unitInterval) {q : ℝ} (hq : 0 < q) :
    (∫⁻ ω, (restrictedLayerCount G (⋃ n, I n) A ω x)^q ∂law p)=
      ⨆ n, ∫⁻ ω, (restrictedLayerCount G (I n) A ω x)^q ∂law p := by
  have hp (ω : Set E) : (restrictedLayerCount G (⋃ n, I n) A ω x)^q =
      ⨆ n, (restrictedLayerCount G (I n) A ω x)^q := by
    rw [restrictedLayerCount_iUnion G I hI A ω x]
    exact (ENNReal.orderIsoRpow q hq).map_iSup _
  simp_rw [hp]
  apply lintegral_iSup
  · intro n
    exact (measurable_restrictedLayerCount G (I n) A x).pow_const q
  · intro n m hnm ω
    exact ENNReal.rpow_le_rpow (restrictedLayerCount_mono_edges G (hI hnm) A ω x) hq.le

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabFractionalRecurrence
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

lemma restrictedLayerCount_le_old_add_new (I J : Set E) (A : Set V)
    (ω : Set E) (x : V) :
    restrictedLayerCount G J A ω x ≤
      restrictedLayerCount G I A ω x + newLayerCount G I J A ω x := by
  unfold restrictedLayerCount newLayerCount
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ A ∧ Conn G (ω ∩ J) x y
  · rw [ite_eq_left hy]
    by_cases hi : Conn G (ω ∩ I) x y
    · simp [hy.1,hy.2,hi]
    · simp [hy.1,hy.2,hi]
  · rw [ite_eq_right hy]
    exact bot_le

variable [Countable V] [Countable E]

theorem restrictedLayerCount_fractional_increment
    (q : E → unitInterval) (I J : Set E) (A : Set V) (x : V)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∫⁻ ω, restrictedLayerCount G J A ω x^s
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (∫⁻ ω, restrictedLayerCount G I A ω x^s
        ∂CriticalPercolation.BernoulliProduct.law q) +
      (∫⁻ ω, newLayerCount G I J A ω x^s
        ∂CriticalPercolation.BernoulliProduct.law q) := by
  calc
    _ ≤ ∫⁻ ω, restrictedLayerCount G I A ω x^s + newLayerCount G I J A ω x^s
        ∂CriticalPercolation.BernoulliProduct.law q := by
      apply lintegral_mono
      intro ω
      exact (ENNReal.rpow_le_rpow (restrictedLayerCount_le_old_add_new G I J A ω x) hs.le).trans
        (ENNReal.rpow_add_le_add_rpow _ _ hs.le hs1)
    _ = _ := lintegral_add_left ((measurable_restrictedLayerCount G I A x).pow_const s) _

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabExtensionGeometry
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

lemma height_difference_jump (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ)
    (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.orbitAdjustedHeight a u v| ≤ R) (x : V) :
    ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
  intro e u v hu hv
  have hh := G.orbitAdjustedHeight_change_base hc hl a x u v
  convert hjump e u v hu hv using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  linarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NeighborDegreeBound
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

lemma neighbor_card_le_degree (hl : LocallyFinite G) (x : V) :
    (finite_neighbors hl x).toFinset.card ≤ degree G x := by
  let f : Step G x → {y // Adj G x y} := fun d => ⟨d.1.2,d.1.1,d.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨y,e,he⟩
    exact ⟨⟨(e,y),he⟩,rfl⟩
  let : Fintype (Step G x) := (finite_steps G hl x).fintype
  have hh := Nat.card_le_card_of_surjective f hf
  have hcard : Nat.card {y // Adj G x y}=(finite_neighbors hl x).toFinset.card :=
    (Nat.card_coe_set_eq _).trans (Set.ncard_eq_toFinset_card _ (finite_neighbors hl x))
  rw [hcard] at hh
  exact hh

lemma exists_neighbor_card_bound (hl : LocallyFinite G) (hq : QuasiTransitive G) :
    ∃ d : ℕ, ∀ x, (finite_neighbors hl x).toFinset.card ≤ d := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hq
  exact ⟨d,fun x => (neighbor_card_le_degree G hl x).trans (hd x)⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HalfspaceFiniteShift
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

lemma walk_fractional_layer_comparison (p : unitInterval) (I : Set E)
    (D W Z : Set V) (hI : I ⊆ Percolation.internalEdges G.ends D) (hW : W ⊆ Z)
    {x y : V} (w : G.fullGraph.Walk x y) (hw : ∀ v ∈ w.support, v ∈ D)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length)*
      (∫⁻ ω, (restrictedLayerCount G.ends I W ω y)^q ∂G.law p) ≤
        ∫⁻ ω, (restrictedLayerCount G.ends (Percolation.internalEdges G.ends D) Z ω x)^q ∂G.law p := by
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by rw [←criticalModel_openGraph G.ends Set.univ]; exact h⟩
  obtain ⟨F,hF,hconn⟩ := walk_finite_open_restriction G.ends (w.map f) D (by
    intro v hv
    rw [SimpleGraph.Walk.support_map] at hv
    have hv' : v ∈ w.support := by
      change v ∈ w.support.map id at hv
      simpa only [List.map_id_fun,id_eq] using hv
    exact hw v hv')
  have hcard : F.card ≤ w.length := by simpa only [SimpleGraph.Walk.length_map] using hF
  have hcost : ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length) ≤
      ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) := by
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_of_le_one (le_min p.2.1 (sub_nonneg.mpr p.2.2))
      ((min_le_left _ _).trans p.2.2) hcard
  exact (mul_le_mul' hcost le_rfl).trans
    (forced_path_fractional_layer_comparison G.ends p F I _ W Z hI hW x y hconn hq)

theorem fractional_ceiling_root_ascent
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (k c B : ℝ) {x y : V} (w : G.fullGraph.Walk x y)
    (hcy : c ≤ G.orbitAdjustedHeight a x y)
    (hw : ∀ v ∈ w.support, G.orbitAdjustedHeight a x v ≤ G.orbitAdjustedHeight a x y)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length)*
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ c})
        {v | -k-B ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+B} ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a y v ≤ 0})
        {v | -(k+G.orbitAdjustedHeight a x y)-B ≤ G.orbitAdjustedHeight a y v ∧
          G.orbitAdjustedHeight a y v ≤ -(k+G.orbitAdjustedHeight a x y)+B} ω y)^q ∂G.law p := by
  rw [←SimpleGraph.Walk.length_reverse w]
  apply G.walk_fractional_layer_comparison p _ _ _ _ _ _ w.reverse _ hq
  · apply Percolation.internalEdges_mono G.ends
    intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change G.orbitAdjustedHeight a x v ≤ c at hv
    change G.orbitAdjustedHeight a y v ≤ 0
    linarith
  · intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  · intro v hv
    have hv' : v ∈ w.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change G.orbitAdjustedHeight a y v ≤ 0
    linarith [hw v hv']

theorem fractional_floor_root_descent
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (k c B : ℝ) {x y : V} (w : G.fullGraph.Walk x y)
    (hcy : G.orbitAdjustedHeight a x y ≤ -c)
    (hw : ∀ v ∈ w.support, G.orbitAdjustedHeight a x y ≤ G.orbitAdjustedHeight a x v)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length)*
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -c ≤ G.orbitAdjustedHeight a x v})
        {v | k-B ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ k+B} ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight a y v})
        {v | (k-G.orbitAdjustedHeight a x y)-B ≤ G.orbitAdjustedHeight a y v ∧
          G.orbitAdjustedHeight a y v ≤ (k-G.orbitAdjustedHeight a x y)+B} ω y)^q ∂G.law p := by
  rw [←SimpleGraph.Walk.length_reverse w]
  apply G.walk_fractional_layer_comparison p _ _ _ _ _ _ w.reverse _ hq
  · apply Percolation.internalEdges_mono G.ends
    intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change -c ≤ G.orbitAdjustedHeight a x v at hv
    change 0 ≤ G.orbitAdjustedHeight a y v
    linarith
  · intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  · intro v hv
    have hv' : v ∈ w.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change 0 ≤ G.orbitAdjustedHeight a y v
    linarith [hw v hv']

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HalfspaceFiniteShiftProfile
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

theorem halfspace_ceiling_shift_profile_fixed [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1) (ρ : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ q : ℝ, 0 ≤ q →
      (∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp (ρ*k))) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ c})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ρ*k+T*c)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpaths⟩ := G.stationaryOrbitHeight_bounded_ascent_to_level
    hc hl hq μ hμ hstat hu R hR hjump
  let δ := min (p : ℝ) (1-p)
  have hδ : 0 < δ := lt_min hp0 (sub_pos.mpr hp1)
  have hδlt : δ < 1 := (min_le_left _ _).trans_lt hp1
  let s := -Real.log δ
  have hs : 0 < s := neg_pos.mpr (Real.log_neg hδ hδlt)
  let T := s*A+abs ρ
  refine ⟨T,by dsimp [T]; positivity,fun q hq0 hprofile => ?_⟩
  obtain ⟨D,hD,hbound⟩ := hprofile
  refine ⟨D*ENNReal.ofReal (Real.exp (s*B+abs ρ*R)),
    ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top,fun k hk c hc0 x => ?_⟩
  obtain ⟨y,w,hlen,hylo,hyhi,hw⟩ := hpaths c hc0 x
  have hXY := G.fractional_ceiling_root_ascent hc hl a p k c R w hylo (fun v hv => (hw v hv).2) hq0
  have hh := finite_energy_cancel_length _ _ δ A B c w.length hδ hδlt.le hlen hXY
  have hshift := hbound (k+G.orbitAdjustedHeight a x y) (by linarith) y
  apply hh.trans ((mul_le_mul' le_rfl hshift).trans ?_)
  have hheight : 0 ≤ G.orbitAdjustedHeight a x y := hc0.trans hylo
  have hr₁ := mul_le_mul_of_nonneg_right (le_abs_self ρ) hheight
  have hr₂ := mul_le_mul_of_nonneg_left hyhi (abs_nonneg ρ)
  have he : -Real.log δ*(A*c+B)+ρ*(k+G.orbitAdjustedHeight a x y) ≤
      (s*B+abs ρ*R)+(ρ*k+T*c) := by
    dsimp [s,T]
    nlinarith
  calc
    _ = D*ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)+ρ*(k+G.orbitAdjustedHeight a x y))) := by
      rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ ≤ D*ENNReal.ofReal (Real.exp ((s*B+abs ρ*R)+(ρ*k+T*c))) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
    _ = _ := by rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _),mul_assoc]

theorem halfspace_floor_shift_profile_fixed [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1) (ρ : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ q : ℝ, 0 ≤ q →
      (∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp (ρ*k))) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -c ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ρ*k+T*c)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpaths⟩ := G.stationaryOrbitHeight_bounded_descent_to_level
    hc hl hq μ hμ hstat hu R hR hjump
  let δ := min (p : ℝ) (1-p)
  have hδ : 0 < δ := lt_min hp0 (sub_pos.mpr hp1)
  have hδlt : δ < 1 := (min_le_left _ _).trans_lt hp1
  let s := -Real.log δ
  have hs : 0 < s := neg_pos.mpr (Real.log_neg hδ hδlt)
  let T := s*A+abs ρ
  refine ⟨T,by dsimp [T]; positivity,fun q hq0 hprofile => ?_⟩
  obtain ⟨D,hD,hbound⟩ := hprofile
  refine ⟨D*ENNReal.ofReal (Real.exp (s*B+abs ρ*R)),
    ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top,fun k hk c hc0 x => ?_⟩
  obtain ⟨y,w,hlen,hylo,hyhi,hw⟩ := hpaths c hc0 x
  have hXY := G.fractional_floor_root_descent hc hl a p k c R w hyhi (fun v hv => (hw v hv).1) hq0
  have hh := finite_energy_cancel_length _ _ δ A B c w.length hδ hδlt.le hlen hXY
  have hshift := hbound (k-G.orbitAdjustedHeight a x y) (by linarith) y
  apply hh.trans ((mul_le_mul' le_rfl hshift).trans ?_)
  have hheight : 0 ≤ -G.orbitAdjustedHeight a x y := by linarith
  have hr₁ := mul_le_mul_of_nonneg_right (le_abs_self ρ) hheight
  have hr₂ := mul_le_mul_of_nonneg_left
    (show -G.orbitAdjustedHeight a x y ≤ c+R by linarith) (abs_nonneg ρ)
  have he : -Real.log δ*(A*c+B)+ρ*(k-G.orbitAdjustedHeight a x y) ≤
      (s*B+abs ρ*R)+(ρ*k+T*c) := by
    dsimp [s,T]
    nlinarith
  calc
    _ = D*ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)+ρ*(k-G.orbitAdjustedHeight a x y))) := by
      rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ ≤ D*ENNReal.ofReal (Real.exp ((s*B+abs ρ*R)+(ρ*k+T*c))) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
    _ = _ := by rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _),mul_assoc]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HalfspaceFractionalRecurrence
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

lemma lower_halfspace_frontier_location (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (J : Set E) (x : V) (hx : f x ≤ b)
    {z : V} (hz : z ∈ openFrontier G (ω ∩ J)
      (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x)) :
    b < f z ∧ f z ≤ b+R := by
  obtain ⟨hz,u,hu,e,he,heq⟩ := hz
  have hub := conn_internalEdges_end_mem G ω {v | f v ≤ b} hx hu
  change f u ≤ b at hub
  have hzb : ¬f z ≤ b := openFrontier_lowerCluster_outside G ω
    {v | f v ≤ b} x hx ⟨hz,u,hu,e,he.1,heq⟩
  have hj := (abs_le.mp (hjump e u z (by rw [heq]; simp) (by rw [heq]; simp))).2
  exact ⟨lt_of_not_ge hzb,by linarith⟩

variable [Countable V] [Countable E]

theorem lower_halfspace_newLayer_fractional_bound
    (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (q : E → unitInterval) (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (J : Set E) (x : V) (hx : f x ≤ b)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x).Finite)
    (A : Set V) {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (L : ℝ≥0∞)
    (hL : ∀ z, b < f z → f z ≤ b+R →
      (∫⁻ ω, restrictedLayerCount G J A ω z^a
        ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, newLayerCount G (internalEdges G {v | f v ≤ b}) J A ω x^(a*c)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (d : ℝ≥0∞)^c*(∫⁻ ω,
        restrictedLayerCount G (internalEdges G {v | f v ≤ b})
          {u | b-R ≤ f u ∧ f u ≤ b} ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q)*L^c := by
  let I := internalEdges G {v | f v ≤ b}
  let B := {u | b-R ≤ f u ∧ f u ≤ b}
  have hfront : (∫⁻ ω, frontierCount G I J ω x^c
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (d : ℝ≥0∞)^c*∫⁻ ω, restrictedLayerCount G I B ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q := by
    calc
      _ ≤ ∫⁻ ω, ((d : ℝ≥0∞)*restrictedLayerCount G I B ω x)^c
          ∂CriticalPercolation.BernoulliProduct.law q := by
        apply lintegral_mono_ae
        filter_upwards [hfin] with ω hω
        exact ENNReal.rpow_le_rpow
          (lower_halfspace_frontierCount_le_top_band G hloc d hd f R b hjump ω J x hx hω) hc.le
      _ = _ := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hc.le]
        exact lintegral_const_mul _ ((measurable_restrictedLayerCount G I B x).pow_const c)
  have hnew := newLayerCount_fractional_bound_on_frontier G hloc q I J x hfin A
    ha ha1 hc hc1 L {z | b < f z ∧ f z ≤ b+R}
    (fun ω z hz => lower_halfspace_frontier_location G f R b hjump ω J x hx hz)
    (fun z hz => hL z hz.1 hz.2)
  exact hnew.trans (mul_le_mul' hfront le_rfl)

theorem lower_halfspace_fractional_recurrence
    (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (q : E → unitInterval) (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (J : Set E) (x : V) (hx : f x ≤ b)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x).Finite)
    (A : Set V) {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (L : ℝ≥0∞)
    (hL : ∀ z, b < f z → f z ≤ b+R →
      (∫⁻ ω, restrictedLayerCount G J A ω z^a
        ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, restrictedLayerCount G J A ω x^(a*c)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (∫⁻ ω, restrictedLayerCount G (internalEdges G {v | f v ≤ b}) A ω x^(a*c)
        ∂CriticalPercolation.BernoulliProduct.law q)+
      (d : ℝ≥0∞)^c*(∫⁻ ω,
        restrictedLayerCount G (internalEdges G {v | f v ≤ b})
          {u | b-R ≤ f u ∧ f u ≤ b} ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q)*L^c := by
  have hac : a*c ≤ 1 := by
    calc a*c ≤ a*1 := mul_le_mul_of_nonneg_left hc1 ha.le
         _ ≤ 1 := by simpa only [mul_one] using ha1
  exact (restrictedLayerCount_fractional_increment G q _ J A x (mul_pos ha hc) hac).trans
    (add_le_add le_rfl (lower_halfspace_newLayer_fractional_bound G hloc d hd q f R b
      hjump J x hx hfin A ha ha1 hc hc1 L hL))

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FullspaceFractionalRecurrence
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

lemma internalEdges_ceilings_iUnion (f : V → ℝ) (R b : ℝ) (hR : 0 < R) :
    (⋃ n : ℕ, internalEdges G {z | f z ≤ b+(n : ℝ)*R})=Set.univ := by
  ext e
  simp only [Set.mem_univ,iff_true]
  have hp : ∀ s : Sym2 V, ∃ n : ℕ, ∀ z ∈ s, f z ≤ b+(n : ℝ)*R := by
    intro s
    induction s using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨N,hN⟩ := exists_nat_gt (max ((f u-b)/R) ((f v-b)/R))
      refine ⟨N,fun z hz => ?_⟩
      have hu := (div_lt_iff₀ hR).mp ((le_max_left _ _).trans_lt hN)
      have hv := (div_lt_iff₀ hR).mp ((le_max_right _ _).trans_lt hN)
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> linarith
  obtain ⟨n,hn⟩ := hp (G e)
  exact mem_iUnion.mpr ⟨n,hn⟩

lemma internalEdges_ceilings_monotone (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R) :
    Monotone (fun n : ℕ => internalEdges G {z | f z ≤ b+(n : ℝ)*R}) := by
  intro n m hnm
  apply internalEdges_mono G
  intro z hz
  have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m) hR
  change f z ≤ b+(n : ℝ)*R at hz
  exact hz.trans (by linarith)

variable [Countable V] [Countable E]

theorem fullspace_fractional_from_ceiling_profiles
    (hl : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hl u).toFinset.card ≤ d)
    (h : V → V → ℝ) (hself : ∀ x, h x x=0)
    (hbase : ∀ x z v, h x v=h x z+h z v)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ x e u v, u ∈ G e → v ∈ G e → |h x v-h x u| ≤ R)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (q t α ρ : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (ht : 0 < t) (ht1 : t < 1)
    (hrate : α+t*ρ < 0)
    (htop : ∀ u ∈ ({t,q*t} : Set ℝ), ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
        (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | h x v ≤ k})
          {v | k-R ≤ h x v ∧ h x v ≤ k+R} ω x)^u ∂law p) ≤
            C*ENNReal.ofReal (Real.exp ((α+ε)*k)))
    (D : ℝ≥0∞) (hD : D < ⊤)
    (hcont : ∀ s : ℝ, 0 ≤ s → ∀ z : V,
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | h z v ≤ R})
        {v | -s-R ≤ h z v ∧ h z v ≤ -s+R} ω z)^q ∂law p) ≤
          D*ENNReal.ofReal (Real.exp (ρ*s))) :
    ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G Set.univ
        {v | k-R ≤ h x v ∧ h x v ≤ k+R} ω x)^(q*t) ∂law p) ≤
          C*ENNReal.ofReal (Real.exp ((α+ζ)*k)) := by
  intro ζ hζ
  let ε := min ζ (-(α+t*ρ)/2)
  have hε : 0 < ε := lt_min hζ (by linarith)
  have hεζ : ε ≤ ζ := min_le_left _ _
  have hεrate : ε ≤ -(α+t*ρ)/2 := min_le_right _ _
  have hqt : 0 < q*t := mul_pos hq ht
  obtain ⟨A,hA,hab⟩ := htop t (by simp) ε hε
  obtain ⟨B,hB,hbb⟩ := htop (q*t) (by simp) ε hε
  let K := (d : ℝ≥0∞)^t*A*D^t*ENNReal.ofReal (Real.exp ((max ρ 0*R)*t))
  have hK : K < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg ht.le (ENNReal.natCast_ne_top d)) hA)
      (ENNReal.rpow_lt_top_of_nonneg ht.le hD.ne)) ENNReal.ofReal_lt_top
  let s := -(α+t*ρ)*R/2
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (mul_pos (neg_pos.mpr hrate) hR) (by norm_num)
  let S : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal (Real.exp (-s*n))
  have hS : S < ⊤ := by
    apply Summable.tsum_ofReal_lt_top
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hs)
  refine ⟨B+K*S,ENNReal.add_lt_top.mpr ⟨hB,ENNReal.mul_lt_top hK hS⟩,fun k hk x => ?_⟩
  let f := h x
  let W := {v | k-R ≤ f v ∧ f v ≤ k+R}
  let F (n : ℕ) := ∫⁻ ω, (restrictedLayerCount G
    (internalEdges G {v | f v ≤ k+(n : ℝ)*R}) W ω x)^(q*t) ∂law p
  let Z := ENNReal.ofReal (Real.exp ((α+ε)*k))
  have h0 : F 0 ≤ B*Z := by simpa only [F,Nat.cast_zero,zero_mul,add_zero] using hbb k hk x
  have hstep (n : ℕ) : F (n+1) ≤ F n+K*Z*ENNReal.ofReal (Real.exp (-s*n)) := by
    let b := k+(n : ℝ)*R
    let J := internalEdges G {v | f v ≤ k+((n : ℝ)+1)*R}
    let L := D*ENNReal.ofReal (Real.exp (ρ*((n : ℝ)*R)+max ρ 0*R))
    have hL (z : V) (hzlo : b < f z) (hzhi : f z ≤ b+R) :
        (∫⁻ ω, (restrictedLayerCount G J W ω z)^q ∂law p) ≤ L := by
      let r := f z-k
      have hr : 0 ≤ r := by dsimp [r,b] at *; nlinarith [Nat.cast_nonneg (α := ℝ) n]
      apply le_trans _ ((hcont r hr z).trans ?_)
      · apply lintegral_mono
        intro ω
        apply ENNReal.rpow_le_rpow _ hq.le
        apply (restrictedLayerCount_mono_edges G ?_ W ω z).trans
        · apply restrictedLayerCount_mono_vertices G
          intro v hv
          have he := hbase x z v
          dsimp [r,f,W] at hv ⊢
          exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
        · apply internalEdges_mono G
          intro v hv
          have he := hbase x z v
          dsimp [J,f,b] at hv hzlo hzhi ⊢
          linarith
      · apply mul_le_mul' le_rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hrlo : (n : ℝ)*R ≤ r := by dsimp [r,b] at *; linarith
        have hrhi : r ≤ (n : ℝ)*R+R := by dsimp [r,b] at *; linarith
        by_cases hρ : 0 ≤ ρ
        · rw [max_eq_left hρ]
          nlinarith
        · rw [max_eq_right (le_of_not_ge hρ)]
          nlinarith
    have hI : ∀ᵐ ω ∂law p, (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x).Finite := by
      filter_upwards [hfin x] with ω hω
      exact hω.subset fun v hv => conn_mono G inter_subset_left hv
    have hh := lower_halfspace_fractional_recurrence G hl d hd (fun _ => p) f R b
      (hjump x) J x (by simp only [f,hself]; dsimp [b]; positivity)
      (by simpa only [CriticalPercolation.BernoulliProduct.law_const,law] using hI)
      W hq hq1 ht ht1.le L
      (fun z hzlo hzhi => by simpa only [CriticalPercolation.BernoulliProduct.law_const,law] using hL z hzlo hzhi)
    simp only [CriticalPercolation.BernoulliProduct.law_const] at hh
    have htop' : (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | f v ≤ b})
        {v | b-R ≤ f v ∧ f v ≤ b} ω x)^t ∂law p) ≤
        A*ENNReal.ofReal (Real.exp ((α+ε)*b)) := by
      apply le_trans _ (hab b (by dsimp [b]; positivity) x)
      apply lintegral_mono
      intro ω
      apply ENNReal.rpow_le_rpow _ ht.le
      apply restrictedLayerCount_mono_vertices G
      intro v hv
      exact ⟨hv.1,hv.2.trans (by linarith)⟩
    have hcast : ((n+1 : ℕ) : ℝ)=(n : ℝ)+1 := by norm_cast
    simp only [F,hcast]
    apply hh.trans
    apply add_le_add le_rfl
    apply (mul_le_mul' (mul_le_mul' le_rfl htop') le_rfl).trans
    dsimp [L]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le,ennreal_exp_rpow _ _ ht.le]
    have he : (α+ε)*b+(ρ*((n : ℝ)*R)+max ρ 0*R)*t ≤
        (max ρ 0*R)*t+((α+ε)*k+(-s*(n : ℝ))) := by
      have hh := mul_le_mul_of_nonneg_right hεrate (mul_nonneg (Nat.cast_nonneg n) hR.le)
      dsimp [b,s]
      nlinarith
    calc
      _ = ((d : ℝ≥0∞)^t*A*D^t)*ENNReal.ofReal
          (Real.exp ((α+ε)*b+(ρ*((n : ℝ)*R)+max ρ 0*R)*t)) := by
        rw [Real.exp_add ((α+ε)*b) ((ρ*((n : ℝ)*R)+max ρ 0*R)*t),
          ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
      _ ≤ ((d : ℝ≥0∞)^t*A*D^t)*ENNReal.ofReal (Real.exp
          ((max ρ 0*R)*t+((α+ε)*k+(-s*(n : ℝ))))) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
      _ = _ := by
        dsimp [K,Z]
        rw [Real.exp_add ((max ρ 0*R)*t) ((α+ε)*k+(-s*(n : ℝ))),
          ENNReal.ofReal_mul (Real.exp_nonneg _),Real.exp_add ((α+ε)*k) (-s*(n : ℝ)),
          ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
  have hF := geometric_increment_factored F B K Z s h0 hstep
  have hlim := restrictedLayerMoment_iUnion G
    (fun n : ℕ => internalEdges G {v | f v ≤ k+(n : ℝ)*R})
    (internalEdges_ceilings_monotone G f R k hR.le) W x p hqt
  rw [internalEdges_ceilings_iUnion G f R k hR] at hlim
  rw [hlim]
  apply (iSup_le fun n => hF n).trans
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (by linarith : α+ε ≤ α+ζ) hk)))

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CriticalFullspaceProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_fullspace_threeQuarter_profiles_bs_oai
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G Set.univ
        {v | k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ k+R} ω x)^(3/4 : ℝ) ∂law (pc G)) ≤
        C*ENNReal.ofReal (Real.exp (-k/2))) ∧
      (∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G Set.univ
        {v | -k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^(3/4 : ℝ) ∂law (pc G)) ≤
        C*ENNReal.ofReal (Real.exp (k/16))) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let h := H.orbitAdjustedHeight a
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  have hp0 : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  have hp1 : (pc G : ℝ) < 1 := by exact_mod_cast hpc1
  have hfin := critical_finite_general_bs G hc hl hq hpc1
  obtain ⟨d,hd⟩ := exists_neighbor_card_bound G hl hq
  obtain ⟨hendup,henddown⟩ := critical_endpoint_fractional_profiles_bs G hc hl hq hpc1 hu μ hμ hstat R hR hjump
  have hhalf := critical_halfspace_fractional_profiles_bs G hc hl hq hpc1 hu μ hμ hstat R hR hjump
  have hbase (x z v : V) : h x v=h x z+h z v := H.orbitAdjustedHeight_change_base hHc hl a x z v
  have hself (x : V) : h x x=0 := H.orbitAdjustedHeight_self a x
  have hj (x : V) := H.height_difference_jump hHc hl a R hjump x
  obtain ⟨T₁,_hT₁,hshift₁⟩ := H.halfspace_ceiling_shift_profile_fixed hHc hl hHq μ hμ hstat hu R hR.le hjump
    (pc G) hp0 hp1 (1/4)
  obtain ⟨D₁,hD₁,hb₁⟩ := hshift₁ (7/8) (by norm_num) ((hhalf (7/8) (by norm_num) (by norm_num)).1 (1/4) (by norm_num))
  let D₁' := D₁*ENNReal.ofReal (Real.exp (T₁*R))
  have hD₁' : D₁' < ⊤ := ENNReal.mul_lt_top hD₁ ENNReal.ofReal_lt_top
  have hcont₁ (s : ℝ) (hs : 0 ≤ s) (z : V) :
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | h z v ≤ R})
        {v | -s-R ≤ h z v ∧ h z v ≤ -s+R} ω z)^(7/8 : ℝ) ∂law (pc G)) ≤
          D₁'*ENNReal.ofReal (Real.exp ((1/4)*s)) := by
    apply le_trans _ ((hb₁ s hs R hR.le z).trans_eq ?_)
    · rfl
    · dsimp [D₁']
      rw [Real.exp_add ((1/4)*s) (T₁*R),ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
  have htop₁ : ∀ u ∈ ({(7/8 : ℝ),(7/8 : ℝ)*(7/8 : ℝ)} : Set ℝ), ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | h x v ≤ k})
        {v | k-R ≤ h x v ∧ h x v ≤ k+R} ω x)^u ∂law (pc G)) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ε)*k)) := by
    intro u hu ε hε
    have hu0 : 0 < u := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl <;> norm_num
    have hu1 : u < 1 := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl <;> norm_num
    exact hendup u hu0 hu1 ε hε
  obtain ⟨C₁,hC₁,hfull₁⟩ := fullspace_fractional_from_ceiling_profiles G hl d hd h hself hbase R hR
    hj (pc G) hfin (7/8) (7/8) (-1) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) htop₁ D₁' hD₁' hcont₁ (1/2) (by norm_num)
  obtain ⟨T₂,_hT₂,hshift₂⟩ := H.halfspace_floor_shift_profile_fixed hHc hl hHq μ hμ hstat hu R hR.le hjump
    (pc G) hp0 hp1 (-1+(1/2 : ℝ))
  obtain ⟨D₂,hD₂,hb₂⟩ := hshift₂ (7/8) (by norm_num) ((hhalf (7/8) (by norm_num) (by norm_num)).2 (1/2) (by norm_num))
  let D₂' := D₂*ENNReal.ofReal (Real.exp (T₂*R))
  have hD₂' : D₂' < ⊤ := ENNReal.mul_lt_top hD₂ ENNReal.ofReal_lt_top
  have hnegceil (x : V) (k : ℝ) : {v | -h x v ≤ k}={v | -k ≤ h x v} := by
    ext v
    change (-h x v ≤ k) ↔ -k ≤ h x v
    constructor <;> intro hv <;> linarith
  have hnegband (x : V) (k : ℝ) : {v | k-R ≤ -h x v ∧ -h x v ≤ k+R}=
      {v | -k-R ≤ h x v ∧ h x v ≤ -k+R} := by
    ext v
    constructor <;> intro hv <;> constructor <;> linarith [hv.1,hv.2]
  have hnegcont (x : V) (k : ℝ) : {v | -k-R ≤ -h x v ∧ -h x v ≤ -k+R}=
      {v | k-R ≤ h x v ∧ h x v ≤ k+R} := by
    ext v
    constructor <;> intro hv <;> constructor <;> linarith [hv.1,hv.2]
  have hcont₂ (s : ℝ) (hs : 0 ≤ s) (z : V) :
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | -h z v ≤ R})
        {v | -s-R ≤ -h z v ∧ -h z v ≤ -s+R} ω z)^(7/8 : ℝ) ∂law (pc G)) ≤
          D₂'*ENNReal.ofReal (Real.exp ((-1/2)*s)) := by
    rw [hnegceil,hnegcont]
    apply le_trans _ ((hb₂ s hs R hR.le z).trans_eq ?_)
    · rfl
    · dsimp [D₂']
      rw [Real.exp_add ((-1+(1/2 : ℝ))*s) (T₂*R),ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [show (-1+(1/2 : ℝ))*s=(-1/2)*s by ring]
      ac_rfl
  have htop₂ : ∀ u ∈ ({(7/8 : ℝ),(7/8 : ℝ)*(7/8 : ℝ)} : Set ℝ), ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | -h x v ≤ k})
        {v | k-R ≤ -h x v ∧ -h x v ≤ k+R} ω x)^u ∂law (pc G)) ≤
          C*ENNReal.ofReal (Real.exp ((0+ε)*k)) := by
    intro u hu ε hε
    have hu0 : 0 < u := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl <;> norm_num
    have hu1 : u < 1 := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl <;> norm_num
    obtain ⟨C,hC,hb⟩ := henddown u hu0 hu1 ε hε
    refine ⟨C,hC,fun k hk x => ?_⟩
    simpa only [hnegceil,hnegband,zero_add] using hb k hk x
  obtain ⟨C₂,hC₂,hfull₂⟩ := fullspace_fractional_from_ceiling_profiles G hl d hd
    (fun x v => -h x v) (fun x => by simp only [hself,neg_zero])
    (fun x z v => by rw [hbase]; ring) R hR
    (fun x e u v hu hv => by simpa only [neg_sub_neg,abs_sub_comm] using hj x e u v hu hv)
    (pc G) hfin (7/8) (7/8) 0 (-1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) htop₂ D₂' hD₂' hcont₂ (1/16) (by norm_num)
  have hmono (W : Set V) (x : V) :
      (∫⁻ ω, (restrictedLayerCount G Set.univ W ω x)^(3/4 : ℝ) ∂law (pc G)) ≤
      (∫⁻ ω, (restrictedLayerCount G Set.univ W ω x)^((7/8 : ℝ)*(7/8 : ℝ)) ∂law (pc G)) := by
    apply lintegral_mono
    intro ω
    rcases restrictedLayerCount_zero_or_one_le G Set.univ W ω x with hz | ho
    · simp only [hz,ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3/4),
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (7/8)*(7/8)),le_refl]
    · exact ENNReal.rpow_le_rpow_of_exponent_le ho (by norm_num)
  refine ⟨C₁+C₂,ENNReal.add_lt_top.mpr ⟨hC₁,hC₂⟩,?_,?_⟩
  · intro k hk x
    apply (hmono _ x).trans ((hfull₁ k hk x).trans ?_)
    have he : (-1+(1/2 : ℝ))*k= -k/2 := by ring
    rw [he]
    exact mul_le_mul' le_self_add le_rfl
  · intro k hk x
    have hh := hfull₂ k hk x
    simp only [hnegband,zero_add] at hh
    apply (hmono _ x).trans (hh.trans ?_)
    have he : (1/16 : ℝ)*k=k/16 := by ring
    rw [he]
    exact mul_le_mul' le_add_self le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Percolation.BenjaminiSchramm.critical_fullspace_threeQuarter_profiles_bs_oai.{u_1, u_2} := @OAI.Percolation.BenjaminiSchramm.critical_fullspace_threeQuarter_profiles_bs_oai.{u_1, u_2}
