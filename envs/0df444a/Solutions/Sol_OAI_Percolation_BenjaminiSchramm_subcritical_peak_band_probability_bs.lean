-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.subcritical_peak_band_probability_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:30:07.361495+00:00
-- url     : https://prove2.me/submissions/3844cc26-acd3-4250-9277-9a8fd7ad4951

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_normalized_peak_surgery_bs
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_subcritical_layer_prefactor_bs

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

lemma measurableSet_restricted_exactCluster [Countable V] [Countable E]
    (I : Set E) (x : V) (S : Set V) :
    MeasurableSet {ω | cluster G (ω ∩ I) x = S} := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  simpa only [criticalModel_cluster,Set.preimage_ofPred_eq] using
    ((criticalModel G).measurableSet_exactCluster x S).preimage hm

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

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_MinimumHeightHit
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

lemma restrictedHit_upper (I : Set E) (x : V) (A : Set V) :
    IsUpperSet (restrictedHit G I x A) := by
  rintro ω η hωη ⟨y,hy,hxy⟩
  exact ⟨y,hy,conn_mono G (Set.inter_subset_inter_left _ hωη) hxy⟩

lemma restrictedHit_finiteWitness (I : Set E) (x : V) (A : Set V) :
    FiniteWitness (restrictedHit G I x A) := by
  rintro ω ⟨y,hy,hxy⟩
  obtain ⟨s,hs,hconn⟩ := finiteWitness_conn G x y _ hxy
  refine ⟨s,fun e he => (hs he).1,y,hy,?_⟩
  exact conn_mono G (show (s : Set E) ⊆ (s : Set E) ∩ I from fun e he => ⟨he,(hs he).2⟩) hconn

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_UpperLayerSecondMoment
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

theorem adjusted_upper_layer_second_moment_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (x : V) (u : ℝ) (n : ℕ) :
    (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {y | G.adjustedLayerIndex a R u x y ≤ (n : ℤ)})
      {y | G.adjustedLayerIndex a R u x y=(n : ℤ)} ω x)^2 ∂G.law p) ≤
      ∑' i : ℤ, if i ≤ (n : ℤ) then G.supAdjustedFullLayerMoment a R p i *
        (G.supAdjustedUpLayerMoment a R p ((n : ℤ)-i).toNat)^2 else 0 := by
  let f := G.adjustedLayerIndex a R u x
  let I := Percolation.internalEdges G.ends {y | f y ≤ (n : ℤ)}
  let A := {y | f y=(n : ℤ)}
  let T (z : V) := G.law p {ω | Percolation.Conn G.ends (ω ∩ I) x z}
  let M (z : V) := ∫⁻ ω, restrictedLayerCount G.ends I A ω z ∂G.law p
  have hcont (z : V) (hz : f z ≤ (n : ℤ)) :
      M z ≤ G.supAdjustedUpLayerMoment a R p ((n : ℤ)-f z).toNat := by
    let v := G.orbitAdjustedHeight a x z/R+u
    have hidx (y : V) : f y=f z+G.adjustedLayerIndex a R v z y :=
      G.adjustedLayerIndex_change_base hc hl a R u x z y
    have hdom : {y : V | f y ≤ (n : ℤ)}=
        {y | G.adjustedLayerIndex a R v z y ≤ (((n : ℤ)-f z).toNat : ℤ)} := by
      ext y
      change f y ≤ (n : ℤ) ↔ G.adjustedLayerIndex a R v z y ≤ (((n : ℤ)-f z).toNat : ℤ)
      rw [hidx,Int.toNat_of_nonneg (sub_nonneg.mpr hz)]
      omega
    have htar : A={y | G.adjustedLayerIndex a R v z y = (((n : ℤ)-f z).toNat : ℤ)} := by
      ext y
      change f y=(n : ℤ) ↔ G.adjustedLayerIndex a R v z y = (((n : ℤ)-f z).toNat : ℤ)
      rw [hidx,Int.toNat_of_nonneg (sub_nonneg.mpr hz)]
      omega
    change (∫⁻ ω, restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {y | f y ≤ (n : ℤ)}) A ω z ∂G.law p) ≤ _
    rw [hdom,htar]
    exact G.adjustedUpLayerMoment_le_sup a R p _ z v
  have hzero (z : V) (hz : ¬f z ≤ (n : ℤ)) : T z=0 := by
    have hx : x ∈ {y | f y ≤ (n : ℤ)} := by
      change f x ≤ (n : ℤ)
      simp only [f,G.adjustedLayerIndex_self,Nat.cast_nonneg]
    have he : {ω : Set E | Percolation.Conn G.ends (ω ∩ I) x z}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hz (Percolation.conn_internal_endpoint G.ends {y | f y ≤ (n : ℤ)} hx hω)
    change G.law p {ω | Percolation.Conn G.ends (ω ∩ I) x z}=0
    rw [he,measure_empty]
  have hrow (i : ℤ) : (∑' z, if f z=i then T z else 0) ≤ G.supAdjustedFullLayerMoment a R p i := by
    apply le_trans _ (G.adjustedFullLayerMoment_le_sup a R p i x u)
    rw [adjustedFullLayerMoment]
    change _ ≤ ∫⁻ ω, restrictedLayerCount G.ends Set.univ {y | f y=i} ω x ∂Percolation.law p
    rw [lintegral_restrictedLayerCount]
    apply ENNReal.tsum_le_tsum
    intro z
    by_cases hz : f z=i
    · simp only [Set.mem_ofPred_eq,hz,if_true,T]
      exact measure_mono fun ω hω => Percolation.conn_mono G.ends
        (show ω ∩ I ⊆ ω ∩ Set.univ from fun e he => ⟨he.1,Set.mem_univ e⟩) hω
    · simp only [Set.mem_ofPred_eq,hz,if_false,le_refl]
  calc
    _ ≤ ∑' z, T z*(M z)^2 := by
      simpa only [pow_two,mul_assoc,T,M,I,A,f,law,Percolation.law] using
        restricted_layer_second_moment G.ends I A A p x
    _ ≤ ∑' z, if f z ≤ (n : ℤ) then
        T z*(G.supAdjustedUpLayerMoment a R p ((n : ℤ)-f z).toNat)^2 else 0 := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z ≤ (n : ℤ)
      · rw [ite_eq_left hz]
        exact mul_le_mul' le_rfl (pow_le_pow_left' (hcont z hz) 2)
      · rw [ite_eq_right hz,hzero z hz,zero_mul]
    _ ≤ ∑' z, ∑' i : ℤ, if f z=i ∧ i ≤ (n : ℤ) then
        T z*(G.supAdjustedUpLayerMoment a R p ((n : ℤ)-i).toNat)^2 else 0 := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z ≤ (n : ℤ)
      · rw [ite_eq_left hz]
        have hband : f z=f z ∧ f z ≤ (n : ℤ) := ⟨rfl,hz⟩
        have ht := ENNReal.le_tsum (f := fun i : ℤ => if f z=i ∧ i ≤ (n : ℤ) then
          T z*(G.supAdjustedUpLayerMoment a R p ((n : ℤ)-i).toNat)^2 else 0) (f z)
        rwa [ite_eq_left hband] at ht
      · rw [ite_eq_right hz]
        exact bot_le
    _ = ∑' i : ℤ, if i ≤ (n : ℤ) then (∑' z, if f z=i then T z else 0)*
        (G.supAdjustedUpLayerMoment a R p ((n : ℤ)-i).toNat)^2 else 0 := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro i
      by_cases hi : i ≤ (n : ℤ)
      · rw [ite_eq_left hi,←ENNReal.tsum_mul_right]
        apply tsum_congr
        intro z
        by_cases hz : f z=i <;>
          simp only [hz,hi,true_and,false_and,if_true,if_false,zero_mul]
      · simp only [hi,and_false,if_false,tsum_zero]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : i ≤ (n : ℤ)
      · rw [ite_eq_left hi,ite_eq_left hi]
        exact mul_le_mul' (hrow i) le_rfl
      · simp only [hi,if_false,le_refl]

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

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma restrictedLayerCount_moment_cauchy (I : Set E) (A : Set V) (p : unitInterval) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p)^2 ≤
      law p (restrictedHit G I x A) *
        (∫⁻ ω, (restrictedLayerCount G I A ω x)^2 ∂law p) := by
  apply lintegral_support_cauchy (law p) _ (measurable_restrictedLayerCount G I A x) _
    (measurableSet_finiteWitness _ (restrictedHit_upper G I x A) (restrictedHit_finiteWitness G I x A))
  intro ω hω
  apply ENNReal.tsum_eq_zero.mpr
  intro y
  exact ite_eq_right (fun h => hω ⟨y,h.1,h.2⟩)

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

lemma openFrontier_reachable (ω : Set E) (I : Set E) (x : V) {u : V}
    (hu : u ∈ openFrontier G ω (cluster G (ω ∩ I) x)) : Conn G ω x u := by
  obtain ⟨_,v,hv,e,he,heq⟩ := hu
  exact (conn_mono G Set.inter_subset_left hv).tail ⟨e,he,heq⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntegerFrontierCrossing
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

lemma integer_lower_frontier_level (f : V → ℤ) (n : ℤ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1)
    (ω : Set E) (x : V) (hx : f x < n) {u : V}
    (hu : u ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G {v | f v < n}) x)) : f u=n := by
  have hout := openFrontier_lowerCluster_outside G ω {v | f v < n} x hx hu
  obtain ⟨_,v,hv,e,_he,heq⟩ := hu
  have hvn := conn_internalEdges_end_mem G ω {v | f v < n} hx hv
  have hj := hjump e v u (by rw [heq]; simp) (by rw [heq]; simp)
  change ¬f u < n at hout
  change f v < n at hvn
  omega

lemma integer_frontierCount_le_fullLayerCount [Countable V] [Countable E]
    (f : V → ℤ) (n : ℤ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1)
    (ω : Set E) (x : V) (hx : f x < n) :
    frontierCount G (internalEdges G {v | f v < n}) Set.univ ω x ≤
      restrictedLayerCount G Set.univ {v | f v=n} ω x := by
  apply ENNReal.tsum_le_tsum
  intro u
  by_cases hu : u ∈ openFrontier G (ω ∩ Set.univ)
      (cluster G (ω ∩ internalEdges G {v | f v < n}) x)
  · have hu' : u ∈ openFrontier G ω (cluster G (ω ∩ internalEdges G {v | f v < n}) x) := by
      simpa only [Set.inter_univ] using hu
    have hn := integer_lower_frontier_level G f n hjump ω x hx hu'
    have hc := openFrontier_reachable G ω (internalEdges G {v | f v < n}) x hu'
    simp only [Set.mem_ofPred_eq,Set.inter_univ,ite_eq_left hu',ite_eq_left (show f u=n ∧ Conn G ω x u from ⟨hn,hc⟩),le_refl]
  · rw [ite_eq_right hu]
    exact bot_le

lemma integer_upper_layer_hit_frontier_probability [Countable V] [Countable E]
    (f : V → ℤ) (n : ℤ) (x : V) (hx : f x < n) (p : unitInterval) :
    law p (restrictedHit G (internalEdges G {v | f v ≤ n}) x {v | f v=n}) ≤
      law p {ω | 0 < frontierCount G (internalEdges G {v | f v < n}) Set.univ ω x} := by
  apply measure_mono
  rintro ω ⟨y,hy,hxy⟩
  let S := cluster G (ω ∩ internalEdges G {v | f v < n}) x
  have hyS : y ∉ S := by
    intro h
    have hh := conn_internalEdges_end_mem G ω {v | f v < n} hx h
    change f y < n at hh
    change f y=n at hy
    omega
  obtain ⟨u,hu,_huy⟩ := conn_last_exit_frontier G ω S (mem_cluster_self G _ x) hyS
    (conn_mono G Set.inter_subset_left hxy)
  have hone : (1 : ℝ≥0∞) ≤ frontierCount G (internalEdges G {v | f v < n}) Set.univ ω x := by
    apply le_trans _ (ENNReal.le_tsum u)
    have hu' : u ∈ openFrontier G (ω ∩ Set.univ) S := by simpa only [Set.inter_univ] using hu
    exact (ite_eq_left hu').symm.le
  exact zero_lt_one.trans_le hone

end Percolation.BenjaminiSchramm

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

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PrefixMaximumBootstrap
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

lemma le_prefixMaximum (h : ℕ → ℝ) {j n : ℕ} (hj : j ≤ n) :
    h j ≤ prefixMaximum h n :=
  Finset.le_sup' h (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerPrefactorBootstrap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma ennreal_iSup_square_le {ι : Sort*} (f : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ i, (f i)^2 ≤ C) : (⨆ i, f i)^2 ≤ C := by
  have hsqrt (z : ℝ≥0∞) : (z^((1 : ℝ)/2))^2=z := by
    rw [←ENNReal.rpow_two,←ENNReal.rpow_mul]
    norm_num
  have hroot (i : ι) : f i ≤ C^((1 : ℝ)/2) := by
    have hh := ENNReal.rpow_le_rpow (h i) (by norm_num : 0 ≤ (1 : ℝ)/2)
    rw [←ENNReal.rpow_two,←ENNReal.rpow_mul] at hh
    norm_num at hh
    exact hh
  exact (pow_le_pow_left' (iSup_le hroot) 2).trans_eq (hsqrt C)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_UpperMomentConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Percolation.BenjaminiSchramm

lemma normalized_upper_convolution_bound (S : ℕ → ℝ) (hS : ∀ n, 0 ≤ S n)
    (β K : ℝ) (hβ : 0 < β)
    (hdecay : ∀ n : ℕ, S n ≤ K*Real.exp (-(3*β/4)*n)) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ,
      (∑ i ∈ Finset.range (n+1), S i*(S (n-i))^2) ≤
        A*Real.exp (-β*n)*prefixMaximum (fun j => Real.exp (β*j)*S j) n := by
  let H : ℕ → ℝ := fun j => Real.exp (β*j)*S j
  let g : ℕ → ℝ := fun j => Real.exp (-β/2*j)
  have hg : Summable g := by
    simpa only [g,mul_comm] using
      (Real.summable_exp_nat_mul_iff.mpr (by linarith : -β/2 < 0))
  have hg0 : ∀ j, 0 ≤ g j := fun _ => (Real.exp_pos _).le
  let B := K^2*∑' j, g j
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg K) (tsum_nonneg hg0)
  refine ⟨B+1,by linarith,fun n => ?_⟩
  let M := prefixMaximum H n
  have hM : 0 ≤ M := (mul_nonneg (Real.exp_pos _).le (hS 0)).trans
    (le_prefixMaximum H (Nat.zero_le n))
  have hs (i : ℕ) (hi : i ≤ n) : S i=Real.exp (-β*i)*H i := by
    dsimp only [H]
    rw [←mul_assoc,←Real.exp_add,show -β*(i : ℝ)+β*i=0 by ring,Real.exp_zero,one_mul]
  have hp (i : ℕ) (hi : i ≤ n) :
      S i*(S (n-i))^2 ≤ Real.exp (-β*n)*M*K^2*g (n-i) := by
    have hsum : (i : ℝ)+(n-i : ℕ)=n := by exact_mod_cast (Nat.add_sub_of_le hi)
    calc
      _ = (Real.exp (-β*i)*H i)*(S (n-i))^2 := by rw [hs i hi]
      _ ≤ (Real.exp (-β*i)*M)*(K*Real.exp (-(3*β/4)*(n-i : ℕ)))^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (le_prefixMaximum H hi) (Real.exp_pos _).le)
          (pow_le_pow_left₀ (hS (n-i)) (hdecay (n-i)) 2) (sq_nonneg _)
          (mul_nonneg (Real.exp_pos _).le hM)
      _ = Real.exp (-β*n)*M*K^2*g (n-i) := by
        have he : Real.exp (-β*i)*(Real.exp (-(3*β/4)*(n-i : ℕ)))^2 =
            Real.exp (-β*n)*g (n-i) := by
          rw [pow_two,←Real.exp_add,←Real.exp_add]
          dsimp only [g]
          rw [←Real.exp_add]
          congr 1
          nlinarith [hsum]
        calc
          _ = M*K^2*(Real.exp (-β*i)*(Real.exp (-(3*β/4)*(n-i : ℕ)))^2) := by ring
          _ = _ := by rw [he]; ring
  have hsumg : (∑ i ∈ Finset.range (n+1), g (n-i)) ≤ ∑' j, g j := by
    have he := Finset.sum_range_reflect g (n+1)
    simp only [Nat.add_sub_cancel] at he
    rw [he]
    exact hg.sum_le_tsum _ (fun j _ => hg0 j)
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), Real.exp (-β*n)*M*K^2*g (n-i) :=
      Finset.sum_le_sum fun i hi => hp i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = Real.exp (-β*n)*M*K^2*(∑ i ∈ Finset.range (n+1), g (n-i)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-β*n)*M*K^2*(∑' j, g j) :=
      mul_le_mul_of_nonneg_left hsumg (by positivity)
    _ = B*Real.exp (-β*n)*M := by dsimp only [B]; ring
    _ ≤ (B+1)*Real.exp (-β*n)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NegativeMomentConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Percolation.BenjaminiSchramm

lemma normalized_negative_square_convolution_bound (S : ℕ → ℝ)
    (hS : ∀ n, 0 ≤ S n) (β K χ : ℝ) (hβ : 0 < β) (hχ : 0 ≤ χ)
    (hbound : ∀ n, S n ≤ χ) (hmul : ∀ n j, S (n+j) ≤ S n*S j)
    (hdecay : ∀ n : ℕ, S n ≤ K*Real.exp (-(3*β/4)*n)) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      Summable (fun j => (S (n+j))^2) ∧
      (∑' j : ℕ, (S (n+j))^2) ≤
        D*Real.exp (-β*n)*prefixMaximum (fun j => Real.exp (β*j)*S j) n := by
  have hgeom : Summable (fun j : ℕ => K^2*Real.exp (-(3*β/2)*j)) := by
    apply Summable.mul_left
    simpa only [mul_comm] using
      (Real.summable_exp_nat_mul_iff.mpr (by linarith : -(3*β/2) < 0))
  have hsqbound (j : ℕ) : (S j)^2 ≤ K^2*Real.exp (-(3*β/2)*j) := by
    calc
      _ ≤ (K*Real.exp (-(3*β/4)*j))^2 := pow_le_pow_left₀ (hS j) (hdecay j) 2
      _ = _ := by
        rw [mul_pow,pow_two (Real.exp _),←Real.exp_add]
        congr 2
        ring
  have hsq : Summable (fun j : ℕ => (S j)^2) :=
    hgeom.of_nonneg_of_le (fun j => sq_nonneg _) hsqbound
  let B : ℝ := ∑' j : ℕ, (S j)^2
  have hB : 0 ≤ B := tsum_nonneg fun _ => sq_nonneg _
  refine ⟨χ*B+1,by positivity,fun n => ?_⟩
  have hpoint (j : ℕ) : (S (n+j))^2 ≤ (S n)^2*(S j)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (hS (n+j)) (hmul n j) 2
  have hnsq : Summable (fun j : ℕ => (S (n+j))^2) :=
    (hsq.mul_left ((S n)^2)).of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
  refine ⟨hnsq,?_⟩
  let H : ℕ → ℝ := fun j => Real.exp (β*j)*S j
  let M := prefixMaximum H n
  have hM : 0 ≤ M := (mul_nonneg (Real.exp_pos _).le (hS 0)).trans
    (le_prefixMaximum H (Nat.zero_le n))
  have he : S n=Real.exp (-β*n)*H n := by
    dsimp only [H]
    rw [←mul_assoc,←Real.exp_add,show -β*(n : ℝ)+β*n=0 by ring,Real.exp_zero,one_mul]
  have hSn : (S n)^2 ≤ χ*Real.exp (-β*n)*M := by
    calc
      _ = S n*(Real.exp (-β*n)*H n) := by rw [←he]; ring
      _ ≤ χ*(Real.exp (-β*n)*M) :=
        mul_le_mul (hbound n) (mul_le_mul_of_nonneg_left
          (le_prefixMaximum H le_rfl) (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hS n))) hχ
      _ = _ := (mul_assoc _ _ _).symm
  calc
    _ ≤ ∑' j : ℕ, (S n)^2*(S j)^2 := hnsq.tsum_le_tsum hpoint (hsq.mul_left _)
    _ = (S n)^2*B := by rw [hsq.tsum_mul_left]
    _ ≤ (χ*Real.exp (-β*n)*M)*B := mul_le_mul_of_nonneg_right hSn hB
    _ = (χ*B)*Real.exp (-β*n)*M := by ring
    _ ≤ (χ*B+1)*Real.exp (-β*n)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Percolation.BenjaminiSchramm

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

variable [Countable V] [Countable E]

lemma measurableSet_strictPeakBandEvent (a : V → ℝ) (l u : ℝ) (x : V) :
    MeasurableSet (G.strictPeakBandEvent a l u x) := by
  exact (Measurable.exists fun z => measurable_const.and
    (measurable_const.and (measurableSet_strictHeightPeakConnection G.ends _ x z).mem)).setOf

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakFrontierTruncation
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

lemma small_frontier_probability_lower (p : unitInterval)
    (A : Set (Set E)) (Z : Set E → ℝ≥0∞) (hZ : Measurable Z)
    (a M N : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) (hN : 0 < N)
    (hlower : ENNReal.ofReal a ≤ law p A)
    (hmoment : (∫⁻ ω, Z ω ∂law p) ≤ ENNReal.ofReal M)
    (hscale : 2*M ≤ N*a) :
    ENNReal.ofReal (a/2) ≤ law p (A ∩ {ω | Z ω ≤ ENNReal.ofReal N}) := by
  let B : Set (Set E) := {ω | Z ω ≤ ENNReal.ofReal N}
  have hB : MeasurableSet B := measurableSet_le hZ measurable_const
  have hbad : law p (A \ B) ≤ ENNReal.ofReal (M/N) := by
    calc
      _ ≤ law p {ω | ENNReal.ofReal N ≤ Z ω} := measure_mono fun ω hω => by
        have hh : ¬ Z ω ≤ ENNReal.ofReal N := hω.2
        exact le_of_not_ge hh
      _ ≤ (∫⁻ ω, Z ω ∂law p)/ENNReal.ofReal N :=
        meas_ge_le_lintegral_div hZ.aemeasurable
          (ENNReal.ofReal_ne_zero_iff.mpr hN) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M/ENNReal.ofReal N := ENNReal.div_le_div_right hmoment _
      _ = _ := (ENNReal.ofReal_div_of_pos hN).symm
  have hbadreal : (law p).real (A \ B) ≤ M/N := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    rwa [ENNReal.toReal_ofReal (div_nonneg hM hN.le)] at hh
  have hlowreal : a ≤ (law p).real A := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hlower
    rwa [ENNReal.toReal_ofReal ha] at hh
  have hdiv : M/N ≤ a/2 := (div_le_iff₀ hN).mpr (by nlinarith)
  have hsplit := measureReal_sdiff_add_inter (μ := law p) (s := A) hB
  apply ENNReal.ofReal_le_of_le_toReal
  change a/2 ≤ (law p).real (A ∩ B)
  linarith

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSurgeryAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma lowerFrontier_partition_measure (hloc : LocallyFinite G) (p : unitInterval)
    (I J : Set E) (x : V) (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) x).Finite)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    law p B = ∑' A : Finset V × Finset V,
      law p (lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V) ∩ B) := by
  have hfin' : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law (fun _ : E => p),
      (cluster G (ω ∩ I) x).Finite := by
    simpa only [CriticalPercolation.BernoulliProduct.law_const,Percolation.law] using hfin
  have hh := lintegral_lowerFrontier_partition G hloc (fun _ : E => p) I J x hfin'
    (B.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hB)
  rw [CriticalPercolation.BernoulliProduct.law_const] at hh
  change (∫⁻ ω, B.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂law p) = _ at hh
  rw [←lintegral_indicator_fun_one hB]
  apply hh.trans
  apply tsum_congr
  intro A
  have he : (lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V)).indicator
      (B.indicator (fun _ => (1 : ℝ≥0∞))) =
      (lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V) ∩ B).indicator
        (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V)
    <;> by_cases hb : ω ∈ B <;> simp [Set.indicator,ha,hb]
  rw [he,lintegral_indicator_fun_one ((measurableSet_lowerFrontierCell G I J x _ _).inter hB)]
  rfl

lemma peak_probability_of_frontier_surgery (hloc : LocallyFinite G) (p : unitInterval)
    (I J : Set E) (x : V) (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) x).Finite)
    (B : Set (Set E)) (hB : MeasurableSet B) (N L d : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hlocal : ∀ (S F : Finset V),
      (lowerFrontierCell G I J x (S : Set V) (F : Set V)).Nonempty →
      (0 < F.card ∧ F.card ≤ N) →
      law p (lowerFrontierCell G I J x (S : Set V) (F : Set V))*
        ENNReal.ofReal (δ^(d*(F.card+L+1))) ≤
          law p (lowerFrontierCell G I J x (S : Set V) (F : Set V) ∩ B)) :
    law p {ω | 0 < frontierCount G I J ω x ∧ frontierCount G I J ω x ≤ (N : ℝ≥0∞)}*
      ENNReal.ofReal (δ^(d*(N+L+1))) ≤ law p B := by
  let C : Set (Set E) := {ω | 0 < frontierCount G I J ω x ∧ frontierCount G I J ω x ≤ (N : ℝ≥0∞)}
  have hC : MeasurableSet C :=
    (measurableSet_lt measurable_const (measurable_frontierCount G I J x)).inter
      (measurableSet_le (measurable_frontierCount G I J x) measurable_const)
  rw [show law p {ω | 0 < frontierCount G I J ω x ∧ frontierCount G I J ω x ≤ (N : ℝ≥0∞)}=law p C from rfl,
    lowerFrontier_partition_measure G hloc p I J x hfin C hC,
    lowerFrontier_partition_measure G hloc p I J x hfin B hB,←ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro A
  let cell := lowerFrontierCell G I J x (A.1 : Set V) (A.2 : Set V)
  by_cases hgood : 0 < A.2.card ∧ A.2.card ≤ N
  · by_cases hcell : cell.Nonempty
    · calc
        _ ≤ law p cell*ENNReal.ofReal (δ^(d*(N+L+1))) := mul_le_mul' (measure_mono Set.inter_subset_left) le_rfl
        _ ≤ law p cell*ENNReal.ofReal (δ^(d*(A.2.card+L+1))) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ hδ1 (Nat.mul_le_mul_left d (by omega))))
        _ ≤ _ := hlocal A.1 A.2 hcell hgood
    · have he : cell=∅ := Set.not_nonempty_iff_eq_empty.mp hcell
      change law p (cell ∩ C)*_ ≤ law p (cell ∩ B)
      simp only [he,Set.empty_inter,measure_empty,zero_mul,le_refl]
  · have he : cell ∩ C=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hω,hωC⟩
      have hcard := frontierCount_eq_card_on_cell G I J x _ A.2 hω
      have hgood' : (0 : ℝ≥0∞) < (A.2.card : ℝ≥0∞) ∧ (A.2.card : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
        simpa only [C,Set.mem_ofPred_eq,hcard] using hωC
      exact hgood (by exact_mod_cast hgood')
    change law p (cell ∩ C)*_ ≤ _
    rw [he,measure_empty,zero_mul]
    exact bot_le

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SignedUpperConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma signed_upper_convolution_bound (S : ℕ → ℝ) (hS : ∀ n, 0 ≤ S n)
    (β K χ : ℝ) (hβ : 0 < β) (hχ : 0 ≤ χ)
    (hbound : ∀ n, S n ≤ χ) (hmul : ∀ n j, S (n+j) ≤ S n*S j)
    (hdecay : ∀ n : ℕ, S n ≤ K*Real.exp (-(3*β/4)*n))
    (F : ℤ → ℝ≥0∞) (hF : ∀ i, F i ≤ ENNReal.ofReal χ)
    (hFpos : ∀ i : ℕ, F i ≤ ENNReal.ofReal (χ*S i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑' i : ℤ, if i ≤ (n : ℤ) then F i*(ENNReal.ofReal (S ((n : ℤ)-i).toNat))^2 else 0) ≤
        ENNReal.ofReal (C*Real.exp (-β*n)*prefixMaximum (fun j => Real.exp (β*j)*S j) n) := by
  obtain ⟨A,hA,hpos⟩ := normalized_upper_convolution_bound S hS β K hβ hdecay
  obtain ⟨D,hD,hneg⟩ := normalized_negative_square_convolution_bound S hS β K χ hβ hχ hbound hmul hdecay
  refine ⟨χ*(A+D)+1,by positivity,fun n => ?_⟩
  let M := prefixMaximum (fun j => Real.exp (β*j)*S j) n
  have hM : 0 ≤ M := (mul_nonneg (Real.exp_pos _).le (hS 0)).trans
    (le_prefixMaximum (fun j => Real.exp (β*j)*S j) (Nat.zero_le n))
  let f (i : ℤ) : ℝ≥0∞ := if i ≤ (n : ℤ) then F i*(ENNReal.ofReal (S ((n : ℤ)-i).toNat))^2 else 0
  have hp : (∑' i : ℕ, f i) ≤ ENNReal.ofReal (χ*A*Real.exp (-β*n)*M) := by
    rw [tsum_eq_sum (s := Finset.range (n+1)) (fun i hi => ?_)]
    · calc
        _ ≤ ∑ i ∈ Finset.range (n+1), ENNReal.ofReal (χ*(S i*(S (n-i))^2)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hz : (i : ℤ) ≤ n := by exact_mod_cast hin
          have hid : ((n : ℤ)-(i : ℤ)).toNat=n-i := by omega
          dsimp only [f]
          rw [ite_eq_left hz,hid]
          calc
            _ ≤ ENNReal.ofReal (χ*S i)*(ENNReal.ofReal (S (n-i)))^2 :=
              mul_le_mul' (hFpos i) le_rfl
            _ = _ := by
              simp only [ENNReal.ofReal_mul hχ,ENNReal.ofReal_mul (hS i),
                ENNReal.ofReal_pow (hS (n-i))]
              ring
        _ = ENNReal.ofReal (χ*(∑ i ∈ Finset.range (n+1), S i*(S (n-i))^2)) := by
          rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
          intro i hi
          exact mul_nonneg hχ (mul_nonneg (hS i) (sq_nonneg _))
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by
          have hh := mul_le_mul_of_nonneg_left (hpos n) hχ
          dsimp only [M] at *
          nlinarith)
    · have hin : n < i := by
        have hh : ¬i < n+1 := by simpa only [Finset.mem_range] using hi
        omega
      have hz : ¬(i : ℤ) ≤ n := by omega
      simp only [f,ite_eq_right hz]
  have hn : (∑' j : ℕ, f (-(j+1))) ≤ ENNReal.ofReal (χ*D*Real.exp (-β*n)*M) := by
    calc
      _ ≤ ∑' j : ℕ, ENNReal.ofReal χ*ENNReal.ofReal ((S (n+(j+1)))^2) := by
        apply ENNReal.tsum_le_tsum
        intro j
        have hz : -((j : ℤ)+1) ≤ (n : ℤ) := by omega
        have hid : ((n : ℤ)-(-((j : ℤ)+1))).toNat=n+(j+1) := by omega
        dsimp only [f]
        rw [ite_eq_left hz,hid,ENNReal.ofReal_pow (hS _)]
        exact mul_le_mul' (hF _) le_rfl
      _ = ENNReal.ofReal χ*(∑' j : ℕ, ENNReal.ofReal ((S (n+(j+1)))^2)) :=
        ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal χ*(∑' j : ℕ, ENNReal.ofReal ((S (n+j))^2)) := by
        apply mul_le_mul' le_rfl
        exact ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
          (fun j => ENNReal.ofReal ((S (n+j))^2))
      _ = ENNReal.ofReal (χ*(∑' j : ℕ, (S (n+j))^2)) := by
        rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hneg n).1,
          ENNReal.ofReal_mul hχ]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have hh := mul_le_mul_of_nonneg_left (hneg n).2 hχ
        dsimp only [M] at *
        nlinarith)
  change (∑' i : ℤ, f i) ≤ _
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  calc
    _ ≤ ENNReal.ofReal (χ*A*Real.exp (-β*n)*M)+ENNReal.ofReal (χ*D*Real.exp (-β*n)*M) :=
      add_le_add hp hn
    _ = ENNReal.ofReal ((χ*(A+D))*Real.exp (-β*n)*M) := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SubcriticalUpperSecondMoment
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
variable {V E : Type*} [Countable V] [Countable E] [Nonempty V] (G : BondGraph V E)

theorem adjusted_upper_layer_second_moment_constant
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (χ : ℝ) (hχ : 0 ≤ χ)
    (hrow : ∀ x, (∑' y, G.law p {ω | Percolation.Conn G.ends ω x y}) ≤ ENNReal.ofReal χ)
    (β K : ℝ) (hβ : 0 < β) (hK : 0 < K)
    (hup : ∀ n : ℕ, G.supAdjustedUpLayerMoment a R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (x : V) (u : ℝ),
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {y | G.adjustedLayerIndex a R u x y ≤ (n : ℤ)})
        {y | G.adjustedLayerIndex a R u x y=(n : ℤ)} ω x)^2 ∂G.law p) ≤
          ENNReal.ofReal (A*Real.exp (-β*n)) := by
  let S : ℕ → ℝ := fun n => (G.supAdjustedUpLayerMoment a R p n).toReal
  have hne (n : ℕ) : G.supAdjustedUpLayerMoment a R p n ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup n)
  have hS (n : ℕ) : 0 ≤ S n := ENNReal.toReal_nonneg
  have hSEq (n : ℕ) : ENNReal.ofReal (S n)=G.supAdjustedUpLayerMoment a R p n := ENNReal.ofReal_toReal (hne n)
  have hbound (n : ℕ) : S n ≤ χ := by
    have hb : G.supAdjustedUpLayerMoment a R p n ≤ ENNReal.ofReal χ := by
      apply iSup_le
      intro x
      apply iSup_le
      intro u
      exact restrictedLayerCount_expectation_le_row_bound G.ends p _ hrow _ _ x
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rwa [ENNReal.toReal_ofReal hχ] at hh
  have hSK (n : ℕ) : S n ≤ K*Real.exp (-β*n) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hup n)
    rwa [ENNReal.toReal_ofReal (mul_nonneg hK.le (Real.exp_nonneg _))] at hh
  have hdecay (n : ℕ) : S n ≤ K*Real.exp (-(3*β/4)*n) := by
    apply (hSK n).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.exp_le_exp.mpr
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmul (n j : ℕ) : S (n+j) ≤ S n*S j := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (hne n) (hne j))
      (G.supAdjustedUpLayerMoment_submultiplicative hc hl a R hR hjump p n j)
    simpa only [ENNReal.toReal_mul] using hh
  have hF (i : ℤ) : G.supAdjustedFullLayerMoment a R p i ≤ ENNReal.ofReal χ :=
    G.supAdjustedFullLayerMoment_le_row_bound a R p _ hrow i
  have hFpos (n : ℕ) : G.supAdjustedFullLayerMoment a R p n ≤ ENNReal.ofReal (χ*S n) := by
    apply (G.supAdjustedFullLayerMoment_up_bound hc hl a R hR hjump p _ hrow n).trans_eq
    rw [←hSEq n]
    rw [←ENNReal.ofReal_mul (hS n)]
    congr 1
    ring
  obtain ⟨A,hA,hsecond⟩ := signed_upper_convolution_bound S hS β K χ hβ hχ hbound hmul hdecay
    (G.supAdjustedFullLayerMoment a R p) hF hFpos
  have hprefix (n : ℕ) : prefixMaximum (fun j => Real.exp (β*j)*S j) n ≤ K := by
    apply Finset.sup'_le
    intro j _
    calc
      _ ≤ Real.exp (β*j)*(K*Real.exp (-β*j)) :=
        mul_le_mul_of_nonneg_left (hSK j) (Real.exp_nonneg _)
      _ = K := by
        rw [show Real.exp (β*(j : ℝ))*(K*Real.exp (-β*j)) =
          K*(Real.exp (β*j)*Real.exp (-β*j)) by ring,←Real.exp_add,
          show β*(j : ℝ)+ -β*j=0 by ring,Real.exp_zero,mul_one]
  refine ⟨A*K,mul_pos hA hK,?_⟩
  intro n x u
  apply (G.adjusted_upper_layer_second_moment_bound hc hl a R p x u n).trans
  have hb := hsecond n
  simp only [hSEq] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left (hprefix n) (mul_nonneg hA.le (Real.exp_nonneg (-β*n)))
  nlinarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_UpwardFrontierProbability
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
lemma supAdjustedFrontierProbability_le_one (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) :
    G.supAdjustedFrontierProbability a R p n ≤ 1 := by
  apply iSup_le
  intro x
  apply iSup_le
  intro u
  exact prob_le_one

theorem adjusted_frontier_probability_lower
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (β A : ℝ) (hA : 0 < A)
    (hlower : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-β*n)) ≤ G.supAdjustedUpLayerMoment a R p n)
    (hsecond : ∀ (n : ℕ) (x : V) (u : ℝ),
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ (n : ℤ)})
        {v | G.adjustedLayerIndex a R u x v=(n : ℤ)} ω x)^2 ∂G.law p) ≤
          ENNReal.ofReal (A*Real.exp (-β*n))) (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (Real.exp (-β*n)/A) ≤ G.supAdjustedFrontierProbability a R p n := by
  let P := G.supAdjustedFrontierProbability a R p n
  let t := Real.exp (-β*n)
  have ht : 0 < t := Real.exp_pos _
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (G.supAdjustedFrontierProbability_le_one a R p n)
  have hsq : (G.supAdjustedUpLayerMoment a R p n)^2 ≤ P*ENNReal.ofReal (A*t) := by
    apply ennreal_iSup_square_le
    intro x
    apply ennreal_iSup_square_le
    intro u
    let f := G.adjustedLayerIndex a R u x
    have hfx : f x < (n : ℤ) := by
      simp only [f,G.adjustedLayerIndex_self]
      exact_mod_cast hn
    have hprob := integer_upper_layer_hit_frontier_probability G.ends f (n : ℤ) x hfx p
    have hsup : G.law p {ω | 0 < frontierCount G.ends
        (Percolation.internalEdges G.ends {v | f v < (n : ℤ)}) Set.univ ω x} ≤ P :=
      le_iSup_of_le x (le_iSup_of_le u le_rfl)
    exact (restrictedLayerCount_moment_cauchy G.ends _ _ p x).trans
      (mul_le_mul' (hprob.trans hsup) (hsecond n x u))
  have hlo : (ENNReal.ofReal t)^2 ≤ P*ENNReal.ofReal (A*t) :=
    (pow_le_pow_left' (hlower n) 2).trans hsq
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hP ENNReal.ofReal_ne_top) hlo
  rw [ENNReal.toReal_pow,ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (mul_nonneg hA.le ht.le)] at hreal
  have hc : t ≤ P.toReal*A := (mul_le_mul_iff_right₀ ht).mp (by nlinarith)
  apply ENNReal.ofReal_le_of_le_toReal
  exact (div_le_iff₀ hA).mpr (by nlinarith)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SubcriticalPeakProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_peak_band_probability_bs_oai
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G) :
    ∃ β : ℝ, R < β ∧ ∃ K : ℝ, 0 < K ∧
      (∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
        ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∃ x : V,
      ENNReal.ofReal (c*Real.exp (-β*n)) ≤
        (criticalModel G).law p ((criticalModel G).strictPeakBandEvent
          ((criticalModel G).stationaryOrbitWeight μ) (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) x) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  obtain ⟨β,hβR,hlo,K,hK,hup⟩ := subcritical_layer_prefactor_bs G hc hl hq μ hμ hstat hu R hR hjump p hp hpc
  have hβ : 0 < β := hR.trans hβR
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq p hpc
  obtain ⟨A,hA,hsecond⟩ := H.adjusted_upper_layer_second_moment_constant hHc hl a R hR hjump p
    χ hχ hrow β K hβ hK hup
  obtain ⟨L,hsurgery⟩ := normalized_peak_surgery_bs G hc hl hq μ hμ hstat hu R hR hjump
  obtain ⟨d,_hd,hd⟩ := exists_degree_bound G hq
  obtain ⟨N,hN⟩ := exists_nat_gt (max (4*A*χ*K) 1)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hN.le)
  have hNscale : 4*A*χ*K ≤ (N : ℝ) := (le_max_left _ _).trans hN.le
  let δ : ℝ := min (p : ℝ) (1-p)
  have hp1 : (p : ℝ) < 1 := (show (p : ℝ) < (pc G : ℝ) from hpc).trans_le (pc G).2.2
  have hδ : 0 < δ := lt_min hp (sub_pos.mpr hp1)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans p.2.2
  let ε : ℝ := δ^(d*(N+L+1))
  have hε : 0 < ε := pow_pos hδ _
  refine ⟨β,hβR,K,hK,hup,ε/(4*A),div_pos hε (by positivity),?_⟩
  intro n hn
  let t := Real.exp (-β*n)
  have ht : 0 < t := Real.exp_pos _
  have hfront := H.adjusted_frontier_probability_lower a R p β A hA hlo hsecond n hn
  have hhalf : ENNReal.ofReal (t/(2*A)) < H.supAdjustedFrontierProbability a R p n := by
    apply lt_of_lt_of_le _ hfront
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < t/A)).mpr
    apply (div_lt_div_iff₀ (by positivity : 0 < 2*A) hA).mpr
    nlinarith
  obtain ⟨x,hx⟩ := lt_iSup_iff.mp hhalf
  obtain ⟨offset,hoffset⟩ := lt_iSup_iff.mp hx
  let f := H.adjustedLayerIndex a R offset x
  let I := internalEdges G {v | f v < (n : ℤ)}
  let Z : Set E → ℝ≥0∞ := fun ω => frontierCount G I Set.univ ω x
  have hfx : f x < (n : ℤ) := by
    simp only [f,H.adjustedLayerIndex_self]
    exact_mod_cast hn
  have hfj : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1 := by
    intro e v w hv hw
    exact (H.adjustedLayerIndex_edge_jump hHc hl a R offset hR hjump x v w e hv hw).2
  have hmoment : (∫⁻ ω, Z ω ∂law p) ≤ ENNReal.ofReal (χ*K*t) := by
    apply (lintegral_mono fun ω => integer_frontierCount_le_fullLayerCount G f n hfj ω x hfx).trans
    apply (H.adjustedFullLayerMoment_up_bound hHc hl a R hR hjump p _ hrow n x offset).trans
    apply (mul_le_mul' (hup n) le_rfl).trans_eq
    rw [←ENNReal.ofReal_mul (mul_nonneg hK.le ht.le)]
    congr 1
    ring
  have hscale : 2*(χ*K*t) ≤ (N : ℝ)*(t/(2*A)) := by
    calc
      _ = (4*A*χ*K*t)/(2*A) := by field_simp; ring
      _ ≤ ((N : ℝ)*t)/(2*A) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hNscale ht.le) (by positivity)
      _ = _ := by ring
  have hsmall := small_frontier_probability_lower p {ω | 0 < Z ω} Z
    (measurable_frontierCount G I Set.univ x) (t/(2*A)) (χ*K*t) N
    (by positivity) (by positivity) hNpos hoffset.le hmoment hscale
  have hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) x).Finite := by
    filter_upwards [subcritical_cluster_finite_ae G p hpc x] with ω hω
    exact hω.subset (fun y hy => conn_mono G Set.inter_subset_left hy)
  let B := H.strictPeakBandEvent a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) x
  have hlocal (S F : Finset V)
      (hcell : (lowerFrontierCell G I Set.univ x (S : Set V) (F : Set V)).Nonempty)
      (hgood : 0 < F.card ∧ F.card ≤ N) :
      law p (lowerFrontierCell G I Set.univ x (S : Set V) (F : Set V))*
        ENNReal.ofReal (δ^(d*(F.card+L+1))) ≤
          law p (lowerFrontierCell G I Set.univ x (S : Set V) (F : Set V) ∩ B) :=
    hsurgery p d hd n hn x offset S F hcell (Finset.card_pos.mp hgood.1)
  have hs := peak_probability_of_frontier_surgery G hl p I Set.univ x hfin B
    (H.measurableSet_strictPeakBandEvent a _ _ x) N L d δ hδ.le hδ1 hlocal
  refine ⟨x,?_⟩
  apply le_trans _ hs
  have hsmall' : ENNReal.ofReal (t/(4*A)) ≤
      law p {ω | 0 < Z ω ∧ Z ω ≤ (N : ℝ≥0∞)} := by
    convert hsmall using 1
    · congr 1
      ring
    · simp only [ENNReal.ofReal_natCast]
      congr 1
  apply (mul_le_mul' hsmall' le_rfl).trans_eq'
  rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ t/(4*A))]
  congr 1
  change (t/(4*A))*ε=ε/(4*A)*t
  ring

end Percolation.BenjaminiSchramm

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Percolation.BenjaminiSchramm.subcritical_peak_band_probability_bs_oai.{u_1, u_2} := @OAI.Percolation.BenjaminiSchramm.subcritical_peak_band_probability_bs_oai.{u_1, u_2}
