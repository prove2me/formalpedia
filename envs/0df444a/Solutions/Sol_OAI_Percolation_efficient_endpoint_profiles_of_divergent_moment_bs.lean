-- Prove2me | solution 1 for OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:34:53.236743+00:00
-- url     : https://prove2.me/submissions/903dbf55-7ea4-4ba0-9b60-4608d3d218af

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

theorem cluster_eq_of_conn {x y : V} (h : Conn G ω x y) :
    cluster G ω x = cluster G ω y := by
  ext z
  exact ⟨fun hxz => conn_trans G ω (conn_symm G ω h) hxz,
    fun hyz => conn_trans G ω h hyz⟩

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

section KernelDomination
attribute [local instance] Classical.propDecidable



theorem exists_operator_of_matrix_domination
    (U K : V → V → ℝ) (hU : ∀ x y, 0 ≤ U x y)
    (hKU : ∀ x y, |K x y| ≤ U x y)
    (B : Hilbert V →L[ℂ] Hilbert V)
    (hB : ∀ x y, B (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ)) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ ‖B‖ ∧
      ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (K x y : ℂ) := by
  have hcol (y : V) : Memℓp (fun x => (K x y : ℂ)) 2 := by
    apply (lp.memℓp (B (lp.single 2 y (1 : ℂ)))).mono'
    intro x
    simpa [hB x y, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU x y)]
      using hKU x y
  let col (y : V) : Hilbert V := ⟨fun x => (K x y : ℂ), hcol y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hLn (f : V →₀ ℂ) : ‖L f‖ ≤ ‖B‖ * ‖finiteEmbedding f‖ := by
    let g : V →₀ ℂ := f.mapRange (fun z => (‖z‖ : ℂ)) (by simp)
    have hg : finiteEmbedding g = positivePart (finiteEmbedding f) := by
      apply lp.ext
      funext x
      simp [g]
    have hpoint (x : V) : ‖L f x‖ ≤ ‖B (finiteEmbedding g) x‖ := by
      have hright : B (finiteEmbedding g) x =
          (∑ y ∈ f.support, ‖f y‖ * U x y : ℝ) := by
        simp only [finiteEmbedding, g, Finsupp.linearCombination_apply]
        rw [Finsupp.sum_mapRange_index (by simp)]
        simp only [Finsupp.sum, map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
          lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hB, Complex.ofReal_sum,
          Complex.ofReal_mul]
      have hnn : 0 ≤ ∑ y ∈ f.support, ‖f y‖ * U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (hU x y))
      rw [hright, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      simp only [L, Finsupp.linearCombination_apply, Finsupp.sum,
        lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      calc
        ‖∑ y ∈ f.support, f y * col y x‖ ≤
            ∑ y ∈ f.support, ‖f y * col y x‖ := norm_sum_le _ _
        _ ≤ ∑ y ∈ f.support, ‖f y‖ * U x y := by
          apply Finset.sum_le_sum
          intro y _
          simpa [col, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left (hKU x y) (norm_nonneg (f y))
    calc
      ‖L f‖ ≤ ‖B (finiteEmbedding g)‖ := lp.norm_mono (by norm_num) hpoint
      _ ≤ ‖B‖ * ‖finiteEmbedding g‖ := B.le_opNorm _
      _ = ‖B‖ * ‖finiteEmbedding f‖ := by rw [hg, norm_positivePart]
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense (norm_nonneg _) hLn, ?_⟩
  intro x y
  have h := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨‖B‖, hLn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at h
  rw [h]
  simp [L, col]

end KernelDomination

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

theorem finiteWitness_conn_finset (G : BondGraph V E) (x : V) (t : Finset V) :
    FiniteWitness {ω | ∀ y ∈ t, Conn G ω x y} := by
  intro ω h
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert a t ha ih =>
    obtain ⟨s, hs, hsa⟩ := finiteWitness_conn G x a ω (h a (by simp))
    obtain ⟨r, hr, hrt⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨s ∪ r, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs hr
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact conn_mono G (by simp) hsa
      · exact conn_mono G (by simp) (hrt y hy)


theorem clusterLarge_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (clusterLarge G x n) := by
  rintro ω η h ⟨t, ht, hc⟩
  exact ⟨t, ht, fun y hy => conn_mono G h (hc y hy)⟩

theorem finiteWitness_clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (clusterLarge G x n) := by
  rintro ω ⟨t, ht, hc⟩
  obtain ⟨s, hs, hsc⟩ := finiteWitness_conn_finset G x t ω hc
  exact ⟨s, hs, t, ht, hsc⟩

theorem measurableSet_clusterLarge [Countable E] (G : BondGraph V E) (x : V) (n : ℕ) :
    MeasurableSet (clusterLarge G x n) :=
  measurableSet_finiteWitness _ (clusterLarge_upper G x n) (finiteWitness_clusterLarge G x n)

theorem clusterLarge_antitone (G : BondGraph V E) (x : V) :
    Antitone (clusterLarge G x) := by
  rintro m n h ω ⟨t, ht, hc⟩
  exact ⟨t, h.trans ht, hc⟩

theorem infinite_cluster_eq_iInter (G : BondGraph V E) (x : V) :
    {ω | (cluster G ω x).Infinite} = ⋂ n, clusterLarge G x n := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h n
    obtain ⟨t, ht, hcard⟩ := h.exists_subset_card_eq n
    exact ⟨t, hcard.ge, ht⟩
  · intro h hfin
    obtain ⟨t, ht, hc⟩ := h (hfin.toFinset.card + 1)
    have hsub : t ⊆ hfin.toFinset := fun y hy => hfin.mem_toFinset.mpr (hc y hy)
    have := Finset.card_le_card hsub
    omega

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

end BKMeasure

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

theorem finiteWitness_edge (e : E) : FiniteWitness {ω : Set E | e ∈ ω} := by
  intro ω he
  exact ⟨{e}, by simpa using he, by simp⟩

end SmallParameter

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Sprinkling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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



theorem finiteEventPolynomial_eq (s : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial s A (p : ℝ) = finiteProbability p s A := by
  unfold finiteEventPolynomial bernoulliPolynomial finiteProbability
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : (t : Set E) ∈ A <;> simp [ht]


end FiniteRusso

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


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

theorem internalEdges_mono (G : BondGraph V E) {S T : Set V} (h : S ⊆ T) :
    internalEdges G S ⊆ internalEdges G T := fun _ he x hx => h (he x hx)

end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Marked
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
    simp only [successMarks_done,successMass_done,if_true,zero_add,mul_one]
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
      simp only [eval,heω,if_false]
    have ho : bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if (edge e t₀ t₁).eval (insert e ω) m then 1 else 0) h) p =
        bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if t₁.eval ω m then 1 else 0) h) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      simp only [eval,Finset.mem_insert_self,if_true]
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
        simp only [eval,hvm,if_false]
      · congr 1
        apply bernoulliPolynomial_congr
        intro m _
        simp only [eval,Finset.mem_insert_self,if_true]
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
      · simp only [heω,if_true]
        rw [← Finset.insert_erase heω,Finset.coe_insert,
          seedMarked_insert_edge G _ R m _ _ _ hv hends]
        by_cases hwm : (searchCrossing G Q R hc).2.2 ∈ m
        · simp only [hwm,if_true,true_iff]
          exact ⟨_,by simp,_,hwm,conn_refl G _ _⟩
        · simp only [hwm,if_false]
          rw [LabelledTree.eval_insert_edge _
            (clusterSearch_valid G n _ _ (F.erase (searchCrossing G Q R hc).2.2)
              (searchAvailable_discover G ha _ _)) (Finset.notMem_erase _ _)]
          exact ih _ _ _ hcard (searchAvailable_discover G ha _ _)
            (Finset.disjoint_insert_left.mpr ⟨hwm,hm⟩) (ω.erase (searchCrossing G Q R hc).1)
            (Finset.erase_subset_erase _ hω)
      · simp only [heω,if_false]
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
  · simp only [hxm,if_true,true_iff]
    exact ⟨x,hxm,conn_refl G _ x⟩
  · simp only [hxm,if_false]
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
  simp only [LabelledTree.forget,ProbeTree.successMass_done,if_true,mul_one]
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

theorem bernoulliPolynomial_open_difference (s : Finset E) (e : E) (he : e ∈ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => if e ∈ t then f t-f (t.erase e) else 0) p =
      p*bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e s)]
  have hclosed : bernoulliPolynomial (s.erase e)
      (fun t => if e ∈ t then f t-f (t.erase e) else 0) p = 0 := by
    rw [← bernoulliPolynomial_zero (s.erase e) p]
    apply bernoulliPolynomial_congr
    intro t ht
    simp [show e ∉ t from fun hh => Finset.notMem_erase e s (ht hh)]
  rw [hclosed,mul_zero,zero_add]
  congr 1
  apply bernoulliPolynomial_congr
  intro t ht
  have het : e ∉ t := fun hh => Finset.notMem_erase e s (ht hh)
  simp [het]


theorem marked_pivotal_russo (G : BondGraph V E) (Q : Finset E) (x : V) (h p : ℝ) :
    markedPivotalMomentOne G Q x h p = p*deriv (markedConnectionPolynomial G Q x h) p := by
  let F := insert x (searchVertices G Q)
  let f : Finset E → Finset V → ℝ := fun ω m =>
    if ∃ y ∈ m, Conn G (ω : Set E) x y then 1 else 0
  have hcard (ω : Finset E) (m : Finset V) : ((markedOpenPivotals G Q x ω m).card:ℝ) =
      ∑ e ∈ Q, if e ∈ ω then f ω m-f (ω.erase e) m else 0 := by
    rw [markedOpenPivotals,Finset.card_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e _
    have hmono : (∃ y ∈ m, Conn G (ω.erase e : Set E) x y) →
        ∃ y ∈ m, Conn G (ω : Set E) x y := by
      rintro ⟨y,hy,hxy⟩
      exact ⟨y,hy,conn_mono G (by exact_mod_cast Finset.erase_subset e ω) hxy⟩
    by_cases he : e ∈ ω <;> by_cases h₁ : ∃ y ∈ m, Conn G (ω : Set E) x y <;>
      by_cases h₀ : ∃ y ∈ m, Conn G (ω.erase e : Set E) x y <;>
      simp only [f,he,h₁,h₀,and_true,and_false,not_true_eq_false,
        not_false_eq_true,if_true,if_false,Nat.cast_one,Nat.cast_zero,sub_self,sub_zero]
    exact False.elim (h₁ (hmono h₀))
  have heq : markedConnectionPolynomial G Q x h =
      bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (f ω) h) := rfl
  rw [heq,(hasDerivAt_bernoulliPolynomial Q _ p).deriv,Finset.mul_sum]
  simp only [markedPivotalMomentOne,hcard,bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← bernoulliPolynomial_open_difference Q e he (fun ω => bernoulliPolynomial F (f ω) h) p]
  apply bernoulliPolynomial_congr
  intro ω _
  by_cases heω : e ∈ ω
  · simp only [heω,if_true,F]
    exact bernoulliPolynomial_sub _ _ _ _
  · simp only [heω,if_false,bernoulliPolynomial_zero]

 
theorem marked_pivotal_first_moment (G : BondGraph V E) (Q : Finset E) (x : V)
    (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    markedPivotalMomentOne G Q x h p ≤
      (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)*
        markedConnectionPolynomial G Q x h p := by
  rw [marked_pivotal_russo]
  exact markedConnection_derivative_bound G Q x p h hp hh d hd hdeg

end MarkedFirstMoment

section PivotalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


theorem pivotal_rootSide_disjoint_marks (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) {e : E} (he : OpenMarkedPivotal G ω m x e) :
    Disjoint (cluster G (ω \ {e}) x) m := by
  rw [Set.disjoint_left]
  exact fun y hy hm => he.2.2 ⟨y,hm,hy⟩



theorem markedEvent_after_pivotal (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (he : OpenMarkedPivotal G ω m x e) (hne : e ≠ f)
    {a b : V} (hab : G e = s(a,b)) (hxa : Conn G (ω \ {e}) x a)
    (hxb : ¬Conn G (ω \ {e}) x b)
    (hf : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) :
    MarkedEvent G (ω \ {f}) m x ↔
      MarkedEvent G ((ω ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ) \ {f}) m b := by
  let W := cluster G (ω \ {e}) x
  have heq : insert e ((ω \ {e}) \ {f}) = ω \ {f} := by
    ext d
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨⟨hd,hde⟩,hdf⟩)
      · exact ⟨he.1,hne⟩
      · exact ⟨hd,hdf⟩
    · rintro ⟨hd,hdf⟩
      by_cases hde : d = e
      · exact Or.inl hde
      · exact Or.inr ⟨⟨hd,hde⟩,hdf⟩
  constructor
  · rintro ⟨y,hy,hxy⟩
    rw [← heq,conn_insert_iff G _ e a b x y hab] at hxy
    rcases hxy with hxy | ⟨_,hby⟩ | ⟨hxb',_⟩
    · exact (he.2.2 ⟨y,hy,conn_mono G Set.sdiff_subset hxy⟩).elim
    · refine ⟨y,hy,conn_mono G ?_ (conn_restrict_cluster_compl_of_subset G (ω \ {e}) x
        Set.sdiff_subset hxb hby)⟩
      intro d hd
      exact ⟨⟨hd.1.1.1,hd.2⟩,hd.1.2⟩
    · exact (hxb (conn_mono G Set.sdiff_subset hxb')).elim
  · rintro ⟨y,hy,hby⟩
    have hxa' : Conn G (ω \ {f}) x a := conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_exterior_of_inside G (ω \ {e}) x hf (conn_refl G _ x) hxa)
    refine ⟨y,hy,(hxa'.tail ⟨e,⟨he.1,hne⟩,hab⟩).trans (conn_mono G ?_ hby)⟩
    exact fun _ h => ⟨h.1.1,h.2⟩

 
theorem openMarkedPivotal_exterior_iff (G : BondGraph V E) (ω : Set E) (m : Set V)
    (x : V) {e : E} (he : OpenMarkedPivotal G ω m x e)
    {a b : V} (hab : G e = s(a,b)) (hxa : Conn G (ω \ {e}) x a)
    (hxb : ¬Conn G (ω \ {e}) x b) (hbm : MarkedEvent G (ω \ {e}) m b)
    (f : E) :
    OpenMarkedPivotal G (ω ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ) m b f ↔
      OpenMarkedPivotal G ω m x f ∧ f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  have hbase : MarkedEvent G (ω ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ) m b := by
    obtain ⟨y,hy,hby⟩ := hbm
    refine ⟨y,hy,conn_mono G ?_ (conn_restrict_cluster_compl G (ω \ {e}) x hxb hby)⟩
    exact fun _ h => ⟨h.1.1,h.2⟩
  have hexterior (hf : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) : e ≠ f := by
    intro h; subst f
    exact ((mem_internalEdges_of_ends G _ e a b hab).mp hf).1 hxa
  constructor
  · intro hf
    have hiff := markedEvent_after_pivotal G ω m x he (hexterior hf.1.2) hab hxa hxb hf.1.2
    exact ⟨⟨hf.1.1,he.2.1,fun h => hf.2.2 (hiff.mp h)⟩,hf.1.2⟩
  · rintro ⟨hf,hout⟩
    have hiff := markedEvent_after_pivotal G ω m x he (hexterior hout) hab hxa hxb hout
    exact ⟨⟨hf.1,hout⟩,hbase,fun h => hf.2.2 (hiff.mpr h)⟩


theorem pivotalRank_injective (G : BondGraph V E) {ω : Set E} (hω : ω.Finite)
    (m : Set V) (x : V) : Set.InjOn (pivotalRank G ω x) {e | OpenMarkedPivotal G ω m x e} := by
  intro e he f hf hsame
  by_contra hne
  rcases pivotal_rootSides_nested G ω m x he hf hne with h | h
  · have hh := Set.ncard_lt_ncard h (cluster_finite_of_finite_edges G (hω.subset Set.sdiff_subset) x)
    exact (Nat.ne_of_lt hh) hsame
  · have hh := Set.ncard_lt_ncard h (cluster_finite_of_finite_edges G (hω.subset Set.sdiff_subset) x)
    exact (Nat.ne_of_lt hh) hsame.symm

 
theorem pivotalRank_lt_iff (G : BondGraph V E) {ω : Set E} (hω : ω.Finite)
    (m : Set V) (x : V) {e f : E} (he : OpenMarkedPivotal G ω m x e)
    (hf : OpenMarkedPivotal G ω m x f) :
    pivotalRank G ω x e < pivotalRank G ω x f ↔
      f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  have hexterior (hout : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) : e ≠ f := by
    obtain ⟨a,b,hab,hxa,_,_⟩ := openMarkedPivotal_oriented G ω m x he
    intro h; subst f
    exact ((mem_internalEdges_of_ends G _ e a b hab).mp hout).1 hxa
  constructor
  · intro hlt
    have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
    rcases pivotal_other_sides G ω m x he hf hne.symm with hinside | hout
    · obtain ⟨a,b,hab,_,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
      obtain ⟨y,hy,hby⟩ := hbm
      have hby' : Conn G (ω \ {f}) b y := conn_mono G
        (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
        (conn_delete_internal_of_outside G (ω \ {e}) x hinside hxb hby)
      have hb : b ∉ cluster G (ω \ {f}) x := fun h => hf.2.2 ⟨y,hy,h.trans hby'⟩
      have ha : a ∉ cluster G (ω \ {f}) x := fun h =>
        hb ((edge_cluster_sides G (ω \ {f}) x ⟨he.1,hne⟩ hab).mp h)
      have hs := pivotal_rootSide_ssubset G ω m x hf hne.symm
        ((mem_internalEdges_of_ends G _ e a b hab).mpr ⟨ha,hb⟩)
      have hrev := Set.ncard_lt_ncard hs
        (cluster_finite_of_finite_edges G (hω.subset Set.sdiff_subset) x)
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hrev) hlt).elim
    · exact hout
  · intro hout
    exact Set.ncard_lt_ncard (pivotal_rootSide_ssubset G ω m x he (hexterior hout) hout)
      (cluster_finite_of_finite_edges G (hω.subset Set.sdiff_subset) x)

end PivotalGeometry

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

section OrderedPivotalMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem sum_choose_rank_suffix {I : Type*} (P : Finset I) (rank : I → ℕ)
    (hinj : Set.InjOn rank (P : Set I)) (i : ℕ) :
    (∑ e ∈ P, ((P.filter fun f => rank e < rank f).card).choose i) =
      P.card.choose (i+1) := by
  induction P using Finset.strongInductionOn with
  | _ P ih =>
    rcases P.eq_empty_or_nonempty with rfl | hP
    · simp
    obtain ⟨e,he,hmin⟩ := Finset.exists_min_image P rank hP
    have hT : P.erase e ⊂ P := Finset.erase_ssubset he
    have hinjT : Set.InjOn rank (↑(P.erase e) : Set I) := fun a ha b hb =>
      hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb)
    have hroot : P.filter (fun f => rank e < rank f) = P.erase e := by
      ext f
      simp only [Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨hf,hlt⟩
        exact ⟨fun h => (Nat.ne_of_lt hlt) (congrArg rank h.symm),hf⟩
      · rintro ⟨hne,hf⟩
        exact ⟨hf,lt_of_le_of_ne (hmin f hf) (fun h => hne (hinj he hf h).symm)⟩
    have hrest (f : I) (hf : f ∈ P.erase e) :
        P.filter (fun g => rank f < rank g) = (P.erase e).filter (fun g => rank f < rank g) := by
      ext g
      simp only [Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨hg,hfg⟩
        refine ⟨⟨?_,hg⟩,hfg⟩
        intro h; subst g
        exact (not_lt_of_ge (hmin f (Finset.mem_of_mem_erase hf))) hfg
      · exact fun h => ⟨h.1.2,h.2⟩
    calc
      _ = (∑ f ∈ P.erase e, ((P.filter fun g => rank f < rank g).card).choose i) +
          ((P.filter fun f => rank e < rank f).card).choose i :=
        (Finset.sum_erase_add _ _ he).symm
      _ = (∑ f ∈ P.erase e, (((P.erase e).filter fun g => rank f < rank g).card).choose i) +
          (P.erase e).card.choose i := by
        rw [hroot]
        congr 1
        exact Finset.sum_congr rfl fun f hf => congrArg (fun s : Finset I => s.card.choose i) (hrest f hf)
      _ = (P.erase e).card.choose (i+1)+(P.erase e).card.choose i := by rw [ih _ hT hinjT]
      _ = P.card.choose (i+1) := by
        have hc : (P.erase e).card+1=P.card := by
          rw [Finset.card_erase_of_mem he]
          have hp := Finset.card_pos.mpr hP
          omega
        rw [← hc,Nat.choose_succ_succ]
        simp [Nat.succ_eq_add_one,Nat.add_comm]

end OrderedPivotalMoments

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

 
theorem markedEvent_internal_marks (G : BondGraph V E) (ω : Set E) (m W : Set V)
    (x : V) (hx : x ∈ W) (hω : ω ⊆ internalEdges G W) :
    MarkedEvent G ω m x ↔ MarkedEvent G ω (m ∩ W) x := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,⟨hy,conn_internal_endpoint G W hx (conn_mono G
      (ω₁ := ω) (ω₂ := ω ∩ internalEdges G W) (fun _ h => ⟨h,hω h⟩) hxy)⟩,hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,hy.1,hxy⟩

theorem openMarkedPivotal_internal_marks (G : BondGraph V E) (ω : Set E)
    (m W : Set V) (x : V) (hx : x ∈ W) (hω : ω ⊆ internalEdges G W) (e : E) :
    OpenMarkedPivotal G ω m x e ↔ OpenMarkedPivotal G ω (m ∩ W) x e := by
  simp only [OpenMarkedPivotal,markedEvent_internal_marks G ω m W x hx hω,
    markedEvent_internal_marks G (ω \ {e}) m W x hx (Set.Subset.trans Set.sdiff_subset hω)]

 
theorem openMarkedPivotal_insert_cut (G : BondGraph V E) (ω : Set E) (m W : Set V)
    (x : V) {e : E} {a b : V} (hW : cluster G ω x = W)
    (hab : G e = s(a,b)) (ha : a ∈ W) (hb : b ∉ W) :
    OpenMarkedPivotal G (insert e ω) m x e ↔
      Disjoint W m ∧ MarkedEvent G (ω ∩ internalEdges G Wᶜ) (m ∩ Wᶜ) b := by
  have he : e ∉ ω := fun he => hb (hW ▸ ((edge_cluster_sides G ω x he hab).mp (hW ▸ ha)))
  have hdel : insert e ω \ {e} = ω := by ext f; simp [he]
  have hxa : Conn G ω x a := by change a ∈ cluster G ω x; rwa [hW]
  constructor
  · intro hp
    have hdis := pivotal_rootSide_disjoint_marks G (insert e ω) m x hp
    rw [hdel,hW] at hdis
    refine ⟨hdis,?_⟩
    obtain ⟨y,hy,hxy⟩ := hp.2.1
    rw [conn_insert_iff G ω e a b x y hab] at hxy
    rcases hxy with hxy | ⟨_,hby⟩ | ⟨hxb,_⟩
    · exact (Set.disjoint_left.mp hdis (hW ▸ hxy) hy).elim
    · have hby' := conn_restrict_cluster_compl G ω x (a := b) (hW ▸ hb) hby
      rw [hW] at hby'
      exact (markedEvent_internal_marks G _ m Wᶜ b hb Set.inter_subset_right).mp ⟨y,hy,hby'⟩
    · exact (hb (hW ▸ hxb)).elim
  · rintro ⟨hdis,y,hy,hby⟩
    refine ⟨Set.mem_insert _ _,?_,?_⟩
    · exact ⟨y,hy.1,(conn_mono G (Set.subset_insert e ω) hxa).tail
        ⟨e,Set.mem_insert _ _,hab⟩ |>.trans (conn_mono G
          (fun _ h => Set.mem_insert_of_mem _ h.1) hby)⟩
    · rw [hdel]
      rintro ⟨z,hz,hxz⟩
      exact Set.disjoint_left.mp hdis (hW ▸ hxz) hz


theorem markedMomentValue_succ (G : BondGraph V E) (Q : Finset E) (x : V)
    (i : ℕ) (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x (i+1) ω m =
      ∑ e ∈ markedOpenPivotals G Q x ω m,
        (((markedOpenPivotals G Q x ω m).filter
          (fun f => f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ)).card.choose i : ℝ) := by
  have hinj : Set.InjOn (pivotalRank G ω x) (↑(markedOpenPivotals G Q x ω m) : Set E) := by
    intro e he f hf
    exact pivotalRank_injective G ω.finite_toSet m x
      ((mem_markedOpenPivotals G Q x ω m e).mp he).2
      ((mem_markedOpenPivotals G Q x ω m f).mp hf).2
  have hs := sum_choose_rank_suffix (markedOpenPivotals G Q x ω m) (pivotalRank G ω x) hinj i
  have heq (e : E) (he : e ∈ markedOpenPivotals G Q x ω m) :
      (markedOpenPivotals G Q x ω m).filter (fun f => f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ) =
      (markedOpenPivotals G Q x ω m).filter (fun f => pivotalRank G ω x e < pivotalRank G ω x f) := by
    apply Finset.filter_congr
    intro f hf
    exact (pivotalRank_lt_iff G ω.finite_toSet m x
      ((mem_markedOpenPivotals G Q x ω m e).mp he).2
      ((mem_markedOpenPivotals G Q x ω m f).mp hf).2).symm
  by_cases h : MarkedEvent G ω m x
  · simp only [markedMomentValue,h,if_true]
    rw [← hs,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [heq e he]
  · have hempty : markedOpenPivotals G Q x ω m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact h ((mem_markedOpenPivotals G Q x ω m e).mp he).2.2.1
    simp [markedMomentValue,h,hempty]

 
theorem conn_mem_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    {ω : Set E} (hω : ω ⊆ Q) {y : V} (hxy : Conn G ω x y) :
    y ∈ insert x (searchVertices G Q) := by
  induction hxy with
  | refl => exact Finset.mem_insert_self _ _
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact Finset.mem_insert_of_mem (mem_searchVertices G (hω he) (by simp [heq]))

theorem markedEvent_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    {ω : Set E} (hω : ω ⊆ Q) (m : Set V) :
    MarkedEvent G ω m x ↔ MarkedEvent G ω (m ∩ ↑(insert x (searchVertices G Q))) x := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,⟨hy,conn_mem_searchSupport G Q x hω hxy⟩,hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,hy.1,hxy⟩

theorem markedOpenPivotals_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (hω : ω ⊆ Q) (m : Finset V) :
    markedOpenPivotals G Q x ω m =
      markedOpenPivotals G Q x ω (m ∩ insert x (searchVertices G Q)) := by
  ext e
  simp only [mem_markedOpenPivotals,OpenMarkedPivotal,Finset.coe_inter]
  rw [markedEvent_searchSupport G Q x (by exact_mod_cast hω),
    markedEvent_searchSupport G Q x (ω := (ω : Set E) \ {e})
      (fun _ h => hω h.1)]

theorem markedMomentValue_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    (i : ℕ) (ω : Finset E) (hω : ω ⊆ Q) (m : Finset V) :
    markedMomentValue G Q x i ω m =
      markedMomentValue G Q x i ω (m ∩ insert x (searchVertices G Q)) := by
  unfold markedMomentValue
  rw [markedOpenPivotals_searchSupport G Q x ω hω m]
  simp only [Finset.coe_inter]
  rw [markedEvent_searchSupport G Q x (by exact_mod_cast hω)]

theorem finiteMarkedMoment_support (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : ℝ) (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteMarkedMoment G Q F x i h p =
      finiteMarkedMoment G Q (insert x (searchVertices G Q)) x i h p := by
  apply bernoulliPolynomial_congr
  intro ω hω
  rw [← bernoulliPolynomial_restrict _ F hF]
  apply bernoulliPolynomial_congr
  intro m _
  exact markedMomentValue_searchSupport G Q x i ω hω m

 
theorem finiteMarkedMoment_first_bound (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteMarkedMoment G Q F x 1 h p ≤
      (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)*
        finiteMarkedMoment G Q F x 0 h p := by
  rw [finiteMarkedMoment_support G Q F x 1 h p hF,
    finiteMarkedMoment_support G Q F x 0 h p hF]
  simpa only [finiteMarkedMoment,markedMomentValue_one,markedMomentValue_zero,MarkedEvent,
    markedPivotalMomentOne,markedConnectionPolynomial,bernoulliPolynomial,Finset.mem_coe] using
    marked_pivotal_first_moment G Q x p h hp hh d hd hdeg


theorem markedOpenPivotals_exterior [Nonempty V] (G : BondGraph V E) (Q : Finset E)
    (x : V) (ω : Finset E) (m : Finset V) {e : E}
    (he : OpenMarkedPivotal G ω m x e) :
    markedOpenPivotals G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e)
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x)) =
      (markedOpenPivotals G Q x ω m).filter
        (fun f => f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ) := by
  obtain ⟨a,b,hab,hxa,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
  have hb := (cut_unique G (cluster G (↑ω \ {e}) x) hab hxa hxb).2
  rw [← hb]
  ext f
  simp only [mem_markedOpenPivotals,exteriorBonds,Finset.mem_filter,coe_exteriorMarks,
    Finset.coe_filter]
  have hmarks := openMarkedPivotal_internal_marks G
    ((ω : Set E) ∩ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ)
    m (cluster G (↑ω \ {e}) x)ᶜ b hxb Set.inter_subset_right f
  have hiff := openMarkedPivotal_exterior_iff G ω m x he hab hxa hxb hbm f
  change (f ∈ Q ∧ f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ) ∧
    OpenMarkedPivotal G ((ω : Set E) ∩ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ)
      ((m : Set V) ∩ (cluster G (↑ω \ {e}) x)ᶜ) b f ↔ _
  rw [← hmarks,hiff]
  tauto

 
theorem markedMomentValue_exterior [Nonempty V] (G : BondGraph V E) (Q : Finset E)
    (x : V) (i : ℕ) (ω : Finset E) (m : Finset V) {e : E}
    (he : OpenMarkedPivotal G ω m x e) :
    markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) i
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x)) =
      (((markedOpenPivotals G Q x ω m).filter
        (fun f => f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ)).card.choose i : ℝ) := by
  have hsuccess : MarkedEvent G (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) := by
    obtain ⟨a,b,hab,hxa,hxb,y,hy,hby⟩ := openMarkedPivotal_oriented G ω m x he
    rw [← (cut_unique G (cluster G (↑ω \ {e}) x) hab hxa hxb).2,
      coe_exteriorBonds,coe_exteriorMarks]
    apply (markedEvent_internal_marks G _ m (cluster G (↑ω \ {e}) x)ᶜ b hxb
      Set.inter_subset_right).mp
    refine ⟨y,hy,conn_mono G ?_ (conn_restrict_cluster_compl G (↑ω \ {e}) x hxb hby)⟩
    exact fun _ h => ⟨h.1.1,h.2⟩
  rw [markedMomentValue,ite_eq_left hsuccess,markedOpenPivotals_exterior G Q x ω m he]

 
theorem markedMomentValue_succ_exterior [Nonempty V] (G : BondGraph V E) (Q : Finset E)
    (x : V) (i : ℕ) (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x (i+1) ω m = ∑ e ∈ Q,
      if OpenMarkedPivotal G ω m x e then
        markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
          (cutOutside G (cluster G (↑ω \ {e}) x) e) i
          (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
          (exteriorMarks m (cluster G (↑ω \ {e}) x)) else 0 := by
  rw [markedMomentValue_succ]
  trans ∑ e ∈ markedOpenPivotals G Q x ω m,
    markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) i
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x))
  · apply Finset.sum_congr rfl
    intro e he
    exact (markedMomentValue_exterior G Q x i ω m
      ((mem_markedOpenPivotals G Q x ω m e).mp he).2).symm
  · have heq : markedOpenPivotals G Q x ω m = Q.filter (fun e => OpenMarkedPivotal G ω m x e) := by
      ext e; simp only [mem_markedOpenPivotals,Finset.mem_filter]
    rw [heq,Finset.sum_filter]

end MarkedRecursion

section CutFactor
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

omit [Nonempty V] in
theorem cut_not_exterior (G : BondGraph V E) (W : Set V) {e : E}
    (hc : CutExists G W e) : e ∉ internalEdges G Wᶜ := by
  obtain ⟨a,b,hab,ha,hb⟩ := hc
  intro he
  exact ((mem_internalEdges_of_ends G Wᶜ e a b hab).mp he).1 ha

omit [Nonempty V] in
theorem exteriorBonds_subset_erase (G : BondGraph V E) (Q : Finset E)
    (W : Set V) {e : E} (hc : CutExists G W e) : exteriorBonds G Q W ⊆ Q.erase e := by
  intro f hf
  obtain ⟨hf,hout⟩ := Finset.mem_filter.mp hf
  exact Finset.mem_erase.mpr ⟨fun h => cut_not_exterior G W hc (h ▸ hout),hf⟩

 
theorem cutMomentValue_blocks (G : BondGraph V E) (Q : Finset E) (F W : Finset V)
    (x : V) (e : E) (i : ℕ) (a b : Finset E) (u v : Finset V)
    (ha : a ⊆ (Q.erase e) \ exteriorBonds G Q W)
    (hb : b ⊆ exteriorBonds G Q W) (hu : u ⊆ W) (hv : v ⊆ F \ W) :
    cutMomentValue G Q x e W i (a ∪ b) (u ∪ v) =
      (if cluster G a x = (W : Set V) then (1:ℝ) else 0) *
      (if u = ∅ then (1:ℝ) else 0) *
      markedMomentValue G (exteriorBonds G Q W) (cutOutside G W e) i b v := by
  have hbout : (b : Set E) ⊆ internalEdges G (W : Set V)ᶜ :=
    fun f hf => (Finset.mem_filter.mp (hb hf)).2
  have hc := cluster_union_external_eq_iff G (a : Set E) b x W hbout
  have he : exteriorBonds G (a ∪ b) W = b := by
    ext f
    simp only [exteriorBonds,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨hf,hout⟩
      rcases hf with hf | hf
      · have hfa := Finset.mem_sdiff.mp (ha hf)
        exact (hfa.2 (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hfa.1,hout⟩)).elim
      · exact hf
    · exact fun hf => ⟨Or.inr hf,hbout hf⟩
  have hm : exteriorMarks (u ∪ v) W = v := by
    ext y
    simp only [exteriorMarks,Finset.mem_filter,Finset.mem_union,Finset.mem_coe]
    constructor
    · rintro ⟨hy,hyW⟩
      rcases hy with hy | hy
      · exact (hyW (hu hy)).elim
      · exact hy
    · intro hy
      exact ⟨Or.inr hy,(Finset.mem_sdiff.mp (hv hy)).2⟩
  have hd : Disjoint (W : Set V) ((u ∪ v : Finset V) : Set V) ↔ u = ∅ := by
    constructor
    · intro h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact Set.disjoint_left.mp h (hu hy) (Finset.mem_union_left v hy)
    · rintro rfl
      apply Set.disjoint_left.mpr
      intro y hy hyv
      have hyv' : y ∈ v := by simpa using hyv
      exact (Finset.mem_sdiff.mp (hv hyv')).2 hy
  rw [Finset.coe_union] at hd
  simp only [cutMomentValue,Finset.coe_union,hc,hd,he,hm]
  split_ifs <;> simp_all

omit [Nonempty V] in
 
theorem bernoulliPolynomial_empty_indicator (F : Finset V) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m = ∅ then (1:ℝ) else 0) h = (1-h)^F.card := by
  unfold bernoulliPolynomial
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro m hm hne
    simp [hne]
  · simp

 
theorem cutMoment_factor (G : BondGraph V E) (Q : Finset E) (F W : Finset V)
    (x : V) (e : E) (i : ℕ) (h p : ℝ) (hW : W ⊆ F) (hc : CutExists G W e) :
    bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
      (cutMomentValue G Q x e W i ω) h) p =
      bernoulliPolynomial ((Q.erase e) \ exteriorBonds G Q W)
        (fun a => if cluster G a x = (W : Set V) then (1:ℝ) else 0) p *
      (1-h)^W.card * finiteMarkedMoment G (exteriorBonds G Q W) (F \ W)
        (cutOutside G W e) i h p := by
  let R := exteriorBonds G Q W
  let A := (Q.erase e) \ R
  let B := F \ W
  have hR : R ⊆ Q.erase e := exteriorBonds_subset_erase G Q W hc
  have hQR : Q.erase e = A ∪ R := by
    dsimp [A]; ext f; simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hAR : Disjoint A R := Finset.disjoint_sdiff.symm
  have hFB : F = W ∪ B := (Finset.union_sdiff_of_subset hW).symm
  have hWB : Disjoint W B := Finset.disjoint_sdiff
  conv_lhs => rw [hQR,bernoulliPolynomial_union A R hAR]
  trans bernoulliPolynomial A (fun a =>
    (if cluster G a x = (W : Set V) then (1:ℝ) else 0) *
      ((1-h)^W.card * finiteMarkedMoment G R B (cutOutside G W e) i h p)) p
  · apply bernoulliPolynomial_congr
    intro a ha
    trans bernoulliPolynomial R (fun b =>
      (if cluster G a x = (W : Set V) then (1:ℝ) else 0) * (1-h)^W.card *
        bernoulliPolynomial B (markedMomentValue G R (cutOutside G W e) i b) h) p
    · apply bernoulliPolynomial_congr
      intro b hb
      rw [hFB,bernoulliPolynomial_union W B hWB]
      trans bernoulliPolynomial W (fun u =>
        (if cluster G a x = (W : Set V) then (1:ℝ) else 0) *
        (if u = ∅ then (1:ℝ) else 0) *
        bernoulliPolynomial B (markedMomentValue G R (cutOutside G W e) i b) h) h
      · apply bernoulliPolynomial_congr
        intro u hu
        rw [← bernoulliPolynomial_const_mul]
        apply bernoulliPolynomial_congr
        intro v hv
        exact cutMomentValue_blocks G Q F W x e i a b u v ha hb hu hv
      · rw [bernoulliPolynomial_mul_const,bernoulliPolynomial_const_mul,
          bernoulliPolynomial_empty_indicator]
    · rw [bernoulliPolynomial_const_mul]
      exact mul_assoc _ _ _
  · rw [bernoulliPolynomial_mul_const]
    exact (mul_assoc _ _ _).symm

end CutFactor

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]


theorem pivotalSuffixValue_insert (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (i : ℕ) (ω : Finset E) (he : e ∉ ω) (m : Finset V) :
    pivotalSuffixValue G Q x e i (insert e ω) m =
      if CutExists G (cluster G ω x) e then
        if Disjoint (cluster G ω x) (m : Set V) then
          markedMomentValue G (exteriorBonds G Q (cluster G ω x))
            (cutOutside G (cluster G ω x) e) i
            (exteriorBonds G ω (cluster G ω x)) (exteriorMarks m (cluster G ω x))
        else 0
      else 0 := by
  have hdel : ((insert e ω : Finset E) : Set E) \ {e} = (ω : Set E) := by
    simp [he]
  by_cases hc : CutExists G (cluster G ω x) e
  · obtain ⟨hab,ha,hb⟩ := cut_spec G (cluster G ω x) hc
    have heout := cut_not_exterior G (cluster G ω x) hc
    have hbe : exteriorBonds G (insert e ω) (cluster G ω x) = exteriorBonds G ω (cluster G ω x) := by
      ext f
      simp only [exteriorBonds,Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hf,hout⟩
        rcases hf with rfl | hf
        · exact (heout hout).elim
        · exact ⟨hf,hout⟩
      · exact fun h => ⟨Or.inr h.1,h.2⟩
    have hp := openMarkedPivotal_insert_cut G (ω : Set E) m (cluster G ω x) x rfl hab ha hb
    have hps : OpenMarkedPivotal G (insert e ω : Finset E) m x e ↔
        Disjoint (cluster G ω x) (m : Set V) ∧
        MarkedEvent G (exteriorBonds G ω (cluster G ω x))
          (exteriorMarks m (cluster G ω x)) (cutOutside G (cluster G ω x) e) := by
      simpa only [Finset.coe_insert,coe_exteriorBonds,coe_exteriorMarks] using hp
    simp only [pivotalSuffixValue,hdel,hbe,hc,if_true,hps]
    by_cases hd : Disjoint (cluster G ω x) (m : Set V) <;>
      by_cases hm : MarkedEvent G (exteriorBonds G ω (cluster G ω x))
        (exteriorMarks m (cluster G ω x)) (cutOutside G (cluster G ω x) e) <;>
      simp only [markedMomentValue,hd,hm,and_true,and_false,if_true,if_false]
  · have hn : ¬OpenMarkedPivotal G (insert e ω : Finset E) m x e := by
      intro hp
      obtain ⟨a,b,hab,hxa,hxb,_⟩ := openMarkedPivotal_oriented G (insert e ω : Finset E) m x hp
      rw [hdel] at hxa hxb
      exact hc ⟨a,b,hab,hxa,hxb⟩
    simp only [pivotalSuffixValue,hn,hc,if_false]

omit [Nonempty V] in
theorem finiteRootComponent_subset (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (ω : Finset E) (hω : ω ⊆ Q) (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteRootComponent G ω x ⊆ F := by
  intro y hy
  have hxy : Conn G (ω : Set E) x y := by
    change y ∈ (finiteRootComponent G ω x : Set V) at hy
    rwa [coe_finiteRootComponent] at hy
  exact hF (conn_mem_searchSupport G Q x (by exact_mod_cast hω) hxy)

omit [Nonempty V] in
 
theorem sum_component_partition (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (ω : Finset E) (hω : ω ⊆ Q) (hF : insert x (searchVertices G Q) ⊆ F)
    (f : Finset V → ℝ) :
    (∑ W ∈ F.powerset, if cluster G ω x = (W : Set V) then f W else 0) =
      f (finiteRootComponent G ω x) := by
  have hmem : finiteRootComponent G ω x ∈ F.powerset :=
    Finset.mem_powerset.mpr (finiteRootComponent_subset G Q F x ω hω hF)
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · simp
  · intro W hW hne
    have hn : cluster G ω x ≠ (W : Set V) := by
      intro h
      apply hne
      apply Finset.coe_injective
      exact h.symm.trans (coe_finiteRootComponent G ω x).symm
    simp [hn]

 
theorem pivotalSuffixValue_component_sum (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (e : E) (i : ℕ) (ω : Finset E) (he : e ∉ ω) (hω : ω ⊆ Q)
    (hF : insert x (searchVertices G Q) ⊆ F) (m : Finset V) :
    pivotalSuffixValue G Q x e i (insert e ω) m = ∑ W ∈ F.powerset,
      if CutExists G W e then cutMomentValue G Q x e W i ω m else 0 := by
  rw [pivotalSuffixValue_insert G Q x e i ω he m]
  symm
  trans ∑ W ∈ F.powerset, if cluster G ω x = (W : Set V) then
    (if CutExists G W e then
      if Disjoint (W : Set V) (m : Set V) then
        markedMomentValue G (exteriorBonds G Q W) (cutOutside G W e) i
          (exteriorBonds G ω W) (exteriorMarks m W) else 0
      else 0) else 0
  · apply Finset.sum_congr rfl
    intro W _
    by_cases hc : CutExists G W e <;> by_cases hw : cluster G ω x = (W : Set V) <;>
      simp [cutMomentValue,hc,hw]
  · rw [sum_component_partition G Q F x ω hω hF]
    simp only [coe_finiteRootComponent]

omit [Nonempty V] in
 
theorem bernoulliPolynomial_open_gate (Q : Finset E) (e : E) (he : e ∈ Q)
    (f : Finset E → ℝ) (p : ℝ) (hf : ∀ ω ⊆ Q, e ∉ ω → f ω = 0) :
    bernoulliPolynomial Q f p =
      p*bernoulliPolynomial (Q.erase e) (fun ω => f (insert e ω)) p := by
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
  have hz : bernoulliPolynomial (Q.erase e) f p = 0 := by
    rw [← bernoulliPolynomial_zero (Q.erase e) p]
    apply bernoulliPolynomial_congr
    intro ω hω
    exact hf ω (Finset.Subset.trans hω (Finset.erase_subset e Q))
      (fun h => Finset.notMem_erase e Q (hω h))
  rw [hz,mul_zero,zero_add]

end PointwiseRecursion

section FiniteMomentRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]


theorem finiteMarkedMoment_recursion (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : ℝ) (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteMarkedMoment G Q F x (i+1) h p = p * ∑ e ∈ Q, ∑ W ∈ F.powerset,
      if CutExists G W e then cutCoefficient G Q x e W h p *
        finiteMarkedMoment G (exteriorBonds G Q W) (F \ W) (cutOutside G W e) i h p else 0 := by
  have hsum : finiteMarkedMoment G Q F x (i+1) h p =
      ∑ e ∈ Q, bernoulliPolynomial Q (fun ω => bernoulliPolynomial F
        (pivotalSuffixValue G Q x e i ω) h) p := by
    change bernoulliPolynomial Q (fun ω => bernoulliPolynomial F
      (fun m => markedMomentValue G Q x (i+1) ω m) h) p = _
    simp only [markedMomentValue_succ_exterior,bernoulliPolynomial_sum]
    rfl
  rw [hsum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [bernoulliPolynomial_open_gate Q e he]
  · congr 1
    trans bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
      (fun m => ∑ W ∈ F.powerset, if CutExists G W e then cutMomentValue G Q x e W i ω m else 0) h) p
    · apply bernoulliPolynomial_congr
      intro ω hω
      apply bernoulliPolynomial_congr
      intro m _
      exact pivotalSuffixValue_component_sum G Q F x e i ω
        (fun h => Finset.notMem_erase e Q (hω h))
        (Finset.Subset.trans hω (Finset.erase_subset e Q)) hF m
    · simp only [bernoulliPolynomial_sum]
      apply Finset.sum_congr rfl
      intro W hW
      by_cases hc : CutExists G W e
      · simp only [hc,if_true]
        exact cutMoment_factor G Q F W x e i h p (Finset.mem_powerset.mp hW) hc
      · simp only [hc,if_false,bernoulliPolynomial_zero]
  · intro ω hω heω
    rw [← bernoulliPolynomial_zero F h]
    apply bernoulliPolynomial_congr
    intro m _
    have hpiv : ¬OpenMarkedPivotal G ω m x e := fun h => heω h.1
    simp only [pivotalSuffixValue,hpiv,if_false]

omit [Nonempty V] in
theorem cutCoefficient_nonneg (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (W : Finset V) (h p : unitInterval) : 0 ≤ cutCoefficient G Q x e W h p := by
  apply mul_nonneg
  · exact bernoulliPolynomial_nonneg _ _ _ p.2 (fun _ _ => by split_ifs <;> norm_num)
  · exact pow_nonneg (sub_nonneg.mpr h.2.2) _

omit [Nonempty V] in
theorem finiteMarkedMoment_nonneg (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : unitInterval) : 0 ≤ finiteMarkedMoment G Q F x i h p := by
  apply bernoulliPolynomial_nonneg _ _ _ p.2
  intro ω _
  apply bernoulliPolynomial_nonneg _ _ _ h.2
  intro m _
  unfold markedMomentValue
  split_ifs <;> positivity

 
theorem exterior_mark_support (G : BondGraph V E) (Q : Finset E) (F W : Finset V)
    (x : V) (e : E) (he : e ∈ Q) (hc : CutExists G W e)
    (hF : insert x (searchVertices G Q) ⊆ F) :
    insert (cutOutside G W e) (searchVertices G (exteriorBonds G Q W)) ⊆ F \ W := by
  have hs := cut_spec G W hc
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact Finset.mem_sdiff.mpr ⟨hF (Finset.mem_insert_of_mem
      (mem_searchVertices G he (by simp [hs.1]))),hs.2.2⟩
  · obtain ⟨f,hf,hyf⟩ := Finset.mem_biUnion.mp hy
    have hfQ := (Finset.mem_filter.mp hf).1
    have hfo := (Finset.mem_filter.mp hf).2
    have hyf' := Sym2.mem_toFinset.mp hyf
    exact Finset.mem_sdiff.mpr ⟨hF (Finset.mem_insert_of_mem
      (mem_searchVertices G hfQ hyf')),hfo y hyf'⟩

omit [Nonempty V] in
 
theorem exterior_degree_bound (G : BondGraph V E) (Q : Finset E) (W : Set V)
    (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    ∀ v, ((exteriorBonds G Q W).filter (fun e => v ∈ G e)).card ≤ d := by
  intro v
  apply le_trans (Finset.card_le_card ?_) (hd v)
  intro e he
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
    (Finset.mem_filter.mp he).2⟩

 
theorem finiteMarkedMoment_geometric (G : BondGraph V E) (p h : unitInterval)
    (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d) (i : ℕ)
    (Q : Finset E) (F : Finset V) (x : V)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteMarkedMoment G Q F x i h p ≤
      ((Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h))^i *
        finiteMarkedMoment G Q F x 0 h p := by
  let A : ℝ := (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)
  have hA : 0 ≤ A := mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr p.2.2))
    (Real.sqrt_nonneg _)
  change _ ≤ A^i * _
  induction i generalizing Q F x with
  | zero => simp
  | succ i ih =>
    have hpow := pow_nonneg hA i
    calc
      finiteMarkedMoment G Q F x (i+1) h p =
          (p:ℝ) * ∑ e ∈ Q, ∑ W ∈ F.powerset,
            if CutExists G W e then cutCoefficient G Q x e W h p *
              finiteMarkedMoment G (exteriorBonds G Q W) (F \ W) (cutOutside G W e) i h p else 0 :=
        finiteMarkedMoment_recursion G Q F x i h p hF
      _ ≤ (p:ℝ) * ∑ e ∈ Q, ∑ W ∈ F.powerset,
            if CutExists G W e then cutCoefficient G Q x e W h p *
              (A^i * finiteMarkedMoment G (exteriorBonds G Q W) (F \ W) (cutOutside G W e) 0 h p)
              else 0 := by
        apply mul_le_mul_of_nonneg_left _ p.2.1
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro W hW
        by_cases hc : CutExists G W e
        · simp only [hc,if_true]
          apply mul_le_mul_of_nonneg_left _ (cutCoefficient_nonneg G Q x e W h p)
          exact ih _ _ _ (exterior_degree_bound G Q W d hdeg) (exterior_mark_support G Q F W x e he hc hF)
        · simp only [hc,if_false,le_refl]
      _ = A^i * finiteMarkedMoment G Q F x 1 h p := by
        rw [show (1:ℕ) = 0+1 from rfl,finiteMarkedMoment_recursion G Q F x 0 h p hF]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro W hW
        by_cases hc : CutExists G W e <;> simp only [hc,if_true,if_false] <;> ring
      _ ≤ A^i * (A * finiteMarkedMoment G Q F x 0 h p) :=
        mul_le_mul_of_nonneg_left (finiteMarkedMoment_first_bound G Q F x p h hp hh d hd hdeg hF) hpow
      _ = A^(i+1) * finiteMarkedMoment G Q F x 0 h p := by rw [pow_succ]; ring

end FiniteMomentRecursion

section MarkedExponential
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem choose_generating_sum (n N : ℕ) (hn : n ≤ N) (z : ℝ) :
    (1+z)^n = ∑ i ∈ Finset.range (N+1), z^i*(n.choose i : ℝ) := by
  rw [add_comm (1:ℝ),add_pow]
  simp only [one_pow,mul_one]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
  intro i hi hin
  have hni : n < i := by simp only [Finset.mem_range,not_lt] at hin; omega
  simp [Nat.choose_eq_zero_of_lt hni]

 
theorem markedMomentValue_generating (G : BondGraph V E) (Q : Finset E) (x : V)
    (z : ℝ) (ω : Finset E) (m : Finset V) :
    (if MarkedEvent G ω m x then (1+z)^(markedOpenPivotals G Q x ω m).card else 0) =
      ∑ i ∈ Finset.range (Q.card+1), z^i*markedMomentValue G Q x i ω m := by
  by_cases hm : MarkedEvent G ω m x
  · simp only [markedMomentValue,hm,if_true]
    exact choose_generating_sum _ _ (Finset.card_filter_le ..) z
  · simp only [markedMomentValue,hm,if_false,mul_zero,Finset.sum_const_zero]

theorem finiteMarkedTail_nonneg (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (r : ℕ) (h p : unitInterval) : 0 ≤ finiteMarkedTail G Q F x r h p := by
  apply bernoulliPolynomial_nonneg _ _ _ p.2
  intro ω _
  apply bernoulliPolynomial_nonneg _ _ _ h.2
  intro m _
  split_ifs <;> norm_num

theorem finiteMarkedGenerating_eq (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (z h p : ℝ) :
    finiteMarkedGenerating G Q F x z h p =
      ∑ i ∈ Finset.range (Q.card+1), z^i*finiteMarkedMoment G Q F x i h p := by
  simp only [finiteMarkedGenerating,markedMomentValue_generating,bernoulliPolynomial_sum,
    bernoulliPolynomial_const_mul]
  rfl

theorem half_geometric_sum_le (N : ℕ) :
    (∑ i ∈ Finset.range N, (1/2:ℝ)^i) ≤ 2 := by
  have heq : (∑ i ∈ Finset.range N, (1/2:ℝ)^i) = 2*(1-(1/2:ℝ)^N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [heq]
  have := pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) N
  linarith

 
theorem finiteMarkedGenerating_le [Nonempty V] (G : BondGraph V E) (p h : unitInterval)
    (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d)
    (Q : Finset E) (F : Finset V) (x : V)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (hF : insert x (searchVertices G Q) ⊆ F) (B : ℝ) (hB : 0 < B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B) :
    finiteMarkedGenerating G Q F x (1/(2*B)) h p ≤ 2*finiteMarkedMoment G Q F x 0 h p := by
  let A : ℝ := (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)
  have hA : 0 ≤ A := mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr p.2.2))
    (Real.sqrt_nonneg _)
  have hb0 := finiteMarkedMoment_nonneg G Q F x 0 h p
  rw [finiteMarkedGenerating_eq]
  calc
    _ ≤ ∑ i ∈ Finset.range (Q.card+1), (1/(2*B))^i*(B^i*finiteMarkedMoment G Q F x 0 h p) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) i)
      apply (finiteMarkedMoment_geometric G p h hp hh d hd i Q F x hdeg hF).trans
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAB i) hb0
    _ = (∑ i ∈ Finset.range (Q.card+1), (1/2:ℝ)^i)*finiteMarkedMoment G Q F x 0 h p := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc,← mul_pow]
      congr 2
      field_simp
    _ ≤ 2*finiteMarkedMoment G Q F x 0 h p := mul_le_mul_of_nonneg_right (half_geometric_sum_le _) hb0

 
theorem finiteMarkedTail_markov (G : BondGraph V E) (p h : unitInterval) (Q : Finset E)
    (F : Finset V) (x : V) (z : ℝ) (hz : 0 ≤ z) (r : ℕ) :
    (1+z)^r * finiteMarkedTail G Q F x r h p ≤ finiteMarkedGenerating G Q F x z h p := by
  unfold finiteMarkedTail finiteMarkedGenerating
  rw [← bernoulliPolynomial_const_mul]
  apply bernoulliPolynomial_mono _ _ _ _ p.2
  intro ω hω
  rw [← bernoulliPolynomial_const_mul]
  apply bernoulliPolynomial_mono _ _ _ _ h.2
  intro m hm
  by_cases he : MarkedEvent G ω m x
  · by_cases hc : r ≤ (markedOpenPivotals G Q x ω m).card
    · simp only [he,hc,and_self,if_true,mul_one]
      exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+z) hc
    · simp only [he,hc,and_false,if_true,if_false,mul_zero]
      exact pow_nonneg (by linarith) _
  · simp only [he,false_and,if_false,mul_zero,le_refl]

 
theorem log_one_add_half_inv_ge (B : ℝ) (hB : 1 ≤ B) :
    1/(4*B) ≤ Real.log (1+1/(2*B)) := by
  have hBp : 0 < B := by linarith
  let z : ℝ := 1/(2*B)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzle : z ≤ 2 := by dsimp [z]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  calc
    1/(4*B) = z/2 := by dsimp [z]; ring
    _ ≤ 2*z/(z+2) := by
      apply (le_div_iff₀ (by linarith : 0 < z+2)).mpr
      have hs := mul_le_mul_of_nonneg_right hzle hz
      nlinarith
    _ ≤ Real.log (1+z) := Real.le_log_one_add_of_nonneg hz

 
theorem finiteMarkedTail_exponential [Nonempty V] (G : BondGraph V E) (p h : unitInterval)
    (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d)
    (Q : Finset E) (F : Finset V) (x : V)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (hF : insert x (searchVertices G Q) ⊆ F) (B : ℝ) (hB : 1 ≤ B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B) (r : ℕ) :
    finiteMarkedTail G Q F x r h p ≤
      2*Real.exp (-(r:ℝ)/(4*B))*finiteMarkedMoment G Q F x 0 h p := by
  have hBp : 0 < B := by linarith
  have hz : 0 ≤ 1/(2*B) := by positivity
  have hbase : 0 < 1+1/(2*B) := by positivity
  have hpow : Real.exp ((r:ℝ)/(4*B)) ≤ (1+1/(2*B))^r := by
    rw [← Real.exp_log (pow_pos hbase r),Real.log_pow]
    apply Real.exp_le_exp.mpr
    have hlog := mul_le_mul_of_nonneg_left (log_one_add_half_inv_ge B hB) (Nat.cast_nonneg r : (0:ℝ) ≤ r)
    simpa only [mul_one_div] using hlog
  have hm := (finiteMarkedTail_markov G p h Q F x (1/(2*B)) hz r).trans
    (finiteMarkedGenerating_le G p h hp hh d hd Q F x hdeg hF B hBp hAB)
  have ht := finiteMarkedTail_nonneg G Q F x r h p
  have he := (mul_le_mul_of_nonneg_right hpow ht).trans hm
  calc
    finiteMarkedTail G Q F x r h p ≤ (2*finiteMarkedMoment G Q F x 0 h p)/Real.exp ((r:ℝ)/(4*B)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using he)
    _ = 2*Real.exp (-(r:ℝ)/(4*B))*finiteMarkedMoment G Q F x 0 h p := by
      rw [neg_div,Real.exp_neg,div_eq_mul_inv]
      ring

end MarkedExponential

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

section FiniteCappedRadius
attribute [local instance] Classical.propDecidable Classical.decEq


theorem sole_root_mark (G : BondGraph V E) (Q : Finset E) (x y : V) (ω : Finset E)
    (m : Finset V) (hxy : Conn G (ω : Set E) x y)
    (hm : m ∩ finiteRootComponent G ω x = {y}) :
    MarkedEvent G ω m x ∧ markedOpenPivotals G Q x ω m = pairOpenPivotals G Q x y ω := by
  have hyW : y ∈ finiteRootComponent G ω x := by
    change y ∈ (finiteRootComponent G ω x : Set V)
    rwa [coe_finiteRootComponent]
  have hym : y ∈ m := (Finset.mem_inter.mp (hm ▸ Finset.mem_singleton_self y)).1
  have hmconn (η : Finset E) (hη : η ⊆ ω) :
      MarkedEvent G η m x ↔ Conn G (η : Set E) x y := by
    constructor
    · rintro ⟨z,hzm,hxz⟩
      have hzW : z ∈ finiteRootComponent G ω x := by
        change z ∈ (finiteRootComponent G ω x : Set V)
        rw [coe_finiteRootComponent]
        exact conn_mono G (by exact_mod_cast hη) hxz
      have hzy : z = y := Finset.mem_singleton.mp (hm ▸ Finset.mem_inter.mpr ⟨hzm,hzW⟩)
      rwa [hzy] at hxz
    · exact fun h => ⟨y,hym,h⟩
  refine ⟨⟨y,hym,hxy⟩,?_⟩
  ext e
  simp only [markedOpenPivotals,pairOpenPivotals,Finset.mem_filter]
  change (e ∈ Q ∧ e ∈ ω ∧ MarkedEvent G ω m x ∧ ¬MarkedEvent G (ω.erase e) m x) ↔ _
  rw [hmconn ω Finset.Subset.rfl,hmconn (ω.erase e) (Finset.erase_subset e ω)]

 
theorem bernoulliPolynomial_exact_indicator (F S : Finset V) (hSF : S ⊆ F) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m = S then (1:ℝ) else 0) h =
      h^S.card*(1-h)^(F.card-S.card) := by
  unfold bernoulliPolynomial
  rw [Finset.sum_eq_single_of_mem S (Finset.mem_powerset.mpr hSF)]
  · simp
  · intro m hm hne
    simp [hne]

 
theorem bernoulliPolynomial_sole_root_mark (G : BondGraph V E) (Q : Finset E)
    (F : Finset V) (x y : V) (ω : Finset E) (hω : ω ⊆ Q)
    (hF : insert x (searchVertices G Q) ⊆ F) (hxy : Conn G (ω : Set E) x y) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m ∩ finiteRootComponent G ω x = {y} then (1:ℝ) else 0) h =
      h*(1-h)^((finiteRootComponent G ω x).card-1) := by
  rw [bernoulliPolynomial_restrict _ _ (finiteRootComponent_subset G Q F x ω hω hF)
    (fun a => if a = {y} then (1:ℝ) else 0) h]
  have hy : y ∈ finiteRootComponent G ω x := by
    change y ∈ (finiteRootComponent G ω x : Set V)
    rwa [coe_finiteRootComponent]
  rw [bernoulliPolynomial_exact_indicator _ {y} (Finset.singleton_subset_iff.mpr hy)]
  simp

 
theorem cappedRadius_mark_comparison (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (M r : ℕ) (p h : unitInterval)
    (hF : insert x (searchVertices G Q) ⊆ F) :
    (h:ℝ)*(1-h)^M*finiteCappedRadiusTail G Q x M r p ≤ finiteMarkedTail G Q F x r h p := by
  unfold finiteCappedRadiusTail finiteMarkedTail
  rw [← bernoulliPolynomial_const_mul]
  apply bernoulliPolynomial_mono _ _ _ _ p.2
  intro ω hω
  by_cases he : CappedRadiusEvent G Q x M r ω
  · obtain ⟨hcap,y,hxy,hr⟩ := he
    have he : CappedRadiusEvent G Q x M r ω := ⟨hcap,y,hxy,hr⟩
    simp only [he,if_true,mul_one]
    calc
      (h:ℝ)*(1-h)^M ≤ (h:ℝ)*(1-h)^((finiteRootComponent G ω x).card-1) := by
        apply mul_le_mul_of_nonneg_left _ h.2.1
        exact pow_le_pow_of_le_one (sub_nonneg.mpr h.2.2) (by linarith [h.2.1])
          (Nat.le_trans (Nat.sub_le _ _) hcap)
      _ = bernoulliPolynomial F
          (fun m => if m ∩ finiteRootComponent G ω x = {y} then (1:ℝ) else 0) h :=
        (bernoulliPolynomial_sole_root_mark G Q F x y ω hω hF hxy h).symm
      _ ≤ _ := by
        apply bernoulliPolynomial_mono _ _ _ _ h.2
        intro m hm
        by_cases hs : m ∩ finiteRootComponent G ω x = {y}
        · obtain ⟨heq,hpiv⟩ := sole_root_mark G Q x y ω m hxy hs
          have hlarge : r ≤ (markedOpenPivotals G Q x ω m).card := hpiv ▸ hr
          simp only [hs,heq,hlarge,and_self,if_true,le_refl]
        · simp only [hs,if_false]
          split_ifs <;> norm_num
  · simp only [he,if_false,mul_zero]
    apply bernoulliPolynomial_nonneg _ _ _ h.2
    intro m hm
    split_ifs <;> norm_num

theorem finiteMarkedMoment_zero_le_one (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (p h : unitInterval) : finiteMarkedMoment G Q F x 0 h p ≤ 1 := by
  unfold finiteMarkedMoment
  rw [← bernoulliPolynomial_const Q (1:ℝ) (p:ℝ)]
  apply bernoulliPolynomial_mono _ _ _ _ p.2
  intro ω hω
  rw [← bernoulliPolynomial_const F (1:ℝ) (h:ℝ)]
  apply bernoulliPolynomial_mono _ _ _ _ h.2
  intro m hm
  rw [markedMomentValue_zero]
  split_ifs <;> norm_num

 
theorem finiteCappedRadiusTail_exponential [Nonempty V] (G : BondGraph V E)
    (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (hh1 : (h:ℝ) < 1)
    (d : ℕ) (hd : 0 < d) (Q : Finset E) (x : V)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (B : ℝ) (hB : 1 ≤ B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B) (M r : ℕ) :
    finiteCappedRadiusTail G Q x M r p ≤
      (2/((h:ℝ)*(1-h)^M))*Real.exp (-(r:ℝ)/(4*B)) := by
  let F := insert x (searchVertices G Q)
  have hcomp := cappedRadius_mark_comparison G Q F x M r p h Finset.Subset.rfl
  have ht := finiteMarkedTail_exponential G p h hp hh d hd Q F x hdeg Finset.Subset.rfl B hB hAB r
  have hm := finiteMarkedMoment_zero_le_one G Q F x p h
  have hb : 0 < (h:ℝ)*(1-h)^M := mul_pos hh (pow_pos (sub_pos.mpr hh1) _)
  have hbound : (h:ℝ)*(1-h)^M*finiteCappedRadiusTail G Q x M r p ≤
      2*Real.exp (-(r:ℝ)/(4*B)) := by
    have hpos : 0 ≤ 2*Real.exp (-(r:ℝ)/(4*B)) := by positivity
    have hl := mul_le_mul_of_nonneg_left hm hpos
    rw [mul_one] at hl
    exact hcomp.trans (ht.trans hl)
  calc
    _ ≤ (2*Real.exp (-(r:ℝ)/(4*B)))/((h:ℝ)*(1-h)^M) :=
      (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := by ring

end FiniteCappedRadius

section PruningGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem pairOpenPivotals_symm (G : BondGraph V E) (Q : Finset E) (ω : Finset E) (x y : V) :
    pairOpenPivotals G Q x y ω = pairOpenPivotals G Q y x ω := by
  ext e
  simp only [pairOpenPivotals,Finset.mem_filter]
  have h₁ : Conn G (ω : Set E) x y ↔ Conn G (ω : Set E) y x :=
    ⟨conn_symm G _,conn_symm G _⟩
  have h₂ : Conn G (ω.erase e : Set E) x y ↔ Conn G (ω.erase e : Set E) y x :=
    ⟨conn_symm G _,conn_symm G _⟩
  rw [h₁,h₂]

 
theorem pairOpenPivotals_triangle_subset (G : BondGraph V E) (Q : Finset E) (ω : Finset E)
    (x y z : V) (hxy : Conn G (ω : Set E) x y) (hyz : Conn G (ω : Set E) y z) :
    pairOpenPivotals G Q x z ω ⊆ pairOpenPivotals G Q x y ω ∪ pairOpenPivotals G Q y z ω := by
  intro e he
  obtain ⟨heQ,heω,_,hnxz⟩ := Finset.mem_filter.mp he
  by_cases hxy' : Conn G (ω.erase e : Set E) x y
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨heQ,heω,hyz,fun hyz' => hnxz (hxy'.trans hyz')⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heQ,heω,hxy,hxy'⟩)

theorem pairOpenPivotals_triangle (G : BondGraph V E) (Q : Finset E) (ω : Finset E)
    (x y z : V) (hxy : Conn G (ω : Set E) x y) (hyz : Conn G (ω : Set E) y z) :
    (pairOpenPivotals G Q x z ω).card ≤
      (pairOpenPivotals G Q x y ω).card+(pairOpenPivotals G Q y z ω).card :=
  (Finset.card_le_card (pairOpenPivotals_triangle_subset G Q ω x y z hxy hyz)).trans
    (Finset.card_union_le _ _)

 
theorem conn_no_crossing_internal (G : BondGraph V E) (W : Set V) (ω : Set E)
    (hc : ∀ e ∈ ω, ¬CutExists G W e) {x y : V} (hx : x ∈ W) (hxy : Conn G ω x y) :
    Conn G (ω ∩ internalEdges G W) x y ∧ y ∈ W := by
  induction hxy with
  | refl => exact ⟨conn_refl _ _ _,hx⟩
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    have hb : b ∈ W := by
      by_contra hn
      exact hc e he ⟨a,b,heq,ih.2,hn⟩
    exact ⟨ih.1.tail ⟨e,⟨he,(mem_internalEdges_of_ends G W e a b heq).mpr ⟨ih.2,hb⟩⟩,heq⟩,hb⟩

 
theorem conn_one_attachment_internal (G : BondGraph V E) (W : Set V) (ω : Set E)
    (e : E) (he : e ∈ ω) (hec : CutExists G W e)
    (hone : ∀ f ∈ ω, CutExists G W f → f = e)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hxy : Conn G ω x y) :
    Conn G (ω ∩ internalEdges G W) x y := by
  obtain ⟨a,b,hab,ha,hb⟩ := hec
  let η := ω \ {e}
  have hn : ∀ f ∈ η, ¬CutExists G W f := by
    intro f hf hc
    exact hf.2 (Set.mem_singleton_iff.mpr (hone f hf.1 hc))
  have hη (u v : V) (hu : u ∈ W) (huv : Conn G η u v) :=
    conn_no_crossing_internal G W η hn hu huv
  have hω : insert e η = ω := by dsimp [η]; ext f; simp [he]
  have hw : Conn G (insert e η) x y := hω ▸ hxy
  rcases (conn_insert_iff G η e a b x y hab).mp hw with h | ⟨_,h⟩ | ⟨h,_⟩
  · exact conn_mono G (show η ∩ internalEdges G W ⊆ ω ∩ internalEdges G W from
      fun _ hf => ⟨hf.1.1,hf.2⟩) (hη x y hx h).1
  · exact (hb (hη y b hy (conn_symm G η h)).2).elim
  · exact (hb (hη x b hx h).2).elim


theorem pairOpenPivotals_one_attachment (G : BondGraph V E) (Q ω : Finset E) (W : Set V)
    (e : E) (he : e ∈ ω) (hec : CutExists G W e)
    (hone : ∀ f ∈ ω, CutExists G W f → f = e)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) :
    pairOpenPivotals G Q x y (internalBonds G ω W) ⊆ pairOpenPivotals G Q x y ω := by
  intro f hf
  obtain ⟨hfQ,hfω,hxy,hnxy⟩ := Finset.mem_filter.mp hf
  have hfint : f ∈ internalEdges G W := (Finset.mem_filter.mp hfω).2
  have hfe : e ≠ f := by
    intro hef
    obtain ⟨a,b,hab,ha,hb⟩ := hec
    have hh : e ∈ internalEdges G W := hef ▸ hfint
    exact hb ((mem_internalEdges_of_ends G W e a b hab).mp hh).2
  have he' : e ∈ ω.erase f := Finset.mem_erase.mpr ⟨hfe,he⟩
  have hcoe : (internalBonds G ω W).erase f = internalBonds G (ω.erase f) W := by
    ext g; simp [internalBonds]; tauto
  refine Finset.mem_filter.mpr ⟨hfQ,(Finset.mem_filter.mp hfω).1,?_,?_⟩
  · exact conn_mono G (by simpa only [coe_internalBonds] using Set.inter_subset_left) hxy
  · intro h
    have hh := conn_one_attachment_internal G W (ω.erase f : Set E) e he' hec
      (fun g hg hc => hone g (Finset.mem_of_mem_erase hg) hc) hx hy h
    apply hnxy
    simpa only [hcoe,coe_internalBonds] using hh

 
theorem conn_first_entry (G : BondGraph V E) (W : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ W) (hy : y ∈ W) (hxy : Conn G ω x y) :
    ∃ a b e, a ∉ W ∧ b ∈ W ∧ e ∈ ω ∧ G e = s(a,b) ∧
      Conn G (ω ∩ internalEdges G Wᶜ) x a := by
  let Entry : Prop := ∃ a b e, a ∉ W ∧ b ∈ W ∧ e ∈ ω ∧ G e = s(a,b) ∧
      Conn G (ω ∩ internalEdges G Wᶜ) x a
  have haux : Conn G (ω ∩ internalEdges G Wᶜ) x y ∨ Entry := by
    clear hy
    induction hxy with
    | refl => exact Or.inl (conn_refl _ _ _)
    | @tail a b hxa hab ih =>
      rcases ih with ih | ih
      · have ha : a ∉ W := conn_internal_endpoint G Wᶜ hx ih
        obtain ⟨e,he,heq⟩ := hab
        by_cases hb : b ∈ W
        · exact Or.inr ⟨a,b,e,ha,hb,he,heq,ih⟩
        · exact Or.inl (ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G Wᶜ e a b heq).mpr ⟨ha,hb⟩⟩,heq⟩)
      · exact Or.inr ih
  rcases haux with h | h
  · exact ((conn_internal_endpoint G Wᶜ hx h) hy).elim
  · exact h


theorem internal_not_cut (G : BondGraph V E) (W : Set V) {e : E}
    (he : e ∈ internalEdges G W) : ¬CutExists G W e := by
  rintro ⟨a,b,hab,ha,hb⟩
  exact hb ((mem_internalEdges_of_ends G W e a b hab).mp he).2

theorem exterior_not_cut (G : BondGraph V E) (W : Set V) {e : E}
    (he : e ∈ internalEdges G Wᶜ) : ¬CutExists G W e := by
  rintro ⟨a,b,hab,ha,hb⟩
  exact ((mem_internalEdges_of_ends G Wᶜ e a b hab).mp he).1 ha

theorem internal_pruneContacts (G : BondGraph V E) (ω : Finset E) (W : Set V) (e : E) :
    internalBonds G (pruneContacts G ω W e) W = internalBonds G ω W := by
  ext f
  simp only [internalBonds,pruneContacts,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,Or.inl (internal_not_cut G W h.2)⟩,h.2⟩

theorem pruneContacts_only_attachment (G : BondGraph V E) (ω : Finset E) (W : Set V) (e : E) :
    ∀ f ∈ pruneContacts G ω W e, CutExists G W f → f = e := by
  intro f hf hc
  exact (Finset.mem_filter.mp hf).2.resolve_left (not_not.mpr hc)

 
theorem exists_pruneContacts_root (G : BondGraph V E) (ω : Finset E) (W : Set V) (x : V)
    (hWroot : W ⊆ cluster G ω x) (hWconn : ∀ a ∈ W, ∀ b ∈ W,
      Conn G (ω ∩ internalEdges G W) a b)
    (hcontact : ∃ e ∈ ω, CutExists G W e) :
    ∃ e ∈ ω, CutExists G W e ∧ W ⊆ cluster G (pruneContacts G ω W e) x := by
  by_cases hx : x ∈ W
  · obtain ⟨e,he,hec⟩ := hcontact
    refine ⟨e,he,hec,?_⟩
    intro y hy
    apply conn_mono G _ (hWconn x hx y hy)
    intro f hf
    exact Finset.mem_filter.mpr ⟨hf.1,Or.inl (internal_not_cut G W hf.2)⟩
  · obtain ⟨e₀,he₀,a,b,hab,ha,hb⟩ := hcontact
    obtain ⟨c,z,e,hc,hz,he,hez,hxc⟩ := conn_first_entry G W ω hx ha (hWroot ha)
    have hec : CutExists G W e := ⟨z,c,by simpa only [Sym2.eq_swap] using hez,hz,hc⟩
    have hep : e ∈ pruneContacts G ω W e := Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩
    have hxz : Conn G (pruneContacts G ω W e : Set E) x z :=
      (conn_mono G (fun f hf => Finset.mem_filter.mpr ⟨hf.1,Or.inl (exterior_not_cut G W hf.2)⟩) hxc).tail
        ⟨e,hep,hez⟩
    refine ⟨e,he,hec,?_⟩
    intro y hy
    exact hxz.trans (conn_mono G (fun f hf =>
      Finset.mem_filter.mpr ⟨hf.1,Or.inl (internal_not_cut G W hf.2)⟩) (hWconn z hz y hy))

end PruningGeometry

section GoodnessGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteRootComponent_mono (G : BondGraph V E) {ω η : Finset E} (h : ω ⊆ η) (x : V) :
    finiteRootComponent G ω x ⊆ finiteRootComponent G η x := by
  intro y hy
  change y ∈ (finiteRootComponent G η x : Set V)
  rw [coe_finiteRootComponent]
  apply conn_mono G (show (ω : Set E) ⊆ η from h)
  change y ∈ (finiteRootComponent G ω x : Set V) at hy
  rwa [coe_finiteRootComponent] at hy


theorem incidentBonds_card_le (G : BondGraph V E) (Q : Finset E) (W : Finset V) (d : ℕ)
    (hd : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    (incidentBonds G Q W).card ≤ d*W.card := by
  calc
    _ ≤ ∑ v ∈ W, (Q.filter fun e => v ∈ G e).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ W, d := Finset.sum_le_sum fun _ _ => hd _
    _ = _ := by simp [Nat.mul_comm]

 

theorem badPieceEvent_pruning (G : BondGraph V E) (Q : Finset E) (x : V) (M K r : ℕ)
    (L : ℝ) (hK : 0 < K) (hr : 2*(r:ℝ) ≤ (K:ℝ)*L)
    (ω : Finset E) (hω : ω ⊆ Q) (h : BadPieceEvent G Q x M K L ω) :
    ∃ η : Finset E, η ⊆ ω ∧ CappedRadiusEvent G Q x M r η ∧
      (ω \ η).card ≤ K ∧ ω \ η ⊆ incidentBonds G Q (finiteRootComponent G η x) := by
  obtain ⟨hcap,W,hW,hWconn,hcontacts,a,ha,b,hb,hbad⟩ := h
  have hcontact : ∃ e ∈ ω, CutExists G (W : Set V) e := by
    have : (openContacts G ω (W : Set V)).Nonempty := Finset.card_pos.mp (hcontacts ▸ hK)
    obtain ⟨e,he⟩ := this
    exact ⟨e,(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩
  have hWroot : (W : Set V) ⊆ cluster G ω x := by
    intro z hz
    have hh : z ∈ (finiteRootComponent G ω x : Set V) := hW hz
    rwa [coe_finiteRootComponent] at hh
  obtain ⟨e,he,hec,hWη⟩ := exists_pruneContacts_root G ω (W : Set V) x hWroot
    (by intro a ha b hb; simpa only [coe_internalBonds] using hWconn a ha b hb) hcontact
  let η := pruneContacts G ω (W : Set V) e
  have hη : η ⊆ ω := Finset.filter_subset _ _
  have hep : e ∈ η := Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩
  have hpiv := pairOpenPivotals_one_attachment G Q η (W : Set V) e hep hec
    (pruneContacts_only_attachment G ω (W : Set V) e) ha hb
  rw [internal_pruneContacts] at hpiv
  have hfar : (K:ℝ)*L < (pairOpenPivotals G Q a b η).card :=
    hbad.trans_le (by exact_mod_cast Finset.card_le_card hpiv)
  have hxa : Conn G (η : Set E) x a := hWη ha
  have hxb : Conn G (η : Set E) x b := hWη hb
  have htri := pairOpenPivotals_triangle G Q η a x b (conn_symm G η hxa) hxb
  rw [pairOpenPivotals_symm G Q η a x] at htri
  have hlarge : r ≤ (pairOpenPivotals G Q x a η).card ∨
      r ≤ (pairOpenPivotals G Q x b η).card := by
    by_contra hn
    push Not at hn
    have htri' : ((pairOpenPivotals G Q a b η).card:ℝ) ≤
        (pairOpenPivotals G Q x a η).card+(pairOpenPivotals G Q x b η).card := by exact_mod_cast htri
    have h₁ : ((pairOpenPivotals G Q x a η).card:ℝ) < r := by exact_mod_cast hn.1
    have h₂ : ((pairOpenPivotals G Q x b η).card:ℝ) < r := by exact_mod_cast hn.2
    linarith
  have hchanges : ω \ η ⊆ openContacts G ω (W : Set V) := by
    intro f hf
    obtain ⟨hfω,hfη⟩ := Finset.mem_sdiff.mp hf
    refine Finset.mem_filter.mpr ⟨hfω,?_⟩
    by_contra hn
    exact hfη (Finset.mem_filter.mpr ⟨hfω,Or.inl hn⟩)
  refine ⟨η,hη,⟨(Finset.card_le_card (finiteRootComponent_mono G hη x)).trans hcap,?_⟩,
    (Finset.card_le_card hchanges).trans (le_of_eq hcontacts),?_⟩
  · rcases hlarge with h | h
    · exact ⟨a,hxa,h⟩
    · exact ⟨b,hxb,h⟩
  · intro f hf
    obtain ⟨hfω,c,z,hcz,hc,_⟩ := Finset.mem_filter.mp (hchanges hf)
    refine (mem_incidentBonds G Q _ f).mpr ⟨hω hfω,c,?_,?_⟩
    · change c ∈ (finiteRootComponent G η x : Set V)
      rw [coe_finiteRootComponent]
      exact hWη hc
    · simp [hcz]

end GoodnessGeometry

section FiniteInverseCost
attribute [local instance] Classical.propDecidable Classical.decEq


theorem bernoulliWeight_closure_ratio (Q ω η : Finset E) (hη : η ⊆ ω) (hω : ω ⊆ Q)
    (p : ℝ) (hp : p < 1) :
    bernoulliWeight Q ω p = bernoulliWeight Q η p*(p/(1-p))^((ω \ η).card) := by
  have h₁ := Finset.card_le_card hη
  have h₂ := Finset.card_le_card hω
  have hj : (ω \ η).card = ω.card-η.card := Finset.card_sdiff_of_subset hη
  have ha : ω.card = η.card+(ω \ η).card := by omega
  have hb : Q.card-η.card = (Q.card-ω.card)+(ω \ η).card := by omega
  have hq : (1-p) ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  unfold bernoulliWeight
  rw [hb,pow_add,div_pow]
  rw [← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero _ hq)).mpr
  rw [ha,pow_add]
  ring

 
theorem bernoulliWeight_closure_le (Q ω η : Finset E) (hη : η ⊆ ω) (hω : ω ⊆ Q)
    (p : unitInterval) (hp : (p:ℝ) < 1) (K : ℕ) (hj : (ω \ η).card ≤ K) :
    bernoulliWeight Q ω p ≤ (max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p := by
  rw [bernoulliWeight_closure_ratio Q ω η hη hω p hp,mul_comm]
  apply mul_le_mul_of_nonneg_right _ (bernoulliWeight_nonneg Q η p)
  calc
    _ ≤ (max 1 ((p:ℝ)/(1-p)))^((ω \ η).card) :=
      pow_le_pow_left₀ (div_nonneg p.2.1 (sub_nonneg.mpr p.2.2)) (le_max_right ..) _
    _ ≤ _ := pow_le_pow_right₀ (le_max_left ..) hj

 
theorem card_small_subsets_le (S : Finset E) (K N : ℕ) (hS : S.card ≤ N) (hN : 1 ≤ N) :
    (S.powerset.filter fun T => T.card ≤ K).card ≤ (K+1)*N^K := by
  have hsub : S.powerset.filter (fun T => T.card ≤ K) ⊆
      (Finset.range (K+1)).biUnion (fun j => S.powersetCard j) := by
    intro T hT
    obtain ⟨hTS,hTK⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_biUnion.mpr ⟨T.card,Finset.mem_range.mpr (Nat.lt_succ_of_le hTK),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hTS,rfl⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (K+1), (S.powersetCard j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (K+1), N^K := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left hS _).trans
        (Nat.pow_le_pow_right hN (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))
    _ = _ := by simp

 
theorem closure_fiber_card_le (A : Finset (Finset E)) (f : Finset E → Finset E)
    (S : Finset E) (η : Finset E) (K N : ℕ) (hN : 1 ≤ N) (hS : S.card ≤ N)
    (hf : ∀ ω ∈ A, f ω = η → f ω ⊆ ω ∧ (ω \ f ω).card ≤ K ∧ ω \ f ω ⊆ S) :
    (A.filter fun ω => f ω = η).card ≤ (K+1)*N^K := by
  have hm : Set.MapsTo (fun ω : Finset E => ω \ η) (A.filter fun ω => f ω = η : Set (Finset E))
      (S.powerset.filter fun T => T.card ≤ K : Set (Finset E)) := by
    intro ω hω
    obtain ⟨hωA,heq⟩ := Finset.mem_filter.mp hω
    obtain ⟨_,hj,hs⟩ := hf ω hωA heq
    rw [heq] at hj hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs,hj⟩
  have hi : Set.InjOn (fun ω : Finset E => ω \ η) (A.filter fun ω => f ω = η : Set (Finset E)) := by
    intro ω hω ζ hζ heq
    obtain ⟨hωA,hωη⟩ := Finset.mem_filter.mp hω
    obtain ⟨hζA,hζη⟩ := Finset.mem_filter.mp hζ
    have h₁ := (hf ω hωA hωη).1
    have h₂ := (hf ζ hζA hζη).1
    rw [hωη] at h₁
    rw [hζη] at h₂
    have : η ∪ (ω \ η) = η ∪ (ζ \ η) := congrArg (fun s => η ∪ s) heq
    simpa only [Finset.union_sdiff_of_subset h₁,Finset.union_sdiff_of_subset h₂] using this
  exact (Finset.card_le_card_of_injOn (fun ω => ω \ η) hm hi).trans (card_small_subsets_le S K N hS hN)

 
theorem finite_closure_comparison (Q : Finset E) (A B : Finset (Finset E))
    (hA : A ⊆ Q.powerset) (f : Finset E → Finset E) (S : Finset E → Finset E)
    (K N : ℕ) (hN : 1 ≤ N) (p : unitInterval) (hp : (p:ℝ) < 1)
    (hf : ∀ ω ∈ A, f ω ∈ B ∧ f ω ⊆ ω ∧ (ω \ f ω).card ≤ K ∧ ω \ f ω ⊆ S (f ω))
    (hS : ∀ η ∈ B, (S η).card ≤ N) :
    (∑ ω ∈ A, bernoulliWeight Q ω p) ≤
      (((K+1)*N^K : ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K*∑ η ∈ B, bernoulliWeight Q η p := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun ω hω => (hf ω hω).1) (fun ω => bernoulliWeight Q ω p),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro η hη
  let T := A.filter fun ω => f ω = η
  have hc : T.card ≤ (K+1)*N^K := closure_fiber_card_le A f (S η) η K N hN (hS η hη) (by
    intro ω hω heq
    have hh := (hf ω hω).2
    simpa only [heq] using hh)
  have hweight : ∀ ω ∈ T, bernoulliWeight Q ω p ≤
      (max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p := by
    intro ω hω
    obtain ⟨hωA,heq⟩ := Finset.mem_filter.mp hω
    have hh := bernoulliWeight_closure_le Q ω (f ω) (hf ω hωA).2.1
      (Finset.mem_powerset.mp (hA hωA)) p hp K (hf ω hωA).2.2.1
    simpa only [heq] using hh
  calc
    _ ≤ ∑ _ω ∈ T, (max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p := Finset.sum_le_sum hweight
    _ = (T.card:ℝ)*((max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p) := by simp
    _ ≤ (((K+1)*N^K:ℕ):ℝ)*((max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
        (mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left ..)) _) (bernoulliWeight_nonneg Q η p))
    _ = _ := by ring

end FiniteInverseCost

section FiniteGoodnessProbability
attribute [local instance] Classical.propDecidable Classical.decEq

theorem bernoulliPolynomial_indicator_weight (Q : Finset E) (P : Finset E → Prop) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => if P ω then 1 else 0) p =
      ∑ ω ∈ Q.powerset.filter P, bernoulliWeight Q ω p := by
  rw [Finset.sum_filter]
  unfold bernoulliPolynomial
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : P ω <;> simp [h,bernoulliWeight]

 
theorem finiteBadPieceProbability_le_radius (G : BondGraph V E) (Q : Finset E) (x : V)
    (M K r d : ℕ) (L : ℝ) (hK : 0 < K) (hN : 1 ≤ d*M)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d)
    (hr : 2*(r:ℝ) ≤ (K:ℝ)*L) (p : unitInterval) (hp : (p:ℝ) < 1) :
    finiteBadPieceProbability G Q x M K L p ≤
      (((K+1)*(d*M)^K:ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K*finiteCappedRadiusTail G Q x M r p := by
  let A := Q.powerset.filter (BadPieceEvent G Q x M K L)
  let B := Q.powerset.filter (CappedRadiusEvent G Q x M r)
  let S := fun η => incidentBonds G Q (finiteRootComponent G η x)
  have hex : ∀ ω : Finset E, ∃ η : Finset E, ω ∈ A →
      η ∈ B ∧ η ⊆ ω ∧ (ω \ η).card ≤ K ∧ ω \ η ⊆ S η := by
    intro ω
    by_cases hω : ω ∈ A
    · obtain ⟨hωQ,hωbad⟩ := Finset.mem_filter.mp hω
      have hωsub := Finset.mem_powerset.mp hωQ
      obtain ⟨η,hη,hcap,hcard,hS⟩ := badPieceEvent_pruning G Q x M K r L hK hr ω hωsub hωbad
      exact ⟨η,fun _ => ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hη.trans hωsub),hcap⟩,
        hη,hcard,hS⟩⟩
    · exact ⟨∅,fun h => (hω h).elim⟩
  choose f hf using hex
  have hS : ∀ η ∈ B, (S η).card ≤ d*M := by
    intro η hη
    exact (incidentBonds_card_le G Q (finiteRootComponent G η x) d hdeg).trans
      (Nat.mul_le_mul_left d (Finset.mem_filter.mp hη).2.1)
  have hc := finite_closure_comparison Q A B (Finset.filter_subset _ _) f S K (d*M) hN p hp hf hS
  simpa only [finiteBadPieceProbability,finiteCappedRadiusTail,bernoulliPolynomial_indicator_weight,
    A,B] using hc

 
theorem finiteBadPieceProbability_exponential [Nonempty V] (G : BondGraph V E)
    (Q : Finset E) (x : V) (M K d : ℕ) (L : ℝ) (hK : 0 < K) (hN : 1 ≤ d*M)
    (hL : 4 ≤ (K:ℝ)*L) (hd : 0 < d)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d)
    (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (hh1 : (h:ℝ) < 1)
    (B : ℝ) (hB : 1 ≤ B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B) :
    finiteBadPieceProbability G Q x M K L p ≤
      (((K+1)*(d*M)^K:ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K*
        (2/((h:ℝ)*(1-h)^M))*Real.exp (-((K:ℝ)*L)/(16*B)) := by
  let r := ⌈(K:ℝ)*L/4⌉₊
  have hpos : 0 ≤ (K:ℝ)*L/4 := by linarith
  have hrlo : (K:ℝ)*L/4 ≤ r := Nat.le_ceil _
  have hrhi : (r:ℝ) < (K:ℝ)*L/4+1 := Nat.ceil_lt_add_one hpos
  have hr : 2*(r:ℝ) ≤ (K:ℝ)*L := by linarith
  have hrad := finiteCappedRadiusTail_exponential G p h hp hh hh1 d hd Q x hdeg B hB hAB M r
  have hcmp := finiteBadPieceProbability_le_radius G Q x M K r d L hK hN hdeg hr p hp
  have hc : 0 ≤ (((K+1)*(d*M)^K:ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K := by positivity
  have hhfac : 0 ≤ 2/((h:ℝ)*(1-h)^M) := by positivity
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hratio : -((r:ℝ)/(4*B)) ≤ -((K:ℝ)*L)/(16*B) := by
    apply (le_div_iff₀ (by positivity : 0 < 16*B)).mpr
    field_simp
    nlinarith
  exact hcmp.trans ((mul_le_mul_of_nonneg_left hrad hc).trans (by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by simpa only [neg_div] using hratio)) (mul_nonneg hc hhfac)))



theorem cappedBadGoodness_iff (G : BondGraph V E) (Q : Finset E) (x : V) (M d : ℕ)
    (L : ℝ) (ω : Finset E) (hω : ω ⊆ Q)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    CappedBadGoodnessEvent G Q x M L ω ↔
      ∃ K ∈ Finset.Icc 1 (d*M), BadPieceEvent G Q x M K L ω := by
  constructor
  · rintro ⟨hcap,hbad⟩
    simp only [FiniteGoodForScale,not_forall] at hbad
    obtain ⟨W,hbad⟩ := hbad
    push Not at hbad
    obtain ⟨hW,hWconn,hK,a,ha,b,hb,hfar⟩ := hbad
    have hinc : openContacts G ω (W : Set V) ⊆ incidentBonds G Q W := by
      intro e he
      obtain ⟨heω,c,z,hcz,hc,_⟩ := Finset.mem_filter.mp he
      exact (mem_incidentBonds G Q W e).mpr ⟨hω heω,c,hc,by simp [hcz]⟩
    have hbound := (Finset.card_le_card hinc).trans ((incidentBonds_card_le G Q W d hdeg).trans
      (Nat.mul_le_mul_left d ((Finset.card_le_card hW).trans hcap)))
    exact ⟨_,Finset.mem_Icc.mpr ⟨hK,hbound⟩,hcap,W,hW,hWconn,rfl,a,ha,b,hb,hfar⟩
  · rintro ⟨K,hK,hcap,W,hW,hWconn,hcontacts,a,ha,b,hb,hfar⟩
    refine ⟨hcap,fun hgood => ?_⟩
    have hh := hgood W hW hWconn (by rw [hcontacts]; exact (Finset.mem_Icc.mp hK).1) a ha b hb
    rw [hcontacts] at hh
    exact not_lt_of_ge hh hfar

 
theorem finiteBadGoodnessProbability_le_sum (G : BondGraph V E) (Q : Finset E) (x : V)
    (M d : ℕ) (L : ℝ) (p : unitInterval)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    finiteBadGoodnessProbability G Q x M L p ≤
      ∑ K ∈ Finset.Icc 1 (d*M), finiteBadPieceProbability G Q x M K L p := by
  unfold finiteBadPieceProbability finiteBadGoodnessProbability
  rw [← bernoulliPolynomial_sum]
  apply bernoulliPolynomial_mono _ _ _ _ p.2
  intro ω hω
  by_cases he : CappedBadGoodnessEvent G Q x M L ω
  · obtain ⟨K,hK,hbad⟩ := (cappedBadGoodness_iff G Q x M d L ω hω hdeg).mp he
    simp only [he,if_true]
    exact (by simp [hbad] : (1:ℝ) ≤ if BadPieceEvent G Q x M K L ω then 1 else 0).trans
      (Finset.single_le_sum (f := fun j => if BadPieceEvent G Q x M j L ω then (1:ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) hK)
  · simp only [he,if_false]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

 
theorem finiteBadGoodnessProbability_geometric [Nonempty V] (G : BondGraph V E)
    (Q : Finset E) (x : V) (M d : ℕ) (L : ℝ) (hN : 1 ≤ d*M) (hL : 4 ≤ L)
    (hd : 0 < d) (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d)
    (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (hh1 : (h:ℝ) < 1)
    (B : ℝ) (hB : 1 ≤ B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B)
    (hq : ((d*M:ℕ):ℝ)*max 1 ((p:ℝ)/(1-p))*Real.exp (-L/(16*B)) ≤ 1) :
    finiteBadGoodnessProbability G Q x M L p ≤
      (2/((h:ℝ)*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
        (((d*M:ℕ):ℝ)*max 1 ((p:ℝ)/(1-p))*Real.exp (-L/(16*B))) := by
  let N := d*M
  let a := max 1 ((p:ℝ)/(1-p))
  let H := 2/((h:ℝ)*(1-h)^M)
  let q := (N:ℝ)*a*Real.exp (-L/(16*B))
  have ha : 0 ≤ a := le_trans zero_le_one (le_max_left ..)
  have hq0 : 0 ≤ q := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) (Real.exp_nonneg _)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hkbound : ∀ K ∈ Finset.Icc 1 N, finiteBadPieceProbability G Q x M K L p ≤ H*((N:ℝ)+1)*q := by
    intro K hK
    obtain ⟨hK1,hKN⟩ := Finset.mem_Icc.mp hK
    have hKR : (1:ℝ) ≤ K := by exact_mod_cast hK1
    have hKL : 4 ≤ (K:ℝ)*L := by nlinarith
    have hexp := finiteBadPieceProbability_exponential G Q x M K d L hK1 hN hKL hd hdeg
      p h hp hh hh1 B hB hAB
    have hid : (((K+1)*(d*M)^K:ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K*
        (2/((h:ℝ)*(1-h)^M))*Real.exp (-((K:ℝ)*L)/(16*B)) = H*((K:ℝ)+1)*q^K := by
      rw [show -((K:ℝ)*L)/(16*B) = (K:ℝ)*(-L/(16*B)) by ring,Real.exp_nat_mul]
      simp only [q,H,N,a,mul_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
      ring
    rw [hid] at hexp
    have hpow : q^K ≤ q := by
      simpa only [pow_one] using pow_le_pow_of_le_one hq0 hq hK1
    calc
      _ ≤ H*((K:ℝ)+1)*q^K := hexp
      _ ≤ H*((N:ℝ)+1)*q := mul_le_mul
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hKN 1) hH)
        hpow (pow_nonneg hq0 _) (mul_nonneg hH (by positivity))
  calc
    _ ≤ ∑ K ∈ Finset.Icc 1 N, finiteBadPieceProbability G Q x M K L p :=
      finiteBadGoodnessProbability_le_sum G Q x M d L p hdeg
    _ ≤ ∑ _K ∈ Finset.Icc 1 N, H*((N:ℝ)+1)*q := Finset.sum_le_sum hkbound
    _ = (N:ℝ)*(H*((N:ℝ)+1)*q) := by simp
    _ = _ := by dsimp [N,H,q,a]; push_cast; ring

end FiniteGoodnessProbability

section GoodnessAsymptotics

 
theorem inverse_mark_cost_le (h : ℝ) (hh : 0 ≤ h) (hh2 : h ≤ 1/2) (M : ℕ) :
    ((1-h)^M)⁻¹ ≤ Real.exp (2*(M:ℝ)*h) := by
  have hq : 0 < 1-h := by linarith
  have hi : 1/(1-h) ≤ 1+2*h := (div_le_iff₀ hq).mpr (by nlinarith)
  have hl := Real.one_sub_inv_le_log_of_pos hq
  rw [one_div] at hi
  have hlog : -2*h ≤ Real.log (1-h) := by linarith
  calc
    ((1-h)^M)⁻¹ = Real.exp (-((M:ℝ)*Real.log (1-h))) := by
      rw [← Real.log_pow,Real.exp_neg,Real.exp_log (pow_pos hq _)]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)
      nlinarith)

 

theorem ghost_scale_estimates (M : ℕ) (ε c a : ℝ) (d : ℕ)
    (hM : 1 ≤ (M:ℝ)) (hε : 0 < ε) (hε1 : ε < 1/2) (hc : 1 ≤ c)
    (ha : 1 ≤ a) (hd : 1 ≤ d)
    (hsmall : (M:ℝ)^(ε-1) ≤ 1/2)
    (hlog : 4*Real.log M ≤ (M:ℝ)^ε)
    (hlog2 : Real.log M ≤ (M:ℝ)^(ε/2))
    (hgrowth : 80*c ≤ (M:ℝ)^(ε/4))
    (hconstant : Real.log (2*(d:ℝ)^2*((d:ℝ)+1)*a) ≤ (M:ℝ)^ε) :
    let h := (M:ℝ)^(ε-1)
    let B := c*(M:ℝ)^(1/2-ε/4)
    let L := (M:ℝ)^(1/2+ε)
    0 < h ∧ h ≤ 1/2 ∧ 1 ≤ B ∧
      c*Real.sqrt (Real.log (1/h)/h) ≤ B ∧
      (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
        (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) ≤ Real.exp (-(M:ℝ)^ε) := by
  dsimp only
  let h := (M:ℝ)^(ε-1)
  let B := c*(M:ℝ)^(1/2-ε/4)
  let L := (M:ℝ)^(1/2+ε)
  have hMp : 0 < (M:ℝ) := lt_of_lt_of_le zero_lt_one hM
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hdp : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hhp : 0 < h := Real.rpow_pos_of_pos hMp _
  have hq : 0 < 1-h := by dsimp [h] at *; linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hinv : 1/h = (M:ℝ)^(1-ε) := by
    dsimp [h]
    rw [show 1-ε = -(ε-1) by ring,Real.rpow_neg hMp.le,one_div]
  have hmh : (M:ℝ)*h = (M:ℝ)^ε := by
    dsimp [h]
    calc
      _ = (M:ℝ)^((1:ℝ)+(ε-1)) := by rw [Real.rpow_add hMp,Real.rpow_one]
      _ = _ := by congr 1; ring
  have hhM : 1/h ≤ (M:ℝ) := by
    rw [hinv]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hM (show 1-ε ≤ (1:ℝ) by linarith)
  have hB1 : 1 ≤ B := by
    have hp := Real.one_le_rpow hM (show 0 ≤ 1/2-ε/4 by linarith)
    dsimp [B]
    nlinarith
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hAB : c*Real.sqrt (Real.log (1/h)/h) ≤ B := by
    apply mul_le_mul_of_nonneg_left _ hcp.le
    have hl : Real.log (1/h) ≤ Real.log M := by
      rw [hinv,Real.log_rpow hMp]
      nlinarith
    have hl2 : Real.log (1/h)/h ≤ (M:ℝ)^(1-ε/2) := by
      calc
        _ = Real.log (1/h)*(M:ℝ)^(1-ε) := by rw [div_eq_mul_one_div,hinv]
        _ ≤ (M:ℝ)^(ε/2)*(M:ℝ)^(1-ε) :=
          mul_le_mul_of_nonneg_right (hl.trans hlog2) (Real.rpow_nonneg hMp.le _)
        _ = _ := by rw [← Real.rpow_add hMp]; congr 1; ring
    calc
      _ ≤ Real.sqrt ((M:ℝ)^(1-ε/2)) := Real.sqrt_le_sqrt hl2
      _ = (M:ℝ)^(1/2-ε/4) := by
        rw [Real.sqrt_eq_rpow,← Real.rpow_mul hMp.le]
        congr 1
        ring
  have hratio : 5*(M:ℝ)^ε ≤ L/(16*B) := by
    have hid : (M:ℝ)^ε*(M:ℝ)^(ε/4)*(M:ℝ)^(1/2-ε/4) = L := by
      dsimp [L]
      rw [← Real.rpow_add hMp,← Real.rpow_add hMp]
      congr 1
      ring
    apply (le_div_iff₀ (by positivity : 0 < 16*B)).mpr
    have hh := mul_le_mul_of_nonneg_left hgrowth
      (mul_nonneg (Real.rpow_nonneg hMp.le ε) (Real.rpow_nonneg hMp.le (1/2-ε/4)))
    dsimp [B]
    nlinarith [hid]
  refine ⟨hhp,hsmall,hB1,hAB,?_⟩
  let A := 2*(d:ℝ)^2*((d:ℝ)+1)*a
  have hAp : 0 < A := by dsimp [A]; positivity
  have hcost : 2/(h*(1-h)^M) ≤ 2*(M:ℝ)*Real.exp (2*(M:ℝ)^ε) := by
    calc
      _ = 2*(1/h)*((1-h)^M)⁻¹ := by field_simp
      _ ≤ 2*(M:ℝ)*Real.exp (2*(M:ℝ)*h) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hhM (by norm_num))
          (inverse_mark_cost_le h hhp.le hsmall M) (inv_nonneg.mpr (pow_nonneg hq.le _)) (by positivity)
      _ = _ := by rw [show 2*(M:ℝ)*h = 2*(M:ℝ)^ε by rw [mul_assoc,hmh]]
  have hN1 : ((d*M:ℕ):ℝ)+1 ≤ ((d:ℝ)+1)*(M:ℝ) := by push_cast; nlinarith
  have hpoint :
      (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
        (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) ≤
      A*(M:ℝ)^4*Real.exp (2*(M:ℝ)^ε-L/(16*B)) := by
    calc
      _ ≤ (2*(M:ℝ)*Real.exp (2*(M:ℝ)^ε))*((d*M:ℕ):ℝ)*(((d:ℝ)+1)*(M:ℝ))*
          (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_right hcost (by positivity)) hN1
          (by positivity) (by positivity)
      _ = _ := by
        rw [show 2*(M:ℝ)^ε-L/(16*B) = 2*(M:ℝ)^ε+(-L/(16*B)) by ring,Real.exp_add]
        dsimp [A]
        push_cast
        ring
  have heq : A*(M:ℝ)^4*Real.exp (2*(M:ℝ)^ε-L/(16*B)) =
      Real.exp (Real.log A+4*Real.log M+2*(M:ℝ)^ε-L/(16*B)) := by
    rw [show Real.log A+4*Real.log M+2*(M:ℝ)^ε-L/(16*B) =
      Real.log A+4*Real.log M+(2*(M:ℝ)^ε-L/(16*B)) by ring,Real.exp_add,
      Real.exp_add,Real.exp_log hAp]
    have hh : Real.exp (4*Real.log M) = (M:ℝ)^4 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hMp] using Real.exp_nat_mul (Real.log M) 4
    rw [hh]
  rw [heq] at hpoint
  exact hpoint.trans (Real.exp_le_exp.mpr (by linarith))

 

theorem eventually_ghost_scale (ε c a : ℝ) (d : ℕ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (hc : 1 ≤ c) (ha : 1 ≤ a) (hd : 1 ≤ d) :
    ∀ᶠ M : ℕ in Filter.atTop,
      let h := (M:ℝ)^(ε-1)
      let B := c*(M:ℝ)^(1/2-ε/4)
      let L := (M:ℝ)^(1/2+ε)
      1 ≤ M ∧ 4 ≤ L ∧ 0 < h ∧ h ≤ 1/2 ∧ 1 ≤ B ∧
        c*Real.sqrt (Real.log (1/h)/h) ≤ B ∧
        (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
          (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) ≤ Real.exp (-(M:ℝ)^ε) := by
  have hh : ∀ᶠ m : ℝ in Filter.atTop, m^(ε-1) ≤ 1/2 := by
    have ht := tendsto_rpow_neg_atTop (show 0 < 1-ε by linarith)
    filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with m hm
    simpa only [neg_sub] using (show m^(-(1-ε)) < 1/2 from hm).le
  have hl := (isLittleO_log_rpow_atTop hε).bound (show (0:ℝ) < 1/4 by norm_num)
  have hl2 := (isLittleO_log_rpow_atTop (show 0 < ε/2 by linarith)).bound zero_lt_one
  have hg := (tendsto_rpow_atTop (show 0 < ε/4 by linarith)).eventually (Filter.eventually_ge_atTop (80*c))
  have hC := (tendsto_rpow_atTop hε).eventually
    (Filter.eventually_ge_atTop (Real.log (2*(d:ℝ)^2*((d:ℝ)+1)*a)))
  have hL := (tendsto_rpow_atTop (show 0 < 1/2+ε by linarith)).eventually (Filter.eventually_ge_atTop 4)
  have hnum : ∀ᶠ m : ℝ in Filter.atTop, 1 ≤ m ∧ 4 ≤ m^(1/2+ε) ∧ m^(ε-1) ≤ 1/2 ∧
      4*Real.log m ≤ m^ε ∧ Real.log m ≤ m^(ε/2) ∧ 80*c ≤ m^(ε/4) ∧
      Real.log (2*(d:ℝ)^2*((d:ℝ)+1)*a) ≤ m^ε := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hh,hl,hl2,hg,hC,hL] with m hm hh hl hl2 hg hC hL
    have hm0 : 0 ≤ m := le_trans zero_le_one hm
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hm),
      abs_of_nonneg (Real.rpow_nonneg hm0 ε)] at hl
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hm),
      abs_of_nonneg (Real.rpow_nonneg hm0 (ε/2)),one_mul] at hl2
    exact ⟨hm,hL,hh,by linarith,hl2,hg,hC⟩
  have hcast : Filter.Tendsto (fun M : ℕ => (M:ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually hnum] with M hM
  obtain ⟨hM,hL,hh,hl,hl2,hg,hC⟩ := hM
  exact ⟨by exact_mod_cast hM,hL,ghost_scale_estimates M ε c a d hM hε hε1 hc ha hd hh hl hl2 hg hC⟩

 
theorem ghost_ratio_le_one (M d : ℕ) (hM : 1 ≤ M) (hd : 1 ≤ d)
    (h B L a ε : ℝ) (hh : 0 < h) (hh2 : h ≤ 1/2) (ha : 0 ≤ a)
    (hb : (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
      (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) ≤ Real.exp (-(M:ℝ)^ε)) :
    ((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B)) ≤ 1 := by
  have hq : 0 < 1-h := by linarith
  have hp : (1-h)^M ≤ 1 := pow_le_one₀ hq.le (by linarith)
  have hden : 0 < h*(1-h)^M := mul_pos hh (pow_pos hq _)
  have hH : 1 ≤ 2/(h*(1-h)^M) := by
    apply (le_div_iff₀ hden).mpr
    have := mul_le_mul_of_nonneg_left hp hh.le
    nlinarith
  have hN : (1:ℝ) ≤ (d*M:ℕ) := by exact_mod_cast Nat.mul_le_mul hd hM
  have hprod : 1 ≤ (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hH hN) (by linarith)
  have hq0 : 0 ≤ ((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B)) := by positivity
  exact (le_mul_of_one_le_left hq0 hprod).trans (hb.trans
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Nat.cast_nonneg M) ε))))

end GoodnessAsymptotics

section UniformFiniteGoodness
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_bad_goodness_stretched_exp [Nonempty V] (G : BondGraph V E)
    (d : ℕ) (hd : 0 < d) (pbar : unitInterval) (hpbar : (pbar:ℝ) < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) :
    ∀ᶠ M : ℕ in Filter.atTop, ∀ (Q : Finset E) (x : V),
      (∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) →
      ∀ p : unitInterval, p ≤ pbar →
        finiteBadGoodnessProbability G Q x M ((M:ℝ)^(1/2+ε)) p ≤
          Real.exp (-(M:ℝ)^ε) := by
  let c := max 1 (Real.sqrt ((d:ℝ)/2)/(1-pbar))
  let a := max 1 ((pbar:ℝ)/(1-pbar))
  have hc : 1 ≤ c := le_max_left ..
  have ha : 1 ≤ a := le_max_left ..
  filter_upwards [eventually_ghost_scale ε c a d hε hε1 hc ha hd] with M hM
  dsimp only at hM
  obtain ⟨hM1,hL,hh,hh2,hB,hAB,hpref⟩ := hM
  intro Q x hdeg p hpp
  have hpp' : (p:ℝ) ≤ pbar := hpp
  have hp : (p:ℝ) < 1 := hpp'.trans_lt hpbar
  let h : unitInterval := ⟨(M:ℝ)^(ε-1),hh.le,by linarith⟩
  let B := c*(M:ℝ)^(1/2-ε/4)
  let L := (M:ℝ)^(1/2+ε)
  have hodds : max 1 ((p:ℝ)/(1-p)) ≤ a := by
    apply max_le (le_max_left ..)
    have hr : (p:ℝ)/(1-p) ≤ (pbar:ℝ)/(1-pbar) :=
      div_le_div₀ pbar.2.1 hpp' (by linarith) (by linarith)
    exact hr.trans (le_max_right ..)
  have hcoeff : Real.sqrt ((d:ℝ)/2)/(1-p) ≤ c := by
    have hr : Real.sqrt ((d:ℝ)/2)/(1-p) ≤ Real.sqrt ((d:ℝ)/2)/(1-pbar) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by linarith) (by linarith)
    exact hr.trans (le_max_right ..)
  have hsqrt : 0 ≤ Real.sqrt (Real.log (1/(h:ℝ))/h) := Real.sqrt_nonneg _
  have hqbar := ghost_ratio_le_one M d hM1 hd h B L a ε hh hh2
    (le_trans zero_le_one ha) hpref
  have hqcmp : ((d*M:ℕ):ℝ)*max 1 ((p:ℝ)/(1-p))*Real.exp (-L/(16*B)) ≤
      ((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hodds (Nat.cast_nonneg _)) (Real.exp_nonneg _)
  have hg := finiteBadGoodnessProbability_geometric G Q x M d L (Nat.mul_le_mul hd hM1)
    hL hd hdeg p h hp hh (by dsimp [h]; linarith) B hB
    ((mul_le_mul_of_nonneg_right hcoeff hsqrt).trans hAB) (hqcmp.trans hqbar)
  refine hg.trans ((mul_le_mul_of_nonneg_left hqcmp ?_).trans hpref)
  have hnon : 0 ≤ 1-(h:ℝ) := sub_nonneg.mpr h.2.2
  positivity

end UniformFiniteGoodness

section InfiniteGoodness
attribute [local instance] Classical.propDecidable Classical.decEq


theorem pivotalDistance_finset (G : BondGraph V E) (Q ω : Finset E) (hω : ω ⊆ Q) (a b : V) :
    pivotalDistance G (ω : Set E) a b = (pairOpenPivotals G Q a b ω).card := by
  have he : {e | OpenMarkedPivotal G (ω : Set E) {b} a e} =
      (pairOpenPivotals G Q a b ω : Set E) := by
    ext e
    simp only [Finset.mem_coe,mem_pairOpenPivotals,Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨hω h.1,h⟩,And.right⟩
  simp only [pivotalDistance,he,Set.ncard_coe_finset]

theorem contactSet_finset (G : BondGraph V E) (ω : Finset E) (W : Set V) :
    contactSet G (ω : Set E) W = (openContacts G ω W : Set E) := by
  ext e
  simp only [contactSet,openContacts,Finset.mem_coe,Finset.mem_filter,Set.mem_ofPred_eq]

theorem finiteGoodForScale_iff (G : BondGraph V E) (Q ω : Finset E) (hω : ω ⊆ Q)
    (x : V) (L : ℝ) : FiniteGoodForScale G Q x L ω ↔ GoodForScale G (ω : Set E) x L := by
  have hroot : ∀ W : Finset V, W ⊆ finiteRootComponent G ω x ↔ (W : Set V) ⊆ cluster G ω x := by
    intro W
    rw [← coe_finiteRootComponent]
    exact Finset.coe_subset.symm
  have hpiv (W : Finset V) (a b : V) := pivotalDistance_finset G Q
    (internalBonds G ω (W : Set V)) ((Finset.filter_subset _ _).trans hω) a b
  simp only [FiniteGoodForScale,GoodForScale,hroot,← coe_internalBonds,contactSet_finset,
    Set.ncard_coe_finset,hpiv]

theorem cappedBadGoodness_finset_iff (G : BondGraph V E) (Q ω : Finset E) (hω : ω ⊆ Q)
    (x : V) (M : ℕ) (L : ℝ) :
    CappedBadGoodness G (ω : Set E) x M L ↔ CappedBadGoodnessEvent G Q x M L ω := by
  have hfin := cluster_finite_of_finite_edges G ω.finite_toSet x
  simp only [CappedBadGoodness,CappedBadGoodnessEvent,hfin,true_and]
  rw [← coe_finiteRootComponent,Set.ncard_coe_finset,finiteGoodForScale_iff G Q ω hω]


end InfiniteGoodness

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

theorem measurableSet_cappedBadGoodness (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) : MeasurableSet {ω | CappedBadGoodness G ω x M L} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : {ω | CappedBadGoodness G ω x M L} =
      {ω | ω ∩ (Q : Set E) ∈ {η | CappedBadGoodness G η x M L}} := by
    ext ω
    exact cappedBadGoodness_local G hloc x M L ω
  rw [he]
  exact measurableSet_finite_restriction Q _

 
theorem bad_goodness_law_eq_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) (p : unitInterval) :
    (law p).real {ω | CappedBadGoodness G ω x M L} =
      finiteBadGoodnessProbability G
        (incidentSupport G hloc (finite_reachBall hloc x M).toFinset) x M L p := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : finiteBadGoodnessProbability G Q x M L p =
      finiteEventPolynomial Q {ω | CappedBadGoodness G ω x M L} p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [Set.mem_ofPred_eq,cappedBadGoodness_finset_iff G Q ω hω]
  change _ = finiteBadGoodnessProbability G Q x M L p
  rw [he,finiteEventPolynomial_restrict]
  congr 1
  ext ω
  exact cappedBadGoodness_local G hloc x M L ω

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

 

theorem bad_goodness_stretched_exp [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (pbar : unitInterval) (hpbar : (pbar:ℝ) < 1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) :
    ∀ᶠ M : ℕ in Filter.atTop, ∀ x : V, ∀ p : unitInterval, p ≤ pbar →
      (law p).real {ω | CappedBadGoodness G ω x M ((M:ℝ)^(1/2+ε))} ≤
        Real.exp (-(M:ℝ)^ε) := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  filter_upwards [finite_bad_goodness_stretched_exp G d hd pbar hpbar ε hε hε1] with M hM
  intro x p hp
  rw [bad_goodness_law_eq_finite G hloc]
  exact hM _ x (fun v => (incident_filter_card_le_degree G hloc _ v).trans (hdeg v)) p hp

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_Geometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical parameters and the geometry, selection and traces of splices. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section CriticalParameter
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem twoPoint_adj_lower [Countable E] (G : BondGraph V E) (p : unitInterval)
    (z x y : V) (hxy : Adj G x y) : (p:ℝ)*twoPoint G p z x ≤ twoPoint G p z y := by
  obtain ⟨e,he⟩ := hxy
  have h := association_finiteWitness p {ω : Set E | e ∈ ω} {ω | Conn G ω z x}
    (fun _ _ hω h => hω h) (fun _ _ hω h => conn_mono G hω h)
    (finiteWitness_edge e) (finiteWitness_conn G z x)
  have hp : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
    simpa using finite_open_probability p {e}
  rw [hp] at h
  exact h.trans (measureReal_mono (fun ω hω =>
    conn_trans G ω hω.2 (Relation.ReflTransGen.single ⟨e,hω.1,he⟩)))


end CriticalParameter

section FiniteExchange
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteExchange_card (M ω η : Finset E) :
    (finiteExchange M ω η).card = (ω \ M).card+(η ∩ M).card := by
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_left.mpr fun e he he' => (Finset.mem_sdiff.mp he).2 (Finset.mem_inter.mp he').2

theorem finiteExchange_card_sum (M ω η : Finset E) :
    (finiteExchange M ω η).card+(finiteExchange M η ω).card = ω.card+η.card := by
  rw [finiteExchange_card,finiteExchange_card]
  have hω := Finset.card_sdiff_add_card_inter ω M
  have hη := Finset.card_sdiff_add_card_inter η M
  omega

theorem finiteExchange_subset (M Q ω η : Finset E) (hω : ω ⊆ Q) (hη : η ⊆ Q) :
    finiteExchange M ω η ⊆ Q := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hω (Finset.mem_sdiff.mp he).1
  · exact hη (Finset.mem_inter.mp he).1

 
theorem bernoulliWeight_exchange (M Q ω η : Finset E) (hω : ω ⊆ Q) (hη : η ⊆ Q)
    (p : ℝ) :
    bernoulliWeight Q (finiteExchange M ω η) p * bernoulliWeight Q (finiteExchange M η ω) p =
      bernoulliWeight Q ω p * bernoulliWeight Q η p := by
  have hc := finiteExchange_card_sum M ω η
  have hcω := Finset.card_le_card hω
  have hcη := Finset.card_le_card hη
  have hcω' := Finset.card_le_card (finiteExchange_subset M Q ω η hω hη)
  have hcη' := Finset.card_le_card (finiteExchange_subset M Q η ω hη hω)
  have hd : (Q.card-(finiteExchange M ω η).card)+(Q.card-(finiteExchange M η ω).card) =
      (Q.card-ω.card)+(Q.card-η.card) := by omega
  unfold bernoulliWeight
  calc
    _ = p^((finiteExchange M ω η).card+(finiteExchange M η ω).card) *
      (1-p)^((Q.card-(finiteExchange M ω η).card)+(Q.card-(finiteExchange M η ω).card)) := by
        rw [pow_add,pow_add]; ring
    _ = p^(ω.card+η.card)*(1-p)^((Q.card-ω.card)+(Q.card-η.card)) := by rw [hc,hd]
    _ = _ := by rw [pow_add,pow_add]; ring

end FiniteExchange

section DeletionGoodness
attribute [local instance] Classical.propDecidable Classical.decEq


theorem contactSet_deleted_cluster (G : BondGraph V E) (ω : Set E) (A : Set V)
    (y : V) (hy : y ∉ A) :
    let B := cluster G (ω ∩ internalEdges G Aᶜ) y
    contactSet G ω B = deletionContacts G ω A B := by
  let ζ := ω ∩ internalEdges G Aᶜ
  let B := cluster G ζ y
  have hB : B ⊆ Aᶜ := slit_cluster_subset G A ω y hy
  ext e
  constructor
  · rintro ⟨he,a,b,hab,ha,hb⟩
    refine ⟨he,a,ha,b,?_,hab⟩
    by_contra hbA
    have heζ : e ∈ ζ := ⟨he,(mem_internalEdges_of_ends G Aᶜ e a b hab).mpr ⟨hB ha,hbA⟩⟩
    exact hb ((edge_cluster_sides G ζ y heζ hab).mp ha)
  · rintro ⟨he,a,ha,b,hb,hab⟩
    exact ⟨he,a,b,hab,ha,fun hh => hB hh hb⟩



theorem capped_good_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L) ↔
      ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧
        (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M ∧
          GoodForScale G (ω ∩ (Q : Set E)) x L) := by
  have hc := capped_cluster_local G hloc x M ω
  have hb := cappedBadGoodness_local G hloc x M L ω
  unfold CappedBadGoodness at hb
  dsimp only at hc hb ⊢
  constructor
  · rintro ⟨hf,hM,hg⟩
    obtain ⟨hf',hM'⟩ := hc.mp ⟨hf,hM⟩
    refine ⟨hf',hM',?_⟩
    by_contra hng
    exact (hb.mpr ⟨hf',hM',hng⟩).2.2 hg
  · rintro ⟨hf,hM,hg⟩
    obtain ⟨hf',hM'⟩ := hc.mpr ⟨hf,hM⟩
    refine ⟨hf',hM',?_⟩
    by_contra hng
    exact (hb.mp ⟨hf',hM',hng⟩).2.2 hg

theorem measurableSet_capped_good (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) :
    MeasurableSet {ω : Set E | (cluster G ω x).Finite ∧
      (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : {ω : Set E | (cluster G ω x).Finite ∧
      (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L} =
    {ω : Set E | (cluster G (ω ∩ (Q : Set E)) x).Finite ∧
      (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M ∧ GoodForScale G (ω ∩ (Q : Set E)) x L} := by
    ext ω
    exact capped_good_local G hloc x M L ω
  rw [he]
  exact measurableSet_finite_restriction Q {η : Set E | (cluster G η x).Finite ∧
      (cluster G η x).ncard ≤ M ∧ GoodForScale G η x L}

end DeletionGoodness

section SpliceSelection
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_maximal_splice_index (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (hj : j ≤ k)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (S : Set V) (hyj : y j ∈ S) (hyk : y k ∉ S) :
    ∃ i ∈ Finset.Icc (j+1) k,
      ((cluster G (η i) (y i)) ∩ S).Nonempty ∧ y i ∉ S ∧
      ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) S := by
  have hjk : j < k := by
    by_contra h
    have hEq : j = k := by omega
    exact hyk (hEq ▸ hyj)
  let T := (Finset.Icc (j+1) k).filter fun i => ((cluster G (η i) (y i)) ∩ S).Nonempty
  have hT : T.Nonempty := by
    refine ⟨j+1,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩,?_⟩⟩
    refine ⟨y j,?_,hyj⟩
    simpa only [Nat.add_sub_cancel,cluster,Set.mem_ofPred_eq] using hchain (j+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  let i := T.max' hT
  have hi : i ∈ T := Finset.max'_mem T hT
  obtain ⟨hiI,hiS⟩ := Finset.mem_filter.mp hi
  have hiU := (Finset.mem_Icc.mp hiI).2
  have hiL := (Finset.mem_Icc.mp hiI).1
  have hl (l : ℕ) (hil : i < l) (hlk : l ≤ k) : Disjoint (cluster G (η l) (y l)) S := by
    apply Set.disjoint_left.mpr
    intro z hz hzS
    have hlT : l ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,hlk⟩,⟨z,hz,hzS⟩⟩
    have hli : l ≤ i := Finset.le_max' T l hlT
    omega
  refine ⟨i,hiI,hiS,?_,hl⟩
  intro hyi
  by_cases hik : i = k
  · exact hyk (hik ▸ hyi)
  · have hic : y i ∈ cluster G (η (i+1)) (y (i+1)) := by
      simpa only [Nat.add_sub_cancel,cluster,Set.mem_ofPred_eq] using hchain (i+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    exact Set.disjoint_left.mp (hl (i+1) (by omega) (by omega)) hic hyi

 

theorem exists_splice_contact (G : BondGraph V E) (η : Set E) (S : Set V) (y : V)
    (hy : y ∉ S) (hmeet : (cluster G η y ∩ S).Nonempty) :
    ∃ e a b, e ∈ η ∧ G e = s(a,b) ∧ a ∈ S ∧
      b ∈ cluster G (η ∩ internalEdges G Sᶜ) y := by
  obtain ⟨v,hv,hvS⟩ := hmeet
  obtain ⟨b,a,e,_,ha,he,hab,hb⟩ := conn_first_entry G S η hy hvS hv
  exact ⟨e,a,b,he,hab.trans (Sym2.eq_swap),ha,hb⟩

 
theorem splice_cluster_cap (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y)
    (N M : ℕ) (hS : (cluster G ω x).Finite) (hN : (cluster G ω x).ncard ≤ N)
    (hC : (cluster G η y).Finite) (hM : (cluster G η y).ncard ≤ M) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    (cluster G (spliceField G S B e ω η) x).Finite ∧
      (cluster G (spliceField G S B e ω η) x).ncard ≤ N+M := by
  let S := cluster G ω x
  let B := cluster G (η ∩ internalEdges G Sᶜ) y
  have hBC : B ⊆ cluster G η y := fun _ hz => conn_mono G Set.inter_subset_left hz
  have hB : B.Finite := hC.subset hBC
  dsimp only
  rw [splice_cluster G ω η x y hy e a b he heη ha hb]
  refine ⟨hS.union hB,?_⟩
  exact (Set.ncard_union_le _ _).trans (Nat.add_le_add hN ((Set.ncard_le_ncard hBC hC).trans hM))



end SpliceSelection

section SpliceTrace
attribute [local instance] Classical.propDecidable Classical.decEq



theorem SpliceTrace.cluster_subset (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : cluster G ω x ⊆ cluster G ωf x := by
  induction h with
  | stop => exact Set.Subset.rfl
  | @step j i ω e a b rest ωf _ _ _ _ hy he hab ha hb ht ih =>
    apply Set.Subset.trans _ ih
    rw [splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb]
    exact Set.subset_union_left



end SpliceTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_GapCodes
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gap Codes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceWeight
attribute [local instance] Classical.propDecidable Classical.decEq


theorem domainBits_exchange (Q : Finset E) (M ω η : Set E) :
    domainBits Q (exchangeOn M ω η) =
      finiteExchange (domainBits Q M) (domainBits Q ω) (domainBits Q η) := by
  ext e
  simp only [mem_domainBits,exchangeOn,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,
    finiteExchange,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
  tauto



theorem spliceTupleWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (s : SpliceState E) : 0 ≤ spliceTupleWeight Q J p s := by
  exact mul_nonneg (bernoulliWeight_nonneg _ _ p)
    (Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p)

 
theorem spliceTupleWeight_exchange (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) (M : Set E) (i : ℕ) (hi : i ∈ J) :
    spliceTupleWeight Q J p (exchangeState M i s) = spliceTupleWeight Q J p s := by
  unfold spliceTupleWeight
  rw [← Finset.mul_prod_erase J (fun l =>
    bernoulliWeight Q (domainBits Q ((exchangeState M i s).2 l)) p) hi,
    ← Finset.mul_prod_erase J (fun l => bernoulliWeight Q (domainBits Q (s.2 l)) p) hi]
  have herase : (∏ l ∈ J.erase i,
      bernoulliWeight Q (domainBits Q ((exchangeState M i s).2 l)) p) =
      ∏ l ∈ J.erase i, bernoulliWeight Q (domainBits Q (s.2 l)) p := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [exchangeState_away _ _ _ _ (Finset.mem_erase.mp hl).1]
  rw [herase,exchangeState_first,exchangeState_at,← mul_assoc,← mul_assoc,
    domainBits_exchange,domainBits_exchange,
    bernoulliWeight_exchange _ _ _ _ (domainBits_subset Q s.1) (domainBits_subset Q (s.2 i)) p]

 
theorem SpliceExecution.weight (G : BondGraph V E) (x : V)
    (s s' : SpliceState E) (code : List (ℕ × E))
    (h : SpliceExecution G x s code s') (Q : Finset E) (J : Finset ℕ)
    (hJ : ∀ q ∈ code, q.1 ∈ J) (p : ℝ) :
    spliceTupleWeight Q J p s' = spliceTupleWeight Q J p s := by
  induction h with
  | nil => rfl
  | cons s s' s'' q code hstep hrest ih =>
    rw [ih (fun r hr => hJ r (List.mem_cons_of_mem _ hr))]
    obtain ⟨y,a,b,_,_,_,_,_,rfl⟩ := hstep
    exact spliceTupleWeight_exchange Q J p s _ q.1 (hJ q (List.mem_cons_self ..))



end SpliceWeight

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section InverseCodeMass
attribute [local instance] Classical.propDecidable Classical.decEq


theorem inverseCodeMass_le_harmonic (M : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    inverseCodeMass M L ≤ 1+2*L*(1+Real.log M) := by
  have hsum : ∑ l ∈ Finset.Icc 1 M, gapWeight L l ≤
      2*L*∑ l ∈ Finset.Icc 1 M, (l:ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    simpa only [gapWeight,div_eq_mul_inv] using min_le_right (1:ℝ) (2*L/l)
  have hh : ∑ l ∈ Finset.Icc 1 M, (l:ℝ)⁻¹ ≤ 1+Real.log M := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using
      harmonic_le_one_add_log M
  unfold inverseCodeMass
  have h := hsum.trans (mul_le_mul_of_nonneg_left hh (by positivity))
  linarith

 
theorem inverseCodeMass_le_log (M : ℕ) (L : ℝ) (hM : 2 ≤ M) (hL : 1 ≤ L) :
    inverseCodeMass M L ≤ 8*L*Real.log M := by
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
    norm_num at hh ⊢
    exact hh
  have hlog : (1:ℝ)/2 ≤ Real.log M := hlog2.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
  have hLl : L/2 ≤ L*Real.log M := by nlinarith
  have hbound := inverseCodeMass_le_harmonic M L (by linarith)
  nlinarith


theorem volume_contactInterval (K a : ℕ) (ha : a < K) :
    volume (contactInterval K a) = ENNReal.ofReal ((K:ℝ)⁻¹) := by
  have hK : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hleft : (a:ℝ)/K ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity,(div_le_one hK).mpr ?_⟩
    exact_mod_cast (Nat.le_of_lt ha)
  have hright : ((a+1:ℕ):ℝ)/K ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity,(div_le_one hK).mpr ?_⟩
    exact_mod_cast (show a+1 ≤ K by omega)
  let lo : unitInterval := ⟨_,hleft⟩
  let hi : unitInterval := ⟨_,hright⟩
  have heq : contactInterval K a = Set.Ico lo hi := rfl
  rw [heq,unitInterval.volume_Ico]
  congr 1
  dsimp only [lo,hi]
  push_cast
  field_simp
  ring



end InverseCodeMass

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_Replay
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteSpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq



theorem GraphSeparated.symm (G : BondGraph V E) (A B : Set V)
    (h : GraphSeparated G A B) : GraphSeparated G B A := by
  refine ⟨h.1.symm,?_⟩
  intro b hb a ha hab
  obtain ⟨e,he⟩ := hab
  exact h.2 a ha b hb ⟨e,he.trans (Sym2.eq_swap ..)⟩

theorem GraphSeparated.mono (G : BondGraph V E) {A B C D : Set V}
    (h : GraphSeparated G A B) (hC : C ⊆ A) (hD : D ⊆ B) : GraphSeparated G C D := by
  exact ⟨h.1.mono hC hD,fun c hc d hd => h.2 c (hC hc) d (hD hd)⟩

theorem GraphSeparated.no_shared_incidence (G : BondGraph V E) (A B : Set V)
    (h : GraphSeparated G A B) (e : E) (a b : V) (ha : a ∈ A) (hb : b ∈ B)
    (hea : a ∈ G e) (heb : b ∈ G e) : False := by
  have hne : a ≠ b := by
    rintro rfl
    exact Set.disjoint_left.mp h.1 ha hb
  exact h.2 a ha b hb ⟨e,(Sym2.mem_and_mem_iff hne).mp ⟨hea,heb⟩⟩

 

theorem slit_cluster_remove_remote (G : BondGraph V E) (η : Set E) (S H : Set V)
    (y : V) (hy : y ∉ S)
    (hsep : GraphSeparated G (cluster G (η ∩ internalEdges G Sᶜ) y) H) :
    cluster G (η ∩ internalEdges G (S \ H)ᶜ) y = cluster G (η ∩ internalEdges G Sᶜ) y := by
  apply Set.Subset.antisymm
  · intro v hv
    induction hv with
    | refl => exact conn_refl G _ y
    | @tail a b hya hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      have hbH : b ∉ H := fun hb => hsep.2 a ih b hb ⟨e,hab⟩
      have hbS : b ∉ S := by
        have hb := ((mem_internalEdges_of_ends G _ e a b hab).mp he.2).2
        exact fun h => hb ⟨h,hbH⟩
      have haS := slit_cluster_subset G S η y hy ih
      exact ih.tail ⟨e,⟨he.1,(mem_internalEdges_of_ends G _ e a b hab).mpr ⟨haS,hbS⟩⟩,hab⟩
  · exact fun _ h => conn_mono G
      (Set.inter_subset_inter_right _ (internalEdges_mono G (by
        intro v hv hvS
        exact hv hvS.1))) h

 

theorem spliceMask_remove_remote (G : BondGraph V E) (S B H : Set V) (e : E)
    (hsep : GraphSeparated G B H) : spliceMask G (S \ H) B e = spliceMask G S B e := by
  ext f
  simp only [spliceMask,Set.mem_insert_iff,Set.mem_ofPred_eq]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨⟨b,hb,hbf⟩,hi⟩
    refine ⟨⟨b,hb,hbf⟩,?_⟩
    intro v hv hvS
    have hvH : v ∉ H := fun hh => hsep.no_shared_incidence G B H f b v hb hh hbf hv
    exact hi v hv ⟨hvS,hvH⟩
  · rintro ⟨hb,hi⟩
    exact ⟨hb,fun v hv h => hi v hv h.1⟩

 
theorem spliceMask_incident (G : BondGraph V E) (S B : Set V) (e : E)
    (b : V) (hb : b ∈ B) (heb : b ∈ G e) :
    ∀ f ∈ spliceMask G S B e, ∃ v ∈ B, v ∈ G f := by
  intro f hf
  rcases Set.mem_insert_iff.mp hf with rfl | hf
  · exact ⟨b,hb,heb⟩
  · exact hf.1



end RemoteSpliceGeometry

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteReplay
attribute [local instance] Classical.propDecidable Classical.decEq



theorem SpliceTrace.replay_eq (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : replaySplice G x η y steps ω = ωf := by
  induction h with
  | stop => rfl
  | step => assumption

 

theorem SpliceTrace.remote_replay (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (H : Set V) (ω₀ : Set E)
    (hroot : cluster G ω₀ x = cluster G ω x \ H)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω x) H)
    (hzH : y k ∉ H) :
    SpliceTrace G x η y k j ω₀ steps (replaySplice G x η y steps ω₀) ∧
      cluster G (replaySplice G x η y steps ω₀) x = cluster G ωf x \ H ∧
      replayMasks G x η y steps ω₀ = replayMasks G x η y steps ω ∧
      replayContacts G x η y steps ω₀ = replayContacts G x η y steps ω := by
  induction h generalizing ω₀ with
  | stop j ω hs =>
    refine ⟨SpliceTrace.stop j ω₀ ?_,hroot,rfl,rfl⟩
    rw [hroot]
    exact ⟨hs,hzH⟩
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    let S₀ := cluster G ω₀ x
    let B₀ := cluster G (η i ∩ internalEdges G S₀ᶜ) (y i)
    let ω₀' := spliceField G S₀ B₀ e ω₀ (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hBo : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hretain : cluster G ω' x ⊆ cluster G ωf x := ht.cluster_subset G x η y k i ω' ωf rest
    have hBT : B ⊆ cluster G ωf x \ S := by
      intro v hv
      refine ⟨hretain ?_,hBo hv⟩
      rw [hC]
      exact Or.inr hv
    have hsepB : GraphSeparated G B H := hsep.mono G hBT Set.Subset.rfl
    have hBB : B₀ = B := by
      dsimp only [B₀,S₀]
      rw [hroot]
      exact slit_cluster_remove_remote G (η i) S H (y i) hy hsepB
    have haH : a ∉ H := fun hh => hsepB.2 b hb a hh ⟨e,hab.trans (Sym2.eq_swap ..)⟩
    have ha₀ : a ∈ S₀ := by rw [show S₀ = S \ H from hroot]; exact ⟨ha,haH⟩
    have hy₀ : y i ∉ S₀ := by rw [show S₀ = S \ H from hroot]; exact fun h => hy h.1
    have hb₀ : b ∈ B₀ := hBB.symm ▸ hb
    have hC₀ : cluster G ω₀' x = S₀ ∪ B₀ :=
      splice_cluster G ω₀ (η i) x (y i) hy₀ e a b hab he ha₀ hb₀
    have hroot' : cluster G ω₀' x = cluster G ω' x \ H := by
      rw [hC₀,hC,hBB,show S₀ = S \ H from hroot]
      ext v
      constructor
      · rintro (⟨hv,hvH⟩ | hv)
        · exact ⟨Or.inl hv,hvH⟩
        · exact ⟨Or.inr hv,fun hvH => Set.disjoint_left.mp hsepB.1 hv hvH⟩
      · rintro ⟨hv,hvH⟩
        exact hv.elim (fun h => Or.inl ⟨h,hvH⟩) Or.inr
    have hsep' : GraphSeparated G (cluster G ωf x \ cluster G ω' x) H := by
      apply hsep.mono G _ Set.Subset.rfl
      intro v hv
      refine ⟨hv.1,fun h => hv.2 ?_⟩
      rw [hC]
      exact Or.inl h
    obtain ⟨ht₀,hfinal,hmasks,hcontacts⟩ := ih ω₀' hroot' hsep'
    have hn₀ : y k ∉ S₀ := by rw [show S₀ = S \ H from hroot]; exact fun h => hn h.1
    have hmax₀ : ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) S₀ := by
      intro l hil hlk
      apply (hmax l hil hlk).mono Set.Subset.rfl
      rw [show S₀ = S \ H from hroot]
      exact Set.sdiff_subset
    have hmask : spliceMask G S₀ B₀ e = spliceMask G S B e := by
      rw [hBB,show S₀ = S \ H from hroot,spliceMask_remove_remote G S B H e hsepB]
    refine ⟨SpliceTrace.step j i ω₀ e a b rest _ hn₀ hji hik hmax₀ hy₀ he hab ha₀ hb₀ ht₀,
      hfinal,?_,?_⟩
    · change (i,spliceMask G S₀ B₀ e)::replayMasks G x η y rest ω₀' =
      (i,spliceMask G S B e)::replayMasks G x η y rest ω'
      rw [hmask,hmasks]
    · change contactSet G (η i) B₀::replayContacts G x η y rest ω₀' =
        contactSet G (η i) B::replayContacts G x η y rest ω'
      rw [hBB,hcontacts]

end RemoteReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeterministicReplay
attribute [local instance] Classical.propDecidable Classical.decEq



theorem followsContactRule_cons (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (choose : ℕ → Set E → E) (i : ℕ) (e : E)
    (rest : List (ℕ × E)) (ω : Set E) :
    FollowsContactRule G x η y choose ((i,e)::rest) ω ↔
      choose i (contactSet G (η i)
        (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))) = e ∧
      FollowsContactRule G x η y choose rest
        (spliceField G (cluster G ω x)
          (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i)) := by
  simp only [FollowsContactRule,replayContacts,List.forall₂_cons]



theorem SpliceTrace.seeded_unique (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ω₁ ω₂ : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η y k j ω c₁ ω₁)
    (h₂ : SpliceTrace G x η y k j ω c₂ ω₂) (choose : ℕ → Set E → E)
    (hc₁ : FollowsContactRule G x η y choose c₁ ω)
    (hc₂ : FollowsContactRule G x η y choose c₂ ω) : c₁ = c₂ ∧ ω₁ = ω₂ := by
  induction h₁ generalizing c₂ ω₂ with
  | stop j ω hs =>
    cases h₂ with
    | stop => exact ⟨rfl,rfl⟩
    | step _ _ _ _ _ _ _ _ hn => exact (hn hs).elim
  | @step j i ω e a b rest ω₁ hn hji hik hmax hy he hab ha hb ht ih =>
    cases h₂ with
    | stop _ _ hs => exact (hn hs).elim
    | step _ l _ f c d tail ω₂ hn₂ hjl hlk hmax₂ hy₂ hf hcd hc hd ht₂ =>
      have haC : a ∈ cluster G (η i) (y i) :=
        (edge_cluster_sides G (η i) (y i) he hab).mpr (conn_mono G Set.inter_subset_left hb)
      have hcC : c ∈ cluster G (η l) (y l) :=
        (edge_cluster_sides G (η l) (y l) hf hcd).mpr (conn_mono G Set.inter_subset_left hd)
      have hil : i = l := by
        rcases lt_trichotomy i l with hil | hil | hli
        · exact (Set.disjoint_left.mp (hmax l hil hlk) hcC hc).elim
        · exact hil
        · exact (Set.disjoint_left.mp (hmax₂ i hli hik) haC ha).elim
      subst l
      obtain ⟨hec,hrest⟩ := (followsContactRule_cons G x η y choose i e rest ω).mp hc₁
      obtain ⟨hfc,htail⟩ := (followsContactRule_cons G x η y choose i f tail ω).mp hc₂
      have hef : e = f := hec.symm.trans hfc
      rw [← hef] at ht₂ htail ⊢
      obtain ⟨hcodes,houts⟩ := ih ω₂ tail ht₂ hrest htail
      exact ⟨congrArg (List.cons (i,e)) hcodes,houts⟩

end DeterministicReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceMaskSupport
attribute [local instance] Classical.propDecidable Classical.decEq


theorem SpliceTrace.masks_incident (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ f ∈ maskUnion (replayMasks G x η y steps ω),
      ∃ b ∈ cluster G ωf x \ cluster G ω x, b ∈ G f := by
  induction h with
  | stop => simp [replayMasks]
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hB : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hretain := ht.cluster_subset G x η y k i ω' ωf rest
    intro f hf
    change f ∈ maskUnion ((i,spliceMask G S B e)::replayMasks G x η y rest ω') at hf
    rw [maskUnion_cons] at hf
    rcases hf with hf | hf
    · obtain ⟨v,hv,hvf⟩ := spliceMask_incident G S B e b hb (by simp [hab]) f hf
      refine ⟨v,⟨hretain ?_,hB hv⟩,hvf⟩
      rw [hC]
      exact Or.inr hv
    · obtain ⟨v,hv,hvf⟩ := ih f hf
      refine ⟨v,⟨hv.1,fun h => hv.2 ?_⟩,hvf⟩
      rw [hC]
      exact Or.inl h

 
theorem replaySplice_off_masks (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (steps : List (ℕ × E)) (ω : Set E) (f : E)
    (hf : f ∉ maskUnion (replayMasks G x η y steps ω)) :
    f ∈ replaySplice G x η y steps ω ↔ f ∈ ω := by
  induction steps generalizing ω with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    simp only [replayMasks,maskUnion_cons,Set.mem_union,not_or] at hf
    change f ∈ replaySplice G x η y rest _ ↔ f ∈ ω
    rw [ih _ hf.2]
    simp only [spliceField,mem_exchangeOn,ite_eq_right hf.1]

 
theorem SpliceTrace.masks_disjoint (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    Disjoint (maskUnion (replayMasks G x η₁ y₁ c₁ ω₁))
      (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) := by
  apply Set.disjoint_left.mpr
  intro f hf₁ hf₂
  obtain ⟨a,ha,hea⟩ := h₁.masks_incident G x η₁ y₁ k j₁ ω₁ ωf c₁ f hf₁
  obtain ⟨b,hb,heb⟩ := h₂.masks_incident G x η₂ y₂ k j₂ ω₂ ωf c₂ f hf₂
  exact hsep.no_shared_incidence G _ _ f a b ha hb hea heb

 

theorem conn_delete_rootBridge (G : BondGraph V E) (ω η : Set E) (x z : V)
    (hη : η ⊆ ω) (e : E) (a b : V) (hab : G e = s(a,b))
    (hb : b ∉ cluster G (ω \ {e}) x) (hz : z ∈ cluster G (ω \ {e}) x)
    (hxz : Conn G η x z) : Conn G (η \ {e}) x z := by
  have hc : Conn G (insert e (η \ {e})) x z := conn_mono G (by
    intro f hf
    by_cases hfe : f = e
    · exact Or.inl hfe
    · exact Or.inr ⟨hf,hfe⟩) hxz
  have hs : η \ {e} ⊆ ω \ {e} := Set.sdiff_subset_sdiff_left hη
  rw [conn_insert_iff G _ e a b x z hab] at hc
  rcases hc with hc | ⟨_,hc⟩ | ⟨hc,_⟩
  · exact hc
  · exact (hb (hz.trans (conn_symm G _ (conn_mono G hs hc)))).elim
  · exact (hb (conn_mono G hs hc)).elim

 
theorem cluster_double_cut (G : BondGraph V E) (ω : Set E) (x : V) (e f : E)
    (a b : V) (hab : G f = s(a,b)) (hb : b ∉ cluster G (ω \ {f}) x) :
    cluster G ((ω \ {e}) \ {f}) x = cluster G (ω \ {e}) x ∩ cluster G (ω \ {f}) x := by
  apply Set.Subset.antisymm
  · intro v hv
    exact ⟨conn_mono G Set.sdiff_subset hv,
      conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩) hv⟩
  · intro v hv
    exact conn_delete_rootBridge G ω (ω \ {e}) x v Set.sdiff_subset f a b hab hb hv.2 hv.1

end TraceMaskSupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointRoot
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem mask_not_crossing_remote (G : BondGraph V E) (U : Set E) (A B : Set V)
    (hU : ∀ e ∈ U, ∃ v ∈ B, v ∈ G e) (hBA : B ⊆ A)
    (e : E) (a b : V) (hab : G e = s(a,b)) (haB : a ∉ B) (hbA : b ∉ A) : e ∉ U := by
  intro he
  obtain ⟨v,hv,hve⟩ := hU e he
  have hvab : v = a ∨ v = b := by simpa only [hab,Sym2.mem_iff] using hve
  rcases hvab with rfl | rfl
  · exact haB hv
  · exact hbA (hBA hv)

 

theorem exchange_patch_symm (U₁ U₂ ω₁ ω₂ ωf : Set E)
    (hdis : Disjoint U₁ U₂)
    (h₁ : ∀ e ∉ U₁, e ∈ ω₁ ↔ e ∈ ωf)
    (h₂ : ∀ e ∉ U₂, e ∈ ω₂ ↔ e ∈ ωf) :
    exchangeOn U₂ ω₁ ω₂ = exchangeOn U₁ ω₂ ω₁ := by
  ext e
  by_cases he₁ : e ∈ U₁
  · have he₂ : e ∉ U₂ := fun h => Set.disjoint_left.mp hdis he₁ h
    simp only [mem_exchangeOn,ite_eq_right he₂,ite_eq_left he₁]
  · by_cases he₂ : e ∈ U₂
    · simp only [mem_exchangeOn,ite_eq_left he₂,ite_eq_right he₁]
    · simp only [mem_exchangeOn,ite_eq_right he₁,ite_eq_right he₂]
      exact (h₁ e he₁).trans (h₂ e he₂).symm

 

theorem SpliceTrace.joint_root (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ i₁ i₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (e₁ e₂ : E) (r₁ r₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ ((i₁,e₁)::r₁) ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ ((i₂,e₂)::r₂) ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    cluster G (exchangeOn (maskUnion (replayMasks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂)) ω₁ ω₂) x =
      cluster G ω₁ x ∩ cluster G ω₂ x := by
  let A₁ := cluster G ω₁ x
  let A₂ := cluster G ω₂ x
  let B₁ := cluster G ωf x \ A₁
  let B₂ := cluster G ωf x \ A₂
  let U₁ := maskUnion (replayMasks G x η₁ y₁ ((i₁,e₁)::r₁) ω₁)
  let U₂ := maskUnion (replayMasks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂)
  let ω₀ := exchangeOn U₂ ω₁ ω₂
  have hsub₁ := h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)
  have hsub₂ := h₂.cluster_subset G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)
  have hBA₁ : B₁ ⊆ A₂ := by
    intro v hv
    by_contra hn
    exact Set.disjoint_left.mp hsep.1 hv ⟨hv.1,hn⟩
  have hBA₂ : B₂ ⊆ A₁ := by
    intro v hv
    by_contra hn
    exact Set.disjoint_left.mp hsep.1 ⟨hv.1,hn⟩ hv
  have hU₁ : ∀ e ∈ U₁, ∃ v ∈ B₁, v ∈ G e :=
    h₁.masks_incident G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)
  have hU₂ : ∀ e ∈ U₂, ∃ v ∈ B₂, v ∈ G e :=
    h₂.masks_incident G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)
  have hdis : Disjoint U₁ U₂ := h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf
    ((i₁,e₁)::r₁) ((i₂,e₂)::r₂) h₂ hsep
  have hoff₁ : ∀ e ∉ U₁, e ∈ ω₁ ↔ e ∈ ωf := by
    intro e he
    rw [← h₁.replay_eq G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)]
    exact (replaySplice_off_masks G x η₁ y₁ ((i₁,e₁)::r₁) ω₁ e he).symm
  have hoff₂ : ∀ e ∉ U₂, e ∈ ω₂ ↔ e ∈ ωf := by
    intro e he
    rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)]
    exact (replaySplice_off_masks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂ e he).symm
  have hsym : ω₀ = exchangeOn U₁ ω₂ ω₁ := exchange_patch_symm U₁ U₂ ω₁ ω₂ ωf hdis hoff₁ hoff₂
  have hcut₁ := h₁.head_cut G x η₁ y₁ k j₁ i₁ ω₁ ωf e₁ r₁
  have hcut₂ := h₂.head_cut G x η₂ y₂ k j₂ i₂ ω₂ ωf e₂ r₂
  obtain ⟨a,b,hab,_,hb,_⟩ := openMarkedPivotal_oriented G ωf {y₂ k} x
    (h₂.seams_pivotal G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂) (i₂,e₂) (by simp))
  have hdouble : cluster G ((ωf \ {e₁}) \ {e₂}) x = A₁ ∩ A₂ := by
    rw [cluster_double_cut G ωf x e₁ e₂ a b hab hb,hcut₁,hcut₂]
  change cluster G ω₀ x = A₁ ∩ A₂
  apply Set.Subset.antisymm
  · intro v hv
    induction hv with
    | refl => exact ⟨conn_refl G _ x,conn_refl G _ x⟩
    | @tail a b hxa hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      constructor
      · by_contra hb
        have hno := mask_not_crossing_remote G U₂ A₁ B₂ hU₂ hBA₂ e a b hab
          (fun hh => hh.2 ih.2) hb
        have he₁ : e ∈ ω₁ := by simpa only [ω₀,mem_exchangeOn,ite_eq_right hno] using he
        exact hb ((edge_cluster_sides G ω₁ x he₁ hab).mp ih.1)
      · by_contra hb
        have hno := mask_not_crossing_remote G U₁ A₂ B₁ hU₁ hBA₁ e a b hab
          (fun hh => hh.2 ih.1) hb
        have he₂ : e ∈ ω₂ := by simpa only [hsym,mem_exchangeOn,ite_eq_right hno] using he
        exact hb ((edge_cluster_sides G ω₂ x he₂ hab).mp ih.2)
  · intro v hv
    have hc : Conn G ((ωf \ {e₁}) \ {e₂}) x v := by
      change v ∈ cluster G ((ωf \ {e₁}) \ {e₂}) x
      rw [hdouble]
      exact hv
    have hr := conn_restrict_cluster G ((ωf \ {e₁}) \ {e₂}) x (mem_cluster_self G _ x) hc
    apply conn_mono G _ hr
    intro e he
    have hi : e ∈ internalEdges G (A₁ ∩ A₂) := by
      simpa only [hdouble] using he.2
    have hno : e ∉ U₂ := by
      intro hu
      obtain ⟨b,hb,heb⟩ := hU₂ e hu
      exact hb.2 (hi b heb).2
    have he₁ : e ∈ ω₁ := (h₁.internal_agreement G x η₁ y₁ k j₁ ω₁ ωf
      ((i₁,e₁)::r₁) e (fun a ha => (hi a ha).1)).mp he.1.1.1
    simpa only [ω₀,mem_exchangeOn,ite_eq_right hno] using he₁

end JointRoot

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MaskExecution
attribute [local instance] Classical.propDecidable Classical.decEq


theorem exchangeState_patchFirst (U τ M : Set E) (i : ℕ) (s : SpliceState E)
    (hdis : Disjoint M U) :
    exchangeState M i (patchFirst U τ s) = patchFirst U τ (exchangeState M i s) := by
  apply Prod.ext
  · ext e
    by_cases heM : e ∈ M
    · have heU : e ∉ U := fun he => Set.disjoint_left.mp hdis heM he
      simp only [exchangeState,patchFirst,mem_exchangeOn,ite_eq_left heM,ite_eq_right heU]
    · by_cases heU : e ∈ U <;>
      simp only [exchangeState,patchFirst,mem_exchangeOn,ite_eq_right heM,heU,if_true,if_false]
  · funext l
    by_cases hli : l = i
    · subst l
      ext e
      by_cases heM : e ∈ M
      · have heU : e ∉ U := fun he => Set.disjoint_left.mp hdis heM he
        simp only [exchangeState,patchFirst,Function.update_self,mem_exchangeOn,ite_eq_left heM,ite_eq_right heU]
      · simp only [exchangeState,patchFirst,Function.update_self,mem_exchangeOn,ite_eq_right heM]
    · simp only [exchangeState,patchFirst,Function.update_of_ne hli]

 

theorem runMasks_patchFirst (ms : List (ℕ × Set E)) (U τ : Set E) (s : SpliceState E)
    (hdis : Disjoint (maskUnion ms) U) :
    runMasks ms (patchFirst U τ s) = patchFirst U τ (runMasks ms s) := by
  induction ms generalizing s with
  | nil => rfl
  | cons q ms ih =>
    obtain ⟨i,M⟩ := q
    rw [maskUnion_cons,Set.disjoint_union_left] at hdis
    simp only [runMasks]
    rw [exchangeState_patchFirst U τ M i s hdis.1,ih _ hdis.2]



theorem runMasks_weight (ms : List (ℕ × Set E)) (s : SpliceState E)
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (hJ : ∀ q ∈ ms, q.1 ∈ J) :
    spliceTupleWeight Q J p (runMasks ms s) = spliceTupleWeight Q J p s := by
  induction ms generalizing s with
  | nil => rfl
  | cons q ms ih =>
    obtain ⟨i,M⟩ := q
    rw [runMasks,ih _ (fun q hq => hJ q (List.mem_cons_of_mem _ hq))]
    exact spliceTupleWeight_exchange Q J p s M i (hJ (i,M) (List.mem_cons_self ..))

 

theorem SpliceTrace.joint_replay_state (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let m₁ := replayMasks G x η₁ y₁ c₁ ω₁
    let m₂ := replayMasks G x η₂ y₂ c₂ ω₂
    let ω₀ := exchangeOn (maskUnion m₂) ω₁ ω₂
    runMasks m₁ (ω₀,η₁) = (ω₂,(runMasks m₁ (ω₁,η₁)).2) := by
  intro m₁ m₂ ω₀
  have hdis := h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep
  have hroot := h₁.runMasks_first G x η₁ y₁ k j₁ ω₁ ωf c₁ η₁ (by intros; rfl)
  have hpatch : exchangeOn (maskUnion m₂) ωf ω₂ = ω₂ := by
    ext e
    by_cases he : e ∈ maskUnion m₂
    · simp only [mem_exchangeOn,ite_eq_left he]
    · simp only [mem_exchangeOn,ite_eq_right he]
      rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf c₂]
      exact replaySplice_off_masks G x η₂ y₂ c₂ ω₂ e he
  change runMasks m₁ (patchFirst (maskUnion m₂) ω₂ (ω₁,η₁)) = _
  rw [runMasks_patchFirst m₁ _ ω₂ _ hdis]
  change (exchangeOn (maskUnion m₂) (runMasks m₁ (ω₁,η₁)).1 ω₂,_) = _
  rw [hroot,hpatch]

end MaskExecution

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.endpoint_not_mem_of_ne_nil (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (hc : c ≠ []) : y k ∉ cluster G ω x := by
  cases h with
  | stop => exact (hc rfl).elim
  | step _ _ _ _ _ _ _ _ hn => exact hn

 

theorem SpliceTrace.joint_virtual (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let ω₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂
    SpliceTrace G x η₁ y₁ k j₁ ω₀ c₁ ω₂ ∧
      replayMasks G x η₁ y₁ c₁ ω₀ = replayMasks G x η₁ y₁ c₁ ω₁ ∧
      replayContacts G x η₁ y₁ c₁ ω₀ = replayContacts G x η₁ y₁ c₁ ω₁ := by
  intro ω₀
  have hroot' : cluster G ω₀ x = cluster G ω₁ x ∩ cluster G ω₂ x := by
    cases c₁ with
    | nil => exact (hc₁ rfl).elim
    | cons q r₁ =>
      obtain ⟨i₁,e₁⟩ := q
      cases c₂ with
      | nil => exact (hc₂ rfl).elim
      | cons q r₂ =>
        obtain ⟨i₂,e₂⟩ := q
        exact h₁.joint_root G x η₁ η₂ y₁ y₂ k j₁ j₂ i₁ i₂ ω₁ ω₂ ωf e₁ e₂ r₁ r₂ h₂ hsep
  let H := cluster G ωf x \ cluster G ω₂ x
  have hroot : cluster G ω₀ x = cluster G ω₁ x \ H := by
    rw [hroot']
    ext v
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,fun hh => hh.2 h2⟩
    · rintro ⟨h1,h2⟩
      refine ⟨h1,?_⟩
      by_contra hn
      exact h2 ⟨h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf c₁ h1,hn⟩
  have hz : y₁ k ∉ H := fun hz => Set.disjoint_left.mp hsep.1
    ⟨h₁.endpoint G x η₁ y₁ k j₁ ω₁ ωf c₁,
      h₁.endpoint_not_mem_of_ne_nil G x η₁ y₁ k j₁ ω₁ ωf c₁ hc₁⟩ hz
  obtain ⟨ht,hout,hm,hcontacts⟩ := h₁.remote_replay G x η₁ y₁ k j₁ ω₁ ωf c₁ H ω₀ hroot hsep hz
  have hf := ht.runMasks_first G x η₁ y₁ k j₁ ω₀ (replaySplice G x η₁ y₁ c₁ ω₀) c₁ η₁
    (by intros; rfl)
  rw [hm] at hf
  have hs := h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep
  have heq : replaySplice G x η₁ y₁ c₁ ω₀ = ω₂ := hf.symm.trans (congrArg Prod.fst hs)
  rw [heq] at ht
  exact ⟨ht,hm,hcontacts⟩

 

theorem joint_restore_seeded_unique (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (choose₁ choose₂ : ℕ → Set E → E)
    (k j₁ j₂ : ℕ) (ω₁ ω₂ ωf σ₁ σ₂ σf : Set E)
    (c₁ c₂ d₁ d₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (g₁ : SpliceTrace G x η₁ y₁ k j₁ σ₁ d₁ σf)
    (g₂ : SpliceTrace G x η₂ y₂ k j₂ σ₂ d₂ σf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ []) (hd₁ : d₁ ≠ []) (hd₂ : d₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (gsep : GraphSeparated G (cluster G σf x \ cluster G σ₁ x)
      (cluster G σf x \ cluster G σ₂ x))
    (hr₁ : FollowsContactRule G x η₁ y₁ choose₁ c₁ ω₁)
    (hr₂ : FollowsContactRule G x η₂ y₂ choose₂ c₂ ω₂)
    (gr₁ : FollowsContactRule G x η₁ y₁ choose₁ d₁ σ₁)
    (gr₂ : FollowsContactRule G x η₂ y₂ choose₂ d₂ σ₂)
    (hrestore : exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂ =
      exchangeOn (maskUnion (replayMasks G x η₂ y₂ d₂ σ₂)) σ₁ σ₂) :
    c₁ = d₁ ∧ c₂ = d₂ ∧ ωf = σf ∧
      (runMasks (replayMasks G x η₁ y₁ c₁ ω₁) (ω₁,η₁)).2 =
        (runMasks (replayMasks G x η₁ y₁ d₁ σ₁) (σ₁,η₁)).2 ∧
      (runMasks (replayMasks G x η₂ y₂ c₂ ω₂) (ω₂,η₂)).2 =
        (runMasks (replayMasks G x η₂ y₂ d₂ σ₂) (σ₂,η₂)).2 := by
  let ω₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂
  let σ₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ d₂ σ₂)) σ₁ σ₂
  obtain ⟨ht,hm,hcontact⟩ := h₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep
  obtain ⟨gt,gm,gcontact⟩ := g₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ σ₁ σ₂ σf d₁ d₂ g₂ hd₁ hd₂ gsep
  have hrc : FollowsContactRule G x η₁ y₁ choose₁ c₁ ω₀ := by
    unfold FollowsContactRule at hr₁ ⊢
    rw [hcontact]
    exact hr₁
  have grc : FollowsContactRule G x η₁ y₁ choose₁ d₁ σ₀ := by
    unfold FollowsContactRule at gr₁ ⊢
    rw [gcontact]
    exact gr₁
  change SpliceTrace G x η₁ y₁ k j₁ σ₀ d₁ σ₂ at gt
  change replayMasks G x η₁ y₁ c₁ ω₀ = _ at hm
  change replayMasks G x η₁ y₁ d₁ σ₀ = _ at gm
  have h00 : ω₀ = σ₀ := hrestore
  rw [← h00] at gt grc
  obtain ⟨hcode₁,hω₂⟩ := ht.seeded_unique G x η₁ y₁ k j₁ ω₀ ω₂ σ₂ c₁ d₁ gt choose₁ hrc grc
  rw [← hω₂] at g₂ gr₂
  obtain ⟨hcode₂,hout⟩ := h₂.seeded_unique G x η₂ y₂ k j₂ ω₂ ωf σf c₂ d₂ g₂ choose₂ hr₂ gr₂
  refine ⟨hcode₁,hcode₂,hout,?_,?_⟩
  · have hs := congrArg Prod.snd (h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep)
    have gs := congrArg Prod.snd (g₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ σ₁ σ₂ σf d₁ d₂
      (hω₂ ▸ g₂) gsep)
    change (runMasks _ (ω₀,η₁)).2 = _ at hs
    change (runMasks _ (σ₀,η₁)).2 = _ at gs
    rw [← hs,← gs,← hm,← gm,h00,hcode₁]
  · rw [hcode₂,hω₂]

end JointReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointWeight
attribute [local instance] Classical.propDecidable Classical.decEq



theorem jointTupleWeight_nonneg (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (p : unitInterval) (s : JointSpliceState E) : 0 ≤ jointTupleWeight Q J₁ J₂ p s := by
  exact mul_nonneg (spliceTupleWeight_nonneg Q J₁ p (s.1,s.2.1))
    (Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p)

theorem replayMasks_indices_mem (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (J : Finset ℕ)
    (hJ : ∀ q ∈ c, q.1 ∈ J) : ∀ q ∈ replayMasks G x η y c ω, q.1 ∈ J := by
  intro q hq
  have hq' : q.1 ∈ (replayMasks G x η y c ω).map Prod.fst := List.mem_map_of_mem hq
  rw [replayMasks_indices G x η y c ω] at hq'
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hq'
  exact he ▸ hJ r hr

 

theorem SpliceTrace.joint_weight (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (hJ₁ : ∀ q ∈ c₁, q.1 ∈ J₁) (hJ₂ : ∀ q ∈ c₂, q.1 ∈ J₂) :
    let m₁ := replayMasks G x η₁ y₁ c₁ ω₁
    let m₂ := replayMasks G x η₂ y₂ c₂ ω₂
    let ω₀ := exchangeOn (maskUnion m₂) ω₁ ω₂
    jointTupleWeight Q J₁ J₂ p (ωf,(runMasks m₁ (ω₁,η₁)).2,(runMasks m₂ (ω₂,η₂)).2) =
      jointTupleWeight Q J₁ J₂ p (ω₀,η₁,η₂) := by
  intro m₁ m₂ ω₀
  have hw₁ := runMasks_weight m₁ (ω₀,η₁) Q J₁ p
    (replayMasks_indices_mem G x η₁ y₁ c₁ ω₁ J₁ hJ₁)
  rw [h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep] at hw₁
  have hw₂ := runMasks_weight m₂ (ω₂,η₂) Q J₂ p
    (replayMasks_indices_mem G x η₂ y₂ c₂ ω₂ J₂ hJ₂)
  unfold spliceTupleWeight at hw₁ hw₂
  rw [h₂.runMasks_first G x η₂ y₂ k j₂ ω₂ ωf c₂ η₂ (by intros; rfl)] at hw₂
  unfold jointTupleWeight
  dsimp only at hw₁ hw₂ ⊢
  calc
    _ = (bernoulliWeight Q (domainBits Q ωf) p *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q ((runMasks m₂ (ω₂,η₂)).2 i)) p) *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p := by ring
    _ = (bernoulliWeight Q (domainBits Q ω₂) p *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (η₂ i)) p) *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p := by rw [hw₂]
    _ = (bernoulliWeight Q (domainBits Q ω₂) p *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p) *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (η₂ i)) p := by ring
    _ = _ := by rw [hw₁]

end JointWeight

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_ReferenceLaws
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectorySupport
attribute [local instance] Classical.propDecidable Classical.decEq



theorem SpliceTrace.trajectory_hits (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (hc : c ≠ []) :
    (cluster G ω x ∩ trajectoryUnion G η y k).Nonempty := by
  cases h with
  | stop => exact (hc rfl).elim
  | step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht =>
    exact ⟨a,ha,(mem_trajectoryUnion G η y k a).mpr ⟨i,by omega,hik,
      (edge_cluster_sides G (η i) (y i) he hab).mpr (conn_mono G Set.inter_subset_left hb)⟩⟩

 

theorem SpliceTrace.added_finite_cap (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M) :
    (cluster G ωf x \ cluster G ω x).Finite ∧ (cluster G ωf x \ cluster G ω x).ncard ≤ k*M := by
  obtain ⟨hf,hc⟩ := trajectoryUnion_finite_cap G η y k M hcaps
  have hs := h.added_subset_trajectory G x η y k j ω ωf c
  exact ⟨hf.subset hs,(Set.ncard_le_ncard hs hf).trans hc⟩

end TrajectorySupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointReferenceEvent
attribute [local instance] Classical.propDecidable Classical.decEq

theorem SpliceTrace.joint_restored_field_symm (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 =
      (jointRestored G x η₂ η₁ y₁ ω₂ ω₁ c₁).1 := by
  apply exchange_patch_symm _ _ ω₁ ω₂ ωf
    (h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep)
  · intro e he
    rw [← h₁.replay_eq G x η₁ y₁ k j₁ ω₁ ωf c₁]
    exact (replaySplice_off_masks G x η₁ y₁ c₁ ω₁ e he).symm
  · intro e he
    rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf c₂]
    exact (replaySplice_off_masks G x η₂ y₂ c₂ ω₂ e he).symm

theorem SpliceTrace.joint_restored_root (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x =
      cluster G ω₁ x ∩ cluster G ω₂ x := by
  cases c₁ with
  | nil => exact (hc₁ rfl).elim
  | cons q r₁ =>
    obtain ⟨i₁,e₁⟩ := q
    cases c₂ with
    | nil => exact (hc₂ rfl).elim
    | cons q r₂ =>
      obtain ⟨i₂,e₂⟩ := q
      exact h₁.joint_root G x η₁ η₂ y₁ y₂ k j₁ j₂ i₁ i₂ ω₁ ω₂ ωf e₁ e₂ r₁ r₂ h₂ hsep

 

theorem SpliceTrace.joint_trajectory_hits (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let A := cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x
    (A ∩ trajectoryUnion G η₁ y₁ k).Nonempty ∧ (A ∩ trajectoryUnion G η₂ y₂ k).Nonempty := by
  intro A
  have hv₁ := (h₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep).1
  have hv₂ := (h₂.joint_virtual G x η₂ η₁ y₂ y₁ k j₂ j₁ ω₂ ω₁ ωf c₂ c₁ h₁ hc₂ hc₁
    (hsep.symm G _ _)).1
  refine ⟨hv₁.trajectory_hits G x η₁ y₁ k j₁ _ ω₂ c₁ hc₁,?_⟩
  change (cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x ∩ _).Nonempty
  rw [h₁.joint_restored_field_symm G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep]
  exact hv₂.trajectory_hits G x η₂ y₂ k j₂ _ ω₁ c₂ hc₂

 

theorem SpliceTrace.joint_restored_size (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ n M : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (hf : (cluster G ω₁ x).Finite) (hn : n ≤ (cluster G ω₁ x).ncard)
    (h2n : (cluster G ω₁ x).ncard < 2*n)
    (hcap₂ : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η₂ i) (y₂ i)).Finite ∧ (cluster G (η₂ i) (y₂ i)).ncard ≤ M) :
    let A := cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x
    A.Finite ∧ n-k*M ≤ A.ncard ∧ A.ncard < 2*n := by
  intro A
  have hA : A = cluster G ω₁ x ∩ cluster G ω₂ x :=
    h₁.joint_restored_root G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep
  have hdiff : A = cluster G ω₁ x \ (cluster G ωf x \ cluster G ω₂ x) := by
    rw [hA]
    ext v
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,fun hh => hh.2 h2⟩
    · rintro ⟨h1,h2⟩
      refine ⟨h1,?_⟩
      by_contra hn
      exact h2 ⟨h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf c₁ h1,hn⟩
  obtain ⟨hBfin,hBcap⟩ := h₂.added_finite_cap G x η₂ y₂ k j₂ M ω₂ ωf c₂ hcap₂
  have hlower := Set.ncard_le_ncard_sdiff_add_ncard (cluster G ω₁ x)
    (cluster G ωf x \ cluster G ω₂ x) hBfin
  rw [← hdiff] at hlower
  refine ⟨hA ▸ hf.inter_of_left _,by omega,?_⟩
  rw [hA]
  exact (Set.ncard_inter_le_ncard_left _ _ hf).trans_lt h2n

end JointReferenceEvent

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallHanging
attribute [local instance] Classical.propDecidable Classical.decEq


theorem mem_hangingSide_iff_pivotal (G : BondGraph V E) (ω : Set E) (x z : V)
    (e : E) (he : e ∈ ω) : z ∈ hangingSide G ω x e ↔ OpenMarkedPivotal G ω {z} x e := by
  constructor
  · rintro ⟨hz,hn⟩
    exact ⟨he,⟨z,rfl,hz⟩,fun ⟨y,hy,hxy⟩ => hn ((Set.mem_singleton_iff.mp hy) ▸ hxy)⟩
  · rintro ⟨_,⟨y,hy,hxy⟩,hn⟩
    exact ⟨(Set.mem_singleton_iff.mp hy) ▸ hxy,fun hz => hn ⟨z,rfl,hz⟩⟩

theorem hangingSide_ncard_add_rank (G : BondGraph V E) (ω : Set E) (x : V)
    (e : E) (hC : (cluster G ω x).Finite) :
    (hangingSide G ω x e).ncard + pivotalRank G ω x e = (cluster G ω x).ncard := by
  have hs : cluster G (ω \ {e}) x ⊆ cluster G ω x := fun _ h => conn_mono G Set.sdiff_subset h
  rw [hangingSide,Set.ncard_sdiff hs (hC.subset hs)]
  exact Nat.sub_add_cancel (Set.ncard_le_ncard hs hC)



theorem smallSeparatingBonds_card_le (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : (smallSeparatingBonds G ω x z v).card ≤ v := by
  have hh := Finset.card_le_card_of_injOn (s := smallSeparatingBonds G ω x z v)
    (t := Finset.Icc 1 v) (fun e => (hangingSide G ω x e).ncard)
  have hmap : Set.MapsTo (fun e => (hangingSide G ω x e).ncard)
      (↑(smallSeparatingBonds G ω x z v)) (↑(Finset.Icc 1 v)) := by
    intro e he
    obtain ⟨he,hcap⟩ := Finset.mem_filter.mp he
    have hp := (mem_separatingBonds G ω x z e).mp he
    exact Finset.mem_Icc.mpr ⟨(Set.ncard_pos (hangingSide_finite G ω x e hC)).mpr
      ⟨z,(mem_hangingSide_iff_pivotal G ω x z e hp.1).mpr hp⟩,hcap⟩
  have hinj : Set.InjOn (fun e => (hangingSide G ω x e).ncard)
      (↑(smallSeparatingBonds G ω x z v)) := by
    intro e he f hf heq
    apply pivotalRank_injective_of_cluster_finite G ω {z} x hC
      ((mem_separatingBonds G ω x z e).mp (Finset.mem_filter.mp he).1)
      ((mem_separatingBonds G ω x z f).mp (Finset.mem_filter.mp hf).1)
    change (hangingSide G ω x e).ncard = (hangingSide G ω x f).ncard at heq
    have he' := hangingSide_ncard_add_rank G ω x e hC
    have hf' := hangingSide_ncard_add_rank G ω x f hC
    omega
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh hmap hinj

theorem mem_smallHangingThrough (G : BondGraph V E) (ω : Set E) (x z w : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : w ∈ smallHangingThrough G ω x z v hC ↔
      ∃ e, OpenMarkedPivotal G ω {z} x e ∧ (hangingSide G ω x e).ncard ≤ v ∧
        w ∈ hangingSide G ω x e := by
  simp [smallHangingThrough, smallSeparatingBonds, and_assoc]

theorem smallHangingThrough_card_le (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) :
    (smallHangingThrough G ω x z v hC).card ≤ v*v := by
  calc
    _ ≤ ∑ e ∈ smallSeparatingBonds G ω x z v, (hangingSide_finite G ω x e hC).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ smallSeparatingBonds G ω x z v, v := by
      apply Finset.sum_le_sum
      intro e he
      rw [← Set.ncard_eq_toFinset_card (hangingSide G ω x e) (hangingSide_finite G ω x e hC)]
      exact (Finset.mem_filter.mp he).2
    _ = (smallSeparatingBonds G ω x z v).card*v := by simp
    _ ≤ v*v := Nat.mul_le_mul_right v (smallSeparatingBonds_card_le G ω x z v hC)

end SmallHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearHanging
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem hangingSide_laminar (G : BondGraph V E) (ω : Set E) (x : V)
    (e f : E) (he : e ∈ ω) (hf : f ∈ ω) :
    Disjoint (hangingSide G ω x e) (hangingSide G ω x f) ∨
      hangingSide G ω x e ⊆ hangingSide G ω x f ∨
      hangingSide G ω x f ⊆ hangingSide G ω x e := by
  by_cases hd : Disjoint (hangingSide G ω x e) (hangingSide G ω x f)
  · exact Or.inl hd
  obtain ⟨z,hze,hzf⟩ := Set.not_disjoint_iff.mp hd
  by_cases hef : e = f
  · exact Or.inr (Or.inl (hef ▸ Set.Subset.refl _))
  rcases pivotal_rootSides_nested G ω {z} x
    ((mem_hangingSide_iff_pivotal G ω x z e he).mp hze)
    ((mem_hangingSide_iff_pivotal G ω x z f hf).mp hzf) hef with h | h
  · exact Or.inr (Or.inr (Set.sdiff_subset_sdiff_right h.1))
  · exact Or.inr (Or.inl (Set.sdiff_subset_sdiff_right h.1))

theorem graphNeighbors_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (d : ℕ) (hdeg : ∀ a, degree G a ≤ d) :
    (graphNeighbors G hloc A).card ≤ A.card*d := by
  calc
    _ ≤ ∑ a ∈ A, (neighbors G hloc a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, d := Finset.sum_le_sum fun a _ =>
      (neighbors_card_le_degree G hloc a).trans (hdeg a)
    _ = _ := by simp



theorem nearHangingEndpoints_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x z : V) (e : E) (v d : ℕ) (hC : (cluster G ω x).Finite)
    (hcap : (hangingSide G ω x e).ncard ≤ v) (hdeg : ∀ a, degree G a ≤ d) :
    (nearHangingEndpoints G hloc ω x z e v hC).card ≤ v+v^2+d*v^3 := by
  let B := (hangingSide_finite G ω x e hC).toFinset
  let N := graphNeighbors G hloc B
  have hB : B.card ≤ v := by
    simpa only [B,← Set.ncard_eq_toFinset_card (hangingSide G ω x e)
      (hangingSide_finite G ω x e hC)] using hcap
  have hN : N.card ≤ v*d := (graphNeighbors_card_le G hloc B d hdeg).trans
    (Nat.mul_le_mul_right d hB)
  have hU : (N.biUnion fun a => smallHangingThrough G ω x a v hC).card ≤ d*v^3 := by
    calc
      _ ≤ ∑ a ∈ N, (smallHangingThrough G ω x a v hC).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ N, v*v := Finset.sum_le_sum fun a _ => smallHangingThrough_card_le G ω x a v hC
      _ = N.card*(v*v) := by simp
      _ ≤ (v*d)*(v*v) := Nat.mul_le_mul_right (v*v) hN
      _ = d*v^3 := by ring
  calc
    _ ≤ (B ∪ smallHangingThrough G ω x z v hC).card +
        (N.biUnion fun a => smallHangingThrough G ω x a v hC).card := Finset.card_union_le ..
    _ ≤ (B.card + (smallHangingThrough G ω x z v hC).card) + d*v^3 :=
      Nat.add_le_add (Finset.card_union_le ..) hU
    _ ≤ (v+v*v)+d*v^3 := Nat.add_le_add_right
      (Nat.add_le_add hB (smallHangingThrough_card_le G ω x z v hC)) _
    _ = v+v^2+d*v^3 := by ring

theorem mem_nearHangingEndpoints_of_not_separated (G : BondGraph V E)
    (hloc : LocallyFinite G) (ω : Set E) (x z w : V) (e f : E) (v : ℕ)
    (hC : (cluster G ω x).Finite)
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {w} x f)
    (hcap : (hangingSide G ω x f).ncard ≤ v)
    (hn : ¬GraphSeparated G (hangingSide G ω x e) (hangingSide G ω x f)) :
    w ∈ nearHangingEndpoints G hloc ω x z e v hC := by
  have hz := (mem_hangingSide_iff_pivotal G ω x z e he.1).mpr he
  have hw := (mem_hangingSide_iff_pivotal G ω x w f hf.1).mpr hf
  rcases hangingSide_laminar G ω x e f he.1 hf.1 with hd | hsub | hsub
  · have hadj : ∃ a ∈ hangingSide G ω x e, ∃ b ∈ hangingSide G ω x f, Adj G a b := by
      by_contra h
      apply hn
      refine ⟨hd,?_⟩
      intro a ha b hb hab
      exact h ⟨a,ha,b,hb,hab⟩
    obtain ⟨a,ha,b,hb,hab⟩ := hadj
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨b,Finset.mem_biUnion.mpr ⟨a,?_,(mem_neighbors G hloc a b).mpr hab⟩,?_⟩
    · exact (hangingSide_finite G ω x e hC).mem_toFinset.mpr ha
    · exact (mem_smallHangingThrough G ω x b w v hC).mpr
        ⟨f,(mem_hangingSide_iff_pivotal G ω x b f hf.1).mp hb,hcap,hw⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact (mem_smallHangingThrough G ω x z w v hC).mpr
      ⟨f,(mem_hangingSide_iff_pivotal G ω x z f hf.1).mp (hsub hz),hcap,hw⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact (hangingSide_finite G ω x e hC).mem_toFinset.mpr (hsub hw)

end NearHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceLaw
attribute [local instance] Classical.propDecidable Classical.decEq


theorem encodeFiniteJoint_injective (Q : Finset E) (J₁ J₂ : Finset ℕ) :
    Function.Injective (encodeFiniteJoint Q J₁ J₂) := by
  intro a b he
  apply Prod.ext (finiteFieldSet_injective Q (congrArg Prod.fst he))
  exact Prod.ext (finiteFieldFamily_injective Q J₁ (congrArg (fun s => s.2.1) he))
    (finiteFieldFamily_injective Q J₂ (congrArg (fun s => s.2.2) he))

theorem jointTupleWeight_encode (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (s : FiniteJointData Q J₁ J₂) :
    jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) =
      finiteFieldWeight Q p s.1 * finiteFamilyWeight Q J₁ p s.2.1 *
        finiteFamilyWeight Q J₂ p s.2.2 := by
  simp only [jointTupleWeight,encodeFiniteJoint,domainBits_finiteFieldSet,
    prod_fieldFamilyWeight,finiteFieldWeight]



end FiniteReferenceLaw

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceFactor
attribute [local instance] Classical.propDecidable Classical.decEq



theorem mem_finiteJointDomain_of_support (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s : JointSpliceState E) (hω : s.1 ⊆ (Q : Set E))
    (hη₁ : ∀ i, s.2.1 i ⊆ (Q : Set E)) (hη₂ : ∀ i, s.2.2 i ⊆ (Q : Set E))
    (hz₁ : ∀ i ∉ J₁, s.2.1 i = ∅) (hz₂ : ∀ i ∉ J₂, s.2.2 i = ∅) :
    s ∈ finiteJointDomain Q J₁ J₂ := by
  let desc (ω : Set E) : FiniteField Q := ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩
  have hdesc (ω : Set E) (h : ω ⊆ (Q : Set E)) : finiteFieldSet Q (desc ω) = ω := by
    ext e
    simp only [finiteFieldSet,desc,Finset.mem_coe,mem_domainBits]
    exact ⟨fun hh => hh.2,fun hh => ⟨h hh,hh⟩⟩
  let a : FiniteJointData Q J₁ J₂ := (desc s.1,fun i => desc (s.2.1 i),fun i => desc (s.2.2 i))
  apply Finset.mem_image.mpr
  refine ⟨a,Finset.mem_univ _,?_⟩
  apply Prod.ext (hdesc s.1 hω)
  apply Prod.ext
  · funext i
    change (if hi : i ∈ J₁ then finiteFieldSet Q (desc (s.2.1 i)) else ∅) = s.2.1 i
    by_cases hi : i ∈ J₁
    · simp only [hi,dite_true,hdesc _ (hη₁ i)]
    · simp only [hi,dite_false,hz₁ i hi]
  · funext i
    change (if hi : i ∈ J₂ then finiteFieldSet Q (desc (s.2.2 i)) else ∅) = s.2.2 i
    by_cases hi : i ∈ J₂
    · simp only [hi,dite_true,hdesc _ (hη₂ i)]
    · simp only [hi,dite_false,hz₂ i hi]

end FiniteReferenceFactor

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeededForward
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_seeded_spliceTrace (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k M : ℕ)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (choose : ℕ → Set E → E)
    (hchoose : ∀ i K, K.Finite → K.Nonempty → choose i K ∈ K)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (N : ℕ) (hfin : (cluster G ω x).Finite) (hN : (cluster G ω x).ncard ≤ N) :
    ∃ steps ωf, SpliceTrace G x η y k j ω steps ωf ∧
      FollowsContactRule G x η y choose steps ω ∧ steps.length ≤ k-j ∧
      y k ∈ cluster G ωf x ∧ (cluster G ωf x).Finite ∧
      (cluster G ωf x).ncard ≤ N+(k-j)*M := by
  generalize hn : k-j = n
  induction n using Nat.strong_induction_on generalizing j ω N with
  | h n ih =>
    by_cases hz : y k ∈ cluster G ω x
    · refine ⟨[],ω,SpliceTrace.stop j ω hz,?_,by simp,hz,hfin,?_⟩
      · exact List.Forall₂.nil
      · exact hN.trans (Nat.le_add_right ..)
    · obtain ⟨i,hiI,hmeet,hyi,hmax⟩ :=
        exists_maximal_splice_index G η y k j hj hchain (cluster G ω x) hyj hz
      obtain ⟨hji,hik⟩ := Finset.mem_Icc.mp hiI
      have hi1 : i ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega,hik⟩
      let B := cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)
      let K := contactSet G (η i) B
      have hBC : B ⊆ cluster G (η i) (y i) := fun _ h => conn_mono G Set.inter_subset_left h
      have hBK : K.Finite := contactSet_finite G hloc (η i) B ((hcaps i hi1).1.subset hBC)
      have hK : K.Nonempty := by
        obtain ⟨e,a,b,he,hab,ha,hb⟩ := exists_splice_contact G (η i) (cluster G ω x) (y i) hyi hmeet
        exact ⟨e,he,b,a,hab.trans (Sym2.eq_swap ..),hb,
          fun h => slit_cluster_subset G (cluster G ω x) (η i) (y i) hyi h ha⟩
      let e := choose i K
      have heK : e ∈ contactSet G (η i) B := hchoose i K hBK hK
      change e ∈ contactSet G (η i)
        (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) at heK
      rw [contactSet_deleted_cluster G (η i) (cluster G ω x) (y i) hyi] at heK
      obtain ⟨he,b,hb,a,ha,hba⟩ := heK
      have hab : G e = s(a,b) := hba.trans (Sym2.eq_swap ..)
      let ω' := spliceField G (cluster G ω x) B e ω (η i)
      have hcap := splice_cluster_cap G ω (η i) x (y i) hyi e a b hab he ha hb N M hfin hN
        (hcaps i hi1).1 (hcaps i hi1).2
      have hyt : y i ∈ cluster G ω' x := by
        change y i ∈ cluster G (spliceField G (cluster G ω x) B e ω (η i)) x
        rw [splice_cluster G ω (η i) x (y i) hyi e a b hab he ha hb]
        exact Or.inr (mem_cluster_self G _ _)
      obtain ⟨steps,ωf,htrace,hrule,hlen,hconn,hf,hs⟩ :=
        ih (k-i) (by omega) i hik ω' hyt (N+M) hcap.1 hcap.2 rfl
      refine ⟨(i,e)::steps,ωf,
        SpliceTrace.step j i ω e a b steps ωf hz (by omega) hik hmax hyi he hab ha hb htrace,
        ?_,?_,hconn,hf,?_⟩
      · exact (followsContactRule_cons G x η y choose i e steps ω).mpr ⟨rfl,hrule⟩
      · simp only [List.length_cons]
        omega
      · have hm : (k-i+1)*M ≤ (k-j)*M := Nat.mul_le_mul_right M (by omega)
        rw [Nat.add_mul,one_mul] at hm
        calc
          _ ≤ (N+M)+(k-i)*M := hs
          _ ≤ N+(k-j)*M := by omega
          _ = N+n*M := by rw [hn]



end SeededForward
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceLocalSupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem reachBall_triangle (G : BondGraph V E) (x y : V) (n m : ℕ)
    (hy : y ∈ reachBall G x n) : reachBall G y m ⊆ reachBall G x (n+m) := by
  induction m with
  | zero => simpa only [reachBall,Nat.add_zero,Set.singleton_subset_iff] using hy
  | succ m ih =>
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl (ih hz)
    · apply Or.inr
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hz ⊢
      obtain ⟨a,ha,haz⟩ := hz
      exact ⟨a,ih ha,haz⟩


end SpliceLocalSupport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformContactSelector
attribute [local instance] Classical.propDecidable Classical.decEq



theorem uniformRank_val_of_lt_one (K : ℕ) (hK : 0 < K) (t : unitInterval)
    (ht : (t:ℝ) < 1) : (uniformRank K hK t).val = ⌊(K:ℝ)*(t:ℝ)⌋₊ := by
  have hp : (0:ℝ) < K := by exact_mod_cast hK
  have hf : ⌊(K:ℝ)*(t:ℝ)⌋₊ < K := (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) t.property.1)).mpr (by nlinarith)
  exact min_eq_left (by omega)

theorem uniformRank_eq_iff (K : ℕ) (hK : 0 < K) (t : unitInterval)
    (ht : (t:ℝ) < 1) (a : Fin K) :
    uniformRank K hK t = a ↔ t ∈ contactInterval K a.val := by
  rw [Fin.ext_iff,uniformRank_val_of_lt_one K hK t ht,
    Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) t.property.1)]
  have hp : (0:ℝ) < K := by exact_mod_cast hK
  simp only [contactInterval,Set.mem_ofPred_eq,Nat.cast_add,Nat.cast_one]
  rw [div_le_iff₀ hp,lt_div_iff₀ hp]
  simp only [mul_comm]

theorem volume_uniformRank_fiber (K : ℕ) (hK : 0 < K) (a : Fin K) :
    volume {t : unitInterval | uniformRank K hK t = a} =
      ENNReal.ofReal ((K:ℝ)⁻¹) := by
  rw [← volume_contactInterval K a.val a.isLt]
  apply measure_congr
  filter_upwards [(volume : Measure unitInterval).ae_ne 1] with t ht
  exact propext (uniformRank_eq_iff K hK t (lt_of_le_of_ne t.property.2
    (fun he => ht (Subtype.ext he))) a)



theorem uniformContact_mem (K : Finset E) (hK : K.Nonempty) (t : unitInterval) :
    uniformContact K hK t ∈ K :=
  ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).property

theorem uniformContact_eq_iff (K : Finset E) (hK : K.Nonempty) (t : unitInterval)
    (e : E) (he : e ∈ K) :
    uniformContact K hK t = e ↔
      uniformRank K.card (Finset.card_pos.mpr hK) t = K.equivFin ⟨e,he⟩ := by
  unfold uniformContact
  change ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).val =
    (⟨e,he⟩ : ↥K).val ↔ _
  rw [← Subtype.ext_iff]
  exact K.equivFin.symm_apply_eq

theorem volume_uniformContact_fiber (K : Finset E) (hK : K.Nonempty)
    (e : E) (he : e ∈ K) : volume {t : unitInterval | uniformContact K hK t = e} =
      ENNReal.ofReal ((K.card:ℝ)⁻¹) := by
  simp_rw [uniformContact_eq_iff K hK _ e he]
  exact volume_uniformRank_fiber K.card (Finset.card_pos.mpr hK) _



theorem chooseContact_mem [Nonempty E] (seed : ℕ → unitInterval)
    (i : ℕ) (K : Set E) (hf : K.Finite) (hn : K.Nonempty) :
    chooseContact seed i K ∈ K := by
  simp only [chooseContact,dite_eq_left hf,dite_eq_left hn]
  exact hf.mem_toFinset.mp (uniformContact_mem _ _ _)

end UniformContactSelector
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty E]

 
theorem chooseContact_congr (u v : ℕ → unitInterval) (i : ℕ) (K : Set E)
    (h : u i = v i) : chooseContact u i K = chooseContact v i K := by
  unfold chooseContact
  split_ifs <;> simp only [h]


theorem replaySeedFiber_univ (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (i : ℕ)
    (hi : ∀ q ∈ c, i ≠ q.1) : replaySeedFiber G x η y c ω i = Set.univ := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨j,e⟩ := q
    simp only [replaySeedFiber,ite_eq_right (hi (j,e) (by simp))]
    exact ih _ (fun q hq => hi q (by simp [hq]))

theorem SpliceTrace.follows_iff_seedFiber (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (seed : ℕ → unitInterval) :
    FollowsContactRule G x η y (chooseContact seed) c ω ↔
      ∀ i, 1 ≤ i → i ≤ k → seed i ∈ replaySeedFiber G x η y c ω i := by
  induction h with
  | stop j ω hz => simp [FollowsContactRule,replayContacts,replaySeedFiber]
  | @step j l ω e a b c ωf hn hjl hlk hm hy he hab ha hb ht ih =>
    rw [followsContactRule_cons,ih]
    have htail : replaySeedFiber G x η y c
        (spliceField G (cluster G ω x)
          (cluster G (η l ∩ internalEdges G (cluster G ω x)ᶜ) (y l)) e ω (η l)) l = Set.univ := by
      apply replaySeedFiber_univ
      intro q hq
      have hq' := ht.seam_data G x η y k l _ ωf c q hq
      omega
    constructor
    · rintro ⟨hc,hr⟩ i hi hik
      by_cases hil : i = l
      · subst i
        simp only [replaySeedFiber,if_true,Set.mem_ofPred_eq]
        exact (chooseContact_congr _ _ l _ rfl).trans hc
      · simpa only [replaySeedFiber,ite_eq_right hil] using hr i hi hik
    · intro hr
      constructor
      · have hh := hr l (by omega) hlk
        simp only [replaySeedFiber,if_true,Set.mem_ofPred_eq] at hh
        exact (chooseContact_congr _ _ l _ rfl).trans hh
      · intro i hi hik
        by_cases hil : i = l
        · subst i
          rw [htail]
          trivial
        · simpa only [replaySeedFiber,ite_eq_right hil] using hr i hi hik



theorem SpliceTrace.seed_event_eq_pi (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf) :
    {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω} =
      Set.pi Set.univ (fun i => replaySeedFiber G x η y c ω (i.val+1)) := by
  ext u
  rw [Set.mem_ofPred_eq,h.follows_iff_seedFiber G x η y k j ω ωf c]
  simp only [Set.mem_pi,Set.mem_univ,true_implies]
  constructor
  · intro hu i
    simpa only [finiteContactSeeds_at] using hu (i.val+1) (by omega) (by omega)
  · intro hu i hi hik
    have hh := hu ⟨i-1,by omega⟩
    have hii : 1 ≤ i ∧ i ≤ k := ⟨hi,hik⟩
    simpa only [finiteContactSeeds,dite_eq_left hii,Nat.sub_add_cancel hi] using hh

 

theorem SpliceTrace.volume_seedFiber (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite) :
    ∀ i, volume (replaySeedFiber G x η y c ω i) =
      ENNReal.ofReal ((traceContactCount G η y ωf x c i : ℝ)⁻¹) := by
  induction c generalizing j ω with
  | nil => simp [replaySeedFiber,traceContactCount]
  | cons q c ih =>
    obtain ⟨l,e⟩ := q
    have hcut := h.head_cut G x η y k j l ω ωf e c
    cases h with
    | step j l ω e a b c ωf hn hjl hlk hm hy he hab ha hb ht =>
      intro i
      by_cases hil : i = l
      · subst i
        simp only [replaySeedFiber,if_true,traceContactCount,seamContactCount,hcut]
        let B := cluster G (η l ∩ internalEdges G (cluster G ω x)ᶜ) (y l)
        let K := contactSet G (η l) B
        have hB : B.Finite := (hcaps l (by omega) hlk).subset (fun _ h => conn_mono G Set.inter_subset_left h)
        have hK : K.Finite := contactSet_finite G hloc (η l) B hB
        have heK : e ∈ K := ⟨he,b,a,hab.trans (Sym2.eq_swap ..),hb,
          fun haB => slit_cluster_subset G (cluster G ω x) (η l) (y l) hy haB ha⟩
        have hnK : K.Nonempty := ⟨e,heK⟩
        change volume {t : unitInterval | chooseContact (fun _ => t) l K = e} = _
        simp only [chooseContact,dite_eq_left hK,dite_eq_left hnK]
        rw [volume_uniformContact_fiber _ _ e (hK.mem_toFinset.mpr heK)]
        rw [← Set.ncard_eq_toFinset_card K hK]
      · simpa only [replaySeedFiber,traceContactCount,ite_eq_right hil] using ih l _ ht i

 
theorem SpliceTrace.seed_probability (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite) :
    ((volume : Measure (Fin k → unitInterval))
      {u | FollowsContactRule G x η y (chooseContact (finiteContactSeeds k u)) c ω}).toReal =
      ∏ i : Fin k, (traceContactCount G η y ωf x c (i.val+1):ℝ)⁻¹ := by
  rw [h.seed_event_eq_pi G x η y k j ω ωf c,MeasureTheory.volume_pi,Measure.pi_pi,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [h.volume_seedFiber G hloc x η y k j ω ωf c hcaps,ENNReal.toReal_ofReal (by positivity)]

end SeededTraceLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_MomentBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceMeasurable
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem uniformRank_fiber_eq (K : ℕ) (hK : 0 < K) (a : Fin K) :
    {t : unitInterval | uniformRank K hK t = a} = contactInterval K a.val ∪
      (if uniformRank K hK 1 = a then {1} else ∅) := by
  ext t
  by_cases ht : t = 1
  · subst t
    have hnot : (1 : unitInterval) ∉ contactInterval K a.val := by
      intro h
      have hp : (0:ℝ) < K := by exact_mod_cast hK
      have hlt := (lt_div_iff₀ hp).mp h.2
      have ha : (a.val:ℝ)+1 ≤ K := by exact_mod_cast (show a.val+1 ≤ K by omega)
      push_cast at hlt
      norm_num at hlt
      linarith
    simp [hnot]
  · have hlt : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 (fun he => ht (Subtype.ext he))
    have he := uniformRank_eq_iff K hK t hlt a
    simp only [Set.mem_union,Set.mem_ofPred_eq]
    split_ifs <;> simpa [ht] using he

theorem measurableSet_contactInterval (K a : ℕ) : MeasurableSet (contactInterval K a) :=
  (measurableSet_le measurable_const measurable_subtype_coe).inter
    (measurableSet_lt measurable_subtype_coe measurable_const)

theorem measurableSet_uniformRank_fiber (K : ℕ) (hK : 0 < K) (a : Fin K) :
    MeasurableSet {t : unitInterval | uniformRank K hK t = a} := by
  rw [uniformRank_fiber_eq]
  apply (measurableSet_contactInterval K a.val).union
  split_ifs
  · exact measurableSet_singleton _
  · exact MeasurableSet.empty

theorem measurableSet_uniformContact_fiber (K : Finset E) (hK : K.Nonempty) (e : E) :
    MeasurableSet {t : unitInterval | uniformContact K hK t = e} := by
  by_cases he : e ∈ K
  · simp_rw [uniformContact_eq_iff K hK _ e he]
    exact measurableSet_uniformRank_fiber _ _ _
  · have hz : {t : unitInterval | uniformContact K hK t = e} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun h => he (h ▸ uniformContact_mem K hK t)
    rw [hz]
    exact MeasurableSet.empty

theorem measurableSet_chooseContact_fiber [Nonempty E] (i : ℕ) (K : Set E) (e : E) :
    MeasurableSet {t : unitInterval | chooseContact (fun _ => t) i K = e} := by
  unfold chooseContact
  split_ifs
  · exact measurableSet_uniformContact_fiber _ _ _
  · by_cases he : Classical.arbitrary E = e <;> simp [he]
  · by_cases he : Classical.arbitrary E = e <;> simp [he]

theorem measurableSet_replaySeedFiber [Nonempty E] (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (i : ℕ) :
    MeasurableSet (replaySeedFiber G x η y c ω i) := by
  induction c generalizing ω with
  | nil => exact MeasurableSet.univ
  | cons q c ih =>
    obtain ⟨j,e⟩ := q
    simp only [replaySeedFiber]
    split_ifs
    · exact measurableSet_chooseContact_fiber _ _ _
    · exact ih _

theorem SpliceTrace.measurableSet_seed_event [Nonempty E] (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf) :
    MeasurableSet {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω} := by
  rw [h.seed_event_eq_pi G x η y k j ω ωf c]
  exact MeasurableSet.univ_pi (fun i => measurableSet_replaySeedFiber G x η y c ω (i.val+1))

end SeededTraceMeasurable
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteTraceDistribution
attribute [local instance] Classical.propDecidable Classical.decEq


theorem SpliceTrace.length_le (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) : c.length ≤ k-j := by
  induction h with
  | stop => simp
  | step => simp only [List.length_cons]; omega

theorem SpliceTrace.mem_boundedTraceCodes (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E)) : c ∈ boundedTraceCodes Q k := by
  rw [Percolation.mem_boundedTraceCodes]
  refine ⟨(h.length_le G x η y k j ω ωf c).trans (Nat.sub_le ..),?_⟩
  intro q hq
  obtain ⟨hj,hk,he,_⟩ := h.seam_data G x η y k j ω ωf c q hq
  exact ⟨by omega,hk,hQ q.1 (by omega) hk he⟩



theorem finite_trace_seed_partition [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k M : ℕ) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E))
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (hfin : (cluster G ω x).Finite) :
    let S := finiteTraceCodes G x η y k j ω Q
    let A := fun c => {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω}
    (⋃ c ∈ S, A c) = Set.univ ∧ Set.PairwiseDisjoint (↑S) A := by
  intro S A
  constructor
  · apply Set.eq_univ_of_forall
    intro u
    obtain ⟨c,ωf,ht,hr,_⟩ := exists_seeded_spliceTrace G hloc x η y k M hchain hcaps
      (chooseContact (finiteContactSeeds k u)) (chooseContact_mem _) j hj ω hyj _ hfin (le_refl _)
    have hc : c ∈ S := (mem_finiteTraceCodes_iff ..).mpr
      ⟨ht.mem_boundedTraceCodes G x η y k j ω ωf c Q hQ,
        (ht.replay_eq G x η y k j ω ωf c).symm ▸ ht⟩
    exact Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨hc,hr⟩⟩
  · intro c hc d hd hcd
    apply Set.disjoint_left.mpr
    intro u huc hud
    have ht := (mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc
    have hs := (mem_finiteTraceCodes_iff G x η y k j ω Q d).mp hd
    exact hcd (ht.2.seeded_unique G x η y k j ω _ _ c d hs.2
      (chooseContact (finiteContactSeeds k u)) huc hud).1

 
theorem sum_finite_trace_probabilities [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k M : ℕ) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E))
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (hfin : (cluster G ω x).Finite) :
    (∑ c ∈ finiteTraceCodes G x η y k j ω Q,
      ∏ i : Fin k, (traceContactCount G η y (replaySplice G x η y c ω) x c (i.val+1):ℝ)⁻¹) = 1 := by
  let S := finiteTraceCodes G x η y k j ω Q
  let A := fun c => {u : Fin k → unitInterval | FollowsContactRule G x η y
    (chooseContact (finiteContactSeeds k u)) c ω}
  have hpart := finite_trace_seed_partition G hloc x η y k M Q hQ hchain hcaps j hj ω hyj hfin
  have hm : ∀ c ∈ S, MeasurableSet (A c) := by
    intro c hc
    exact ((mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc).2.measurableSet_seed_event
      G x η y k j ω _ c
  have hsum : ∑ c ∈ S, volume (A c) = 1 := by
    rw [← measure_biUnion_finset hpart.2 hm,hpart.1,measure_univ]
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (fun c _ => measure_ne_top volume (A c)),ENNReal.toReal_one] at hr
  rw [← hr]
  apply Finset.sum_congr rfl
  intro c hc
  exact (((mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc).2.seed_probability
    G hloc x η y k j ω _ c (fun i hi hik => (hcaps i (Finset.mem_Icc.mpr ⟨hi,hik⟩)).1)).symm

end FiniteTraceDistribution
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSpliceState
attribute [local instance] Classical.propDecidable Classical.decEq



theorem encodeFiniteSplice_injective (Q : Finset E) (J : Finset ℕ) :
    Function.Injective (encodeFiniteSplice Q J) := by
  intro a b he
  exact Prod.ext (finiteFieldSet_injective Q (congrArg Prod.fst he))
    (finiteFieldFamily_injective Q J (congrArg Prod.snd he))

end FiniteSpliceState

end Percolation

 
open MeasureTheory
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteInverseLoad_density {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (mass : I → ℝ) (B : Finset (SpliceState E)) (hB : ∀ a, out a ∈ B)
    (f : SpliceState E → ℝ) :
    (∑ a, spliceTupleWeight Q (Finset.Icc 1 k) p (inp a) * mass a * f (out a)) =
      ∑ t ∈ B, spliceTupleWeight Q (Finset.Icc 1 k) p t * finiteInverseLoad out mass t * f t := by
  have hw (a : I) : spliceTupleWeight Q (Finset.Icc 1 k) p (inp a) =
      spliceTupleWeight Q (Finset.Icc 1 k) p (out a) := by
    symm
    apply (hex a).weight G x (inp a) (out a) (steps a) Q (Finset.Icc 1 k) _ p
    intro q hq
    have h := (htrace a).seam_data G x (inp a).2 (y a) k 0 (inp a).1 (out a).1 (steps a) q hq
    exact Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩
  simp only [finiteInverseLoad,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite,mul_zero,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq,ite_eq_left (hB a),hw a]

end FiniteSwitchDensity

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ContactIntegratedSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_event_mass_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : I → Set Ω)
    (hm : ∀ a, MeasurableSet (P a)) (w : I → ℝ) (B : ℝ)
    (hpoint : ∀ u, (∑ a, if u ∈ P a then w a else 0) ≤ B) :
    (∑ a, w a * μ.real (P a)) ≤ B := by
  let f (a : I) : Ω → ℝ := (P a).indicator (fun _ => w a)
  have hf : ∀ a, Integrable (f a) μ := fun a => (integrable_const _).indicator (hm a)
  have hi := integral_mono (integrable_finsetSum _ (fun a _ => hf a))
    (integrable_const B) (fun u => hpoint u)
  change (∫ u, ∑ a, f a u ∂μ) ≤ (∫ _ : Ω, B ∂μ) at hi
  rw [integral_finsetSum _ (fun a _ => hf a)] at hi
  simpa only [f,integral_indicator_const _ (hm _),smul_eq_mul,mul_comm,
    integral_const,probReal_univ,one_smul,mul_one] using hi



end ContactIntegratedSecondMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteRootLoad
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteRootLoad_mean (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : SpliceState E → ℝ) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * finiteRootLoad Q J p f ω) =
      ∑ s ∈ finiteSpliceDomain Q J, spliceTupleWeight Q J p s * f s := by
  rw [finiteSpliceDomain,Finset.sum_image (encodeFiniteSplice_injective Q J).injOn,
    Fintype.sum_prod_type]
  simp only [spliceTupleWeight,finiteRootLoad,Finset.mul_sum,encodeFiniteSplice,
    domainBits_finiteFieldSet,prod_fieldFamilyWeight,finiteFieldWeight,mul_assoc]

 

theorem finiteRootLoad_second_moment (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (f₁ f₂ : SpliceState E → ℝ) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J₁ p f₁ ω * finiteRootLoad Q J₂ p f₂ ω) =
    ∑ s : FiniteJointData Q J₁ J₂, jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) *
      f₁ (finiteFieldSet Q s.1,finiteFieldFamily Q J₁ s.2.1) *
      f₂ (finiteFieldSet Q s.1,finiteFieldFamily Q J₂ s.2.2) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Fintype.sum_prod_type]
  simp only [finiteRootLoad,Finset.mul_sum,Finset.sum_mul,jointTupleWeight_encode]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η₁ _
  apply Finset.sum_congr rfl
  intro η₂ _
  ring


end FiniteRootLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePairLoad
attribute [local instance] Classical.propDecidable Classical.decEq


theorem pairSpliceOutput_mem (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s t : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J₁)
    (ht : t ∈ finiteSpliceDomain Q J₂) :
    pairSpliceOutput s t ∈ finiteJointDomain Q J₁ J₂ := by
  have h₁ := (mem_finiteSpliceDomain_iff Q J₁ s).mp hs
  have h₂ := (mem_finiteSpliceDomain_iff Q J₂ t).mp ht
  exact mem_finiteJointDomain_of_support Q J₁ J₂ _ h₁.1 h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2

 
theorem finiteInverseLoad_mul {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (t : JointSpliceState E) :
    finiteInverseLoad out₁ m₁ (t.1,t.2.1) * finiteInverseLoad out₂ m₂ (t.1,t.2.2) =
    ∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ pairSpliceOutput (out₁ a) (out₂ b) = t
      then m₁ a * m₂ b else 0 := by
  simp only [finiteInverseLoad,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : (out₁ a = (t.1,t.2.1) ∧ out₂ b = (t.1,t.2.2)) ↔
      ((out₁ a).1 = (out₂ b).1 ∧ pairSpliceOutput (out₁ a) (out₂ b) = t) := by
    cases h₁ : out₁ a with | mk r₁ u₁ =>
      cases h₂ : out₂ b with | mk r₂ u₂ =>
        rcases t with ⟨r,u,v⟩
        simpa [pairSpliceOutput,Prod.mk.injEq] using
          (show (r₁ = r ∧ u₁ = u) ∧ (r₂ = r ∧ u₂ = v) ↔
            r₁ = r₂ ∧ r₁ = r ∧ u₁ = u ∧ u₂ = v from by aesop)
  simp only [← he]
  split_ifs <;> simp_all

 

theorem finiteRootLoad_pair_expansion {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ)
    (hs₁ : ∀ a, out₁ a ∈ finiteSpliceDomain Q J₁)
    (hs₂ : ∀ b, out₂ b ∈ finiteSpliceDomain Q J₂) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J₁ p (finiteInverseLoad out₁ m₁) ω *
      finiteRootLoad Q J₂ p (finiteInverseLoad out₂ m₂) ω) =
    ∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0 := by
  rw [finiteRootLoad_second_moment]
  have hdom : (∑ s : FiniteJointData Q J₁ J₂,
      jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) *
        finiteInverseLoad out₁ m₁ ((encodeFiniteJoint Q J₁ J₂ s).1,(encodeFiniteJoint Q J₁ J₂ s).2.1) *
        finiteInverseLoad out₂ m₂ ((encodeFiniteJoint Q J₁ J₂ s).1,(encodeFiniteJoint Q J₁ J₂ s).2.2)) =
      ∑ t ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p t *
        finiteInverseLoad out₁ m₁ (t.1,t.2.1) * finiteInverseLoad out₂ m₂ (t.1,t.2.2) := by
    rw [finiteJointDomain,Finset.sum_image (encodeFiniteJoint_injective Q J₁ J₂).injOn]
  apply hdom.trans
  simp only [mul_assoc,finiteInverseLoad_mul,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases he : (out₁ a).1 = (out₂ b).1
  · simp only [he,true_and,if_true]
    rw [Finset.sum_ite_eq,ite_eq_left (pairSpliceOutput_mem Q J₁ J₂ _ _ (hs₁ a) (hs₂ b))]
  · simp [he]

theorem traceIndex_output_code_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteTraceIndex G x k Q A y =>
      (traceIndexOutput G x k Q A y a,traceIndexCode G x k Q A y a)) := by
  intro a b he
  have hc : traceIndexCode G x k Q A y a = traceIndexCode G x k Q A y b := congrArg Prod.snd he
  have ho : traceIndexOutput G x k Q A y a = traceIndexOutput G x k Q A y b := congrArg Prod.fst he
  apply traceIndex_injective G x k Q A y
  apply Prod.ext
  · apply SpliceExecution.input_unique G x _ _ _ (traceIndexCode G x k Q A y a)
      (traceIndex_valid G x k Q A y a).2
    change SpliceExecution G x b.1.val (traceIndexCode G x k Q A y a) (traceIndexOutput G x k Q A y a)
    rw [hc,ho]
    exact (traceIndex_valid G x k Q A y b).2
  · exact hc

end FinitePairLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedJointMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem jointRestored_injective {I : Type*}
    (G : BondGraph V E) (x : V) (k : ℕ)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    : Function.Injective (fun a => jointRestored G x (η₁ a) (η₂ a)
      (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)) := by
  let out (a : I) := jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
    (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)
  let rest (a : I) := jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)
  change Function.Injective rest
  intro a b he
  have hη₁ : η₁ a = η₁ b := congrArg (fun s : JointSpliceState E => s.2.1) he
  have hη₂ : η₂ a = η₂ b := congrArg (fun s : JointSpliceState E => s.2.2) he
  have gb₁ : SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ b) (c₁ b) (ωf b) := by
    rw [hη₁]; exact h₁ b
  have gb₂ : SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ b) (c₂ b) (ωf b) := by
    rw [hη₂]; exact h₂ b
  have grb₁ : FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ b) (ω₁ b) := by
    rw [hη₁]; exact hr₁ b
  have grb₂ : FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ b) (ω₂ b) := by
    rw [hη₂]; exact hr₂ b
  have hfield : exchangeOn (maskUnion (replayMasks G x (η₂ a) (y₂ (η₂ a)) (c₂ a) (ω₂ a))) (ω₁ a) (ω₂ a) =
      exchangeOn (maskUnion (replayMasks G x (η₂ a) (y₂ (η₂ a)) (c₂ b) (ω₂ b))) (ω₁ b) (ω₂ b) := by
    have hh := congrArg Prod.fst he
    simpa only [rest,jointRestored,← hη₂] using hh
  obtain ⟨hcode₁,hcode₂,hfieldf,haux₁,haux₂⟩ := joint_restore_seeded_unique G x
    (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) choose₁ choose₂ k 0 0
    (ω₁ a) (ω₂ a) (ωf a) (ω₁ b) (ω₂ b) (ωf b)
    (c₁ a) (c₂ a) (c₁ b) (c₂ b) (h₁ a) (h₂ a) gb₁ gb₂
    (hc₁ a) (hc₂ a) (hc₁ b) (hc₂ b) (hsep a) (hsep b)
    (hr₁ a) (hr₂ a) grb₁ grb₂ hfield
  have hout : out a = out b := by
    apply Prod.ext hfieldf
    apply Prod.ext
    · simpa only [out,jointOutput,hη₁] using haux₁
    · simpa only [out,jointOutput,hη₂] using haux₂
  exact hir (Prod.ext hout (Prod.ext hcode₁ hcode₂))

 

theorem finite_joint_weighted_mass_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (B : Finset (JointSpliceState E))
    (hB : ∀ a, jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a) ∈ B) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)) ≤
      ∑ s ∈ B, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p s * m₁ s.2.1 * m₂ s.2.2 := by
  let out (a : I) := jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
    (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)
  let rest (a : I) := jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)
  have hinj : Function.Injective rest := jointRestored_injective G x k η₁ η₂ y₁ y₂ choose₁ choose₂
    ω₁ ω₂ ωf c₁ c₂ hir h₁ h₂ hc₁ hc₂ hsep hr₁ hr₂
  have hw : ∀ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p (out a) =
      jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p (rest a) := by
    intro a
    apply (h₁ a).joint_weight G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) k 0 0
      (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hsep a) Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    · intro q hq
      have hr := (h₁ a).seam_data G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a) q hq
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩
    · intro q hq
      have hr := (h₂ a).seam_data G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a) q hq
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩
  change (∑ a, jointTupleWeight Q _ _ p (out a) * m₁ (η₁ a) * m₂ (η₂ a)) ≤ _
  simp_rw [hw]
  change (∑ a, jointTupleWeight Q _ _ p (rest a) * m₁ (rest a).2.1 * m₂ (rest a).2.2) ≤ _
  rw [← Finset.sum_image (f := fun s : JointSpliceState E =>
    jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p s * m₁ s.2.1 * m₂ s.2.2) hinj.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    exact hB a
  · intro s _ _
    exact mul_nonneg (mul_nonneg (jointTupleWeight_nonneg Q _ _ p s) (hm₁ _)) (hm₂ _)

end WeightedJointMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteFamilyIntegral
attribute [local instance] Classical.propDecidable Classical.decEq


theorem finiteFamilyIntegral_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : (ℕ → Set E) → ℝ) (hf : ∀ η, 0 ≤ f η) : 0 ≤ finiteFamilyIntegral Q J p f := by
  exact Finset.sum_nonneg fun η _ => mul_nonneg (finiteFamilyWeight_nonneg Q J p η) (hf _)

theorem finiteFamilyIntegral_mono (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f g : (ℕ → Set E) → ℝ) (hfg : ∀ η, f η ≤ g η) :
    finiteFamilyIntegral Q J p f ≤ finiteFamilyIntegral Q J p g := by
  exact Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left (hfg _) (finiteFamilyWeight_nonneg Q J p η)

theorem finiteFamilyIntegral_sum {I : Type*} (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (S : Finset I) (f : I → (ℕ → Set E) → ℝ) :
    finiteFamilyIntegral Q J p (fun η => ∑ i ∈ S, f i η) =
      ∑ i ∈ S, finiteFamilyIntegral Q J p (f i) := by
  simp only [finiteFamilyIntegral,Finset.mul_sum]
  exact Finset.sum_comm

 
theorem finiteJointDomain_integral_factor (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (f₁ f₂ : Set E → (ℕ → Set E) → ℝ) :
    (∑ s ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p s * f₁ s.1 s.2.1 * f₂ s.1 s.2.2) =
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteFamilyIntegral Q J₁ p (f₁ (finiteFieldSet Q ω)) *
      finiteFamilyIntegral Q J₂ p (f₂ (finiteFieldSet Q ω)) := by
  rw [finiteJointDomain,Finset.sum_image (encodeFiniteJoint_injective Q J₁ J₂).injOn]
  simp only [jointTupleWeight_encode]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Fintype.sum_prod_type]
  simp only [finiteFamilyIntegral,Finset.mul_sum,Finset.sum_mul,encodeFiniteJoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η₂ _
  apply Finset.sum_congr rfl
  intro η₁ _
  ring

theorem finiteJointDomain_weighted_event_factor (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (P : Set E → Prop) (H₁ H₂ : Set E → (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) :
    (∑ s ∈ (finiteJointDomain Q J₁ J₂).filter (fun s => P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2),
      jointTupleWeight Q J₁ J₂ p s * m₁ s.2.1 * m₂ s.2.2) =
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if P (finiteFieldSet Q ω) then
        finiteFamilyIntegral Q J₁ p (fun η => if H₁ (finiteFieldSet Q ω) η then m₁ η else 0) *
        finiteFamilyIntegral Q J₂ p (fun η => if H₂ (finiteFieldSet Q ω) η then m₂ η else 0) else 0) := by
  rw [Finset.sum_filter]
  have he : (∑ s ∈ finiteJointDomain Q J₁ J₂,
      if P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2 then
        jointTupleWeight Q J₁ J₂ p s * m₁ s.2.1 * m₂ s.2.2 else 0) =
    ∑ s ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p s *
      (if P s.1 ∧ H₁ s.1 s.2.1 then m₁ s.2.1 else 0) *
      (if H₂ s.1 s.2.2 then m₂ s.2.2 else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp_all
  rw [he,finiteJointDomain_integral_factor Q J₁ J₂ p
    (fun ω η => if P ω ∧ H₁ ω η then m₁ η else 0)
    (fun ω η => if H₂ ω η then m₂ η else 0)]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hP : P (finiteFieldSet Q ω)
  · simp only [hP,true_and,if_true,mul_assoc]
  · simp [hP,finiteFamilyIntegral]

end FiniteFamilyIntegral

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedSeparatedSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_separated_weighted_second_moment_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k n M : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (success₁ success₂ : (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    (hbin : ∀ a, (cluster G (ω₁ a) x).Finite ∧ n ≤ (cluster G (ω₁ a) x).ncard ∧
      (cluster G (ω₁ a) x).ncard < 2*n)
    (hcap₂ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₂ a i) (y₂ (η₂ a) i)).Finite ∧
      (cluster G (η₂ a i) (y₂ (η₂ a) i)).ncard ≤ M)
    (hsc₁ : ∀ a, success₁ (η₁ a)) (hsc₂ : ∀ a, success₂ (η₂ a))
    (hsω₁ : ∀ a, ω₁ a ⊆ (Q : Set E)) (hsω₂ : ∀ a, ω₂ a ⊆ (Q : Set E))
    (hsη₁ : ∀ a i, η₁ a i ⊆ (Q : Set E)) (hsη₂ : ∀ a i, η₂ a i ⊆ (Q : Set E))
    (hz₁ : ∀ a i, i ∉ Finset.Icc 1 k → η₁ a i = ∅)
    (hz₂ : ∀ a i, i ∉ Finset.Icc 1 k → η₂ a i = ∅) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₁ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₂ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let J := Finset.Icc 1 k
  let P (ω : Set E) := (cluster G ω x).Finite ∧ n-k*M ≤ (cluster G ω x).ncard ∧
    (cluster G ω x).ncard < 2*n
  let H₁ (ω : Set E) (η : ℕ → Set E) := success₁ η ∧
    (cluster G ω x ∩ trajectoryUnion G η (y₁ η) k).Nonempty
  let H₂ (ω : Set E) (η : ℕ → Set E) := success₂ η ∧
    (cluster G ω x ∩ trajectoryUnion G η (y₂ η) k).Nonempty
  let B := (finiteJointDomain Q J J).filter fun s => P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2
  have hB (a : I) : jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a) ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_finiteJointDomain_of_support Q J J _
      (exchangeOn_subset _ _ _ _ (hsω₁ a) (hsω₂ a)) (hsη₁ a) (hsη₂ a) (hz₁ a) (hz₂ a),?_⟩
    have hroot := (h₁ a).joint_restored_size G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      k 0 0 n M (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hc₁ a) (hc₂ a) (hsep a)
      (hbin a).1 (hbin a).2.1 (hbin a).2.2 (hcap₂ a)
    have hhits := (h₁ a).joint_trajectory_hits G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      k 0 0 (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hc₁ a) (hc₂ a) (hsep a)
    exact ⟨hroot,⟨hsc₁ a,hhits.1⟩,hsc₂ a,hhits.2⟩
  have h := finite_joint_weighted_mass_le G x k p Q η₁ η₂ y₁ y₂ choose₁ choose₂ ω₁ ω₂ ωf c₁ c₂
    hir h₁ h₂ hc₁ hc₂ hsep hr₁ hr₂ m₁ m₂ hm₁ hm₂ B hB
  apply h.trans_eq
  convert finiteJointDomain_weighted_event_factor Q J J p P H₁ H₂ m₁ m₂ using 1 <;>
    simp only [B, J, P, H₁, H₂]
  apply Finset.sum_congr rfl
  intro ω _
  apply congrArg (fun z : ℝ => finiteFieldWeight Q p ω * z)
  split_ifs
  · apply congrArg₂ (· * ·)
    · apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      split_ifs <;> rfl
    · apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      split_ifs <;> rfl
  · rfl

end WeightedSeparatedSecondMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedContactSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_separated_weighted_contact_second_moment_le {I : Type*} [Fintype I] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (success₁ success₂ : (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hbin : ∀ a, (cluster G (ω₁ a) x).Finite ∧ n ≤ (cluster G (ω₁ a) x).ncard ∧
      (cluster G (ω₁ a) x).ncard < 2*n)
    (hcap₁ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₁ a i) (y₁ (η₁ a) i)).Finite)
    (hcap₂ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₂ a i) (y₂ (η₂ a) i)).Finite ∧
      (cluster G (η₂ a i) (y₂ (η₂ a) i)).ncard ≤ M)
    (hsc₁ : ∀ a, success₁ (η₁ a)) (hsc₂ : ∀ a, success₂ (η₂ a))
    (hsω₁ : ∀ a, ω₁ a ⊆ (Q : Set E)) (hsω₂ : ∀ a, ω₂ a ⊆ (Q : Set E))
    (hsη₁ : ∀ a i, η₁ a i ⊆ (Q : Set E)) (hsη₂ : ∀ a i, η₂ a i ⊆ (Q : Set E))
    (hz₁ : ∀ a i, i ∉ Finset.Icc 1 k → η₁ a i = ∅)
    (hz₂ : ∀ a i, i ∉ Finset.Icc 1 k → η₂ a i = ∅) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a) *
      (∏ i : Fin k, (traceContactCount G (η₁ a) (y₁ (η₁ a)) (ωf a) x (c₁ a) (i.val+1):ℝ)⁻¹) *
      (∏ i : Fin k, (traceContactCount G (η₂ a) (y₂ (η₂ a)) (ωf a) x (c₂ a) (i.val+1):ℝ)⁻¹)) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₁ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₂ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let S := Fin k → unitInterval
  let μ : Measure (S × S) := (volume : Measure S).prod volume
  let P₁ (a : I) : Set S := {u | FollowsContactRule G x (η₁ a) (y₁ (η₁ a))
    (chooseContact (finiteContactSeeds k u)) (c₁ a) (ω₁ a)}
  let P₂ (a : I) : Set S := {u | FollowsContactRule G x (η₂ a) (y₂ (η₂ a))
    (chooseContact (finiteContactSeeds k u)) (c₂ a) (ω₂ a)}
  let w (a : I) := jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)
  have hmeas₁ (a : I) : MeasurableSet (P₁ a) :=
    (h₁ a).measurableSet_seed_event G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a)
  have hmeas₂ (a : I) : MeasurableSet (P₂ a) :=
    (h₂ a).measurableSet_seed_event G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a)
  have hp (a : I) : μ.real (P₁ a ×ˢ P₂ a) =
      (∏ i : Fin k, (traceContactCount G (η₁ a) (y₁ (η₁ a)) (ωf a) x (c₁ a) (i.val+1):ℝ)⁻¹) *
      (∏ i : Fin k, (traceContactCount G (η₂ a) (y₂ (η₂ a)) (ωf a) x (c₂ a) (i.val+1):ℝ)⁻¹) := by
    rw [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      (h₁ a).seed_probability G hloc x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a) (hcap₁ a),
      (h₂ a).seed_probability G hloc x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a) (fun i hi hik => (hcap₂ a i hi hik).1)]
  conv_lhs => arg 2; ext a; rw [mul_assoc,← hp a]
  apply finite_event_mass_le μ (fun a => P₁ a ×ˢ P₂ a) (fun a => (hmeas₁ a).prod (hmeas₂ a)) w
  intro u
  let J := {a : I // u ∈ P₁ a ×ˢ P₂ a}
  have hb := finite_separated_weighted_second_moment_le G x k n M p Q
    (fun a : J => η₁ a.val) (fun a : J => η₂ a.val) y₁ y₂ success₁ success₂ m₁ m₂ hm₁ hm₂
    (chooseContact (finiteContactSeeds k u.1)) (chooseContact (finiteContactSeeds k u.2))
    (fun a : J => ω₁ a.val) (fun a : J => ω₂ a.val) (fun a : J => ωf a.val)
    (fun a : J => c₁ a.val) (fun a : J => c₂ a.val)
    (fun _ _ he => Subtype.ext (hir he)) (fun a => h₁ a.val) (fun a => h₂ a.val)
    (fun a => hc₁ a.val) (fun a => hc₂ a.val) (fun a => hsep a.val)
    (fun a => a.property.1) (fun a => a.property.2)
    (fun a => hbin a.val) (fun a => hcap₂ a.val) (fun a => hsc₁ a.val) (fun a => hsc₂ a.val)
    (fun a => hsω₁ a.val) (fun a => hsω₂ a.val) (fun a => hsη₁ a.val) (fun a => hsη₂ a.val)
    (fun a => hz₁ a.val) (fun a => hz₂ a.val)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  have he := Finset.sum_subtype (p := fun a => u ∈ P₁ a ×ˢ P₂ a) (F := inferInstance) (Finset.univ.filter (fun a => u ∈ P₁ a ×ˢ P₂ a))
    (by intro a; simp) w
  simpa [Finset.sum_filter,w] using he

end WeightedContactSecondMoment

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_TrajectoryMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
section OldPathWeight
attribute [local instance] Classical.propDecidable Classical.decEq


theorem finiteFieldIntegral_nonneg (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ finiteFieldIntegral Q p f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (finiteFieldWeight_nonneg Q p ω) (hf _)

theorem finiteFieldIntegral_sum {I : Type*} (Q : Finset E) (p : ℝ) (S : Finset I)
    (f : I → Set E → ℝ) :
    finiteFieldIntegral Q p (fun ω => ∑ i ∈ S, f i ω) =
      ∑ i ∈ S, finiteFieldIntegral Q p (f i) := by
  simp only [finiteFieldIntegral, Finset.mul_sum]
  exact Finset.sum_comm

 

theorem finiteFamilyIntegral_prod (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : ↥J → Set E → ℝ) :
    finiteFamilyIntegral Q J p (fun η => ∏ i : ↥J, f i (η i)) =
      ∏ i : ↥J, finiteFieldIntegral Q p (f i) := by
  simp only [finiteFamilyIntegral, finiteFamilyWeight, finiteFieldFamily_at,
    ← Finset.prod_mul_distrib, finiteFieldIntegral]
  exact (Fintype.prod_sum (fun (i : ↥J) (ω : FiniteField Q) =>
    finiteFieldWeight Q p ω * f i (finiteFieldSet Q ω))).symm



theorem oldPathWeight_integral (Q : Finset E) (k : ℕ) (p : ℝ)
    (q : Set E → V → V → ℝ) (y : ℕ → V) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (oldPathWeight k q y) =
      ∏ i : ↥(Finset.Icc 1 k), finiteFieldIntegral Q p (fun ω => q ω (y i) (y (i.val-1))) := by
  unfold oldPathWeight
  exact finiteFamilyIntegral_prod Q (Finset.Icc 1 k) p
    (fun i ω => q ω (y i) (y (i.val-1)))



end OldPathWeight

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}



theorem oldRunWeight_integral (Q : Finset E) (p : ℝ) (k : ℕ)
    (q : Set E → W → W → ℝ) (z : W) (y : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p
      (fun η => oldRunWeight (fun i => q (η i)) k z y) =
    oldRunWeight (fun _ => finiteOldKernel Q p q) k z y := by
  calc
    _ = finiteFamilyIntegral Q (Finset.Icc 1 k) p
        (fun η => oldPathWeight k q (oldRunVertices k z y) η) := by
      apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      exact (oldPathWeight_oldRunVertices k q η z y).symm
    _ = ∏ i : ↥(Finset.Icc 1 k), finiteOldKernel Q p q
        (oldRunVertices k z y i) (oldRunVertices k z y (i.val-1)) :=
      oldPathWeight_integral Q k p q _
    _ = oldRunWeight (fun _ => finiteOldKernel Q p q) k z y :=
      oldPathWeight_oldRunVertices k (fun (_ : Set E) => finiteOldKernel Q p q)
        (fun _ => ∅) z y



end IndependentOldRun

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P : Type*}



theorem sum_traceIndexMass [Nonempty E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (k M : ℕ) (Q : Finset E) (A : Finset (SpliceState E))
    (y : SpliceState E → ℕ → V) (s : ↥A)
    (hs : s.val ∈ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hy : y s.val 0 ∈ cluster G s.val.1 x)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (s.val.2 i) (y s.val i) (y s.val (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (s.val.2 i) (y s.val i)).Finite ∧
      (cluster G (s.val.2 i) (y s.val i)).ncard ≤ M) :
    (∑ c : ↥(finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q),
      traceIndexMass G x k Q A y ⟨s,c⟩) = 1 := by
  have hs' := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s.val).mp hs
  have hn := sum_finite_trace_probabilities G hloc x s.val.2 (y s.val) k M Q
    (fun i _ _ => hs'.2.1 i) hchain hcaps 0 (Nat.zero_le _) s.val.1 hy
    (cluster_finite_of_finite_edges G (Q.finite_toSet.subset hs'.1) x)
  rw [← Finset.sum_coe_sort (finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q)] at hn
  rw [← hn]
  apply Finset.sum_congr rfl
  intro c _
  have ht := ((mem_finiteTraceCodes_iff G x s.val.2 (y s.val) k 0 s.val.1 Q c.val).mp c.property).2
  have hf := ht.runMasks_first G x s.val.2 (y s.val) k 0 s.val.1 _ c.val s.val.2 (by intros; rfl)
  simp only [traceIndexMass,traceIndexOutput,hf]

 
theorem finiteChoiceForwardLoad_mean [Fintype P] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k M : ℕ) (Q : Finset E) (p : ℝ)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ)
    (hA : ∀ r, A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hy : ∀ r s, s ∈ A r → y r s 0 ∈ cluster G s.1 x)
    (hchain : ∀ r s, s ∈ A r → ∀ i ∈ Finset.Icc 1 k, Conn G (s.2 i) (y r s i) (y r s (i-1)))
    (hcaps : ∀ r s, s ∈ A r → ∀ i ∈ Finset.Icc 1 k,
      (cluster G (s.2 i) (y r s i)).Finite ∧ (cluster G (s.2 i) (y r s i)).ncard ≤ M) :
    (∑ t ∈ finiteSpliceDomain Q (Finset.Icc 1 k), spliceTupleWeight Q (Finset.Icc 1 k) p t *
      finiteChoiceForwardLoad G x k Q A y q t) =
      ∑ r, ∑ s ∈ A r, spliceTupleWeight Q (Finset.Icc 1 k) p s * q s r := by
  have hd := finiteInverseLoad_density G x k Q p
    (choiceTraceInput G x k Q A y) (choiceTraceOutput G x k Q A y)
    (choiceTraceCode G x k Q A y) (fun a => y a.1 a.2.1.val)
    (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1)
    (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).2)
    (choiceTraceMass G x k Q A y q) (finiteSpliceDomain Q (Finset.Icc 1 k))
    (fun a => traceIndexOutput_mem G x k Q (A a.1) (y a.1) (hA a.1) a.2) (fun _ => 1)
  simp only [mul_one] at hd
  unfold finiteChoiceForwardLoad
  rw [← hd,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.sum_sigma,← Finset.sum_coe_sort (A r)
    (fun s => spliceTupleWeight Q (Finset.Icc 1 k) p s * q s r)]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ c : ↥(finiteTraceCodes G x s.val.2 (y r s.val) k 0 s.val.1 Q),
    spliceTupleWeight Q (Finset.Icc 1 k) p s.val *
      (q s.val r * traceIndexMass G x k Q (A r) (y r) ⟨s,c⟩)) = _
  simp only [← mul_assoc,← Finset.mul_sum]
  rw [sum_traceIndexMass G hloc x k M Q (A r) (y r) s (hA r s.property)
    (hy r _ s.property) (hchain r _ s.property) (hcaps r _ s.property),mul_one]

end ChoiceForwardDensity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointRootMass
attribute [local instance] Classical.propDecidable Classical.decEq


theorem auxiliaryTupleWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (s : SpliceState E) : 0 ≤ auxiliaryTupleWeight Q J p s :=
  Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p



theorem sum_endpointRootMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (endpoint : I → V) (m : I → ℝ) (ω : Set E) (S : Finset V) :
    (∑ z ∈ S, endpointRootMass Q J p out endpoint m ω z) =
      ∑ a, if (out a).1 = ω ∧ endpoint a ∈ S then auxiliaryTupleWeight Q J p (out a) * m a else 0 := by
  simp only [endpointRootMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hr : (out a).1 = ω
  · simp only [hr,true_and,Finset.sum_ite_eq]
  · simp [hr]

end EndpointRootMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearPairMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_near_pair_mass_le_cover {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : unitInterval)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (hm₁ : ∀ a, 0 ≤ m₁ a) (hm₂ : ∀ b, 0 ≤ m₂ b)
    (endpoint : I₂ → V) (R : I₁ → I₂ → Prop) (S : I₁ → Finset V)
    (hS : ∀ a b, (out₁ a).1 = (out₂ b).1 → R a b → endpoint b ∈ S a) :
    (∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ R a b then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0) ≤
    ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a *
      ∑ z ∈ S a, endpointRootMass Q J₂ p out₂ endpoint m₂ (out₁ a).1 z := by
  apply Finset.sum_le_sum
  intro a _
  rw [sum_endpointRootMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  by_cases h : (out₁ a).1 = (out₂ b).1 ∧ R a b
  · have hh : (out₂ b).1 = (out₁ a).1 ∧ endpoint b ∈ S a :=
      ⟨h.1.symm,hS a b h.1 h.2⟩
    rw [ite_eq_left h,ite_eq_left hh]
    change (spliceTupleWeight Q J₁ p (out₁ a) * auxiliaryTupleWeight Q J₂ p (out₂ b)) *
      m₁ a * m₂ b ≤ _
    ring_nf
    exact le_refl _
  · rw [ite_eq_right h]
    apply mul_nonneg (mul_nonneg (spliceTupleWeight_nonneg Q J₁ p _) (hm₁ a))
    split_ifs
    · exact mul_nonneg (auxiliaryTupleWeight_nonneg Q J₂ p _) (hm₂ b)
    · exact le_refl 0

 

theorem finite_near_pair_mass_le {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : unitInterval)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (hm₁ : ∀ a, 0 ≤ m₁ a) (hm₂ : ∀ b, 0 ≤ m₂ b)
    (endpoint : I₂ → V) (R : I₁ → I₂ → Prop) (S : I₁ → Finset V)
    (hS : ∀ a b, (out₁ a).1 = (out₂ b).1 → R a b → endpoint b ∈ S a)
    (N : ℕ) (hN : ∀ a, (S a).card ≤ N) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a z, z ∈ S a → endpointRootMass Q J₂ p out₂ endpoint m₂ (out₁ a).1 z ≤ C) :
    (∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ R a b then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0) ≤
    (N:ℝ) * C * ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a := by
  apply (finite_near_pair_mass_le_cover Q J₁ J₂ p out₁ out₂ m₁ m₂ hm₁ hm₂ endpoint R S hS).trans
  calc
    _ ≤ ∑ a, spliceTupleWeight Q J₁ p (out₁ a) * m₁ a * ((N:ℝ)*C) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (spliceTupleWeight_nonneg Q J₁ p _) (hm₁ a))
      calc
        _ ≤ ∑ _z ∈ S a, C := Finset.sum_le_sum (fun z hz => hb a z hz)
        _ = ((S a).card:ℝ) * C := by simp
        _ ≤ (N:ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hN a) hC
    _ = _ := by rw [← Finset.sum_mul]; ring

end NearPairMass
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearHangingMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem SpliceTrace.head_hanging (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf) :
    hangingSide G ωf x e = cluster G ωf x \ cluster G ω x := by
  rw [hangingSide,h.head_cut G x η y k j i ω ωf e rest]

theorem SpliceTrace.head_hanging_cap (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i M : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hcaps : ∀ l, 1 ≤ l → l ≤ k →
      (cluster G (η l) (y l)).Finite ∧ (cluster G (η l) (y l)).ncard ≤ M) :
    (hangingSide G ωf x e).ncard ≤ k*M := by
  rw [h.head_hanging G x η y k j i ω ωf e rest]
  exact (h.added_finite_cap G x η y k j M ω ωf ((i,e)::rest) hcaps).2



end NearHangingMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldRunArrival
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]

theorem oldRunArrival_nonneg (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (k : ℕ) (z : W) (A : Finset W) : 0 ≤ oldRunArrival K k z A := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact oldRunWeight_nonneg K hK k z y
  · exact le_refl 0

theorem oldRunArrival_zero (K : ℕ → W → W → ℝ) (z : W) (A : Finset W) :
    oldRunArrival K 0 z A = if z ∈ A then 1 else 0 := by
  by_cases h : z ∈ A
  · simp [oldRunArrival,oldRunVertices,oldRunWeight,h]
  · simp [oldRunArrival,oldRunVertices,h]

theorem oldRunArrival_succ (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (A : Finset W) :
    oldRunArrival K (k+1) z A = ∑ a, K (k+1) z a * oldRunArrival K k a A := by
  unfold oldRunArrival
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun y => if oldRunVertices k y.1 y.2 0 ∈ A then
      K (k+1) z y.1 * oldRunWeight K k y.1 y.2 else 0)
    (by
      intro y
      by_cases h : oldRunVertices k (y 0) (Fin.tail y) 0 ∈ A
      · simp [oldRunVertices_succ_of_le k z y 0 (Nat.zero_le k),oldRunConsEquiv,oldRunWeight,h]
      · simp [oldRunVertices_succ_of_le k z y 0 (Nat.zero_le k),oldRunConsEquiv,h]),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum,mul_ite,mul_zero]

 

theorem sum_oldRunArrival_le (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (u : ℝ) (hu : 0 ≤ u) (hcol : ∀ i b, ∑ a, K i a b ≤ u) (k : ℕ) (A : Finset W) :
    (∑ z, oldRunArrival K k z A) ≤ (A.card:ℝ) * u^k := by
  induction k with
  | zero => simp [oldRunArrival_zero]
  | succ k ih =>
    simp only [oldRunArrival_succ]
    rw [Finset.sum_comm]
    calc
      _ = ∑ a, (∑ z, K (k+1) z a) * oldRunArrival K k a A := by
        simp only [Finset.sum_mul]
      _ ≤ ∑ a, u * oldRunArrival K k a A := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hcol _ _) (oldRunArrival_nonneg K hK k a A)
      _ = u * ∑ a, oldRunArrival K k a A := (Finset.mul_sum _ _ _).symm
      _ ≤ u*((A.card:ℝ)*u^k) := mul_le_mul_of_nonneg_left ih hu
      _ = (A.card:ℝ)*u^(k+1) := by ring


end OldRunArrival

end Percolation

 
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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteTrajectoryMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]

theorem finiteTrajectoryHit_le_sum (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : unitInterval) (k : ℕ) (q : Set E → W → W → ℝ)
    (hq : ∀ ω a b, 0 ≤ q ω a b) (z : W) (A : Finset V) :
    finiteTrajectoryHit G e Q p k q z A ≤ ∑ a ∈ A, finiteTrajectoryMass G e Q p k q z a := by
  unfold finiteTrajectoryHit finiteTrajectoryMass
  rw [← finiteFamilyIntegral_sum]
  apply finiteFamilyIntegral_mono
  intro η
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y _
  have hn := oldRunWeight_nonneg (fun i => q (η i)) (fun _ => hq _) k z y
  by_cases h : ((A:Set V) ∩ trajectoryUnion G η (e ∘ oldRunVertices k z y) k).Nonempty
  · rw [ite_eq_left h]
    obtain ⟨a,ha,hat⟩ := h
    have hs := Finset.single_le_sum (s := A)
      (f := fun a => if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k then
        oldRunWeight (fun i => q (η i)) k z y else 0)
      (fun a _ => by split_ifs; exact hn; exact le_refl 0) ha
    simpa only [ite_eq_left hat] using hs
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg fun a _ => by split_ifs; exact hn; exact le_refl 0



end FiniteTrajectoryMass

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_EndpointKernels
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
section SeparatedTracePair
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_trace_pair_separated_le [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ)
    (Q : Finset E) (p : unitInterval)
    (A₁ A₂ : Finset (SpliceState E)) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (hA₁ : A₁ ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hA₂ : A₂ ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hbin : ∀ s ∈ A₁, (cluster G s.1 x).Finite ∧ n ≤ (cluster G s.1 x).ncard ∧
      (cluster G s.1 x).ncard < 2*n)
    (hcap₁ : ∀ s ∈ A₁, ∀ i, 1 ≤ i → i ≤ k → (cluster G (s.2 i) (y₁ s.2 i)).Finite)
    (hcap₂ : ∀ s ∈ A₂, ∀ i, 1 ≤ i → i ≤ k → (cluster G (s.2 i) (y₂ s.2 i)).Finite ∧
      (cluster G (s.2 i) (y₂ s.2 i)).ncard ≤ M) :
    (∑ a : FiniteTraceIndex G x k Q A₁ (fun s => y₁ s.2),
      ∑ b : FiniteTraceIndex G x k Q A₂ (fun s => y₂ s.2),
      if (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 =
          (traceIndexOutput G x k Q A₂ (fun s => y₂ s.2) b).1 ∧
        a.2.val ≠ [] ∧ b.2.val ≠ [] ∧
        GraphSeparated G
          (cluster G (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 x \ cluster G a.1.val.1 x)
          (cluster G (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 x \ cluster G b.1.val.1 x)
      then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
        (pairSpliceOutput (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a)
          (traceIndexOutput G x k Q A₂ (fun s => y₂ s.2) b)) *
        (m₁ a.1.val.2 * traceIndexMass G x k Q A₁ (fun s => y₁ s.2) a) *
        (m₂ b.1.val.2 * traceIndexMass G x k Q A₂ (fun s => y₂ s.2) b) else 0) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let T₁ := FiniteTraceIndex G x k Q A₁ (fun s => y₁ s.2)
  let T₂ := FiniteTraceIndex G x k Q A₂ (fun s => y₂ s.2)
  let out₁ := traceIndexOutput G x k Q A₁ (fun s => y₁ s.2)
  let out₂ := traceIndexOutput G x k Q A₂ (fun s => y₂ s.2)
  let P (a : T₁ × T₂) := (out₁ a.1).1 = (out₂ a.2).1 ∧ a.1.2.val ≠ [] ∧ a.2.2.val ≠ [] ∧
    GraphSeparated G (cluster G (out₁ a.1).1 x \ cluster G a.1.1.val.1 x)
      (cluster G (out₁ a.1).1 x \ cluster G a.2.1.val.1 x)
  let I := {a : T₁ × T₂ // P a}
  let η₁ (a : I) := a.val.1.1.val.2
  let η₂ (a : I) := a.val.2.1.val.2
  let ω₁ (a : I) := a.val.1.1.val.1
  let ω₂ (a : I) := a.val.2.1.val.1
  let ωf (a : I) := (out₁ a.val.1).1
  let c₁ (a : I) := a.val.1.2.val
  let c₂ (a : I) := a.val.2.2.val
  have hout (a : I) : jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) = pairSpliceOutput (out₁ a.val.1) (out₂ a.val.2) := rfl
  have hinj : Function.Injective (fun a : I =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),c₁ a,c₂ a)) := by
    intro a b he
    dsimp only at he
    rw [hout a,hout b] at he
    have ho₁ : out₁ a.val.1 = out₁ b.val.1 := Prod.ext
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.1) he)
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.2.1) he)
    have ho₂ : out₂ a.val.2 = out₂ b.val.2 := Prod.ext
      (a.property.1.symm.trans ((congrArg Prod.fst ho₁).trans b.property.1))
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.2.2) he)
    apply Subtype.ext
    exact Prod.ext
      (traceIndex_output_code_injective G x k Q A₁ (fun s => y₁ s.2)
        (Prod.ext ho₁ (congrArg (fun z => z.2.1) he)))
      (traceIndex_output_code_injective G x k Q A₂ (fun s => y₂ s.2)
        (Prod.ext ho₂ (congrArg (fun z => z.2.2) he)))
  have htr₁ (a : I) : SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a) :=
    (traceIndex_valid G x k Q A₁ (fun s => y₁ s.2) a.val.1).1
  have htr₂ (a : I) : SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a) := by
    change SpliceTrace G x _ _ _ _ _ _ (out₁ a.val.1).1
    rw [a.property.1]
    exact (traceIndex_valid G x k Q A₂ (fun s => y₂ s.2) a.val.2).1
  have hs₁ (a : I) := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp (hA₁ a.val.1.1.property)
  have hs₂ (a : I) := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp (hA₂ a.val.2.1.property)
  have hb := finite_separated_weighted_contact_second_moment_le G hloc x k n M p Q η₁ η₂ y₁ y₂
    (fun _ => True) (fun _ => True) m₁ m₂ hm₁ hm₂ ω₁ ω₂ ωf c₁ c₂ hinj htr₁ htr₂
    (fun a => a.property.2.1) (fun a => a.property.2.2.1) (fun a => a.property.2.2.2)
    (fun a => hbin _ a.val.1.1.property) (fun a => hcap₁ _ a.val.1.1.property)
    (fun a => hcap₂ _ a.val.2.1.property) (fun _ => trivial) (fun _ => trivial)
    (fun a => (hs₁ a).1) (fun a => (hs₂ a).1) (fun a => (hs₁ a).2.1)
    (fun a => (hs₂ a).2.1) (fun a => (hs₁ a).2.2) (fun a => (hs₂ a).2.2)
  simp only [true_and] at hb
  apply le_trans _ hb
  let w (a : T₁ × T₂) := jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    (pairSpliceOutput (out₁ a.1) (out₂ a.2)) *
    (m₁ a.1.1.val.2 * traceIndexMass G x k Q A₁ (fun s => y₁ s.2) a.1) *
    (m₂ a.2.1.val.2 * traceIndexMass G x k Q A₂ (fun s => y₂ s.2) a.2)
  have he := Finset.sum_subtype (p := P) (F := inferInstance) (Finset.univ.filter P)
    (by intro a; simp) w
  rw [Finset.sum_filter,Fintype.sum_prod_type] at he
  change (∑ a : T₁, ∑ b : T₂, if P (a,b) then w (a,b) else 0) ≤ _
  rw [he]
  apply Finset.sum_le_sum
  intro a _
  rw [hout a]
  change w a.val ≤ _
  simp only [w,traceIndexMass,η₁,η₂,ωf,c₁,c₂,out₁,out₂]
  rw [← a.property.1]
  exact le_of_eq (by ring)

end SeparatedTracePair

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceSeparatedMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P₁ P₂ : Type*} [Fintype P₁] [Fintype P₂]



theorem finiteChoiceSeparatedPairMass_le [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ)
    (Q : Finset E) (p : unitInterval)
    (A₁ : P₁ → Finset (SpliceState E)) (A₂ : P₂ → Finset (SpliceState E))
    (y₁ : P₁ → (ℕ → Set E) → ℕ → V) (y₂ : P₂ → (ℕ → Set E) → ℕ → V)
    (m₁ : P₁ → (ℕ → Set E) → ℝ) (m₂ : P₂ → (ℕ → Set E) → ℝ)
    (hm₁ : ∀ r η, 0 ≤ m₁ r η) (hm₂ : ∀ r η, 0 ≤ m₂ r η)
    (hA₁ : ∀ r, A₁ r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hA₂ : ∀ r, A₂ r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hbin : ∀ r s, s ∈ A₁ r → (cluster G s.1 x).Finite ∧ n ≤ (cluster G s.1 x).ncard ∧
      (cluster G s.1 x).ncard < 2*n)
    (hcap₁ : ∀ r s, s ∈ A₁ r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y₁ r s.2 i)).Finite)
    (hcap₂ : ∀ r s, s ∈ A₂ r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y₂ r s.2 i)).Finite ∧ (cluster G (s.2 i) (y₂ r s.2 i)).ncard ≤ M) :
    finiteChoiceSeparatedPairMass G x k Q p A₁ A₂ y₁ y₂ m₁ m₂ ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteChoiceHit G k Q p y₁ m₁ (cluster G (finiteFieldSet Q ω) x) *
        finiteChoiceHit G k Q p y₂ m₂ (cluster G (finiteFieldSet Q ω) x) else 0) := by
  let R (ω : FiniteField Q) := (cluster G (finiteFieldSet Q ω) x).Finite ∧
    n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
    (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  let H₁ (r : P₁) (ω : FiniteField Q) := finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ r η) k).Nonempty then m₁ r η else 0)
  let H₂ (r : P₂) (ω : FiniteField Q) := finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ r η) k).Nonempty then m₂ r η else 0)
  have hb : finiteChoiceSeparatedPairMass G x k Q p A₁ A₂ y₁ y₂ m₁ m₂ ≤
      ∑ r : P₁, ∑ s : P₂, ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
        (if R ω then H₁ r ω * H₂ s ω else 0) := by
    unfold finiteChoiceSeparatedPairMass
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro r _
    conv_lhs => arg 2; ext a; rw [Fintype.sum_sigma]
    conv_lhs => rw [Finset.sum_comm]
    simp only [choiceTraceOutput,choiceTraceInput,choiceTraceCode,choiceTraceMass,
      traceIndexInput,traceIndexCode]
    apply Finset.sum_le_sum
    intro s _
    exact finite_trace_pair_separated_le G hloc x k n M Q p (A₁ r) (A₂ s)
      (y₁ r) (y₂ s) (m₁ r) (m₂ s) (hm₁ r) (hm₂ s) (hA₁ r) (hA₂ s)
      (hbin r) (hcap₁ r) (hcap₂ s)
  apply hb.trans_eq
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext s; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  change (∑ s : P₂, ∑ r : P₁, finiteFieldWeight Q p ω * (if R ω then H₁ r ω * H₂ s ω else 0)) =
    finiteFieldWeight Q p ω * (if R ω then (∑ r : P₁, H₁ r ω) * (∑ s : P₂, H₂ s ω) else 0)
  by_cases h : R ω
  · simp only [ite_eq_left h,← Finset.mul_sum,← Finset.sum_mul]
  · simp only [ite_eq_right h,mul_zero,Finset.sum_const_zero]

end ChoiceSeparatedMass

end Percolation

 
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



theorem kernel_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) :
    0 ≤ q.kernel p x y := integral_nonneg (fun ω => q.nonneg ω x y)

theorem kernel_outside_ball_zero (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V)
    (hy : y ∉ reachBall G x M) : q.kernel p x y = 0 := by
  simp only [kernel,q.outside_ball_zero _ x y hy,integral_zero]

theorem summable_kernel (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Summable (q.kernel p x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  apply q.kernel_outside_ball_zero p x y
  simpa only [Set.Finite.mem_toFinset] using hy

 

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

 

theorem outside_reverse_ball_zero (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V)
    (hx : x ∉ reachBall G y M) : q.mass ω x y = 0 := by
  by_contra h
  obtain ⟨_,_,hc,hfin,hcap,_⟩ := q.support ω x y h
  have he := cluster_eq_of_conn G ω hc
  rw [he] at hfin hcap
  exact hx (finite_cluster_subset_reachBall G ω y hfin M hcap (conn_symm G ω hc))

theorem kernel_outside_reverse_ball_zero (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x y : V) (hx : x ∉ reachBall G y M) : q.kernel p x y = 0 := by
  simp only [kernel,q.outside_reverse_ball_zero _ x y hx,integral_zero]

theorem summable_kernel_column (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (y : V) :
    Summable (fun x => q.kernel p x y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y M).toFinset)
  intro x hx
  apply q.kernel_outside_reverse_ball_zero p x y
  simpa only [Set.Finite.mem_toFinset] using hx

theorem mass_zero_of_start_not_mem (q : LocalEndpointRule G hloc O M L) (ω : Set E)
    (x y : V) (hx : x ∉ O) : q.mass ω x y = 0 := by
  by_contra h
  exact hx (q.support ω x y h).1

theorem mass_zero_of_end_not_mem (q : LocalEndpointRule G hloc O M L) (ω : Set E)
    (x y : V) (hy : y ∉ O) : q.mass ω x y = 0 := by
  by_contra h
  exact hy (q.support ω x y h).2.1

theorem kernel_zero_of_start_not_mem (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (x y : V) (hx : x ∉ O) : q.kernel p x y = 0 := by
  simp only [kernel,q.mass_zero_of_start_not_mem _ x y hx,integral_zero]

theorem kernel_zero_of_end_not_mem (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (x y : V) (hy : y ∉ O) : q.kernel p x y = 0 := by
  simp only [kernel,q.mass_zero_of_end_not_mem _ x y hy,integral_zero]

 

theorem kernel_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (x y : V) :
    q.kernel p (a x) (a y) = q.kernel p x y := by
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable
    (q.measurable_mass x y).aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [kernel,q.covariance a b ha] using h.symm

theorem successProbability_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    0 ≤ q.successProbability p x := tsum_nonneg (q.kernel_nonneg p x)

theorem successProbability_le_one (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    q.successProbability p x ≤ 1 := q.kernel_row_le_one p x

theorem successProbability_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (x : V) :
    q.successProbability p (a x) = q.successProbability p x := by
  unfold successProbability
  rw [← a.tsum_eq (fun y => q.kernel p (a x) y)]
  exact tsum_congr (q.kernel_covariant p a b ha x)

theorem successProbability_orbit (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (o x : V) (hx : x ∈ vertexOrbit G o) : q.successProbability p x = q.successProbability p o := by
  obtain ⟨a,b,ha,rfl⟩ := hx
  exact q.successProbability_covariant p a b ha o

theorem kernel_column_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (y : V) :
    (∑' x, q.kernel p x (a y)) = ∑' x, q.kernel p x y := by
  rw [← a.tsum_eq (fun x => q.kernel p x (a y))]
  exact tsum_congr (fun x => q.kernel_covariant p a b ha x y)

end LocalEndpointRule
end LocalEndpointKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointTransport
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem kernel_column_orbit (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (y : V) (hy : y ∈ vertexOrbit G o) :
    (∑' x, q.kernel p x y) = ∑' x, q.kernel p x o := by
  obtain ⟨a,b,ha,rfl⟩ := hy
  exact q.kernel_column_covariant p a b ha o

 

theorem kernel_column_eq_success {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (y : V) (hy : y ∈ vertexOrbit G (root i₀)) :
    (∑' x, q.kernel p x y) = q.successProbability p (root i₀) := by
  let O := vertexOrbit G (root i₀)
  let w : ι → ℝ := fun i => if root i ∈ O then weight i else 0
  have ho : root i₀ ∈ O := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have hw' (i : ι) : 0 ≤ w i := by
    dsimp [w]
    split_ifs
    · exact hw i
    · exact le_rfl
  have hpos : 0 < ∑ i, w i := by
    have hi : w i₀ ≤ ∑ i, w i := Finset.single_le_sum (fun i _ => hw' i) (Finset.mem_univ i₀)
    have he : w i₀ = weight i₀ := ite_eq_left ho
    rw [he] at hi
    exact hw₀.trans_le hi
  have ht := htr.real root weight Γ (q.kernel p)
    (by intro a ha x z; obtain ⟨b,hb⟩ := hΓ a ha; exact q.kernel_covariant p a b hb x z)
    (q.summable_kernel p) (q.summable_kernel_column p)
  have hr (i : ι) : weight i * (∑' z, q.kernel p (root i) z) =
      w i * q.successProbability p (root i₀) := by
    by_cases hi : root i ∈ O
    · have he := q.successProbability_orbit p (root i₀) (root i) hi
      change weight i * q.successProbability p (root i) = _
      rw [he]
      simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' z, q.kernel p (root i) z) = 0 := by
        simp only [q.kernel_zero_of_start_not_mem p _ _ hi,tsum_zero]
      rw [he,mul_zero]
  have hc (i : ι) : weight i * (∑' x, q.kernel p x (root i)) =
      w i * (∑' x, q.kernel p x (root i₀)) := by
    by_cases hi : root i ∈ O
    · rw [q.kernel_column_orbit (root i₀) p (root i) hi]
      simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' x, q.kernel p x (root i)) = 0 := by
        simp only [q.kernel_zero_of_end_not_mem p _ _ hi,tsum_zero]
      rw [he,mul_zero]
  simp_rw [hr,hc] at ht
  rw [← Finset.sum_mul,← Finset.sum_mul] at ht
  rw [q.kernel_column_orbit (root i₀) p y hy]
  exact (mul_left_cancel₀ (ne_of_gt hpos) ht).symm

 
theorem kernel_column_le_success {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (y : V) :
    (∑' x, q.kernel p x y) ≤ q.successProbability p (root i₀) := by
  by_cases hy : y ∈ vertexOrbit G (root i₀)
  · exact (q.kernel_column_eq_success root weight Γ htr hΓ hw i₀ hw₀ p y hy).le
  · simpa only [q.kernel_zero_of_end_not_mem p _ _ hy,tsum_zero] using
      q.successProbability_nonneg p (root i₀)

end LocalEndpointRule
end EndpointTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointSchur
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem kernel_row_le_success (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval) (x : V) :
    (∑' y, q.kernel p x y) ≤ q.successProbability p o := by
  by_cases hx : x ∈ vertexOrbit G o
  · exact (q.successProbability_orbit p o x hx).le
  · simpa only [q.kernel_zero_of_start_not_mem p _ _ hx,tsum_zero] using
      q.successProbability_nonneg p o


end LocalEndpointRule
end EndpointSchur

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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedLocalLoad
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem row_nonneg (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) : 0 ≤ q.row ω x :=
  tsum_nonneg (q.nonneg ω x)

theorem integrable_mass (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) :
    Integrable (fun ω => q.mass ω x y) (law p) :=
  integrable_finite_local _ p _ (q.locality · x y)

theorem integrable_row (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.row ω x) (law p) :=
  integrable_finite_local _ p _ (q.row_locality · x)

theorem integrable_sq_row (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.row ω x ^ 2) (law p) :=
  integrable_finite_local _ p _ (fun ω => congrArg (· ^ 2) (q.row_locality ω x))



end CappedLocalLoad
end CappedLocalLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TruncationLoss
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem cap_of_row_ne_zero (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V)
    (hr : q.row ω x ≠ 0) : (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M := by
  obtain ⟨y,hy⟩ : ∃ y, q.mass ω x y ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hr (by simp only [row,hn,tsum_zero])
  exact (q.support ω x y hy).2.2.2

theorem truncate_scaled_row (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x : V) :
    b * (∑' y, (q.truncate b hb L).mass ω x y) =
      if q.row ω x ≤ b ∧ CappedGoodness G ω x M L then q.row ω x else 0 := by
  by_cases h : q.row ω x ≤ b ∧ CappedGoodness G ω x M L
  · simp only [truncate,ite_eq_left h,tsum_mul_left,← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul]
    rfl
  · simp only [truncate,ite_eq_right h,tsum_zero,mul_zero]

theorem truncate_mass_le (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x y : V) :
    (q.truncate b hb L).mass ω x y ≤ b⁻¹ * q.mass ω x y := by
  change (if _ then _ else _) ≤ _
  split_ifs
  · rfl
  · exact mul_nonneg (inv_nonneg.mpr hb.le) (q.nonneg ω x y)

 

theorem truncate_pointwise_loss (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x : V) :
    q.row ω x ≤ b * (∑' y, (q.truncate b hb L).mass ω x y) + q.row ω x ^ 2 / b +
      b * ({η | CappedBadGoodness G η x M L}.indicator (1 : Set E → ℝ) ω) := by
  rw [q.truncate_scaled_row b hb L]
  have hs : 0 ≤ q.row ω x ^ 2 / b := div_nonneg (sq_nonneg _) hb.le
  have hi : 0 ≤ ({η | CappedBadGoodness G η x M L}.indicator (1 : Set E → ℝ) ω) := by
    apply Set.indicator_nonneg
    intro η _
    norm_num
  by_cases hr : q.row ω x ≤ b
  · by_cases hg : CappedGoodness G ω x M L
    · simp only [hr,hg,and_self,if_true]
      nlinarith
    · simp only [hg,and_false,if_false,zero_add]
      by_cases hz : q.row ω x = 0
      · rw [hz]
        positivity
      · have hc := q.cap_of_row_ne_zero ω x hz
        have hbad : CappedBadGoodness G ω x M L := ⟨hc.1,hc.2,fun h => hg ⟨hc.1,hc.2,h⟩⟩
        rw [Set.indicator_of_mem (show ω ∈ {η | CappedBadGoodness G η x M L} from hbad)]
        change q.row ω x ≤ q.row ω x ^ 2 / b + b * 1
        linarith
  · simp only [hr,false_and,if_false,zero_add]
    have htail : q.row ω x ≤ q.row ω x ^ 2 / b := by
      apply (le_div_iff₀ hb).mpr
      have ht := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hr)) (q.row_nonneg ω x)
      nlinarith
    exact htail.trans (le_add_of_nonneg_right (mul_nonneg hb.le hi))

 

theorem truncate_mean_loss (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x : V) :
    (∫ ω, q.row ω x ∂law p) ≤ b * (q.truncate b hb L).successProbability p x +
      (∫ ω, q.row ω x ^ 2 ∂law p) / b + b * (law p).real {ω | CappedBadGoodness G ω x M L} := by
  let t := q.truncate b hb L
  have ht : Integrable (fun ω => ∑' y, t.mass ω x y) (law p) := by
    apply integrable_finite_local
      (incidentSupport G hloc (finite_reachBall hloc x t.radius).toFinset) p
    intro ω
    exact tsum_congr (t.locality ω x)
  have hbad := measurableSet_cappedBadGoodness G hloc x M L
  have hi : Integrable ({ω | CappedBadGoodness G ω x M L}.indicator (1 : Set E → ℝ)) (law p) :=
    (integrable_const (1:ℝ)).indicator hbad
  have h := integral_mono (q.integrable_row p x)
    (((ht.const_mul b).add ((q.integrable_sq_row p x).div_const b)).add (hi.const_mul b))
    (q.truncate_pointwise_loss b hb L · x)
  dsimp only [Pi.add_apply] at h
  have he₁ := integral_add ((ht.const_mul b).add ((q.integrable_sq_row p x).div_const b)) (hi.const_mul b)
  have he₂ := integral_add (ht.const_mul b) ((q.integrable_sq_row p x).div_const b)
  dsimp only [Pi.add_apply] at he₁ he₂
  rw [he₁,he₂,integral_const_mul,integral_div,integral_const_mul,
    integral_indicator_one hbad] at h
  rw [← t.kernel_row_integral p x] at h
  exact h

theorem truncate_success_lower (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x : V) (a : ℝ)
    (hmean : a ≤ ∫ ω, q.row ω x ∂law p)
    (hmoment : (∫ ω, q.row ω x ^ 2 ∂law p) / b ≤ a/4)
    (hbad : b * (law p).real {ω | CappedBadGoodness G ω x M L} ≤ a/4) :
    a / (2*b) ≤ (q.truncate b hb L).successProbability p x := by
  have hh := q.truncate_mean_loss p b hb L x
  apply (div_le_iff₀ (mul_pos (by norm_num) hb)).mpr
  nlinarith

end CappedLocalLoad
end TruncationLoss

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Amplification
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
open MeasureTheory
section AmplificationMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem amplificationMarginal_mean [Nonempty E] (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      ∑ r, ∑ s ∈ q.amplificationInputs Q B x k n z r,
        spliceTupleWeight Q (Finset.Icc 1 k) p s * q.amplificationWeight B k z s r := by
  rw [integral_finite_local Q p _ (q.amplificationMarginal_local Q B x k n z p)]
  simp only [amplificationMarginal,restrictFiniteField_fieldSet]
  rw [finiteRootLoad_mean]
  apply finiteChoiceForwardLoad_mean G hloc x k M Q p
  · exact q.amplificationInputs_subset Q B x k n z
  · intro r s hs
    exact ((q.mem_amplificationInputs Q B x k n z r s).mp hs).2.2.2.2.2.1
  · intro r s hs i hi
    exact (q.amplificationInputs_chain Q B x k n z r s hs i
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).1
  · intro r s hs i hi
    have hc := q.amplificationInputs_chain Q B x k n z r s hs i
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
    exact ⟨hc.2.1,hc.2.2.1⟩

end LocalEndpointRule
end AmplificationMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMeanKernel
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finiteSpliceDomain_integral_factor (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : Set E → ℝ) (g : (ℕ → Set E) → ℝ) :
    (∑ s ∈ finiteSpliceDomain Q J, spliceTupleWeight Q J p s * f s.1 * g s.2) =
      finiteFieldIntegral Q p f * finiteFamilyIntegral Q J p g := by
  have hh := finiteRootLoad_mean Q J p (fun s => f s.1 * g s.2)
  simp only [← mul_assoc] at hh
  rw [← hh]
  simp only [finiteRootLoad,finiteFieldIntegral,finiteFamilyIntegral,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  ring


namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem finiteOldKernel_eq_kernel (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (p : unitInterval) (a b : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    finiteOldKernel Q p q.mass a b = q.kernel p a b := by
  symm
  exact integral_finite_local Q p _ (finite_local_of_subset _ Q hQ _ (q.locality · a b))

 

theorem amplificationMarginal_mean_kernel [Nonempty E] (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ O) (hz : z.val ∈ O)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      ∑ r : Fin k → ↥B, finiteBinConnection G Q p x n (amplificationVertices B k z r 0) *
        oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r := by
  rw [q.amplificationMarginal_mean Q B x k n z p]
  apply Finset.sum_congr rfl
  intro r _
  let f : Set E → ℝ := fun ω => if n ≤ (cluster G ω x).ncard ∧
      (cluster G ω x).ncard < 2*n ∧ amplificationVertices B k z r 0 ∈ cluster G ω x then 1 else 0
  let g : (ℕ → Set E) → ℝ := fun η =>
    oldRunWeight (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z r
  have he : (∑ s ∈ q.amplificationInputs Q B x k n z r,
      spliceTupleWeight Q (Finset.Icc 1 k) p s * q.amplificationWeight B k z s r) =
      ∑ s ∈ finiteSpliceDomain Q (Finset.Icc 1 k), spliceTupleWeight Q (Finset.Icc 1 k) p s * f s.1 * g s.2 := by
    rw [amplificationInputs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    change (if _ then _ else _) = _
    by_cases hw : q.amplificationWeight B k z s r = 0
    · have hg : g s.2 = 0 := hw
      simp [hx,hz,hw,hg]
    · simp only [hx,hz,true_and,hw,ne_eq,not_false_eq_true,and_true]
      by_cases hbin : n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
          amplificationVertices B k z r 0 ∈ cluster G s.1 x
      · simp [f,hbin,g,amplificationWeight]
      · simp only [hbin,if_false,f,mul_zero,zero_mul]
  rw [he,finiteSpliceDomain_integral_factor]
  dsimp only [g]
  rw [oldRunWeight_integral Q p k (fun ω (a b : ↥B) => q.mass ω a.val b.val) z r]
  change finiteBinConnection G Q p x n _ * _ = _
  congr 1
  apply congrArg (fun K : ℕ → ↥B → ↥B → ℝ => oldRunWeight K k z r)
  funext i a b
  exact q.finiteOldKernel_eq_kernel Q p a.val b.val (hQ a.val a.property)

end LocalEndpointRule
end AmplificationMeanKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinConnection
attribute [local instance] Classical.propDecidable Classical.decEq



theorem binConnectionMass_nonneg (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) :
    0 ≤ binConnectionMass G n ω x y := by unfold binConnectionMass; split_ifs <;> norm_num

theorem binConnectionMass_symm (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) :
    binConnectionMass G n ω x y = binConnectionMass G n ω y x := by
  by_cases hc : Conn G ω x y
  · have he := cluster_eq_of_conn G ω hc
    simp only [binConnectionMass,hc,conn_symm G ω hc,and_true,he]
  · have hc' : ¬Conn G ω y x := fun h => hc (conn_symm G ω h)
    simp only [binConnectionMass,hc,hc',and_false,if_false]

theorem binConnectionMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binConnectionMass G n ω x y = binConnectionMass G n (ω ∩ (Q : Set E)) x y := by
  dsimp only
  let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
  have hp : ((cluster G ω x).Finite ∧ n ≤ (cluster G ω x).ncard ∧
      (cluster G ω x).ncard < 2*n ∧ Conn G ω x y) ↔
      ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧ n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard ∧
      (cluster G (ω ∩ (Q : Set E)) x).ncard < 2*n ∧ Conn G (ω ∩ (Q : Set E)) x y) := by
    constructor
    · rintro ⟨hf,hn,hN,hc⟩
      have hs : cluster G ω x ⊆ (finite_reachBall hloc x (2*n)).toFinset := by
        simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hf (2*n) hN.le
      have he := cluster_restrict_incident_of_full G hloc _ ω x hs
      change cluster G (ω ∩ (Q : Set E)) x = cluster G ω x at he
      refine ⟨he.symm ▸ hf,he.symm ▸ hn,he.symm ▸ hN,?_⟩
      change y ∈ cluster G (ω ∩ (Q : Set E)) x
      rw [he]
      exact hc
    · rintro ⟨hf,hn,hN,hc⟩
      have he := cluster_restrict_of_cap G hloc Q ω x (2*n) (Finset.Subset.refl _) hf hN.le
      exact ⟨he ▸ hf,he ▸ hn,he ▸ hN,conn_mono G Set.inter_subset_left hc⟩
  exact if_congr hp rfl rfl

theorem binConnectionMass_support (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (h : binConnectionMass G n ω x y ≠ 0) :
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard < 2*n ∧ Conn G ω x y := by
  unfold binConnectionMass at h
  split_ifs at h with hp
  · exact ⟨hp.1,hp.2.2.1,hp.2.2.2⟩
  · exact (h rfl).elim

theorem binConnectionMass_outside (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binConnectionMass G n ω x y = 0 := by
  by_contra h
  obtain ⟨hf,hN,hc⟩ := binConnectionMass_support G n ω x y h
  exact hy (finite_cluster_subset_reachBall G ω x hf (2*n) hN.le hc)

theorem binConnection_nonneg (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) :
    0 ≤ binConnection G p n x y := integral_nonneg fun ω => binConnectionMass_nonneg G n ω x y

theorem binConnection_symm (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) :
    binConnection G p n x y = binConnection G p n y x :=
  integral_congr_ae (ae_of_all _ fun ω => binConnectionMass_symm G n ω x y)

theorem binConnection_outside (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binConnection G p n x y = 0 := by
  simp only [binConnection,fun ω => binConnectionMass_outside G n ω x y hy,integral_zero]

end BinConnection

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteBinConnection
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteBinConnection_eq_binConnection (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (p : unitInterval) (x : V) (n : ℕ) (y : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q) :
    finiteBinConnection G Q p x n y = binConnection G p n x y := by
  rw [binConnection, integral_finite_local Q p _
    (finite_local_of_subset _ Q hQ _ (fun ω => binConnectionMass_local G hloc n ω x y))]
  unfold finiteBinConnection finiteFieldIntegral
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  have hf : (cluster G (finiteFieldSet Q ω) x).Finite :=
    cluster_finite_of_finite_edges G ω.val.finite_toSet x
  unfold cluster at hf
  simp only [binConnectionMass,cluster,Set.mem_ofPred_eq,hf,true_and]
  exact if_congr Iff.rfl rfl rfl

end FiniteBinConnection

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePathOperator
attribute [local instance] Classical.propDecidable Classical.decEq


namespace PositiveRealMatrix
variable {A H : Hilbert V →L[ℂ] Hilbert V}

theorem real (hA : PositiveRealMatrix A) (x y : V) :
    matrixCoeff A x y = ((matrixCoeff A x y).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (hA x y).1

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

theorem star (hA : PositiveRealMatrix A) : PositiveRealMatrix (star A) := by
  intro x y
  simpa only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_im,Complex.conj_re,neg_eq_zero] using hA y x

end PositiveRealMatrix

 

theorem oldRun_test_succ {W : Type*} [Fintype W]
    (K : ℕ → W → W → ℝ) (F : W → ℝ) (k : ℕ) (z : W) :
    (∑ r : Fin (k+1) → W, oldRunWeight K (k+1) z r * F (oldRunVertices (k+1) z r 0)) =
      ∑ a : W, K (k+1) z a *
        ∑ r : Fin k → W, oldRunWeight K k a r * F (oldRunVertices k a r 0) := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun r => K (k+1) z r.1 * oldRunWeight K k r.1 r.2 * F (oldRunVertices k r.1 r.2 0))
      (by intro r; simp only [oldRunWeight,oldRunConsEquiv,Equiv.coe_fn_mk,
        oldRunVertices_succ_of_le k z r 0 (Nat.zero_le k)]), Fintype.sum_prod_type]
  simp only [Finset.mul_sum,mul_assoc]

 

theorem finite_oldRun_operator_domination (A H : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (hH : PositiveRealMatrix H)
    (B : Finset V) (k : ℕ) (z : ↥B) (x : V) :
    (∑ r : Fin k → ↥B,
      oldRunWeight (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re) k z r *
        (matrixCoeff H (oldRunVertices k z r 0).val x).re) ≤
      (matrixCoeff (A^k*H) z.val x).re := by
  induction k generalizing z with
  | zero => simp [oldRunWeight,oldRunVertices]
  | succ k ih =>
    rw [oldRun_test_succ (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re)
      (fun a : ↥B => (matrixCoeff H a.val x).re) k z]
    calc
      _ ≤ ∑ a : ↥B, (matrixCoeff A z.val a.val).re * (matrixCoeff (A^k*H) a.val x).re :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih a) (hA z.val a.val).2
      _ ≤ ∑' a, (matrixCoeff A z.val a).re * (matrixCoeff (A^k*H) a x).re := by
        rw [Finset.sum_coe_sort B (fun a => (matrixCoeff A z.val a).re * (matrixCoeff (A^k*H) a x).re)]
        exact (hA.mul_hasSum (A^k*H) z.val x).summable.sum_le_tsum B
          (fun a _ => mul_nonneg (hA z.val a).2 (((hA.pow k).mul hH) a x).2)
      _ = (matrixCoeff (A^(k+1)*H) z.val x).re := by
        rw [(hA.mul_hasSum (A^k*H) z.val x).tsum_eq,pow_succ',mul_assoc]

end PositivePathOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitBinOperator
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binConnectionMass_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (n : ℕ) (ω : Set E) (x y : V) :
    binConnectionMass G n (b ⁻¹' ω) x y = binConnectionMass G n ω (a x) (a y) := by
  have hf : (cluster G (b ⁻¹' ω) x).Finite ↔ (cluster G ω (a x)).Finite := by
    rw [← cluster_aut G hab ω x]
    exact (Set.finite_image_iff a.injective.injOn).symm
  have hn : (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
    rw [← cluster_aut G hab ω x,Set.ncard_image_of_injective _ a.injective]
  simp only [binConnectionMass,hf,hn,conn_aut_iff G hab]

theorem binConnection_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (n : ℕ) (x y : V) :
    binConnection G p n (a x) (a y) = binConnection G p n x y := by
  have hm : Measurable (fun ω => binConnectionMass G n ω x y) :=
    measurable_finite_local _ _ (fun ω => binConnectionMass_local G hloc n ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [binConnection,binConnectionMass_covariant G hab] using h.symm


theorem orbitBinConnection_nonneg (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : 0 ≤ orbitBinConnection G p o n x y := by
  unfold orbitBinConnection
  split_ifs
  · exact binConnection_nonneg G p n x y
  · exact le_rfl

theorem orbitBinConnection_symm (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : orbitBinConnection G p o n x y = orbitBinConnection G p o n y x := by
  simp only [orbitBinConnection,and_comm,binConnection_symm G p n]

theorem orbitBinConnection_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (n : ℕ) (x y : V) :
    orbitBinConnection G p o n (a x) (a y) = orbitBinConnection G p o n x y := by
  simp only [orbitBinConnection,mem_vertexOrbit_aut_iff G o hab,binConnection_covariant G hloc p hab n]

theorem orbitBinConnection_summable (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) : Summable (orbitBinConnection G p o n x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x (2*n)).toFinset)
  intro y hy
  have hz := binConnection_outside G p n x y (by simpa only [Set.Finite.mem_toFinset] using hy)
  simp only [orbitBinConnection,hz,ite_self]

theorem orbitBinConnection_row (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) (hx : x ∈ vertexOrbit G o) :
    (∑' y, orbitBinConnection G p o n x y) = binOrbitRow G p o n := by
  obtain ⟨a,b,hab,rfl⟩ := hx
  rw [← a.tsum_eq (fun y => orbitBinConnection G p o n (a o) y)]
  exact tsum_congr (fun y => orbitBinConnection_covariant G hloc p o hab n o y)

theorem orbitBinConnection_row_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) :
    (∑' y, orbitBinConnection G p o n x y) ≤ binOrbitRow G p o n := by
  by_cases hx : x ∈ vertexOrbit G o
  · exact (orbitBinConnection_row G hloc p o n x hx).le
  · simp only [orbitBinConnection,hx,false_and,if_false,tsum_zero]
    exact tsum_nonneg (orbitBinConnection_nonneg G p o n o)

 

theorem exists_orbitBinConnection_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) :
    ∃ H : Hilbert V →L[ℂ] Hilbert V, ‖H‖ ≤ binOrbitRow G p o n ∧
      ∀ x y, matrixCoeff H x y = (orbitBinConnection G p o n x y : ℂ) := by
  have hr (x : V) (S : Finset V) : (∑ y ∈ S, orbitBinConnection G p o n x y) ≤ binOrbitRow G p o n :=
    ((orbitBinConnection_summable G hloc p o n x).sum_le_tsum S
      (fun y _ => orbitBinConnection_nonneg G p o n x y)).trans (orbitBinConnection_row_le G hloc p o n x)
  exact exists_operator_of_row_column_bound (orbitBinConnection G p o n) (binOrbitRow G p o n)
    (tsum_nonneg (orbitBinConnection_nonneg G p o n o)) (orbitBinConnection_nonneg G p o n) hr
    (fun y S => by simpa only [orbitBinConnection_symm G p o n] using hr y S)

end OrbitBinOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open MeasureTheory
section AmplificationOperatorDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem oldRun_endpoint_mem {W : Type*} (P : W → Prop) (K : ℕ → W → W → ℝ)
    (hK : ∀ i a b, K i a b ≠ 0 → P b) (k : ℕ) (z : W) (hz : P z)
    (r : Fin k → W) (hr : oldRunWeight K k z r ≠ 0) : P (oldRunVertices k z r 0) := by
  induction k generalizing z with
  | zero => exact hz
  | succ k ih =>
    have hm := mul_ne_zero_iff.mp hr
    rw [oldRunVertices_succ_of_le _ _ _ _ (Nat.zero_le k)]
    exact ih (r 0) (hK _ _ _ hm.1) (Fin.tail r) hm.2

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationMarginal_operator_le [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ vertexOrbit G o) (hz : z.val ∈ vertexOrbit G o)
    (hroot : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q)
    (hquery : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q)
    (A H : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ a b, matrixCoeff A a b = (q.kernel p a b : ℂ))
    (hH : ∀ a b, matrixCoeff H a b = (orbitBinConnection G p o n a b : ℂ)) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) ≤
      (matrixCoeff (A^k*H) z.val x).re := by
  have hposA : PositiveRealMatrix A := fun a b => by
    rw [hA a b]
    exact ⟨rfl,q.kernel_nonneg p a b⟩
  have hposH : PositiveRealMatrix H := fun a b => by
    rw [hH a b]
    exact ⟨rfl,orbitBinConnection_nonneg G p o n a b⟩
  rw [q.amplificationMarginal_mean_kernel Q B x k n z p hx hz hquery]
  have he : (∑ r : Fin k → ↥B, finiteBinConnection G Q p x n (amplificationVertices B k z r 0) *
      oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r) =
      ∑ r : Fin k → ↥B,
        oldRunWeight (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re) k z r *
          (matrixCoeff H (oldRunVertices k z r 0).val x).re := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [hA,hH,Complex.ofReal_re,
      finiteBinConnection_eq_binConnection G hloc Q p x n _ hroot]
    by_cases hr : oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r = 0
    · simp only [hr,mul_zero,zero_mul]
    · have hy : (oldRunVertices k z r 0).val ∈ vertexOrbit G o :=
        oldRun_endpoint_mem (fun a : ↥B => a.val ∈ vertexOrbit G o)
          (fun _ (a b : ↥B) => q.kernel p a.val b.val)
          (fun _ a b hab => by
            by_contra hb
            exact hab (q.kernel_zero_of_end_not_mem p a.val b.val hb)) k z hz r hr
      rw [orbitBinConnection,ite_eq_left ⟨hy,hx⟩,binConnection_symm G p n]
      exact mul_comm _ _
  rw [he]
  exact finite_oldRun_operator_domination A H hposA hposH B k z x

end LocalEndpointRule

 

theorem exists_operator_of_amplification_domination
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (o : V) (n k : ℕ)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (F : V → V → ℝ) (hF : ∀ x z, 0 ≤ F x z)
    (hdom : ∀ (H : Hilbert V →L[ℂ] Hilbert V),
      (∀ x y, matrixCoeff H x y = (orbitBinConnection G p o n x y : ℂ)) →
      ∀ x z, F x z ≤ (matrixCoeff (A^k*H) z x).re) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ binOrbitRow G p o n * ‖A‖^k ∧
      ∀ x z, matrixCoeff T x z = (F x z : ℂ) := by
  obtain ⟨H,hHnorm,hH⟩ := exists_orbitBinConnection_operator G hloc p o n
  have hposH : PositiveRealMatrix H := fun x y => by
    rw [hH x y]
    exact ⟨rfl,orbitBinConnection_nonneg G p o n x y⟩
  have hpos := ((hA.pow k).mul hposH).star
  have htr (x z : V) : (matrixCoeff (star (A^k*H)) x z).re = (matrixCoeff (A^k*H) z x).re := by
    simp only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_re]
  obtain ⟨T,hTnorm,hT⟩ := exists_operator_of_matrix_domination
    (fun x z => (matrixCoeff (star (A^k*H)) x z).re) F (fun x z => (hpos x z).2)
    (fun x z => by rw [abs_of_nonneg (hF x z),htr]; exact hdom H hH x z)
    (star (A^k*H)) (fun x z => hpos.real x z)
  refine ⟨T,hTnorm.trans ?_,hT⟩
  have hpow : ∀ j : ℕ, ‖A^j‖ ≤ ‖A‖^j := by
    intro j
    induction j with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ j ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
  calc
    ‖star (A^k*H)‖ = ‖A^k*H‖ := by
      change ‖ContinuousLinearMap.adjoint (A^k*H)‖ = _
      exact LinearIsometryEquiv.norm_map _ _
    _ ≤ ‖A^k‖ * ‖H‖ := norm_mul_le _ _
    _ ≤ ‖A‖^k * binOrbitRow G p o n := mul_le_mul (hpow k) hHnorm
      (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ = binOrbitRow G p o n * ‖A‖^k := mul_comm _ _

end AmplificationOperatorDomination

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterVisitKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem conditionalSuccess_nonneg (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    0 ≤ q.conditionalSuccess ω x := tsum_nonneg (q.nonneg ω x)

theorem conditionalSuccess_support (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V)
    (h : q.conditionalSuccess ω x ≠ 0) :
    x ∈ O ∧ (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M := by
  have he : ∃ y, q.mass ω x y ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h (by simp only [conditionalSuccess,hn,tsum_zero])
  obtain ⟨y,hy⟩ := he
  obtain ⟨hx,_,_,hf,hc,_⟩ := q.support ω x y hy
  exact ⟨hx,hf,hc⟩

theorem conditionalSuccess_local (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    q.conditionalSuccess ω x = q.conditionalSuccess
      (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset : Set E)) x :=
  tsum_congr (q.locality ω x)

theorem conditionalSuccess_integrable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.conditionalSuccess ω x) (law p) :=
  integrable_finite_local _ p _ (fun ω => q.conditionalSuccess_local ω x)

theorem conditionalSuccess_mean (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∫ ω, q.conditionalSuccess ω x ∂law p) = q.successProbability p x :=
  (q.kernel_row_integral p x).symm

theorem conditionalSuccess_covariant (q : LocalEndpointRule G hloc O M L)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (ω : Set E) (x : V) :
    q.conditionalSuccess (b ⁻¹' ω) x = q.conditionalSuccess ω (a x) := by
  unfold conditionalSuccess
  simp_rw [q.covariance a b hab]
  exact a.tsum_eq _



theorem clusterVisitMass_nonneg (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) :
    0 ≤ q.clusterVisitMass ω x a := by
  unfold clusterVisitMass
  split_ifs
  · exact q.conditionalSuccess_nonneg ω x
  · exact le_refl _

theorem clusterVisitMass_outside (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V)
    (ha : a ∉ reachBall G x M) : q.clusterVisitMass ω x a = 0 := by
  by_cases h : q.conditionalSuccess ω x = 0
  · simp only [clusterVisitMass,h,ite_self]
  · obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
    exact ite_eq_right (fun hmem => ha (finite_cluster_subset_reachBall G ω x hf M hc hmem))

theorem clusterVisitMass_local (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
    q.clusterVisitMass ω x a = q.clusterVisitMass (ω ∩ (Q : Set E)) x a := by
  dsimp only
  let Q := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
  change q.clusterVisitMass ω x a = q.clusterVisitMass (ω ∩ (Q:Set E)) x a
  have he := finite_local_of_subset _ Q
    (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
    (fun ω => q.conditionalSuccess ω x) (fun ω => q.conditionalSuccess_local ω x) ω
  by_cases h : q.conditionalSuccess ω x = 0
  · have h' : q.conditionalSuccess (ω ∩ (Q:Set E)) x = 0 := he.symm.trans h
    simp only [clusterVisitMass,h,h',ite_self]
  · obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
    have hs : cluster G ω x ⊆ (finite_reachBall hloc x (max q.radius M)).toFinset := by
      simpa only [Set.Finite.coe_toFinset] using
        finite_cluster_subset_reachBall G ω x hf _ (hc.trans (le_max_right _ _))
    have hc' := cluster_restrict_incident_of_full G hloc _ ω x hs
    change cluster G (ω ∩ (Q:Set E)) x = cluster G ω x at hc'
    change (if a ∈ cluster G ω x then _ else _) = (if a ∈ cluster G (ω ∩ (Q:Set E)) x then _ else _)
    rw [hc',he]

theorem clusterVisitMass_integrable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V) :
    Integrable (fun ω => q.clusterVisitMass ω x a) (law p) :=
  integrable_finite_local _ p _ (fun ω => q.clusterVisitMass_local ω x a)

theorem clusterVisitMass_covariant (q : LocalEndpointRule G hloc O M L)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (ω : Set E) (x y : V) :
    q.clusterVisitMass (b ⁻¹' ω) x y = q.clusterVisitMass ω (a x) (a y) := by
  have hc : y ∈ cluster G (b ⁻¹' ω) x ↔ a y ∈ cluster G ω (a x) := by
    rw [← cluster_aut G hab ω x]
    constructor
    · intro hy; exact ⟨y,hy,rfl⟩
    · rintro ⟨z,hz,he⟩
      exact (a.injective he) ▸ hz
  simp only [clusterVisitMass,hc,q.conditionalSuccess_covariant a b hab]

theorem clusterVisitMass_row_le (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    (∑' a, q.clusterVisitMass ω x a) ≤ M * q.conditionalSuccess ω x := by
  by_cases h : q.conditionalSuccess ω x = 0
  · simp only [clusterVisitMass,h,ite_self,tsum_zero,mul_zero,le_refl]
  obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
  rw [tsum_eq_sum (f := q.clusterVisitMass ω x) (s := hf.toFinset) (fun a ha => ite_eq_right (by simpa only [Set.Finite.mem_toFinset] using ha))]
  have he : (∑ a ∈ hf.toFinset, q.clusterVisitMass ω x a) =
      (hf.toFinset.card:ℝ) * q.conditionalSuccess ω x := by
    calc
      _ = ∑ _a ∈ hf.toFinset, q.conditionalSuccess ω x := Finset.sum_congr rfl (fun a ha => ite_eq_left (hf.mem_toFinset.mp ha))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (q.conditionalSuccess_nonneg ω x)
  exact_mod_cast (by simpa only [← Set.ncard_eq_toFinset_card _ hf] using hc)

theorem clusterVisitKernel_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V) :
    0 ≤ q.clusterVisitKernel p x a := integral_nonneg (fun ω => q.clusterVisitMass_nonneg ω x a)

theorem clusterVisitKernel_outside (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V)
    (ha : a ∉ reachBall G x M) : q.clusterVisitKernel p x a = 0 := by
  simp only [clusterVisitKernel,q.clusterVisitMass_outside _ x a ha,integral_zero]

theorem clusterVisitKernel_summable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Summable (q.clusterVisitKernel p x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro a ha
  exact q.clusterVisitKernel_outside p x a (by simpa only [Set.Finite.mem_toFinset] using ha)

theorem clusterVisitKernel_row_le (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∑' a, q.clusterVisitKernel p x a) ≤ M * q.successProbability p x := by
  let B := (finite_reachBall hloc x M).toFinset
  have he (ω : Set E) : (∑' a, q.clusterVisitMass ω x a) = ∑ a ∈ B, q.clusterVisitMass ω x a :=
    tsum_eq_sum (fun a ha => q.clusterVisitMass_outside ω x a (by simpa only [B,Set.Finite.mem_toFinset] using ha))
  rw [tsum_eq_sum (s := B) (fun a ha => q.clusterVisitKernel_outside p x a (by simpa only [B,Set.Finite.mem_toFinset] using ha))]
  simp only [clusterVisitKernel]
  rw [← integral_finsetSum B (fun a _ => q.clusterVisitMass_integrable p x a)]
  calc
    _ ≤ ∫ ω, (M:ℝ) * q.conditionalSuccess ω x ∂law p :=
      integral_mono (integrable_finsetSum B (fun a _ => q.clusterVisitMass_integrable p x a))
        ((q.conditionalSuccess_integrable p x).const_mul _) (fun ω => by rw [← he]; exact q.clusterVisitMass_row_le ω x)
    _ = _ := by rw [integral_const_mul,q.conditionalSuccess_mean]

theorem clusterVisitKernel_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x y : V) :
    q.clusterVisitKernel p (a x) (a y) = q.clusterVisitKernel p x y := by
  have hm : Measurable (fun ω => q.clusterVisitMass ω x y) :=
    measurable_finite_local _ _ (fun ω => q.clusterVisitMass_local ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [clusterVisitKernel,q.clusterVisitMass_covariant a b hab] using h.symm

end LocalEndpointRule
end ClusterVisitKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section VisitEnvelope
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}



theorem visitEnvelope_nonneg (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (x a : V) : 0 ≤ q.visitEnvelope o p k x a := by
  induction k generalizing x with
  | zero => exact le_refl _
  | succ k ih =>
    exact add_nonneg (mul_nonneg (pow_nonneg (q.successProbability_nonneg p o) _) (q.clusterVisitKernel_nonneg p x a))
      (tsum_nonneg (fun y => mul_nonneg (q.kernel_nonneg p x y) (ih y)))

theorem visitEnvelope_covariant (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x y : V) :
    q.visitEnvelope o p k (a x) (a y) = q.visitEnvelope o p k x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    simp only [visitEnvelope,q.clusterVisitKernel_covariant p a b hab]
    congr 1
    rw [← a.tsum_eq (fun z => q.kernel p (a x) z * q.visitEnvelope o p k z (a y))]
    exact tsum_congr fun z => by rw [q.kernel_covariant p a b hab,ih]

 

theorem visitEnvelope_row_bound (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (x : V) :
    Summable (q.visitEnvelope o p k x) ∧
      (∑' a, q.visitEnvelope o p k x a) ≤ (k*M:ℕ) * q.successProbability p o ^ k := by
  let u := q.successProbability p o
  have hu : 0 ≤ u := q.successProbability_nonneg p o
  induction k generalizing x with
  | zero => simp only [visitEnvelope,zero_mul,Nat.cast_zero,pow_zero,mul_one,tsum_zero,le_refl,and_true]; exact summable_zero
  | succ k ih =>
    let B := (finite_reachBall hloc x M).toFinset
    have he (a : V) : (∑' y, q.kernel p x y * q.visitEnvelope o p k y a) =
        ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a :=
      tsum_eq_sum (fun y hy => by
        rw [q.kernel_outside_ball_zero p x y (by simpa only [B,Set.Finite.mem_toFinset] using hy),zero_mul])
    have ht (a : V) : q.visitEnvelope o p (k+1) x a =
        u^k * q.clusterVisitKernel p x a + ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a := by
      exact congrArg (_ + ·) (he a)
    have hsum : Summable (fun a => ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a) :=
      summable_sum (s := B) (fun y _ => (ih y).1.mul_left _)
    have hs := ((q.clusterVisitKernel_summable p x).mul_left (u^k)).add hsum
    have hs' : Summable (q.visitEnvelope o p (k+1) x) := by
      change Summable (fun a => q.visitEnvelope o p (k+1) x a)
      simpa only [ht] using hs
    refine ⟨hs',?_⟩
    simp_rw [ht]
    rw [Summable.tsum_add ((q.clusterVisitKernel_summable p x).mul_left _) hsum,tsum_mul_left,
      Summable.tsum_finsetSum (fun y _ => (ih y).1.mul_left _)]
    simp_rw [tsum_mul_left]
    have hr : (∑ y ∈ B, q.kernel p x y) ≤ u :=
      ((q.summable_kernel p x).sum_le_tsum B (fun y _ => q.kernel_nonneg p x y)).trans
        (q.kernel_row_le_success o p x)
    calc
      _ ≤ u^k * (M*u) + ∑ y ∈ B, q.kernel p x y * ((k*M:ℕ)*u^k) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
          exact (q.clusterVisitKernel_row_le p x).trans
            (mul_le_mul_of_nonneg_left (q.kernel_row_le_success o p x) (Nat.cast_nonneg _))
        · exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih y).2 (q.kernel_nonneg p x y)
      _ ≤ u^k * (M*u) + u*((k*M:ℕ)*u^k) := by
        rw [← Finset.sum_mul]
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hr (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu _)))
      _ = ((k+1)*M:ℕ) * q.successProbability p o ^ (k+1) := by
        change _ = ((k+1)*M:ℕ) * u^(k+1)
        simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
        ring

end LocalEndpointRule
end VisitEnvelope

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MarkedOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

theorem oldRunWeight_congr (K K' : ℕ → W → W → ℝ) (k : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ k → ∀ a b, K i a b = K' i a b) (z : W) (r : Fin k → W) :
    oldRunWeight K k z r = oldRunWeight K' k z r := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunWeight]
    rw [h (k+1) (by omega) (by omega),ih (fun i hi hik => h i hi (by omega))]

theorem oldRunWeight_prod (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    oldRunWeight K k z r = ∏ i ∈ Finset.Icc 1 k,
      K i (oldRunVertices k z r i) (oldRunVertices k z r (i-1)) := by
  induction k generalizing z with
  | zero => simp [oldRunWeight]
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    have he : (∏ i ∈ Finset.Icc 1 k, K i (oldRunVertices (k+1) z r i)
        (oldRunVertices (k+1) z r (i-1))) = oldRunWeight K k (r 0) (Fin.tail r) := by
      rw [ih]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [oldRunVertices_succ_of_le _ _ _ _ hi'.2,
        oldRunVertices_succ_of_le _ _ _ _ (by omega)]
    rw [he,oldRunVertices_last,Nat.add_sub_cancel,
      oldRunVertices_succ_of_le _ _ _ _ (le_refl _),oldRunVertices_last]
    exact mul_comm _ _



theorem markedOldRun_nonneg (K C : ℕ → W → W → ℝ)
    (hK : ∀ i a b, 0 ≤ K i a b) (hC : ∀ i a b, 0 ≤ C i a b)
    (k : ℕ) (z : W) (r : Fin k → W) : 0 ≤ markedOldRun K C k z r := by
  apply Finset.sum_nonneg
  intro i _
  apply oldRunWeight_nonneg
  intro j a b
  split_ifs
  · exact hC j a b
  · exact hK j a b

theorem markedOldRun_succ (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin (k+1) → W) :
    markedOldRun K C (k+1) z r =
      K (k+1) z (r 0) * markedOldRun K C k (r 0) (Fin.tail r) +
      C (k+1) z (r 0) * oldRunWeight K k (r 0) (Fin.tail r) := by
  unfold markedOldRun
  rw [Finset.sum_Icc_succ_top (by omega),Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hne : k+1 ≠ i := by have := Finset.mem_Icc.mp hi; omega
    simp only [oldRunWeight,ite_eq_right hne]
  · simp only [oldRunWeight,if_true]
    congr 1
    apply oldRunWeight_congr
    intro i hi hik a b
    exact ite_eq_right (by omega)

theorem sum_markedOldRun_succ [Fintype W] (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) :
    (∑ r : Fin (k+1) → W, markedOldRun K C (k+1) z r) =
      ∑ b : W, (K (k+1) z b * (∑ r : Fin k → W, markedOldRun K C k b r) +
        C (k+1) z b * (∑ r : Fin k → W, oldRunWeight K k b r)) := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun r => K (k+1) z r.1 * markedOldRun K C k r.1 r.2 + C (k+1) z r.1 * oldRunWeight K k r.1 r.2)
      (by intro r; exact markedOldRun_succ K C k z r),Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib,Finset.mul_sum]

 
theorem oldRunWeight_integral_indexed (Q : Finset E) (p : ℝ)
    (q : ℕ → Set E → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => oldRunWeight (fun i => q i (η i)) k z r) =
      oldRunWeight (fun i a b => finiteFieldIntegral Q p (fun ω => q i ω a b)) k z r := by
  calc
    _ = finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
        ∏ i : ↥(Finset.Icc 1 k), q i (η i) (oldRunVertices k z r i)
          (oldRunVertices k z r (i.val-1))) := by
      congr 1
      funext η
      rw [oldRunWeight_prod]
      exact (Finset.prod_coe_sort (Finset.Icc 1 k)
        (fun i => q i (η i) (oldRunVertices k z r i) (oldRunVertices k z r (i-1)))).symm
    _ = ∏ i : ↥(Finset.Icc 1 k), finiteFieldIntegral Q p (fun ω =>
        q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i.val-1))) :=
      finiteFamilyIntegral_prod Q (Finset.Icc 1 k) p
        (fun i ω => q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i.val-1)))
    _ = _ := by
      rw [oldRunWeight_prod]
      exact Finset.prod_coe_sort (Finset.Icc 1 k) (fun i => finiteFieldIntegral Q p
        (fun ω => q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i-1))))

theorem markedOldRun_integral (Q : Finset E) (p : ℝ)
    (q c : ℕ → Set E → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p
      (fun η => markedOldRun (fun i => q i (η i)) (fun i => c i (η i)) k z r) =
      markedOldRun (fun i a b => finiteFieldIntegral Q p (fun ω => q i ω a b))
        (fun i a b => finiteFieldIntegral Q p (fun ω => c i ω a b)) k z r := by
  unfold markedOldRun
  rw [finiteFamilyIntegral_sum]
  apply Finset.sum_congr rfl
  intro i _
  change finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
      oldRunWeight (fun j => (fun ω a b => if j=i then c j ω a b else q j ω a b) (η j)) k z r) = _
  rw [oldRunWeight_integral_indexed Q p (fun j ω a b => if j=i then c j ω a b else q j ω a b) k z r]
  congr 1
  funext j a b
  by_cases h : j = i <;> simp only [h,if_true,if_false]

 

theorem trajectory_indicator_le_marked (G : BondGraph V E) (e : W → V)
    (q : Set E → W → W → ℝ) (hq : ∀ ω x y, 0 ≤ q ω x y)
    (k : ℕ) (η : ℕ → Set E) (z : W) (r : Fin k → W) (a : V) :
    (if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z r) k then
      oldRunWeight (fun i => q (η i)) k z r else 0) ≤
      markedOldRun (fun i => q (η i))
        (fun i x y => if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) k z r := by
  have hC : ∀ i x y, 0 ≤ (if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) := by
    intro i x y; split_ifs; exact hq _ _ _; exact le_refl _
  by_cases ha : a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z r) k
  · rw [ite_eq_left ha]
    obtain ⟨i,hi,hik,hai⟩ := (mem_trajectoryUnion G η (e ∘ oldRunVertices k z r) k a).mp ha
    have he : oldRunWeight (fun j x y => if j=i then
        (if a ∈ cluster G (η j) (e x) then q (η j) x y else 0) else q (η j) x y) k z r =
        oldRunWeight (fun j => q (η j)) k z r := by
      simp_rw [oldRunWeight_prod]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp only [if_true,Function.comp_apply] at hai ⊢
        exact ite_eq_left hai
      · exact ite_eq_right hji
    rw [← he]
    unfold markedOldRun
    apply Finset.single_le_sum _ (Finset.mem_Icc.mpr ⟨hi,hik⟩)
    intro j _
    apply oldRunWeight_nonneg
    intro l x y
    split_ifs
    · exact hq _ _ _
    · exact le_refl _
    · exact hq _ _ _
  · rw [ite_eq_right ha]
    exact markedOldRun_nonneg _ _ (fun _ => hq _) hC k z r

end MarkedOldRun

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryEnvelopeDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteTrajectoryMass_le_marked {W : Type*} [Fintype W]
    (G : BondGraph V E) (e : W → V) (Q : Finset E) (p : unitInterval) (k : ℕ)
    (q : Set E → W → W → ℝ) (hq : ∀ ω x y, 0 ≤ q ω x y) (z : W) (a : V) :
    finiteTrajectoryMass G e Q p k q z a ≤
      ∑ r : Fin k → W, markedOldRun (fun _ => finiteOldKernel Q p q)
        (fun _ x y => finiteFieldIntegral Q p (fun ω => if a ∈ cluster G ω (e x) then q ω x y else 0)) k z r := by
  unfold finiteTrajectoryMass
  calc
    _ ≤ finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => ∑ r : Fin k → W,
        markedOldRun (fun i => q (η i))
          (fun i x y => if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) k z r) :=
      finiteFamilyIntegral_mono Q (Finset.Icc 1 k) p _ _ (fun η => Finset.sum_le_sum (fun r _ =>
        trajectory_indicator_le_marked G e q hq k η z r a))
    _ = _ := by
      rw [finiteFamilyIntegral_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact markedOldRun_integral Q p (fun _ => q)
        (fun _ ω x y => if a ∈ cluster G ω (e x) then q ω x y else 0) k z r

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem finite_marked_step_row_le (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x a : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ y : ↥B, finiteFieldIntegral Q p (fun ω =>
      if a ∈ cluster G ω x then q.mass ω x y.val else 0)) ≤ q.clusterVisitKernel p x a := by
  rw [← finiteFieldIntegral_sum]
  have he : q.clusterVisitKernel p x a = finiteFieldIntegral Q p (fun ω => q.clusterVisitMass ω x a) :=
    integral_finite_local Q p _ (finite_local_of_subset _ Q hQ _ (q.clusterVisitMass_local · x a))
  rw [he]
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (finiteFieldWeight_nonneg Q p ω)
  dsimp only
  by_cases ha : a ∈ cluster G (finiteFieldSet Q ω) x
  · simp only [ha,if_true,clusterVisitMass]
    rw [Finset.sum_coe_sort B (fun y => q.mass (finiteFieldSet Q ω) x y)]
    exact (q.summable_mass _ x).sum_le_tsum B (fun y _ => q.nonneg _ x y)
  · simp only [ha,if_false,clusterVisitMass,Finset.sum_const_zero,le_refl]

 

theorem sum_markedOldRun_le_envelope (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (z : ↥B) (a : V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ r : Fin k → ↥B, markedOldRun
      (fun _ => finiteOldKernel Q p (fun ω (x y : ↥B) => q.mass ω x.val y.val))
      (fun _ (x y : ↥B) => finiteFieldIntegral Q p (fun ω =>
        if a ∈ cluster G ω x.val then q.mass ω x.val y.val else 0)) k z r) ≤
      q.visitEnvelope o p k z.val a := by
  let u := q.successProbability p o
  let K : ↥B → ↥B → ℝ := finiteOldKernel Q p (fun ω (x y : ↥B) => q.mass ω x.val y.val)
  let C : ↥B → ↥B → ℝ := fun x y => finiteFieldIntegral Q p (fun ω =>
    if a ∈ cluster G ω x.val then q.mass ω x.val y.val else 0)
  have hK (x y : ↥B) : K x y = q.kernel p x.val y.val :=
    q.finiteOldKernel_eq_kernel Q p x.val y.val
      ((incidentSupport_ball_mono G hloc x.val (le_max_left _ _)).trans (hQ x.val x.property))
  have hKn (x y : ↥B) : 0 ≤ K x y := by rw [hK]; exact q.kernel_nonneg p _ _
  have hCn (x y : ↥B) : 0 ≤ C x y := by
    apply finiteFieldIntegral_nonneg
    intro ω; split_ifs; exact q.nonneg ω _ _; exact le_refl _
  have hKr (x : ↥B) : (∑ y, K x y) ≤ u := by
    simp only [hK]
    rw [Finset.sum_coe_sort B (fun y => q.kernel p x.val y)]
    exact ((q.summable_kernel p x.val).sum_le_tsum B (fun y _ => q.kernel_nonneg p x.val y)).trans
      (q.kernel_row_le_success o p x.val)
  have hCr (x : ↥B) : (∑ y, C x y) ≤ q.clusterVisitKernel p x.val a :=
    q.finite_marked_step_row_le o Q B p x.val a (hQ x.val x.property)
  change (∑ r : Fin k → ↥B, markedOldRun (fun _ => K) (fun _ => C) k z r) ≤ _
  induction k generalizing z with
  | zero => simp [markedOldRun,visitEnvelope]
  | succ k ih =>
    rw [sum_markedOldRun_succ]
    have hs : Summable (fun y => q.kernel p z.val y * q.visitEnvelope o p k y a) := by
      apply summable_of_ne_finset_zero (s := (finite_reachBall hloc z.val M).toFinset)
      intro y hy
      rw [q.kernel_outside_ball_zero p z.val y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul]
    calc
      _ ≤ ∑ y : ↥B, (K z y * q.visitEnvelope o p k y.val a + C z y * u^k) :=
        Finset.sum_le_sum fun y _ => add_le_add
          (mul_le_mul_of_nonneg_left (ih y) (hKn z y))
          (mul_le_mul_of_nonneg_left (sum_oldRunWeight_le (fun _ => K) (fun _ => hKn)
            u (q.successProbability_nonneg p o) (fun _ => hKr) k y) (hCn z y))
      _ = (∑ y : ↥B, K z y * q.visitEnvelope o p k y.val a) + (∑ y : ↥B, C z y)*u^k := by
        rw [Finset.sum_add_distrib,Finset.sum_mul]
      _ ≤ (∑' y, q.kernel p z.val y * q.visitEnvelope o p k y a) + q.clusterVisitKernel p z.val a * u^k := by
        apply add_le_add
        · simp only [hK]
          rw [Finset.sum_coe_sort B (fun y => q.kernel p z.val y * q.visitEnvelope o p k y a)]
          exact hs.sum_le_tsum B (fun y _ => mul_nonneg (q.kernel_nonneg p z.val y) (q.visitEnvelope_nonneg o p k y a))
        · exact mul_le_mul_of_nonneg_right (hCr z) (pow_nonneg (q.successProbability_nonneg p o) _)
      _ = q.visitEnvelope o p (k+1) z.val a := by rw [visitEnvelope]; ring

theorem finiteTrajectoryMass_le_envelope (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (z : ↥B) (a : V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    finiteTrajectoryMass G Subtype.val Q p k (fun ω (x y : ↥B) => q.mass ω x.val y.val) z a ≤
      q.visitEnvelope o p k z.val a :=
  (finiteTrajectoryMass_le_marked G Subtype.val Q p k _ (fun ω x y => q.nonneg ω x.val y.val) z a).trans
    (q.sum_markedOldRun_le_envelope o Q B p k z a hQ)

end LocalEndpointRule
end TrajectoryEnvelopeDomination

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_EndpointMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryHitTransport
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable {ι : Type*} [Fintype ι]

 

theorem visitEnvelope_column_bound (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (a : V) :
    Summable (fun z => q.visitEnvelope o p k z a) ∧
      (∑' z, q.visitEnvelope o p k z a) ≤ c*((k*M:ℕ)*q.successProbability p o ^ k) := by
  apply transported_column_of_row_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (q.visitEnvelope o p k) (q.visitEnvelope_nonneg o p k) _
    (fun z => (q.visitEnvelope_row_bound o p k z).1) _
    (fun z => (q.visitEnvelope_row_bound o p k z).2) a
  intro b hb x y
  obtain ⟨d,hd⟩ := hΓ hb
  exact q.visitEnvelope_covariant o p k b d hd x y

 

theorem finiteTrajectoryHit_sum_le (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (A : Finset V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ z : ↥B, finiteTrajectoryHit G Subtype.val Q p k
      (fun ω (x y : ↥B) => q.mass ω x.val y.val) z A) ≤
      (A.card:ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)) := by
  have hcol := fun a => q.visitEnvelope_column_bound hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin o p k a
  calc
    _ ≤ ∑ z : ↥B, ∑ a ∈ A, q.visitEnvelope o p k z.val a := by
      apply Finset.sum_le_sum
      intro z _
      exact (finiteTrajectoryHit_le_sum G Subtype.val Q p k _ (fun ω x y => q.nonneg ω x.val y.val) z A).trans
        (Finset.sum_le_sum fun a _ => q.finiteTrajectoryMass_le_envelope o Q B p k z a hQ)
    _ = ∑ a ∈ A, ∑ z : ↥B, q.visitEnvelope o p k z.val a := Finset.sum_comm
    _ ≤ ∑ _a ∈ A, c*((k*M:ℕ)*q.successProbability p o ^ k) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Finset.sum_coe_sort B (fun z => q.visitEnvelope o p k z a)]
      exact ((hcol a).1.sum_le_tsum B (fun z _ => q.visitEnvelope_nonneg o p k z a)).trans (hcol a).2
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end LocalEndpointRule
end TrajectoryHitTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointHit
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteChoiceHit_allRuns {W : Type*} [Fintype W]
    (G : BondGraph V E) (e : W → V) (Q : Finset E) (p : ℝ) (k : ℕ)
    (q : Set E → W → W → ℝ) (A : Finset V) :
    finiteChoiceHit G k Q p
      (fun (r : W × (Fin k → W)) _ => e ∘ oldRunVertices k r.1 r.2)
      (fun r η => oldRunWeight (fun i => q (η i)) k r.1 r.2) (A : Set V) =
      ∑ z : W, finiteTrajectoryHit G e Q p k q z A := by
  unfold finiteChoiceHit finiteTrajectoryHit
  rw [Fintype.sum_prod_type]
  simp only [finiteFamilyIntegral_sum]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem allAmplificationWeight_nonneg (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (r : ↥B × (Fin k → ↥B)) (η : ℕ → Set E) :
    0 ≤ q.allAmplificationWeight B k r η :=
  oldRunWeight_nonneg (fun i (a b : ↥B) => q.mass (η i) a.val b.val) (fun i a b => q.nonneg (η i) a.val b.val) k r.1 r.2

variable {ι : Type*} [Fintype ι]

theorem allAmplificationHit_bound (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (A : Set V) (hf : A.Finite)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    finiteChoiceHit G k Q p (allAmplificationVertices B k) (q.allAmplificationWeight B k) A ≤
      (A.ncard:ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)) := by
  have he : finiteChoiceHit G k Q p (allAmplificationVertices B k) (q.allAmplificationWeight B k) A =
      ∑ z : ↥B, finiteTrajectoryHit G Subtype.val Q p k
        (fun ω (a b : ↥B) => q.mass ω a.val b.val) z hf.toFinset := by
    rw [← finiteChoiceHit_allRuns]
    rw [hf.coe_toFinset]
    rfl
  rw [he,Set.ncard_eq_toFinset_card A hf]
  exact q.finiteTrajectoryHit_sum_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin o Q B p k hf.toFinset hQ

end LocalEndpointRule
end AllEndpointHit

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointSeparated
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteChoiceHit_nonneg {P : Type*} [Fintype P]
    (G : BondGraph V E) (k : ℕ) (Q : Finset E) (p : unitInterval)
    (y : P → (ℕ → Set E) → ℕ → V) (m : P → (ℕ → Set E) → ℝ)
    (hm : ∀ r η, 0 ≤ m r η) (A : Set V) : 0 ≤ finiteChoiceHit G k Q p y m A := by
  apply Finset.sum_nonneg
  intro r _
  apply finiteFamilyIntegral_nonneg
  intro η
  split_ifs
  · exact hm r η
  · exact le_refl _

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable {ι : Type*} [Fintype ι]

 

theorem amplificationSeparatedSecondMoment_le [Nonempty E] (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x : V) (k n : ℕ)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆ Q) :
    finiteChoiceSeparatedPairMass G x k Q p
      (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
      (allAmplificationVertices B k) (allAmplificationVertices B k)
      (q.allAmplificationWeight B k) (q.allAmplificationWeight B k) ≤
      (((2*n:ℕ):ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)))^2 *
        finiteClusterWindowMass G Q p x (n-k*M) (2*n) := by
  let A := q.allAmplificationInputs Q B x k n
  let y := allAmplificationVertices (E := E) B k
  let m := q.allAmplificationWeight B k
  have hA (r) : A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k) :=
    q.amplificationInputs_subset Q B x k n r.1 r.2
  have hbin r s (hs : s ∈ A r) : (cluster G s.1 x).Finite ∧
      n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n := by
    have hd := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s).mp (hA r hs)
    have hb := (q.mem_amplificationInputs Q B x k n r.1 r.2 s).mp hs
    exact ⟨cluster_finite_of_finite_edges G (Q.finite_toSet.subset hd.1) x,hb.2.2.2.1,hb.2.2.2.2.1⟩
  have hcap r s (hs : s ∈ A r) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      (cluster G (s.2 i) (y r s.2 i)).Finite ∧ (cluster G (s.2 i) (y r s.2 i)).ncard ≤ M := by
    have hd := q.amplificationInputs_chain Q B x k n r.1 r.2 s hs i hi hik
    exact ⟨hd.2.1,hd.2.2.1⟩
  have hm := q.allAmplificationWeight_nonneg B k
  have hb := finiteChoiceSeparatedPairMass_le G hloc x k n M Q p A A y y m m hm hm hA hA hbin
    (fun r s hs i hi hik => (hcap r s hs i hi hik).1) hcap
  let d : ℝ := c*((k*M:ℕ)*q.successProbability p o ^ k)
  have hd : 0 ≤ d := mul_nonneg hc (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (q.successProbability_nonneg p o) _))
  let t : ℝ := ((2*n:ℕ):ℝ)*d
  apply hb.trans
  unfold finiteClusterWindowMass finiteFieldIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  have he : t^2 * (finiteFieldWeight Q p ω * (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then 1 else 0)) =
      finiteFieldWeight Q p ω * (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then t^2 else 0) := by
    split_ifs <;> ring
  change _ ≤ t^2 * _
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (finiteFieldWeight_nonneg Q p ω)
  by_cases h : (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  · rw [ite_eq_left h,ite_eq_left h]
    have hhit := q.allAmplificationHit_bound hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
      o Q B p k (cluster G (finiteFieldSet Q ω) x) h.1 hQ
    have hc' : ((cluster G (finiteFieldSet Q ω) x).ncard:ℝ) ≤ ((2*n:ℕ):ℝ) := by exact_mod_cast h.2.2.le
    have hhit' : finiteChoiceHit G k Q p y m (cluster G (finiteFieldSet Q ω) x) ≤ t :=
      hhit.trans (mul_le_mul_of_nonneg_right hc' hd)
    simpa only [pow_two] using mul_self_le_mul_self
      (finiteChoiceHit_nonneg G k Q p y m hm _) hhit'
  · rw [ite_eq_right h,ite_eq_right h]

end LocalEndpointRule
end AllEndpointSeparated

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finiteRootLoad_sum {P : Type*} (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (S : Finset P) (f : P → SpliceState E → ℝ) (ω : FiniteField Q) :
    finiteRootLoad Q J p (fun s => ∑ z ∈ S, f z s) ω =
      ∑ z ∈ S, finiteRootLoad Q J p (f z) ω := by
  simp only [finiteRootLoad,Finset.mul_sum]
  exact Finset.sum_comm

 

theorem finiteChoiceForwardLoad_prod {P R : Type*} [Fintype P] [Fintype R]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P × R → Finset (SpliceState E)) (y : P × R → SpliceState E → ℕ → V)
    (m : SpliceState E → P × R → ℝ) (t : SpliceState E) :
    finiteChoiceForwardLoad G x k Q A y m t = ∑ z : P,
      finiteChoiceForwardLoad G x k Q (fun r => A (z,r)) (fun r => y (z,r))
        (fun s r => m s (z,r)) t := by
  unfold finiteChoiceForwardLoad finiteInverseLoad
  rw [Fintype.sum_sigma,Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma,choiceTraceOutput,choiceTraceMass,choiceTraceInput]
  rfl

 
theorem endpointRootMass_choice_prod {P R : Type*} [Fintype P] [Fintype R]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (A : P × R → Finset (SpliceState E)) (y : P × R → SpliceState E → ℕ → V)
    (m : SpliceState E → P × R → ℝ) (e : P → V) (he : Function.Injective e)
    (z : P) (ω : Set E) :
    endpointRootMass Q (Finset.Icc 1 k) p (choiceTraceOutput G x k Q A y)
      (fun a => e a.1.1) (choiceTraceMass G x k Q A y m) ω (e z) =
      ∑ a : FiniteChoiceTraceIndex G x k Q (fun r => A (z,r)) (fun r => y (z,r)),
        if (choiceTraceOutput G x k Q (fun r => A (z,r)) (fun r => y (z,r)) a).1 = ω then
          auxiliaryTupleWeight Q (Finset.Icc 1 k) p
            (choiceTraceOutput G x k Q (fun r => A (z,r)) (fun r => y (z,r)) a) *
          choiceTraceMass G x k Q (fun r => A (z,r)) (fun r => y (z,r)) (fun s r => m s (z,r)) a else 0 := by
  unfold endpointRootMass
  rw [Fintype.sum_sigma,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z]
  · rw [Fintype.sum_sigma]
    simp only [choiceTraceOutput,choiceTraceMass,choiceTraceInput,and_true]
    rfl
  · intro z' _ hz'
    have hh : e z' ≠ e z := fun h => hz' (he h)
    simp only [hh,and_false,if_false,Finset.sum_const_zero]
  · intro hz
    exact (hz (Finset.mem_univ z)).elim

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem amplificationRow_eq_load (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    q.amplificationRow Q B x k n p ω = finiteRootLoad Q (Finset.Icc 1 k) p
      (finiteInverseLoad (q.amplificationOutput Q B x k n) (q.amplificationMass Q B x k n))
      (restrictFiniteField Q ω) := by
  change _ = finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteChoiceForwardLoad G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)) _
  have hf : (finiteChoiceForwardLoad G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)) =
      (fun t => ∑ z : ↥B, finiteChoiceForwardLoad G x k Q (q.amplificationInputs Q B x k n z)
        (fun r _ => amplificationVertices B k z r) (q.amplificationWeight B k z) t) := by
    funext t
    exact finiteChoiceForwardLoad_prod G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2) t
  rw [hf,finiteRootLoad_sum]
  rfl

theorem amplificationEndpointMass_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) (z : ↥B) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) (finiteFieldSet Q ω) z.val =
      q.amplificationMarginal Q B x k n z p (finiteFieldSet Q ω) := by
  change endpointRootMass Q (Finset.Icc 1 k) p (choiceTraceOutput G x k Q _ _)
    _ (choiceTraceMass G x k Q _ _ _) _ _ = _
  rw [endpointRootMass_choice_prod G x k Q p _ _ _ Subtype.val Subtype.val_injective z]
  unfold amplificationMarginal finiteChoiceForwardLoad
  rw [restrictFiniteField_fieldSet,finiteRootLoad_eq_sum]
  · rfl
  · intro a
    exact traceIndexOutput_mem G x k Q _ _ (q.amplificationInputs_subset Q B x k n z a.1) a.2

end LocalEndpointRule
end AllEndpointMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AmplificationIndexFacts
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem amplificationOutput_mem (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    q.amplificationOutput Q B x k n a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) :=
  traceIndexOutput_mem G x k Q _ _ (q.amplificationInputs_subset Q B x k n a.1.1 a.1.2) a.2

theorem amplificationMass_nonneg (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    0 ≤ q.amplificationMass Q B x k n a :=
  mul_nonneg (q.allAmplificationWeight_nonneg B k a.1 (q.amplificationInput Q B x k n a).2)
    (Finset.prod_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem amplificationIndex_trace (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    SpliceTrace G x (q.amplificationInput Q B x k n a).2
      (amplificationVertices B k a.1.1 a.1.2) k 0 (q.amplificationInput Q B x k n a).1
      (q.amplificationCode Q B x k n a) (q.amplificationOutput Q B x k n a).1 :=
  (traceIndex_valid G x k Q _ _ a.2).1

theorem amplificationIndex_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    x ∈ O ∧ a.1.1.val ∈ O ∧ Conn G (q.amplificationOutput Q B x k n a).1 x a.1.1.val ∧
      (cluster G (q.amplificationOutput Q B x k n a).1 x).Finite ∧
      (cluster G (q.amplificationOutput Q B x k n a).1 x).ncard ≤ 2*n+k*M :=
  q.amplificationTrace_support Q B x k n a.1.1 a.1.2 a.2.1.val a.2.1.property _ _
    (q.amplificationIndex_trace Q B x k n a)

theorem amplificationIndex_caps (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n)
    (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    (cluster G ((q.amplificationInput Q B x k n a).2 i) (amplificationVertices B k a.1.1 a.1.2 i)).Finite ∧
    (cluster G ((q.amplificationInput Q B x k n a).2 i) (amplificationVertices B k a.1.1 a.1.2 i)).ncard ≤ M := by
  have hc := q.amplificationInputs_chain Q B x k n a.1.1 a.1.2 a.2.1.val a.2.1.property i hi hik
  exact ⟨hc.2.1,hc.2.2.1⟩

theorem amplificationEndpointMass_outside (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E)
    (z : V) (hz : z ∉ B) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) ω z = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · exact (hz (h.2 ▸ a.1.1.property)).elim
  · rfl

 

theorem amplificationEndpointMass_bound (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E)
    (hω : ω ⊆ (Q : Set E)) (z : V) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) ω z ≤ inverseCodeMass M L ^ k := by
  by_cases hz : z ∈ B
  · let z' : ↥B := ⟨z,hz⟩
    have hfield : finiteFieldSet Q (restrictFiniteField Q ω) = ω := by
      rw [finiteFieldSet_restrict,Set.inter_eq_left.mpr hω]
    rw [← hfield,q.amplificationEndpointMass_eq Q B x k n p _ z']
    exact (q.amplificationMarginal_bounds hL Q B x k n z' p _).2
  · rw [q.amplificationEndpointMass_outside Q B x k n p ω z hz]
    apply pow_nonneg
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => gapWeight_nonneg L (by linarith) l)

end LocalEndpointRule
end AmplificationIndexFacts

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NoSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem traceIndexMass_nil (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) (hc : traceIndexCode G x k Q A y a = []) :
    traceIndexMass G x k Q A y a = 1 := by
  change a.2.val = [] at hc
  simp [traceIndexMass,hc,traceContactCount]

 

theorem finiteChoiceNilLoad_le {P : Type*} [Fintype P]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (m : SpliceState E → P → ℝ) (hm : ∀ s r, 0 ≤ m s r) (t : SpliceState E) :
    finiteInverseLoad (choiceTraceOutput G x k Q A y)
      (fun a => if choiceTraceCode G x k Q A y a = [] then choiceTraceMass G x k Q A y m a else 0) t ≤
      ∑ r, if t ∈ A r then m t r else 0 := by
  let I := FiniteChoiceTraceIndex G x k Q A y
  let S : I → Prop := fun a => choiceTraceOutput G x k Q A y a = t ∧ choiceTraceCode G x k Q A y a = []
  let J := {a : I // S a}
  have hin (a : J) : choiceTraceInput G x k Q A y a.val = t := by
    have he := (traceIndex_valid G x k Q (A a.val.1) (y a.val.1) a.val.2).2
    change SpliceExecution G x (choiceTraceInput G x k Q A y a.val)
      (choiceTraceCode G x k Q A y a.val) (choiceTraceOutput G x k Q A y a.val) at he
    rw [a.property.1,a.property.2,SpliceExecution.nil_iff] at he
    exact he
  have hi : Function.Injective (fun a : J => a.val.1) := by
    intro a b hab
    apply Subtype.ext
    apply choiceTrace_injective G x k Q A y
    exact Prod.ext ((hin a).trans (hin b).symm)
      (Prod.ext hab (a.property.2.trans b.property.2.symm))
  have hm' (a : J) : choiceTraceMass G x k Q A y m a.val = m t a.val.1 := by
    unfold choiceTraceMass
    rw [hin a,traceIndexMass_nil G x k Q (A a.val.1) (y a.val.1) a.val.2 a.property.2,mul_one]
  have hA (a : J) : t ∈ A a.val.1 := (hin a) ▸ a.val.2.1.property
  have he : finiteInverseLoad (choiceTraceOutput G x k Q A y)
      (fun a => if choiceTraceCode G x k Q A y a = [] then choiceTraceMass G x k Q A y m a else 0) t =
      ∑ a : J, m t a.val.1 := by
    unfold finiteInverseLoad
    simp only [← ite_and]
    change (∑ a : I, if S a then choiceTraceMass G x k Q A y m a else 0) = _
    calc
      _ = ∑ a : J, choiceTraceMass G x k Q A y m a.val := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by intro a; simp) _
      _ = _ := Finset.sum_congr rfl (fun a _ => hm' a)
  rw [he]
  have hb := sum_comp_le_sum_of_injective (fun a : J => a.val.1) hi
    (fun r => if t ∈ A r then m t r else 0) (by intro r; split_ifs; exact hm t r; exact le_refl _)
  simpa only [ite_eq_left (hA _)] using hb

end NoSwitchDensity

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointNil
attribute [local instance] Classical.propDecidable Classical.decEq

theorem oldRunArrival_integral {W : Type*} [Fintype W]
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (A : Finset W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => oldRunArrival (fun i => q (η i)) k z A) =
      oldRunArrival (fun _ => finiteOldKernel Q p q) k z A := by
  unfold oldRunArrival
  rw [finiteFamilyIntegral_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : oldRunVertices k z r 0 ∈ A
  · simp only [ite_eq_left h]
    exact oldRunWeight_integral Q p k q z r
  · simp [h,finiteFamilyIntegral]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem amplificationNilRow_arrival_le (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) :
    q.amplificationNilRow Q B x k n p ω ≤
      if n ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧ (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        ∑ z : ↥B, oldRunArrival (fun _ => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)) k z
          (Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x) else 0 := by
  let A : Finset ↥B := Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x
  let H := n ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧ (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  have hb (η : ℕ → Set E) :
      finiteInverseLoad (q.amplificationOutput Q B x k n)
        (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0)
        (finiteFieldSet Q ω,η) ≤
      if H then ∑ z : ↥B, oldRunArrival (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z A else 0 := by
    apply (finiteChoiceNilLoad_le G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2)
      (fun s r => q.allAmplificationWeight B k r s.2)
      (fun s r => q.allAmplificationWeight_nonneg B k r s.2) (finiteFieldSet Q ω,η)).trans
    rw [Fintype.sum_prod_type]
    by_cases h : H
    · rw [ite_eq_left h]
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro r _
      by_cases hs : (finiteFieldSet Q ω,η) ∈ q.allAmplificationInputs Q B x k n (z,r)
      · rw [ite_eq_left hs]
        have hi := (q.mem_amplificationInputs Q B x k n z r _).mp hs
        have ha : oldRunVertices k z r 0 ∈ A := by
          simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,amplificationVertices] using hi.2.2.2.2.2.1
        rw [ite_eq_left ha]
        exact le_rfl
      · rw [ite_eq_right hs]
        split_ifs
        · exact oldRunWeight_nonneg _ (fun i a b => q.nonneg (η i) a.val b.val) k z r
        · exact le_refl _
    · rw [ite_eq_right h]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro z _
      apply Finset.sum_eq_zero
      intro r _
      rw [ite_eq_right (by
        intro hs
        have hi := (q.mem_amplificationInputs Q B x k n z r _).mp hs
        exact h ⟨hi.2.2.2.1,hi.2.2.2.2.1⟩)]
  change _ ≤ if H then ∑ z : ↥B,
    oldRunArrival (fun _ => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)) k z A else 0
  calc
    _ ≤ finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if H then
        ∑ z : ↥B, oldRunArrival (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z A else 0) := by
      apply Finset.sum_le_sum
      intro η _
      exact mul_le_mul_of_nonneg_left (hb _) (finiteFamilyWeight_nonneg Q (Finset.Icc 1 k) p η)
    _ = _ := by
      by_cases h : H
      · simp only [ite_eq_left h,finiteFamilyIntegral_sum]
        apply Finset.sum_congr rfl
        intro z _
        exact oldRunArrival_integral Q p k (fun η (a b : ↥B) => q.mass η a.val b.val) z A
      · simp only [ite_eq_right h,finiteFamilyIntegral,mul_zero,Finset.sum_const_zero]

end LocalEndpointRule
end AllEndpointNil

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointNilBound
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}



theorem amplificationNilRow_bound {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    q.amplificationNilRow Q B x k n p ω ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k := by
  apply (q.amplificationNilRow_arrival_le Q B x k n p ω).trans
  split_ifs with h
  · let A : Finset ↥B := Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x
    let K := fun (_ : ℕ) => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)
    have hK (i : ℕ) (a b : ↥B) : K i a b = q.kernel p a.val b.val :=
      q.finiteOldKernel_eq_kernel Q p a.val b.val (hQ a.val a.property)
    have hnK (i : ℕ) (a b : ↥B) : 0 ≤ K i a b := by rw [hK i a b]; exact q.kernel_nonneg p a.val b.val
    have hc (i : ℕ) (b : ↥B) : (∑ a, K i a b) ≤ q.successProbability p (root i₀) := by
      simp only [hK]
      rw [Finset.sum_coe_sort B (fun a => q.kernel p a b.val)]
      exact ((q.summable_kernel_column p b.val).sum_le_tsum B (fun a _ => q.kernel_nonneg p a b.val)).trans
        (q.kernel_column_le_success root weight Γ htr hΓ hw i₀ hw₀ p b.val)
    have hf : (cluster G (finiteFieldSet Q ω) x).Finite := cluster_finite_of_finite_edges G
      ω.val.finite_toSet x
    have hcard : A.card ≤ 2*n := by
      have hh : A.card ≤ hf.toFinset.card := Finset.card_le_card_of_injOn Subtype.val
        (by intro a ha; exact hf.mem_toFinset.mpr (Finset.mem_filter.mp ha).2)
        (fun _ _ _ _ he => Subtype.val_injective he)
      rw [← Set.ncard_eq_toFinset_card (cluster G (finiteFieldSet Q ω) x) hf] at hh
      exact hh.trans h.2.le
    calc
      _ ≤ (A.card:ℝ) * q.successProbability p (root i₀)^k :=
        sum_oldRunArrival_le K hnK _ (q.successProbability_nonneg p (root i₀)) hc k A
      _ ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg (q.successProbability_nonneg p (root i₀)) _)
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (q.successProbability_nonneg p (root i₀)) _)

end LocalEndpointRule
end AllEndpointNilBound

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointNear
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



theorem amplificationNearPairMass_bound [Nonempty E]
    (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n d : ℕ) (p : unitInterval)
    (hdeg : ∀ a, degree G a ≤ d) :
    q.amplificationNearPairMass Q B x k n p ≤
      (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L ^ k *
        ∑ a : q.AmplificationIndex Q B x k n,
          spliceTupleWeight Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n a) *
            q.amplificationMass Q B x k n a := by
  let out := q.amplificationOutput Q B x k n
  let code := q.amplificationCode Q B x k n
  let added := q.amplificationAdded Q B x k n
  let m := q.amplificationMass Q B x k n
  let e (a : q.AmplificationIndex Q B x k n) := (code a).headD (0,Classical.choice ‹Nonempty E›) |>.2
  have hfin (a : q.AmplificationIndex Q B x k n) : (cluster G (out a).1 x).Finite :=
    (q.amplificationIndex_support Q B x k n a).2.2.2.1
  have hhead (a : q.AmplificationIndex Q B x k n) (hc : code a ≠ []) :
      OpenMarkedPivotal G (out a).1 {a.1.1.val} x (e a) ∧
      hangingSide G (out a).1 x (e a) = added a ∧
      (hangingSide G (out a).1 x (e a)).ncard ≤ k*M := by
    cases hh : code a with
    | nil => exact (hc hh).elim
    | cons w rest =>
      have ht := q.amplificationIndex_trace Q B x k n a
      change SpliceTrace G x (q.amplificationInput Q B x k n a).2
        (amplificationVertices B k a.1.1 a.1.2) k 0 (q.amplificationInput Q B x k n a).1
        (code a) (out a).1 at ht
      rw [hh] at ht
      have he : e a = w.2 := by simp only [e,hh,List.headD_cons]
      rw [he]
      refine ⟨?_,ht.head_hanging G x _ _ k 0 w.1 _ _ w.2 rest,
        ht.head_hanging_cap G x _ _ k 0 w.1 M _ _ w.2 rest (q.amplificationIndex_caps Q B x k n a)⟩
      simpa only [amplificationVertices,oldRunVertices_last] using
        ht.seams_pivotal G x _ _ k 0 _ _ (w::rest) w (List.mem_cons_self)
  let S (a : q.AmplificationIndex Q B x k n) : Finset V := if code a = [] then ∅ else
    nearHangingEndpoints G hloc (out a).1 x a.1.1.val (e a) (k*M) (hfin a)
  let R (a b : q.AmplificationIndex Q B x k n) := code a ≠ [] ∧ code b ≠ [] ∧
    ¬GraphSeparated G (added a) (added b)
  have hS (a b : q.AmplificationIndex Q B x k n) (he : (out a).1 = (out b).1) (h : R a b) :
      b.1.1.val ∈ S a := by
    obtain ⟨hpa,hea,_⟩ := hhead a h.1
    obtain ⟨hpb,heb,hcb⟩ := hhead b h.2.1
    have hn := h.2.2
    rw [← hea,← heb,← he] at hn
    rw [← he] at hpb hcb
    simp only [S,ite_eq_right h.1]
    exact mem_nearHangingEndpoints_of_not_separated G hloc (out a).1 x a.1.1.val b.1.1.val
      (e a) (e b) (k*M) (hfin a) hpa hpb hcb hn
  have hN (a : q.AmplificationIndex Q B x k n) : (S a).card ≤ (k*M)+(k*M)^2+d*(k*M)^3 := by
    by_cases h : code a = []
    · simp only [S,ite_eq_left h,Finset.card_empty,Nat.zero_le]
    · simp only [S,ite_eq_right h]
      exact nearHangingEndpoints_card_le G hloc (out a).1 x a.1.1.val (e a) (k*M) d
        (hfin a) (hhead a h).2.2 hdeg
  have hC : 0 ≤ inverseCodeMass M L ^ k := pow_nonneg
    (add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => gapWeight_nonneg L (by linarith) l)) _
  simpa only [amplificationNearPairMass,out,m,R,added] using finite_near_pair_mass_le Q (Finset.Icc 1 k) (Finset.Icc 1 k) p out out m m
    (q.amplificationMass_nonneg Q B x k n) (q.amplificationMass_nonneg Q B x k n)
    (fun a => a.1.1.val) R S hS ((k*M)+(k*M)^2+d*(k*M)^3) hN _ hC
    (fun a z _ => q.amplificationEndpointMass_bound hL Q B x k n p (out a).1
      ((mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) (out a)).mp (q.amplificationOutput_mem Q B x k n a)).1 z)

end LocalEndpointRule
end AllEndpointNear

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteThreeClass
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finiteRootLoad_three_classes_le {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : unitInterval) (out : I → SpliceState E)
    (m : I → ℝ) (hm : ∀ a, 0 ≤ m a) (hs : ∀ a, out a ∈ finiteSpliceDomain Q J)
    (C : I → Prop) (R : I → I → Prop) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J p (finiteInverseLoad out m) ω ^ 2) ≤
      2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
        finiteRootLoad Q J p (finiteInverseLoad out (fun a => if C a then m a else 0)) ω *
        finiteRootLoad Q J p (finiteInverseLoad out m) ω) +
      commonRootPairMass Q J p out m (fun a b => ¬C a ∧ ¬C b ∧ R a b) +
      commonRootPairMass Q J p out m (fun a b => ¬C a ∧ ¬C b ∧ ¬R a b) := by
  let m₀ := fun a => if C a then m a else 0
  let row := finiteRootLoad Q J p (finiteInverseLoad out m)
  let nilrow := finiteRootLoad Q J p (finiteInverseLoad out m₀)
  have hcross : (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω * nilrow ω) =
      ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω := by
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have heq : 2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) =
      (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) +
      (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω * nilrow ω) := by
    rw [hcross]; ring
  change _ ≤ 2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) + _ + _
  rw [heq]
  dsimp only [nilrow,row]
  simp only [pow_two,← mul_assoc]
  rw [finiteRootLoad_pair_expansion Q J J p out out m m hs hs,
    finiteRootLoad_pair_expansion Q J J p out out m₀ m hs hs,
    finiteRootLoad_pair_expansion Q J J p out out m m₀ hs hs]
  unfold commonRootPairMass
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hw : 0 ≤ jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) :=
    jointTupleWeight_nonneg Q J J p _
  have ht : 0 ≤ jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) * m a * m b :=
    mul_nonneg (mul_nonneg hw (hm a)) (hm b)
  dsimp only [m₀]
  by_cases hab : (out a).1 = (out b).1
  · simp only [hab,true_and,if_true]
    by_cases ha : C a <;> by_cases hb : C b <;> by_cases hr : R a b <;>
      simp only [ha,hb,hr,not_true_eq_false,not_false_eq_true,and_true,and_false,
        if_true,if_false,mul_zero,zero_mul] <;> linarith
  · simp only [hab,false_and,if_false,zero_add,le_refl]

end FiniteThreeClass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointMomentIdentities
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteRootLoad_inverse_mean {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E) (m : I → ℝ)
    (hs : ∀ a, out a ∈ finiteSpliceDomain Q J) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * finiteRootLoad Q J p (finiteInverseLoad out m) ω) =
      ∑ a, spliceTupleWeight Q J p (out a) * m a := by
  rw [finiteRootLoad_mean]
  simp only [finiteInverseLoad,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_ite_eq,ite_eq_left (hs a)]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem amplificationRow_nonneg (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    0 ≤ q.amplificationRow Q B x k n p ω := by
  rw [q.amplificationRow_eq_load]
  apply finiteRootLoad_nonneg
  intro s _
  exact finiteInverseLoad_nonneg _ _ (q.amplificationMass_nonneg Q B x k n) s

theorem amplificationRow_mean_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) :
    finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) =
      ∑ a : q.AmplificationIndex Q B x k n,
        spliceTupleWeight Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n a) *
          q.amplificationMass Q B x k n a := by
  simp only [finiteFieldIntegral,q.amplificationRow_eq_load,restrictFiniteField_fieldSet]
  exact finiteRootLoad_inverse_mean Q (Finset.Icc 1 k) p _ _ (q.amplificationOutput_mem Q B x k n)

 

theorem amplificationSeparated_class_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) :
    commonRootPairMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (q.amplificationMass Q B x k n) (fun a b =>
        q.amplificationCode Q B x k n a ≠ [] ∧ q.amplificationCode Q B x k n b ≠ [] ∧
        GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)) =
    finiteChoiceSeparatedPairMass G x k Q p
      (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
      (allAmplificationVertices B k) (allAmplificationVertices B k)
      (q.allAmplificationWeight B k) (q.allAmplificationWeight B k) := by
  unfold commonRootPairMass finiteChoiceSeparatedPairMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with ha hb hb
  · rfl
  · exfalso
    apply hb
    dsimp only [amplificationAdded,amplificationOutput,amplificationCode,amplificationInput] at ha
    rcases ha with ⟨he,hca,hcb,hsep⟩
    refine ⟨he,hca,hcb,?_⟩
    simpa only [he] using hsep
  · exfalso
    apply ha
    dsimp only [amplificationAdded,amplificationOutput,amplificationCode,amplificationInput]
    rcases hb with ⟨he,hca,hcb,hsep⟩
    refine ⟨he,hca,hcb,?_⟩
    simpa only [he] using hsep
  · rfl

end LocalEndpointRule
end AllEndpointMomentIdentities

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationRow_second_moment_le [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x : V) (k n d : ℕ)
    (hdeg : ∀ a, degree G a ≤ d)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆ Q) :
    finiteFieldIntegral Q p (fun ω => q.amplificationRow Q B x k n p ω ^ 2) ≤
      (((4*n:ℕ):ℝ) * q.successProbability p (root i₀)^k +
        (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L ^ k) *
          finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) +
      (((2*n:ℕ):ℝ) * (c*((k*M:ℕ)*q.successProbability p (root i₀)^k)))^2 *
        finiteClusterWindowMass G Q p x (n-k*M) (2*n) := by
  let out := q.amplificationOutput Q B x k n
  let m := q.amplificationMass Q B x k n
  let C := fun a => q.amplificationCode Q B x k n a = []
  let R := fun a b => ¬GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)
  let row := finiteRootLoad Q (Finset.Icc 1 k) p (finiteInverseLoad out m)
  let nilrow := q.amplificationNilRow Q B x k n p
  let b₀ := ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω
  let bnil := ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω
  let S := finiteChoiceSeparatedPairMass G x k Q p
    (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
    (allAmplificationVertices B k) (allAmplificationVertices B k)
    (q.allAmplificationWeight B k) (q.allAmplificationWeight B k)
  have hrow (ω : FiniteField Q) : q.amplificationRow Q B x k n p (finiteFieldSet Q ω) = row ω := by
    rw [q.amplificationRow_eq_load,restrictFiniteField_fieldSet]
  have hmean : finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) = b₀ := by
    simp only [finiteFieldIntegral,hrow,b₀]
  have hpart := finiteRootLoad_three_classes_le Q (Finset.Icc 1 k) p out m
    (q.amplificationMass_nonneg Q B x k n) (q.amplificationOutput_mem Q B x k n) C R
  have hnear_eq : commonRootPairMass Q (Finset.Icc 1 k) p out m
      (fun a b => ¬C a ∧ ¬C b ∧ R a b) = q.amplificationNearPairMass Q B x k n p := by
    simp only [commonRootPairMass,amplificationNearPairMass,C,R,out,m]
  have hsep_eq : commonRootPairMass Q (Finset.Icc 1 k) p out m
      (fun a b => ¬C a ∧ ¬C b ∧ ¬R a b) = S := by
    simpa only [C,R,not_not] using q.amplificationSeparated_class_eq Q B x k n p
  rw [hnear_eq,hsep_eq] at hpart
  have hnilfun : finiteInverseLoad out (fun a => @ite ℝ (C a) (Classical.propDecidable _) (m a) 0) =
      finiteInverseLoad (q.amplificationOutput Q B x k n)
        (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0) := by
    apply congrArg (finiteInverseLoad out)
    funext a
    dsimp only [C,m]
    split_ifs <;> rfl
  rw [hnilfun] at hpart
  change (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω ^ 2) ≤
    2*bnil + q.amplificationNearPairMass Q B x k n p + S at hpart
  have hnil : bnil ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k * b₀ := by
    dsimp only [bnil,b₀]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    have hr : 0 ≤ row ω := by rw [← hrow]; exact q.amplificationRow_nonneg Q B x k n p _
    have hn := q.amplificationNilRow_bound root weight Γ htr (fun a ha => hΓ ha) hw i₀ hw₀ Q B x k n p ω
      (fun a ha => (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (hQ a ha))
    calc
      _ ≤ finiteFieldWeight Q p ω * (((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k) * row ω :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (finiteFieldWeight_nonneg Q p ω)) hr
      _ = _ := by ring
  have hnear := q.amplificationNearPairMass_bound hL Q B x k n d p hdeg
  rw [← q.amplificationRow_mean_eq Q B x k n p,hmean] at hnear
  have hsep := q.amplificationSeparatedSecondMoment_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (root i₀) Q B p x k n hQ
  have hfinal := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hnil (show (0:ℝ) ≤ 2 by norm_num)) hnear) hsep
  rw [hmean]
  simp only [finiteFieldIntegral,hrow]
  apply hpart.trans
  convert hfinal using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end LocalEndpointRule
end AllEndpointSecondMoment

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Covariance
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section CanonicalAmplificationRow
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationBonds_query {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (x a : V) (ha : a ∈ q.amplificationBall k n x) :
    incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆
      q.amplificationBonds k n x := by
  apply incidentSupport_mono
  intro y hy
  simp only [Set.Finite.mem_toFinset] at hy ⊢
  exact reachBall_triangle G x a (2*n+k*M) (max q.radius M)
    (by simpa only [amplificationBall,Set.Finite.mem_toFinset] using ha) hy

theorem amplificationBonds_root {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (x : V) :
    incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆
      q.amplificationBonds k n x := by
  apply incidentSupport_ball_mono
  unfold amplificationRadius
  omega

theorem amplificationLoad_row (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (ω : Set E) (x : V) :
    (q.amplificationLoad o hL k n p).row ω x =
      q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p ω / n := by
  change (∑' z, q.amplifiedMass k n p ω x z) = _
  rw [tsum_eq_sum (s := q.amplificationBall k n x) (fun z hz => by
    simp only [amplifiedMass,dite_eq_right hz])]
  rw [← Finset.sum_coe_sort]
  simp only [amplifiedMass,dite_eq_left (Subtype.prop _)]
  exact (Finset.sum_div _ _ _).symm

theorem amplificationRow_local {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    q.amplificationRow Q B x k n p ω = q.amplificationRow Q B x k n p (ω ∩ (Q : Set E)) := by
  unfold amplificationRow
  apply Finset.sum_congr rfl
  intro z _
  exact q.amplificationMarginal_local Q B x k n z p ω

theorem amplificationLoad_mean_finite (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (x : V) :
    (∫ ω, (q.amplificationLoad o hL k n p).row ω x ∂law p) =
      finiteFieldIntegral (q.amplificationBonds k n x) p
        (q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p) / n := by
  simp_rw [q.amplificationLoad_row o hL k n p]
  rw [integral_div]
  congr 1
  exact integral_finite_local _ p _ (q.amplificationRow_local _ _ x k n p)

theorem amplificationLoad_second_moment_finite (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) (x : V) :
    (∫ ω, (q.amplificationLoad o hL k n p).row ω x ^ 2 ∂law p) =
      finiteFieldIntegral (q.amplificationBonds k n x) p (fun ω =>
        q.amplificationRow (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n p ω ^ 2) / (n:ℝ)^2 := by
  simp_rw [q.amplificationLoad_row o hL k n p,div_pow]
  rw [integral_div]
  congr 1
  exact integral_finite_local _ p _ (fun ω => congrArg (·^2) (q.amplificationRow_local _ _ x k n p ω))

end LocalEndpointRule
end CanonicalAmplificationRow

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section NormalizedAmplificationMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationLoad_second_moment_le [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (x : V) (k n d : ℕ) (hn : 0 < n)
    (hdeg : ∀ a, degree G a ≤ d) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ^ 2 ∂law p) ≤
      (4 * q.successProbability p (root i₀)^k +
        (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L^k / n) *
          (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ∂law p) +
      (2 * (c*((k*M:ℕ)*q.successProbability p (root i₀)^k)))^2 *
        finiteClusterWindowMass G (q.amplificationBonds k n x) p x (n-k*M) (2*n) := by
  rw [q.amplificationLoad_second_moment_finite,q.amplificationLoad_mean_finite]
  have h := q.amplificationRow_second_moment_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
    i₀ hw₀ hL (q.amplificationBonds k n x) (q.amplificationBall k n x) p x k n d hdeg
    (fun a ha => q.amplificationBonds_query k n x a ha)
  have hn' : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  apply (div_le_div_of_nonneg_right h (sq_nonneg (n:ℝ))).trans_eq
  push_cast
  field_simp

end LocalEndpointRule
end NormalizedAmplificationMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FinitePathExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finitePathTest_succ (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (k : ℕ) (z : ↥B) :
    finitePathTest B K F (k+1) z = ∑ a : ↥B, K z.val a.val * finitePathTest B K F k a :=
  oldRun_test_succ (fun _ (a b : ↥B) => K a.val b.val) (fun (a : ↥B) => F a.val) k z

 

theorem finitePathTest_support (G : BondGraph V E) (B : Finset V) (K : V → V → ℝ) (F : V → ℝ)
    (O : Set V) (x : V) (R M : ℕ)
    (hK : ∀ a b, K a b ≠ 0 → a ∈ O ∧ a ∈ reachBall G b M)
    (hF : ∀ a, F a ≠ 0 → a ∈ O ∧ a ∈ reachBall G x R)
    (k : ℕ) (z : ↥B) (hz : finitePathTest B K F k z ≠ 0) :
    z.val ∈ O ∧ z.val ∈ reachBall G x (R+k*M) := by
  induction k generalizing z with
  | zero => simpa using hF z.val (by simpa using hz)
  | succ k ih =>
    rw [finitePathTest_succ] at hz
    obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    have hh := mul_ne_zero_iff.mp ha
    obtain ⟨haO,haB⟩ := ih a hh.2
    obtain ⟨hzO,hzB⟩ := hK z.val a.val hh.1
    refine ⟨hzO,?_⟩
    have hg := reachBall_triangle G x a.val (R+k*M) M haB hzB
    simpa only [Nat.add_mul,one_mul,Nat.add_assoc] using hg

 

theorem finitePathTest_total (G : BondGraph V E) (B : Finset V) (K : V → V → ℝ) (F : V → ℝ)
    (O : Set V) (x : V) (R M N : ℕ) (u : ℝ)
    (hK : ∀ a b, K a b ≠ 0 → a ∈ O ∧ a ∈ reachBall G b M)
    (hF : ∀ a, F a ≠ 0 → a ∈ O ∧ a ∈ reachBall G x R)
    (hcolumn : ∀ j < N, ∀ a : ↥B, a.val ∈ O → a.val ∈ reachBall G x (R+j*M) →
      ∑ z : ↥B, K z.val a.val = u) :
    ∀ j ≤ N, (∑ z : ↥B, finitePathTest B K F j z) = u^j * ∑ z : ↥B, F z.val := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    simp_rw [finitePathTest_succ]
    rw [Finset.sum_comm]
    have he : (∑ a : ↥B, ∑ z : ↥B, K z.val a.val * finitePathTest B K F j a) =
        u * ∑ a : ↥B, finitePathTest B K F j a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul]
      by_cases ha : finitePathTest B K F j a = 0
      · simp only [ha,mul_zero]
      · obtain ⟨haO,haB⟩ := finitePathTest_support G B K F O x R M hK hF j a ha
        rw [hcolumn j (by omega) a haO haB]
    rw [he,ih (by omega)]
    ring

end FinitePathExhaustion

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationBoundaryExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem kernel_range_support {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (a b : V) (h : q.kernel p a b ≠ 0) : a ∈ O ∧ a ∈ reachBall G b M := by
  constructor
  · by_contra ha
    exact h (q.kernel_zero_of_start_not_mem p a b ha)
  · by_contra ha
    exact h (q.kernel_outside_reverse_ball_zero p a b ha)

theorem orbitBinConnection_range_support (o : V) (p : unitInterval) (n : ℕ) (x a : V)
    (h : orbitBinConnection G p o n x a ≠ 0) :
    a ∈ vertexOrbit G o ∧ a ∈ reachBall G x (2*n) := by
  have ha : a ∈ vertexOrbit G o := by
    by_contra ha
    exact h (by simp only [orbitBinConnection,ha,and_false,if_false])
  refine ⟨ha,?_⟩
  by_contra hb
  exact h (by simp only [orbitBinConnection,binConnection_outside G p n x a hb,ite_self])

theorem amplificationBall_column {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (k n j : ℕ) (hj : j < k) (x a : V)
    (ha : a ∈ reachBall G x (2*n+j*M)) :
    (∑ z : ↥(q.amplificationBall k n x), q.kernel p z.val a) = ∑' z, q.kernel p z a := by
  rw [Finset.sum_coe_sort (q.amplificationBall k n x) (fun z => q.kernel p z a)]
  symm
  apply tsum_eq_sum
  intro z hz
  apply q.kernel_outside_reverse_ball_zero
  intro hza
  have hh := reachBall_triangle G x a (2*n+j*M) M ha hza
  have hle : (2*n+j*M)+M ≤ 2*n+k*M := by
    calc
      _ = 2*n+(j+1)*M := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right M (by omega)) _
  exact hz (by
    simpa only [amplificationBall,Set.Finite.mem_toFinset] using (reachBall_mono G x hle hh))

theorem amplificationPath_total {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (k n : ℕ) (x : V) (hx : x ∈ vertexOrbit G (root i₀)) :
    (∑ z : ↥(q.amplificationBall k n x),
      finitePathTest (q.amplificationBall k n x) (q.kernel p) (orbitBinConnection G p (root i₀) n x) k z) =
      q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n := by
  have ht := finitePathTest_total G (q.amplificationBall k n x) (q.kernel p)
    (orbitBinConnection G p (root i₀) n x) (vertexOrbit G (root i₀)) x (2*n) M k
    (q.successProbability p (root i₀)) (q.kernel_range_support p)
    (orbitBinConnection_range_support (root i₀) p n x) (by
      intro j hj a haO haB
      rw [q.amplificationBall_column p k n j hj x a.val haB]
      exact q.kernel_column_eq_success root weight Γ htr hΓ hw i₀ hw₀ p a.val haO) k le_rfl
  rw [ht]
  congr 1
  rw [Finset.sum_coe_sort (q.amplificationBall k n x) (orbitBinConnection G p (root i₀) n x),← orbitBinConnection_row G hloc p (root i₀) n x hx]
  symm
  apply tsum_eq_sum
  intro z hz
  by_contra h
  have hb := (orbitBinConnection_range_support (root i₀) p n x z h).2
  exact hz (by
    simpa only [amplificationBall,Set.Finite.mem_toFinset] using
      reachBall_mono G x (Nat.le_add_right (2*n) (k*M)) hb)

end LocalEndpointRule
end AmplificationBoundaryExhaustion

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationExactMean
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationMarginal_mean_pathTest [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ vertexOrbit G o)
    (hroot : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q)
    (hquery : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      finitePathTest B (q.kernel p) (orbitBinConnection G p o n x) k z := by
  by_cases hz : z.val ∈ vertexOrbit G o
  · rw [q.amplificationMarginal_mean_kernel Q B x k n z p hx hz hquery]
    unfold finitePathTest
    apply Finset.sum_congr rfl
    intro r _
    rw [finiteBinConnection_eq_binConnection G hloc Q p x n _ hroot]
    by_cases hr : oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r = 0
    · simp only [hr,mul_zero,zero_mul]
    · have hy : (oldRunVertices k z r 0).val ∈ vertexOrbit G o :=
        oldRun_endpoint_mem (fun a : ↥B => a.val ∈ vertexOrbit G o)
          (fun _ (a b : ↥B) => q.kernel p a.val b.val)
          (fun _ a b hab => by
            by_contra hb
            exact hab (q.kernel_zero_of_end_not_mem p a.val b.val hb)) k z hz r hr
      rw [orbitBinConnection,ite_eq_left ⟨hx,hy⟩]
      exact mul_comm _ _
  · have hm (ω : Set E) : q.amplificationMarginal Q B x k n z p ω = 0 := by
      by_contra h
      exact hz (q.amplificationMarginal_support Q B x k n z p ω h).2.1
    simp_rw [hm,integral_zero]
    symm
    by_contra h
    exact hz (finitePathTest_support G B (q.kernel p) (orbitBinConnection G p o n x)
      (vertexOrbit G o) x (2*n) M (q.kernel_range_support p)
      (orbitBinConnection_range_support o p n x) k z h).1

 

theorem amplificationLoad_mean [Nonempty E] {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n : ℕ) (x : V) (hx : x ∈ vertexOrbit G (root i₀)) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω x ∂law p) =
      q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n := by
  simp_rw [q.amplificationLoad_row]
  rw [integral_div]
  congr 1
  unfold amplificationRow
  rw [integral_finsetSum _ (fun z _ => integrable_finite_local _ p _
    (q.amplificationMarginal_local _ _ x k n z p))]
  simp_rw [q.amplificationMarginal_mean_pathTest (root i₀) _ _ x k n _ p hx
    (q.amplificationBonds_root k n x) (fun a ha =>
      (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (q.amplificationBonds_query k n x a ha))]
  exact q.amplificationPath_total root weight Γ htr hΓ hw i₀ hw₀ p k n x hx

end LocalEndpointRule
end AmplificationExactMean

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationLoadOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem kernel_nonneg (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) :
    0 ≤ q.kernel p x y := integral_nonneg (q.nonneg · x y)

end CappedLocalLoad

 
theorem exists_operator_of_scaled_matrix (F : V → V → ℝ) (c C : ℝ) (hc : 0 < c)
    (A : Hilbert V →L[ℂ] Hilbert V) (hAnorm : ‖A‖ ≤ C)
    (hA : ∀ x y, matrixCoeff A x y = (c * F x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ C/c ∧
      ∀ x y, matrixCoeff T x y = (F x y : ℂ) := by
  refine ⟨((c⁻¹:ℝ):ℂ) • A,?_,?_⟩
  · rw [norm_smul,Complex.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left hAnorm (inv_nonneg.mpr hc.le)
  · intro x y
    change ((c⁻¹:ℝ):ℂ)*matrixCoeff A x y = _
    rw [hA]
    have hc' : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    simp only [Complex.ofReal_inv]
    field_simp

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationLoad_scaled_kernel [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (hL : 1 ≤ L)
    (k n : ℕ) (hn : 0 < n) (p : unitInterval) (x z : V)
    (hz : z ∈ q.amplificationBall k n x) :
    (n:ℝ) * (q.amplificationLoad o hL k n p).kernel p x z =
      ∫ ω, q.amplificationMarginal (q.amplificationBonds k n x) (q.amplificationBall k n x)
        x k n ⟨z,hz⟩ p ω ∂law p := by
  change (n:ℝ) * (∫ ω, q.amplifiedMass k n p ω x z ∂law p) = _
  simp only [amplifiedMass,dite_eq_left hz,integral_div]
  have hn' : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp

 

theorem amplificationLoad_exists_operator [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (hL : 1 ≤ L)
    (k n : ℕ) (hn : 0 < n) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ a b, matrixCoeff A a b = (q.kernel p a b : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ binOrbitRow G p o n * ‖A‖^k / n ∧
      ∀ x z, matrixCoeff T x z = ((q.amplificationLoad o hL k n p).kernel p x z : ℂ) := by
  let F := (q.amplificationLoad o hL k n p).kernel p
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hposA : PositiveRealMatrix A := fun x z => by
    rw [hA]
    exact ⟨rfl,q.kernel_nonneg p x z⟩
  obtain ⟨S,hSnorm,hS⟩ := exists_operator_of_amplification_domination G hloc p o n k A hposA
    (fun x z => (n:ℝ)*F x z) (fun x z => mul_nonneg hn'.le ((q.amplificationLoad o hL k n p).kernel_nonneg p x z))
    (by
      intro H hH x z
      have hposH : PositiveRealMatrix H := fun a b => by
        rw [hH]
        exact ⟨rfl,orbitBinConnection_nonneg G p o n a b⟩
      have hpos := (((hposA.pow k).mul hposH) z x).2
      by_cases hz : z ∈ q.amplificationBall k n x
      · rw [q.amplificationLoad_scaled_kernel o hL k n hn p x z hz]
        by_cases ho : x ∈ vertexOrbit G o ∧ z ∈ vertexOrbit G o
        · exact q.amplificationMarginal_operator_le o _ _ x k n ⟨z,hz⟩ p ho.1 ho.2
            (q.amplificationBonds_root k n x) (fun a ha =>
              (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (q.amplificationBonds_query k n x a ha)) A H hA hH
        · have hm (ω : Set E) : q.amplificationMarginal (q.amplificationBonds k n x)
              (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω = 0 := by
            by_contra h
            have hs := q.amplificationMarginal_support _ _ x k n ⟨z,hz⟩ p ω h
            exact ho ⟨hs.1,hs.2.1⟩
          simpa only [hm,integral_zero] using hpos
      · have he : F x z = 0 := by
          change (∫ ω, q.amplifiedMass k n p ω x z ∂law p) = 0
          simp only [amplifiedMass,dite_eq_right hz,integral_zero]
        simpa only [he,mul_zero] using hpos)
  exact exists_operator_of_scaled_matrix F n _ hn' S hSnorm (by
    intro x z
    simpa only [Complex.ofReal_mul] using hS x z)

end LocalEndpointRule
end AmplificationLoadOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section TruncationOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem truncate_kernel_le (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x y : V) :
    (q.truncate b hb L).kernel p x y ≤ b⁻¹ * q.kernel p x y := by
  rw [kernel,← integral_const_mul]
  exact integral_mono ((q.truncate b hb L).integrable_mass p x y)
    ((q.integrable_mass p x y).const_mul b⁻¹) (q.truncate_mass_le b hb L · x y)

 

theorem truncate_exists_operator (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.kernel p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ ‖A‖/b ∧
      ∀ x y, matrixCoeff T x y = ((q.truncate b hb L).kernel p x y : ℂ) := by
  have hscale (x y : V) : matrixCoeff (((b⁻¹:ℝ):ℂ) • A) x y = (b⁻¹ * q.kernel p x y : ℝ) := by
    change ((b⁻¹:ℝ):ℂ)*matrixCoeff A x y = _
    rw [hA,Complex.ofReal_mul]
  obtain ⟨T,hT,hK⟩ := exists_operator_of_matrix_domination
    (fun x y => b⁻¹ * q.kernel p x y) ((q.truncate b hb L).kernel p)
    (fun x y => mul_nonneg (inv_nonneg.mpr hb.le) (q.kernel_nonneg p x y))
    (fun x y => by
      rw [abs_of_nonneg ((q.truncate b hb L).kernel_nonneg p x y)]
      exact q.truncate_kernel_le p b hb L x y)
    (((b⁻¹:ℝ):ℂ) • A) hscale
  refine ⟨T,hT.trans_eq ?_,hK⟩
  rw [norm_smul,Complex.norm_of_nonneg (inv_nonneg.mpr hb.le)]
  ring

end CappedLocalLoad
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 
theorem normalize_mass_operator (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V) (C : ℝ) (hAnorm : ‖A‖ ≤ C)
    (hA : ∀ x y, matrixCoeff A x y = (q.kernel p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ C/q.successProbability p o ∧
      ∀ x y, matrixCoeff T x y = (q.normalizedKernel o p x y : ℂ) := by
  apply exists_operator_of_scaled_matrix (q.normalizedKernel o p) (q.successProbability p o) C hu A hAnorm
  intro x y
  rw [hA]
  simp only [normalizedKernel,← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc,mul_inv_cancel₀ hu.ne',one_mul]

 

theorem mass_operator_of_normalized (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ = q.successProbability p o * ‖A‖ ∧
      ∀ x y, matrixCoeff T x y = (q.kernel p x y : ℂ) := by
  refine ⟨(q.successProbability p o : ℂ) • A,?_,?_⟩
  · rw [norm_smul,Complex.norm_of_nonneg hu.le]
  · intro x y
    change (q.successProbability p o : ℂ)*matrixCoeff A x y = _
    rw [hA]
    simp only [normalizedKernel,← Complex.ofReal_mul]
    congr 1
    rw [← mul_assoc,mul_inv_cancel₀ hu.ne',one_mul]

end LocalEndpointRule
end TruncationOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationTruncationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem normalized_operator_norm_pos (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) : 0 < ‖A‖ := by
  apply norm_pos_iff.mpr
  intro ha
  have hz (y : V) : q.kernel p o y = 0 := by
    have he := hA o y
    rw [ha] at he
    have he' : (q.successProbability p o)⁻¹ * q.kernel p o y = 0 :=
      Complex.ofReal_eq_zero.mp he.symm
    exact (mul_eq_zero.mp he').resolve_left (inv_ne_zero hu.ne')
  have he : q.successProbability p o = 0 := by
    simp only [successProbability,hz,tsum_zero]
  exact hu.ne' he

 

theorem amplification_truncation_step [Nonempty E] {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n : ℕ) (hn : 0 < n)
    (hu : 0 < q.successProbability p (root i₀))
    (hbin : 0 < binOrbitRow G p (root i₀) n)
    (b L' : ℝ) (hb : 0 < b)
    (hmoment : (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p) / b ≤
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/4)
    (hbad : b * (law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/4)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) (2*n+k*M) L',
      (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n)/(2*b) ≤
        q'.successProbability p (root i₀) ∧
      ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧ ‖A'‖ ≤ 2*‖A‖^k ∧
        ∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ) := by
  let load := q.amplificationLoad (root i₀) hL k n p
  let q' := load.truncate b hb L'
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hb₀ : 0 < q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n :=
    div_pos (mul_pos (pow_pos hu _) hbin) hn'
  have hself : root i₀ ∈ vertexOrbit G (root i₀) := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have hmean := q.amplificationLoad_mean root weight Γ htr hΓ hw i₀ hw₀ hL p k n (root i₀) hself
  have hnew := load.truncate_success_lower p b hb L' (root i₀) _ hmean.ge hmoment hbad
  have hu' : 0 < q'.successProbability p (root i₀) :=
    (div_pos hb₀ (mul_pos (by norm_num) hb)).trans_le hnew
  obtain ⟨B,hBnorm,hB⟩ := q.mass_operator_of_normalized (root i₀) p hu A hA
  obtain ⟨C,hCnorm,hC⟩ := q.amplificationLoad_exists_operator (root i₀) hL k n hn p B hB
  obtain ⟨D,hDnorm,hD⟩ := load.truncate_exists_operator p b hb L' C hC
  have hD' : ‖D‖ ≤ (binOrbitRow G p (root i₀) n * (q.successProbability p (root i₀)*‖A‖)^k/n)/b := by
    rw [hBnorm] at hCnorm
    exact hDnorm.trans (div_le_div_of_nonneg_right hCnorm hb.le)
  obtain ⟨A',hA'norm,hA'⟩ := q'.normalize_mass_operator (root i₀) p hu' D _ hD' hD
  refine ⟨q',hnew,A',q'.normalized_operator_norm_pos (root i₀) p hu' A' hA',hA'norm.trans ?_,hA'⟩
  apply (div_le_iff₀ hu').mpr
  apply (div_le_iff₀ hb).mpr
  apply (div_le_iff₀ hn').mpr
  have hret := (div_le_iff₀ (mul_pos (show (0:ℝ)<2 by norm_num) hb)).mp hnew
  have hret' := (div_le_iff₀ hn').mp hret
  rw [mul_pow]
  calc
    _ = (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n) * ‖A‖^k := by ring
    _ ≤ (q'.successProbability p (root i₀)*(2*b)*n)*‖A‖^k :=
      mul_le_mul_of_nonneg_right hret' (pow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

end LocalEndpointRule
end AmplificationTruncationStep

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

theorem finiteClusterWindowMass_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (p : unitInterval) (x : V) (lo hi : ℕ)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x hi).toFinset ⊆ Q) :
    finiteClusterWindowMass G Q p x lo hi = clusterWindowProbability G p x lo hi := by
  let S := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  let f : Set E → ℝ := fun ω => if ClusterWindow G x lo hi ω then 1 else 0
  have hf (ω) : f ω = f (ω ∩ (S : Set E)) :=
    if_congr (clusterWindow_local G hloc x lo hi ω) rfl rfl
  have he := integral_finite_local Q p f (finite_local_of_subset S Q hQ f hf)
  trans ∫ ω, f ω ∂law p
  · rw [he]
    unfold finiteClusterWindowMass finiteFieldIntegral
    apply Finset.sum_congr rfl
    intro η _
    congr 1
    unfold f ClusterWindow
    dsimp only
    split_ifs <;> rfl
  change (∫ ω, ({η | ClusterWindow G x lo hi η}.indicator (1 : Set E → ℝ)) ω ∂law p) = _
  exact integral_indicator_one (measurableSet_clusterWindow G hloc x lo hi)

theorem clusterWindowProbability_nonneg (G : BondGraph V E) (p : unitInterval)
    (x : V) (lo hi : ℕ) : 0 ≤ clusterWindowProbability G p x lo hi := ENNReal.toReal_nonneg

theorem clusterWindowProbability_mono (G : BondGraph V E) (p : unitInterval)
    (x : V) {a b c d : ℕ} (hac : c ≤ a) (hbd : b ≤ d) :
    clusterWindowProbability G p x a b ≤ clusterWindowProbability G p x c d := by
  apply measureReal_mono
  · intro ω h
    exact ⟨h.1,hac.trans h.2.1,h.2.2.trans_le hbd⟩
  · exact measure_ne_top _ _

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem finiteClusterWindowMass_amplification (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (k n : ℕ) (p : unitInterval) (x : V) :
    finiteClusterWindowMass G (q.amplificationBonds k n x) p x (n-k*M) (2*n) =
      clusterWindowProbability G p x (n-k*M) (2*n) := by
  apply finiteClusterWindowMass_eq G hloc
  exact incidentSupport_ball_mono G hloc x (by dsimp [amplificationRadius]; omega)

end LocalEndpointRule
end ClusterWindowLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section QuantitativeAmplificationMoment
attribute [local instance] Classical.propDecidable Classical.decEq


theorem amplificationMomentFactor_pos (k M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    0 < amplificationMomentFactor k M d c a t := by
  unfold amplificationMomentFactor
  positivity

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationLoad_moment_factor [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n d : ℕ) (hn : 0 < n) (hdeg : ∀ x, degree G x ≤ d)
    (a t π : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hπ : 0 ≤ π)
    (hbin : a*n*π ≤ binOrbitRow G p (root i₀) n)
    (hwindow : clusterWindowProbability G p (root i₀) (n-k*M) (2*n) ≤ t*π)
    (hcode : inverseCodeMass M L^k ≤ n*q.successProbability p (root i₀)^k) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p) ≤
      amplificationMomentFactor k M d c a t * q.successProbability p (root i₀)^k *
        (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n) := by
  let u := q.successProbability p (root i₀)
  let B := u^k * binOrbitRow G p (root i₀) n / n
  let D : ℝ := (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ)
  have hu : 0 ≤ u^k := pow_nonneg (q.successProbability_nonneg p _) _
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hB : a*π*u^k ≤ B := by
    apply (le_div_iff₀ hn').mpr
    calc
      _ = u^k*(a*n*π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbin hu
  have hB0 : 0 ≤ B := (mul_nonneg (mul_nonneg ha.le hπ) hu).trans hB
  have hcoef : 4*u^k+D*inverseCodeMass M L^k/n ≤ (4+D)*u^k := by
    have h := mul_le_mul_of_nonneg_left hcode (show 0 ≤ D by positivity)
    have h' : D*inverseCodeMass M L^k/n ≤ D*u^k := by
      apply (div_le_iff₀ hn').mpr
      nlinarith only [h]
    nlinarith only [h']
  have hrem : (2*(c*((k*M:ℕ)*u^k)))^2*(t*π) ≤
      ((2*c*(k*M:ℕ))^2*t/a)*u^k*B := by
    have h := mul_le_mul_of_nonneg_left hB
      (show 0 ≤ ((2*c*(k*M:ℕ))^2*t/a)*u^k from
        mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) ht) ha.le) hu)
    calc
      _ = (((2*c*(k*M:ℕ))^2*t/a)*u^k)*(a*π*u^k) := by
        field_simp
      _ ≤ _ := h
  have hself : root i₀ ∈ vertexOrbit G (root i₀) := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have he := q.amplificationLoad_mean root weight Γ htr
    (fun e he => hΓ he) hw i₀ hw₀ hL p k n (root i₀) hself
  have hm := q.amplificationLoad_second_moment_le hconn root weight Γ hΓ htr hcov hw hw1
    c hc hmin i₀ hw₀ hL p (root i₀) k n d hn hdeg
  rw [he,q.finiteClusterWindowMass_amplification] at hm
  change _ ≤ (4*u^k+D*inverseCodeMass M L^k/n)*B +
    (2*(c*((k*M:ℕ)*u^k)))^2*clusterWindowProbability G p (root i₀) (n-k*M) (2*n) at hm
  calc
    _ ≤ _ := hm
    _ ≤ (4+D)*u^k*B + (2*(c*((k*M:ℕ)*u^k)))^2*(t*π) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hB0)
        (mul_le_mul_of_nonneg_left hwindow (sq_nonneg _))
    _ ≤ (4+D)*u^k*B + ((2*c*(k*M:ℕ))^2*t/a)*u^k*B := add_le_add (le_refl _) hrem
    _ = _ := by dsimp [amplificationMomentFactor,D,B,u]; ring

end LocalEndpointRule
end QuantitativeAmplificationMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section QuantitativeAmplificationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem quantitative_amplification_step [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n d : ℕ) (hn : 0 < n) (hdeg : ∀ x, degree G x ≤ d)
    (hu : 0 < q.successProbability p (root i₀))
    (a t π L' : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hπ : 0 < π)
    (hbin : a*n*π ≤ binOrbitRow G p (root i₀) n)
    (hwindow : clusterWindowProbability G p (root i₀) (n-k*M) (2*n) ≤ t*π)
    (hcode : inverseCodeMass M L^k ≤ n*q.successProbability p (root i₀)^k)
    (hbad : 16*amplificationMomentFactor k M d c a t *
      (law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤ a*π)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) (2*n+k*M) L',
      a*π/(8*amplificationMomentFactor k M d c a t) ≤ q'.successProbability p (root i₀) ∧
      ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧ ‖A'‖ ≤ 2*‖A‖^k ∧
        ∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ) := by
  let Q := amplificationMomentFactor k M d c a t
  let u := q.successProbability p (root i₀)
  let B := u^k*binOrbitRow G p (root i₀) n / n
  let b := 4*Q*u^k
  have hQ : 0 < Q := amplificationMomentFactor_pos k M d c a t ha ht
  have huk : 0 < u^k := pow_pos hu _
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hQ) huk
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hbin0 : 0 < binOrbitRow G p (root i₀) n :=
    (mul_pos (mul_pos ha hn') hπ).trans_le hbin
  have hB : a*π*u^k ≤ B := by
    apply (le_div_iff₀ hn').mpr
    calc
      _ = u^k*(a*n*π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbin huk.le
  have hm := q.amplificationLoad_moment_factor hconn root weight Γ hΓ htr hcov hw hw1
    c hc hmin i₀ hw₀ hL p k n d hn hdeg a t π ha ht hπ.le hbin hwindow hcode
  have hmoment : (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p)/b ≤ B/4 := by
    apply (div_le_iff₀ hb).mpr
    change _ ≤ Q*u^k*B at hm
    calc
      _ ≤ Q*u^k*B := hm
      _ = _ := by dsimp [b]; ring
  have hbad' : b*(law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤ B/4 := by
    have hh := mul_le_mul_of_nonneg_right hbad huk.le
    dsimp [b]
    nlinarith only [hh,hB]
  obtain ⟨q',hq',A',hA'pos,hA'norm,hA'⟩ := q.amplification_truncation_step root weight Γ htr
    (fun e he => hΓ he) hw i₀ hw₀ hL p k n hn hu hbin0 b L' hb hmoment hbad' A hA
  refine ⟨q',?_,A',hA'pos,hA'norm,hA'⟩
  apply le_trans _ hq'
  change a*π/(8*Q) ≤ B/(2*b)
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hQ) (mul_pos (by norm_num) hb)).mpr
  have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ 8*Q by positivity)
  dsimp [b]
  nlinarith only [hh]

end LocalEndpointRule
end QuantitativeAmplificationStep
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionAdjustedKernel
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

theorem integral_cappedConnectionMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (x y : V) :
    (∫ ω, cappedConnectionMass G p S c M L ω x y ∂law p) =
      c*S x y/twoPoint G p x y * (law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} := by
  have hm : MeasurableSet {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} :=
    (measurableSet_capped_good G hloc x M L).inter (measurableSet_conn G x y)
  simpa only [cappedConnectionMass,Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_comm] using
    integral_indicator_const (μ := law p) (c*S x y/twoPoint G p x y) hm

theorem integral_cappedConnectionMass_bounds (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (M : ℕ) (L : ℝ) (x y : V) :
    let K := ∫ ω, cappedConnectionMass G p S c M L ω x y ∂law p
    K ≤ c*S x y ∧ c*S x y ≤ K + S x y * (law p).real {ω | ¬ CappedGoodness G ω x M L} := by
  dsimp only
  rw [integral_cappedConnectionMass G hloc]
  by_cases hs : S x y = 0
  · simp only [hs,mul_zero,zero_div,zero_mul,zero_add,le_refl,and_self]
  have ht : 0 < twoPoint G p x y := hc.trans_le (hτ x y hs)
  let a := c*S x y/twoPoint G p x y
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hc.le (hS x y)) ht.le
  have hle : a ≤ S x y := by
    apply (div_le_iff₀ ht).mpr
    exact (mul_le_mul_of_nonneg_right (hτ x y hs) (hS x y)).trans_eq (mul_comm _ _)
  have he : a*twoPoint G p x y = c*S x y := div_mul_cancel₀ _ ht.ne'
  have hsub : {ω : Set E | CappedGoodness G ω x M L ∧ Conn G ω x y} ⊆ {ω | Conn G ω x y} :=
    fun _ h => h.2
  have hm : (law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} ≤ twoPoint G p x y := by
    exact measureReal_mono hsub (measure_ne_top _ _)
  have hcover : {ω : Set E | Conn G ω x y} ⊆
      {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} ∪ {ω | ¬ CappedGoodness G ω x M L} := by
    intro ω h
    by_cases hg : CappedGoodness G ω x M L
    · exact Or.inl ⟨hg,h⟩
    · exact Or.inr hg
  have hb : twoPoint G p x y ≤
      (law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} +
        (law p).real {ω | ¬ CappedGoodness G ω x M L} :=
    (measureReal_mono hcover (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  constructor
  · exact (mul_le_mul_of_nonneg_left hm ha).trans_eq he
  · calc
      c*S x y = a*twoPoint G p x y := he.symm
      _ ≤ a*((law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} +
          (law p).real {ω | ¬ CappedGoodness G ω x M L}) := mul_le_mul_of_nonneg_left hb ha
      _ ≤ a*(law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} +
          S x y*(law p).real {ω | ¬ CappedGoodness G ω x M L} := by
        rw [mul_add]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hle measureReal_nonneg)

 

theorem connectionAdjustedRule_success_lower
    (G : BondGraph V E) (hloc : LocallyFinite G) (O : Set V) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hSsum : ∀ x, Summable (S x)) (hrow : ∀ x, ∑' y, S x y ≤ 1)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (hO : ∀ x y, S x y ≠ 0 → x ∈ O ∧ y ∈ O)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, S (a x) (a y) = S x y)
    (M : ℕ) (L : ℝ) (x : V) :
    c*(∑' y, S x y) ≤
      (connectionAdjustedRule G hloc O p S c hc hS hSsum hrow hτ hO hcov M L).successProbability p x +
        (law p).real {ω | ¬ CappedGoodness G ω x M L} := by
  let q := connectionAdjustedRule G hloc O p S c hc hS hSsum hrow hτ hO hcov M L
  let ε := (law p).real {ω | ¬ CappedGoodness G ω x M L}
  have h (y : V) : c*S x y ≤ q.kernel p x y + S x y * ε :=
    (integral_cappedConnectionMass_bounds G hloc p S c hc hS hτ M L x y).2
  have hh := ((hSsum x).mul_left c).tsum_le_tsum h
    ((q.summable_kernel p x).add ((hSsum x).mul_right ε))
  rw [(q.summable_kernel p x).tsum_add ((hSsum x).mul_right ε),tsum_mul_left,tsum_mul_right] at hh
  exact hh.trans (add_le_add le_rfl ((mul_le_mul_of_nonneg_right (hrow x) measureReal_nonneg).trans_eq (one_mul ε)))

end ConnectionAdjustedKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionAdjustedOperator
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem connectionAdjustedRule_operator
    (G : BondGraph V E) (hloc : LocallyFinite G) (o : V) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hSsum : ∀ x, Summable (S x)) (hrow : ∀ x, ∑' y, S x y ≤ 1)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (hO : ∀ x y, S x y ≠ 0 → x ∈ vertexOrbit G o ∧ y ∈ vertexOrbit G o)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, S (a x) (a y) = S x y)
    (M : ℕ) (L b : ℝ) (hb : 0 < b) (hret : b ≤ ∑' y, S o y)
    (hbad : (law p).real {ω | ¬ CappedGoodness G ω o M L} ≤ c*b/2)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (S x y : ℂ)) :
    ∃ q : LocalEndpointRule G hloc (vertexOrbit G o) M L,
      c*b/2 ≤ q.successProbability p o ∧
      ∃ T : Hilbert V →L[ℂ] Hilbert V, 0 < ‖T‖ ∧ ‖T‖ ≤ 2*‖A‖/b ∧
        ∀ x y, matrixCoeff T x y = (q.normalizedKernel o p x y : ℂ) := by
  let q := connectionAdjustedRule G hloc (vertexOrbit G o) p S c hc hS hSsum hrow hτ hO hcov M L
  have hlo := connectionAdjustedRule_success_lower G hloc (vertexOrbit G o) p S c hc hS hSsum hrow hτ hO hcov M L o
  have hs : c*b/2 ≤ q.successProbability p o := by
    have hmul := mul_le_mul_of_nonneg_left hret hc.le
    change _ ≤ q.successProbability p o + _ at hlo
    linarith
  have hu : 0 < q.successProbability p o := (by positivity : 0 < c*b/2).trans_le hs
  have hcA (x y : V) : matrixCoeff ((c:ℂ) • A) x y = (c*S x y : ℝ) := by
    change (c:ℂ)*matrixCoeff A x y = _
    rw [hA,Complex.ofReal_mul]
  obtain ⟨B,hBn,hB⟩ := exists_operator_of_matrix_domination
    (fun x y => c*S x y) (q.kernel p) (fun x y => mul_nonneg hc.le (hS x y))
    (fun x y => by
      rw [abs_of_nonneg (q.kernel_nonneg p x y)]
      exact (integral_cappedConnectionMass_bounds G hloc p S c hc hS hτ M L x y).1)
    ((c:ℂ) • A) hcA
  have hBn' : ‖B‖ ≤ c*‖A‖ := by
    simpa only [norm_smul,Complex.norm_of_nonneg hc.le] using hBn
  obtain ⟨T,hTn,hT⟩ := q.normalize_mass_operator o p hu B _ hBn' hB
  refine ⟨q,hs,T,q.normalized_operator_norm_pos o p hu T hT,hTn.trans ?_,hT⟩
  apply (div_le_iff₀ hu).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hb).mpr
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ 2*‖A‖ by positivity)
  nlinarith only [hh]

end ConnectionAdjustedOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Real
open scoped Topology
section CappedGoodnessLimit
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

omit [Countable V] in
theorem clusterLarge_probability_tendsto_zero (G : BondGraph V E) (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    Tendsto (fun M : ℕ => (law p).real (clusterLarge G x M)) atTop (𝓝 0) := by
  have hz : law p {ω | (cluster G ω x).Infinite} = 0 := by
    simpa only [Set.Infinite] using (ae_iff.mp hfin)
  have ht := (ENNReal.tendsto_toReal (measure_ne_top (law p) (⋂ M, clusterLarge G x M))).comp
    (tendsto_measure_iInter_atTop (fun M => (measurableSet_clusterLarge G x M).nullMeasurableSet)
      (clusterLarge_antitone G x) ⟨0,measure_ne_top _ _⟩)
  rw [← infinite_cluster_eq_iInter,hz,ENNReal.toReal_zero] at ht
  exact ht

omit [Countable V] [Countable E] in
theorem cappedGoodness_failure_le (G : BondGraph V E) (p : unitInterval)
    (x : V) (M : ℕ) (L : ℝ) :
    (law p).real {ω | ¬ CappedGoodness G ω x M L} ≤
      (law p).real (clusterLarge G x M) + (law p).real {ω | CappedBadGoodness G ω x M L} := by
  have hsub : {ω : Set E | ¬ CappedGoodness G ω x M L} ⊆
      clusterLarge G x M ∪ {ω | CappedBadGoodness G ω x M L} := by
    intro ω hbad
    by_cases hf : (cluster G ω x).Finite
    · by_cases hM : (cluster G ω x).ncard ≤ M
      · exact Or.inr ⟨hf,hM,fun hg => hbad ⟨hf,hM,hg⟩⟩
      · apply Or.inl
        refine ⟨hf.toFinset,?_,fun y hy => hf.mem_toFinset.mp hy⟩
        rw [← Set.ncard_eq_toFinset_card _ hf]
        omega
    · obtain ⟨t,ht,hcard⟩ := (show (cluster G ω x).Infinite from hf).exists_subset_card_eq M
      exact Or.inl ⟨t,hcard.ge,ht⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)

omit [Countable V] in
 

theorem cappedGoodness_failure_eventually_small [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : (p:ℝ) < 1) (x : V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, (law p).real {ω | ¬ CappedGoodness G ω x M ((M:ℝ)^(1/2+ε))} ≤ δ := by
  have htail := (clusterLarge_probability_tendsto_zero G p x hfin).eventually
    (Iio_mem_nhds (show (0:ℝ) < δ/2 by positivity))
  have hr : Tendsto (fun M : ℕ => (M:ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun M : ℕ => Real.exp (-(M:ℝ)^ε)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hr)
  have he := hexp.eventually (Iio_mem_nhds (show (0:ℝ) < δ/2 by positivity))
  filter_upwards [htail,he,bad_goodness_stretched_exp G hloc hqt p hp ε hε hε1] with M ht he hg
  have hbad := hg x p le_rfl
  have hle := cappedGoodness_failure_le G p x M ((M:ℝ)^(1/2+ε))
  linarith

end CappedGoodnessLimit

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

theorem twoPoint_reachBall_lower [Countable E] (G : BondGraph V E) (p : unitInterval)
    (x : V) (k : ℕ) (y : V) (hy : y ∈ reachBall G x k) :
    (p:ℝ)^k ≤ twoPoint G p x y := by
  induction k generalizing y with
  | zero =>
    simp only [reachBall,Set.mem_singleton_iff] at hy
    subst y
    simp only [pow_zero,twoPoint_self,le_refl]
  | succ k ih =>
    rcases hy with hy | hy
    · have h : (p:ℝ)^(k+1) ≤ (p:ℝ)^k := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg p.2.1 k) p.2.2
      exact h.trans (ih y hy)
    · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy
      obtain ⟨z,hz,hzy⟩ := hy
      have h := mul_le_mul_of_nonneg_left (ih z hz) p.2.1
      rw [←pow_succ'] at h
      exact h.trans (twoPoint_adj_lower G p x z y hzy)

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
open MeasureTheory Filter
open scoped Topology
section StartingEndpointRule
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem starting_endpoint_rule_of_walk (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω (root i₀)).Finite)
    (a : ℝ) (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hsym : IsSelfAdjoint P) (hnorm : ‖P‖ < 1)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (η : ℝ) (hη : 0 < η) (M₀ : ℕ) :
    ∃ M ≥ M₀, ∃ q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M ((M:ℝ)^(1/2+ε)),
      0 < q.successProbability p (root i₀) ∧
      ∃ T : Hilbert V →L[ℂ] Hilbert V, 0 < ‖T‖ ∧ ‖T‖ < η ∧
        ∀ x y, matrixCoeff T x y = (q.normalizedKernel (root i₀) p x y : ℂ) := by
  let O := vertexOrbit G (root i₀)
  have ho : root i₀ ∈ O := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
  let b : ℝ := ∑ i, if root i ∈ O then weight i else 0
  have hb : 0 < b := by
    have hn (i : ι) : 0 ≤ if root i ∈ O then weight i else 0 := by split_ifs; exact hw i; exact le_rfl
    have hh := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ i₀)
    simp only [ite_eq_left ho] at hh
    exact hw₀.trans_le hh
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg P) hnorm
  obtain ⟨k,hk⟩ := (ht.eventually (Iio_mem_nhds (show (0:ℝ) < η*b/2 by positivity))).exists
  have hk1 : ‖P‖^k ≤ 1 := pow_le_one₀ (norm_nonneg P) hnorm.le
  have hk2 : 2*‖P‖^(2*k)/b < η := by
    rw [show 2*k = k+k from Nat.two_mul k,pow_add]
    have hh : ‖P‖^k*‖P‖^k ≤ ‖P‖^k := mul_le_of_le_one_right (pow_nonneg (norm_nonneg P) _) hk1
    apply (div_lt_iff₀ hb).mpr
    change ‖P‖^k < η*b/2 at hk
    nlinarith only [hh,hk]
  let K : V → V → ℝ := fun x y => (matrixCoeff (P^(2*k)) x y).re
  let S : V → V → ℝ := fun x y => if x ∈ O ∧ y ∈ O then K x y else 0
  have hK (x y : V) : 0 ≤ K x y := (hpos.pow (2*k) x y).2
  have hS (x y : V) : 0 ≤ S x y := by dsimp [S]; split_ifs; exact hK x y; exact le_rfl
  have hSK (x y : V) : S x y ≤ K x y := by dsimp [S]; split_ifs; exact le_rfl; exact hK x y
  have hsum (x : V) : HasSum (K x) 1 := walkPower_hasSum G hloc a P hpos hP (2*k) x
  have hSsum (x : V) : Summable (S x) := Summable.of_nonneg_of_le (hS x) (hSK x) (hsum x).summable
  have hrow (x : V) : ∑' y, S x y ≤ 1 := by
    rw [←(hsum x).tsum_eq]
    exact (hSsum x).tsum_le_tsum (hSK x) (hsum x).summable
  have hτ (x y : V) (hxy : S x y ≠ 0) : (p:ℝ)^(2*k) ≤ twoPoint G p x y := by
    apply twoPoint_reachBall_lower G p x (2*k) y
    by_contra hn
    have hz := walkPower_support G hloc a P hpos hP (2*k) x y hn
    apply hxy
    dsimp [S,K]
    rw [hz]
    split_ifs <;> rfl
  have hO (x y : V) (hxy : S x y ≠ 0) : x ∈ O ∧ y ∈ O := by
    by_contra ho
    exact hxy (ite_eq_right ho)
  have hcov (g : V ≃ V) (d : E ≃ E) (hg : IsAut G g d) (x y : V) : S (g x) (g y) = S x y := by
    simp only [S,O,mem_vertexOrbit_aut_iff G (root i₀) hg,K,
      walkPower_invariant G hloc a P hP (2*k) g ⟨d,hg⟩]
  have hret : b ≤ ∑' y, S (root i₀) y := by
    simpa only [b,S,K,ho,true_and,O] using
      walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k
  obtain ⟨A,hAn,hA⟩ := exists_operator_of_matrix_domination K S hK
    (fun x y => by rw [abs_of_nonneg (hS x y)]; exact hSK x y) (P^(2*k)) (hpos.pow (2*k)).real
  have hc : 0 < (p:ℝ)^(2*k) := pow_pos hp _
  have hbad := cappedGoodness_failure_eventually_small G hloc hqt p hp1 (root i₀) hfin ε hε hε1
    ((p:ℝ)^(2*k)*b/2) (by positivity)
  obtain ⟨M,hM,hMb⟩ := ((eventually_ge_atTop M₀).and hbad).exists
  obtain ⟨q,hq,T,hTpos,hTn,hT⟩ := connectionAdjustedRule_operator G hloc (root i₀) p S
    ((p:ℝ)^(2*k)) hc hS hSsum hrow hτ hO hcov M ((M:ℝ)^(1/2+ε)) b hb hret hMb A hA
  refine ⟨M,hM,q,(by positivity : 0 < (p:ℝ)^(2*k)*b/2).trans_le hq,T,hTpos,?_,hT⟩
  apply lt_of_le_of_lt hTn
  apply lt_of_le_of_lt _ hk2
  have hpow (j : ℕ) : ‖P^j‖ ≤ ‖P‖^j := by
    induction j with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ j ih =>
      rw [pow_succ,pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg P))
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hAn.trans (hpow (2*k))) (by norm_num)) hb.le

end StartingEndpointRule
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section NonamenableStartingMap
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem nonamenable_starting_endpoint_rule (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω (root i₀)).Finite)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (η : ℝ) (hη : 0 < η) (M₀ : ℕ) :
    ∃ M ≥ M₀, ∃ q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M ((M:ℝ)^(1/2+ε)),
      0 < q.successProbability p (root i₀) ∧
      ∃ T : Hilbert V →L[ℂ] Hilbert V, 0 < ‖T‖ ∧ ‖T‖ < η ∧
        ∀ x y, matrixCoeff T x y = (q.normalizedKernel (root i₀) p x y : ℂ) := by
  obtain ⟨D,P,hD,hdeg,hPn,hPs,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  have hDr : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have ha : 0 ≤ (1:ℝ)/(2*D) := by positivity
  have haD : (1:ℝ)/(2*D)*D ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hpos : PositiveRealMatrix P := by
    intro x y
    change (P (lp.single 2 y (1:ℂ)) x).im = 0 ∧ 0 ≤ (P (lp.single 2 y (1:ℂ)) x).re
    rw [hP]
    exact ⟨Complex.ofReal_im _,walkKernel_nonneg G hloc D hdeg _ ha haD x y⟩
  exact starting_endpoint_rule_of_walk G hloc hqt p hp hp1 root weight Γ hΓ htr hw hw1 i₀ hw₀ hfin
    _ P hpos hPs.isSelfAdjoint hPn hP ε hε hε1 η hη M₀

end NonamenableStartingMap
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteOrbitPartition
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_partition_square_bound {α ι : Type*} [Fintype ι]
    (C : Finset α) (color : α → ι) (q : α → ℝ)
    (hq : ∀ x ∈ C, (∑ y ∈ C, if color y = color x then (1:ℝ) else 0) ≤ q x) :
    (C.card:ℝ)^2 ≤ Fintype.card ι * ∑ x ∈ C, q x := by
  let c : ι → ℝ := fun i => ∑ x ∈ C, if color x=i then 1 else 0
  have hsum : (∑ i, c i) = C.card := by
    dsimp only [c]
    rw [Finset.sum_comm]
    simp
  have hsq : (∑ i, c i^2) = ∑ x ∈ C, c (color x) := by
    have he (i : ι) : c i^2 = ∑ x ∈ C, if color x=i then c i else 0 := by
      rw [pow_two]
      conv_lhs => lhs; change ∑ x ∈ C, if color x=i then (1:ℝ) else 0
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp only [one_mul,zero_mul]
    simp only [he]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    simp
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1:ℝ)) c
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hsum,hsq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hq) (Nat.cast_nonneg _))

theorem vertexOrbit_eq_of_mem (G : BondGraph V E) (o x : V) (hx : x ∈ vertexOrbit G o) :
    vertexOrbit G x = vertexOrbit G o := by
  obtain ⟨a,b,hab,rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.trans c,b.trans d,isAut_trans G hab hcd,hc⟩
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.symm.trans c,b.symm.trans d,isAut_trans G (isAut_symm G hab) hcd,by simpa using hc⟩

 

theorem finite_sameOrbit_pairs_lower (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (C : Finset V) :
    (C.card:ℝ)^2 ≤ Fintype.card ι *
      ∑ x ∈ C, ∑ y ∈ C, if y ∈ vertexOrbit G x then (1:ℝ) else 0 := by
  let color : V → ι := fun x => (hcover x).choose
  have hc (x : V) : x ∈ vertexOrbit G (root (color x)) := (hcover x).choose_spec
  apply finite_partition_square_bound C color
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  by_cases h : color y = color x
  · have hm : y ∈ vertexOrbit G x := by
      rw [vertexOrbit_eq_of_mem G (root (color x)) x (hc x)]
      simpa only [h] using hc y
    simp only [ite_eq_left h,ite_eq_left hm,le_refl]
  · simp only [ite_eq_right h]
    split_ifs <;> norm_num

end FiniteOrbitPartition
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinOrbitRowMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binMass_eq_of_window (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hb : ClusterWindow G x n (2*n) ω) :
    binConnectionMass G n ω x y = if y ∈ cluster G ω x then 1 else 0 := by
  simp only [binConnectionMass,hb.1,hb.2.1,hb.2.2,true_and]
  rfl

theorem binMass_zero_of_not_window (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hb : ¬ ClusterWindow G x n (2*n) ω) : binConnectionMass G n ω x y = 0 := by
  apply ite_eq_right
  exact fun h => hb ⟨h.1,h.2.1,h.2.2.1⟩

theorem binSizeMass_eq (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V)
    (hb : ClusterWindow G x n (2*n) ω) : binSizeMass G n ω x = (cluster G ω x).ncard := by
  unfold binSizeMass
  simp only [binMass_eq_of_window G n ω x _ hb]
  rw [tsum_eq_sum (s := hb.1.toFinset) (fun y hy => by simp only [Set.Finite.mem_toFinset] at hy; simp only [ite_eq_right hy])]
  have he : (∑ y ∈ hb.1.toFinset, if y ∈ cluster G ω x then (1:ℝ) else 0) = ∑ _y ∈ hb.1.toFinset, (1:ℝ) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact ite_eq_left (hb.1.mem_toFinset.mp hy)
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hb.1]

theorem binOrbitRowMass_eq (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V)
    (hb : ClusterWindow G x n (2*n) ω) :
    binOrbitRowMass G n ω x = ∑ y ∈ hb.1.toFinset, if y ∈ vertexOrbit G x then (1:ℝ) else 0 := by
  unfold binOrbitRowMass
  rw [tsum_eq_sum (s := hb.1.toFinset) (fun y hy => by
    have hc : y ∉ cluster G ω x := fun h => hy (hb.1.mem_toFinset.mpr h)
    rw [binMass_eq_of_window G n ω x y hb,ite_eq_right hc,ite_self])]
  apply Finset.sum_congr rfl
  intro y hy
  rw [binMass_eq_of_window G n ω x y hb,ite_eq_left (hb.1.mem_toFinset.mp hy)]

theorem binOrbitRowMass_nonneg (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) :
    0 ≤ binOrbitRowMass G n ω x := by
  apply tsum_nonneg
  intro y
  split_ifs
  · exact binConnectionMass_nonneg G n ω x y
  · exact le_rfl

theorem binOrbitRowMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binOrbitRowMass G n ω x = binOrbitRowMass G n (ω ∩ (Q : Set E)) x := by
  dsimp only [binOrbitRowMass]
  apply tsum_congr
  intro y
  rw [binConnectionMass_local G hloc n ω x y]

theorem binSizeMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binSizeMass G n ω x = binSizeMass G n (ω ∩ (Q : Set E)) x := by
  dsimp only [binSizeMass]
  apply tsum_congr
  intro y
  exact binConnectionMass_local G hloc n ω x y

theorem binOrbitRowMass_covariant (G : BondGraph V E) (n : ℕ) (ω : Set E)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    binOrbitRowMass G n (b ⁻¹' ω) x = binOrbitRowMass G n ω (a x) := by
  unfold binOrbitRowMass
  rw [←a.tsum_eq (fun y => if y ∈ vertexOrbit G (a x) then binConnectionMass G n ω (a x) y else 0)]
  have ho : vertexOrbit G (a x) = vertexOrbit G x := vertexOrbit_eq_of_mem G x (a x) ⟨a,b,hab,rfl⟩
  simp only [ho,mem_vertexOrbit_aut_iff G x hab,binConnectionMass_covariant G hab]

theorem binSizeMass_covariant (G : BondGraph V E) (n : ℕ) (ω : Set E)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    binSizeMass G n (b ⁻¹' ω) x = binSizeMass G n ω (a x) := by
  unfold binSizeMass
  rw [←a.tsum_eq (fun y => binConnectionMass G n ω (a x) y)]
  simp only [binConnectionMass_covariant G hab]

end BinOrbitRowMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinOrbitTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binOrbitRowMass_zero (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V)
    (hb : ¬ ClusterWindow G x n (2*n) ω) : binOrbitRowMass G n ω x = 0 := by
  simp only [binOrbitRowMass,binMass_zero_of_not_window G n ω x _ hb,ite_self,tsum_zero]

theorem binOrbitTransportMass_nonneg (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) :
    0 ≤ binOrbitTransportMass G n ω x y := by
  exact div_nonneg (mul_nonneg (binConnectionMass_nonneg G n ω x y) (binOrbitRowMass_nonneg G n ω y))
    (tsum_nonneg (binConnectionMass_nonneg G n ω x))

theorem binOrbitTransportMass_column (G : BondGraph V E) (n : ℕ) (hn : 0 < n)
    (ω : Set E) (y : V) : (∑' x, binOrbitTransportMass G n ω x y) = binOrbitRowMass G n ω y := by
  by_cases hb : ClusterWindow G y n (2*n) ω
  · have he (x : V) : binOrbitTransportMass G n ω x y =
        binConnectionMass G n ω x y * (binOrbitRowMass G n ω y / binSizeMass G n ω y) := by
      by_cases hz : binConnectionMass G n ω x y = 0
      · simp only [binOrbitTransportMass,hz,zero_mul,zero_div]
      · obtain ⟨hf,hN,hc⟩ := binConnectionMass_support G n ω x y hz
        have hset := cluster_eq_of_conn G ω hc
        have hbx : ClusterWindow G x n (2*n) ω := by
          unfold ClusterWindow at hb ⊢
          simpa only [hset] using hb
        rw [binOrbitTransportMass,binSizeMass_eq G n ω x hbx,binSizeMass_eq G n ω y hb,hset]
        exact mul_div_assoc _ _ _
    rw [show (∑' x, binOrbitTransportMass G n ω x y) =
      ∑' x, binConnectionMass G n ω x y*(binOrbitRowMass G n ω y/binSizeMass G n ω y) from tsum_congr he,
      tsum_mul_right]
    have hcol : (∑' x, binConnectionMass G n ω x y) = binSizeMass G n ω y := by
      simp only [binConnectionMass_symm G n ω,binSizeMass]
    rw [hcol]
    have hs : binSizeMass G n ω y ≠ 0 := by
      rw [binSizeMass_eq G n ω y hb]
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hn.trans_le hb.2.1))
    exact mul_div_cancel₀ _ hs
  · have he : ∀ x, binOrbitTransportMass G n ω x y = 0 := by
      intro x
      simp only [binOrbitTransportMass,binOrbitRowMass_zero G n ω y hb,mul_zero,zero_div]
    simp only [he,tsum_zero,binOrbitRowMass_zero G n ω y hb]

theorem binOrbitTransportMass_row (G : BondGraph V E)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (n : ℕ) (hn : 0 < n) (ω : Set E) (x : V) :
    (if ClusterWindow G x n (2*n) ω then (n:ℝ)/Fintype.card ι else 0) ≤
      ∑' y, binOrbitTransportMass G n ω x y := by
  by_cases hb : ClusterWindow G x n (2*n) ω
  · rw [ite_eq_left hb]
    let C := hb.1.toFinset
    have hs : (0:ℝ) < (cluster G ω x).ncard := Nat.cast_pos.mpr (hn.trans_le hb.2.1)
    have ht : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    have hqy (y : V) (hy : y ∈ C) : binOrbitRowMass G n ω y =
        ∑ z ∈ C, if z ∈ vertexOrbit G y then (1:ℝ) else 0 := by
      have hc : Conn G ω x y := hb.1.mem_toFinset.mp hy
      have he := cluster_eq_of_conn G ω hc
      have hby : ClusterWindow G y n (2*n) ω := by
        unfold ClusterWindow at hb ⊢
        simpa only [←he] using hb
      rw [binOrbitRowMass_eq G n ω y hby]
      have hC : hby.1.toFinset = C := by
        apply Finset.coe_injective
        simpa only [C,Set.Finite.coe_toFinset] using he.symm
      rw [hC]
    have he : (∑' y, binOrbitTransportMass G n ω x y) =
        (∑ y ∈ C, ∑ z ∈ C, if z ∈ vertexOrbit G y then (1:ℝ) else 0)/(cluster G ω x).ncard := by
      rw [tsum_eq_sum (s := C) (fun y hy => by
        have hc : y ∉ cluster G ω x := fun h => hy (hb.1.mem_toFinset.mpr h)
        simp only [binOrbitTransportMass,binMass_eq_of_window G n ω x y hb,ite_eq_right hc,zero_mul,zero_div])]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [binOrbitTransportMass,binMass_eq_of_window G n ω x y hb,
        ite_eq_left (hb.1.mem_toFinset.mp hy),one_mul,binSizeMass_eq G n ω x hb,hqy y hy]
    rw [he]
    apply (div_le_div_iff₀ ht hs).mpr
    have h := finite_sameOrbit_pairs_lower G root hcover C
    have hC : (C.card:ℝ) = (cluster G ω x).ncard := by
      exact_mod_cast (Set.ncard_eq_toFinset_card _ hb.1).symm
    rw [hC] at h
    have hn' : (n:ℝ) ≤ (cluster G ω x).ncard := by exact_mod_cast hb.2.1
    nlinarith [mul_le_mul_of_nonneg_right hn' hs.le]
  · rw [ite_eq_right hb]
    exact tsum_nonneg (binOrbitTransportMass_nonneg G n ω x)

end BinOrbitTransport

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
section AveragedBinOrbitTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integral_tsum_of_finite_support {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset α) (f : Ω → α → ℝ)
    (hi : ∀ x, Integrable (fun ω => f ω x) μ)
    (hs : ∀ ω x, x ∉ S → f ω x = 0) :
    (∫ ω, ∑' x, f ω x ∂μ) = ∑' x, ∫ ω, f ω x ∂μ := by
  have he (ω) : (∑' x, f ω x) = ∑ x ∈ S, f ω x := tsum_eq_sum (hs ω)
  rw [show (∫ ω, ∑' x, f ω x ∂μ) = ∫ ω, ∑ x ∈ S, f ω x ∂μ by simp only [he],
    integral_finsetSum _ (fun x _ => hi x),tsum_eq_sum (s := S) (fun x hx => by simp only [hs _ x hx,integral_zero])]

theorem binOrbitTransportMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x y : V) :
    let Qx := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    let Qy := incidentSupport G hloc (finite_reachBall hloc y (2*n)).toFinset
    binOrbitTransportMass G n ω x y = binOrbitTransportMass G n (ω ∩ ((Qx∪Qy : Finset E) : Set E)) x y := by
  let Qx := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
  let Qy := incidentSupport G hloc (finite_reachBall hloc y (2*n)).toFinset
  have hB := finite_local_of_subset Qx (Qx∪Qy) Finset.subset_union_left
    (fun ω => binConnectionMass G n ω x y) (fun ω => binConnectionMass_local G hloc n ω x y) ω
  have hq := finite_local_of_subset Qy (Qx∪Qy) Finset.subset_union_right
    (fun ω => binOrbitRowMass G n ω y) (fun ω => binOrbitRowMass_local G hloc n ω y) ω
  have hs := finite_local_of_subset Qx (Qx∪Qy) Finset.subset_union_left
    (fun ω => binSizeMass G n ω x) (fun ω => binSizeMass_local G hloc n ω x) ω
  exact congrArg₂ (· / ·) (congrArg₂ (· * ·) hB hq) hs

theorem binOrbitTransportMass_integrable (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (x y : V) : Integrable (fun ω => binOrbitTransportMass G n ω x y) (law p) :=
  integrable_finite_local _ p _ (fun ω => binOrbitTransportMass_local G hloc n ω x y)

theorem binOrbitTransportMass_outside (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binOrbitTransportMass G n ω x y = 0 := by
  simp only [binOrbitTransportMass,binConnectionMass_outside G n ω x y hy,zero_mul,zero_div]

theorem binOrbitTransport_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (n : ℕ) (x y : V) :
    binOrbitTransport G p n (a x) (a y) = binOrbitTransport G p n x y := by
  have hm : Measurable (fun ω => binOrbitTransportMass G n ω x y) :=
    measurable_finite_local _ _ (fun ω => binOrbitTransportMass_local G hloc n ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [binOrbitTransport,binOrbitTransportMass,binConnectionMass_covariant G hab,
    binOrbitRowMass_covariant G n _ hab,binSizeMass_covariant G n _ hab] using h.symm

theorem binOrbitTransport_outside (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binOrbitTransport G p n x y = 0 := by
  simp only [binOrbitTransport,binOrbitTransportMass_outside G n _ x y hy,integral_zero]

theorem binOrbitTransportMass_outside_column (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hx : x ∉ reachBall G y (2*n)) : binOrbitTransportMass G n ω x y = 0 := by
  have hB : binConnectionMass G n ω x y = 0 := by
    rw [binConnectionMass_symm]
    exact binConnectionMass_outside G n ω y x hx
  simp only [binOrbitTransportMass,hB,zero_mul,zero_div]

theorem binOrbitTransport_row_integral (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (x : V) :
    (∑' y, binOrbitTransport G p n x y) = ∫ ω, ∑' y, binOrbitTransportMass G n ω x y ∂law p := by
  symm
  apply integral_tsum_of_finite_support (law p) (finite_reachBall hloc x (2*n)).toFinset _
    (binOrbitTransportMass_integrable G hloc p n x)
  intro ω y hy
  exact binOrbitTransportMass_outside G n ω x y (by simpa only [Set.Finite.mem_toFinset] using hy)

theorem integral_binOrbitRowMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (x : V) :
    (∫ ω, binOrbitRowMass G n ω x ∂law p) = binOrbitRow G p x n := by
  have hx : x ∈ vertexOrbit G x := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
  unfold binOrbitRowMass
  rw [integral_tsum_of_finite_support (law p) (finite_reachBall hloc x (2*n)).toFinset _
    (fun y => by
      by_cases hy : y ∈ vertexOrbit G x
      · simp only [ite_eq_left hy]
        exact integrable_finite_local _ p _ (fun ω => binConnectionMass_local G hloc n ω x y)
      · simp only [ite_eq_right hy]; exact integrable_const (0:ℝ))
    (fun ω y hy => by
      have hz := binConnectionMass_outside G n ω x y (by simpa only [Set.Finite.mem_toFinset] using hy)
      simp only [hz,ite_self])]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ vertexOrbit G x
  · simp only [orbitBinConnection,hx,hy,true_and,if_true,binConnection]
  · simp only [orbitBinConnection,hy,and_false,if_false,integral_zero]

theorem binOrbitTransport_column (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (hn : 0 < n) (y : V) :
    (∑' x, binOrbitTransport G p n x y) = binOrbitRow G p y n := by
  rw [←integral_binOrbitRowMass G hloc p n y,←show (∫ ω, ∑' x, binOrbitTransportMass G n ω x y ∂law p) =
    ∑' x, binOrbitTransport G p n x y from
      integral_tsum_of_finite_support (law p) (finite_reachBall hloc y (2*n)).toFinset _
        (fun x => binOrbitTransportMass_integrable G hloc p n x y)
        (fun ω x hx => binOrbitTransportMass_outside_column G n ω x y (by simpa only [Set.Finite.mem_toFinset] using hx))]
  simp only [binOrbitTransportMass_column G n hn]

end AveragedBinOrbitTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedOrbitBinLower
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binOrbitTransport_row_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p : unitInterval) (n : ℕ) (hn : 0 < n) (x : V) :
    (n:ℝ)/Fintype.card ι * clusterWindowProbability G p x n (2*n) ≤
      ∑' y, binOrbitTransport G p n x y := by
  let B := (finite_reachBall hloc x (2*n)).toFinset
  have he (ω) : (∑' y, binOrbitTransportMass G n ω x y) =
      ∑ y ∈ B, binOrbitTransportMass G n ω x y := by
    apply tsum_eq_sum
    intro y hy
    exact binOrbitTransportMass_outside G n ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  have hi : Integrable (fun ω => ∑' y, binOrbitTransportMass G n ω x y) (law p) := by
    simp only [he]
    exact integrable_finsetSum B (fun y _ => binOrbitTransportMass_integrable G hloc p n x y)
  let W := {ω | ClusterWindow G x n (2*n) ω}
  have hm : MeasurableSet W := measurableSet_clusterWindow G hloc x n (2*n)
  have hl : Integrable (W.indicator (fun _ => (n:ℝ)/Fintype.card ι)) (law p) :=
    (integrable_const _).indicator hm
  calc
    _ = ∫ ω, W.indicator (fun _ => (n:ℝ)/Fintype.card ι) ω ∂law p := by
      rw [integral_indicator_const _ hm]
      simp only [smul_eq_mul,clusterWindowProbability,W,mul_comm]
    _ ≤ ∫ ω, ∑' y, binOrbitTransportMass G n ω x y ∂law p := by
      apply integral_mono hl hi
      intro ω
      exact binOrbitTransportMass_row G root hcover n hn ω x
    _ = _ := (binOrbitTransport_row_integral G hloc p n x).symm

 

theorem weighted_binOrbitRow_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p : unitInterval) (n : ℕ) (hn : 0 < n) :
    (n:ℝ)/Fintype.card ι * (∑ i, weight i * clusterWindowProbability G p (root i) n (2*n)) ≤
      ∑ i, weight i * binOrbitRow G p (root i) n := by
  have hr (x : V) : Summable (binOrbitTransport G p n x) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x (2*n)).toFinset)
    intro y hy
    exact binOrbitTransport_outside G p n x y (by simpa only [Set.Finite.mem_toFinset] using hy)
  have hc (y : V) : Summable (fun x => binOrbitTransport G p n x y) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y (2*n)).toFinset)
    intro x hx
    have hz (ω) := binOrbitTransportMass_outside_column G n ω x y (by simpa only [Set.Finite.mem_toFinset] using hx)
    simp only [binOrbitTransport,hz,integral_zero]
  have ht := htr.real root weight Γ (binOrbitTransport G p n)
    (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; exact binOrbitTransport_covariant G hloc p hab n x y) hr hc
  calc
    _ = ∑ i, weight i * ((n:ℝ)/Fintype.card ι * clusterWindowProbability G p (root i) n (2*n)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, weight i * ∑' y, binOrbitTransport G p n (root i) y :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (binOrbitTransport_row_lower G hloc root hcover p n hn (root i)) (hw i))
    _ = ∑ i, weight i * ∑' x, binOrbitTransport G p n x (root i) := ht
    _ = _ := by simp only [binOrbitTransport_column G hloc p n hn]

theorem exists_binOrbitRow_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p : unitInterval) (n : ℕ) (hn : 0 < n) :
    ∃ i, (n:ℝ)/Fintype.card ι * (∑ j, weight j * clusterWindowProbability G p (root j) n (2*n)) ≤
      binOrbitRow G p (root i) n := by
  have h := weighted_binOrbitRow_lower G hloc root weight Γ hΓ htr (fun i => (hw i).le) hcover p n hn
  by_contra! he
  let c := (n:ℝ)/Fintype.card ι * (∑ j, weight j * clusterWindowProbability G p (root j) n (2*n))
  have hs : (∑ i, weight i * binOrbitRow G p (root i) n) < ∑ i, weight i*c := by
    apply Finset.sum_lt_sum (fun i _ => (mul_lt_mul_of_pos_left (he i) (hw i)).le)
    exact ⟨Classical.arbitrary ι,Finset.mem_univ _,mul_lt_mul_of_pos_left (he _) (hw _)⟩
  rw [←Finset.sum_mul,hw1,one_mul] at hs
  exact (not_lt_of_ge h) hs

end WeightedOrbitBinLower

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DyadicRecords
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem summable_dyadic_of_scaled_bound (π : ℕ → ℝ) (hπ : ∀ j, 0 ≤ π j)
    (α β C : ℝ) (hαβ : α < β)
    (hC : ∀ j : ℕ, (2:ℝ)^(β*(j:ℝ))*π j ≤ C) :
    Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*π j) := by
  let r := (2:ℝ)^(α-β)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hαβ)
  have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left C
  apply hs.of_nonneg_of_le (fun j => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hπ j))
  intro j
  have he : (2:ℝ)^(α*(j:ℝ)) = r^j * (2:ℝ)^(β*(j:ℝ)) := by
    rw [show r^j = (2:ℝ)^((α-β)*(j:ℝ)) by rw [Real.rpow_mul (by norm_num),Real.rpow_natCast],
      ←Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [he,mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hC j) (pow_nonneg hr0 j)).trans_eq (mul_comm _ _)

theorem unbounded_scaled_dyadic (π : ℕ → ℝ) (hπ : ∀ j, 0 ≤ π j)
    (α β : ℝ) (hαβ : α < β)
    (hdiv : ¬ Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*π j)) :
    ∀ C : ℝ, ∃ j : ℕ, C < (2:ℝ)^(β*(j:ℝ))*π j := by
  intro C
  by_contra! hC
  exact hdiv (summable_dyadic_of_scaled_bound π hπ α β C hαβ hC)

 
theorem late_record_of_unbounded (f : ℕ → ℝ) (hf : ∀ C : ℝ, ∃ j, C < f j) (N : ℕ) :
    ∃ j, N < j ∧ 1 ≤ f j ∧ ∀ i ≤ j, f i ≤ f j := by
  obtain ⟨a,ha,hamax⟩ := (Finset.range (N+1)).exists_max_image f ⟨0,by simp⟩
  obtain ⟨b,hb⟩ := hf (max 1 (f a))
  obtain ⟨j,hj,hjmax⟩ := (Finset.range (b+1)).exists_max_image f ⟨0,by simp⟩
  have hb' : max 1 (f a) < f j := hb.trans_le (hjmax b (by simp))
  refine ⟨j,?_,(le_max_left _ _).trans hb'.le,?_⟩
  · by_contra! hjN
    have he := hamax j (Finset.mem_range.mpr (by omega))
    exact (not_lt_of_ge he) ((le_max_right _ _).trans_lt hb')
  · intro i hi
    exact hjmax i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))

 

theorem finite_family_unbounded_choice {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop) (h : ∀ N, ∃ j, N ≤ j ∧ ∃ i, P i j) :
    ∃ i, ∀ N, ∃ j, N ≤ j ∧ P i j := by
  by_contra! hnot
  choose L hL using hnot
  obtain ⟨j,hj,i,hi⟩ := h (∑ i, L i)
  have hLi : L i ≤ ∑ t, L t := Finset.single_le_sum (fun t _ => Nat.zero_le (L t)) (Finset.mem_univ i)
  exact hL i j (hLi.trans hj) hi

theorem record_dyadic_bounds (π : ℕ → ℝ) (β : ℝ) (j : ℕ)
    (hrec : ∀ i ≤ j+1, (2:ℝ)^(β*(i:ℝ))*π i ≤ (2:ℝ)^(β*((j+1:ℕ):ℝ))*π (j+1))
    (h1 : 1 ≤ (2:ℝ)^(β*((j+1:ℕ):ℝ))*π (j+1)) :
    (2:ℝ)^(-β*((j+1:ℕ):ℝ)) ≤ π (j+1) ∧ π j ≤ (2:ℝ)^β*π (j+1) := by
  have hpos : 0 < (2:ℝ)^(β*((j+1:ℕ):ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (2:ℝ)^(-β*((j+1:ℕ):ℝ)) = 1/(2:ℝ)^(β*((j+1:ℕ):ℝ)) := by
    rw [show -β*((j+1:ℕ):ℝ) = -(β*((j+1:ℕ):ℝ)) by ring,Real.rpow_neg (by norm_num)]
    simp only [one_div]
  refine ⟨?_,?_⟩
  · rw [hinv]
    exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using h1)
  · have hr := hrec j (by omega)
    have he : (2:ℝ)^(β*((j+1:ℕ):ℝ)) = (2:ℝ)^(β*(j:ℝ))*(2:ℝ)^β := by
      rw [Nat.cast_add,Nat.cast_one,mul_add,mul_one,Real.rpow_add (by norm_num)]
    rw [he,mul_assoc] at hr
    exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _)).mp hr

end DyadicRecords

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitDyadicScales
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterWindowProbability_split (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    clusterWindowProbability G p x a c = clusterWindowProbability G p x a b + clusterWindowProbability G p x b c := by
  have he : {ω | ClusterWindow G x a c ω} =
      {ω | ClusterWindow G x a b ω} ∪ {ω | ClusterWindow G x b c ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_union,ClusterWindow]
    constructor
    · rintro ⟨hf,ha,hc⟩
      by_cases hb : (cluster G ω x).ncard < b
      · exact Or.inl ⟨hf,ha,hb⟩
      · exact Or.inr ⟨hf,by omega,hc⟩
    · rintro (⟨hf,ha,hb⟩|⟨hf,hb,hc⟩)
      · exact ⟨hf,ha,hb.trans_le hbc⟩
      · exact ⟨hf,hab.trans hb,hc⟩
  have hd : Disjoint {ω | ClusterWindow G x a b ω} {ω | ClusterWindow G x b c ω} := by
    apply Set.disjoint_left.mpr
    intro ω h₁ h₂
    exact (not_lt_of_ge h₂.2.1) h₁.2.2
  unfold clusterWindowProbability
  rw [he,measureReal_union hd (measurableSet_clusterWindow G hloc x b c)]

theorem weightedWindowProbability_nonneg {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (a b : ℕ) :
    0 ≤ weightedWindowProbability G p root weight a b := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (clusterWindowProbability_nonneg G p (root i) a b))

theorem weightedWindowProbability_split {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    weightedWindowProbability G p root weight a c =
      weightedWindowProbability G p root weight a b + weightedWindowProbability G p root weight b c := by
  simp only [weightedWindowProbability,clusterWindowProbability_split G hloc p _ a b c hab hbc,
    mul_add,Finset.sum_add_distrib]



theorem orbit_dyadic_scales (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (p : unitInterval)
    (α β : ℝ) (hαβ : α < β)
    (hdiv : ¬ Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*dyadicBinProbability G p root weight j)) :
    ∃ i, ∀ N, ∃ j, N ≤ j ∧
      ((2^(j+1):ℕ):ℝ)^(-β) ≤ dyadicBinProbability G p root weight (j+1) ∧
      weightedWindowProbability G p root weight (2^j) (2^(j+2)) ≤
        (1+(2:ℝ)^β)*dyadicBinProbability G p root weight (j+1) ∧
      (((2^(j+1):ℕ):ℝ)/Fintype.card ι)*dyadicBinProbability G p root weight (j+1) ≤
        binOrbitRow G p (root i) (2^(j+1)) := by
  let π := dyadicBinProbability G p root weight
  let f := fun j : ℕ => (2:ℝ)^(β*(j:ℝ))*π j
  have hπ : ∀ j, 0 ≤ π j := fun j => weightedWindowProbability_nonneg G p root weight (fun i => (hw i).le) _ _
  have hf := unbounded_scaled_dyadic π hπ α β hαβ hdiv
  let P := fun i j => 1 ≤ f (j+1) ∧ (∀ t ≤ j+1, f t ≤ f (j+1)) ∧
    (((2^(j+1):ℕ):ℝ)/Fintype.card ι)*π (j+1) ≤ binOrbitRow G p (root i) (2^(j+1))
  have hpick : ∀ N, ∃ j, N ≤ j ∧ ∃ i, P i j := by
    intro N
    obtain ⟨t,ht,h1,hr⟩ := late_record_of_unbounded f hf N
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    obtain ⟨i,hi⟩ := exists_binOrbitRow_lower G hloc root weight Γ hΓ htr hw hw1 hcover p (2^(j+1)) (by positivity)
    have he : 2*2^(j+1) = 2^(j+2) := by rw [show j+2 = (j+1)+1 by omega,pow_succ]; omega
    refine ⟨j,by omega,i,h1,hr,?_⟩
    simpa only [P,π,dyadicBinProbability,weightedWindowProbability,he] using hi
  obtain ⟨i,hi⟩ := finite_family_unbounded_choice P hpick
  refine ⟨i,?_⟩
  intro N
  obtain ⟨j,hj,h1,hr,hb⟩ := hi N
  have hs := record_dyadic_bounds π β j hr h1
  refine ⟨j,hj,?_,?_,hb⟩
  · have he : (((2^(j+1):ℕ):ℝ)^(-β)) = (2:ℝ)^(-β*((j+1:ℕ):ℝ)) := by
      rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [he]
    exact hs.1
  · rw [weightedWindowProbability_split G hloc p root weight (2^j) (2^(j+1)) (2^(j+2))
      (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))]
    change π j + π (j+1) ≤ (1+(2:ℝ)^β)*π (j+1)
    nlinarith only [hs.2]

end OrbitDyadicScales

end Percolation

 
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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedMomentScales
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_cluster_power_of_weighted_dyadic (G : BondGraph V E)
    (hloc : LocallyFinite G) {ι : Type*} [Fintype ι] (p : unitInterval)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 < weight i)
    (α : ℝ) (hα : 0 < α)
    (hs : Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*dyadicBinProbability G p root weight j))
    (i : ι) : Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p) := by
  have hle (j : ℕ) : weight i * clusterWindowProbability G p (root i) (2^j) (2^(j+1)) ≤
      dyadicBinProbability G p root weight j := by
    exact Finset.single_le_sum
      (fun t _ => mul_nonneg (hw t).le (clusterWindowProbability_nonneg G p (root t) _ _))
      (Finset.mem_univ i)
  have hs' : Summable (fun j : ℕ => weight i *
      ((2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p (root i) (2^j) (2^(j+1)))) := by
    apply hs.of_nonneg_of_le
    · intro j
      exact mul_nonneg (hw i).le (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (clusterWindowProbability_nonneg G p (root i) _ _))
    · intro j
      have h := mul_le_mul_of_nonneg_left (hle j) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (α*(j:ℝ)))
      nlinarith only [h]
  apply integrable_cluster_power_of_dyadic G hloc p (root i) α hα
  have he : (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p (root i) (2^j) (2^(j+1))) =
      (fun j : ℕ => (weight i)⁻¹ * (weight i *((2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p (root i) (2^j) (2^(j+1))))) := by
    funext j
    rw [←mul_assoc,inv_mul_cancel₀ (hw i).ne',one_mul]
  rw [he]
  exact hs'.mul_left _

 

theorem orbit_scales_of_divergent_moment (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (p : unitInterval)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p)) :
    ∃ i, ∀ N, ∃ j, N ≤ j ∧
      ((2^(j+1):ℕ):ℝ)^(-β) ≤ dyadicBinProbability G p root weight (j+1) ∧
      weightedWindowProbability G p root weight (2^j) (2^(j+2)) ≤
        (1+(2:ℝ)^β)*dyadicBinProbability G p root weight (j+1) ∧
      (((2^(j+1):ℕ):ℝ)/Fintype.card ι)*dyadicBinProbability G p root weight (j+1) ≤
        binOrbitRow G p (root i) (2^(j+1)) := by
  apply orbit_dyadic_scales G hloc root weight Γ hΓ htr hw hw1 hcover p α β hαβ
  intro hs
  obtain ⟨i,hi⟩ := hdiv
  exact hi (integrable_cluster_power_of_weighted_dyadic G hloc p root weight hw α hα hs i)

end WeightedMomentScales
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section LogarithmicChainLength

theorem logarithmicChainLength_bounds (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 1 ≤ n) :
    (logarithmicChainLength t n:ℝ)*t ≤ Real.log n ∧
      Real.log n < ((logarithmicChainLength t n:ℝ)+1)*t := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn'
  constructor
  · exact (le_div_iff₀ ht).mp (Nat.floor_le (div_nonneg hlog ht.le))
  · exact (div_lt_iff₀ ht).mp (Nat.lt_floor_add_one (Real.log n/t))

theorem tendsto_logarithmicChainLength (t : ℝ) (ht : 0 < t) :
    Tendsto (logarithmicChainLength t) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const ht)

theorem tendsto_log_div_chainLength (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => Real.log n / logarithmicChainLength t n) atTop (nhds t) := by
  have hk : Tendsto (fun n : ℕ => (logarithmicChainLength t n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_logarithmicChainLength t ht)
  have hlim : Tendsto (fun n : ℕ => t + t/(logarithmicChainLength t n:ℝ)) atTop (nhds t) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hk)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_ge_atTop (1:ℕ),hk.eventually_gt_atTop 0] with n hn hk0
    exact (le_div_iff₀ hk0).mpr (by simpa only [mul_comm] using (logarithmicChainLength_bounds t ht n hn).1)
  · filter_upwards [eventually_ge_atTop (1:ℕ),hk.eventually_gt_atTop 0] with n hn hk0
    have h := (logarithmicChainLength_bounds t ht n hn).2.le
    apply (div_le_iff₀ hk0).mpr
    calc
      _ ≤ ((logarithmicChainLength t n:ℝ)+1)*t := h
      _ = _ := by field_simp

theorem tendsto_chainLength_div_scale (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => (logarithmicChainLength t n:ℝ)/n) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => (Real.log n/(n:ℝ))/t) atTop (nhds 0) := by
    simpa only [zero_div,Function.comp_def,id_eq] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).div_const t
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
  · exact Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (le_div_iff₀ ht).mpr
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hn').mpr (logarithmicChainLength_bounds t ht n hn).1

theorem eventually_chain_volume_small (t : ℝ) (ht : 0 < t) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2*logarithmicChainLength t n*M ≤ n := by
  have hlim : Tendsto (fun n : ℕ => (2*(logarithmicChainLength t n:ℝ)*M)/(n:ℝ)) atTop (nhds 0) := by
    have h := (tendsto_chainLength_div_scale t ht).const_mul (2*(M:ℝ))
    simpa only [mul_zero] using h.congr (fun n => by ring)
  filter_upwards [(tendsto_order.mp hlim).2 1 (by norm_num),eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (div_lt_iff₀ hn').mp hn
  norm_num only [one_mul] at h
  exact_mod_cast h.le

end LogarithmicChainLength
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationPolynomial

theorem amplificationMomentFactor_ge_four (k M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    4 ≤ amplificationMomentFactor k M d c a t := by
  unfold amplificationMomentFactor
  have h1 : (0:ℝ) ≤ ((k*M)+(k*M)^2+d*(k*M)^3:ℕ) := Nat.cast_nonneg _
  have h2 : (0:ℝ) ≤ (2*c*(k*M:ℕ))^2*t/a := by positivity
  linarith

theorem amplificationMomentFactor_cubic (k M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    amplificationMomentFactor k M d c a t ≤ amplificationMomentFactor 1 M d c a t * ((k:ℝ)+1)^3 := by
  let b := (2*c*(M:ℝ))^2*t/a
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hk1 : (1:ℝ) ≤ (k:ℝ)+1 := by linarith
  have h13 : (1:ℝ) ≤ ((k:ℝ)+1)^3 := one_le_pow₀ hk1
  have h1 : (k:ℝ) ≤ ((k:ℝ)+1)^3 := by
    calc
      _ ≤ (k:ℝ)+1 := by linarith
      _ = ((k:ℝ)+1)^1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hk1 (by omega)
  have h2 : (k:ℝ)^2 ≤ ((k:ℝ)+1)^3 :=
    (pow_le_pow_left₀ hk (by linarith : (k:ℝ) ≤ (k:ℝ)+1) 2).trans (pow_le_pow_right₀ hk1 (by omega))
  have h3 : (k:ℝ)^3 ≤ ((k:ℝ)+1)^3 := pow_le_pow_left₀ hk (by linarith) 3
  have he (j : ℕ) : amplificationMomentFactor j M d c a t =
      4 + (M:ℝ)*j + (M:ℝ)^2*(j:ℝ)^2 + ((d:ℝ)*(M:ℝ)^3)*(j:ℝ)^3 + b*(j:ℝ)^2 := by
    simp only [amplificationMomentFactor,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,b]
    ring
  rw [he k,he 1]
  norm_num only [Nat.cast_one,one_pow,mul_one]
  have hh0 := mul_le_mul_of_nonneg_left h13 (by norm_num : (0:ℝ) ≤ 4)
  have hh1 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg M : (0:ℝ) ≤ M)
  have hh2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (M:ℝ))
  have hh3 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ (d:ℝ)*(M:ℝ)^3 by positivity)
  have hhb := mul_le_mul_of_nonneg_left h2 hb
  nlinarith only [hh0,hh1,hh2,hh3,hhb]

theorem tendsto_log_amplificationMomentFactor_div (M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    Tendsto (fun k : ℕ => Real.log (amplificationMomentFactor k M d c a t)/(k:ℝ)) atTop (nhds 0) := by
  let C := amplificationMomentFactor 1 M d c a t
  have hC : 0 < C := amplificationMomentFactor_pos _ _ _ _ _ _ ha ht
  have hplus : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun k : ℕ => Real.log ((k:ℝ)+1)/(k:ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hplus
  have hupper : Tendsto (fun k : ℕ => (Real.log C + 3*Real.log ((k:ℝ)+1))/(k:ℝ)) atTop (nhds 0) := by
    have h := ((tendsto_const_nhds (x := Real.log C)).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))).add (hlog.const_mul 3)
    simpa only [zero_add,mul_zero,add_div,mul_div_assoc] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun k => div_nonneg
      (Real.log_nonneg (by have := amplificationMomentFactor_ge_four k M d c a t ha ht; linarith)) (Nat.cast_nonneg _))
  · exact Eventually.of_forall (fun k => by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have hh := Real.log_le_log (amplificationMomentFactor_pos k M d c a t ha ht)
        (amplificationMomentFactor_cubic k M d c a t ha ht)
      have hp : (0:ℝ) < (k:ℝ)+1 := by positivity
      simpa only [C,Real.log_mul hC.ne' (pow_pos hp 3).ne',Real.log_pow,Nat.cast_ofNat] using hh)

end AmplificationPolynomial
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationScalarBudget

theorem eventually_inverseCodeMass_budget (s ξ : ℝ) (hs : 0 ≤ s) (hξ : 0 < ξ) :
    ∀ᶠ M : ℕ in atTop, 2 ≤ M ∧ 1 ≤ (M:ℝ)^s ∧
      inverseCodeMass M ((M:ℝ)^s) ≤ (M:ℝ)^(s+ξ) := by
  have hl := (isLittleO_log_rpow_atTop hξ).bound (by norm_num : (0:ℝ) < 1/8)
  have hcast : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),hcast.eventually hl] with M hM hl
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM'
  have hL : 1 ≤ (M:ℝ)^s := Real.one_le_rpow hM' hs
  refine ⟨hM,hL,?_⟩
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hM'),
    abs_of_nonneg (Real.rpow_nonneg hM0.le ξ)] at hl
  calc
    _ ≤ 8*(M:ℝ)^s*Real.log M := inverseCodeMass_le_log M _ hM hL
    _ ≤ (M:ℝ)^s*(M:ℝ)^ξ := by
      have hh := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hM0.le s)
      nlinarith only [hh]
    _ = _ := (Real.rpow_add hM0 _ _).symm

theorem code_bound_of_logarithmic_chain (u W t : ℝ) (hu : 0 < u) (hW : 0 ≤ W)
    (ht : 0 < t) (hbudget : W ≤ u*Real.exp t) (n : ℕ) (hn : 1 ≤ n) :
    W^logarithmicChainLength t n ≤ (n:ℝ)*u^logarithmicChainLength t n := by
  let k := logarithmicChainLength t n
  have hexp : Real.exp ((k:ℝ)*t) ≤ (n:ℝ) := by
    have h := Real.exp_le_exp.mpr (logarithmicChainLength_bounds t ht n hn).1
    have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simpa only [Real.exp_log hnp] using h
  calc
    W^k ≤ (u*Real.exp t)^k := pow_le_pow_left₀ hW hbudget _
    _ = u^k*Real.exp ((k:ℝ)*t) := by rw [mul_pow,←Real.exp_nat_mul]
    _ ≤ u^k*n := mul_le_mul_of_nonneg_left hexp (pow_nonneg hu.le _)
    _ = _ := mul_comm _ _

theorem tendsto_rpow_mul_stretched_exp (γ ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun x : ℝ => x^γ * Real.exp (-(x^ε))) atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (γ/ε) 1 zero_lt_one).comp (tendsto_rpow_atTop hε)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  simp only [Function.comp_def,neg_mul,one_mul,←Real.rpow_mul hx]
  rw [mul_div_cancel₀ γ hε.ne']

end AmplificationScalarBudget
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationGoodnessDecay

theorem eventually_amplification_goodness_decay (T : ℝ) (hT : 0 < T)
    (M d : ℕ) (c a b β ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      16*amplificationMomentFactor (logarithmicChainLength T n) M d c a b *
        Real.exp (-((2*n+logarithmicChainLength T n*M:ℕ):ℝ)^ε) ≤ a*(n:ℝ)^(-β) := by
  let C := amplificationMomentFactor 1 M d c a b
  have hC : 0 < C := amplificationMomentFactor_pos _ _ _ _ _ _ ha hb
  have hd : Tendsto (fun n : ℕ => 128*C*((n:ℝ)^(β+3)*Real.exp (-(n:ℝ)^ε))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_rpow_mul_stretched_exp (β+3) ε hε).comp tendsto_natCast_atTop_atTop).const_mul (128*C)
  have hk := (tendsto_order.mp (tendsto_chainLength_div_scale T hT)).2 1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℕ),hk,(tendsto_order.mp hd).2 a ha] with n hn hk hd
  let k := logarithmicChainLength T n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hkn : (k:ℝ) ≤ n := by
    exact ((div_lt_iff₀ hn0).mp hk).le.trans_eq (one_mul _)
  have hQ : amplificationMomentFactor k M d c a b ≤ 8*C*(n:ℝ)^3 := by
    have hp : ((k:ℝ)+1)^3 ≤ (2*(n:ℝ))^3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    calc
      _ ≤ C*((k:ℝ)+1)^3 := amplificationMomentFactor_cubic k M d c a b ha hb
      _ ≤ C*(2*(n:ℝ))^3 := mul_le_mul_of_nonneg_left hp hC.le
      _ = _ := by ring
  have he : Real.exp (-((2*n+k*M:ℕ):ℝ)^ε) ≤ Real.exp (-(n:ℝ)^ε) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hε.le
    exact_mod_cast (show n ≤ 2*n+k*M by omega)
  have hpow : 0 < (n:ℝ)^β := Real.rpow_pos_of_pos hn0 _
  rw [Real.rpow_neg hn0.le,←div_eq_mul_inv]
  apply (le_div_iff₀ hpow).mpr
  calc
    _ ≤ (16*(8*C*(n:ℝ)^3)*Real.exp (-(n:ℝ)^ε))*(n:ℝ)^β := by
      apply mul_le_mul_of_nonneg_right _ hpow.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by norm_num)) he
        (Real.exp_pos _).le (by positivity)
    _ = 128*C*((n:ℝ)^(β+3)*Real.exp (-(n:ℝ)^ε)) := by
      rw [Real.rpow_add hn0,show (n:ℝ)^(3:ℝ) = (n:ℝ)^3 by norm_cast]
      ring
    _ ≤ a := hd.le

end AmplificationGoodnessDecay
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationLogEstimates

theorem log_inv_success_le (a Q n β u : ℝ) (ha : 0 < a) (hQ : 0 < Q)
    (hn : 0 < n) (hbound : a*n^(-β)/(8*Q) ≤ u) :
    Real.log (1/u) ≤ β*Real.log n + Real.log Q + Real.log (8/a) := by
  have hl : 0 < a*n^(-β)/(8*Q) := by positivity
  have hu : 0 < u := hl.trans_le hbound
  have h := Real.log_le_log hl hbound
  rw [Real.log_div (mul_pos ha (Real.rpow_pos_of_pos hn _)).ne' (mul_pos (by norm_num) hQ).ne',
    Real.log_mul ha.ne' (Real.rpow_pos_of_pos hn _).ne',Real.log_rpow hn,
    Real.log_mul (by norm_num : (8:ℝ) ≠ 0) hQ.ne'] at h
  rw [one_div,Real.log_inv,Real.log_div (by norm_num : (8:ℝ) ≠ 0) ha.ne']
  linarith

theorem log_inv_norm_ge (r r' : ℝ) (k : ℕ) (hr : 0 < r) (hr' : 0 < r')
    (hbound : r' ≤ 2*r^k) :
    (k:ℝ)*Real.log (1/r) - Real.log 2 ≤ Real.log (1/r') := by
  have h := Real.log_le_log hr' hbound
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_pos hr _).ne',Real.log_pow] at h
  simp only [one_div,Real.log_inv]
  linarith

 

theorem eventually_amplification_log_estimates (T ξ β H : ℝ)
    (hT : 0 < T) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hH : 0 < H)
    (M d : ℕ) (c a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      let k := logarithmicChainLength T n
      β*Real.log n + Real.log (amplificationMomentFactor k M d c a b) + Real.log (8/a) ≤
        (k:ℝ)*(β+ξ)*T ∧
      Real.log ((2*n+k*M:ℕ):ℝ) ≤ (k:ℝ)*(1+ξ)*T ∧
      (k:ℝ)*(1-ξ)*H ≤ (k:ℝ)*H-Real.log 2 ∧
      2*H ≤ (k:ℝ)*(1-ξ)*H ∧ 1 ≤ k := by
  let k := logarithmicChainLength T
  have hk : Tendsto k atTop atTop := tendsto_logarithmicChainLength T hT
  have hkR : Tendsto (fun n => (k n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hU : Tendsto (fun n : ℕ =>
      (β*Real.log n + Real.log (amplificationMomentFactor (k n) M d c a b) + Real.log (8/a))/(k n:ℝ))
      atTop (nhds (β*T)) := by
    have h1 := (tendsto_log_div_chainLength T hT).const_mul β
    have h2 := (tendsto_log_amplificationMomentFactor_div M d c a b ha hb).comp hk
    have h3 := (tendsto_const_nhds (x := Real.log (8/a))).div_atTop hkR
    simpa only [add_zero,add_div,mul_div_assoc,Function.comp_def] using (h1.add h2).add h3
  have hm : Tendsto (fun n : ℕ => (Real.log n+Real.log 3)/(k n:ℝ)) atTop (nhds T) := by
    simpa only [add_zero,add_div] using (tendsto_log_div_chainLength T hT).add
      ((tendsto_const_nhds (x := Real.log 3)).div_atTop hkR)
  have hHlim : Tendsto (fun n : ℕ => Real.log 2/(k n:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hkR
  have hU' := (tendsto_order.mp hU).2 ((β+ξ)*T) (by nlinarith)
  have hm' := (tendsto_order.mp hm).2 ((1+ξ)*T) (by nlinarith)
  have hH' := (tendsto_order.mp hHlim).2 (ξ*H) (mul_pos hξ hH)
  filter_upwards [hU',hm',hH',hkR.eventually_ge_atTop (2/(1-ξ)),
    hk.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ),eventually_chain_volume_small T hT M]
    with n hUn hmn hHn hklarge hk1 hn hvol
  have hkp : (0:ℝ) < k n := by exact_mod_cast (show 0 < k n by omega)
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcap : (2*n+k n*M:ℕ) ≤ 3*n := by
    dsimp [k] at *
    rw [Nat.mul_assoc] at hvol
    omega
  have hcap0 : (0:ℝ) < (2*n+k n*M:ℕ) := by exact_mod_cast (show 0 < 2*n+k n*M by omega)
  refine ⟨?_,?_,?_,?_,hk1⟩
  · have h := (div_lt_iff₀ hkp).mp hUn
    nlinarith only [h]
  · calc
      _ ≤ Real.log (3*(n:ℝ)) := Real.log_le_log hcap0 (by exact_mod_cast hcap)
      _ = Real.log n + Real.log 3 := by rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hnp.ne']; ring
      _ ≤ _ := by have h := (div_lt_iff₀ hkp).mp hmn; nlinarith only [h]
  · have h := (div_lt_iff₀ hkp).mp hHn
    nlinarith only [h]
  · have h := (div_le_iff₀ (sub_pos.mpr hξ1)).mp hklarge
    have hh := mul_le_mul_of_nonneg_right h hH.le
    nlinarith only [hh]

end AmplificationLogEstimates
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section AsymptoticAmplificationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem asymptotic_amplification_step [Nonempty V] [Nonempty E]
    (hconn : Connected G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (hp : (p:ℝ) < 1) (d : ℕ) (hdeg : ∀ x, degree G x ≤ d)
    (hu : 0 < q.successProbability p (root i₀))
    (a b β ε ξ T : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hT : 0 < T)
    (hbudget : inverseCodeMass M L ≤ q.successProbability p (root i₀)*Real.exp T)
    (A : Hilbert V →L[ℂ] Hilbert V) (hApos : 0 < ‖A‖)
    (hH : 0 < Real.log (1/‖A‖))
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∀ᶠ n : ℕ in atTop, ∀ π : ℝ,
      (n:ℝ)^(-β) ≤ π →
      a*n*π ≤ binOrbitRow G p (root i₀) n →
      clusterWindowProbability G p (root i₀) (n-logarithmicChainLength T n*M) (2*n) ≤ b*π →
      ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀))
          (2*n+logarithmicChainLength T n*M) (((2*n+logarithmicChainLength T n*M:ℕ):ℝ)^(1/2+ε)),
        0 < q'.successProbability p (root i₀) ∧
        Real.log (1/q'.successProbability p (root i₀)) ≤ (logarithmicChainLength T n:ℝ)*(β+ξ)*T ∧
        Real.log ((2*n+logarithmicChainLength T n*M:ℕ):ℝ) ≤ (logarithmicChainLength T n:ℝ)*(1+ξ)*T ∧
        ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧
          (logarithmicChainLength T n:ℝ)*(1-ξ)*Real.log (1/‖A‖) ≤ Real.log (1/‖A'‖) ∧
          2*Real.log (1/‖A‖) ≤ Real.log (1/‖A'‖) ∧
          (∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ)) ∧
          1 ≤ logarithmicChainLength T n := by
  let k := logarithmicChainLength T
  let cap := fun n => 2*n+k n*M
  have hcap : Tendsto cap atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ cap n by dsimp [cap]; omega) tendsto_id
  have hgood := hcap.eventually (bad_goodness_stretched_exp G hloc hqt p hp ε hε hε1)
  have hdecay := eventually_amplification_goodness_decay T hT M d c a b β ε ha hb hε
  have hlogs := eventually_amplification_log_estimates T ξ β (Real.log (1/‖A‖))
    hT hξ hξ1 hH M d c a b ha hb
  filter_upwards [hgood,hdecay,hlogs,eventually_ge_atTop (1:ℕ)] with n hgood hdecay hlogs hn
  intro π hπ hbin hwindow
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hπ0 : 0 < π := (Real.rpow_pos_of_pos hnR (-β)).trans_le hπ
  have hQ : 0 < amplificationMomentFactor (k n) M d c a b := amplificationMomentFactor_pos _ _ _ _ _ _ ha hb
  have hcoden : inverseCodeMass M L^(k n) ≤ n*q.successProbability p (root i₀)^(k n) := by
    apply code_bound_of_logarithmic_chain _ _ _ hu _ hT hbudget n hn
    unfold inverseCodeMass
    exact add_nonneg zero_le_one (Finset.sum_nonneg (fun l _ => gapWeight_nonneg L (by linarith) l))
  have hbad : 16*amplificationMomentFactor (k n) M d c a b *
      (law p).real {ω | CappedBadGoodness G ω (root i₀) (cap n) ((cap n:ℝ)^(1/2+ε))} ≤ a*π := by
    calc
      _ ≤ 16*amplificationMomentFactor (k n) M d c a b * Real.exp (-(cap n:ℝ)^ε) :=
        mul_le_mul_of_nonneg_left (hgood (root i₀) p le_rfl) (by positivity)
      _ ≤ a*(n:ℝ)^(-β) := hdecay
      _ ≤ _ := mul_le_mul_of_nonneg_left hπ ha.le
  obtain ⟨q',hup,A',hAp,hAr,hA'⟩ := q.quantitative_amplification_step hconn root weight Γ hΓ htr hcov
    hw hw1 c hc hmin i₀ hw₀ hL p (k n) n d hn0 hdeg hu a b π ((cap n:ℝ)^(1/2+ε))
    ha hb hπ0 hbin hwindow hcoden hbad A hA
  have hup0 : 0 < q'.successProbability p (root i₀) := (by positivity : 0 < a*π/(8*amplificationMomentFactor (k n) M d c a b)).trans_le hup
  have hulo : a*(n:ℝ)^(-β)/(8*amplificationMomentFactor (k n) M d c a b) ≤ q'.successProbability p (root i₀) := by
    apply le_trans _ hup
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hπ ha.le) (by positivity)
  have hulo' := log_inv_success_le a (amplificationMomentFactor (k n) M d c a b) (n:ℝ) β
    (q'.successProbability p (root i₀)) ha hQ hnR hulo
  have hH' := log_inv_norm_ge ‖A‖ ‖A'‖ (k n) hApos hAp hAr
  exact ⟨q',hup0,hulo'.trans hlogs.1,hlogs.2.1,A',hAp,hlogs.2.2.1.trans hH',
    hlogs.2.2.2.1.trans (hlogs.2.2.1.trans hH'),hA',hlogs.2.2.2.2⟩

end LocalEndpointRule
end AsymptoticAmplificationStep
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section WeightedScaleWindow
attribute [local instance] Classical.propDecidable Classical.decEq

theorem weightedWindowProbability_term_le {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (i : ι) (a b : ℕ) :
    weight i * clusterWindowProbability G p (root i) a b ≤ weightedWindowProbability G p root weight a b :=
  Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (clusterWindowProbability_nonneg G p (root j) a b)) (Finset.mem_univ i)

theorem orbit_scale_window_bound {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (i : ι) (hi : 0 < weight i)
    (j k M : ℕ) (hvol : 2*k*M ≤ 2^(j+1)) (β π : ℝ)
    (hwindow : weightedWindowProbability G p root weight (2^j) (2^(j+2)) ≤ (1+(2:ℝ)^β)*π) :
    clusterWindowProbability G p (root i) (2^(j+1)-k*M) (2*2^(j+1)) ≤
      ((1+(2:ℝ)^β)/weight i)*π := by
  have he : 2^(j+1) = 2*2^j := by rw [pow_succ]; omega
  have he' : 2*2^(j+1) = 2^(j+2) := by rw [show j+2 = (j+1)+1 by omega,pow_succ]; omega
  have hl : 2^j ≤ 2^(j+1)-k*M := by
    rw [he,Nat.mul_assoc] at hvol
    rw [he]
    omega
  have hmono := clusterWindowProbability_mono G p (root i) hl (le_of_eq he')
  have hterm := weightedWindowProbability_term_le G p root weight hw i (2^j) (2^(j+2))
  have hb := (mul_le_mul_of_nonneg_left hmono hi.le).trans (hterm.trans hwindow)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hi).mpr (by simpa only [mul_comm] using hb)

theorem tendsto_dyadic_scale : Tendsto (fun j : ℕ => 2^(j+1)) atTop atTop :=
  tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (j+1).lt_two_pow_self.le) tendsto_id

end WeightedScaleWindow
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EndpointProfile



namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p : unitInterval} {o : V} {s : ℝ}

theorem U_nonneg (q : EndpointProfile G hloc p o s) : 0 ≤ q.U := by
  unfold U
  rw [one_div,Real.log_inv]
  have h := Real.log_nonpos q.success_pos.le (q.rule.successProbability_le_one p o)
  linarith

theorem m_pos (q : EndpointProfile G hloc p o s) (hcap : 2 ≤ q.cap) : 0 < q.m := by
  exact Real.log_pos (by exact_mod_cast (show 1 < q.cap by omega))

theorem cost_pos (q : EndpointProfile G hloc p o s) (hcap : 2 ≤ q.cap)
    (ξ : ℝ) (hsξ : 0 < s+ξ) : 0 < q.cost ξ := by
  exact add_pos_of_nonneg_of_pos q.U_nonneg (mul_pos hsξ (q.m_pos hcap))

theorem exp_cost_identity (q : EndpointProfile G hloc p o s) (hcap : 0 < q.cap) (ξ : ℝ) :
    q.rule.successProbability p o * Real.exp (q.cost ξ) = (q.cap:ℝ)^(s+ξ) := by
  have hcp : (0:ℝ) < q.cap := Nat.cast_pos.mpr hcap
  simp only [cost,U,m,Real.exp_add,Real.exp_log (one_div_pos.mpr q.success_pos)]
  calc
    _ = Real.exp ((s+ξ)*Real.log q.cap) := by field_simp [ne_of_gt q.success_pos]
    _ = _ := by rw [Real.rpow_def_of_pos hcp]; congr 1; ring

end EndpointProfile

variable [Countable V] [Countable E] [Nonempty V]

theorem starting_endpoint_profile (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω (root i₀)).Finite)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (M₀ : ℕ) :
    ∃ q : EndpointProfile G hloc p (root i₀) (1/2+ε), M₀ ≤ q.cap ∧ 1 < q.H := by
  obtain ⟨M,hM,q,hq,A,hAp,hAn,hA⟩ := nonamenable_starting_endpoint_rule G hloc hqt hh p hp hp1
    root weight Γ hΓ htr hw hw1 i₀ hw₀ hfin ε hε hε1 (Real.exp (-2)) (Real.exp_pos _) M₀
  refine ⟨⟨M,q,hq,A,hAp,hA⟩,hM,?_⟩
  have h := Real.log_lt_log hAp hAn
  rw [Real.log_exp] at h
  change 1 < Real.log (1/‖A‖)
  rw [one_div,Real.log_inv]
  linarith

end EndpointProfile

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EndpointProfileStep
attribute [local instance] Classical.propDecidable Classical.decEq

namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G}

theorem amplify_at_scales [Nonempty V] [Nonempty E]
    (hconn : Connected G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i : ι) (p : unitInterval) (hp : (p:ℝ) < 1)
    (d : ℕ) (hdeg : ∀ x, degree G x ≤ d)
    (ε ξ β : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hscales : ∀ N, ∃ j, N ≤ j ∧
      ((2^(j+1):ℕ):ℝ)^(-β) ≤ dyadicBinProbability G p root weight (j+1) ∧
      weightedWindowProbability G p root weight (2^j) (2^(j+2)) ≤
        (1+(2:ℝ)^β)*dyadicBinProbability G p root weight (j+1) ∧
      (((2^(j+1):ℕ):ℝ)/Fintype.card ι)*dyadicBinProbability G p root weight (j+1) ≤
        binOrbitRow G p (root i) (2^(j+1)))
    (q : EndpointProfile G hloc p (root i) (1/2+ε)) (hM : 2 ≤ q.cap)
    (hL : 1 ≤ (q.cap:ℝ)^(1/2+ε))
    (hbudget : inverseCodeMass q.cap ((q.cap:ℝ)^(1/2+ε)) ≤ (q.cap:ℝ)^(1/2+ε+ξ))
    (hH : 0 < q.H) (N : ℕ) :
    ∃ (q' : EndpointProfile G hloc p (root i) (1/2+ε)) (k : ℕ),
      N ≤ q'.cap ∧ 1 ≤ k ∧
      q'.U ≤ (k:ℝ)*(β+ξ)*q.cost ξ ∧
      q'.m ≤ (k:ℝ)*(1+ξ)*q.cost ξ ∧
      (k:ℝ)*(1-ξ)*q.H ≤ q'.H ∧ 2*q.H ≤ q'.H := by
  let a : ℝ := 1/Fintype.card ι
  let b : ℝ := (1+(2:ℝ)^β)/weight i
  let T := q.cost ξ
  have ht : 0 < T := q.cost_pos hM ξ (by linarith)
  have hcard : (0:ℝ) < Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
  have ha : 0 < a := one_div_pos.mpr hcard
  have hb : 0 ≤ b := div_nonneg (by positivity) (hw i).le
  have hbudget' : inverseCodeMass q.cap ((q.cap:ℝ)^(1/2+ε)) ≤
      q.rule.successProbability p (root i)*Real.exp T := by
    rw [q.exp_cost_identity (by omega) ξ]
    exact hbudget
  have hstep := q.rule.asymptotic_amplification_step hconn hqt root weight Γ hΓ htr hcov
    (fun i => (hw i).le) hw1 c hc hmin i (hw i) hL p hp d hdeg q.success_pos
    a b β ε ξ T ha hb hε hε1 hξ hξ1 ht hbudget' q.op q.norm_pos hH q.coeff
  have hvol := eventually_chain_volume_small T ht q.cap
  have he := tendsto_dyadic_scale.eventually (hstep.and (hvol.and (eventually_ge_atTop N)))
  obtain ⟨J,hJ⟩ := eventually_atTop.1 he
  obtain ⟨j,hj,hπ,hwide,hbin⟩ := hscales J
  obtain ⟨hs,hvol,hN⟩ := hJ j hj
  have hwin := orbit_scale_window_bound G p root weight (fun i => (hw i).le) i (hw i)
    j (logarithmicChainLength T (2^(j+1))) q.cap hvol β _ hwide
  have hbin' : a*(2^(j+1):ℕ)*dyadicBinProbability G p root weight (j+1) ≤
      binOrbitRow G p (root i) (2^(j+1)) := by
    dsimp [a]
    simpa only [div_eq_mul_inv,one_mul,mul_comm (_⁻¹)] using hbin
  obtain ⟨q',hup,hU,hm,A',hAp,hH',hH'',hA',hk⟩ := hs _ hπ hbin' hwin
  refine ⟨⟨_,q',hup,A',hAp,hA'⟩,_,?_,hk,hU,hm,hH',hH''⟩
  change N ≤ 2*2^(j+1)+logarithmicChainLength T (2^(j+1))*q.cap
  omega

end EndpointProfile
end EndpointProfileStep

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationContraction

theorem exists_amplification_contraction (β s : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hsmall : β+s < 1) : ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧
      0 ≤ amplificationContraction β s ξ ∧ amplificationContraction β s ξ < 1 := by
  have hd : 0 < 4+s := by linarith
  have hδ : 0 < (1-(β+s))/(4+s) := div_pos (by linarith) hd
  obtain ⟨ξ,hξ,hξupper⟩ := exists_between (lt_min zero_lt_one hδ)
  have hξ1 := hξupper.trans_le (min_le_left _ _)
  have hprod : ξ*(4+s) < 1-(β+s) := (lt_div_iff₀ hd).mp (hξupper.trans_le (min_le_right _ _))
  have hx2 : ξ^2 < ξ := by nlinarith [mul_pos hξ (sub_pos.mpr hξ1)]
  refine ⟨ξ,hξ,hξ1,?_,?_⟩
  · unfold amplificationContraction
    positivity
  · unfold amplificationContraction
    apply (div_lt_one (by linarith : 0 < 1-ξ)).mpr
    nlinarith

 

theorem amplification_cost_contraction (t t' H H' β s ξ : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hH : 0 < H) (hξ1 : ξ < 1) (hk : 1 ≤ k)
    (hC : 0 ≤ amplificationContraction β s ξ)
    (ht' : t' ≤ (k:ℝ)*(β+ξ+(s+ξ)*(1+ξ))*t)
    (hH' : (k:ℝ)*(1-ξ)*H ≤ H') :
    t'/H' ≤ amplificationContraction β s ξ*(t/H) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hd : 0 < (k:ℝ)*(1-ξ)*H := mul_pos (mul_pos hk0 (by linarith)) hH
  have hH'p := hd.trans_le hH'
  apply (div_le_iff₀ hH'p).mpr
  have he : (k:ℝ)*(β+ξ+(s+ξ)*(1+ξ))*t =
      amplificationContraction β s ξ*(t/H)*((k:ℝ)*(1-ξ)*H) := by
    unfold amplificationContraction
    field_simp [hH.ne', (sub_pos.mpr hξ1).ne']
  rw [he] at ht'
  exact ht'.trans (mul_le_mul_of_nonneg_left hH' (mul_nonneg hC (div_nonneg ht hH.le)))

namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p : unitInterval} {o : V} {s : ℝ}

theorem cost_contraction (q q' : EndpointProfile G hloc p o s) (β ξ : ℝ) (k : ℕ)
    (hM : 2 ≤ q.cap) (hsξ : 0 < s+ξ) (hH : 0 < q.H) (hξ1 : ξ < 1) (hk : 1 ≤ k)
    (hC : 0 ≤ amplificationContraction β s ξ)
    (hU : q'.U ≤ (k:ℝ)*(β+ξ)*q.cost ξ)
    (hm : q'.m ≤ (k:ℝ)*(1+ξ)*q.cost ξ)
    (hH' : (k:ℝ)*(1-ξ)*q.H ≤ q'.H) :
    q'.cost ξ/q'.H ≤ amplificationContraction β s ξ*(q.cost ξ/q.H) := by
  apply amplification_cost_contraction _ _ _ _ β s ξ k (q.cost_pos hM ξ hsξ).le hH hξ1 hk hC _ hH'
  unfold cost at *
  have hh := mul_le_mul_of_nonneg_left hm hsξ.le
  nlinarith only [hU,hh]

theorem total_cost_le (q : EndpointProfile G hloc p o s) (hM : 2 ≤ q.cap)
    (ξ : ℝ) (hsξ : 0 < s+ξ) : q.U+q.m ≤ (1+1/(s+ξ))*q.cost ξ := by
  have hm := (q.m_pos hM).le
  have hU := q.U_nonneg
  have hU' : q.U ≤ q.cost ξ := by unfold cost; nlinarith
  have hm' : q.m ≤ q.cost ξ/(s+ξ) := by
    apply (le_div_iff₀ hsξ).mpr
    unfold cost
    nlinarith
  calc
    _ ≤ q.cost ξ+q.cost ξ/(s+ξ) := add_le_add hU' hm'
    _ = _ := by ring

end EndpointProfile
end AmplificationContraction

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
open Filter
section ContractingIteration

 

theorem exists_efficient_of_contracting_successor {S : Type*}
    (g H : S → ℝ) (C : ℝ) (hC : 0 ≤ C) (hC1 : C < 1)
    (hstep : ∀ x, ∃ y, g y ≤ C*g x ∧ 2*H x ≤ H y)
    (x₀ : S) (hH₀ : 0 < H x₀) (η R : ℝ) (hη : 0 < η) :
    ∃ x, g x < η ∧ R < H x := by
  classical
  choose f hf using hstep
  let x : ℕ → S := fun n => f^[n] x₀
  have hx (n : ℕ) : x (n+1) = f (x n) := Function.iterate_succ_apply' f n x₀
  have hbounds (n : ℕ) : g (x n) ≤ C^n*g x₀ ∧ (2:ℝ)^n*H x₀ ≤ H (x n) := by
    induction n with
    | zero => simp only [x,Function.iterate_zero,id_eq,pow_zero,one_mul,le_refl,and_self]
    | succ n ih =>
      rw [hx]
      obtain ⟨hg,hH⟩ := hf (x n)
      constructor
      · calc
          _ ≤ C*g (x n) := hg
          _ ≤ C*(C^n*g x₀) := mul_le_mul_of_nonneg_left ih.1 hC
          _ = _ := by rw [pow_succ]; ring
      · calc
          _ = 2*((2:ℝ)^n*H x₀) := by rw [pow_succ]; ring
          _ ≤ 2*H (x n) := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
          _ ≤ _ := hH
  have hg : Tendsto (fun n : ℕ => C^n*g x₀) atTop (nhds 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hC hC1).mul_const (g x₀)
  have hH : Tendsto (fun n : ℕ => (2:ℝ)^n*H x₀) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).atTop_mul_const hH₀
  obtain ⟨n,hg',hH'⟩ := ((tendsto_order.mp hg).2 η hη |>.and
    (hH.eventually (eventually_gt_atTop R))).exists
  exact ⟨x n,(hbounds n).1.trans_lt hg',hH'.trans_le (hbounds n).2⟩

end ContractingIteration

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EfficientEndpointProfiles
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem efficient_endpoint_profiles_of_divergent_moment_bs_oai
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law p, (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p)) :
    ∃ i, ∀ η : ℝ, 0 < η → ∀ R : ℝ,
      ∃ q : EndpointProfile G hloc p (root i) (1/2+ε),
        2 ≤ q.cap ∧ 1 < q.H ∧ R < q.H ∧ q.U+q.m < η*q.H := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,e,he,hx⟩ := hcov x
    obtain ⟨b,hb⟩ := hΓ he
    exact ⟨i,e,b,hb,hx⟩
  obtain ⟨i,hscales⟩ := orbit_scales_of_divergent_moment G hloc root weight Γ hΓ htr hw hw1 hcover p α β hα hαβ hdiv
  obtain ⟨ξ,hξ,hξ1,hC,hC1⟩ := exists_amplification_contraction β (1/2+ε) (by linarith) (by linarith) hsmall
  have hsξ : 0 < 1/2+ε+ξ := by linarith
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.1 (eventually_inverseCodeMass_budget (1/2+ε) ξ (by linarith) hξ)
  obtain ⟨q₀,hq₀,hH₀⟩ := starting_endpoint_profile G hloc hqt hh p hp hp1 root weight Γ hΓ htr
    (fun i => (hw i).le) hw1 i (hw i) (hfin i) ε hε hε1 M₀
  obtain ⟨d,_,hdeg⟩ := exists_degree_bound G hqt
  let c : ℝ := ∑ j, 1/weight j
  have hc : 0 ≤ c := Finset.sum_nonneg (fun j _ => (one_div_pos.mpr (hw j)).le)
  have hmin (j : ι) : 1 ≤ c*weight j := by
    apply (div_le_iff₀ (hw j)).mp
    exact Finset.single_le_sum (fun l _ => (one_div_pos.mpr (hw l)).le) (Finset.mem_univ j)
  let S := {q : EndpointProfile G hloc p (root i) (1/2+ε) // M₀ ≤ q.cap ∧ 1 < q.H}
  let g : S → ℝ := fun q => q.val.cost ξ/q.val.H
  let H : S → ℝ := fun q => q.val.H
  have hstep : ∀ q : S, ∃ q' : S, g q' ≤ amplificationContraction β (1/2+ε) ξ*g q ∧ 2*H q ≤ H q' := by
    intro q
    have hcap := hM₀ q.val.cap q.property.1
    have hH : 0 < q.val.H := lt_trans zero_lt_one q.property.2
    obtain ⟨r,k,hr,hk,hU,hm,hH',hH''⟩ := q.val.amplify_at_scales hconn hqt root weight Γ hΓ htr hcov hw hw1
      c hc hmin i p hp1 d hdeg ε ξ β hε hε1 hξ hξ1 hscales hcap.1 hcap.2.1 hcap.2.2 hH M₀
    have hrH : 1 < r.H := by linarith [q.property.2]
    refine ⟨⟨r,hr,hrH⟩,?_,hH''⟩
    exact q.val.cost_contraction r β ξ k hcap.1 hsξ hH hξ1 hk hC hU hm hH'
  refine ⟨i,?_⟩
  intro η hη R
  let D : ℝ := 1+1/(1/2+ε+ξ)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨q,hg,hR⟩ := exists_efficient_of_contracting_successor g H (amplificationContraction β (1/2+ε) ξ)
    hC hC1 hstep ⟨q₀,hq₀,hH₀⟩ (lt_trans zero_lt_one hH₀) (η/D) R (div_pos hη hD)
  have hcap := (hM₀ q.val.cap q.property.1).1
  refine ⟨q.val,hcap,q.property.2,hR,?_⟩
  have hH : 0 < q.val.H := lt_trans zero_lt_one q.property.2
  have hcost := q.val.total_cost_le hcap ξ hsξ
  have hratio : (q.val.U+q.val.m)/q.val.H ≤ D*g q := by
    have h := div_le_div_of_nonneg_right hcost hH.le
    simpa only [D,g,mul_div_assoc] using h
  apply (div_lt_iff₀ hH).mp
  apply hratio.trans_lt
  have hg' := (lt_div_iff₀ hD).mp hg
  simpa only [mul_comm] using hg'

end EfficientEndpointProfiles

end Percolation


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment_bs_oai.{u, v, u_1} := @OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment_bs_oai.{u, v, u_1}
