-- Prove2me | solution 1 for OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:05:48.53735+00:00
-- url     : https://prove2.me/submissions/0d83b74d-d271-43e1-b77b-f3f2aeb1ccb0

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_LocalEndpointRule_quantitative_amplification_step

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

end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Marked
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
    simp only [successMarks_done,successMass_done,ite_true,zero_add,mul_one]
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
      simp only [eval,heω,ite_false]
    have ho : bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if (edge e t₀ t₁).eval (insert e ω) m then 1 else 0) h) p =
        bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if t₁.eval ω m then 1 else 0) h) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      simp only [eval,Finset.mem_insert_self,ite_true]
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
        simp only [eval,hvm,ite_false]
      · congr 1
        apply bernoulliPolynomial_congr
        intro m _
        simp only [eval,Finset.mem_insert_self,ite_true]
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
      · simp only [heω,ite_true]
        rw [← Finset.insert_erase heω,Finset.coe_insert,
          seedMarked_insert_edge G _ R m _ _ _ hv hends]
        by_cases hwm : (searchCrossing G Q R hc).2.2 ∈ m
        · simp only [hwm,ite_true,true_iff]
          exact ⟨_,by simp,_,hwm,conn_refl G _ _⟩
        · simp only [hwm,ite_false]
          rw [LabelledTree.eval_insert_edge _
            (clusterSearch_valid G n _ _ (F.erase (searchCrossing G Q R hc).2.2)
              (searchAvailable_discover G ha _ _)) (Finset.notMem_erase _ _)]
          exact ih _ _ _ hcard (searchAvailable_discover G ha _ _)
            (Finset.disjoint_insert_left.mpr ⟨hwm,hm⟩) (ω.erase (searchCrossing G Q R hc).1)
            (Finset.erase_subset_erase _ hω)
      · simp only [heω,ite_false]
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
  · simp only [hxm,ite_true,true_iff]
    exact ⟨x,hxm,conn_refl G _ x⟩
  · simp only [hxm,ite_false]
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
  simp only [LabelledTree.forget,ProbeTree.successMass_done,ite_true,mul_one]
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
        not_false_eq_true,ite_true,ite_false,Nat.cast_one,Nat.cast_zero,sub_self,sub_zero]
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
  · simp only [heω,ite_true,F]
    exact bernoulliPolynomial_sub _ _ _ _
  · simp only [heω,ite_false,bernoulliPolynomial_zero]

 
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
  · simp only [markedMomentValue,h,ite_true]
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
    simp only [pivotalSuffixValue,hdel,hbe,hc,ite_true,hps]
    by_cases hd : Disjoint (cluster G ω x) (m : Set V) <;>
      by_cases hm : MarkedEvent G (exteriorBonds G ω (cluster G ω x))
        (exteriorMarks m (cluster G ω x)) (cutOutside G (cluster G ω x) e) <;>
      simp only [markedMomentValue,hd,hm,and_true,and_false,ite_true,ite_false]
  · have hn : ¬OpenMarkedPivotal G (insert e ω : Finset E) m x e := by
      intro hp
      obtain ⟨a,b,hab,hxa,hxb,_⟩ := openMarkedPivotal_oriented G (insert e ω : Finset E) m x hp
      rw [hdel] at hxa hxb
      exact hc ⟨a,b,hab,hxa,hxb⟩
    simp only [pivotalSuffixValue,hn,hc,ite_false]

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
      · simp only [hc,ite_true]
        exact cutMoment_factor G Q F W x e i h p (Finset.mem_powerset.mp hW) hc
      · simp only [hc,ite_false,bernoulliPolynomial_zero]
  · intro ω hω heω
    rw [← bernoulliPolynomial_zero F h]
    apply bernoulliPolynomial_congr
    intro m _
    have hpiv : ¬OpenMarkedPivotal G ω m x e := fun h => heω h.1
    simp only [pivotalSuffixValue,hpiv,ite_false]

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
        · simp only [hc,ite_true]
          apply mul_le_mul_of_nonneg_left _ (cutCoefficient_nonneg G Q x e W h p)
          exact ih _ _ _ (exterior_degree_bound G Q W d hdeg) (exterior_mark_support G Q F W x e he hc hF)
        · simp only [hc,ite_false,le_refl]
      _ = A^i * finiteMarkedMoment G Q F x 1 h p := by
        rw [show (1:ℕ) = 0+1 from rfl,finiteMarkedMoment_recursion G Q F x 0 h p hF]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro W hW
        by_cases hc : CutExists G W e <;> simp only [hc,ite_true,ite_false] <;> ring
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
  · simp only [markedMomentValue,hm,ite_true]
    exact choose_generating_sum _ _ (Finset.card_filter_le ..) z
  · simp only [markedMomentValue,hm,ite_false,mul_zero,Finset.sum_const_zero]

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
    · simp only [he,hc,and_self,ite_true,mul_one]
      exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+z) hc
    · simp only [he,hc,and_false,ite_true,ite_false,mul_zero]
      exact pow_nonneg (by linarith) _
  · simp only [he,false_and,ite_false,mul_zero,le_refl]

 
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
    simp only [he,ite_true,mul_one]
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
          simp only [hs,heq,hlarge,and_self,ite_true,le_refl]
        · simp only [hs,ite_false]
          split_ifs <;> norm_num
  · simp only [he,ite_false,mul_zero]
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
    simp only [he,ite_true]
    exact (by simp [hbad] : (1:ℝ) ≤ if BadPieceEvent G Q x M K L ω then 1 else 0).trans
      (Finset.single_le_sum (f := fun j => if BadPieceEvent G Q x M j L ω then (1:ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) hK)
  · simp only [he,ite_false]
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

theorem adj_symm (G : BondGraph V E) {x y : V} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,he.trans (Sym2.eq_swap)⟩

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
  simp only [Finset.mem_insert_self,ite_true]
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
      simp only [hx,ite_true]
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
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_Geometry
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

section DeletionGoodness
attribute [local instance] Classical.propDecidable Classical.decEq


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

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_GapCodes
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


end InverseCodeMass

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



theorem successProbability_le_one (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    q.successProbability p x ≤ 1 := q.kernel_row_le_one p x

end LocalEndpointRule
end LocalEndpointKernel

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
    simp only [binConnectionMass,hc,hc',and_false,ite_false]

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

end BinConnection

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

end PositiveRealMatrix



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

end OrbitBinOperator

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Covariance
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
section AmplificationLoadOperator
attribute [local instance] Classical.propDecidable Classical.decEq


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

end AmplificationLoadOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section TruncationOperator
attribute [local instance] Classical.propDecidable Classical.decEq
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



end LocalEndpointRule
end AmplificationTruncationStep

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

theorem clusterWindowProbability_nonneg (G : BondGraph V E) (p : unitInterval)
    (x : V) (lo hi : ℕ) : 0 ≤ clusterWindowProbability G p x lo hi := ENNReal.toReal_nonneg

theorem clusterWindowProbability_mono (G : BondGraph V E) (p : unitInterval)
    (x : V) {a b c d : ℕ} (hac : c ≤ a) (hbd : b ≤ d) :
    clusterWindowProbability G p x a b ≤ clusterWindowProbability G p x c d := by
  apply measureReal_mono
  · intro ω h
    exact ⟨h.1,hac.trans h.2.1,h.2.2.trans_le hbd⟩
  · exact measure_ne_top _ _

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

end QuantitativeAmplificationMoment
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
  · simp only [orbitBinConnection,hx,hy,true_and,ite_true,binConnection]
  · simp only [orbitBinConnection,hy,and_false,ite_false,integral_zero]

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

 

theorem efficient_endpoint_profiles_of_divergent_moment_oai
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

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment_oai.{u, v, u_1} := @OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment_oai.{u, v, u_1}
