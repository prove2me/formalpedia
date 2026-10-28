-- Prove2me | solution 1 for OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T00:52:53.39481+00:00
-- url     : https://prove2.me/submissions/c0e8995c-4f19-495e-b03c-7ed963eeb606

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

theorem cluster_eq_of_conn {x y : V} (h : Conn G ω x y) :
    cluster G ω x = cluster G ω y := by
  ext z
  exact ⟨fun hxz => conn_trans G ω (conn_symm G ω h) hxz,
    fun hyz => conn_trans G ω h hyz⟩

theorem conn_univ_of_connected (h : Connected G) (x y : V) : Conn G Set.univ x y := by
  apply Relation.ReflTransGen.mono (r := Adj G) ?_ x y (h x y)
  rintro a b ⟨e, he⟩
  exact ⟨e, Set.mem_univ _, he⟩

end Deterministic

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
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_Uniqueness
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

section FinitePairBound
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate

theorem norm_deltaSum_sq (F : Finset V) : ‖deltaSum F‖ ^ 2 = (F.card : ℝ) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_deltaSum]
  simp only [map_sum, deltaSum_apply]
  trans ∑ _x ∈ F, (1 : ℝ)
  · apply Finset.sum_congr rfl
    intro x hx
    simp [hx]
  · simp


end FinitePairBound

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

 theorem bernoulliPolynomial_add (s : Finset E) (f g : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => f t+g t) p =
      bernoulliPolynomial s f p + bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial, add_mul, Finset.sum_add_distrib]

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

section GraphSearchCost
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma mem_searchVertices (G : BondGraph V E) {Q : Finset E} {e : E} (he : e ∈ Q)
    {v : V} (hv : v ∈ G e) : v ∈ searchVertices G Q :=
  Finset.mem_biUnion.mpr ⟨e,he,Sym2.mem_toFinset.mpr hv⟩

end GraphSearchCost

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


theorem conn_mem_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    {ω : Set E} (hω : ω ⊆ Q) {y : V} (hxy : Conn G ω x y) :
    y ∈ insert x (searchVertices G Q) := by
  induction hxy with
  | refl => exact Finset.mem_insert_self _ _
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact Finset.mem_insert_of_mem (mem_searchVertices G (hω he) (by simp [heq]))

end MarkedRecursion

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

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


end PointwiseRecursion

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
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeCode
attribute [local instance] Classical.propDecidable Classical.decEq


theorem bridgeIndex_pos (G : BondGraph V E) (ω : Set E) (x z : V) {e : E}
    (he : OpenMarkedPivotal G ω {z} x e) : 0 < bridgeIndex G ω x z e := by
  apply Finset.card_pos.mpr
  exact ⟨e,Finset.mem_filter.mpr ⟨(mem_separatingBonds G ω x z e).mpr he,le_refl _⟩⟩

end BridgeCode

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


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

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



theorem exists_normalized_operator {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p (root i₀)) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A‖ ∧ ‖A‖ ≤ 1 ∧
      ∀ x y, A (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel (root i₀) p x y : ℂ) := by
  let u := q.successProbability p (root i₀)
  have hu₀ : u ≠ 0 := ne_of_gt hu
  have hn (x y : V) : 0 ≤ q.normalizedKernel (root i₀) p x y :=
    mul_nonneg (inv_nonneg.mpr hu.le) (q.kernel_nonneg p x y)
  have hr (x : V) (S : Finset V) : (∑ y ∈ S, q.normalizedKernel (root i₀) p x y) ≤ 1 := by
    change (∑ y ∈ S, u⁻¹ * q.kernel p x y) ≤ 1
    rw [← Finset.mul_sum]
    calc
      _ ≤ u⁻¹ * (∑' y, q.kernel p x y) := mul_le_mul_of_nonneg_left
        ((q.summable_kernel p x).sum_le_tsum S (fun y _ => q.kernel_nonneg p x y)) (inv_nonneg.mpr hu.le)
      _ ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left
        (q.kernel_row_le_success (root i₀) p x) (inv_nonneg.mpr hu.le)
      _ = 1 := inv_mul_cancel₀ hu₀
  have hc (y : V) (S : Finset V) : (∑ x ∈ S, q.normalizedKernel (root i₀) p x y) ≤ 1 := by
    change (∑ x ∈ S, u⁻¹ * q.kernel p x y) ≤ 1
    rw [← Finset.mul_sum]
    calc
      _ ≤ u⁻¹ * (∑' x, q.kernel p x y) := mul_le_mul_of_nonneg_left
        ((q.summable_kernel_column p y).sum_le_tsum S (fun x _ => q.kernel_nonneg p x y)) (inv_nonneg.mpr hu.le)
      _ ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left
        (q.kernel_column_le_success root weight Γ htr hΓ hw i₀ hw₀ p y) (inv_nonneg.mpr hu.le)
      _ = 1 := inv_mul_cancel₀ hu₀
  obtain ⟨A,hA,hK⟩ := exists_operator_of_row_column_bound (q.normalizedKernel (root i₀) p) 1 (by norm_num) hn hr hc
  refine ⟨A,?_,hA,hK⟩
  apply norm_pos_iff.mpr
  intro ha
  have hz (y : V) : q.kernel p (root i₀) y = 0 := by
    have h := hK (root i₀) y
    rw [ha] at h
    have he : u⁻¹ * q.kernel p (root i₀) y = 0 := Complex.ofReal_eq_zero.mp h.symm
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hu₀)
  have he : u = 0 := by simp only [u,successProbability,hz,tsum_zero]
  exact hu₀ he

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

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem kernel_finite_sum (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset
    q.kernel p x y = ∑ η : FiniteField Q, finiteFieldWeight Q p η * q.mass (finiteFieldSet Q η) x y :=
  integral_finite_local _ p (fun ω => q.mass ω x y) (fun ω => q.locality ω x y)

theorem continuous_kernel (q : LocalEndpointRule G hloc O M L) (x y : V) :
    Continuous (fun p : unitInterval => q.kernel p x y) := by
  simp_rw [q.kernel_finite_sum]
  apply continuous_finsetSum
  intro η _
  unfold finiteFieldWeight bernoulliWeight
  fun_prop

theorem continuous_successProbability (q : LocalEndpointRule G hloc O M L) (x : V) :
    Continuous (fun p : unitInterval => q.successProbability p x) := by
  have he (p : unitInterval) : q.successProbability p x =
      ∑ y ∈ (finite_reachBall hloc x M).toFinset, q.kernel p x y := by
    apply tsum_eq_sum
    intro y hy
    exact q.kernel_outside_ball_zero p x y (by simpa only [Set.Finite.mem_toFinset] using hy)
  simp_rw [he]
  exact continuous_finsetSum _ (fun y _ => q.continuous_kernel x y)

end LocalEndpointRule
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

theorem binSizeMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binSizeMass G n ω x = binSizeMass G n (ω ∩ (Q : Set E)) x := by
  dsimp only [binSizeMass]
  apply tsum_congr
  intro y
  exact binConnectionMass_local G hloc n ω x y

theorem binSizeMass_covariant (G : BondGraph V E) (n : ℕ) (ω : Set E)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    binSizeMass G n (b ⁻¹' ω) x = binSizeMass G n ω (a x) := by
  unfold binSizeMass
  rw [←a.tsum_eq (fun y => binConnectionMass G n ω (a x) y)]
  simp only [binConnectionMass_covariant G hab]

end BinOrbitRowMass

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

end AveragedBinOrbitTransport

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
section ShortBoundaryPivotal
attribute [local instance] Classical.propDecidable Classical.decEq



theorem bridgeIndex_le_short_trail (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) (e : E) (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (l : List E) (hl : Along G x l a)
    (ho : ∀ f ∈ l, f ∈ ω) : bridgeIndex G ω x z e ≤ l.length+1 := by
  unfold bridgeIndex
  have hsub : (separatingBonds G ω x z).filter (fun f => pivotalRank G ω x f ≤ pivotalRank G ω x e) ⊆
      (e::l).toFinset := by
    intro f hf
    obtain ⟨hf,hfe⟩ := Finset.mem_filter.mp hf
    have hfp := (mem_separatingBonds G ω x z f).mp hf
    by_cases h : f = e
    · subst f; simp
    by_contra hnot
    have hn : f ∉ l := fun hfl => hnot (List.mem_toFinset.mpr (List.mem_cons_of_mem _ hfl))
    have hlt : pivotalRank G ω x f < pivotalRank G ω x e := by
      apply lt_of_le_of_ne hfe
      intro heq
      exact h (pivotalRank_injective_of_cluster_finite G ω {z} x hC hfp he heq)
    have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC hfp he).mp hlt
    have hb : ¬ Conn G (ω \ {f}) x b := ((mem_internalEdges_of_ends G _ e a b hab).mp hout).2
    apply hb
    have hxa : Conn G (ω \ {f}) x a := hl.conn (fun g hg => ⟨ho g hg,fun hgf => hn ((Set.mem_singleton_iff.mp hgf) ▸ hg)⟩)
    exact hxa.tail ⟨e,⟨he.1,fun hEq => h hEq.symm⟩,hab⟩
  exact (Finset.card_le_card hsub).trans (by simpa only [List.length_cons] using List.toFinset_card_le (e::l))

theorem ShortClosedBoundary.open_pivotal (G : BondGraph V E) (ω : Set E) (x z : V)
    (M : ℕ) (e : E) (h : ShortClosedBoundary G ω x z M e) :
    OpenMarkedPivotal G (insert e ω) {z} x e := by
  obtain ⟨he,hxz,a,b,l,hab,hl,ho,_,hbz⟩ := h
  refine ⟨Set.mem_insert e ω,⟨z,rfl,?_⟩,?_⟩
  · have hxa := hl.conn ho
    exact (conn_mono G (Set.subset_insert e ω) hxa).trans
      ((Relation.ReflTransGen.single ⟨e,Set.mem_insert e ω,hab⟩).trans
        (conn_mono G (Set.subset_insert e ω) hbz))
  · rintro ⟨y,hy,hxy⟩
    have hy' : y = z := Set.mem_singleton_iff.mp hy
    subst y
    apply hxz
    apply conn_mono G _ hxy
    intro f hf
    rcases hf.1 with hfe | hfω
    · exact (hf.2 (Set.mem_singleton_iff.mpr hfe)).elim
    · exact hfω

theorem ShortClosedBoundary.bridgeIndex_le (G : BondGraph V E) (ω : Set E) (x z : V)
    (hω : ω.Finite) (M : ℕ) (e : E) (h : ShortClosedBoundary G ω x z M e) :
    bridgeIndex G (insert e ω) x z e ≤ M := by
  have hpiv := ShortClosedBoundary.open_pivotal G ω x z M e h
  obtain ⟨_,_,a,b,l,hab,hl,ho,hlen,_⟩ := h
  have hc := cluster_finite_of_finite_edges G (hω.insert e) x
  have hb := bridgeIndex_le_short_trail G (insert e ω) x z hc e hpiv
    a b hab l hl (fun f hf => Set.mem_insert_of_mem e (ho f hf))
  exact hb.trans (by omega)

end ShortBoundaryPivotal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryCounting
attribute [local instance] Classical.propDecidable Classical.decEq

theorem firstOpenBridgeCount_le (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (ω : Finset E) :
    firstOpenBridgeCount G Q x z M ω ≤ if Conn G ω x z then M else 0 := by
  by_cases hc : Conn G ω x z
  · rw [ite_eq_left hc]
    unfold firstOpenBridgeCount
    let S := Q.filter (fun e => OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M)
    have hm : Set.MapsTo (bridgeIndex G ω x z) (S : Set E) (Finset.Icc 1 M) := by
      intro e he
      have he' := (Finset.mem_filter.mp he).2
      exact Finset.mem_Icc.mpr ⟨bridgeIndex_pos G ω x z he'.1,he'.2⟩
    have hi : Set.InjOn (bridgeIndex G ω x z) (S : Set E) := by
      intro e he f hf h
      exact bridgeIndex_injective G ω x z (cluster_finite_of_finite_edges G ω.finite_toSet x)
        (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp hf).2.1 h
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using
      (Finset.card_le_card_of_injOn (bridgeIndex G ω x z) hm hi)
  · rw [ite_eq_right hc]
    unfold firstOpenBridgeCount
    have he : Q.filter (fun e => OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨y,hy,hxy⟩ := (Finset.mem_filter.mp he).2.1.2.1
      exact hc ((Set.mem_singleton_iff.mp hy) ▸ hxy)
    rw [he,Finset.card_empty]

theorem bernoulliPolynomial_bit_balance (Q : Finset E) (e : E) (he : e ∈ Q)
    (f : Finset E → ℝ) (p : ℝ) :
    p*bernoulliPolynomial Q (fun ω => if e ∉ ω then f ω else 0) p =
      (1-p)*bernoulliPolynomial Q (fun ω => if e ∈ ω then f (ω.erase e) else 0) p := by
  conv_lhs => rw [←Finset.insert_erase he]
  conv_rhs => rw [←Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q),
    bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
  have hc : bernoulliPolynomial (Q.erase e) (fun ω => if e ∉ ω then f ω else 0) p =
      bernoulliPolynomial (Q.erase e) f p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),not_false_eq_true,ite_true]
  have hco : bernoulliPolynomial (Q.erase e) (fun ω => if e ∉ insert e ω then f (insert e ω) else 0) p = 0 := by
    simp only [Finset.mem_insert_self,not_true_eq_false,ite_false,bernoulliPolynomial_zero]
  have ho : bernoulliPolynomial (Q.erase e) (fun ω => if e ∈ ω then f (ω.erase e) else 0) p = 0 := by
    calc
      _ = bernoulliPolynomial (Q.erase e) (fun _ => 0) p := by
        apply bernoulliPolynomial_congr
        intro ω hω
        simp only [show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),ite_false]
      _ = 0 := bernoulliPolynomial_zero _ _
  have hoo : bernoulliPolynomial (Q.erase e)
      (fun ω => if e ∈ insert e ω then f ((insert e ω).erase e) else 0) p =
      bernoulliPolynomial (Q.erase e) f p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [Finset.mem_insert_self,ite_true,Finset.erase_insert
      (show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h))]
  rw [hc,hco,ho,hoo]
  ring

end ShortBoundaryCounting

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryExpectation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem bernoulliPolynomial_closed_count_balance (Q : Finset E)
    (P : Finset E → E → Prop) (hP : ∀ ω e, P ω e → e ∉ ω) (p : ℝ) :
    p*bernoulliPolynomial Q (fun ω => ((Q.filter (P ω)).card:ℝ)) p =
      (1-p)*bernoulliPolynomial Q
        (fun ω => ((Q.filter (fun e => e ∈ ω ∧ P (ω.erase e) e)).card:ℝ)) p := by
  have hbal (e : E) (he : e ∈ Q) :
      p*bernoulliPolynomial Q (fun ω => if P ω e then 1 else 0) p =
        (1-p)*bernoulliPolynomial Q (fun ω => if e ∈ ω ∧ P (ω.erase e) e then 1 else 0) p := by
    have h := bernoulliPolynomial_bit_balance Q e he (fun ω => if P ω e then 1 else 0) p
    have hL : bernoulliPolynomial Q (fun ω => if e ∉ ω then (if P ω e then 1 else 0) else 0) p =
        bernoulliPolynomial Q (fun ω => if P ω e then 1 else 0) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      by_cases hp : P ω e
      · simp only [hp,hP ω e hp,not_false_eq_true,ite_true]
      · simp only [hp,ite_false,ite_self]
    have hR : bernoulliPolynomial Q (fun ω => if e ∈ ω then (if P (ω.erase e) e then 1 else 0) else 0) p =
        bernoulliPolynomial Q (fun ω => if e ∈ ω ∧ P (ω.erase e) e then 1 else 0) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      by_cases hm : e ∈ ω <;> simp only [hm,true_and,false_and,ite_true,ite_false]
    rw [hL,hR] at h
    exact h
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    bernoulliPolynomial_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e he => hbal e he)

theorem shortClosedBoundary_erase_first (G : BondGraph V E) (ω : Finset E)
    (x z : V) (M : ℕ) (e : E) (he : e ∈ ω)
    (h : ShortClosedBoundary G (ω.erase e) x z M e) :
    OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M := by
  have h₁ := ShortClosedBoundary.open_pivotal G (ω.erase e) x z M e h
  have h₂ := ShortClosedBoundary.bridgeIndex_le G (ω.erase e) x z (ω.erase e).finite_toSet M e h
  rw [←Finset.coe_insert,Finset.insert_erase he] at h₁ h₂
  exact ⟨h₁,h₂⟩

theorem shortRecoveredBoundaryCount_le (G : BondGraph V E) (Q ω : Finset E)
    (x z : V) (M : ℕ) :
    (Q.filter (fun e => e ∈ ω ∧ ShortClosedBoundary G (ω.erase e) x z M e)).card ≤
      if Conn G ω x z then M else 0 := by
  apply le_trans _ (firstOpenBridgeCount_le G Q x z M ω)
  apply Finset.card_le_card
  intro e he
  obtain ⟨heQ,heω,hb⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨heQ,shortClosedBoundary_erase_first G ω x z M e heω hb⟩

 

theorem finite_short_boundary_expectation (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    bernoulliPolynomial Q (fun ω => (shortClosedBoundaryCount G Q x z M ω:ℝ)) p ≤
      ((1-p)/p)*M*bernoulliPolynomial Q (fun ω => if Conn G ω x z then 1 else 0) p := by
  have hbal := bernoulliPolynomial_closed_count_balance Q
    (fun ω e => ShortClosedBoundary G ω x z M e) (fun ω e h => h.1) p
  have hmono := bernoulliPolynomial_mono Q
    (fun ω => ((Q.filter (fun e => e ∈ ω ∧ ShortClosedBoundary G (ω.erase e) x z M e)).card:ℝ))
    (fun ω => (M:ℝ)*(if Conn G ω x z then 1 else 0)) p ⟨hp.le,hp1⟩ (by
      intro ω _
      have h := shortRecoveredBoundaryCount_le G Q ω x z M
      by_cases hc : Conn G ω x z
      · simp only [hc,ite_true,mul_one] at *
        exact_mod_cast h
      · simp only [hc,ite_false,mul_zero] at *
        exact_mod_cast h)
  rw [bernoulliPolynomial_const_mul] at hmono
  have hbound := mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hp1)
  rw [←hbal] at hbound
  change p*bernoulliPolynomial Q (fun ω => (shortClosedBoundaryCount G Q x z M ω:ℝ)) p ≤ _ at hbound
  have hdiv := (le_div_iff₀ hp).mpr (show
      bernoulliPolynomial Q (fun ω => (shortClosedBoundaryCount G Q x z M ω:ℝ)) p*p ≤ _ by
        simpa only [mul_comm p] using hbound)
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hdiv

end ShortBoundaryExpectation

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClusterResampling
attribute [local instance] Classical.propDecidable Classical.decEq

theorem bernoulliPolynomial_commute {F : Type*} (Q : Finset E) (R : Finset F)
    (f : Finset E → Finset F → ℝ) (p q : ℝ) :
    bernoulliPolynomial Q (fun a => bernoulliPolynomial R (f a) q) p =
      bernoulliPolynomial R (fun b => bernoulliPolynomial Q (fun a => f a b) p) q := by
  simp only [bernoulliPolynomial,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem exteriorBonds_union_blocks (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (a b : Finset E) (ha : a ⊆ Q \ exteriorBonds G Q W)
    (hb : b ⊆ exteriorBonds G Q W) : exteriorBonds G (a ∪ b) W = b := by
  ext e
  simp only [exteriorBonds,Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨he,heW⟩
    rcases he with he | he
    · obtain ⟨heQ,heR⟩ := Finset.mem_sdiff.mp (ha he)
      exact (heR (Finset.mem_filter.mpr ⟨heQ,heW⟩)).elim
    · exact he
  · intro he
    exact ⟨Or.inr he,(Finset.mem_filter.mp (hb he)).2⟩

 
theorem cluster_cell_exterior_factor (G : BondGraph V E) (Q : Finset E)
    (x : V) (W : Set V) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial Q (fun ω =>
      (if cluster G ω x = W then (1:ℝ) else 0)*f (exteriorBonds G ω W)) p =
      bernoulliPolynomial (Q \ exteriorBonds G Q W)
        (fun a => if cluster G a x = W then (1:ℝ) else 0) p *
      bernoulliPolynomial (exteriorBonds G Q W) f p := by
  let R := exteriorBonds G Q W
  let A := Q \ R
  have hQ : A ∪ R = Q := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  conv_lhs => rw [←hQ,bernoulliPolynomial_union A R Finset.sdiff_disjoint]
  trans bernoulliPolynomial A (fun a =>
    (if cluster G a x = W then (1:ℝ) else 0)*bernoulliPolynomial R f p) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro b hb
    have hc := cluster_union_external_eq_iff G (a:Set E) b x W
      (fun e he => (Finset.mem_filter.mp (hb he)).2)
    rw [exteriorBonds_union_blocks G Q W a b ha hb]
    simp only [Finset.coe_union,hc]
  · exact bernoulliPolynomial_mul_const A _ _ p

theorem cluster_cell_incident_probability (G : BondGraph V E) (Q : Finset E)
    (x : V) (W : Set V) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => if cluster G ω x = W then (1:ℝ) else 0) p =
      bernoulliPolynomial (Q \ exteriorBonds G Q W)
        (fun a => if cluster G a x = W then (1:ℝ) else 0) p := by
  have h := cluster_cell_exterior_factor G Q x W (fun _ => 1) p
  simpa only [mul_one,bernoulliPolynomial_const] using h



theorem cluster_resample_cell_independent (G : BondGraph V E) (Q : Finset E)
    (x : V) (W : Set V) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q (fun η =>
      (if cluster G ω x = W then (1:ℝ) else 0)*f (resampleClusterAt G Q W ω η)) p) p =
      bernoulliPolynomial Q (fun ω => if cluster G ω x = W then (1:ℝ) else 0) p *
      bernoulliPolynomial Q f p := by
  let R := exteriorBonds G Q W
  let A := Q \ R
  let c := bernoulliPolynomial A (fun a => if cluster G a x = W then (1:ℝ) else 0) p
  rw [bernoulliPolynomial_commute]
  trans bernoulliPolynomial Q (fun η => c * bernoulliPolynomial R
    (fun b => f (b ∪ (η ∩ A))) p) p
  · apply bernoulliPolynomial_congr
    intro η _
    exact cluster_cell_exterior_factor G Q x W (fun b => f (b ∪ (η ∩ A))) p
  · rw [bernoulliPolynomial_const_mul,bernoulliPolynomial_restrict A Q Finset.sdiff_subset
      (fun a => bernoulliPolynomial R (fun b => f (b ∪ a)) p) p,
      bernoulliPolynomial_commute]
    have hQ : R ∪ A = Q := Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
    rw [←bernoulliPolynomial_union R A Finset.disjoint_sdiff,hQ,
      cluster_cell_incident_probability G Q x W p]

end ClusterResampling
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ResampledBoundary
attribute [local instance] Classical.propDecidable Classical.decEq

theorem resampleClusterAt_subset (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (ω η : Finset E) (hω : ω ⊆ Q) :
    resampleClusterAt G Q W ω η ⊆ Q := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hω (Finset.mem_filter.mp he).1
  · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1

theorem resampleClusterAt_external (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (ω η : Finset E) {e : E} (he : e ∈ resampleClusterAt G Q W ω η)
    (heW : e ∈ internalEdges G Wᶜ) : e ∈ ω := by
  rcases Finset.mem_union.mp he with he | he
  · exact (Finset.mem_filter.mp he).1
  · obtain ⟨_,heA⟩ := Finset.mem_inter.mp he
    obtain ⟨heQ,heR⟩ := Finset.mem_sdiff.mp heA
    exact (heR (Finset.mem_filter.mpr ⟨heQ,heW⟩)).elim

 

theorem resampled_path_boundary (G : BondGraph V E) (Q ω η : Finset E)
    (hω : ω ⊆ Q) (x z y : V) (M : ℕ)
    (hy : Conn G ω z y) (hx : ¬Conn G ω x z)
    (l : List E) (hl : Along G x l y) (hlen : l.length ≤ M)
    (ho : ∀ e ∈ l, e ∈ resampleClusterAt G Q (cluster G ω z) ω η) :
    ∃ e ∈ Q, ShortClosedBoundary G ω x z M e := by
  let W := cluster G ω z
  have hxW : x ∉ W := fun h => hx (conn_symm G ω h)
  rcases hl.first_outside (internalEdges G Wᶜ) with hall | ⟨a,b,e,l₁,l₂,heq,h₁,hab,_,hfirst,hen⟩
  · have hc : Conn G ((Set.univ:Set E) ∩ internalEdges G Wᶜ) x y :=
      hl.conn (fun e he => ⟨Set.mem_univ e,hall e he⟩)
    exact ((conn_internal_endpoint G Wᶜ hxW hc) hy).elim
  · subst l
    have heopen := ho e (List.mem_append_right _ (by simp))
    have heQ := resampleClusterAt_subset G Q W ω η hω heopen
    have hprefix : ∀ f ∈ l₁, f ∈ ω := by
      intro f hf
      exact resampleClusterAt_external G Q W ω η
        (ho f (List.mem_append_left _ hf)) (hfirst f hf)
    have hxa : Conn G ((ω:Set E) ∩ internalEdges G Wᶜ) x a :=
      h₁.conn (fun f hf => ⟨hprefix f hf,hfirst f hf⟩)
    have haW : a ∉ W := conn_internal_endpoint G Wᶜ hxW hxa
    have hbW : b ∈ W := by
      by_contra hbW
      exact hen ((mem_internalEdges_of_ends G Wᶜ e a b hab).mpr ⟨haW,hbW⟩)
    have heclosed : e ∉ ω := by
      intro heω
      apply haW
      exact (show Conn G ω z b from hbW).tail ⟨e,heω,hab.trans (Sym2.eq_swap ..)⟩
    refine ⟨e,heQ,heclosed,hx,a,b,l₁,hab,h₁,hprefix,?_,conn_symm G ω hbW⟩
    simp only [List.length_append,List.length_cons] at hlen
    omega


theorem resampled_hit_le_boundaryCount (G : BondGraph V E) (Q ω η : Finset E)
    (hω : ω ⊆ Q) (x z y : V) (M : ℕ)
    (hpath : ∃ l : List E, Along G x l y ∧ l.length ≤ M ∧
      ∀ e ∈ l, e ∈ resampleRootCluster G Q z ω η) :
    (if Conn G ω z y then (1:ℝ) else 0) ≤
      (if Conn G ω x z then (1:ℝ) else 0) + shortClosedBoundaryCount G Q x z M ω := by
  by_cases hy : Conn G ω z y
  · rw [ite_eq_left hy]
    by_cases hx : Conn G ω x z
    · rw [ite_eq_left hx]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · rw [ite_eq_right hx,zero_add]
      obtain ⟨l,hl,hlen,ho⟩ := hpath
      obtain ⟨e,heQ,he⟩ := resampled_path_boundary G Q ω η hω x z y M hy hx l hl hlen ho
      have hpos : 0 < shortClosedBoundaryCount G Q x z M ω :=
        Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨heQ,he⟩⟩
      exact_mod_cast hpos
  · rw [ite_eq_right hy]
    positivity

end ResampledBoundary
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RootResamplingLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem rootCluster_resampling_law (G : BondGraph V E) (Q : Finset E)
    (x : V) (f : Finset V → Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q
      (fun η => f (finiteRootComponent G ω x) (resampleRootCluster G Q x ω η)) p) p =
      bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q
        (f (finiteRootComponent G ω x)) p) p := by
  let F := insert x (searchVertices G Q)
  let c := fun (W : Finset V) (ω : Finset E) => if cluster G ω x = (W:Set V) then (1:ℝ) else 0
  have hpart (ω η : Finset E) (hω : ω ⊆ Q) :
      f (finiteRootComponent G ω x) (resampleRootCluster G Q x ω η) =
        ∑ W ∈ F.powerset, c W ω * f W (resampleClusterAt G Q W ω η) := by
    have h := sum_component_partition G Q F x ω hω (by rfl)
      (fun W => f W (resampleClusterAt G Q W ω η))
    simpa only [c,ite_mul,one_mul,zero_mul,coe_finiteRootComponent,
      resampleRootCluster] using h.symm
  trans ∑ W ∈ F.powerset,
    bernoulliPolynomial Q (c W) p * bernoulliPolynomial Q (f W) p
  · trans bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q (fun η =>
      ∑ W ∈ F.powerset, c W ω * f W (resampleClusterAt G Q W ω η)) p) p
    · apply bernoulliPolynomial_congr
      intro ω hω
      apply bernoulliPolynomial_congr
      intro η _
      exact hpart ω η hω
    · simp only [bernoulliPolynomial_sum]
      apply Finset.sum_congr rfl
      intro W _
      exact cluster_resample_cell_independent G Q x W (f W) p
  · trans bernoulliPolynomial Q (fun ω => ∑ W ∈ F.powerset,
      c W ω * bernoulliPolynomial Q (f W) p) p
    · rw [bernoulliPolynomial_sum]
      apply Finset.sum_congr rfl
      intro W _
      exact (bernoulliPolynomial_mul_const Q (c W) _ p).symm
    · apply bernoulliPolynomial_congr
      intro ω hω
      have h := sum_component_partition G Q F x ω hω (by rfl)
        (fun W => bernoulliPolynomial Q (f W) p)
      simpa only [c,ite_mul,one_mul,zero_mul] using h

end RootResamplingLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteMaximalSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootCluster_resampled_selector (G : BondGraph V E) (Q : Finset E)
    (w : V) (Z : Finset E → V) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q (fun η =>
      if Conn G ω w (Z (resampleRootCluster G Q w ω η)) then (1:ℝ) else 0) p) p =
      bernoulliPolynomial Q (fun η => bernoulliPolynomial Q (fun ω =>
        if Conn G ω w (Z η) then (1:ℝ) else 0) p) p := by
  have hm (ω : Finset E) (y : V) :
      y ∈ finiteRootComponent G ω w ↔ Conn G ω w y := by
    change y ∈ (finiteRootComponent G ω w : Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  have h := rootCluster_resampling_law G Q w (fun W η => if Z η ∈ W then (1:ℝ) else 0) p
  simp only [hm] at h
  exact h.trans (bernoulliPolynomial_commute Q Q _ p p)

theorem finite_selector_connection_bound (G : BondGraph V E) (Q : Finset E)
    (x w : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ Q, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    bernoulliPolynomial Q (fun η => bernoulliPolynomial Q (fun ω =>
      if Conn G ω w (Z η) then (1:ℝ) else 0) p) p ≤
      (1+(1-p)/p*M)*bernoulliPolynomial Q (fun ω => if Conn G ω x w then (1:ℝ) else 0) p := by
  rw [←rootCluster_resampled_selector G Q w Z p]
  have hmono := bernoulliPolynomial_mono Q
    (fun ω => bernoulliPolynomial Q (fun η =>
      if Conn G ω w (Z (resampleRootCluster G Q w ω η)) then (1:ℝ) else 0) p)
    (fun ω => (if Conn G ω x w then (1:ℝ) else 0)+shortClosedBoundaryCount G Q x w M ω)
    p ⟨hp.le,hp1⟩ (by
      intro ω hω
      calc
        _ ≤ bernoulliPolynomial Q (fun _ =>
          (if Conn G ω x w then (1:ℝ) else 0)+shortClosedBoundaryCount G Q x w M ω) p := by
            apply bernoulliPolynomial_mono Q _ _ p ⟨hp.le,hp1⟩
            intro η _
            exact resampled_hit_le_boundaryCount G Q ω η hω x w _ M
              (hZ _ (resampleClusterAt_subset G Q _ ω η hω))
        _ = _ := bernoulliPolynomial_const Q _ p)
  rw [bernoulliPolynomial_add] at hmono
  have hb := finite_short_boundary_expectation G Q x w M p hp hp1
  calc
    _ ≤ _ := hmono
    _ ≤ bernoulliPolynomial Q (fun ω => if Conn G ω x w then (1:ℝ) else 0) p +
      ((1-p)/p)*M*bernoulliPolynomial Q (fun ω => if Conn G ω x w then (1:ℝ) else 0) p :=
        add_le_add le_rfl hb
    _ = _ := by ring



end FiniteMaximalSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedConnectionLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem tendsto_bernoulliPolynomial {ι : Type*} {l : Filter ι}
    (Q : Finset E) (f : ι → Finset E → ℝ) (g : Finset E → ℝ) (p : ℝ)
    (h : ∀ a ⊆ Q, Tendsto (fun i => f i a) l (𝓝 (g a))) :
    Tendsto (fun i => bernoulliPolynomial Q (f i) p) l
      (𝓝 (bernoulliPolynomial Q g p)) := by
  unfold bernoulliPolynomial
  exact tendsto_finsetSum _ (fun a ha =>
    ((h a (Finset.mem_powerset.mp ha)).mul_const _).mul_const _)

theorem conn_finite_exhaustion (G : BondGraph V E) (S : Set E)
    (Q : ℕ → Finset E) (hQ : Monotone Q) (hcover : ∀ e ∈ S, ∃ n, e ∈ Q n)
    {ω : Set E} {x y : V} (h : Conn G (ω ∩ S) x y) :
    ∃ n, Conn G (ω ∩ (Q n : Set E)) x y := by
  induction h with
  | refl => exact ⟨0,conn_refl _ _ _⟩
  | @tail a b hxa hab ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨e,he,hab⟩ := hab
    obtain ⟨m,hm⟩ := hcover e he.2
    refine ⟨max n m,?_⟩
    exact (conn_mono G (Set.inter_subset_inter_right _
      (show (Q n:Set E) ⊆ (Q (max n m):Set E) from hQ (le_max_left n m))) hn).tail
      ⟨e,⟨he.1,hQ (le_max_right n m) hm⟩,hab⟩

theorem finite_connection_polynomial_tendsto (G : BondGraph V E) (S : Set E)
    (Q : ℕ → Finset E) (hQ : Monotone Q) (hsub : ∀ n, (Q n:Set E) ⊆ S)
    (hcover : ∀ e ∈ S, ∃ n, e ∈ Q n) (p : unitInterval) (x y : V) :
    Tendsto (fun n => bernoulliPolynomial (Q n) (fun ω => if Conn G ω x y then (1:ℝ) else 0) p)
      atTop (𝓝 ((law p).real {ω | Conn G (ω ∩ S) x y})) := by
  have he (n : ℕ) : bernoulliPolynomial (Q n) (fun ω => if Conn G ω x y then (1:ℝ) else 0) p =
      (law p).real {ω | Conn G (ω ∩ (Q n:Set E)) x y} :=
    finiteEventPolynomial_restrict (Q n) {ω | Conn G ω x y} p
  simp_rw [he]
  have hm : Monotone (fun n => {ω : Set E | Conn G (ω ∩ (Q n:Set E)) x y}) := by
    intro m n h ω hc
    exact conn_mono G (Set.inter_subset_inter_right _ (show (Q m:Set E) ⊆ (Q n:Set E) from hQ h)) hc
  have hu : (⋃ n, {ω : Set E | Conn G (ω ∩ (Q n:Set E)) x y}) =
      {ω : Set E | Conn G (ω ∩ S) x y} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,hn⟩ => conn_mono G (Set.inter_subset_inter_right _ (hsub n)) hn,
      conn_finite_exhaustion G S Q hQ hcover⟩
  have ht := tendsto_measure_iUnion_atTop (μ := law p) hm
  rw [hu] at ht
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht

theorem restrictedBondExhaustion_mono [Encodable E] (S : Set E) (K : Finset E) :
    Monotone (restrictedBondExhaustion S K) := by
  intro m n h
  exact Finset.union_subset_union (by rfl) (Finset.filter_subset_filter _ (vertexExhaustion_mono h))

theorem restrictedBondExhaustion_cover [Encodable E] (S : Set E) (K : Finset E)
    (e : E) (he : e ∈ S) : ∃ n, e ∈ restrictedBondExhaustion S K n := by
  obtain ⟨n,hn⟩ := subset_vertexExhaustion ({e}:Finset E)
  exact ⟨n,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn (by simp),he⟩)⟩

theorem restrictedBondExhaustion_subset [Encodable E] (S : Set E) (K : Finset E)
    (hK : (K:Set E) ⊆ S) (n : ℕ) : (restrictedBondExhaustion S K n:Set E) ⊆ S := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hK he
  · exact (Finset.mem_filter.mp he).2

end RestrictedConnectionLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedSelectorBound
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem restricted_selector_connection_bound [Countable E] (G : BondGraph V E)
    (S : Set E) (K : Finset E) (hK : (K:Set E) ⊆ S)
    (x w : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ K, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : unitInterval) (hp : 0 < (p:ℝ)) :
    bernoulliPolynomial K (fun η => (law p).real {ω | Conn G (ω ∩ S) w (Z η)}) p ≤
      (1+(1-(p:ℝ))/p*M)*(law p).real {ω | Conn G (ω ∩ S) x w} := by
  let := Encodable.ofCountable E
  let Q := restrictedBondExhaustion S K
  have hlim (a b : V) := finite_connection_polynomial_tendsto G S Q
    (restrictedBondExhaustion_mono S K) (restrictedBondExhaustion_subset S K hK)
    (restrictedBondExhaustion_cover S K) p a b
  have hleft := tendsto_bernoulliPolynomial K
    (fun n η => bernoulliPolynomial (Q n) (fun ω => if Conn G ω w (Z η) then (1:ℝ) else 0) p)
    (fun η => (law p).real {ω | Conn G (ω ∩ S) w (Z η)}) p (fun η _ => hlim w (Z η))
  have hright := (hlim x w).const_mul (1+(1-(p:ℝ))/p*M)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Eventually.of_forall
  intro n
  have hZQ : ∀ η ⊆ Q n, ∃ l : List E, Along G x l (Z (η ∩ K)) ∧
      l.length ≤ M ∧ ∀ e ∈ l, e ∈ η := by
    intro η _
    obtain ⟨l,hl,hlen,ho⟩ := hZ (η ∩ K) Finset.inter_subset_right
    exact ⟨l,hl,hlen,fun e he => (Finset.mem_inter.mp (ho e he)).1⟩
  have h := finite_selector_connection_bound G (Q n) x w M (fun η => Z (η ∩ K)) hZQ p hp p.2.2
  rw [bernoulliPolynomial_restrict K (Q n) Finset.subset_union_left
    (fun η => bernoulliPolynomial (Q n) (fun ω => if Conn G ω w (Z η) then (1:ℝ) else 0) p) p] at h
  exact h

theorem restrictedTwoPoint_le (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x y : V) :
    (law p).real {ω | Conn G (ω ∩ S) x y} ≤ twoPoint G p x y := by
  exact measureReal_mono (fun _ h => conn_mono G Set.inter_subset_left h)

theorem summable_restrictedTwoPoint [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (S : Set E) (x : V) :
    Summable (fun y => (law p).real {ω | Conn G (ω ∩ S) x y}) := by
  obtain ⟨C,_,hC⟩ := subcritical_row_bound G hloc hqt p hp
  apply summable_of_sum_le (fun _ => measureReal_nonneg)
  intro F
  exact (Finset.sum_le_sum (fun y _ => restrictedTwoPoint_le G S p x y)).trans (hC x F)

end RestrictedSelectorBound
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section SelectorSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_bernoulliPolynomial {A : Type*} (K : Finset E)
    (f : Finset E → A → ℝ) (p : ℝ) (hf : ∀ η ⊆ K, Summable (f η)) :
    Summable (fun y => bernoulliPolynomial K (fun η => f η y) p) := by
  unfold bernoulliPolynomial
  apply summable_sum
  intro η hη
  exact ((hf η (Finset.mem_powerset.mp hη)).mul_right _).mul_right _

theorem bernoulliPolynomial_tsum {A : Type*} (K : Finset E)
    (f : Finset E → A → ℝ) (p : ℝ) (hf : ∀ η ⊆ K, Summable (f η)) :
    bernoulliPolynomial K (fun η => ∑' y, f η y) p =
      ∑' y, bernoulliPolynomial K (fun η => f η y) p := by
  unfold bernoulliPolynomial
  rw [Summable.tsum_finsetSum (fun η hη =>
    ((hf η (Finset.mem_powerset.mp hη)).mul_right _).mul_right _)]
  apply Finset.sum_congr rfl
  intro η _
  rw [tsum_mul_right,tsum_mul_right]

theorem restrictedTwoPoint_symm (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x y : V) :
    (law p).real {ω | Conn G (ω ∩ S) x y} =
      (law p).real {ω | Conn G (ω ∩ S) y x} := by
  congr 1
  ext ω
  exact ⟨conn_symm G _,conn_symm G _⟩

 

theorem restricted_selected_susceptibility_bound [Countable E] (G : BondGraph V E)
    (S : Set E) (K : Finset E) (hK : (K:Set E) ⊆ S)
    (x : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ K, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) y z})) :
    bernoulliPolynomial K (fun η => restrictedSusceptibility G S p (Z η)) p ≤
      (1+(1-(p:ℝ))/p*M)*restrictedSusceptibility G S p x := by
  unfold restrictedSusceptibility
  rw [bernoulliPolynomial_tsum K _ p (fun η _ => hfin (Z η)),←tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_bernoulliPolynomial K _ p (fun η _ => hfin (Z η)))
    ((hfin x).mul_left _)
  intro w
  have h := restricted_selector_connection_bound G S K hK x w M Z hZ p hp
  simpa only [restrictedTwoPoint_symm G S p (Z _) w] using h

 

theorem subcritical_selected_susceptibility_bound
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (S : Set E) (K : Finset E) (hK : (K:Set E) ⊆ S)
    (x : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ K, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G) :
    bernoulliPolynomial K (fun η => restrictedSusceptibility G S p (Z η)) p ≤
      (1+(1-(p:ℝ))/p*M)*restrictedSusceptibility G S p x :=
  restricted_selected_susceptibility_bound G S K hK x M Z hZ p hp
    (summable_restrictedTwoPoint G hloc hqt p hpc S)

end SelectorSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicBall
attribute [local instance] Classical.propDecidable Classical.decEq


theorem intrinsicBall_mono (G : BondGraph V E) {ω η : Set E} (h : ω ⊆ η) (x : V) (M : ℕ) :
    intrinsicBall G ω x M ⊆ intrinsicBall G η x M := by
  rintro y ⟨l,hl,hlen,ho⟩
  exact ⟨l,hl,hlen,fun e he => h (ho e he)⟩

theorem Along.bonds_in_incidentBall {G : BondGraph V E} (hloc : LocallyFinite G)
    {x y : V} {l : List E} (h : Along G x l y) (M : ℕ) (hlen : l.length ≤ M) :
    ∀ e ∈ l, e ∈ incidentSupport G hloc (finite_reachBall hloc x M).toFinset := by
  rcases h.first_outside (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E)
    with h | ⟨a,b,e,l₁,l₂,heq,h₁,he,_,_,hnot⟩
  · exact h
  · exfalso
    apply hnot
    apply (mem_incidentSupport G hloc _ e).mpr
    refine ⟨a,?_,by simp [he]⟩
    apply (finite_reachBall hloc x M).mem_toFinset.mpr
    apply reachBall_mono G x (show l₁.length ≤ M by subst l; simp only [List.length_append,List.length_cons] at hlen; omega)
    exact h₁.mem_reachBall

theorem intrinsicBall_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E)) x M =
      intrinsicBall G ω x M := by
  apply Set.Subset.antisymm (intrinsicBall_mono G Set.inter_subset_left x M)
  rintro y ⟨l,hl,hlen,ho⟩
  exact ⟨l,hl,hlen,fun e he => ⟨ho e he,hl.bonds_in_incidentBall hloc M hlen e he⟩⟩

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
section IntrinsicMaximum
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicMaximizer_spec (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    intrinsicMaximizer G hloc ω x M f ∈ intrinsicBall G ω x M ∧
      ∀ y ∈ intrinsicBall G ω x M, f y ≤ f (intrinsicMaximizer G hloc ω x M f) :=
  Classical.choose_spec (intrinsicBall_exists_max G hloc ω x M f)

theorem intrinsicPotentialMax_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    intrinsicPotentialMax G ω x M f = f (intrinsicMaximizer G hloc ω x M f) := by
  have h := intrinsicMaximizer_spec G hloc ω x M f
  apply IsGreatest.csSup_eq
  exact ⟨⟨_,h.1,rfl⟩,fun _ ⟨y,hy,he⟩ => he ▸ h.2 y hy⟩

theorem le_intrinsicPotentialMax (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) (y : V) (hy : y ∈ intrinsicBall G ω x M) :
    f y ≤ intrinsicPotentialMax G ω x M f := by
  rw [intrinsicPotentialMax_eq G hloc]
  exact (intrinsicMaximizer_spec G hloc ω x M f).2 y hy

theorem intrinsicBondSupport_coe (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (M : ℕ) :
    (intrinsicBondSupport G hloc S x M : Set E) =
      (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) ∩ S := by
  ext e
  simp [intrinsicBondSupport]

theorem intrinsicBall_domain_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (S ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G (ω ∩ (intrinsicBondSupport G hloc S x M : Set E)) x M =
      intrinsicBall G (ω ∩ S) x M := by
  rw [intrinsicBondSupport_coe]
  have he : ω ∩ ((incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) ∩ S) =
      (ω ∩ S) ∩ (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) := by
    ext e; simp [and_left_comm,and_comm,and_assoc]
  rw [he,intrinsicBall_restrict G hloc]

theorem intrinsicPotentialMax_domain_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (S ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    intrinsicPotentialMax G (ω ∩ S) x M f =
      intrinsicPotentialMax G ((ω ∩ (intrinsicBondSupport G hloc S x M : Set E)) ∩ S) x M f := by
  have hsub : (intrinsicBondSupport G hloc S x M : Set E) ⊆ S := by
    rw [intrinsicBondSupport_coe]; exact Set.inter_subset_right
  rw [Set.inter_assoc,Set.inter_eq_left.mpr hsub]
  unfold intrinsicPotentialMax
  rw [intrinsicBall_domain_restrict G hloc]

end IntrinsicMaximum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section MaximalSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem maximal_restricted_susceptibility_bound
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (S : Set E) (x : V) (M : ℕ) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hpc : p < pc G) :
    (∫ ω, intrinsicPotentialMax G (ω ∩ S) x M (restrictedSusceptibility G S p) ∂law p) ≤
      (1+(1-(p:ℝ))/p*M)*restrictedSusceptibility G S p x := by
  let K := intrinsicBondSupport G hloc S x M
  let f := restrictedSusceptibility G S p
  let Z : Finset E → V := fun η => intrinsicMaximizer G hloc η x M f
  have hK : (K:Set E) ⊆ S := by
    rw [intrinsicBondSupport_coe]; exact Set.inter_subset_right
  rw [integral_eq_bernoulliPolynomial K p _ (fun ω =>
    intrinsicPotentialMax_domain_local G hloc S ω x M f)]
  have he : bernoulliPolynomial K (fun η => intrinsicPotentialMax G ((η:Set E) ∩ S) x M f) p =
      bernoulliPolynomial K (fun η => f (Z η)) p := by
    apply bernoulliPolynomial_congr K _ p
    intro η hη
    rw [Set.inter_eq_left.mpr (fun e he => hK (hη he))]
    exact intrinsicPotentialMax_eq G hloc η x M f
  rw [he]
  apply subcritical_selected_susceptibility_bound G hloc hqt S K hK x M Z _ p hp hpc
  intro η _
  exact (intrinsicMaximizer_spec G hloc η x M f).1



theorem intrinsicBall_internal_subset (G : BondGraph V E) (D : Set V)
    (ω : Set E) (x : V) (hx : x ∈ D) (M : ℕ) :
    intrinsicBall G (ω ∩ internalEdges G D) x M ⊆ D := by
  rintro y ⟨l,hl,_,ho⟩
  exact conn_internal_endpoint G D hx (hl.conn ho)

theorem inducedSusceptibility_max_eq (G : BondGraph V E) (D : Set V)
    (ω : Set E) (p : unitInterval) (x : V) (hx : x ∈ D) (M : ℕ) :
    intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (inducedSusceptibility G D p) =
      intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (restrictedSusceptibility G (internalEdges G D) p) := by
  unfold intrinsicPotentialMax
  congr 1
  apply Set.image_congr
  intro y hy
  exact ite_eq_left (intrinsicBall_internal_subset G D ω x hx M hy)

 

theorem maximal_induced_susceptibility_bound
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (D : Set V) (x : V) (hx : x ∈ D) (M : ℕ) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hpc : p < pc G) :
    (∫ ω, intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (inducedSusceptibility G D p) ∂law p) ≤
      (1+(1-(p:ℝ))/p*M)*inducedSusceptibility G D p x := by
  simp_rw [inducedSusceptibility_max_eq G D _ p x hx M]
  rw [inducedSusceptibility,ite_eq_left hx]
  exact maximal_restricted_susceptibility_bound G hloc hqt (internalEdges G D) x M p hp hpc

end MaximalSusceptibility
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

theorem restrictedTwoPoint_path_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S) (z : V) :
    (p:ℝ)^l.length*(law p).real {ω | Conn G (ω ∩ S) y z} ≤
      (law p).real {ω | Conn G (ω ∩ S) x z} := by
  induction hl with
  | nil => simp
  | @cons x a y l e he ht ih =>
    have hh := mul_le_mul_of_nonneg_left (ih (fun d hd => hS d (List.mem_cons_of_mem _ hd))) p.2.1
    have ha := restrictedTwoPoint_adj_lower G S p x a z e he (hS e (by simp))
    simpa only [List.length_cons,pow_succ',mul_assoc] using hh.trans ha

theorem restrictedSusceptibility_nonneg (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x : V) : 0 ≤ restrictedSusceptibility G S p x :=
  tsum_nonneg (fun _ => measureReal_nonneg)

theorem restrictedSusceptibility_path_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S)
    (hfin : ∀ a, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) a z})) :
    (p:ℝ)^l.length*restrictedSusceptibility G S p y ≤ restrictedSusceptibility G S p x := by
  unfold restrictedSusceptibility
  rw [←tsum_mul_left]
  exact ((hfin y).mul_left _).tsum_le_tsum (restrictedTwoPoint_path_lower G S p hl hS) (hfin x)

 

theorem restrictedSusceptibility_short_path_bound [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) (hp : 0 < (p:ℝ)) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S) (M : ℕ) (hlen : l.length ≤ M)
    (hfin : ∀ a, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) a z})) :
    restrictedSusceptibility G S p y ≤ (p:ℝ)^(-(M:ℤ))*restrictedSusceptibility G S p x := by
  have hh := restrictedSusceptibility_path_lower G S p hl hS hfin
  have hpow : (p:ℝ)^M ≤ (p:ℝ)^l.length :=
    pow_le_pow_of_le_one p.2.1 p.2.2 hlen
  have hbound := (mul_le_mul_of_nonneg_right hpow (restrictedSusceptibility_nonneg G S p y)).trans hh
  rw [zpow_neg,zpow_natCast,←div_eq_inv_mul]
  exact (le_div_iff₀ (pow_pos hp M)).mpr (by simpa only [mul_comm] using hbound)

end RestrictedPathPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortPathsDeletedDomain
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_short_of_cluster_cap (G : BondGraph V E) (ω : Set E) (x y : V)
    (hxy : Conn G ω x y) (hfin : (cluster G ω x).Finite)
    (M : ℕ) (hM : (cluster G ω x).ncard ≤ M) :
    ∃ l : List E, Along G x l y ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ ω := by
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp hxy
  let q := w.toPath
  have hs : q.val.support.toFinset ⊆ hfin.toFinset := by
    intro z hz
    have hz' : z ∈ q.val.support := List.mem_toFinset.mp hz
    exact hfin.mem_toFinset.mpr ((conn_iff_reachable G ω x z).mpr ⟨q.val.takeUntil z hz'⟩)
  have hc : q.val.length+1 ≤ (cluster G ω x).ncard := by
    have hc := Finset.card_le_card hs
    rwa [List.toFinset_card_of_nodup q.property.support_nodup,
      SimpleGraph.Walk.length_support,←Set.ncard_eq_toFinset_card _ hfin] at hc
  obtain ⟨l,hl,he,ho⟩ := walk_lift_bonds G ω q.val
  have hlen : l.length = q.val.length := by
    have hh := congrArg List.length he
    simpa only [List.length_map,SimpleGraph.Walk.length_edges] using hh
  exact ⟨l,hl,by omega,ho⟩

 

theorem Along.last_entrance {G : BondGraph V E} {x y : V} {l : List E}
    (hl : Along G x l y) (D : Set V) (hy : y ∈ D) :
    (x ∈ D ∧ ∀ e ∈ l, e ∈ internalEdges G D) ∨
      ∃ a b e l₁ l₂, l = l₁ ++ e::l₂ ∧ Along G x l₁ a ∧ G e = s(a,b) ∧
        a ∉ D ∧ b ∈ D ∧ Along G b l₂ y ∧ ∀ d ∈ l₂, d ∈ internalEdges G D := by
  induction hl with
  | nil => exact Or.inl ⟨hy,by simp⟩
  | @cons x z y l e he ht ih =>
    rcases ih hy with ⟨hz,hall⟩ | ⟨a,b,d,l₁,l₂,heq,h₁,hd,ha,hb,h₂,hs⟩
    · by_cases hx : x ∈ D
      · left
        refine ⟨hx,?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact (mem_internalEdges_of_ends G D d x z he).mpr ⟨hx,hz⟩
        · exact hall d hd
      · right
        exact ⟨x,z,e,[],l,rfl,.nil x,he,hx,hz,ht,hall⟩
    · right
      exact ⟨a,b,d,e::l₁,l₂,by simp [heq],.cons e he h₁,hd,ha,hb,h₂,hs⟩

end ShortPathsDeletedDomain
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
section DeletedDomainPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem inducedSusceptibility_nonneg (G : BondGraph V E) (D : Set V)
    (p : unitInterval) (x : V) : 0 ≤ inducedSusceptibility G D p x := by
  unfold inducedSusceptibility
  split_ifs
  · exact restrictedSusceptibility_nonneg G _ p x
  · rfl

theorem deletedBoundaryPotential_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) :
    0 ≤ deletedBoundaryPotential G hloc D p x M := by
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => inducedSusceptibility_nonneg G D p b))

theorem le_deletedBoundaryPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) (a b : V)
    (ha : a ∈ reachBall G x M) (haD : a ∉ D) (hab : Adj G a b) :
    inducedSusceptibility G D p b ≤ deletedBoundaryPotential G hloc D p x M := by
  apply le_trans (Finset.single_le_sum (fun z _ => inducedSusceptibility_nonneg G D p z)
    ((mem_neighbors G hloc a b).mpr hab))
  apply Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun y _ => inducedSusceptibility_nonneg G D p y))
  exact Finset.mem_filter.mpr ⟨(finite_reachBall hloc x M).mem_toFinset.mpr ha,haD⟩

theorem deletedLocalPotential_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (ω : Set E) (x : V) (M : ℕ) :
    0 ≤ deletedLocalPotential G D p ω x M := by
  unfold deletedLocalPotential
  split_ifs
  · rw [intrinsicPotentialMax_eq G hloc]
    exact inducedSusceptibility_nonneg G D p _
  · rfl

 

theorem short_path_deleted_potential_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : Set V)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (ω : Set E) (x y : V) (M : ℕ)
    (l : List E) (hl : Along G x l y) (hlen : l.length ≤ M) (ho : ∀ e ∈ l, e ∈ ω)
    (hfin : ∀ a, Summable (fun z => (law p).real {η | Conn G (η ∩ internalEdges G D) a z})) :
    inducedSusceptibility G D p y ≤ deletedLocalPotential G D p ω x M +
      (p:ℝ)^(-(M:ℤ))*deletedBoundaryPotential G hloc D p x M := by
  have hpM : 0 ≤ (p:ℝ)^(-(M:ℤ)) := zpow_nonneg p.2.1 _
  have hn := deletedLocalPotential_nonneg G hloc D p ω x M
  have hb := deletedBoundaryPotential_nonneg G hloc D p x M
  by_cases hy : y ∈ D
  · rcases hl.last_entrance D hy with ⟨hx,hall⟩ | ⟨a,b,e,l₁,l₂,heq,h₁,he,ha,hbD,h₂,hs⟩
    · have hreach : y ∈ intrinsicBall G (ω ∩ internalEdges G D) x M :=
        ⟨l,hl,hlen,fun e he => ⟨ho e he,hall e he⟩⟩
      have hh := le_intrinsicPotentialMax G hloc _ x M (inducedSusceptibility G D p) y hreach
      change _ ≤ (if x ∈ D then _ else 0) + _
      rw [ite_eq_left hx]
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg hpM hb))
    · have hlen₂ : l₂.length ≤ M := by subst l; simp only [List.length_append,List.length_cons] at hlen; omega
      have hpath := restrictedSusceptibility_short_path_bound G (internalEdges G D) p hp h₂ hs M hlen₂ hfin
      have hχ : inducedSusceptibility G D p y ≤ (p:ℝ)^(-(M:ℤ))*inducedSusceptibility G D p b := by
        simpa only [inducedSusceptibility,ite_eq_left hy,ite_eq_left hbD] using hpath
      have haBall : a ∈ reachBall G x M := reachBall_mono G x
        (show l₁.length ≤ M by subst l; simp only [List.length_append,List.length_cons] at hlen; omega) h₁.mem_reachBall
      exact hχ.trans ((mul_le_mul_of_nonneg_left
        (le_deletedBoundaryPotential G hloc D p x M a b haBall ha ⟨e,he⟩) hpM).trans
          (le_add_of_nonneg_left hn))
  · rw [inducedSusceptibility,ite_eq_right hy]
    exact add_nonneg hn (mul_nonneg hpM hb)

end DeletedDomainPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalKernelAction
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem summable_mass_action (q : LocalEndpointRule G hloc O M L)
    (ω : Set E) (x : V) (f : V → ℝ) : Summable (fun y => q.mass ω x y * f y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  rw [q.outside_ball_zero ω x y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul]

theorem integrable_mass_action (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x : V) (f : V → ℝ) :
    Integrable (fun ω => ∑' y, q.mass ω x y * f y) (law p) := by
  apply integrable_finite_local (incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset) p
  intro ω
  exact tsum_congr (fun y => congrArg (· * f y) (q.locality ω x y))

theorem kernel_action_integral (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x : V) (f : V → ℝ) :
    (∑' y, q.kernel p x y * f y) = ∫ ω, (∑' y, q.mass ω x y * f y) ∂law p := by
  let B := (finite_reachBall hloc x M).toFinset
  have h₁ : (∑' y, q.kernel p x y*f y) = ∑ y ∈ B, q.kernel p x y*f y :=
    tsum_eq_sum fun y hy => by
      rw [q.kernel_outside_ball_zero p x y (by simpa only [B,Set.Finite.mem_toFinset] using hy),zero_mul]
  have h₂ (ω : Set E) : (∑' y, q.mass ω x y*f y) = ∑ y ∈ B, q.mass ω x y*f y :=
    tsum_eq_sum fun y hy => by
      rw [q.outside_ball_zero ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy),zero_mul]
  rw [h₁]
  simp_rw [h₂]
  rw [integral_finsetSum B (fun y _ => (q.integrable_mass p x y).mul_const (f y))]
  apply Finset.sum_congr rfl
  intro y _
  exact (integral_mul_const (f y) (fun ω => q.mass ω x y)).symm

theorem mass_action_le (q : LocalEndpointRule G hloc O M L)
    (ω : Set E) (x : V) (f : V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ y, q.mass ω x y ≠ 0 → f y ≤ C) :
    (∑' y, q.mass ω x y * f y) ≤ C := by
  calc
    _ ≤ ∑' y, q.mass ω x y * C := by
      apply (q.summable_mass_action ω x f).tsum_le_tsum _ ((q.summable_mass ω x).mul_right C)
      intro y
      by_cases h : q.mass ω x y = 0
      · simp only [h,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hf y h) (q.nonneg ω x y)
    _ = (∑' y, q.mass ω x y)*C := tsum_mul_right
    _ ≤ C := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (q.row_le_one ω x) hC

end LocalEndpointRule
end LocalKernelAction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalMapDeletedPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_deletedLocalPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) :
    Integrable (fun ω => deletedLocalPotential G D p ω x M) (law p) := by
  by_cases hx : x ∈ D
  · simp only [deletedLocalPotential,ite_eq_left hx]
    exact integrable_finite_local _ p _ (fun ω =>
      intrinsicPotentialMax_domain_local G hloc (internalEdges G D) ω x M (inducedSusceptibility G D p))
  · simp only [deletedLocalPotential,ite_eq_right hx]
    exact integrable_const 0

theorem integral_deletedLocalPotential_le
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (D : Set V) (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G) (x : V) (M : ℕ) :
    (∫ ω, deletedLocalPotential G D p ω x M ∂law p) ≤
      (1+(1-(p:ℝ))/p*M)*inducedSusceptibility G D p x := by
  by_cases hx : x ∈ D
  · simp only [deletedLocalPotential,ite_eq_left hx]
    exact maximal_induced_susceptibility_bound G hloc hqt D x hx M p hp hpc
  · simp only [deletedLocalPotential,inducedSusceptibility,ite_eq_right hx,integral_zero,mul_zero,le_refl]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem kernel_deleted_potential_bound
    [Countable V] [Countable E] [Nonempty V]
    (q : LocalEndpointRule G hloc O M L) (hqt : QuasiTransitive G)
    (D : Set V) (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G) (x : V) :
    (∑' y, q.kernel p x y * inducedSusceptibility G D p y) ≤
      (1+(1-(p:ℝ))/p*M)*inducedSusceptibility G D p x +
        (p:ℝ)^(-(M:ℤ))*deletedBoundaryPotential G hloc D p x M := by
  let f := inducedSusceptibility G D p
  let C := (p:ℝ)^(-(M:ℤ))*deletedBoundaryPotential G hloc D p x M
  have hC : 0 ≤ C := mul_nonneg (zpow_nonneg p.2.1 _) (deletedBoundaryPotential_nonneg G hloc D p x M)
  have hpoint (ω : Set E) : (∑' y, q.mass ω x y * f y) ≤ deletedLocalPotential G D p ω x M + C := by
    apply q.mass_action_le ω x f _ (add_nonneg (deletedLocalPotential_nonneg G hloc D p ω x M) hC)
    intro y hy
    obtain ⟨_,_,hxy,hfin,hcap,_⟩ := q.support ω x y hy
    obtain ⟨l,hl,hlen,ho⟩ := conn_short_of_cluster_cap G ω x y hxy hfin M hcap
    exact short_path_deleted_potential_bound G hloc D p hp ω x y M l hl hlen ho
      (summable_restrictedTwoPoint G hloc hqt p hpc (internalEdges G D))
  rw [q.kernel_action_integral]
  have hi := integrable_deletedLocalPotential G hloc D p x M
  calc
    _ ≤ ∫ ω, deletedLocalPotential G D p ω x M + C ∂law p :=
      integral_mono (q.integrable_mass_action p x f) (hi.add (integrable_const C)) hpoint
    _ = (∫ ω, deletedLocalPotential G D p ω x M ∂law p) + C := by
      rw [integral_add hi (integrable_const C)]; simp
    _ ≤ _ := by
      have hh := integral_deletedLocalPotential_le G hloc hqt D p hp hpc x M
      dsimp [C]
      linarith

end LocalEndpointRule
end LocalMapDeletedPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OrbitKernelTransport
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem orbit_kernel_column_eq_row
    (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀) (K : V → V → ℝ)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y)
    (hout : ∀ x y, x ∉ vertexOrbit G (root i₀) → K x y = 0)
    (hin : ∀ x y, y ∉ vertexOrbit G (root i₀) → K x y = 0)
    (hr : ∀ x, Summable (K x)) (hc : ∀ y, Summable (fun x => K x y))
    (y : V) (hy : y ∈ vertexOrbit G (root i₀)) :
    (∑' x, K x y) = ∑' z, K (root i₀) z := by
  let O := vertexOrbit G (root i₀)
  let w : ι → ℝ := fun i => if root i ∈ O then weight i else 0
  have hrow (x : V) (hx : x ∈ O) : (∑' z, K x z) = ∑' z, K (root i₀) z := by
    obtain ⟨a,b,ha,rfl⟩ := hx
    rw [← a.tsum_eq (fun z => K (a (root i₀)) z)]
    exact tsum_congr (hcov a b ha (root i₀))
  have hcol (x : V) (hx : x ∈ O) : (∑' z, K z x) = ∑' z, K z (root i₀) := by
    obtain ⟨a,b,ha,rfl⟩ := hx
    rw [← a.tsum_eq (fun z => K z (a (root i₀)))]
    exact tsum_congr (fun z => hcov a b ha z (root i₀))
  have ho : root i₀ ∈ O := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e; simp
  have hw' (i : ι) : 0 ≤ w i := by
    dsimp [w]; split_ifs
    · exact hw i
    · rfl
  have hpos : 0 < ∑ i, w i := by
    have hi := Finset.single_le_sum (fun i _ => hw' i) (Finset.mem_univ i₀)
    have he : w i₀ = weight i₀ := ite_eq_left ho
    rw [he] at hi
    exact hw₀.trans_le hi
  have ht := htr.real root weight Γ K
    (by intro a ha x z; obtain ⟨b,hb⟩ := hΓ a ha; exact hcov a b hb x z) hr hc
  have h₁ (i : ι) : weight i * (∑' z, K (root i) z) = w i * (∑' z, K (root i₀) z) := by
    by_cases hi : root i ∈ O
    · rw [hrow (root i) hi]; simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' z, K (root i) z) = 0 := by simp only [hout _ _ hi,tsum_zero]
      rw [he,mul_zero]
  have h₂ (i : ι) : weight i * (∑' z, K z (root i)) = w i * (∑' z, K z (root i₀)) := by
    by_cases hi : root i ∈ O
    · rw [hcol (root i) hi]; simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' z, K z (root i)) = 0 := by simp only [hin _ _ hi,tsum_zero]
      rw [he,mul_zero]
  simp_rw [h₁,h₂] at ht
  rw [← Finset.sum_mul,← Finset.sum_mul] at ht
  rw [hcol y hy]
  exact (mul_left_cancel₀ (ne_of_gt hpos) ht).symm

 

theorem operator_norm_le_absolute_sums (K : V → V → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hr : ∀ x (S : Finset V), (∑ y ∈ S, |K x y|) ≤ D)
    (hc : ∀ y (S : Finset V), (∑ x ∈ S, |K x y|) ≤ D)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) : ‖A‖ ≤ D := by
  obtain ⟨B,hBn,hB⟩ := exists_operator_of_row_column_bound (fun x y => |K x y|) D hD
    (fun _ _ => abs_nonneg _) hr hc
  obtain ⟨A',hAn,hA'⟩ := exists_operator_of_matrix_domination
    (fun x y => |K x y|) K (fun _ _ => abs_nonneg _) (fun _ _ => le_rfl) B hB
  have he := kernel_extension_unique hA hA'
  rw [he]
  exact hAn.trans hBn

end OrbitKernelTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointDifference
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)

theorem kernelDifference_nonneg (p r : unitInterval) (x y : V) :
    0 ≤ q.kernelDifference o p r x y := abs_nonneg _

theorem kernelDifference_covariant (p r : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (x y : V) :
    q.kernelDifference o p r (a x) (a y) = q.kernelDifference o p r x y := by
  simp only [kernelDifference,normalizedKernel,q.kernel_covariant p a b ha,q.kernel_covariant r a b ha]

theorem kernelDifference_outside (p r : unitInterval) (x y : V) (hy : y ∉ reachBall G x M) :
    q.kernelDifference o p r x y = 0 := by
  simp only [kernelDifference,normalizedKernel,q.kernel_outside_ball_zero p x y hy,
    q.kernel_outside_ball_zero r x y hy,mul_zero,sub_self,abs_zero]

theorem kernelDifference_reverse_outside (p r : unitInterval) (x y : V) (hx : x ∉ reachBall G y M) :
    q.kernelDifference o p r x y = 0 := by
  simp only [kernelDifference,normalizedKernel,q.kernel_outside_reverse_ball_zero p x y hx,
    q.kernel_outside_reverse_ball_zero r x y hx,mul_zero,sub_self,abs_zero]

theorem kernelDifference_start (p r : unitInterval) (x y : V) (hx : x ∉ vertexOrbit G o) :
    q.kernelDifference o p r x y = 0 := by
  simp only [kernelDifference,normalizedKernel,q.kernel_zero_of_start_not_mem p x y hx,
    q.kernel_zero_of_start_not_mem r x y hx,mul_zero,sub_self,abs_zero]

theorem kernelDifference_end (p r : unitInterval) (x y : V) (hy : y ∉ vertexOrbit G o) :
    q.kernelDifference o p r x y = 0 := by
  simp only [kernelDifference,normalizedKernel,q.kernel_zero_of_end_not_mem p x y hy,
    q.kernel_zero_of_end_not_mem r x y hy,mul_zero,sub_self,abs_zero]

theorem summable_kernelDifference (p r : unitInterval) (x : V) :
    Summable (q.kernelDifference o p r x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  exact q.kernelDifference_outside o p r x y (by simpa only [Set.Finite.mem_toFinset] using hy)

theorem summable_kernelDifference_column (p r : unitInterval) (y : V) :
    Summable (fun x => q.kernelDifference o p r x y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y M).toFinset)
  intro x hx
  exact q.kernelDifference_reverse_outside o p r x y (by simpa only [Set.Finite.mem_toFinset] using hx)

theorem differenceRow_nonneg (p r : unitInterval) : 0 ≤ q.differenceRow o p r :=
  tsum_nonneg (q.kernelDifference_nonneg o p r o)

theorem differenceRow_finite (p r : unitInterval) :
    q.differenceRow o p r = ∑ y ∈ (finite_reachBall hloc o M).toFinset, q.kernelDifference o p r o y := by
  apply tsum_eq_sum
  intro y hy
  exact q.kernelDifference_outside o p r o y (by simpa only [Set.Finite.mem_toFinset] using hy)

theorem kernelDifference_row_le (p r : unitInterval) (x : V) :
    (∑' y, q.kernelDifference o p r x y) ≤ q.differenceRow o p r := by
  by_cases hx : x ∈ vertexOrbit G o
  · obtain ⟨a,b,ha,rfl⟩ := hx
    rw [← a.tsum_eq (fun y => q.kernelDifference o p r (a o) y)]
    exact le_of_eq (tsum_congr (q.kernelDifference_covariant o p r a b ha o))
  · simpa only [q.kernelDifference_start o p r x _ hx,tsum_zero] using q.differenceRow_nonneg o p r

 

theorem norm_sub_le_differenceRow {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀) (ho : o = root i₀)
    (p r : unitInterval) (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel o p x y : ℂ))
    (hB : ∀ x y, B (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel o r x y : ℂ)) :
    ‖A-B‖ ≤ q.differenceRow o p r := by
  subst o
  have hc (y : V) : (∑' x, q.kernelDifference (root i₀) p r x y) ≤ q.differenceRow (root i₀) p r := by
    by_cases hy : y ∈ vertexOrbit G (root i₀)
    · exact (orbit_kernel_column_eq_row G root weight Γ htr hΓ hw i₀ hw₀
        (q.kernelDifference (root i₀) p r) (q.kernelDifference_covariant (root i₀) p r)
        (q.kernelDifference_start (root i₀) p r) (q.kernelDifference_end (root i₀) p r)
        (q.summable_kernelDifference (root i₀) p r) (q.summable_kernelDifference_column (root i₀) p r) y hy).le
    · simpa only [q.kernelDifference_end (root i₀) p r _ y hy,tsum_zero] using
        q.differenceRow_nonneg (root i₀) p r
  apply operator_norm_le_absolute_sums
    (fun x y => q.normalizedKernel (root i₀) p x y-q.normalizedKernel (root i₀) r x y)
    _ (q.differenceRow_nonneg (root i₀) p r)
  · intro x S
    exact ((q.summable_kernelDifference (root i₀) p r x).sum_le_tsum S
      (fun y _ => q.kernelDifference_nonneg (root i₀) p r x y)).trans (q.kernelDifference_row_le (root i₀) p r x)
  · intro y S
    exact ((q.summable_kernelDifference_column (root i₀) p r y).sum_le_tsum S
      (fun x _ => q.kernelDifference_nonneg (root i₀) p r x y)).trans (hc y)
  · intro x y
    change A (lp.single 2 y (1:ℂ)) x - B (lp.single 2 y (1:ℂ)) x = _
    rw [hA,hB,Complex.ofReal_sub]

end LocalEndpointRule
end EndpointDifference
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section EndpointOperatorContinuity
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem exists_normalized_operator_all {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (p : unitInterval) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ 1 ∧
      ∀ x y, A (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel (root i₀) p x y : ℂ) := by
  by_cases hu : q.successProbability p (root i₀) = 0
  · refine ⟨0,by simp,?_⟩
    intro x y
    simp only [normalizedKernel,hu,inv_zero,zero_mul,Complex.ofReal_zero,
      zero_apply,lp.coeFn_zero,Pi.zero_apply]
  · obtain ⟨A,_,hA,hK⟩ := q.exists_normalized_operator root weight Γ htr hΓ hw i₀ hw₀ p
      (lt_of_le_of_ne (q.successProbability_nonneg p (root i₀)) (Ne.symm hu))
    exact ⟨A,hA,hK⟩

theorem continuousAt_differenceRow (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p₀ : unitInterval)
    (hu : q.successProbability p₀ o ≠ 0) :
    ContinuousAt (fun p => q.differenceRow o p p₀) p₀ := by
  simp_rw [q.differenceRow_finite o]
  apply tendsto_finsetSum
  intro y _
  exact ((((q.continuous_successProbability o).continuousAt.inv₀ hu).mul
    (q.continuous_kernel o y).continuousAt).sub continuousAt_const).abs

 

theorem exists_continuous_normalized_operators {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) :
    ∃ A : unitInterval → (Hilbert V →L[ℂ] Hilbert V),
      (∀ p, ‖A p‖ ≤ 1) ∧
      (∀ p x y, A p (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel (root i₀) p x y : ℂ)) ∧
      ∀ p, q.successProbability p (root i₀) ≠ 0 → ContinuousAt A p := by
  choose A hn hK using q.exists_normalized_operator_all root weight Γ htr hΓ hw i₀ hw₀
  refine ⟨A,hn,hK,?_⟩
  intro p hu
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun r => norm_nonneg (A r-A p))
    (fun r => q.norm_sub_le_differenceRow (root i₀) root weight Γ htr hΓ hw i₀ hw₀ rfl r p (A r) (A p) (hK r) (hK p))
  have h := (q.continuousAt_differenceRow (root i₀) p hu).tendsto
  have hz : q.differenceRow (root i₀) p p = 0 := by
    simp only [differenceRow,kernelDifference,sub_self,abs_zero,tsum_zero]
  rwa [hz] at h

end LocalEndpointRule
end EndpointOperatorContinuity
end Percolation

 
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

theorem susceptibility_aut [Countable V] [Countable E] (G : BondGraph V E)
    (p : unitInterval) {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x : V) :
    susceptibility G p (a x) = susceptibility G p x := by
  unfold susceptibility
  rw [←a.tsum_eq]
  simp only [twoPoint_aut G p h]

theorem susceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ susceptibility G p x := by
  have hd : twoPoint G p x x = 1 := by
    have he : {ω : Set E | Conn G ω x x} = Set.univ := Set.eq_univ_of_forall (fun _ => conn_refl G _ x)
    simp only [twoPoint,he,measure_univ,ENNReal.toReal_one]
  rw [←hd]
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).le_tsum x (fun _ _ => twoPoint_nonneg G p _ _)

theorem rootSusceptibility_nonneg (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) (p : unitInterval) :
    0 ≤ rootSusceptibility G root weight p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (susceptibility_nonneg G p _))

theorem susceptibility_le_rootSusceptibility [Countable V] [Countable E]
    (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i) (p : unitInterval) (x : V) :
    susceptibility G p x ≤ c*rootSusceptibility G root weight p := by
  obtain ⟨i,a,b,hab,hax⟩ := hcov x
  rw [←hax,susceptibility_aut G p hab]
  calc
    _ ≤ (c*weight i)*susceptibility G p (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) (susceptibility_nonneg G p _)
    _ = c*(weight i*susceptibility G p (root i)) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (susceptibility_nonneg G p _)) (Finset.mem_univ i)) hc

 
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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteKernelNorm
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem kernel_sum_le_norm_card (K : V → V → ℝ)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) (F : Finset V) :
    ∑ x ∈ F, ∑ y ∈ F, K x y ≤ ‖A‖*F.card := by
  have he : inner ℂ (deltaSum F) (A (deltaSum F)) =
      ((∑ x ∈ F, ∑ y ∈ F, K x y : ℝ) : ℂ) := by
    rw [inner_deltaSum]
    simp only [deltaSum,map_sum,lp.coeFn_sum,Finset.sum_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hA x y
  have h := (Complex.re_le_norm (inner ℂ (deltaSum F) (A (deltaSum F)))).trans
    ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)))
  rw [he,Complex.ofReal_re] at h
  calc
    _ ≤ ‖deltaSum F‖*(‖A‖*‖deltaSum F‖) := h
    _ = ‖A‖*‖deltaSum F‖^2 := by ring
    _ = _ := by rw [norm_deltaSum_sq]

 
theorem kernel_average_le_norm (K : V → V → ℝ)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ))
    (F : Finset V) (hF : F.Nonempty) :
    (∑ x ∈ F, ∑ y ∈ F, K x y)/(F.card:ℝ) ≤ ‖A‖ := by
  exact (div_le_iff₀ (Nat.cast_pos.mpr hF.card_pos)).mpr (kernel_sum_le_norm_card K A hA F)

end FiniteKernelNorm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinClusterSlice
attribute [local instance] Classical.propDecidable Classical.decEq

theorem mem_binClusterSlice (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V) :
    y ∈ binClusterSlice G o n ω x ↔ ClusterWindow G x n (2*n) ω ∧ Conn G ω x y ∧ y ∈ vertexOrbit G o := by
  unfold binClusterSlice
  split_ifs with h
  · simp only [Finset.mem_filter,Set.Finite.mem_toFinset,h,true_and,cluster,Set.mem_ofPred_eq]
  · simp only [Finset.notMem_empty,h,false_and]

theorem binClusterSlice_eq_of_conn (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E)
    {x y : V} (h : Conn G ω x y) : binClusterSlice G o n ω x = binClusterSlice G o n ω y := by
  have hc := cluster_eq_of_conn G ω h
  have hw : ClusterWindow G x n (2*n) ω ↔ ClusterWindow G y n (2*n) ω := by
    unfold ClusterWindow
    rw [hc]
  ext z
  simp only [mem_binClusterSlice,hw]
  have hz : Conn G ω x z ↔ Conn G ω y z := by change z ∈ cluster G ω x ↔ z ∈ cluster G ω y; rw [hc]
  rw [hz]

theorem binSizeMass_eq_of_conn (G : BondGraph V E) (n : ℕ) (ω : Set E)
    {x y : V} (hc : Conn G ω x y) : binSizeMass G n ω x = binSizeMass G n ω y := by
  have he := cluster_eq_of_conn G ω hc
  have hw : ClusterWindow G x n (2*n) ω ↔ ClusterWindow G y n (2*n) ω := by
    unfold ClusterWindow
    rw [he]
  by_cases hx : ClusterWindow G x n (2*n) ω
  · rw [binSizeMass_eq G n ω x hx,binSizeMass_eq G n ω y (hw.mp hx),he]
  · have hy := fun h => hx (hw.mpr h)
    simp only [binSizeMass,binMass_zero_of_not_window G n ω x _ hx,
      binMass_zero_of_not_window G n ω y _ hy,tsum_zero]

theorem mem_binClusterSlice_iff_mass (G : BondGraph V E) (o : V) (n : ℕ)
    (ω : Set E) (x y : V) :
    y ∈ binClusterSlice G o n ω x ↔
      binConnectionMass G n ω x y = 1 ∧ y ∈ vertexOrbit G o := by
  rw [mem_binClusterSlice]
  have he : binConnectionMass G n ω x y =
      if ClusterWindow G x n (2*n) ω ∧ Conn G ω x y then 1 else 0 := by
    unfold binConnectionMass ClusterWindow
    congr 1
    apply propext; tauto
  rw [he]
  by_cases h : ClusterWindow G x n (2*n) ω ∧ Conn G ω x y
  · rw [ite_eq_left h]
    simp only [h.1,h.2,true_and]
  · rw [ite_eq_right h]
    simp only [zero_ne_one,false_and]
    tauto

theorem binClusterSlice_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (o : V) (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binClusterSlice G o n ω x = binClusterSlice G o n (ω ∩ (Q : Set E)) x := by
  intro Q
  ext y
  rw [mem_binClusterSlice_iff_mass,mem_binClusterSlice_iff_mass,
    binConnectionMass_local G hloc n ω x y]

end BinClusterSlice
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteClassTransport
attribute [local instance] Classical.propDecidable Classical.decEq


theorem finiteClassTransport_row (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ) (x : V) :
    (∑' y, finiteClassTransport S t K x y) = t x * ∑ z ∈ S x, K x z := by
  rw [tsum_eq_sum (s := S x) (fun y hy => (show finiteClassTransport S t K x y = 0 from ite_eq_right hy))]
  have he : (∑ y ∈ S x, finiteClassTransport S t K x y) =
      (S x).card * (t x / (S x).card * ∑ z ∈ S x, K x z) := by
    simp only [finiteClassTransport]
    rw [Finset.sum_ite_mem]
    simp only [Finset.inter_self,Finset.sum_const,nsmul_eq_mul]
  rw [he]
  by_cases h : (S x).Nonempty
  · have hc : ((S x).card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.card_pos.ne'
    field_simp
  · have hs := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hs,Finset.card_empty,Nat.cast_zero,Finset.sum_empty,mul_zero]

theorem finiteClassTransport_column (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ)
    (hsym : ∀ x y, y ∈ S x ↔ x ∈ S y)
    (heq : ∀ x y, y ∈ S x → S y = S x)
    (ht : ∀ x y, y ∈ S x → t y = t x) (x : V) :
    (∑' y, finiteClassTransport S t K y x) =
      t x / (S x).card * ∑ y ∈ S x, ∑ z ∈ S x, K y z := by
  rw [tsum_eq_sum (s := S x) (fun y hy => (show finiteClassTransport S t K y x = 0 from
    ite_eq_right (fun h => hy ((hsym x y).mpr h))))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [finiteClassTransport,ite_eq_left ((hsym x y).mp hy),heq x y hy,ht x y hy]

 
theorem finiteClassTransport_column_le (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ) (ht0 : ∀ x, 0 ≤ t x)
    (hsym : ∀ x y, y ∈ S x ↔ x ∈ S y)
    (heq : ∀ x y, y ∈ S x → S y = S x)
    (ht : ∀ x y, y ∈ S x → t y = t x)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) (x : V) :
    (∑' y, finiteClassTransport S t K y x) ≤ ‖A‖*t x := by
  rw [finiteClassTransport_column S t K hsym heq ht]
  by_cases h : (S x).Nonempty
  · have hh := mul_le_mul_of_nonneg_left (kernel_average_le_norm K A hA (S x) h) (ht0 x)
    simpa only [div_mul_eq_mul_div,mul_div_assoc,mul_comm (t x) ‖A‖] using hh
  · have hs := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hs,Finset.card_empty,Nat.cast_zero,div_zero,Finset.sum_empty,mul_zero]
    exact mul_nonneg (norm_nonneg _) (ht0 x)

end FiniteClassTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinDiagonalClass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem mem_binOrbitClass (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V) :
    y ∈ binOrbitClass G o n ω x ↔ x ∈ vertexOrbit G o ∧
      ClusterWindow G x n (2*n) ω ∧ Conn G ω x y ∧ y ∈ vertexOrbit G o := by
  unfold binOrbitClass
  split_ifs with h
  · simp only [mem_binClusterSlice,h,true_and]
  · simp only [Finset.notMem_empty,h,false_and]

theorem binOrbitClass_symm (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V) :
    y ∈ binOrbitClass G o n ω x ↔ x ∈ binOrbitClass G o n ω y := by
  have h (x y : V) (hy : y ∈ binOrbitClass G o n ω x) : x ∈ binOrbitClass G o n ω y := by
    obtain ⟨hx,hw,hc,hy⟩ := (mem_binOrbitClass G o n ω x y).mp hy
    have hwy : ClusterWindow G y n (2*n) ω := by
      unfold ClusterWindow at hw ⊢
      rw [←cluster_eq_of_conn G ω hc]
      exact hw
    exact (mem_binOrbitClass G o n ω y x).mpr ⟨hy,hwy,conn_symm G ω hc,hx⟩
  exact ⟨h x y,h y x⟩

theorem binOrbitClass_eq (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∈ binOrbitClass G o n ω x) : binOrbitClass G o n ω y = binOrbitClass G o n ω x := by
  obtain ⟨hx,_,hc,hy⟩ := (mem_binOrbitClass G o n ω x y).mp hy
  simp only [binOrbitClass,ite_eq_left hx,ite_eq_left hy]
  exact (binClusterSlice_eq_of_conn G o n ω hc).symm

theorem binOrbitClass_mass_eq (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∈ binOrbitClass G o n ω x) : binSizeMass G n ω y = binSizeMass G n ω x :=
  (binSizeMass_eq_of_conn G n ω ((mem_binOrbitClass G o n ω x y).mp hy).2.2.1).symm

theorem binOrbitClass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (o : V) (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binOrbitClass G o n ω x = binOrbitClass G o n (ω ∩ (Q : Set E)) x := by
  intro Q
  unfold binOrbitClass
  rw [binClusterSlice_local G hloc o n ω x]

theorem binOrbitClass_mem_covariant (G : BondGraph V E) (o : V)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (n : ℕ) (ω : Set E) (x y : V) :
    y ∈ binOrbitClass G o n (b ⁻¹' ω) x ↔ a y ∈ binOrbitClass G o n ω (a x) := by
  unfold binOrbitClass
  simp only [mem_vertexOrbit_aut_iff G o hab]
  split_ifs
  · simp only [mem_binClusterSlice_iff_mass,binConnectionMass_covariant G hab,
      mem_vertexOrbit_aut_iff G o hab]
  · simp only [Finset.notMem_empty]

theorem binOrbitClass_covariant (G : BondGraph V E) (o : V)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (n : ℕ) (ω : Set E) (x : V) :
    (binOrbitClass G o n (b ⁻¹' ω) x).image a = binOrbitClass G o n ω (a x) := by
  ext y
  constructor
  · rintro hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    exact (binOrbitClass_mem_covariant G o hab n ω x z).mp hz
  · intro hy
    exact Finset.mem_image.mpr ⟨a.symm y,(binOrbitClass_mem_covariant G o hab n ω x (a.symm y)).mpr
      (by simpa only [Equiv.apply_symm_apply] using hy),a.apply_symm_apply y⟩

theorem binOrbitClass_reach (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∈ binOrbitClass G o n ω x) : y ∈ reachBall G x (2*n) := by
  obtain ⟨_,hw,hc,_⟩ := (mem_binOrbitClass G o n ω x y).mp hy
  exact finite_cluster_subset_reachBall G ω x hw.1 (2*n) hw.2.2.le hc

end BinDiagonalClass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinDiagonalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binDiagonalMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (o : V) (n : ℕ) (K : V → V → ℝ) (ω : Set E) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binDiagonalMass G o n K ω x y = binDiagonalMass G o n K (ω ∩ (Q : Set E)) x y := by
  intro Q
  simp only [binDiagonalMass,finiteClassTransport]
  rw [binOrbitClass_local G hloc o n ω x,binSizeMass_local G hloc n ω x]

theorem binDiagonalMass_integrable (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (K : V → V → ℝ) (x y : V) :
    Integrable (fun ω => binDiagonalMass G o n K ω x y) (law p) :=
  integrable_finite_local _ p _ (fun ω => binDiagonalMass_local G hloc o n K ω x y)

theorem binDiagonalMass_outside (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) (hy : y ∉ reachBall G x (2*n)) :
    binDiagonalMass G o n K ω x y = 0 :=
  ite_eq_right (fun h => hy (binOrbitClass_reach G o n ω x y h))

theorem binDiagonalMass_outside_column (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) (hx : x ∉ reachBall G y (2*n)) :
    binDiagonalMass G o n K ω x y = 0 :=
  ite_eq_right (fun h => hx (binOrbitClass_reach G o n ω y x ((binOrbitClass_symm G o n ω x y).mp h)))

theorem binDiagonalMass_row_zero (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) (hx : x ∉ vertexOrbit G o) :
    binDiagonalMass G o n K ω x y = 0 :=
  ite_eq_right (fun h => hx ((mem_binOrbitClass G o n ω x y).mp h).1)

theorem binDiagonalMass_column_zero (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) (hy : y ∉ vertexOrbit G o) :
    binDiagonalMass G o n K ω x y = 0 :=
  ite_eq_right (fun h => hy ((mem_binOrbitClass G o n ω x y).mp h).2.2.2)

theorem binDiagonalMass_covariant (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (hK : ∀ x y, K (a x) (a y) = K x y) (ω : Set E) (x y : V) :
    binDiagonalMass G o n K (b ⁻¹' ω) x y = binDiagonalMass G o n K ω (a x) (a y) := by
  have hs := binOrbitClass_covariant G o hab n ω x
  have hc : (binOrbitClass G o n (b ⁻¹' ω) x).card = (binOrbitClass G o n ω (a x)).card := by
    rw [←hs,Finset.card_image_of_injective _ a.injective]
  have hsum : (∑ z ∈ binOrbitClass G o n (b ⁻¹' ω) x, K x z) =
      ∑ z ∈ binOrbitClass G o n ω (a x), K (a x) z := by
    rw [←hs,Finset.sum_image (fun _ _ _ _ h => a.injective h)]
    simp only [hK]
  simp only [binDiagonalMass,finiteClassTransport,binOrbitClass_mem_covariant G o hab,
    binSizeMass_covariant G n ω hab,hc,hsum]

theorem binDiagonalMass_row (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x : V) :
    (∑' y, binDiagonalMass G o n K ω x y) =
      binSizeMass G n ω x ^ 2 * ∑ z ∈ binOrbitClass G o n ω x, K x z :=
  finiteClassTransport_row _ _ K x

theorem binDiagonalMass_column (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x : V) :
    (∑' y, binDiagonalMass G o n K ω y x) =
      binSizeMass G n ω x ^ 2 / (binOrbitClass G o n ω x).card *
        ∑ y ∈ binOrbitClass G o n ω x, ∑ z ∈ binOrbitClass G o n ω x, K y z := by
  apply finiteClassTransport_column _ _ K (binOrbitClass_symm G o n ω) (binOrbitClass_eq G o n ω)
  intro x y hy
  rw [binOrbitClass_mass_eq G o n ω x y hy]

theorem binDiagonalMass_column_le (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) (ω : Set E) (x : V) :
    (∑' y, binDiagonalMass G o n K ω y x) ≤ ‖A‖ * binSizeMass G n ω x ^ 2 := by
  apply finiteClassTransport_column_le _ _ K (fun _ => sq_nonneg _)
    (binOrbitClass_symm G o n ω) (binOrbitClass_eq G o n ω) _ A hA
  intro x y hy
  rw [binOrbitClass_mass_eq G o n ω x y hy]

end BinDiagonalTransport
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
section BinDiagonalLoss
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binDiagonalKernel_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (K : V → V → ℝ)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (hK : ∀ x y, K (a x) (a y) = K x y) (x y : V) :
    binDiagonalKernel G p o n K (a x) (a y) = binDiagonalKernel G p o n K x y := by
  have hm : Measurable (fun ω => binDiagonalMass G o n K ω x y) :=
    measurable_finite_local _ _ (fun ω => binDiagonalMass_local G hloc o n K ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [binDiagonalKernel,binDiagonalMass_covariant G o n K hab hK] using h.symm

theorem binDiagonalKernel_row_integral (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (K : V → V → ℝ) (x : V) :
    (∑' y, binDiagonalKernel G p o n K x y) =
      ∫ ω, binSizeMass G n ω x ^ 2 * ∑ z ∈ binOrbitClass G o n ω x, K x z ∂law p := by
  rw [←show (∫ ω, ∑' y, binDiagonalMass G o n K ω x y ∂law p) =
      ∑' y, binDiagonalKernel G p o n K x y from
    integral_tsum_of_finite_support (law p) (finite_reachBall hloc x (2*n)).toFinset _
      (fun y => binDiagonalMass_integrable G hloc p o n K x y)
      (fun ω y hy => binDiagonalMass_outside G o n K ω x y (by simpa only [Set.Finite.mem_toFinset] using hy))]
  simp only [binDiagonalMass_row]

theorem binDiagonalKernel_column_integral (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (K : V → V → ℝ) (x : V) :
    (∑' y, binDiagonalKernel G p o n K y x) =
      ∫ ω, ∑' y, binDiagonalMass G o n K ω y x ∂law p := by
  symm
  exact integral_tsum_of_finite_support (law p) (finite_reachBall hloc x (2*n)).toFinset _
    (fun y => binDiagonalMass_integrable G hloc p o n K y x)
    (fun ω y hy => binDiagonalMass_outside_column G o n K ω y x (by simpa only [Set.Finite.mem_toFinset] using hy))

theorem integral_binDiagonalLoss (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (p : unitInterval) (n : ℕ) (K : V → V → ℝ)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y) :
    (∫ ω, binSizeMass G n ω (root i₀)^2 *
      ∑ z ∈ binOrbitClass G (root i₀) n ω (root i₀), K (root i₀) z ∂law p) =
    ∫ ω, binSizeMass G n ω (root i₀)^2 / (binOrbitClass G (root i₀) n ω (root i₀)).card *
      ∑ y ∈ binOrbitClass G (root i₀) n ω (root i₀),
        ∑ z ∈ binOrbitClass G (root i₀) n ω (root i₀), K y z ∂law p := by
  have hr (x : V) : Summable (binDiagonalKernel G p (root i₀) n K x) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x (2*n)).toFinset)
    intro y hy
    simp only [binDiagonalKernel,binDiagonalMass_outside G (root i₀) n K _ x y
      (by simpa only [Set.Finite.mem_toFinset] using hy),integral_zero]
  have hc (y : V) : Summable (fun x => binDiagonalKernel G p (root i₀) n K x y) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y (2*n)).toFinset)
    intro x hx
    simp only [binDiagonalKernel,binDiagonalMass_outside_column G (root i₀) n K _ x y
      (by simpa only [Set.Finite.mem_toFinset] using hx),integral_zero]
  have ht := orbit_kernel_column_eq_row G root weight Γ htr hΓ hw i₀ hw₀
    (binDiagonalKernel G p (root i₀) n K)
    (fun a b hab x y => binDiagonalKernel_covariant G hloc p (root i₀) n K hab (hcov a b hab) x y)
    (fun x y hx => by simp only [binDiagonalKernel,binDiagonalMass_row_zero G _ n K _ x y hx,integral_zero])
    (fun x y hy => by simp only [binDiagonalKernel,binDiagonalMass_column_zero G _ n K _ x y hy,integral_zero])
    hr hc (root i₀) ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
  rw [binDiagonalKernel_row_integral G hloc,binDiagonalKernel_column_integral G hloc] at ht
  simpa only [binDiagonalMass_column] using ht.symm

 

theorem integral_binDiagonalLoss_le (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (p : unitInterval) (n : ℕ) (K : V → V → ℝ)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) :
    (∫ ω, binSizeMass G n ω (root i₀)^2 *
      ∑ z ∈ binOrbitClass G (root i₀) n ω (root i₀), K (root i₀) z ∂law p) ≤
      ‖A‖ * ∫ ω, binSizeMass G n ω (root i₀)^2 ∂law p := by
  rw [integral_binDiagonalLoss G hloc root weight Γ htr hΓ hw i₀ hw₀ p n K hcov]
  have hi : Integrable (fun ω => ∑' y, binDiagonalMass G (root i₀) n K ω y (root i₀)) (law p) := by
    have he (ω : Set E) : (∑' y, binDiagonalMass G (root i₀) n K ω y (root i₀)) =
        ∑ y ∈ (finite_reachBall hloc (root i₀) (2*n)).toFinset, binDiagonalMass G (root i₀) n K ω y (root i₀) := by
      apply tsum_eq_sum
      intro y hy
      exact binDiagonalMass_outside_column G (root i₀) n K ω y (root i₀)
        (by simpa only [Set.Finite.mem_toFinset] using hy)
    simp only [he]
    exact integrable_finsetSum _ (fun y _ => binDiagonalMass_integrable G hloc p (root i₀) n K y (root i₀))
  have hs : Integrable (fun ω => binSizeMass G n ω (root i₀)^2) (law p) :=
    integrable_finite_local _ p _ (fun ω => congrArg (fun t : ℝ => t^2) (binSizeMass_local G hloc n ω (root i₀)))
  rw [←integral_const_mul]
  exact integral_mono (by simpa only [binDiagonalMass_column] using hi) (hs.const_mul ‖A‖)
    (fun ω => by simpa only [binDiagonalMass_column] using binDiagonalMass_column_le G (root i₀) n K A hA ω (root i₀))

end BinDiagonalLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DyadicDiagonalStrata
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binSizeMass_zero (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V)
    (hw : ¬ ClusterWindow G x n (2*n) ω) : binSizeMass G n ω x = 0 := by
  simp only [binSizeMass,binMass_zero_of_not_window G n ω x _ hw,tsum_zero]

theorem binOrbitClass_eq_full (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x : V)
    (hx : x ∈ vertexOrbit G o) (hw : ClusterWindow G x n (2*n) ω) :
    binOrbitClass G o n ω x = fullOrbitClass G o ω x := by
  simp only [binOrbitClass,ite_eq_left hx,binClusterSlice,dite_eq_left hw,fullOrbitClass,dite_eq_left hw.1]

theorem dyadic_window_iff (G : BondGraph V E) (ω : Set E) (x : V) (j : ℕ)
    (hz : (cluster G ω x).ncard ≠ 0) :
    ClusterWindow G x (2^j) (2*(2^j)) ω ↔ Nat.log 2 (cluster G ω x).ncard = j := by
  constructor
  · intro h
    apply Nat.log_eq_of_pow_le_of_lt_pow h.2.1
    simpa only [pow_succ,Nat.mul_comm] using h.2.2
  · intro h
    refine ⟨Set.finite_of_ncard_ne_zero hz,?_,?_⟩
    · rw [←h]
      exact Nat.pow_log_le_self 2 hz
    · rw [←h,show 2*2^(Nat.log 2 (cluster G ω x).ncard) = 2^(Nat.log 2 (cluster G ω x).ncard+1) by simp only [pow_succ,Nat.mul_comm]]
      exact Nat.lt_pow_succ_log_self (by norm_num) _

theorem dyadic_binSizeMass_sq (G : BondGraph V E) (ω : Set E) (x : V) (j : ℕ) :
    binSizeMass G (2^j) ω x ^ 2 =
      if Nat.log 2 (cluster G ω x).ncard = j then ((cluster G ω x).ncard:ℝ)^2 else 0 := by
  by_cases hz : (cluster G ω x).ncard = 0
  · have hw : ¬ClusterWindow G x (2^j) (2*(2^j)) ω := by
      intro h
      have hp : 0 < 2^j := pow_pos (by omega) _
      have hl := h.2.1
      omega
    simp only [binSizeMass_zero G (2^j) ω x hw,hz,Nat.cast_zero,zero_pow (by omega : 2 ≠ 0),ite_self]
  · by_cases hw : ClusterWindow G x (2^j) (2*(2^j)) ω
    · rw [binSizeMass_eq G (2^j) ω x hw,ite_eq_left ((dyadic_window_iff G ω x j hz).mp hw)]
    · rw [binSizeMass_zero G (2^j) ω x hw,ite_eq_right (fun h => hw ((dyadic_window_iff G ω x j hz).mpr h))]
      norm_num

theorem dyadic_binDiagonalMass (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (ω : Set E) (x : V) (hx : x ∈ vertexOrbit G o) (j : ℕ) :
    binSizeMass G (2^j) ω x ^ 2 * ∑ z ∈ binOrbitClass G o (2^j) ω x, K x z =
      if Nat.log 2 (cluster G ω x).ncard = j then diagonalLossMass G o K ω x else 0 := by
  by_cases hw : ClusterWindow G x (2^j) (2*(2^j)) ω
  · have hz : (cluster G ω x).ncard ≠ 0 := by
      have hp : 0 < 2^j := pow_pos (by omega) _
      have hl := hw.2.1
      omega
    rw [ite_eq_left ((dyadic_window_iff G ω x j hz).mp hw),binOrbitClass_eq_full G o (2^j) ω x hx hw,
      binSizeMass_eq G (2^j) ω x hw]
    rfl
  · rw [binSizeMass_zero G (2^j) ω x hw]
    simp only [zero_pow (by omega : 2 ≠ 0),zero_mul]
    by_cases hz : (cluster G ω x).ncard = 0
    · simp only [diagonalLossMass,hz,Nat.cast_zero,zero_pow (by omega : 2 ≠ 0),zero_mul,ite_self]
    · rw [ite_eq_right (fun h => hw ((dyadic_window_iff G ω x j hz).mpr h))]

theorem diagonalLossMass_nonneg (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (ω : Set E) (x : V) : 0 ≤ diagonalLossMass G o K ω x :=
  mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun z _ => hK x z))

theorem diagonalLossMass_le (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (L : ℝ) (hrow : ∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L) (ω : Set E) (x : V) :
    diagonalLossMass G o K ω x ≤ L*((cluster G ω x).ncard:ℝ)^2 := by
  exact (mul_le_mul_of_nonneg_left (hrow x _) (sq_nonneg _)).trans_eq (mul_comm _ _)

end DyadicDiagonalStrata
end Percolation

 
namespace Percolation
open MeasureTheory Filter
open scoped Topology
section DiscreteStratumIntegral
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem integral_le_of_discrete_strata {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (J : Ω → ℕ) (f g : Ω → ℝ) (C L : ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfg : ∀ ω, f ω ≤ L*g ω) (hgi : Integrable g μ)
    (hfi : ∀ j, Integrable (fun ω => if J ω = j then f ω else 0) μ)
    (hgi' : ∀ j, Integrable (fun ω => if J ω = j then g ω else 0) μ)
    (h : ∀ j, (∫ ω, (if J ω = j then f ω else 0) ∂μ) ≤
      C*(∫ ω, (if J ω = j then g ω else 0) ∂μ)) :
    (∫ ω, f ω ∂μ) ≤ C*(∫ ω, g ω ∂μ) := by
  let F : ℕ → Ω → ℝ := fun N ω => ∑ j ∈ Finset.range N, if J ω = j then f ω else 0
  let H : ℕ → Ω → ℝ := fun N ω => ∑ j ∈ Finset.range N, if J ω = j then g ω else 0
  have he (q : Ω → ℝ) (N : ℕ) (ω : Ω) :
      (∑ j ∈ Finset.range N, if J ω = j then q ω else 0) = if J ω < N then q ω else 0 := by
    simp only [Finset.sum_ite_eq,Finset.mem_range]
  have hFi (N : ℕ) : Integrable (F N) μ := integrable_finsetSum _ (fun j _ => hfi j)
  have hHi (N : ℕ) : Integrable (H N) μ := integrable_finsetSum _ (fun j _ => hgi' j)
  have hFbody (N : ℕ) (ω : Ω) : ‖F N ω‖ ≤ L*g ω := by
    dsimp [F]
    rw [he]
    split_ifs
    · simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 ω)] using hfg ω
    · simpa only [norm_zero,abs_zero] using (hf0 ω).trans (hfg ω)
  have hHbody (N : ℕ) (ω : Ω) : ‖H N ω‖ ≤ g ω := by
    dsimp [H]
    rw [he]
    split_ifs
    · simp only [abs_of_nonneg (hg0 ω),le_refl]
    · simpa only [norm_zero,abs_zero] using hg0 ω
  have ht (q : Ω → ℝ) (ω : Ω) : Tendsto
      (fun N => ∑ j ∈ Finset.range N, if J ω = j then q ω else 0) atTop (𝓝 (q ω)) := by
    have he' : (fun N => ∑ j ∈ Finset.range N, if J ω = j then q ω else 0) =ᶠ[atTop] (fun _ => q ω) := by
      filter_upwards [eventually_ge_atTop (J ω+1)] with N hN
      rw [he,ite_eq_left (by omega)]
    exact tendsto_const_nhds.congr' he'.symm
  have htF := tendsto_integral_of_dominated_convergence (fun ω => L*g ω)
    (fun N => (hFi N).aestronglyMeasurable) (hgi.const_mul L)
    (fun N => Eventually.of_forall (hFbody N)) (Eventually.of_forall (ht f))
  have htH := tendsto_integral_of_dominated_convergence g
    (fun N => (hHi N).aestronglyMeasurable) hgi
    (fun N => Eventually.of_forall (hHbody N)) (Eventually.of_forall (ht g))
  apply le_of_tendsto_of_tendsto htF (tendsto_const_nhds.mul htH)
  exact Eventually.of_forall (fun N => by
    change (∫ ω, F N ω ∂μ) ≤ C*(∫ ω, H N ω ∂μ)
    simp only [F,H,integral_finsetSum _ (fun j _ => hfi j),
      integral_finsetSum _ (fun j _ => hgi' j),Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => h j))

end DiscreteStratumIntegral
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DiagonalLoss
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem integral_diagonalLoss_le (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (p : unitInterval) (K : V → V → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y)
    (L : ℝ) (hrow : ∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ))
    (hs : Integrable (fun ω => ((cluster G ω (root i₀)).ncard:ℝ)^2) (law p)) :
    (∫ ω, diagonalLossMass G (root i₀) K ω (root i₀) ∂law p) ≤
      ‖A‖*(∫ ω, ((cluster G ω (root i₀)).ncard:ℝ)^2 ∂law p) := by
  have hx : root i₀ ∈ vertexOrbit G (root i₀) := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
  have hs' (j : ℕ) : Integrable (fun ω => binSizeMass G (2^j) ω (root i₀)^2) (law p) :=
    integrable_finite_local _ p _ (fun ω => congrArg (fun t : ℝ => t^2)
      (binSizeMass_local G hloc (2^j) ω (root i₀)))
  have hf' (j : ℕ) : Integrable (fun ω => binSizeMass G (2^j) ω (root i₀)^2 *
      ∑ z ∈ binOrbitClass G (root i₀) (2^j) ω (root i₀), K (root i₀) z) (law p) := by
    apply integrable_finite_local _ p _
    intro ω
    rw [binOrbitClass_local G hloc (root i₀) (2^j) ω (root i₀),binSizeMass_local G hloc (2^j) ω (root i₀)]
  apply integral_le_of_discrete_strata (law p) (fun ω => Nat.log 2 (cluster G ω (root i₀)).ncard)
    (fun ω => diagonalLossMass G (root i₀) K ω (root i₀))
    (fun ω => ((cluster G ω (root i₀)).ncard:ℝ)^2) ‖A‖ L
    (fun ω => diagonalLossMass_nonneg G (root i₀) K hK ω (root i₀))
    (fun _ => sq_nonneg _) (fun ω => diagonalLossMass_le G (root i₀) K L hrow ω (root i₀)) hs
  · intro j
    simpa only [dyadic_binDiagonalMass G (root i₀) K _ (root i₀) hx] using hf' j
  · intro j
    simpa only [dyadic_binSizeMass_sq] using hs' j
  · intro j
    have h := integral_binDiagonalLoss_le G hloc root weight Γ htr hΓ hw i₀ hw₀ p (2^j) K hcov A hA
    simp only [dyadic_binDiagonalMass G (root i₀) K _ (root i₀) hx] at h
    simpa only [dyadic_binSizeMass_sq] using h



end DiagonalLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section RootSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem second_moment_le_rootSusceptibility_cube [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcov : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    (∫ ω, ((cluster G ω x).ncard:ℝ)^2 ∂law p) ≤
      (c*rootSusceptibility G root weight p)^3 := by
  let C := c*rootSusceptibility G root weight p
  have hC : 0 ≤ C := mul_nonneg hc (rootSusceptibility_nonneg G root weight hw p)
  have hrow (z : V) : (∑' y, law p {ω | Conn G ω z y}) ≤ ENNReal.ofReal C := by
    rw [←ennreal_susceptibility G hloc hqt p hp]
    exact ENNReal.ofReal_le_ofReal (susceptibility_le_rootSusceptibility G root weight hw hcov c hc hmin p z)
  have hm : Measurable (fun ω : Set E => ((cluster G ω x).ncard:ℝ)^2) :=
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
  rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal (pow_nonneg hC _))

theorem diagonalLoss_le_rootSusceptibility_cube [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (K : V → V → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y)
    (L : ℝ) (hrow : ∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) :
    (∫ ω, diagonalLossMass G (root i₀) K ω (root i₀) ∂law p) ≤
      ‖A‖*(c*rootSusceptibility G root weight p)^3 := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  exact (integral_diagonalLoss_le G hloc root weight Γ htr hΓ hw i₀ hw₀ p K hK hcov L hrow A hA
    (hs (root i₀)).1).trans (mul_le_mul_of_nonneg_left
      (second_moment_le_rootSusceptibility_cube G hloc hqt root weight hw hcover c hc hmin p hp (root i₀))
      (norm_nonneg _))

end RootSecondMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DiagonalSeries
attribute [local instance] Classical.propDecidable Classical.decEq

theorem diagonalLossTerm_nonneg (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (x y : V) (ω : Set E) :
    0 ≤ diagonalLossTerm G o K x y ω := by
  unfold diagonalLossTerm
  split_ifs
  · exact mul_nonneg (hK x y) (sq_nonneg _)
  · exact le_rfl

theorem diagonalLossTerm_le (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (x y : V) (ω : Set E) :
    diagonalLossTerm G o K x y ω ≤ K x y*((cluster G ω x).ncard:ℝ)^2 := by
  unfold diagonalLossTerm
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hK x y) (sq_nonneg _)

theorem diagonalLossMass_eq_tsum (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (x : V) (ω : Set E) :
    diagonalLossMass G o K ω x = ∑' y, diagonalLossTerm G o K x y ω := by
  by_cases hf : (cluster G ω x).Finite
  · let S := fullOrbitClass G o ω x
    have hs (y : V) : y ∈ S ↔ y ∈ vertexOrbit G o ∧ Conn G ω x y := by
      dsimp only [S,fullOrbitClass]
      rw [dite_eq_left hf]
      simp only [Finset.mem_filter,Set.Finite.mem_toFinset,cluster,Set.mem_ofPred_eq]
      exact and_comm
    rw [tsum_eq_sum (s := S) (fun y hy => by
      simp only [diagonalLossTerm,ite_eq_right (fun h => hy ((hs y).mpr h))])]
    rw [diagonalLossMass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [diagonalLossTerm,ite_eq_left ((hs y).mp hy),mul_comm]
  · have hn := Set.Infinite.ncard hf
    simp only [diagonalLossMass,diagonalLossTerm,hn,Nat.cast_zero,zero_pow (by omega : 2 ≠ 0),
      mul_zero,zero_mul,ite_self,tsum_zero]

theorem integrable_diagonalLossTerm [Countable V] [Countable E] (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (x y : V) (p : unitInterval)
    (hs : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p)) :
    Integrable (diagonalLossTerm G o K x y) (law p) := by
  by_cases hy : y ∈ vertexOrbit G o
  · convert (hs.indicator (measurableSet_conn G x y)).const_mul (K x y) using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [diagonalLossTerm,hy,true_and,Set.indicator,Set.mem_ofPred_eq]
    split_ifs <;> simp only [mul_zero]
  · have he : diagonalLossTerm G o K x y = (fun _ : Set E => (0:ℝ)) := by
      funext ω
      simp only [diagonalLossTerm,hy,false_and,ite_false]
    rw [he]
    exact integrable_const 0

 

theorem integral_diagonalLoss_eq_series [Countable V] [Countable E]
    (G : BondGraph V E) (o : V) (K : V → V → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (L : ℝ) (hrow : ∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L)
    (x : V) (p : unitInterval)
    (hs : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p)) :
    (∫ ω, diagonalLossMass G o K ω x ∂law p) =
      ∑' y, if y ∈ vertexOrbit G o then
        K x y*(∫ ω, (if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) ∂law p) else 0 := by
  have hi (y : V) := integrable_diagonalLossTerm G o K x y p hs
  have hzero (y : V) (ω : Set E) := diagonalLossTerm_nonneg G o K hK x y ω
  have hn : Summable (fun y => ∫ ω, ‖diagonalLossTerm G o K x y ω‖ ∂law p) := by
    simp only [Real.norm_of_nonneg (hzero _ _)]
    apply summable_of_sum_le (fun y => integral_nonneg (hzero y)) (c := L*(∫ ω, ((cluster G ω x).ncard:ℝ)^2 ∂law p))
    intro S
    rw [←integral_finsetSum _ (fun y _ => hi y),←integral_const_mul]
    apply integral_mono (integrable_finsetSum _ (fun y _ => hi y)) (hs.const_mul L)
    intro ω
    calc
      _ ≤ ∑ y ∈ S, K x y*((cluster G ω x).ncard:ℝ)^2 :=
        Finset.sum_le_sum (fun y _ => diagonalLossTerm_le G o K hK x y ω)
      _ = (∑ y ∈ S, K x y)*((cluster G ω x).ncard:ℝ)^2 := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow x S) (sq_nonneg _)
  rw [show (fun ω => diagonalLossMass G o K ω x) = (fun ω => ∑' y, diagonalLossTerm G o K x y ω) from
    funext (diagonalLossMass_eq_tsum G o K x)]
  rw [←integral_tsum_of_summable_integral_norm hi hn]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ vertexOrbit G o
  · simp only [diagonalLossTerm,hy,true_and,ite_true]
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by dsimp only; split_ifs <;> simp only [mul_zero])
  · simp only [diagonalLossTerm,hy,false_and,ite_false,integral_zero]

end DiagonalSeries
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section RootSusceptibilityLower
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_rootSusceptibility_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ a : ℝ, 0 < a ∧ ∀ (p : unitInterval), p₀ ≤ (p:ℝ) → p < pc G → ∀ x,
      a*rootSusceptibility G root weight p ≤ susceptibility G p x := by
  have hex (ij : ι × ι) : ∃ l : List E, Along G (root ij.1) l (root ij.2) := by
    obtain ⟨l,hl,_,_⟩ := conn_exists_bond_trail G (conn_univ_of_connected G hconn (root ij.1) (root ij.2))
    exact ⟨l,hl⟩
  choose path hpath using hex
  let N := ∑ ij : ι × ι, (path ij).length
  have hlen (i j : ι) : (path (i,j)).length ≤ N :=
    Finset.single_le_sum (f := fun ij : ι × ι => (path ij).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i,j))
  refine ⟨p₀^N,pow_pos hp₀ N,fun p hp hpcrit x => ?_⟩
  obtain ⟨j,a,b,hab,hax⟩ := hcover x
  have hfin (z : V) : Summable (fun y => (law p).real {ω | Conn G (ω ∩ Set.univ) z y}) := by
    simp only [Set.inter_univ]
    exact summable_twoPoint_subcritical G hloc hqt p hpcrit z
  have heq (z : V) : restrictedSusceptibility G Set.univ p z = susceptibility G p z := by
    simp only [restrictedSusceptibility,susceptibility,Set.inter_univ,twoPoint,Measure.real]
  have hb (i : ι) : p₀^N*susceptibility G p (root i) ≤ susceptibility G p (root j) := by
    have h := restrictedSusceptibility_path_lower G Set.univ p (hpath (j,i)) (fun _ _ => Set.mem_univ _) hfin
    rw [heq,heq] at h
    have hpow : p₀^N ≤ (p:ℝ)^(path (j,i)).length :=
      (pow_le_pow_left₀ hp₀.le hp N).trans (pow_le_pow_of_le_one p.2.1 p.2.2 (hlen j i))
    exact (mul_le_mul_of_nonneg_right hpow (susceptibility_nonneg G p _)).trans h
  rw [←hax,susceptibility_aut G p hab]
  calc
    _ = ∑ i, weight i*(p₀^N*susceptibility G p (root i)) := by
      simp only [rootSusceptibility,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, weight i*susceptibility G p (root j) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = susceptibility G p (root j) := by rw [←Finset.sum_mul,hw1,one_mul]

end RootSusceptibilityLower
end Percolation

 
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

theorem integral_mul_finite_local (I R : Finset E) (hdis : Disjoint I R)
    (p : unitInterval) (f g : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (I:Set E)))
    (hg : ∀ ω, g ω = g (ω ∩ (R:Set E))) :
    (∫ ω, f ω*g ω ∂law p) = (∫ ω, f ω ∂law p)*(∫ ω, g ω ∂law p) := by
  have hf' := finite_local_of_subset I (I∪R) Finset.subset_union_left f hf
  have hg' := finite_local_of_subset R (I∪R) Finset.subset_union_right g hg
  rw [integral_eq_bernoulliPolynomial (I∪R) p _ (fun ω => by rw [hf' ω,hg' ω]),
    integral_eq_bernoulliPolynomial I p f hf,integral_eq_bernoulliPolynomial R p g hg,
    bernoulliPolynomial_union I R hdis]
  have hi (a b : Finset E) (ha : a ⊆ I) (hb : b ⊆ R) :
      ((a ∪ b : Finset E):Set E) ∩ (I:Set E) = a := by
    ext e
    simp only [Finset.coe_union,Set.mem_inter_iff,Set.mem_union,Finset.mem_coe]
    constructor
    · rintro ⟨he,hI⟩
      rcases he with he | he
      · exact he
      · exact ((Finset.disjoint_left.mp hdis) hI (hb he)).elim
    · intro he
      exact ⟨Or.inl he,ha he⟩
  have hr (a b : Finset E) (ha : a ⊆ I) (hb : b ⊆ R) :
      ((a ∪ b : Finset E):Set E) ∩ (R:Set E) = b := by
    ext e
    simp only [Finset.coe_union,Set.mem_inter_iff,Set.mem_union,Finset.mem_coe]
    constructor
    · rintro ⟨he,hR⟩
      rcases he with he | he
      · exact ((Finset.disjoint_left.mp hdis) (ha he) hR).elim
      · exact he
    · intro he
      exact ⟨Or.inr he,hb he⟩
  trans bernoulliPolynomial I (fun a => f a*bernoulliPolynomial R (fun b => g b) p) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro b hb
    rw [hf ((a∪b : Finset E):Set E),hg ((a∪b : Finset E):Set E),hi a b ha hb,hr a b ha hb]
  · exact bernoulliPolynomial_mul_const I _ _ p

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

 

theorem cluster_cell_finite_exterior_independence [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V) (x : V)
    (R : Finset E) (hR : (R:Set E) ⊆ internalEdges G (W:Set V)ᶜ)
    (p : unitInterval) (f : Set E → ℝ) (hf : ∀ ω, f ω = f (ω ∩ (R:Set E))) :
    (∫ ω, (if cluster G ω x = (W:Set V) then (1:ℝ) else 0)*f ω ∂law p) =
      (law p).real {ω | cluster G ω x = (W:Set V)} * (∫ ω, f ω ∂law p) := by
  have hdis : Disjoint (incidentSupport G hloc W) R := by
    rw [←complement_incidentSupport G hloc W] at hR
    exact Finset.disjoint_left.mpr (fun e he h => hR h he)
  have hc (ω : Set E) :
      (if cluster G ω x = (W:Set V) then (1:ℝ) else 0) =
        (if cluster G (ω ∩ (incidentSupport G hloc W:Set E)) x = (W:Set V) then 1 else 0) := by
    simp only [cluster_restrict_incident_eq_iff G hloc W _ (by rfl)]
  rw [integral_mul_finite_local _ R hdis p _ f hc hf]
  congr 1
  have hm : MeasurableSet {ω : Set E | cluster G ω x = (W:Set V)} := measurableSet_cluster_eq G x W
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using integral_indicator_one hm

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

 

theorem cluster_cell_exterior_connection_independent [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V)
    (x y z : V) (p : unitInterval) :
    (law p).real {ω | cluster G ω x = (W:Set V) ∧ Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} =
      (law p).real {ω | cluster G ω x = (W:Set V)} *
        (law p).real {ω | Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} := by
  let := Encodable.ofCountable E
  let S := internalEdges G (W:Set V)ᶜ
  let R := restrictedBondExhaustion S ∅
  have hmono : Monotone R := restrictedBondExhaustion_mono S ∅
  have hsub (n : ℕ) : (R n:Set E) ⊆ S := restrictedBondExhaustion_subset S ∅ (by simp) n
  have hcover (e : E) (he : e ∈ S) : ∃ n, e ∈ R n := restrictedBondExhaustion_cover S ∅ e he
  let A : Set (Set E) := {ω | cluster G ω x = (W:Set V)}
  let B (n : ℕ) : Set (Set E) := {ω | Conn G (ω ∩ (R n:Set E)) y z}
  let Btop : Set (Set E) := {ω | Conn G (ω ∩ S) y z}
  have hB : Monotone B := fun n m h ω hc =>
    conn_mono G (Set.inter_subset_inter_right _ (show (R n:Set E) ⊆ (R m:Set E) from hmono h)) hc
  have hu : (⋃ n, B n) = Btop := by
    ext ω
    simp only [B,Btop,Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,hn⟩ => conn_mono G (Set.inter_subset_inter_right _ (hsub n)) hn,
      conn_finite_exhaustion G S R hmono hcover⟩
  have huA : (⋃ n, A ∩ B n) = A ∩ Btop := by rw [←Set.inter_iUnion,hu]
  have htB := tendsto_measure_iUnion_atTop (μ := law p) hB
  have htA := tendsto_measure_iUnion_atTop (μ := law p)
    (show Monotone (fun n => A ∩ B n) from fun _ _ h => Set.inter_subset_inter_right _ (hB h))
  rw [hu] at htB
  rw [huA] at htA
  have htB' := (ENNReal.tendsto_toReal (measure_ne_top (law p) Btop)).comp htB
  have htA' := (ENNReal.tendsto_toReal (measure_ne_top (law p) (A∩Btop))).comp htA
  have he (n : ℕ) : (law p).real (A ∩ B n) = (law p).real A * (law p).real (B n) := by
    have h := cluster_cell_finite_exterior_independence G hloc W x (R n) (hsub n) p
      (fun ω => if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0)
      (fun ω => by rw [Set.inter_assoc,Set.inter_self])
    have hf : (∫ ω, (if cluster G ω x = (W:Set V) then (1:ℝ) else 0)*
        (if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0) ∂law p) = (law p).real (A ∩ B n) := by
      rw [←integral_event_indicator p (A∩B n)
        ((measurableSet_cluster_eq G x W).inter (measurableSet_restrictedConn G _ y z))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        dsimp only [A,B,Set.mem_inter_iff,Set.mem_ofPred_eq]
        split_ifs <;> simp_all)
    rw [hf] at h
    rw [show (∫ ω, (if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0) ∂law p) =
      (law p).real (B n) from integral_event_indicator p (B n) (measurableSet_restrictedConn G _ y z)] at h
    exact h
  exact tendsto_nhds_unique htA' ((tendsto_const_nhds.mul htB').congr (fun n => (he n).symm))

end ExteriorConnectionIndependence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExposedClusterGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_exterior_of_cluster_eq (G : BondGraph V E) (ω : Set E)
    (x y z : V) (W : Set V) (hW : cluster G ω x = W) (hy : y ∉ W) :
    Conn G (ω ∩ internalEdges G Wᶜ) y z ↔ Conn G ω y z := by
  refine ⟨conn_mono G Set.inter_subset_left,fun h => ?_⟩
  have hout (a : V) (ha : Conn G ω y a) : a ∉ W := by
    intro haW
    have hxa : Conn G ω x a := by change a ∈ cluster G ω x; rwa [hW]
    exact hy (hW ▸ (hxa.trans (conn_symm G _ ha) : y ∈ cluster G ω x))
  induction h with
  | refl => exact conn_refl G _ y
  | @tail a b hya hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G Wᶜ e a b heq).mpr
      ⟨hout a hya,hout b (hya.tail ⟨e,he,heq⟩)⟩⟩,heq⟩

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
section ExteriorCellSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_cell_exterior_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (W : Finset V) (x y : V) :
    (∫ ω, (if cluster G ω x = (W:Set V) ∧ ¬Conn G ω x y
      then ((cluster G ω y).ncard:ℝ) else 0) ∂law p) =
      (law p).real {ω | cluster G ω x = (W:Set V)} *
        inducedSusceptibility G (W:Set V)ᶜ p y := by
  by_cases hy : y ∈ (W:Set V)
  · rw [inducedSusceptibility,ite_eq_right (fun h => h hy),mul_zero]
    calc
      _ = ∫ _ω : Set E, (0:ℝ) ∂law p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          split_ifs with h
          · have hc : Conn G ω x y := by change y ∈ cluster G ω x; rwa [h.1]
            exact (h.2 hc).elim
          · rfl)
      _ = 0 := integral_zero _ _
  · simp only [inducedSusceptibility,Set.mem_compl_iff,hy,not_false_eq_true,ite_true]
    calc
      _ = ∫ ω, (if cluster G ω x = (W:Set V) then ((cluster G ω y).ncard:ℝ) else 0) ∂law p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          by_cases hc : cluster G ω x = (W:Set V)
          · have hnc : ¬Conn G ω x y := by intro h; exact hy (hc ▸ h)
            simp [hc,hnc]
          · simp only [hc,false_and,ite_false])
      _ = ∑' z, (law p).real {ω | cluster G ω x = (W:Set V) ∧ Conn G ω y z} :=
        integral_cluster_size_event G hloc hqt p hp y _ (measurableSet_cluster_eq G x W)
      _ = ∑' z, (law p).real {ω | cluster G ω x = (W:Set V)} *
          (law p).real {ω | Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} := by
        apply tsum_congr
        intro z
        rw [show {ω : Set E | cluster G ω x = (W:Set V) ∧ Conn G ω y z} =
            {ω | cluster G ω x = (W:Set V) ∧ Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} from by
          ext ω
          exact ⟨fun h => ⟨h.1,(conn_exterior_of_cluster_eq G ω x y z W h.1 hy).mpr h.2⟩,
            fun h => ⟨h.1,conn_mono G Set.inter_subset_left h.2⟩⟩]
        exact cluster_cell_exterior_connection_independent G hloc W x y z p
      _ = _ := tsum_mul_left

theorem restrictedSusceptibility_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (S : Set E) (y : V) :
    restrictedSusceptibility G S p y ≤ susceptibility G p y := by
  apply Summable.tsum_le_tsum _ (summable_restrictedTwoPoint G hloc hqt p hp S y)
    (summable_twoPoint_subcritical G hloc hqt p hp y)
  exact fun z => ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun ω hc => conn_mono G Set.inter_subset_left hc))

theorem inducedSusceptibility_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Set V) (y : V) :
    inducedSusceptibility G D p y ≤ susceptibility G p y := by
  unfold inducedSusceptibility
  split_ifs
  · exact restrictedSusceptibility_le_susceptibility G hloc hqt p hp _ y
  · exact susceptibility_nonneg G p y

end ExteriorCellSusceptibility
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

 

theorem integral_cluster_finite_partition [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V)
    (f : Set E → ℝ) (hf : Integrable f (law p)) :
    (∫ ω, f ω ∂law p) = ∑' W : Finset V,
      ∫ ω, (if cluster G ω x = (W:Set V) then f ω else 0) ∂law p := by
  let F (W : Finset V) (ω : Set E) := if cluster G ω x = (W:Set V) then f ω else 0
  have hi (W : Finset V) : Integrable (F W) (law p) := by
    have he : F W = {ω : Set E | cluster G ω x = (W:Set V)}.indicator f := by
      funext ω
      simp only [F,Set.indicator,Set.mem_ofPred_eq]
      split_ifs <;> rfl
    rw [he]
    exact hf.indicator (measurableSet_cluster_eq G x W)
  have hb (S : Finset (Finset V)) (ω : Set E) : (∑ W ∈ S, ‖F W ω‖) ≤ ‖f ω‖ := by
    by_cases hex : ∃ W ∈ S, cluster G ω x = (W:Set V)
    · obtain ⟨W,hWS,hW⟩ := hex
      rw [Finset.sum_eq_single W]
      · simp only [F,hW,ite_true,le_refl]
      · intro U _ hU
        have hu : cluster G ω x ≠ (U:Set V) := fun h => hU (Finset.coe_injective (h.symm.trans hW))
        simp only [F,ite_eq_right hu,norm_zero]
      · exact fun h => (h hWS).elim
    · have he (W : Finset V) (hW : W ∈ S) : cluster G ω x ≠ (W:Set V) := fun h => hex ⟨W,hW,h⟩
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
      exact (tsum_cluster_cells G ω x hω (f ω)).symm
    _ = _ := (integral_tsum_of_summable_integral_norm hi hn).symm

end ClusterPartition
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshExteriorMoment
attribute [local instance] Classical.propDecidable Classical.decEq

theorem freshExteriorMoment_eq_tsum (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) :
    freshExteriorMoment G p x y ω = ∑' W : Finset V, if cluster G ω x = (W:Set V)
      then (W.card:ℝ)*inducedSusceptibility G (W:Set V)ᶜ p y else 0 := by
  by_cases hf : (cluster G ω x).Finite
  · let W := hf.toFinset
    have hW : cluster G ω x = (W:Set V) := hf.coe_toFinset.symm
    rw [tsum_eq_single W (fun U hU => ite_eq_right (fun h => hU (Finset.coe_injective (h.symm.trans hW)))),ite_eq_left hW]
    simp only [freshExteriorMoment,hW,Set.ncard_coe_finset]
  · have he (W : Finset V) : cluster G ω x ≠ (W:Set V) := fun h => hf (h ▸ W.finite_toSet)
    simp only [freshExteriorMoment,Set.Infinite.ncard hf,Nat.cast_zero,zero_mul,ite_eq_right (he _),tsum_zero]

theorem measurable_freshExteriorMoment [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) : Measurable (freshExteriorMoment G p x y) := by
  simp_rw [show freshExteriorMoment G p x y = (fun ω => ∑' W : Finset V, if cluster G ω x = (W:Set V)
      then (W.card:ℝ)*inducedSusceptibility G (W:Set V)ᶜ p y else 0) from funext (freshExteriorMoment_eq_tsum G p x y)]
  apply Measurable.tsum
  intro W
  exact Measurable.ite (measurableSet_cluster_eq G x W) measurable_const measurable_const

theorem freshExteriorMoment_nonneg (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : 0 ≤ freshExteriorMoment G p x y ω :=
  mul_nonneg (Nat.cast_nonneg _) (inducedSusceptibility_nonneg G _ p y)

theorem integrable_freshExteriorMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (freshExteriorMoment G p x y) (law p) := by
  apply ((susceptibility_eq_integral G hloc hqt p hp x).1.mul_const (susceptibility G p y)).mono'
    (measurable_freshExteriorMoment G p x y).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_of_nonneg (freshExteriorMoment_nonneg G p x y ω)]
    exact mul_le_mul_of_nonneg_left (inducedSusceptibility_le_susceptibility G hloc hqt p hp _ y) (Nat.cast_nonneg _))

theorem integrable_distinct_cluster_product [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fun ω => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) (law p) := by
  have he : (fun ω : Set E => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) =
      {ω : Set E | Conn G ω x y}ᶜ.indicator
        (fun ω => ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) := by
    funext ω
    simp only [Set.indicator,Set.mem_compl_iff,Set.mem_ofPred_eq]
  rw [he]
  exact (subcritical_cluster_association G hloc hqt p hp x y).1.indicator
    (measurableSet_conn G x y).compl

 

theorem integral_freshExteriorMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    (∫ ω, freshExteriorMoment G p x y ω ∂law p) =
      ∫ ω, (if ¬Conn G ω x y then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) ∂law p := by
  rw [integral_cluster_finite_partition G p hp x _ (integrable_freshExteriorMoment G hloc hqt p hp x y),
    integral_cluster_finite_partition G p hp x _ (integrable_distinct_cluster_product G hloc hqt p hp x y)]
  apply tsum_congr
  intro W
  have hl : (∫ ω, (if cluster G ω x = (W:Set V) then freshExteriorMoment G p x y ω else 0) ∂law p) =
      (W.card:ℝ)*inducedSusceptibility G (W:Set V)ᶜ p y * (law p).real {ω | cluster G ω x = (W:Set V)} := by
    rw [←integral_event_indicator p _ (measurableSet_cluster_eq G x W),←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only [Set.mem_ofPred_eq]
      by_cases hc : cluster G ω x = (W:Set V)
      · simp only [hc,ite_true,freshExteriorMoment,Set.ncard_coe_finset,mul_one]
      · simp only [hc,ite_false,mul_zero])
  have hr : (∫ ω, (if cluster G ω x = (W:Set V) then
      (if ¬Conn G ω x y then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) else 0) ∂law p) =
      (W.card:ℝ)*((law p).real {ω | cluster G ω x = (W:Set V)} * inducedSusceptibility G (W:Set V)ᶜ p y) := by
    rw [←cluster_cell_exterior_susceptibility G hloc hqt p hp W x y,←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only
      by_cases hc : cluster G ω x = (W:Set V)
      · simp only [hc,true_and,ite_true,Set.ncard_coe_finset]
        split_ifs <;> simp only [mul_zero]
      · simp only [hc,false_and,ite_false,mul_zero])
  rw [hl,hr]
  ring

end FreshExteriorMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctClusterMoments
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinctClusterMoment_nonneg (G : BondGraph V E) (p : unitInterval) (x y : V) :
    0 ≤ distinctClusterMoment G p x y := by
  apply integral_nonneg
  intro ω
  dsimp only [Pi.zero_apply]
  split_ifs <;> positivity

theorem cluster_ncard_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
  rw [←cluster_aut G hab,Set.ncard_image_of_injective _ a.injective]

theorem distinctClusterMoment_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) :
    distinctClusterMoment G p (a x) (a y) = distinctClusterMoment G p x y := by
  have hs (z : V) : Measurable (fun ω : Set E => ((cluster G ω z).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc z)
  have hm : Measurable (fun ω : Set E => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) :=
    Measurable.ite (measurableSet_conn G x y).compl ((hs x).mul (hs y)) measurable_const
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [distinctClusterMoment,conn_aut_iff G hab,cluster_ncard_covariant G hab] using h.symm

theorem neighborClusterMoment_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) : 0 ≤ neighborClusterMoment G hloc p x :=
  Finset.sum_nonneg (fun y _ => distinctClusterMoment_nonneg G p x y)

theorem neighbors_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    neighbors G hloc (a x) = (neighbors G hloc x).map a.toEmbedding := by
  ext y
  simp only [mem_neighbors,Finset.mem_map,Equiv.coe_toEmbedding]
  constructor
  · intro h
    refine ⟨a.symm y,?_,by simp⟩
    simpa only [a.symm_apply_apply] using adj_aut G (isAut_symm G hab) h
  · rintro ⟨z,hz,rfl⟩
    exact adj_aut G hab hz

theorem neighborClusterMoment_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    neighborClusterMoment G hloc p (a x) = neighborClusterMoment G hloc p x := by
  simp only [neighborClusterMoment,neighbors_covariant G hloc hab,Finset.sum_map,Equiv.coe_toEmbedding,
    distinctClusterMoment_covariant G hloc p hab]

theorem neighborMoment_le_rootMoment [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcov : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i) (p : unitInterval) (x : V) :
    neighborClusterMoment G hloc p x ≤ c*rootNeighborMoment G hloc root weight p := by
  obtain ⟨i,a,b,hab,hax⟩ := hcov x
  rw [←hax,neighborClusterMoment_covariant G hloc p hab]
  calc
    _ ≤ (c*weight i)*neighborClusterMoment G hloc p (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) (neighborClusterMoment_nonneg G hloc p _)
    _ = c*(weight i*neighborClusterMoment G hloc p (root i)) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (neighborClusterMoment_nonneg G hloc p _)) (Finset.mem_univ i)) hc

end DistinctClusterMoments
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
open MeasureTheory
section ExposedBoundaryPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_exposedVertexPotential [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    Integrable (exposedVertexPotential G p x a b) (law p) := by
  have he : exposedVertexPotential G p x a b = {ω | Conn G ω x a}.indicator (freshExteriorMoment G p a b) := by
    funext ω
    simp only [exposedVertexPotential,Set.indicator,Set.mem_ofPred_eq]
  rw [he]
  exact (integrable_freshExteriorMoment G hloc hqt p hp a b).indicator (measurableSet_conn G x a)

theorem integral_exposedVertexPotential_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    (∫ ω, exposedVertexPotential G p x a b ω ∂law p) ≤ distinctClusterMoment G p a b := by
  rw [←show (∫ ω, freshExteriorMoment G p a b ω ∂law p) = distinctClusterMoment G p a b from
    integral_freshExteriorMoment G hloc hqt p hp a b]
  apply integral_mono (integrable_exposedVertexPotential G hloc hqt p hp x a b)
    (integrable_freshExteriorMoment G hloc hqt p hp a b)
  intro ω
  unfold exposedVertexPotential
  split_ifs
  · rfl
  · exact freshExteriorMoment_nonneg G p a b ω

theorem exposedBoundaryPotential_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x v : V) (M : ℕ) (ω : Set E) :
    ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M =
      ∑ a ∈ (finite_reachBall hloc v M).toFinset,
        ∑ b ∈ neighbors G hloc a, exposedVertexPotential G p x a b ω := by
  unfold deletedBoundaryPotential
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : Conn G ω x a
  · have hc := cluster_eq_of_conn G ω ha
    have hn : a ∉ (cluster G ω x)ᶜ := by exact not_not.mpr ha
    simp only [ite_eq_left hn,Finset.mul_sum]
    simp only [exposedVertexPotential,ite_eq_left ha,freshExteriorMoment,hc]
  · have hn : ¬a ∉ (cluster G ω x)ᶜ := by exact not_not.mpr ha
    simp only [ite_eq_right hn,mul_zero,exposedVertexPotential,ite_eq_right ha,Finset.sum_const_zero]

 

theorem integral_exposedBoundaryPotential_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x v : V) (M : ℕ) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M) (law p) ∧
    (∫ ω, ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M ∂law p) ≤
      ∑ a ∈ (finite_reachBall hloc v M).toFinset, neighborClusterMoment G hloc p a := by
  simp_rw [exposedBoundaryPotential_eq G hloc p x v M]
  have hi (a : V) := integrable_finsetSum (neighbors G hloc a)
    (fun b _ => integrable_exposedVertexPotential G hloc hqt p hp x a b)
  refine ⟨integrable_finsetSum _ (fun a _ => hi a),?_⟩
  rw [integral_finsetSum _ (fun a _ => hi a)]
  apply Finset.sum_le_sum
  intro a _
  rw [integral_finsetSum _ (fun b _ => integrable_exposedVertexPotential G hloc hqt p hp x a b)]
  exact Finset.sum_le_sum (fun b _ => integral_exposedVertexPotential_le G hloc hqt p hp x a b)

end ExposedBoundaryPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformExposedBoundary
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_ncard_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (M : ℕ) :
    (reachBall G (a x) M).ncard = (reachBall G x M).ncard := by
  have he : reachBall G (a x) M = a '' reachBall G x M := by
    ext y
    constructor
    · intro h
      exact ⟨a.symm y,by simpa only [Equiv.symm_apply_apply] using mem_reachBall_aut G (isAut_symm G hab) h,by simp⟩
    · rintro ⟨z,hz,rfl⟩
      exact mem_reachBall_aut G hab hz
  rw [he,Set.ncard_image_of_injective _ a.injective]

theorem reachBall_card_le_root_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (M : ℕ) (x : V) : (finite_reachBall hloc x M).toFinset.card ≤
      ∑ i, (reachBall G (root i) M).ncard := by
  obtain ⟨i,a,b,hab,hax⟩ := hcover x
  rw [←Set.ncard_eq_toFinset_card (reachBall G x M) (finite_reachBall hloc x M),←hax,reachBall_ncard_covariant G hab]
  exact Finset.single_le_sum (f := fun i => (reachBall G (root i) M).ncard) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem rootNeighborMoment_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) : 0 ≤ rootNeighborMoment G hloc root weight p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (neighborClusterMoment_nonneg G hloc p _))

 

theorem integral_exposedBoundaryPotential_uniform [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (x v : V) (M : ℕ) :
    (∫ ω, ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M ∂law p) ≤
      (∑ i, ((reachBall G (root i) M).ncard:ℝ))*c*rootNeighborMoment G hloc root weight p := by
  let B := (finite_reachBall hloc v M).toFinset
  calc
    _ ≤ ∑ a ∈ B, neighborClusterMoment G hloc p a :=
      (integral_exposedBoundaryPotential_le G hloc hqt p hp x v M).2
    _ ≤ ∑ _a ∈ B, c*rootNeighborMoment G hloc root weight p :=
      Finset.sum_le_sum (fun a _ => neighborMoment_le_rootMoment G hloc root weight hw hcover c hc hmin p a)
    _ = (B.card:ℝ)*(c*rootNeighborMoment G hloc root weight p) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hb : (B.card:ℝ) ≤ ∑ i, ((reachBall G (root i) M).ncard:ℝ) := by
        exact_mod_cast reachBall_card_le_root_sum G hloc root hcover M v
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb
        (mul_nonneg hc (rootNeighborMoment_nonneg G hloc root weight hw p))

end UniformExposedBoundary
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctMomentPotential
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem kernel_distinctMoment_integral [Countable V] [Countable E] [Nonempty V]
    (q : LocalEndpointRule G hloc O M L) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x v : V) :
    (∑' y, q.kernel p v y * distinctClusterMoment G p x y) =
      ∫ ω, (∑' y, q.kernel p v y * freshExteriorMoment G p x y ω) ∂law p := by
  rw [integral_tsum_of_finite_support (law p) (finite_reachBall hloc v M).toFinset _
    (fun y => (integrable_freshExteriorMoment G hloc hqt p hp x y).const_mul (q.kernel p v y))
    (fun ω y hy => by rw [q.kernel_outside_ball_zero p v y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul])]
  apply tsum_congr
  intro y
  rw [integral_const_mul,integral_freshExteriorMoment G hloc hqt p hp]
  rfl

theorem integrable_kernel_freshMoment [Countable V] [Countable E] [Nonempty V]
    (q : LocalEndpointRule G hloc O M L) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x v : V) :
    Integrable (fun ω => ∑' y, q.kernel p v y * freshExteriorMoment G p x y ω) (law p) := by
  have he (ω) : (∑' y, q.kernel p v y * freshExteriorMoment G p x y ω) =
      ∑ y ∈ (finite_reachBall hloc v M).toFinset, q.kernel p v y * freshExteriorMoment G p x y ω :=
    tsum_eq_sum (fun y hy => by rw [q.kernel_outside_ball_zero p v y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul])
  simp_rw [he]
  exact integrable_finsetSum _ (fun y _ => (integrable_freshExteriorMoment G hloc hqt p hp x y).const_mul _)

 
theorem kernel_distinctMoment_bound [Countable V] [Countable E] [Nonempty V]
    (q : LocalEndpointRule G hloc O M L) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G) (x v : V) :
    (∑' y, q.kernel p v y * distinctClusterMoment G p x y) ≤
      (1+(1-(p:ℝ))/p*M)*distinctClusterMoment G p x v +
        (p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c*rootNeighborMoment G hloc root weight p := by
  let C := 1+(1-(p:ℝ))/p*M
  let R := (p:ℝ)^(-(M:ℤ))
  let b := fun ω : Set E => ((cluster G ω x).ncard:ℝ)*deletedBoundaryPotential G hloc (cluster G ω x)ᶜ p v M
  have hi := (integral_exposedBoundaryPotential_le G hloc hqt p hpc x v M).1
  have hpoint (ω : Set E) : (∑' y, q.kernel p v y * freshExteriorMoment G p x y ω) ≤
      C*freshExteriorMoment G p x v ω + R*b ω := by
    have h := mul_le_mul_of_nonneg_left (q.kernel_deleted_potential_bound hqt (cluster G ω x)ᶜ p hp hpc v)
      (Nat.cast_nonneg (cluster G ω x).ncard : (0:ℝ) ≤ _)
    rw [←tsum_mul_left] at h
    calc
      _ = ∑' y, ((cluster G ω x).ncard:ℝ)*(q.kernel p v y * inducedSusceptibility G (cluster G ω x)ᶜ p y) := by
        apply tsum_congr
        intro y
        simp only [freshExteriorMoment]
        ring
      _ ≤ _ := h
      _ = _ := by dsimp [C,R,b,freshExteriorMoment]; ring
  rw [q.kernel_distinctMoment_integral hqt p hpc x v]
  calc
    _ ≤ ∫ ω, C*freshExteriorMoment G p x v ω + R*b ω ∂law p :=
      integral_mono (q.integrable_kernel_freshMoment hqt p hpc x v)
        (((integrable_freshExteriorMoment G hloc hqt p hpc x v).const_mul C).add (hi.const_mul R)) hpoint
    _ = C*distinctClusterMoment G p x v + R*(∫ ω, b ω ∂law p) := by
      rw [integral_add ((integrable_freshExteriorMoment G hloc hqt p hpc x v).const_mul C) (hi.const_mul R),
        integral_const_mul,integral_const_mul,integral_freshExteriorMoment G hloc hqt p hpc]
      rfl
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (integral_exposedBoundaryPotential_uniform G hloc hqt root weight hw hcover c hc hmin p hpc x v M)
        (zpow_nonneg p.2.1 (-(M:ℤ)))
      dsimp [C,R,b] at *
      nlinarith

end LocalEndpointRule
end DistinctMomentPotential
end Percolation

 
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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePotentialIteration
attribute [local instance] Classical.propDecidable Classical.decEq

theorem realAction_mono (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (f g : V → ℝ) (hfg : ∀ x, f x ≤ g x) (x : V) : realAction A f x ≤ realAction A g x := by
  exact (finiteKernel_summable_mul _ ha x f).tsum_le_tsum
    (fun y => mul_le_mul_of_nonneg_left (hfg y) (hA x y).2) (finiteKernel_summable_mul _ ha x g)

theorem realAction_affine (A : Hilbert V →L[ℂ] Hilbert V)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (f : V → ℝ) (a b : ℝ) (x : V) :
    realAction A (fun y => a*f y+b) x = a*realAction A f x + b*realAction A (fun _ => 1) x := by
  unfold realAction
  simp_rw [mul_add]
  rw [Summable.tsum_add]
  · have he (y : V) : (matrixCoeff A x y).re*(a*f y) = a*((matrixCoeff A x y).re*f y) := by ring
    simp_rw [he]
    simp only [tsum_mul_left,tsum_mul_right,mul_one]
    ring
  · exact finiteKernel_summable_mul _ ha x (fun y => a*f y)
  · exact finiteKernel_summable_mul _ ha x (fun _ => b)

theorem realAction_pow_succ (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (j : ℕ) (f : V → ℝ) (x : V) :
    realAction (A^(j+1)) f x = realAction A (realAction (A^j) f) x := by
  rw [pow_succ']
  exact finite_positive_product_action A (A^j) hA ha (finite_positive_pow_support A hA ha j) f x

 

theorem realAction_pow_potential_bound (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1)
    (f : V → ℝ) (Z B : ℝ) (hZ : 2 ≤ Z) (hB : 0 ≤ B)
    (hf : ∀ x, realAction A f x ≤ Z*f x+B) (j : ℕ) (x : V) :
    realAction (A^j) f x ≤ Z^j*f x + B*(Z^j-1) := by
  have hz : 0 ≤ Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  induction j generalizing x with
  | zero =>
      simp only [pow_zero,realAction,positive_identity_action,one_mul,sub_self,mul_zero,add_zero,le_refl]
  | succ j ih =>
      rw [realAction_pow_succ A hA ha]
      calc
        _ ≤ realAction A (fun y => Z^j*f y+B*(Z^j-1)) x := realAction_mono A hA ha _ _ ih x
        _ = Z^j*realAction A f x + (B*(Z^j-1))*realAction A (fun _ => 1) x := realAction_affine A ha f _ _ x
        _ ≤ Z^j*(Z*f x+B) + B*(Z^j-1) := add_le_add
          (mul_le_mul_of_nonneg_left (hf x) (pow_nonneg hz _))
          (by
            simpa only [mul_one] using (mul_le_mul_of_nonneg_left (hrow x)
              (mul_nonneg hB (sub_nonneg.mpr (one_le_pow₀ hz1)))))
        _ ≤ Z^(j+1)*f x+B*(Z^(j+1)-1) := by
          have hh := mul_nonneg (mul_nonneg hB (pow_nonneg hz j)) (show 0 ≤ Z-2 by linarith)
          rw [pow_succ]
          nlinarith only [hh]

theorem realAction_pow_potential_at_zero (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1)
    (f : V → ℝ) (Z B : ℝ) (hZ : 2 ≤ Z) (hB : 0 ≤ B)
    (hf : ∀ x, realAction A f x ≤ Z*f x+B) (j : ℕ) (x : V) (hx : f x = 0) :
    realAction (A^j) f x ≤ B*Z^j := by
  have h := realAction_pow_potential_bound A hA ha hrow f Z B hZ hB hf j x
  rw [hx,mul_zero,zero_add] at h
  nlinarith

end PositivePotentialIteration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedPositiveOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem normalized_operator_positive (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) : PositiveRealMatrix A := by
  intro x y
  rw [hA]
  exact ⟨rfl,mul_nonneg (inv_nonneg.mpr (q.successProbability_nonneg p o)) (q.kernel_nonneg p x y)⟩

theorem normalized_operator_finite (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) (x : V) :
    (Function.support (fun y => (matrixCoeff A x y).re)).Finite := by
  apply (finite_reachBall hloc x M).subset
  intro y hy
  by_contra hn
  apply hy
  change (matrixCoeff A x y).re = 0
  simp only [hA,normalizedKernel,q.kernel_outside_ball_zero p x y hn,mul_zero,Complex.ofReal_zero,Complex.zero_re]

theorem normalized_operator_action (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) (f : V → ℝ) (x : V) :
    realAction A f x = (q.successProbability p o)⁻¹ * (∑' y, q.kernel p x y*f y) := by
  simp only [realAction,hA,Complex.ofReal_re,normalizedKernel,mul_assoc,tsum_mul_left]

theorem normalized_operator_row_le (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (hu : 0 < q.successProbability p o) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) (x : V) :
    realAction A (fun _ => 1) x ≤ 1 := by
  rw [q.normalized_operator_action o p A hA]
  simp only [mul_one]
  calc
    _ ≤ (q.successProbability p o)⁻¹ * q.successProbability p o :=
      mul_le_mul_of_nonneg_left (q.kernel_row_le_success o p x) (inv_nonneg.mpr hu.le)
    _ = 1 := inv_mul_cancel₀ hu.ne'

theorem normalized_operator_row_eq (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (hu : 0 < q.successProbability p o) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) (x : V)
    (hx : x ∈ vertexOrbit G o) : realAction A (fun _ => 1) x = 1 := by
  rw [q.normalized_operator_action o p A hA]
  simp only [mul_one]
  change (q.successProbability p o)⁻¹ * q.successProbability p x = 1
  rw [q.successProbability_orbit p o x hx,inv_mul_cancel₀ hu.ne']

theorem normalized_operator_invariant (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ)) :
    KernelInvariant (vertexAut G) A := by
  rintro a ⟨b,hab⟩ x y
  simp only [hA,normalizedKernel,q.kernel_covariant p a b hab]

theorem normalized_operator_end_support (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ))
    (x y : V) (hy : y ∉ vertexOrbit G o) : (matrixCoeff A x y).re = 0 := by
  simp only [hA,normalizedKernel,q.kernel_zero_of_end_not_mem p x y hy,mul_zero,Complex.ofReal_zero,Complex.zero_re]

end LocalEndpointRule
end NormalizedPositiveOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UpperDistinctMomentIteration
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinctClusterMoment_self (G : BondGraph V E) (p : unitInterval) (x : V) :
    distinctClusterMoment G p x x = 0 := by
  have hs (ω : Set E) : Conn G ω x x := .refl
  simp only [distinctClusterMoment,hs,not_true_eq_false,ite_false,integral_zero]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem normalized_power_distinctMoment_upper [Countable V] [Countable E] [Nonempty V]
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G)
    (hu : 0 < q.successProbability p o)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel o p x y : ℂ))
    (Z : ℝ) (hZ : 2 ≤ Z)
    (hscale : (q.successProbability p o)⁻¹*(1+(1-(p:ℝ))/p*M) ≤ Z)
    (j : ℕ) (x : V) :
    realAction (A^j) (distinctClusterMoment G p x) x ≤
      ((q.successProbability p o)⁻¹*(p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c)*
        rootNeighborMoment G hloc root weight p * Z^j := by
  let B := ((q.successProbability p o)⁻¹*(p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c)*
    rootNeighborMoment G hloc root weight p
  have hB : 0 ≤ B := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr hu.le) (zpow_nonneg p.2.1 _))
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))) hc)
      (rootNeighborMoment_nonneg G hloc root weight hw p)
  have hf (v : V) : realAction A (distinctClusterMoment G p x) v ≤ Z*distinctClusterMoment G p x v+B := by
    rw [q.normalized_operator_action o p A hA]
    calc
      _ ≤ (q.successProbability p o)⁻¹ *
          ((1+(1-(p:ℝ))/p*M)*distinctClusterMoment G p x v+
            (p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c*rootNeighborMoment G hloc root weight p) :=
        mul_le_mul_of_nonneg_left
          (q.kernel_distinctMoment_bound hqt root weight hw hcover c hc hmin p hp hpc x v) (inv_nonneg.mpr hu.le)
      _ = ((q.successProbability p o)⁻¹*(1+(1-(p:ℝ))/p*M))*distinctClusterMoment G p x v+B := by dsimp [B]; ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hscale (distinctClusterMoment_nonneg G p x v)
        linarith
  exact realAction_pow_potential_at_zero A (q.normalized_operator_positive o p A hA)
    (q.normalized_operator_finite o p A hA) (q.normalized_operator_row_le o p hu A hA)
    (distinctClusterMoment G p x) Z B hZ hB hf j x (distinctClusterMoment_self G p x)

end LocalEndpointRule
end UpperDistinctMomentIteration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePowerStochasticity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem realAction_pow_row_le (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1) (j : ℕ) (x : V) :
    realAction (A^j) (fun _ => 1) x ≤ 1 := by
  induction j generalizing x with
  | zero => rw [pow_zero]; exact (positive_identity_action (fun _ => 1) x).le
  | succ j ih =>
      rw [realAction_pow_succ A hA ha]
      exact (realAction_mono A hA ha _ (fun _ => 1) ih x).trans (hrow x)

theorem positive_pow_end_support (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (O : Set V) (hO : ∀ x y, y ∉ O → (matrixCoeff A x y).re = 0)
    (j : ℕ) (x y : V) (hx : x ∈ O) (hy : y ∉ O) : (matrixCoeff (A^j) x y).re = 0 := by
  cases j with
  | zero =>
      have hxy : x ≠ y := fun h => hy (h ▸ hx)
      simp only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right hxy,Complex.zero_re]
  | succ j =>
      rw [pow_succ,←((hA.pow j).mul_hasSum A x y).tsum_eq]
      simp only [hO _ y hy,mul_zero,tsum_zero]

theorem realAction_pow_row_eq_on (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (O : Set V) (hO : ∀ x y, y ∉ O → (matrixCoeff A x y).re = 0)
    (hrow : ∀ x ∈ O, realAction A (fun _ => 1) x = 1)
    (j : ℕ) (x : V) (hx : x ∈ O) : realAction (A^j) (fun _ => 1) x = 1 := by
  induction j generalizing x with
  | zero => rw [pow_zero]; exact positive_identity_action (fun _ => 1) x
  | succ j ih =>
      rw [realAction_pow_succ A hA ha]
      calc
        _ = realAction A (fun _ => 1) x := by
          apply tsum_congr
          intro y
          by_cases hy : y ∈ O
          · rw [ih y hy]
          · rw [hO x y hy,zero_mul,zero_mul]
        _ = 1 := hrow x hx

end PositivePowerStochasticity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectedMomentLoss
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_connected_cluster_square [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fun ω => if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) (law p) := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  have he : (fun ω : Set E => if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) =
      {ω | Conn G ω x y}.indicator (fun ω => ((cluster G ω x).ncard:ℝ)^2) := by
    funext ω
    simp only [Set.indicator,Set.mem_ofPred_eq]
  rw [he]
  exact (hs x).1.indicator (measurableSet_conn G x y)

theorem distinct_add_connected_cluster_moment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    distinctClusterMoment G p x y + connectedClusterMoment G p x y =
      ∫ ω, ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) ∂law p := by
  rw [distinctClusterMoment,connectedClusterMoment,
    ←integral_add (integrable_distinct_cluster_product G hloc hqt p hp x y)
      (integrable_connected_cluster_square G hloc hqt p hp x y)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases h : Conn G ω x y
    · simp only [h,not_true_eq_false,ite_false,ite_true,zero_add,cluster_eq_of_conn G ω h,pow_two]
    · simp only [h,not_false_eq_true,ite_true,ite_false,add_zero])

theorem distinctClusterMoment_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    susceptibility G p x * susceptibility G p y - connectedClusterMoment G p x y ≤
      distinctClusterMoment G p x y := by
  have h := (subcritical_cluster_association G hloc hqt p hp x y).2
  rw [←distinct_add_connected_cluster_moment G hloc hqt p hp] at h
  linarith

 
theorem realAction_connectedMoment_eq_diagonalLoss [Countable V] [Countable E]
    (G : BondGraph V E) (o : V) (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1)
    (x : V) (hend : ∀ y, y ∉ vertexOrbit G o → (matrixCoeff A x y).re = 0)
    (p : unitInterval) (hs : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p)) :
    realAction A (connectedClusterMoment G p x) x =
      ∫ ω, diagonalLossMass G o (fun a b => (matrixCoeff A a b).re) ω x ∂law p := by
  have hr (z : V) (S : Finset V) : (∑ y ∈ S, (matrixCoeff A z y).re) ≤ 1 := by
    have hsrow : Summable (fun y => (matrixCoeff A z y).re) := by
      simpa only [mul_one] using finiteKernel_summable_mul (fun a b => (matrixCoeff A a b).re) ha z (fun _ => 1)
    exact (hsrow.sum_le_tsum S (fun y _ => (hA z y).2)).trans (by simpa only [realAction,mul_one] using hrow z)
  rw [integral_diagonalLoss_eq_series G o _ (fun a b => (hA a b).2) 1 hr x p hs]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ vertexOrbit G o
  · rw [ite_eq_left hy]
    rfl
  · simp only [ite_eq_right hy,hend y hy,zero_mul]

end ConnectedMomentLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LowerDistinctMomentOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem realAction_distinctMoment_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (b : ℝ) (hb : 0 ≤ b)
    (hχ : ∀ x, b ≤ susceptibility G p x)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (ha : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (hinv : KernelInvariant (vertexAut G) A)
    (hrow : ∀ x, realAction A (fun _ => 1) x ≤ 1)
    (heq : realAction A (fun _ => 1) (root i₀) = 1)
    (hend : ∀ y, y ∉ vertexOrbit G (root i₀) → (matrixCoeff A (root i₀) y).re = 0) :
    b^2-‖A‖*(c*rootSusceptibility G root weight p)^3 ≤
      realAction A (distinctClusterMoment G p (root i₀)) (root i₀) := by
  let x := root i₀
  let f := connectedClusterMoment G p x
  have hr (z : V) (S : Finset V) : (∑ y ∈ S, (matrixCoeff A z y).re) ≤ 1 := by
    have hsrow : Summable (fun y => (matrixCoeff A z y).re) := by
      simpa only [mul_one] using finiteKernel_summable_mul (fun a b => (matrixCoeff A a b).re) ha z (fun _ => 1)
    exact (hsrow.sum_le_tsum S (fun y _ => (hA z y).2)).trans (by simpa only [realAction,mul_one] using hrow z)
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  have hf : realAction A f x ≤ ‖A‖*(c*rootSusceptibility G root weight p)^3 := by
    rw [realAction_connectedMoment_eq_diagonalLoss G (root i₀) A hA ha hrow x hend p (hs x).1]
    exact diagonalLoss_le_rootSusceptibility_cube G hloc hqt root weight Γ htr hΓ hw i₀ hw₀ hcover c hc hmin p hp
      (fun a b => (matrixCoeff A a b).re) (fun a b => (hA a b).2)
      (fun a b hab z y => congrArg Complex.re (hinv a ⟨b,hab⟩ z y)) 1 hr A (hA.real)
  have hpnt (y : V) : (-1)*f y+b^2 ≤ distinctClusterMoment G p x y := by
    have h := distinctClusterMoment_lower G hloc hqt p hp x y
    have hprod : b*b ≤ susceptibility G p x * susceptibility G p y :=
      mul_le_mul (hχ x) (hχ y) hb (susceptibility_nonneg G p x)
    dsimp [f]
    nlinarith only [h,hprod]
  have hi := realAction_mono A hA ha (fun y => (-1)*f y+b^2)
    (distinctClusterMoment G p x) hpnt x
  rw [realAction_affine A ha f (-1) (b^2) x,heq] at hi
  nlinarith only [hi,hf]

end LowerDistinctMomentOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctMomentSandwich
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem normalized_power_moment_sandwich [Countable V] [Countable E] [Nonempty V]
    (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G)
    (hu : 0 < q.successProbability p (root i₀))
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ))
    (a : ℝ) (ha : 0 ≤ a) (hχ : ∀ x, a*rootSusceptibility G root weight p ≤ susceptibility G p x)
    (Z : ℝ) (hZ : 2 ≤ Z)
    (hscale : (q.successProbability p (root i₀))⁻¹*(1+(1-(p:ℝ))/p*M) ≤ Z) (j : ℕ) :
    (a*rootSusceptibility G root weight p)^2 - ‖A‖^j*(c*rootSusceptibility G root weight p)^3 ≤
      ((q.successProbability p (root i₀))⁻¹*(p:ℝ)^(-(M:ℤ))*(∑ i, ((reachBall G (root i) M).ncard:ℝ))*c)*
        rootNeighborMoment G hloc root weight p * Z^j := by
  have hpos := q.normalized_operator_positive (root i₀) p A hA
  have hfin := q.normalized_operator_finite (root i₀) p A hA
  have hrow := q.normalized_operator_row_le (root i₀) p hu A hA
  have hend := q.normalized_operator_end_support (root i₀) p A hA
  have hx : root i₀ ∈ vertexOrbit G (root i₀) := ⟨Equiv.refl V,Equiv.refl E,(fun _ => by simp),rfl⟩
  have hlo := realAction_distinctMoment_lower G hloc hqt root weight Γ htr hΓ hw i₀ hw₀ hcover c hc hmin p hpc
    (a*rootSusceptibility G root weight p) (mul_nonneg ha (rootSusceptibility_nonneg G root weight hw p)) hχ
    (A^j) (hpos.pow j) (finite_positive_pow_support A hpos hfin j)
    ((q.normalized_operator_invariant (root i₀) p A hA).pow j)
    (realAction_pow_row_le A hpos hfin hrow j)
    (realAction_pow_row_eq_on A hpos hfin _ hend
      (q.normalized_operator_row_eq (root i₀) p hu A hA) j (root i₀) hx)
    (positive_pow_end_support A hpos _ hend j (root i₀) · hx)
  have hhi := q.normalized_power_distinctMoment_upper (root i₀) hqt root weight hw hcover c hc hmin p hp hpc hu A hA Z hZ hscale j (root i₀)
  have hpow : ‖A^j‖ ≤ ‖A‖^j := by
    cases j with
    | zero =>
      simp only [pow_zero]
      have he : (1 : Hilbert V →L[ℂ] Hilbert V) = ContinuousLinearMap.id ℂ (Hilbert V) := by ext x; rfl
      rw [he]
      exact ContinuousLinearMap.norm_id_le
    | succ j => exact norm_pow_le' A (Nat.succ_pos j)
  have hn := mul_le_mul_of_nonneg_right hpow
    (pow_nonneg (mul_nonneg hc (rootSusceptibility_nonneg G root weight hw p)) 3)
  linarith

end LocalEndpointRule
end DistinctMomentSandwich
end Percolation

 
namespace Percolation
section LogarithmicPowerChoice

 

theorem exists_logarithmic_power (r h Z T : ℝ) (hr : 0 ≤ r) (hh : 0 < h)
    (hrh : r ≤ Real.exp (-h)) (hZ : 1 ≤ Z) (hT : 1 ≤ T) :
    ∃ j : ℕ, r^j ≤ T⁻¹ ∧ Z^j ≤ Z*T^(Real.log Z/h) := by
  let t := Real.log T/h
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg hT) hh.le
  let j := Nat.ceil t
  have hlo : t ≤ (j:ℝ) := Nat.le_ceil t
  have hhi : (j:ℝ) ≤ t+1 := (Nat.ceil_lt_add_one ht).le
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  refine ⟨j,?_,?_⟩
  · calc
      r^j ≤ (Real.exp (-h))^j := pow_le_pow_left₀ hr hrh j
      _ = Real.exp ((j:ℝ)*(-h)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-Real.log T) := by
        apply Real.exp_le_exp.mpr
        have hl : Real.log T ≤ (j:ℝ)*h := (div_le_iff₀ hh).mp hlo
        nlinarith
      _ = T⁻¹ := by rw [Real.exp_neg,Real.exp_log hTp]
  · calc
      Z^j = Real.exp ((j:ℝ)*Real.log Z) := by rw [Real.exp_nat_mul,Real.exp_log hZp]
      _ ≤ Real.exp ((t+1)*Real.log Z) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hlogZ)
      _ = Z*T^(Real.log Z/h) := by
        rw [Real.rpow_def_of_pos hTp,←Real.exp_log hZp,←Real.exp_add]
        simp only [Real.log_exp]
        congr 1
        dsimp [t]
        ring

 

theorem moment_sandwich_power_law (a c C Z h r χ N : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) (hZ : 1 ≤ Z) (hh : 0 < h)
    (hr : 0 ≤ r) (hrh : r ≤ Real.exp (-h)) (hχ : 1 ≤ χ) (hN : 0 ≤ N)
    (hs : ∀ j : ℕ, (a*χ)^2-r^j*(c*χ)^3 ≤ C*N*Z^j) :
    let T := 1+2*c^3/a^2
    a^2/(2*C*Z*T^(Real.log Z/h))*χ^(2-Real.log Z/h) ≤ N := by
  let T := 1+2*c^3/a^2
  have hap : 0 < a^2 := sq_pos_of_pos ha
  have hT : 1 ≤ T := by
    have hn : 0 ≤ 2*c^3/a^2 := by positivity
    dsimp [T]
    linarith
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hχp : 0 < χ := zero_lt_one.trans_le hχ
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hTx : 1 ≤ T*χ := by nlinarith
  obtain ⟨j,hrj,hZj⟩ := exists_logarithmic_power r h Z (T*χ) hr hh hrh hZ hTx
  have hbudget : 2*c^3 ≤ a^2*T := by dsimp [T]; field_simp; nlinarith
  have hsmall : r^j*(c*χ)^3 ≤ a^2/2*χ^2 := by
    calc
      _ ≤ (T*χ)⁻¹*(c*χ)^3 := mul_le_mul_of_nonneg_right hrj (pow_nonneg (mul_nonneg hc hχp.le) _)
      _ = c^3/T*χ^2 := by field_simp
      _ ≤ a^2/2*χ^2 := mul_le_mul_of_nonneg_right ((div_le_iff₀ hTp).mpr (by nlinarith [hbudget])) (sq_nonneg χ)
  have hlarge : a^2/2*χ^2 ≤ C*N*(Z*(T*χ)^(Real.log Z/h)) := by
    have hs' := hs j
    have hprod := mul_le_mul_of_nonneg_left hZj (mul_nonneg hC.le hN)
    nlinarith only [hsmall,hs',hprod]
  have hpow : 0 < χ^(Real.log Z/h) := Real.rpow_pos_of_pos hχp _
  have hTpow : 0 < T^(Real.log Z/h) := Real.rpow_pos_of_pos hTp _
  have he : C*N*(Z*(T*χ)^(Real.log Z/h)) =
      (C*Z*T^(Real.log Z/h))*N*χ^(Real.log Z/h) := by
    rw [Real.mul_rpow hTp.le hχp.le]
    ring
  rw [he] at hlarge
  have hden : 0 < 2*C*Z*T^(Real.log Z/h) := by positivity
  change a^2/(2*C*Z*T^(Real.log Z/h))*χ^(2-Real.log Z/h) ≤ N
  rw [Real.rpow_sub hχp,Real.rpow_two]
  calc
    _ = (a^2*χ^2)/(2*C*Z*T^(Real.log Z/h)*χ^(Real.log Z/h)) := by
      rw [div_mul_div_comm]
    _ ≤ N := (div_le_iff₀ (mul_pos hden hpow)).mpr (by nlinarith only [hlarge])

end LogarithmicPowerChoice
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section ProfileContinuity
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

theorem exp_neg_H (q : EndpointProfile G hloc p₀ o s) : Real.exp (-q.H) = ‖q.op‖ := by
  rw [H,one_div,Real.log_inv,neg_neg,Real.exp_log q.norm_pos]

 

theorem exists_nearby_operators {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : EndpointProfile G hloc p₀ (root i₀) s) (hp₀ : 0 < (p₀:ℝ)) :
    ∃ A : unitInterval → (Hilbert V →L[ℂ] Hilbert V),
      (∀ p x y, matrixCoeff (A p) x y = (q.rule.normalizedKernel (root i₀) p x y : ℂ)) ∧
      ∀ᶠ p in nhds p₀, q.rule.successProbability p₀ (root i₀)/2 ≤ q.rule.successProbability p (root i₀) ∧
        ‖A p‖ ≤ Real.exp (-(q.H-1)) ∧ (p₀:ℝ)/2 ≤ (p:ℝ) := by
  obtain ⟨A,_,hA,hcont⟩ := q.rule.exists_continuous_normalized_operators root weight Γ htr hΓ hw i₀ hw₀
  have he : A p₀ = q.op := kernel_extension_unique (hA p₀) q.coeff
  have hnorm : ContinuousAt (fun p => ‖A p‖) p₀ := (hcont p₀ q.success_pos.ne').norm
  have hb : ‖A p₀‖ < Real.exp (-(q.H-1)) := by
    rw [he,←q.exp_neg_H]
    exact Real.exp_lt_exp.mpr (by linarith)
  have ha := hnorm.eventually_lt continuousAt_const hb
  have hu : ∀ᶠ p in nhds p₀, q.rule.successProbability p₀ (root i₀)/2 < q.rule.successProbability p (root i₀) :=
    continuousAt_const.eventually_lt (q.rule.continuous_successProbability (root i₀)).continuousAt (by linarith [q.success_pos])
  have hp : ∀ᶠ p : unitInterval in nhds p₀, (p₀:ℝ)/2 < (p:ℝ) :=
    continuousAt_const.eventually_lt continuous_subtype_val.continuousAt (by linarith)
  refine ⟨A,hA,?_⟩
  filter_upwards [ha,hu,hp] with p ha hu hp
  exact ⟨hu.le,ha.le,hp.le⟩

end EndpointProfile
end ProfileContinuity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section MapScaleBudget
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

theorem potentialScale_pos (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ)) :
    0 < q.potentialScale p₀ := by
  exact mul_pos (inv_pos.mpr q.success_pos) (by
    have hn : 0 ≤ (1-(p₀:ℝ))/p₀*q.cap := mul_nonneg (div_nonneg (sub_nonneg.mpr p₀.2.2) hp₀.le) (Nat.cast_nonneg _)
    linarith)

theorem geometricScale_two_le (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ)) :
    2 ≤ q.geometricScale := by
  have hu : 1 ≤ (q.rule.successProbability p₀ o)⁻¹ :=
    (one_le_inv₀ q.success_pos).mpr (q.rule.successProbability_le_one p₀ o)
  have hb : 0 ≤ (1-(p₀:ℝ))/p₀*q.cap :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr p₀.2.2) hp₀.le) (Nat.cast_nonneg _)
  dsimp [geometricScale,potentialScale]
  nlinarith

theorem eventually_potentialScale_le (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ)) :
    ∀ᶠ p in nhds p₀, q.potentialScale p ≤ q.geometricScale := by
  have hu := (q.rule.continuous_successProbability o).continuousAt.inv₀ q.success_pos.ne'
  have hv : ContinuousAt (fun p : unitInterval => ((1-(p:ℝ))/p)) p₀ :=
    (continuousAt_const.sub continuous_subtype_val.continuousAt).div continuous_subtype_val.continuousAt hp₀.ne'
  have he : ContinuousAt q.potentialScale p₀ := hu.mul (continuousAt_const.add (hv.mul continuousAt_const))
  have hlt : q.potentialScale p₀ < q.geometricScale := by
    dsimp only [geometricScale]
    linarith [q.potentialScale_pos hp₀]
  filter_upwards [he.eventually_lt continuousAt_const hlt] with p hp
  exact hp.le

end EndpointProfile
end MapScaleBudget
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section ProfileNeighborMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

 

theorem eventually_neighborMoment_lower_oai [Countable V] [Countable E] [Nonempty V]
    (hconn : Connected G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (q : EndpointProfile G hloc p₀ (root i₀) s) (hp₀ : 0 < (p₀:ℝ)) (hH : 1 < q.H) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ p in nhds p₀, p < pc G →
      b*(rootSusceptibility G root weight p)^(2-Real.log q.geometricScale/(q.H-1)) ≤
        rootNeighborMoment G hloc root weight p := by
  obtain ⟨a,ha,hχ⟩ := exists_rootSusceptibility_lower G hconn hloc hqt root weight hw hw1 hcover
    ((p₀:ℝ)/2) (by linarith)
  obtain ⟨A,hA,hnear⟩ := q.exists_nearby_operators root weight Γ htr hΓ hw i₀ hw₀ hp₀
  let B : unitInterval → ℝ := fun p =>
    (q.rule.successProbability p (root i₀))⁻¹*(p:ℝ)^(-(q.cap:ℤ))*(∑ i, ((reachBall G (root i) q.cap).ncard:ℝ))*c
  have hB (p : unitInterval) : 0 ≤ B p := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (q.rule.successProbability_nonneg p _))
      (zpow_nonneg p.2.1 _)) (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))) hc
  have hBc : ContinuousAt B p₀ := by
    exact ((((q.rule.continuous_successProbability (root i₀)).continuousAt.inv₀ q.success_pos.ne').mul
      (continuous_subtype_val.continuousAt.zpow₀ (-(q.cap:ℤ)) (Or.inl hp₀.ne'))).mul continuousAt_const).mul continuousAt_const
  let C := B p₀+1
  have hC : 0 < C := by dsimp [C]; linarith [hB p₀]
  have hCB : ∀ᶠ p in nhds p₀, B p ≤ C := by
    filter_upwards [hBc.eventually_lt continuousAt_const (show B p₀ < C by dsimp [C]; linarith)] with p hp
    exact hp.le
  let Z := q.geometricScale
  let h := q.H-1
  let T := 1+2*c^3/a^2
  let b := a^2/(2*C*Z*T^(Real.log Z/h))
  have hz : 2 ≤ Z := q.geometricScale_two_le hp₀
  have ht : 0 < T := by
    have hh : 0 ≤ 2*c^3/a^2 := by positivity
    dsimp [T]
    linarith
  have hb : 0 < b := div_pos (sq_pos_of_pos ha) (by
    have hp := Real.rpow_pos_of_pos ht (Real.log Z/h)
    have hZp : 0 < Z := by linarith
    positivity)
  refine ⟨b,hb,?_⟩
  filter_upwards [hnear,hCB,q.eventually_potentialScale_le hp₀] with p hnear hCB hscale
  intro hpc
  obtain ⟨hu,hAn,hpp⟩ := hnear
  have hp : 0 < (p:ℝ) := lt_of_lt_of_le (by linarith : 0 < (p₀:ℝ)/2) hpp
  have hup : 0 < q.rule.successProbability p (root i₀) :=
    lt_of_lt_of_le (by linarith [q.success_pos]) hu
  have hχ1 : 1 ≤ rootSusceptibility G root weight p := by
    calc
      1 = ∑ i, weight i*1 := by simp only [mul_one,hw1]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (susceptibility_one_le G hloc hqt p hpc (root i)) (hw i))
  apply moment_sandwich_power_law a c C Z h ‖A p‖ (rootSusceptibility G root weight p)
    (rootNeighborMoment G hloc root weight p) ha hc hC (by linarith) (by dsimp [h]; linarith)
    (norm_nonneg _) hAn hχ1 (rootNeighborMoment_nonneg G hloc root weight hw p)
  intro j
  have hs := q.rule.normalized_power_moment_sandwich hqt root weight Γ htr hΓ hw i₀ hw₀ hcover c hc hmin p hp hpc hup
    (A p) (hA p) a ha.le (hχ p hpp hpc) Z hz hscale j
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCB (rootNeighborMoment_nonneg G hloc root weight hw p)) (pow_nonneg (by linarith) j))

end EndpointProfile
end ProfileNeighborMoment
end Percolation


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower_oai.{u, v, u_1} := @OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower_oai.{u, v, u_1}
