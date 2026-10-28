-- Prove2me | solution 1 for OAI.Percolation.critical_rootTriangleSqrt_derivative_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:33:24.697643+00:00
-- url     : https://prove2.me/submissions/4b7beb01-b5dc-40e6-815e-8fff2112ffb8

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_efficient_endpoint_profiles_of_divergent_moment_bs

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

theorem conn_univ_of_connected (h : Connected G) (x y : V) : Conn G Set.univ x y := by
  apply Relation.ReflTransGen.mono (r := Adj G) ?_ x y (h x y)
  rintro a b ⟨e, he⟩
  exact ⟨e, Set.mem_univ _, he⟩

end Deterministic

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

end Kernel

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

 
theorem map_openEdges (p : unitInterval) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p) =
      law p := by
  unfold law
  rw [setBernoulli_eq_map]
  have hmeas : Measurable (fun labels : E → unitInterval => fun e => labels e ≤ p) :=
    Measurable.of_eval (fun e => (measurable_threshold p).comp (measurable_pi_apply e))
  have he : (fun labels : E → unitInterval => openEdges labels p) =
      (fun f : E → Prop => {e | f e}) ∘ (fun labels e => labels e ≤ p) := rfl
  rw [he, ← Measure.map_map measurable_setOfPred hmeas]
  unfold labelLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_threshold p)]
  simp only [map_threshold, Set.mem_univ, bernoulliMeasure_def]

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

section CouplingOrder
variable [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
theorem measurable_openEdges (p : unitInterval) :
    Measurable (fun labels : E → unitInterval => openEdges labels p) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_threshold p).comp (measurable_pi_apply e)))

theorem twoPoint_eq_labelLaw (p : unitInterval) (x y : V) :
    twoPoint G p x y =
      (labelLaw {labels : E → unitInterval | Conn G (openEdges labels p) x y}).toReal := by
  unfold twoPoint
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p)
    (measurableSet_conn G x y)]
  rfl

omit [Countable E] in
theorem openEdges_mono (labels : E → unitInterval) : Monotone (openEdges labels) := by
  intro p q hpq e he
  exact he.trans hpq

theorem twoPoint_mono (x y : V) : Monotone (fun p => twoPoint G p x y) := by
  intro p q hpq
  change twoPoint G p x y ≤ twoPoint G q x y
  rw [twoPoint_eq_labelLaw, twoPoint_eq_labelLaw]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro labels h
  exact conn_mono G (openEdges_mono labels hpq) h

end CouplingOrder

section CouplingLimits
open Filter Topology


theorem ae_labels_ne [Countable E] (q : unitInterval) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), ∀ e, labels e ≠ q := by
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  simp only [not_not]
  change labelLaw ((fun labels : E → unitInterval => labels e) ⁻¹' {q}) = 0
  rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton q)]
  change (Measure.infinitePi (fun _ : E => (volume : Measure unitInterval))).map
    (fun labels => labels e) {q} = 0
  rw [Measure.infinitePi_map_eval]
  simp

end CouplingLimits

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

theorem measurableSet_infinite_cluster [Countable E] (G : BondGraph V E) (x : V) :
    MeasurableSet {ω | (cluster G ω x).Infinite} := by
  rw [infinite_cluster_eq_iInter]
  exact MeasurableSet.iInter (measurableSet_clusterLarge G x)


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
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

section SprinklingLaw
attribute [local instance] Classical.propDecidable

 theorem map_bool_or (p a : unitInterval) :
    (Measure.infinitePi (fun b : Bool => bitLaw (pairParameter p a b))).map
      (fun f : Bool → Prop => ∃ b, f b) = bitLaw (sprinkleParameter p a) := by
  let μ := (Measure.infinitePi (fun b : Bool => bitLaw (pairParameter p a b))).map
      (fun f : Bool → Prop => ∃ b, f b)
  have hm : Measurable (fun f : Bool → Prop => ∃ b, f b) := .of_discrete
  have : IsProbabilityMeasure μ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hf : μ.real {False} = (1-(p : ℝ)) * (1-(a : ℝ)) := by
    change ((Measure.infinitePi _).map _).real _ = _
    rw [Measure.real, Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun f : Bool → Prop => ∃ b, f b) ⁻¹' ({False} : Set Prop) =
        ((Finset.univ : Finset Bool) : Set Bool).pi (fun _ => ({False} : Set Prop)) := by
      ext f
      simp [and_comm]
    rw [he, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    simp [pairParameter, bitLaw, ENNReal.toReal_mul]
  have ht : μ.real {True} = (p : ℝ) + (1-p)*a := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext b; simp
    rw [he, measureReal_compl (measurableSet_singleton _), probReal_univ, hf]
    ring
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (sprinkleParameter p a)).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [ht]
    simp [bitLaw, Measure.real, sprinkleParameter]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hf]
    simp [bitLaw, Measure.real, sprinkleParameter]
    ring

 theorem measurable_fieldUnion : Measurable (fieldUnion : (Bool → Set E) → Set E) := by
  have hm (e : E) : Measurable (fun f : Bool → Set E => e ∈ fieldUnion f) := by
    apply measurableSet_setOfPred.mp
    change MeasurableSet ({f : Bool → Set E | e ∈ f true} ∪ {f | e ∈ f false})
    apply MeasurableSet.union <;> apply measurableSet_setOfPred.mpr
    · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp
        (measurable_pi_apply true)
    · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp
        (measurable_pi_apply false)
  exact measurable_setOfPred.comp (Measurable.of_eval hm)

 theorem map_fieldUnion (p a : unitInterval) :
    (fieldLaw p a).map (fieldUnion : (Bool → Set E) → Set E) = law (sprinkleParameter p a) := by
  let μ := fun b : Bool => bitLaw (pairParameter p a b)
  let s := fun f : Bool → E → Prop => fun b => {e | f b e}
  have hs : Measurable s := Measurable.of_eval
    (fun b => measurable_setOfPred.comp (measurable_pi_apply b))
  have hstart : (Measure.infinitePi (fun b : Bool => Measure.infinitePi (fun _ : E => μ b))).map s =
      fieldLaw p a := by
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_setOfPred)]
    congr 1
    funext b
    rw [law, setBernoulli_eq_map]
    rfl
  rw [← hstart, Measure.map_map measurable_fieldUnion hs]
  let f := (MeasurableEquiv.curry Bool E Prop).symm
  let swap := MeasurableEquiv.piCongrLeft (fun _ : E × Bool => Prop) (Equiv.prodComm Bool E)
  let c := MeasurableEquiv.curry E Bool Prop
  let b := fun g : E → Bool → Prop => fun e => ∃ j, g e j
  have hb : Measurable b := Measurable.of_eval
    (fun e => (Measurable.of_discrete : Measurable (fun f : Bool → Prop => ∃ j, f j)).comp
      (measurable_pi_apply e))
  have he : fieldUnion ∘ s = (fun g : E → Prop => {e | g e}) ∘ b ∘ c ∘ swap ∘ f := by
    funext g
    ext e
    simp [fieldUnion, s, b, c, swap, f, Function.comp_def, Bool.exists_bool, or_comm, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]
  rw [he, ← Measure.map_map measurable_setOfPred (hb.comp (c.measurable.comp (swap.measurable.comp f.measurable))),
    ← Measure.map_map hb (c.measurable.comp (swap.measurable.comp f.measurable))]
  rw [← Measure.map_map c.measurable (swap.measurable.comp f.measurable),
    ← Measure.map_map swap.measurable f.measurable]
  rw [Measure.infinitePi_map_curry_symm]
  rw [show (Measure.infinitePi (fun x : Bool × E => μ x.1)).map swap =
      Measure.infinitePi (fun x : E × Bool => μ x.2) from
    Measure.infinitePi_map_piCongrLeft (fun x : E × Bool => μ x.2) (Equiv.prodComm Bool E)]
  rw [Measure.infinitePi_map_curry (fun (_ : E) (j : Bool) => μ j)]
  dsimp only [b]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  have hm : (Measure.infinitePi (fun j : Bool => μ j)).map Exists =
      bitLaw (sprinkleParameter p a) := map_bool_or p a
  rw [hm, law, setBernoulli_eq_map]
  rfl

 theorem fieldLaw_map_pair (p a : unitInterval) :
    (fieldLaw p a).map (fun f : Bool → Set E => (f true, f false)) =
      (law p).prod (law a) := by
  simpa [fieldLaw, pairParameter] using
    (Measure.infinitePi_map_eval_prod (P := fun b : Bool => (law (pairParameter p a b) : Measure (Set E)))
    (by decide : true ≠ false))

 theorem law_map_union (p a : unitInterval) :
    ((law p : Measure (Set E)).prod (law a)).map (fun f => f.1 ∪ f.2) =
      law (sprinkleParameter p a) := by
  rw [← fieldLaw_map_pair p a, Measure.map_map]
  · exact map_fieldUnion p a
  · have h : Measurable (fun f : Set E × Set E => fun e => e ∈ f.1 ∪ f.2) := by
      apply Measurable.of_eval
      intro e
      apply measurableSet_setOfPred.mp
      change MeasurableSet ({f : Set E × Set E | e ∈ f.1} ∪ {f | e ∈ f.2})
      apply MeasurableSet.union <;> apply measurableSet_setOfPred.mpr
      · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_fst
      · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_snd
    exact measurable_setOfPred.comp h
  · exact (measurable_pi_apply true).prodMk (measurable_pi_apply false)

end SprinklingLaw

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

end MarkedFirstMoment

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

section CutFactor
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

omit [Nonempty V] in
 
theorem bernoulliPolynomial_empty_indicator (F : Finset V) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m = ∅ then (1:ℝ) else 0) h = (1-h)^F.card := by
  unfold bernoulliPolynomial
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro m hm hne
    simp [hne]
  · simp


end CutFactor

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



end GoodnessGeometry

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

end FiniteQuadraticForms

section PositiveConnectionKernel
open scoped ComplexOrder Matrix
attribute [local instance] Classical.propDecidable

 

theorem equivalenceMatrix_posSemidef {α : Type*} [Fintype α] (R : Setoid α) :
    Matrix.PosSemidef (fun x y => if R.r x y then (1:ℂ) else 0) := by
  classical
  let : Fintype (Quotient R) := Fintype.ofFinite (Quotient R)
  let J : Matrix (Quotient R) α ℂ := fun q x => if q = Quotient.mk R x then 1 else 0
  have hJ : Jᴴ * J = (fun x y => if R.r x y then (1:ℂ) else 0) := by
    ext x y
    change (∑ q : Quotient R, star (J q x) * J q y) = _
    have hr : R.r y x ↔ R.r x y := ⟨R.symm, R.symm⟩
    simp [J, Quotient.eq, hr]
  rw [← hJ]
  exact Matrix.posSemidef_conjTranspose_mul_self J

theorem connection_quadratic_nonneg (G : BondGraph V E) (ω : Set E)
    (S : Finset V) (f : V → ℂ) :
    0 ≤ ∑ x ∈ S, ∑ y ∈ S,
      star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y := by
  classical
  let R : Setoid S := ⟨fun x y => Conn G ω x y,
    ⟨fun x => conn_refl G ω x, fun h => conn_symm G ω h, fun h h' => conn_trans G ω h h'⟩⟩
  have h := (equivalenceMatrix_posSemidef R).dotProduct_mulVec_nonneg
    (fun x : S => f x)
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply] at h
  change 0 ≤ ∑ x : S, ∑ y : S,
    star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y) at h
  have he : (∑ x : S, ∑ y : S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y)) =
      ∑ x ∈ S, ∑ y ∈ S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y) := by
    rw [Finset.sum_coe_sort S (fun x => ∑ y : S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y))]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_coe_sort S (fun y =>
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y))
  rw [he] at h
  simpa only [mul_assoc] using h

variable [Countable V] [Countable E]

theorem conn_indicator_integrable (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Integrable (fun ω => if Conn G ω x y then (1:ℂ) else 0) (law p) := by
  change Integrable ({ω | Conn G ω x y}.indicator (fun _ => (1:ℂ))) (law p)
  exact (integrable_const (1:ℂ)).indicator (measurableSet_conn G x y)

theorem twoPoint_eq_integral (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (twoPoint G p x y : ℂ) =
      ∫ ω, (if Conn G ω x y then (1:ℂ) else 0) ∂law p := by
  simpa only [Set.indicator, Set.mem_ofPred_eq, Measure.real, twoPoint,
    Complex.real_smul, mul_one] using
    (integral_indicator_const (μ := law p) (1:ℂ) (measurableSet_conn G x y)).symm

theorem twoPoint_quadratic_nonneg (G : BondGraph V E) (p : unitInterval)
    (S : Finset V) (f : V → ℂ) :
    0 ≤ ∑ x ∈ S, ∑ y ∈ S, star (f x) * (twoPoint G p x y : ℂ) * f y := by
  have hi (x y : V) : Integrable
      (fun ω => star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y) (law p) :=
    ((conn_indicator_integrable G p x y).const_mul _).mul_const _
  have hsum : (∑ x ∈ S, ∑ y ∈ S, star (f x) * (twoPoint G p x y : ℂ) * f y) =
      ∫ ω, ∑ x ∈ S, ∑ y ∈ S,
        star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y ∂law p := by
    rw [integral_finsetSum S (fun x _ => integrable_finsetSum S (fun y _ => hi x y))]
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum S (fun y _ => hi x y)]
    apply Finset.sum_congr rfl
    intro y _
    rw [integral_mul_const, integral_const_mul, twoPoint_eq_integral]
  rw [hsum]
  exact integral_nonneg (fun ω => connection_quadratic_nonneg G ω S f)

 

theorem HasKernel.isPositive (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A) : A.IsPositive := by
  have hs : A.toLinearMap.IsSymmetric :=
    symmetric_of_symmetric_kernel A (twoPoint G p) (fun x y => hA x y) (twoPoint_symm G p)
  refine ⟨hs, ?_⟩
  intro f
  apply finiteEmbedding_dense.induction_on f
    (p := fun g => 0 ≤ (inner ℂ (A g) g).re)
  · exact isClosed_le continuous_const (by fun_prop)
  · intro g
    rw [show inner ℂ (A (finiteEmbedding g)) (finiteEmbedding g) =
      inner ℂ (finiteEmbedding g) (A (finiteEmbedding g)) from hs _ _, finiteEmbedding_inner_left]
    simp only [kernel_finiteEmbedding A (twoPoint G p) (fun x y => hA x y)]
    simp_rw [Finset.mul_sum]
    have h := twoPoint_quadratic_nonneg G p g.support g
    apply Complex.nonneg_iff.mp at h
    convert h.1 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

end PositiveConnectionKernel

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable
local instance spectralContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

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


theorem matrixCoeff_invariant_iff (a : V ≃ V) (A : Hilbert V →L[ℂ] Hilbert V) :
    (∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y) ↔
      Commute A (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap := by
  constructor
  · intro h
    change A * (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap =
      (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap * A
    apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
    intro y
    apply ContinuousLinearMap.ext
    intro c
    ext x
    have hs : lp.single (E := fun _ : V => ℂ) 2 y c =
        c • lp.single 2 y (1:ℂ) := by rw [← lp.single_smul]; simp
    have hh := h (a.symm x) y
    simp only [Equiv.apply_symm_apply] at hh
    change A (permuteHilbert a (lp.single 2 y c)) x =
      permuteHilbert a (A (lp.single 2 y c)) x
    rw [hs]
    simp only [map_smul, permuteHilbert_single, lp.coeFn_smul, Pi.smul_apply,
      permuteHilbert_apply]
    change c * matrixCoeff A x (a y) = c * matrixCoeff A (a.symm x) y
    rw [hh]
  · intro h x y
    have hh := congrArg (fun F : Hilbert V →L[ℂ] Hilbert V =>
      F (lp.single 2 y (1:ℂ)) (a x)) h.eq
    simpa only [mul_apply_eq_comp, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, permuteHilbert_single, permuteHilbert_apply,
      Equiv.symm_apply_apply, matrixCoeff] using hh

 attribute [local instance] OAI.Percolation.spectralRealOperatorScalarTower
attribute [local instance] OAI.Percolation.spectralRealOperatorSMulCommClass
attribute [local instance] OAI.Percolation.spectralNonUnitalContinuousFunctionalCalculus
theorem matrixCoeff_sqrt_invariant (a : V ≃ V) (A : Hilbert V →L[ℂ] Hilbert V)
    (h : ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y) :
    ∀ x y, matrixCoeff (CFC.sqrt A) (a x) (a y) = matrixCoeff (CFC.sqrt A) x y := by
  apply (matrixCoeff_invariant_iff a _).mpr
  rw [CFC.sqrt_eq_cfc]
  exact ((matrixCoeff_invariant_iff a A).mp h).cfc_nnreal NNReal.sqrt

 theorem matrixCoeff_mul_invariant (a : V ≃ V) (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y)
    (hB : ∀ x y, matrixCoeff B (a x) (a y) = matrixCoeff B x y) :
    ∀ x y, matrixCoeff (A*B) (a x) (a y) = matrixCoeff (A*B) x y := by
  intro x y
  simp only [matrixCoeff_mul]
  rw [← a.tsum_eq (fun z => matrixCoeff A (a x) z * matrixCoeff B z (a y))]
  simp only [hA,hB]

 theorem matrixCoeff_nonneg (A : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) (x : V) :
    0 ≤ matrixCoeff A x x := by
  rw [matrixCoeff_eq_inner]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hA).inner_nonneg_right _

 theorem matrixCoeff_mono {A B : Hilbert V →L[ℂ] Hilbert V} (h : A ≤ B) (x : V) :
    matrixCoeff A x x ≤ matrixCoeff B x x := by
  have hh := matrixCoeff_nonneg (B-A) (sub_nonneg.mpr h) x
  simpa only [matrixCoeff, sub_apply, lp.coeFn_sub,
    Pi.sub_apply, sub_nonneg] using hh

section RootTrace
variable {ι : Type*} [Fintype ι]
variable (root : ι → V) (weight : ι → ℝ)

theorem rootTrace_nonneg (hw : ∀ i, 0 ≤ weight i)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) : 0 ≤ rootTrace root weight A := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (by simpa using hw i)
    (matrixCoeff_nonneg A hA (root i))

theorem rootTrace_mono (hw : ∀ i, 0 ≤ weight i)
    {A B : Hilbert V →L[ℂ] Hilbert V} (h : A ≤ B) :
    rootTrace root weight A ≤ rootTrace root weight B := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (matrixCoeff_mono h (root i)) (by simpa using hw i)

theorem KernelInvariant.mul {Γ : Set (V ≃ V)}
    {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B) :
    KernelInvariant Γ (A*B) := by
  intro a ha
  exact matrixCoeff_mul_invariant a A B (hA a ha) (hB a ha)

attribute [local instance] OAI.Percolation.spectralRealOperatorScalarTower
attribute [local instance] OAI.Percolation.spectralRealOperatorSMulCommClass
attribute [local instance] OAI.Percolation.spectralNonUnitalContinuousFunctionalCalculus
theorem KernelInvariant.sqrt {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) :
    KernelInvariant Γ (CFC.sqrt A) := by
  intro a ha
  exact matrixCoeff_sqrt_invariant a A (hA a ha)



theorem rootTrace_cyclic {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B) :
    rootTrace root weight (A*B) = rootTrace root weight (B*A) := by
  have ht := htr (fun x y => matrixCoeff A x y * matrixCoeff B y x)
    (by intro a ha x y; rw [hA a ha, hB a ha])
    (fun x => (operator_kernel_hasSum A (B (lp.single 2 x (1:ℂ))) x).summable)
    (fun y => by
      simpa only [matrixCoeff, mul_comm] using
        (operator_kernel_hasSum B (A (lp.single 2 y (1:ℂ))) y).summable)
  simpa only [rootTrace, matrixCoeff_mul, mul_comm] using ht

theorem rootTrace_diag_le {Γ : Set (V ≃ V)}
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (c : ℝ) (hc : 0 ≤ c)
    (hmin : ∀ i, 1 ≤ c * weight i)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : KernelInvariant Γ A)
    (hApos : 0 ≤ A) (x : V) :
    matrixCoeff A x x ≤ (c : ℂ) * rootTrace root weight A := by
  obtain ⟨i,a,ha,hax⟩ := hcov x
  have hi : (weight i : ℂ) * matrixCoeff A (root i) (root i) ≤
      rootTrace root weight A := by
    unfold rootTrace
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j => (weight j : ℂ) * matrixCoeff A (root j) (root j))
      (fun j _ => mul_nonneg (by simpa using hw j) (matrixCoeff_nonneg A hApos _))
      (Finset.mem_univ i)
  calc
    matrixCoeff A x x = matrixCoeff A (root i) (root i) := by
      rw [← hax, hA a ha]
    _ ≤ (c * weight i : ℝ) * matrixCoeff A (root i) (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1:ℂ) ≤ ((c * weight i : ℝ) : ℂ) by exact_mod_cast hmin i)
        (matrixCoeff_nonneg A hApos (root i))
    _ = (c : ℂ) * ((weight i : ℂ) * matrixCoeff A (root i) (root i)) := by
      push_cast; ring
    _ ≤ (c : ℂ) * rootTrace root weight A :=
      mul_le_mul_of_nonneg_left hi (by exact_mod_cast hc)

theorem rootTrace_positive_mul_le {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) (hBsa : IsSelfAdjoint B) :
    rootTrace root weight (B*A) ≤ (‖B‖ : ℂ) * rootTrace root weight A := by
  let S := CFC.sqrt A
  have hS : S*S = A := CFC.sqrt_mul_sqrt_self A hApos
  have hSstar : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hSI : KernelInvariant Γ S := hA.sqrt
  have hbound : S*B*S ≤ ‖B‖ • A := by
    convert (CStarAlgebra.star_left_conjugate_le_norm_smul (a := S) (b := B) hBsa) using 1
    · rw [hSstar]
    · rw [hSstar, hS]
      ext f x
      rfl
  calc
    rootTrace root weight (B*A) = rootTrace root weight (S*(B*S)) := by
      rw [rootTrace_cyclic root weight htr S (B*S) hSI (hB.mul hSI)]
      rw [mul_assoc, hS]
    _ = rootTrace root weight (S*B*S) := by rw [mul_assoc]
    _ ≤ rootTrace root weight (‖B‖ • A) := rootTrace_mono root weight hw hbound
    _ = (‖B‖ : ℂ) * rootTrace root weight A := rootTrace_real_smul root weight _ _

 theorem matrixCoeff_gram (L M : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (L*star M) x y =
      inner ℂ (star L (lp.single 2 x (1:ℂ))) (star M (lp.single 2 y (1:ℂ))) := by
  rw [matrixCoeff_eq_inner]
  change inner ℂ _ (L ((ContinuousLinearMap.adjoint M) _)) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rfl

 theorem matrixCoeff_gram_norm_sq_le
    (L M : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff (L*star M) x y‖ ^ 2 ≤
      (matrixCoeff (L*star L) x x).re * (matrixCoeff (M*star M) y y).re := by
  simp only [matrixCoeff_gram]
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
      (star L (lp.single 2 x (1:ℂ))) (star M (lp.single 2 y (1:ℂ)))
  rw [norm_inner_symm (star M (lp.single 2 y (1:ℂ)))] at h
  simpa only [pow_two, RCLike.re_to_complex] using h

 theorem matrixCoeff_positive_product_norm_sq_le
    (A B : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) (x y : V) :
    ‖matrixCoeff (B*A) x y‖ ^ 2 ≤
      (matrixCoeff (B*A*star B) x x).re * (matrixCoeff A y y).re := by
  let S := CFC.sqrt A
  have hSS : S*S = A := CFC.sqrt_mul_sqrt_self A hA
  have hSstar : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  convert matrixCoeff_gram_norm_sq_le (B*S) S x y using 1 <;>
    simp only [star_mul, hSstar, mul_assoc, ← mul_assoc S S, hSS]



end RootTrace

end InvariantOperatorTrace

section InvariantPercolationOperators
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable


theorem HasKernel.invariant [Countable V] [Countable E] (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A) :
    KernelInvariant (vertexAut G) A := by
  rintro a ⟨b, hab⟩ x y
  change A (lp.single 2 (a y) (1:ℂ)) (a x) = A (lp.single 2 y (1:ℂ)) x
  rw [hA, hA, twoPoint_aut G p hab]

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

theorem clusterWindowProbability_nonneg (G : BondGraph V E) (p : unitInterval)
    (x : V) (lo hi : ℕ) : 0 ≤ clusterWindowProbability G p x lo hi := ENNReal.toReal_nonneg

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
section WalkOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem matrixCoeff_real_symm (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : IsSelfAdjoint A) (x y : V) : (matrixCoeff A x y).re = (matrixCoeff A y x).re := by
  have h := congrArg Complex.re (matrixCoeff_adjoint A x y)
  simpa only [hA.star_eq,Complex.star_def,Complex.conj_re] using h

end WalkOrbitReturn
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
    simp only [show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),not_false_eq_true,if_true]
  have hco : bernoulliPolynomial (Q.erase e) (fun ω => if e ∉ insert e ω then f (insert e ω) else 0) p = 0 := by
    simp only [Finset.mem_insert_self,not_true_eq_false,if_false,bernoulliPolynomial_zero]
  have ho : bernoulliPolynomial (Q.erase e) (fun ω => if e ∈ ω then f (ω.erase e) else 0) p = 0 := by
    calc
      _ = bernoulliPolynomial (Q.erase e) (fun _ => 0) p := by
        apply bernoulliPolynomial_congr
        intro ω hω
        simp only [show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),if_false]
      _ = 0 := bernoulliPolynomial_zero _ _
  have hoo : bernoulliPolynomial (Q.erase e)
      (fun ω => if e ∈ insert e ω then f ((insert e ω).erase e) else 0) p =
      bernoulliPolynomial (Q.erase e) f p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [Finset.mem_insert_self,if_true,Finset.erase_insert
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
      · simp only [hp,hP ω e hp,not_false_eq_true,if_true]
      · simp only [hp,if_false,ite_self]
    have hR : bernoulliPolynomial Q (fun ω => if e ∈ ω then (if P (ω.erase e) e then 1 else 0) else 0) p =
        bernoulliPolynomial Q (fun ω => if e ∈ ω ∧ P (ω.erase e) e then 1 else 0) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      by_cases hm : e ∈ ω <;> simp only [hm,true_and,false_and,if_true,if_false]
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
      · simp only [hc,if_true,mul_one] at *
        exact_mod_cast h
      · simp only [hc,if_false,mul_zero] at *
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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_ExteriorMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
      simp only [diagonalLossTerm,hy,false_and,if_false]
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
  · simp only [diagonalLossTerm,hy,true_and,if_true]
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by dsimp only; split_ifs <;> simp only [mul_zero])
  · simp only [diagonalLossTerm,hy,false_and,if_false,integral_zero]

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
      · simp only [hωA,if_true,f,true_and]
        exact cluster_size_eq_tsum_real G ω y hω
      · simp only [hωA,if_false,f,false_and,tsum_zero]
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
  · simp only [inducedSusceptibility,Set.mem_compl_iff,hy,not_false_eq_true,if_true]
    calc
      _ = ∫ ω, (if cluster G ω x = (W:Set V) then ((cluster G ω y).ncard:ℝ) else 0) ∂law p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          by_cases hc : cluster G ω x = (W:Set V)
          · have hnc : ¬Conn G ω x y := by intro h; exact hy (hc ▸ h)
            simp [hc,hnc]
          · simp only [hc,false_and,if_false])
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
      · simp only [F,hW,if_true,le_refl]
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
      · simp only [hc,if_true,freshExteriorMoment,Set.ncard_coe_finset,mul_one]
      · simp only [hc,if_false,mul_zero])
  have hr : (∫ ω, (if cluster G ω x = (W:Set V) then
      (if ¬Conn G ω x y then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) else 0) ∂law p) =
      (W.card:ℝ)*((law p).real {ω | cluster G ω x = (W:Set V)} * inducedSusceptibility G (W:Set V)ᶜ p y) := by
    rw [←cluster_cell_exterior_susceptibility G hloc hqt p hp W x y,←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only
      by_cases hc : cluster G ω x = (W:Set V)
      · simp only [hc,true_and,if_true,Set.ncard_coe_finset]
        split_ifs <;> simp only [mul_zero]
      · simp only [hc,false_and,if_false,mul_zero])
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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_DistinctMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,if_true,Complex.one_re,one_mul]

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
  simp only [distinctClusterMoment,hs,not_true_eq_false,if_false,integral_zero]

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
    · simp only [h,not_true_eq_false,if_false,if_true,zero_add,cluster_eq_of_conn G ω h,pow_two]
    · simp only [h,not_false_eq_true,if_true,if_false,add_zero])

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

theorem log_geometricScale_le (q : EndpointProfile G hloc p₀ o s) (hp₀ : 0 < (p₀:ℝ))
    (hM : 1 ≤ q.cap) :
    Real.log q.geometricScale ≤ q.U+q.m+Real.log (2*(1+1/(p₀:ℝ))) := by
  have hM' : (1:ℝ) ≤ q.cap := by exact_mod_cast hM
  have hMp : (0:ℝ) < q.cap := zero_lt_one.trans_le hM'
  have hb : 1+(1-(p₀:ℝ))/p₀*q.cap ≤ (1+1/(p₀:ℝ))*q.cap := by
    apply (mul_le_mul_iff_of_pos_right hp₀).mp
    field_simp
    nlinarith
  have Hz : q.geometricScale ≤ (1/q.rule.successProbability p₀ o)*(q.cap:ℝ)*(2*(1+1/(p₀:ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (inv_nonneg.mpr q.success_pos.le))
    simpa only [geometricScale,potentialScale,one_div,mul_assoc,mul_comm,mul_left_comm] using h
  have hc : 0 < 2*(1+1/(p₀:ℝ)) := by positivity
  have h := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (q.geometricScale_two_le hp₀)) Hz
  rw [Real.log_mul (mul_ne_zero (one_div_ne_zero q.success_pos.ne') hMp.ne') hc.ne',
    Real.log_mul (one_div_ne_zero q.success_pos.ne') hMp.ne'] at h
  exact h

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

 

theorem eventually_neighborMoment_lower [Countable V] [Countable E] [Nonempty V]
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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EfficientProfileMomentConsequence
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem neighborMoment_growth_of_divergent_moment
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (p₀ : unitInterval) (hp₀ : 0 < (p₀:ℝ)) (hp₁ : (p₀:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law p₀, (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p₀)) :
    ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∀ᶠ p in nhds p₀, p < pc G →
      b*(rootSusceptibility G root weight p)^(2-γ) ≤ rootNeighborMoment G hloc root weight p := by
  obtain ⟨i,heff⟩ := efficient_endpoint_profiles_of_divergent_moment_bs G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 p₀ hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hw i)).le)
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  intro γ hγ
  let C := Real.log (2*(1+1/(p₀:ℝ)))
  have hC : 0 ≤ C := Real.log_nonneg (by
    have hinv : 0 ≤ 1/(p₀:ℝ) := (one_div_pos.mpr hp₀).le
    nlinarith)
  obtain ⟨q,hM,hH,hR,hcost⟩ := heff (γ/4) (by linarith) (2+4*C/γ)
  have hH2 : 2 < q.H := by
    have hn : 0 ≤ 4*C/γ := div_nonneg (mul_nonneg (by norm_num) hC) hγ.le
    linarith
  have hCsmall : C < γ*q.H/4 := by
    have hx : 4*C < (q.H-2)*γ := (div_lt_iff₀ hγ).mp (by linarith : 4*C/γ < q.H-2)
    nlinarith
  have hexp : Real.log q.geometricScale/(q.H-1) ≤ γ := by
    apply (div_le_iff₀ (by linarith : 0 < q.H-1)).mpr
    have hz := q.log_geometricScale_le hp₀ (by omega)
    have hm : γ*q.H/2 ≤ γ*(q.H-1) := by nlinarith
    dsimp [C] at hCsmall
    nlinarith only [hz,hcost,hCsmall,hm]
  obtain ⟨b,hb,hnear⟩ := q.eventually_neighborMoment_lower hconn hqt root weight Γ htr
    (fun a ha => hΓ ha) (fun i => (hw i).le) hw1 i (hw i) hcover c hc hmin hp₀ hH
  refine ⟨b,hb,?_⟩
  filter_upwards [hnear] with p hp
  intro hpc
  have hχ : 1 ≤ rootSusceptibility G root weight p := by
    calc
      1 = ∑ i, weight i*1 := by simp only [mul_one,hw1]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (susceptibility_one_le G hloc hqt p hpc (root i)) (hw i).le)
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hχ (by linarith :
    2-γ ≤ 2-Real.log q.geometricScale/(q.H-1))) hb.le).trans (hp hpc)

end EfficientProfileMomentConsequence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory Function
section PivotalSprinklingGain
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_set_union_pair : Measurable (fun f : Set E × Set E => f.1 ∪ f.2) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  apply measurableSet_setOfPred.mp
  change MeasurableSet ({f : Set E × Set E | e ∈ f.1} ∪ {f | e ∈ f.2})
  apply MeasurableSet.union <;> apply measurableSet_setOfPred.mpr
  · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_fst
  · exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).comp measurable_snd

theorem measurable_set_insert (e : E) : Measurable (fun ω : Set E => insert e ω) := by
  have h : Measurable (fun ω : Set E => ({e}:Set E) ∪ ω) :=
    measurable_set_union_pair.comp (measurable_const.prodMk measurable_id)
  simpa only [Set.singleton_union] using (h : Measurable (fun ω : Set E => {e} ∪ ω))

theorem measurableSet_closedPivotal (A : Set (Set E)) (hA : MeasurableSet A) (e : E) :
    MeasurableSet (closedPivotal A e) := by
  exact (measurableSet_mem e).compl.inter (hA.compl.inter (hA.preimage (measurable_set_insert e)))

theorem measurableSet_singleSprinkle (Q : Finset E) (e : (Q : Set E)) :
    MeasurableSet (singleSprinkle Q e) :=
  (measurableSet_singleton _).preimage (measurable_set_restrict (Q:Set E))

theorem singleSprinkle_disjoint (Q : Finset E) :
    Pairwise (Disjoint on singleSprinkle Q) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro η ha hb
  apply hab
  have h : ({a} : Set (Q:Set E)) = {b} := ha.symm.trans hb
  simpa only [Set.singleton_eq_singleton_iff] using h

theorem singleSprinkle_mem (Q : Finset E) (e : (Q:Set E)) {η : Set E}
    (hη : η ∈ singleSprinkle Q e) : e.val ∈ η := by
  have h : e ∈ Subtype.val ⁻¹' η := by rw [hη]; exact Set.mem_singleton e
  exact h

theorem singleSprinkle_probability (Q : Finset E) (e : (Q:Set E)) (a : unitInterval) :
    (law a).real (singleSprinkle Q e) = (a:ℝ)*(1-(a:ℝ))^(Q.card-1) := by
  have h := congrArg (fun μ : Measure (Set (Q:Set E)) => μ.real {({e}:Set (Q:Set E))})
    (law_map_restrict a (Q:Set E))
  rw [Measure.real,Measure.map_apply (measurable_set_restrict _) (measurableSet_singleton _)] at h
  change (law a).real (singleSprinkle Q e) = _ at h
  rw [h,law,setBernoulli_real_singleton a (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ,Set.ncard_singleton]
  simp only [Set.ncard_univ,Nat.card_eq_fintype_card,pow_one]
  rw [show Fintype.card (Q:Set E) = Q.card from Fintype.card_coe Q]

 

theorem event_sprinkling_gain (p a : unitInterval) (Q : Finset E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hup : IsUpperSet A) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) * (∑ e ∈ Q, (law p).real (closedPivotal A e)) ≤
      (law (sprinkleParameter p a)).real A - (law p).real A := by
  let μ : Measure (Set E × Set E) := (law p).prod (law a)
  let B : Set (Set E × Set E) := {f | f.1 ∉ A ∧ f.1 ∪ f.2 ∈ A}
  let C (e : (Q:Set E)) := (closedPivotal A e.val) ×ˢ singleSprinkle Q e
  have hB : MeasurableSet B := (hA.compl.preimage measurable_fst).inter (hA.preimage measurable_set_union_pair)
  have hC (e : (Q:Set E)) : MeasurableSet (C e) :=
    (measurableSet_closedPivotal A hA e.val).prod (measurableSet_singleSprinkle Q e)
  have hd : Pairwise (Disjoint on C) := by
    intro e f hef
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact Set.disjoint_left.mp (singleSprinkle_disjoint Q hef) hz.2 hz'.2
  have hsub : (⋃ e, C e) ⊆ B := by
    intro z hz
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp hz
    refine ⟨he.1.2.1,?_⟩
    apply hup _ he.1.2.2
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact Or.inr (singleSprinkle_mem Q e he.2)
    · exact Or.inl hf
  have hgain : μ.real B = (law (sprinkleParameter p a)).real A - (law p).real A := by
    have he : (fun f : Set E × Set E => f.1 ∪ f.2) ⁻¹' A = (A ×ˢ Set.univ) ∪ B := by
      ext f
      simp only [Set.mem_preimage,Set.mem_union,Set.mem_prod,Set.mem_univ,and_true,B,Set.mem_ofPred_eq]
      exact ⟨fun h => by by_cases ha : f.1 ∈ A; exact Or.inl ha; exact Or.inr ⟨ha,h⟩,
        fun h => h.elim (fun ha => hup Set.subset_union_left ha) And.right⟩
    have hd : Disjoint (A ×ˢ (Set.univ : Set (Set E))) B := by
      apply Set.disjoint_left.mpr
      intro f hf hf'
      exact hf'.1 hf.1
    have hm := congrArg (fun ν : Measure (Set E) => ν.real A) (law_map_union p a)
    rw [Measure.real,Measure.map_apply measurable_set_union_pair hA] at hm
    change μ.real ((fun f : Set E × Set E => f.1 ∪ f.2) ⁻¹' A) = _ at hm
    rw [he,measureReal_union hd hB] at hm
    have hp : μ.real (A ×ˢ Set.univ) = (law p).real A := by
      rw [measureReal_prod_prod,probReal_univ,mul_one]
    rw [hp] at hm
    linarith
  have hs : μ.real (⋃ e, C e) =
      (a:ℝ)*(1-(a:ℝ))^(Q.card-1) * (∑ e ∈ Q, (law p).real (closedPivotal A e)) := by
    rw [measureReal_iUnion_fintype hd hC]
    simp only [C,μ,measureReal_prod_prod,singleSprinkle_probability]
    rw [←Finset.sum_mul,mul_comm]
    congr 1
    apply Finset.sum_bij (fun e _ => e.val)
    · intro e _; exact e.property
    · intro e _ f _ h; exact Subtype.ext h
    · intro e he; exact ⟨⟨e,he⟩,Finset.mem_univ _,rfl⟩
    · intro _ _; rfl
  rw [←hs,←hgain]
  exact measureReal_mono hsub

end PivotalSprinklingGain
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Susceptibility
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SusceptibilityPivotalGain
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sprinkleParameter_ge_left (p a : unitInterval) : p ≤ sprinkleParameter p a := by
  change (p:ℝ) ≤ (p:ℝ)+(1-(p:ℝ))*(a:ℝ)
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr p.2.2) a.2.1)

 

theorem susceptibility_sprinkling_gain [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p a : unitInterval) (hq : sprinkleParameter p a < pc G) (x : V)
    (Q : Finset E) (F : Finset V) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) *
      (∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω x y} e)) ≤
      susceptibility G (sprinkleParameter p a) x - susceptibility G p x := by
  have hpa := sprinkleParameter_ge_left p a
  have hp : p < pc G := lt_of_le_of_lt hpa hq
  have hsum := (summable_twoPoint_subcritical G hloc hqt (sprinkleParameter p a) hq x).sub
    (summable_twoPoint_subcritical G hloc hqt p hp x)
  calc
    _ = ∑ y ∈ F, (a:ℝ)*(1-(a:ℝ))^(Q.card-1)*
      (∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω x y} e)) := Finset.mul_sum _ _ _
    _ ≤ ∑ y ∈ F, (twoPoint G (sprinkleParameter p a) x y - twoPoint G p x y) := by
      apply Finset.sum_le_sum
      intro y _
      exact event_sprinkling_gain p a Q {ω | Conn G ω x y} (measurableSet_conn G x y)
        (fun _ _ h hc => conn_mono G h hc)
    _ ≤ ∑' y, (twoPoint G (sprinkleParameter p a) x y - twoPoint G p x y) :=
      hsum.sum_le_tsum F (fun y _ => sub_nonneg.mpr (twoPoint_mono G x y hpa))
    _ = _ := (summable_twoPoint_subcritical G hloc hqt (sprinkleParameter p a) hq x).tsum_sub
      (summable_twoPoint_subcritical G hloc hqt p hp x)

 
theorem rootSusceptibility_sprinkling_gain [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p a : unitInterval) (hq : sprinkleParameter p a < pc G)
    (Q : Finset E) (F : Finset V) :
    (a:ℝ)*(1-(a:ℝ))^(Q.card-1) *
      (∑ i, weight i*(∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω (root i) y} e))) ≤
      rootSusceptibility G root weight (sprinkleParameter p a) - rootSusceptibility G root weight p := by
  rw [rootSusceptibility,rootSusceptibility,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (susceptibility_sprinkling_gain G hloc hqt p a hq (root i) Q F) (hw i)
  convert h using 1 <;> ring

end SusceptibilityPivotalGain
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrientedPivotalConnections
attribute [local instance] Classical.propDecidable Classical.decEq



theorem measurableSet_orientedPivotalEvent [Countable V] [Countable E]
    (G : BondGraph V E) (x y a b : V) : MeasurableSet (orientedPivotalEvent G x y a b) :=
  (measurableSet_conn G x a).inter ((measurableSet_conn G b y).inter (measurableSet_conn G a b).compl)

theorem orientedPivotalEvent_disjoint (G : BondGraph V E) (x y a b : V) :
    Disjoint (orientedPivotalEvent G x y a b) (orientedPivotalEvent G x y b a) := by
  apply Set.disjoint_left.mpr
  intro ω h h'
  exact h.2.2 ((conn_symm G ω h.1).trans h'.1)

theorem closedPivotal_conn (G : BondGraph V E) (e : E) (a b x y : V)
    (he : G e = s(a,b)) :
    closedPivotal {ω | Conn G ω x y} e =
      orientedPivotalEvent G x y a b ∪ orientedPivotalEvent G x y b a := by
  ext ω
  constructor
  · rintro ⟨_,hn,hc⟩
    rcases (conn_insert_iff G ω e a b x y he).mp hc with h | h | h
    · exact (hn h).elim
    · exact Or.inl ⟨h.1,h.2,fun hab => hn (h.1.trans (hab.trans h.2))⟩
    · exact Or.inr ⟨h.1,h.2,fun hba => hn (h.1.trans (hba.trans h.2))⟩
  · intro h
    have hi : ∀ a b : V, G e = s(a,b) → ω ∈ orientedPivotalEvent G x y a b →
        ω ∈ closedPivotal {ω | Conn G ω x y} e := by
      intro a b he h
      refine ⟨?_,?_,?_⟩
      · intro heω
        exact h.2.2 (.single ⟨e,heω,he⟩)
      · intro hxy
        exact h.2.2 ((conn_symm G ω h.1).trans (hxy.trans (conn_symm G ω h.2.1)))
      · exact (conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨h.1,h.2.1⟩))
    exact h.elim (hi a b he) (hi b a (he.trans (Sym2.eq_swap ..)))

theorem closedPivotal_conn_probability [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (e : E) (a b x y : V) (he : G e = s(a,b)) :
    (law p).real (closedPivotal {ω | Conn G ω x y} e) =
      (law p).real (orientedPivotalEvent G x y a b) +
      (law p).real (orientedPivotalEvent G x y b a) := by
  rw [closedPivotal_conn G e a b x y he]
  exact measureReal_union (orientedPivotalEvent_disjoint G x y a b)
    (measurableSet_orientedPivotalEvent G x y b a)


end OrientedPivotalConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PivotalMomentIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem distinctClusterMass_eq_pivotal (G : BondGraph V E) (ω : Set E) (a b : V) :
    (if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) =
      ∑' x, ∑' y, if ω ∈ orientedPivotalEvent G x y a b then (1:ℝ≥0∞) else 0 := by
  by_cases hab : Conn G ω a b
  · simp only [hab,not_true_eq_false,if_false,orientedPivotalEvent,Set.mem_ofPred_eq,
       and_false,if_false,tsum_zero]
  · rw [ite_eq_left hab,clusterMass_mul]
    apply tsum_congr
    intro x
    apply tsum_congr
    intro y
    apply if_congr _ rfl rfl
    simp only [orientedPivotalEvent,Set.mem_ofPred_eq,hab,not_false_eq_true,and_true]
    exact and_congr (show Conn G ω a x ↔ Conn G ω x a from ⟨conn_symm G ω,conn_symm G ω⟩) Iff.rfl

theorem lintegral_distinctClusterMass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (a b : V) :
    (∫⁻ ω, (if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) ∂law p) =
      ∑' x, ∑' y, law p (orientedPivotalEvent G x y a b) := by
  have hm (x y : V) : Measurable (fun ω : Set E =>
      if ω ∈ orientedPivotalEvent G x y a b then (1:ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_orientedPivotalEvent G x y a b) measurable_const measurable_const
  simp_rw [distinctClusterMass_eq_pivotal]
  rw [lintegral_tsum (fun x => (Measurable.tsum (fun y => hm x y)).aemeasurable)]
  apply tsum_congr
  intro x
  rw [lintegral_tsum (fun y => (hm x y).aemeasurable)]
  apply tsum_congr
  intro y
  simpa only [Set.indicator,Pi.one_apply] using
    (lintegral_indicator_one (μ := law p) (measurableSet_orientedPivotalEvent G x y a b))

theorem ennreal_distinctClusterMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    ENNReal.ofReal (distinctClusterMoment G p a b) =
      ∑' x, ∑' y, law p (orientedPivotalEvent G x y a b) := by
  have hi := integrable_distinct_cluster_product G hloc hqt p hp a b
  have hn : 0 ≤ᵐ[law p] (fun ω => if ¬Conn G ω a b
      then ((cluster G ω a).ncard:ℝ)*((cluster G ω b).ncard:ℝ) else 0) := by
    exact Filter.Eventually.of_forall (fun ω => by dsimp only; split_ifs <;> positivity)
  have he : (fun ω => ENNReal.ofReal (if ¬Conn G ω a b
      then ((cluster G ω a).ncard:ℝ)*((cluster G ω b).ncard:ℝ) else 0)) =ᵐ[law p]
      (fun ω => if ¬Conn G ω a b then clusterMass G ω a * clusterMass G ω b else 0) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp a,
      subcritical_cluster_finite_ae G p hp b] with ω ha hb
    by_cases hab : Conn G ω a b
    · simp only [hab,not_true_eq_false,if_false,ENNReal.ofReal_zero]
    · simp only [hab,not_false_eq_true,if_true]
      rw [clusterMass_eq_ncard G ω a ha,clusterMass_eq_ncard G ω b hb,
        ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp only [ENNReal.ofReal_natCast]
  rw [←lintegral_distinctClusterMass,←lintegral_congr_ae he]
  exact ofReal_integral_eq_lintegral_ofReal hi hn

theorem summable_orientedPivotal_pairs [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    Summable (fun xy : V × V => (law p).real (orientedPivotalEvent G xy.1 xy.2 a b)) := by
  apply ENNReal.summable_toReal
  rw [ENNReal.tsum_prod',←ennreal_distinctClusterMoment G hloc hqt p hp a b]
  exact ENNReal.ofReal_ne_top

theorem distinctClusterMoment_eq_pivotal [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a b : V) :
    distinctClusterMoment G p a b =
      ∑' x, ∑' y, (law p).real (orientedPivotalEvent G x y a b) := by
  rw [←(summable_orientedPivotal_pairs G hloc hqt p hp a b).tsum_prod]
  change distinctClusterMoment G p a b =
    ∑' xy : V × V, (law p (orientedPivotalEvent G xy.1 xy.2 a b)).toReal
  rw [←ENNReal.tsum_toReal_eq (f := fun xy : V × V => law p (orientedPivotalEvent G xy.1 xy.2 a b))
    (fun _ => measure_ne_top _ _), ENNReal.tsum_prod',
    ←ennreal_distinctClusterMoment G hloc hqt p hp a b,
    ENNReal.toReal_ofReal (distinctClusterMoment_nonneg G p a b)]

end PivotalMomentIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PivotalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem orientedPivotal_probability_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x y z w : V) :
    (law p).real (orientedPivotalEvent G (a x) (a y) (a z) (a w)) =
      (law p).real (orientedPivotalEvent G x y z w) := by
  have he : orientedPivotalEvent G (a x) (a y) (a z) (a w) =
      (fun ω => b ⁻¹' ω) ⁻¹' orientedPivotalEvent G x y z w := by
    ext ω
    simp only [orientedPivotalEvent,Set.mem_ofPred_eq,Set.mem_preimage,conn_aut_iff G hab]
  unfold Measure.real
  rw [he,←Measure.map_apply (measurable_set_preimage b)
    (measurableSet_orientedPivotalEvent G x y z w),law_map_preimage_equiv]

theorem pivotalTransportMass_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x a : V) : 0 ≤ pivotalTransportMass G hloc p x a :=
  Finset.sum_nonneg (fun _ _ => tsum_nonneg (fun _ => measureReal_nonneg))

theorem pivotalTransportMass_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x z : V) :
    pivotalTransportMass G hloc p (a x) (a z) = pivotalTransportMass G hloc p x z := by
  simp only [pivotalTransportMass,neighbors_covariant G hloc hab,Finset.sum_map,Equiv.coe_toEmbedding]
  apply Finset.sum_congr rfl
  intro w _
  rw [←a.tsum_eq (fun y => (law p).real (orientedPivotalEvent G (a x) y (a z) (a w)))]
  exact tsum_congr (fun y => orientedPivotal_probability_covariant G p hab x y z w)

theorem pivotalTransportMass_incoming_summable [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a : V) :
    Summable (fun x => pivotalTransportMass G hloc p x a) := by
  apply summable_sum
  intro b _
  exact (summable_orientedPivotal_pairs G hloc hqt p hp a b).prod

theorem pivotalTransportMass_incoming [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (a : V) :
    (∑' x, pivotalTransportMass G hloc p x a) = neighborClusterMoment G hloc p a := by
  unfold pivotalTransportMass neighborClusterMoment
  rw [Summable.tsum_finsetSum (fun b _ =>
    (summable_orientedPivotal_pairs G hloc hqt p hp a b).prod)]
  exact Finset.sum_congr rfl (fun b _ => (distinctClusterMoment_eq_pivotal G hloc hqt p hp a b).symm)

end PivotalTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PivotalTransportTotal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pivotalTransportMass_outgoing_summable
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (pivotalTransportMass G hloc p x) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  exact (transported_column_of_row_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (fun a x => pivotalTransportMass G hloc p x a)
    (fun a x => pivotalTransportMass_nonneg G hloc p x a)
    (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; exact pivotalTransportMass_covariant G hloc p hab y x)
    (pivotalTransportMass_incoming_summable G hloc hqt p hp)
    (c*rootNeighborMoment G hloc root weight p)
    (fun a => by
      rw [pivotalTransportMass_incoming G hloc hqt p hp]
      exact neighborMoment_le_rootMoment G hloc root weight hw hcover c hc hmin p a) x).1

 

theorem rootPivotalMass_eq_neighborMoment
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) :
    (∑ i, weight i * ∑' a, pivotalTransportMass G hloc p (root i) a) =
      rootNeighborMoment G hloc root weight p := by
  rw [htr.real root weight Γ (pivotalTransportMass G hloc p)
    (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; exact pivotalTransportMass_covariant G hloc p hab x y)
    (pivotalTransportMass_outgoing_summable G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp)
    (pivotalTransportMass_incoming_summable G hloc hqt p hp)]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun t => weight i*t)
    (pivotalTransportMass_incoming G hloc hqt p hp (root i)))

end PivotalTransportTotal
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FinitePivotalComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem orientedPivotal_probability_le_closed [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (e : E) (x y a b : V) (he : G e = s(a,b)) :
    (law p).real (orientedPivotalEvent G x y a b) ≤
      (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  rw [closedPivotal_conn_probability G p e a b x y he]
  exact le_add_of_nonneg_right measureReal_nonneg

 

theorem finite_neighbor_pivotal_le_incident [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y a : V) :
    (∑ b ∈ neighbors G hloc a, (law p).real (orientedPivotalEvent G x y a b)) ≤
      ∑ e ∈ (hloc a).toFinset, (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  let B := neighbors G hloc a
  have he (b : B) : ∃ e, G e = s(a,(b:V)) := (mem_neighbors G hloc a b).mp b.property
  choose edge hedge using he
  have hinj : Function.Injective edge := by
    intro b c h
    apply Subtype.ext
    have hh := (hedge b).symm.trans ((congrArg G h).trans (hedge c))
    rcases Sym2.eq_iff.mp hh with h | h
    · exact h.2
    · exact h.2.trans h.1
  calc
    _ = ∑ b : B, (law p).real (orientedPivotalEvent G x y a b) := (Finset.sum_coe_sort B _).symm
    _ ≤ ∑ b : B, (law p).real (closedPivotal {ω | Conn G ω x y} (edge b)) :=
      Finset.sum_le_sum (fun b _ => orientedPivotal_probability_le_closed G p (edge b) x y a b (hedge b))
    _ = ∑ e ∈ Finset.univ.image edge, (law p).real (closedPivotal {ω | Conn G ω x y} e) :=
      (Finset.sum_image (f := fun e => (law p).real (closedPivotal {ω | Conn G ω x y} e))
        (s := Finset.univ) (fun _ _ _ _ h => hinj h)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp he
        rw [Set.Finite.mem_toFinset]
        change a ∈ G (edge b)
        rw [hedge b]
        exact Sym2.mem_mk_left _ _
      · intro _ _ _
        exact measureReal_nonneg

theorem finite_incident_sum_le_twice (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (f : E → ℝ) (hf : ∀ e, 0 ≤ f e) :
    (∑ a ∈ A, ∑ e ∈ (hloc a).toFinset, f e) ≤ 2*∑ e ∈ incidentSupport G hloc A, f e := by
  let Q := incidentSupport G hloc A
  have heq (a : V) (ha : a ∈ A) :
      (∑ e ∈ (hloc a).toFinset, f e) = ∑ e ∈ Q, if a ∈ G e then f e else 0 := by
    rw [←Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext e
    simp only [Set.Finite.mem_toFinset,Finset.mem_filter]
    exact ⟨fun he => ⟨(mem_incidentSupport G hloc A e).mpr ⟨a,ha,he⟩,he⟩,fun h => h.2⟩
  calc
    _ = ∑ a ∈ A, ∑ e ∈ Q, if a ∈ G e then f e else 0 := Finset.sum_congr rfl heq
    _ = ∑ e ∈ Q, ∑ a ∈ A, if a ∈ G e then f e else 0 := Finset.sum_comm
    _ ≤ ∑ e ∈ Q, 2*f e := by
      apply Finset.sum_le_sum
      intro e _
      have hsub : A.filter (fun a => a ∈ G e) ⊆ (G e).toFinset := by
        intro a ha
        exact Sym2.mem_toFinset.mpr (Finset.mem_filter.mp ha).2
      rw [←Finset.sum_filter,Finset.sum_const, nsmul_eq_mul]
      have hc : (A.filter (fun a => a ∈ G e)).card ≤ 2 := (Finset.card_le_card hsub).trans (by
        rw [Sym2.card_toFinset]; split_ifs <;> omega)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf e)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_oriented_pivotal_sum_le [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) (A : Finset V) :
    (∑ a ∈ A, ∑ b ∈ neighbors G hloc a, (law p).real (orientedPivotalEvent G x y a b)) ≤
      2*∑ e ∈ incidentSupport G hloc A, (law p).real (closedPivotal {ω | Conn G ω x y} e) := by
  exact (Finset.sum_le_sum (fun a _ => finite_neighbor_pivotal_le_incident G hloc p x y a)).trans
    (finite_incident_sum_le_twice G hloc A _ (fun _ => measureReal_nonneg))

end FinitePivotalComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SubcriticalSusceptibilityContinuity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem eventually_cluster_eq_at_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (labels : E → unitInterval) (p : unitInterval) (x : V)
    (hneq : ∀ e, labels e ≠ p) (hfin : (cluster G (openEdges labels p) x).Finite) :
    ∀ᶠ q in nhds p, cluster G (openEdges labels q) x = cluster G (openEdges labels p) x := by
  let Q := incidentSupport G hloc hfin.toFinset
  have he (e : E) : ∀ᶠ q in nhds p, (e ∈ openEdges labels q ↔ e ∈ openEdges labels p) := by
    change ∀ᶠ q in nhds p, (labels e ≤ q ↔ labels e ≤ p)
    by_cases hp : labels e ≤ p
    · have hlt : labels e < p := lt_of_le_of_ne hp (hneq e)
      filter_upwards [eventually_gt_nhds hlt] with q hq
      exact iff_of_true hq.le hp
    · have hlt : p < labels e := lt_of_not_ge hp
      filter_upwards [eventually_lt_nhds hlt] with q hq
      exact iff_of_false (not_le.mpr hq) hp
  filter_upwards [(eventually_all_finset Q).mpr (fun e _ => he e)] with q hq
  apply cluster_eq_of_incident_agreement G
  intro e he
  apply (hq e _).symm
  obtain ⟨v,hv,hve⟩ := he
  exact (mem_incidentSupport G hloc hfin.toFinset e).mpr ⟨v,hfin.mem_toFinset.mpr hv,hve⟩

theorem label_cluster_finite_ae_subcritical [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), (cluster G (openEdges labels p) x).Finite := by
  apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
    (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges p).aemeasurable
  rw [map_openEdges]
  exact subcritical_cluster_finite_ae G p hp x

theorem susceptibility_eq_label_integral [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Integrable (fun labels : E → unitInterval => ((cluster G (openEdges labels p) x).ncard:ℝ)) labelLaw ∧
    susceptibility G p x = ∫ labels : E → unitInterval, ((cluster G (openEdges labels p) x).ncard:ℝ) ∂labelLaw := by
  obtain ⟨hi,he⟩ := susceptibility_eq_integral G hloc hqt p hp x
  have hi' : Integrable (fun ω : Set E => ((cluster G ω x).ncard:ℝ))
      ((labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p)) := by
    rwa [map_openEdges]
  refine ⟨hi'.comp_measurable (measurable_openEdges p),?_⟩
  rw [he,←integral_map (measurable_openEdges p).aemeasurable hi'.aestronglyMeasurable,map_openEdges]

 

theorem continuousAt_susceptibility_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : ContinuousAt (fun q => susceptibility G q x) p := by
  obtain ⟨r,hpr,hr⟩ := exists_between hp
  let F (q : unitInterval) (labels : E → unitInterval) : ℝ := ((cluster G (openEdges labels q) x).ncard:ℝ)
  have hm (q : unitInterval) : Measurable (F q) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      ((measurable_cluster_ncard G hloc x).comp (measurable_openEdges q))
  have hcont : ContinuousAt (fun q => ∫ labels, F q labels ∂labelLaw) p := by
    apply continuousAt_of_dominated
      (bound := F r) (Filter.Eventually.of_forall (fun q => (hm q).aestronglyMeasurable))
    · filter_upwards [eventually_lt_nhds hpr] with q hqr
      filter_upwards [label_cluster_finite_ae_subcritical G r hr x] with labels hfin
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      dsimp only [F]
      exact_mod_cast Set.ncard_le_ncard (show cluster G (openEdges labels q) x ⊆ cluster G (openEdges labels r) x from
        fun y hy => conn_mono G (openEdges_mono labels hqr.le) hy) hfin
    · exact (susceptibility_eq_label_integral G hloc hqt r hr x).1
    · filter_upwards [ae_labels_ne (E := E) p,label_cluster_finite_ae_subcritical G p hp x] with labels hneq hfin
      apply Filter.EventuallyEq.continuousAt
      filter_upwards [eventually_cluster_eq_at_finite G hloc labels p x hneq hfin] with q hq
      exact congrArg (fun S : Set V => (S.ncard:ℝ)) hq
  apply (continuousAt_congr _).mpr hcont
  filter_upwards [eventually_lt_nhds hp] with q hq
  exact (susceptibility_eq_label_integral G hloc hqt q hq x).2

theorem continuousAt_rootSusceptibility_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp : p < pc G) :
    ContinuousAt (rootSusceptibility G root weight) p := by
  exact tendsto_finsetSum Finset.univ (fun i _ => continuousAt_const.mul
    (continuousAt_susceptibility_subcritical G hloc hqt p hp (root i)))

end SubcriticalSusceptibilityContinuity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section FiniteRootPivotalApproximation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_orientedPivotal_targets [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    Summable (fun y => (law p).real (orientedPivotalEvent G x y a b)) := by
  apply (summable_twoPoint_subcritical G hloc hqt p hp b).of_nonneg_of_le
  · exact fun _ => measureReal_nonneg
  · intro y
    exact measureReal_mono (fun _ h => h.2.1)

theorem finiteRootPivotalMass_nonneg (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) (Q : Finset E) (F : Finset V) :
    0 ≤ finiteRootPivotalMass G root weight p Q F :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i)
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => measureReal_nonneg))))

 

theorem exists_finiteRootPivotalMass_gt
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (B : ℝ)
    (hB : B < rootNeighborMoment G hloc root weight p / 2) :
    ∃ Q : Finset E, ∃ F : Finset V, B < finiteRootPivotalMass G root weight p Q F := by
  have hs (x : V) := pivotalTransportMass_outgoing_summable G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp x
  let f (a : V) := ∑ i, weight i*pivotalTransportMass G hloc p (root i) a
  have hsf : Summable f := summable_sum (fun i _ => (hs (root i)).mul_left (weight i))
  have htf : (∑' a, f a) = rootNeighborMoment G hloc root weight p := by
    rw [Summable.tsum_finsetSum (fun i _ => (hs (root i)).mul_left (weight i))]
    simp_rw [tsum_mul_left]
    exact rootPivotalMass_eq_neighborMoment G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp
  have hB' : 2*B < ∑' a, f a := by rw [htf]; linarith
  obtain ⟨A,hA⟩ := ((tendsto_order.mp hsf.hasSum).1 (2*B) hB').exists
  let g (y : V) := ∑ i, weight i*(∑ a ∈ A, ∑ b ∈ neighbors G hloc a,
    (law p).real (orientedPivotalEvent G (root i) y a b))
  have hst (i : ι) (a b : V) := summable_orientedPivotal_targets G hloc hqt p hp (root i) a b
  have hsg : Summable g := summable_sum (fun i _ =>
    (summable_sum (fun a _ => summable_sum (fun b _ => hst i a b))).mul_left (weight i))
  have htg : (∑' y, g y) = ∑ a ∈ A, f a := by
    rw [Summable.tsum_finsetSum (fun i _ =>
      (summable_sum (fun a _ => summable_sum (fun b _ => hst i a b))).mul_left (weight i))]
    simp_rw [tsum_mul_left]
    simp_rw [Summable.tsum_finsetSum (fun a _ => summable_sum (fun b _ => hst _ a b))]
    simp_rw [Summable.tsum_finsetSum (fun b _ => hst _ _ b)]
    simp only [f,Finset.mul_sum,pivotalTransportMass]
    rw [Finset.sum_comm]
  obtain ⟨F,hF⟩ := ((tendsto_order.mp hsg.hasSum).1 (2*B) (by rwa [htg])).exists
  refine ⟨incidentSupport G hloc A,F,?_⟩
  have hb : (∑ y ∈ F, g y) ≤ 2*finiteRootPivotalMass G root weight p (incidentSupport G hloc A) F := by
    unfold g finiteRootPivotalMass
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.mul_sum, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (hw i)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun y _ => finite_oriented_pivotal_sum_le G hloc p (root i) y A)
  linarith

end FiniteRootPivotalApproximation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section VanishingSprinkles
attribute [local instance] Classical.propDecidable Classical.decEq

theorem vanishingSprinkle_pos (n : ℕ) : 0 < (vanishingSprinkle n : ℝ) := by
  dsimp [vanishingSprinkle]
  positivity

theorem tendsto_vanishingSprinkle :
    Tendsto (fun n => (vanishingSprinkle n:ℝ)) atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem sprinkle_sequence_gt (p : unitInterval) (hp : (p:ℝ) < 1) (n : ℕ) :
    p < sprinkleParameter p (vanishingSprinkle n) := by
  change (p:ℝ) < (p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)
  exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hp) (vanishingSprinkle_pos n))

theorem tendsto_sprinkle_sequence (p : unitInterval) :
    Tendsto (fun n => sprinkleParameter p (vanishingSprinkle n)) atTop (nhds p) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => (p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)) atTop (nhds (p:ℝ))
  convert tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_vanishingSprinkle) using 1; simp

theorem tendsto_sprinkle_sequence_right (p : unitInterval) (hp : (p:ℝ) < 1) :
    Tendsto (fun n => (sprinkleParameter p (vanishingSprinkle n):ℝ)) atTop (nhdsWithin (p:ℝ) (Set.Ioi (p:ℝ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨continuous_subtype_val.continuousAt.tendsto.comp (tendsto_sprinkle_sequence p),
    Eventually.of_forall (sprinkle_sequence_gt p hp)⟩

 

theorem rootSusceptibility_sequence_slope_lower
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) (hp : p < pc G) (Q : Finset E) (F : Finset V) (d : ℝ)
    (hd : d < finiteRootPivotalMass G root weight p Q F) :
    ∀ᶠ n in atTop,
      ((sprinkleParameter p (vanishingSprinkle n):ℝ)-(p:ℝ))*d ≤
      rootSusceptibility G root weight (sprinkleParameter p (vanishingSprinkle n)) -
      rootSusceptibility G root weight p := by
  have ht : Tendsto (fun n => (1-(vanishingSprinkle n:ℝ))^(Q.card-1) *
      finiteRootPivotalMass G root weight p Q F) atTop
      (nhds (finiteRootPivotalMass G root weight p Q F)) := by
    convert ((tendsto_const_nhds.sub tendsto_vanishingSprinkle).pow (Q.card-1)).mul tendsto_const_nhds using 1; simp
  have hnn := finiteRootPivotalMass_nonneg G root weight hw p Q F
  filter_upwards [(tendsto_sprinkle_sequence p).eventually (eventually_lt_nhds hp),
      ht.eventually (eventually_gt_nhds hd)] with n hn hdn
  have hgain := rootSusceptibility_sprinkling_gain G hloc hqt root weight hw
    p (vanishingSprinkle n) hn Q F
  change (vanishingSprinkle n:ℝ)*(1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
    finiteRootPivotalMass G root weight p Q F ≤ _ at hgain
  by_cases hd0 : 0 ≤ d
  · have hdp : (1-(p:ℝ))*d ≤ (1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
        finiteRootPivotalMass G root weight p Q F := by
      calc
        _ ≤ d := by nlinarith [p.2.1]
        _ ≤ _ := hdn.le
    have hm := mul_le_mul_of_nonneg_left hdp (vanishingSprinkle n).2.1
    calc
      _ = (vanishingSprinkle n:ℝ)*((1-(p:ℝ))*d) := by
        change ((p:ℝ)+(1-(p:ℝ))*(vanishingSprinkle n:ℝ)-(p:ℝ))*d = _
        ring
      _ ≤ (vanishingSprinkle n:ℝ)*((1-(vanishingSprinkle n:ℝ))^(Q.card-1)*
          finiteRootPivotalMass G root weight p Q F) := hm
      _ ≤ _ := by simpa only [mul_assoc] using hgain
  · have hmono : 0 ≤ rootSusceptibility G root weight (sprinkleParameter p (vanishingSprinkle n)) - rootSusceptibility G root weight p :=
      (mul_nonneg (mul_nonneg (vanishingSprinkle n).2.1 (pow_nonneg (sub_nonneg.mpr (vanishingSprinkle n).2.2) _)) hnn).trans hgain
    have hdp : ((sprinkleParameter p (vanishingSprinkle n):ℝ)-(p:ℝ))*d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (sprinkleParameter_ge_left _ _)) (le_of_not_ge hd0)
    linarith

end VanishingSprinkles
end Percolation

 
namespace Percolation
open Filter
section NegativePowerRightSlopes

 

theorem frequently_rpow_slope_le_of_sequence
    (f : ℝ → ℝ) (x d e : ℝ) (hx : 0 < f x) (hd : 0 < d) (he : e < 0)
    (z : ℕ → ℝ) (hz : Tendsto z atTop (nhdsWithin x (Set.Ioi x)))
    (hgain : ∀ᶠ n in atTop, (z n-x)*d ≤ f (z n)-f x) :
    ∀ r, e*(f x)^(e-1)*d < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope (fun t => (f t)^e) x y < r := by
  let A (t : ℝ) := f x+(t-x)*d
  have hA : HasDerivAt A d x := by
    simpa only [zero_add, one_mul] using! (hasDerivAt_const x (f x)).add (((hasDerivAt_id x).sub_const x).mul_const d)
  have hAx : A x = f x := by simp [A]
  have hR : HasDerivAt (fun t => (A t)^e) (e*(f x)^(e-1)*d) x := by
    simpa only [hAx] using! (Real.hasDerivAt_rpow_const (p := e) (Or.inl (show A x ≠ 0 by rw [hAx]; exact hx.ne'))).comp x hA
  intro r hr
  have hlim := hR.tendsto_slope.comp (hz.mono_right (nhdsWithin_mono x (show Set.Ioi x ⊆ {x}ᶜ from fun y hy => by simpa using ne_of_gt hy)))
  have hright : ∀ᶠ n in atTop, x < z n := (tendsto_nhdsWithin_iff.mp hz).2
  apply hz.frequently
  apply Filter.Eventually.frequently
  filter_upwards [hgain, hright, hlim.eventually (eventually_lt_nhds hr)] with n hn hzn hnr
  have hApos : 0 < A (z n) := by dsimp [A]; positivity
  have hAr : A (z n) ≤ f (z n) := by dsimp [A]; linarith
  have hp := Real.rpow_le_rpow_of_nonpos hApos hAr he.le
  apply lt_of_le_of_lt _ hnr
  simp only [Function.comp_apply, slope_def_field, hAx]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hp _) (sub_pos.mpr hzn).le

end NegativePowerRightSlopes
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ActualSusceptibilityRightSlope
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootSusceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ rootSusceptibility G root weight p := by
  calc
    1 = ∑ i, weight i*1 := by simp only [mul_one, hw1]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (susceptibility_one_le G hloc hqt p hp (root i)) (hw i))

theorem continuousAt_realRootSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp : p < pc G) :
    ContinuousAt (realRootSusceptibility G root weight) (p:ℝ) := by
  apply ContinuousAt.comp (f := Set.projIcc 0 1 zero_le_one)
  · simpa only [Set.projIcc_val] using continuousAt_rootSusceptibility_subcritical G hloc hqt root weight p hp
  · exact continuous_projIcc.continuousAt

 

theorem rootSusceptibility_power_right_slope
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (b γ : ℝ) (hb : 0 < b) (hγ : γ < 1)
    (hD : b*(rootSusceptibility G root weight p)^(2-γ) ≤ rootNeighborMoment G hloc root weight p) :
    ∀ r, -(1-γ)*b/4 < r → ∃ᶠ y in nhdsWithin (p:ℝ) (Set.Ioi (p:ℝ)),
      slope (fun t => (realRootSusceptibility G root weight t)^(γ-1)) (p:ℝ) y < r := by
  let χ := rootSusceptibility G root weight p
  have hχ : 0 < χ := lt_of_lt_of_le zero_lt_one (rootSusceptibility_one_le G hloc hqt root weight hw hw1 p hp)
  let d := (b/4)*χ^(2-γ)
  have hd : 0 < d := mul_pos (by positivity) (Real.rpow_pos_of_pos hχ _)
  have hBd : d < rootNeighborMoment G hloc root weight p/2 := by
    dsimp [d, χ] at *
    nlinarith [Real.rpow_pos_of_pos hχ (2-γ)]
  obtain ⟨Q,F,hQ⟩ := exists_finiteRootPivotalMass_gt G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin p hp d hBd
  have hg := rootSusceptibility_sequence_slope_lower G hloc hqt root weight hw p hp Q F d hQ
  have hp1 : (p:ℝ) < 1 := lt_of_lt_of_le hp (pc G).2.2
  have hsl := frequently_rpow_slope_le_of_sequence (realRootSusceptibility G root weight)
    (p:ℝ) d (γ-1) (by simpa only [realRootSusceptibility_coe] using hχ) hd (by linarith)
    (fun n => (sprinkleParameter p (vanishingSprinkle n):ℝ)) (tendsto_sprinkle_sequence_right p hp1)
    (by simpa only [realRootSusceptibility_coe] using hg)
  have heq : (γ-1)*(realRootSusceptibility G root weight (p:ℝ))^(γ-1-1)*d = -(1-γ)*b/4 := by
    rw [realRootSusceptibility_coe]
    change (γ-1)*χ^(γ-1-1)*((b/4)*χ^(2-γ)) = _
    rw [show γ-1-1 = γ-2 by ring]
    calc
      _ = ((γ-1)*b/4)*(χ^(γ-2)*χ^(2-γ)) := by ring
      _ = _ := by rw [←Real.rpow_add hχ, sub_add_sub_cancel, sub_self, Real.rpow_zero]; ring
  rwa [heq] at hsl

end ActualSusceptibilityRightSlope
end Percolation

 
namespace Percolation
open Filter
section IntegratedRightSlopes

 

theorem interval_decrease_of_right_slope (f : ℝ → ℝ) (a b k : ℝ)
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hs : ∀ x ∈ Set.Ico a b, ∀ r, -k < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope f x y < r) :
    k*(b-a) ≤ f a-f b := by
  let B (t : ℝ) := f a-k*(t-a)
  have hB : ContinuousOn B (Set.Icc a b) := by fun_prop
  have hB' (x : ℝ) : HasDerivAt B (-k) x := by
    simpa only [one_mul, sub_zero, mul_one, zero_sub] using!
      (hasDerivAt_const x (f a)).sub (((hasDerivAt_id x).sub_const a).const_mul k)
  have h := image_le_of_liminf_slope_right_le_deriv_boundary hf
    (show f a ≤ B a by simp [B]) hB (fun x _ => (hB' x).hasDerivWithinAt) hs ⟨hab,le_rfl⟩
  dsimp [B] at h
  linarith

 

theorem right_slope_distance_bound (f : ℝ → ℝ) (a b k : ℝ)
    (hab : a < b) (hk : 0 < k)
    (hpos : ∀ x ∈ Set.Ico a b, 0 ≤ f x)
    (hc : ContinuousOn f (Set.Ico a b))
    (hs : ∀ x ∈ Set.Ico a b, ∀ r, -k < r →
      ∃ᶠ y in nhdsWithin x (Set.Ioi x), slope f x y < r) :
    k*(b-a) ≤ f a := by
  have hbound (r : ℝ) (hr : r ∈ Set.Ico a b) : k*(r-a) ≤ f a := by
    have hsub : Set.Icc a r ⊆ Set.Ico a b := fun t ht => ⟨ht.1,lt_of_le_of_lt ht.2 hr.2⟩
    have h := interval_decrease_of_right_slope f a r k hr.1 (hc.mono hsub)
      (fun x hx => hs x ⟨hx.1,lt_trans hx.2 hr.2⟩)
    linarith [hpos r hr]
  by_contra h
  have hd : a+f a/k < b := by
    have hh : f a < k*(b-a) := lt_of_not_ge h
    have hv : f a/k < b-a := (div_lt_iff₀ hk).mpr (by nlinarith)
    linarith
  obtain ⟨r,hr1,hr2⟩ := exists_between hd
  have ha : a ≤ r := by
    have hf := hpos a ⟨le_rfl,hab⟩
    have hd0 := div_nonneg hf hk.le
    linarith
  have hb := hbound r ⟨ha,hr2⟩
  have hr : f a < (r-a)*k := (div_lt_iff₀ hk).mp (by linarith : f a/k < r-a)
  nlinarith

end IntegratedRightSlopes
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ActualIntegratedSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem susceptibility_bound_of_neighborMoment
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (b γ : ℝ) (hb : 0 < b) (hγ : γ < 1)
    (hD : ∀ q, p ≤ q → q < pc G → b*(rootSusceptibility G root weight q)^(2-γ) ≤
      rootNeighborMoment G hloc root weight q) :
    rootSusceptibility G root weight p ≤
      (((1-γ)*b/4)*((pc G:ℝ)-(p:ℝ)))^(-1/(1-γ)) := by
  let k := (1-γ)*b/4
  have hk : 0 < k := by dsimp [k]; positivity
  let f (t : ℝ) := (realRootSusceptibility G root weight t)^(γ-1)
  have hparam (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans p.2.1 ht.1, le_trans ht.2.le (pc G).2.2⟩
  have hcp (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :
      ContinuousAt (realRootSusceptibility G root weight) t :=
    continuousAt_realRootSusceptibility G hloc hqt root weight ⟨t,hparam t ht⟩ ht.2
  have hpos (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :
      0 < realRootSusceptibility G root weight t := by
    have hh := rootSusceptibility_one_le G hloc hqt root weight hw hw1 ⟨t,hparam t ht⟩ ht.2
    rw [←realRootSusceptibility_coe] at hh
    exact lt_of_lt_of_le zero_lt_one hh
  have hcont : ContinuousOn f (Set.Ico (p:ℝ) (pc G:ℝ)) := by
    intro t ht
    exact ((hcp t ht).rpow_const (Or.inl (hpos t ht).ne')).continuousWithinAt
  have hs (t : ℝ) (ht : t ∈ Set.Ico (p:ℝ) (pc G:ℝ)) :=
    rootSusceptibility_power_right_slope G hconn hloc hqt root weight Γ hΓ htr hcov hw hw1 c hc hmin
      ⟨t,hparam t ht⟩ ht.2 b γ hb hγ (hD ⟨t,hparam t ht⟩ ht.1 ht.2)
  have hdist : k*((pc G:ℝ)-(p:ℝ)) ≤ f (p:ℝ) := by
    apply right_slope_distance_bound f (p:ℝ) (pc G:ℝ) k hp hk
      (fun t ht => (Real.rpow_pos_of_pos (hpos t ht) _).le) hcont
    intro t ht r hr
    apply hs t ht r
    dsimp [k] at hr
    linarith
  have hχ := lt_of_lt_of_le zero_lt_one (rootSusceptibility_one_le G hloc hqt root weight hw hw1 p hp)
  have hd : 0 < k*((pc G:ℝ)-(p:ℝ)) := mul_pos hk (sub_pos.mpr hp)
  have he : -1/(1-γ) = 1/(γ-1) := by rw [show γ-1=-(1-γ) by ring, div_neg, neg_div]
  have he0 : 1/(γ-1) < 0 := one_div_neg.mpr (by linarith)
  have hinv := Real.rpow_le_rpow_of_nonpos hd hdist he0.le
  rw [he]
  apply le_trans _ hinv
  change rootSusceptibility G root weight p ≤
    ((realRootSusceptibility G root weight (p:ℝ))^(γ-1))^(1/(γ-1))
  rw [realRootSusceptibility_coe,←Real.rpow_mul hχ.le]
  rw [mul_one_div_cancel (by linarith : γ-1 ≠ 0),Real.rpow_one]

end ActualIntegratedSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SusceptibilityGrowthConsequence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem eventually_upper_interval_unit (p₀ : unitInterval) (P : unitInterval → Prop)
    (h : ∀ᶠ p in nhds p₀, P p) :
    ∀ᶠ p in nhds p₀, p < p₀ → ∀ q, p ≤ q → q < p₀ → P q := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp h
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨ε,hε,?_⟩
  intro p hp hpp q hpq hq
  apply hball
  have hd : dist q p₀ ≤ dist p p₀ := by
    change |(q:ℝ)-(p₀:ℝ)| ≤ |(p:ℝ)-(p₀:ℝ)|
    rw [abs_of_nonpos (sub_nonpos.mpr (show (q:ℝ) ≤ (p₀:ℝ) from hq.le)),abs_of_nonpos (sub_nonpos.mpr (show (p:ℝ) ≤ (p₀:ℝ) from hpp.le))]
    have hpqR : (p:ℝ) ≤ (q:ℝ) := hpq
    linarith
  exact lt_of_le_of_lt hd hp

 

theorem susceptibility_growth_of_divergent_moment
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G))) :
    ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in nhds (pc G), p < pc G →
      rootSusceptibility G root weight p ≤ C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ)) := by
  intro γ hγ hγ1
  obtain ⟨b,hb,hnear⟩ := neighborMoment_growth_of_divergent_moment G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 (pc G) hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv γ hγ
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hw i)).le)
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  let k := (1-γ)*b/4
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k^(-1/(1-γ)),Real.rpow_pos_of_pos hk _,?_⟩
  filter_upwards [eventually_upper_interval_unit (pc G) _ hnear] with p hp
  intro hpc
  have hD (q : unitInterval) (hpq : p ≤ q) (hq : q < pc G) := hp hpc q hpq hq hq
  have hs := susceptibility_bound_of_neighborMoment G hconn hloc hqt root weight Γ hΓ htr hcov
    (fun i => (hw i).le) hw1 c hc hmin p hpc b γ hb hγ1 hD
  rwa [Real.mul_rpow hk.le (sub_pos.mpr (show (p:ℝ) < (pc G:ℝ) from hpc)).le] at hs

end SusceptibilityGrowthConsequence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedSearchTransfer
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exponential_transfer_of_deriv_bound (H : ℝ → ℝ) (a b K : ℝ)
    (hH : Differentiable ℝ H) (hab : a ≤ b)
    (hb : ∀ t ∈ Set.Icc a b, deriv H t ≤ K*H t) :
    H b ≤ Real.exp (K*(b-a))*H a := by
  let F (t : ℝ) := Real.exp (-K*(t-a))*H t
  have hF (t : ℝ) : HasDerivAt F (Real.exp (-K*(t-a))*(deriv H t-K*H t)) t := by
    have he := (((hasDerivAt_id t).sub_const a).const_mul (-K)).exp
    convert! he.mul (hH t).hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    ring
  have hanti : AntitoneOn F (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hb t (interior_subset ht)))
  have h := hanti ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (K*(b-a))).le
  simpa only [F, sub_self,mul_zero,Real.exp_zero,one_mul,←mul_assoc,←Real.exp_add,
    neg_mul,add_neg_cancel,Real.exp_zero,one_mul,neg_zero,add_zero] using hm

 

theorem markedConnection_transfer (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (p q h : unitInterval) (hp : 0 < (p:ℝ)) (hpq : p ≤ q) (hq : (q:ℝ) < 1)
    (hh : 0 < (h:ℝ)) :
    markedConnectionPolynomial G Q x h q ≤
      Real.exp ((Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ)))) *
        Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*((q:ℝ)-(p:ℝ))) *
      markedConnectionPolynomial G Q x h p := by
  let H := markedConnectionPolynomial G Q x h
  have hdiff : Differentiable ℝ H := fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt
  apply exponential_transfer_of_deriv_bound H p q _ hdiff hpq
  intro t ht
  let r : unitInterval := ⟨t,⟨le_trans p.2.1 ht.1,le_trans ht.2 q.2.2⟩⟩
  have hr0 : 0 < t := lt_of_lt_of_le hp ht.1
  have hr1 : t < 1 := lt_of_le_of_lt ht.2 hq
  have HB := markedConnection_derivative_bound G Q x r h hr1 hh d hd hdeg
  have hH : 0 ≤ H t := by
    change 0 ≤ markedConnectionPolynomial G Q x h r
    rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg r h _
  have hs : 0 ≤ Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ)) := Real.sqrt_nonneg _
  have hden : (p:ℝ)*(1-(q:ℝ)) ≤ t*(1-t) := by
    exact mul_le_mul ht.1 (by linarith [ht.2]) (sub_pos.mpr hq).le (by positivity)
  have hratio : Real.sqrt ((d:ℝ)/2)/(t*(1-t)) ≤
      Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ))) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos hp (sub_pos.mpr hq)) hden
  have hle : deriv H t ≤ (Real.sqrt ((d:ℝ)/2)/(t*(1-t)))*
      Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*H t := by
    have HBr : deriv H t ≤ ((Real.sqrt ((d:ℝ)/2)/(1-t))*
        Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*H t)/t := by
      apply (le_div_iff₀ hr0).mpr
      simpa only [mul_comm (deriv H t) t] using HB
    convert HBr using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  exact hle.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hs) hH)

end MarkedSearchTransfer
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedComponentIdentity
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem markedConnection_component_polynomial (G : BondGraph V E)
    (Q : Finset E) (x : V) (h p : ℝ) :
    markedConnectionPolynomial G Q x h p =
      bernoulliPolynomial Q (fun ω => 1-(1-h)^(finiteRootComponent G ω x).card) p := by
  apply bernoulliPolynomial_congr
  intro ω hω
  let C := finiteRootComponent G ω x
  let F := insert x (searchVertices G Q)
  have hCF : C ⊆ F := finiteRootComponent_subset G Q F x ω hω le_rfl
  have he (m : Finset V) : (∃ y ∈ m, Conn G (ω:Set E) x y) ↔ m ∩ C ≠ ∅ := by
    rw [Finset.nonempty_iff_ne_empty.symm]
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,Finset.mem_inter.mpr ⟨hy,by change y ∈ (C:Set V); simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hxy⟩⟩
    · rintro ⟨y,hy⟩
      refine ⟨y,(Finset.mem_inter.mp hy).1,?_⟩
      have hm : y ∈ (C:Set V) := (Finset.mem_inter.mp hy).2
      simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hm
  have hid : bernoulliPolynomial F (fun m => if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0) h =
      1-bernoulliPolynomial F (fun m => if m ∩ C = ∅ then 1 else 0) h := by
    calc
      _ = bernoulliPolynomial F (fun m => 1-(if m ∩ C = ∅ then 1 else 0)) h := by
        apply bernoulliPolynomial_congr
        intro m _
        by_cases hm : m ∩ C = ∅
        · have hn : ¬∃ y ∈ m, Conn G (ω:Set E) x y := fun hc => (he m).mp hc hm
          simp only [hm,hn,if_false,if_true,sub_self]
        · have hy := (he m).mpr hm
          simp only [hm,hy,if_false,if_true,sub_zero]
      _ = _ := by rw [bernoulliPolynomial_sub,bernoulliPolynomial_const]
  rw [hid,bernoulliPolynomial_restrict C F hCF (fun m => if m = ∅ then 1 else 0) h,
    bernoulliPolynomial_empty_indicator]

theorem one_sub_pow_one_sub_le (h : unitInterval) (n : ℕ) :
    1-(1-(h:ℝ))^n ≤ (h:ℝ)*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr h.2.2)
    have hn : 0 ≤ (h:ℝ)^2*n := by positivity
    nlinarith

end MarkedComponentIdentity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MarkedConnectionLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem markedConnection_integral (G : BondGraph V E) (Q : Finset E) (x : V)
    (h p : unitInterval) :
    markedConnectionPolynomial G Q x h p =
      ∫ ω, (1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard) ∂law p := by
  rw [integral_eq_bernoulliPolynomial Q p _ (by intro ω; simp only [Set.inter_assoc,Set.inter_self]),
    markedConnection_component_polynomial]
  apply bernoulliPolynomial_congr
  intro ω hω
  rw [Set.inter_eq_left.mpr (show (ω:Set E) ⊆ Q from hω)]
  congr 2
  rw [←coe_finiteRootComponent,Set.ncard_coe_finset]

theorem markedConnection_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (Q : Finset E) (x : V) (h p : unitInterval) (hp : p < pc G) :
    markedConnectionPolynomial G Q x h p ≤ (h:ℝ)*susceptibility G p x := by
  obtain ⟨hi,he⟩ := susceptibility_eq_integral G hloc hqt p hp x
  rw [markedConnection_integral,he,←integral_const_mul]
  apply integral_mono_ae
  · exact integrable_finite_local Q p _ (by intro ω; simp only [Set.inter_assoc,Set.inter_self])
  · exact hi.const_mul _
  · filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    apply (one_sub_pow_one_sub_le h _).trans
    apply mul_le_mul_of_nonneg_left _ h.2.1
    exact_mod_cast Set.ncard_le_ncard (fun y hy => conn_mono G Set.inter_subset_left hy) hω

 

theorem one_sub_pow_one_sub_ge_half (h : unitInterval) (n : ℕ)
    (hn : 1 ≤ (h:ℝ)*n) : (1:ℝ)/2 ≤ 1-(1-(h:ℝ))^n := by
  have hb (m : ℕ) : (1+(h:ℝ)*m)*(1-(h:ℝ))^m ≤ 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hp : 0 ≤ (1-(h:ℝ))^m := pow_nonneg (sub_nonneg.mpr h.2.2) _
      have ha : (1+(h:ℝ)*(m+1))*(1-(h:ℝ)) ≤ 1+(h:ℝ)*m := by
        have hh : 0 ≤ (h:ℝ)^2*((m:ℝ)+1) := by positivity
        nlinarith
      have hm := mul_le_mul_of_nonneg_right ha hp
      rw [Nat.cast_succ,pow_succ]
      nlinarith
  have hp : 0 ≤ (1-(h:ℝ))^n := pow_nonneg (sub_nonneg.mpr h.2.2) _
  have hm := mul_le_mul_of_nonneg_right hn hp
  have hb' := hb n
  nlinarith

 

theorem clusterWindow_le_markedConnection (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) (p h : unitInterval) (hh : 1 ≤ (h:ℝ)*lo) :
    clusterWindowProbability G p x lo hi ≤ 2*markedConnectionPolynomial G
      (incidentSupport G hloc (finite_reachBall hloc x hi).toFinset) x h p := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  let f (ω : Set E) := 1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard
  let A := {ω | ClusterWindow G x lo hi ω}
  have hA : MeasurableSet A := measurableSet_clusterWindow G hloc x lo hi
  have hf : Integrable f (law p) := integrable_finite_local Q p _
    (by intro ω; simp only [f,Set.inter_assoc,Set.inter_self])
  have hnon (ω : Set E) : 0 ≤ f ω := by
    apply sub_nonneg.mpr
    exact pow_le_one₀ (sub_nonneg.mpr h.2.2) (by linarith [h.2.1])
  have hbound (ω : Set E) : A.indicator (fun _ => (1:ℝ)/2) ω ≤ f ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have hs : cluster G ω x ⊆ (finite_reachBall hloc x hi).toFinset := by
        simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hω.1 hi hω.2.2.le
      have he := cluster_restrict_incident_of_full G hloc _ ω x hs
      change 1/2 ≤ 1-(1-(h:ℝ))^(cluster G (ω ∩ (Q:Set E)) x).ncard
      rw [he]
      apply one_sub_pow_one_sub_ge_half
      exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hω.2.1) h.2.1)
    · rw [Set.indicator_of_notMem hω]
      exact hnon ω
  have hib := integral_mono ((integrable_const _).indicator hA) hf hbound
  rw [integral_indicator_const _ hA] at hib
  have he := markedConnection_integral G Q x h p
  change markedConnectionPolynomial G Q x h p = ∫ ω, f ω ∂law p at he
  rw [←he] at hib
  change (law p).real A ≤ 2*markedConnectionPolynomial G Q x h p
  simp only [smul_eq_mul] at hib
  linarith

end MarkedConnectionLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_FractionalMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section GhostPowerTransfer
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem sqrt_log_power_bound (h : unitInterval) (hh : 0 < (h:ℝ))
    (a : ℝ) (ha : 1/2 < a) :
    Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a ≤ Real.sqrt (1/(2*a-1)) := by
  let ε := 2*a-1
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hpow := Real.rpow_pos_of_pos hh ε
  have hl := Real.log_le_rpow_div (show 0 ≤ 1/(h:ℝ) by positivity) hε
  rw [Real.div_rpow (by norm_num) hh.le,Real.one_rpow] at hl
  have hpowid : ((h:ℝ)^a)^2 = (h:ℝ)^ε*(h:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hh.le]
    have he : a*(2:ℝ) = ε+1 := by dsimp [ε]; ring
    norm_num only [Nat.cast_ofNat]
    rw [he,Real.rpow_add hh,Real.rpow_one]
  have hbase : (Real.log (1/(h:ℝ))/(h:ℝ))*((h:ℝ)^a)^2 ≤ 1/ε := by
    rw [hpowid]
    calc
      _ = Real.log (1/(h:ℝ))*(h:ℝ)^ε := by field_simp
      _ ≤ ((1/(h:ℝ)^ε)/ε)*(h:ℝ)^ε := mul_le_mul_of_nonneg_right hl hpow.le
      _ = 1/ε := by field_simp
  have hlog : 0 ≤ Real.log (1/(h:ℝ))/(h:ℝ) := div_nonneg
    (Real.log_nonneg ((one_le_div hh).mpr h.2.2)) hh.le
  have hsq := Real.sq_sqrt hlog
  have htarget := Real.sq_sqrt (one_div_pos.mpr hε).le
  have hn := Real.sqrt_nonneg (1/ε)
  change _ ≤ Real.sqrt (1/ε)
  nlinarith [sq_nonneg (Real.sqrt (1/ε)-Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a)]

 

theorem markedConnection_power_transfer (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (p q h : unitInterval) (hq0 : 0 < (q:ℝ)) (hq1 : (q:ℝ) < 1)
    (hp : (q:ℝ)/2 ≤ (p:ℝ)) (hh : 0 < (h:ℝ))
    (a : ℝ) (ha : 1/2 < a) (he : (q:ℝ)-(p:ℝ) = (h:ℝ)^a) :
    markedConnectionPolynomial G Q x h q ≤
      Real.exp ((Real.sqrt ((d:ℝ)/2)/(((q:ℝ)/2)*(1-(q:ℝ)))) *
        Real.sqrt (1/(2*a-1))) * markedConnectionPolynomial G Q x h p := by
  have hp0 : 0 < (p:ℝ) := lt_of_lt_of_le (half_pos hq0) hp
  have hpq : p ≤ q := by change (p:ℝ) ≤ (q:ℝ); linarith [Real.rpow_pos_of_pos hh a]
  have H := markedConnection_transfer G Q x d hd hdeg p q h hp0 hpq hq1 hh
  apply H.trans
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    rw [he]
    have hr : Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ))) ≤
        Real.sqrt ((d:ℝ)/2)/(((q:ℝ)/2)*(1-(q:ℝ))) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos (half_pos hq0) (sub_pos.mpr hq1))
        (mul_le_mul_of_nonneg_right hp (sub_pos.mpr hq1).le)
    calc
      _ = (Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ)))) *
        (Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*(h:ℝ)^a) := by ring
      _ ≤ _ := mul_le_mul hr (sqrt_log_power_bound h hh a ha)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg h.2.1 _)) (by positivity)
  · rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg p h _

end GhostPowerTransfer
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section DyadicGhostParameters
attribute [local instance] Classical.propDecidable Classical.decEq

theorem dyadicGhost_pos (j : ℕ) : 0 < (dyadicGhost j:ℝ) := pow_pos (by norm_num) _

theorem dyadicGhost_volume (j : ℕ) : (dyadicGhost j:ℝ)*(2^j:ℕ) = 1 := by
  simp only [dyadicGhost,Nat.cast_pow,Nat.cast_ofNat,←mul_pow]
  norm_num

theorem tendsto_dyadicGhost : Tendsto (fun j => (dyadicGhost j:ℝ)) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem dyadicGhost_rpow (j : ℕ) (t : ℝ) :
    (dyadicGhost j:ℝ)^t = (2:ℝ)^(-t*(j:ℝ)) := by
  change ((1/2:ℝ)^j)^t = _
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [show (1/2:ℝ) = (2:ℝ)^(-1:ℝ) by norm_num,
    ←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

 

theorem eventually_dyadic_backstep (q : unitInterval) (hq : 0 < (q:ℝ))
    (a : ℝ) (ha : 0 < a) (P : unitInterval → Prop) (hP : ∀ᶠ p in nhds q, P p) :
    ∀ᶠ j : ℕ in atTop, ∃ p : unitInterval,
      (q:ℝ)/2 ≤ (p:ℝ) ∧ p < q ∧ (q:ℝ)-(p:ℝ) = (dyadicGhost j:ℝ)^a ∧ P p := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hP
  have ht : Tendsto (fun j => (dyadicGhost j:ℝ)^a) atTop (nhds 0) := by
    simpa only [Real.zero_rpow ha.ne', Function.comp_apply] using!
      (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.comp tendsto_dyadicGhost
  filter_upwards [ht.eventually (eventually_lt_nhds (half_pos hq)),ht.eventually (eventually_lt_nhds hε)] with j hj hεj
  have hz := Real.rpow_pos_of_pos (dyadicGhost_pos j) a
  let p : unitInterval := ⟨(q:ℝ)-(dyadicGhost j:ℝ)^a,⟨by linarith,by linarith [q.2.2]⟩⟩
  refine ⟨p,by dsimp [p]; linarith,by change (q:ℝ)-(dyadicGhost j:ℝ)^a < (q:ℝ); linarith,
    by dsimp [p]; ring,?_⟩
  apply hball
  change |((q:ℝ)-(dyadicGhost j:ℝ)^a)-(q:ℝ)| < ε
  rw [show (q:ℝ)-(dyadicGhost j:ℝ)^a-(q:ℝ) = -(dyadicGhost j:ℝ)^a by ring,abs_neg,abs_of_pos hz]
  exact hεj

end DyadicGhostParameters
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section CriticalDyadicTail
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_dyadic_bound_of_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hq0 : 0 < (pc G:ℝ)) (hq1 : (pc G:ℝ) < 1)
    (C b a : ℝ) (hC : 0 < C) (ha : 1/2 < a)
    (hχ : ∀ᶠ p in nhds (pc G), p < pc G → ∀ x,
      susceptibility G p x ≤ C*((pc G:ℝ)-(p:ℝ))^(-b)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ j : ℕ in atTop, ∀ x,
      clusterWindowProbability G (pc G) x (2^j) (2^(j+1)) ≤
        K*(dyadicGhost j:ℝ)^(1-a*b) := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  let B := Real.exp ((Real.sqrt ((d:ℝ)/2)/(((pc G:ℝ)/2)*(1-(pc G:ℝ)))) * Real.sqrt (1/(2*a-1)))
  have hB : 0 < B := Real.exp_pos _
  refine ⟨2*B*C,by positivity,?_⟩
  filter_upwards [eventually_dyadic_backstep (pc G) hq0 a (by linarith) _ hχ] with j hj
  obtain ⟨p,hp,hpc,he,hχp⟩ := hj
  intro x
  let Q := incidentSupport G hloc (finite_reachBall hloc x (2^(j+1))).toFinset
  have hwin := clusterWindow_le_markedConnection G hloc x (2^j) (2^(j+1)) (pc G) (dyadicGhost j)
    (by rw [dyadicGhost_volume])
  have htra := markedConnection_power_transfer G Q x d hd
    (fun v => (incident_filter_card_le_degree G hloc Q v).trans (hdeg v)) p (pc G) (dyadicGhost j)
    hq0 hq1 hp (dyadicGhost_pos j) a ha he
  have hsub := markedConnection_le_susceptibility G hloc hqt Q x (dyadicGhost j) p hpc
  have hid : (dyadicGhost j:ℝ)*((dyadicGhost j:ℝ)^a)^(-b) = (dyadicGhost j:ℝ)^(1-a*b) := by
    rw [←Real.rpow_mul (dyadicGhost j).2.1]
    calc
      _ = (dyadicGhost j:ℝ)^1*(dyadicGhost j:ℝ)^(a*(-b)) := by rw [Real.rpow_one]
      _ = (dyadicGhost j:ℝ)^(1+a*(-b)) := (Real.rpow_add (dyadicGhost_pos j) _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ 2*markedConnectionPolynomial G Q x (dyadicGhost j) (pc G) := hwin
    _ ≤ 2*(B*markedConnectionPolynomial G Q x (dyadicGhost j) p) :=
      mul_le_mul_of_nonneg_left htra (by norm_num)
    _ ≤ 2*(B*((dyadicGhost j:ℝ)*susceptibility G p x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hB.le) (by norm_num)
    _ ≤ 2*(B*((dyadicGhost j:ℝ)*(C*((pc G:ℝ)-(p:ℝ))^(-b)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hχp hpc x) (dyadicGhost j).2.1) hB.le) (by norm_num)
    _ = 2*B*C*((dyadicGhost j:ℝ)*((dyadicGhost j:ℝ)^a)^(-b)) := by rw [he]; ring
    _ = _ := by rw [hid]

 

theorem critical_power_integrable_of_dyadic_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (α θ K : ℝ) (hα : 0 < α) (hθ : α < θ)
    (hbound : ∀ᶠ j : ℕ in atTop, ∀ x,
      clusterWindowProbability G p x (2^j) (2^(j+1)) ≤ K*(dyadicGhost j:ℝ)^θ) :
    ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) := by
  intro x
  apply integrable_cluster_power_of_dyadic G hloc p x α hα
  have hs : Summable (fun j : ℕ => K*((2:ℝ)^(α-θ))^j) := by
    apply Summable.mul_left
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hθ)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hbound] with j hj
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (clusterWindowProbability_nonneg G p x _ _))]
  calc
    _ ≤ (2:ℝ)^(α*(j:ℝ))*(K*(dyadicGhost j:ℝ)^θ) :=
      mul_le_mul_of_nonneg_left (hj x) (Real.rpow_nonneg (by norm_num) _)
    _ = K*((2:ℝ)^(α-θ))^j := by
      rw [dyadicGhost_rpow,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [show (α-θ)*(j:ℝ) = α*(j:ℝ)+(-θ*(j:ℝ)) by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
      ring

end CriticalDyadicTail
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section MomentFromGrowth
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_moment_of_susceptibility_growth [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hq0 : 0 < (pc G:ℝ)) (hq1 : (pc G:ℝ) < 1)
    (hgrowth : ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ p in nhds (pc G), p < pc G → ∀ x,
        susceptibility G p x ≤ C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ)))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :
    ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law (pc G)) := by
  let γ := (1/2-α)/2
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  have hprod : (1/2:ℝ) < (1-γ)*(1-α) := by
    have : 0 < γ*α := mul_pos hγ hα
    dsimp [γ] at *
    nlinarith
  obtain ⟨a,ha,hap⟩ := exists_between hprod
  have hden : 0 < 1-γ := sub_pos.mpr hγ1
  obtain ⟨C,hC,hnear⟩ := hgrowth γ hγ hγ1
  have he : -(1/(1-γ)) = -1/(1-γ) := by ring
  obtain ⟨K,hK,hbound⟩ := critical_dyadic_bound_of_susceptibility G hloc hqt hq0 hq1
    C (1/(1-γ)) a hC ha (by simpa only [he] using hnear)
  apply critical_power_integrable_of_dyadic_bound G hloc (pc G) α (1-a*(1/(1-γ))) K hα _ hbound
  have : a*(1/(1-γ)) < 1-α := by
    rw [mul_one_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [hap]
  linarith

end MomentFromGrowth
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section CriticalRootMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_root_power_integrable
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :
    ∀ i, Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G)) := by
  by_contra hbad
  have hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G)) :=
    not_forall.mp hbad
  obtain ⟨β,hαβ,hβ⟩ := exists_between hα1
  let ε := (1/2-β)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hε1 : ε < 1/2 := by dsimp [ε]; linarith
  have hsmall : β+(1/2+ε) < 1 := by dsimp [ε]; linarith
  have hg := susceptibility_growth_of_divergent_moment G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 hp₀ hp₁ hfin α β ε hα hαβ hε hε1 hsmall hdiv
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 < c := Finset.sum_pos (fun i _ => one_div_pos.mpr (hw i)) Finset.univ_nonempty
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  have hall := critical_moment_of_susceptibility_growth G hloc hqt hp₀ hp₁ (by
    intro γ hγ hγ1
    obtain ⟨C,hC,hnear⟩ := hg γ hγ hγ1
    refine ⟨c*C,mul_pos hc hC,?_⟩
    filter_upwards [hnear] with p hp
    intro hpc x
    calc
      _ ≤ c*rootSusceptibility G root weight p :=
        susceptibility_le_rootSusceptibility G root weight (fun i => (hw i).le) hcover c hc.le hmin p x
      _ ≤ c*(C*((pc G:ℝ)-(p:ℝ))^(-1/(1-γ))) := mul_le_mul_of_nonneg_left (hp hpc) hc.le
      _ = _ := by ring) α hα hα1
  obtain ⟨i,hi⟩ := hdiv
  exact hi (hall (root i))

end CriticalRootMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformFractionalMoments
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_cluster_power (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (α : ℝ) :
    Measurable (fun ω : Set E => ((cluster G ω x).ncard:ℝ)^α) :=
  (measurable_of_countable (fun n : ℕ => (n:ℝ)^α)).comp (measurable_cluster_ncard G hloc x)

theorem integrable_cluster_power_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (α : ℝ) :
    Integrable (fun ω => ((cluster G ω (a x)).ncard:ℝ)^α) (law p) ↔
      Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) := by
  have h := integrable_map_measure (μ := law p)
    (measurable_cluster_power G hloc x α).aestronglyMeasurable
    (measurable_set_preimage b).aemeasurable
  rw [law_map_preimage_equiv] at h
  have he : ((fun ω : Set E => ((cluster G ω x).ncard:ℝ)^α) ∘ (fun ω => b ⁻¹' ω)) =
      (fun ω : Set E => ((cluster G ω (a x)).ncard:ℝ)^α) := by
    funext ω
    dsimp only [Function.comp_apply]
    rw [cluster_ncard_covariant G hab]
  rw [he] at h
  exact h.symm

theorem integral_cluster_power_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (α : ℝ) :
    (∫ ω, ((cluster G ω (a x)).ncard:ℝ)^α ∂law p) =
      ∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p := by
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable
    (measurable_cluster_power G hloc x α).aestronglyMeasurable
  rw [law_map_preimage_equiv] at h
  simpa only [cluster_ncard_covariant G hab] using! h.symm

 
theorem uniform_cluster_power_of_root [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (α : ℝ)
    (hi : ∀ i, Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x,
      Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) ∧
      (∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) ≤ C := by
  let C := 1+∑ i, ∫ ω, ((cluster G ω (root i)).ncard:ℝ)^α ∂law p
  have hn (x : V) : 0 ≤ ∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p :=
    integral_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC : 0 < C := by dsimp [C]; linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hn (root i))]
  refine ⟨C,hC,?_⟩
  intro x
  obtain ⟨i,a,b,hab,rfl⟩ := hcover x
  refine ⟨(integrable_cluster_power_covariant G hloc p hab (root i) α).mpr (hi i),?_⟩
  rw [integral_cluster_power_covariant G hloc p hab]
  have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hn (root j)) (Finset.mem_univ i)
  dsimp [C]
  linarith

end UniformFractionalMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FractionalMomentCoupling
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_power_mono_integral [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (p q : unitInterval) (hpq : p ≤ q)
    (α : ℝ) (hα : 0 ≤ α)
    (hfin : ∀ᵐ ω ∂law q, (cluster G ω x).Finite)
    (hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law q)) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) ∧
      (∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) ≤
      ∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law q := by
  let f (r : unitInterval) (labels : E → unitInterval) := ((cluster G (openEdges labels r) x).ncard:ℝ)^α
  have hm (r : unitInterval) : Measurable (f r) :=
    (measurable_cluster_power G hloc x α).comp (measurable_openEdges r)
  have hmap (r : unitInterval) :
      Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law r) ↔ Integrable (f r) labelLaw := by
    rw [←map_openEdges r]
    exact integrable_map_measure (measurable_cluster_power G hloc x α).aestronglyMeasurable
      (measurable_openEdges r).aemeasurable
  have hf : ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), (cluster G (openEdges labels q) x).Finite := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges q).aemeasurable
    rwa [map_openEdges]
  have hle : f p ≤ᵐ[labelLaw] f q := by
    filter_upwards [hf] with labels hlabels
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hα
    exact_mod_cast Set.ncard_le_ncard (show cluster G (openEdges labels p) x ⊆ cluster G (openEdges labels q) x from
      fun y hy => conn_mono G (openEdges_mono labels hpq) hy) hlabels
  have hiq := (hmap q).mp hi
  have hip : Integrable (f p) labelLaw := hiq.mono' (hm p).aestronglyMeasurable (by
    filter_upwards [hle] with labels hl
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] )
  refine ⟨(hmap p).mpr hip,?_⟩
  have he (r : unitInterval) : (∫ labels, f r labels ∂labelLaw) =
      ∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law r := by
    rw [←map_openEdges r]
    exact (integral_map (measurable_openEdges r).aemeasurable
      (measurable_cluster_power G hloc x α).aestronglyMeasurable).symm
  rw [←he p,←he q]
  exact integral_mono_ae hip hiq hle

end FractionalMomentCoupling
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section GhostFractionalPower
attribute [local instance] Classical.propDecidable Classical.decEq

theorem one_sub_pow_one_sub_le_power (h : unitInterval) (n : ℕ) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    1-(1-(h:ℝ))^n ≤ (h:ℝ)^α*(n:ℝ)^α := by
  rw [←Real.mul_rpow h.2.1 (Nat.cast_nonneg _)]
  by_cases ht : (h:ℝ)*n ≤ 1
  · exact (one_sub_pow_one_sub_le h n).trans (Real.self_le_rpow_of_le_one (mul_nonneg h.2.1 (Nat.cast_nonneg _)) ht hα1)
  · have ht' : 1 ≤ (h:ℝ)*n := (lt_of_not_ge ht).le
    exact (sub_le_self _ (pow_nonneg (sub_nonneg.mpr h.2.2) _)).trans (Real.one_le_rpow ht' hα)

theorem markedConnection_le_cluster_power (G : BondGraph V E) (Q : Finset E)
    (x : V) (h p : unitInterval) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p)) :
    markedConnectionPolynomial G Q x h p ≤ (h:ℝ)^α*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) := by
  rw [markedConnection_integral,←integral_const_mul]
  apply integral_mono_ae
  · exact integrable_finite_local Q p _ (by intro ω; simp only [Set.inter_assoc,Set.inter_self])
  · exact hi.const_mul _
  · filter_upwards [hfin] with ω hω
    apply (one_sub_pow_one_sub_le_power h _ α hα hα1).trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg h.2.1 _)
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hα
    exact_mod_cast Set.ncard_le_ncard (fun y hy => conn_mono G Set.inter_subset_left hy) hω

end GhostFractionalPower
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterTailCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClusterTailIndicator_mono (G : BondGraph V E) (x : V) (n : ℕ) :
    Monotone (finiteClusterTailIndicator G x n) := by
  intro ω η hωη
  have hc := Finset.card_le_card (finiteRootComponent_mono G hωη x)
  unfold finiteClusterTailIndicator
  split_ifs <;> norm_num
  omega

theorem finiteClusterTail_nonneg (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    0 ≤ finiteClusterTail G Q x n p := by
  apply bernoulliPolynomial_nonneg _ _ p p.2
  intro ω _
  unfold finiteClusterTailIndicator
  split_ifs <;> norm_num

end ClusterTailCovariance
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_TailBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteStretchedTail
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_finite_ae_mono [Countable E] (G : BondGraph V E)
    (x : V) (p q : unitInterval) (hpq : p ≤ q)
    (hq : ∀ᵐ ω ∂law q, (cluster G ω x).Finite) :
    ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
  have hlabels : ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      (cluster G (openEdges labels q) x).Finite := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges q).aemeasurable
    rwa [map_openEdges]
  rw [←map_openEdges p]
  apply (ae_map_iff (measurable_openEdges p).aemeasurable
    (by simpa only [Set.compl_ofPred,Set.not_infinite] using (measurableSet_infinite_cluster G x).compl)).mpr
  filter_upwards [hlabels] with labels hl
  exact hl.subset (fun y h => conn_mono G (openEdges_mono labels hpq) h)

theorem finiteClusterTail_le_markedConnection (G : BondGraph V E) (Q : Finset E)
    (x : V) (n : ℕ) (p h : unitInterval) (hn : 1 ≤ (h:ℝ)*n) :
    finiteClusterTail G Q x n p ≤ 2*markedConnectionPolynomial G Q x h p := by
  have hh : (1:ℝ)/2*finiteClusterTail G Q x n p ≤ markedConnectionPolynomial G Q x h p := by
    rw [finiteClusterTail,←bernoulliPolynomial_const_mul,markedConnection_component_polynomial]
    apply bernoulliPolynomial_mono _ _ _ p p.2
    intro ω _
    unfold finiteClusterTailIndicator
    by_cases hs : n ≤ (finiteRootComponent G ω x).card
    · simp only [ite_eq_left hs,mul_one]
      apply one_sub_pow_one_sub_ge_half
      exact hn.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) h.2.1)
    · simp only [ite_eq_right hs,mul_zero]
      apply sub_nonneg.mpr
      exact pow_le_one₀ (sub_nonneg.mpr h.2.2) (by linarith [h.2.1])
  linarith



end FiniteStretchedTail
end Percolation

 
namespace Percolation
open MeasureTheory Filter
section ExponentialPowerBound

 

theorem exists_exp_neg_le_rpow (r : ℝ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → Real.exp (-t) ≤ K*t^(-r) := by
  obtain ⟨m,hm⟩ := exists_nat_ge r
  let K : ℝ := m.factorial
  have hK1 : 1 ≤ K := by
    dsimp [K]
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos m))
  refine ⟨K,by linarith,?_⟩
  intro t ht
  rw [Real.rpow_neg ht.le,←div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht r)).mpr
  by_cases ht1 : t ≤ 1
  · have hp := Real.rpow_le_one ht.le ht1 hr
    have he : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    exact (mul_le_of_le_one_left (Real.rpow_nonneg ht.le r) he).trans (hp.trans hK1)
  · have hpow : t^r ≤ t^m := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le (le_of_not_ge ht1) hm
    have hTaylor : t^m ≤ K*Real.exp t := by
      have hh := Real.pow_div_factorial_le_exp t ht.le m
      exact (div_le_iff₀ (show (0:ℝ) < (m.factorial:ℝ) by positivity)).mp hh |>.trans_eq (mul_comm _ _)
    calc
      _ ≤ Real.exp (-t)*(K*Real.exp t) :=
        mul_le_mul_of_nonneg_left (hpow.trans hTaylor) (Real.exp_pos _).le
      _ = K := by rw [Real.exp_neg]; field_simp

end ExponentialPowerBound
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SourceAlmostLinear
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_finite_ae_covariant [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    ∀ᵐ ω ∂law p, (cluster G ω (a x)).Finite := by
  have hh : ∀ᵐ ω ∂law p, (cluster G (b ⁻¹' ω) x).Finite := by
    apply ae_of_ae_map (μ := law p) (p := fun ω : Set E => (cluster G ω x).Finite)
      (measurable_set_preimage b).aemeasurable
    rwa [law_map_preimage_equiv]
  filter_upwards [hh] with ω hω
  rw [←cluster_aut G hab ω x]
  exact hω.image a



end SourceAlmostLinear
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section QueryTranscriptLaw
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

theorem leaf_congr (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {ω η : Finset E} (h : ∀ e ∈ Q, e ∈ ω ↔ e ∈ η) : t.leaf ω = t.leaf η := by
  induction t generalizing Q with
  | done => rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    simp only [leaf,h e ht.1]
    split
    · rw [ih₁ ht.2.2 (fun a ha => h a (Finset.mem_of_mem_erase ha))]
    · rw [ih₀ ht.2.1 (fun a ha => h a (Finset.mem_of_mem_erase ha))]

theorem leaf_insert (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {e : E} (he : e ∉ Q) (ω : Finset E) : t.leaf (insert e ω) = t.leaf ω := by
  apply leaf_congr t ht
  intro a ha
  simp [show a ≠ e from fun h => he (h ▸ ha)]

 
theorem leaf_expectation (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : ℝ) (f : t.forget.Leaf → ℝ) :
    bernoulliPolynomial Q (fun ω => f (t.leaf ω)) p =
      ∑ l, ProbeTree.weight p 0 t.forget l*f l := by
  induction t generalizing Q with
  | done b =>
    change bernoulliPolynomial Q (fun _ => f ()) p = ∑ l : Unit, 1*f l
    simp [bernoulliPolynomial_const,Finset.sum_singleton]
  | query e t₀ t₁ ih₀ ih₁ =>
    obtain ⟨he,h₀,h₁⟩ := ht
    conv_lhs => rw [←Finset.insert_erase he]
    rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
    have hc : bernoulliPolynomial (Q.erase e) (fun ω => f ((query e t₀ t₁).leaf ω)) p =
        bernoulliPolynomial (Q.erase e) (fun ω => f (Sum.inl (t₀.leaf ω))) p := by
      apply bernoulliPolynomial_congr
      intro ω hω
      simp only [leaf,show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),if_false]
    have ho : bernoulliPolynomial (Q.erase e) (fun ω => f ((query e t₀ t₁).leaf (insert e ω))) p =
        bernoulliPolynomial (Q.erase e) (fun ω => f (Sum.inr (t₁.leaf ω))) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      simp only [leaf,Finset.mem_insert_self,if_true,
        leaf_insert t₁ h₁ (Finset.notMem_erase e Q)]
    rw [hc,ho,ih₀ h₀ (fun l => f (Sum.inl l)),ih₁ h₁ (fun l => f (Sum.inr l))]
    change _ = ∑ l : t₀.forget.Leaf ⊕ t₁.forget.Leaf, _
    simp only [Fintype.sum_sum_type,ProbeTree.weight,Finset.mul_sum,mul_assoc]


theorem score_mgf (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (lam : ℝ) :
    bernoulliPolynomial Q (fun ω => Real.exp (lam*t.score p ω-lam^2*(t.queryCount ω:ℝ)/8)) p ≤ 1 := by
  change bernoulliPolynomial Q (fun ω => Real.exp (lam*ProbeTree.score p t.forget (t.leaf ω)-
    lam^2*(ProbeTree.queries t.forget (t.leaf ω):ℝ)/8)) p ≤ 1
  rw [leaf_expectation t ht p (fun l => Real.exp (lam*ProbeTree.score p t.forget l-
    lam^2*(ProbeTree.queries t.forget l:ℝ)/8))]
  exact ProbeTree.score_mgf p 0 lam t.forget

end EdgeQueryTree
end QueryTranscriptLaw
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section CappedQueryConcentration
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

 

theorem capped_score_mgf (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (lam : ℝ) (N : ℕ) (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => Real.exp (lam*t.score p ω)) p ≤ Real.exp (lam^2*(N:ℝ)/8) := by
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => Real.exp (lam^2*(N:ℝ)/8)*
        Real.exp (lam*t.score p ω-lam^2*(t.queryCount ω:ℝ)/8)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω hω
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn : (t.queryCount ω:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr (hN ω hω)
      nlinarith [sq_nonneg lam]
    _ = Real.exp (lam^2*(N:ℝ)/8)*bernoulliPolynomial Q
        (fun ω => Real.exp (lam*t.score p ω-lam^2*(t.queryCount ω:ℝ)/8)) p :=
      bernoulliPolynomial_const_mul _ _ _ _
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left (t.score_mgf ht p lam) (Real.exp_pos _).le

theorem capped_score_chernoff (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (lam a : ℝ) (hlam : 0 ≤ lam) (N : ℕ)
    (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => if a ≤ t.score p ω then 1 else 0) p ≤
      Real.exp (-lam*a+lam^2*(N:ℝ)/8) := by
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => Real.exp (-lam*a)*Real.exp (lam*t.score p ω)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      split_ifs with h
      · rw [←Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      · positivity
    _ = Real.exp (-lam*a)*bernoulliPolynomial Q (fun ω => Real.exp (lam*t.score p ω)) p :=
      bernoulliPolynomial_const_mul _ _ _ _
    _ ≤ Real.exp (-lam*a)*Real.exp (lam^2*(N:ℝ)/8) :=
      mul_le_mul_of_nonneg_left (t.capped_score_mgf ht p lam N hN) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem capped_neg_score_chernoff (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (lam a : ℝ) (hlam : 0 ≤ lam) (N : ℕ)
    (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => if a ≤ -t.score p ω then 1 else 0) p ≤
      Real.exp (-lam*a+lam^2*(N:ℝ)/8) := by
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => Real.exp (-lam*a)*Real.exp ((-lam)*t.score p ω)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      split_ifs with h
      · rw [←Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      · positivity
    _ = Real.exp (-lam*a)*bernoulliPolynomial Q (fun ω => Real.exp ((-lam)*t.score p ω)) p :=
      bernoulliPolynomial_const_mul _ _ _ _
    _ ≤ Real.exp (-lam*a)*Real.exp ((-lam)^2*(N:ℝ)/8) :=
      mul_le_mul_of_nonneg_left (t.capped_score_mgf ht p (-lam) N hN) (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

 

theorem capped_score_tail (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN0 : 0 < N)
    (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => if a ≤ |t.score p ω| then 1 else 0) p ≤
      2*Real.exp (-2*a^2/(N:ℝ)) := by
  let lam : ℝ := 4*a/(N:ℝ)
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN0
  have hlam : 0 ≤ lam := div_nonneg (by positivity) hNr.le
  have he : -lam*a+lam^2*(N:ℝ)/8 = -2*a^2/(N:ℝ) := by
    dsimp [lam]
    field_simp
    ring
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => (if a ≤ t.score p ω then 1 else 0)+
        (if a ≤ -t.score p ω then 1 else 0)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      by_cases h : a ≤ |t.score p ω|
      · rcases le_abs.mp h with h₁ | h₂
        · simp only [ite_eq_left h,ite_eq_left h₁]; split_ifs <;> norm_num
        · simp only [ite_eq_left h,ite_eq_left h₂]; split_ifs <;> norm_num
      · simp only [ite_eq_right h]; split_ifs <;> norm_num
    _ = bernoulliPolynomial Q (fun ω => if a ≤ t.score p ω then 1 else 0) p+
        bernoulliPolynomial Q (fun ω => if a ≤ -t.score p ω then 1 else 0) p :=
      bernoulliPolynomial_add _ _ _ _
    _ ≤ Real.exp (-lam*a+lam^2*(N:ℝ)/8)+Real.exp (-lam*a+lam^2*(N:ℝ)/8) :=
      add_le_add (t.capped_score_chernoff ht p lam a hlam N hN)
        (t.capped_neg_score_chernoff ht p lam a hlam N hN)
    _ = _ := by rw [he]; ring

end EdgeQueryTree
end CappedQueryConcentration
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section QueryScoreSets
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

theorem readSet_query (e : E) (t₀ t₁ : EdgeQueryTree E) {Q : Finset E}
    (ht : (query e t₀ t₁).Valid Q) (ω : Finset E) :
    (query e t₀ t₁).readSet Q ω = insert e
      (if e ∈ ω then t₁.readSet (Q.erase e) ω else t₀.readSet (Q.erase e) ω) := by
  ext i
  by_cases hie : i = e
  · subst i
    simp only [mem_readSet,reads,true_or,and_true,Finset.mem_insert_self,iff_true]
    exact ht.1
  · by_cases heω : e ∈ ω <;> simp [mem_readSet,reads,hie,heω]

theorem score_query (e : E) (t₀ t₁ : EdgeQueryTree E) (ω : Finset E) (p : ℝ) :
    (query e t₀ t₁).score p ω =
      (if e ∈ ω then t₁.score p ω else t₀.score p ω)+(if e ∈ ω then 1 else 0)-p := by
  by_cases h : e ∈ ω
  · simp only [score,leaf,ite_eq_left h,ProbeTree.score]; ring
  · simp only [score,leaf,ite_eq_right h,ProbeTree.score]; ring

theorem queryCount_query (e : E) (t₀ t₁ : EdgeQueryTree E) (ω : Finset E) :
    (query e t₀ t₁).queryCount ω =
      (if e ∈ ω then t₁.queryCount ω else t₀.queryCount ω)+1 := by
  by_cases h : e ∈ ω <;> simp [queryCount,leaf,h,ProbeTree.queries]


theorem score_eq_sum (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (ω : Finset E) (p : ℝ) :
    t.score p ω = ∑ e ∈ t.readSet Q ω, ((if e ∈ ω then 1 else 0)-p) := by
  induction t generalizing Q with
  | done b =>
    have hs : (done b : EdgeQueryTree E).readSet Q ω = ∅ := by
      ext e
      simp only [mem_readSet,reads,and_false,Finset.notMem_empty]
    rw [hs,Finset.sum_empty]
    rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    rw [score_query,readSet_query _ _ _ ht]
    have h₀ : e ∉ t₀.readSet (Q.erase e) ω := by simp [readSet]
    have h₁ : e ∉ t₁.readSet (Q.erase e) ω := by simp [readSet]
    by_cases heω : e ∈ ω
    · simp only [ite_eq_left heω,Finset.sum_insert h₁,ih₁ ht.2.2]; ring
    · simp only [ite_eq_right heω,Finset.sum_insert h₀,ih₀ ht.2.1]; ring

end EdgeQueryTree
end QueryScoreSets
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceExploration
attribute [local instance] Classical.propDecidable Classical.decEq



theorem incidencePick_spec (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : IncidencePending G Q R) :
    (incidencePick G Q R h).1 ∈ Q ∧ (incidencePick G Q R h).2.1 ∈ R ∧
      G (incidencePick G Q R h).1 = s((incidencePick G Q R h).2.1,(incidencePick G Q R h).2.2) :=
  Classical.choose_spec h

theorem incidenceSearch_valid (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V) :
    (incidenceSearch G n Q R).Valid Q := by
  induction n generalizing Q R with
  | zero => trivial
  | succ n ih =>
    simp only [incidenceSearch]
    split_ifs with hc
    · exact ⟨(incidencePick_spec G Q R hc).1,ih _ _,ih _ _⟩
    · trivial

theorem incidenceSearch_cap (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V)
    (ω : Finset E) : (incidenceSearch G n Q R).queryCount ω ≤ n := by
  induction n generalizing Q R with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [incidenceSearch]
    split_ifs
    · rw [EdgeQueryTree.queryCount_query]
      split <;> exact Nat.add_le_add_right (ih _ _) 1
    · exact Nat.zero_le _



theorem incidentBonds_erase (G : BondGraph V E) (Q : Finset E) (C : Finset V) (e : E) :
    incidentBonds G (Q.erase e) C = (incidentBonds G Q C).erase e := by
  ext f
  simp only [mem_incidentBonds,Finset.mem_erase]
  tauto

theorem incidencePending_of_mem (G : BondGraph V E) {Q : Finset E} {R : Finset V}
    {e : E} (h : e ∈ incidentBonds G Q R) : IncidencePending G Q R := by
  obtain ⟨he,a,ha,hae⟩ := (mem_incidentBonds G Q R e).mp h
  obtain ⟨b,hab⟩ := Sym2.mem_iff_exists.mp hae
  exact ⟨(e,a,b),he,ha,hab⟩

end IncidenceExploration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceInvariantSteps
attribute [local instance] Classical.propDecidable Classical.decEq

namespace IncidenceInvariant

theorem closed_step {G : BondGraph V E} {Q ω : Finset E} {R C : Finset V}
    (h : IncidenceInvariant G Q ω R C) (e : E) (he : e ∉ ω) :
    IncidenceInvariant G (Q.erase e) ω R C := by
  refine ⟨h.discovered,h.closed,?_⟩
  have heq : ω ∩ Q.erase e = ω ∩ Q := by ext f; simp only [Finset.mem_inter,Finset.mem_erase]; grind
  simpa only [heq] using h.reachable

theorem open_step {G : BondGraph V E} {Q ω : Finset E} {R C : Finset V}
    (h : IncidenceInvariant G Q ω R C) {e : E} (heQ : e ∈ Q) (heω : e ∈ ω)
    {a b : V} (ha : a ∈ R) (hab : G e = s(a,b)) :
    IncidenceInvariant G (Q.erase e) ω (insert b R) C := by
  have hb : b ∈ C := h.closed a (h.discovered ha) e heω b hab
  refine ⟨Finset.insert_subset hb h.discovered,h.closed,?_⟩
  have heq : ((ω ∩ Q : Finset E):Set E) = insert e ((ω ∩ Q.erase e : Finset E):Set E) := by
    ext f
    simp only [Finset.mem_coe,Finset.mem_inter,Finset.mem_erase,Set.mem_insert_iff]
    grind
  intro y hy
  obtain ⟨r,hr,hry⟩ := h.reachable y hy
  rw [heq] at hry
  rcases (conn_insert_iff G _ e a b r y hab).mp hry with h₀ | h₁ | h₁
  · exact ⟨r,Finset.mem_insert_of_mem hr,h₀⟩
  · exact ⟨b,Finset.mem_insert_self _ _,h₁.2⟩
  · exact ⟨a,Finset.mem_insert_of_mem ha,h₁.2⟩

theorem no_pending {G : BondGraph V E} {Q ω : Finset E} {R C : Finset V}
    (h : IncidenceInvariant G Q ω R C) (hp : ¬ IncidencePending G Q R) :
    incidentBonds G Q C = ∅ := by
  have hCR : C ⊆ R := by
    intro y hy
    obtain ⟨r,hr,hry⟩ := h.reachable y hy
    clear hy
    induction hry with
    | refl => exact hr
    | @tail a b _ hab ih =>
      obtain ⟨e,he,heab⟩ := hab
      exact (hp ⟨(e,a,b),(Finset.mem_inter.mp he).2,ih,heab⟩).elim
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  apply hp
  apply incidencePending_of_mem G (e := e)
  obtain ⟨heQ,a,ha,hae⟩ := (mem_incidentBonds G Q C e).mp he
  exact (mem_incidentBonds G Q R e).mpr ⟨heQ,a,hCR ha,hae⟩

end IncidenceInvariant
end IncidenceInvariantSteps
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceCompletion
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem incidenceSearch_readSet (G : BondGraph V E) (n : ℕ) (Q ω : Finset E) (R C : Finset V)
    (hinv : IncidenceInvariant G Q ω R C) (hn : (incidentBonds G Q C).card ≤ n) :
    (incidenceSearch G n Q R).readSet Q ω = incidentBonds G Q C := by
  induction n generalizing Q R with
  | zero =>
    have he : incidentBonds G Q C = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    simp [incidenceSearch,EdgeQueryTree.readSet,EdgeQueryTree.reads,he]
  | succ n ih =>
    simp only [incidenceSearch]
    split_ifs with hc
    · obtain ⟨he,ha,hab⟩ := incidencePick_spec G Q R hc
      have heC : (incidencePick G Q R hc).1 ∈ incidentBonds G Q C :=
        (mem_incidentBonds G Q C _).mpr ⟨he,_,hinv.discovered ha,by rw [hab]; simp⟩
      have hn' : (incidentBonds G (Q.erase (incidencePick G Q R hc).1) C).card ≤ n := by
        rw [incidentBonds_erase,Finset.card_erase_of_mem heC]
        have hh := Finset.card_pos.mpr ⟨_,heC⟩
        omega
      rw [EdgeQueryTree.readSet_query _ _ _ ⟨he,incidenceSearch_valid ..,incidenceSearch_valid ..⟩]
      by_cases heω : (incidencePick G Q R hc).1 ∈ ω
      · rw [ite_eq_left heω,ih _ _ (hinv.open_step he heω ha hab) hn',incidentBonds_erase,
          Finset.insert_erase heC]
      · rw [ite_eq_right heω,ih _ _ (hinv.closed_step _ heω) hn',incidentBonds_erase,
          Finset.insert_erase heC]
    · rw [hinv.no_pending hc]
      ext e
      simp only [EdgeQueryTree.mem_readSet,EdgeQueryTree.reads,
        Finset.notMem_empty,and_false]

theorem incidenceInvariant_root (G : BondGraph V E) (Q ω : Finset E) (hω : ω ⊆ Q) (x : V) :
    IncidenceInvariant G Q ω {x} (finiteRootComponent G ω x) := by
  have hmem (y : V) : y ∈ finiteRootComponent G ω x ↔ Conn G (ω:Set E) x y := by
    change y ∈ ((finiteRootComponent G ω x:Set V)) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro y hy
    rw [Finset.mem_singleton] at hy
    subst y
    exact (hmem x).mpr (conn_refl G _ _)
  · intro a ha e he b hab
    exact (hmem b).mpr ((hmem a).mp ha |>.tail ⟨e,he,hab⟩)
  · intro y hy
    refine ⟨x,Finset.mem_singleton_self _,?_⟩
    rw [Finset.inter_eq_left.mpr hω]
    exact (hmem y).mp hy

 

theorem incidenceSearch_completed_score (G : BondGraph V E) (n : ℕ) (Q ω : Finset E)
    (hω : ω ⊆ Q) (x : V) (p : ℝ)
    (hn : (incidentBonds G Q (finiteRootComponent G ω x)).card ≤ n) :
    (incidenceSearch G n Q {x}).score p ω =
      ∑ e ∈ incidentBonds G Q (finiteRootComponent G ω x), ((if e ∈ ω then 1 else 0)-p) := by
  rw [EdgeQueryTree.score_eq_sum _ (incidenceSearch_valid ..),
    incidenceSearch_readSet G n Q ω {x} _ (incidenceInvariant_root G Q ω hω x) hn]

theorem incidenceSearch_score_tail (G : BondGraph V E) (n : ℕ) (hn : 0 < n)
    (Q : Finset E) (R : Finset V) (p : unitInterval) (a : ℝ) (ha : 0 ≤ a) :
    bernoulliPolynomial Q (fun ω => if a ≤ |(incidenceSearch G n Q R).score p ω| then 1 else 0) p ≤
      2*Real.exp (-2*a^2/(n:ℝ)) :=
  EdgeQueryTree.capped_score_tail _ (incidenceSearch_valid ..) p a ha n hn
    (fun ω _ => incidenceSearch_cap G n Q R ω)

end IncidenceCompletion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExteriorExplorationLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_exterior_expectation_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (f : Finset V → Finset E → ℝ) (K : ℝ)
    (hf : ∀ W : Finset V, bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p ≤ K) :
    bernoulliPolynomial Q (fun ω => f (finiteRootComponent G ω x)
      (exteriorBonds G ω (finiteRootComponent G ω x:Set V))) p ≤ K := by
  let F := insert x (searchVertices G Q)
  have hpoint (ω : Finset E) (hω : ω ⊆ Q) :
      f (finiteRootComponent G ω x) (exteriorBonds G ω (finiteRootComponent G ω x:Set V)) =
      ∑ W ∈ F.powerset, (if cluster G ω x = (W:Set V) then (1:ℝ) else 0)*
        f W (exteriorBonds G ω (W:Set V)) := by
    rw [←sum_component_partition G Q F x ω hω (by rfl)
      (fun W => f W (exteriorBonds G ω (W:Set V)))]
    apply Finset.sum_congr rfl
    intro W _
    split_ifs <;> simp
  rw [bernoulliPolynomial_congr Q hpoint,bernoulliPolynomial_sum]
  calc
    _ = ∑ W ∈ F.powerset,
        bernoulliPolynomial Q (fun ω => if cluster G ω x = (W:Set V) then (1:ℝ) else 0) p*
        bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p := by
      apply Finset.sum_congr rfl
      intro W _
      rw [cluster_cell_exterior_factor,←cluster_cell_incident_probability G Q x (W:Set V) p]
    _ ≤ ∑ W ∈ F.powerset,
        bernoulliPolynomial Q (fun ω => if cluster G ω x = (W:Set V) then (1:ℝ) else 0) p*K := by
      apply Finset.sum_le_sum
      intro W _
      apply mul_le_mul_of_nonneg_left (hf W)
      exact bernoulliPolynomial_nonneg _ _ p p.2 (fun _ _ => by split_ifs <;> norm_num)
    _ = K := by
      rw [←Finset.sum_mul,←bernoulliPolynomial_sum]
      have hh : bernoulliPolynomial Q (fun ω => ∑ W ∈ F.powerset,
          if cluster G ω x = (W:Set V) then (1:ℝ) else 0) p = 1 := by
        trans bernoulliPolynomial Q (fun _ => (1:ℝ)) p
        · apply bernoulliPolynomial_congr
          intro ω hω
          exact sum_component_partition G Q F x ω hω (by rfl) (fun _ => 1)
        · exact bernoulliPolynomial_const Q 1 p
      rw [hh,one_mul]

theorem exteriorSearchScore_tail (G : BondGraph V E) (n : ℕ) (hn : 0 < n)
    (Q : Finset E) (x v : V) (p : unitInterval) (a : ℝ) (ha : 0 < a) :
    bernoulliPolynomial Q (fun ω => if a ≤ |exteriorSearchScore G n Q x v p ω| then 1 else 0) p ≤
      2*Real.exp (-2*a^2/(n:ℝ)) := by
  apply cluster_exterior_expectation_bound G Q x p
    (fun W η => if a ≤ |if v ∈ W then 0 else
      (incidenceSearch G n (exteriorBonds G Q (W:Set V)) {v}).score p η| then 1 else 0)
  intro W
  by_cases hv : v ∈ W
  · simp only [ite_eq_left hv,abs_zero,ite_eq_right (not_le.mpr ha),bernoulliPolynomial_zero]
    positivity
  · simp only [ite_eq_right hv]
    exact incidenceSearch_score_tail G n hn _ _ p a ha.le

end ExteriorExplorationLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClosedClusterContacts
attribute [local instance] Classical.propDecidable Classical.decEq



theorem incident_exterior_subset (G : BondGraph V E) (Q : Finset E) (A B : Finset V) :
    incidentBonds G (exteriorBonds G Q (A:Set V)) B ⊆ incidentBonds G Q B := by
  intro e he
  obtain ⟨he,b,hb,hbe⟩ := (mem_incidentBonds G _ B e).mp he
  exact (mem_incidentBonds G Q B e).mpr ⟨(Finset.mem_filter.mp he).1,b,hb,hbe⟩

 

theorem incident_exterior_difference (G : BondGraph V E) (Q : Finset E) (A B : Finset V)
    (hAB : Disjoint A B) :
    incidentBonds G Q B \ incidentBonds G (exteriorBonds G Q (A:Set V)) B =
      contactBonds G Q A B := by
  ext e
  simp only [Finset.mem_sdiff,mem_incidentBonds,contactBonds,Finset.mem_filter]
  constructor
  · rintro ⟨⟨he,b,hb,hbe⟩,hn⟩
    obtain ⟨a,hea⟩ := Sym2.mem_iff_exists.mp hbe
    have hbA : b ∉ A := fun hh => Finset.disjoint_left.mp hAB hh hb
    have ha : a ∈ A := by
      by_contra ha
      apply hn
      refine ⟨Finset.mem_filter.mpr ⟨he,?_⟩,b,hb,hbe⟩
      exact (mem_internalEdges_of_ends G (A:Set V)ᶜ e b a hea).mpr ⟨hbA,ha⟩
    exact ⟨he,a,ha,b,hb,hea.trans (Sym2.eq_swap ..)⟩
  · rintro ⟨he,a,ha,b,hb,hab⟩
    refine ⟨⟨he,b,hb,by rw [hab]; simp⟩,?_⟩
    rintro ⟨he',_⟩
    exact (Finset.mem_filter.mp he').2 a (by rw [hab]; simp) ha

theorem finiteRootComponent_disjoint (G : BondGraph V E) (ω : Finset E) (x v : V)
    (h : ¬Conn G (ω:Set E) x v) :
    Disjoint (finiteRootComponent G ω x) (finiteRootComponent G ω v) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have h₁ : Conn G (ω:Set E) x z := by
    change z ∈ (finiteRootComponent G ω x:Set V) at hz
    rwa [coe_finiteRootComponent] at hz
  have h₂ : Conn G (ω:Set E) v z := by
    change z ∈ (finiteRootComponent G ω v:Set V) at hz'
    rwa [coe_finiteRootComponent] at hz'
  exact h (h₁.trans (conn_symm G _ h₂))

theorem distinct_contact_closed (G : BondGraph V E) (Q ω : Finset E) (x v : V)
    (h : ¬Conn G (ω:Set E) x v) {e : E}
    (he : e ∈ contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)) : e ∉ ω := by
  obtain ⟨_,a,ha,b,hb,hab⟩ := Finset.mem_filter.mp he
  have h₁ : Conn G (ω:Set E) x a := by
    change a ∈ (finiteRootComponent G ω x:Set V) at ha
    rwa [coe_finiteRootComponent] at ha
  have h₂ : Conn G (ω:Set E) v b := by
    change b ∈ (finiteRootComponent G ω v:Set V) at hb
    rwa [coe_finiteRootComponent] at hb
  intro heω
  exact h ((h₁.tail ⟨e,heω,hab⟩).trans (conn_symm G _ h₂))

theorem finiteRootComponent_exterior (G : BondGraph V E) (ω : Finset E) (x v : V)
    (h : ¬Conn G (ω:Set E) x v) :
    finiteRootComponent G (exteriorBonds G ω (finiteRootComponent G ω x:Set V)) v =
      finiteRootComponent G ω v := by
  apply Finset.coe_injective
  simp only [coe_finiteRootComponent,coe_exteriorBonds]
  ext z
  exact conn_exterior_of_cluster_eq G ω x v z (cluster G ω x) rfl h

end ClosedClusterContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExplorationScoreDifference
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem incidence_exterior_score_difference (G : BondGraph V E) (n : ℕ) (Q ω : Finset E)
    (hω : ω ⊆ Q) (x v : V) (p : ℝ) (h : ¬Conn G (ω:Set E) x v)
    (hn : (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ n) :
    (incidenceSearch G n Q {v}).score p ω - exteriorSearchScore G n Q x v p ω =
      -p*(contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card := by
  let A := finiteRootComponent G ω x
  let B := finiteRootComponent G ω v
  let R := exteriorBonds G Q (A:Set V)
  let η := exteriorBonds G ω (A:Set V)
  have hv : v ∉ A := by
    intro hv
    apply h
    change v ∈ (A:Set V) at hv
    simpa only [A,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hv
  have hη : η ⊆ R := by
    intro e he
    obtain ⟨he,heA⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hω he,heA⟩
  have hB : finiteRootComponent G η v = B := finiteRootComponent_exterior G ω x v h
  have hsub : incidentBonds G R B ⊆ incidentBonds G Q B := incident_exterior_subset G Q A B
  have hn' : (incidentBonds G R (finiteRootComponent G η v)).card ≤ n := by
    rw [hB]
    exact (Finset.card_le_card hsub).trans hn
  have hs₁ := incidenceSearch_completed_score G n Q ω hω v p hn
  have hs₂ := incidenceSearch_completed_score G n R η hη v p hn'
  rw [hB] at hs₂
  have hb (e : E) (he : e ∈ incidentBonds G R B) : (e ∈ η ↔ e ∈ ω) := by
    have heR := ((mem_incidentBonds G R B e).mp he).1
    change e ∈ exteriorBonds G ω (A:Set V) ↔ e ∈ ω
    simp only [exteriorBonds,Finset.mem_filter]
    exact and_iff_left (Finset.mem_filter.mp heR).2
  have hs₂' : (incidenceSearch G n R {v}).score p η =
      ∑ e ∈ incidentBonds G R B, ((if e ∈ ω then 1 else 0)-p) := by
    rw [hs₂]
    exact Finset.sum_congr rfl (fun e he => by simp only [hb e he])
  change (incidenceSearch G n Q {v}).score p ω -
    (if v ∈ A then 0 else (incidenceSearch G n R {v}).score p η) = _
  rw [ite_eq_right hv,hs₁,hs₂',←Finset.sum_sdiff hsub,add_sub_cancel_right]
  change (∑ e ∈ incidentBonds G Q B \ incidentBonds G (exteriorBonds G Q (A:Set V)) B,
    ((if e ∈ ω then (1:ℝ) else 0)-p)) = _
  rw [incident_exterior_difference G Q A B (finiteRootComponent_disjoint G ω x v h)]
  have hc (e : E) (he : e ∈ contactBonds G Q A B) : e ∉ ω := distinct_contact_closed G Q ω x v h he
  rw [show (∑ e ∈ contactBonds G Q A B, ((if e ∈ ω then (1:ℝ) else 0)-p)) =
      ∑ _e ∈ contactBonds G Q A B, -p from Finset.sum_congr rfl (fun e he => by rw [ite_eq_right (hc e he)]; ring)]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end ExplorationScoreDifference
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ContactConcentration
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactBonds_comm (G : BondGraph V E) (Q : Finset E) (A B : Finset V) :
    contactBonds G Q A B = contactBonds G Q B A := by
  ext e
  simp only [contactBonds,Finset.mem_filter]
  constructor <;> rintro ⟨he,a,ha,b,hb,hab⟩
  · exact ⟨he,b,hb,a,ha,hab.trans (Sym2.eq_swap ..)⟩
  · exact ⟨he,b,hb,a,ha,hab.trans (Sym2.eq_swap ..)⟩

 

theorem ordered_cluster_contact_tail (G : BondGraph V E) (Q : Finset E)
    (x v : V) (p : unitInterval) (N : ℕ) (hN : 0 < N) (a : ℝ) (ha : 0 < a) :
    bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ N ∧
      2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
        (finiteRootComponent G ω v)).card then 1 else 0) p ≤
      4*Real.exp (-2*a^2/(N:ℝ)) := by
  calc
    _ ≤ bernoulliPolynomial Q (fun ω =>
        (if a ≤ |(incidenceSearch G N Q {v}).score p ω| then 1 else 0)+
        (if a ≤ |exteriorSearchScore G N Q x v p ω| then 1 else 0)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω hω
      by_cases h : ¬Conn G (ω:Set E) x v ∧
          (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ N ∧
          2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
            (finiteRootComponent G ω v)).card
      · have hd := incidence_exterior_score_difference G N Q ω hω x v p h.1 h.2.1
        have huo : a ≤ |(incidenceSearch G N Q {v}).score p ω| ∨
            a ≤ |exteriorSearchScore G N Q x v p ω| := by
          by_contra hh
          push Not at hh
          have h₁ := (abs_lt.mp hh.1).1
          have h₂ := (abs_lt.mp hh.2).2
          nlinarith [h.2.2]
        simp only [ite_eq_left h]
        rcases huo with huo | huo <;> simp only [ite_eq_left huo] <;> split_ifs <;> norm_num
      · simp only [ite_eq_right h]; split_ifs <;> norm_num
    _ = bernoulliPolynomial Q (fun ω =>
        if a ≤ |(incidenceSearch G N Q {v}).score p ω| then 1 else 0) p+
        bernoulliPolynomial Q (fun ω =>
        if a ≤ |exteriorSearchScore G N Q x v p ω| then 1 else 0) p :=
      bernoulliPolynomial_add _ _ _ _
    _ ≤ 2*Real.exp (-2*a^2/(N:ℝ))+2*Real.exp (-2*a^2/(N:ℝ)) :=
      add_le_add (incidenceSearch_score_tail G N hN Q {v} p a ha.le)
        (exteriorSearchScore_tail G N hN Q x v p a ha)
    _ = _ := by ring

end ContactConcentration
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_LargeContacts
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
section UnorderedContactConcentration
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_contact_tail (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d)
    (x v : V) (p : unitInterval) (m : ℕ) (hdm : 0 < d*m) (a : ℝ) (ha : 0 < a) :
    bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m ∧
      2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
        (finiteRootComponent G ω v)).card then 1 else 0) p ≤
      8*Real.exp (-2*a^2/(d*m:ℕ)) := by
  let f (x v : V) (ω : Finset E) : ℝ :=
    if ¬Conn G (ω:Set E) x v ∧ (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ d*m ∧
      2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
        (finiteRootComponent G ω v)).card then 1 else 0
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => f x v ω+f v x ω) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      by_cases h : ¬Conn G (ω:Set E) x v ∧
          min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m ∧
          2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
            (finiteRootComponent G ω v)).card
      · simp only [ite_eq_left h]
        rcases le_total (finiteRootComponent G ω v).card (finiteRootComponent G ω x).card with hc | hc
        · have hsmall : (finiteRootComponent G ω v).card ≤ m := by simpa only [min_eq_right hc] using h.2.1
          have hh : ¬Conn G (ω:Set E) x v ∧ (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ d*m ∧
              2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card :=
            ⟨h.1,(incidentBonds_card_le G Q _ d hd).trans (Nat.mul_le_mul_left d hsmall),h.2.2⟩
          simp only [f,ite_eq_left hh]; split_ifs <;> norm_num
        · have hsmall : (finiteRootComponent G ω x).card ≤ m := by simpa only [min_eq_left hc] using h.2.1
          have hh : ¬Conn G (ω:Set E) v x ∧ (incidentBonds G Q (finiteRootComponent G ω x)).card ≤ d*m ∧
              2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω v) (finiteRootComponent G ω x)).card := by
            refine ⟨fun hc' => h.1 (conn_symm G _ hc'),
              (incidentBonds_card_le G Q _ d hd).trans (Nat.mul_le_mul_left d hsmall),?_⟩
            rw [contactBonds_comm G Q (finiteRootComponent G ω v)]
            exact h.2.2
          simp only [f,ite_eq_left hh]; split_ifs <;> norm_num
      · simp only [ite_eq_right h,f]; split_ifs <;> norm_num
    _ = bernoulliPolynomial Q (f x v) p+bernoulliPolynomial Q (f v x) p :=
      bernoulliPolynomial_add ..
    _ ≤ 4*Real.exp (-2*a^2/(d*m:ℕ))+4*Real.exp (-2*a^2/(d*m:ℕ)) :=
      add_le_add (ordered_cluster_contact_tail G Q x v p (d*m) hdm a ha)
        (ordered_cluster_contact_tail G Q v x p (d*m) hdm a ha)
    _ = _ := by ring

end UnorderedContactConcentration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TwoLargeFiniteClusters
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_exterior_weighted_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (F : Finset V → ℝ) (hF : ∀ W, 0 ≤ F W)
    (f : Finset V → Finset E → ℝ) (K : ℝ)
    (hf : ∀ W : Finset V, bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p ≤ K) :
    bernoulliPolynomial Q (fun ω => F (finiteRootComponent G ω x)*f (finiteRootComponent G ω x)
      (exteriorBonds G ω (finiteRootComponent G ω x:Set V))) p ≤
      K*bernoulliPolynomial Q (fun ω => F (finiteRootComponent G ω x)) p := by
  have hh := cluster_exterior_expectation_bound G Q x p
    (fun W η => F W*f W η-K*F W) 0 (fun W => by
      rw [bernoulliPolynomial_sub,bernoulliPolynomial_const_mul,bernoulliPolynomial_const]
      exact sub_nonpos.mpr (by simpa only [mul_comm K] using mul_le_mul_of_nonneg_left (hf W) (hF W)))
  rw [bernoulliPolynomial_sub,bernoulliPolynomial_const_mul] at hh
  exact sub_nonpos.mp hh

theorem finiteClusterTail_domain_mono (G : BondGraph V E) {Q R : Finset E} (hRQ : R ⊆ Q)
    (x : V) (n : ℕ) (p : unitInterval) : finiteClusterTail G R x n p ≤ finiteClusterTail G Q x n p := by
  unfold finiteClusterTail
  rw [←bernoulliPolynomial_restrict R Q hRQ]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  exact finiteClusterTailIndicator_mono G x n Finset.inter_subset_left

 

theorem two_large_clusters_tail (G : BondGraph V E) (Q : Finset E)
    (x v : V) (n m : ℕ) (p : unitInterval) :
    bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      n ≤ (finiteRootComponent G ω x).card ∧ m ≤ (finiteRootComponent G ω v).card
        then 1 else 0) p ≤ finiteClusterTail G Q v m p*finiteClusterTail G Q x n p := by
  let F (W : Finset V) : ℝ := if n ≤ W.card then 1 else 0
  let f (W : Finset V) (η : Finset E) : ℝ := if v ∈ W then 0 else finiteClusterTailIndicator G v m η
  have hF : ∀ W, 0 ≤ F W := fun W => by dsimp [F]; split_ifs <;> norm_num
  have hf (W : Finset V) : bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p ≤
      finiteClusterTail G Q v m p := by
    by_cases hv : v ∈ W
    · simp only [f,ite_eq_left hv,bernoulliPolynomial_zero]
      exact finiteClusterTail_nonneg G Q v m p
    · simp only [f,ite_eq_right hv]
      exact finiteClusterTail_domain_mono G (Finset.filter_subset _ _) v m p
  have hp := cluster_exterior_weighted_bound G Q x p F hF f (finiteClusterTail G Q v m p) hf
  have heq : bernoulliPolynomial Q (fun ω => F (finiteRootComponent G ω x)*f (finiteRootComponent G ω x)
      (exteriorBonds G ω (finiteRootComponent G ω x:Set V))) p =
      bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      n ≤ (finiteRootComponent G ω x).card ∧ m ≤ (finiteRootComponent G ω v).card then 1 else 0) p := by
    apply bernoulliPolynomial_congr
    intro ω _
    have hv : v ∈ finiteRootComponent G ω x ↔ Conn G (ω:Set E) x v := by
      change v ∈ (finiteRootComponent G ω x:Set V) ↔ _
      rw [coe_finiteRootComponent]
      rfl
    by_cases hc : Conn G (ω:Set E) x v
    · simp only [F,f,ite_eq_left (hv.mpr hc),mul_zero,not_true_eq_false,hc,false_and,if_false]
    · simp only [F,f,ite_eq_right (fun h => hc (hv.mp h)),finiteClusterTailIndicator,
        finiteRootComponent_exterior G ω x v hc]
      split_ifs <;> norm_num <;> grind
  rw [heq] at hp
  exact hp

end TwoLargeFiniteClusters
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section EndpointClusterTails
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteClusterTail_of_endpoint_moment [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) (α C : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (Q : Finset E) (x : V) (p : unitInterval) (hpq : p ≤ q) (n : ℕ) (hn : 1 ≤ n) :
    finiteClusterTail G Q x n p ≤ 2*C*(n:ℝ)^(-α) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let h : unitInterval := ⟨1/(n:ℝ),⟨by positivity,by apply (div_le_one hn0).mpr; exact_mod_cast hn⟩⟩
  have hh : 0 < (h:ℝ) := by dsimp [h]; positivity
  have hhpow : (h:ℝ)^α = (n:ℝ)^(-α) := by
    dsimp [h]
    rw [one_div,Real.inv_rpow hn0.le,Real.rpow_neg hn0.le]
  have hhn : 1 ≤ (h:ℝ)*n := by dsimp [h]; rw [one_div,inv_mul_cancel₀ hn0.ne']
  have hm := cluster_power_mono_integral G hloc x p q hpq α hα (hfin x) (hI x)
  have hb := markedConnection_le_cluster_power G Q x h p α hα hα1
    (cluster_finite_ae_mono G x p q hpq (hfin x)) hm.1
  have hM : markedConnectionPolynomial G Q x h p ≤ C*(n:ℝ)^(-α) := by
    apply hb.trans
    rw [hhpow]
    simpa only [mul_comm C] using
      mul_le_mul_of_nonneg_left (hm.2.trans (hC x)) (Real.rpow_nonneg (Nat.cast_nonneg n) (-α))
  have hb' := (finiteClusterTail_le_markedConnection G Q x n p h hhn).trans
    (mul_le_mul_of_nonneg_left hM (by norm_num : (0:ℝ) ≤ 2))
  simpa only [mul_assoc] using hb'

end EndpointClusterTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ContactBinFirstMoment
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactBonds_card_le (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d) (A B : Finset V) :
    (contactBonds G Q A B).card ≤ d*min A.card B.card := by
  have hh (A B : Finset V) : (contactBonds G Q A B).card ≤ d*A.card := by
    apply (Finset.card_le_card (t := incidentBonds G Q A) _).trans (incidentBonds_card_le G Q A d hd)
    intro e he
    obtain ⟨he,a,ha,b,_,hab⟩ := Finset.mem_filter.mp he
    exact (mem_incidentBonds G Q A e).mpr ⟨he,a,ha,by rw [hab]; simp⟩
  rcases le_total A.card B.card with h | h
  · rw [min_eq_left h]; exact hh A B
  · rw [min_eq_right h,contactBonds_comm G Q A B]; exact hh B A



theorem clusterContactBin_bound (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d)
    (x v : V) (p : unitInterval) (hp : 0 < (p:ℝ)) (n m : ℕ) (hdm : 0 < d*m)
    (a : ℝ) (ha : 0 < a) :
    bernoulliPolynomial Q (clusterContactBin G Q x v n m) p ≤
      (2*a/(p:ℝ))*(finiteClusterTail G Q v n p*finiteClusterTail G Q x n p)+
      (d*m:ℕ)*(8*Real.exp (-2*a^2/(d*m:ℕ))) := by
  let D (ω : Finset E) : Prop := ¬Conn G (ω:Set E) x v ∧
    n ≤ (finiteRootComponent G ω x).card ∧ n ≤ (finiteRootComponent G ω v).card
  let T (ω : Finset E) : Prop := ¬Conn G (ω:Set E) x v ∧
    min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m ∧
    2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => (2*a/(p:ℝ))*(if D ω then 1 else 0)+
        (d*m:ℕ)*(if T ω then 1 else 0)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      unfold clusterContactBin
      by_cases h : ¬Conn G (ω:Set E) x v ∧
          n ≤ min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ∧
          min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m
      · have hD : D ω := ⟨h.1,(le_min_iff.mp h.2.1).1,(le_min_iff.mp h.2.1).2⟩
        simp only [ite_eq_left h,ite_eq_left hD,mul_one]
        by_cases ht : T ω
        · rw [ite_eq_left ht,mul_one]
          have hk : (contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card ≤ d*m :=
            (contactBonds_card_le G Q d hd _ _).trans (Nat.mul_le_mul_left d h.2.2)
          have hk' : ((contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card:ℝ) ≤ (d*m:ℕ) := by exact_mod_cast hk
          have hapos : 0 ≤ 2*a/(p:ℝ) := by positivity
          linarith
        · rw [ite_eq_right ht,mul_zero,add_zero]
          apply (le_div_iff₀ hp).mpr
          have hn : ¬ 2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card :=
            fun hh => ht ⟨h.1,h.2.2,hh⟩
          simpa only [mul_comm] using (not_le.mp hn).le
      · simp only [ite_eq_right h]
        split_ifs <;> positivity
    _ = (2*a/(p:ℝ))*bernoulliPolynomial Q (fun ω => if D ω then 1 else 0) p+
        (d*m:ℕ)*bernoulliPolynomial Q (fun ω => if T ω then 1 else 0) p := by
      rw [bernoulliPolynomial_add,bernoulliPolynomial_const_mul,bernoulliPolynomial_const_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (two_large_clusters_tail G Q x v n n p) (by positivity))
      (mul_le_mul_of_nonneg_left (cluster_contact_tail G Q d hd x v p m hdm a ha) (Nat.cast_nonneg _))

end ContactBinFirstMoment
end Percolation

 
namespace Percolation
section StretchedContactDecay

theorem exists_stretched_exp_volume_bound (d ε r : ℝ) (hd : 0 < d) (hε : 0 < ε) (hr : r ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z → z*Real.exp (-(z^ε)/d) ≤ C*z^r := by
  let s := (1-r)/ε
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨K,hK,hKb⟩ := exists_exp_neg_le_rpow s hs
  refine ⟨K*d^s,by positivity,?_⟩
  intro z hz
  have he := mul_le_mul_of_nonneg_left (hKb (z^ε/d) (by positivity)) hz.le
  have hex : ε*(-s) = r-1 := by dsimp [s]; field_simp; ring
  have hid : (z^ε/d)^(-s) = z^(r-1)*d^s := by
    rw [Real.div_rpow (Real.rpow_nonneg hz.le ε) hd.le,←Real.rpow_mul hz.le,hex,
      Real.rpow_neg hd.le,div_inv_eq_mul]
  have hzpow : z*z^(r-1) = z^r := by
    conv_lhs => lhs; rw [←Real.rpow_one z]
    rw [←Real.rpow_add hz]
    congr 1
    ring
  calc
    _ ≤ z*(K*(z^ε/d)^(-s)) := by simpa only [neg_div] using he
    _ = (K*d^s)*(z*z^(r-1)) := by rw [hid]; ring
    _ = _ := by rw [hzpow]

theorem contact_tail_exponent (d z ε : ℝ) (hd : 0 < d) (hz : 0 < z) :
    -2*(z^((1:ℝ)/2+ε))^2/(d*(2*z)) = -(z^(2*ε))/d := by
  have hpow : (z^((1:ℝ)/2+ε))^2 = z*z^(2*ε) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ((1:ℝ)/2+ε)*2 = 1+2*ε by ring,Real.rpow_add hz,Real.rpow_one]
  rw [hpow]
  field_simp

end StretchedContactDecay
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformContactBins
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem clusterContactBin_power_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval)
    (α ε C p₀ : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) (hC0 : 0 < C) (hp₀ : 0 < p₀)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (d : ℕ) (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q : Finset E), (∀ z, (Q.filter fun e => z ∈ G e).card ≤ d) →
      ∀ (x v : V) (p : unitInterval), p₀ ≤ (p:ℝ) → p ≤ q → ∀ n : ℕ, 1 ≤ n →
      bernoulliPolynomial Q (clusterContactBin G Q x v n (2*n)) p ≤
        A*(n:ℝ)^((1:ℝ)/2+ε-2*α) := by
  let r : ℝ := (1:ℝ)/2+ε-2*α
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  obtain ⟨K,hK,hKb⟩ := exists_stretched_exp_volume_bound (d:ℝ) (2*ε) r hd' (by positivity) (by dsimp [r]; linarith)
  refine ⟨8*C^2/p₀+16*(d:ℝ)*K,by positivity,?_⟩
  intro Q hdeg x v p hpp hpq n hn
  have hn' : 0 < n := by omega
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn'
  have hp : 0 < (p:ℝ) := hp₀.trans_le hpp
  let a : ℝ := (n:ℝ)^((1:ℝ)/2+ε)
  have ha : 0 < a := Real.rpow_pos_of_pos hnr _
  have hb := clusterContactBin_bound G Q d hdeg x v p hp n (2*n) (by positivity) a ha
  have ht (y : V) := finiteClusterTail_of_endpoint_moment G hloc q α C hα hα1 hfin hI hC Q y p hpq n hn
  have hprod : finiteClusterTail G Q v n p*finiteClusterTail G Q x n p ≤ 4*C^2*(n:ℝ)^(-2*α) := by
    calc
      _ ≤ (2*C*(n:ℝ)^(-α))*(2*C*(n:ℝ)^(-α)) :=
        mul_le_mul (ht v) (ht x) (finiteClusterTail_nonneg G Q x n p) (by positivity)
      _ = _ := by
        rw [show (2*C*(n:ℝ)^(-α))*(2*C*(n:ℝ)^(-α)) = 4*C^2*((n:ℝ)^(-α)*(n:ℝ)^(-α)) by ring,
          ←Real.rpow_add hnr]
        congr 2
        ring
  have hfirst : (2*a/(p:ℝ))*(finiteClusterTail G Q v n p*finiteClusterTail G Q x n p) ≤
      (8*C^2/p₀)*(n:ℝ)^r := by
    calc
      _ ≤ (2*a/p₀)*(4*C^2*(n:ℝ)^(-2*α)) :=
        mul_le_mul (div_le_div_of_nonneg_left (by positivity) hp₀ hpp) hprod
          (mul_nonneg (finiteClusterTail_nonneg G Q v n p) (finiteClusterTail_nonneg G Q x n p)) (by positivity)
      _ = (8*C^2/p₀)*((n:ℝ)^((1:ℝ)/2+ε)*(n:ℝ)^(-2*α)) := by dsimp [a]; ring
      _ = _ := by rw [←Real.rpow_add hnr]; congr 2; dsimp [r]; ring
  have hex : -2*a^2/(d*(2*n):ℕ) = -((n:ℝ)^(2*ε))/(d:ℝ) := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    exact contact_tail_exponent d n ε hd' hnr
  have hsecond : (d*(2*n):ℕ)*(8*Real.exp (-2*a^2/(d*(2*n):ℕ))) ≤
      (16*(d:ℝ)*K)*(n:ℝ)^r := by
    rw [hex]
    calc
      _ = (16*(d:ℝ))*((n:ℝ)*Real.exp (-((n:ℝ)^(2*ε))/(d:ℝ))) := by
        push_cast
        ring
      _ ≤ (16*(d:ℝ))*(K*(n:ℝ)^r) := mul_le_mul_of_nonneg_left (hKb n hnr) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hb
    _ ≤ (8*C^2/p₀)*(n:ℝ)^r+(16*(d:ℝ)*K)*(n:ℝ)^r := add_le_add hfirst hsecond
    _ = _ := by dsimp [r]; ring

end UniformContactBins
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContacts
attribute [local instance] Classical.propDecidable Classical.decEq


theorem contactSet_subset_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (B : Set V) : closedContactSet G (A:Set V) B ⊆ (incidentSupport G hloc A:Set E) := by
  rintro e ⟨a,ha,b,_,hab⟩
  exact (mem_incidentSupport G hloc A e).mpr ⟨a,ha,by rw [hab]; simp⟩

theorem coe_contactBonds_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (A B : Finset V) (hQ : incidentSupport G hloc A ⊆ Q) :
    (contactBonds G Q A B : Set E) = closedContactSet G A B := by
  ext e
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨hQ (contactSet_subset_incident G hloc A B h),h⟩

theorem contactSet_ncard_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d)
    (A B : Set V) (hA : A.Finite) (hB : B.Finite) :
    (closedContactSet G A B).ncard ≤ d*min A.ncard B.ncard := by
  let Q := incidentSupport G hloc (hA.toFinset ∪ hB.toFinset)
  have hdeg (z : V) : (Q.filter fun e => z ∈ G e).card ≤ d := by
    calc
      _ = ((Q.filter fun e => z ∈ G e):Set E).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ {e | z ∈ G e}.ncard := Set.ncard_le_ncard (fun e he => (Finset.mem_filter.mp he).2) (hloc z)
      _ ≤ d := hd z
  have hQ : incidentSupport G hloc hA.toFinset ⊆ Q :=
    incidentSupport_mono G hloc Finset.subset_union_left
  have he := coe_contactBonds_eq G hloc Q hA.toFinset hB.toFinset hQ
  simp only [Set.Finite.coe_toFinset] at he
  rw [←he,Set.ncard_coe_finset]
  simpa only [←Set.ncard_eq_toFinset_card] using contactBonds_card_le G Q d hdeg hA.toFinset hB.toFinset

theorem fullContactBin_nonneg (G : BondGraph V E) (x v : V) (n m : ℕ) (ω : Set E) :
    0 ≤ fullContactBin G x v n m ω := by unfold fullContactBin; split_ifs <;> positivity

theorem fullContactBin_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d) (x v : V) (n m : ℕ) (hn : 0 < n) (ω : Set E) :
    fullContactBin G x v n m ω ≤ (d*m:ℕ) := by
  unfold fullContactBin
  split_ifs with h
  · have hx : (cluster G ω x).Finite := Set.finite_of_ncard_ne_zero (by omega)
    have hv : (cluster G ω v).Finite := Set.finite_of_ncard_ne_zero (by omega)
    exact_mod_cast (contactSet_ncard_le G hloc d hd _ _ hx hv).trans (Nat.mul_le_mul_left d h.2.2)
  · positivity

end InfiniteContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ContactMeasurability
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_clusterContactCount [Countable V] [Countable E]
    (G : BondGraph V E) (x v : V) : Measurable (fun ω : Set E => clusterContactCount G ω x v) := by
  apply measurable_ncard.comp
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  apply measurableSet_setOfPred.mp
  change MeasurableSet {ω : Set E | ∃ a, Conn G ω x a ∧ ∃ b, Conn G ω v b ∧ G e = s(a,b)}
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  have he : {ω : Set E | Conn G ω x a ∧ ∃ b, Conn G ω v b ∧ G e = s(a,b)} =
      {ω | Conn G ω x a} ∩ ⋃ b, {ω | Conn G ω v b ∧ G e = s(a,b)} := by ext ω; simp
  rw [he]
  apply (measurableSet_conn G x a).inter
  apply MeasurableSet.iUnion
  intro b
  by_cases h : G e = s(a,b)
  · simpa only [h,and_true] using measurableSet_conn G v b
  · simp only [h,and_false,Set.ofPred_false]; exact MeasurableSet.empty

theorem measurable_fullContactBin [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x v : V) (n m : ℕ) :
    Measurable (fullContactBin G x v n m) := by
  have hs : Measurable (fun ω : Set E => min (cluster G ω x).ncard (cluster G ω v).ncard) :=
    (measurable_cluster_ncard G hloc x).min (measurable_cluster_ncard G hloc v)
  exact ((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (measurable_clusterContactCount G x v)).ite
    (((measurableSet_conn G x v).compl).inter ((measurableSet_le measurable_const hs).inter
      (measurableSet_le hs measurable_const))) measurable_const

theorem coe_domainBits (Q : Finset E) (ω : Set E) :
    (domainBits Q ω:Set E) = ω ∩ (Q:Set E) := by ext e; simp only [mem_domainBits,Set.mem_inter_iff,Finset.mem_coe,and_comm]

theorem domainBits_local (Q : Finset E) (ω : Set E) :
    domainBits Q (ω ∩ (Q:Set E)) = domainBits Q ω := by
  ext e
  simp only [mem_domainBits,Set.mem_inter_iff,Finset.mem_coe]
  tauto

theorem domainBits_of_subset (Q ω : Finset E) (hω : ω ⊆ Q) : domainBits Q (ω:Set E) = ω := by
  ext e
  simp only [mem_domainBits,Finset.mem_coe]
  exact ⟨fun h => h.2,fun h => ⟨hω h,h⟩⟩

theorem integral_domainBits (Q : Finset E) (p : unitInterval) (f : Finset E → ℝ) :
    (∫ ω, f (domainBits Q ω) ∂law p) = bernoulliPolynomial Q f p := by
  rw [integral_eq_bernoulliPolynomial Q p _ (fun ω => by rw [domainBits_local])]
  apply bernoulliPolynomial_congr
  intro ω hω
  rw [domainBits_of_subset Q ω hω]

end ContactMeasurability
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContactLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem fullContactBin_eq_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x v : V) (hx : (cluster G ω x).Finite) (hv : (cluster G ω v).Finite)
    (Q : Finset E) (hQx : incidentSupport G hloc hx.toFinset ⊆ Q)
    (hQv : incidentSupport G hloc hv.toFinset ⊆ Q) (n m : ℕ) :
    clusterContactBin G Q x v n m (domainBits Q ω) = fullContactBin G x v n m ω := by
  have hcluster (y : V) (hy : (cluster G ω y).Finite) (hQ : incidentSupport G hloc hy.toFinset ⊆ Q) :
      cluster G (domainBits Q ω:Set E) y = cluster G ω y := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hy.toFinset Q hQ ω y).mpr
      (Set.Finite.coe_toFinset hy).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  have hcx := hcluster x hx hQx
  have hcv := hcluster v hv hQv
  have hFx : finiteRootComponent G (domainBits Q ω) x = hx.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcx,Set.Finite.coe_toFinset]
  have hFv : finiteRootComponent G (domainBits Q ω) v = hv.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcv,Set.Finite.coe_toFinset]
  have hconn : Conn G (domainBits Q ω:Set E) x v ↔ Conn G ω x v := by
    change v ∈ cluster G (domainBits Q ω:Set E) x ↔ v ∈ cluster G ω x
    rw [hcx]
  have hc : (contactBonds G Q hx.toFinset hv.toFinset).card = clusterContactCount G ω x v := by
    rw [←Set.ncard_coe_finset,coe_contactBonds_eq G hloc Q _ _ hQx]
    simp only [Set.Finite.coe_toFinset,clusterContactCount]
  simp only [clusterContactBin,fullContactBin,hconn,hFx,hFv,←Set.ncard_eq_toFinset_card,hc]

theorem clusterContactBin_norm_le (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d)
    (x v : V) (n m : ℕ) (ω : Finset E) : ‖clusterContactBin G Q x v n m ω‖ ≤ (d*m:ℕ) := by
  unfold clusterContactBin
  split_ifs with h
  · rw [Real.norm_natCast]
    exact_mod_cast (contactBonds_card_le G Q d hd _ _).trans (Nat.mul_le_mul_left d h.2.2)
  · simp only [norm_zero]; positivity

theorem fullContactBin_integral_le_of_finite [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d) (x v : V) (p : unitInterval)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hv : ∀ᵐ ω ∂law p, (cluster G ω v).Finite) (n m : ℕ) (B : ℝ)
    (hB : ∀ Q : Finset E, bernoulliPolynomial Q (clusterContactBin G Q x v n m) p ≤ B) :
    (∫ ω, fullContactBin G x v n m ω ∂law p) ≤ B := by
  let : Encodable E := Encodable.ofCountable E
  let Q := vertexExhaustion (V := E)
  let f := fun j ω => clusterContactBin G (Q j) x v n m (domainBits (Q j) ω)
  have hfl (j : ℕ) (ω : Set E) : f j ω = f j (ω ∩ (Q j:Set E)) := by
    dsimp [f]; rw [domainBits_local]
  have hfi (j : ℕ) : Integrable (f j) (law p) := integrable_finite_local (Q j) p (f j) (hfl j)
  have hdeg (j : ℕ) (z : V) : ((Q j).filter fun e => z ∈ G e).card ≤ d := by
    calc
      _ = (((Q j).filter fun e => z ∈ G e):Set E).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ {e | z ∈ G e}.ncard := Set.ncard_le_ncard (fun e he => (Finset.mem_filter.mp he).2) (hloc z)
      _ ≤ d := hd z
  have ht : ∀ᵐ ω ∂law p, Tendsto (fun j => f j ω) atTop (nhds (fullContactBin G x v n m ω)) := by
    filter_upwards [hx,hv] with ω hωx hωv
    obtain ⟨jx,hjx⟩ := subset_vertexExhaustion (incidentSupport G hloc hωx.toFinset)
    obtain ⟨jv,hjv⟩ := subset_vertexExhaustion (incidentSupport G hloc hωv.toFinset)
    have he : (fun j => f j ω) =ᶠ[atTop] (fun _ => fullContactBin G x v n m ω) := by
      filter_upwards [eventually_ge_atTop (max jx jv)] with j hj
      exact fullContactBin_eq_finite G hloc ω x v hωx hωv (Q j)
        (hjx.trans (vertexExhaustion_mono (le_max_left jx jv |>.trans hj)))
        (hjv.trans (vertexExhaustion_mono (le_max_right jx jv |>.trans hj))) n m
    exact tendsto_const_nhds.congr' he.symm
  have hdom := tendsto_integral_of_dominated_convergence (fun _ : Set E => (d*m:ℕ))
    (fun j => (hfi j).aestronglyMeasurable) (integrable_const _)
    (fun j => Eventually.of_forall (fun ω => clusterContactBin_norm_le G (Q j) d (hdeg j) x v n m _)) ht
  apply le_of_tendsto hdom
  exact Eventually.of_forall (fun j => by rw [show (∫ ω, f j ω ∂law p) =
    bernoulliPolynomial (Q j) (clusterContactBin G (Q j) x v n m) p from by dsimp [f]; exact integral_domainBits (Q j) p (clusterContactBin G (Q j) x v n m)]; exact hB (Q j))

end InfiniteContactLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullContactPower
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem fullContactBin_power_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval)
    (α ε C p₀ : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) (hC0 : 0 < C) (hp₀ : 0 < p₀)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ z, {e | z ∈ G e}.ncard ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (x v : V) (p : unitInterval), p₀ ≤ (p:ℝ) → p ≤ q →
      ∀ n : ℕ, 1 ≤ n → (∫ ω, fullContactBin G x v n (2*n) ω ∂law p) ≤
        A*(n:ℝ)^((1:ℝ)/2+ε-2*α) := by
  obtain ⟨A,hA,hAb⟩ := clusterContactBin_power_bound G hloc q α ε C p₀ hα hα1 hε hr hC0 hp₀ hfin hI hC d hd
  refine ⟨A,hA,?_⟩
  intro x v p hpp hpq n hn
  apply fullContactBin_integral_le_of_finite G hloc d hdeg x v p
    (cluster_finite_ae_mono G x p q hpq (hfin x)) (cluster_finite_ae_mono G v p q hpq (hfin v))
  intro Q
  apply hAb Q _ x v p hpp hpq n hn
  intro z
  calc
    _ = ((Q.filter fun e => z ∈ G e):Set E).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ {e | z ∈ G e}.ncard := Set.ncard_le_ncard (fun e he => (Finset.mem_filter.mp he).2) (hloc z)
    _ ≤ d := hdeg z

theorem integrable_fullContactBin [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d) (x v : V) (n m : ℕ) (hn : 0 < n) (p : unitInterval) :
    Integrable (fullContactBin G x v n m) (law p) := by
  apply Integrable.mono' (integrable_const ((d*m:ℕ):ℝ)) (measurable_fullContactBin G hloc x v n m).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (fullContactBin_nonneg G x v n m ω)]
    exact fullContactBin_le G hloc d hd x v n m hn ω)

end FullContactPower
end Percolation

 
namespace Percolation
open MeasureTheory
section NonnegativeDyadicIntegration

 

theorem integral_le_tsum_majorants {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (F : ℕ → Ω → ℝ) (hfm : AEStronglyMeasurable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hF0 : ∀ j ω, 0 ≤ F j ω) (hFi : ∀ j, Integrable (F j) μ)
    (hs : Summable (fun j => ∫ ω, F j ω ∂μ))
    (hb : ∀ ω, ENNReal.ofReal (f ω) ≤ ∑' j, ENNReal.ofReal (F j ω)) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ ∑' j, ∫ ω, F j ω ∂μ := by
  have he : (∫⁻ ω, ∑' j, ENNReal.ofReal (F j ω) ∂μ) =
      ENNReal.ofReal (∑' j, ∫ ω, F j ω ∂μ) := by
    rw [lintegral_tsum (fun j => (hFi j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [←ofReal_integral_eq_lintegral_ofReal (hFi _) (Filter.Eventually.of_forall (hF0 _))]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hF0 j)) hs).symm
  have hle := (lintegral_mono hb).trans_eq he
  have hi : Integrable f μ := ⟨hfm,(hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)).mpr
    (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf0)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg (fun j => integral_nonneg (hF0 j)))).mp hle

theorem dyadic_rpow_identity (L : ℕ) (hL : 0 < L) (r : ℝ) (j : ℕ) :
    ((2^j*L:ℕ):ℝ)^r = (L:ℝ)^r*((2:ℝ)^r)^j := by
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.mul_rpow (by positivity) (by positivity),
    ←Real.rpow_natCast,←Real.rpow_mul (by norm_num),mul_comm (j:ℝ) r,Real.rpow_mul (by norm_num),Real.rpow_natCast,mul_comm]

theorem dyadic_rpow_summable (L : ℕ) (hL : 0 < L) (r : ℝ) (hr : r < 0) :
    Summable (fun j : ℕ => ((2^j*L:ℕ):ℝ)^r) := by
  simp only [dyadic_rpow_identity L hL r]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)).mul_left _

theorem dyadic_rpow_sum (L : ℕ) (hL : 0 < L) (r : ℝ) (hr : r < 0) :
    (∑' j : ℕ, ((2^j*L:ℕ):ℝ)^r) = (L:ℝ)^r*(1-(2:ℝ)^r)⁻¹ := by
  simp only [dyadic_rpow_identity L hL r,tsum_mul_left]
  rw [tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)]

end NonnegativeDyadicIntegration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullLargeContacts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem fullLargeContact_nonneg (G : BondGraph V E) (x v : V) (L : ℕ) (ω : Set E) :
    0 ≤ fullLargeContact G x v L ω := by unfold fullLargeContact; split_ifs <;> positivity

theorem measurable_fullLargeContact [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x v : V) (L : ℕ) :
    Measurable (fullLargeContact G x v L) := by
  have hs : Measurable (fun ω : Set E => min (cluster G ω x).ncard (cluster G ω v).ncard) :=
    (measurable_cluster_ncard G hloc x).min (measurable_cluster_ncard G hloc v)
  exact ((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (measurable_clusterContactCount G x v)).ite
    (((measurableSet_conn G x v).compl).inter (measurableSet_le measurable_const hs)) measurable_const

theorem fullLargeContact_le_dyadic (G : BondGraph V E) (x v : V) (L : ℕ) (hL : 0 < L) (ω : Set E) :
    ENNReal.ofReal (fullLargeContact G x v L ω) ≤
      ∑' j : ℕ, ENNReal.ofReal (fullContactBin G x v (2^j*L) (2*(2^j*L)) ω) := by
  by_cases h : ¬Conn G ω x v ∧ L ≤ min (cluster G ω x).ncard (cluster G ω v).ncard
  · let k := min (cluster G ω x).ncard (cluster G ω v).ncard
    let j := Nat.log 2 (k/L)
    have hq : k/L ≠ 0 := by
      have : 1 ≤ k/L := (Nat.le_div_iff_mul_le hL).mpr (by rw [one_mul]; exact h.2)
      omega
    have hl := (Nat.le_div_iff_mul_le hL).mp (Nat.pow_log_le_self 2 hq)
    have hu := (Nat.div_lt_iff_lt_mul hL).mp (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (k/L))
    have hbin : fullContactBin G x v (2^j*L) (2*(2^j*L)) ω = fullLargeContact G x v L ω := by
      rw [fullLargeContact,ite_eq_left h,fullContactBin,ite_eq_left]
      refine ⟨h.1,hl,?_⟩
      calc
        _ = k := rfl
        _ ≤ 2^(Nat.log 2 (k/L)+1)*L := hu.le
        _ = _ := by dsimp [j]; rw [pow_succ]; ring
    exact (le_of_eq (congrArg ENNReal.ofReal hbin.symm)).trans
      (ENNReal.le_tsum (f := fun scale =>
        ENNReal.ofReal (fullContactBin G x v (2^scale*L) (2*(2^scale*L)) ω)) j)
  · simp only [fullLargeContact,ite_eq_right h,ENNReal.ofReal_zero]; exact bot_le

 

theorem fullLargeContact_bound_of_bins [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d) (x v : V) (p : unitInterval)
    (A r : ℝ) (_hA : 0 ≤ A) (hr : r < 0)
    (hB : ∀ n : ℕ, 1 ≤ n → (∫ ω, fullContactBin G x v n (2*n) ω ∂law p) ≤ A*(n:ℝ)^r)
    (L : ℕ) (hL : 0 < L) :
    Integrable (fullLargeContact G x v L) (law p) ∧
      (∫ ω, fullLargeContact G x v L ω ∂law p) ≤ A*(1-(2:ℝ)^r)⁻¹*(L:ℝ)^r := by
  let F := fun j => fullContactBin G x v (2^j*L) (2*(2^j*L))
  have hbp (j : ℕ) : 0 < 2^j*L := Nat.mul_pos (pow_pos (by norm_num) _) hL
  have hFi (j : ℕ) : Integrable (F j) (law p) := integrable_fullContactBin G hloc d hd x v _ _ (hbp j) p
  have hsumB := (dyadic_rpow_summable L hL r hr).mul_left A
  have hsum : Summable (fun j => ∫ ω, F j ω ∂law p) :=
    hsumB.of_nonneg_of_le (fun j => integral_nonneg (fullContactBin_nonneg G x v _ _))
      (fun j => hB _ (hbp j))
  obtain ⟨hi,hb⟩ := integral_le_tsum_majorants (law p) (fullLargeContact G x v L) F
    (measurable_fullLargeContact G hloc x v L).aestronglyMeasurable
    (fullLargeContact_nonneg G x v L) (fun j => fullContactBin_nonneg G x v _ _) hFi hsum
    (fullLargeContact_le_dyadic G x v L hL)
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ ∑' j : ℕ, A*((2^j*L:ℕ):ℝ)^r := hsum.tsum_le_tsum (fun j => hB _ (hbp j)) hsumB
    _ = _ := by rw [tsum_mul_left,dyadic_rpow_sum L hL r hr]; ring

end FullLargeContacts
end Percolation

 
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

theorem fullLargeContact_power_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (q : unitInterval)
    (α ε C p₀ : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) (hC0 : 0 < C) (hp₀ : 0 < p₀)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (x v : V) (p : unitInterval), p₀ ≤ (p:ℝ) → p ≤ q →
      ∀ L : ℕ, 1 ≤ L → Integrable (fullLargeContact G x v L) (law p) ∧
        (∫ ω, fullLargeContact G x v L ω ∂law p) ≤ A*(L:ℝ)^((1:ℝ)/2+ε-2*α) := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  have hdn (x : V) := (incident_ncard_le_degree G hloc x).trans (hdeg x)
  obtain ⟨A,hA,hAb⟩ := fullContactBin_power_bound G hloc q α ε C p₀ hα hα1 hε hr hC0 hp₀ hfin hI hC d hd hdn
  refine ⟨A*(1-(2:ℝ)^((1:ℝ)/2+ε-2*α))⁻¹,?_ ,?_⟩
  · exact mul_pos hA (inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)))
  · intro x v p hpp hpq L hL
    exact fullLargeContact_bound_of_bins G hloc d hdn x v p A _ hA.le hr (hAb x v p hpp hpq) L hL

 

theorem critical_large_contact_bound
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ (x v : V) (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p ≤ pc G →
      ∀ L : ℕ, 1 ≤ L → Integrable (fullLargeContact G x v L) (law p) ∧
        (∫ ω, fullLargeContact G x v L ω ∂law p) ≤ A*(L:ℝ)^((1:ℝ)/2+ε-2*α) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  have hfinite : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
    intro x
    obtain ⟨i,a,b,hab,rfl⟩ := hcover x
    exact cluster_finite_ae_covariant G (pc G) hab (root i) (hfin i)
  obtain ⟨C,hC,hb⟩ := uniform_cluster_power_of_root G hloc (pc G) root hcover α
    (critical_root_power_integrable G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α hα hα1)
  exact fullLargeContact_power_bound G hloc hqt (pc G) α ε C ((pc G:ℝ)/2) hα.le (by linarith)
    hε hr hC (by positivity) hfinite (fun x => (hb x).1) (fun x => (hb x).2)

end UniformLargeContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ExtendedTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem enn_sum_iSup_nat {α : Type*} (s : Finset α) (f : ℕ → α → ℝ≥0∞)
    (hm : ∀ a, Monotone (fun n => f n a)) :
    (∑ a ∈ s, ⨆ n, f n a) = ⨆ n, ∑ a ∈ s, f n a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,ih]
    exact ENNReal.iSup_add_iSup_of_monotone (hm a) (fun n m h =>
      Finset.sum_le_sum fun a _ => hm a h)

theorem enn_tsum_iSup_nat {α : Type*} (f : ℕ → α → ℝ≥0∞)
    (hm : ∀ a, Monotone (fun n => f n a)) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  simp_rw [ENNReal.tsum_eq_iSup_sum,enn_sum_iSup_nat _ f hm]
  exact iSup_comm

 

theorem RootTransport.ennreal (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (m : V → V → ℝ≥0∞)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y) :
    (∑ i, ENNReal.ofReal (weight i) * ∑' y, m (root i) y) =
      (∑ i, ENNReal.ofReal (weight i) * ∑' x, m x (root i)) := by
  let cut (n : ℕ) (x y : V) : ℝ≥0∞ :=
    if transportCut G n x y then min (m x y) n else 0
  have hc0 (n : ℕ) (x y : V) : cut n x y ≠ ⊤ := by
    dsimp [cut]
    split_ifs
    · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
    · exact ENNReal.zero_ne_top
  have hcm (x y : V) : Monotone (fun n => cut n x y) := by
    intro n k hnk
    dsimp [cut]
    split_ifs with hn hk
    · exact min_le_min_left _ (by exact_mod_cast hnk)
    · exact False.elim (hk (transportCut_mono G hnk hn))
    · exact zero_le
    · exact le_refl _
  have hcs (x y : V) : (⨆ n, cut n x y) = m x y := by
    apply le_antisymm
    · refine iSup_le fun n => ?_
      dsimp [cut]
      split_ifs
      · exact min_le_left _ _
      · exact zero_le
    · obtain ⟨N,hN⟩ := exists_transportCut G hconn y {x}
      have hxy := hN x (Finset.mem_singleton_self x)
      have he : (⨆ k : ℕ, min (m x y) (k:ℝ≥0∞)) = m x y := by
        rw [←inf_iSup_eq,ENNReal.iSup_natCast,inf_top_eq]
      rw [←he]
      refine iSup_le fun k => le_iSup_of_le (max N k) ?_
      dsimp [cut]
      rw [ite_eq_left (transportCut_mono G (le_max_left N k) hxy)]
      exact min_le_min_left _ (by exact_mod_cast le_max_right N k)
  have hrow (n : ℕ) (x : V) : Summable (fun y => (cut n x y).toReal) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x n).toFinset)
    intro y hy
    have hh : ¬transportCut G n x y := fun h => hy ((Set.Finite.mem_toFinset _).mpr h.1)
    simp only [cut,ite_eq_right hh,ENNReal.toReal_zero]
  have hcol (n : ℕ) (y : V) : Summable (fun x => (cut n x y).toReal) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
    intro x hx
    have hh : ¬transportCut G n x y := fun h => hx ((Set.Finite.mem_toFinset _).mpr h.2)
    simp only [cut,ite_eq_right hh,ENNReal.toReal_zero]
  have he (n : ℕ) :
      (∑ i, ENNReal.ofReal (weight i) * ∑' y, cut n (root i) y) =
        (∑ i, ENNReal.ofReal (weight i) * ∑' x, cut n x (root i)) := by
    have ht := htr.real root weight Γ (fun x y => (cut n x y).toReal)
      (fun a ha x y => by
        obtain ⟨b,hb⟩ := hΓ ha
        simp only [cut,transportCut_aut G hb,hi a ha]) (hrow n) (hcol n)
    apply_fun ENNReal.ofReal at ht
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i)
      (tsum_nonneg fun _ => ENNReal.toReal_nonneg)),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i)
      (tsum_nonneg fun _ => ENNReal.toReal_nonneg))] at ht
    simp_rw [ENNReal.ofReal_mul (hw _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) (hrow n _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) (hcol n _),
      ENNReal.ofReal_toReal (hc0 n _ _)] at ht
    exact ht
  have hlim (f : ι → V → ℝ≥0∞) (g : ℕ → ι → V → ℝ≥0∞)
      (hmono : ∀ i y, Monotone (fun n => g n i y)) (hs : ∀ i y, (⨆ n, g n i y) = f i y) :
      (∑ i, ENNReal.ofReal (weight i) * ∑' y, f i y) =
        ⨆ n, ∑ i, ENNReal.ofReal (weight i) * ∑' y, g n i y := by
    simp_rw [←hs,enn_tsum_iSup_nat _ (hmono _),ENNReal.mul_iSup]
    exact enn_sum_iSup_nat _ _ (fun i n k h => mul_le_mul_right (ENNReal.tsum_le_tsum
      (fun y => hmono i y h)) _)
  rw [hlim (fun i y => m (root i) y) (fun n i y => cut n (root i) y)
    (fun i y => hcm (root i) y) (fun i y => hcs (root i) y),
    hlim (fun i x => m x (root i)) (fun n i x => cut n x (root i))
    (fun i x => hcm x (root i)) (fun i x => hcs x (root i))]
  exact iSup_congr he

end ExtendedTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterAveraging
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_clusterAveragingKernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x y : V) :
    Measurable (fun ω => clusterAveragingKernel G ω x y) := by
  exact (((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
    (measurable_cluster_ncard G hloc x)).inv).ite (measurableSet_conn G x y) measurable_const

theorem clusterAveragingKernel_symm (G : BondGraph V E) (ω : Set E) (x y : V) :
    clusterAveragingKernel G ω x y = clusterAveragingKernel G ω y x := by
  by_cases h : Conn G ω x y
  · simp only [clusterAveragingKernel,ite_eq_left h,ite_eq_left (conn_symm G ω h),cluster_eq_of_conn G ω h]
  · have h' : ¬Conn G ω y x := fun hh => h (conn_symm G ω hh)
    simp only [clusterAveragingKernel,ite_eq_right h,ite_eq_right h']

theorem cluster_ncard_pos (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : 0 < (cluster G ω x).ncard :=
  (Set.ncard_pos hf).mpr ⟨x,mem_cluster_self G ω x⟩

theorem clusterAveragingKernel_row (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : (∑' y, clusterAveragingKernel G ω x y) = 1 := by
  have he : (fun y => clusterAveragingKernel G ω x y) =
      (fun y => (if Conn G ω x y then (1:ℝ≥0∞) else 0)*((cluster G ω x).ncard:ℝ≥0∞)⁻¹) := by
    funext y
    unfold clusterAveragingKernel
    split_ifs <;> simp
  rw [he,ENNReal.tsum_mul_right]
  change clusterMass G ω x * ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ = 1
  rw [clusterMass_eq_ncard G ω x hf]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (cluster_ncard_pos G ω x hf).ne') (ENNReal.natCast_ne_top _)

theorem clusterAveragingKernel_column (G : BondGraph V E) (ω : Set E) (y : V)
    (hf : (cluster G ω y).Finite) : (∑' x, clusterAveragingKernel G ω x y) = 1 := by
  simp_rw [clusterAveragingKernel_symm G ω]
  exact clusterAveragingKernel_row G ω y hf

theorem clusterAveragingKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    clusterAveragingKernel G (b ⁻¹' ω) x y = clusterAveragingKernel G ω (a x) (a y) := by
  simp only [clusterAveragingKernel,conn_aut_iff G hab,cluster_ncard_covariant G hab]

 

theorem root_cluster_average [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (f : Set E → V → ℝ≥0∞) (hf : ∀ x, Measurable (fun ω => f ω x))
    (hi : ∀ a ∈ Γ, ∀ b, IsAut G a b → ∀ ω x, f (b ⁻¹' ω) x = f ω (a x)) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
      clusterAveragingKernel G ω (root i) y * f ω y ∂law p) =
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, f ω (root i) ∂law p) := by
  let m (x y : V) : ℝ≥0∞ := ∫⁻ ω, clusterAveragingKernel G ω x y * f ω y ∂law p
  have hm (x y : V) : Measurable (fun ω => clusterAveragingKernel G ω x y * f ω y) :=
    (measurable_clusterAveragingKernel G hloc x y).mul (hf y)
  have hinv : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    have ht := lintegral_map (μ := law p) (hm x y) (measurable_set_preimage b)
    rw [law_map_preimage_equiv] at ht
    dsimp only [m]
    rw [ht]
    apply lintegral_congr
    intro ω
    rw [clusterAveragingKernel_aut G hb,hi a ha b hb]
  have ht := htr.ennreal G hconn hloc root weight Γ hΓ hw m hinv
  have hr (x : V) : (∑' y, m x y) = ∫⁻ ω, ∑' y, clusterAveragingKernel G ω x y*f ω y ∂law p := by
    exact (lintegral_tsum (fun y => (hm x y).aemeasurable)).symm
  have hc (y : V) : (∑' x, m x y) = ∫⁻ ω, f ω y ∂law p := by
    rw [show (∑' x, m x y) = ∫⁻ ω, ∑' x, clusterAveragingKernel G ω x y*f ω y ∂law p from
      (lintegral_tsum (fun x => (hm x y).aemeasurable)).symm]
    apply lintegral_congr_ae
    filter_upwards [hfin y] with ω hω
    rw [ENNReal.tsum_mul_right,clusterAveragingKernel_column G ω y hω,one_mul]
  simpa only [hr,hc] using ht

end ClusterAveraging
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PositiveClusterPairs
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_weighted_resum (G : BondGraph V E) (ω : Set E)
    (hfin : ∀ x, (cluster G ω x).Finite) (f : V → V → ℝ≥0∞)
    (hc : ∀ x y, Conn G ω x y → f x y = f y y) :
    (∑' x, ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ *
      ∑' y, if Conn G ω x y then f x y else 0) = ∑' y, f y y := by
  have he (x y : V) : ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ *
      (if Conn G ω x y then f x y else 0) = clusterAveragingKernel G ω x y*f y y := by
    by_cases h : Conn G ω x y
    · simp only [ite_eq_left h,clusterAveragingKernel,hc x y h]
    · simp only [ite_eq_right h,clusterAveragingKernel,mul_zero,zero_mul]
  simp_rw [←ENNReal.tsum_mul_left,he]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro y
  rw [ENNReal.tsum_mul_right,clusterAveragingKernel_column G ω y (hfin y),one_mul]

theorem clusterPairDensity_reroot_pointwise (G : BondGraph V E) (ω : Set E)
    (hfin : ∀ x, (cluster G ω x).Finite) (J F : V → V → ℝ≥0∞)
    (hF : ∀ x y a b, Conn G ω x a → Conn G ω y b → F x y = F a b) (x : V) :
    clusterPairDensity G ω (fun a b => clusterPairKernel G ω J a b * F a b) x =
      ∑' a, clusterAveragingKernel G ω x a *
        ∑' b, J a b * (if ¬Conn G ω a b then F a b else 0) := by
  let K (a b : V) : ℝ≥0∞ := if ¬Conn G ω a b then F a b else 0
  have hK (a b c d : V) (hac : Conn G ω a c) (hbd : Conn G ω b d) : K a b = K c d := by
    have he : Conn G ω a b ↔ Conn G ω c d := by
      constructor
      · intro h; exact conn_trans G ω (conn_symm G ω hac) (conn_trans G ω h hbd)
      · intro h; exact conn_trans G ω hac (conn_trans G ω h (conn_symm G ω hbd))
    simp only [K,he,hF a b c d hac hbd]
  have hterm (y : V) : ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ *
      (if ¬Conn G ω x y then clusterPairKernel G ω J x y*F x y else 0) =
      ∑' a, if Conn G ω x a then ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ *
        ∑' b, if Conn G ω y b then J a b*K x y else 0 else 0 := by
    have hcond : (if ¬Conn G ω x y then clusterPairKernel G ω J x y*F x y else 0) =
        clusterPairKernel G ω J x y*K x y := by dsimp [K]; split_ifs <;> simp
    rw [hcond,clusterPairKernel,←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro a
    by_cases hxa : Conn G ω x a
    · rw [ite_eq_left hxa,←ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro b
      by_cases hyb : Conn G ω y b <;> simp only [hxa,hyb,and_self,and_false,
        if_true,if_false,zero_mul]
    · simp only [hxa,false_and,if_false,tsum_zero,zero_mul,mul_zero]
  unfold clusterPairDensity
  simp_rw [hterm]
  rw [ENNReal.tsum_comm,←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases hxa : Conn G ω x a
  · simp only [ite_eq_left hxa,clusterAveragingKernel]
    congr 1
    rw [cluster_weighted_resum G ω hfin (fun y b => J a b*K x y)
      (fun y b hyb => congrArg (fun t => J a b*t) (hK x y x b (conn_refl G ω x) hyb))]
    apply tsum_congr
    intro b
    rw [hK x b a b hxa (conn_refl G ω b)]
  · simp only [ite_eq_right hxa,tsum_zero,mul_zero,clusterAveragingKernel,zero_mul]

end PositiveClusterPairs
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterPairRerooting
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairFunctional_reroot [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (hF : ∀ ω x y a b, Conn G ω x a → Conn G ω y b → F ω x y = F ω a b)
    (hi : ∀ a ∈ Γ, ∀ b, IsAut G a b → ∀ ω x y, F (b ⁻¹' ω) x y = F ω (a x) (a y)) :
    clusterPairFunctional G p root weight (fun ω x y => clusterPairKernel G ω J x y * F ω x y) =
      ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
        J (root i) y * (if ¬Conn G ω (root i) y then F ω (root i) y else 0) ∂law p := by
  let f (ω : Set E) (x : V) : ℝ≥0∞ :=
    ∑' y, J x y * (if ¬Conn G ω x y then F ω x y else 0)
  have hf (x : V) : Measurable (fun ω => f ω x) := by
    apply Measurable.tsum
    intro y
    exact measurable_const.mul ((hm x y).ite (measurableSet_conn G x y).compl measurable_const)
  have hfe : ∀ a ∈ Γ, ∀ b, IsAut G a b → ∀ ω x, f (b ⁻¹' ω) x = f ω (a x) := by
    intro a ha b hab ω x
    dsimp [f]
    rw [←a.tsum_eq (fun y => J (a x) y * (if ¬Conn G ω (a x) y then F ω (a x) y else 0))]
    apply tsum_congr
    intro y
    rw [hJ a ha,conn_aut_iff G hab,hi a ha b hab]
  have ht := root_cluster_average G hconn hloc root weight Γ hΓ htr hw p hfin f hf hfe
  rw [clusterPairFunctional]
  calc
    _ = ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
        clusterAveragingKernel G ω (root i) y*f ω y ∂law p := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_all_iff.mpr hfin] with ω hω
      exact clusterPairDensity_reroot_pointwise G ω hω J (F ω) (hF ω) (root i)
    _ = _ := ht

end ClusterPairRerooting
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairReversal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairDensity_eq_tsum (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x : V) :
    clusterPairDensity G ω F x = ∑' y, clusterPairMass G ω F x y := by
  simp only [clusterPairDensity,clusterPairMass,←ENNReal.tsum_mul_left,mul_assoc]

theorem clusterPairMass_swap (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x y : V) :
    clusterPairMass G ω F x y = clusterPairMass G ω (fun a b => F b a) y x := by
  have he : Conn G ω x y ↔ Conn G ω y x := ⟨conn_symm G ω,conn_symm G ω⟩
  simp only [clusterPairMass,he,mul_comm]

theorem measurable_clusterPairMass [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (F : Set E → V → V → ℝ≥0∞) (hf : ∀ x y, Measurable (fun ω => F ω x y)) (x y : V) :
    Measurable (fun ω => clusterPairMass G ω (F ω) x y) := by
  have hs (x : V) : Measurable (fun ω => ((cluster G ω x).ncard:ℝ≥0∞)⁻¹) :=
    (((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_cluster_ncard G hloc x))).inv
  exact ((hs x).mul (hs y)).mul ((hf x y).ite (measurableSet_conn G x y).compl measurable_const)

theorem clusterPairFunctional_swap [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hf : ∀ x y, Measurable (fun ω => F ω x y))
    (hi : ∀ a ∈ Γ, ∀ b, IsAut G a b → ∀ ω x y, F (b ⁻¹' ω) x y = F ω (a x) (a y)) :
    clusterPairFunctional G p root weight F =
      clusterPairFunctional G p root weight (fun ω x y => F ω y x) := by
  let m (x y : V) : ℝ≥0∞ := ∫⁻ ω, clusterPairMass G ω (F ω) x y ∂law p
  have hm := measurable_clusterPairMass G hloc F hf
  have hinv : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    have ht := lintegral_map (μ := law p) (hm x y) (measurable_set_preimage b)
    rw [law_map_preimage_equiv] at ht
    dsimp only [m]
    rw [ht]
    apply lintegral_congr
    intro ω
    simp only [clusterPairMass,cluster_ncard_covariant G hb,conn_aut_iff G hb,hi a ha b hb]
  have ht := htr.ennreal G hconn hloc root weight Γ hΓ hw m hinv
  have hr (x : V) : (∑' y, m x y) = ∫⁻ ω, clusterPairDensity G ω (F ω) x ∂law p := by
    simp_rw [clusterPairDensity_eq_tsum]
    exact (lintegral_tsum (fun y => (hm x y).aemeasurable)).symm
  have hc (y : V) : (∑' x, m x y) =
      ∫⁻ ω, clusterPairDensity G ω (fun a b => F ω b a) y ∂law p := by
    simp_rw [clusterPairDensity_eq_tsum,←clusterPairMass_swap G _ (F _)]
    exact (lintegral_tsum (fun x => (hm x y).aemeasurable)).symm
  simpa only [hr,hc,clusterPairFunctional] using ht

end PairReversal
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_ContactTrace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
section IndexedEdgeKernel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem enn_ncard_eq_tsum {α : Type*} (A : Set α) (hA : A.Finite) :
    (A.ncard:ℝ≥0∞) = ∑' a, if a ∈ A then (1:ℝ≥0∞) else 0 := by
  rw [tsum_eq_sum (s := hA.toFinset) (fun a ha => by
    simp only [Set.Finite.mem_toFinset] at ha
    exact ite_eq_right ha)]
  simp only [Set.ncard_eq_toFinset_card A hA]
  rw [Finset.sum_congr rfl (fun a ha => ite_eq_left ((Set.Finite.mem_toFinset _).mp ha))]
  simp



theorem indexedEdgeKernel_symm (G : BondGraph V E) (x y : V) :
    indexedEdgeKernel G x y = indexedEdgeKernel G y x := by rw [indexedEdgeKernel,indexedEdgeKernel,Sym2.eq_swap]

theorem indexedEdgeKernel_row (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    (∑' y, indexedEdgeKernel G x y) = (degree G x:ℝ≥0∞) := by
  change (∑' y, ∑' e, if G e = s(x,y) then (1:ℝ≥0∞) else 0) = _
  rw [ENNReal.tsum_comm,←ENNReal.tsum_prod]
  have hn := (enn_ncard_eq_tsum _ (finite_steps G hloc x)).symm
  have he : (∑' (p : E × V), if G p.1 = s(x,p.2) then (1:ℝ≥0∞) else 0) =
      (({ey : E × V | G ey.1 = s(x,ey.2)} : Set (E × V)).ncard:ℝ≥0∞) := by
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    apply tsum_congr
    intro ey
    by_cases h : G ey.1 = s(x,ey.2) <;> simp only [Set.mem_ofPred_eq,h,if_true,if_false]
  rw [he]
  change (({ey : E × V | G ey.1 = s(x,ey.2)} : Set (E × V)).ncard:ℝ≥0∞) = (Nat.card (Step G x):ℝ≥0∞)
  rw [←Nat.card_coe_set_eq]; rfl

theorem indexedEdgeKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x y : V) :
    indexedEdgeKernel G (a x) (a y) = indexedEdgeKernel G x y := by
  unfold indexedEdgeKernel
  rw [←b.tsum_eq (fun e => if G e = s(a x,a y) then (1:ℝ≥0∞) else 0)]
  apply tsum_congr
  intro e
  have he : G (b e) = s(a x,a y) ↔ G e = s(x,y) := by
    rw [hab e,←Sym2.map_mk]
    exact (Sym2.map.injective a.injective).eq_iff
  simp only [he]

end IndexedEdgeKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactKernelCounting
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contact_endpoints_unique (G : BondGraph V E) (ω : Set E) (x y : V)
    (hd : ¬Conn G ω x y) {e : E} {a b c d : V}
    (ha : Conn G ω x a) (_hb : Conn G ω y b)
    (_hc : Conn G ω x c) (he : Conn G ω y d)
    (hab : G e = s(a,b)) (hcd : G e = s(c,d)) : a = c ∧ b = d := by
  rcases Sym2.eq_iff.mp (hab.symm.trans hcd) with h | h
  · exact h
  · exfalso
    apply hd
    exact conn_trans G ω ha (by simpa only [h.1] using conn_symm G ω he)

theorem closedContactSet_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (A B : Set V) (hA : A.Finite) : (closedContactSet G A B).Finite := by
  have hs := contactSet_subset_incident G hloc hA.toFinset B
  rw [Set.Finite.coe_toFinset] at hs
  exact (incidentSupport G hloc hA.toFinset).finite_toSet.subset hs

theorem clusterPairKernel_edge (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x y : V) (hd : ¬Conn G ω x y) (hx : (cluster G ω x).Finite) :
    clusterPairKernel G ω (indexedEdgeKernel G) x y = (clusterContactCount G ω x y:ℝ≥0∞) := by
  have hed (e : E) :
      (∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0) =
      if e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) then 1 else 0 := by
    by_cases h : e ∈ closedContactSet G (cluster G ω x) (cluster G ω y)
    · obtain ⟨a,ha,b,hb,hab⟩ := h
      change Conn G ω x a at ha
      change Conn G ω y b at hb
      have hh : e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) := ⟨a,ha,b,hb,hab⟩
      rw [ite_eq_left hh,tsum_eq_single a]
      · rw [tsum_eq_single b]
        · exact ite_eq_left ⟨ha,hb,hab⟩
        · intro d hdb
          apply ite_eq_right
          intro hc
          exact hdb (contact_endpoints_unique G ω x y hd hc.1 hc.2.1 ha hb hc.2.2 hab).2
      · intro c hca
        apply ENNReal.tsum_eq_zero.mpr
        intro d
        apply ite_eq_right
        intro hc
        exact hca (contact_endpoints_unique G ω x y hd hc.1 hc.2.1 ha hb hc.2.2 hab).1
    · rw [ite_eq_right h]
      apply ENNReal.tsum_eq_zero.mpr
      intro a
      apply ENNReal.tsum_eq_zero.mpr
      intro b
      apply ite_eq_right
      intro hab
      exact h ⟨a,hab.1,b,hab.2.1,hab.2.2⟩
  have he (a b : V) : (if Conn G ω x a ∧ Conn G ω y b then indexedEdgeKernel G a b else 0) =
      ∑' e, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
    by_cases ha : Conn G ω x a <;> by_cases hb : Conn G ω y b <;>
      simp only [ha,hb,and_self,true_and,false_and,if_true,if_false,indexedEdgeKernel,tsum_zero]
  rw [clusterPairKernel]
  simp_rw [he]
  calc
    _ = ∑' e, ∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
      calc
        _ = ∑' a, ∑' e, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
          apply tsum_congr; intro a; exact ENNReal.tsum_comm
        _ = _ := ENNReal.tsum_comm
    _ = ∑' e, if e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) then (1:ℝ≥0∞) else 0 := tsum_congr hed
    _ = _ := (enn_ncard_eq_tsum _ (closedContactSet_finite G hloc _ _ hx)).symm

end ContactKernelCounting
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem closedContactSet_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (A B : Set V) :
    b '' closedContactSet G A B = closedContactSet G (a '' A) (a '' B) := by
  ext e
  constructor
  · rintro ⟨f,⟨x,hx,y,hy,hf⟩,rfl⟩
    exact ⟨a x,Set.mem_image_of_mem a hx,a y,Set.mem_image_of_mem a hy,by rw [hab f,hf,Sym2.map_mk]⟩
  · rintro ⟨z,⟨x,hx,rfl⟩,w,⟨y,hy,rfl⟩,he⟩
    refine ⟨b.symm e,⟨x,hx,y,hy,?_⟩,b.apply_symm_apply e⟩
    apply Sym2.map.injective a.injective
    rw [←hab,Sym2.map_mk]
    simpa only [Equiv.apply_symm_apply] using he

theorem clusterContactCount_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    clusterContactCount G (b ⁻¹' ω) x y = clusterContactCount G ω (a x) (a y) := by
  unfold clusterContactCount
  rw [←cluster_aut G hab ω x,←cluster_aut G hab ω y,←closedContactSet_aut G hab,
    Set.ncard_image_of_injective _ b.injective]

theorem fullLargeContact_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) (L : ℕ) :
    fullLargeContact G x y L (b ⁻¹' ω) = fullLargeContact G (a x) (a y) L ω := by
  simp only [fullLargeContact,conn_aut_iff G hab,cluster_ncard_covariant G hab,clusterContactCount_aut G hab]

theorem fullLargeContact_cluster_constant (G : BondGraph V E) (ω : Set E)
    (L : ℕ) (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) :
    fullLargeContact G x y L ω = fullLargeContact G a b L ω := by
  have hc : Conn G ω x y ↔ Conn G ω a b := by
    constructor
    · intro h; exact conn_trans G ω (conn_symm G ω hxa) (conn_trans G ω h hyb)
    · intro h; exact conn_trans G ω hxa (conn_trans G ω h (conn_symm G ω hyb))
  simp only [fullLargeContact,clusterContactCount,cluster_eq_of_conn G ω hxa,
    cluster_eq_of_conn G ω hyb,hc]

theorem fullLargeContact_distinct (G : BondGraph V E) (ω : Set E) (x y : V) (L : ℕ) :
    (if ¬Conn G ω x y then ENNReal.ofReal (fullLargeContact G x y L ω) else 0) =
      ENNReal.ofReal (fullLargeContact G x y L ω) := by
  by_cases h : Conn G ω x y
  · simp only [fullLargeContact,h,not_true_eq_false,false_and,if_false,ENNReal.ofReal_zero]
  · exact ite_eq_left h

end ContactCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactSquareTrace
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactSquareLarge_reroot [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite) (L : ℕ) :
    clusterPairFunctional G p root weight (contactSquareLarge G L) =
      ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
        indexedEdgeKernel G (root i) y * ENNReal.ofReal (fullLargeContact G (root i) y L ω) ∂law p := by
  have hj : ∀ a ∈ Γ, ∀ x y, indexedEdgeKernel G (a x) (a y) = indexedEdgeKernel G x y := by
    intro a ha x y
    obtain ⟨b,hab⟩ := hΓ ha
    exact indexedEdgeKernel_aut G hab x y
  have ht := clusterPairFunctional_reroot G hconn hloc root weight Γ hΓ htr hw p hfin
    (indexedEdgeKernel G) hj (fun ω x y => ENNReal.ofReal (fullLargeContact G x y L ω))
    (fun x y => (measurable_fullLargeContact G hloc x y L).ennreal_ofReal)
    (fun ω x y a b hxa hyb => congrArg ENNReal.ofReal (fullLargeContact_cluster_constant G ω L x y a b hxa hyb))
    (fun a _ b hab ω x y => congrArg ENNReal.ofReal (fullLargeContact_aut G hab ω x y L))
  simp_rw [fullLargeContact_distinct] at ht
  rw [←ht]
  unfold clusterPairFunctional
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hfin (root i)] with ω hω
  unfold clusterPairDensity
  congr 1
  apply tsum_congr
  intro y
  congr 1
  by_cases hd : Conn G ω (root i) y
  · simp only [hd,not_true_eq_false,if_false]
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [clusterPairKernel_edge G hloc ω (root i) y hd hω]
    unfold contactSquareLarge fullLargeContact
    by_cases hs : L ≤ min (cluster G ω (root i)).ncard (cluster G ω y).ncard
    · simp only [hd,hs,not_false_eq_true,true_and,if_true,ENNReal.ofReal_natCast,pow_two]
    · simp only [hs,and_false,if_false,ENNReal.ofReal_zero,mul_zero]

theorem contactSquareLarge_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite) (L d : ℕ)
    (hd : ∀ x, degree G x ≤ d) (B : ℝ) (_hB : 0 ≤ B)
    (hI : ∀ x y, Integrable (fullLargeContact G x y L) (law p))
    (hb : ∀ x y, (∫ ω, fullLargeContact G x y L ω ∂law p) ≤ B) :
    clusterPairFunctional G p root weight (contactSquareLarge G L) ≤ ENNReal.ofReal ((d:ℝ)*B) := by
  have hi (x y : V) : (∫⁻ ω, ENNReal.ofReal (fullLargeContact G x y L ω) ∂law p) ≤ ENNReal.ofReal B := by
    rw [←ofReal_integral_eq_lintegral_ofReal (hI x y) (Filter.Eventually.of_forall (fullLargeContact_nonneg G x y L))]
    exact ENNReal.ofReal_le_ofReal (hb x y)
  have hr (x : V) : (∫⁻ ω, ∑' y, indexedEdgeKernel G x y * ENNReal.ofReal (fullLargeContact G x y L ω) ∂law p) ≤
      ENNReal.ofReal ((d:ℝ)*B) := by
    have hm (y : V) : Measurable (fun ω => indexedEdgeKernel G x y * ENNReal.ofReal (fullLargeContact G x y L ω)) :=
      (measurable_const : Measurable (fun _ : Set E => indexedEdgeKernel G x y)).mul (measurable_fullLargeContact G hloc x y L).ennreal_ofReal
    rw [lintegral_tsum (fun y => (hm y).aemeasurable)]
    simp_rw [lintegral_const_mul _ (measurable_fullLargeContact G hloc x _ L).ennreal_ofReal]
    calc
      _ ≤ ∑' y, indexedEdgeKernel G x y * ENNReal.ofReal B := ENNReal.tsum_le_tsum (fun y => mul_le_mul_right (hi x y) _)
      _ = (degree G x:ℝ≥0∞)*ENNReal.ofReal B := by rw [ENNReal.tsum_mul_right,indexedEdgeKernel_row G hloc x]
      _ ≤ (d:ℝ≥0∞)*ENNReal.ofReal B := mul_le_mul_left (by exact_mod_cast hd x) _
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast]
  rw [contactSquareLarge_reroot G hconn hloc root weight Γ hΓ htr hw p hfin L]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (weight i)*ENNReal.ofReal ((d:ℝ)*B) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_right (hr (root i)) _)
    _ = _ := by rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hw1,ENNReal.ofReal_one,one_mul]

end ContactSquareTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section CriticalContactSquare
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_contact_square_bound_nat
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p ≤ pc G →
      ∀ L : ℕ, 1 ≤ L → clusterPairFunctional G p root weight (contactSquareLarge G L) ≤
        ENNReal.ofReal (C*(L:ℝ)^((1:ℝ)/2+ε-2*α)) := by
  obtain ⟨A,hA,hb⟩ := critical_large_contact_bound G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  refine ⟨(d:ℝ)*A,mul_pos (by exact_mod_cast hd) hA,?_⟩
  intro p hp hpq L hL
  have hf : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
    intro x
    obtain ⟨i,a,ha,rfl⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact cluster_finite_ae_mono G (a (root i)) p (pc G) hpq
      (cluster_finite_ae_covariant G (pc G) hab (root i) (hfin i))
  have h := contactSquareLarge_bound G hconn hloc root weight Γ hΓ htr (fun i => (hw i).le) hw1 p hf
    L d hdeg (A*(L:ℝ)^((1:ℝ)/2+ε-2*α)) (mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _))
    (fun x y => (hb x y p hp hpq L hL).1) (fun x y => (hb x y p hp hpq L hL).2)
  simpa only [mul_assoc] using h

end CriticalContactSquare
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section DistinctClusterBK
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinct_cluster_disjoint_occurrence (G : BondGraph V E) (ω : Set E)
    (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) (hd : ¬Conn G ω x y) :
    ω ∈ DisjointOccurrence {η | Conn G η x a} {η | Conn G η y b} := by
  obtain ⟨s,hs,hsa⟩ := finiteWitness_conn G x a _ (conn_restrict_cluster G ω x (mem_cluster_self G ω x) hxa)
  obtain ⟨t,ht,htb⟩ := finiteWitness_conn G y b _ (conn_restrict_cluster_compl G ω x hd hyb)
  refine ⟨s,t,fun e he => (hs he).1,fun e he => (ht he).1,?_,hsa,htb⟩
  apply Finset.disjoint_left.mpr
  intro e he ht'
  obtain ⟨⟨z,w⟩,hr⟩ := Quot.exists_rep (G e)
  have hz : z ∈ G e := by rw [←hr]; exact Sym2.mem_mk_left z w
  exact (ht ht').2 z hz ((hs he).2 z hz)

theorem distinct_cluster_two_point_bound [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y a b : V) :
    law p {ω | Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y} ≤
      law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b} := by
  calc
    _ ≤ law p (DisjointOccurrence {ω | Conn G ω x a} {ω | Conn G ω y b}) :=
      measure_mono (fun ω h => distinct_cluster_disjoint_occurrence G ω x y a b h.1 h.2.1 h.2.2)
    _ ≤ _ := bk_ennreal p _ _ (fun _ _ h hc => conn_mono G h hc)
      (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x a) (finiteWitness_conn G y b)

theorem measurable_clusterPairKernel [Countable V] [Countable E]
    (G : BondGraph V E) (J : V → V → ℝ≥0∞) (x y : V) :
    Measurable (fun ω => clusterPairKernel G ω J x y) := by
  apply Measurable.tsum
  intro a
  apply Measurable.tsum
  intro b
  exact measurable_const.ite ((measurableSet_conn G x a).inter (measurableSet_conn G y b)) measurable_const

theorem clusterPairKernel_cluster_constant (G : BondGraph V E) (ω : Set E)
    (J : V → V → ℝ≥0∞) (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) :
    clusterPairKernel G ω J x y = clusterPairKernel G ω J a b := by
  have hx (z : V) : Conn G ω x z ↔ Conn G ω a z :=
    ⟨fun h => conn_trans G ω (conn_symm G ω hxa) h,fun h => conn_trans G ω hxa h⟩
  have hy (z : V) : Conn G ω y z ↔ Conn G ω b z :=
    ⟨fun h => conn_trans G ω (conn_symm G ω hyb) h,fun h => conn_trans G ω hyb h⟩
  simp only [clusterPairKernel,hx,hy]

theorem clusterPairKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (J : V → V → ℝ≥0∞) (hJ : ∀ x y, J (a x) (a y) = J x y)
    (ω : Set E) (x y : V) :
    clusterPairKernel G (b ⁻¹' ω) J x y = clusterPairKernel G ω J (a x) (a y) := by
  unfold clusterPairKernel
  rw [←a.tsum_eq (fun x' => ∑' y', if Conn G ω (a x) x' ∧ Conn G ω (a y) y' then J x' y' else 0)]
  apply tsum_congr
  intro x'
  rw [←a.tsum_eq (fun y' => if Conn G ω (a x) (a x') ∧ Conn G ω (a y) y' then J (a x') y' else 0)]
  simp only [hJ,conn_aut_iff G hab]

end DistinctClusterBK
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairSquareDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairKernel_distinct_integral [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (J : V → V → ℝ≥0∞) (x y : V) :
    (∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p) =
      ∑' a, ∑' b, J a b * law p {ω | Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y} := by
  have he (ω : Set E) : (if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0) =
      ∑' a, ∑' b, J a b * (if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0) := by
    by_cases hd : Conn G ω x y
    · simp only [hd,not_true_eq_false,and_false,if_false,mul_zero,tsum_zero]
    · rw [ite_eq_left hd,clusterPairKernel]
      apply tsum_congr; intro a
      apply tsum_congr; intro b
      by_cases h : Conn G ω x a ∧ Conn G ω y b
      · simp only [h.1,h.2,hd,not_false_eq_true,and_self,if_true,mul_one]
      · have hn : ¬ (Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y) := fun h' => h ⟨h'.1,h'.2.1⟩
        simp only [ite_eq_right h,ite_eq_right hn,mul_zero]
  have hm (a b : V) : Measurable (fun ω => if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite ((measurableSet_conn G x a).inter ((measurableSet_conn G y b).inter (measurableSet_conn G x y).compl)) measurable_const
  have hm' (a b : V) : Measurable (fun ω : Set E => J a b * (if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0)) :=
    (measurable_const : Measurable (fun _ : Set E => J a b)).mul (hm a b)
  simp_rw [he]
  rw [lintegral_tsum (fun a => (Measurable.tsum (fun b => hm' a b)).aemeasurable)]
  apply tsum_congr; intro a
  rw [lintegral_tsum (fun b => (hm' a b).aemeasurable)]
  apply tsum_congr; intro b
  rw [lintegral_const_mul _ (hm a b)]
  congr 1
  convert
    (lintegral_indicator_one (μ := law p) ((measurableSet_conn G x a).inter ((measurableSet_conn G y b).inter (measurableSet_conn G x y).compl))) using 1
  · apply lintegral_congr
    intro ω
    simp only [Set.indicator,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_ofPred_eq,Pi.one_apply]
  · congr 1

theorem clusterPairKernel_distinct_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (J : V → V → ℝ≥0∞) (x y : V) :
    (∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p) ≤
      ∑' a, ∑' b, J a b * (law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b}) := by
  rw [clusterPairKernel_distinct_integral]
  exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
    mul_le_mul_right (distinct_cluster_two_point_bound G p x y a b) _))

 

theorem clusterPairFunctional_square_diagram [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y) :
    clusterPairFunctional G p root weight (fun ω x y => (clusterPairKernel G ω J x y)^2) ≤
      ∑ i, ENNReal.ofReal (weight i) * ∑' v, ∑' a, ∑' b,
        J (root i) v * (J a b * (law p {ω | Conn G ω (root i) a} * law p {ω | Conn G ω v b})) := by
  have ht := clusterPairFunctional_reroot G hconn hloc root weight Γ hΓ htr hw p hfin J hJ
    (fun ω x y => clusterPairKernel G ω J x y) (measurable_clusterPairKernel G J)
    (fun ω x y a b => clusterPairKernel_cluster_constant G ω J x y a b)
    (fun a ha b hab ω x y => clusterPairKernel_aut G hab J (hJ a ha) ω x y)
  simp only [←pow_two] at ht
  rw [ht]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_right
  have hm (v : V) : Measurable (fun ω : Set E => if ¬Conn G ω (root i) v then clusterPairKernel G ω J (root i) v else 0) :=
    (measurable_clusterPairKernel G J (root i) v).ite (measurableSet_conn G (root i) v).compl measurable_const
  have hm' (v : V) : Measurable (fun ω : Set E => J (root i) v * (if ¬Conn G ω (root i) v then clusterPairKernel G ω J (root i) v else 0)) :=
    (measurable_const : Measurable (fun _ : Set E => J (root i) v)).mul (hm v)
  rw [lintegral_tsum (fun v => (hm' v).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro v
  rw [lintegral_const_mul _ (hm v)]
  simp_rw [ENNReal.tsum_mul_left]
  exact mul_le_mul_right (clusterPairKernel_distinct_bound G p J (root i) v) _

end PairSquareDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactRealCutoff
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactSquareLargeReal_eq_ceil (G : BondGraph V E) (L : ℝ)
    (ω : Set E) (x y : V) :
    contactSquareLargeReal G L ω x y = contactSquareLarge G ⌈L⌉₊ ω x y := by
  have he : L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) ↔
      ⌈L⌉₊ ≤ min (cluster G ω x).ncard (cluster G ω y).ncard := by
    rw [←Nat.cast_min, Nat.ceil_le]
  simp only [contactSquareLargeReal,contactSquareLarge,he]

 

theorem critical_contact_square_bound
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p ≤ pc G →
      ∀ L : ℝ, 1 ≤ L → clusterPairFunctional G p root weight (contactSquareLargeReal G L) ≤
        ENNReal.ofReal (C*L^((1:ℝ)/2+ε-2*α)) := by
  obtain ⟨C,hC,hb⟩ := critical_contact_square_bound_nat G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  refine ⟨C,hC,?_⟩
  intro p hp hpq L hL
  have hLn : 1 ≤ ⌈L⌉₊ := by
    have hc : (1:ℝ) ≤ (⌈L⌉₊:ℝ) := hL.trans (Nat.le_ceil L)
    exact_mod_cast hc
  have hEq : contactSquareLargeReal G L = contactSquareLarge G ⌈L⌉₊ := funext fun ω => funext fun x => funext fun y => contactSquareLargeReal_eq_ceil G L ω x y
  rw [hEq]
  exact (hb p hp hpq _ hLn).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < L) (Nat.le_ceil L) hr.le) hC.le))

end ContactRealCutoff
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section NonnegativeOperatorDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem ennMatrixCoeff_mul {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : PositiveRealMatrix A) (hB : PositiveRealMatrix B) (x y : V) :
    ennMatrixCoeff (A*B) x y = ∑' z, ennMatrixCoeff A x z * ennMatrixCoeff B z y := by
  unfold ennMatrixCoeff
  rw [←(hA.mul_hasSum B x y).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun z => mul_nonneg (hA x z).2 (hB z y).2) (hA.mul_hasSum B x y).summable]
  apply tsum_congr; intro z
  exact ENNReal.ofReal_mul (hA x z).2

theorem ennMatrixCoeff_symm {A : Hilbert V →L[ℂ] Hilbert V}
    (hA : IsSelfAdjoint A) (x y : V) : ennMatrixCoeff A x y = ennMatrixCoeff A y x := by
  unfold ennMatrixCoeff
  rw [matrixCoeff_real_symm A hA x y]

theorem HasKernel.ennMatrixCoeff [Countable E] (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    ennMatrixCoeff T x y = law p {ω | Conn G ω x y} := by
  unfold Percolation.ennMatrixCoeff matrixCoeff
  rw [hT x y]
  simp only [Complex.ofReal_re,twoPoint,ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem HasKernel.positiveRealMatrix (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) : PositiveRealMatrix T := by
  intro x y
  change (T (lp.single 2 y (1:ℂ)) x).im = 0 ∧ 0 ≤ (T (lp.single 2 y (1:ℂ)) x).re
  rw [hT x y]
  exact ⟨rfl,twoPoint_nonneg G p x y⟩

theorem square_kernel_diagram (J T : Hilbert V →L[ℂ] Hilbert V)
    (hJ : PositiveRealMatrix J) (hT : PositiveRealMatrix T)
    (hsJ : IsSelfAdjoint J) (hsT : IsSelfAdjoint T) (x : V) :
    (∑' v, ∑' a, ∑' b, ennMatrixCoeff J x v * (ennMatrixCoeff J a b *
      (ennMatrixCoeff T x a * ennMatrixCoeff T v b))) = ennMatrixCoeff (J*T*J*T) x x := by
  rw [mul_assoc,mul_assoc,ennMatrixCoeff_mul hJ (hT.mul (hJ.mul hT))]
  apply tsum_congr; intro v
  rw [ennMatrixCoeff_mul hT (hJ.mul hT)]
  simp_rw [ennMatrixCoeff_mul hJ hT]
  simp_rw [←ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro b
  apply tsum_congr; intro a
  rw [ennMatrixCoeff_symm hsJ b a,ennMatrixCoeff_symm hsT a x]
  ac_rfl

theorem enn_rootTrace {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) :
    (∑ i, ENNReal.ofReal (weight i) * ennMatrixCoeff A (root i) (root i)) =
      ENNReal.ofReal (rootTrace root weight A).re := by
  unfold rootTrace ennMatrixCoeff
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (hA _ _).2)]
  apply Finset.sum_congr rfl; intro i _
  exact (ENNReal.ofReal_mul (hw i)).symm

end NonnegativeOperatorDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal ComplexOrder
section KernelSquareTrace
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] spectralRealOperatorScalarTower spectralRealOperatorSMulCommClass

theorem rootTrace_six_le_cube {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : KernelInvariant Γ T) (hpos : 0 ≤ T) :
    (rootTrace root weight (T^6)).re ≤ ‖T‖^3*(rootTrace root weight (T^3)).re := by
  have hp3 : 0 ≤ T^3 := CStarAlgebra.pow_nonneg (a := T) hpos 3
  have h := rootTrace_positive_mul_le root weight htr hw (T^3) (T^3)
    (hT.pow 3) (hT.pow 3) hp3 (IsSelfAdjoint.of_nonneg hp3)
  have he : T^3*T^3 = T^6 := by rw [←pow_add]
  rw [he] at h
  have hr := (Complex.le_def.mp h).1
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  exact hr.trans (mul_le_mul_of_nonneg_right (norm_pow_le' T (by norm_num : 0 < (3:ℕ)))
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw (T^3) hp3)).1)

 

theorem clusterPairFunctional_twoPoint_square_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) :
    clusterPairFunctional G p root weight (fun ω x y =>
      (clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y)^2) ≤
      ENNReal.ofReal (‖T‖^3*(rootTrace root weight (T^3)).re) := by
  have hp := hT.positiveRealMatrix G p T
  have hpos : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (hT.isPositive G p T)
  have hsa := IsSelfAdjoint.of_nonneg hpos
  have hI : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hJ : ∀ a ∈ Γ, ∀ x y, ennMatrixCoeff (T^2) (a x) (a y) = ennMatrixCoeff (T^2) x y := by
    intro a ha x y
    unfold ennMatrixCoeff
    rw [(hI.pow 2) a ha]
  have hb := clusterPairFunctional_square_diagram G hconn hloc root weight Γ hΓ htr hw p hfin
    (ennMatrixCoeff (T^2)) hJ
  have hd (x : V) : (∑' v, ∑' a, ∑' b, ennMatrixCoeff (T^2) x v * (ennMatrixCoeff (T^2) a b *
      (law p {ω | Conn G ω x a} * law p {ω | Conn G ω v b}))) = ennMatrixCoeff (T^6) x x := by
    simp_rw [←hT.ennMatrixCoeff G p T]
    rw [square_kernel_diagram (T^2) T (hp.pow 2) hp (hsa.pow 2) hsa]
    congr 1
  simp_rw [hd] at hb
  rw [enn_rootTrace root weight hw (T^6) (hp.pow 6)] at hb
  exact hb.trans (ENNReal.ofReal_le_ofReal (rootTrace_six_le_cube root weight htr hw T hI hpos))

end KernelSquareTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteClusterKernel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClusterWeight_expand (G : BondGraph V E) (f : V → ℝ)
    (Q ω : Finset E) (hω : ω ⊆ Q) (x : V) :
    finiteClusterWeight G f x ω = ∑ y ∈ insert x (searchVertices G Q),
      f y * (if Conn G (ω:Set E) x y then (1:ℝ) else 0) := by
  unfold finiteClusterWeight
  calc
    _ = ∑ y ∈ finiteRootComponent G ω x, f y * (if Conn G (ω:Set E) x y then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hc : Conn G (ω:Set E) x y := by
        change y ∈ (finiteRootComponent G ω x:Set V) at hy
        rwa [coe_finiteRootComponent] at hy
      rw [ite_eq_left hc,mul_one]
    _ = _ := Finset.sum_subset (finiteRootComponent_subset G Q _ x ω hω (by rfl)) (by
      intro y _ hy
      have hn : ¬Conn G (ω:Set E) x y := by
        intro h
        apply hy
        change y ∈ (finiteRootComponent G ω x:Set V)
        rwa [coe_finiteRootComponent]
      rw [ite_eq_right hn,mul_zero])

theorem finiteClusterWeight_expectation_le [Countable E]
    (G : BondGraph V E) (Q : Finset E) (f : V → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : V) (p : unitInterval) (hs : Summable (fun y => f y*twoPoint G p x y)) :
    bernoulliPolynomial Q (finiteClusterWeight G f x) p ≤ ∑' y, f y*twoPoint G p x y := by
  have he : bernoulliPolynomial Q (finiteClusterWeight G f x) p =
      bernoulliPolynomial Q (fun ω => ∑ y ∈ insert x (searchVertices G Q), f y*(if Conn G (ω:Set E) x y then (1:ℝ) else 0)) p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    exact finiteClusterWeight_expand G f Q ω hω x
  rw [he,bernoulliPolynomial_sum]
  calc
    _ ≤ ∑ y ∈ insert x (searchVertices G Q), f y*twoPoint G p x y := by
      apply Finset.sum_le_sum
      intro y _
      have hpQ : bernoulliPolynomial Q (fun ω => if Conn G (ω:Set E) x y then (1:ℝ) else 0) p =
          (law p).real {ω | Conn G (ω ∩ (Q:Set E)) x y} :=
        finiteEventPolynomial_restrict Q {ω | Conn G ω x y} p
      rw [bernoulliPolynomial_const_mul,hpQ]
      apply mul_le_mul_of_nonneg_left _ (hf y)
      exact measureReal_mono (fun ω h => conn_mono G Set.inter_subset_left h)
    _ ≤ _ := hs.sum_le_tsum _ (fun y _ => mul_nonneg (hf y) (twoPoint_nonneg G p x y))

theorem finitePairKernel_nonneg (G : BondGraph V E) (J : V → V → ℝ)
    (hJ : ∀ a b, 0 ≤ J a b) (ω : Finset E) (x y : V) : 0 ≤ finitePairKernel G J ω x y :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hJ a b

theorem finitePairKernel_exterior (G : BondGraph V E) (J : V → V → ℝ)
    (ω : Finset E) (x y : V) (hd : ¬Conn G (ω:Set E) x y) :
    finitePairKernel G J ω x y = ∑ a ∈ finiteRootComponent G ω x,
      finiteClusterWeight G (J a) y (exteriorBonds G ω (finiteRootComponent G ω x:Set V)) := by
  unfold finitePairKernel finiteClusterWeight
  rw [finiteRootComponent_exterior G ω x y hd]

end FiniteClusterKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallFinitePairKernel
attribute [local instance] Classical.propDecidable Classical.decEq


theorem finiteSmallPairKernel_bound [Countable E]
    (G : BondGraph V E) (Q : Finset E) (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b)
    (x y : V) (p : unitInterval) (L M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ a, Summable (fun b => J a b*twoPoint G p y b))
    (hb : ∀ a, (∑' b, J a b*twoPoint G p y b) ≤ M) :
    bernoulliPolynomial Q (finiteSmallPairKernel G J L x y) p ≤
      M*bernoulliPolynomial Q (finiteSmallClusterSize G L x) p := by
  let f (W : Finset V) (η : Finset E) : ℝ :=
    (if (W.card:ℝ) < L ∧ y ∉ W then ∑ a ∈ W, finiteClusterWeight G (J a) y η else 0) -
      M*(if (W.card:ℝ) < L then (W.card:ℝ) else 0)
  have hf (W : Finset V) : bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p ≤ 0 := by
    by_cases hW : (W.card:ℝ) < L
    · by_cases hy : y ∈ W
      · simp only [f,hW,hy,not_true_eq_false,and_false,if_false,if_true,zero_sub,
          bernoulliPolynomial_const]
        exact neg_nonpos.mpr (mul_nonneg hM (Nat.cast_nonneg _))
      · simp only [f,hW,hy,not_false_eq_true,and_self,if_true,bernoulliPolynomial_sub,
          bernoulliPolynomial_const,bernoulliPolynomial_sum]
        apply sub_nonpos.mpr
        calc
          _ ≤ ∑ _a ∈ W, M := Finset.sum_le_sum fun a _ =>
            (finiteClusterWeight_expectation_le G _ (J a) (hJ a) y p (hs a)).trans (hb a)
          _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    · simp only [f,hW,false_and,if_false,mul_zero,sub_zero,bernoulliPolynomial_zero]
      exact le_rfl
  have ht := cluster_exterior_expectation_bound G Q x p f 0 hf
  have he (ω : Finset E) : f (finiteRootComponent G ω x)
      (exteriorBonds G ω (finiteRootComponent G ω x:Set V)) =
      finiteSmallPairKernel G J L x y ω - M*finiteSmallClusterSize G L x ω := by
    have hm : y ∈ finiteRootComponent G ω x ↔ Conn G (ω:Set E) x y := by
      change y ∈ (finiteRootComponent G ω x:Set V) ↔ _
      rw [coe_finiteRootComponent]
      rfl
    unfold f finiteSmallPairKernel finiteSmallClusterSize
    simp only [hm]
    by_cases hc : (finiteRootComponent G ω x).card < L ∧ ¬Conn G (ω:Set E) x y
    · rw [ite_eq_left hc,ite_eq_left hc,finitePairKernel_exterior G J ω x y hc.2]
    · rw [ite_eq_right hc,ite_eq_right hc]
  simp_rw [he] at ht
  rw [bernoulliPolynomial_sub,bernoulliPolynomial_const_mul] at ht
  exact sub_nonpos.mp ht

end SmallFinitePairKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SmallSizeFractionalMoment
attribute [local instance] Classical.propDecidable Classical.decEq

theorem small_count_le_power (s L α : ℝ) (hs : 0 ≤ s) (hL : 0 ≤ L) (hα : α ≤ 1) :
    (if s < L then s else 0) ≤ L^(1-α)*s^α := by
  by_cases h : s < L
  · rw [ite_eq_left h]
    rcases eq_or_lt_of_le hs with rfl | hs'
    · positivity
    · calc
        s = s^(1-α)*s^α := by rw [←Real.rpow_add hs']; simp only [sub_add_cancel,Real.rpow_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs h.le (by linarith)) (Real.rpow_nonneg hs α)
  · rw [ite_eq_right h]
    exact mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg hs _)

theorem finiteSmallClusterSize_moment_bound [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (p : unitInterval)
    (L α : ℝ) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hI : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p)) :
    bernoulliPolynomial Q (finiteSmallClusterSize G L x) p ≤
      L^(1-α)*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) := by
  let f (ω : Set E) := finiteSmallClusterSize G L x (domainBits Q ω)
  have hf : Integrable f (law p) := integrable_finite_local Q p f (fun ω => by
    dsimp [f]; rw [domainBits_local])
  rw [←integral_domainBits Q p (finiteSmallClusterSize G L x),←integral_const_mul]
  apply integral_mono_ae hf (hI.const_mul _)
  filter_upwards [hfin] with ω hω
  have hc : (finiteRootComponent G (domainBits Q ω) x).card ≤ (cluster G ω x).ncard := by
    rw [←Set.ncard_coe_finset,coe_finiteRootComponent,coe_domainBits]
    exact Set.ncard_le_ncard (fun y hy => conn_mono G Set.inter_subset_left hy) hω
  have hc' : ((finiteRootComponent G (domainBits Q ω) x).card:ℝ) ≤ (cluster G ω x).ncard := by exact_mod_cast hc
  exact (small_count_le_power _ L α (Nat.cast_nonneg _) hL hα1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hc' hα0) (Real.rpow_nonneg hL _))

theorem finiteSmallPairKernel_moment_bound [Countable E]
    (G : BondGraph V E) (Q : Finset E) (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b)
    (x y : V) (p : unitInterval) (L M α : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hI : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p))
    (hs : ∀ a, Summable (fun b => J a b*twoPoint G p y b))
    (hb : ∀ a, (∑' b, J a b*twoPoint G p y b) ≤ M) :
    bernoulliPolynomial Q (finiteSmallPairKernel G J L x y) p ≤
      M*(L^(1-α)*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p)) :=
  (finiteSmallPairKernel_bound G Q J hJ x y p L M hM hs hb).trans
    (mul_le_mul_of_nonneg_left (finiteSmallClusterSize_moment_bound G Q x p L α hL hα0 hα1 hfin hI) hM)

end SmallSizeFractionalMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section SmallKernelLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairKernel_finite (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (ω : Finset E) (x y : V) :
    clusterPairKernel G ω J x y =
      ∑ a ∈ finiteRootComponent G ω x, ∑ b ∈ finiteRootComponent G ω y, J a b := by
  have hm (x a : V) : a ∈ finiteRootComponent G ω x ↔ Conn G (ω:Set E) x a := by
    change a ∈ (finiteRootComponent G ω x:Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  rw [clusterPairKernel,tsum_eq_sum (s := finiteRootComponent G ω x) (fun a ha => by
    simp only [←hm x a,ha,false_and,if_false,tsum_zero])]
  apply Finset.sum_congr rfl
  intro a ha
  rw [tsum_eq_sum (s := finiteRootComponent G ω y) (fun b hb => by
    simp only [←hm y b,hb,and_false,if_false])]
  apply Finset.sum_congr rfl
  intro b hb
  rw [ite_eq_left ⟨(hm x a).mp ha,(hm y b).mp hb⟩]

theorem ofReal_finitePairKernel (G : BondGraph V E) (J : V → V → ℝ)
    (hJ : ∀ a b, 0 ≤ J a b) (ω : Finset E) (x y : V) :
    ENNReal.ofReal (finitePairKernel G J ω x y) =
      clusterPairKernel G ω (fun a b => ENNReal.ofReal (J a b)) x y := by
  rw [clusterPairKernel_finite]
  unfold finitePairKernel finiteClusterWeight
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => hJ a b)]
  apply Finset.sum_congr rfl
  intro a _
  exact ENNReal.ofReal_sum_of_nonneg (fun b _ => hJ a b)

theorem smallPairKernel_eq_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b) (L : ℝ)
    (ω : Set E) (x y : V) (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite)
    (Q : Finset E) (hQx : incidentSupport G hloc hx.toFinset ⊆ Q)
    (hQy : incidentSupport G hloc hy.toFinset ⊆ Q) :
    ENNReal.ofReal (finiteSmallPairKernel G J L x y (domainBits Q ω)) =
      smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω := by
  have hcluster (z : V) (hz : (cluster G ω z).Finite) (hQ : incidentSupport G hloc hz.toFinset ⊆ Q) :
      cluster G (domainBits Q ω:Set E) z = cluster G ω z := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hz.toFinset Q hQ ω z).mpr
      (Set.Finite.coe_toFinset hz).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  have hxC := hcluster x hx hQx
  have hyC := hcluster y hy hQy
  have hxN : (finiteRootComponent G (domainBits Q ω) x).card = (cluster G ω x).ncard := by
    rw [←Set.ncard_coe_finset,coe_finiteRootComponent,hxC]
  have hxconn (a : V) : Conn G (domainBits Q ω:Set E) x a ↔ Conn G ω x a := by
    change a ∈ cluster G (domainBits Q ω:Set E) x ↔ a ∈ cluster G ω x
    rw [hxC]
  have hyconn (b : V) : Conn G (domainBits Q ω:Set E) y b ↔ Conn G ω y b := by
    change b ∈ cluster G (domainBits Q ω:Set E) y ↔ b ∈ cluster G ω y
    rw [hyC]
  unfold finiteSmallPairKernel smallPairKernel
  rw [hxN]
  simp only [hxconn]
  split_ifs
  · rw [ofReal_finitePairKernel G J hJ]
    simp only [clusterPairKernel,hxconn,hyconn]
  · exact ENNReal.ofReal_zero

end SmallKernelLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section SmallKernelFatou
attribute [local instance] Classical.propDecidable Classical.decEq

theorem smallPairKernel_lintegral_le_of_finite [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b) (L : ℝ) (x y : V) (p : unitInterval)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hy : ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (B : ℝ)
    (hB : ∀ Q : Finset E, bernoulliPolynomial Q (finiteSmallPairKernel G J L x y) p ≤ B) :
    (∫⁻ ω, smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω ∂law p) ≤ ENNReal.ofReal B := by
  let : Encodable E := Encodable.ofCountable E
  let Q := vertexExhaustion (V := E)
  let f := fun j ω => finiteSmallPairKernel G J L x y (domainBits (Q j) ω)
  have hfi (j : ℕ) : Integrable (f j) (law p) := integrable_finite_local (Q j) p (f j) (fun ω => by
    dsimp [f]; rw [domainBits_local])
  have hfn (j : ℕ) : 0 ≤ᵐ[law p] f j := Eventually.of_forall (fun ω => by
    dsimp [f,finiteSmallPairKernel]
    split_ifs
    · exact finitePairKernel_nonneg G J hJ _ x y
    · exact le_rfl)
  have heq : ∀ᵐ ω ∂law p,
      liminf (fun j => ENNReal.ofReal (f j ω)) atTop =
        smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω := by
    filter_upwards [hx,hy] with ω hωx hωy
    obtain ⟨jx,hjx⟩ := subset_vertexExhaustion (incidentSupport G hloc hωx.toFinset)
    obtain ⟨jy,hjy⟩ := subset_vertexExhaustion (incidentSupport G hloc hωy.toFinset)
    have he : (fun j => ENNReal.ofReal (f j ω)) =ᶠ[atTop]
        (fun _ => smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω) := by
      filter_upwards [eventually_ge_atTop (max jx jy)] with j hj
      exact smallPairKernel_eq_finite G hloc J hJ L ω x y hωx hωy (Q j)
        (hjx.trans (vertexExhaustion_mono (le_max_left jx jy |>.trans hj)))
        (hjy.trans (vertexExhaustion_mono (le_max_right jx jy |>.trans hj)))
    exact (tendsto_const_nhds.congr' he.symm).liminf_eq
  calc
    _ = ∫⁻ ω, liminf (fun j => ENNReal.ofReal (f j ω)) atTop ∂law p := lintegral_congr_ae (heq.mono (fun _ h => h.symm))
    _ ≤ liminf (fun j => ∫⁻ ω, ENNReal.ofReal (f j ω) ∂law p) atTop :=
      lintegral_liminf_le' (fun j => (hfi j).aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal B := liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall (fun j => by
      rw [←ofReal_integral_eq_lintegral_ofReal (hfi j) (hfn j)]
      apply ENNReal.ofReal_le_ofReal
      rw [show (∫ ω, f j ω ∂law p) = bernoulliPolynomial (Q j) (finiteSmallPairKernel G J L x y) p from
        integral_domainBits (Q j) p (finiteSmallPairKernel G J L x y)]
      exact hB (Q j))))

 

theorem smallPairKernel_moment_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b)
    (x y : V) (p : unitInterval) (L M α : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hy : ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p))
    (hs : ∀ a, Summable (fun b => J a b*twoPoint G p y b))
    (hb : ∀ a, (∑' b, J a b*twoPoint G p y b) ≤ M) :
    (∫⁻ ω, smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω ∂law p) ≤
      ENNReal.ofReal (M*(L^(1-α)*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p))) :=
  smallPairKernel_lintegral_le_of_finite G hloc J hJ L x y p hx hy _ (fun Q =>
    finiteSmallPairKernel_moment_bound G Q J hJ x y p L M α hL hM hα0 hα1 hx hI hs hb)

end SmallKernelFatou
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal ComplexOrder
section SmallTwoPointKernel
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] spectralRealOperatorScalarTower spectralRealOperatorSMulCommClass

theorem matrixCoeff_positive_trace_norm {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : KernelInvariant Γ A) (hpos : 0 ≤ A) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ c*(rootTrace root weight A).re := by
  have hd (z : V) : (matrixCoeff A z z).re ≤ c*(rootTrace root weight A).re := by
    have h := (Complex.le_def.mp (rootTrace_diag_le root weight hcov hw c hc hmin A hA hpos z)).1
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using h
  have hn (z : V) : 0 ≤ (matrixCoeff A z z).re := (Complex.nonneg_iff.mp (matrixCoeff_nonneg A hpos z)).1
  have hC : 0 ≤ c*(rootTrace root weight A).re := mul_nonneg hc
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw A hpos)).1
  have hs := matrixCoeff_positive_product_norm_sq_le A 1 hpos x y
  simp only [one_mul,star_one,mul_one] at hs
  have hp := mul_le_mul (hd x) (hd y) (hn y) hC
  nlinarith [norm_nonneg (matrixCoeff A x y)]

theorem smallPairKernel_twoPoint_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (x y : V) (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (L α : ℝ) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hy : ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p)) :
    (∫⁻ ω, smallPairKernel G (ennMatrixCoeff (T^2)) L x y ω ∂law p) ≤
      ENNReal.ofReal ((c*(rootTrace root weight (T^3)).re)*
        (L^(1-α)*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p))) := by
  have hp := hT.positiveRealMatrix G p T
  have hpos : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (hT.isPositive G p T)
  have hp3 := CStarAlgebra.pow_nonneg (a := T) hpos 3
  have hTI : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hM : 0 ≤ c*(rootTrace root weight (T^3)).re := mul_nonneg hc
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw _ hp3)).1
  have he (b : V) : (matrixCoeff T b y).re = twoPoint G p y b := by
    change (T (lp.single 2 y (1:ℂ)) b).re = _
    rw [hT b y,Complex.ofReal_re,twoPoint_symm G p b y]
  have hs (a : V) : HasSum (fun b => (matrixCoeff (T^2) a b).re * twoPoint G p y b)
      (matrixCoeff (T^3) a y).re := by
    simpa only [he,←pow_succ] using (hp.pow 2).mul_hasSum T a y
  apply smallPairKernel_moment_bound G hloc (fun a b => (matrixCoeff (T^2) a b).re)
    (fun a b => ((hp.pow 2) a b).2) x y p L _ α hL hM hα0 hα1 hx hy hI
    (fun a => (hs a).summable)
  intro a
  rw [(hs a).tsum_eq]
  exact (Complex.re_le_norm _).trans (matrixCoeff_positive_trace_norm root weight Γ hcov hw c hc hmin _ (hTI.pow 3) hp3 a y)

end SmallTwoPointKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactSmallReroot
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_smallPairKernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (J : V → V → ℝ≥0∞) (L : ℝ) (x y : V) :
    Measurable (smallPairKernel G J L x y) := by
  exact (measurable_clusterPairKernel G J x y).ite
    ((measurableSet_lt ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x))
      measurable_const).inter (measurableSet_conn G x y).compl) measurable_const

theorem smallPairKernel_cluster_constant (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (L : ℝ) (ω : Set E) (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) :
    smallPairKernel G J L x y ω = smallPairKernel G J L a b ω := by
  have hc : Conn G ω x y ↔ Conn G ω a b := by
    constructor
    · intro h; exact conn_trans G ω (conn_symm G ω hxa) (conn_trans G ω h hyb)
    · intro h; exact conn_trans G ω hxa (conn_trans G ω h (conn_symm G ω hyb))
  simp only [smallPairKernel,cluster_eq_of_conn G ω hxa,hc,
    clusterPairKernel_cluster_constant G ω J x y a b hxa hyb]

theorem smallPairKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (J : V → V → ℝ≥0∞) (hJ : ∀ x y, J (a x) (a y) = J x y)
    (L : ℝ) (ω : Set E) (x y : V) :
    smallPairKernel G J L x y (b ⁻¹' ω) = smallPairKernel G J L (a x) (a y) ω := by
  simp only [smallPairKernel,cluster_ncard_covariant G hab,conn_aut_iff G hab,
    clusterPairKernel_aut G hab J hJ]

theorem smallPairKernel_distinct (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (L : ℝ) (ω : Set E) (x y : V) :
    (if ¬Conn G ω x y then smallPairKernel G J L x y ω else 0) = smallPairKernel G J L x y ω := by
  by_cases h : Conn G ω x y
  · simp only [smallPairKernel,h,not_true_eq_false,and_false,if_false]
  · exact ite_eq_left h

 
theorem contact_smallPairKernel_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y)
    (L : ℝ) (d : ℕ) (hd : ∀ x, degree G x ≤ d) (B : ℝ)
    (hb : ∀ x y, (∫⁻ ω, smallPairKernel G J L x y ω ∂law p) ≤ ENNReal.ofReal B) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * smallPairKernel G J L x y ω) ≤
      ENNReal.ofReal ((d:ℝ)*B) := by
  have hj : ∀ a ∈ Γ, ∀ x y, indexedEdgeKernel G (a x) (a y) = indexedEdgeKernel G x y := by
    intro a ha x y
    obtain ⟨b,hab⟩ := hΓ ha
    exact indexedEdgeKernel_aut G hab x y
  rw [clusterPairFunctional_reroot G hconn hloc root weight Γ hΓ htr hw p hfin
    (indexedEdgeKernel G) hj (fun ω x y => smallPairKernel G J L x y ω)
    (measurable_smallPairKernel G hloc J L)
    (fun ω x y a b hxa hyb => smallPairKernel_cluster_constant G J L ω x y a b hxa hyb)
    (fun a ha b hab ω x y => smallPairKernel_aut G hab J (hJ a ha) L ω x y)]
  simp_rw [smallPairKernel_distinct]
  have hr (x : V) : (∫⁻ ω, ∑' y, indexedEdgeKernel G x y * smallPairKernel G J L x y ω ∂law p) ≤
      ENNReal.ofReal ((d:ℝ)*B) := by
    have hm (y : V) : Measurable (fun ω => indexedEdgeKernel G x y * smallPairKernel G J L x y ω) :=
      (measurable_const : Measurable (fun _ : Set E => indexedEdgeKernel G x y)).mul (measurable_smallPairKernel G hloc J L x y)
    rw [lintegral_tsum (fun y => (hm y).aemeasurable)]
    simp_rw [lintegral_const_mul _ (measurable_smallPairKernel G hloc J L x _)]
    calc
      _ ≤ ∑' y, indexedEdgeKernel G x y * ENNReal.ofReal B := ENNReal.tsum_le_tsum (fun y => mul_le_mul_right (hb x y) _)
      _ = (degree G x:ℝ≥0∞)*ENNReal.ofReal B := by rw [ENNReal.tsum_mul_right,indexedEdgeKernel_row G hloc x]
      _ ≤ (d:ℝ≥0∞)*ENNReal.ofReal B := mul_le_mul_left (by exact_mod_cast hd x) _
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (weight i)*ENNReal.ofReal ((d:ℝ)*B) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_right (hr (root i)) _)
    _ = _ := by rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hw1,ENNReal.ofReal_one,one_mul]

end ContactSmallReroot
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairMeasure
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairFunctional_eq_lintegral [Countable V] [Countable E]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (root : ι → V) (weight : ι → ℝ)
    (F : Set E → V → V → ℝ≥0∞) (hF : ∀ x y, Measurable (fun ω => F ω x y)) :
    clusterPairFunctional G p root weight F =
      ∫⁻ t, F t.1 (root t.2.1) t.2.2 ∂clusterPairMeasure G p root weight := by
  let d : Set E × (ι × V) → ℝ≥0∞ := fun t => ENNReal.ofReal (weight t.2.1) *
    clusterPairMass G t.1 (fun _ _ => 1) (root t.2.1) t.2.2
  let f : Set E × (ι × V) → ℝ≥0∞ := fun t => F t.1 (root t.2.1) t.2.2
  have hd : Measurable d := by
    apply measurable_from_prod_countable_left
    intro q
    exact (measurable_const : Measurable (fun _ : Set E => ENNReal.ofReal (weight q.1))).mul
      (measurable_clusterPairMass G hloc (fun _ _ _ => 1) (fun _ _ => measurable_const) (root q.1) q.2)
  have hf : Measurable f := measurable_from_prod_countable_left (fun q => hF (root q.1) q.2)
  change _ = ∫⁻ t, f t ∂((law p).prod Measure.count).withDensity d
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf,lintegral_prod _ ((hd.mul hf).aemeasurable)]
  have he (ω : Set E) (i : ι) (y : V) :
      (d*f) (ω,(i,y)) = ENNReal.ofReal (weight i)*clusterPairMass G ω (F ω) (root i) y := by
    dsimp [d,f,clusterPairMass]
    (split_ifs <;> simp only [mul_one,mul_zero,zero_mul]); ring
  simp_rw [lintegral_count,ENNReal.tsum_prod',he,tsum_fintype]
  have hm (i : ι) : Measurable (fun ω => ∑' y, ENNReal.ofReal (weight i)*clusterPairMass G ω (F ω) (root i) y) :=
    Measurable.tsum (fun y => measurable_const.mul (measurable_clusterPairMass G hloc F hF (root i) y))
  rw [lintegral_finsetSum _ (fun i _ => hm i)]
  simp_rw [ENNReal.tsum_mul_left]
  rw [clusterPairFunctional]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_const_mul _ (Measurable.tsum (fun y => measurable_clusterPairMass G hloc F hF (root i) y))]
  congr 1
  apply lintegral_congr
  intro ω
  exact clusterPairDensity_eq_tsum G ω (F ω) (root i)

 

theorem clusterPairFunctional_cauchy_schwarz [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F H : Set E → V → V → ℝ≥0∞)
    (hF : ∀ x y, Measurable (fun ω => F ω x y))
    (hH : ∀ x y, Measurable (fun ω => H ω x y)) :
    clusterPairFunctional G p root weight (fun ω x y => F ω x y*H ω x y) ≤
      (clusterPairFunctional G p root weight (fun ω x y => (F ω x y)^2))^((1:ℝ)/2) *
      (clusterPairFunctional G p root weight (fun ω x y => (H ω x y)^2))^((1:ℝ)/2) := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  rw [clusterPairFunctional_eq_lintegral G hloc p root weight (fun ω x y => F ω x y*H ω x y) (fun x y => (hF x y).mul (hH x y)),
    clusterPairFunctional_eq_lintegral G hloc p root weight (fun ω x y => (F ω x y)^2) (fun x y => (hF x y).pow_const 2),
    clusterPairFunctional_eq_lintegral G hloc p root weight (fun ω x y => (H ω x y)^2) (fun x y => (hH x y).pow_const 2)]
  have hf : Measurable (fun t : Set E × (ι × V) => F t.1 (root t.2.1) t.2.2) :=
    measurable_from_prod_countable_left (fun q => hF (root q.1) q.2)
  have hh : Measurable (fun t : Set E × (ι × V) => H t.1 (root t.2.1) t.2.2) :=
    measurable_from_prod_countable_left (fun q => hH (root q.1) q.2)
  simpa only [Pi.mul_apply,ENNReal.rpow_two] using
    ENNReal.lintegral_mul_le_Lp_mul_Lq (clusterPairMeasure G p root weight) Real.HolderConjugate.two_two hf.aemeasurable hh.aemeasurable

end PairMeasure
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_RussoRows
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
open MeasureTheory
open scoped ENNReal
section PairFunctionalAlgebra
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairFunctional_mono_distinct (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F H : Set E → V → V → ℝ≥0∞)
    (h : ∀ ω x y, ¬Conn G ω x y → F ω x y ≤ H ω x y) :
    clusterPairFunctional G p root weight F ≤ clusterPairFunctional G p root weight H := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_right
  apply lintegral_mono
  intro ω
  unfold clusterPairDensity
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro y
  apply mul_le_mul_right
  by_cases hc : Conn G ω (root i) y
  · simp only [hc,not_true_eq_false,if_false,le_refl]
  · simpa only [ite_eq_left hc] using h ω (root i) y hc

theorem clusterPairFunctional_congr_ae (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F H : Set E → V → V → ℝ≥0∞)
    (h : ∀ᵐ ω ∂law p, ∀ x y, ¬Conn G ω x y → F ω x y = H ω x y) :
    clusterPairFunctional G p root weight F = clusterPairFunctional G p root weight H := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω
  unfold clusterPairDensity
  congr 1
  apply tsum_congr
  intro y
  congr 1
  by_cases hc : Conn G ω (root i) y
  · simp only [hc,not_true_eq_false,if_false]
  · rw [ite_eq_left hc,ite_eq_left hc,hω (root i) y hc]

theorem clusterPairFunctional_add [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F H : Set E → V → V → ℝ≥0∞)
    (hF : ∀ x y, Measurable (fun ω => F ω x y))
    (hH : ∀ x y, Measurable (fun ω => H ω x y)) :
    clusterPairFunctional G p root weight (fun ω x y => F ω x y+H ω x y) =
      clusterPairFunctional G p root weight F + clusterPairFunctional G p root weight H := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  rw [clusterPairFunctional_eq_lintegral G hloc p root weight _ hF,
    clusterPairFunctional_eq_lintegral G hloc p root weight _ hH,
    clusterPairFunctional_eq_lintegral G hloc p root weight (fun ω x y => F ω x y+H ω x y) (fun x y => (hF x y).add (hH x y))]
  exact lintegral_add_left (measurable_from_prod_countable_left (fun q => hF (root q.1) q.2)) _

theorem clusterPairKernel_symm (G : BondGraph V E) (ω : Set E)
    (J : V → V → ℝ≥0∞) (hJ : ∀ x y, J x y = J y x) (x y : V) :
    clusterPairKernel G ω J x y = clusterPairKernel G ω J y x := by
  unfold clusterPairKernel
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  apply tsum_congr
  intro b
  simp only [and_comm,hJ b a]

end PairFunctionalAlgebra
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section LargeContactCauchySchwarz
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_largeContactKernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (L : ℝ) (x y : V) :
    Measurable (fun ω => largeContactKernel G L ω x y) := by
  have hm (z : V) : Measurable (fun ω : Set E => ((cluster G ω z).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc z)
  exact (measurable_clusterPairKernel G (indexedEdgeKernel G) x y).ite
    (measurableSet_le measurable_const ((hm x).min (hm y))) measurable_const

theorem clusterPairFunctional_largeContact_sq [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (L : ℝ) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    clusterPairFunctional G p root weight (fun ω x y => (largeContactKernel G L ω x y)^2) =
      clusterPairFunctional G p root weight (contactSquareLargeReal G L) := by
  apply clusterPairFunctional_congr_ae G p root weight
  filter_upwards [ae_all_iff.mpr hfin] with ω hω
  intro x y hxy
  dsimp only [largeContactKernel,contactSquareLargeReal]
  split_ifs
  · rw [clusterPairKernel_edge G hloc ω x y hxy (hω x)]
  · rw [zero_pow (by decide : 2 ≠ 0)]

theorem clusterPairFunctional_largeContact_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (L : ℝ) (B : ℝ≥0∞)
    (hB : clusterPairFunctional G p root weight (contactSquareLargeReal G L) ≤ B) :
    clusterPairFunctional G p root weight (fun ω x y =>
      largeContactKernel G L ω x y * clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y) ≤
      B^((1:ℝ)/2)* (ENNReal.ofReal (‖T‖^3*(rootTrace root weight (T^3)).re))^((1:ℝ)/2) := by
  have hh := clusterPairFunctional_cauchy_schwarz G hloc p root weight
    (largeContactKernel G L) (fun ω x y => clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y)
    (measurable_largeContactKernel G hloc L) (measurable_clusterPairKernel G _)
  rw [clusterPairFunctional_largeContact_sq G hloc L p root weight hfin] at hh
  exact hh.trans (mul_le_mul
    (ENNReal.rpow_le_rpow hB (by positivity))
    (ENNReal.rpow_le_rpow (clusterPairFunctional_twoPoint_square_bound G hconn hloc root weight Γ hΓ htr hw p hfin T hT) (by positivity))
    bot_le bot_le)

end LargeContactCauchySchwarz
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal ComplexOrder
section SmallTraceTerm
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contact_smallTwoPoint_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (L α C : ℝ) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hI : ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p))
    (hC : ∀ x, (∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) ≤ C)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * smallPairKernel G (ennMatrixCoeff (T^2)) L x y ω) ≤
      ENNReal.ofReal ((d:ℝ)*c*C*L^(1-α)*(rootTrace root weight (T^3)).re) := by
  have hTI : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hJ : ∀ a ∈ Γ, ∀ x y, ennMatrixCoeff (T^2) (a x) (a y) = ennMatrixCoeff (T^2) x y := by
    intro a ha x y
    unfold ennMatrixCoeff
    rw [(hTI.pow 2) a ha]
  have hpos : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (hT.isPositive G p T)
  have hMt : 0 ≤ c*(rootTrace root weight (T^3)).re := mul_nonneg hc
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw _ (CStarAlgebra.pow_nonneg (a := T) hpos 3))).1
  have hh := contact_smallPairKernel_bound G hconn hloc root weight Γ hΓ htr hw hw1 p hfin
    (ennMatrixCoeff (T^2)) hJ L d hd (c*C*L^(1-α)*(rootTrace root weight (T^3)).re) (fun x y => by
      refine (smallPairKernel_twoPoint_bound G hloc root weight Γ hΓ hcov hw c hc hmin x y p T hT L α hL hα0 hα1 (hfin x) (hfin y) (hI x)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (c*(rootTrace root weight (T^3)).re)*(L^(1-α)*C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg hL _)) hMt
        _ = _ := by ring)
  convert hh using 1; congr 1; ring

end SmallTraceTerm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal ComplexOrder
section MixedTraceTerm
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contact_smallPairKernel_swap [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y) (L : ℝ) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) y x * smallPairKernel G J L y x ω) =
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * smallPairKernel G J L x y ω) := by
  symm
  apply clusterPairFunctional_swap G hconn hloc root weight Γ hΓ htr hw p
    (fun ω x y => clusterPairKernel G ω (indexedEdgeKernel G) x y * smallPairKernel G J L x y ω)
  · intro x y
    exact (measurable_clusterPairKernel G _ x y).mul (measurable_smallPairKernel G hloc J L x y)
  · intro a ha b hab ω x y
    rw [clusterPairKernel_aut G hab _ (indexedEdgeKernel_aut G hab),smallPairKernel_aut G hab J (hJ a ha)]

 

theorem clusterPairFunctional_twoPoint_mixed_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (L α C : ℝ) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hI : ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p))
    (hC : ∀ x, (∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) ≤ C)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (B : ℝ≥0∞)
    (hB : clusterPairFunctional G p root weight (contactSquareLargeReal G L) ≤ B) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y) ≤
    2*ENNReal.ofReal ((d:ℝ)*c*C*L^(1-α)*(rootTrace root weight (T^3)).re) +
      B^((1:ℝ)/2)* (ENNReal.ofReal (‖T‖^3*(rootTrace root weight (T^3)).re))^((1:ℝ)/2) := by
  let J := ennMatrixCoeff (T^2)
  let A := fun ω x y => clusterPairKernel G ω (indexedEdgeKernel G) x y*smallPairKernel G J L x y ω
  let D := fun ω x y => largeContactKernel G L ω x y*clusterPairKernel G ω J x y
  have heS (ω : Set E) (x y : V) : clusterPairKernel G ω (indexedEdgeKernel G) y x =
      clusterPairKernel G ω (indexedEdgeKernel G) x y := clusterPairKernel_symm G ω _ (indexedEdgeKernel_symm G) y x
  have hpos : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (hT.isPositive G p T)
  have hJS (ω : Set E) (x y : V) : clusterPairKernel G ω J y x = clusterPairKernel G ω J x y :=
    clusterPairKernel_symm G ω J (ennMatrixCoeff_symm ((IsSelfAdjoint.of_nonneg hpos).pow 2)) y x
  have hTI : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hJI : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y := by
    intro a ha x y
    dsimp [J,ennMatrixCoeff]
    rw [(hTI.pow 2) a ha]
  have hA (x y : V) : Measurable (fun ω => A ω x y) :=
    (measurable_clusterPairKernel G _ x y).mul (measurable_smallPairKernel G hloc J L x y)
  have hD (x y : V) : Measurable (fun ω => D ω x y) :=
    (measurable_largeContactKernel G hloc L x y).mul (measurable_clusterPairKernel G J x y)
  have hpw (ω : Set E) (x y : V) (hxy : ¬Conn G ω x y) :
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y ≤ A ω x y + A ω y x + D ω x y := by
    have hyx : ¬Conn G ω y x := fun h => hxy (conn_symm G ω h)
    by_cases hx : ((cluster G ω x).ncard:ℝ) < L
    · have ha : A ω x y = clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y := by
        dsimp [A,smallPairKernel]; rw [ite_eq_left ⟨hx,hxy⟩]
      rw [←ha]
      exact le_add_of_le_left (le_add_right le_rfl)
    · by_cases hy : ((cluster G ω y).ncard:ℝ) < L
      · have ha : A ω y x = clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y := by
          dsimp [A,smallPairKernel]; rw [ite_eq_left ⟨hy,hyx⟩,heS ω x y,hJS ω x y]
        rw [←ha]
        exact le_add_of_le_left (le_add_left le_rfl)
      · have hg : L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) := le_min (le_of_not_gt hx) (le_of_not_gt hy)
        have hh : D ω x y = clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y := by
          dsimp [D,largeContactKernel]; rw [ite_eq_left hg]
        rw [←hh]
        exact le_add_left le_rfl
  have ha := contact_smallTwoPoint_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1 c hc hmin p hfin T hT L α C hL hα0 hα1 hI hC d hd
  have hb := clusterPairFunctional_largeContact_bound G hconn hloc root weight Γ hΓ htr hw p hfin T hT L B hB
  calc
    _ ≤ clusterPairFunctional G p root weight (fun ω x y => A ω x y+A ω y x+D ω x y) :=
      clusterPairFunctional_mono_distinct G p root weight _ _ hpw
    _ = (clusterPairFunctional G p root weight A + clusterPairFunctional G p root weight A) + clusterPairFunctional G p root weight D := by
      rw [clusterPairFunctional_add G hloc p root weight (fun ω x y => A ω x y+A ω y x) D (fun x y => (hA x y).add (hA y x)) hD,
        clusterPairFunctional_add G hloc p root weight A (fun ω x y => A ω y x) hA (fun x y => hA y x)]
      rw [contact_smallPairKernel_swap G hconn hloc root weight Γ hΓ htr hw p J hJI L]
    _ ≤ _ := by simpa only [two_mul] using add_le_add (add_le_add ha ha) hb

end MixedTraceTerm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section UniformMixedTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_mixed_trace_bound
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p ≤ pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T →
      ∀ L : ℝ, 1 ≤ L →
        clusterPairFunctional G p root weight (fun ω x y =>
          clusterPairKernel G ω (indexedEdgeKernel G) x y *
          clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y) ≤
        2*ENNReal.ofReal (A*L^(1-α)*(rootTrace root weight (T^3)).re) +
          (ENNReal.ofReal (B*L^((1:ℝ)/2+ε-2*α)))^((1:ℝ)/2) *
          (ENNReal.ofReal (‖T‖^3*(rootTrace root weight (T^3)).re))^((1:ℝ)/2) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  have hfinite : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
    intro x
    obtain ⟨i,a,b,hab,rfl⟩ := hcover x
    exact cluster_finite_ae_covariant G (pc G) hab (root i) (hfin i)
  obtain ⟨C,hC,hCb⟩ := uniform_cluster_power_of_root G hloc (pc G) root hcover α
    (critical_root_power_integrable G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α hα hα1)
  obtain ⟨B,hB,hBb⟩ := critical_contact_square_bound G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  obtain ⟨d,hd,hdg⟩ := exists_degree_bound G hqt
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 < c := Finset.sum_pos (fun i _ => one_div_pos.mpr (hw i)) Finset.univ_nonempty
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  refine ⟨(d:ℝ)*c*C,B,mul_pos (mul_pos (by exact_mod_cast hd) hc) hC,hB,?_⟩
  intro p hp hpq T hT L hL
  have hm (x : V) := cluster_power_mono_integral G hloc x p (pc G) hpq α hα.le (hfinite x) (hCb x).1
  exact clusterPairFunctional_twoPoint_mixed_bound G hconn hloc root weight Γ hΓ htr hcov
    (fun i => (hw i).le) hw1 c hc.le hmin p
    (fun x => cluster_finite_ae_mono G x p (pc G) hpq (hfinite x))
    T hT L α C (by linarith) hα.le (by linarith)
    (fun x => (hm x).1) (fun x => (hm x).2.trans (hCb x).2) d hdg _ (hBb p hp hpq L hL)

end UniformMixedTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionRussoContacts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem closedPivotal_connection_iff (G : BondGraph V E) (ω : Set E) (x y : V) (e : E) :
    ω ∈ closedPivotal {η | Conn G η x y} e ↔
      ¬Conn G ω x y ∧ e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) := by
  constructor
  · rintro ⟨_,hxy,hins⟩
    refine ⟨hxy,?_⟩
    obtain ⟨⟨a,b⟩,hab⟩ := Quot.exists_rep (G e)
    have he : G e = s(a,b) := hab.symm
    rcases (conn_insert_iff G ω e a b x y he).mp hins with h | h | h
    · exact (hxy h).elim
    · exact ⟨a,h.1,b,conn_symm G ω h.2,he⟩
    · exact ⟨b,h.1,a,conn_symm G ω h.2,by rw [he,Sym2.eq_swap]⟩
  · rintro ⟨hxy,a,hxa,b,hyb,he⟩
    have hclosed : e ∉ ω := by
      intro heω
      exact hxy (hxa.trans ((Relation.ReflTransGen.single ⟨e,heω,he⟩).trans (conn_symm G ω hyb)))
    refine ⟨hclosed,hxy,?_⟩
    exact (conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨hxa,conn_symm G ω hyb⟩))

theorem finiteClosedContact_eq_sum (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) :
    finiteClosedContact G Q x y ω =
      ∑ e ∈ Q, if (ω:Set E) ∈ closedPivotal {η | Conn G η x y} e then (1:ℝ) else 0 := by
  have hm (z a : V) : a ∈ finiteRootComponent G ω z ↔ Conn G (ω:Set E) z a := by
    change a ∈ (finiteRootComponent G ω z:Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  simp only [closedPivotal_connection_iff,closedContactSet,Set.mem_ofPred_eq,finiteClosedContact]
  by_cases hxy : Conn G (ω:Set E) x y
  · simp only [hxy,not_true_eq_false,false_and,if_false,Finset.sum_const_zero]
  · rw [ite_eq_left hxy]
    simp only [hxy,not_false_eq_true,true_and,contactBonds,hm,cluster,Set.mem_ofPred_eq]
    rw [Finset.sum_boole]

theorem finite_connection_russo_contacts (G : BondGraph V E) (Q : Finset E)
    (x y : V) (p : ℝ) :
    (1-p)*deriv (finiteEventPolynomial Q {ω | Conn G ω x y}) p =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) p := by
  change (1-p)*deriv (bernoulliPolynomial Q (fun ω => if Conn G (ω:Set E) x y then 1 else 0)) p = _
  rw [closed_difference_russo]
  have he : finiteClosedContact G Q x y = fun (ω : Finset E) =>
      ∑ e ∈ Q, if (ω:Set E) ∈ closedPivotal {η | Conn G η x y} e then (1:ℝ) else 0 :=
    funext (finiteClosedContact_eq_sum G Q x y)
  rw [he,bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply bernoulliPolynomial_congr
  intro ω _
  exact (closedPivotal_difference {η | Conn G η x y}
    (fun _ _ h hc => conn_mono G h hc) e ω).symm

end ConnectionRussoContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactApproximation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClosedContact_eq_full (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x y : V) (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite)
    (Q : Finset E) (hQx : incidentSupport G hloc hx.toFinset ⊆ Q)
    (hQy : incidentSupport G hloc hy.toFinset ⊆ Q) :
    finiteClosedContact G Q x y (domainBits Q ω) = fullLargeContact G x y 0 ω := by
  have hcluster (z : V) (hz : (cluster G ω z).Finite) (hQ : incidentSupport G hloc hz.toFinset ⊆ Q) :
      cluster G (domainBits Q ω:Set E) z = cluster G ω z := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hz.toFinset Q hQ ω z).mpr
      (Set.Finite.coe_toFinset hz).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  have hcx := hcluster x hx hQx
  have hcy := hcluster y hy hQy
  have hFx : finiteRootComponent G (domainBits Q ω) x = hx.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcx,Set.Finite.coe_toFinset]
  have hFy : finiteRootComponent G (domainBits Q ω) y = hy.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcy,Set.Finite.coe_toFinset]
  have hconn : Conn G (domainBits Q ω:Set E) x y ↔ Conn G ω x y := by
    change y ∈ cluster G (domainBits Q ω:Set E) x ↔ y ∈ cluster G ω x
    rw [hcx]
  have hc : (contactBonds G Q hx.toFinset hy.toFinset).card = clusterContactCount G ω x y := by
    rw [←Set.ncard_coe_finset,coe_contactBonds_eq G hloc Q _ _ hQx]
    simp only [Set.Finite.coe_toFinset,clusterContactCount]
  simp only [finiteClosedContact,fullLargeContact,hconn,hFx,hFy,hc,Nat.zero_le,and_true]

theorem finiteClosedContact_nonneg (G : BondGraph V E) (Q : Finset E) (x y : V) (ω : Finset E) :
    0 ≤ finiteClosedContact G Q x y ω := by
  unfold finiteClosedContact
  split_ifs <;> positivity

theorem finiteClosedContact_le_size (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q η : Finset E) (ω : Set E)
    (hη : (η:Set E) ⊆ ω) (x y : V) (hfin : (cluster G ω x).Finite) :
    finiteClosedContact G Q x y η ≤ (d:ℝ)*(cluster G ω x).ncard := by
  have hdQ (z : V) : (Q.filter fun e => z ∈ G e).card ≤ d :=
    (incident_filter_card_le_degree G hloc Q z).trans (hd z)
  have hs : (finiteRootComponent G η x).card ≤ (cluster G ω x).ncard := by
    rw [←Set.ncard_coe_finset,coe_finiteRootComponent]
    exact Set.ncard_le_ncard (fun z hz => conn_mono G hη hz) hfin
  unfold finiteClosedContact
  split_ifs
  · positivity
  · exact_mod_cast (contactBonds_card_le G Q d hdQ _ _).trans
      (Nat.mul_le_mul_left d ((min_le_left _ _).trans hs))



end UniformContactApproximation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ContactRegularity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem fullLargeContact_zero_le_size (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (ω : Set E) (x y : V)
    (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite) :
    fullLargeContact G x y 0 ω ≤ (d:ℝ)*(cluster G ω x).ncard := by
  let Q := incidentSupport G hloc hx.toFinset ∪ incidentSupport G hloc hy.toFinset
  rw [←finiteClosedContact_eq_full G hloc ω x y hx hy Q Finset.subset_union_left Finset.subset_union_right]
  exact finiteClosedContact_le_size G hloc d hd Q (domainBits Q ω) ω
    (by rw [coe_domainBits]; exact Set.inter_subset_left) x y hx

theorem integrable_fullContact_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fullLargeContact G x y 0) (law p) := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  apply ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ)).mono'
    (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
  rw [Real.norm_of_nonneg (fullLargeContact_nonneg G x y 0 ω)]
  exact fullLargeContact_zero_le_size G hloc d hd ω x y hx hy

theorem fullContact_label_integral [Countable E] [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) :
    (∫ labels, fullLargeContact G x y 0 (openEdges labels p) ∂labelLaw) =
      ∫ ω, fullLargeContact G x y 0 ω ∂law p := by
  rw [←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable).symm

theorem fullContact_label_integrable [Countable E] [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) :
    Integrable (fun labels => fullLargeContact G x y 0 (openEdges labels p)) labelLaw ↔
      Integrable (fullLargeContact G x y 0) (law p) := by
  rw [←map_openEdges p]
  exact (integrable_map_measure (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable
    (measurable_openEdges p).aemeasurable).symm

end ContactRegularity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactError
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_clusterSupportIn [Countable V] [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) :
    MeasurableSet {ω : Set E | ClusterSupportIn G Q ω x} := by
  simp only [ClusterSupportIn,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  have he : {ω : Set E | Conn G ω x a → ∀ e, a ∈ G e → e ∈ Q} =
      {ω | ¬Conn G ω x a} ∪ {ω | ∀ e, a ∈ G e → e ∈ Q} := by ext ω; simp only [Set.mem_union,Set.mem_ofPred_eq]; tauto
  rw [he]
  apply (measurableSet_conn G x a).compl.union
  by_cases h : ∀ e, a ∈ G e → e ∈ Q
  · convert (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Set E))) using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    exact h
  · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Set E))) using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    exact h

theorem clusterSupportIn_of_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω : Set E) (x : V) (hx : (cluster G ω x).Finite)
    (hQ : incidentSupport G hloc hx.toFinset ⊆ Q) : ClusterSupportIn G Q ω x := by
  intro a ha e he
  exact hQ ((mem_incidentSupport G hloc hx.toFinset e).mpr ⟨a,hx.mem_toFinset.mpr ha,he⟩)

theorem finiteClosedContact_eq_full_of_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω η : Set E) (hη : η ⊆ ω) (x y : V)
    (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite)
    (hQx : ClusterSupportIn G Q ω x) (hQy : ClusterSupportIn G Q ω y) :
    finiteClosedContact G Q x y (domainBits Q η) = fullLargeContact G x y 0 η := by
  have hsub (z : V) : cluster G η z ⊆ cluster G ω z := fun a ha => conn_mono G hη ha
  have hfx := hx.subset (hsub x)
  have hfy := hy.subset (hsub y)
  apply finiteClosedContact_eq_full G hloc η x y hfx hfy
  · intro e he
    obtain ⟨a,ha,he⟩ := (mem_incidentSupport G hloc hfx.toFinset e).mp he
    exact hQx a (hsub x (hfx.mem_toFinset.mp ha)) e he
  · intro e he
    obtain ⟨a,ha,he⟩ := (mem_incidentSupport G hloc hfy.toFinset e).mp he
    exact hQy a (hsub y (hfy.mem_toFinset.mp ha)) e he

theorem measurable_contactApproxError [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (Q : Finset E) (d : ℕ) (x y : V) :
    Measurable (contactApproxError G Q d x y) := by
  exact measurable_const.ite ((measurableSet_clusterSupportIn G Q x).inter
    (measurableSet_clusterSupportIn G Q y))
    (measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x)))

theorem contactApproxError_nonneg (G : BondGraph V E) (Q : Finset E) (d : ℕ) (x y : V) (ω : Set E) :
    0 ≤ contactApproxError G Q d x y ω := by unfold contactApproxError; split_ifs <;> positivity

theorem contactApproxError_le (G : BondGraph V E) (Q : Finset E) (d : ℕ) (x y : V) (ω : Set E) :
    contactApproxError G Q d x y ω ≤ (d:ℝ)*(cluster G ω x).ncard := by
  unfold contactApproxError; split_ifs <;> first | positivity | exact le_rfl

theorem contact_uniform_error_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q : Finset E) (ω η : Set E)
    (hη : η ⊆ ω) (x y : V) (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite) :
    ‖finiteClosedContact G Q x y (domainBits Q η) - fullLargeContact G x y 0 η‖ ≤
      contactApproxError G Q d x y ω := by
  unfold contactApproxError
  split_ifs with h
  · rw [finiteClosedContact_eq_full_of_support G hloc Q ω η hη x y hx hy h.1 h.2,sub_self,norm_zero]
  · have hsub (z : V) : cluster G η z ⊆ cluster G ω z := fun a ha => conn_mono G hη ha
    have hf := finiteClosedContact_le_size G hloc d hd Q (domainBits Q η) ω
      (by rw [coe_domainBits]; exact Set.inter_subset_left.trans hη) x y hx
    have hg : fullLargeContact G x y 0 η ≤ (d:ℝ)*(cluster G ω x).ncard := by
      exact (fullLargeContact_zero_le_size G hloc d hd η x y (hx.subset (hsub x)) (hy.subset (hsub y))).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Set.ncard_le_ncard (hsub x) hx) (Nat.cast_nonneg _))
    rw [Real.norm_eq_abs,abs_sub_le_iff]
    have hfn := finiteClosedContact_nonneg G Q x y (domainBits Q η)
    have hgn := fullLargeContact_nonneg G x y 0 η
    constructor <;> linarith

end UniformContactError
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactExpectation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_contactApproxError [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (Q : Finset E) (d : ℕ) (x y : V) :
    Integrable (contactApproxError G Q d x y) (law p) := by
  apply ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ)).mono'
    (measurable_contactApproxError G hloc Q d x y).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (contactApproxError_nonneg G Q d x y ω)]; exact contactApproxError_le G Q d x y ω)

theorem contactApproxError_integral_tendsto_zero [Countable V] [Encodable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (d : ℕ) (x y : V) :
    Tendsto (fun n => ∫ ω, contactApproxError G (vertexExhaustion n) d x y ω ∂law p) atTop (nhds 0) := by
  have ht : ∀ᵐ ω ∂law p, Tendsto (fun n => contactApproxError G (vertexExhaustion n) d x y ω) atTop (nhds 0) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
    obtain ⟨nx,hnx⟩ := subset_vertexExhaustion (incidentSupport G hloc hx.toFinset)
    obtain ⟨ny,hny⟩ := subset_vertexExhaustion (incidentSupport G hloc hy.toFinset)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max nx ny)] with n hn
    exact (ite_eq_left ⟨clusterSupportIn_of_incident G hloc _ ω x hx
      (hnx.trans (vertexExhaustion_mono ((le_max_left nx ny).trans hn))),
      clusterSupportIn_of_incident G hloc _ ω y hy
      (hny.trans (vertexExhaustion_mono ((le_max_right nx ny).trans hn)))⟩).symm
  have hh := tendsto_integral_of_dominated_convergence (fun ω : Set E => (d:ℝ)*(cluster G ω x).ncard)
    (fun n => (measurable_contactApproxError G hloc (vertexExhaustion n) d x y).aestronglyMeasurable)
    ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ))
    (fun n => Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (contactApproxError_nonneg G _ d x y ω)]; exact contactApproxError_le G _ d x y ω)) ht
  simpa only [integral_zero] using hh

theorem finiteClosedContact_label_integral [Countable E] (G : BondGraph V E)
    (Q : Finset E) (p : unitInterval) (x y : V) :
    (∫ labels, finiteClosedContact G Q x y (domainBits Q (openEdges labels p)) ∂labelLaw) =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) p := by
  rw [←integral_domainBits Q p (finiteClosedContact G Q x y),←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_finite_local Q (fun ω => finiteClosedContact G Q x y (domainBits Q ω)) (fun ω => by rw [domainBits_local])).aestronglyMeasurable).symm

theorem contactApproxError_label_integral [Countable V] [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (Q : Finset E) (p : unitInterval) (d : ℕ) (x y : V) :
    (∫ labels, contactApproxError G Q d x y (openEdges labels p) ∂labelLaw) =
      ∫ ω, contactApproxError G Q d x y ω ∂law p := by
  rw [←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_contactApproxError G hloc Q d x y).aestronglyMeasurable).symm

theorem contact_expectation_uniform_error [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q : Finset E) (b q : unitInterval)
    (hb : b < pc G) (hq : q ≤ b) (x y : V) :
    ‖bernoulliPolynomial Q (finiteClosedContact G Q x y) q -
      ∫ ω, fullLargeContact G x y 0 ω ∂law q‖ ≤
      ∫ ω, contactApproxError G Q d x y ω ∂law b := by
  have hf : Integrable (fun labels => finiteClosedContact G Q x y (domainBits Q (openEdges labels q))) labelLaw := by
    have hi := integrable_finite_local Q q (fun ω => finiteClosedContact G Q x y (domainBits Q ω))
      (fun ω => by rw [domainBits_local])
    rw [←map_openEdges q] at hi
    exact hi.comp_measurable (measurable_openEdges q)
  have hg := (fullContact_label_integrable G hloc q x y).mpr
    (integrable_fullContact_subcritical G hloc hqt q (hq.trans_lt hb) x y)
  have hi : Integrable (fun labels => contactApproxError G Q d x y (openEdges labels b)) labelLaw := by
    have hh := integrable_contactApproxError G hloc hqt b hb Q d x y
    rw [←map_openEdges b] at hh
    exact hh.comp_measurable (measurable_openEdges b)
  rw [←finiteClosedContact_label_integral G Q q x y,←fullContact_label_integral G hloc q x y,
    ←integral_sub hf hg,←contactApproxError_label_integral G hloc Q b d x y]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hf.sub hg).norm hi
  filter_upwards [label_cluster_finite_ae_subcritical G b hb x,label_cluster_finite_ae_subcritical G b hb y] with labels hx hy
  exact contact_uniform_error_bound G hloc d hd Q _ _ (openEdges_mono labels hq) x y hx hy

end UniformContactExpectation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section PointwiseRussoLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_connection_deriv_eq (G : BondGraph V E) (Q : Finset E)
    (x y : V) (t : ℝ) (ht : t ≠ 1) :
    deriv (finiteEventPolynomial Q {ω | Conn G ω x y}) t =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) t / (1-t) := by
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm ht))).mpr
  rw [mul_comm]
  exact finite_connection_russo_contacts G Q x y t

theorem finite_connection_deriv_tendstoUniformlyOn [Countable V] [Encodable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x y : V) :
    TendstoUniformlyOn (fun n => deriv (finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y}))
      (fun t => realContactExpectation G x y t / (1-t)) atTop (Set.Icc 0 (b:ℝ)) := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  have hb1 : (b:ℝ) < 1 := lt_of_lt_of_le hb (pc G).2.2
  have hden : 0 < 1-(b:ℝ) := sub_pos.mpr hb1
  have ht := (contactApproxError_integral_tendsto_zero G hloc hqt b hb d x y).div_const (1-(b:ℝ))
  rw [zero_div] at ht
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with n hn t ht
  let q : unitInterval := ⟨t,ht.1,ht.2.trans b.2.2⟩
  have hqb : q ≤ b := ht.2
  have hqt1 : t < 1 := ht.2.trans_lt hb1
  have he := contact_expectation_uniform_error G hloc hqt d hd (vertexExhaustion n) b q hb hqb x y
  have hn0 : 0 ≤ ∫ ω, contactApproxError G (vertexExhaustion n) d x y ω ∂law b :=
    integral_nonneg (contactApproxError_nonneg G _ d x y)
  rw [dist_comm,Real.dist_eq,finite_connection_deriv_eq G _ x y t (ne_of_lt hqt1),←sub_div,abs_div,
    abs_of_pos (sub_pos.mpr hqt1)]
  change |bernoulliPolynomial _ _ (q:ℝ) - realContactExpectation G x y (q:ℝ)| / (1-t) < ε
  rw [realContactExpectation_coe]
  apply lt_of_le_of_lt _ hn
  exact div_le_div₀ hn0 (by simpa only [Real.norm_eq_abs] using he) hden (sub_le_sub_left ht.2 1)

theorem finite_connection_polynomial_tendsto_twoPoint [Encodable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Tendsto (fun n => finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y} p)
      atTop (nhds (twoPoint G p x y)) := by
  have ht := finite_connection_polynomial_tendsto G Set.univ (vertexExhaustion (V := E))
    vertexExhaustion_mono (fun _ => Set.subset_univ _) (fun e _ => by
      obtain ⟨n,hn⟩ := subset_vertexExhaustion ({e}:Finset E)
      exact ⟨n,hn (by simp)⟩) p x y
  simpa only [Set.inter_univ,finiteEventPolynomial,Set.mem_ofPred_eq,twoPoint,Measure.real] using ht

 

theorem hasDerivAt_realTwoPoint_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (x y : V) :
    HasDerivAt (realTwoPoint G x y)
      ((∫ ω, fullLargeContact G x y 0 ω ∂law p)/(1-(p:ℝ))) (p:ℝ) := by
  let : Encodable E := Encodable.ofCountable E
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  have hu := (finite_connection_deriv_tendstoUniformlyOn G hloc hqt b hb x y).mono
    (show Set.Ioo 0 (b:ℝ) ⊆ Set.Icc 0 (b:ℝ) from Set.Ioo_subset_Icc_self)
  have hh := hasDerivAt_of_tendstoUniformlyOn (f := fun n => finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y})
    (g := realTwoPoint G x y) (g' := fun t => realContactExpectation G x y t/(1-t)) isOpen_Ioo hu
    (Eventually.of_forall (fun n t _ => by
      change HasDerivAt (bernoulliPolynomial (vertexExhaustion n) (fun (ω : Finset E) => if Conn G (ω:Set E) x y then (1:ℝ) else 0)) _ t
      exact (hasDerivAt_bernoulliPolynomial (vertexExhaustion n)
        (fun (ω : Finset E) => if Conn G (ω:Set E) x y then (1:ℝ) else 0) t).differentiableAt.hasDerivAt))
    (fun t ht => by
      let q : unitInterval := ⟨t,ht.1.le,ht.2.le.trans b.2.2⟩
      simpa only [←realTwoPoint_coe G x y q] using finite_connection_polynomial_tendsto_twoPoint G q x y)
    (show (p:ℝ) ∈ Set.Ioo 0 (b:ℝ) from ⟨hp0,hpb⟩)
  simpa only [realContactExpectation_coe] using hh

end PointwiseRussoLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conn_probability_symm (G : BondGraph V E) (p : unitInterval) (x y : V) :
    law p {ω | Conn G ω x y} = law p {ω | Conn G ω y x} := by
  congr 1
  ext ω
  exact ⟨conn_symm G ω,conn_symm G ω⟩

theorem conn_probability_mono [Countable V] [Countable E] (G : BondGraph V E)
    (p q : unitInterval) (hpq : p ≤ q) (x y : V) :
    law p {ω | Conn G ω x y} ≤ law q {ω | Conn G ω x y} := by
  rw [←ENNReal.ofReal_toReal (measure_ne_top (law p) _),←ENNReal.ofReal_toReal (measure_ne_top (law q) _)]
  exact ENNReal.ofReal_le_ofReal (twoPoint_mono G x y hpq)

theorem fullContact_lintegral_eq_kernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    (∫⁻ ω, ENNReal.ofReal (fullLargeContact G x y 0 ω) ∂law p) =
      ∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω (indexedEdgeKernel G) x y else 0 ∂law p := by
  apply lintegral_congr_ae
  filter_upwards [hx] with ω hω
  by_cases hxy : Conn G ω x y
  · simp only [fullLargeContact,hxy,not_true_eq_false,false_and,if_false,ENNReal.ofReal_zero]
  · rw [ite_eq_left hxy,clusterPairKernel_edge G hloc ω x y hxy hω]
    simp only [fullLargeContact,hxy,Nat.zero_le,not_false_eq_true,and_self,if_true,ENNReal.ofReal_natCast]

theorem fullContact_expectation_le_diagram [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    ENNReal.ofReal (∫ ω, fullLargeContact G x y 0 ω ∂law p) ≤ russoDiagram G p x y := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_fullContact_subcritical G hloc hqt p hp x y)
    (Eventually.of_forall (fullLargeContact_nonneg G x y 0))]
  rw [fullContact_lintegral_eq_kernel G hloc p x y (subcritical_cluster_finite_ae G p hp x)]
  exact clusterPairKernel_distinct_bound G p (indexedEdgeKernel G) x y

theorem russoDiagram_mono [Countable V] [Countable E] (G : BondGraph V E)
    (p q : unitInterval) (hpq : p ≤ q) (x y : V) : russoDiagram G p x y ≤ russoDiagram G q x y := by
  exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
    mul_le_mul_right (mul_le_mul' (conn_probability_mono G p q hpq x a)
      (conn_probability_mono G p q hpq y b)) _))

theorem russoDiagram_symm (G : BondGraph V E) (p : unitInterval) (x y : V) :
    russoDiagram G p x y = russoDiagram G p y x := by
  unfold russoDiagram
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro b
  apply tsum_congr; intro a
  rw [indexedEdgeKernel_symm G a b,mul_comm (law p {ω | Conn G ω x a})]

theorem russoDiagram_row_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ x, ∑' y, law p {ω | Conn G ω x y} ≤ C) (x : V) :
    (∑' y, russoDiagram G p x y) ≤ (d:ℝ≥0∞)*C^2 := by
  unfold russoDiagram
  rw [ENNReal.tsum_comm]
  calc
    _ = ∑' a, ∑' b, indexedEdgeKernel G a b * law p {ω | Conn G ω x a} *
        ∑' y, law p {ω | Conn G ω b y} := by
      apply tsum_congr; intro a
      rw [ENNReal.tsum_comm]
      apply tsum_congr; intro b
      simp_rw [←mul_assoc,conn_probability_symm G p _ b]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' a, ∑' b, indexedEdgeKernel G a b * law p {ω | Conn G ω x a} * C := by
      exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b => mul_le_mul_right (hC b) _))
    _ = ∑' a, (degree G a:ℝ≥0∞) * law p {ω | Conn G ω x a} * C := by
      apply tsum_congr; intro a
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_right,indexedEdgeKernel_row G hloc a]
    _ ≤ ∑' a, (d:ℝ≥0∞) * law p {ω | Conn G ω x a} * C := by
      exact ENNReal.tsum_le_tsum (fun a => mul_le_mul_left (mul_le_mul_left (show (degree G a:ℝ≥0∞) ≤ (d:ℝ≥0∞) by exact_mod_cast hd a) _) _)
    _ = (d:ℝ≥0∞)*(∑' a, law p {ω | Conn G ω x a})*C := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _ ≤ (d:ℝ≥0∞)*C^2 := by
      rw [pow_two,←mul_assoc]
      exact mul_le_mul_left (mul_le_mul_right (hC x) _) _

end RussoDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoMajorant
attribute [local instance] Classical.propDecidable Classical.decEq

theorem russoDiagram_row_ne_top [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x : V) : (∑' y, russoDiagram G b x y) ≠ ⊤ := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  obtain ⟨C,_,hC⟩ := subcritical_ennreal_row_bound G hloc hqt b hb
  exact ne_top_of_le_ne_top (by finiteness) (russoDiagram_row_bound G hloc d hd b _ hC x)

theorem russoDiagram_ne_top [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x y : V) : russoDiagram G b x y ≠ ⊤ :=
  ne_top_of_le_ne_top (russoDiagram_row_ne_top G hloc hqt b hb x) (ENNReal.le_tsum y)

theorem summable_russoMajorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x : V) : Summable (russoMajorant G b x) :=
  (ENNReal.summable_toReal (russoDiagram_row_ne_top G hloc hqt b hb x)).div_const _

theorem russoSlope_nonneg (G : BondGraph V E) (x y : V) (t : ℝ) (ht : t ≤ 1) :
    0 ≤ russoSlope G x y t := by
  exact div_nonneg (integral_nonneg (fullLargeContact_nonneg G x y 0)) (sub_nonneg.mpr ht)

theorem russoMajorant_nonneg (G : BondGraph V E) (b : unitInterval) (x y : V) :
    0 ≤ russoMajorant G b x y := div_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr b.2.2)

theorem russoSlope_le_majorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b p : unitInterval) (hb : b < pc G) (hp : p ≤ b) (x y : V) :
    russoSlope G x y (p:ℝ) ≤ russoMajorant G b x y := by
  have hp' := hp.trans_lt hb
  have he := (fullContact_expectation_le_diagram G hloc hqt p hp' x y).trans (russoDiagram_mono G p b hp x y)
  have hn : 0 ≤ ∫ ω, fullLargeContact G x y 0 ω ∂law p := integral_nonneg (fullLargeContact_nonneg G x y 0)
  have hc : (∫ ω, fullLargeContact G x y 0 ω ∂law p) ≤ (russoDiagram G b x y).toReal := by
    simpa only [ENNReal.toReal_ofReal hn] using ENNReal.toReal_mono (russoDiagram_ne_top G hloc hqt b hb x y) he
  simp only [russoSlope,realContactExpectation_coe,russoMajorant]
  exact div_le_div₀ ENNReal.toReal_nonneg hc (sub_pos.mpr ((show (b:ℝ) < (pc G:ℝ) from hb).trans_le (pc G).2.2)) (sub_le_sub_left (show (p:ℝ) ≤ (b:ℝ) from hp) 1)

theorem hasDerivAt_realTwoPoint_slope [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 (pc G:ℝ)) (x y : V) :
    HasDerivAt (realTwoPoint G x y) (russoSlope G x y t) t := by
  let p : unitInterval := ⟨t, ht.1.le,ht.2.le.trans (pc G).2.2⟩
  change HasDerivAt (realTwoPoint G x y) (russoSlope G x y (p:ℝ)) (p:ℝ)
  simpa only [russoSlope,realContactExpectation_coe] using hasDerivAt_realTwoPoint_subcritical G hloc hqt p ht.1 ht.2 x y

end RussoMajorant
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoRows
attribute [local instance] Classical.propDecidable Classical.decEq

theorem russoMajorant_symm (G : BondGraph V E) (b : unitInterval) (x y : V) :
    russoMajorant G b x y = russoMajorant G b y x := by
  rw [russoMajorant,russoDiagram_symm,russoMajorant]

theorem russoMajorant_uniform_row_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, ∑' y, russoMajorant G b x y ≤ R := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  obtain ⟨C,_,hC⟩ := subcritical_ennreal_row_bound G hloc hqt b hb
  let R : ℝ≥0∞ := (d:ℝ≥0∞)*(ENNReal.ofReal C)^2
  have hR : R ≠ ⊤ := by dsimp [R]; finiteness
  have hden : 0 < 1-(b:ℝ) := sub_pos.mpr ((show (b:ℝ) < (pc G:ℝ) from hb).trans_le (pc G).2.2)
  refine ⟨R.toReal/(1-(b:ℝ)),div_nonneg ENNReal.toReal_nonneg hden.le,fun x => ?_⟩
  simp only [russoMajorant,tsum_div_const]
  rw [←ENNReal.tsum_toReal_eq (russoDiagram_ne_top G hloc hqt b hb x)]
  exact div_le_div_of_nonneg_right (ENNReal.toReal_mono hR (russoDiagram_row_bound G hloc d hd b _ hC x)) hden.le

 

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

theorem summable_russoMajorant_pair [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab : V×V => russoMajorant G p x ab.1 * twoPoint G p ab.1 ab.2) ∧
    Summable (fun ab : V×V => twoPoint G p x ab.1 * russoMajorant G p ab.1 ab.2) := by
  obtain ⟨C,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  have hs := summable_twoPoint_subcritical G hloc hqt p hp
  have hr := summable_russoMajorant G hloc hqt p hp
  obtain ⟨R,_,hR⟩ := russoMajorant_uniform_row_bound G hloc hqt p hp
  exact ⟨summable_kernel_pair _ _ (russoMajorant_nonneg G p) (twoPoint_nonneg G p) hr hs C
    (fun x => (hs x).tsum_le_of_sum_le (hrow x)) x,
    summable_kernel_pair _ _ (twoPoint_nonneg G p) (russoMajorant_nonneg G p) hs hr R hR x⟩

end RussoRows
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RealTriangle
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_triangleMajorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x : V) : Summable (triangleMajorant G b x) := by
  obtain ⟨h₁,h₂⟩ := summable_russoMajorant_pair G hloc hqt b hb x
  have h₃ : Summable (fun ab : V×V => russoMajorant G b x ab.2 * twoPoint G b ab.2 ab.1) := by
    exact h₁.comp_injective (i := fun ab : V×V => (ab.2,ab.1)) (Equiv.prodComm V V).injective
  exact (h₁.add h₂).add h₃

theorem hasDerivAt_realTriangleTerm [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 (pc G:ℝ)) (x : V) (ab : V×V) :
    HasDerivAt (realTriangleTerm G x ab) (realTriangleSlope G x ab t) t := by
  have hs := hasDerivAt_realTwoPoint_slope G hloc hqt t ht
  convert! ((hs x ab.1).mul (hs ab.1 ab.2)).mul (hs ab.2 x) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [realTriangleSlope,Pi.mul_apply]
  ring

theorem realTriangleSlope_nonneg (G : BondGraph V E) (x : V) (ab : V×V) (t : ℝ) (ht : t ≤ 1) :
    0 ≤ realTriangleSlope G x ab t := by
  have hT (a b : V) : 0 ≤ realTwoPoint G a b t := twoPoint_nonneg G _ a b
  dsimp [realTriangleSlope]
  exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (russoSlope_nonneg G _ _ t ht) (hT _ _)) (hT _ _))
    (mul_nonneg (mul_nonneg (hT _ _) (russoSlope_nonneg G _ _ t ht)) (hT _ _)))
    (mul_nonneg (mul_nonneg (hT _ _) (hT _ _)) (russoSlope_nonneg G _ _ t ht))

theorem realTriangleSlope_le_majorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b p : unitInterval) (hb : b < pc G) (hp : p ≤ b) (x : V) (ab : V×V) :
    realTriangleSlope G x ab (p:ℝ) ≤ triangleMajorant G b x ab := by
  have hs := russoSlope_le_majorant G hloc hqt b p hb hp
  have hn := russoSlope_nonneg (G := G)
  have hm (a z : V) : twoPoint G p a z ≤ twoPoint G b a z := twoPoint_mono G a z hp
  simp only [realTriangleSlope,realTwoPoint_coe,triangleMajorant]
  apply add_le_add
  · apply add_le_add
    · calc
        _ ≤ russoMajorant G b x ab.1 * twoPoint G b ab.1 ab.2 * 1 :=
          mul_le_mul (mul_le_mul (hs _ _) (hm _ _) (twoPoint_nonneg G p _ _) (russoMajorant_nonneg G b _ _))
            (twoPoint_le_one G p _ _) (twoPoint_nonneg G p _ _) (mul_nonneg (russoMajorant_nonneg G b _ _) (twoPoint_nonneg G b _ _))
        _ = _ := mul_one _
    · calc
        _ ≤ twoPoint G b x ab.1 * russoMajorant G b ab.1 ab.2 * 1 :=
          mul_le_mul (mul_le_mul (hm _ _) (hs _ _) (hn _ _ _ p.2.2) (twoPoint_nonneg G b _ _))
            (twoPoint_le_one G p _ _) (twoPoint_nonneg G p _ _) (mul_nonneg (twoPoint_nonneg G b _ _) (russoMajorant_nonneg G b _ _))
        _ = _ := mul_one _
  · calc
      _ ≤ 1 * twoPoint G b ab.1 ab.2 * russoMajorant G b ab.2 x :=
        mul_le_mul (mul_le_mul (twoPoint_le_one G p _ _) (hm _ _) (twoPoint_nonneg G p _ _) zero_le_one)
          (hs _ _) (hn _ _ _ p.2.2) (mul_nonneg zero_le_one (twoPoint_nonneg G b _ _))
      _ = _ := by rw [one_mul,twoPoint_symm G b,russoMajorant_symm G b]; ring

end RealTriangle
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



theorem hasDerivAt_realTriangle_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (x : V) :
    HasDerivAt (realTriangle G x) (∑' ab, realTriangleSlope G x ab (p:ℝ)) (p:ℝ) := by
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  apply hasDerivAt_tsum_of_isPreconnected (summable_triangleMajorant G hloc hqt b hb x)
    isOpen_Ioo isPreconnected_Ioo
    (fun ab t ht => hasDerivAt_realTriangleTerm G hloc hqt t ⟨ht.1,lt_trans ht.2 hb⟩ x ab)
    (fun ab t ht => ?_) (show (p:ℝ) ∈ Set.Ioo 0 (b:ℝ) from ⟨hp0,hpb⟩)
    (summable_realTriangleTerm G hloc hqt p hp x) ⟨hp0,hpb⟩
  let q : unitInterval := ⟨t,ht.1.le,ht.2.le.trans b.2.2⟩
  have hq : q ≤ b := ht.2.le
  rw [Real.norm_eq_abs,abs_of_nonneg (realTriangleSlope_nonneg G x ab t q.2.2)]
  exact realTriangleSlope_le_majorant G hloc hqt b q hb hq x ab

theorem hasDerivAt_rootTriangle_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) :
    HasDerivAt (rootTriangle G root weight)
      (∑ i, weight i * ∑' ab, realTriangleSlope G (root i) ab (p:ℝ)) (p:ℝ) := by
  exact HasDerivAt.fun_sum (fun i _ => (hasDerivAt_realTriangle_subcritical G hloc hqt p hp0 hp (root i)).const_mul (weight i))

end TriangleDerivative
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_TraceBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
section RussoOperator
attribute [local instance] Classical.propDecidable Classical.decEq

theorem russoSlope_symm [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (x y : V) :
    russoSlope G x y (p:ℝ) = russoSlope G y x (p:ℝ) := by
  have hh := hasDerivAt_realTwoPoint_slope G hloc hqt p ⟨hp0,hp⟩ x y
  have he : realTwoPoint G x y = realTwoPoint G y x := funext (fun _ => twoPoint_symm G _ x y)
  rw [he] at hh
  exact hh.unique (hasDerivAt_realTwoPoint_slope G hloc hqt p ⟨hp0,hp⟩ y x)

theorem russoSlope_aut [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) :
    russoSlope G (a x) (a y) (p:ℝ) = russoSlope G x y (p:ℝ) := by
  have hh := hasDerivAt_realTwoPoint_slope G hloc hqt p ⟨hp0,hp⟩ (a x) (a y)
  have he : realTwoPoint G (a x) (a y) = realTwoPoint G x y := funext (fun _ => twoPoint_aut G _ hab x y)
  rw [he] at hh
  exact hh.unique (hasDerivAt_realTwoPoint_slope G hloc hqt p ⟨hp0,hp⟩ x y)

 

theorem exists_russoOperator [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) :
    ∃ D : Hilbert V →L[ℂ] Hilbert V,
      ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ) := by
  obtain ⟨R,hR,hrow⟩ := russoMajorant_uniform_row_bound G hloc hqt p hp
  have hb (x : V) (s : Finset V) : ∑ y ∈ s, russoSlope G x y (p:ℝ) ≤ R := by
    calc
      _ ≤ ∑ y ∈ s, russoMajorant G p x y := Finset.sum_le_sum (fun y _ => russoSlope_le_majorant G hloc hqt p p hp le_rfl x y)
      _ ≤ ∑' y, russoMajorant G p x y := Summable.sum_le_tsum s (fun y _ => russoMajorant_nonneg G p x y)
        (summable_russoMajorant G hloc hqt p hp x)
      _ ≤ R := hrow x
  obtain ⟨D,_,hD⟩ := exists_operator_of_row_column_bound (fun x y => russoSlope G x y (p:ℝ)) R hR
    (fun x y => russoSlope_nonneg G x y p p.2.2) hb
    (fun y s => by simpa only [russoSlope_symm G hloc hqt p hp0 hp] using hb y s)
  exact ⟨D,hD⟩

theorem russoOperator_positiveReal (G : BondGraph V E) (p : unitInterval)
    (D : Hilbert V →L[ℂ] Hilbert V)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) : PositiveRealMatrix D := by
  intro x y
  rw [hD x y]
  exact ⟨rfl,russoSlope_nonneg G x y p p.2.2⟩

theorem russoOperator_invariant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (D : Hilbert V →L[ℂ] Hilbert V)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ))
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) : KernelInvariant Γ D := by
  intro a ha x y
  obtain ⟨b,hab⟩ := hΓ ha
  simp only [hD,russoSlope_aut G hloc hqt p hp0 hp hab]

end RussoOperator
end Percolation

 
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

theorem triangleSlope_eq_matrixCoeff (G : BondGraph V E) (p : unitInterval)
    (T D : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) (x : V) :
    (∑' ab, realTriangleSlope G x ab (p:ℝ)) =
      (matrixCoeff (D*T*T + T*D*T + T*T*D) x x).re := by
  have ht := hT.positiveRealMatrix G p T
  have hd := russoOperator_positiveReal G p D hD
  have h₁ := (hd.triple_hasSum ht ht x x)
  have h₂ := (ht.triple_hasSum hd ht x x)
  have h₃ := (ht.triple_hasSum ht hd x x)
  have h := (h₁.add h₂).add h₃
  have ha (A B : Hilbert V →L[ℂ] Hilbert V) : matrixCoeff (A+B) x x = matrixCoeff A x x + matrixCoeff B x x := rfl
  simp only [ha,Complex.add_re]
  simpa only [hD,Complex.ofReal_re,HasKernel.matrixCoeff_re G p T hT,
    realTriangleSlope,realTwoPoint_coe] using h.tsum_eq

end PositiveTriangleSeries
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RootTriangleTraceDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootTrace_triangleSlope_cyclic
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    {Γ : Set (V ≃ V)} (htr : RootTransport root weight Γ)
    (T D : Hilbert V →L[ℂ] Hilbert V) (hT : KernelInvariant Γ T) (hD : KernelInvariant Γ D) :
    rootTrace root weight (D*T*T+T*D*T+T*T*D) = 3*rootTrace root weight (T^2*D) := by
  have h₁ : rootTrace root weight (D*T*T) = rootTrace root weight (T^2*D) := by
    rw [mul_assoc,rootTrace_cyclic root weight htr D (T*T) hD (hT.mul hT),pow_two]
  have h₂ : rootTrace root weight (T*D*T) = rootTrace root weight (T^2*D) := by
    rw [mul_assoc,rootTrace_cyclic root weight htr T (D*T) hT (hD.mul hT),h₁]
  rw [rootTrace_add,rootTrace_add,h₁,h₂,←pow_two]
  ring

 

theorem hasDerivAt_rootTriangle_trace [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (T D : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) :
    HasDerivAt (rootTriangle G root weight) (3*(rootTrace root weight (T^2*D)).re) (p:ℝ) := by
  have hti : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hdi := russoOperator_invariant G hloc hqt p hp0 hp D hD Γ hΓ
  have hs := hasDerivAt_rootTriangle_subcritical G hloc hqt root weight p hp0 hp
  have he : (∑ i, weight i * ∑' ab, realTriangleSlope G (root i) ab (p:ℝ)) =
      3*(rootTrace root weight (T^2*D)).re := by
    simp only [triangleSlope_eq_matrixCoeff G p T D hT hD]
    have hr := congrArg Complex.re (rootTrace_triangleSlope_cyclic root weight htr T D hti hdi)
    simpa only [rootTrace,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] using hr
  exact he ▸ hs

end RootTriangleTraceDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section ContactKernelReroot
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem contactKernel_reroot [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y) =
      ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
        J (root i) y * ENNReal.ofReal (fullLargeContact G (root i) y 0 ω) ∂law p := by
  have ht := clusterPairFunctional_reroot G hconn hloc root weight Γ hΓ htr hw p hfin
    J hJ (fun ω x y => ENNReal.ofReal (fullLargeContact G x y 0 ω))
    (fun x y => (measurable_fullLargeContact G hloc x y 0).ennreal_ofReal)
    (fun ω x y a b hxa hyb => congrArg ENNReal.ofReal (fullLargeContact_cluster_constant G ω 0 x y a b hxa hyb))
    (fun a _ b hab ω x y => congrArg ENNReal.ofReal (fullLargeContact_aut G hab ω x y 0))
  simp_rw [fullLargeContact_distinct] at ht
  rw [←ht]
  unfold clusterPairFunctional
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hfin (root i)] with ω hω
  unfold clusterPairDensity
  congr 1
  apply tsum_congr
  intro y
  congr 1
  by_cases hd : Conn G ω (root i) y
  · simp only [hd,not_true_eq_false,if_false]
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [clusterPairKernel_edge G hloc ω (root i) y hd hω]
    simp only [fullLargeContact,hd,not_false_eq_true,Nat.zero_le,and_self,if_true,ENNReal.ofReal_natCast]
    exact mul_comm _ _

theorem contact_lintegral_eq_russoOperator [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Hilbert V →L[ℂ] Hilbert V)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) (x y : V) :
    (∫⁻ ω, ENNReal.ofReal (fullLargeContact G x y 0 ω) ∂law p) =
      ENNReal.ofReal (1-(p:ℝ)) * ennMatrixCoeff D x y := by
  rw [←ofReal_integral_eq_lintegral_ofReal (integrable_fullContact_subcritical G hloc hqt p hp x y)
    (Eventually.of_forall (fullLargeContact_nonneg G x y 0))]
  simp only [ennMatrixCoeff,hD,Complex.ofReal_re,russoSlope,realContactExpectation_coe]
  rw [←ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)]
  congr 1
  have hd : 1-(p:ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr ((show (p:ℝ) < (pc G:ℝ) from hp).trans_le (pc G).2.2))
  exact (mul_div_cancel₀ _ hd).symm

end ContactKernelReroot
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section MixedRussoTrace
attribute [local instance] Classical.propDecidable Classical.decEq

theorem mixedFunctional_eq_russoTrace [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (J D : Hilbert V →L[ℂ] Hilbert V) (hJ : PositiveRealMatrix J) (hiJ : KernelInvariant Γ J)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω (ennMatrixCoeff J) x y) =
      ENNReal.ofReal ((1-(p:ℝ))*(rootTrace root weight (J*D)).re) := by
  have hd := russoOperator_positiveReal G p D hD
  have hdi (x y : V) : ennMatrixCoeff D x y = ennMatrixCoeff D y x := by
    simp only [ennMatrixCoeff,hD,Complex.ofReal_re,russoSlope_symm G hloc hqt p hp0 hp x y]
  have hji : ∀ a ∈ Γ, ∀ x y, ennMatrixCoeff J (a x) (a y) = ennMatrixCoeff J x y := by
    intro a ha x y; unfold ennMatrixCoeff; rw [hiJ a ha]
  rw [contactKernel_reroot G hconn hloc root weight Γ hΓ htr hw p
    (subcritical_cluster_finite_ae G p hp) (ennMatrixCoeff J) hji]
  have he (x : V) : (∫⁻ ω, ∑' y, ennMatrixCoeff J x y * ENNReal.ofReal (fullLargeContact G x y 0 ω) ∂law p) =
      ENNReal.ofReal (1-(p:ℝ)) * ennMatrixCoeff (J*D) x x := by
    have hm (y : V) : Measurable (fun ω : Set E => ennMatrixCoeff J x y * ENNReal.ofReal (fullLargeContact G x y 0 ω)) :=
      (measurable_const : Measurable (fun _ : Set E => ennMatrixCoeff J x y)).mul
        (measurable_fullLargeContact G hloc x y 0).ennreal_ofReal
    rw [lintegral_tsum (fun y => (hm y).aemeasurable)]
    simp_rw [lintegral_const_mul _ (measurable_fullLargeContact G hloc x _ 0).ennreal_ofReal,
      contact_lintegral_eq_russoOperator G hloc hqt p hp D hD]
    rw [ennMatrixCoeff_mul hJ hd,←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro y
    rw [hdi x y]
    ac_rfl
  simp_rw [he]
  rw [ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2),←enn_rootTrace root weight hw (J*D) (hJ.mul hd),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

theorem mixedFunctional_toReal_eq_russoTrace [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (J D : Hilbert V →L[ℂ] Hilbert V) (hJ : PositiveRealMatrix J) (hiJ : KernelInvariant Γ J)
    (hD : ∀ x y, matrixCoeff D x y = (russoSlope G x y (p:ℝ):ℂ)) :
    (clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω (ennMatrixCoeff J) x y)).toReal =
      (1-(p:ℝ))*(rootTrace root weight (J*D)).re := by
  rw [mixedFunctional_eq_russoTrace G hconn hloc hqt root weight Γ hΓ htr hw p hp0 hp J D hJ hiJ hD]
  apply ENNReal.toReal_ofReal
  apply mul_nonneg (sub_nonneg.mpr p.2.2)
  have hd := hJ.mul (russoOperator_positiveReal G p D hD)
  simp only [rootTrace,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hd _ _).2)

end MixedRussoTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RootTriangleRusso
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem rootTriangle_russo [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) :
    (1-(p:ℝ))*deriv (rootTriangle G root weight) (p:ℝ) =
      3*(clusterPairFunctional G p root weight (fun ω x y =>
        clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y)).toReal := by
  obtain ⟨D,hD⟩ := exists_russoOperator G hloc hqt p hp0 hp
  have hi : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  rw [(hasDerivAt_rootTriangle_trace G hloc hqt root weight Γ hΓ htr p hp0 hp T D hT hD).deriv,
    mixedFunctional_toReal_eq_russoTrace G hconn hloc hqt root weight Γ hΓ htr hw p hp0 hp
      (T^2) D ((hT.positiveRealMatrix G p T).pow 2) (hi.pow 2) hD]
  ring

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
open MeasureTheory
open scoped ENNReal
section RealMixedTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem critical_mixed_trace_bound_real
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T →
      ∀ L : ℝ, 1 ≤ L →
        (clusterPairFunctional G p root weight (fun ω x y =>
          clusterPairKernel G ω (indexedEdgeKernel G) x y *
          clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y)).toReal ≤
        2*(A*L^(1-α)*rootTriangle G root weight (p:ℝ)) +
          (B*L^((1:ℝ)/2+ε-2*α))^((1:ℝ)/2) *
          (‖T‖^3*rootTriangle G root weight (p:ℝ))^((1:ℝ)/2) := by
  obtain ⟨A,B,hA,hB,hb⟩ := critical_mixed_trace_bound G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  refine ⟨A,B,hA,hB,?_⟩
  intro p hp hpq T hT L hL
  have ht : 0 ≤ rootTriangle G root weight (p:ℝ) := (rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 p hpq).trans' (by norm_num)
  have ha : 0 ≤ A*L^(1-α)*rootTriangle G root weight (p:ℝ) := mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _)) ht
  have hc : 0 ≤ B*L^((1:ℝ)/2+ε-2*α) := mul_nonneg hB.le (Real.rpow_nonneg (by linarith) _)
  have hn : 0 ≤ ‖T‖^3*rootTriangle G root weight (p:ℝ) := mul_nonneg (pow_nonneg (norm_nonneg _) _) ht
  have hb' := hb p hp hpq.le T hT L hL
  rw [←rootTriangle_eq_trace G p root weight T hT] at hb'
  have htop : 2*ENNReal.ofReal (A*L^(1-α)*rootTriangle G root weight (p:ℝ)) +
      (ENNReal.ofReal (B*L^((1:ℝ)/2+ε-2*α)))^((1:ℝ)/2) *
      (ENNReal.ofReal (‖T‖^3*rootTriangle G root weight (p:ℝ)))^((1:ℝ)/2) ≠ ⊤ := by finiteness
  have hh := ENNReal.toReal_mono htop hb'
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hh
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofNat,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hc,ENNReal.toReal_ofReal hn] using hh

end RealMixedTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceNumerics
attribute [local instance] Classical.propDecidable Classical.decEq


lemma sqrt_mixed_power (B L m a r : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hm : 0 ≤ m) (ha : 0 ≤ a) :
    (B*L^r)^((1:ℝ)/2) * (m^3*a)^((1:ℝ)/2) =
      Real.sqrt B * L^(r/2) * m^((3:ℝ)/2) * Real.sqrt a := by
  rw [Real.mul_rpow hB (Real.rpow_nonneg hL _), Real.mul_rpow (pow_nonneg hm _) ha,
    ←Real.rpow_mul hL,←Real.rpow_natCast m 3,←Real.rpow_mul hm,
    ←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
  rw [show r*(1/2:ℝ) = r/2 by ring]
  norm_num only [Nat.cast_ofNat]
  ring

lemma sqrt_derivative_estimate (p q A B L m a a' F : ℝ)
    (hp : p ≤ q) (hq : q < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 1 ≤ L) (hm : 0 ≤ m) (ha : 1 ≤ a)
    (α r : ℝ) (hid : (1-p)*a' = 3*F)
    (hF : F ≤ 2*(A*L^(1-α)*a) + (B*L^r)^((1:ℝ)/2)*(m^3*a)^((1:ℝ)/2)) :
    a'/(2*Real.sqrt a) ≤
      (3*(A+Real.sqrt B)/(1-q))*L^(1-α)*Real.sqrt a +
      (3*(A+Real.sqrt B)/(1-q))*L^(r/2)*m^((3:ℝ)/2) := by
  have ha0 : 0 < a := by linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hp1 : 0 < 1-p := by linarith
  have hq1 : 0 < 1-q := by linarith
  have he := Real.sq_sqrt ha0.le
  have hL0 : 0 ≤ L := by linarith
  rw [sqrt_mixed_power B L m a r hB hL0 hm ha0.le] at hF
  have hu : 0 ≤ L^(1-α) := Real.rpow_nonneg hL0 _
  have hv : 0 ≤ L^(r/2)*m^((3:ℝ)/2) := mul_nonneg (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hm _)
  have hB0 := Real.sqrt_nonneg B
  have hcoef : 3*A/(1-p) ≤ 3*(A+Real.sqrt B)/(1-q) := by
    apply (div_le_div_iff₀ hp1 hq1).mpr
    nlinarith
  have hcoef2 : 3*Real.sqrt B/(2*(1-p)) ≤ 3*(A+Real.sqrt B)/(1-q) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hp1) hq1).mpr
    nlinarith
  have hbase : a'/(2*Real.sqrt a) ≤ 3*A/(1-p)*L^(1-α)*Real.sqrt a +
      (3*Real.sqrt B/(2*(1-p)))*(L^(r/2)*m^((3:ℝ)/2)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hs)).mpr
    apply (mul_le_mul_iff_right₀ hp1).mp
    have hex : (3*A/(1-p)*L^(1-α)*Real.sqrt a +
        (3*Real.sqrt B/(2*(1-p)))*(L^(r/2)*m^((3:ℝ)/2))) * (2*Real.sqrt a) * (1-p) =
        3*(2*(A*L^(1-α)*a) + Real.sqrt B*L^(r/2)*m^((3:ℝ)/2)*Real.sqrt a) := by
      field_simp
      ring_nf
      rw [he]
      ring
    rw [hid,mul_comm (1-p) _,hex]
    linarith
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hu) hs.le)
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef2 hv))

end TraceNumerics
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TraceSquareRoot
attribute [local instance] Classical.propDecidable Classical.decEq

theorem hasDerivAt_rootTriangleSqrt [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) :
    HasDerivAt (rootTriangleSqrt G root weight)
      (deriv (rootTriangle G root weight) (p:ℝ) / (2*rootTriangleSqrt G root weight (p:ℝ))) (p:ℝ) := by
  apply (hasDerivAt_rootTriangle_subcritical G hloc hqt root weight p hp0 hp).differentiableAt.hasDerivAt.sqrt
  have hh := rootTriangle_one_le G hloc hqt root weight hw hw1 p hp
  linarith

 
theorem critical_rootTriangleSqrt_derivative_bs_oai
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T →
      ∀ L : ℝ, 1 ≤ L →
        deriv (rootTriangleSqrt G root weight) (p:ℝ) ≤
        C*L^(1-α)*rootTriangleSqrt G root weight (p:ℝ) +
          C*L^(((1:ℝ)/2+ε-2*α)/2)*‖T‖^((3:ℝ)/2) := by
  obtain ⟨A,B,hA,hB,hb⟩ := critical_mixed_trace_bound_real G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  refine ⟨3*(A+Real.sqrt B)/(1-(pc G:ℝ)),div_pos (mul_pos (by norm_num)
    (add_pos_of_pos_of_nonneg hA (Real.sqrt_nonneg B))) (sub_pos.mpr hp₁),?_⟩
  intro p hp hpq T hT L hL
  have hp0 : 0 < (p:ℝ) := lt_of_lt_of_le (half_pos hp₀) hp
  rw [(hasDerivAt_rootTriangleSqrt G hloc hqt root weight (fun i => (hw i).le) hw1 p hp0 hpq).deriv]
  exact sqrt_derivative_estimate p (pc G) A B L ‖T‖ (rootTriangle G root weight p)
    (deriv (rootTriangle G root weight) p) _ hpq.le hp₁ hA.le hB.le hL (norm_nonneg _)
    (rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 p hpq) α _
    (rootTriangle_russo G hconn hloc hqt root weight Γ hΓ htr (fun i => (hw i).le) p hp0 hpq T hT)
    (hb p hp hpq T hT L hL)

end TraceSquareRoot
end Percolation


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.critical_rootTriangleSqrt_derivative_bs_oai.{u, v, u_1} := @OAI.Percolation.critical_rootTriangleSqrt_derivative_bs_oai.{u, v, u_1}
