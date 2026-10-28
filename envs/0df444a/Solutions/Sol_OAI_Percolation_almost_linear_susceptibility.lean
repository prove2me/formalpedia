-- Prove2me | solution 1 for OAI.Percolation.almost_linear_susceptibility
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T00:54:49.268615+00:00
-- url     : https://prove2.me/submissions/b21d75f1-7bc1-4b43-8cb7-f6d8bdf3008c

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_critical_root_power_integrable

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

section CouplingOrder
variable [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
theorem measurable_openEdges (p : unitInterval) :
    Measurable (fun labels : E → unitInterval => openEdges labels p) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_threshold p).comp (measurable_pi_apply e)))

omit [Countable E] in
theorem openEdges_mono (labels : E → unitInterval) : Monotone (openEdges labels) := by
  intro p q hpq e he
  exact he.trans hpq

end CouplingOrder

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

section ORLift
attribute [local instance] Classical.propDecidable

instance bitLaw_isProbabilityMeasure (q : unitInterval) : IsProbabilityMeasure (bitLaw q) := by
  rw [bitLaw, ← map_threshold q]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)


end ORLift

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

end SharpnessBridge

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

section LabelledExploration
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem bernoulliPolynomial_affine (s : Finset E) (f g : Finset E → ℝ) (a b p : ℝ) :
    bernoulliPolynomial s (fun t => a*f t+b*g t) p =
      a*bernoulliPolynomial s f p+b*bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> ring

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


end GraphMarkedSearch

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

end GoodnessLaw

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

end ClusterResampling
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedConnectionLimit
attribute [local instance] Classical.propDecidable Classical.decEq

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

end RestrictedConnectionLimit
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicBall
attribute [local instance] Classical.propDecidable Classical.decEq


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
section DistinctClusterMoments
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_ncard_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
  rw [←cluster_aut G hab,Set.ncard_image_of_injective _ a.injective]

end DistinctClusterMoments
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Susceptibility
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
          simp only [hm,hn,ite_false,ite_true,sub_self]
        · have hy := (he m).mpr hm
          simp only [hm,hy,ite_false,ite_true,sub_zero]
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



end MarkedConnectionLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_FractionalMoments
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
variable {E : Type v}
section DecisionCovarianceAlgebra
attribute [local instance] Classical.propDecidable Classical.decEq

theorem bernoulliPolynomial_abs (Q : Finset E) (p : unitInterval) (f : Finset E → ℝ) :
    |bernoulliPolynomial Q f p| ≤ bernoulliPolynomial Q (fun ω => |f ω|) p := by
  rw [abs_le]
  constructor
  · have h := bernoulliPolynomial_mono Q (fun ω => -|f ω|) f p p.2
      (fun _ _ => neg_abs_le _)
    have he : bernoulliPolynomial Q (fun ω => -|f ω|) p =
        -bernoulliPolynomial Q (fun ω => |f ω|) p := by
      simp only [bernoulliPolynomial,neg_mul,Finset.sum_neg_distrib]
    rwa [he] at h
  · exact bernoulliPolynomial_mono Q f (fun ω => |f ω|) p p.2 (fun _ _ => le_abs_self _)

theorem coordinateVariation_nonneg (Q : Finset E) (p : unitInterval) (f : Finset E → ℝ) (e : E) :
    0 ≤ coordinateVariation Q p f e :=
  bernoulliPolynomial_nonneg _ _ p p.2 (fun _ _ => abs_nonneg _)

 
theorem finiteCovariance_first_coordinate (S : Finset E) (e : E) (he : e ∉ S)
    (p : ℝ) (f g : Finset E → ℝ) :
    finiteCovariance (insert e S) p f g =
      (1-p)*finiteCovariance S p (coordinateAverage e p f) g +
      p*finiteCovariance S p (coordinateAverage e p f) (fun ω => g (insert e ω)) +
      p*(1-p)*bernoulliPolynomial S
        (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p := by
  unfold finiteCovariance
  rw [bernoulliPolynomial_insert S e he,bernoulliPolynomial_insert S e he,
    bernoulliPolynomial_insert S e he]
  have hav := bernoulliPolynomial_affine S f (fun ω => f (insert e ω)) (1-p) p p
  change bernoulliPolynomial S (coordinateAverage e p f) p = _ at hav
  rw [hav]
  have h0 : bernoulliPolynomial S (fun ω => coordinateAverage e p f ω*g ω) p =
      (1-p)*bernoulliPolynomial S (fun ω => f ω*g ω) p+
      p*bernoulliPolynomial S (fun ω => f (insert e ω)*g ω) p := by
    simpa only [coordinateAverage,add_mul,mul_assoc] using
      bernoulliPolynomial_affine S (fun ω => f ω*g ω) (fun ω => f (insert e ω)*g ω) (1-p) p p
  have h1 : bernoulliPolynomial S (fun ω => coordinateAverage e p f ω*g (insert e ω)) p =
      (1-p)*bernoulliPolynomial S (fun ω => f ω*g (insert e ω)) p+
      p*bernoulliPolynomial S (fun ω => f (insert e ω)*g (insert e ω)) p := by
    simpa only [coordinateAverage,add_mul,mul_assoc] using
      bernoulliPolynomial_affine S (fun ω => f ω*g (insert e ω)) (fun ω => f (insert e ω)*g (insert e ω)) (1-p) p p
  rw [h0,h1]
  have herr : bernoulliPolynomial S (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p =
      bernoulliPolynomial S (fun ω => f (insert e ω)*g (insert e ω)) p-
      bernoulliPolynomial S (fun ω => f (insert e ω)*g ω) p-
      bernoulliPolynomial S (fun ω => f ω*g (insert e ω)) p+
      bernoulliPolynomial S (fun ω => f ω*g ω) p := by
    simp only [bernoulliPolynomial]
    simp only [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [herr]
  ring

end DecisionCovarianceAlgebra
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section CoordinateAveragingBounds
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem coordinateVariation_average_le (S : Finset E) (e j : E) (he : e ∉ S) (hje : j ≠ e)
    (p : unitInterval) (f : Finset E → ℝ) :
    coordinateVariation S p (coordinateAverage e p f) j ≤ coordinateVariation (insert e S) p f j := by
  unfold coordinateVariation
  rw [Finset.erase_insert_of_ne hje.symm,bernoulliPolynomial_insert _ e (by simp [he])]
  let f₀ := fun ω : Finset E => |f (insert j ω)-f ω|
  let f₁ := fun ω : Finset E => |f (insert j (insert e ω))-f (insert e ω)|
  change _ ≤ (1-(p:ℝ))*bernoulliPolynomial (S.erase j) f₀ p+
    (p:ℝ)*bernoulliPolynomial (S.erase j) f₁ p
  rw [←bernoulliPolynomial_affine]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  have hid : coordinateAverage e p f (insert j ω)-coordinateAverage e p f ω =
      (1-(p:ℝ))*(f (insert j ω)-f ω)+(p:ℝ)*(f (insert j (insert e ω))-f (insert e ω)) := by
    simp only [coordinateAverage,Finset.insert_comm e j]
    ring
  rw [hid]
  calc
    _ ≤ |(1-(p:ℝ))*(f (insert j ω)-f ω)|+|(p:ℝ)*(f (insert j (insert e ω))-f (insert e ω))| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr p.2.2),abs_of_nonneg p.2.1]

 

theorem finiteCovariance_first_bound (S : Finset E) (e : E) (he : e ∉ S)
    (p : unitInterval) (f g : Finset E → ℝ)
    (hg : ∀ ω ⊆ insert e S, g ω ∈ Set.Icc (0:ℝ) 1) :
    |finiteCovariance (insert e S) p f g| ≤
      (1-(p:ℝ))*|finiteCovariance S p (coordinateAverage e p f) g|+
      (p:ℝ)*|finiteCovariance S p (coordinateAverage e p f) (fun ω => g (insert e ω))|+
      (p:ℝ)*(1-(p:ℝ))*coordinateVariation (insert e S) p f e := by
  have hgood : |bernoulliPolynomial S (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p| ≤
      coordinateVariation (insert e S) p f e := by
    apply (bernoulliPolynomial_abs S p _).trans
    unfold coordinateVariation
    rw [Finset.erase_insert he]
    apply bernoulliPolynomial_mono _ _ _ p p.2
    intro ω hω
    rw [abs_mul]
    have h₀ := hg ω (hω.trans (Finset.subset_insert _ _))
    have h₁ := hg (insert e ω) (Finset.insert_subset_insert e hω)
    have hd : |g (insert e ω)-g ω| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h₀.1,h₀.2,h₁.1,h₁.2]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (abs_nonneg (f (insert e ω)-f ω))
  rw [finiteCovariance_first_coordinate S e he]
  calc
    _ ≤ |(1-(p:ℝ))*finiteCovariance S p (coordinateAverage e p f) g+
          (p:ℝ)*finiteCovariance S p (coordinateAverage e p f) (fun ω => g (insert e ω))|+
        |(p:ℝ)*(1-(p:ℝ))*bernoulliPolynomial S (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p| := abs_add_le _ _
    _ ≤ |(1-(p:ℝ))*finiteCovariance S p (coordinateAverage e p f) g|+
          |(p:ℝ)*finiteCovariance S p (coordinateAverage e p f) (fun ω => g (insert e ω))|+
        |(p:ℝ)*(1-(p:ℝ))*bernoulliPolynomial S (fun ω => (f (insert e ω)-f ω)*(g (insert e ω)-g ω)) p| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr p.2.2),abs_of_nonneg p.2.1,
        abs_of_nonneg (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2))]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgood (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)))

end CoordinateAveragingBounds
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section EdgeDecisionTrees
attribute [local instance] Classical.propDecidable Classical.decEq


namespace EdgeQueryTree

theorem value_mem (t : EdgeQueryTree E) (ω : Finset E) : t.value ω ∈ Set.Icc (0:ℝ) 1 := by
  unfold value
  split <;> simp

theorem revealment_nonneg (p : unitInterval) (i : E) (t : EdgeQueryTree E) : 0 ≤ t.revealment p i := by
  induction t with
  | done => rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    simp only [revealment]
    split_ifs
    · norm_num
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.2.2) ih₀) (mul_nonneg p.2.1 ih₁)

theorem eval_congr (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {ω η : Finset E} (h : ∀ e ∈ Q, e ∈ ω ↔ e ∈ η) : t.eval ω = t.eval η := by
  induction t generalizing Q with
  | done => rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    simp only [eval,h e ht.1]
    split
    · exact ih₁ ht.2.2 (fun a ha => h a (Finset.mem_of_mem_erase ha))
    · exact ih₀ ht.2.1 (fun a ha => h a (Finset.mem_of_mem_erase ha))

theorem eval_insert (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {e : E} (he : e ∉ Q) (ω : Finset E) : t.eval (insert e ω) = t.eval ω := by
  apply eval_congr t ht
  intro a ha
  simp [show a ≠ e from fun h => he (h ▸ ha)]

theorem reads_congr (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {ω η : Finset E} (h : ∀ e ∈ Q, e ∈ ω ↔ e ∈ η) (i : E) : t.reads ω i ↔ t.reads η i := by
  induction t generalizing Q with
  | done => rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    simp only [reads,h e ht.1]
    split
    · rw [ih₁ ht.2.2 (fun a ha => h a (Finset.mem_of_mem_erase ha))]
    · rw [ih₀ ht.2.1 (fun a ha => h a (Finset.mem_of_mem_erase ha))]

end EdgeQueryTree
end EdgeDecisionTrees
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section EdgeTreeCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteCovariance_congr_right (Q : Finset E) (p : ℝ) (f : Finset E → ℝ)
    {g h : Finset E → ℝ} (he : ∀ ω ⊆ Q, g ω = h ω) :
    finiteCovariance Q p f g = finiteCovariance Q p f h := by
  unfold finiteCovariance
  rw [bernoulliPolynomial_congr Q (fun ω hω => congrArg (f ω * ·) (he ω hω)),
    bernoulliPolynomial_congr Q he]

namespace EdgeQueryTree

 

theorem covariance_bound (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (f : Finset E → ℝ) :
    |finiteCovariance Q p f t.value| ≤
      ∑ i ∈ Q, t.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
  induction t generalizing Q f with
  | done b =>
    have hv : (done b : EdgeQueryTree E).value = (fun _ => if b then (1:ℝ) else 0) := rfl
    rw [hv]
    cases b
    · simp [finiteCovariance,revealment]
    · simp [finiteCovariance,revealment,bernoulliPolynomial_const]
  | query e t₀ t₁ ih₀ ih₁ =>
    have he := ht.1
    have heS : e ∉ Q.erase e := Finset.notMem_erase _ _
    have hQ : insert e (Q.erase e) = Q := Finset.insert_erase he
    let fav := coordinateAverage e (p:ℝ) f
    have hcov₀ : finiteCovariance (Q.erase e) p fav (query e t₀ t₁).value =
        finiteCovariance (Q.erase e) p fav t₀.value := by
      apply finiteCovariance_congr_right
      intro ω hω
      have heω : e ∉ ω := fun h => heS (hω h)
      simp only [value,eval,ite_eq_right heω]
    have hcov₁ : finiteCovariance (Q.erase e) p fav (fun ω => (query e t₀ t₁).value (insert e ω)) =
        finiteCovariance (Q.erase e) p fav t₁.value := by
      apply finiteCovariance_congr_right
      intro ω _
      simp only [value,eval,Finset.mem_insert_self,ite_true,eval_insert t₁ ht.2.2 heS]
    have hav (i : E) (hi : i ∈ Q.erase e) :
        coordinateVariation (Q.erase e) p fav i ≤ coordinateVariation Q p f i := by
      simpa only [hQ] using coordinateVariation_average_le (Q.erase e) e i heS
        (Finset.ne_of_mem_erase hi) p f
    have hb₀ : |finiteCovariance (Q.erase e) p fav t₀.value| ≤
        ∑ i ∈ Q.erase e, t₀.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
      apply (ih₀ ht.2.1 fav).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hav i hi) (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)))
        (revealment_nonneg p i t₀)
    have hb₁ : |finiteCovariance (Q.erase e) p fav t₁.value| ≤
        ∑ i ∈ Q.erase e, t₁.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
      apply (ih₁ ht.2.2 fav).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hav i hi) (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)))
        (revealment_nonneg p i t₁)
    have hfirst := finiteCovariance_first_bound (Q.erase e) e heS p f (query e t₀ t₁).value
      (fun ω _ => value_mem _ ω)
    change _ ≤ (1-(p:ℝ))*|finiteCovariance (Q.erase e) p fav (query e t₀ t₁).value|+
      (p:ℝ)*|finiteCovariance (Q.erase e) p fav (fun ω => (query e t₀ t₁).value (insert e ω))|+_ at hfirst
    rw [hQ,hcov₀,hcov₁] at hfirst
    apply hfirst.trans
    calc
      _ ≤ (1-(p:ℝ))*(∑ i ∈ Q.erase e, t₀.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i))+
          (p:ℝ)*(∑ i ∈ Q.erase e, t₁.revealment p i * ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i))+
          (p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f e :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb₀ (sub_nonneg.mpr p.2.2))
          (mul_le_mul_of_nonneg_left hb₁ p.2.1)) le_rfl
      _ = _ := by
        rw [←Finset.sum_erase_add _ _ he]
        congr 1
        · rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [revealment,ite_eq_right (Finset.ne_of_mem_erase hi)]
          ring
        · simp [revealment]

end EdgeQueryTree
end EdgeTreeCovariance
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section RevealmentProbability
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

theorem reads_insert (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {e : E} (he : e ∉ Q) (ω : Finset E) (i : E) : t.reads (insert e ω) i ↔ t.reads ω i := by
  apply reads_congr t ht
  intro a ha
  simp [show a ≠ e from fun h => he (h ▸ ha)]

 
theorem revealment_eq_probability (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : ℝ) (i : E) :
    t.revealment p i = bernoulliPolynomial Q (fun ω => if t.reads ω i then 1 else 0) p := by
  induction t generalizing Q with
  | done => simp [revealment,reads]
  | query e t₀ t₁ ih₀ ih₁ =>
    by_cases hie : i = e
    · subst i
      simp [revealment,reads,bernoulliPolynomial_const]
    · have heS : e ∉ Q.erase e := Finset.notMem_erase _ _
      conv_rhs => rw [←Finset.insert_erase ht.1]
      rw [bernoulliPolynomial_insert _ e heS]
      simp only [revealment,ite_eq_right hie]
      rw [ih₀ ht.2.1,ih₁ ht.2.2]
      congr 1
      · congr 1
        apply bernoulliPolynomial_congr
        intro ω hω
        have heω : e ∉ ω := fun h => heS (hω h)
        simp only [reads,hie,false_or,ite_eq_right heω]
      · congr 1
        apply bernoulliPolynomial_congr
        intro ω _
        simp only [reads,hie,false_or,Finset.mem_insert_self,ite_true,reads_insert t₁ ht.2.2 heS]

end EdgeQueryTree
end RevealmentProbability
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeededEdgeSearch
attribute [local instance] Classical.propDecidable Classical.decEq



theorem seededEdgeSearch_valid (G : BondGraph V E) (x : V) (n : ℕ) (Q : Finset E) (R : Finset V) :
    (seededEdgeSearch G x n Q R).Valid Q := by
  induction n generalizing Q R with
  | zero => trivial
  | succ n ih =>
    simp only [seededEdgeSearch]
    split_ifs with hc
    · exact ⟨(searchCrossing_spec G Q R hc).1,ih _ _,ih _ _⟩
    · trivial

theorem seedMarked_singleton_of_no_crossing (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (x : V) (h : ¬ SearchCrossing G Q R) (ω : Finset E) (hω : ω ⊆ Q) :
    SeedMarked G (ω : Set E) R {x} ↔ x ∈ R := by
  constructor
  · intro hx
    by_contra hn
    exact seedMarked_false_of_no_crossing G Q R {x} h (by simpa using hn) ω hω hx
  · intro hx
    exact ⟨x,hx,x,Finset.mem_singleton_self x,conn_refl G _ x⟩

 
theorem seededEdgeSearch_correct (G : BondGraph V E) (x : V) (n : ℕ) (Q : Finset E) (R : Finset V)
    (hn : Q.card ≤ n) (ω : Finset E) (hω : ω ⊆ Q) :
    (seededEdgeSearch G x n Q R).eval ω = true ↔ SeedMarked G (ω : Set E) R {x} := by
  induction n generalizing Q R ω with
  | zero =>
    have hQ : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [seededEdgeSearch,EdgeQueryTree.eval,decide_eq_true_eq]
    exact (seedMarked_singleton_of_no_crossing G Q R x (by simp [SearchCrossing,hQ]) ω hω).symm
  | succ n ih =>
    simp only [seededEdgeSearch]
    split_ifs with hc
    · obtain ⟨he,ha,hb,hends⟩ := searchCrossing_spec G Q R hc
      have hcard : (Q.erase (searchCrossing G Q R hc).1).card ≤ n := by
        rw [Finset.card_erase_of_mem he]; omega
      simp only [EdgeQueryTree.eval]
      by_cases heω : (searchCrossing G Q R hc).1 ∈ ω
      · simp only [ite_eq_left heω]
        rw [←Finset.insert_erase heω,Finset.coe_insert,seedMarked_insert_edge G _ R {x} _ _ _ ha hends,
          EdgeQueryTree.eval_insert _ (seededEdgeSearch_valid G x n _ _) (Finset.notMem_erase _ _)]
        exact ih _ _ hcard _ (Finset.erase_subset_erase _ hω)
      · simp only [ite_eq_right heω]
        exact ih _ _ hcard ω (Finset.subset_erase.mpr ⟨hω,heω⟩)
    · simp only [EdgeQueryTree.eval,decide_eq_true_eq]
      exact (seedMarked_singleton_of_no_crossing G Q R x hc ω hω).symm

 

theorem seededEdgeSearch_reads (G : BondGraph V E) (x : V) (n : ℕ) (Q : Finset E) (R : Finset V)
    (ω : Finset E) (i : E) (hi : (seededEdgeSearch G x n Q R).reads ω i) :
    ∃ a ∈ G i, ∃ r ∈ R, Conn G (ω : Set E) r a := by
  induction n generalizing Q R with
  | zero => exact hi.elim
  | succ n ih =>
    simp only [seededEdgeSearch] at hi
    split_ifs at hi with hc
    · obtain ⟨he,ha,hb,hends⟩ := searchCrossing_spec G Q R hc
      rcases hi with rfl | hi
      · refine ⟨(searchCrossing G Q R hc).2.1,?_,_,ha,conn_refl G _ _⟩
        rw [hends]; simp
      · split_ifs at hi with heω
        · obtain ⟨a,hai,r,hr,hra⟩ := ih _ _ hi
          rcases Finset.mem_insert.mp hr with rfl | hr
          · refine ⟨a,hai,(searchCrossing G Q R hc).2.1,ha,?_⟩
            exact (Relation.ReflTransGen.single ⟨(searchCrossing G Q R hc).1,heω,hends⟩).trans hra
          · exact ⟨a,hai,r,hr,hra⟩
        · exact ih _ _ hi
    · exact hi.elim

end SeededEdgeSearch
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RandomizedDecisionCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteCovariance_average_right (Q : Finset E) (F : Finset V) (p h : ℝ)
    (f : Finset E → ℝ) (g : Finset V → Finset E → ℝ) :
    finiteCovariance Q p f (fun ω => bernoulliPolynomial F (fun m => g m ω) h) =
      bernoulliPolynomial F (fun m => finiteCovariance Q p f (g m)) h := by
  unfold finiteCovariance
  rw [bernoulliPolynomial_sub,bernoulliPolynomial_const_mul,
    ←bernoulliPolynomial_commute Q F (fun ω m => g m ω) p h]
  congr 1
  calc
    _ = bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (fun m => f ω*g m ω) h) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      exact (bernoulliPolynomial_const_mul F (fun m => g m ω) (f ω) h).symm
    _ = _ := bernoulliPolynomial_commute Q F _ p h

 

theorem EdgeQueryTree.randomized_covariance_bound (Q : Finset E) (F : Finset V)
    (p h : unitInterval) (f : Finset E → ℝ) (trees : Finset V → EdgeQueryTree E)
    (ht : ∀ m ⊆ F, (trees m).Valid Q) :
    |finiteCovariance Q p f (fun ω => bernoulliPolynomial F (fun m => (trees m).value ω) h)| ≤
      ∑ i ∈ Q, bernoulliPolynomial F (fun m => (trees m).revealment p i) h *
        ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
  rw [finiteCovariance_average_right]
  apply (bernoulliPolynomial_abs F h _).trans
  calc
    _ ≤ bernoulliPolynomial F (fun m => ∑ i ∈ Q, (trees m).revealment p i *
        ((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i)) h := by
      apply bernoulliPolynomial_mono _ _ _ h h.2
      intro m hm
      exact (trees m).covariance_bound (ht m hm) p f
    _ = _ := by simp only [bernoulliPolynomial_sum,bernoulliPolynomial_mul_const]

theorem seededEdgeSearch_value (G : BondGraph V E) (x : V) (Q : Finset E)
    (m : Finset V) (ω : Finset E) (hω : ω ⊆ Q) :
    (seededEdgeSearch G x Q.card Q m).value ω =
      if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0 := by
  have hc := seededEdgeSearch_correct G x Q.card Q m le_rfl ω hω
  have he : SeedMarked G (ω:Set E) m {x} ↔ ∃ y ∈ m, Conn G (ω:Set E) x y := by
    simp only [SeedMarked,Finset.mem_singleton,exists_eq_left]
    exact exists_congr (fun y => and_congr_right (fun _ => ⟨conn_symm G _,conn_symm G _⟩))
  unfold EdgeQueryTree.value
  simp only [hc,he]

theorem finiteSeedProbability_tree (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (h : ℝ) (ω : Finset E) (hω : ω ⊆ Q) :
    finiteSeedProbability G F ω x h =
      bernoulliPolynomial F (fun m => (seededEdgeSearch G x Q.card Q m).value ω) h := by
  apply bernoulliPolynomial_congr
  intro m _
  exact (seededEdgeSearch_value G x Q m ω hω).symm

end RandomizedDecisionCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeedRevealmentBounds
attribute [local instance] Classical.propDecidable Classical.decEq

theorem seededEdgeSearch_reads_endpoints (G : BondGraph V E) (x : V) (Q : Finset E)
    (m : Finset V) (ω : Finset E) (i : E) (a b : V) (he : G i = s(a,b))
    (hi : (seededEdgeSearch G x Q.card Q m).reads ω i) :
    (∃ y ∈ m, Conn G (ω:Set E) a y) ∨ (∃ y ∈ m, Conn G (ω:Set E) b y) := by
  obtain ⟨z,hz,r,hr,hrz⟩ := seededEdgeSearch_reads G x Q.card Q m ω i hi
  rw [he] at hz
  rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
  · exact Or.inl ⟨r,hr,conn_symm G _ hrz⟩
  · exact Or.inr ⟨r,hr,conn_symm G _ hrz⟩

theorem seededEdgeSearch_mean_revealment_le (G : BondGraph V E) (x : V)
    (Q : Finset E) (F : Finset V) (p h : unitInterval) (i : E) (a b : V) (he : G i = s(a,b)) :
    bernoulliPolynomial F (fun m => (seededEdgeSearch G x Q.card Q m).revealment p i) h ≤
      bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω a h) p +
      bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω b h) p := by
  simp_rw [EdgeQueryTree.revealment_eq_probability _ (seededEdgeSearch_valid G x Q.card Q _)]
  rw [←bernoulliPolynomial_commute,←bernoulliPolynomial_add]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  unfold finiteSeedProbability
  rw [←bernoulliPolynomial_add]
  apply bernoulliPolynomial_mono _ _ _ h h.2
  intro m _
  have hr := seededEdgeSearch_reads_endpoints G x Q m ω i a b he
  by_cases hread : (seededEdgeSearch G x Q.card Q m).reads ω i
  · rcases hr hread with ha | hb
    · simp only [ite_eq_left hread,ite_eq_left ha]
      split_ifs <;> norm_num
    · simp only [ite_eq_left hread,ite_eq_left hb]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hread]
    split_ifs <;> norm_num

 

theorem finiteSeedProbability_component (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (hF : insert x (searchVertices G Q) ⊆ F)
    (ω : Finset E) (hω : ω ⊆ Q) (h : ℝ) :
    finiteSeedProbability G F ω x h = 1-(1-h)^(finiteRootComponent G ω x).card := by
  let C := finiteRootComponent G ω x
  have hCF : C ⊆ F := finiteRootComponent_subset G Q F x ω hω hF
  have he (m : Finset V) : (∃ y ∈ m, Conn G (ω:Set E) x y) ↔ m ∩ C ≠ ∅ := by
    rw [Finset.nonempty_iff_ne_empty.symm]
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,Finset.mem_inter.mpr ⟨hy,by change y ∈ (C:Set V); simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hxy⟩⟩
    · rintro ⟨y,hy⟩
      refine ⟨y,(Finset.mem_inter.mp hy).1,?_⟩
      have hm : y ∈ (C:Set V) := (Finset.mem_inter.mp hy).2
      simpa only [C,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hm
  calc
    _ = bernoulliPolynomial F (fun m => 1-(if m ∩ C = ∅ then 1 else 0)) h := by
      apply bernoulliPolynomial_congr
      intro m _
      by_cases hm : m ∩ C = ∅
      · have hn : ¬∃ y ∈ m, Conn G (ω:Set E) x y := fun hc => (he m).mp hc hm
        simp only [hm,hn,ite_false,ite_true,sub_self]
      · have hy := (he m).mpr hm
        simp only [hm,hy,ite_false,ite_true,sub_zero]
    _ = 1-bernoulliPolynomial F (fun m => if m ∩ C = ∅ then 1 else 0) h := by
      rw [bernoulliPolynomial_sub,bernoulliPolynomial_const]
    _ = _ := by rw [bernoulliPolynomial_restrict C F hCF (fun m => if m = ∅ then 1 else 0) h,
      bernoulliPolynomial_empty_indicator]

end SeedRevealmentBounds
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

theorem finiteSeedProbability_expectation (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (hF : insert x (searchVertices G Q) ⊆ F) (h p : ℝ) :
    bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω x h) p =
      markedConnectionPolynomial G Q x h p := by
  rw [markedConnection_component_polynomial]
  apply bernoulliPolynomial_congr
  intro ω hω
  exact finiteSeedProbability_component G Q F x hF ω hω h

theorem finiteSeedProbability_le_cluster_power (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (hF : insert x (searchVertices G Q) ⊆ F) (h p : unitInterval)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p)) :
    bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω x h) p ≤
      (h:ℝ)^α*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) := by
  rw [finiteSeedProbability_expectation G Q F x hF]
  exact markedConnection_le_cluster_power G Q x h p α hα hα1 hfin hi

end GhostFractionalPower
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section MonotoneDecisionRusso
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sum_coordinateVariation_eq_deriv (Q : Finset E) (f : Finset E → ℝ)
    (hf : Monotone f) (p : ℝ) :
    (∑ i ∈ Q, coordinateVariation Q p f i) = deriv (bernoulliPolynomial Q f) p := by
  rw [(hasDerivAt_bernoulliPolynomial Q f p).deriv]
  apply Finset.sum_congr rfl
  intro i _
  apply bernoulliPolynomial_congr
  intro ω _
  exact abs_of_nonneg (sub_nonneg.mpr (hf (Finset.subset_insert _ _)))

theorem EdgeQueryTree.randomized_covariance_le_deriv (Q : Finset E) (F : Finset V)
    (p h : unitInterval) (f : Finset E → ℝ) (hf : Monotone f)
    (trees : Finset V → EdgeQueryTree E) (ht : ∀ m ⊆ F, (trees m).Valid Q)
    (R : ℝ) (hR : ∀ i ∈ Q, bernoulliPolynomial F (fun m => (trees m).revealment p i) h ≤ R) :
    |finiteCovariance Q p f (fun ω => bernoulliPolynomial F (fun m => (trees m).value ω) h)| ≤
      R*((p:ℝ)*(1-(p:ℝ)))*deriv (bernoulliPolynomial Q f) p := by
  apply (randomized_covariance_bound Q F p h f trees ht).trans
  calc
    _ ≤ ∑ i ∈ Q, R*((p:ℝ)*(1-(p:ℝ))*coordinateVariation Q p f i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hR i hi)
        (mul_nonneg (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)) (coordinateVariation_nonneg Q p f i))
    _ = _ := by simp only [←mul_assoc,←Finset.mul_sum,sum_coordinateVariation_eq_deriv Q f hf]

 

theorem seededEdgeSearch_revealment_of_moments (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (α C : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law p))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law p) ≤ C) :
    ∀ i ∈ Q, bernoulliPolynomial (insert x (searchVertices G Q))
      (fun m => (seededEdgeSearch G x Q.card Q m).revealment p i) h ≤ 2*C*(h:ℝ)^α := by
  intro i hi
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G i)
  have he' : G i = s(a,b) := he.symm
  have hFa : insert a (searchVertices G Q) ⊆ insert x (searchVertices G Q) :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_of_mem (mem_searchVertices G hi (by rw [he']; simp)),Finset.subset_insert _ _⟩
  have hFb : insert b (searchVertices G Q) ⊆ insert x (searchVertices G Q) :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_of_mem (mem_searchVertices G hi (by rw [he']; simp)),Finset.subset_insert _ _⟩
  have ha := finiteSeedProbability_le_cluster_power G Q _ a hFa h p α hα hα1 (hfin a) (hI a)
  have hb := finiteSeedProbability_le_cluster_power G Q _ b hFb h p α hα hα1 (hfin b) (hI b)
  have hca := mul_le_mul_of_nonneg_left (hC a) (Real.rpow_nonneg h.2.1 α)
  have hcb := mul_le_mul_of_nonneg_left (hC b) (Real.rpow_nonneg h.2.1 α)
  have hr := seededEdgeSearch_mean_revealment_le G x Q (insert x (searchVertices G Q)) p h i a b he'
  linarith

theorem finiteSeed_covariance_upper (G : BondGraph V E) (Q : Finset E) (x : V)
    (p h : unitInterval) (α C : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law p))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law p) ≤ C)
    (f : Finset E → ℝ) (hf : Monotone f) :
    |finiteCovariance Q p f (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h)| ≤
      (2*C*(h:ℝ)^α)*((p:ℝ)*(1-(p:ℝ)))*deriv (bernoulliPolynomial Q f) p := by
  have hc := EdgeQueryTree.randomized_covariance_le_deriv Q (insert x (searchVertices G Q)) p h f hf
    (fun m => seededEdgeSearch G x Q.card Q m) (fun _ _ => seededEdgeSearch_valid G x Q.card Q _)
    (2*C*(h:ℝ)^α) (seededEdgeSearch_revealment_of_moments G Q x p h α C hα hα1 hfin hI hC)
  convert hc using 2
  all_goals try with_reducible_and_instances rfl
  apply finiteCovariance_congr_right
  intro ω hω
  exact finiteSeedProbability_tree G Q _ x h ω hω

end MonotoneDecisionRusso
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

theorem finiteClusterTail_deriv_nonneg (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    0 ≤ deriv (finiteClusterTail G Q x n) p := by
  change 0 ≤ deriv (bernoulliPolynomial Q (finiteClusterTailIndicator G x n)) p
  rw [←sum_coordinateVariation_eq_deriv Q _ (finiteClusterTailIndicator_mono G x n)]
  exact Finset.sum_nonneg (fun i _ => coordinateVariation_nonneg Q p _ i)

 

theorem finiteSeed_covariance_lower (G : BondGraph V E) (Q : Finset E) (x : V)
    (n : ℕ) (p h : unitInterval) (hn : 1 ≤ (h:ℝ)*n) (B : ℝ)
    (hB : markedConnectionPolynomial G Q x h p ≤ B) :
    (1/2-B)*finiteClusterTail G Q x n p ≤ finiteCovariance Q p
      (finiteClusterTailIndicator G x n)
      (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h) := by
  have hprod : (1:ℝ)/2*finiteClusterTail G Q x n p ≤
      bernoulliPolynomial Q (fun ω => finiteClusterTailIndicator G x n ω*
        finiteSeedProbability G (insert x (searchVertices G Q)) ω x h) p := by
    rw [finiteClusterTail,←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_mono _ _ _ p p.2
    intro ω hω
    rw [finiteSeedProbability_component G Q _ x le_rfl ω hω]
    unfold finiteClusterTailIndicator
    by_cases hsize : n ≤ (finiteRootComponent G ω x).card
    · simp only [ite_eq_left hsize,mul_one,one_mul]
      apply one_sub_pow_one_sub_ge_half
      exact hn.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) h.2.1)
    · simp only [ite_eq_right hsize,mul_zero,zero_mul,le_refl]
  have hmean := finiteSeedProbability_expectation G Q (insert x (searchVertices G Q)) x le_rfl (h:ℝ) p
  unfold finiteCovariance
  rw [hmean]
  change _ ≤ _-finiteClusterTail G Q x n p*markedConnectionPolynomial G Q x h p
  have hm := mul_le_mul_of_nonneg_left hB (finiteClusterTail_nonneg G Q x n p)
  nlinarith

end ClusterTailCovariance
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_TailBounds
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
section ClusterTailDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClusterTail_derivative_bound (G : BondGraph V E) (Q : Finset E) (x : V)
    (n : ℕ) (p h : unitInterval) (hn : 1 ≤ (h:ℝ)*n) (α C : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC0 : 0 < C) (hsmall : C*(h:ℝ)^α ≤ 1/4)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law p))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law p) ≤ C) :
    finiteClusterTail G Q x n p ≤ 8*C*(h:ℝ)^α*deriv (finiteClusterTail G Q x n) p := by
  have hmark := (markedConnection_le_cluster_power G Q x h p α hα hα1 (hfin x) (hI x)).trans
    (mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg h.2.1 α))
  rw [mul_comm ((h:ℝ)^α) C] at hmark
  have hlow := finiteSeed_covariance_lower G Q x n p h hn (C*(h:ℝ)^α) hmark
  have hupp := finiteSeed_covariance_upper G Q x p h α C hα hα1 hfin hI hC
    (finiteClusterTailIndicator G x n) (finiteClusterTailIndicator_mono G x n)
  have hF := finiteClusterTail_nonneg G Q x n p
  have hd := finiteClusterTail_deriv_nonneg G Q x n p
  have hp : (p:ℝ)*(1-(p:ℝ)) ≤ 1 := by nlinarith [p.2.1,p.2.2]
  have hprod := mul_le_mul_of_nonneg_right hp hd
  have hR : 0 ≤ 2*C*(h:ℝ)^α := mul_nonneg (by positivity) (Real.rpow_nonneg h.2.1 α)
  have hh := mul_le_mul_of_nonneg_left hprod hR
  have ha := le_abs_self (finiteCovariance Q p (finiteClusterTailIndicator G x n)
    (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h))
  have hs := mul_le_mul_of_nonneg_right hsmall hF
  change |_| ≤ _*deriv (finiteClusterTail G Q x n) p at hupp
  nlinarith

theorem exponential_transfer_of_deriv_lower (H : ℝ → ℝ) (a b K : ℝ)
    (hH : Differentiable ℝ H) (hab : a ≤ b)
    (hb : ∀ t ∈ Set.Icc a b, K*H t ≤ deriv H t) :
    H a ≤ Real.exp (-K*(b-a))*H b := by
  let F (t : ℝ) := Real.exp (-K*(t-a))*H t
  have hF (t : ℝ) : HasDerivAt F (Real.exp (-K*(t-a))*(deriv H t-K*H t)) t := by
    have he := (((hasDerivAt_id t).sub_const a).const_mul (-K)).exp
    convert! he.mul (hH t).hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    ring
  have hmono : MonotoneOn F (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv]
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hb t (interior_subset ht)))
  have hh := hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  simpa only [F,sub_self,mul_zero,Real.exp_zero,one_mul] using hh

end ClusterTailDerivative
end Percolation

 
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

 

theorem finiteClusterTail_stretched [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (x : V) (n : ℕ) (p q h : unitInterval) (hpq : p ≤ q)
    (hh : 0 < (h:ℝ)) (hn : 1 ≤ (h:ℝ)*n) (α C : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC0 : 0 < C) (hsmall : C*(h:ℝ)^α ≤ 1/4)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    finiteClusterTail G Q x n p ≤
      Real.exp (-((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α))*(2*C*(h:ℝ)^α) := by
  have hden : 0 < 8*C*(h:ℝ)^α := by positivity
  have hexp := exponential_transfer_of_deriv_lower (finiteClusterTail G Q x n) p q
    (1/(8*C*(h:ℝ)^α)) (fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt) hpq
  have hder : ∀ t ∈ Set.Icc (p:ℝ) (q:ℝ),
      (1/(8*C*(h:ℝ)^α))*finiteClusterTail G Q x n t ≤ deriv (finiteClusterTail G Q x n) t := by
    intro t ht
    let r : unitInterval := ⟨t,⟨p.2.1.trans ht.1,ht.2.trans q.2.2⟩⟩
    have hrq : r ≤ q := ht.2
    have hmoment (y : V) := cluster_power_mono_integral G hloc y r q hrq α hα (hfin y) (hI y)
    have he := finiteClusterTail_derivative_bound G Q x n r h hn α C hα hα1 hC0 hsmall
      (fun y => cluster_finite_ae_mono G y r q hrq (hfin y)) (fun y => (hmoment y).1)
      (fun y => (hmoment y).2.trans (hC y))
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm (deriv (finiteClusterTail G Q x n) t)] using he
  have he := hexp hder
  have hb := (finiteClusterTail_le_markedConnection G Q x n q h hn).trans
    (mul_le_mul_of_nonneg_left ((markedConnection_le_cluster_power G Q x h q α hα hα1 (hfin x) (hI x)).trans
      (mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg hh.le α))) (by norm_num : (0:ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α))).le
  have heq : -(1/(8*C*(h:ℝ)^α))*((q:ℝ)-(p:ℝ)) = -((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α) := by ring
  rw [heq] at he
  have hb' : Real.exp (-((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α))*(2*((h:ℝ)^α*C)) =
      Real.exp (-((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α))*(2*C*(h:ℝ)^α) := by ring
  exact he.trans (hm.trans_eq hb')

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
section PolynomialTails
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exp_stretched_power_bound (r K δ C z : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hz : 0 < z) (hK : ∀ t : ℝ, 0 < t → Real.exp (-t) ≤ K*t^(-r)) :
    Real.exp (-δ/(8*C*z))*(2*C*z) ≤
      (2*C*K*(8*C)^r)*δ^(-r)*z^(1+r) := by
  have he := mul_le_mul_of_nonneg_right (hK (δ/(8*C*z)) (by positivity))
    (by positivity : 0 ≤ 2*C*z)
  have hid : (δ/(8*C*z))^(-r)*(2*C*z) =
      (2*C*(8*C)^r)*δ^(-r)*z^(1+r) := by
    rw [Real.div_rpow hδ.le (by positivity),Real.mul_rpow (by positivity : 0 ≤ 8*C) hz.le,
      Real.rpow_neg (by positivity : 0 ≤ 8*C),Real.rpow_neg hz.le,
      Real.rpow_add hz,Real.rpow_one]
    field_simp
  calc
    _ ≤ K*(δ/(8*C*z))^(-r)*(2*C*z) := by simpa only [neg_div] using he
    _ = K*((δ/(8*C*z))^(-r)*(2*C*z)) := by ring
    _ = _ := by rw [hid]; ring

 

theorem finiteClusterTail_polynomial_large [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (q : unitInterval) (α C r : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC0 : 0 < C)
    (hr : 0 ≤ r)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q : Finset E) (x : V) (p : unitInterval), p < q →
      ∀ n : ℕ, 1 ≤ n → C*(n:ℝ)^(-α) ≤ 1/4 →
      finiteClusterTail G Q x n p ≤ A*((q:ℝ)-(p:ℝ))^(-r)*(n:ℝ)^(-α*(1+r)) := by
  obtain ⟨K,hK,hKb⟩ := exists_exp_neg_le_rpow r hr
  refine ⟨2*C*K*(8*C)^r,by positivity,?_⟩
  intro Q x p hp n hn hsmall
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let h : unitInterval := ⟨1/(n:ℝ),⟨by positivity,by apply (div_le_one hn0).mpr; exact_mod_cast hn⟩⟩
  have hh : 0 < (h:ℝ) := by dsimp [h]; positivity
  have hhpow : (h:ℝ)^α = (n:ℝ)^(-α) := by
    dsimp [h]
    rw [one_div,Real.inv_rpow hn0.le,Real.rpow_neg hn0.le]
  have hhprod : 1 ≤ (h:ℝ)*n := by dsimp [h]; rw [one_div,inv_mul_cancel₀ hn0.ne']
  have hst := finiteClusterTail_stretched G hloc Q x n p q h hp.le hh hhprod α C hα hα1 hC0
    (by rwa [hhpow]) hfin hI hC
  have he := exp_stretched_power_bound r K ((q:ℝ)-(p:ℝ)) C ((h:ℝ)^α)
    (sub_pos.mpr hp) hC0 (Real.rpow_pos_of_pos hh α) hKb
  apply hst.trans
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  rw [hhpow,←Real.rpow_mul hn0.le]

end PolynomialTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformPolynomialTails
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClusterTail_le_one (G : BondGraph V E) (Q : Finset E) (x : V)
    (n : ℕ) (p : unitInterval) : finiteClusterTail G Q x n p ≤ 1 := by
  rw [finiteClusterTail,←bernoulliPolynomial_const Q 1 p]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  unfold finiteClusterTailIndicator
  split_ifs <;> norm_num

 

theorem finiteClusterTail_polynomial [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (q : unitInterval) (α C r : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 < C)
    (hr : 0 ≤ r)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q : Finset E) (x : V) (p : unitInterval), p < q →
      ∀ n : ℕ, 1 ≤ n →
      finiteClusterTail G Q x n p ≤ A*((q:ℝ)-(p:ℝ))^(-r)*(n:ℝ)^(-α*(1+r)) := by
  obtain ⟨A,hA,hbig⟩ := finiteClusterTail_polynomial_large G hloc q α C r hα.le hα1 hC0 hr hfin hI hC
  have ht : Tendsto (fun n : ℕ => C*(n:ℝ)^(-α)) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_apply] using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)))
  let s := α*(1+r)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  let B : ℝ := ((N+1:ℕ):ℝ)^s+A
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro Q x p hp n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hδ : 0 < (q:ℝ)-(p:ℝ) := sub_pos.mpr hp
  have hhead : 1 ≤ ((q:ℝ)-(p:ℝ))^(-r) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ (by linarith [p.2.1,q.2.2]) (by linarith)
  by_cases hnN : N ≤ n
  · apply (hbig Q x p hp n hn (hN n hnN).le).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by dsimp [B]; linarith [Real.rpow_nonneg (Nat.cast_nonneg (N+1)) s]) (Real.rpow_nonneg hδ.le _)) (Real.rpow_nonneg hn0.le _)
  · have hnB : (n:ℝ)^s ≤ B := by
      apply (Real.rpow_le_rpow hn0.le (show (n:ℝ) ≤ ((N+1:ℕ):ℝ) by exact_mod_cast (by omega : n ≤ N+1)) hs).trans
      dsimp [B]
      linarith
    have hBδ : B ≤ B*((q:ℝ)-(p:ℝ))^(-r) := by nlinarith
    have hbound : 1 ≤ B*((q:ℝ)-(p:ℝ))^(-r)*(n:ℝ)^(-s) := by
      rw [Real.rpow_neg hn0.le,←div_eq_mul_inv]
      exact (one_le_div (Real.rpow_pos_of_pos hn0 s)).mpr (hnB.trans hBδ)
    exact (finiteClusterTail_le_one G Q x n p).trans (by simpa only [s,neg_mul] using hbound)

end UniformPolynomialTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section TailSummation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem natCast_eq_sum_tail (k M : ℕ) (hk : k ≤ M) :
    (k:ℝ) = ∑ i ∈ Finset.range M, if i+1 ≤ k then (1:ℝ) else 0 := by
  rw [Finset.sum_boole]
  congr 1
  have hh : (Finset.range M).filter (fun i => i+1 ≤ k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hh,Finset.card_range]

theorem finiteClusterSize_eq_sum_tail (G : BondGraph V E) (Q : Finset E) (x : V) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card:ℝ)) p =
      ∑ n ∈ Finset.range (insert x (searchVertices G Q)).card, finiteClusterTail G Q x (n+1) p := by
  simp only [finiteClusterTail]
  rw [←bernoulliPolynomial_sum]
  apply bernoulliPolynomial_congr
  intro ω hω
  exact natCast_eq_sum_tail _ _ (Finset.card_le_card (finiteRootComponent_subset G Q _ x ω hω (by rfl)))

theorem summable_shifted_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^(-s)) := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))

 
theorem finiteClusterSize_bound_of_tail (G : BondGraph V E) (Q : Finset E) (x : V)
    (p : unitInterval) (A s : ℝ) (hA : 0 ≤ A) (hs : 1 < s)
    (hf : ∀ n : ℕ, 1 ≤ n → finiteClusterTail G Q x n p ≤ A*(n:ℝ)^(-s)) :
    bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card:ℝ)) p ≤
      A*(∑' n : ℕ, ((n+1:ℕ):ℝ)^(-s)) := by
  rw [finiteClusterSize_eq_sum_tail,←tsum_mul_left]
  have hsumm := (summable_shifted_rpow s hs).mul_left A
  apply (Finset.sum_le_sum (fun n _ => hf (n+1) (by omega))).trans
  exact hsumm.sum_le_tsum _ (fun n _ => mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end TailSummation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SusceptibilityExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_connection_row_le_size (G : BondGraph V E) (Q : Finset E)
    (x : V) (K : Finset V) (p : unitInterval) :
    (∑ y ∈ K, bernoulliPolynomial Q (fun ω => if Conn G ω x y then (1:ℝ) else 0) p) ≤
      bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card:ℝ)) p := by
  rw [←bernoulliPolynomial_sum]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  rw [Finset.sum_boole]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro y hy
  change y ∈ (finiteRootComponent G ω x : Set V)
  rw [coe_finiteRootComponent]
  exact (Finset.mem_filter.mp hy).2

 

theorem susceptibility_bound_of_finite_size [Countable E] (G : BondGraph V E)
    (x : V) (p : unitInterval) (B : ℝ)
    (hB : ∀ Q : Finset E, bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card:ℝ)) p ≤ B) :
    Summable (twoPoint G p x) ∧ susceptibility G p x ≤ B := by
  let : Encodable E := Encodable.ofCountable E
  let Q := vertexExhaustion (V := E)
  have hrow (K : Finset V) : (∑ y ∈ K, twoPoint G p x y) ≤ B := by
    have ht (y : V) : Tendsto (fun n => bernoulliPolynomial (Q n)
        (fun ω => if Conn G ω x y then (1:ℝ) else 0) p) atTop (nhds (twoPoint G p x y)) := by
      have hc (e : E) (_ : e ∈ (Set.univ : Set E)) : ∃ n, e ∈ Q n := by
        obtain ⟨n,hn⟩ := subset_vertexExhaustion ({e} : Finset E)
        exact ⟨n,hn (by simp)⟩
      simpa only [Set.inter_univ,twoPoint,Measure.real] using! finite_connection_polynomial_tendsto G Set.univ Q
        vertexExhaustion_mono (fun _ => Set.subset_univ _) hc p x y
    apply le_of_tendsto (tendsto_finsetSum K (fun y _ => ht y))
    exact Filter.Eventually.of_forall (fun n => (finite_connection_row_le_size G (Q n) x K p).trans (hB (Q n)))
  exact ⟨summable_of_sum_le (twoPoint_nonneg G p x) hrow,
    Real.tsum_le_of_sum_le (twoPoint_nonneg G p x) hrow⟩

end SusceptibilityExhaustion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SusceptibilityPowerFromMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem susceptibility_power_of_uniform_moment [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (q : unitInterval) (α C r : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 < C)
    (hr : 0 ≤ r) (hs : 1 < α*(1+r))
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : unitInterval), p < q → ∀ x,
      Summable (twoPoint G p x) ∧ susceptibility G p x ≤ D*((q:ℝ)-(p:ℝ))^(-r) := by
  obtain ⟨A,hA,hbound⟩ := finiteClusterTail_polynomial G hloc q α C r hα hα1 hC0 hr hfin hI hC
  let S := ∑' n : ℕ, ((n+1:ℕ):ℝ)^(-(α*(1+r)))
  have hS : 0 ≤ S := tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨1+A*S,by positivity,?_⟩
  intro p hp x
  have hδ : 0 < (q:ℝ)-(p:ℝ) := sub_pos.mpr (show (p:ℝ)<(q:ℝ) from hp)
  apply susceptibility_bound_of_finite_size
  intro Q
  have hh := finiteClusterSize_bound_of_tail G Q x p (A*((q:ℝ)-(p:ℝ))^(-r)) (α*(1+r))
    (mul_nonneg hA.le (Real.rpow_nonneg hδ.le _)) hs (by
      intro n hn
      simpa only [neg_mul] using hbound Q x p hp n hn)
  calc
    _ ≤ (A*((q:ℝ)-(p:ℝ))^(-r))*S := hh
    _ = (A*S)*((q:ℝ)-(p:ℝ))^(-r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hδ.le _)

 

theorem almost_linear_susceptibility_of_moments [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hmom : ∀ α : ℝ, 0 < α → α < 1/2 → ∃ C : ℝ, 0 < C ∧ ∀ y,
      Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q) ∧
      (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : unitInterval), p < q → ∀ x,
      Summable (twoPoint G p x) ∧ susceptibility G p x ≤ D*((q:ℝ)-(p:ℝ))^(-1-η) := by
  let α : ℝ := 1/(2+η/2)
  have hden : 0 < 2+η/2 := by linarith
  have hα : 0 < α := one_div_pos.mpr hden
  have hαhalf : α < 1/2 := by
    apply (div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)).mpr
    linarith
  have hs : 1 < α*(1+(1+η)) := by
    dsimp [α]
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (one_lt_div hden).mpr
    linarith
  obtain ⟨C,hC,hm⟩ := hmom α hα hαhalf
  obtain ⟨D,hD,hbound⟩ := susceptibility_power_of_uniform_moment G hloc q α C (1+η) hα
    (by linarith) hC (by linarith) hs hfin (fun y => (hm y).1) (fun y => (hm y).2)
  refine ⟨D,hD,?_⟩
  intro p hp x
  simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using hbound p hp x

end SusceptibilityPowerFromMoment
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

 

theorem almost_linear_susceptibility_oai
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : unitInterval), p < pc G → ∀ x,
      susceptibility G p x ≤ D*((pc G:ℝ)-(p:ℝ))^(-1-η) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  have hfinite : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
    intro x
    obtain ⟨i,a,b,hab,rfl⟩ := hcover x
    exact cluster_finite_ae_covariant G (pc G) hab (root i) (hfin i)
  have hmom (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :=
    uniform_cluster_power_of_root G hloc (pc G) root hcover α
      (critical_root_power_integrable G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α hα hα1)
  obtain ⟨D,hD,hb⟩ := almost_linear_susceptibility_of_moments G hloc (pc G) hfinite hmom η hη
  exact ⟨D,hD,fun p hp x => (hb p hp x).2⟩

end SourceAlmostLinear
end Percolation


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.almost_linear_susceptibility_oai.{u, v, u_1} := @OAI.Percolation.almost_linear_susceptibility_oai.{u, v, u_1}
