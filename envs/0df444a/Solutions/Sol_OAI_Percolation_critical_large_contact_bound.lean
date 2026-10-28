-- Prove2me | solution 1 for OAI.Percolation.critical_large_contact_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:01:18.268052+00:00
-- url     : https://prove2.me/submissions/20f3d3ad-c446-4e3e-af4f-15f89aaf0b26

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

end ProbeTree
end MarkedExploration

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

end ClusterResampling
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
section FiniteLocalIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

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

end FiniteLocalIndependence

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

end ExposedClusterGeometry
end Percolation


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
      simp only [leaf,show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),ite_false]
    have ho : bernoulliPolynomial (Q.erase e) (fun ω => f ((query e t₀ t₁).leaf (insert e ω))) p =
        bernoulliPolynomial (Q.erase e) (fun ω => f (Sum.inr (t₁.leaf ω))) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      simp only [leaf,Finset.mem_insert_self,ite_true,
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
    · simp only [F,f,ite_eq_left (hv.mpr hc),mul_zero,not_true_eq_false,hc,false_and,ite_false]
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

 

theorem critical_large_contact_bound_oai
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


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.critical_large_contact_bound_oai.{u, v, u_1} := @OAI.Percolation.critical_large_contact_bound_oai.{u, v, u_1}
