-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.full_application_reduced_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:24:34.691504+00:00
-- url     : https://prove2.me/submissions/eec0f18e-e277-4dba-ba26-5ded1159c644

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_finite_general_bs
import Theorems.Thm_OAI_Percolation_BenjaminiSchramm_full_application_conditional_bs

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

section Countability


theorem countable_vertices [Nonempty V] {G : BondGraph V E}
    (hG : LocallyFinite G) (hconn : Connected G) : Countable V := by
  let x : V := Classical.arbitrary V
  have he : (Set.univ : Set V) = ⋃ n, reachBall G x n := by
    ext y
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact exists_mem_reachBall (hconn x y)
  apply Set.countable_univ_iff.mp
  rw [he]
  exact Set.countable_iUnion (fun n => (finite_reachBall hG x n).countable)

theorem countable_edges [Countable V] {G : BondGraph V E}
    (hG : LocallyFinite G) : Countable E := by
  have he : (Set.univ : Set E) = ⋃ x, {e | x ∈ G e} := by
    ext e
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨(G e).out.1, Sym2.out_fst_mem _⟩
  apply Set.countable_univ_iff.mp
  rw [he]
  exact Set.countable_iUnion (fun x => (hG x).countable)

end Countability

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

theorem openEdges_eq_iUnion_of_tendsto (labels : E → unitInterval)
    (q : unitInterval) (hneq : ∀ e, labels e ≠ q) (p : ℕ → unitInterval)
    (hle : ∀ n, p n ≤ q) (hlim : Tendsto p atTop (𝓝 q)) :
    openEdges labels q = ⋃ n, openEdges labels (p n) := by
  ext e
  constructor
  · intro he
    have hlt : labels e < q := lt_of_le_of_ne he (hneq e)
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).1 _ hlt).exists
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  · intro he
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
    exact hn.trans (hle n)

 

theorem twoPoint_tendsto_of_monotone [Countable V] [Countable E]
    (G : BondGraph V E) (p : ℕ → unitInterval) (hp : Monotone p)
    (q : unitInterval) (hle : ∀ n, p n ≤ q) (hlim : Tendsto p atTop (𝓝 q))
    (x y : V) : Tendsto (fun n => twoPoint G (p n) x y) atTop (𝓝 (twoPoint G q x y)) := by
  let s (n : ℕ) : Set (E → unitInterval) := {labels | Conn G (openEdges labels (p n)) x y}
  have hs : Monotone s := by
    intro m n hmn labels hl
    exact conn_mono G (openEdges_mono labels (hp hmn)) hl
  have he : {labels : E → unitInterval | Conn G (openEdges labels q) x y} =ᵐ[labelLaw]
      ⋃ n, s n := by
    filter_upwards [ae_labels_ne (E := E) q] with labels hlabels
    show (Conn G (openEdges labels q) x y) = (labels ∈ ⋃ n, s n)
    apply propext
    rw [openEdges_eq_iUnion_of_tendsto labels q hlabels p hle hlim, conn_iUnion_iff]
    · simp [s]
    · exact fun m n hmn => openEdges_mono labels (hp hmn)
  rw [twoPoint_eq_labelLaw G q x y, measure_congr he]
  have ht := (tendsto_measure_iUnion_atTop (μ := (labelLaw : Measure (E → unitInterval))) hs)
  have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  simpa only [Function.comp_def, s, ← twoPoint_eq_labelLaw] using hr

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
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_EndpointKernels
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

end ClusterWindowLaw
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

theorem restrictedSusceptibility_path_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S)
    (hfin : ∀ a, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) a z})) :
    (p:ℝ)^l.length*restrictedSusceptibility G S p y ≤ restrictedSusceptibility G S p x := by
  unfold restrictedSusceptibility
  rw [←tsum_mul_left]
  exact ((hfin y).mul_left _).tsum_le_tsum (restrictedTwoPoint_path_lower G S p hl hS) (hfin x)



end RestrictedPathPotential
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
open MeasureTheory Filter
open scoped Topology
section ExteriorConnectionIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integral_event_indicator (p : unitInterval) (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ ω, (if ω ∈ A then (1:ℝ) else 0) ∂law p) = (law p).real A := by
  simpa only [Set.indicator,Pi.one_apply] using (integral_indicator_one (μ := law p) hA)



end ExteriorConnectionIndependence
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
open MeasureTheory Filter
section SubcriticalSusceptibilityContinuity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem label_cluster_finite_ae_subcritical [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), (cluster G (openEdges labels p) x).Finite := by
  apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
    (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges p).aemeasurable
  rw [map_openEdges]
  exact subcritical_cluster_finite_ae G p hp x

end SubcriticalSusceptibilityContinuity
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

end ActualSusceptibilityRightSlope
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
      simp only [value,eval,Finset.mem_insert_self,if_true,eval_insert t₁ ht.2.2 heS]
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
        simp only [reads,hie,false_or,Finset.mem_insert_self,if_true,reads_insert t₁ ht.2.2 heS]

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
        simp only [hm,hn,if_false,if_true,sub_self]
      · have hy := (he m).mpr hm
        simp only [hm,hy,if_false,if_true,sub_zero]
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

theorem finiteSeedProbability_expectation (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (hF : insert x (searchVertices G Q) ⊆ F) (h p : ℝ) :
    bernoulliPolynomial Q (fun ω => finiteSeedProbability G F ω x h) p =
      markedConnectionPolynomial G Q x h p := by
  rw [markedConnection_component_polynomial]
  apply bernoulliPolynomial_congr
  intro ω hω
  exact finiteSeedProbability_component G Q F x hF ω hω h

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
section ClusterTailDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

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
section ContactConcentration
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactBonds_comm (G : BondGraph V E) (Q : Finset E) (A B : Finset V) :
    contactBonds G Q A B = contactBonds G Q B A := by
  ext e
  simp only [contactBonds,Finset.mem_filter]
  constructor <;> rintro ⟨he,a,ha,b,hb,hab⟩
  · exact ⟨he,b,hb,a,ha,hab.trans (Sym2.eq_swap ..)⟩
  · exact ⟨he,b,hb,a,ha,hab.trans (Sym2.eq_swap ..)⟩



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

end ContactBinFirstMoment
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

end FullLargeContacts
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



end PairSquareDiagram
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


end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PublishedConsequences
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
namespace BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq

theorem law_restrict_finite_cluster (G : BondGraph V E) (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) (A : Set (Set E)) :
    law p {ω | ω ∈ A ∧ (cluster G ω x).Finite} = law p A := by
  apply measure_congr
  filter_upwards [hfin] with ω hω
  exact propext (and_iff_left hω)

theorem criticalFiniteTail_eq (G : BondGraph V E)
    (A : V → ℕ → Set (Set E)) (x : V)
    (hfin : ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite) :
    criticalFiniteTail G A x = criticalTail G A x := by
  funext n
  unfold criticalFiniteTail criticalTail
  rw [law_restrict_finite_cluster G (pc G) x hfin (A x n)]

end BenjaminiSchramm
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_EventMeasurability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem volumeEvent_eq_clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) :
    volumeEvent G x n = clusterLarge G x n := by
  ext ω
  constructor
  · intro h
    by_cases hf : (cluster G ω x).Finite
    · have hn : n ≤ (cluster G ω x).ncard := by
        change (n : ℕ∞) ≤ (cluster G ω x).encard at h
        rw [← hf.cast_ncard_eq] at h
        exact_mod_cast h
      exact ⟨hf.toFinset, by simpa only [← Set.ncard_eq_toFinset_card _ hf] using hn,
        fun y hy => hf.mem_toFinset.mp hy⟩
    · obtain ⟨t, ht, hn⟩ := (Set.not_finite.mp hf).exists_subset_card_eq n
      exact ⟨t, hn.ge, ht⟩
  · rintro ⟨t, hn, ht⟩
    change (n : ℕ∞) ≤ (cluster G ω x).encard
    have hsub : (t : Set V) ⊆ cluster G ω x := ht
    have hcard := Set.encard_le_encard hsub
    have hn' : (n : ℕ∞) ≤ (t.card : ℕ∞) := by exact_mod_cast hn
    exact hn'.trans (by simpa using hcard)

theorem measurableSet_volumeEvent [Countable E] (G : BondGraph V E) (x : V) (n : ℕ) :
    MeasurableSet (volumeEvent G x n) := by
  rw [volumeEvent_eq_clusterLarge]
  exact measurableSet_clusterLarge G x n

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostTail
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

attribute [local instance] Classical.propDecidable Classical.decEq

theorem seeded_revealment_of_ghost_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (B : ℝ)
    (hB : ∀ y, markedConnectionPolynomial G Q y h p ≤ B) :
    ∀ i ∈ Q, bernoulliPolynomial (insert x (searchVertices G Q))
      (fun m => (seededEdgeSearch G x Q.card Q m).revealment p i) h ≤ 2 * B := by
  intro i hi
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G i)
  have he' : G i = s(a,b) := he.symm
  have hFa : insert a (searchVertices G Q) ⊆ insert x (searchVertices G Q) :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_of_mem
      (mem_searchVertices G hi (by rw [he']; simp)),Finset.subset_insert _ _⟩
  have hFb : insert b (searchVertices G Q) ⊆ insert x (searchVertices G Q) :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_of_mem
      (mem_searchVertices G hi (by rw [he']; simp)),Finset.subset_insert _ _⟩
  have ha := hB a
  have hb := hB b
  rw [←finiteSeedProbability_expectation G Q _ a hFa] at ha
  rw [←finiteSeedProbability_expectation G Q _ b hFb] at hb
  have hr := seededEdgeSearch_mean_revealment_le G x Q
    (insert x (searchVertices G Q)) p h i a b he'
  linarith

theorem covariance_of_ghost_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (B : ℝ)
    (hB : ∀ y, markedConnectionPolynomial G Q y h p ≤ B)
    (f : Finset E → ℝ) (hf : Monotone f) :
    |finiteCovariance Q p f
      (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h)| ≤
      (2 * B) * ((p : ℝ) * (1 - p)) * deriv (bernoulliPolynomial Q f) p := by
  have hc := EdgeQueryTree.randomized_covariance_le_deriv Q
    (insert x (searchVertices G Q)) p h f hf
    (fun m => seededEdgeSearch G x Q.card Q m)
    (fun _ _ => seededEdgeSearch_valid G x Q.card Q _)
    (2 * B) (seeded_revealment_of_ghost_bound G Q x p h B hB)
  convert hc using 2
  all_goals try with_reducible_and_instances rfl
  apply finiteCovariance_congr_right
  intro ω hω
  exact finiteSeedProbability_tree G Q _ x h ω hω

theorem tail_derivative_of_ghost_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (n : ℕ) (p h : unitInterval) (B : ℝ)
    (hn : 1 ≤ (h : ℝ) * n) (hB0 : 0 ≤ B) (hsmall : B ≤ 1 / 4)
    (hB : ∀ y, markedConnectionPolynomial G Q y h p ≤ B) :
    finiteClusterTail G Q x n p ≤ 8 * B * deriv (finiteClusterTail G Q x n) p := by
  have hlow := finiteSeed_covariance_lower G Q x n p h hn B (hB x)
  have hupp := covariance_of_ghost_bound G Q x p h B hB
    (finiteClusterTailIndicator G x n) (finiteClusterTailIndicator_mono G x n)
  have hF := finiteClusterTail_nonneg G Q x n p
  have hd := finiteClusterTail_deriv_nonneg G Q x n p
  have hp : (p : ℝ) * (1 - p) ≤ 1 := by nlinarith [p.2.1,p.2.2]
  have hprod := mul_le_mul_of_nonneg_right hp hd
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * B by positivity)
  have ha := le_abs_self (finiteCovariance Q p (finiteClusterTailIndicator G x n)
    (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h))
  have hs := mul_le_mul_of_nonneg_right hsmall hF
  change |_| ≤ _ * deriv (finiteClusterTail G Q x n) p at hupp
  nlinarith

theorem tail_transfer_of_ghost_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (n : ℕ) (p q h : unitInterval) (B : ℝ) (hpq : p ≤ q)
    (hn : 1 ≤ (h : ℝ) * n) (hB0 : 0 < B) (hsmall : B ≤ 1 / 4)
    (hB : ∀ r : unitInterval, p ≤ r → r ≤ q →
      ∀ y, markedConnectionPolynomial G Q y h r ≤ B) :
    finiteClusterTail G Q x n p ≤
      Real.exp (-((q : ℝ) - p) / (8 * B)) * (2 * B) := by
  have hden : 0 < 8 * B := by positivity
  have hder : ∀ t ∈ Set.Icc (p : ℝ) q,
      (1 / (8 * B)) * finiteClusterTail G Q x n t ≤
        deriv (finiteClusterTail G Q x n) t := by
    intro t ht
    let r : unitInterval := ⟨t,⟨p.2.1.trans ht.1,ht.2.trans q.2.2⟩⟩
    have he := tail_derivative_of_ghost_bound G Q x n r h B hn hB0.le hsmall
      (hB r ht.1 ht.2)
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm (deriv (finiteClusterTail G Q x n) t)] using he
  have he := exponential_transfer_of_deriv_lower (finiteClusterTail G Q x n) p q
    (1 / (8 * B)) (fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt)
    hpq hder
  have hb := (finiteClusterTail_le_markedConnection G Q x n q h hn).trans
    (mul_le_mul_of_nonneg_left (hB q hpq le_rfl x) (by norm_num : (0 : ℝ) ≤ 2))
  have heq : -(1 / (8 * B)) * ((q : ℝ) - p) = -((q : ℝ) - p) / (8 * B) := by ring
  rw [heq] at he
  exact he.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostVolume
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

open MeasureTheory

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem markedConnection_le_truncated_tails (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (N : ℕ) :
    markedConnectionPolynomial G Q x h p ≤
      (h : ℝ) * (∑ i ∈ Finset.range N, finiteClusterTail G Q x (i + 1) p) +
        finiteClusterTail G Q x N p := by
  rw [markedConnection_component_polynomial]
  simp only [finiteClusterTail]
  rw [←bernoulliPolynomial_sum,←bernoulliPolynomial_const_mul,←bernoulliPolynomial_add]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  let m := (finiteRootComponent G ω x).card
  change 1 - (1 - (h : ℝ)) ^ m ≤
    (h : ℝ) * (∑ i ∈ Finset.range N, if i + 1 ≤ m then (1 : ℝ) else 0) +
      if N ≤ m then (1 : ℝ) else 0
  by_cases hm : m ≤ N
  · rw [←natCast_eq_sum_tail m N hm]
    exact (one_sub_pow_one_sub_le h m).trans
      (le_add_of_nonneg_right (by split_ifs <;> norm_num))
  · have hNm : N ≤ m := by omega
    rw [ite_eq_left hNm]
    have hs : 0 ≤ (h : ℝ) *
        (∑ i ∈ Finset.range N, if i + 1 ≤ m then (1 : ℝ) else 0) :=
      mul_nonneg h.2.1 (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    have hp := pow_nonneg (sub_nonneg.mpr h.2.2) m
    linarith

theorem inverse_sqrt_step (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℕ) ≤
      2 * (Real.sqrt (n + 1 : ℕ) - Real.sqrt n) := by
  have ha : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
  have hb := Real.sqrt_nonneg (n : ℝ)
  have hab : Real.sqrt (n : ℝ) ≤ Real.sqrt (n + 1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
  have ha2 := Real.sq_sqrt (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity)
  have hb2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
  apply (div_le_iff₀ ha).mpr
  have hdiff := sq_nonneg (Real.sqrt (n + 1 : ℕ) - Real.sqrt (n : ℝ))
  norm_num only [Nat.cast_add,Nat.cast_one] at ha2
  norm_num only [Nat.cast_add,Nat.cast_one] at ha hab hdiff ⊢
  nlinarith

theorem sum_inverse_sqrt_le (N : ℕ) :
    (∑ i ∈ Finset.range N, 1 / Real.sqrt (i + 1 : ℕ)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := inverse_sqrt_step N
    linarith

theorem markedConnection_le_sqrt_scale (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
    (hh : (h : ℝ) * (m : ℝ) ^ 2 ≤ 1)
    (htail : ∀ n : ℕ, 0 < n →
      finiteClusterTail G Q x n p ≤ C / Real.sqrt n) :
    markedConnectionPolynomial G Q x h p ≤ 3 * C / m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmsq : 0 < m ^ 2 := pow_pos hm _
  have hs := Finset.sum_le_sum (s := Finset.range (m ^ 2))
    (fun i _ => htail (i + 1) (by omega))
  have hs' : (∑ i ∈ Finset.range (m ^ 2), finiteClusterTail G Q x (i + 1) p) ≤
      2 * C * m := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m ^ 2), C / Real.sqrt (i + 1 : ℕ) := hs
      _ = C * (∑ i ∈ Finset.range (m ^ 2), 1 / Real.sqrt (i + 1 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ C * (2 * Real.sqrt (m ^ 2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (sum_inverse_sqrt_le (m ^ 2)) hC
      _ = 2 * C * m := by
        rw [Nat.cast_pow,Real.sqrt_sq (by positivity)]
        ring
  have ht := htail (m ^ 2) hmsq
  rw [Nat.cast_pow,Real.sqrt_sq (by positivity)] at ht
  have hmark := (markedConnection_le_truncated_tails G Q x p h (m ^ 2)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hs' h.2.1) ht)
  apply hmark.trans
  apply (le_div_iff₀ hmR).mpr
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * C by positivity)
  have hCdiv : (C / (m : ℝ)) * m = C := div_mul_cancel₀ C hmR.ne'
  nlinarith

theorem finiteClusterTail_le_volume_probability [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    finiteClusterTail G Q x n p ≤ (law p (volumeEvent G x n)).toReal := by
  let f (ω : Set E) : ℝ := if n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard then 1 else 0
  have hf : ∀ ω, f ω = f (ω ∩ (Q : Set E)) := by
    intro ω
    simp only [f,Set.inter_assoc,Set.inter_self]
  have he : (∫ ω, f ω ∂law p) = finiteClusterTail G Q x n p := by
    rw [integral_eq_bernoulliPolynomial Q p f hf]
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [f,finiteClusterTailIndicator,
      Set.inter_eq_left.mpr (show (ω : Set E) ⊆ Q from hω),
      ←coe_finiteRootComponent,Set.ncard_coe_finset]
  rw [←he]
  change (∫ ω, f ω ∂law p) ≤ (law p).real (volumeEvent G x n)
  rw [←integral_event_indicator p (volumeEvent G x n)
    (measurableSet_volumeEvent G x n)]
  apply integral_mono (integrable_finite_local Q p f hf)
    (by simpa only [Set.indicator,Pi.one_apply] using!
      (integrable_const (1 : ℝ)).indicator (measurableSet_volumeEvent G x n))
  intro ω
  dsimp [f]
  split_ifs with hn hv
  · rfl
  · exfalso
    apply hv
    change (n : ℕ∞) ≤ (cluster G ω x).encard
    have hn' : (n : ℕ∞) ≤ ((cluster G (ω ∩ (Q : Set E)) x).ncard : ℕ∞) := by
      exact_mod_cast hn
    exact hn'.trans ((Set.ncard_le_encard _).trans
      (Set.encard_le_encard (fun y hy => conn_mono G Set.inter_subset_left hy)))
  · norm_num
  · rfl

theorem finiteClusterTail_le_criticalTail [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ)
    (p : unitInterval) (hp : p ≤ pc G) :
    finiteClusterTail G Q x n p ≤ criticalTail G (volumeEvent G) x n := by
  have hmono := bernoulliPolynomial_monotoneOn Q (finiteClusterTailIndicator G x n)
    (finiteClusterTailIndicator_mono G x n)
  exact (hmono p.2 (pc G).2 hp).trans
    (finiteClusterTail_le_volume_probability G Q x n (pc G))

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostCritical
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem volume_probability_aut [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (n : ℕ) :
    law p (volumeEvent G (a x) n) = law p (volumeEvent G x n) := by
  have he : volumeEvent G (a x) n =
      (fun ω => b ⁻¹' ω) ⁻¹' volumeEvent G x n := by
    ext ω
    change (n : ℕ∞) ≤ (cluster G ω (a x)).encard ↔
      (n : ℕ∞) ≤ (cluster G (b ⁻¹' ω) x).encard
    rw [←cluster_aut G hab,a.injective.encard_image]
  rw [he,←Measure.map_apply (measurable_set_preimage b)
    (measurableSet_volumeEvent G x n),law_map_preimage_equiv]

theorem uniform_critical_volume_upper [Countable E]
    (G : BondGraph V E) (hqt : QuasiTransitive G)
    (hvol : ∀ x, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x n, 0 < n →
      criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n := by
  obtain ⟨O,hO⟩ := hqt
  choose c hc hb using hvol
  let C := 1 + ∑ o ∈ O, c o
  have hC : 0 < C := by
    have hs := Finset.sum_nonneg (s := O) (fun o _ => (hc o).le)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro x n hn
  obtain ⟨o,ho,a,b,hab,rfl⟩ := hO x
  have he : criticalTail G (volumeEvent G) (a o) n =
      criticalTail G (volumeEvent G) o n := by
    unfold criticalTail
    rw [volume_probability_aut G (pc G) hab]
  rw [he]
  apply (hb o n hn).trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hs := Finset.single_le_sum (s := O) (fun z _ => (hc z).le) ho
  dsimp [C]
  linarith

theorem uniform_critical_volume_upper_of_powerTail [Countable E]
    (G : BondGraph V E) (hqt : QuasiTransitive G)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x n, 0 < n →
      criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n := by
  apply uniform_critical_volume_upper G hqt
  intro x
  obtain ⟨c,C,_hc,hC,hb⟩ := hvol x
  refine ⟨C,hC,?_⟩
  intro n hn
  have hh := (hb n hn).2
  rw [Real.rpow_neg (Nat.cast_nonneg n),←Real.sqrt_eq_rpow] at hh
  simpa only [div_eq_mul_inv] using hh

theorem critical_ghost_bound_at_square_scale [Countable E]
    (G : BondGraph V E) (C : ℝ) (hC : 0 ≤ C)
    (hvol : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n)
    (Q : Finset E) (x : V) (p h : unitInterval) (hp : p ≤ pc G)
    (m : ℕ) (hm : 0 < m) (hh : (h : ℝ) * (m : ℝ) ^ 2 ≤ 1) :
    markedConnectionPolynomial G Q x h p ≤ 3 * C / m := by
  exact markedConnection_le_sqrt_scale G Q x p h m hm C hC hh
    (fun n hn => (finiteClusterTail_le_criticalTail G Q x n p hp).trans (hvol x n hn))

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CriticalSusceptibility
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem volume_threshold_le_clusterMass (G : BondGraph V E) (ω : Set E)
    (x : V) (n : ℕ) (hn : ω ∈ volumeEvent G x n) :
    (n : ℝ≥0∞) ≤ clusterMass G ω x := by
  rw [volumeEvent_eq_clusterLarge] at hn
  obtain ⟨F,hF,hsub⟩ := hn
  have he : (∑ y ∈ F, if Conn G ω x y then (1 : ℝ≥0∞) else 0) = F.card := by
    calc
      _ = ∑ _y ∈ F, (1 : ℝ≥0∞) :=
        Finset.sum_congr rfl (fun y hy => ite_eq_left (hsub y hy))
      _ = _ := by simp
  calc
    (n : ℝ≥0∞) ≤ F.card := by exact_mod_cast hF
    _ = ∑ y ∈ F, if Conn G ω x y then (1 : ℝ≥0∞) else 0 := he.symm
    _ ≤ clusterMass G ω x := ENNReal.sum_le_tsum F

theorem volume_probability_times_threshold_le_mass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V) (n : ℕ) :
    (n : ℝ≥0∞) * law p (volumeEvent G x n) ≤
      ∑' y, law p {ω | Conn G ω x y} := by
  rw [←lintegral_clusterMass]
  rw [←lintegral_indicator_const (measurableSet_volumeEvent G x n) (n : ℝ≥0∞)]
  apply lintegral_mono
  intro ω
  by_cases hn : ω ∈ volumeEvent G x n
  · rw [Set.indicator_of_mem hn]
    exact volume_threshold_le_clusterMass G ω x n hn
  · rw [Set.indicator_of_notMem hn]
    exact bot_le

theorem critical_mass_expectation_top_of_volume_lower [Countable V] [Countable E]
    (G : BondGraph V E) (x : V)
    (hvol : PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    (∑' y, law (pc G) {ω | Conn G ω x y}) = ⊤ := by
  obtain ⟨c,C,hc,_hC,hb⟩ := hvol
  by_contra htop
  let R := (∑' y, law (pc G) {ω | Conn G ω x y}).toReal
  obtain ⟨m,hm⟩ := exists_nat_gt (max 0 (R / c))
  have hmR : 0 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast hmR
  have hcm : R < c * m := by
    have hh := (le_max_right 0 (R / c)).trans_lt hm
    exact (div_lt_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  have hlower := (hb (m ^ 2) (pow_pos hm0 _)).1
  rw [Real.rpow_neg (Nat.cast_nonneg _),←Real.sqrt_eq_rpow,Nat.cast_pow,
    Real.sqrt_sq hmR.le] at hlower
  have hupp := ENNReal.toReal_mono htop
    (volume_probability_times_threshold_le_mass G (pc G) x (m ^ 2))
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hupp
  have htail : criticalTail G (volumeEvent G) x (m ^ 2) =
      (law (pc G) (volumeEvent G x (m ^ 2))).toReal := rfl
  rw [←htail,Nat.cast_pow] at hupp
  have hl := mul_le_mul_of_nonneg_left hlower (sq_nonneg (m : ℝ))
  have hid : (m : ℝ) ^ 2 * (c * (m : ℝ)⁻¹) = c * m := by
    field_simp
  rw [hid] at hl
  exact (not_lt_of_ge (hl.trans hupp)) hcm

theorem susceptibility_unbounded_below_critical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hpc0 : 0 < pc G) (x : V)
    (hvol : PowerTail (criticalTail G (volumeEvent G) x) (1 / 2))
    (a : unitInterval) (ha : a < pc G) (B : ℝ) :
    ∃ p : unitInterval, a ≤ p ∧ p < pc G ∧ B < susceptibility G p x := by
  by_contra! hbound
  obtain ⟨p,hp,hpcrit,hlim⟩ := exists_seq_strictMono_tendsto' hpc0
  have hpa : ∀ᶠ n in atTop, a ≤ p n :=
    (tendsto_order.mp hlim).1 a ha |>.mono (fun _ h => h.le)
  have hrow (F : Finset V) : ∑ y ∈ F, twoPoint G (pc G) x y ≤ B := by
    apply le_of_tendsto (tendsto_finsetSum F (fun y _ =>
      twoPoint_tendsto_of_monotone G p hp.monotone (pc G)
        (fun n => (hpcrit n).2.le) hlim x y))
    filter_upwards [hpa] with n hn
    exact ((summable_twoPoint_subcritical G hloc hqt (p n) (hpcrit n).2 x).sum_le_tsum F
      (fun y _ => twoPoint_nonneg G (p n) x y)).trans
      (hbound (p n) hn (hpcrit n).2)
  have hs := summable_of_sum_le (twoPoint_nonneg G (pc G) x) hrow
  have he : ENNReal.ofReal (susceptibility G (pc G) x) =
      ∑' y, law (pc G) {ω | Conn G ω x y} := by
    rw [susceptibility,ENNReal.ofReal_tsum_of_nonneg (twoPoint_nonneg G (pc G) x) hs]
    apply tsum_congr
    intro y
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [critical_mass_expectation_top_of_volume_lower G x hvol] at he
  exact ENNReal.ofReal_ne_top he

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ReciprocalGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Percolation.BenjaminiSchramm

theorem reciprocal_lower_of_derivative_upper
    (f : ℝ → ℝ) (a b K : ℝ) (hK : 0 < K)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Ioo a b, deriv f x ≤ K * (f x) ^ 2)
    (hunbounded : ∀ x ∈ Ioo a b, ∀ B : ℝ,
      ∃ y, x ≤ y ∧ y < b ∧ B < f y)
    (x : ℝ) (hx : x ∈ Ioo a b) : 1 / (K * (b - x)) ≤ f x := by
  have hinverse : 1 / f x ≤ K * (b - x) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y,hxy,hyb,hfy⟩ := hunbounded x hx (1 / ε)
    have hy : y ∈ Ioo a b := ⟨hx.1.trans_le hxy,hyb⟩
    have hsub : Icc x y ⊆ Ioo a b := fun z hz =>
      ⟨hx.1.trans_le hz.1,hz.2.trans_lt hyb⟩
    have hg (z : ℝ) (hz : z ∈ Icc x y) :
        HasDerivAt (fun t => 1 / f t) (-deriv f z / (f z) ^ 2) z := by
      simpa only [one_div,Pi.inv_apply] using!
        (hdiff z (hsub hz)).hasDerivAt.inv (hpos z (hsub hz)).ne'
    have hbound (z : ℝ) (hz : z ∈ interior (Icc x y)) :
        -K ≤ deriv (fun t => 1 / f t) z := by
      rw [(hg z (interior_subset hz)).deriv,neg_div]
      apply neg_le_neg
      exact (div_le_iff₀ (sq_pos_of_pos (hpos z (hsub (interior_subset hz))))).mpr
        (hderiv z (hsub (interior_subset hz)))
    have hdist := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
      (fun z hz => (hg z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hg z (interior_subset hz)).differentiableAt.differentiableWithinAt)
      hbound x ⟨le_rfl,hxy⟩ y ⟨hxy,le_rfl⟩ hxy
    have hinv : 1 / f y < ε := by
      apply (div_lt_iff₀ (hpos y hy)).mpr
      have hh := (div_lt_iff₀ hε).mp hfy
      nlinarith
    have hKdist := mul_le_mul_of_nonneg_left (show y - x ≤ b - x by linarith) hK.le
    linarith
  have hmul := mul_le_mul_of_nonneg_right hinverse (hpos x hx).le
  rw [div_mul_cancel₀ 1 (hpos x hx).ne'] at hmul
  apply (div_le_iff₀ (mul_pos hK (sub_pos.mpr hx.2))).mpr
  nlinarith

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SusceptibilityUpper
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_tail_square_scale [Countable E]
    (G : BondGraph V E) (C : ℝ) (hC : 0 < C)
    (hvol : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n)
    (Q : Finset E) (x : V) (p : unitInterval) (hp : p ≤ pc G)
    (m n : ℕ) (hm : 0 < m) (hmC : 12 * C ≤ m) (hmn : m ^ 2 ≤ n) :
    finiteClusterTail G Q x n p ≤
      (6 * C / m) * Real.exp (-((pc G : ℝ) - p) * m / (24 * C)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let h : unitInterval := ⟨1 / (m : ℝ) ^ 2,⟨by positivity,
    (div_le_one (by positivity)).mpr (by nlinarith)⟩⟩
  have hh : (h : ℝ) * (m : ℝ) ^ 2 = 1 := by dsimp [h]; field_simp
  have hn : 1 ≤ (h : ℝ) * n := by
    rw [←hh]
    apply mul_le_mul_of_nonneg_left _ h.2.1
    exact_mod_cast hmn
  have hB0 : 0 < 3 * C / m := by positivity
  have hsmall : 3 * C / m ≤ 1 / 4 := by
    apply (div_le_iff₀ hmR).mpr
    linarith
  have hb (r : unitInterval) (_hpr : p ≤ r) (hr : r ≤ pc G) (y : V) :=
    critical_ghost_bound_at_square_scale G C hC.le hvol Q y r h hr m hm hh.le
  have ht := tail_transfer_of_ghost_bound G Q x n p (pc G) h (3 * C / m)
    hp hn hB0 hsmall hb
  have he : -((pc G : ℝ) - p) / (8 * (3 * C / m)) =
      -((pc G : ℝ) - p) * m / (24 * C) := by field_simp; ring
  rw [he] at ht
  convert ht using 1 <;> first | rfl | ring

theorem finite_tail_antitone (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) : Antitone (fun n => finiteClusterTail G Q x n p) := by
  intro n m hnm
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  dsimp [finiteClusterTailIndicator]
  split_ifs <;> norm_num
  omega

theorem square_block_tail_sum (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (m : ℕ) :
    (∑ i ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), finiteClusterTail G Q x (i + 1) p) ≤
      (2 * m + 1 : ℕ) * finiteClusterTail G Q x (m ^ 2) p := by
  calc
    _ ≤ ∑ _i ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), finiteClusterTail G Q x (m ^ 2) p := by
      apply Finset.sum_le_sum
      intro i hi
      exact finite_tail_antitone G Q x p ((Finset.mem_Ico.mp hi).1.trans (Nat.le_succ i))
    _ = _ := by
      simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
      congr 1
      have he : (m + 1) ^ 2 - m ^ 2 = 2 * m + 1 := by
        have hh : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
        omega
      rw [he]

theorem sum_exp_neg_le (t : ℝ) (ht : 0 < t) (N : ℕ) :
    (∑ i ∈ Finset.range N, Real.exp (-t * i)) ≤ 1 + 1 / t := by
  have hq : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-t) := sub_pos.mpr hq
  have hsum : (∑ i ∈ Finset.range N, Real.exp (-t * i)) ≤
      1 / (1 - Real.exp (-t)) := by
    simp_rw [mul_comm (-t),Real.exp_nat_mul]
    apply (le_div_iff₀ hden).mpr
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg (Real.exp_pos (-t)).le N]
  apply hsum.trans
  apply (div_le_iff₀ hden).mpr
  have he := Real.add_one_le_exp t
  have he0 := Real.exp_pos t
  rw [Real.exp_neg]
  apply (mul_le_mul_iff_right₀ he0).mp
  field_simp
  nlinarith

theorem finite_mean_upper_from_volume [Countable E]
    (G : BondGraph V E) (C : ℝ) (hC : 0 < C)
    (hvol : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n)
    (M : ℕ) (hM : 0 < M) (hMC : 12 * C ≤ M)
    (Q : Finset E) (x : V) (p : unitInterval) (hp : p < pc G) :
    bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card : ℝ)) p ≤
      (M : ℝ) ^ 2 + 18 * C * (1 + 24 * C / ((pc G : ℝ) - p)) := by
  let δ : ℝ := (pc G : ℝ) - p
  have hδ : 0 < δ := sub_pos.mpr hp
  let f := fun n => finiteClusterTail G Q x (n + 1) p
  let g := fun m : ℕ => Real.exp (-(δ / (24 * C)) * m)
  have hpartial (K : ℕ) : (∑ i ∈ Finset.range (K ^ 2), f i) ≤
      (M : ℝ) ^ 2 + 18 * C * (∑ m ∈ Finset.range K, g m) := by
    induction K with
    | zero => simp
    | succ K ih =>
      by_cases hKM : K < M
      · have hf1 : (∑ i ∈ Finset.range ((K + 1) ^ 2), f i) ≤ ((K + 1) ^ 2 : ℕ) := by
          calc
            _ ≤ ∑ _i ∈ Finset.range ((K + 1) ^ 2), (1 : ℝ) :=
              Finset.sum_le_sum (fun i _ => finiteClusterTail_le_one G Q x (i + 1) p)
            _ = _ := by simp
        have hsq : (((K + 1) ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
          exact_mod_cast Nat.pow_le_pow_left (show K + 1 ≤ M by omega) 2
        have hg0 : 0 ≤ 18 * C * (∑ m ∈ Finset.range (K + 1), g m) :=
          mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
        exact hf1.trans (hsq.trans (le_add_of_nonneg_right hg0))
      · have hMK : M ≤ K := by omega
        have hK : 0 < K := hM.trans_le hMK
        have hKC : 12 * C ≤ K := hMC.trans (by exact_mod_cast hMK)
        have ht := finite_tail_square_scale G C hC hvol Q x p hp.le K (K ^ 2) hK hKC le_rfl
        have hblock := square_block_tail_sum G Q x p K
        have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
        have hratio : (2 * (K : ℝ) + 1) * (6 * C / K) ≤ 18 * C := by
          rw [←mul_div_assoc]
          apply (div_le_iff₀ (show 0 < (K : ℝ) by positivity)).mpr
          nlinarith
        have hblock' : (∑ i ∈ Finset.Ico (K ^ 2) ((K + 1) ^ 2), f i) ≤ 18 * C * g K := by
          apply hblock.trans
          apply (mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ (2 * K + 1 : ℕ))).trans
          have he : -δ * K / (24 * C) = -(δ / (24 * C)) * K := by ring
          change (2 * K + 1 : ℕ) * ((6 * C / K) * Real.exp (-δ * K / (24 * C))) ≤ _
          rw [he]
          have hh := mul_le_mul_of_nonneg_right hratio (Real.exp_pos (-(δ / (24 * C)) * K)).le
          push_cast
          simpa only [mul_assoc,g] using hh
        rw [←Finset.sum_range_add_sum_Ico f (Nat.pow_le_pow_left (Nat.le_succ K) 2),
          Finset.sum_range_succ]
        have hh := add_le_add ih hblock'
        simpa only [mul_add,add_assoc] using hh
  let N := (insert x (searchVertices G Q)).card
  have hN : N ≤ N ^ 2 := Nat.le_self_pow two_ne_zero N
  rw [finiteClusterSize_eq_sum_tail]
  have hle : (∑ i ∈ Finset.range N, f i) ≤ ∑ i ∈ Finset.range (N ^ 2), f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
      (fun i _ _ => finiteClusterTail_nonneg G Q x (i + 1) p)
  apply (hle.trans (hpartial N)).trans
  have ht : 0 < δ / (24 * C) := by positivity
  have hs := sum_exp_neg_le (δ / (24 * C)) ht N
  have he : 1 / (δ / (24 * C)) = 24 * C / δ := by field_simp
  rw [he] at hs
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hs (show 0 ≤ 18 * C by positivity))

theorem susceptibility_upper_of_critical_volume [Countable E]
    (G : BondGraph V E) (hqt : QuasiTransitive G)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ p : unitInterval, p < pc G → ∀ x,
      susceptibility G p x ≤ A / ((pc G : ℝ) - p) := by
  obtain ⟨C,hC,hb⟩ := uniform_critical_volume_upper_of_powerTail G hqt hvol
  obtain ⟨M,hMC⟩ := exists_nat_gt (12 * C)
  have hM : 0 < M := by
    have hh : (0 : ℝ) < M := (by positivity : 0 < 12 * C).trans hMC
    exact_mod_cast hh
  let A : ℝ := (M : ℝ) ^ 2 + 18 * C + 432 * C ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro p hp x
  have hδ : 0 < (pc G : ℝ) - p := sub_pos.mpr hp
  have hδ1 : (pc G : ℝ) - p ≤ 1 := by linarith [(pc G).2.2,p.2.1]
  have hbound := (susceptibility_bound_of_finite_size G x p
    ((M : ℝ) ^ 2 + 18 * C * (1 + 24 * C / ((pc G : ℝ) - p)))
    (fun Q => finite_mean_upper_from_volume G C hC hb M hM hMC.le Q x p hp)).2
  apply hbound.trans
  apply (le_div_iff₀ hδ).mpr
  have hbase := mul_le_mul_of_nonneg_left hδ1
    (show 0 ≤ (M : ℝ) ^ 2 + 18 * C by positivity)
  have hid :
      ((M : ℝ) ^ 2 + 18 * C * (1 + 24 * C / ((pc G : ℝ) - p))) *
          ((pc G : ℝ) - p) =
      ((M : ℝ) ^ 2 + 18 * C) * ((pc G : ℝ) - p) + 432 * C ^ 2 := by
    field_simp
    ring
  rw [hid]
  dsimp [A]
  linarith

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SusceptibilityDerivative
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_russoSlope [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun y => russoSlope G x y (p : ℝ)) := by
  exact (summable_russoMajorant G hloc hqt p hp x).of_nonneg_of_le
    (fun y => russoSlope_nonneg G x y p p.2.2)
    (fun y => russoSlope_le_majorant G hloc hqt p p hp le_rfl x y)

theorem hasDerivAt_realSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (x : V) :
    HasDerivAt (realSusceptibility G x) (∑' y, russoSlope G x y (p : ℝ)) p := by
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  apply hasDerivAt_tsum_of_isPreconnected (summable_russoMajorant G hloc hqt b hb x)
    isOpen_Ioo isPreconnected_Ioo
    (fun y t ht => hasDerivAt_realTwoPoint_slope G hloc hqt t
      ⟨ht.1,lt_trans ht.2 hb⟩ x y)
    (fun y t ht => ?_) (show (p : ℝ) ∈ Set.Ioo 0 (b : ℝ) from ⟨hp0,hpb⟩)
    (by simpa only [realTwoPoint_coe] using summable_twoPoint_subcritical G hloc hqt p hp x)
    ⟨hp0,hpb⟩
  let q : unitInterval := ⟨t,ht.1.le,ht.2.le.trans b.2.2⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (russoSlope_nonneg G x y t q.2.2)]
  exact russoSlope_le_majorant G hloc hqt b q hb ht.2.le x y

theorem susceptibility_derivative_upper [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp : p < pc G) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ z, susceptibility G p z ≤ C) (x : V) :
    deriv (realSusceptibility G x) p ≤ (d : ℝ) * C ^ 2 / (1 - p) := by
  rw [(hasDerivAt_realSusceptibility G hloc hqt p hp0 hp x).deriv]
  have hmajor := (summable_russoSlope G hloc hqt p hp x).tsum_le_tsum
    (fun y => russoSlope_le_majorant G hloc hqt p p hp le_rfl x y)
    (summable_russoMajorant G hloc hqt p hp x)
  have hCenn (z : V) : (∑' y, law p {ω | Conn G ω z y}) ≤ ENNReal.ofReal C := by
    rw [←ennreal_susceptibility G hloc hqt p hp z]
    exact ENNReal.ofReal_le_ofReal (hC z)
  have hdiag := russoDiagram_row_bound G hloc d hd p (ENNReal.ofReal C) hCenn x
  have htop : (d : ℝ≥0∞) * ENNReal.ofReal C ^ 2 ≠ ⊤ := by finiteness
  have hreal := ENNReal.toReal_mono htop hdiag
  rw [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hC0] at hreal
  apply hmajor.trans
  simp only [russoMajorant,tsum_div_const]
  rw [←ENNReal.tsum_toReal_eq (russoDiagram_ne_top G hloc hqt p hp x)]
  exact div_le_div_of_nonneg_right hreal
    (sub_nonneg.mpr p.2.2)

theorem hasDerivAt_realRootSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G) :
    HasDerivAt (realRootSusceptibility G root weight)
      (∑ i, weight i * (∑' y, russoSlope G (root i) y (p : ℝ))) p := by
  have he : realRootSusceptibility G root weight =
      fun t => ∑ i, weight i * realSusceptibility G (root i) t := by
    funext t
    simp only [realRootSusceptibility,rootSusceptibility,susceptibility,
      realSusceptibility,realTwoPoint]
  rw [he]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_realSusceptibility G hloc hqt p hp0 hp (root i)).const_mul (weight i))

theorem rootSusceptibility_derivative_upper [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (c : ℝ) (hc : 0 ≤ c)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : p < pc G)
    (hC : ∀ z, susceptibility G p z ≤ c * rootSusceptibility G root weight p) :
    deriv (realRootSusceptibility G root weight) p ≤
      (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - p) := by
  rw [(hasDerivAt_realRootSusceptibility G hloc hqt root weight p hp0 hp).deriv]
  have hrow (i : ι) : (∑' y, russoSlope G (root i) y (p : ℝ)) ≤
      (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - p) := by
    have hh := susceptibility_derivative_upper G hloc hqt d hd p hp0 hp
      (c * rootSusceptibility G root weight p)
      (mul_nonneg hc (rootSusceptibility_nonneg G root weight hw p)) hC (root i)
    rwa [(hasDerivAt_realSusceptibility G hloc hqt p hp0 hp (root i)).deriv] at hh
  calc
    _ ≤ ∑ i, weight i *
        ((d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - p)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hw i))
    _ = _ := by rw [←Finset.sum_mul,hw1,one_mul]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SusceptibilityLaw
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootSusceptibility_lower_of_critical_volume
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hpc0 : 0 < (pc G : ℝ)) (hpc1 : (pc G : ℝ) < 1)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c * weight i)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    ∃ k : ℝ, 0 < k ∧ ∀ p : unitInterval,
      (pc G : ℝ) / 2 < p → p < pc G →
      k / ((pc G : ℝ) - p) ≤ rootSusceptibility G root weight p := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  let K : ℝ := (d : ℝ) * c ^ 2 / (1 - pc G)
  have hK : 0 < K := by dsimp [K]; positivity
  have hparam (t : ℝ) (ht : t ∈ Set.Ioo ((pc G : ℝ) / 2) (pc G : ℝ)) :
      t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(by linarith [ht.1]),ht.2.le.trans (pc G).2.2⟩
  have hC (p : unitInterval) (z : V) :
      susceptibility G p z ≤ c * rootSusceptibility G root weight p :=
    susceptibility_le_rootSusceptibility G root weight hw hcover c hc.le hmin p z
  have hderiv (t : ℝ) (ht : t ∈ Set.Ioo ((pc G : ℝ) / 2) (pc G : ℝ)) :
      deriv (realRootSusceptibility G root weight) t ≤
        K * realRootSusceptibility G root weight t ^ 2 := by
    let p : unitInterval := ⟨t,hparam t ht⟩
    have hp0 : 0 < (p : ℝ) := by dsimp [p]; linarith [ht.1]
    have hp : p < pc G := ht.2
    have hh := rootSusceptibility_derivative_upper G hloc hqt root weight hw hw1
      d hdeg c hc.le p hp0 hp (hC p)
    have hnum : 0 ≤ (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 := by positivity
    have hden : 0 < 1 - (pc G : ℝ) := sub_pos.mpr hpc1
    have hle :
        (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - p) ≤
        (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - pc G) :=
      div_le_div_of_nonneg_left hnum hden (by change 1 - (pc G : ℝ) ≤ 1 - t; linarith [ht.2])
    have he :
        (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - pc G) =
        K * rootSusceptibility G root weight p ^ 2 := by dsimp [K]; ring
    change deriv (realRootSusceptibility G root weight) (p : ℝ) ≤
      K * realRootSusceptibility G root weight (p : ℝ) ^ 2
    rw [realRootSusceptibility_coe]
    exact hh.trans (hle.trans_eq he)
  have hunbounded (t : ℝ) (ht : t ∈ Set.Ioo ((pc G : ℝ) / 2) (pc G : ℝ))
      (B : ℝ) : ∃ s, t ≤ s ∧ s < (pc G : ℝ) ∧
        B < realRootSusceptibility G root weight s := by
    let p : unitInterval := ⟨t,hparam t ht⟩
    let x : V := Classical.ofNonempty
    obtain ⟨q,hpq,hq,hB⟩ := susceptibility_unbounded_below_critical G hloc hqt hpc0
      x (hvol x) p ht.2 (c * B)
    refine ⟨q,hpq,hq,?_⟩
    rw [realRootSusceptibility_coe]
    have hh := hB.trans_le (hC q x)
    nlinarith
  refine ⟨1 / K,one_div_pos.mpr hK,fun p hp0 hp => ?_⟩
  have hh := reciprocal_lower_of_derivative_upper
    (realRootSusceptibility G root weight) ((pc G : ℝ) / 2) (pc G : ℝ) K hK
    (fun t ht => by
      let q : unitInterval := ⟨t,hparam t ht⟩
      have hh := rootSusceptibility_one_le G hloc hqt root weight hw hw1 q ht.2
      rw [←realRootSusceptibility_coe] at hh
      exact zero_lt_one.trans_le hh)
    (fun t ht => by
      let q : unitInterval := ⟨t,hparam t ht⟩
      have hq0 : 0 < (q : ℝ) := by dsimp [q]; linarith [ht.1]
      exact (hasDerivAt_realRootSusceptibility G hloc hqt root weight q hq0 ht.2).differentiableAt)
    hderiv hunbounded p ⟨hp0,hp⟩
  simpa only [realRootSusceptibility_coe,div_div] using hh

theorem susceptibilityLaw_of_critical_volume [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc1 : (pc G : ℝ) < 1)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    SusceptibilityLaw G := by
  obtain ⟨O,hO⟩ := hqt
  have hqt : QuasiTransitive G := ⟨O,hO⟩
  have hOne : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO (Classical.ofNonempty : V)
    exact ⟨o,ho⟩
  let : Nonempty O := hOne.to_subtype
  let root : O → V := Subtype.val
  let c : ℝ := Fintype.card O
  let weight : O → ℝ := fun _ => 1 / c
  have hc : 0 < c := by dsimp [c]; exact_mod_cast Fintype.card_pos
  have hw (i : O) : 0 ≤ weight i := (one_div_pos.mpr hc).le
  have hw1 : ∑ i, weight i = 1 := by
    simp only [weight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change c * (1 / c) = 1
    exact mul_one_div_cancel hc.ne'
  have hmin (i : O) : 1 ≤ c * weight i := by
    dsimp [weight]
    rw [mul_one_div_cancel hc.ne']
  have hcover (x : V) : ∃ i, x ∈ vertexOrbit G (root i) := by
    obtain ⟨o,ho,a,b,hab,hax⟩ := hO x
    exact ⟨⟨o,ho⟩,a,b,hab,hax⟩
  have hpc0 : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  obtain ⟨k,hk,hroot⟩ := rootSusceptibility_lower_of_critical_volume G hloc hqt hpc0 hpc1
    root weight hw hw1 hcover c hc hmin hvol
  obtain ⟨a,ha,hlower⟩ := exists_rootSusceptibility_lower G hconn hloc hqt root weight
    hw hw1 hcover ((pc G : ℝ) / 2) (by positivity)
  obtain ⟨A,hA,hupper⟩ := susceptibility_upper_of_critical_volume G hqt hvol
  intro x
  refine ⟨a*k,A,(pc G : ℝ)/2,mul_pos ha hk,hA,by positivity,?_⟩
  intro p hp hnear
  have hp0 : (pc G : ℝ) / 2 < p := by linarith
  refine ⟨?_,hupper p hp x⟩
  calc
    a*k / ((pc G : ℝ) - p) = a * (k / ((pc G : ℝ) - p)) := by ring
    _ ≤ a * rootSusceptibility G root weight p :=
      mul_le_mul_of_nonneg_left (hroot p hp0 hp) ha.le
    _ ≤ susceptibility G p x := hlower p hp0.le hp x

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_InputReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

open MeasureTheory

universe u v
variable {V : Type u} {E : Type v}

theorem susceptibilityLaw_of_publishedVolume [Infinite V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hvolume : HutchcroftCriticalVolumeInput G) (hgap : pc G < ptwo G) :
    SusceptibilityLaw G := by
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  have hp1 : pc G < 1 := hgap.trans_le (ptwo G).2.2
  have hfin := critical_finite_general_bs G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hp1
  apply susceptibilityLaw_of_critical_volume G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hp1
  intro x
  have hh := hvolume hgraph hgap x
  rwa [criticalFiniteTail_eq G (volumeEvent G) x (hfin x)] at hh

theorem firstMomentInput_of_volume [Infinite V]
    (G : BondGraph V E) (hvolume : HutchcroftCriticalVolumeInput G) :
    HutchcroftFirstMomentInput G := by
  intro hgraph hgap x
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  obtain ⟨c,C,δ,hc,hC,hδ,hb⟩ := susceptibilityLaw_of_publishedVolume G hgraph hvolume hgap x
  refine ⟨c,C,δ,hc,hC,hδ,fun p hp hnear => ?_⟩
  rw [←(susceptibility_eq_integral G hgraph.locallyFinite hgraph.quasiTransitive p hp x).2]
  exact hb p hp hnear

theorem full_application_reduced_bs_oai [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G))
    (htheta : TrianglePercolationProbabilityInput (subdivision G))
    (hvolume : HutchcroftCriticalVolumeInput (subdivision G))
    (hradii : HutchcroftCriticalRadiiInput (subdivision G)) :
    MainConclusion G ∧ CriticalLawsConclusion G :=
  full_application_conditional_bs G hconn hloc hqt hh hutchcroft2019
    (firstMomentInput_of_volume (subdivision G) hvolume) htheta hvolume hradii

end Percolation.BenjaminiSchramm

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Percolation.BenjaminiSchramm.full_application_reduced_bs_oai.{u, v} := @OAI.Percolation.BenjaminiSchramm.full_application_reduced_bs_oai.{u, v}
