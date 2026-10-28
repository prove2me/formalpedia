-- Prove2me | solution 1 for OAI.Percolation.critical_rootTriangle_subpower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:01:42.07199+00:00
-- url     : https://prove2.me/submissions/1929838f-1269-42fc-9b23-20d1caa2ba13

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002
import Theorems.Thm_OAI_Percolation_almost_linear_susceptibility
import Theorems.Thm_OAI_Percolation_critical_large_contact_bound
import Theorems.Thm_OAI_Percolation_critical_root_power_integrable

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

section Countability


theorem exists_mem_reachBall {G : BondGraph V E} {x y : V}
    (h : Relation.ReflTransGen (Adj G) x y) : ∃ n, y ∈ reachBall G x n := by
  induction h with
  | refl => exact ⟨0, Set.mem_singleton _⟩
  | @tail y z _ hyz ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, Or.inr ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨y, hn, hyz⟩

end Countability

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

 
theorem operatorBounded_of_lt_pc [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : OperatorBounded G p := by
  obtain ⟨C,hC,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  obtain ⟨A,_,hA⟩ := exists_operator_of_row_column_bound (twoPoint G p) C hC
    (twoPoint_nonneg G p) hrow (fun y F => by
      simpa only [twoPoint_symm G p] using hrow y F)
  exact ⟨A,hA⟩

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

section GoodnessGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

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



end NonnegativeTransport

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
section WalkOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem matrixCoeff_real_symm (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : IsSelfAdjoint A) (x y : V) : (matrixCoeff A x y).re = (matrixCoeff A y x).re := by
  have h := congrArg Complex.re (matrixCoeff_adjoint A x y)
  simpa only [hA.star_eq,Complex.star_def,Complex.conj_re] using h

end WalkOrbitReturn
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

end FiniteStretchedTail
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

end ExteriorExplorationLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClosedClusterContacts
attribute [local instance] Classical.propDecidable Classical.decEq



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
        ite_true,ite_false,zero_mul]
    · simp only [hxa,false_and,ite_false,tsum_zero,zero_mul,mul_zero]
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
    by_cases h : G ey.1 = s(x,ey.2) <;> simp only [Set.mem_ofPred_eq,h,ite_true,ite_false]
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
      simp only [ha,hb,and_self,true_and,false_and,ite_true,ite_false,indexedEdgeKernel,tsum_zero]
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
  · simp only [fullLargeContact,h,not_true_eq_false,false_and,ite_false,ENNReal.ofReal_zero]
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
  · simp only [hd,not_true_eq_false,ite_false]
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [clusterPairKernel_edge G hloc ω (root i) y hd hω]
    unfold contactSquareLarge fullLargeContact
    by_cases hs : L ≤ min (cluster G ω (root i)).ncard (cluster G ω y).ncard
    · simp only [hd,hs,not_false_eq_true,true_and,ite_true,ENNReal.ofReal_natCast,pow_two]
    · simp only [hs,and_false,ite_false,ENNReal.ofReal_zero,mul_zero]

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
    · simp only [hd,not_true_eq_false,and_false,ite_false,mul_zero,tsum_zero]
    · rw [ite_eq_left hd,clusterPairKernel]
      apply tsum_congr; intro a
      apply tsum_congr; intro b
      by_cases h : Conn G ω x a ∧ Conn G ω y b
      · simp only [h.1,h.2,hd,not_false_eq_true,and_self,ite_true,mul_one]
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
  have hp3 : 0 ≤ T^3 := CStarAlgebra.pow_nonneg hpos 3
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
      · simp only [f,hW,hy,not_true_eq_false,and_false,ite_false,ite_true,zero_sub,
          bernoulliPolynomial_const]
        exact neg_nonpos.mpr (mul_nonneg hM (Nat.cast_nonneg _))
      · simp only [f,hW,hy,not_false_eq_true,and_self,ite_true,bernoulliPolynomial_sub,
          bernoulliPolynomial_const,bernoulliPolynomial_sum]
        apply sub_nonpos.mpr
        calc
          _ ≤ ∑ _a ∈ W, M := Finset.sum_le_sum fun a _ =>
            (finiteClusterWeight_expectation_le G _ (J a) (hJ a) y p (hs a)).trans (hb a)
          _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    · simp only [f,hW,false_and,ite_false,mul_zero,sub_zero,bernoulliPolynomial_zero]
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
    simp only [←hm x a,ha,false_and,ite_false,tsum_zero])]
  apply Finset.sum_congr rfl
  intro a ha
  rw [tsum_eq_sum (s := finiteRootComponent G ω y) (fun b hb => by
    simp only [←hm y b,hb,and_false,ite_false])]
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
  have hp3 := CStarAlgebra.pow_nonneg hpos 3
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
  · simp only [smallPairKernel,h,not_true_eq_false,and_false,ite_false]
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
  · simp only [hc,not_true_eq_false,ite_false,le_refl]
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
  · simp only [hc,not_true_eq_false,ite_false]
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
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw _ (CStarAlgebra.pow_nonneg hpos 3))).1
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
  · simp only [hxy,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero]
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
  · simp only [fullLargeContact,hxy,not_true_eq_false,false_and,ite_false,ENNReal.ofReal_zero]
  · rw [ite_eq_left hxy,clusterPairKernel_edge G hloc ω x y hxy hω]
    simp only [fullLargeContact,hxy,Nat.zero_le,not_false_eq_true,and_self,ite_true,ENNReal.ofReal_natCast]

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
  · simp only [hd,not_true_eq_false,ite_false]
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [clusterPairKernel_edge G hloc ω (root i) y hd hω]
    simp only [fullLargeContact,hd,not_false_eq_true,Nat.zero_le,and_self,ite_true,ENNReal.ofReal_natCast]
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

 
theorem critical_rootTriangleSqrt_derivative
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

 
namespace Percolation
section TraceExponents

lemma trace_exponent_choices (η : ℝ) (hη : 0 < η) :
    ∃ α ε ρ lambda : ℝ, 0 < α ∧ α < 1/2 ∧ 0 < ε ∧ 0 < ρ ∧ 0 < lambda ∧
      (1:ℝ)/2+ε-2*α < 0 ∧ lambda*(1-α) < 1 ∧
      lambda*(((1:ℝ)/2+ε-2*α)/2) + (3:ℝ)/2*(1+ρ) < 1+η/2 := by
  let ζ := min (1/2:ℝ) η
  let d := min (ζ/16) (η/32)
  have hz : 0 < ζ := lt_min (by norm_num) hη
  have hz1 : ζ ≤ 1/2 := min_le_left _ _
  have hze : ζ ≤ η := min_le_right _ _
  have hd : 0 < d := lt_min (div_pos hz (by norm_num)) (div_pos hη (by norm_num))
  have hdz : d ≤ ζ/16 := min_le_left _ _
  have hde : d ≤ η/32 := min_le_right _ _
  have hzd : 0 ≤ ζ*d := mul_nonneg hz.le hd.le
  refine ⟨1/2-d,d,d,2-ζ,?_,?_,hd,hd,?_,?_,?_,?_⟩ <;> nlinarith

lemma trace_scale_large_term (δ D lambda r ρ : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) :
    (δ^(-lambda))^(r/2)*(D*δ^(-1-ρ))^((3:ℝ)/2) =
      D^((3:ℝ)/2)*δ^(-(lambda*(r/2)+(3:ℝ)/2*(1+ρ))) := by
  rw [Real.mul_rpow hD (Real.rpow_nonneg hδ.le _),←Real.rpow_mul hδ.le,←Real.rpow_mul hδ.le]
  rw [show δ^(-lambda*(r/2))*(D^((3:ℝ)/2)*δ^((-1-ρ)*((3:ℝ)/2))) =
    D^((3:ℝ)/2)*(δ^(-lambda*(r/2))*δ^((-1-ρ)*((3:ℝ)/2))) by ring,
    ←Real.rpow_add hδ]
  congr 2
  ring

lemma trace_scale_derivative (δ D C lambda r ρ α b b' m : ℝ)
    (hδ : 0 < δ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb : 0 ≤ b) (hm : 0 ≤ m) (hmD : m ≤ D*δ^(-1-ρ))
    (hd : b' ≤ C*(δ^(-lambda))^(1-α)*b + C*(δ^(-lambda))^(r/2)*m^((3:ℝ)/2)) :
    b' ≤ (C*(1+D^((3:ℝ)/2)))*δ^(-(lambda*(1-α)))*b +
      (C*(1+D^((3:ℝ)/2)))*δ^(-(lambda*(r/2)+(3:ℝ)/2*(1+ρ))) := by
  have hs := Real.rpow_le_rpow hm hmD (by norm_num : (0:ℝ) ≤ 3/2)
  have he : (δ^(-lambda))^(1-α) = δ^(-(lambda*(1-α))) := by rw [←Real.rpow_mul hδ.le]; congr 1; ring
  have hc1 : C ≤ C*(1+D^((3:ℝ)/2)) := by nlinarith [Real.rpow_nonneg hD ((3:ℝ)/2)]
  have hc2 : C*D^((3:ℝ)/2) ≤ C*(1+D^((3:ℝ)/2)) := by nlinarith
  calc
    b' ≤ C*(δ^(-lambda))^(1-α)*b + C*(δ^(-lambda))^(r/2)*m^((3:ℝ)/2) := hd
    _ ≤ C*(δ^(-lambda))^(1-α)*b + C*(δ^(-lambda))^(r/2)*(D*δ^(-1-ρ))^((3:ℝ)/2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (mul_nonneg hC (Real.rpow_nonneg (Real.rpow_nonneg hδ.le _) _)))
    _ = C*δ^(-(lambda*(1-α)))*b + (C*D^((3:ℝ)/2))*δ^(-(lambda*(r/2)+(3:ℝ)/2*(1+ρ))) := by
      rw [he,mul_assoc C ((δ^(-lambda))^(r/2)),trace_scale_large_term δ D lambda r ρ hδ hD]; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hδ.le _)) hb)
      (mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hδ.le _))

end TraceExponents
end Percolation

 
namespace Percolation
section IntegratingFactor

lemma hasDerivAt_gap_rpow (q r t : ℝ) (ht : t < q) :
    HasDerivAt (fun x : ℝ => (q-x)^r) (-r*(q-t)^(r-1)) t := by
  convert! ((hasDerivAt_const t q).sub (hasDerivAt_id t)).rpow_const
    (Or.inl (ne_of_gt (sub_pos.mpr ht))) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Pi.sub_apply, id_eq]
  ring

lemma hasDerivAt_traceIntegratingFactor (q C A t : ℝ) (hA : A < 1) (ht : t < q) :
    HasDerivAt (traceIntegratingFactor q C A)
      (-C*(q-t)^(-A)*traceIntegratingFactor q C A t) t := by
  have hd := ((hasDerivAt_gap_rpow q (1-A) t ht).const_mul (C/(1-A))).exp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  unfold traceIntegratingFactor
  rw [show 1-A-1 = -A by ring]
  field_simp [ne_of_gt (sub_pos.mpr hA)]

lemma traceIntegratingFactor_bounds (q C A t : ℝ) (hC : 0 ≤ C) (hA : A < 1)
    (ht : t < q) (hd : q-t ≤ 1) :
    1 ≤ traceIntegratingFactor q C A t ∧
      traceIntegratingFactor q C A t ≤ Real.exp (C/(1-A)) := by
  have hk : 0 ≤ C/(1-A) := div_nonneg hC (sub_pos.mpr hA).le
  have hr : 0 ≤ (q-t)^(1-A) := Real.rpow_nonneg (sub_pos.mpr ht).le _
  constructor
  · exact Real.one_le_exp (mul_nonneg hk hr)
  · apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right hk (Real.rpow_le_one (sub_pos.mpr ht).le hd (sub_pos.mpr hA).le)

lemma hasDerivAt_traceComparison (f : ℝ → ℝ) (q C A κ t : ℝ)
    (hA : A < 1) (hκ : 0 < κ) (ht : t < q) (hf : DifferentiableAt ℝ f t) :
    HasDerivAt (fun x => traceIntegratingFactor q C A x*f x -
      (C*Real.exp (C/(1-A))/κ)*(q-x)^(-κ))
      (traceIntegratingFactor q C A t*(deriv f t-C*(q-t)^(-A)*f t) -
        C*Real.exp (C/(1-A))*(q-t)^(-κ-1)) t := by
  have hh := ((hasDerivAt_traceIntegratingFactor q C A t hA ht).mul hf.hasDerivAt).sub
    ((hasDerivAt_gap_rpow q (-κ) t ht).const_mul (C*Real.exp (C/(1-A))/κ))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [ne_of_gt hκ]
  ring

 

theorem singular_ode_subpower (f : ℝ → ℝ) (q s C A B κ : ℝ)
    (hs : s < q) (hqs : q-s ≤ 1) (hC : 0 < C) (hA : A < 1)
    (hκ : 0 < κ) (hB : B ≤ 1+κ)
    (hf : ∀ t ∈ Set.Ico s q, DifferentiableAt ℝ f t)
    (hn : ∀ t ∈ Set.Ico s q, 0 ≤ f t)
    (hd : ∀ t ∈ Set.Ico s q,
      deriv f t ≤ C*(q-t)^(-A)*f t + C*(q-t)^(-B)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Set.Ico s q, f t ≤ K*(q-t)^(-κ) := by
  let M := Real.exp (C/(1-A))
  let Q := C*M/κ
  let g := fun t => traceIntegratingFactor q C A t*f t - Q*(q-t)^(-κ)
  have hM : 0 < M := Real.exp_pos _
  have hQ : 0 < Q := div_pos (mul_pos hC hM) hκ
  have hgs (t : ℝ) (ht : t ∈ Set.Ico s q) :
      HasDerivAt g (traceIntegratingFactor q C A t*(deriv f t-C*(q-t)^(-A)*f t) -
        C*M*(q-t)^(-κ-1)) t := hasDerivAt_traceComparison f q C A κ t hA hκ ht.2 (hf t ht)
  have hgn (t : ℝ) (ht : t ∈ Set.Ico s q) : deriv g t ≤ 0 := by
    have htq : 0 < q-t := sub_pos.mpr ht.2
    have ht1 : q-t ≤ 1 := by linarith [ht.1]
    obtain ⟨hw,hwM⟩ := traceIntegratingFactor_bounds q C A t hC.le hA ht.2 ht1
    have hpow : (q-t)^(-B) ≤ (q-t)^(-κ-1) :=
      Real.rpow_le_rpow_of_exponent_ge htq ht1 (by linarith)
    have hmul := mul_le_mul_of_nonneg_left (hd t ht) (show 0 ≤ traceIntegratingFactor q C A t by linarith)
    have h₂ := mul_le_mul_of_nonneg_right hwM (mul_nonneg hC.le (Real.rpow_nonneg htq.le (-B)))
    have h₃ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC.le hM.le)
    rw [(hgs t ht).deriv]
    dsimp only [M] at hM ⊢
    dsimp only [M] at h₃
    nlinarith
  have hgmono : AntitoneOn g (Set.Ico s q) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico s q)
    · intro t ht
      exact (hgs t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hgs t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      exact hgn t (interior_subset ht)
  have hsI : s ∈ Set.Ico s q := ⟨le_rfl,hs⟩
  refine ⟨M*f s+Q,add_pos_of_nonneg_of_pos (mul_nonneg hM.le (hn s hsI)) hQ,?_⟩
  intro t ht
  have htq : 0 < q-t := sub_pos.mpr ht.2
  have ht1 : q-t ≤ 1 := by linarith [ht.1]
  obtain ⟨hwt,_⟩ := traceIntegratingFactor_bounds q C A t hC.le hA ht.2 ht1
  obtain ⟨_,hws⟩ := traceIntegratingFactor_bounds q C A s hC.le hA hs hqs
  have hmono := hgmono hsI ht ht.1
  have hneg : 0 ≤ Q*(q-s)^(-κ) := mul_nonneg hQ.le (Real.rpow_nonneg (sub_pos.mpr hs).le _)
  have hft := mul_le_mul_of_nonneg_right hwt (hn t ht)
  have hfs := mul_le_mul_of_nonneg_right hws (hn s hsI)
  have hpow : 1 ≤ (q-t)^(-κ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos htq ht1 (neg_nonpos.mpr hκ.le)
  have hscale := mul_le_mul_of_nonneg_left hpow (mul_nonneg hM.le (hn s hsI))
  dsimp only [g] at hmono
  dsimp only [M] at hscale ⊢
  nlinarith

end IntegratingFactor
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SubpowerTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_rootTriangle_subpower_oai
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
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      rootTriangle G root weight (p:ℝ) ≤ K*((pc G:ℝ)-(p:ℝ))^(-η) := by
  obtain ⟨α,ε,ρ,lambda,hα,hα1,hε,hρ,hlambda,hr,hA,hB⟩ := trace_exponent_choices η hη
  obtain ⟨C₀,hC₀,hder⟩ := critical_rootTriangleSqrt_derivative G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  obtain ⟨D,hD,hχ⟩ := almost_linear_susceptibility G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin ρ hρ
  let C := C₀*(1+D^((3:ℝ)/2))
  let A := lambda*(1-α)
  let B := lambda*(((1:ℝ)/2+ε-2*α)/2)+(3:ℝ)/2*(1+ρ)
  have hC : 0 < C := mul_pos hC₀ (by linarith [Real.rpow_nonneg hD.le ((3:ℝ)/2)])
  have hunit (t : ℝ) (ht : t ∈ Set.Ico ((pc G:ℝ)/2) (pc G:ℝ)) : t ∈ unitInterval :=
    ⟨(half_pos hp₀).le.trans ht.1,ht.2.le.trans (pc G).2.2⟩
  have hdf (t : ℝ) (ht : t ∈ Set.Ico ((pc G:ℝ)/2) (pc G:ℝ)) :
      DifferentiableAt ℝ (rootTriangleSqrt G root weight) t := by
    exact (hasDerivAt_rootTriangleSqrt G hloc hqt root weight (fun i => (hw i).le) hw1
      ⟨t,hunit t ht⟩ ((half_pos hp₀).trans_le ht.1) ht.2).differentiableAt
  have hod (t : ℝ) (ht : t ∈ Set.Ico ((pc G:ℝ)/2) (pc G:ℝ)) :
      deriv (rootTriangleSqrt G root weight) t ≤ C*((pc G:ℝ)-t)^(-A)*rootTriangleSqrt G root weight t +
        C*((pc G:ℝ)-t)^(-B) := by
    let p : unitInterval := ⟨t,hunit t ht⟩
    have hδ : 0 < (pc G:ℝ)-t := sub_pos.mpr ht.2
    have hδ1 : (pc G:ℝ)-t ≤ 1 := by linarith [(pc G).2.2,ht.1]
    obtain ⟨T,hT⟩ := operatorBounded_of_lt_pc G hloc hqt p ht.2
    have hm := hT.norm_le_susceptibility_bound G hloc hqt p ht.2 T (D*((pc G:ℝ)-t)^(-1-ρ))
      (mul_nonneg hD.le (Real.rpow_nonneg hδ.le _)) (hχ p ht.2)
    have hL : 1 ≤ (((pc G:ℝ)-t)^(-lambda)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hlambda.le)
    exact trace_scale_derivative ((pc G:ℝ)-t) D C₀ lambda ((1:ℝ)/2+ε-2*α) ρ α
      (rootTriangleSqrt G root weight t) (deriv (rootTriangleSqrt G root weight) t) ‖T‖
      hδ hD.le hC₀.le (Real.sqrt_nonneg _) (norm_nonneg _) hm
      (hder p ht.1 ht.2 T hT (((pc G:ℝ)-t)^(-lambda)) hL)
  obtain ⟨K,hK,hb⟩ := singular_ode_subpower (rootTriangleSqrt G root weight) (pc G) ((pc G:ℝ)/2)
    C A B (η/2) (by linarith) (by linarith [(pc G).2.2]) hC hA (half_pos hη) hB.le
    hdf (fun _ _ => Real.sqrt_nonneg _) hod
  refine ⟨K^2,sq_pos_of_pos hK,?_⟩
  intro p hp hpq
  have ha : 0 ≤ rootTriangle G root weight (p:ℝ) :=
    le_trans (by norm_num) (rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 p hpq)
  have hb' := pow_le_pow_left₀ (Real.sqrt_nonneg (rootTriangle G root weight (p:ℝ))) (hb p ⟨hp,hpq⟩) 2
  change (Real.sqrt (rootTriangle G root weight (p:ℝ)))^2 ≤ _ at hb'
  rw [Real.sq_sqrt ha,mul_pow] at hb'
  have he : (((pc G:ℝ)-(p:ℝ))^(-(η/2)))^2 = ((pc G:ℝ)-(p:ℝ))^(-η) := by
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul (sub_pos.mpr (show (p:ℝ)<(pc G:ℝ) from hpq)).le]
    congr 1
    norm_num
  rw [he] at hb'
  exact hb'

end SubpowerTrace
end Percolation


end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.critical_rootTriangle_subpower_oai.{u, v, u_1} := @OAI.Percolation.critical_rootTriangle_subpower_oai.{u, v, u_1}
