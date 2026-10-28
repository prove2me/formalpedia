-- Prove2me | solution 1 for OAI.Percolation.exists_finite_scale_obstruction_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:49:19.176871+00:00
-- url     : https://prove2.me/submissions/588e65de-ec13-4758-ad7a-7b7410944d7c

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_exists_uniform_averaged_decrease_bs
import Theorems.Thm_OAI_Percolation_twoPoint_double_restricted_bound_bs

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

 theorem finite_steps (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Set.Finite {ey : E × V | G ey.1 = s(x,ey.2)} := by
  apply ((hloc x).prod (finite_neighbors hloc x)).subset
  rintro ⟨e,y⟩ he
  change G e = s(x,y) at he
  exact ⟨by change x ∈ G e; rw [he]; simp, e, he⟩

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

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


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

end FiniteQuadraticForms

section SymmetricWalk
attribute [local instance] Classical.propDecidable



 theorem walkKernel_symmetric (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : walkKernel G hloc a x y = walkKernel G hloc a y x := by
  have ha : Adj G x y ↔ Adj G y x := ⟨adj_symm G,adj_symm G⟩
  by_cases h : x = y
  · subst y; rfl
  · simp [walkKernel,h,Ne.symm h,ha]

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

end SymmetricWalk

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

theorem KernelInvariant.star {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) :
    KernelInvariant Γ (star A) := by
  intro a ha x y
  simp only [matrixCoeff_adjoint, hA a ha]

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

theorem rootTrace_conjugate_le {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) :
    rootTrace root weight (B*A*star B) ≤ ((‖B‖ ^ 2 : ℝ) : ℂ) * rootTrace root weight A := by
  calc
    rootTrace root weight (B*A*star B) = rootTrace root weight (star B*(B*A)) :=
      rootTrace_cyclic root weight htr (B*A) (star B) (hB.mul hA) hB.star
    _ = rootTrace root weight ((star B*B)*A) := by rw [mul_assoc]
    _ ≤ (‖star B*B‖ : ℂ) * rootTrace root weight A :=
      rootTrace_positive_mul_le root weight htr hw A (star B*B) hA (hB.star.mul hB)
        hApos (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg B))
    _ = ((‖B‖ ^ 2 : ℝ) : ℂ) * rootTrace root weight A := by
      have hnorm := CStarRing.norm_star_mul_self (x := B)
      have hn : ‖star B * B‖ = ‖B‖ ^ 2 := by
        convert hnorm using 1; simp only [pow_two]
      rw [hn]

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

 

theorem matrixCoeff_smoothing {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) (hdiag : ∀ y, matrixCoeff A y y = 1) (x y : V) :
    ‖matrixCoeff (B*A) x y‖ ≤ Real.sqrt c * ‖B‖ := by
  have htA : rootTrace root weight A = 1 := by
    simp only [rootTrace, hdiag, mul_one, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]
  have hD : 0 ≤ B*A*star B := star_right_conjugate_nonneg hApos B
  have hi : KernelInvariant Γ (B*A*star B) := (hB.mul hA).mul hB.star
  have ht := rootTrace_conjugate_le root weight htr hw A B hA hB hApos
  rw [htA, mul_one] at ht
  have hd : matrixCoeff (B*A*star B) x x ≤ ((c * ‖B‖^2 : ℝ) : ℂ) := by
    calc
      _ ≤ (c : ℂ) * rootTrace root weight (B*A*star B) :=
        rootTrace_diag_le root weight hcov hw c hc hmin _ hi hD x
      _ ≤ (c : ℂ) * ((‖B‖^2 : ℝ) : ℂ) :=
        mul_le_mul_of_nonneg_left ht (by exact_mod_cast hc)
      _ = _ := by push_cast; rfl
  have hd' : (matrixCoeff (B*A*star B) x x).re ≤ c * ‖B‖^2 :=
    (Complex.le_def.mp hd).1
  have hs : ‖matrixCoeff (B*A) x y‖ ^ 2 ≤ c * ‖B‖ ^ 2 := by
    have hh := matrixCoeff_positive_product_norm_sq_le A B hApos x y
    rw [hdiag, Complex.one_re, mul_one] at hh
    exact hh.trans hd'
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow, Real.sq_sqrt hc]

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

 

theorem twoPoint_operator_smoothing [Countable V] [Countable E] [Nonempty V] {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (A P : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hP : KernelInvariant (vertexAut G) P) (l : ℕ) (x y : V) :
    ‖matrixCoeff (P^l*A) x y‖ ≤ Real.sqrt c * ‖P‖^l := by
  have hdiag (y : V) : matrixCoeff A y y = 1 := by
    change A (lp.single 2 y (1:ℂ)) y = 1
    rw [hA y y, twoPoint_self, Complex.ofReal_one]
  have h := matrixCoeff_smoothing root weight htr hcov hw hsum c hc hmin A (P^l)
    (hA.invariant G p A) (hP.pow l) ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (hA.isPositive G p A)) hdiag x y
  have hn (n : ℕ) : ‖P^n‖ ≤ ‖P‖^n := by
    induction n with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg P))
  exact h.trans (mul_le_mul_of_nonneg_left (hn l) (Real.sqrt_nonneg c))
end InvariantPercolationOperators

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_TrajectoryMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Amplification
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
section FiniteOrbitPartition
attribute [local instance] Classical.propDecidable Classical.decEq



theorem vertexOrbit_eq_of_mem (G : BondGraph V E) (o x : V) (hx : x ∈ vertexOrbit G o) :
    vertexOrbit G x = vertexOrbit G o := by
  obtain ⟨a,b,hab,rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.trans c,b.trans d,isAut_trans G hab hcd,hc⟩
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.symm.trans c,b.symm.trans d,isAut_trans G (isAut_symm G hab) hcd,by simpa using hc⟩



end FiniteOrbitPartition
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
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
section OrbitKernelTransport
attribute [local instance] Classical.propDecidable Classical.decEq



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

theorem susceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ susceptibility G p x := by
  have hd : twoPoint G p x x = 1 := by
    have he : {ω : Set E | Conn G ω x x} = Set.univ := Set.eq_univ_of_forall (fun _ => conn_refl G _ x)
    simp only [twoPoint,he,measure_univ,ENNReal.toReal_one]
  rw [←hd]
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).le_tsum x (fun _ _ => twoPoint_nonneg G p _ _)


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



end ExteriorConnectionIndependence
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_DistinctMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
section OrientedPivotalConnections
attribute [local instance] Classical.propDecidable Classical.decEq



theorem measurableSet_orientedPivotalEvent [Countable V] [Countable E]
    (G : BondGraph V E) (x y a b : V) : MeasurableSet (orientedPivotalEvent G x y a b) :=
  (measurableSet_conn G x a).inter ((measurableSet_conn G b y).inter (measurableSet_conn G a b).compl)


theorem orientedPivotalEvent_subset_disjoint (G : BondGraph V E) (x y a b : V) :
    orientedPivotalEvent G x y a b ⊆
      DisjointOccurrence {ω | Conn G ω x a} {ω | Conn G ω b y} := by
  intro ω hω
  have hx : x ∈ cluster G ω a := conn_symm G ω hω.1
  have hb : b ∉ cluster G ω a := hω.2.2
  obtain ⟨Q,hQ,hQa⟩ := finiteWitness_conn G x a _ (conn_restrict_cluster G ω a hx hω.1)
  obtain ⟨R,hR,hRb⟩ := finiteWitness_conn G b y _ (conn_restrict_cluster_compl G ω a hb hω.2.1)
  refine ⟨Q,R,fun e he => (hQ he).1,fun e he => (hR he).1,?_,hQa,hRb⟩
  apply Finset.disjoint_left.mpr
  intro e heQ heR
  obtain ⟨⟨z,w⟩,he⟩ := Quot.exists_rep (G e)
  have hz : z ∈ G e := by rw [←he]; exact Sym2.mem_mk_left z w
  exact (hR heR).2 z hz ((hQ heQ).2 z hz)

end OrientedPivotalConnections
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
open MeasureTheory
section UniformLargeContacts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incident_ncard_le_degree (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    {e | x ∈ G e}.ncard ≤ degree G x := by
  have he : ((hloc x).toFinset.filter fun e => x ∈ G e) = (hloc x).toFinset := by
    ext e
    simp only [Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,and_self]
  simpa only [he,←Set.ncard_eq_toFinset_card] using incident_filter_card_le_degree G hloc (hloc x).toFinset x

end UniformLargeContacts
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
section NonnegativeOperatorDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem HasKernel.positiveRealMatrix (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) : PositiveRealMatrix T := by
  intro x y
  change (T (lp.single 2 y (1:ℂ)) x).im = 0 ∧ 0 ≤ (T (lp.single 2 y (1:ℂ)) x).re
  rw [hT x y]
  exact ⟨rfl,twoPoint_nonneg G p x y⟩

end NonnegativeOperatorDiagram
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
open MeasureTheory Filter
open scoped ENNReal
section RussoRows
attribute [local instance] Classical.propDecidable Classical.decEq



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

end RussoRows
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

end PositiveTriangleSeries
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RootTriangleRusso
attribute [local instance] Classical.propDecidable Classical.decEq


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

end TraceNumerics
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormRatio
attribute [local instance] Classical.propDecidable Classical.decEq



theorem susceptibility_bddAbove [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : BddAbove (Set.range (susceptibility G p)) := by
  obtain ⟨C,_,hC⟩ := subcritical_row_bound G hloc hqt p hp
  refine ⟨C,?_⟩
  rintro _ ⟨x,rfl⟩
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).tsum_le_of_sum_le (hC x)

theorem susceptibility_le_max [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    susceptibility G p x ≤ maxSusceptibility G p :=
  le_csSup (susceptibility_bddAbove G hloc hqt p hp) (Set.mem_range_self x)

theorem maxSusceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : 1 ≤ maxSusceptibility G p := by
  let x : V := Classical.choice inferInstance
  exact (susceptibility_one_le G hloc hqt p hp x).trans (susceptibility_le_max G hloc hqt p hp x)

theorem HasKernel.norm_le_maxSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : ‖T‖ ≤ maxSusceptibility G p :=
  hT.norm_le_susceptibility_bound G hloc hqt p hp T _
    (le_trans zero_le_one (maxSusceptibility_one_le G hloc hqt p hp))
    (susceptibility_le_max G hloc hqt p hp)

theorem HasKernel.norm_one_le [Countable E] [Nonempty V]
    (G : BondGraph V E) (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G p T) : 1 ≤ ‖T‖ := by
  let x : V := Classical.choice inferInstance
  have hd : twoPoint G p x x = 1 := twoPoint_self G p x
  have hh := (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (T (lp.single 2 x (1:ℂ))) x).trans (T.le_opNorm (lp.single 2 x (1:ℂ)))
  simpa [hT x x,hd,lp.norm_single] using hh

end NormRatio
end Percolation


namespace Percolation
universe u
section ChronologicalErasure
open List
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq



namespace HoldingWalk
variable {H : SimpleGraph V} {k : ℕ} {x y : V}

theorem mass_nonneg (P : V → V → ℝ) (hP : ∀ a b, 0 ≤ P a b) (w : HoldingWalk H k x y) :
    0 ≤ w.mass P := by
  induction w with
  | nil => exact zero_le_one
  | hold w ih => exact mul_nonneg (hP _ _) ih
  | step h w ih => exact mul_nonneg (hP _ _) ih

theorem length_vertices (w : HoldingWalk H k x y) : w.vertices.length = k+1 := by
  induction w with
  | nil => rfl
  | hold w ih => simpa only [vertices,List.length_cons] using congrArg (fun n => n+1) ih
  | step h w ih => simpa only [vertices,List.length_cons] using congrArg (fun n => n+1) ih

theorem withoutHolds_length (w : HoldingWalk H k x y) : w.withoutHolds.length ≤ k := by
  induction w with
  | nil => simp [withoutHolds]
  | hold w ih => exact ih.trans (Nat.le_succ _)
  | step h w ih => simpa only [withoutHolds,SimpleGraph.Walk.length_cons] using Nat.succ_le_succ ih

theorem withoutHolds_support (w : HoldingWalk H k x y) : w.withoutHolds.support <+ w.vertices := by
  induction w with
  | nil => exact List.Sublist.refl _
  | hold w ih => exact ih.cons _
  | step h w ih => exact ih.cons_cons _



theorem erase_isPath (w : HoldingWalk H k x y) : w.erase.IsPath :=
  w.withoutHolds.reverse.bypass_isPath.reverse

theorem erase_length (w : HoldingWalk H k x y) : w.erase.length ≤ k := by
  have hh := w.withoutHolds.reverse.length_bypass_le_length
  simpa only [erase,SimpleGraph.Walk.length_reverse] using hh.trans (by simpa using w.withoutHolds_length)

theorem erase_support (w : HoldingWalk H k x y) : w.erase.support <+ w.vertices := by
  have hh := w.withoutHolds.reverse.support_bypass_sublist_support.reverse
  simp only [SimpleGraph.Walk.support_reverse,List.reverse_reverse] at hh
  simpa only [erase,SimpleGraph.Walk.support_reverse] using hh.trans w.withoutHolds_support

end HoldingWalk
end ChronologicalErasure
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorMonotonicity
attribute [local instance] Classical.propDecidable Classical.decEq



lemma pivotal_restrict_of_conn (G : BondGraph V E) {S T : Set E} (hST : S ⊆ T)
    {x y : V} (hc : Conn G S x y) (e : E) (hp : ¬Conn G (T \ {e}) x y) :
    e ∈ S ∧ ¬Conn G (S \ {e}) x y := by
  constructor
  · by_contra he
    apply hp
    apply conn_mono G ?_ hc
    intro d hd
    exact ⟨hST hd,fun hde => he ((Set.mem_singleton_iff.mp hde) ▸ hd)⟩
  · intro h
    exact hp (conn_mono G (Set.sdiff_subset_sdiff_left hST) h)

 

theorem corridorCounted_restrict (G : BondGraph V E) (retained blockers : Set E)
    {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω') (x y : V)
    (hc : Conn G (ω ∩ internalEdges G D) x y)
    (ht : corridorCounted G retained blockers D' ω' x y) :
    corridorCounted G retained blockers D ω x y := by
  have hs : ω ∩ internalEdges G D ⊆ ω' ∩ internalEdges G D' :=
    Set.inter_subset_inter hω (internalEdges_mono G hD)
  refine ⟨hc,fun e he => pivotal_restrict_of_conn G hs hc e (ht.2.1 e he).2,?_⟩
  exact ht.2.2.mono_right hs

lemma corridorCounted_symm (G : BondGraph V E) (retained blockers : Set E)
    (D : Set V) (ω : Set E) (x y : V) :
    corridorCounted G retained blockers D ω x y ↔ corridorCounted G retained blockers D ω y x := by
  constructor <;> rintro ⟨hc,hp,hb⟩
  · exact ⟨conn_symm G _ hc,fun e he => ⟨(hp e he).1,fun hc => (hp e he).2 (conn_symm G _ hc)⟩,hb⟩
  · exact ⟨conn_symm G _ hc,fun e he => ⟨(hp e he).1,fun hc => (hp e he).2 (conn_symm G _ hc)⟩,hb⟩

 

theorem measurableSet_corridorCounted [Countable E] (G : BondGraph V E)
    (retained blockers : Set E) (D : Set V) (x y : V) :
    MeasurableSet {ω | corridorCounted G retained blockers D ω x y} := by
  have hmem (e : E) : MeasurableSet {ω : Set E | e ∈ ω ∩ internalEdges G D} := by
    by_cases he : e ∈ internalEdges G D
    · simpa only [Set.mem_inter_iff,he,and_true] using measurableSet_mem e
    · simp only [Set.mem_inter_iff,he,and_false,Set.ofPred_false]; exact MeasurableSet.empty
  have hp (e : E) : MeasurableSet {ω : Set E | e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y} := by
    apply (hmem e).inter
    have heq (ω : Set E) : (ω ∩ internalEdges G D) \ {e} = ω ∩ (internalEdges G D \ {e}) := by
      ext d; simp only [Set.mem_inter_iff,Set.mem_sdiff]; tauto
    simp_rw [heq]
    exact (measurableSet_restrictedConn G _ x y).compl
  have hb : MeasurableSet {ω : Set E | Disjoint blockers (ω ∩ internalEdges G D)} := by
    simp only [Set.disjoint_left,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun (_ : e ∈ blockers) => (hmem e).compl))
  have hkeep : MeasurableSet {ω : Set E | ∀ e ∈ retained, e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun (_ : e ∈ retained) => hp e))
  exact (measurableSet_restrictedConn G _ x y).inter (hkeep.inter hb)

end CorridorMonotonicity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralCorridors
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem path_isPath (w : RawCorridor G k) : w.path.IsPath := w.2.2.erase_isPath

theorem path_length (w : RawCorridor G k) : w.path.length ≤ k := w.2.2.erase_length

theorem retained_disjoint_blockers (w : RawCorridor G k) : Disjoint w.retained w.blockers := by
  exact Set.disjoint_left.mpr (fun e he hb => hb.2 he)

theorem weight_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (w : RawCorridor G k) : 0 ≤ w.weight P p := by
  exact mul_nonneg (mul_nonneg (w.2.2.mass_nonneg P hP) (inv_nonneg.mpr (pow_nonneg p.2.1 _)))
    (inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr p.2.2) _))

end RawCorridor
end LiteralCorridors
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Corridors
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorEligibility
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem edge_has_label (w : RawCorridor G k) (s : Sym2 V) (hs : s ∈ w.path.edges) :
    ∃ e ∈ w.retained, G e = s := by
  induction s using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨_,e,_,he⟩ := w.path.adj_of_mem_edges hs
    exact ⟨e,by simpa only [retained,Set.mem_ofPred_eq,he] using hs,he⟩

theorem image_retained (w : RawCorridor G k) : G '' w.retained = {s | s ∈ w.path.edges} := by
  ext s
  constructor
  · rintro ⟨e,he,rfl⟩; exact he
  · exact w.edge_has_label s

theorem retained_ncard (hG : Function.Injective G) (w : RawCorridor G k) :
    w.retained.ncard = w.path.length := by
  rw [←hG.injOn.ncard_image (s := w.retained),w.image_retained]
  have hh := List.toFinset_card_of_nodup w.path_isPath.isTrail.edges_nodup
  simpa only [←List.coe_toFinset,Set.ncard_coe_finset,SimpleGraph.Walk.length_edges] using hh

 

theorem support_subset_of_retained (w : RawCorridor G k) (hlen : 0 < w.path.length)
    (D : Set V) (he : w.retained ⊆ internalEdges G D) :
    ∀ z ∈ w.path.support, z ∈ D := by
  intro z hz
  obtain ⟨s,hs,hzs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hlen)).mp hz
  obtain ⟨e,he',hGe⟩ := w.edge_has_label s hs
  exact he he' z (hGe.symm ▸ hzs)

theorem retained_incident_interior (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (e : E) (he : e ∈ w.retained) : ∃ z ∈ w.interior, z ∈ G e := by
  change G e ∈ w.path.edges at he
  generalize hab : G e = s at he
  induction s using Sym2.inductionOn with
  | _ a b =>
    have hedge : s(a,b) ∈ w.path.edges := he
    have ha := w.path.fst_mem_support_of_mem_edges hedge
    have hb := w.path.snd_mem_support_of_mem_edges hedge
    have habne : a ≠ b := (w.path.adj_of_mem_edges hedge).1
    by_contra hn
    have hna : a ∉ w.interior := fun hi => hn ⟨a,hi,by simp⟩
    have hnb : b ∉ w.interior := fun hi => hn ⟨b,hi,by simp⟩
    have hax : a = w.base ∨ a = w.endpoint := by simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,ha,true_and,Finset.mem_insert,Finset.mem_singleton,not_not] using hna
    have hbx : b = w.base ∨ b = w.endpoint := by simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,hb,true_and,Finset.mem_insert,Finset.mem_singleton,not_not] using hnb
    have hedge' : s(w.base,w.endpoint) ∈ w.path.edges := by
      rcases hax with rfl | rfl <;> rcases hbx with rfl | rfl
      · exact (habne rfl).elim
      · exact hedge
      · simpa only [Sym2.eq_swap] using hedge
      · exact (habne rfl).elim
    have hh := w.path_isPath.length_eq_one_of_mem_edges hedge'
    omega

theorem specified_disjoint_exterior (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) :
    Disjoint (w.retained ∪ w.blockers) (internalEdges G (w.interior : Set V)ᶜ) := by
  apply Set.disjoint_left.mpr
  intro e he hx
  obtain ⟨z,hz,he⟩ := he.elim (w.retained_incident_interior hlen e) (fun hb => hb.1)
  exact hx z he hz

end RawCorridor
end CorridorEligibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactCorridorPattern
attribute [local instance] Classical.propDecidable Classical.decEq

theorem edgePattern_eq_restriction (A B : Finset E) (hAB : Disjoint A B) :
    edgePattern A B = {ω | ω ∩ ((A ∪ B : Finset E) : Set E) = (A : Set E)} := by
  ext ω
  constructor
  · rintro ⟨ha,hb⟩
    apply Set.Subset.antisymm
    · rintro e ⟨he,heQ⟩
      rcases Finset.mem_union.mp heQ with h | h
      · exact h
      · exact (Set.disjoint_left.mp hb h he).elim
    · intro e he
      exact ⟨ha he,Finset.mem_union_left _ he⟩
  · intro h
    constructor
    · intro e he
      exact ((Set.ext_iff.mp h e).mpr he).1
    · apply Set.disjoint_left.mpr
      intro e he hw
      have ha : e ∈ A := (Set.ext_iff.mp h e).mp ⟨hw,Finset.mem_union_right _ he⟩
      exact Finset.disjoint_left.mp hAB ha he

theorem measurableSet_edgePattern (A B : Finset E) (hAB : Disjoint A B) :
    MeasurableSet (edgePattern A B) := by
  rw [edgePattern_eq_restriction A B hAB]
  exact measurableSet_finite_restriction (A∪B) {(A:Set E)}

 
theorem edgePattern_probability (A B : Finset E) (hAB : Disjoint A B) (p : unitInterval) :
    (law p).real (edgePattern A B) = (p:ℝ)^A.card*(1-(p:ℝ))^B.card := by
  let f : Set E → ℝ := fun ω => if ω ∈ edgePattern A B then 1 else 0
  have hf (ω : Set E) : f ω = f (ω ∩ ((A∪B:Finset E):Set E)) := by
    simp only [f,edgePattern_eq_restriction A B hAB,Set.mem_ofPred_eq,Set.inter_assoc,Set.inter_self]
  rw [←integral_event_indicator p _ (measurableSet_edgePattern A B hAB)]
  change (∫ ω, f ω ∂law p) = _
  rw [integral_eq_bernoulliPolynomial (A∪B) p f hf]
  trans bernoulliPolynomial (A∪B) (fun η => if η=A then 1 else 0) p
  · apply bernoulliPolynomial_congr
    intro η hη
    have he : (η:Set E) ∩ ((A∪B:Finset E):Set E) = (η:Set E) :=
      Set.inter_eq_left.mpr hη
    simp only [f,edgePattern_eq_restriction A B hAB,Set.mem_ofPred_eq,he,Finset.coe_inj]
  · simp only [bernoulliPolynomial,ite_mul,zero_mul,one_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_powerset,Finset.subset_union_left,if_true,Finset.card_union_of_disjoint hAB,
      Nat.add_sub_cancel_left]

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem calibrationEvent_eq (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) : w.calibrationEvent =
      edgePattern (w.retained_finite hG).toFinset (w.blockers_finite hloc).toFinset := by
  simp only [calibrationEvent,edgePattern,Set.Finite.coe_toFinset]

theorem calibration_probability (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (p : unitInterval) :
    (law p).real w.calibrationEvent = (p:ℝ)^w.path.length*(1-(p:ℝ))^w.blockers.ncard := by
  rw [w.calibrationEvent_eq hG hloc,edgePattern_probability]
  · rw [←Set.ncard_eq_toFinset_card w.retained (w.retained_finite hG),←Set.ncard_eq_toFinset_card w.blockers (w.blockers_finite hloc),w.retained_ncard hG]
  · apply Finset.disjoint_left.mpr
    intro e he hb
    exact Set.disjoint_left.mp w.retained_disjoint_blockers
      ((w.retained_finite hG).mem_toFinset.mp he) ((w.blockers_finite hloc).mem_toFinset.mp hb)

 

theorem calibration_identity (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (P : V → V → ℝ) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) :
    w.weight P p * (law p).real w.calibrationEvent = w.probability P := by
  rw [w.calibration_probability hG hloc p]
  unfold weight
  have h₁ := pow_ne_zero w.path.length hp.ne'
  have h₂ := pow_ne_zero w.blockers.ncard (sub_pos.mpr hp₁).ne'
  field_simp

end RawCorridor
end ExactCorridorPattern
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorTerminalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem path_internal_two_neighbors {H : SimpleGraph V} {u v z : V}
    (q : H.Walk u v) (hq : q.IsPath) (hz : z ∈ q.support) (hzu : z ≠ u) (hzv : z ≠ v) :
    ∃ a b : V, a ≠ b ∧ s(z,a) ∈ q.edges ∧ s(z,b) ∈ q.edges := by
  induction q with
  | nil => simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz; exact (hzu hz).elim
  | @cons u a v h q ih =>
    have htail : q.IsPath := hq.of_cons
    have huz : u ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hq).2
    have hzq : z ∈ q.support := (List.mem_cons.mp hz).resolve_left hzu
    by_cases hza : z = a
    · subst z
      cases q with
      | nil => exact (hzv rfl).elim
      | @cons a b v h' q =>
        refine ⟨u,b,?_,?_,?_⟩
        · intro hub
          apply huz
          subst b
          simp
        · simp only [SimpleGraph.Walk.edges_cons,List.mem_cons,Sym2.eq_swap]; exact Or.inl trivial
        · simp only [SimpleGraph.Walk.edges_cons,List.mem_cons]; exact Or.inr (Or.inl trivial)
    · obtain ⟨b,c,hbc,hb,hc⟩ := ih htail hzq hza hzv
      exact ⟨b,c,hbc,List.mem_cons_of_mem _ hb,List.mem_cons_of_mem _ hc⟩

 

theorem pivotal_image_mem_edges (G : BondGraph V E) (ω : Set E) {x y : V}
    (q : (openSimpleGraph G ω).Walk x y) (e : E)
    (hp : ¬Conn G (ω \ {e}) x y) : G e ∈ q.edges := by
  obtain ⟨l,hl,hmap,ho⟩ := walk_lift_bonds G ω q
  by_contra he
  apply hp
  apply hl.conn
  intro f hf
  refine ⟨ho f hf,?_⟩
  intro hfe
  have hfe' : f = e := Set.mem_singleton_iff.mp hfe
  subst f
  apply he
  rw [←hmap]
  exact List.mem_map_of_mem hf

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem counted_terminal_outside (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : corridorCounted G w.retained w.blockers D ω x y) : x ∉ w.interior ∧ y ∉ w.interior := by
  have hleft (x y : V) (hc : corridorCounted G w.retained w.blockers D ω x y) : x ∉ w.interior := by
    intro hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxs : x ∈ w.path.support := List.mem_toFinset.mp hx'.1
    have hxne : x ≠ w.base ∧ x ≠ w.endpoint := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hx'.2
    have hxu := hxne.1
    have hxv := hxne.2
    obtain ⟨a,b,hab,ha,hb⟩ := path_internal_two_neighbors w.path w.path_isPath hxs hxu hxv
    obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.1
    let qp := q.bypass
    have hqp : qp.IsPath := q.bypass_isPath
    obtain ⟨e,he,hGe⟩ := w.edge_has_label _ ha
    obtain ⟨f,hf,hGf⟩ := w.edge_has_label _ hb
    have hea := pivotal_image_mem_edges G _ qp e (hc.2.1 e he).2
    have heb := pivotal_image_mem_edges G _ qp f (hc.2.1 f hf).2
    rw [hGe] at hea
    rw [hGf] at heb
    exact hab ((hqp.eq_snd_of_mem_edges hea).trans (hqp.eq_snd_of_mem_edges heb).symm)
  exact ⟨hleft x y hc,hleft y x ((corridorCounted_symm G _ _ D ω x y).mp hc)⟩

end RawCorridor
end CorridorTerminalGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section CorridorIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_inter_const (S : Set E) : Measurable (fun ω : Set E => ω ∩ S) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).and measurable_const

 
theorem restriction_events_independent (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (law p) ((fun ω => ω ∩ S) ⁻¹' A ∩ (fun ω => ω ∩ T) ⁻¹' B) =
      (law p) ((fun ω => ω ∩ S) ⁻¹' A) * (law p) ((fun ω => ω ∩ T) ⁻¹' B) := by
  let μ : Measure (E → Prop) := Measure.infinitePi (fun _ => bitLaw p)
  let σ : E → MeasurableSpace (E → Prop) := fun e =>
    MeasurableSpace.comap (fun f : E → Prop => f e) inferInstance
  have hi : iIndep σ μ := iIndepFun_infinitePi (X := fun (_ : E) (b : Prop) => b)
    (fun _ => measurable_id)
  have hle (e : E) : σ e ≤ (inferInstance : MeasurableSpace (E → Prop)) :=
    (measurable_pi_apply e).comap_le
  have hr (S : Set E) : @Measurable (E → Prop) (Set E) (⨆ e ∈ S, σ e) inferInstance
      (fun f => {e | f e} ∩ S) := by
    let : MeasurableSpace (E → Prop) := ⨆ e ∈ S, σ e
    apply measurable_setOfPred.comp
    apply Measurable.of_eval
    intro e
    change @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun f => f e ∧ e ∈ S)
    by_cases he : e ∈ S
    · have hm : @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun f => f e) :=
        Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
      simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,he,and_true] using hm
    · simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,he,and_false] using
        (measurable_const : @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun _ => False))
  have hm : (law p : Measure (Set E)) = μ.map (fun f => {e | f e}) := by
    simp only [law,setBernoulli_eq_map,Set.mem_univ,μ,bitLaw,bernoulliMeasure_def]
  rw [hm,Measure.map_apply measurable_setOfPred ((hA.preimage (measurable_inter_const S)).inter
    (hB.preimage (measurable_inter_const T))),
    Measure.map_apply measurable_setOfPred (hA.preimage (measurable_inter_const S)),
    Measure.map_apply measurable_setOfPred (hB.preimage (measurable_inter_const T))]
  exact (Indep_iff _ _ _).mp (indep_iSup_of_disjoint hle hi hST) _ _
    (hA.preimage (hr S)) (hB.preimage (hr T))

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem calibration_restriction (w : RawCorridor G k) (ω : Set E) :
    ω ∈ w.calibrationEvent ↔ ω ∩ (w.retained ∪ w.blockers) ∈ w.calibrationEvent := by
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨fun e he => ⟨ha he,Or.inl he⟩,hb.mono_right Set.inter_subset_left⟩
  · rintro ⟨ha,hb⟩
    refine ⟨fun e he => (ha he).1,Set.disjoint_left.mpr ?_⟩
    intro e he hw
    exact Set.disjoint_left.mp hb he ⟨hw,Or.inr he⟩

 

theorem calibration_independent (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) (p : unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (law p) (w.calibrationEvent ∩ (fun ω => ω ∩ internalEdges G (w.interior : Set V)ᶜ) ⁻¹' A) =
      (law p) w.calibrationEvent *
        (law p) ((fun ω => ω ∩ internalEdges G (w.interior : Set V)ᶜ) ⁻¹' A) := by
  have hQ : MeasurableSet w.calibrationEvent := by
    rw [w.calibrationEvent_eq hG hloc]
    apply measurableSet_edgePattern
    apply Finset.disjoint_left.mpr
    intro e he hb
    exact Set.disjoint_left.mp w.retained_disjoint_blockers
      ((w.retained_finite hG).mem_toFinset.mp he) ((w.blockers_finite hloc).mem_toFinset.mp hb)
  have heq : (fun ω => ω ∩ (w.retained ∪ w.blockers)) ⁻¹' w.calibrationEvent = w.calibrationEvent := by
    ext ω; exact (w.calibration_restriction ω).symm
  have hh := restriction_events_independent p _ _ (w.specified_disjoint_exterior hlen)
    w.calibrationEvent A hQ hA
  simpa only [heq] using hh

end RawCorridor
end CorridorIndependence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorContraction
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_union_attachment (G : BondGraph V E) (S T : Set E) (A : Set V)
    (hclosed : ∀ a b, a ∈ A → Conn G S a b → b ∈ A)
    (hT : ∀ e ∈ T, ∀ z ∈ G e, z ∈ A) {x y : V} (hc : Conn G (S ∪ T) x y) :
    Conn G S x y ∨ x ∈ A ∧ y ∈ A := by
  induction hc with
  | refl => exact Or.inl (conn_refl G S x)
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    rcases he with he | he
    · have hab : Conn G S a b := Relation.ReflTransGen.single ⟨e,he,heq⟩
      exact ih.elim (fun h => Or.inl (conn_trans G S h hab))
        (fun h => Or.inr ⟨h.1,hclosed a b h.2 hab⟩)
    · have ha := hT e he a (heq.symm ▸ (by simp : a ∈ s(a,b)))
      have hb := hT e he b (heq.symm ▸ (by simp : b ∈ s(a,b)))
      exact Or.inr ⟨ih.elim (fun h => hclosed a x ha (conn_symm G S h)) And.left,hb⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem support_exterior_ports (w : RawCorridor G k) {z : V}
    (hz : z ∈ w.path.support) (ho : z ∉ w.interior) : z = w.base ∨ z = w.endpoint := by
  simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,hz,true_and,
    Finset.mem_insert,Finset.mem_singleton,not_not] using ho

theorem attachment_closed (w : RawCorridor G k) (ω : Set E) (a b : V)
    (ha : a ∈ w.attachment ω) (hc : Conn G (w.exterior ω) a b) : b ∈ w.attachment ω := by
  rcases ha with ha | ha | ha
  · rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hc with rfl | ho
    · exact Or.inl ha
    · rcases w.support_exterior_ports ha ho.1 with rfl | rfl
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · exact Or.inr (Or.inl (conn_trans G _ ha hc))
  · exact Or.inr (Or.inr (conn_trans G _ ha hc))

theorem open_subset_exterior_retained (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) : ω ⊆ w.exterior ω ∪ w.retained := by
  intro e he
  by_cases hr : e ∈ w.retained
  · exact Or.inr hr
  · left
    refine ⟨he,?_⟩
    intro z hz hi
    exact Set.disjoint_left.mp hq.2 ⟨⟨z,hi,hz⟩,hr⟩ he

theorem connection_exterior_or_attachment (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) {x y : V} (hc : Conn G ω x y) :
    Conn G (w.exterior ω) x y ∨ x ∈ w.attachment ω ∧ y ∈ w.attachment ω := by
  apply conn_union_attachment G _ w.retained (w.attachment ω) (w.attachment_closed ω)
    (fun e he z hz => Or.inl (SimpleGraph.Walk.mem_support_of_mem_edges he hz))
  exact conn_mono G (w.open_subset_exterior_retained ω hq) hc

theorem attachment_outside (w : RawCorridor G k) (ω : Set E) {z : V}
    (ha : z ∈ w.attachment ω) (hz : z ∉ w.interior) :
    Conn G (w.exterior ω) w.base z ∨ Conn G (w.exterior ω) w.endpoint z := by
  rcases ha with ha | ha | ha
  · rcases w.support_exterior_ports ha hz with rfl | rfl
    · exact Or.inl (conn_refl G _ _)
    · exact Or.inr (conn_refl G _ _)
  · exact Or.inl ha
  · exact Or.inr ha

 
theorem counted_exterior_orientation (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (ω : Set E) (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hc : corridorCounted G w.retained w.blockers Set.univ ω x y) :
    ¬Conn G (w.exterior ω) w.base w.endpoint ∧
      ((Conn G (w.exterior ω) w.base x ∧ Conn G (w.exterior ω) w.endpoint y) ∨
       (Conn G (w.exterior ω) w.endpoint x ∧ Conn G (w.exterior ω) w.base y)) := by
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  have hc' : Conn G ω x y := by simpa only [hi,Set.inter_univ] using hc.1
  have hs : w.retained.Nonempty := by
    have hp : w.path.edges ≠ [] := by
      intro he
      have hh := congrArg List.length he
      simp only [SimpleGraph.Walk.length_edges,List.length_nil] at hh
      omega
    obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hp
    obtain ⟨e,he,_⟩ := w.edge_has_label s hs
    exact ⟨e,he⟩
  have hnot : ¬Conn G (w.exterior ω) x y := by
    intro h
    obtain ⟨e,he⟩ := hs
    apply (hc.2.1 e he).2
    apply conn_mono G ?_ h
    intro f hf
    refine ⟨?_,?_⟩
    · simpa only [hi,Set.inter_univ] using hf.1
    · intro hfe
      have hfe' := Set.mem_singleton_iff.mp hfe
      subst f
      exact Set.disjoint_left.mp (w.specified_disjoint_exterior hlen) (Or.inl he) hf.2
  have hatt := (w.connection_exterior_or_attachment ω hq hc').resolve_left hnot
  have hout := w.counted_terminal_outside Set.univ ω x y hc
  have hx := w.attachment_outside ω hatt.1 hout.1
  have hy := w.attachment_outside ω hatt.2 hout.2
  have hne : ¬Conn G (w.exterior ω) w.base w.endpoint := by
    intro h
    apply hnot
    have hx' : Conn G (w.exterior ω) w.base x := hx.elim id (conn_trans G _ h)
    have hy' : Conn G (w.exterior ω) w.base y := hy.elim id (conn_trans G _ h)
    exact conn_trans G _ (conn_symm G _ hx') hy'
  refine ⟨hne,?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hnot (conn_trans G _ (conn_symm G _ hx) hy)).elim
  · exact Or.inl ⟨hx,hy⟩
  · exact Or.inr ⟨hx,hy⟩
  · exact (hnot (conn_trans G _ (conn_symm G _ hx) hy)).elim

end RawCorridor
end CorridorContraction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CorridorBKCalibration
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem measurableSet_exteriorOrientations (w : RawCorridor G k) (x y : V) :
    MeasurableSet (w.exteriorOrientations x y) :=
  (measurableSet_orientedPivotalEvent G x y w.base w.endpoint).union
    (measurableSet_orientedPivotalEvent G x y w.endpoint w.base)

omit [Countable V] [Countable E] in
theorem counted_subset_calibration_exterior (w : RawCorridor G k)
    (hlen : 3 ≤ w.path.length) (x y : V) :
    {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} ⊆
      w.calibrationEvent ∩ (w.exterior ⁻¹' w.exteriorOrientations x y) := by
  intro ω hc
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  have hq : ω ∈ w.calibrationEvent := by
    refine ⟨fun e he => ?_,?_⟩
    · simpa only [hi,Set.inter_univ] using (hc.2.1 e he).1
    · simpa only [hi,Set.inter_univ] using hc.2.2
  refine ⟨hq,?_⟩
  obtain ⟨hne,ho⟩ := w.counted_exterior_orientation hlen ω hq x y hc
  rcases ho with ho | ho
  · exact Or.inl ⟨conn_symm G _ ho.1,ho.2,hne⟩
  · exact Or.inr ⟨conn_symm G _ ho.1,ho.2,fun h => hne (conn_symm G _ h)⟩

omit [Countable V] in
theorem exterior_orientation_BK (w : RawCorridor G k) (p : unitInterval) (x y a b : V) :
    (law p).real (w.exterior ⁻¹' orientedPivotalEvent G x y a b) ≤
      twoPoint G p x a * twoPoint G p b y := by
  apply le_trans (measureReal_mono ?_) (bk p {ω | Conn G ω x a} {ω | Conn G ω b y}
    (fun _ _ h hc => conn_mono G h hc) (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x a) (finiteWitness_conn G b y))
  intro ω h
  exact disjointOccurrence_upper _ _ Set.inter_subset_left
    (orientedPivotalEvent_subset_disjoint G x y a b h)

 

theorem counted_weight_bound (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (x y : V) :
    w.weight P p * (law p).real {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} ≤
      w.probability P * (twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y) := by
  have hi := w.calibration_independent hG hloc hlen p (w.exteriorOrientations x y)
    (w.measurableSet_exteriorOrientations x y)
  have hir : (law p).real (w.calibrationEvent ∩ w.exterior ⁻¹' w.exteriorOrientations x y) =
      (law p).real w.calibrationEvent * (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) := by
    exact congrArg ENNReal.toReal hi |>.trans ENNReal.toReal_mul
  have hb : (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) ≤
      twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y := by
    apply le_trans (measureReal_union_le _ _)
    exact add_le_add (w.exterior_orientation_BK p x y w.base w.endpoint)
      (w.exterior_orientation_BK p x y w.endpoint w.base)
  calc
    _ ≤ w.weight P p * (law p).real (w.calibrationEvent ∩ w.exterior ⁻¹' w.exteriorOrientations x y) :=
      mul_le_mul_of_nonneg_left (measureReal_mono (w.counted_subset_calibration_exterior hlen x y))
        (w.weight_nonneg P hP p)
    _ = w.probability P * (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) := by
      rw [hir,←mul_assoc,w.calibration_identity hG hloc P p hp hp₁]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (w.2.2.mass_nonneg P hP)

end RawCorridor
end CorridorBKCalibration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathIntegration
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawFrom
variable {H : SimpleGraph V}

theorem integral_zero (P : V → V → ℝ) (x : V) (f : V → ℝ) :
    integral (H := H) P 0 x f = f x := by
  unfold integral
  rw [←(zeroEquiv x).symm.tsum_eq]
  simp only [zeroEquiv,Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,one_mul,tsum_fintype,Fintype.sum_unique]

theorem integral_succ [∀ x, Finite (H.neighborSet x)] (P : V → V → ℝ)
    (k : ℕ) (x : V) (f : V → ℝ) :
    integral (H := H) P (k+1) x f =
      P x x * integral (H := H) P k x f +
        ∑' z : H.neighborSet x, P x z * integral (H := H) P k z f := by
  unfold integral
  rw [←(succEquiv k x).symm.tsum_eq]
  let := Fintype.ofFinite (RawFrom H k x)
  let := Fintype.ofFinite (H.neighborSet x)
  let (z : H.neighborSet x) := Fintype.ofFinite (RawFrom H k z)
  simp only [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,succEquiv,
    Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,mul_assoc,Finset.mul_sum]

end RawFrom

theorem finite_openSimpleGraph_neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Finite ((openSimpleGraph G Set.univ).neighborSet x) := by
  apply Set.Finite.to_subtype
  apply (finite_neighbors hloc x).subset
  intro y hy
  obtain ⟨_,e,_,he⟩ := hy
  exact ⟨e,he⟩

end RawPathIntegration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem sum_step_decomposition (H : SimpleGraph V) (P : V → V → ℝ)
    (hs : ∀ x, (Function.support (P x)).Finite)
    (hstep : ∀ x y, x ≠ y → ¬H.Adj x y → P x y = 0) (x : V) (f : V → ℝ) :
    (∑' y, P x y * f y) = P x x * f x + ∑' y : H.neighborSet x, P x y * f y := by
  rw [(finiteKernel_summable_mul P hs x f).tsum_eq_add_tsum_ite x]
  congr 1
  have he : (∑' y : H.neighborSet x, if (y:V) = x then (0:ℝ) else P x y * f y) =
      ∑' y, if y = x then (0:ℝ) else P x y * f y := by
    apply tsum_subtype_eq_of_support_subset (f := fun y : V => if y = x then (0:ℝ) else P x y * f y)
    intro y hy
    by_contra hn
    apply hy
    by_cases h : y = x
    · simp only [h,if_true]
    · simp only [ite_eq_right h,hstep x y (Ne.symm h) hn,zero_mul]
  rw [←he]
  apply tsum_congr
  intro y
  have hn : (y:V) ≠ x := by
    intro h
    have hy : H.Adj x y := y.property
    rw [h] at hy
    exact H.loopless.irrefl x hy
  rw [ite_eq_right hn]

 theorem raw_integral_operator (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x : V) (f : V → ℝ) :
    RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k x f =
      ∑' y, (matrixCoeff (P^k) x y).re * f y := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) :=
    finite_openSimpleGraph_neighbors G hloc z
  have hs (x : V) : (Function.support (walkKernel G hloc a x)).Finite := by
    simpa only [pow_one,hP,Complex.ofReal_re] using walkPower_finite_support G hloc a P hpos hP 1 x
  have hsP (x : V) : (Function.support (fun y => (matrixCoeff P x y).re)).Finite := by
    simpa only [hP,Complex.ofReal_re] using hs x
  induction k generalizing x with
  | zero => rw [RawFrom.integral_zero,pow_zero,positive_identity_action]
  | succ k ih =>
    rw [RawFrom.integral_succ,pow_succ',finite_positive_product_action P (P^k) hpos hsP
      (finite_positive_pow_support P hpos hsP k)]
    simp only [hP,Complex.ofReal_re]
    rw [sum_step_decomposition (openSimpleGraph G Set.univ) (walkKernel G hloc a) hs]
    · simp only [ih]
    · intro u v huv hn
      apply walkKernel_zero_of_not_step G hloc a u v huv
      intro ha
      apply hn
      obtain ⟨e,he⟩ := ha
      exact ⟨huv,e,Set.mem_univ e,he⟩

end RawPathOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSum
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}



theorem counted_iff (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted D ω x y ↔ 3 ≤ w.path.length ∧ corridorCounted G w.retained w.blockers D ω x y := by
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · rintro ⟨hlen,hc⟩
    exact ⟨hlen,w.support_subset_of_retained (by omega) D (fun e he => (hc.2.1 e he).1.2),hc⟩

theorem counted_base_mem_walk (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : w.counted D ω x y) (q : (openSimpleGraph G (ω ∩ internalEdges G D)).Walk x y) :
    w.base ∈ q.support := by
  have hl : 0 < w.path.length := by have := hc.1; omega
  obtain ⟨s,hs,hbs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hl)).mp w.path.start_mem_support
  obtain ⟨e,he,hGe⟩ := w.edge_has_label s hs
  have heq := pivotal_image_mem_edges G _ q e (hc.2.2.2.1 e he).2
  exact SimpleGraph.Walk.mem_support_of_mem_edges heq (hGe.symm ▸ hbs)

theorem counted_symm (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted D ω x y ↔ w.counted D ω y x := by
  rw [counted_iff,counted_iff,corridorCounted_symm]

theorem measurableSet_counted [Countable E] (w : RawCorridor G k) (D : Set V) (x y : V) :
    MeasurableSet {ω | w.counted D ω x y} := by
  simp_rw [w.counted_iff]
  by_cases h : 3 ≤ w.path.length
  · simpa only [h,true_and] using measurableSet_corridorCounted G w.retained w.blockers D x y
  · simp only [h,false_and,Set.ofPred_false]; exact MeasurableSet.empty

end RawCorridor

 theorem finite_corridors_on_bases (G : BondGraph V E) (hloc : LocallyFinite G) (k : ℕ)
    (S : Set V) (hS : S.Finite) : {w : RawCorridor G k | w.base ∈ S}.Finite := by
  let (x : V) : Finite ((openSimpleGraph G Set.univ).neighborSet x) :=
    finite_openSimpleGraph_neighbors G hloc x
  let : Finite S := hS.to_subtype
  let f : (Σ x : S, RawFrom (openSimpleGraph G Set.univ) k x.val) → RawCorridor G k :=
    fun w => ⟨w.1.val,w.2⟩
  have hr : {w : RawCorridor G k | w.base ∈ S} = Set.range f := by
    ext w
    constructor
    · intro hw
      exact ⟨⟨⟨w.base,hw⟩,w.2⟩,rfl⟩
    · rintro ⟨w,rfl⟩
      exact w.1.property
  rw [hr]
  exact Set.finite_range f

 

theorem finite_counted_corridors (G : BondGraph V E) (hloc : LocallyFinite G) (k : ℕ)
    (D : Set V) (ω : Set E) (x y : V) : {w : RawCorridor G k | w.counted D ω x y}.Finite := by
  by_cases hc : Conn G (ω ∩ internalEdges G D) x y
  · obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc
    apply (finite_corridors_on_bases G hloc k {z | z ∈ q.support} (List.finite_toSet _)).subset
    exact fun w hw => w.counted_base_mem_walk D ω x y hw q
  · have he : {w : RawCorridor G k | w.counted D ω x y} = ∅ := by
      ext w
      exact ⟨fun h => hc h.2.2.1,False.elim⟩
    rw [he]
    exact Set.finite_empty

end CorridorSum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualCorridorPenalty
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenaltyTerm_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) {k : ℕ} (D : Set V)
    (ω : Set E) (x y : V) (w : RawCorridor G k) :
    0 ≤ corridorPenaltyTerm G P p D ω x y w := by
  unfold corridorPenaltyTerm
  split_ifs
  · exact w.weight_nonneg P hP p
  · exact le_rfl

theorem corridorPenalty_finite_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    (Function.support (corridorPenaltyTerm G P p (k := k) D ω x y)).Finite := by
  apply (finite_counted_corridors G hloc k D ω x y).subset
  intro w hw
  by_contra hn
  exact hw (ite_eq_right hn)

theorem corridorPenalty_summable (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    Summable (corridorPenaltyTerm G P p (k := k) D ω x y) :=
  summable_of_hasFiniteSupport (corridorPenalty_finite_support G hloc P p k D ω x y)

theorem corridorPenalty_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (D : Set V)
    (ω : Set E) (x y : V) : 0 ≤ corridorPenalty G P p k D ω x y :=
  tsum_nonneg (corridorPenaltyTerm_nonneg G P hP p D ω x y)

theorem corridorPenalty_symm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenalty G P p k D ω x y = corridorPenalty G P p k D ω y x := by
  unfold corridorPenalty
  apply tsum_congr
  intro w
  simp only [corridorPenaltyTerm,w.counted_symm D ω x y]

theorem corridorPenalty_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω')
    (x y : V) (hc : Conn G (ω ∩ internalEdges G D) x y) :
    corridorPenalty G P p k D' ω' x y ≤ corridorPenalty G P p k D ω x y := by
  apply (corridorPenalty_summable G hloc P p k D' ω' x y).tsum_le_tsum ?_
    (corridorPenalty_summable G hloc P p k D ω x y)
  intro w
  by_cases hn : w.counted D' ω' x y
  · have ho : w.counted D ω x y := (w.counted_iff D ω x y).mpr
      ⟨hn.1,corridorCounted_restrict G _ _ hD hω x y hc hn.2.2⟩
    simp only [corridorPenaltyTerm,hn,ho,if_true,le_refl]
  · simpa only [corridorPenaltyTerm,hn,if_false] using corridorPenaltyTerm_nonneg G P hP p D ω x y w

theorem measurable_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    Measurable (fun ω => corridorPenaltyTerm G P p D ω x y w) := by
  exact Measurable.ite (w.measurableSet_counted D x y) measurable_const measurable_const

theorem measurable_corridorPenalty [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (x y : V) :
    Measurable (fun ω => corridorPenalty G P p k D ω x y) := by
  exact Measurable.tsum (fun w => measurable_corridorPenaltyTerm G P p D x y w)

end ActualCorridorPenalty
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq



theorem deformedConnection_nonneg (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    0 ≤ deformedConnection G P p k t D ω x y := by
  unfold deformedConnection
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem deformedConnection_le_one (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x y : V) : deformedConnection G P p k t D ω x y ≤ 1 := by
  unfold deformedConnection
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (corridorPenalty_nonneg G P hP p k D ω x y)
  · exact zero_le_one

theorem deformedConnection_symm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t D ω x y = deformedConnection G P p k t D ω y x := by
  have hc : Conn G (ω ∩ internalEdges G D) x y ↔ Conn G (ω ∩ internalEdges G D) y x :=
    ⟨conn_symm G _,conn_symm G _⟩
  simp only [deformedConnection,corridorPenalty_symm G P p k D ω x y,hc]
  congr 1
  apply propext; tauto

theorem deformedConnection_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω')
    (x y : V) : deformedConnection G P p k t D ω x y ≤ deformedConnection G P p k t D' ω' x y := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · have hc' : x ∈ D' ∧ y ∈ D' ∧ Conn G (ω' ∩ internalEdges G D') x y :=
      ⟨hD hc.1,hD hc.2.1,conn_mono G (Set.inter_subset_inter hω (internalEdges_mono G hD)) hc.2.2⟩
    simp only [deformedConnection,hc,hc']
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (corridorPenalty_restrict G hloc P hP p k hD hω x y hc.2.2)
      (neg_nonpos.mpr ht)
  · simpa only [deformedConnection,hc,if_false] using deformedConnection_nonneg G P p k t D' ω' x y

theorem measurable_deformedConnection [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ)
    (D : Set V) (x y : V) : Measurable (fun ω => deformedConnection G P p k t D ω x y) := by
  have hs : MeasurableSet {ω : Set E | x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y} := by
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
    · simpa only [hx,hy,true_and] using measurableSet_restrictedConn G (internalEdges G D) x y
    all_goals simp only [hx,hy,false_and,and_false,Set.ofPred_false]; exact MeasurableSet.empty
  exact Measurable.ite hs ((measurable_corridorPenalty G P p k D x y).const_mul (-t)).exp measurable_const

theorem integrable_deformedConnection [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (fun ω => deformedConnection G P p k t D ω x y) (law p) := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (measurable_deformedConnection G P p k t D x y).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (deformedConnection_nonneg G P p k t D ω x y)]
  exact deformedConnection_le_one G P hP p k t ht D ω x y

end ActualWeightedConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedConnectionEndpoints
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_zero (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k 0 D ω x y =
      if x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y then 1 else 0 := by
  simp only [deformedConnection,neg_zero,zero_mul,Real.exp_zero]

theorem deformedConnection_full_zero (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (ω : Set E) (x y : V) : deformedConnection G P p k 0 Set.univ ω x y =
      if Conn G ω x y then 1 else 0 := by
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  simp only [deformedConnection_zero,Set.mem_univ,true_and,hi,Set.inter_univ]

theorem deformedConnection_change (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x y : V) :
    0 ≤ deformedConnection G P p k 0 D ω x y - deformedConnection G P p k t D ω x y ∧
    deformedConnection G P p k 0 D ω x y - deformedConnection G P p k t D ω x y ≤
      t*corridorPenalty G P p k D ω x y := by
  have hN := corridorPenalty_nonneg G P hP p k D ω x y
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · simp only [deformedConnection,hc,if_true,neg_zero,zero_mul,Real.exp_zero,and_self]
    constructor
    · exact sub_nonneg.mpr ((Real.exp_le_one_iff).mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hN))
    · have h := Real.one_sub_le_exp_neg (t*corridorPenalty G P p k D ω x y)
      rw [←neg_mul] at h
      linarith
  · simp only [deformedConnection,hc,if_false,sub_self]
    exact ⟨le_rfl,mul_nonneg ht hN⟩

theorem deformedKernel_zero [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) (k : ℕ) (x y : V) :
    deformedKernel G P p k 0 Set.univ x y = twoPoint G p x y := by
  unfold deformedKernel
  simp_rw [deformedConnection_full_zero]
  have hi := integral_indicator_const (μ := law p) (1:ℝ) (measurableSet_conn G x y)
  simpa only [Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_one,Measure.real,twoPoint] using hi

end WeightedConnectionEndpoints
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkDiagrams
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_diagram_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (k : ℕ) (x y : V) :
    HasSum (fun w : RawCorridor G k => w.probability (walkKernel G hloc a) *
      ((matrixCoeff A x w.base).re * (matrixCoeff A w.endpoint y).re))
      (matrixCoeff (A*(P^k*A)) x y).re := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) :=
    finite_openSimpleGraph_neighbors G hloc z
  let F := fun w : RawCorridor G k => w.probability (walkKernel G hloc a) *
    ((matrixCoeff A x w.base).re * (matrixCoeff A w.endpoint y).re)
  have hFn (w : RawCorridor G k) : 0 ≤ F w :=
    mul_nonneg (w.2.2.mass_nonneg _ hK) (mul_nonneg (hA _ _).2 (hA _ _).2)
  have hr (z : V) : (∑' w : RawFrom (openSimpleGraph G Set.univ) k z, F ⟨z,w⟩) =
      (matrixCoeff A x z).re * (matrixCoeff (P^k*A) z y).re := by
    have h := raw_integral_operator G hloc a P hpos hP k z (fun u => (matrixCoeff A u y).re)
    have he : (∑' w : RawFrom (openSimpleGraph G Set.univ) k z, F ⟨z,w⟩) =
        (matrixCoeff A x z).re * RawFrom.integral (H := openSimpleGraph G Set.univ)
          (walkKernel G hloc a) k z (fun u => (matrixCoeff A u y).re) := by
      rw [RawFrom.integral,←tsum_mul_left]
      apply tsum_congr
      intro w
      dsimp only [F,RawCorridor.probability,RawCorridor.base,RawCorridor.endpoint]
      change w.2.mass _ * (_ * _) = _ * (w.2.mass _ * _)
      ring
    rw [he,h,((hpos.pow k).mul_hasSum A z y).tsum_eq]
  have ho := hA.mul_hasSum (P^k*A) x y
  have hs : Summable F := (summable_sigma_of_nonneg hFn).mpr ⟨fun z => by
    let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) k z)
    exact (hasSum_fintype _).summable,by simpa only [hr] using ho.summable⟩
  have he : (∑' w, F w) = (matrixCoeff (A*(P^k*A)) x y).re := by
    rw [hs.tsum_sigma]
    simpa only [hr] using ho.tsum_eq
  exact he ▸ hs.hasSum

 theorem sandwich_selfAdjoint (A P : Hilbert V →L[ℂ] Hilbert V)
    (hA : IsSelfAdjoint A) (hP : IsSelfAdjoint P) (k : ℕ) : IsSelfAdjoint (A*(P^k*A)) := by
  change star (A*(P^k*A)) = A*(P^k*A)
  simp only [star_mul,hA.star_eq,(hP.pow k).star_eq,mul_assoc]

end RawWalkDiagrams
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkSymmetricDiagrams
attribute [local instance] Classical.propDecidable Classical.decEq

theorem raw_two_diagrams_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (hAs : IsSelfAdjoint A)
    (k : ℕ) (x y : V) :
    HasSum (fun w : RawCorridor G k => w.probability (walkKernel G hloc a) *
      ((matrixCoeff A x w.base).re * (matrixCoeff A w.endpoint y).re +
       (matrixCoeff A x w.endpoint).re * (matrixCoeff A w.base y).re))
      (2*(matrixCoeff (A*(P^k*A)) x y).re) := by
  have h₁ := raw_diagram_hasSum G hloc a P hpos hP hK A hA k x y
  have h₂ := raw_diagram_hasSum G hloc a P hpos hP hK A hA k y x
  have hh := h₁.add h₂
  have hC := matrixCoeff_real_symm (A*(P^k*A)) (sandwich_selfAdjoint A P hAs hPs k) y x
  rw [hC,←two_mul] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  rw [matrixCoeff_real_symm A hAs y w.base,matrixCoeff_real_symm A hAs w.endpoint x]
  ring

end RawWalkSymmetricDiagrams
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PenaltyTermExpectation
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem integrable_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    Integrable (fun ω => corridorPenaltyTerm G P p D ω x y w) (law p) := by
  exact (integrable_const (w.weight P p)).indicator (w.measurableSet_counted D x y)

theorem integral_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    (∫ ω, corridorPenaltyTerm G P p D ω x y w ∂law p) =
      w.weight P p * (law p).real {ω | w.counted D ω x y} := by
  have h := integral_indicator_const (μ := law p) (w.weight P p) (w.measurableSet_counted D x y)
  simpa only [corridorPenaltyTerm,Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_comm] using h

 
theorem integral_corridorPenaltyTerm_le [Countable V] [Countable E]
    (G : BondGraph V E) (hG : Function.Injective G) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) {k : ℕ} (x y : V) (w : RawCorridor G k) :
    (∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w ∂law p) ≤
      w.probability P * (twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y) := by
  rw [integral_corridorPenaltyTerm]
  by_cases hl : 3 ≤ w.path.length
  · have he : {ω | w.counted Set.univ ω x y} =
        {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} := by
      ext ω
      simp only [Set.mem_ofPred_eq,w.counted_iff,hl,true_and]
    rw [he]
    exact w.counted_weight_bound hG hloc hl P hP p hp hp₁ x y
  · have he : {ω | w.counted Set.univ ω x y} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq,w.counted_iff,hl,false_and,Set.mem_empty_iff_false]
    rw [he,measureReal_empty,mul_zero]
    exact mul_nonneg (w.2.2.mass_nonneg P hP) (add_nonneg
      (mul_nonneg (twoPoint_nonneg G p x w.base) (twoPoint_nonneg G p w.endpoint y))
      (mul_nonneg (twoPoint_nonneg G p x w.endpoint) (twoPoint_nonneg G p w.base y)))

end PenaltyTermExpectation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullCorridorPenaltyExpectation
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

theorem corridorPenalty_integrable_bound (G : BondGraph V E)
    (hG : Function.Injective G) (hloc : LocallyFinite G) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (hAs : IsSelfAdjoint A)
    (hAT : ∀ x y, matrixCoeff A x y = (twoPoint G p x y : ℂ)) (k : ℕ) (x y : V) :
    Integrable (fun ω => corridorPenalty G (walkKernel G hloc a) p k Set.univ ω x y) (law p) ∧
    (∫ ω, corridorPenalty G (walkKernel G hloc a) p k Set.univ ω x y ∂law p) ≤
      2*(matrixCoeff (A*(P^k*A)) x y).re := by
  let K := walkKernel G hloc a
  have hK (u v : V) : 0 ≤ K u v := by simpa only [hP,Complex.ofReal_re] using (hpos u v).2
  let F := fun w : RawCorridor G k => fun ω : Set E => corridorPenaltyTerm G K p Set.univ ω x y w
  have hFi (w : RawCorridor G k) : Integrable (F w) (law p) := integrable_corridorPenaltyTerm G K p Set.univ x y w
  have hFn (w : RawCorridor G k) (ω : Set E) : 0 ≤ F w ω := corridorPenaltyTerm_nonneg G K hK p _ ω x y w
  have hd := raw_two_diagrams_hasSum G hloc a P hpos hPs hP hK A hA hAs k x y
  simp only [hAT,Complex.ofReal_re] at hd
  have hb (w : RawCorridor G k) := integral_corridorPenaltyTerm_le G hG hloc K hK p hp hp₁ x y w
  have hs : Summable (fun w => ∫ ω, F w ω ∂law p) := Summable.of_nonneg_of_le
    (fun w => integral_nonneg (hFn w)) hb hd.summable
  have hsN (ω : Set E) := corridorPenalty_summable G hloc K p k Set.univ ω x y
  have hlin : (∫⁻ ω, ENNReal.ofReal (corridorPenalty G K p k Set.univ ω x y) ∂law p) =
      ENNReal.ofReal (∑' w, ∫ ω, F w ω ∂law p) := by
    have he (ω : Set E) : ENNReal.ofReal (corridorPenalty G K p k Set.univ ω x y) =
        ∑' w, ENNReal.ofReal (F w ω) := ENNReal.ofReal_tsum_of_nonneg (fun w => hFn w ω) (hsN ω)
    simp_rw [he]
    rw [lintegral_tsum (fun w => (hFi w).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [←ofReal_integral_eq_lintegral_ofReal (hFi _) (Filter.Eventually.of_forall (hFn _))]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun w => integral_nonneg (hFn w)) hs).symm
  have hNn (ω : Set E) := corridorPenalty_nonneg G K hK p k Set.univ ω x y
  have hi : Integrable (fun ω => corridorPenalty G K p k Set.univ ω x y) (law p) :=
    ⟨(measurable_corridorPenalty G K p k Set.univ x y).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hNn)).mpr (by rw [hlin]; exact ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  have hn : Summable (fun w => ∫ ω, ‖F w ω‖ ∂law p) := by
    simpa only [Real.norm_of_nonneg (hFn _ _)] using hs
  change (∫ ω, ∑' w, F w ω ∂law p) ≤ _
  rw [←integral_tsum_of_summable_integral_norm hFi hn]
  exact (hs.tsum_le_tsum hb hd.summable).trans_eq hd.tsum_eq

end FullCorridorPenaltyExpectation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SmallDeformationEntrywise
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem deformedKernel_change_bound (G : BondGraph V E)
    (hG : Function.Injective G) (hloc : LocallyFinite G) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (hAs : IsSelfAdjoint A)
    (hAT : ∀ x y, matrixCoeff A x y = (twoPoint G p x y : ℂ))
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x y : V) :
    0 ≤ twoPoint G p x y - deformedKernel G (walkKernel G hloc a) p k t Set.univ x y ∧
    twoPoint G p x y - deformedKernel G (walkKernel G hloc a) p k t Set.univ x y ≤
      2*t*(matrixCoeff (A*(P^k*A)) x y).re := by
  let K := walkKernel G hloc a
  have hK (u v : V) : 0 ≤ K u v := by simpa only [hP,Complex.ofReal_re] using (hpos u v).2
  have hi₀ := integrable_deformedConnection G K hK p k 0 (le_refl _) Set.univ x y
  have hi := integrable_deformedConnection G K hK p k t ht Set.univ x y
  have he : twoPoint G p x y - deformedKernel G K p k t Set.univ x y =
      ∫ ω, deformedConnection G K p k 0 Set.univ ω x y - deformedConnection G K p k t Set.univ ω x y ∂law p := by
    rw [integral_sub hi₀ hi]
    change _ = deformedKernel G K p k 0 Set.univ x y - _
    rw [deformedKernel_zero]
    rfl
  rw [he]
  refine ⟨integral_nonneg (fun ω => (deformedConnection_change G K hK p k t ht Set.univ ω x y).1),?_⟩
  obtain ⟨hNi,hNb⟩ := corridorPenalty_integrable_bound G hG hloc p hp hp₁ a P hpos hPs hP A hA hAs hAT k x y
  calc
    _ ≤ ∫ ω, t*corridorPenalty G K p k Set.univ ω x y ∂law p :=
      integral_mono (hi₀.sub hi) (hNi.const_mul t)
        (fun ω => (deformedConnection_change G K hK p k t ht Set.univ ω x y).2)
    _ = t*∫ ω, corridorPenalty G K p k Set.univ ω x y ∂law p := integral_const_mul _ _
    _ ≤ t*(2*(matrixCoeff (A*(P^k*A)) x y).re) := mul_le_mul_of_nonneg_left hNb ht
    _ = _ := by ring

omit [Countable V] [Countable E] in
theorem deformedKernel_nonneg (G : BondGraph V E) (P : V → V → ℝ) (p : unitInterval)
    (k : ℕ) (t : ℝ) (D : Set V) (x y : V) : 0 ≤ deformedKernel G P p k t D x y :=
  integral_nonneg (fun ω => deformedConnection_nonneg G P p k t D ω x y)

end SmallDeformationEntrywise
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_ClusterProducts
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster Products for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallDeformationOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem exists_deformedOperator_small_change (G : BondGraph V E)
    (hG : Function.Injective G) (hloc : LocallyFinite G) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (hAs : IsSelfAdjoint A)
    (hAT : ∀ x y, matrixCoeff A x y = (twoPoint G p x y : ℂ))
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V,
      (∀ x y, matrixCoeff B x y = (deformedKernel G (walkKernel G hloc a) p k t Set.univ x y : ℂ)) ∧
      ‖B‖ ≤ ‖A‖ ∧ ‖A-B‖ ≤ 2*t*‖P‖^k*‖A‖^2 ∧ ‖A‖-2*t*‖P‖^k*‖A‖^2 ≤ ‖B‖ := by
  let K := deformedKernel G (walkKernel G hloc a) p k t Set.univ
  have hKn (x y : V) : 0 ≤ K x y := deformedKernel_nonneg G _ p k t _ x y
  have hb (x y : V) := deformedKernel_change_bound G hG hloc p hp hp₁ a P hpos hPs hP A hA hAs hAT k t ht x y
  obtain ⟨B,hBn,hBK⟩ := exists_operator_of_matrix_domination (twoPoint G p) K (twoPoint_nonneg G p)
    (fun x y => by rw [abs_of_nonneg (hKn x y)]; exact sub_nonneg.mp (hb x y).1) A hAT
  have hBK' (x y : V) : matrixCoeff B x y = (K x y : ℂ) := hBK x y
  let C := A*(P^k*A)
  have hCn : PositiveRealMatrix C := hA.mul ((hpos.pow k).mul hA)
  have hscale (x y : V) : matrixCoeff (((2*t:ℝ):ℂ) • C) x y =
      (2*t*(matrixCoeff C x y).re : ℝ) := by
    change ((2*t:ℝ):ℂ)*matrixCoeff C x y = _
    rw [hCn.real]
    simp only [Complex.ofReal_re,Complex.ofReal_mul]
  obtain ⟨D,hDn,hDK⟩ := exists_operator_of_matrix_domination
    (fun x y => 2*t*(matrixCoeff C x y).re) (fun x y => twoPoint G p x y - K x y)
    (fun x y => mul_nonneg (mul_nonneg (by norm_num) ht) (hCn x y).2)
    (fun x y => by rw [abs_of_nonneg (hb x y).1]; exact (hb x y).2)
    (((2*t:ℝ):ℂ) • C) hscale
  have he : D = A-B := kernel_extension_unique hDK (by
    intro x y
    change matrixCoeff A x y - matrixCoeff B x y = _
    rw [hAT,hBK',Complex.ofReal_sub])
  rw [he] at hDn
  have hCnorm : ‖C‖ ≤ ‖A‖*‖P‖^k*‖A‖ := by
    calc
      _ ≤ ‖A‖*‖P^k*A‖ := norm_mul_le _ _
      _ ≤ ‖A‖*(‖P^k‖*‖A‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖A‖*(‖P‖^k*‖A‖) := by
        gcongr
        cases k with
        | zero =>
          simp only [pow_zero]
          have he : (1 : Hilbert V →L[ℂ] Hilbert V) = ContinuousLinearMap.id ℂ (Hilbert V) := by ext f; rfl
          rw [he]
          exact ContinuousLinearMap.norm_id_le
        | succ j => exact norm_pow_le' P (Nat.succ_pos j)
      _ = _ := by ring
  have hd : ‖A-B‖ ≤ 2*t*‖P‖^k*‖A‖^2 := by
    calc
      _ ≤ ‖((2*t:ℝ):ℂ) • C‖ := hDn
      _ = 2*t*‖C‖ := by rw [norm_smul,Complex.norm_of_nonneg (mul_nonneg (by norm_num) ht)]
      _ ≤ 2*t*(‖A‖*‖P‖^k*‖A‖) := mul_le_mul_of_nonneg_left hCnorm (mul_nonneg (by norm_num) ht)
      _ = _ := by ring
  refine ⟨B,hBK,hBn,hd,?_⟩
  have hh : ‖A‖ ≤ ‖A-B‖+‖B‖ := by simpa only [sub_add_cancel] using norm_add_le (A-B) B
  linarith

end SmallDeformationOperators
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


theorem SimpleVisit.mono (G : BondGraph V E) {S T : Set E} {A B : Set V}
    (hST : S ⊆ T) (hAB : A ⊆ B) {x y : V} (h : SimpleVisit G S A x y) :
    SimpleVisit G T B x y := by
  obtain ⟨q,hq,z,hz,ha⟩ := h
  have hg : openSimpleGraph G S ≤ openSimpleGraph G T := by
    rintro a b ⟨hne,e,he,hGe⟩
    exact ⟨hne,e,hST he,hGe⟩
  exact ⟨q.mapLe hg,hq.mapLe hg,z,by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hz,hAB ha⟩

theorem walk_conn_restrict_vertices (G : BondGraph V E) (S : Set E) {x y : V}
    (q : (openSimpleGraph G S).Walk x y) (D : Set V)
    (hD : ∀ z ∈ q.support, z ∈ D) : Conn G (S ∩ internalEdges G D) x y := by
  obtain ⟨l,hl,hm,ho⟩ := walk_lift_bonds G S q
  apply hl.conn
  intro e he
  refine ⟨ho e he,?_⟩
  intro z hz
  exact hD z (SimpleGraph.Walk.mem_support_of_mem_edges (hm ▸ List.mem_map_of_mem he) hz)

theorem conn_restrict_of_no_simpleVisit (G : BondGraph V E) (S : Set E)
    (A : Set V) (x y : V) (hc : Conn G S x y) (hn : ¬SimpleVisit G S A x y) :
    Conn G (S ∩ internalEdges G Aᶜ) x y := by
  obtain ⟨q⟩ := (conn_iff_reachable G S x y).mp hc
  exact walk_conn_restrict_vertices G S q.bypass Aᶜ
    (fun z hz ha => hn ⟨q.bypass,q.bypass_isPath,z,hz,ha⟩)

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem counted_support_subset_walk (w : RawCorridor G k) (D : Set V) (ω : Set E)
    (x y : V) (hc : w.counted D ω x y)
    (q : (openSimpleGraph G (ω ∩ internalEdges G D)).Walk x y) :
    ∀ z ∈ w.path.support, z ∈ q.support := by
  intro z hz
  have hl : 0 < w.path.length := by have := hc.1; omega
  obtain ⟨s,hs,hzs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hl)).mp hz
  obtain ⟨e,he,hGe⟩ := w.edge_has_label s hs
  exact SimpleGraph.Walk.mem_support_of_mem_edges
    (pivotal_image_mem_edges G _ q e (hc.2.2.2.1 e he).2) (hGe.symm ▸ hzs)

end RawCorridor

 

theorem simplePath_disjoint_at (G : BondGraph V E) (S : Set E) {x y z : V}
    (q : (openSimpleGraph G S).Walk x y) (hq : q.IsPath) (hz : z ∈ q.support) :
    S ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} := by
  obtain ⟨a,ha,hea,hoa⟩ := walk_lift_bonds G S (q.takeUntil z hz)
  obtain ⟨b,hb,heb,hob⟩ := walk_lift_bonds G S (q.dropUntil z hz)
  refine ⟨a.toFinset,b.toFinset,?_,?_,?_,?_,?_⟩
  · intro e he; exact hoa e (List.mem_toFinset.mp he)
  · intro e he; exact hob e (List.mem_toFinset.mp he)
  · apply Finset.disjoint_left.mpr
    intro e hae hbe
    exact List.disjoint_left.mp (hq.isTrail.disjoint_edges_takeUntil_dropUntil hz)
      (hea ▸ List.mem_map_of_mem (List.mem_toFinset.mp hae))
      (heb ▸ List.mem_map_of_mem (List.mem_toFinset.mp hbe))
  · exact ha.conn (fun e he => List.mem_toFinset.mpr he)
  · exact hb.conn (fun e he => List.mem_toFinset.mpr he)

end DeletionGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionCounted
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_delete_of_no_visit (G : BondGraph V E) (ω : Set E) (D A : Set V)
    (x y : V) (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y)
    (S : Set E) (hS : S ⊆ ω ∩ internalEdges G D) (hc : Conn G S x y) :
    Conn G (S ∩ internalEdges G (D \ A)) x y := by
  have hno : ¬SimpleVisit G S A x y := fun h => hn (h.mono G hS (fun _ => Or.inl))
  have h := conn_restrict_of_no_simpleVisit G S A x y hc hno
  apply conn_mono G ?_ h
  rintro e ⟨he,ha⟩
  exact ⟨he,fun z hz => ⟨(hS he).2 z hz,ha z hz⟩⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_before_deletion_of_no_visit (w : RawCorridor G k)
    (D A : Set V) (ω : Set E) (x y : V)
    (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y)
    (hc : w.counted (D \ A) ω x y) : w.counted D ω x y := by
  have hs : ω ∩ internalEdges G (D \ A) ⊆ ω ∩ internalEdges G D :=
    Set.inter_subset_inter_right _ (internalEdges_mono G Set.sdiff_subset)
  apply (w.counted_iff D ω x y).mpr
  refine ⟨hc.1,conn_mono G hs hc.2.2.1,?_,?_⟩
  · intro e he
    refine ⟨hs (hc.2.2.2.1 e he).1,?_⟩
    intro hbad
    have hd := conn_delete_of_no_visit G ω D A x y hn
      ((ω ∩ internalEdges G D) \ {e}) Set.sdiff_subset hbad
    apply (hc.2.2.2.1 e he).2
    apply conn_mono G ?_ hd
    rintro f ⟨⟨⟨hfω,hfD⟩,hfne⟩,hfnew⟩
    exact ⟨⟨hfω,hfnew⟩,hfne⟩
  · apply Set.disjoint_left.mpr
    intro e he ho
    have henew : e ∉ internalEdges G (D \ A) := fun he' =>
      Set.disjoint_left.mp hc.2.2.2.2 he ⟨ho.1,he'⟩
    obtain ⟨a,ha,hna⟩ : ∃ a ∈ G e, a ∉ D \ A := by
      change ¬(∀ a ∈ G e, a ∈ D \ A) at henew
      push Not at henew
      exact henew
    have haA : a ∈ A := by
      by_contra ha'
      exact hna ⟨ho.2 a ha,ha'⟩
    obtain ⟨z,hzi,hze⟩ := he.1
    obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2.1
    have hz : z ∈ q.bypass.support := w.counted_support_subset_walk (D \ A) ω x y hc q.bypass z
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hzi).1)
    have hv : SimpleVisit G (ω ∩ internalEdges G (D \ A)) (closedBondNeighborhood G A) x y :=
      ⟨q.bypass,q.bypass_isPath,z,hz,Or.inr ⟨e,hze,a,ha,haA⟩⟩
    exact hn (hv.mono G hs (Set.Subset.refl _))

end RawCorridor
end DeletionCounted
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionWeightedLoss
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem deformedConnection_no_visit (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (ω : Set E) (x y : V)
    (hn : ¬SimpleVisit G (ω ∩ internalEdges G D) (closedBondNeighborhood G A) x y) :
    deformedConnection G P p k t D ω x y ≤ deformedConnection G P p k t (D \ A) ω x y := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2
    have hx : x ∉ A := fun ha => hn ⟨q.bypass,q.bypass_isPath,x,q.bypass.start_mem_support,Or.inl ha⟩
    have hy : y ∉ A := fun ha => hn ⟨q.bypass,q.bypass_isPath,y,q.bypass.end_mem_support,Or.inl ha⟩
    have hc' : x ∈ D \ A ∧ y ∈ D \ A ∧ Conn G (ω ∩ internalEdges G (D \ A)) x y := by
      refine ⟨⟨hc.1,hx⟩,⟨hc.2.1,hy⟩,?_⟩
      apply conn_mono G ?_ (conn_delete_of_no_visit G ω D A x y hn _ (Set.Subset.refl _) hc.2.2)
      rintro e ⟨⟨heω,heD⟩,henew⟩
      exact ⟨heω,henew⟩
    simp only [deformedConnection,hc,hc']
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left ?_ (neg_nonpos.mpr ht)
    apply (corridorPenalty_summable G hloc P p k (D \ A) ω x y).tsum_le_tsum ?_
      (corridorPenalty_summable G hloc P p k D ω x y)
    intro w
    by_cases hw : w.counted (D \ A) ω x y
    · have hw' := w.counted_before_deletion_of_no_visit D A ω x y hn hw
      simp only [corridorPenaltyTerm,hw,hw',if_true,le_refl]
    · simpa only [corridorPenaltyTerm,hw,if_false] using corridorPenaltyTerm_nonneg G P hP p D ω x y w
  · simpa only [deformedConnection,hc,if_false] using deformedConnection_nonneg G P p k t (D \ A) ω x y

 

theorem deformedConnection_deletion_pointwise (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ≤
      if ∃ z ∈ closedBondNeighborhood G A,
        ω ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} then 1 else 0 := by
  split_ifs with h
  · linarith [deformedConnection_le_one G P hP p k t ht D ω x y,
      deformedConnection_nonneg G P p k t (D \ A) ω x y]
  · apply sub_nonpos.mpr
    apply deformedConnection_no_visit G hloc P hP p k t ht D A ω x y
    rintro ⟨q,hq,z,hz,hza⟩
    apply h
    exact ⟨z,hza,disjointOccurrence_upper _ _ Set.inter_subset_left (simplePath_disjoint_at G _ q hq hz)⟩

end DeletionWeightedLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeletionKernelBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem deformedKernel_deletion_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D A : Set V) (x y : V)
    (hs : Summable (fun z : closedBondNeighborhood G A => twoPoint G p x z * twoPoint G p z y)) :
    deformedKernel G P p k t D x y - deformedKernel G P p k t (D \ A) x y ≤
      ∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y := by
  let B := fun z : closedBondNeighborhood G A =>
    DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y}
  let U := ⋃ z, B z
  have hBm (z : closedBondNeighborhood G A) : MeasurableSet (B z) :=
    measurableSet_finiteWitness _ (disjointOccurrence_upper _ _) (finiteWitness_disjointOccurrence _ _)
  have hUm : MeasurableSet U := MeasurableSet.iUnion hBm
  have hBn (z : closedBondNeighborhood G A) : 0 ≤ twoPoint G p x z * twoPoint G p z y :=
    mul_nonneg (twoPoint_nonneg G p x z) (twoPoint_nonneg G p z y)
  have hBK (z : closedBondNeighborhood G A) : law p (B z) ≤ ENNReal.ofReal (twoPoint G p x z * twoPoint G p z y) := by
    rw [←ENNReal.ofReal_toReal (measure_ne_top (law p) (B z))]
    exact ENNReal.ofReal_le_ofReal (bk p _ _ (fun _ _ h hc => conn_mono G h hc)
      (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x z) (finiteWitness_conn G z y))
  have hU : (law p).real U ≤ ∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y := by
    have hh : law p U ≤ ENNReal.ofReal (∑' z : closedBondNeighborhood G A, twoPoint G p x z * twoPoint G p z y) := by
      calc
        _ ≤ ∑' z, law p (B z) := measure_iUnion_le B
        _ ≤ ∑' z : closedBondNeighborhood G A, ENNReal.ofReal (twoPoint G p x z * twoPoint G p z y) := ENNReal.tsum_le_tsum hBK
        _ = _ := (ENNReal.ofReal_tsum_of_nonneg hBn hs).symm
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (tsum_nonneg hBn))
  have hUi : Integrable (U.indicator (fun _ : Set E => (1:ℝ))) (law p) := (integrable_const _).indicator hUm
  have hpoint (ω : Set E) : deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ≤
      U.indicator (fun _ : Set E => (1:ℝ)) ω := by
    have he : ω ∈ U ↔ ∃ z ∈ closedBondNeighborhood G A, ω ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} := by
      simp [U,B]
    simpa only [Set.indicator_apply,he] using deformedConnection_deletion_pointwise G hloc P hP p k t ht D A ω x y
  have hi := integrable_deformedConnection G P hP p k t ht D x y
  have hi' := integrable_deformedConnection G P hP p k t ht (D \ A) x y
  calc
    _ = ∫ ω, deformedConnection G P p k t D ω x y - deformedConnection G P p k t (D \ A) ω x y ∂law p := (integral_sub hi hi').symm
    _ ≤ ∫ ω, U.indicator (fun _ : Set E => (1:ℝ)) ω ∂law p := integral_mono (hi.sub hi') hUi hpoint
    _ = (law p).real U := integral_indicator_one hUm
    _ ≤ _ := hU

end DeletionKernelBound
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedKernel_le_twoPoint [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    deformedKernel G P p k t D x y ≤ twoPoint G p x y := by
  rw [←deformedKernel_zero G P p k x y]
  apply integral_mono (integrable_deformedConnection G P hP p k t ht D x y)
    (integrable_deformedConnection G P hP p k 0 (le_refl _) Set.univ x y)
  intro ω
  exact (deformedConnection_mono G hloc P hP p k t ht (Set.subset_univ D)
    (Set.Subset.refl _) x y).trans (sub_nonneg.mp (deformedConnection_change G P hP p k t ht Set.univ ω x y).1)

theorem summable_deformedKernel [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    Summable (deformedKernel G P p k t D x) :=
  Summable.of_nonneg_of_le (deformedKernel_nonneg G P p k t D x)
    (deformedKernel_le_twoPoint G hloc P hP p k t ht D x)
    (summable_twoPoint_subcritical G hloc hqt p hp x)

end DeformedSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionSusceptibilityEstimate
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem summable_twoPoint_restricted_pair (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x : V) (N : Set V) :
    Summable (fun zy : N×V => twoPoint G p x zy.1 * twoPoint G p zy.1 zy.2) := by
  apply (summable_twoPoint_pair G hloc hqt p hp x).comp_injective (i := fun zy : N×V => (zy.1.val,zy.2))
  intro a b hab
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hab)) (congrArg (fun z : V×V => z.2) hab)



theorem deformedSusceptibility_deletion (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D A : Set V) (x : V) :
    deformedSusceptibility G P p k t D x -
      maxSusceptibility G p * (∑' z : closedBondNeighborhood G A, twoPoint G p x z) ≤
      deformedSusceptibility G P p k t (D \ A) x := by
  let N := closedBondNeighborhood G A
  have hpairs := summable_twoPoint_restricted_pair G hloc hqt p hp x N
  have hdiag (y : V) := hpairs.prod_symm.prod_factor y
  have hi := summable_deformedKernel G hloc hqt P hP p hp k t ht D x
  have hi' := summable_deformedKernel G hloc hqt P hP p hp k t ht (D \ A) x
  have hb := (hi.sub hi').tsum_le_tsum
    (fun y => deformedKernel_deletion_bound G hloc P hP p k t ht D A x y (hdiag y)) hpairs.prod_symm.prod
  rw [hi.tsum_sub hi'] at hb
  change deformedSusceptibility G P p k t D x - deformedSusceptibility G P p k t (D \ A) x ≤ _ at hb
  have herr := twoPoint_double_restricted_bound_bs G hloc hqt p hp x N
  linarith

end DeletionSusceptibilityEstimate
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_deformedClusterMass [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    Measurable (fun ω => deformedClusterMass G P p k t D ω x) :=
  Measurable.tsum (fun y => measurable_deformedConnection G P p k t D x y)

end ExteriorWeightedConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedMassIntegrals
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedClusterMass_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) :
    0 ≤ deformedClusterMass G P p k t D ω x :=
  tsum_nonneg (deformedConnection_nonneg G P p k t D ω x)

theorem deformedClusterMass_le_ncard (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    deformedClusterMass G P p k t D ω x ≤ ((cluster G ω x).ncard:ℝ) := by
  unfold deformedClusterMass
  rw [tsum_eq_sum (s := hf.toFinset) (fun y hy => by
    have hn : ¬Conn G ω x y := fun hc => hy (hf.mem_toFinset.mpr hc)
    have hn' : ¬Conn G (ω ∩ internalEdges G D) x y := fun hc => hn (conn_mono G Set.inter_subset_left hc)
    simp only [deformedConnection,hn',and_false,if_false])]
  calc
    _ ≤ ∑ _y ∈ hf.toFinset, (1:ℝ) := Finset.sum_le_sum (fun y _ => deformedConnection_le_one G P hP p k t ht D ω x y)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hf]

theorem integrable_deformedClusterMass [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    Integrable (fun ω => deformedClusterMass G P p k t D ω x) (law p) := by
  apply Integrable.mono' (susceptibility_eq_integral G hloc hqt p hp x).1
    (measurable_deformedClusterMass G P p k t D x).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
  rw [Real.norm_of_nonneg (deformedClusterMass_nonneg G P p k t D ω x)]
  exact deformedClusterMass_le_ncard G P hP p k t ht D ω x hω

 

theorem deformedSusceptibility_eq_integral [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x : V) :
    deformedSusceptibility G P p k t D x = ∫ ω, deformedClusterMass G P p k t D ω x ∂law p := by
  have hi := integrable_deformedConnection G P hP p k t ht D x
  have hs : Summable (fun y => ∫ ω, ‖deformedConnection G P p k t D ω x y‖ ∂law p) := by
    simp only [Real.norm_of_nonneg (deformedConnection_nonneg G P p k t D _ x _)]
    exact summable_deformedKernel G hloc hqt P hP p hp k t ht D x
  exact integral_tsum_of_summable_integral_norm hi hs

end DeformedMassIntegrals
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section DisjointCoordinateObservables
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem restriction_functions_independent (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (f g : Set E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ ω, f ω = f (ω ∩ S)) (hgT : ∀ ω, g ω = g (ω ∩ T)) :
    IndepFun f g (law p) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  have he (h : Set E → ℝ) (U : Set E) (hU : ∀ ω, h ω = h (ω ∩ U)) (C : Set ℝ) :
      (fun ω => ω ∩ U) ⁻¹' (h ⁻¹' C) = h ⁻¹' C := by
    ext ω
    simp only [Set.mem_preimage,←hU ω]
  simpa only [he f S hfS A,he g T hgT B] using
    restriction_events_independent p S T hST (f ⁻¹' A) (g ⁻¹' B)
      (hA.preimage hf) (hB.preimage hg)

theorem integral_mul_disjoint_coordinates (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (f g : Set E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ ω, f ω = f (ω ∩ S)) (hgT : ∀ ω, g ω = g (ω ∩ T)) :
    (∫ ω, f ω*g ω ∂law p) = (∫ ω, f ω ∂law p)*(∫ ω, g ω ∂law p) :=
  (restriction_functions_independent p S T hST f g hf hg hfS hgT).integral_mul_eq_mul_integral
    hf.aestronglyMeasurable hg.aestronglyMeasurable

end DisjointCoordinateObservables
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshWeightedMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedSusceptibility_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    0 ≤ deformedSusceptibility G P p k t D x :=
  tsum_nonneg (deformedKernel_nonneg G P p k t D x)

end FreshWeightedMass
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteNeighborhoodMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem closedBondNeighborhood_finset (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V) :
    closedBondNeighborhood G (W:Set V) = (W ∪ W.biUnion (neighbors G hloc) : Finset V) := by
  ext z
  simp only [closedBondNeighborhood,Set.mem_ofPred_eq,Finset.mem_coe,Finset.mem_union,Finset.mem_biUnion]
  constructor
  · rintro (hz | ⟨e,hz,a,ha,haW⟩)
    · exact Or.inl hz
    · by_cases hza : a = z
      · exact Or.inl (hza ▸ haW)
      · exact Or.inr ⟨a,haW,(mem_neighbors G hloc a z).mpr
          ⟨e,(Sym2.mem_and_mem_iff hza).mp ⟨ha,hz⟩⟩⟩
  · rintro (hz | ⟨a,ha,haz⟩)
    · exact Or.inl hz
    · obtain ⟨e,he⟩ := (mem_neighbors G hloc a z).mp haz
      exact Or.inr ⟨e,he.symm ▸ Sym2.mem_mk_right a z,a,he.symm ▸ Sym2.mem_mk_left a z,ha⟩

end FiniteNeighborhoodMass
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Derivatives
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSizeBounds
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incidentSupport_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (W : Finset V) :
    (incidentSupport G hloc W).card ≤ W.card*d := by
  apply Finset.card_biUnion_le_card_mul
  intro x _
  rw [←Set.ncard_eq_toFinset_card _ (hloc x)]
  exact (incident_ncard_le_degree G hloc x).trans (hd x)

theorem reachBall_ncard_le_pow (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (x : V) (k : ℕ) :
    (reachBall G x k).ncard ≤ (d+1)^k := by
  induction k with
  | zero => simp only [reachBall,Set.ncard_singleton,pow_zero,le_refl]
  | succ k ih =>
    let W := (finite_reachBall hloc x k).toFinset
    have he : reachBall G x (k+1) = (W ∪ W.biUnion (neighbors G hloc) : Finset V) := by
      ext z
      simp only [reachBall,Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,Finset.mem_coe,
        Finset.mem_union,Finset.mem_biUnion,mem_neighbors,Set.Finite.mem_toFinset,W,Adj,exists_prop]
    rw [he,Set.ncard_coe_finset]
    have hb : (W.biUnion (neighbors G hloc)).card ≤ W.card*d :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun a _ => (neighbors_card_le_degree G hloc a).trans (hd a))
    have hi : W.card ≤ (d+1)^k := by simpa only [W,←Set.ncard_eq_toFinset_card] using ih
    calc
      _ ≤ W.card + (W.biUnion (neighbors G hloc)).card := Finset.card_union_le _ _
      _ ≤ W.card + W.card*d := Nat.add_le_add_left hb _
      _ = W.card*(d+1) := by ring
      _ ≤ (d+1)^k*(d+1) := Nat.mul_le_mul_right _ hi
      _ = _ := (pow_succ _ _).symm

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem interior_card_le (w : RawCorridor G k) : w.interior.card ≤ w.path.length := by
  have hs : w.interior ⊂ w.path.support.toFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset,?_⟩
    intro he
    have hb : w.base ∈ w.path.support.toFinset := List.mem_toFinset.mpr w.path.start_mem_support
    rw [←he] at hb
    have hn : w.base ∉ w.interior := by simp only [interior,Finset.mem_sdiff,Finset.mem_insert,
      true_or,not_true_eq_false,and_false,not_false_eq_true]
    exact hn hb
  have hh := Finset.card_lt_card hs
  rw [List.toFinset_card_of_nodup w.path_isPath.support_nodup,SimpleGraph.Walk.length_support] at hh
  omega

theorem blockers_ncard_le (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (w : RawCorridor G k) : w.blockers.ncard ≤ d*k := by
  have hs : w.blockers ⊆ (incidentSupport G hloc w.interior : Set E) :=
    fun e he => (mem_incidentSupport G hloc w.interior e).mpr he.1
  calc
    _ ≤ (incidentSupport G hloc w.interior : Set E).ncard := Set.ncard_le_ncard hs (Finset.finite_toSet _)
    _ = (incidentSupport G hloc w.interior).card := Set.ncard_coe_finset _
    _ ≤ w.interior.card*d := incidentSupport_card_le G hloc d hd _
    _ ≤ k*d := Nat.mul_le_mul_right _ (w.interior_card_le.trans w.path_length)
    _ = _ := Nat.mul_comm _ _

end RawCorridor
end CorridorSizeBounds
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkTotalMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_finite_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x : V) : (Function.support (walkKernel G hloc a x)).Finite := by
  apply (Finset.finite_toSet (insert x (neighbors G hloc x))).subset
  intro y hy
  by_contra hn
  have hn' : y ≠ x ∧ ¬Adj G x y := by simpa only [Finset.mem_coe,Finset.mem_insert,mem_neighbors,not_or] using hn
  exact hy (by simp only [walkKernel,ite_eq_right hn'.1.symm,ite_eq_right hn'.2,add_zero])

theorem walkKernel_tsum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ) (x : V) :
    (∑' y, walkKernel G hloc a x y) = 1 := by
  rw [tsum_eq_sum (s := insert x (neighbors G hloc x))]
  · exact walkKernel_row_sum G hloc a x
  · intro y hy
    have hn : y ≠ x ∧ ¬Adj G x y := by simpa only [Finset.mem_insert,mem_neighbors,not_or] using hy
    simp only [walkKernel,ite_eq_right hn.1.symm,ite_eq_right hn.2,add_zero]

theorem raw_integral_one (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (k : ℕ) (x : V) :
    RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k x (fun _ => 1) = 1 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  induction k generalizing x with
  | zero => exact RawFrom.integral_zero _ _ _
  | succ k ih =>
    rw [RawFrom.integral_succ]
    simp only [ih,mul_one]
    have he := sum_step_decomposition (openSimpleGraph G Set.univ) (walkKernel G hloc a)
      (walkKernel_finite_support G hloc a) (fun x y hxy hn => by
        apply walkKernel_zero_of_not_step G hloc a x y hxy
        intro h
        obtain ⟨e,he⟩ := h
        exact hn ⟨hxy,e,Set.mem_univ e,he⟩) x (fun _ => 1)
    simpa only [mul_one,walkKernel_tsum G hloc a] using he.symm

 
theorem rawFrom_probability_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (k : ℕ) (x : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) k x, w.2.mass (walkKernel G hloc a)) = 1 := by
  simpa only [RawFrom.integral,mul_one] using raw_integral_one G hloc a k x

end RawWalkTotalMass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkFiniteBases
attribute [local instance] Classical.propDecidable Classical.decEq

theorem raw_probability_on_bases_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (k : ℕ) (S : Set V) (hS : S.Finite) :
    (∑' w : RawCorridor G k, if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) = (S.ncard:ℝ) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  have hs : Summable (fun w : RawCorridor G k => if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (finite_corridors_on_bases G hloc k S hS).subset
    intro w hw
    by_contra hn
    exact hw (ite_eq_right hn)
  rw [hs.tsum_sigma]
  have he (x : V) : (∑' w : RawFrom (openSimpleGraph G Set.univ) k x,
      if (RawCorridor.base ⟨x,w⟩) ∈ S then (RawCorridor.probability (walkKernel G hloc a) ⟨x,w⟩) else 0) =
      if x ∈ S then 1 else 0 := by
    by_cases hx : x ∈ S
    · simp only [RawCorridor.base,RawCorridor.probability,hx,if_true,rawFrom_probability_sum G hloc a k x]
    · simp only [RawCorridor.base,hx,if_false,tsum_zero]
  simp only [he]
  rw [tsum_eq_sum (s := hS.toFinset)]
  · rw [Finset.sum_congr rfl (fun x hx => ite_eq_left (hS.mem_toFinset.mp hx))]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [←Set.ncard_eq_toFinset_card _ hS]
  · intro x hx
    exact ite_eq_right (fun h => hx (hS.mem_toFinset.mpr h))

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem base_mem_reachBall_of_retained (w : RawCorridor G k) (e : E)
    (he : e ∈ w.retained) (z : V) (hz : z ∈ G e) : w.base ∈ reachBall G z k := by
  have hs : z ∈ w.path.support := SimpleGraph.Walk.mem_support_of_mem_edges he hz
  let q := (w.path.takeUntil z hs).reverse
  have hq : q.length ≤ k := by
    change (w.path.takeUntil z hs).reverse.length ≤ k
    rw [SimpleGraph.Walk.length_reverse]
    exact (w.path.length_takeUntil_le_length hs).trans w.path_length
  have hh := walk_mem_reachBall G Set.univ (x := z) q 0 (by simp only [reachBall,Set.mem_singleton_iff])
  simp only [Nat.zero_add] at hh
  exact reachBall_mono_local G z hq hh

theorem counted_base_mem_cluster (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : w.counted D ω x y) : w.base ∈ cluster G ω x := by
  obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.2.2.1
  have hm := w.counted_base_mem_walk D ω x y hc q
  exact conn_mono G Set.inter_subset_left ((conn_iff_reachable G _ x w.base).mpr ⟨q.takeUntil w.base hm⟩)

end RawCorridor
end RawWalkFiniteBases
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformRawWeight
attribute [local instance] Classical.propDecidable Classical.decEq


theorem rawWeightBase_one_le {r q : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hq : 0 < q) (hq₁ : q ≤ 1) (d : ℕ) : 1 ≤ rawWeightBase r q d := by
  exact one_le_mul_of_one_le_of_one_le ((one_le_inv₀ hr).mpr hr₁)
    (one_le_pow₀ ((one_le_inv₀ hq).mpr hq₁))

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem weight_le_uniform (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (w : RawCorridor G k) : w.weight P p ≤ w.probability P * (rawWeightBase r q d)^k := by
  have hp₀ : 0 < (p:ℝ) := hr.trans_le hrp
  have hp₁ : 0 < 1-(p:ℝ) := hq.trans_le hqp
  have hr₁ : r ≤ 1 := hrp.trans p.2.2
  have hq₁ : q ≤ 1 := hqp.trans (sub_le_self _ p.2.1)
  have hi : (p:ℝ)⁻¹ ≤ r⁻¹ := inv_anti₀ hr hrp
  have hj : (1-(p:ℝ))⁻¹ ≤ q⁻¹ := inv_anti₀ hq hqp
  have hL : ((p:ℝ)^w.path.length)⁻¹ ≤ (r⁻¹)^k := by
    simp only [←inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr p.2.1) hi _).trans
      (pow_le_pow_right₀ ((one_le_inv₀ hr).mpr hr₁) w.path_length)
  have hB : ((1-(p:ℝ))^w.blockers.ncard)⁻¹ ≤ ((q⁻¹)^d)^k := by
    simp only [←inv_pow,←pow_mul]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hp₁.le) hj _).trans
      (pow_le_pow_right₀ ((one_le_inv₀ hq).mpr hq₁) (w.blockers_ncard_le hloc d hd))
  unfold weight
  calc
    _ = w.probability P * (((p:ℝ)^w.path.length)⁻¹ * ((1-(p:ℝ))^w.blockers.ncard)⁻¹) := mul_assoc _ _ _
    _ ≤ w.probability P * ((r⁻¹)^k * ((q⁻¹)^d)^k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hL hB
        (inv_nonneg.mpr (pow_nonneg hp₁.le _)) (pow_nonneg (inv_nonneg.mpr hr.le) _))
        (w.2.2.mass_nonneg P hP)
    _ = _ := by rw [rawWeightBase,mul_pow]

end RawCorridor
end UniformRawWeight
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformPenaltyDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_raw_selection (G : BondGraph V E) (hloc : LocallyFinite G)
    (k : ℕ) (S : Set V) (hS : S.Finite) (Q : RawCorridor G k → Prop)
    (hQ : ∀ w, Q w → w.base ∈ S) (f : RawCorridor G k → ℝ) :
    Summable (fun w => if Q w then f w else 0) := by
  apply summable_of_hasFiniteSupport
  apply (finite_corridors_on_bases G hloc k S hS).subset
  intro w hw
  by_contra hn
  exact hw (ite_eq_right (fun h => hn (hQ w h)))

theorem mask_le_mask_mul {U W : Prop} [Decidable U] [Decidable W] (hUW : U → W)
    {f g B : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hfg : f ≤ g*B) :
    (if U then f else 0) ≤ (if W then g else 0)*B := by
  by_cases hU : U
  · simp only [hU,hUW hU,if_true]; exact hfg
  · rw [ite_eq_right hU]
    by_cases hW : W
    · rw [ite_eq_left hW]; exact mul_nonneg hg hB
    · rw [ite_eq_right hW,zero_mul]

theorem raw_weight_sum_le_on_bases (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (S : Set V) (hS : S.Finite) (Q : RawCorridor G k → Prop)
    (hQ : ∀ w, Q w → w.base ∈ S) :
    (∑' w : RawCorridor G k, if Q w then w.weight (walkKernel G hloc a) p else 0) ≤
      (S.ncard:ℝ)*(rawWeightBase r q d)^k := by
  have hf := summable_raw_selection G hloc k S hS Q hQ
    (fun w => w.weight (walkKernel G hloc a) p)
  have hg := summable_raw_selection G hloc k S hS (fun w => w.base ∈ S)
    (fun _ h => h) (fun w => w.probability (walkKernel G hloc a))
  have hB : 0 ≤ (rawWeightBase r q d)^k := pow_nonneg
    (zero_le_one.trans (rawWeightBase_one_le hr (hrp.trans p.2.2) hq (hqp.trans (sub_le_self _ p.2.1)) d)) _
  have hpoint (w : RawCorridor G k) :
      (if Q w then w.weight (walkKernel G hloc a) p else 0) ≤
        (if w.base ∈ S then w.probability (walkKernel G hloc a) else 0) * (rawWeightBase r q d)^k :=
    mask_le_mask_mul (hQ w) (w.2.2.mass_nonneg _ hP) hB
      (w.weight_le_uniform hloc d hd (walkKernel G hloc a) hP p hr hq hrp hqp)
  have hb := hf.tsum_le_tsum hpoint (hg.mul_right ((rawWeightBase r q d)^k))
  rw [tsum_mul_right,raw_probability_on_bases_sum G hloc a k S hS] at hb
  exact hb

 

theorem corridorPenalty_le_cluster (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) (hf : (cluster G ω x).Finite) :
    corridorPenalty G (walkKernel G hloc a) p k D ω x y ≤
      ((cluster G ω x).ncard:ℝ)*(rawWeightBase r q d)^k := by
  exact raw_weight_sum_le_on_bases G hloc d hd a hP p hr hq hrp hqp k _ hf
    (fun w => w.counted D ω x y) (fun w hw => w.counted_base_mem_cluster D ω x y hw)

 

theorem raw_edge_weight_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrp : r ≤ (p:ℝ)) (hqp : q ≤ 1-(p:ℝ))
    (k : ℕ) (e : E) (z : V) (hz : z ∈ G e) :
    (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤
      (((d:ℝ)+1)*rawWeightBase r q d)^k := by
  have hb := raw_weight_sum_le_on_bases G hloc d hd a hP p hr hq hrp hqp k
    (reachBall G z k) (finite_reachBall hloc z k) (fun w => e ∈ w.retained)
    (fun w hw => w.base_mem_reachBall_of_retained e hw z hz)
  have hcard : ((reachBall G z k).ncard:ℝ) ≤ ((d:ℝ)+1)^k := by
    exact_mod_cast reachBall_ncard_le_pow G hloc d hd z k
  have hB : 0 ≤ (rawWeightBase r q d)^k := pow_nonneg
    (zero_le_one.trans (rawWeightBase_one_le hr (hrp.trans p.2.2) hq (hqp.trans (sub_le_self _ p.2.1)) d)) _
  exact hb.trans ((mul_le_mul_of_nonneg_right hcard hB).trans_eq (mul_pow _ _ _).symm)

end UniformPenaltyDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExponentialCorridorCost
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pow_le_exp_div_self {B : ℝ} (hB : 1 ≤ B) {k : ℕ} (hk : 0 < k) :
    B^k ≤ Real.exp ((Real.log B + 1)*(k:ℝ))/(k:ℝ) := by
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  apply (le_div_iff₀ (Nat.cast_pos.mpr hk)).mpr
  have hh : (k:ℝ) ≤ Real.exp (k:ℝ) := by linarith [Real.add_one_le_exp (k:ℝ)]
  calc
    _ ≤ B^k * Real.exp (k:ℝ) := mul_le_mul_of_nonneg_left hh (pow_nonneg hB₀.le _)
    _ = Real.exp ((k:ℝ)*Real.log B) * Real.exp (k:ℝ) := by rw [Real.exp_nat_mul,Real.exp_log hB₀]
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

 

theorem exists_uniform_corridor_edge_cost (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (k : ℕ), 3 ≤ k → ∀ e : E,
      (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤
        Real.exp (C*(k:ℝ))/(k:ℝ) := by
  let B := ((d:ℝ)+1)*rawWeightBase ((pc G:ℝ)/2) (1-(pc G:ℝ)) d
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    (rawWeightBase_one_le (half_pos hpcrit) (by have := (pc G).2.2; linarith)
      (sub_pos.mpr hpcrit₁) (sub_le_self _ (pc G).2.1) d)
  refine ⟨Real.log B + 1,by linarith [Real.log_nonneg hB],?_⟩
  intro p hpnear hp k hk e
  obtain ⟨z,z',hzz⟩ : ∃ z z', G e = s(z,z') := by
    obtain ⟨⟨z,z'⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨z,z',hh.symm⟩
  have he : z ∈ G e := hzz.symm ▸ Sym2.mem_mk_left z z'
  have hq : 1-(pc G:ℝ) ≤ 1-(p:ℝ) := sub_le_sub_left (show (p:ℝ) ≤ (pc G:ℝ) from hp.le) (1:ℝ)
  exact (raw_edge_weight_bound G hloc d hd a hP p (half_pos hpcrit)
    (sub_pos.mpr hpcrit₁) hpnear hq k e z he).trans (pow_le_exp_div_self hB (by omega))

end ExponentialCorridorCost
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LiteralDeformationDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_eq_zero_of_not_conn (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) (hn : ¬Conn G ω x y) :
    deformedConnection G P p k t D ω x y = 0 := by
  have hnc : ¬Conn G (ω ∩ internalEdges G D) x y := fun h => hn (conn_mono G Set.inter_subset_left h)
  simp only [deformedConnection,hnc,and_false,if_false]

theorem deformedClusterMass_eq_sum (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : deformedClusterMass G P p k t D ω x =
      ∑ y ∈ hf.toFinset, deformedConnection G P p k t D ω x y := by
  apply tsum_eq_sum
  intro y hy
  exact deformedConnection_eq_zero_of_not_conn G P p k t D ω x y (fun h => hy (hf.mem_toFinset.mpr h))

theorem deformedDerivativeMass_eq_sum (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : deformedDerivativeMass G P p k t D ω x =
      ∑ y ∈ hf.toFinset, corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y := by
  apply tsum_eq_sum
  intro y hy
  rw [deformedConnection_eq_zero_of_not_conn G P p k t D ω x y (fun h => hy (hf.mem_toFinset.mpr h)),mul_zero]

theorem measurable_deformedDerivativeMass [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    Measurable (fun ω => deformedDerivativeMass G P p k t D ω x) :=
  Measurable.tsum (fun y => (measurable_corridorPenalty G P p k D x y).mul
    (measurable_deformedConnection G P p k t D x y))

theorem deformedDerivativeMass_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ)
    (D : Set V) (ω : Set E) (x : V) : 0 ≤ deformedDerivativeMass G P p k t D ω x :=
  tsum_nonneg (fun y => mul_nonneg (corridorPenalty_nonneg G P hP p k D ω x y)
    (deformedConnection_nonneg G P p k t D ω x y))

theorem hasDerivAt_deformedConnection (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    HasDerivAt (fun s => deformedConnection G P p k s D ω x y)
      (-(corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y)) t := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · simp only [deformedConnection,hc,and_self,if_true]
    simpa only [Pi.neg_apply,id_eq,neg_mul,one_mul,mul_neg,mul_comm] using
      (((hasDerivAt_id t).neg.mul_const (corridorPenalty G P p k D ω x y)).exp)
  · simpa only [deformedConnection,hc,if_false,mul_zero,neg_zero] using hasDerivAt_const t (0:ℝ)

 

theorem hasDerivAt_deformedClusterMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) :
    HasDerivAt (fun s => deformedClusterMass G P p k s D ω x)
      (-deformedDerivativeMass G P p k t D ω x) t := by
  have hh := HasDerivAt.fun_sum (u := hf.toFinset) (fun y _ => hasDerivAt_deformedConnection G P p k t D ω x y)
  simpa only [deformedClusterMass_eq_sum G P p k _ D ω x hf,
    deformedDerivativeMass_eq_sum G P p k t D ω x hf,Finset.sum_neg_distrib] using hh

end LiteralDeformationDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationDerivativeDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedDerivativeMass_le_square (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x : V) (hf : (cluster G ω x).Finite) :
    deformedDerivativeMass G (walkKernel G hloc a) p k t D ω x ≤
      ((cluster G ω x).ncard:ℝ)^2 * (rawWeightBase p (1-(p:ℝ)) d)^k := by
  rw [deformedDerivativeMass_eq_sum G (walkKernel G hloc a) p k t D ω x hf]
  calc
    _ ≤ ∑ _y ∈ hf.toFinset, ((cluster G ω x).ncard:ℝ)*(rawWeightBase p (1-(p:ℝ)) d)^k := by
      apply Finset.sum_le_sum
      intro y _
      have hn := corridorPenalty_nonneg G (walkKernel G hloc a) hP p k D ω x y
      exact (mul_le_of_le_one_right hn (deformedConnection_le_one G (walkKernel G hloc a) hP p k t ht D ω x y)).trans
        (corridorPenalty_le_cluster G hloc d hd a hP p hp0 (sub_pos.mpr hp1) le_rfl le_rfl k D ω x y hf)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
      ring

end DeformationDerivativeDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section DeformationDifferentiation
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem hasDerivAt_deformedSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 < t)
    (D : Set V) (x : V) :
    HasDerivAt (fun s => deformedSusceptibility G (walkKernel G hloc a) p k s D x)
      (-(∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t D ω x ∂law p)) t := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  have hp1 : (p:ℝ) < 1 := (show (p:ℝ) < (pc G:ℝ) from hp).trans_le (pc G).2.2
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := law p) (s := Set.Ioi 0) (x₀ := t)
    (F := fun s ω => deformedClusterMass G (walkKernel G hloc a) p k s D ω x)
    (F' := fun s ω => -deformedDerivativeMass G (walkKernel G hloc a) p k s D ω x)
    (bound := fun ω => ((cluster G ω x).ncard:ℝ)^2*(rawWeightBase p (1-(p:ℝ)) d)^k)
    (Ioi_mem_nhds ht)
    (Filter.Eventually.of_forall (fun s => (measurable_deformedClusterMass G (walkKernel G hloc a) p k s D x).aestronglyMeasurable))
    (integrable_deformedClusterMass G hloc hqt (walkKernel G hloc a) hP p hp k t ht.le D x)
    (measurable_deformedDerivativeMass G (walkKernel G hloc a) p k t D x).neg.aestronglyMeasurable
    (by
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      intro s hs
      rw [norm_neg,Real.norm_of_nonneg (deformedDerivativeMass_nonneg G (walkKernel G hloc a) hP p k s D ω x)]
      exact deformedDerivativeMass_le_square G hloc d hd a hP p hp0 hp1 k s hs.le D ω x hω)
    ((hs x).1.mul_const _)
    (by
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      intro s _
      exact hasDerivAt_deformedClusterMass G (walkKernel G hloc a) p k s D ω x hω)
  rw [integral_neg] at hder
  apply hder.2.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact deformedSusceptibility_eq_integral G hloc hqt (walkKernel G hloc a) hP p hp k s hs.le D x

end DeformationDifferentiation
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalMoveGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_move_terminal (w : RawCorridor G k) (D : Set V) (ω : Set E)
    (F : Set E) (hF : F ⊆ ω ∩ internalEdges G D) (b z y : V)
    (hbz : Conn G F b z) (hc : w.counted D ω b y) (hdis : Disjoint F w.retained) :
    w.counted D ω z y := by
  apply (w.counted_iff D ω z y).mpr
  refine ⟨hc.1,conn_trans G _ (conn_symm G _ (conn_mono G hF hbz)) hc.2.2.1,?_,hc.2.2.2.2⟩
  intro e he
  refine ⟨(hc.2.2.2.1 e he).1,?_⟩
  intro hzy
  apply (hc.2.2.2.1 e he).2
  apply conn_trans G _ (conn_mono G ?_ hbz) hzy
  intro f hf
  refine ⟨hF hf,?_⟩
  intro hfe
  have hh : f = e := Set.mem_singleton_iff.mp hfe
  exact Set.disjoint_left.mp hdis hf (hh.symm ▸ he)

end RawCorridor

 

theorem corridorPenaltyTerm_move_bound (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (D : Set V) (ω : Set E)
    (F : Finset E) (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V)
    (hbz : Conn G (F:Set E) b z) (w : RawCorridor G k) :
    corridorPenaltyTerm G P p D ω b y w ≤
      (∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0) + corridorPenaltyTerm G P p D ω z y w := by
  have hn := w.weight_nonneg P hP p
  have hs : 0 ≤ ∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0 :=
    Finset.sum_nonneg (fun e _ => by split_ifs; exact hn; exact le_rfl)
  by_cases hc : w.counted D ω b y
  · rw [corridorPenaltyTerm,ite_eq_left hc]
    by_cases hd : Disjoint (F:Set E) w.retained
    · have hc' := w.counted_move_terminal D ω F hF b z y hbz hc hd
      simpa only [corridorPenaltyTerm,hc',if_true] using le_add_of_nonneg_left hs
    · obtain ⟨e,he,hew⟩ := Set.not_disjoint_iff.mp hd
      have he' : (if e ∈ w.retained then w.weight P p else 0) ≤
          ∑ f ∈ F, if f ∈ w.retained then w.weight P p else 0 :=
        Finset.single_le_sum (f := fun f => if f ∈ w.retained then w.weight P p else 0) (fun f _ => by split_ifs; exact hn; exact le_rfl) he
      rw [ite_eq_left hew] at he'
      exact he'.trans (le_add_of_nonneg_right (corridorPenaltyTerm_nonneg G P hP p D ω z y w))
  · rw [corridorPenaltyTerm,ite_eq_right hc]
    exact add_nonneg hs (corridorPenaltyTerm_nonneg G P hP p D ω z y w)

end TerminalMoveGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalMovePenalty
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_raw_edge_weights (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (e : E) :
    Summable (fun w : RawCorridor G k => if e ∈ w.retained then w.weight P p else 0) := by
  obtain ⟨z,z',hzz⟩ : ∃ z z', G e = s(z,z') := by
    obtain ⟨⟨z,z'⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨z,z',hh.symm⟩
  have he : z ∈ G e := hzz.symm ▸ Sym2.mem_mk_left z z'
  exact summable_raw_selection G hloc k (reachBall G z k) (finite_reachBall hloc z k)
    (fun w => e ∈ w.retained) (fun w hw => w.base_mem_reachBall_of_retained e hw z he)
    (fun w => w.weight P p)

 

theorem corridorPenalty_move_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V) (hbz : Conn G (F:Set E) b z) :
    corridorPenalty G P p k D ω b y ≤
      (∑ e ∈ F, ∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) +
        corridorPenalty G P p k D ω z y := by
  have hs : Summable (fun w : RawCorridor G k => ∑ e ∈ F, if e ∈ w.retained then w.weight P p else 0) :=
    (hasSum_sum (fun e (_ : e ∈ F) => (summable_raw_edge_weights G hloc P p k e).hasSum)).summable
  have hr := corridorPenalty_summable G hloc P p k D ω z y
  have hl := (corridorPenalty_summable G hloc P p k D ω b y).tsum_le_tsum
    (corridorPenaltyTerm_move_bound G P hP p k D ω F hF b z y hbz) (hs.add hr)
  rw [hs.tsum_add hr,Summable.tsum_finsetSum (fun e _ => summable_raw_edge_weights G hloc P p k e)] at hl
  exact hl

end TerminalMovePenalty
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteOpeningAssociation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_union_const (S : Set E) : Measurable (fun ω : Set E => ω ∪ S) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).or measurable_const

theorem measurableSet_finite_open (F : Finset E) : MeasurableSet {ω : Set E | (F:Set E) ⊆ ω} := by
  have he : {ω : Set E | (F:Set E) ⊆ ω} = ⋂ e ∈ F, {ω : Set E | e ∈ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Finset.mem_coe,Set.subset_def]
  rw [he]
  exact F.measurableSet_biInter (fun e _ => measurableSet_setOfPred.mpr ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable))

 

theorem finite_open_integral_lower (p : unitInterval) (F : Finset E) (f : Set E → ℝ)
    (hf : Measurable f) (hn : ∀ ω, 0 ≤ f ω) (hb : ∀ ω, f ω ≤ 1)
    (hm : Monotone f) :
    (p:ℝ)^F.card*(∫ ω, f ω ∂law p) ≤ ∫ ω, if (F:Set E) ⊆ ω then f ω else 0 ∂law p := by
  let J : Set E → ℝ := fun ω => if (F:Set E) ⊆ ω then 1 else 0
  let g : Set E → ℝ := fun ω => f (ω ∪ (F:Set E))
  have hJ : Measurable J := Measurable.ite (measurableSet_finite_open F) measurable_const measurable_const
  have hg : Measurable g := hf.comp (measurable_union_const (F:Set E))
  have hi (f : Set E → ℝ) (hfm : Measurable f) (hfn : ∀ ω, 0 ≤ f ω) (hfb : ∀ ω, f ω ≤ 1) : Integrable f (law p) := by
    exact Integrable.mono' (integrable_const (1:ℝ)) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (hfn ω)]; exact hfb ω))
  have hfi := hi f hf hn hb
  have hgi := hi g hg (fun ω => hn _) (fun ω => hb _)
  have hJint : (∫ ω, J ω ∂law p) = (p:ℝ)^F.card := by
    have hh := integral_indicator_const (μ := law p) (1:ℝ) (measurableSet_finite_open F)
    simpa only [Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_one,finite_open_probability,J] using hh
  have he := integral_mul_disjoint_coordinates p (F:Set E) (F:Set E)ᶜ disjoint_compl_right J g hJ hg
    (fun ω => by simp only [J,Set.subset_inter_iff,Set.Subset.refl,and_true])
    (fun ω => by
      dsimp only [g]
      congr 1
      ext e
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
      tauto)
  calc
    _ ≤ (p:ℝ)^F.card*(∫ ω, g ω ∂law p) := mul_le_mul_of_nonneg_left
      (integral_mono hfi hgi (fun ω => hm Set.subset_union_left)) (pow_nonneg p.2.1 _)
    _ = (∫ ω, J ω ∂law p)*(∫ ω, g ω ∂law p) := by rw [hJint]
    _ = ∫ ω, J ω*g ω ∂law p := he.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hF : (F:Set E) ⊆ ω
        · simp only [J,g,hF,if_true,one_mul,Set.union_eq_left.mpr hF]
        · simp only [J,hF,if_false,zero_mul])

end FiniteOpeningAssociation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TerminalConnectionComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenalty_move_edge_cost (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ ω ∩ internalEdges G D) (b z y : V) (hbz : Conn G (F:Set E) b z)
    (c : ℝ) (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    corridorPenalty G P p k D ω b y ≤ (F.card:ℝ)*c+corridorPenalty G P p k D ω z y := by
  apply (corridorPenalty_move_bound G hloc P hP p k D ω F hF b z y hbz).trans
  apply add_le_add _ le_rfl
  exact (Finset.sum_le_sum (fun e _ => hc e)).trans_eq (by simp only [Finset.sum_const,nsmul_eq_mul])

 

theorem deformedConnection_move_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (ω : Set E) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z y : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (if (F:Set E) ⊆ ω then deformedConnection G P p k t D ω z y else 0) ≤
      deformedConnection G P p k t D ω b y := by
  by_cases ho : (F:Set E) ⊆ ω
  · rw [ite_eq_left ho]
    by_cases hz : z ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) z y
    · have hFa : (F:Set E) ⊆ ω ∩ internalEdges G D := fun e he => ⟨ho he,hF he⟩
      have hb' : b ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) b y :=
        ⟨hb,hz.2.1,conn_trans G _ (conn_mono G hFa hbz) hz.2.2⟩
      simp only [deformedConnection,hz,hb',and_self,if_true]
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonpos_left
        (corridorPenalty_move_edge_cost G hloc P hP p k D ω F hFa b z y hbz c hc) (neg_nonpos.mpr ht)
      simpa only [mul_add] using hh
    · rw [deformedConnection,ite_eq_right hz,mul_zero]
      exact deformedConnection_nonneg G P p k t D ω b y
  · rw [ite_eq_right ho,mul_zero]
    exact deformedConnection_nonneg G P p k t D ω b y

end TerminalConnectionComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section EndpointSusceptibilityComparison
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedKernel_move_lower [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z y : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card * deformedKernel G P p k t D z y ≤
      deformedKernel G P p k t D b y := by
  have hi := integrable_deformedConnection G P hP p k t ht D z y
  have hIi := hi.indicator (measurableSet_finite_open F)
  have has := finite_open_integral_lower p F (fun ω => deformedConnection G P p k t D ω z y)
    (measurable_deformedConnection G P p k t D z y)
    (fun ω => deformedConnection_nonneg G P p k t D ω z y)
    (fun ω => deformedConnection_le_one G P hP p k t ht D ω z y)
    (fun _ _ hω => deformedConnection_mono G hloc P hP p k t ht (Set.Subset.refl _) hω z y)
  have hb' := integral_mono (hIi.const_mul (Real.exp (-t*((F.card:ℝ)*c))))
    (integrable_deformedConnection G P hP p k t ht D b y)
    (fun ω => deformedConnection_move_lower G hloc P hP p k t ht D ω F hF b z y hb hbz c hc)
  simp only [Set.indicator,Set.mem_ofPred_eq,integral_const_mul] at hb'
  have hh := mul_le_mul_of_nonneg_left has (Real.exp_pos (-t*((F.card:ℝ)*c))).le
  simp only [mul_assoc] at hh ⊢
  exact hh.trans hb'

 
theorem deformedSusceptibility_move_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (F : Finset E)
    (hF : (F:Set E) ⊆ internalEdges G D) (b z : V) (hb : b ∈ D)
    (hbz : Conn G (F:Set E) b z) (c : ℝ)
    (hc : ∀ e, (∑' w : RawCorridor G k, if e ∈ w.retained then w.weight P p else 0) ≤ c) :
    Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card * deformedSusceptibility G P p k t D z ≤
      deformedSusceptibility G P p k t D b := by
  simpa only [deformedSusceptibility,tsum_mul_left] using
    ((summable_deformedKernel G hloc hqt P hP p hp k t ht D z).mul_left
      (Real.exp (-t*((F.card:ℝ)*c)) * (p:ℝ)^F.card)).tsum_le_tsum
      (fun y => deformedKernel_move_lower G hloc P hP p k t ht D F hF b z y hb hbz c hc)
      (summable_deformedKernel G hloc hqt P hP p hp k t ht D b)

end EndpointSusceptibilityComparison
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Calibration
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformDeformedEndpoint
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_uniform_deformed_endpoint_comparison [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (k : ℕ), 3 ≤ k → ∀ (t : ℝ), 0 ≤ t → ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b := by
  obtain ⟨C,hC,hcost⟩ := exists_uniform_corridor_edge_cost G hloc d hd a hP hpcrit hpcrit₁
  refine ⟨C,hC,?_⟩
  intro p hpnear hp k hk t ht D b z l hb hl hD
  have hc : ∀ e, (∑' w : RawCorridor G k,
      if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤ Real.exp (C*(k:ℝ)) := by
    intro e
    exact (hcost p hpnear hp k hk e).trans (div_le_self (Real.exp_pos _).le (by exact_mod_cast (show 1 ≤ k by omega)))
  have hh := deformedSusceptibility_move_lower G hloc hqt (walkKernel G hloc a) hP p hp k t ht D
    l.toFinset (fun e he => hD e (List.mem_toFinset.mp he)) b z hb
    (hl.conn (fun e he => List.mem_toFinset.mpr he)) (Real.exp (C*(k:ℝ))) hc
  have hcard : (l.toFinset.card:ℝ) ≤ (l.length:ℝ) := Nat.cast_le.mpr l.toFinset_card_le
  have he : Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) ≤
      Real.exp (-t*((l.toFinset.card:ℝ)*Real.exp (C*(k:ℝ)))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le) (neg_nonpos.mpr ht)
  have hpw : (p:ℝ)^l.length ≤ (p:ℝ)^l.toFinset.card :=
    pow_le_pow_of_le_one p.2.1 p.2.2 l.toFinset_card_le
  exact (mul_le_mul_of_nonneg_right (mul_le_mul he hpw (pow_nonneg p.2.1 _) (Real.exp_pos _).le)
    (tsum_nonneg (deformedKernel_nonneg G (walkKernel G hloc a) p k t D z))).trans hh

end UniformDeformedEndpoint
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedLegComparison
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}
theorem base_not_interior (w : RawCorridor G k) : w.base ∉ w.interior := by
  simp only [interior,Finset.mem_sdiff,Finset.mem_insert,true_or,not_true_eq_false,and_false,not_false_eq_true]
theorem endpoint_not_interior (w : RawCorridor G k) : w.endpoint ∉ w.interior := by
  simp only [interior,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,or_true,not_true_eq_false,and_false,not_false_eq_true]
end RawCorridor


end WeightedLegComparison
end Percolation


namespace Percolation
universe u u' v
section ErasureNaturality
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {H : SimpleGraph V} {H' : SimpleGraph V'}

theorem walk_map_dropUntil (f : H →g H') (hf : Function.Injective f)
    {x y : V} (w : H.Walk x y) (z : V) (hz : z ∈ w.support) :
    (w.dropUntil z hz).map f = (w.map f).dropUntil (f z)
      (by simpa only [SimpleGraph.Walk.support_map] using List.mem_map_of_mem hz) := by
  induction w with
  | @nil x =>
    have he : z = x := by simpa using hz
    subst z
    rfl
  | @cons x a y h w ih =>
    by_cases he : x = z
    · subst z
      simp only [SimpleGraph.Walk.dropUntil_first]
    · have hfe : f x ≠ f z := fun h => he (hf h)
      simp only [SimpleGraph.Walk.dropUntil,he,hfe,SimpleGraph.Walk.map_cons]
      exact ih _

 

theorem walk_map_bypass (f : H →g H') (hf : Function.Injective f)
    {x y : V} (w : H.Walk x y) : w.bypass.map f = (w.map f).bypass := by
  induction w with
  | nil => rfl
  | @cons x a y h w ih =>
    have hm : f x ∈ (w.map f).bypass.support ↔ x ∈ w.bypass.support := by
      rw [←ih,SimpleGraph.Walk.support_map]
      exact List.mem_map_of_injective hf
    by_cases hx : x ∈ w.bypass.support
    · have hfx := hm.mpr hx
      simp only [SimpleGraph.Walk.bypass,SimpleGraph.Walk.map_cons,dite_eq_left hx,dite_eq_left hfx]
      simp only [walk_map_dropUntil f hf,ih]
    · have hfx := mt hm.mp hx
      simp only [SimpleGraph.Walk.bypass,SimpleGraph.Walk.map_cons,dite_eq_right hx,dite_eq_right hfx,ih]

namespace HoldingWalk

theorem map_vertices (f : H →g H') {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).vertices = w.vertices.map f := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [map,vertices,List.map_cons,ih]
  | step h w ih => simp only [map,vertices,List.map_cons,ih]

theorem map_withoutHolds (f : H →g H') {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).withoutHolds = w.withoutHolds.map f := by
  induction w with
  | nil => rfl
  | hold w ih => exact ih
  | step h w ih => simp only [map,withoutHolds,SimpleGraph.Walk.map_cons,ih]

theorem map_erase (f : H →g H') (hf : Function.Injective f)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).erase = w.erase.map f := by
  simp only [erase,map_withoutHolds,SimpleGraph.Walk.reverse_map,
    ←walk_map_bypass f hf]

end HoldingWalk
end ErasureNaturality
end Percolation

 
namespace Percolation
universe u u' u'' v
section RawWalkMaps
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {V'' : Type u''}
  {H : SimpleGraph V} {H' : SimpleGraph V'} {H'' : SimpleGraph V''}
namespace HoldingWalk

theorem mass_map (f : H →g H') (P : V → V → ℝ) (Q : V' → V' → ℝ)
    (hPQ : ∀ x y, Q (f x) (f y) = P x y)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : (w.map f).mass Q = w.mass P := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [map,mass,hPQ,ih]
  | step h w ih => simp only [map,mass,hPQ,ih]
end HoldingWalk

end RawWalkMaps
section GraphAutWalks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {E : Type v}

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem aut_path {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path = w.path.map (autSimpleGraph G hab).toHom :=
  w.2.2.map_erase _ a.injective

theorem aut_path_length {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.length = w.path.length := by
  have hh := congrArg (fun q => q.length) (aut_path hab w)
  exact hh.trans (SimpleGraph.Walk.length_map _ _)

end RawCorridor
end GraphAutWalks
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TemplateCovariance
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem aut_base {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).base = a w.base := rfl

theorem aut_endpoint {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).endpoint = a w.endpoint := rfl

theorem aut_support {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.support = w.path.support.map a := by
  exact (congrArg (fun q => q.support) (aut_path hab w)).trans
    (SimpleGraph.Walk.support_map _ _)

theorem aut_edges {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.edges = w.path.edges.map (Sym2.map a) := by
  exact (congrArg (fun q => q.edges) (aut_path hab w)).trans
    (SimpleGraph.Walk.edges_map _ _)

theorem aut_interior {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (z : V) :
    a z ∈ (autEquiv hab w).interior ↔ z ∈ w.interior := by
  simp only [interior,Finset.mem_sdiff,List.mem_toFinset]
  rw [aut_support hab w]
  simp only [aut_base,aut_endpoint,Finset.mem_insert,Finset.mem_singleton,
    List.mem_map_of_injective a.injective,a.injective.eq_iff]

theorem aut_retained {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (e : E) :
    b e ∈ (autEquiv hab w).retained ↔ e ∈ w.retained := by
  simp only [retained,Set.mem_ofPred_eq,aut_edges hab w,hab e]
  exact List.mem_map_of_injective (Sym2.map.injective a.injective)

theorem aut_blockers {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (e : E) :
    b e ∈ (autEquiv hab w).blockers ↔ e ∈ w.blockers := by
  simp only [blockers,Set.mem_sdiff,Set.mem_ofPred_eq,aut_retained]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨z,hz,he⟩
    rw [hab e] at he
    obtain ⟨y,hy,rfl⟩ := Sym2.mem_map.mp he
    exact ⟨y,(aut_interior hab w y).mp hz,hy⟩
  · rintro ⟨z,hz,he⟩
    refine ⟨a z,(aut_interior hab w z).mpr hz,?_⟩
    rw [hab e]
    exact Sym2.mem_map.mpr ⟨z,he,rfl⟩

theorem aut_blockers_ncard {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).blockers.ncard = w.blockers.ncard := by
  have he : w.blockers = b ⁻¹' (autEquiv hab w).blockers := by
    ext e
    exact (aut_blockers hab w e).symm
  rw [he,Set.ncard_preimage_of_injective_subset_range b.injective]
  exact fun e _ => b.surjective e

theorem aut_probability {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y) (w : RawCorridor G k) :
    (autEquiv hab w).probability P = w.probability P :=
  w.2.2.mass_map (autSimpleGraph G hab).toHom P P hP

theorem aut_weight {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y) (p : ℝ) (w : RawCorridor G k) :
    (autEquiv hab w).weight P p = w.weight P p := by
  simp only [weight,aut_probability hab P hP,aut_path_length,aut_blockers_ncard]

end RawCorridor
end TemplateCovariance
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_AveragedDecrease
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CountedCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem preimage_diff_singleton (b : E ≃ E) (ω : Set E) (e : E) :
    (b ⁻¹' ω) \ {e} = b ⁻¹' (ω \ {b e}) := by
  ext f
  simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]

theorem corridorCounted_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set E) (D : Set V) (ω : Set E) (x y : V) :
    corridorCounted G (b ⁻¹' S) (b ⁻¹' B) (a ⁻¹' D) (b ⁻¹' ω) x y ↔
      corridorCounted G S B D ω (a x) (a y) := by
  have he : (b ⁻¹' ω) ∩ internalEdges G (a ⁻¹' D) = b ⁻¹' (ω ∩ internalEdges G D) := by
    rw [internalEdges_aut_preimage G hab,Set.preimage_inter]
  simp only [corridorCounted,he,conn_aut_iff G hab,preimage_diff_singleton,
    Set.mem_preimage]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨hp,hB⟩
    constructor
    · intro e he
      obtain ⟨f,rfl⟩ := b.surjective e
      exact hp f he
    · apply Set.disjoint_left.mpr
      intro e he hw
      obtain ⟨f,rfl⟩ := b.surjective e
      exact Set.disjoint_left.mp hB he hw
  · rintro ⟨hp,hB⟩
    exact ⟨fun e he => hp (b e) he,Set.disjoint_left.mpr (fun e he hw => Set.disjoint_left.mp hB he hw)⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem aut_counted {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted (a ⁻¹' D) (b ⁻¹' ω) x y ↔ (autEquiv hab w).counted D ω (a x) (a y) := by
  have hr : w.retained = b ⁻¹' (autEquiv hab w).retained := by
    ext e
    exact (aut_retained hab w e).symm
  have hb : w.blockers = b ⁻¹' (autEquiv hab w).blockers := by
    ext e
    exact (aut_blockers hab w e).symm
  rw [counted_iff,counted_iff,aut_path_length,hr,hb,corridorCounted_aut G hab]

end RawCorridor

theorem corridorPenaltyTerm_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) {k : ℕ} (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenaltyTerm G P p (a ⁻¹' D) (b ⁻¹' ω) x y w =
      corridorPenaltyTerm G P p D ω (a x) (a y) (RawCorridor.autEquiv hab w) := by
  simp only [corridorPenaltyTerm,w.aut_counted hab D ω x y,RawCorridor.aut_weight hab P hP]

theorem corridorPenalty_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenalty G P p k (a ⁻¹' D) (b ⁻¹' ω) x y =
      corridorPenalty G P p k D ω (a x) (a y) := by
  unfold corridorPenalty
  rw [←(RawCorridor.autEquiv hab).tsum_eq (corridorPenaltyTerm G P p D ω (a x) (a y))]
  exact tsum_congr (fun w => corridorPenaltyTerm_aut G hab P hP p w D ω x y)

end CountedCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t (a ⁻¹' D) (b ⁻¹' ω) x y =
      deformedConnection G P p k t D ω (a x) (a y) := by
  simp only [deformedConnection,corridorPenalty_aut G hab P hP,Set.mem_preimage,
    internalEdges_aut_preimage G hab,←Set.preimage_inter,conn_aut_iff G hab]

theorem deformedKernel_aut [Countable V] [Countable E]
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) :
    deformedKernel G P p k t D (a x) (a y) = deformedKernel G P p k t (a ⁻¹' D) x y := by
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable
    (measurable_deformedConnection G P p k t (a ⁻¹' D) x y).aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [deformedKernel,deformedConnection_aut G hab P hP] using h.symm

theorem deformedSusceptibility_aut [Countable V] [Countable E]
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) :
    deformedSusceptibility G P p k t D (a x) = deformedSusceptibility G P p k t (a ⁻¹' D) x := by
  unfold deformedSusceptibility
  rw [←a.tsum_eq (deformedKernel G P p k t D (a x))]
  exact tsum_congr (fun y => deformedKernel_aut G hab P hP p k t D x y)



end DeformationCovariance
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedDerivative
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]



theorem hasDerivAt_averagedDeformedSusceptibility (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight)
      (-(∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p)) t := by
  have he : -(∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p) =
      ∑ i, weight i * (-(∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p)) := by
    simp only [mul_neg,Finset.sum_neg_distrib]
  rw [he]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_deformedSusceptibility G hloc hqt d hd a hP p hp0 hp k t ht Set.univ (root i)).const_mul (weight i))

end AveragedDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PathAverage
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem rawPathAverage_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (f g : RawCorridor G k → ℝ) (hfg : ∀ w, f w ≤ g w) :
    rawPathAverage G P k root weight f ≤ rawPathAverage G P k root weight g := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  unfold rawPathAverage
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) k (root i))
  simp only [tsum_fintype]
  exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hfg _) (w.2.mass_nonneg P hP))

theorem rawPathAverage_const_mul (G : BondGraph V E) (P : V → V → ℝ) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (c : ℝ) (f : RawCorridor G k → ℝ) :
    rawPathAverage G P k root weight (fun w => c*f w) = c*rawPathAverage G P k root weight f := by
  unfold rawPathAverage
  simp only [←mul_left_comm c,tsum_mul_left,Finset.mul_sum]

end PathAverage
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeformedRowComparison
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

 

theorem exists_uniform_deformed_row_comparison (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C cf : ℝ, 0 < C ∧ 0 < cf ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G → ∀ (k : ℕ), 3 ≤ k → ∀ (t : ℝ),
      0 ≤ t → t*Real.exp (C*(k:ℝ)) ≤ 1 → ∀ x,
      cf*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x := by
  obtain ⟨C,hC,hmove⟩ := exists_uniform_deformed_endpoint_comparison G hloc hqt d hd a hP hpcrit hpcrit₁
  have hex (ij : ι × ι) : ∃ l : List E, Along G (root ij.1) l (root ij.2) := by
    obtain ⟨l,hl,_,_⟩ := conn_exists_bond_trail G (conn_univ_of_connected G hconn (root ij.1) (root ij.2))
    exact ⟨l,hl⟩
  choose path hpath using hex
  let N := ∑ ij : ι × ι, (path ij).length
  have hlen (i j : ι) : (path (i,j)).length ≤ N :=
    Finset.single_le_sum (f := fun ij : ι × ι => (path ij).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i,j))
  refine ⟨C,Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N,hC,mul_pos (Real.exp_pos _) (pow_pos (half_pos hpcrit) N),?_⟩
  intro p hpnear hp k hk t ht htc x
  obtain ⟨j,g,b,hgb,hgx⟩ := hcover x
  have hb (i : ι) : (Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N)*
      deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root i) ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root j) := by
    have hh := hmove p hpnear hp k hk t ht Set.univ (root j) (root i) (path (j,i))
      (Set.mem_univ _) (hpath (j,i)) (fun _ _ _ _ => Set.mem_univ _)
    have hpow : ((pc G:ℝ)/2)^N ≤ (p:ℝ)^(path (j,i)).length :=
      (pow_le_pow_left₀ (half_pos hpcrit).le hpnear N).trans
        (pow_le_pow_of_le_one p.2.1 p.2.2 (hlen j i))
    have he : Real.exp (-(N:ℝ)) ≤ Real.exp (-t*((path (j,i)).length*Real.exp (C*(k:ℝ)))) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right htc (Nat.cast_nonneg (path (j,i)).length : (0:ℝ) ≤ _)
      have hn : ((path (j,i)).length:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr (hlen j i)
      nlinarith
    exact (mul_le_mul_of_nonneg_right (mul_le_mul he hpow (pow_nonneg (half_pos hpcrit).le _) (Real.exp_pos _).le)
      (deformedSusceptibility_nonneg G _ p k t Set.univ (root i))).trans hh
  rw [←hgx,deformedSusceptibility_aut G hgb _ (walkKernel_covariant G hloc a hgb)]
  simp only [Set.preimage_univ]
  calc
    _ = ∑ i, weight i*((Real.exp (-(N:ℝ))*((pc G:ℝ)/2)^N)*
        deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root i)) := by
      simp only [averagedDeformedSusceptibility,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ ∑ i, weight i*deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root j) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = _ := by rw [←Finset.sum_mul,hw1,one_mul]

end DeformedRowComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredSegments
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]


theorem segmentAnchors_nonempty_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    (segmentAnchors G hloc γ n hdiam i x).Nonempty ↔ x ∈ vertexOrbit G (γ i) := by
  constructor
  · rintro ⟨s,hs⟩
    obtain ⟨⟨a,b,h,rfl⟩,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
    exact ⟨a,b,h,hx⟩
  · rintro ⟨a,b,h,hx⟩
    exact ⟨a ∘ γ,(mem_segmentAnchors G hloc γ n hdiam i x _).mpr ⟨⟨a,b,h,rfl⟩,hx⟩⟩

end AnchoredSegments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionKernels
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem segmentAnchors_map (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    segmentAnchors G hloc γ n hdiam i (a x) =
      (segmentAnchors G hloc γ n hdiam i x).map (segmentAut a).toEmbedding := by
  ext s
  rw [Finset.mem_map,mem_segmentAnchors]
  constructor
  · rintro ⟨hs,hx⟩
    refine ⟨a.symm ∘ s,(mem_segmentAnchors G hloc γ n hdiam i x _).mpr ⟨?_,?_⟩,?_⟩
    · exact (segmentOrbit_aut_iff G γ s (isAut_symm G h)).mpr hs
    · simp only [Function.comp_apply,hx,Equiv.symm_apply_apply]
    · funext j; exact a.apply_symm_apply (s j)
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨ht,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x t).mp ht
    exact ⟨(segmentOrbit_aut_iff G γ t h).mpr ht,congrArg a hx⟩

theorem segmentAnchors_card_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    (segmentAnchors G hloc γ n hdiam i (a x)).card = (segmentAnchors G hloc γ n hdiam i x).card := by
  rw [segmentAnchors_map G hloc γ n hdiam i x h,Finset.card_map]



theorem anchoredPositionKernel_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V) :
    0 ≤ anchoredPositionKernel G hloc γ n hdiam i j x y := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs <;> positivity

theorem anchoredPositionKernel_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    anchoredPositionKernel G hloc γ n hdiam i j (a x) (a y) =
      anchoredPositionKernel G hloc γ n hdiam i j x y := by
  simp only [anchoredPositionKernel,segmentAnchors_map G hloc γ n hdiam i x h,
    Finset.card_map,Finset.sum_map,Equiv.toEmbedding_apply,
    segmentAut,Equiv.coe_fn_mk,Function.comp_apply,Equiv.apply_eq_iff_eq]

end AnchoredPositionKernels
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionRows
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem anchoredPositionKernel_hasSum (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x : V) :
    HasSum (anchoredPositionKernel G hloc γ n hdiam i j x)
      (if x ∈ vertexOrbit G (γ i) then (1:ℝ) else 0) := by
  have hh := hasSum_sum (s := segmentAnchors G hloc γ n hdiam i x)
    (fun s _ => hasSum_ite_eq (s j) (((segmentAnchors G hloc γ n hdiam i x).card:ℝ)⁻¹))
  have he : (∑ s ∈ segmentAnchors G hloc γ n hdiam i x,
      ((segmentAnchors G hloc γ n hdiam i x).card:ℝ)⁻¹) =
      if x ∈ vertexOrbit G (γ i) then (1:ℝ) else 0 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    by_cases hx : x ∈ vertexOrbit G (γ i)
    · have hn := Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i x).mpr hx)
      rw [ite_eq_left hx,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
    · have he : segmentAnchors G hloc γ n hdiam i x = ∅ := Finset.not_nonempty_iff_eq_empty.mp
        (fun h => hx ((segmentAnchors_nonempty_iff G hloc γ n hdiam i x).mp h))
      simp only [he,Finset.card_empty,Nat.cast_zero,zero_mul,ite_eq_right hx]
  rw [he] at hh
  exact hh

end AnchoredPositionRows
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionColumns
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem anchoredPositionKernel_columnSummable (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (y : V) :
    Summable (fun x => anchoredPositionKernel G hloc γ n hdiam i j x y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
  intro x hx
  simp only [Set.Finite.mem_toFinset] at hx
  apply Finset.sum_eq_zero
  intro s hs
  apply ite_eq_right
  intro hy
  obtain ⟨⟨a,b,hab,rfl⟩,he⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
  change a (γ i) = x at he
  change y = a (γ j) at hy
  exact hx (by simpa only [he,←hy] using mem_reachBall_aut G hab (hdiam j i))

end AnchoredPositionColumns
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
section AsymmetricSchur
open scoped ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_operator_of_unit_row_column_bound (U : V → V → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hU : ∀ x y, 0 ≤ U x y)
    (hrow : ∀ x (s : Finset V), ∑ y ∈ s, U x y ≤ 1)
    (hcol : ∀ y (s : Finset V), ∑ x ∈ s, U x y ≤ D) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ Real.sqrt D ∧
      ∀ x y, matrixCoeff A x y = (U x y : ℂ) := by
  have hentry (x y : V) : U x y ≤ 1 := by simpa only [Finset.sum_singleton] using hrow x {y}
  have hcm (y : V) : Memℓp (fun x => (U x y : ℂ)) 2 := by
    apply (memℓp_gen_iff'' (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    refine ⟨D,hD,fun s => ?_⟩
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact (Finset.sum_le_sum (fun x _ => by nlinarith [hentry x y,hU x y])).trans (hcol y s)
  let col (y : V) : Hilbert V := ⟨fun x => (U x y : ℂ),hcm y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hn (f : V →₀ ℂ) : ‖L f‖ ≤ Real.sqrt D * ‖finiteEmbedding f‖ := by
    apply lp.norm_le_of_forall_sum_le (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    intro s
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    have hpoint (x : V) : ‖L f x‖^2 ≤ ∑ y ∈ f.support, ‖f y‖^2 * U x y := by
      have hn0 : 0 ≤ ∑ y ∈ f.support, ‖f y‖*U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (hU x y))
      have hn1 : ‖L f x‖ ≤ ∑ y ∈ f.support, ‖f y‖*U x y := by
        simp only [L,Finsupp.linearCombination_apply,Finsupp.sum,lp.coeFn_sum,
          Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro y _
        simp [col,abs_of_nonneg (hU x y)]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul f.support
        (f := fun y => U x y) (g := fun y => ‖f y‖^2*U x y)
        (r := fun y => ‖f y‖*U x y)
        (fun y _ => hU x y)
        (fun y _ => mul_nonneg (sq_nonneg _) (hU x y)) (fun y _ => by nlinarith)
      have hn2 : 0 ≤ ∑ y ∈ f.support, ‖f y‖^2*U x y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (sq_nonneg _) (hU x y))
      have hr := mul_le_mul_of_nonneg_right (hrow x f.support) hn2
      rw [one_mul] at hr
      exact (sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn1).trans (hcs.trans hr)
    calc
      ∑ x ∈ s, ‖L f x‖^2 ≤ ∑ x ∈ s, ∑ y ∈ f.support, ‖f y‖^2*U x y :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = ∑ y ∈ f.support, ‖f y‖^2*∑ x ∈ s, U x y := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ f.support, ‖f y‖^2*D :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hcol y s) (sq_nonneg _))
      _ = D*∑ y ∈ f.support, ‖finiteEmbedding f y‖^2 := by
        simp only [finiteEmbedding_apply]
        rw [←Finset.sum_mul,mul_comm]
      _ ≤ D*‖finiteEmbedding f‖^2 := by
        apply mul_le_mul_of_nonneg_left _ hD
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) (finiteEmbedding f) f.support
      _ = (Real.sqrt D*‖finiteEmbedding f‖)^2 := by rw [mul_pow,Real.sq_sqrt hD]
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense (Real.sqrt_nonneg _) hn,?_⟩
  intro x y
  have he := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨Real.sqrt D,hn⟩
    (Finsupp.single y (1:ℂ))
  simp only [finiteEmbedding_single] at he
  change (L.extendOfNorm finiteEmbedding) (lp.single 2 y (1:ℂ)) x = _
  rw [he]
  simp [L,col]

end AsymmetricSchur
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]



theorem exists_anchoredPositionOperator_uniform (G : BondGraph V E) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ a ∈ Γ, a (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) :
    ∃ H : Hilbert V →L[ℂ] Hilbert V,
      (∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam i j x y : ℂ)) ∧
      ‖H‖ ≤ Real.sqrt c := by
  let U := anchoredPositionKernel G hloc γ n hdiam i j
  have hn : ∀ x y, 0 ≤ U x y := anchoredPositionKernel_nonneg G hloc γ n hdiam i j
  have hr : ∀ x, Summable (U x) := fun x => (anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).summable
  have hcol := anchoredPositionKernel_columnSummable G hloc γ n hdiam i j
  have hb (x : V) : (∑' y, U x y) ≤ 1 := by
    rw [(anchoredPositionKernel_hasSum G hloc γ n hdiam i j x).tsum_eq]
    split_ifs <;> norm_num
  have hi : ∀ a ∈ Γ, ∀ x y, U (a x) (a y) = U x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    exact anchoredPositionKernel_aut G hloc γ n hdiam i j x y hb
  have hbcol (y : V) : (∑' x, U x y) ≤ c := by
    simpa only [mul_one] using transported_column_le root weight Γ htr hcov hw hw1 c hc hmin U hn hi hr hcol 1 hb y
  obtain ⟨H,hHn,hH⟩ := exists_operator_of_unit_row_column_bound U c hc hn
    (fun x s => ((hr x).sum_le_tsum s (fun y _ => hn x y)).trans (hb x))
    (fun y s => ((hcol y).sum_le_tsum s (fun x _ => hn x y)).trans (hbcol y))
  exact ⟨H,hH,hHn⟩

end AnchoredPositionOperators
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
section RawReversal
namespace HoldingWalk
variable {H : SimpleGraph V}


theorem mass_snocHold (P : V → V → ℝ) {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.mass P = w.mass P * P y y := by
  induction w with
  | nil => simp only [snocHold,mass,mul_one,one_mul]
  | hold w ih => simp only [snocHold,mass,ih,mul_assoc]
  | step h w ih => simp only [snocHold,mass,ih,mul_assoc]

theorem mass_snocStep (P : V → V → ℝ) {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).mass P = w.mass P * P y z := by
  induction w with
  | nil => simp only [snocStep,mass,mul_one,one_mul]
  | hold w ih => simp only [snocStep,mass,ih,mul_assoc]
  | step h' w ih => simp only [snocStep,mass,ih,mul_assoc]

theorem mass_reverse (P : V → V → ℝ) (hP : ∀ x y, P x y = P y x)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.reverse.mass P = w.mass P := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,mass_snocHold,mass,ih,mul_comm]
  | step h w ih => simp only [reverse,mass_snocStep,mass,ih,hP,mul_comm]

theorem vertices_snocHold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.vertices = w.vertices ++ [y] := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocHold,vertices,ih,List.cons_append]
  | step h w ih => simp only [snocHold,vertices,ih,List.cons_append]

theorem vertices_snocStep {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).vertices = w.vertices ++ [z] := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocStep,vertices,ih,List.cons_append]
  | step h' w ih => simp only [snocStep,vertices,ih,List.cons_append]

theorem vertices_reverse {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.reverse.vertices = w.vertices.reverse := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,vertices_snocHold,vertices,ih,List.reverse_cons]
  | step h w ih => simp only [reverse,vertices_snocStep,vertices,ih,List.reverse_cons]

end HoldingWalk
end RawReversal
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_Labels
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledEscapeExperiment



namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem mass_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (ξ : EscapeLabel G γ ep neg L m) : 0 ≤ ξ.mass P :=
  mul_nonneg (mul_nonneg (ξ.middle.mass_nonneg P hP) (ξ.leftTail.2.mass_nonneg P hP))
    (ξ.rightTail.2.mass_nonneg P hP)

theorem mass_reverse (P : V → V → ℝ) (hP : ∀ x y, P x y = P y x)
    (ξ : EscapeLabel G γ ep neg L m) : ξ.reverse.mass P = ξ.mass P := by
  simp only [mass,reverse,HoldingWalk.mass_reverse P hP]
  ring



end EscapeLabel
end LabeledEscapeExperiment
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FiniteRootedLabels
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

instance finite_rootedLabelCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    Finite (RootedLabelCode G hloc γ n hdiam center ep neg L m x) := by
  let (z : V) := finite_openSimpleGraph_neighbors G hloc z
  unfold RootedLabelCode
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem finite_rootedEscapeLabels (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    Finite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} :=
  Finite.of_equiv _ (rootedLabelEquiv G hloc γ n hdiam center ep neg L m x).symm

end FiniteRootedLabels
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem segmentAnchors_card_on_orbit (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V)
    (hx : x ∈ vertexOrbit G (γ i)) :
    (segmentAnchors G hloc γ n hdiam i x).card = (segmentAnchors G hloc γ n hdiam i (γ i)).card := by
  obtain ⟨a,b,h,rfl⟩ := hx
  exact segmentAnchors_card_aut G hloc γ n hdiam i (γ i) h

theorem segmentAnchors_card_eq_indicator (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    ((segmentAnchors G hloc γ n hdiam i x).card : ℝ) =
      if x ∈ vertexOrbit G (γ i) then (segmentAnchors G hloc γ n hdiam i (γ i)).card else 0 := by
  split_ifs with hx
  · exact congrArg Nat.cast (segmentAnchors_card_on_orbit G hloc γ n hdiam i x hx)
  · have hh := (segmentAnchors_nonempty_iff G hloc γ n hdiam i x).not.mpr hx
    rw [Finset.not_nonempty_iff_eq_empty.mp hh]
    rfl

theorem labelFromCode_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (P : V → V → ℝ)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.mass P =
      c.2.1.2.mass P * c.2.2.2.1.2.mass P * c.2.2.2.2.2.mass P := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem rooted_label_mass_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      ξ.1.mass (walkKernel G hloc a)) =
    ∑ s ∈ segmentAnchors G hloc γ n hdiam center x,
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
        segmentReturnMass G hloc a γ ep L (s ep) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  change (∑' s : (segmentAnchors G hloc γ n hdiam center x), _) = _
  rw [tsum_fintype]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro s _
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  have he (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep)) :
      (∑' h : (segmentAnchors G hloc γ n hdiam ep mid.1),
        ∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
            tails.2.2.mass (walkKernel G hloc a)) =
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
        (if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0) := by
    have ht (h : (segmentAnchors G hloc γ n hdiam ep mid.1)) :
        (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
            tails.2.2.mass (walkKernel G hloc a)) = mid.2.mass (walkKernel G hloc a) := by
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
      simp only [tsum_mul_left,rawFrom_probability_sum G hloc a,mul_one]
    simp only [ht,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    rw [segmentAnchors_card_eq_indicator G hloc γ n hdiam ep mid.1]
    split_ifs <;> ring
  calc
    _ = ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
          (if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0) := by
      apply tsum_congr
      intro mid
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      exact he mid
    _ = _ := tsum_mul_left

end LabeledMass
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledNormalization
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

omit [Fintype I] in
theorem segmentReturnMass_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) :
    segmentReturnMass G hloc a γ ep L x =
      ∑' y, if y ∈ vertexOrbit G (γ ep) then (matrixCoeff (P^L) x y).re else 0 := by
  have hh := raw_integral_operator G hloc a P hpos hP L x
    (fun y => if y ∈ vertexOrbit G (γ ep) then 1 else 0)
  simpa only [RawFrom.integral,mul_ite,mul_one,mul_zero,segmentReturnMass] using hh

omit [Fintype I] in
theorem segmentReturnMass_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) :
    segmentReturnMass G hloc a γ ep L (g x) = segmentReturnMass G hloc a γ ep L x := by
  rw [segmentReturnMass_operator G hloc a γ ep L (g x) P hpos hP,
    segmentReturnMass_operator G hloc a γ ep L x P hpos hP,←g.tsum_eq]
  apply tsum_congr
  intro y
  rw [mem_vertexOrbit_aut_iff G (γ ep) hg]
  have hh := walkPower_invariant G hloc a P hP L g ⟨b,hg⟩ x y
  rw [hh]

omit [Fintype I] in
theorem segmentReturnMass_on_orbit (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V)
    (hx : x ∈ vertexOrbit G (γ ep))
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) :
    segmentReturnMass G hloc a γ ep L x = segmentReturnMass G hloc a γ ep L (γ ep) := by
  obtain ⟨g,b,hg,rfl⟩ := hx
  exact segmentReturnMass_aut G hloc a γ ep L (γ ep) P hpos hP hg



theorem rooted_label_probability_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hq : segmentReturnMass G hloc a γ ep L (γ ep) ≠ 0) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) = 1 := by
  have hN (i : I) : ((segmentAnchors G hloc γ n hdiam i (γ i)).card : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i (γ i)).mpr
      (by exact ⟨Equiv.refl V,Equiv.refl E,(fun e => by simp),rfl⟩))
  simp only [escapeLabelProbability,tsum_div_const]
  rw [rooted_label_mass_sum G hloc a γ n hdiam center ep neg L m x]
  have he (s : I → V) (hs : s ∈ segmentAnchors G hloc γ n hdiam center x) :
      segmentReturnMass G hloc a γ ep L (s ep) = segmentReturnMass G hloc a γ ep L (γ ep) := by
    obtain ⟨⟨g,b,hg,rfl⟩,_⟩ := (mem_segmentAnchors G hloc γ n hdiam center x s).mp hs
    exact segmentReturnMass_aut G hloc a γ ep L (γ ep) P hpos hP hg
  rw [Finset.sum_congr rfl (fun s hs => congrArg (fun q => _ * q) (he s hs))]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx,←mul_assoc]
  exact div_self (mul_ne_zero (mul_ne_zero (hN center) (hN ep)) hq)

theorem escapeLabelProbability_reverse (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) :
    escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.reverse =
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ := by
  simp only [escapeLabelProbability,EscapeLabel.mass_reverse _ (walkKernel_symmetric G hloc a)]

end LabeledNormalization
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}

namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem mass_autMap (hloc : LocallyFinite G) (a₀ : ℝ)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    (autMap hab ξ).mass (walkKernel G hloc a₀) = ξ.mass (walkKernel G hloc a₀) := by
  change (ξ.middle.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) *
    (ξ.leftTail.2.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) *
    (ξ.rightTail.2.map (autSimpleGraph G hab).toHom).mass (walkKernel G hloc a₀) = _
  simp only [HoldingWalk.mass_map (autSimpleGraph G hab).toHom _ _ (walkKernel_covariant G hloc a₀ hab)]
  rfl

end EscapeLabel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LazyOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem positive_lazy_power_step (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (k : ℕ) (x y : V) :
    (1/2) * (matrixCoeff (P^k) x y).re ≤ (matrixCoeff (P^(k+1)) x y).re := by
  have hs := hpos.mul_hasSum (P^k) x y
  have hh := hs.summable.sum_le_tsum ({x} : Finset V)
    (fun z _ => mul_nonneg (hpos x z).2 ((hpos.pow k) z y).2)
  simp only [Finset.sum_singleton,hs.tsum_eq,←pow_succ'] at hh
  exact (mul_le_mul_of_nonneg_right (hdiag x) ((hpos.pow k) x y).2).trans hh

 

theorem walkPower_orbit_return_lower (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (L : ℕ) :
    (1/2) * (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' y, if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^L) (root i₀) y).re else 0 := by
  have hsum (k : ℕ) : Summable (fun y =>
      if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^k) (root i₀) y).re else 0) := by
    simpa only [mul_ite,mul_one,mul_zero] using finiteKernel_summable_mul
      (fun x y => (matrixCoeff (P^k) x y).re) (walkPower_finite_support G hloc a P hpos hP k)
      (root i₀) (fun y => if y ∈ vertexOrbit G (root i₀) then 1 else 0)
  obtain ⟨k,hk | hk⟩ := Nat.even_or_odd' L
  · rw [hk]
    have hh := walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k
    have hn : 0 ≤ ∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0 :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hw i | rfl)
    linarith
  · rw [hk]
    have hh := mul_le_mul_of_nonneg_left
      (walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k)
      (show (0:ℝ) ≤ 1/2 by norm_num)
    apply hh.trans
    rw [←tsum_mul_left]
    apply ((hsum (2*k)).mul_left (1/2)).tsum_le_tsum _ (hsum (2*k+1))
    intro y
    split_ifs
    · exact positive_lazy_power_step P hpos hdiag (2*k) (root i₀) y
    · simp only [mul_zero,le_refl]

end LazyOrbitReturn
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section UniformLabeledLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

omit [Fintype I] in
 

theorem segmentReturnMass_uniform_lower (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (γ : I → V) (ep : I) (L : ℕ) :
    1/(2*c) ≤ segmentReturnMass G hloc a γ ep L (γ ep) := by
  obtain ⟨i,g,hg,hx⟩ := hcov (γ ep)
  obtain ⟨b,hb⟩ := hΓ hg
  have hO := vertexOrbit_eq_of_mem G (root i) (γ ep) ⟨g,b,hb,hx⟩
  rw [←hx,segmentReturnMass_aut G hloc a γ ep L (root i) P hpos hP hb]
  rw [segmentReturnMass_operator G hloc a γ ep L (root i) P hpos hP]
  rw [hO]
  have hh := walkPower_orbit_return_lower G hloc a root weight Γ hΓ htr
    (fun i => (hw i).le) hw1 i (hw i) P hpos hsym hP hdiag L
  have hi : weight i ≤ ∑ r, if root r ∈ vertexOrbit G (root i) then weight r else 0 := by
    have hx' : root i ∈ vertexOrbit G (root i) := ⟨Equiv.refl _,Equiv.refl _,isAut_refl G,rfl⟩
    simpa only [ite_eq_left hx'] using Finset.single_le_sum
      (f := fun r => if root r ∈ vertexOrbit G (root i) then weight r else 0)
      (fun r _ => by split_ifs <;> first | exact (hw r).le | rfl) (Finset.mem_univ i)
  apply le_trans _ hh
  have hct : 0 < 2*c := mul_pos (by norm_num) hc
  apply (div_le_iff₀ hct).mpr
  have hh' := mul_le_mul_of_nonneg_left hi hc.le
  nlinarith [hmin i]

 

theorem rooted_label_probability_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    HasSum (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) 1 := by
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hp : 0 < segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).trans_le hq
  have hs : Summable (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  rw [←rooted_label_probability_sum G hloc a γ n hdiam center ep neg L m x hx P hpos hP (ne_of_gt hp)]
  exact hs.hasSum

end UniformLabeledLaw
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem escapeLabelTransport_reverse (center : I) (B : EscapeLabel G γ ep neg L m → ℝ) (x y : V) :
    escapeLabelTransport center B x y =
      escapeLabelTransport center (fun ξ => B ξ.reverse) y x := by
  unfold escapeLabelTransport
  exact (EscapeLabel.reverseRootedEquiv center y x).tsum_eq _ |>.symm

theorem escapeLabelTransport_aut (center : I) (B : EscapeLabel G γ ep neg L m → ℝ)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (hB : ∀ ξ, B (EscapeLabel.autMap hab ξ) = B ξ) (x y : V) :
    escapeLabelTransport center B (a x) (a y) = escapeLabelTransport center B x y := by
  unfold escapeLabelTransport
  rw [←(labelAutPairEquiv hab center x y).tsum_eq]
  exact tsum_congr (fun ξ => hB ξ.1)

variable [Fintype I]

theorem finite_pair_label_sigma (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I) (x : V) :
    Finite (Σ y : V, {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}) := by
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  exact Finite.of_equiv _ (labelEndpointEquiv center x).symm

theorem escapeLabelTransport_row_sum (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (x : V) :
    (∑' y, escapeLabelTransport center B x y) =
      ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1 := by
  let := finite_pair_label_sigma hloc n hdiam center (ep := ep) (neg := neg) (L := L) (m := m) x
  have hs : Summable (fun ξ : Σ y : V, {ξ : EscapeLabel G γ ep neg L m //
      ξ.first center = x ∧ ξ.last center = y} => B ξ.2.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  unfold escapeLabelTransport
  rw [←hs.tsum_sigma]
  exact (labelEndpointEquiv (G := G) (γ := γ) (ep := ep) (neg := neg) (L := L) (m := m) center x).tsum_eq (fun ξ => B ξ.1)

theorem escapeLabelTransport_rowSummable (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (x : V) :
    Summable (escapeLabelTransport center B x) := by
  let := finite_pair_label_sigma hloc n hdiam center (ep := ep) (neg := neg) (L := L) (m := m) x
  have hs : Summable (fun ξ : Σ y : V, {ξ : EscapeLabel G γ ep neg L m //
      ξ.first center = x ∧ ξ.last center = y} => B ξ.2.1) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  exact hs.sigma

theorem escapeLabelTransport_columnSummable (hloc : LocallyFinite G) (n : ℕ)
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (B : EscapeLabel G γ ep neg L m → ℝ) (y : V) :
    Summable (fun x => escapeLabelTransport center B x y) := by
  simp only [escapeLabelTransport_reverse center B]
  exact escapeLabelTransport_rowSummable hloc n hdiam center (fun ξ => B ξ.reverse) y

end LabeledTransport
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledReRooting
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

theorem EscapeLabel.first_orbit (ξ : EscapeLabel G γ ep neg L m) (i : I) :
    ξ.first i ∈ vertexOrbit G (γ i) := by
  obtain ⟨a,b,h,he⟩ := ξ.first_mem
  exact ⟨a,b,h,(congrFun he i).symm⟩

theorem EscapeLabel.last_orbit (ξ : EscapeLabel G γ ep neg L m) (i : I) :
    ξ.last i ∈ vertexOrbit G (γ i) := by
  obtain ⟨a,b,h,he⟩ := ξ.last_mem
  exact ⟨a,b,h,(congrFun he i).symm⟩

theorem escapeLabelTransport_zero (center : I) (B : EscapeLabel G γ ep neg L m → ℝ)
    (x y : V) (hxy : x ∉ vertexOrbit G (γ center) ∨ y ∉ vertexOrbit G (γ center)) :
    escapeLabelTransport center B x y = 0 := by
  let : IsEmpty {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} :=
    ⟨fun ξ => by
      rcases hxy with hx | hy
      · exact hx (ξ.2.1 ▸ ξ.1.first_orbit center)
      · exact hy (ξ.2.2 ▸ ξ.1.last_orbit center)⟩
  exact tsum_empty

variable [Fintype I]

 

theorem rooted_label_weight_reversal (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center : I)
    (hθ : 0 < ∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)
    (B : EscapeLabel G γ ep neg L m → ℝ)
    (hB : ∀ (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) ξ, B (EscapeLabel.autMap hab ξ) = B ξ)
    (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1) =
      ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}, B ξ.1.reverse := by
  let M := escapeLabelTransport center B
  have hM (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (u v : V) : M (a u) (a v) = M u v :=
    escapeLabelTransport_aut center B hab (hB a b hab) u v
  have hr (u : V) : (∑' v, M u v) = if u ∈ vertexOrbit G (γ center) then ∑' v, M (γ center) v else 0 := by
    split_ifs with hu
    · obtain ⟨a,b,hab,rfl⟩ := hu
      rw [←a.tsum_eq]
      exact tsum_congr (fun v => hM a b hab (γ center) v)
    · calc
        _ = ∑' _ : V, (0:ℝ) := tsum_congr (fun v => escapeLabelTransport_zero center B u v (Or.inl hu))
        _ = 0 := tsum_zero
  have hc (v : V) : (∑' u, M u v) = if v ∈ vertexOrbit G (γ center) then ∑' u, M u (γ center) else 0 := by
    split_ifs with hv
    · obtain ⟨a,b,hab,rfl⟩ := hv
      rw [←a.tsum_eq]
      exact tsum_congr (fun u => hM a b hab u (γ center))
    · calc
        _ = ∑' _ : V, (0:ℝ) := tsum_congr (fun u => escapeLabelTransport_zero center B u v (Or.inr hv))
        _ = 0 := tsum_zero
  have ht := htr.real root weight Γ M
    (fun a ha u v => by obtain ⟨b,hb⟩ := hΓ ha; exact hM a b hb u v)
    (escapeLabelTransport_rowSummable hloc n hdiam center B)
    (escapeLabelTransport_columnSummable hloc n hdiam center B)
  have hfactor (f : V → ℝ) (q : ℝ) (he : ∀ u, f u = if u ∈ vertexOrbit G (γ center) then q else 0) :
      (∑ i, weight i*f (root i)) = (∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)*q := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [he]
    split_ifs <;> simp only [mul_zero,zero_mul]
  rw [hfactor _ _ hr,hfactor _ _ hc] at ht
  have hrc := (mul_left_cancel₀ (ne_of_gt hθ)) ht
  have hxe : (∑' v, M x v) = ∑' u, M u x := by
    rw [hr x,hc x,ite_eq_left hx,ite_eq_left hx]
    exact hrc
  calc
    _ = ∑' v, M x v := (escapeLabelTransport_row_sum hloc n hdiam center B x).symm
    _ = ∑' u, M u x := hxe
    _ = ∑' u, escapeLabelTransport center (fun ξ => B ξ.reverse) x u :=
      tsum_congr (fun u => escapeLabelTransport_reverse center B u x)
    _ = _ := escapeLabelTransport_row_sum hloc n hdiam center (fun ξ => B ξ.reverse) x

end LabeledReRooting
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section ExactLabeledReversal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem escapeLabelProbability_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    (a₀ : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m (EscapeLabel.autMap hab ξ) =
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ := by
  simp only [escapeLabelProbability,EscapeLabel.mass_autMap]

 

theorem rooted_escape_label_reversal (G : BondGraph V E) (hloc : LocallyFinite G) (a₀ : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I) (L m : ℕ)
    (hθ : 0 < ∑ i, if root i ∈ vertexOrbit G (γ center) then weight i else 0)
    (F : EscapeLabel G γ ep neg L m → ℝ)
    (hF : ∀ (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) ξ, F (EscapeLabel.autMap hab ξ) = F ξ)
    (x : V) (hx : x ∈ vertexOrbit G (γ center)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ.1 * F ξ.1) =
    ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ.1 * F ξ.1.reverse := by
  have hh := rooted_label_weight_reversal hloc root weight Γ hΓ htr n hdiam center hθ
    (fun ξ => escapeLabelProbability G hloc a₀ γ n hdiam center ep neg L m ξ * F ξ)
    (fun a b hab ξ => by rw [escapeLabelProbability_aut G hloc a₀ γ n hdiam center ep neg L m hab,hF a b hab]) x hx
  simpa only [escapeLabelProbability_reverse] using hh

theorem escapeLabelProbability_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) :
    0 ≤ escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ := by
  have hq : 0 ≤ segmentReturnMass G hloc a γ ep L (γ ep) := by
    apply tsum_nonneg
    intro mid
    split_ifs
    · exact mid.2.mass_nonneg _ hP
    · rfl
  exact div_nonneg (ξ.mass_nonneg _ hP) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hq)

end ExactLabeledReversal
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LongGeodesics
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_geodesic_length (G : BondGraph V E) [Infinite V]
    (hloc : LocallyFinite G) (hconn : Connected G) (x : V) (N : ℕ) :
    ∃ y : V, ∃ q : (openSimpleGraph G Set.univ).Walk x y,
      q.length = N ∧ q.length = (openSimpleGraph G Set.univ).dist x y := by
  obtain ⟨z,hz⟩ := (finite_reachBall hloc x N).exists_notMem
  have hc := (conn_iff_reachable G Set.univ x z).mp (conn_univ_of_connected G hconn x z)
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist
  have hN : N < q.length := by
    by_contra hh
    have hm := walk_mem_reachBall G Set.univ q 0 (show x ∈ reachBall G x 0 from rfl)
    have hm' : z ∈ reachBall G x q.length := by simpa only [Nat.zero_add] using hm
    exact hz (reachBall_mono_local G x (Nat.le_of_not_gt hh) hm')
  refine ⟨q.getVert N,q.take N,?_,?_⟩
  · simp only [SimpleGraph.Walk.take_length,inf_eq_left.mpr hN.le]
  · exact SimpleGraph.length_eq_dist_of_subwalk hq (q.isSubwalk_take N)

 

theorem geodesic_getVert_dist (H : SimpleGraph V) {x y : V} (q : H.Walk x y)
    (hq : q.length = H.dist x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ q.length) :
    H.dist (q.getVert i) (q.getVert j) = j-i := by
  have hs := SimpleGraph.length_eq_dist_of_subwalk hq
    (((q.drop i).isSubwalk_take (j-i)).trans (q.isSubwalk_drop i))
  have he : (q.drop i).getVert (j-i) = q.getVert j := by
    rw [SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hij]
  rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,he,
    min_eq_left (Nat.sub_le_sub_right hj i)] at hs
  exact hs.symm

end LongGeodesics
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
namespace HoldingWalk
variable {H : SimpleGraph V}



theorem mass_append (P : V → V → ℝ) {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) :
    (w.append v).mass P = w.mass P*v.mass P := by
  induction w with
  | nil => simp only [append,mass,one_mul]
  | hold w ih => simp only [append,mass,ih,mul_assoc]
  | step h w ih => simp only [append,mass,ih,mul_assoc]

end HoldingWalk
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GeodesicSegments
attribute [local instance] Classical.propDecidable Classical.decEq



theorem geodesicSegment_adj (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N)
    (i : ℕ) (hi : i < N) :
    (openSimpleGraph G Set.univ).Adj
      (geodesicSegment G q N ⟨i,by omega⟩) (geodesicSegment G q N ⟨i+1,by omega⟩) := by
  change (openSimpleGraph G Set.univ).Adj (q.getVert i) (q.getVert (i+1))
  exact q.adj_getVert_succ (by omega)

theorem geodesicSegment_injective (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N)
    (hq : q.length = (openSimpleGraph G Set.univ).dist x y) :
    Function.Injective (geodesicSegment G q N) := by
  intro i j hh
  apply Fin.ext
  exact (q.isPath_of_length_eq_dist hq).getVert_injOn
    (by change i.val ≤ q.length; omega) (by change j.val ≤ q.length; omega) hh

theorem geodesicSegment_diameter (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) (hN : q.length = N) :
    ∀ i j, geodesicSegment G q N j ∈ reachBall G (geodesicSegment G q N i) N := by
  intro i j
  have hc : (openSimpleGraph G Set.univ).Reachable (q.getVert i) (q.getVert j) :=
    (q.take i).reachable.symm.trans (q.take j).reachable
  obtain ⟨r,hr⟩ := hc.exists_walk_length_eq_dist
  have hd : (openSimpleGraph G Set.univ).dist (q.getVert i) (q.getVert j) ≤ N := by
    rcases le_total i.val j.val with hij | hji
    · have hle := SimpleGraph.dist_le ((q.drop i).take (j-i))
      rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
        SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hij] at hle
      exact hle.trans (by omega)
    · have hle := SimpleGraph.dist_le ((q.drop j).take (i-j))
      rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
        SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hji] at hle
      rw [SimpleGraph.dist_comm] at hle
      exact hle.trans (by omega)
  have hm := walk_mem_reachBall G Set.univ r 0 (show q.getVert i ∈ reachBall G (q.getVert i) 0 from rfl)
  apply reachBall_mono_local G (q.getVert i) (a := r.length) (by omega)
  simpa only [Nat.zero_add, geodesicSegment] using hm

theorem walkKernel_step (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {x y : V} (h : (openSimpleGraph G Set.univ).Adj x y) : walkKernel G hloc a x y = a := by
  have hh := (openSimpleGraph_univ_adj G x y).mp h
  simp only [walkKernel,ite_eq_right hh.1,ite_eq_left hh.2,zero_add]

end GeodesicSegments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualTailPotentials
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_tail_twoPoint_expectation (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x b : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * twoPoint G p w.1 b) =
      (matrixCoeff (P^m*A) x b).re := by
  have he : (fun y => twoPoint G p y b) = (fun y => (matrixCoeff A y b).re) := by
    funext y
    rw [matrixCoeff,hA y b,Complex.ofReal_re]
  change RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) m x (twoPoint G p · b) = _
  rw [he,raw_integral_operator G hloc a P hpos hP]
  exact ((hpos.pow m).mul_hasSum A x b).tsum_eq

 

theorem raw_tail_potential_bound [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x : V) (S : Finset V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * ∑ b ∈ S, twoPoint G p w.1 b) ≤
      (S.card:ℝ) * Real.sqrt c * ‖P‖^m := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  have hPinv : KernelInvariant (vertexAut G) P := by
    intro e he x y
    obtain ⟨f,hf⟩ := he
    rw [hP,hP,walkKernel_covariant G hloc a hf]
  calc
    _ = ∑ b ∈ S, (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
        w.2.mass (walkKernel G hloc a) * twoPoint G p w.1 b) := by
      simp only [tsum_fintype,Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ b ∈ S, (matrixCoeff (P^m*A) x b).re := by
      apply Finset.sum_congr rfl
      intro b _
      exact raw_tail_twoPoint_expectation G hloc a P A hpos hP p hA m x b
    _ ≤ ∑ _b ∈ S, Real.sqrt c * ‖P‖^m := by
      apply Finset.sum_le_sum
      intro b _
      exact (Complex.re_le_norm _).trans (twoPoint_operator_smoothing G p root weight htr hcov hw hsum c hc hmin A P hA hPinv m x b)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]

end ActualTailPotentials
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AuxiliaryTailMarkov
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_weighted_markov {α : Type*} [Fintype α] (μ F : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x) (t : ℝ) (ht : 0 < t) :
    (∑ x, if t < F x then μ x else 0) ≤ (∑ x, μ x*F x)/t := by
  apply (le_div_iff₀ ht).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · exact mul_le_mul_of_nonneg_left hx.le (hμ x)
  · exact (by simpa only [zero_mul] using mul_nonneg (hμ x) (hF x))

theorem raw_tail_potential_failure [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x : V) (S : Finset V)
    (t : ℝ) (ht : 0 < t) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if t < ∑ b ∈ S, twoPoint G p w.1 b then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((S.card:ℝ) * Real.sqrt c * ‖P‖^m)/t := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hM := finite_weighted_markov
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w => ∑ b ∈ S, twoPoint G p w.1 b)
    (fun w => w.2.mass_nonneg _ hK)
    (fun w => Finset.sum_nonneg (fun b _ => twoPoint_nonneg G p w.1 b)) t ht
  have hB := raw_tail_potential_bound G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m x S
  simp only [tsum_fintype] at hB ⊢
  exact hM.trans (div_le_div_of_nonneg_right hB ht.le)

 

theorem finite_product_failure_union {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (ν : β → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hμ1 : ∑ x, μ x = 1) (hν1 : ∑ y, ν y = 1) (B : α → Prop) (C : β → Prop) :
    (∑ z : α × β, if B z.1 ∨ C z.2 then μ z.1*ν z.2 else 0) ≤
      (∑ x, if B x then μ x else 0) + ∑ y, if C y then ν y else 0 := by
  calc
    _ ≤ ∑ z : α × β, ((if B z.1 then μ z.1 else 0)*ν z.2 + μ z.1*(if C z.2 then ν z.2 else 0)) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hB : B z.1 <;> by_cases hC : C z.2 <;>
        simp [hB,hC]
      exact mul_nonneg (hμ _) (hν _)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,hμ1,hν1,mul_one,one_mul]

end AuxiliaryTailMarkov
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentTailPotentialTests
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem two_raw_tail_potential_failure [Countable V] [Countable E] [Nonempty V]
    {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ e ∈ vertexAut G, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hA : HasKernel G p A) (m : ℕ) (x y : V) (S : Finset V)
    (t : ℝ) (ht : 0 < t) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) m y,
      if (t < ∑ b ∈ S, twoPoint G p w.1.1 b) ∨ (t < ∑ b ∈ S, twoPoint G p w.2.1 b)
      then w.1.2.mass (walkKernel G hloc a) * w.2.2.mass (walkKernel G hloc a) else 0) ≤
      2*((S.card:ℝ) * Real.sqrt c * ‖P‖^m)/t := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m y)
  have hK (u v : V) : 0 ≤ walkKernel G hloc a u v := by
    simpa only [hP,Complex.ofReal_re] using (hpos u v).2
  have hμ := rawFrom_probability_sum G hloc a m x
  have hν := rawFrom_probability_sum G hloc a m y
  simp only [tsum_fintype] at hμ hν
  have hU := finite_product_failure_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w : RawFrom (openSimpleGraph G Set.univ) m y => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK) (fun w => w.2.mass_nonneg _ hK) hμ hν
    (fun w => t < ∑ b ∈ S, twoPoint G p w.1 b)
    (fun w => t < ∑ b ∈ S, twoPoint G p w.1 b)
  have hx := raw_tail_potential_failure G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m x S t ht
  have hy := raw_tail_potential_failure G hloc a root weight htr hcov hw hsum c hc hmin P A hpos hP p hA m y S t ht
  simp only [tsum_fintype] at hx hy ⊢
  exact hU.trans ((add_le_add hx hy).trans_eq (by ring))

end IndependentTailPotentialTests
end Percolation

 
namespace Percolation
section LogarithmicTailLength

 

theorem logarithmic_tail_power (ρ X : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hX : 0 < X) :
    ρ ^ ⌈(2/(-Real.log ρ))*Real.log X⌉₊ ≤ X^(-2:ℝ) := by
  have hl : Real.log ρ ≠ 0 := ne_of_lt (Real.log_neg hρ hρ1)
  calc
    _ = ρ ^ (⌈(2/(-Real.log ρ))*Real.log X⌉₊ : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ρ ^ ((2/(-Real.log ρ))*Real.log X) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1.le (Nat.le_ceil _)
    _ = X^(-2:ℝ) := by
      rw [Real.rpow_def_of_pos hρ,Real.rpow_def_of_pos hX]
      congr 1
      field_simp [hl]

 

theorem exists_uniform_logarithmic_tail_cutoff (ρ A : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (kmin : ℕ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ 1 < (-Real.log ρ)*C₁ ∧
      ∃ k₀ : ℕ, kmin ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        A*((k:ℝ)+1)*R*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊ ≤ 1/4 := by
  have hlambda : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
  refine ⟨2/(-Real.log ρ),div_pos (by norm_num) hlambda,?_,max kmin ⌈4*A⌉₊,le_max_left _ _,?_⟩
  · rw [mul_div_cancel₀ _ (ne_of_gt hlambda)]
    norm_num
  · intro k hk R hR
    have hk' : ⌈4*A⌉₊ ≤ k := (le_max_right _ _).trans hk
    have hAk : 4*A ≤ (k:ℝ) := (Nat.le_ceil (4*A)).trans (by exact_mod_cast hk')
    have hkpos : 0 < (k:ℝ)+1 := by positivity
    have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
    let X : ℝ := ((k:ℝ)+1)*R
    have hX : 0 < X := mul_pos hkpos hRp
    have hXk : (k:ℝ)+1 ≤ X := by dsimp [X]; exact le_mul_of_one_le_right hkpos.le hR
    have hp := logarithmic_tail_power ρ X hρ hρ1 hX
    have hneg : X^(-2:ℝ) = (X^2)⁻¹ := by rw [Real.rpow_neg,show (2:ℝ) = (2:ℕ) by norm_num,Real.rpow_natCast]; exact hX.le
    calc
      _ = A*X*ρ^⌈(2/(-Real.log ρ))*Real.log X⌉₊ := by dsimp [X]; ring
      _ ≤ A*X*X^(-2:ℝ) := mul_le_mul_of_nonneg_left hp (mul_nonneg hA hX.le)
      _ = A/X := by rw [hneg]; field_simp [ne_of_gt hX]
      _ ≤ 1/4 := (div_le_iff₀ hX).mpr (by linarith)

end LogarithmicTailLength
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}



theorem position_mem_vertices {k : ℕ} {x y : V} (w : HoldingWalk H k x y) (i : ℕ) :
    w.position i ∈ w.vertices := by
  induction w generalizing i with
  | nil => simp only [position,vertices,List.mem_singleton]
  | hold w ih => cases i <;> simp only [position,vertices,List.mem_cons,true_or,ih,or_true]
  | step h w ih => cases i <;> simp only [position,vertices,List.mem_cons,true_or,ih,or_true]

theorem mem_vertices_iff_position {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) :
    z ∈ w.vertices ↔ ∃ i : ℕ, i ≤ k ∧ w.position i = z := by
  induction w with
  | nil => simp only [vertices,List.mem_singleton,Nat.le_zero,exists_eq_left,position,eq_comm]
  | @hold k x y w ih =>
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨0,Nat.zero_le _,rfl⟩
      · obtain ⟨i,hi,he⟩ := ih.mp hz
        exact ⟨i+1,Nat.succ_le_succ hi,he⟩
    · rintro ⟨i,hi,he⟩
      cases i with
      | zero => exact List.mem_cons.mpr (Or.inl he.symm)
      | succ i => exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨i,Nat.le_of_succ_le_succ hi,he⟩))
  | @step k x u y h w ih =>
    constructor
    · intro hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨0,Nat.zero_le _,rfl⟩
      · obtain ⟨i,hi,he⟩ := ih.mp hz
        exact ⟨i+1,Nat.succ_le_succ hi,he⟩
    · rintro ⟨i,hi,he⟩
      cases i with
      | zero => exact List.mem_cons.mpr (Or.inl he.symm)
      | succ i => exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨i,Nat.le_of_succ_le_succ hi,he⟩))

end HoldingWalk
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_CollisionTails
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawTimeMarginals
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_position_integral (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (i m : ℕ) (him : i ≤ m) (x : V) (f : V → ℝ) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      w.2.mass (walkKernel G hloc a) * f (w.2.position i)) =
      RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) i x f := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  induction i generalizing m x with
  | zero =>
    simp only [HoldingWalk.position_zero,tsum_mul_right,rawFrom_probability_sum G hloc a,one_mul,RawFrom.integral_zero]
  | succ i ih =>
    cases m with
    | zero => omega
    | succ m =>
      rw [←(RawFrom.succEquiv m x).symm.tsum_eq,RawFrom.integral_succ]
      let (z : V) := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m z)
      let := Fintype.ofFinite ((openSimpleGraph G Set.univ).neighborSet x)
      have hh (z : V) := ih m (Nat.le_of_succ_le_succ him) z
      simp only [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,RawFrom.succEquiv,
        Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,HoldingWalk.position,mul_assoc]
      simp only [tsum_fintype] at hh
      simp only [←Finset.mul_sum,hh]

theorem raw_position_probability (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m : ℕ) (him : i ≤ m) (x z : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if w.2.position i = z then w.2.mass (walkKernel G hloc a) else 0) =
      (matrixCoeff (P^i) x z).re := by
  have hh := raw_position_integral G hloc a i m him x (fun y => if y = z then (1:ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero] at hh
  rw [hh,raw_integral_operator G hloc a P hpos hP]
  simp only [mul_ite,mul_one,mul_zero,tsum_ite_eq]

end RawTimeMarginals
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentRawCollisions
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_two_time_collision (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m j n : ℕ) (him : i ≤ m) (hjn : j ≤ n) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if w.1.2.position i = w.2.2.position j then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) =
      (matrixCoeff (P^(i+j)) x y).re := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) n y)
  have hi (w : RawFrom (openSimpleGraph G Set.univ) m x) :
      (∑' v : RawFrom (openSimpleGraph G Set.univ) n y,
        if w.2.position i = v.2.position j then w.2.mass (walkKernel G hloc a)*v.2.mass (walkKernel G hloc a) else 0) =
      w.2.mass (walkKernel G hloc a)*(matrixCoeff (P^j) y (w.2.position i)).re := by
    rw [← raw_position_probability G hloc a P hpos hP j n hjn y (w.2.position i),←tsum_mul_left]
    apply tsum_congr
    intro v
    by_cases hh : w.2.position i = v.2.position j
    · simp only [ite_eq_left hh,ite_eq_left hh.symm]
    · simp only [ite_eq_right hh,ite_eq_right (Ne.symm hh),mul_zero]
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
  simp only [hi]
  rw [raw_position_integral G hloc a i m him x (fun z => (matrixCoeff (P^j) y z).re),raw_integral_operator G hloc a P hpos hP]
  simp only [matrixCoeff_real_symm (P^j) (hsym.pow j) y]
  rw [((hpos.pow i).mul_hasSum (P^j) x y).tsum_eq,←pow_add]

theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  apply (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (A (lp.single 2 y (1:ℂ))) x).trans
  simpa using A.le_opNorm (lp.single 2 y (1:ℂ))

theorem matrixCoeff_power_le (P : Hilbert V →L[ℂ] Hilbert V) (k : ℕ) (x y : V) :
    (matrixCoeff (P^k) x y).re ≤ ‖P‖^k := by
  have hn (k : ℕ) : ‖P^k‖ ≤ ‖P‖^k := by
    induction k with
    | zero => simpa only [pow_zero,ContinuousLinearMap.one_def] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ k ih =>
      rw [pow_succ,pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg P))
  exact (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (P^k) x y).trans (hn k))

end IndependentRawCollisions
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePropagation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_exists_short_walk (G : BondGraph V E) (x : V) (k : ℕ) {y : V}
    (hy : y ∈ reachBall G x k) :
    ∃ q : (openSimpleGraph G Set.univ).Walk x y, q.length ≤ k := by
  induction k generalizing y with
  | zero =>
    have he : y = x := hy
    subst y
    exact ⟨.nil,by simp⟩
  | succ k ih =>
    rcases hy with hy | hy
    · obtain ⟨q,hq⟩ := ih hy
      exact ⟨q,hq.trans (Nat.le_succ _)⟩
    · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy
      obtain ⟨z,hz,hzy⟩ := hy
      obtain ⟨q,hq⟩ := ih hz
      by_cases he : z = y
      · subst z
        exact ⟨q,hq.trans (Nat.le_succ _)⟩
      · let h : (openSimpleGraph G Set.univ).Adj z y :=
          (openSimpleGraph_univ_adj G z y).mpr ⟨he,hzy⟩
        refine ⟨q.append (.cons h .nil),?_⟩
        simpa only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.length_nil,zero_add] using Nat.add_le_add_right hq 1

theorem dist_le_of_mem_reachBall (G : BondGraph V E) (x y : V) (k : ℕ)
    (hy : y ∈ reachBall G x k) : (openSimpleGraph G Set.univ).dist x y ≤ k := by
  obtain ⟨q,hq⟩ := reachBall_exists_short_walk G x k hy
  exact (SimpleGraph.dist_le q).trans hq

theorem walkPower_zero_of_lt_dist (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x y : V) (hk : k < (openSimpleGraph G Set.univ).dist x y) :
    (matrixCoeff (P^k) x y).re = 0 := by
  apply walkPower_support G hloc a P hpos hP
  intro hy
  exact Nat.not_le_of_gt hk (dist_le_of_mem_reachBall G x y k hy)

 

theorem raw_two_time_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (i m j n : ℕ) (him : i ≤ m) (hjn : j ≤ n) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if w.1.2.position i = w.2.2.position j then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      if i+j < (openSimpleGraph G Set.univ).dist x y then 0 else ‖P‖^(i+j) := by
  rw [raw_two_time_collision G hloc a P hpos hsym hP i m j n him hjn x y]
  split_ifs with hh
  · exact (walkPower_zero_of_lt_dist G hloc a P hpos hP (i+j) x y hh).le
  · exact matrixCoeff_power_le P (i+j) x y

end FinitePropagation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualCollisionUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_nonnegative_event_union {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (B : α → β → Prop) :
    (∑ a, if ∃ b, B a b then μ a else 0) ≤ ∑ b, ∑ a, if B a b then μ a else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hh : ∃ b, B a b
  · obtain ⟨b,hb⟩ := hh
    rw [ite_eq_left ⟨b,hb⟩]
    calc
      μ a = (if B a b then μ a else 0) := (ite_eq_left hb).symm
      _ ≤ ∑ b, if B a b then μ a else 0 :=
        Finset.single_le_sum (f := fun b => if B a b then μ a else 0)
          (fun b _ => by split_ifs; exact hμ a; exact le_rfl) (Finset.mem_univ b)
  · rw [ite_eq_right hh]
    exact Finset.sum_nonneg (fun b _ => by split_ifs; exact hμ a; exact le_rfl)

 

theorem raw_intersection_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (m n : ℕ) (x y : V) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
    ∑ i : Fin (m+1), ∑ j : Fin (n+1),
      if i.val+j.val < (openSimpleGraph G Set.univ).dist x y then 0 else ‖P‖^(i.val+j.val) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) m x)
  let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) n y)
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have he (w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y) :
      (∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices) ↔
        ∃ ij : Fin (m+1) × Fin (n+1), w.1.2.position ij.1 = w.2.2.position ij.2 := by
    constructor
    · rintro ⟨z,hz,hz'⟩
      obtain ⟨i,hi,he⟩ := w.1.2.mem_vertices_iff_position.mp hz
      obtain ⟨j,hj,he'⟩ := w.2.2.mem_vertices_iff_position.mp hz'
      exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),he.trans he'.symm⟩
    · rintro ⟨⟨i,j⟩,hij⟩
      exact ⟨w.1.2.position i,w.1.2.position_mem_vertices i,hij ▸ w.2.2.position_mem_vertices j⟩
  simp only [he,tsum_fintype]
  have hu := finite_nonnegative_event_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y =>
      w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a))
    (fun w => mul_nonneg (w.1.2.mass_nonneg _ hK) (w.2.2.mass_nonneg _ hK))
    (fun w (ij : Fin (m+1) × Fin (n+1)) => w.1.2.position ij.1 = w.2.2.position ij.2)
  apply hu.trans
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [tsum_fintype] using
    raw_two_time_collision_bound G hloc a P hpos hsym hP i m j n (by omega) (by omega) x y

end ActualCollisionUnion
end Percolation

 
namespace Percolation
section UniformCollisionTails
attribute [local instance] Classical.propDecidable Classical.decEq

theorem geometric_cutoff_summable (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J : ℕ) :
    Summable (fun i : ℕ => if J ≤ i then ρ^i else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity)
    (fun i => by split_ifs <;> first | exact le_rfl | exact pow_nonneg hρ i)
    (summable_geometric_of_lt_one hρ hρ1)

theorem geometric_cutoff_tsum (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J : ℕ) :
    (∑' i : ℕ, if J ≤ i then ρ^i else 0) = ρ^J/(1-ρ) := by
  have hs := geometric_cutoff_summable ρ hρ hρ1 J
  rw [←hs.sum_add_tsum_nat_add J]
  have hz : (∑ i ∈ Finset.range J, if J ≤ i then ρ^i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (Nat.not_le_of_gt (Finset.mem_range.mp hi))
  rw [hz,zero_add]
  simp only [Nat.le_add_left,if_true,pow_add,tsum_mul_right,
    tsum_geometric_of_lt_one hρ hρ1,div_eq_mul_inv]
  exact mul_comm _ _

theorem finite_geometric_cutoff_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (J M : ℕ) :
    (∑ i : Fin M, if J ≤ i.val then ρ^i.val else 0) ≤ ρ^J/(1-ρ) := by
  change (∑ i : Fin M, (fun n : ℕ => if J ≤ n then ρ^n else 0) i.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if J ≤ n then ρ^n else 0) M,←geometric_cutoff_tsum ρ hρ hρ1 J]
  exact Summable.sum_le_tsum (s := Finset.range M) (fun i _ => by split_ifs <;> positivity)
    (geometric_cutoff_summable ρ hρ hρ1 J)

 

theorem finite_double_geometric_cutoff_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (J M N D : ℕ) (hD : 2*J ≤ D) :
    (∑ i : Fin M, ∑ j : Fin N, if i.val+j.val < D then 0 else ρ^(i.val+j.val)) ≤
      2*ρ^J/(1-ρ)^2 := by
  let q : ℕ → ℝ := fun i => if J ≤ i then ρ^i else 0
  have hq (i : ℕ) : 0 ≤ q i := by dsimp [q]; split_ifs <;> positivity
  have hp (i : ℕ) : 0 ≤ ρ^i := pow_nonneg hρ i
  have hQ := finite_geometric_cutoff_bound ρ hρ hρ1 J M
  have hQ' := finite_geometric_cutoff_bound ρ hρ hρ1 J N
  have hS := finite_geometric_cutoff_bound ρ hρ hρ1 0 M
  have hS' := finite_geometric_cutoff_bound ρ hρ hρ1 0 N
  simp only [Nat.zero_le,if_true,pow_zero,one_div] at hS hS'
  have hd : 0 < 1-ρ := sub_pos.mpr hρ1
  calc
    _ ≤ ∑ i : Fin M, ∑ j : Fin N, (q i.val*ρ^j.val + ρ^i.val*q j.val) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hh : i.val+j.val < D
      · rw [ite_eq_left hh]
        exact add_nonneg (mul_nonneg (hq _) (hp _)) (mul_nonneg (hp _) (hq _))
      · rw [ite_eq_right hh,pow_add]
        have hj : J ≤ i.val ∨ J ≤ j.val := by omega
        rcases hj with hi | hj
        · simp only [q,ite_eq_left hi]
          exact le_add_of_nonneg_right (mul_nonneg (hp _) (by split_ifs <;> positivity))
        · simp only [q,ite_eq_left hj]
          exact le_add_of_nonneg_left (mul_nonneg (by split_ifs <;> positivity) (hp _))
    _ = (∑ i : Fin M, q i.val)*(∑ j : Fin N, ρ^j.val) +
        (∑ i : Fin M, ρ^i.val)*(∑ j : Fin N, q j.val) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
    _ ≤ (ρ^J/(1-ρ))*(1-ρ)⁻¹ + (1-ρ)⁻¹*(ρ^J/(1-ρ)) := by
      apply add_le_add
      · exact mul_le_mul hQ hS' (Finset.sum_nonneg (fun i _ => hp _)) (by positivity)
      · exact mul_le_mul hS hQ' (Finset.sum_nonneg (fun i _ => hq _)) (by positivity)
    _ = _ := by field_simp; ring

end UniformCollisionTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformRawCollision
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_intersection_uniform_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hcontract : ‖P‖ < 1)
    (m n J : ℕ) (x y : V) (hD : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) n y,
      if ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      2*‖P‖^J/(1-‖P‖)^2 :=
  (raw_intersection_probability_bound G hloc a P hpos hsym hP m n x y).trans
    (finite_double_geometric_cutoff_bound ‖P‖ (norm_nonneg _) hcontract J (m+1) (n+1) _ hD)


end UniformRawCollision
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}



theorem mass_fromPositions (P : V → V → ℝ) (a : ℝ)
    (hP : ∀ x y, H.Adj x y → P x y = a)
    (k : ℕ) (f : Fin (k+1) → V) (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) :
    (fromPositions k f h).mass P = a^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change P (f 0) (f 1) * (fromPositions k (fun i => f i.succ) (fun i => h i.succ)).mass P = a^(k+1)
    have he : P (f 0) (f 1) = a := by simpa using hP _ _ (h 0)
    rw [he,ih,pow_succ']

theorem position_fromPositions (k : ℕ) (f : Fin (k+1) → V)
    (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) (i : ℕ) (hi : i ≤ k) :
    (fromPositions k f h).position i = f ⟨i,by omega⟩ := by
  induction k generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih (fun j => f j.succ) (fun j => h j.succ) i (by omega)

end HoldingWalk
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

theorem position_append_left {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) (i : ℕ) (hi : i ≤ k) :
    (w.append v).position i = w.position i := by
  induction w generalizing i with
  | nil =>
    obtain rfl : i = 0 := by omega
    exact v.position_zero
  | hold w ih => cases i with
    | zero => rfl
    | succ i => exact ih v i (by omega)
  | step h w ih => cases i with
    | zero => rfl
    | succ i => exact ih v i (by omega)

theorem position_append_right {k l : ℕ} {x y z : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) (i : ℕ) :
    (w.append v).position (k+i) = v.position i := by
  induction w with
  | nil => simp only [Nat.zero_add,append]
  | hold w ih => simpa only [Nat.succ_add,append,position] using ih v
  | step h w ih => simpa only [Nat.succ_add,append,position] using ih v

 

theorem ext_positions {k : ℕ} {x y : V} (w v : HoldingWalk H k x y)
    (h : ∀ i : ℕ, i ≤ k → w.position i = v.position i) : w = v := by
  induction k generalizing x y with
  | zero => cases w; cases v; rfl
  | succ k ih =>
    cases w with
    | hold w =>
      cases v with
      | hold v =>
        congr 1
        exact ih w v (fun i hi => h (i+1) (Nat.succ_le_succ hi))
      | step hv v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        exact (hv.ne he).elim
    | step hw w =>
      cases v with
      | hold v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        exact (hw.ne he.symm).elim
      | step hv v =>
        have he := h 1 (Nat.succ_le_succ (Nat.zero_le k))
        simp only [position,position_zero] at he
        cases he
        congr 1
        exact ih w v (fun i hi => h (i+1) (Nat.succ_le_succ hi))

end HoldingWalk
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IntrinsicVisibleBlocks
attribute [local instance] Classical.propDecidable Classical.decEq

theorem positiveStem_mass (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ))
    (P : V → V → ℝ) (a : ℝ) (hP : ∀ x y, H.Adj x y → P x y = a) :
    (positiveStem H J s hs).mass P = a^J :=
  HoldingWalk.mass_fromPositions P a hP J _ _

theorem escapeLabelRaw_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    (escapeLabelRaw G J L m γ hγ ξ).mass (walkKernel G hloc a) =
      a^(J+J)*ξ.middle.mass (walkKernel G hloc a) := by
  simp only [escapeLabelRaw,HoldingWalk.mass_append,HoldingWalk.mass_reverse _ (walkKernel_symmetric G hloc a),
    positiveStem_mass _ _ _ _ _ a (fun _ _ h => walkKernel_step G hloc a h),pow_add]
  ring

theorem escapeLabelRaw_middle_position (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (i : ℕ) (hi : i ≤ L) :
    (escapeLabelRaw G J L m γ hγ ξ).position (J+i) = ξ.middle.position i := by
  rw [escapeLabelRaw,HoldingWalk.position_append_right,HoldingWalk.position_append_left _ _ i hi]

end IntrinsicVisibleBlocks
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
namespace RawFrom
variable {H : SimpleGraph V}

 
theorem ext_positions {k : ℕ} {x : V} (w v : RawFrom H k x)
    (h : ∀ i : ℕ, i ≤ k → w.2.position i = v.2.position i) : w = v := by
  rcases w with ⟨y,w⟩
  rcases v with ⟨z,v⟩
  have he : y = z := by simpa only [HoldingWalk.position_length] using h k le_rfl
  subst z
  exact Sigma.ext rfl (heq_of_eq (HoldingWalk.ext_positions w v h))

end RawFrom



end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RootedRawProjection
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootedEscapeLabelRaw_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    (rootedEscapeLabelRaw G J L m γ hγ x ξ).2.mass (walkKernel G hloc a) =
      a^(J+J)*ξ.1.middle.mass (walkKernel G hloc a) := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact escapeLabelRaw_mass G hloc a J L m γ hγ ξ

theorem rootedEscapeLabelRaw_middle_position (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (i : ℕ) (hi : i ≤ L) :
    (rootedEscapeLabelRaw G J L m γ hγ x ξ).2.position (J+i) = ξ.1.middle.position i := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact escapeLabelRaw_middle_position G J L m γ hγ ξ i hi

theorem rootedEscapeLabelRaw_fiber_middle_mass (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (ha : 0 < a) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x)
    (hw : rootedEscapeLabelRaw G J L m γ hγ x ξ = w) :
    ξ.1.middle.mass (walkKernel G hloc a) = w.2.mass (walkKernel G hloc a)/a^(J+J) := by
  apply (eq_div_iff (ne_of_gt (pow_pos ha _))).mpr
  rw [mul_comm,←rootedEscapeLabelRaw_mass G hloc a J L m γ hγ x ξ,hw]

theorem rootedEscapeLabelRaw_fiber_middle_positions (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x})
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x)
    (hw : rootedEscapeLabelRaw G J L m γ hγ x ξ = w) :
    ∀ i : ℕ, i ≤ L → ξ.1.middle.position i = w.2.position (J+i) := by
  intro i hi
  rw [←rootedEscapeLabelRaw_middle_position G J L m γ hγ x ξ i hi,hw]

end RootedRawProjection
end Percolation

 
namespace Percolation
section FiniteFiberDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_auxiliary_event_bound {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hs : ∑ a, μ a = 1)
    (B : α → Prop) (c : ℝ) (hc : 0 ≤ c) :
    (∑ a, if B a then c*μ a else 0) ≤ c := by
  calc
    _ ≤ ∑ a, c*μ a := Finset.sum_le_sum (fun a _ => by
      split_ifs; exact le_rfl; exact mul_nonneg hc (hμ a))
    _ = c := by rw [←Finset.mul_sum,hs,mul_one]

 

theorem finite_nested_unique_fiber_bound {β : Type*} [Fintype β]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    {T : (b : β) → γ b → Type*} [∀ b c, Fintype (T b c)]
    (μ : β → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (ν : (b : β) → (c : γ b) → T b c → ℝ) (hν : ∀ b c t, 0 ≤ ν b c t)
    (hs : ∀ b c, ∑ t, ν b c t = 1)
    (B : (b : β) → (c : γ b) → T b c → Prop)
    (N C : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hcard : ∀ b, (Fintype.card (γ b) : ℝ) ≤ N)
    (hunique : ∀ b c t b' c' t', B b c t → B b' c' t' → b = b')
    (hbound : ∀ b c t, B b c t → μ b ≤ C) :
    (∑ b, ∑ c, ∑ t, if B b c t then μ b*ν b c t else 0) ≤ N*C := by
  by_cases hh : ∃ b c t, B b c t
  · obtain ⟨b,c,t,hb⟩ := hh
    have he : (∑ b', ∑ c', ∑ t', if B b' c' t' then μ b'*ν b' c' t' else 0) =
        ∑ c', ∑ t', if B b c' t' then μ b*ν b c' t' else 0 := by
      apply Finset.sum_eq_single b
      · intro b' _ hne
        apply Finset.sum_eq_zero
        intro c' _
        apply Finset.sum_eq_zero
        intro t' _
        exact ite_eq_right (fun hb' => hne (hunique b' c' t' b c t hb' hb))
      · simp
    rw [he]
    calc
      _ ≤ ∑ _c : γ b, μ b := Finset.sum_le_sum (fun c' _ =>
        finite_auxiliary_event_bound (ν b c') (hν b c') (hs b c') (B b c') (μ b) (hμ b))
      _ = (Fintype.card (γ b) : ℝ)*μ b := by simp
      _ ≤ N*C := mul_le_mul (hcard b) (hbound b c t hb) (hμ b) hN
  · have hz : ∀ b c t, ¬B b c t := by simpa only [not_exists] using hh
    simp only [hz,if_false,Finset.sum_const_zero]
    exact mul_nonneg hN hC

end FiniteFiberDomination
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CodeMiddleIdentities
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem labelFromCode_middle_position (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) (i : ℕ) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.middle.position i =
      c.2.1.2.position i := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

theorem labelFromCode_middle_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (P : V → V → ℝ)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    (labelFromCode G hloc γ n hdiam center ep neg L m x c).1.middle.mass P =
      c.2.1.2.mass P := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨hhm,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

end CodeMiddleIdentities
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralFiberEstimate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rooted_code_single_anchor_fiber_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (s : segmentAnchors G hloc γ n hdiam (segmentCenter J) x)
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val (Fin.last (J+J))),
      ∑' h : segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) mid.1,
        ∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val 0) ×
            RawFrom (openSimpleGraph G Set.univ) m (h.val 0),
          if rootedEscapeLabelRaw G J L m γ hγ x
              (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
                ⟨s,mid,h,tails⟩) = w then
            mid.2.mass (walkKernel G hloc a) * tails.1.2.mass (walkKernel G hloc a) *
              tails.2.2.mass (walkKernel G hloc a) else 0) ≤
      ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
        (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  simp only [tsum_fintype,mul_assoc]
  convert finite_nested_unique_fiber_bound
    (β := RawFrom (openSimpleGraph G Set.univ) L (s.val (Fin.last (J+J))))
    (γ := fun mid => segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) mid.1)
    (T := fun _ h => RawFrom (openSimpleGraph G Set.univ) m (s.val 0) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val 0))
    (fun mid => mid.2.mass (walkKernel G hloc a))
    (fun mid => mid.2.mass_nonneg _ hK)
    (fun _ _ tails => tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a))
    (fun _ _ tails => mul_nonneg (tails.1.2.mass_nonneg _ hK) (tails.2.2.mass_nonneg _ hK)) ?_
    (fun mid h tails => rootedEscapeLabelRaw G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) = w)
    (((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ))
    (w.2.mass (walkKernel G hloc a)/a^(J+J)) ?_ ?_ ?_ ?_ ?_ using 1
  · apply Finset.sum_congr rfl
    intro mid _
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro tails _
    split_ifs <;> rfl
  · intro mid h
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    simpa only [tsum_fintype,mul_one] using congrArg₂ (fun r s : ℝ => r*s)
      (rawFrom_probability_sum G hloc a m (s.val 0))
      (rawFrom_probability_sum G hloc a m (h.val 0))
  · positivity
  · exact div_nonneg (w.2.mass_nonneg _ hK) (pow_nonneg ha.le _)
  · intro mid
    rw [Fintype.card_coe,segmentAnchors_card_eq_indicator G hloc γ n hdiam (Fin.last (J+J)) mid.1]
    split_ifs
    · exact le_rfl
    · exact_mod_cast Nat.zero_le _
  · intro mid h tails mid' h' tails' hh hh'
    apply RawFrom.ext_positions
    intro i hi
    have he := rootedEscapeLabelRaw_fiber_middle_positions G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) w hh i hi
    have he' := rootedEscapeLabelRaw_fiber_middle_positions G J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid',h',tails'⟩) w hh' i hi
    have hm := labelFromCode_middle_position G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩ i
    have hm' := labelFromCode_middle_position G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid',h',tails'⟩ i
    exact hm.symm.trans (he.trans (he'.symm.trans hm'))
  · intro mid h tails hh
    have he := rootedEscapeLabelRaw_fiber_middle_mass G hloc a ha J L m γ hγ x
      (labelFromCode G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x ⟨s,mid,h,tails⟩) w hh
    have hm := labelFromCode_middle_mass G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x (walkKernel G hloc a) ⟨s,mid,h,tails⟩
    exact (hm.symm.trans he).le

end LiteralFiberEstimate
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralProjectionDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem rooted_label_raw_fiber_mass_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if rootedEscapeLabelRaw G J L m γ hγ x ξ = w then ξ.1.mass (walkKernel G hloc a) else 0) ≤
      ((segmentAnchors G hloc γ n hdiam (segmentCenter J) x).card : ℝ) *
      ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
        (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let R := rootedLabelEquiv G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  calc
    _ ≤ ∑' _s : segmentAnchors G hloc γ n hdiam (segmentCenter J) x,
        ((segmentAnchors G hloc γ n hdiam (Fin.last (J+J)) (γ (Fin.last (J+J)))).card : ℝ) *
          (w.2.mass (walkKernel G hloc a)/a^(J+J)) := by
      apply (summable_of_hasFiniteSupport (Set.toFinite _)).tsum_le_tsum _
        (summable_of_hasFiniteSupport (Set.toFinite _))
      intro s
      rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      conv_lhs => arg 1; ext mid; rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
      exact rooted_code_single_anchor_fiber_bound G hloc a ha hK J L m γ hγ n hdiam x s w
    _ = _ := by
      simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring

end LiteralProjectionDomination
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedProjection
attribute [local instance] Classical.propDecidable Classical.decEq

theorem tsum_indicator_div {α : Type*} (f : α → ℝ) (B : α → Prop) [DecidablePred B] (d : ℝ) :
    (∑' a, if B a then f a/d else 0) = (∑' a, if B a then f a else 0)/d := by
  rw [←tsum_div_const]
  apply tsum_congr
  intro a
  split_ifs <;> simp

theorem rooted_label_raw_projection_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if rootedEscapeLabelRaw G J L m γ hγ x ξ = w then
        escapeLabelProbability G hloc a γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) ≤
      w.2.mass (walkKernel G hloc a)/(a^(J+J)*q) := by
  have hN (i : Fin (J+J+1)) : 0 < ((segmentAnchors G hloc γ n hdiam i (γ i)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam i (γ i)).mpr
      (by exact ⟨Equiv.refl V,Equiv.refl E,(fun e => by simp),rfl⟩))
  have hQ := hq.trans_le hqle
  have hA := pow_pos ha (J+J)
  have hm := w.2.mass_nonneg (walkKernel G hloc a) hK
  simp only [escapeLabelProbability,tsum_indicator_div]
  have hb := rooted_label_raw_fiber_mass_bound G hloc a ha hK J L m γ hγ n hdiam x w
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam (segmentCenter J) x hx] at hb
  apply (div_le_div_of_nonneg_right hb (mul_nonneg (mul_nonneg (hN (segmentCenter J)).le (hN (Fin.last (J+J))).le) hQ.le)).trans
  calc
    _ = w.2.mass (walkKernel G hloc a)/
        (a^(J+J)*segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J)))) := by
      field_simp [(hN (segmentCenter J)).ne', (hN (Fin.last (J+J))).ne']
    _ ≤ _ := div_le_div_of_nonneg_left hm (mul_pos hA hq) (mul_le_mul_of_nonneg_left hqle hA.le)

end NormalizedProjection
end Percolation

 
namespace Percolation
universe u
variable {V : Type u}
section SuffixCollisionOperator

theorem operator_pow_norm_le (P : Hilbert V →L[ℂ] Hilbert V) (k : ℕ) : ‖P^k‖ ≤ ‖P‖^k := by
  cases k with
  | zero => simpa only [pow_zero,ContinuousLinearMap.one_def] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
  | succ k => exact norm_pow_le' P (Nat.succ_pos k)

 

theorem positive_rows_collision_hasSum (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (x y : V) :
    HasSum (fun z => (matrixCoeff A x z).re*(matrixCoeff B y z).re)
      (matrixCoeff (A*star B) x y).re := by
  simpa only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_re] using
    hA.mul_hasSum (star B) x y

theorem positive_rows_collision_bound (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (x y : V) :
    (∑' z, (matrixCoeff A x z).re*(matrixCoeff B y z).re) ≤ ‖A‖*‖B‖ := by
  rw [(positive_rows_collision_hasSum A B hA x y).tsum_eq]
  apply (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (A*star B) x y).trans _)
  have hs : ‖star B‖ = ‖B‖ := ContinuousLinearMap.adjoint.norm_map B
  simpa only [hs] using norm_mul_le A (star B)

theorem walk_suffix_collision_operator_bound (P H : Hilbert V →L[ℂ] Hilbert V)
    (hP : PositiveRealMatrix P) (C : ℝ) (hH : ‖H‖ ≤ C) (l L : ℕ) (x y : V) :
    (∑' z, (matrixCoeff (P^l) x z).re*(matrixCoeff (P^L*H) y z).re) ≤
      C*‖P‖^(l+L) := by
  calc
    _ ≤ ‖P^l‖*‖P^L*H‖ := positive_rows_collision_bound _ _ (hP.pow l) x y
    _ ≤ ‖P‖^l*(‖P‖^L*C) := mul_le_mul (operator_pow_norm_le P l)
      ((norm_mul_le _ _).trans (mul_le_mul (operator_pow_norm_le P L) hH (norm_nonneg H)
        (pow_nonneg (norm_nonneg P) L))) (norm_nonneg _) (pow_nonneg (norm_nonneg P) l)
    _ = _ := by rw [pow_add]; ring

end SuffixCollisionOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchored_position_expectation (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (L : ℕ) (x z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L x,
      mid.2.mass (walkKernel G hloc a)*anchoredPositionKernel G hloc γ n hdiam ep j mid.1 z) =
      (matrixCoeff (P^L*H) x z).re := by
  change RawFrom.integral (walkKernel G hloc a) L x
    (fun y => anchoredPositionKernel G hloc γ n hdiam ep j y z) = _
  rw [raw_integral_operator G hloc a P hpos hP]
  simpa only [hH,Complex.ofReal_re] using ((hpos.pow L).mul_hasSum H x z).tsum_eq

 

theorem raw_tail_anchored_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (C : ℝ) (hHC : ‖H‖ ≤ C) (l m L : ℕ) (hlm : l ≤ m) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) ≤
      C*‖P‖^(l+L) := by
  simp only [raw_anchored_position_expectation G hloc a γ n hdiam ep j P H hpos hP hH]
  rw [raw_position_integral G hloc a l m hlm x (fun z => (matrixCoeff (P^L*H) y z).re),
    raw_integral_operator G hloc a P hpos hP]
  exact walk_suffix_collision_operator_bound P H hpos C hHC l L x y

end ActualSuffixCollision
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

theorem raw_tail_anchored_collision_uniform (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (l m L : ℕ) (hlm : l ≤ m) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) ≤
      Real.sqrt c*‖P‖^(l+L) := by
  obtain ⟨H,hH,hHn⟩ := exists_anchoredPositionOperator_uniform G hloc root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j
  exact raw_tail_anchored_collision_bound G hloc a γ n hdiam ep j P H hpos hP hH
    (Real.sqrt c) hHn l m L hlm x y

end UniformSuffixCollision
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GlobalAnchorDenominator
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem anchoredPositionKernel_global_denominator (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I) (x z : V) :
    (∑ h : segmentAnchors G hloc γ n hdiam ep x,
      if h.val j = z then ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ)⁻¹ else 0) =
      anchoredPositionKernel G hloc γ n hdiam ep j x z := by
  rw [Finset.sum_coe_sort _ (fun h : I → V => if h j = z then
    ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ)⁻¹ else 0)]
  by_cases hx : x ∈ vertexOrbit G (γ ep)
  · unfold anchoredPositionKernel
    rw [segmentAnchors_card_on_orbit G hloc γ n hdiam ep x hx]
    apply Finset.sum_congr rfl
    intro h _
    simp only [eq_comm]
  · have hz := ((segmentAnchors_nonempty_iff G hloc γ n hdiam ep x).not.mpr hx)
    have he := Finset.not_nonempty_iff_eq_empty.mp hz
    simp only [anchoredPositionKernel,he,Finset.sum_empty]

theorem finite_geometric_sum_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (M : ℕ) :
    (∑ i : Fin M, ρ^i.val) ≤ 1/(1-ρ) := by
  simpa only [Nat.zero_le,if_true,pow_zero] using finite_geometric_cutoff_bound ρ hρ hρ1 0 M

end GlobalAnchorDenominator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralSuffixExperiment
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_tail_anchor_collision_identity (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (l m L : ℕ) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if tail.2.position l = h.val j then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      tail.2.mass (walkKernel G hloc a) *
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
          mid.2.mass (walkKernel G hloc a)*
            anchoredPositionKernel G hloc γ n hdiam ep j mid.1 (tail.2.position l)) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  simp only [tsum_fintype]
  apply Finset.sum_congr rfl
  intro tail _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mid _
  rw [←anchoredPositionKernel_global_denominator G hloc γ n hdiam ep j mid.1 (tail.2.position l)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : tail.2.position l = h.val j
  · simp only [ite_eq_left hh,ite_eq_left hh.symm,div_eq_mul_inv,mul_assoc]
  · simp only [ite_eq_right hh,ite_eq_right (Ne.symm hh),mul_zero]

end LiteralSuffixExperiment
end Percolation

 
namespace Percolation
section NestedFiniteUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_threefold_event_union {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    (μ : (a : α) → (b : β) → γ b → ℝ) (hμ : ∀ a b c, 0 ≤ μ a b c)
    (B : (a : α) → (b : β) → γ b → δ → Prop) :
    (∑ a, ∑ b, ∑ c, if ∃ d, B a b c d then μ a b c else 0) ≤
      ∑ d, ∑ a, ∑ b, ∑ c, if B a b c d then μ a b c else 0 := by
  have hh := finite_nonnegative_event_union
    (fun ξ : α × Sigma γ => μ ξ.1 ξ.2.1 ξ.2.2)
    (fun ξ => hμ ξ.1 ξ.2.1 ξ.2.2)
    (fun ξ : α × Sigma γ => B ξ.1 ξ.2.1 ξ.2.2)
  simpa only [Fintype.sum_prod_type,Fintype.sum_sigma] using hh

end NestedFiniteUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WholeSuffixCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι S : Type*} [Fintype I] [Fintype ι] [Fintype S]

 

theorem raw_tail_whole_suffix_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I) (j : S → I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hρ : ‖P‖ < 1) (m L : ℕ) (x y : V) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if ∃ ij : Fin (m+1) × S, tail.2.position ij.1.val = h.val (j ij.2) then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L/(1-‖P‖) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  simp only [tsum_fintype]
  have hu := finite_threefold_event_union
    (α := RawFrom (openSimpleGraph G Set.univ) m x)
    (β := RawFrom (openSimpleGraph G Set.univ) L y)
    (γ := fun mid => segmentAnchors G hloc γ n hdiam ep mid.1)
    (δ := Fin (m+1) × S)
    (fun tail mid _ => tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
      (segmentAnchors G hloc γ n hdiam ep (γ ep)).card)
    (fun tail mid _ => div_nonneg (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK)) (Nat.cast_nonneg _))
    (fun tail _ h ij => tail.2.position ij.1.val = h.val (j ij.2))
  apply hu.trans
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Fin (m+1), ∑ _s : S, Real.sqrt c*‖P‖^(i.val+L) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro s _
      have hh := raw_tail_anchored_collision_uniform G hloc a root weight Γ hΓ htr hw hw1 hcov c hc hmin
        γ n hdiam ep (j s) P hpos hP i.val m L (by omega) x y
      rw [←raw_tail_anchor_collision_identity G hloc a γ n hdiam ep (j s) i.val m L x y] at hh
      simpa only [tsum_fintype] using hh
    _ = ((Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L)*(∑ i : Fin (m+1), ‖P‖^i.val) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_add,←Finset.mul_sum,←Finset.sum_mul]
      ring
    _ ≤ ((Fintype.card S : ℝ)*Real.sqrt c*‖P‖^L)*(1/(1-‖P‖)) :=
      mul_le_mul_of_nonneg_left (finite_geometric_sum_bound ‖P‖ (norm_nonneg P) hρ (m+1)) (by positivity)
    _ = _ := by ring

end WholeSuffixCollision
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualAnchorPointTest
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

theorem raw_anchor_position_identity (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (L : ℕ) (y z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if h.val j = z then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      mid.2.mass (walkKernel G hloc a)*anchoredPositionKernel G hloc γ n hdiam ep j mid.1 z) := by
  apply tsum_congr
  intro mid
  rw [←anchoredPositionKernel_global_denominator G hloc γ n hdiam ep j mid.1 z,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp only [div_eq_mul_inv,mul_zero]

theorem raw_anchor_point_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep j : I)
    (P H : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hH : ∀ x y, matrixCoeff H x y = (anchoredPositionKernel G hloc γ n hdiam ep j x y : ℂ))
    (C : ℝ) (hC : ‖H‖ ≤ C) (L : ℕ) (y z : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if h.val j = z then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤ C*‖P‖^L := by
  rw [raw_anchor_position_identity G hloc a γ n hdiam ep j L y z,
    raw_anchored_position_expectation G hloc a γ n hdiam ep j P H hpos hP hH L y z]
  apply (Complex.re_le_norm _).trans ((matrixCoeff_norm_le (P^L*H) y z).trans _)
  calc
    _ ≤ ‖P^L‖*‖H‖ := norm_mul_le _ _
    _ ≤ ‖P‖^L*C := mul_le_mul (operator_pow_norm_le P L) hC (norm_nonneg _) (pow_nonneg (norm_nonneg P) L)
    _ = _ := mul_comm _ _

end ActualAnchorPointTest
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_PositiveEscapes
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Escapes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
section DependentFiniteUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_dependent_event_union {β δ : Type*} [Fintype β] [Fintype δ]
    {γ : β → Type*} [∀ b, Fintype (γ b)]
    (μ : (b : β) → γ b → ℝ) (hμ : ∀ b c, 0 ≤ μ b c)
    (B : (b : β) → γ b → δ → Prop) :
    (∑ b, ∑ c, if ∃ d, B b c d then μ b c else 0) ≤
      ∑ d, ∑ b, ∑ c, if B b c d then μ b c else 0 := by
  have hh := finite_nonnegative_event_union
    (fun ξ : Sigma γ => μ ξ.1 ξ.2)
    (fun ξ => hμ ξ.1 ξ.2)
    (fun ξ : Sigma γ => B ξ.1 ξ.2)
  simpa only [Fintype.sum_sigma] using hh

end DependentFiniteUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualFinitePositionHits
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι S T : Type*} [Fintype I] [Fintype ι] [Fintype S] [Fintype T]

 

theorem raw_anchor_finite_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (j : S → I) (z : T → V)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (L : ℕ) (y : V) :
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if ∃ st : S × T, h.val (j st.1) = z st.2 then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (Fintype.card S : ℝ)*(Fintype.card T : ℝ)*Real.sqrt c*‖P‖^L := by
  let (v : V) : Finite ((openSimpleGraph G Set.univ).neighborSet v) := finite_openSimpleGraph_neighbors G hloc v
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) L y) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  simp only [tsum_fintype]
  have hu := finite_dependent_event_union
    (β := RawFrom (openSimpleGraph G Set.univ) L y)
    (γ := fun mid => segmentAnchors G hloc γ n hdiam ep mid.1)
    (δ := S × T)
    (fun mid _ => mid.2.mass (walkKernel G hloc a)/(segmentAnchors G hloc γ n hdiam ep (γ ep)).card)
    (fun mid _ => div_nonneg (mid.2.mass_nonneg _ hK) (Nat.cast_nonneg _))
    (fun _ h st => h.val (j st.1) = z st.2)
  apply hu.trans
  calc
    _ ≤ ∑ _st : S × T, Real.sqrt c*‖P‖^L := by
      apply Finset.sum_le_sum
      intro st _
      obtain ⟨H,hH,hHn⟩ := exists_anchoredPositionOperator_uniform G hloc root weight Γ hΓ htr hw hw1 hcov
        c hc hmin γ n hdiam ep (j st.1)
      simpa only [tsum_fintype] using raw_anchor_point_collision_bound G hloc a γ n hdiam ep (j st.1)
        P H hpos hP hH (Real.sqrt c) hHn L y (z st.2)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul]; ring

end ActualFinitePositionHits
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EarlyFiniteCollisions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {S : Type*} [Fintype S]

 

theorem raw_hits_distant_set_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m J : ℕ) (x : V) (z : S → V) (hD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (z s)) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x,
      if ∃ s, z s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      (Fintype.card S : ℝ)*‖P‖^J/(1-‖P‖) := by
  let (v : V) : Finite ((openSimpleGraph G Set.univ).neighborSet v) := finite_openSimpleGraph_neighbors G hloc v
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) m x) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have he (w : RawFrom (openSimpleGraph G Set.univ) m x) :
      (∃ s, z s ∈ w.2.vertices) ↔ ∃ si : S × Fin (m+1), w.2.position si.2.val = z si.1 := by
    constructor
    · rintro ⟨s,hs⟩
      obtain ⟨i,hi,he⟩ := w.2.mem_vertices_iff_position.mp hs
      exact ⟨(s,⟨i,by omega⟩),he⟩
    · rintro ⟨⟨s,i⟩,he⟩
      exact ⟨s,he ▸ w.2.position_mem_vertices i.val⟩
  simp only [he,tsum_fintype]
  have hu := finite_nonnegative_event_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK)
    (fun w (si : S × Fin (m+1)) => w.2.position si.2.val = z si.1)
  apply hu.trans
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _s : S, ∑ i : Fin (m+1), if J ≤ i.val then ‖P‖^i.val else 0 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro i _
      have hh := raw_position_probability G hloc a P hpos hP i.val m (by omega) x (z s)
      simp only [tsum_fintype] at hh
      rw [hh]
      split_ifs with hi
      · exact matrixCoeff_power_le P i.val x (z s)
      · exact (walkPower_zero_of_lt_dist G hloc a P hpos hP i.val x (z s) (by have hd := hD s; omega)).le
    _ ≤ ∑ _s : S, ‖P‖^J/(1-‖P‖) := Finset.sum_le_sum (fun _ _ =>
      finite_geometric_cutoff_bound ‖P‖ (norm_nonneg _) hρ J (m+1))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end EarlyFiniteCollisions
end Percolation

 
namespace Percolation
section QuantitativeEarlyCutoff



theorem earlyCollisionCost_tendsto (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Filter.Tendsto (earlyCollisionCost ρ) Filter.atTop (nhds 0) := by
  have hn : ‖ρ‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hρ] using hρ1
  have ht : Filter.Tendsto (fun J : ℕ => (J:ℝ)*ρ^J) Filter.atTop (nhds 0) := by
    simpa only [pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1 hn).tendsto_atTop_zero
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1
  have hh := (((ht.add hp).const_mul 2).div_const (1-ρ)).add ((hp.const_mul 2).div_const ((1-ρ)^2))
  have he : earlyCollisionCost ρ = (fun J : ℕ => 2*((J:ℝ)*ρ^J+ρ^J)/(1-ρ)+2*ρ^J/(1-ρ)^2) := by
    funext J
    unfold earlyCollisionCost
    ring
  rw [he]
  simpa only [zero_add,mul_zero,zero_div] using hh

theorem exists_earlyCollisionCutoff (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → earlyCollisionCost ρ J < ε := by
  exact Filter.eventually_atTop.mp ((earlyCollisionCost_tendsto ρ hρ hρ1).eventually (gt_mem_nhds hε))

end QuantitativeEarlyCutoff
end Percolation

 
namespace Percolation
section WeightedBinaryUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_weighted_event_or {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (B C : α → Prop) [DecidablePred B] [DecidablePred C] :
    (∑ a, if B a ∨ C a then μ a else 0) ≤
      (∑ a, if B a then μ a else 0) + ∑ a, if C a then μ a else 0 := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hb : B a <;> by_cases hc : C a <;> simp only [hb,hc,or_self,or_false,false_or,if_true,if_false,add_zero,zero_add,le_refl]
  exact le_add_of_nonneg_right (hμ a)

end WeightedBinaryUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ActualEarlyExperiment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_early_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if ((∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices)) ∨
          (∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices) then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      earlyCollisionCost ‖P‖ J := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) m x) := Fintype.ofFinite _
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) L y) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hu := finite_weighted_event_or
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y =>
      w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a))
    (fun w => mul_nonneg (w.1.2.mass_nonneg _ hK) (w.2.2.mass_nonneg _ hK))
    (fun w => (∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices))
    (fun w => ∃ z, z ∈ w.1.2.vertices ∧ z ∈ w.2.2.vertices)
  have hp := finite_product_failure_union
    (fun w : RawFrom (openSimpleGraph G Set.univ) m x => w.2.mass (walkKernel G hloc a))
    (fun w : RawFrom (openSimpleGraph G Set.univ) L y => w.2.mass (walkKernel G hloc a))
    (fun w => w.2.mass_nonneg _ hK) (fun w => w.2.mass_nonneg _ hK)
    (by simpa only [tsum_fintype] using rawFrom_probability_sum G hloc a m x)
    (by simpa only [tsum_fintype] using rawFrom_probability_sum G hloc a L y)
    (fun w => ∃ s, pos s ∈ w.2.vertices) (fun w => ∃ s, neg s ∈ w.2.vertices)
  have hx := raw_hits_distant_set_bound G hloc a P hpos hP hρ m J x pos hposD
  have hy := raw_hits_distant_set_bound G hloc a P hpos hP hρ L J y neg hnegD
  have hi := raw_intersection_uniform_bound G hloc a P hpos hsym hP hρ m L J x y hxy
  simp only [tsum_fintype,Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hx hy hi ⊢
  have hx' : (∑ w : RawFrom (openSimpleGraph G Set.univ) m x,
      if ∃ s, pos s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((J:ℝ)+1)*‖P‖^J/(1-‖P‖) := by
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> rfl
  have hy' : (∑ w : RawFrom (openSimpleGraph G Set.univ) L y,
      if ∃ s, neg s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) ≤
      ((J:ℝ)+1)*‖P‖^J/(1-‖P‖) := by
    convert hy using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> rfl
  have hp' : (∑ w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if (∃ s, pos s ∈ w.1.2.vertices) ∨ (∃ s, neg s ∈ w.2.2.vertices) then
        w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) ≤
      (∑ w : RawFrom (openSimpleGraph G Set.univ) m x,
        if ∃ s, pos s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) +
      (∑ w : RawFrom (openSimpleGraph G Set.univ) L y,
        if ∃ s, neg s ∈ w.2.vertices then w.2.mass (walkKernel G hloc a) else 0) := by
    convert hp using 1
    · apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> rfl
    · congr 1 <;> apply Finset.sum_congr rfl <;> intro w _ <;> split_ifs <;> rfl
  have hr : (((J:ℝ)+1)*‖P‖^J/(1-‖P‖) + ((J:ℝ)+1)*‖P‖^J/(1-‖P‖)) +
      2*‖P‖^J/(1-‖P‖)^2 = earlyCollisionCost ‖P‖ J := by
    unfold earlyCollisionCost
    ring
  have hh := hu.trans ((add_le_add (hp'.trans (add_le_add hx' hy')) hi).trans_eq hr)
  exact hh

end ActualEarlyExperiment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ConditioningCost
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchor_event_le_unconditioned (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (m L : ℕ) (x y : V)
    (B : RawFrom (openSimpleGraph G Set.univ) m x → RawFrom (openSimpleGraph G Set.univ) L y → Prop) [∀ tail mid, Decidable (B tail mid)] :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B tail mid then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
    (∑' w : RawFrom (openSimpleGraph G Set.univ) m x × RawFrom (openSimpleGraph G Set.univ) L y,
      if B w.1 w.2 then w.1.2.mass (walkKernel G hloc a)*w.2.2.mass (walkKernel G hloc a) else 0) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam ep (γ ep)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  simp only [tsum_fintype,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro tail _
  apply Finset.sum_le_sum
  intro mid _
  by_cases hb : B tail mid
  · simp only [ite_eq_left hb,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    have hc : ((segmentAnchors G hloc γ n hdiam ep mid.1).card : ℝ) ≤
        (segmentAnchors G hloc γ n hdiam ep (γ ep)).card := by
      rw [segmentAnchors_card_eq_indicator G hloc γ n hdiam ep mid.1]
      split_ifs
      · exact le_rfl
      · exact_mod_cast Nat.zero_le _
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hN).mpr
    have hh := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK))
    nlinarith
  · simp only [ite_eq_right hb,Finset.sum_const_zero]
    exact le_rfl

end ConditioningCost
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EarlyAnchoredCollision
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 

theorem raw_anchor_early_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' _h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
              (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices) then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      earlyCollisionCost ‖P‖ J := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  exact (raw_anchor_event_le_unconditioned G hloc a hK γ n hdiam ep m L x y
    (fun tail mid => ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
      (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices))).trans
    (raw_early_collision_bound G hloc a P hpos hsym hP hρ m L J x y pos neg hposD hnegD hxy)

 

theorem raw_tail_integrate_anchor_event (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (m L : ℕ) (x y : V)
    (B : (mid : RawFrom (openSimpleGraph G Set.univ) L y) →
      segmentAnchors G hloc γ n hdiam ep mid.1 → Prop) [∀ mid h, Decidable (B mid h)] :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B mid h then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
    (∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        if B mid h then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) := by
  have he (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) :
      (if B mid h then tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
        (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) =
      tail.2.mass (walkKernel G hloc a) *
        (if B mid h then mid.2.mass (walkKernel G hloc a)/
          (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) := by
    split_ifs <;> ring
  simp only [he,tsum_mul_left,tsum_mul_right,rawFrom_probability_sum G hloc a,one_mul]

end EarlyAnchoredCollision
end Percolation

 
namespace Percolation
section DependentUnion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_threefold_event_or {α β : Type*} {γ : β → Type*}
    [Fintype α] [Fintype β] [∀ b, Fintype (γ b)]
    (μ : α → (b : β) → γ b → ℝ) (hμ : ∀ a b c, 0 ≤ μ a b c)
    (B C : α → (b : β) → γ b → Prop)
    [∀ a b c, Decidable (B a b c)] [∀ a b c, Decidable (C a b c)] :
    (∑ a, ∑ b, ∑ c, if B a b c ∨ C a b c then μ a b c else 0) ≤
      (∑ a, ∑ b, ∑ c, if B a b c then μ a b c else 0) +
      (∑ a, ∑ b, ∑ c, if C a b c then μ a b c else 0) := by
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro c _
  by_cases hb : B a b c <;> by_cases hc : C a b c <;>
    simp only [hb,hc,or_self,or_false,false_or,if_true,if_false,add_zero,zero_add,le_refl]
  exact le_add_of_nonneg_right (hμ a b c)

end DependentUnion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CombinedRawAvoidance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]



theorem raw_first_escape_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 ≤ weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  let μ := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (_h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
      (segmentAnchors G hloc γ n hdiam ep (γ ep)).card
  have hμ : ∀ tail mid h, 0 ≤ μ tail mid h := fun tail mid _ =>
    div_nonneg (mul_nonneg (tail.2.mass_nonneg _ hK) (mid.2.mass_nonneg _ hK)) (Nat.cast_nonneg _)
  let B := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (_h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
      (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices)
  let C := fun (_tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ∃ st : Fin (J+1) × Fin (J+1), h.val (j st.1) = neg st.2
  let D := fun (tail : RawFrom (openSimpleGraph G Set.univ) m x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L y)
      (h : segmentAnchors G hloc γ n hdiam ep mid.1) =>
    ∃ ij : Fin (m+1) × Fin (J+1), tail.2.position ij.1.val = h.val (j ij.2)
  have hu := finite_threefold_event_or μ hμ B (fun tail mid h => C tail mid h ∨ D tail mid h)
  have hv := finite_threefold_event_or μ hμ C D
  have he := raw_anchor_early_collision_bound G hloc a γ n hdiam ep P hpos hsym hP hρ
    m L J x y pos neg hposD hnegD hxy
  have hn := raw_anchor_finite_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j neg P hpos hP L y
  rw [←raw_tail_integrate_anchor_event G hloc a γ n hdiam ep m L x y
    (fun _ h => ∃ st : Fin (J+1) × Fin (J+1), h.val (j st.1) = neg st.2)] at hn
  have ht := raw_tail_whole_suffix_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam ep j P hpos hP hρ m L x y
  simp only [tsum_fintype,Fintype.card_fin,Nat.cast_add,Nat.cast_one] at he hn ht ⊢
  have hr : earlyCollisionCost ‖P‖ J +
      ((((J:ℝ)+1)*((J:ℝ)+1)*Real.sqrt c*‖P‖^L) +
        ((J:ℝ)+1)*Real.sqrt c*‖P‖^L/(1-‖P‖)) =
      earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
    unfold suffixCollisionCost
    ring
  have hh := hu.trans ((add_le_add he (hv.trans (add_le_add hn ht))).trans_eq hr)
  apply le_trans ?_ hh
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro tail _
  apply Finset.sum_congr rfl
  intro mid _
  apply Finset.sum_congr rfl
  intro h _
  unfold firstEscapeCollision B C D μ
  split_ifs <;> rfl

end CombinedRawAvoidance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormalizedFirstEscape
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

theorem conditional_first_escape_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (hy : y ∈ vertexOrbit G (γ ep))
    (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
        segmentReturnMass G hloc a γ ep L y ≤
      2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  have hb := raw_first_escape_collision_bound G hloc a root weight Γ hΓ htr
    (fun r => (hw r).le) hw1 hcov c hc.le hmin γ n hdiam ep P hpos hsym hP hρ
    m L J x y pos neg j hposD hnegD hxy
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  rw [←segmentReturnMass_on_orbit G hloc a γ ep L y hy P hpos hP] at hq
  have htc : 0 < 2*c := mul_pos (by norm_num) hc
  have hqp : 0 < segmentReturnMass G hloc a γ ep L y := (one_div_pos.mpr htc).trans_le hq
  apply (div_le_iff₀ hqp).mpr
  apply hb.trans
  have hB : 0 ≤ earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L := by
    unfold earlyCollisionCost suffixCollisionCost
    have : 0 < 1-‖P‖ := sub_pos.mpr hρ
    positivity
  have h1 : 1 ≤ (2*c)*segmentReturnMass G hloc a γ ep L y := by
    exact (div_le_iff₀ htc).mp hq |>.trans_eq (mul_comm _ _)
  have hh := mul_le_mul_of_nonneg_right h1 hB
  nlinarith only [hh]

end NormalizedFirstEscape
end Percolation

 
namespace Percolation
section FirstEscapeChoiceOrder

 

theorem exists_first_escape_uniform_cutoffs (ρ c ε : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      2*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L) < ε := by
  have hδ : 0 < ε/(4*c) := div_pos hε (by positivity)
  obtain ⟨J₀,hJ₀⟩ := exists_earlyCollisionCutoff ρ hρ hρ1 (ε/(4*c)) hδ
  let J := max J₀ 1
  have hJ : 0 < J := lt_of_lt_of_le (by omega : 0 < 1) (le_max_right _ _)
  have he : earlyCollisionCost ρ J < ε/(4*c) := hJ₀ J (le_max_left _ _)
  have hel : 2*c*earlyCollisionCost ρ J < ε := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*c)).mp he
    nlinarith
  have ht : Filter.Tendsto
      (fun L : ℕ => 2*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L))
      Filter.atTop (nhds (2*c*earlyCollisionCost ρ J)) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul
      (suffixCollisionCost ρ c J)).const_add (earlyCollisionCost ρ J)
    have hh' := hh.const_mul (2*c)
    simpa only [mul_zero,add_zero] using hh'
  obtain ⟨L₀,hL₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hel))
  exact ⟨J,hJ,L₀,hL₀⟩

end FirstEscapeChoiceOrder
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralGeodesicSeparation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem graph_dist_aut (G : BondGraph V E) (hconn : Connected G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) :
    (openSimpleGraph G Set.univ).dist (a x) (a y) =
      (openSimpleGraph G Set.univ).dist x y := by
  have hreach (x y : V) : (openSimpleGraph G Set.univ).Reachable x y :=
    (conn_iff_reachable G Set.univ x y).mp (conn_univ_of_connected G hconn x y)
  obtain ⟨q,hq⟩ := (hreach x y).exists_walk_length_eq_dist
  obtain ⟨r,hr⟩ := (hreach (a x) (a y)).exists_walk_length_eq_dist
  have hq' := SimpleGraph.dist_le (q.map (autSimpleGraph G hab).toHom)
  have hr' := SimpleGraph.dist_le (r.map (autSimpleGraph G (isAut_symm G hab)).toHom)
  simp only [SimpleGraph.Walk.length_map,hq] at hq'
  change (openSimpleGraph G Set.univ).dist (a.symm (a x)) (a.symm (a y)) ≤ _ at hr'
  simp only [a.symm_apply_apply,SimpleGraph.Walk.length_map,hr] at hr'
  exact le_antisymm hq' hr'



end LiteralGeodesicSeparation
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ProjectionEvents
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_event_fiber_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (μ : α → ℝ) (B : β → Prop) [DecidablePred B] :
    (∑ a, if B (f a) then μ a else 0) =
      ∑ b, if B b then ∑ a, if f a = b then μ a else 0 else 0 := by
  calc
    _ = ∑ a, ∑ b, if B b then (if f a = b then μ a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      have hf : (fun b => if B b then (if f a = b then μ a else 0) else 0) =
          fun b => if f a = b then (if B (f a) then μ a else 0) else 0 := by
        funext b
        by_cases h : f a = b
        · subst b
          simp
        · simp [h]
      rw [hf]
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : B b <;> simp [h]

 

theorem rooted_label_raw_event_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (B : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x → Prop) [DecidablePred B] :
    (∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if B (rootedEscapeLabelRaw G J L m γ hγ x ξ) then
        escapeLabelProbability G hloc a γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) ≤
      (∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x,
        if B w then w.2.mass (walkKernel G hloc a) else 0)/(a^(J+J)*q) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let := finite_rootedEscapeLabels G hloc γ n hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let : Fintype {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} := Fintype.ofFinite _
  let : Fintype (RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x) := Fintype.ofFinite _
  rw [←tsum_indicator_div]
  simp only [tsum_fintype]
  rw [finite_event_fiber_sum]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : B w
  · simp only [hw,if_true]
    simpa only [tsum_fintype] using
      rooted_label_raw_projection_bound G hloc a ha hK J L m γ hγ n hdiam x hx q hq hqle w
  · simp only [hw,if_false,le_refl]

end ProjectionEvents
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FirstLabeledMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]


theorem labelFromCode_first_collision (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx
      (labelFromCode G hloc γ n hdiam center ep neg L m x c).1 =
    firstEscapeCollision G J m L (c.1.val neg) (c.1.val ep)
      (fun t => c.1.val (posIdx t)) (fun t => c.1.val (negIdx t)) suffixIdx
      c.2.2.2.1 c.2.1 c.2.2.1.val := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem raw_rooted_first_collision_marginal (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        ξ.1.mass (walkKernel G hloc a) else 0) =
    ∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
          ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
            if firstEscapeCollision G J m L (s.val neg) (s.val ep)
              (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
              tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a) else 0 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass,labelFromCode_first_collision]
  unfold RootedLabelCode at *
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  apply tsum_congr
  intro s
  rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
  have hh (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep)) :
      (∑' hh : Σ h : segmentAnchors G hloc γ n hdiam ep mid.1,
          RawFrom (openSimpleGraph G Set.univ) m (s.val neg) × RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if firstEscapeCollision G J m L (s.val neg) (s.val ep)
          (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx hh.2.1 mid hh.1.val then
          mid.2.mass (walkKernel G hloc a)*hh.2.1.2.mass (walkKernel G hloc a)*hh.2.2.2.mass (walkKernel G hloc a) else 0) =
      ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
        ∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
          if firstEscapeCollision G J m L (s.val neg) (s.val ep)
            (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a) else 0 := by
    rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_sigma]
    apply tsum_congr
    intro h
    rw [(summable_of_hasFiniteSupport (Set.toFinite _)).tsum_prod]
    apply tsum_congr
    intro tail
    split_ifs
    · simp only [tsum_mul_left,rawFrom_probability_sum G hloc a,mul_one]
      exact mul_comm _ _
    · simp only [tsum_zero]
  simp_rw [hh]
  simp only [tsum_fintype]
  conv_lhs =>
    arg 2
    intro mid
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end FirstLabeledMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section NormalizedMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_first_collision_probability_marginal (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (J L m : ℕ) (x : V)
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    (∑' s : segmentAnchors G hloc γ n hdiam center x,
      (∑' tail : RawFrom (openSimpleGraph G Set.univ) m (s.val neg),
        ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
          ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
            if firstEscapeCollision G J m L (s.val neg) (s.val ep)
              (fun t => s.val (posIdx t)) (fun t => s.val (negIdx t)) suffixIdx tail mid h.val then
              tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
                (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
          segmentReturnMass G hloc a γ ep L (γ ep)) /
      (segmentAnchors G hloc γ n hdiam center (γ center)).card := by
  simp only [escapeLabelProbability,tsum_indicator_div,tsum_div_const]
  rw [raw_rooted_first_collision_marginal G hloc a γ n hdiam center ep neg J L m x posIdx negIdx suffixIdx]
  ring

end NormalizedMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FullFirstEscapeBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 

theorem rooted_first_collision_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  rw [rooted_first_collision_probability_marginal G hloc a γ n hdiam center ep neg J L m x posIdx negIdx suffixIdx]
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam center (γ center)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  apply (div_le_iff₀ hN).mpr
  simp only [tsum_fintype]
  calc
    _ ≤ ∑ s : segmentAnchors G hloc γ n hdiam center x,
        2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
      apply Finset.sum_le_sum
      intro s _
      have hs := ((mem_segmentAnchors G hloc γ n hdiam center x s.val).mp s.property).1
      have hy : s.val ep ∈ vertexOrbit G (γ ep) := by
        obtain ⟨g,b,hg,he⟩ := hs
        rw [he]
        exact ⟨g,b,hg,rfl⟩
      obtain ⟨hp,hn,hxy⟩ := hsep s.val hs
      have hh := conditional_first_escape_collision_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
        c hc hmin γ n hdiam ep P hpos hsym hP hdiag hρ m L J (s.val neg) (s.val ep) hy
        (fun i => s.val (posIdx i)) (fun i => s.val (negIdx i)) suffixIdx hp hn hxy
      rw [segmentReturnMass_on_orbit G hloc a γ ep L (s.val ep) hy P hpos hP] at hh
      simpa only [tsum_fintype] using hh
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx]
      ring

end FullFirstEscapeBound
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CollisionNaturality
attribute [local instance] Classical.propDecidable Classical.decEq

namespace HoldingWalk
variable {W : Type*} {H : SimpleGraph V} {H' : SimpleGraph W}
theorem map_position (f : H →g H') {k : ℕ} {x y : V} (q : HoldingWalk H k x y) (i : ℕ) :
    (q.map f).position i = f (q.position i) := by
  induction q generalizing i with
  | nil => rfl
  | hold q ih => cases i <;> simp only [map,position,ih]
  | step h q ih => cases i <;> simp only [map,position,ih]
end HoldingWalk

theorem list_common_vertex_map_iff {W : Type*} (f : V → W) (hf : Function.Injective f)
    (l r : List V) :
    (∃ z, z ∈ l.map f ∧ z ∈ r.map f) ↔ ∃ z, z ∈ l ∧ z ∈ r := by
  constructor
  · rintro ⟨z,hz,hz'⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hz'
    have : y = x := hf he
    subst y
    exact ⟨x,hx,hy⟩
  · rintro ⟨z,hz,hz'⟩
    exact ⟨f z,List.mem_map.mpr ⟨z,hz,rfl⟩,List.mem_map.mpr ⟨z,hz',rfl⟩⟩

 
theorem labelFirstEscapeCollision_aut (G : BondGraph V E) (γ : I → V) (ep neg : I)
    (J L m : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx (EscapeLabel.autMap hab ξ) ↔
      labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ := by
  dsimp only [labelFirstEscapeCollision,firstEscapeCollision,EscapeLabel.autMap,Function.comp_apply,autSimpleGraph]
  simp only [HoldingWalk.map_vertices,HoldingWalk.map_position]
  change (((∃ s, a (ξ.first (posIdx s)) ∈ ξ.leftTail.2.vertices.map a) ∨
    (∃ s, a (ξ.first (negIdx s)) ∈ ξ.middle.vertices.map a)) ∨
    (∃ z, z ∈ ξ.leftTail.2.vertices.map a ∧ z ∈ ξ.middle.vertices.map a)) ∨
    ((∃ st : Fin (J+1) × Fin (J+1), a (ξ.last (suffixIdx st.1)) = a (ξ.first (negIdx st.2))) ∨
      (∃ ij : Fin (m+1) × Fin (J+1), a (ξ.leftTail.2.position ij.1.val) = a (ξ.last (suffixIdx ij.2)))) ↔ _
  rw [list_common_vertex_map_iff a a.injective]
  simp only [List.mem_map,Equiv.apply_eq_iff_eq]
  simp

end CollisionNaturality
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section BothEscapeEvents
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rootOrbitWeight_pos (G : BondGraph V E)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (hw : ∀ i, 0 < weight i)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x) (x : V) :
    0 < ∑ i, if root i ∈ vertexOrbit G x then weight i else 0 := by
  obtain ⟨r,g,hg,he⟩ := hcov x
  obtain ⟨b,hab⟩ := hΓ hg
  have hr : root r ∈ vertexOrbit G x := by
    refine ⟨g.symm,b.symm,isAut_symm G hab,?_⟩
    rw [←he,Equiv.symm_apply_apply]
  have hh : (if root r ∈ vertexOrbit G x then weight r else 0) ≤
      ∑ i, if root i ∈ vertexOrbit G x then weight i else 0 :=
    Finset.single_le_sum (f := fun i => if root i ∈ vertexOrbit G x then weight i else 0)
      (fun i _ => by split_ifs <;> first | exact (hw i).le | rfl) (Finset.mem_univ r)
  simpa only [ite_eq_left hr] using lt_of_lt_of_le (by simpa only [ite_eq_left hr] using hw r) hh

 

theorem rooted_escape_collision_reversal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0 := by
  have hh := rooted_escape_label_reversal G hloc a root weight Γ hΓ htr γ n hdiam center ep neg L m
    (rootOrbitWeight_pos G root weight Γ hΓ hw hcov (γ center))
    (fun ξ => if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ then (1:ℝ) else 0)
    (fun g b hab ξ => by rw [labelFirstEscapeCollision_aut G γ ep neg J L m posIdx negIdx suffixIdx hab ξ]) x hx
  simpa only [mul_ite,mul_one,mul_zero] using hh

end BothEscapeEvents
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section BothEscapeBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rooted_both_collision_probability_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep)) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
        labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hb := rooted_first_collision_probability_bound G hloc a root weight Γ hΓ htr hw hw1 hcov
    c hc hmin γ n hdiam center ep neg P hpos hsym hP hdiag hρ m L J x hx posIdx negIdx suffixIdx hsep
  have he := rooted_escape_collision_reversal G hloc a root weight Γ hΓ htr hw hcov
    γ n hdiam center ep neg m L J x hx posIdx negIdx suffixIdx
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}
  have hu := finite_weighted_event_or
    (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1)
    (fun ξ => escapeLabelProbability_nonneg G hloc a hK γ n hdiam center ep neg L m ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse)
  simp only [tsum_fintype] at hb he ⊢
  rw [←he] at hu
  linarith

end BothEscapeBound
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_SelectionBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
section BothEscapeChoiceOrder

 

theorem exists_both_escape_uniform_cutoffs (ρ c ε : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^L) < ε := by
  obtain ⟨J,hJ,L₀,hL₀⟩ := exists_first_escape_uniform_cutoffs ρ c (ε/2) hρ hρ1 hc (by positivity)
  refine ⟨J,hJ,L₀,fun L hL => ?_⟩
  have hh := hL₀ L hL
  linarith

end BothEscapeChoiceOrder
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section TailConditioning
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_event_of_tail_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (B : EscapeLabel G γ ep neg L m → Prop) (ε : ℝ)
    (hB : ∀ (s : segmentAnchors G hloc γ n hdiam center x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
      (h : segmentAnchors G hloc γ n hdiam ep mid.1),
      (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
          tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0) ≤ ε) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1 then ξ.1.mass (walkKernel G hloc a) else 0) ≤
      ε * ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
        ξ.1.mass (walkKernel G hloc a) := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq,←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  simp only [tsum_fintype,Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro mid _
  apply Finset.sum_le_sum
  intro h _
  have hh := hB s mid h
  simp only [tsum_fintype] at hh
  have ht : (∑ tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a)) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    simpa only [tsum_fintype,mul_one] using congrArg₂ (fun r t : ℝ => r*t)
      (rawFrom_probability_sum G hloc a m (s.val neg))
      (rawFrom_probability_sum G hloc a m (h.val neg))
  calc
    _ = mid.2.mass (walkKernel G hloc a) *
        ∑ tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
          if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
            tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tails _
      split_ifs <;> simp only [mul_zero,mul_assoc]
    _ ≤ mid.2.mass (walkKernel G hloc a)*ε := mul_le_mul_of_nonneg_left hh (mid.2.mass_nonneg _ hK)
    _ = _ := by
      simp only [mul_assoc,←Finset.mul_sum]
      rw [ht]
      ring

end TailConditioning
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section NormalizedTailConditioning
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_probability_of_tail_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ g ∈ Γ, g (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center)) 
    (B : EscapeLabel G γ ep neg L m → Prop) (ε : ℝ)
    (hB : ∀ (s : segmentAnchors G hloc γ n hdiam center x)
      (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
      (h : segmentAnchors G hloc γ n hdiam ep mid.1),
      (∑' tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg),
        if B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 then
          tails.1.2.mass (walkKernel G hloc a)*tails.2.2.mass (walkKernel G hloc a) else 0) ≤ ε) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1 then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤ ε := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hqp : 0 ≤ segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).le.trans hq
  let D := ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) *
    ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
      segmentReturnMass G hloc a γ ep L (γ ep)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hqp
  have hr := rooted_label_event_of_tail_bound G hloc a hK γ n hdiam center ep neg L m x B ε hB
  have hs := (rooted_label_probability_hasSum G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ n hdiam center ep neg L m x hx).tsum_eq
  have hd := div_le_div_of_nonneg_right hr hD
  have he : (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      ξ.1.mass (walkKernel G hloc a))/D = 1 := by
    simpa only [escapeLabelProbability,tsum_div_const,D] using hs
  simpa only [escapeLabelProbability,tsum_indicator_div,tsum_div_const,D,
    mul_div_assoc,he,mul_one] using hd

end NormalizedTailConditioning
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FullPotentialTests
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]


theorem labelFromCode_potential_failure (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (t : ℝ) (s : segmentAnchors G hloc γ n hdiam center x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
    (h : segmentAnchors G hloc γ n hdiam ep mid.1)
    (tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg)) :
    labelPotentialFailure G p γ ep neg L m F t
      (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1 ↔
      (t < ∑ b ∈ F s.val mid h.val, twoPoint G p tails.1.1 b) ∨
      (t < ∑ b ∈ F s.val mid h.val, twoPoint G p tails.2.1 b) := by
  rcases s with ⟨s,hs⟩
  rcases mid with ⟨z,mid⟩
  rcases h with ⟨h,hh⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 

theorem rooted_label_potential_failure_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if labelPotentialFailure G p γ ep neg L m F t ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*(N*Real.sqrt c*‖P‖^m)/t := by
  apply rooted_label_probability_of_tail_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ n hdiam center ep neg L m x hx
  intro s mid h
  simp only [labelFromCode_potential_failure]
  have hh := two_raw_tail_potential_failure G hloc a root weight htr hcov (fun r => (hw r).le) hw1
    c hc.le hmin P A hpos hP p hA m (s.val neg) (h.val neg) (F s.val mid h.val) t ht
  apply hh.trans
  gcongr
  exact hN s.val mid h.val

end FullPotentialTests
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CombinedSelectionEvents
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 

theorem rooted_label_collision_potential_failure_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (hρ : ‖P‖ < 1) (J : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep))
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if (labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
        labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse) ∨
        labelPotentialFailure G p γ ep neg L m F t ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
        2*(N*Real.sqrt c*‖P‖^m)/t := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hb := rooted_both_collision_probability_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hw hw1 hcov c hc hmin γ n hdiam center ep neg P hpos hsym hP hdiag hρ m L J x hx posIdx negIdx suffixIdx hsep
  have hp := rooted_label_potential_failure_bound G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA γ n hdiam center ep neg L m x hx F N hN t ht
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}
  have hu := finite_weighted_event_or
    (fun ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} =>
      escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1)
    (fun ξ => escapeLabelProbability_nonneg G hloc a hK γ n hdiam center ep neg L m ξ.1)
    (fun ξ => labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
      labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse)
    (fun ξ => labelPotentialFailure G p γ ep neg L m F t ξ.1)
  simp only [tsum_fintype] at hb hp ⊢
  exact hu.trans (add_le_add hb hp)

end CombinedSelectionEvents
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section QuantitativeSelectionMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem finite_weighted_success_lower {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∑ a, μ a = 1) (B : α → Prop) [DecidablePred B] (ε : ℝ)
    (hB : (∑ a, if B a then μ a else 0) ≤ ε) :
    1-ε ≤ ∑ a, if ¬B a then μ a else 0 := by
  have he : (∑ a, if ¬B a then μ a else 0) + (∑ a, if B a then μ a else 0) = 1 := by
    rw [←Finset.sum_add_distrib,←hμ]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : B a <;> simp only [h,not_true_eq_false,not_false_eq_true,if_true,if_false,zero_add,add_zero]
  linarith



end QuantitativeSelectionMass
end Percolation

 
namespace Percolation
section JointSelectionChoiceOrder

 

theorem exists_joint_collision_potential_cutoffs (ρ c d τ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hd : 0 ≤ d) (hτ : 0 < τ) :
    ∃ J : ℕ, 0 < J ∧ ∃ L₀ : ℕ, ∃ C₁ : ℝ, 0 < C₁ ∧ 1 < (-Real.log ρ)*C₁ ∧
      ∃ k₀ : ℕ, J+J+L₀ ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^(k-(J+J))) +
          2*((d+1)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) ≤ 3/8 := by
  obtain ⟨J,hJ,L₀,hL₀⟩ := exists_both_escape_uniform_cutoffs ρ c (1/8) hρ.le hρ1 hc (by norm_num)
  let A : ℝ := 2*(d+1)*Real.sqrt c/τ
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.sqrt_nonneg _)) hτ.le
  obtain ⟨C₁,hC₁,hlam,k₀,hk₀,hk⟩ := exists_uniform_logarithmic_tail_cutoff ρ A hρ hρ1 hA (J+J+L₀)
  refine ⟨J,hJ,L₀,C₁,hC₁,hlam,k₀,hk₀,fun k hk' R hR => ?_⟩
  have hL : L₀ ≤ k-(J+J) := by omega
  have hb := hL₀ (k-(J+J)) hL
  have hp := hk k hk' R hR
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have he : 2*((d+1)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) =
      A*((k:ℝ)+1)*R*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊ := by
    dsimp only [A]
    field_simp [hτ.ne',hRp.ne']
  rw [he]
  linarith

end JointSelectionChoiceOrder
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section SpineMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem labelFromCode_anchor_event (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (B : (I → V) → (I → V) → Prop)
    (s : segmentAnchors G hloc γ n hdiam center x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep))
    (h : segmentAnchors G hloc γ n hdiam ep mid.1)
    (tails : RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
      RawFrom (openSimpleGraph G Set.univ) m (h.val neg)) :
    B (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1.first
      (labelFromCode G hloc γ n hdiam center ep neg L m x ⟨s,mid,h,tails⟩).1.last ↔ B s.val h.val := by
  rcases s with ⟨s,hs⟩
  rcases mid with ⟨z,mid⟩
  rcases h with ⟨h,hh⟩
  obtain ⟨_,hhz⟩ := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
  subst z
  rfl

 
theorem rooted_label_anchor_event_marginal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (B : (I → V) → (I → V) → Prop)
    [∀ s h, Decidable (B s h)] :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if B ξ.1.first ξ.1.last then ξ.1.mass (walkKernel G hloc a) else 0) =
    ∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if B s.val h.val then mid.2.mass (walkKernel G hloc a) else 0 := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) := finite_openSimpleGraph_neighbors G hloc z
  let (k : ℕ) (z : V) : Fintype (RawFrom (openSimpleGraph G Set.univ) k z) := Fintype.ofFinite _
  let := finite_rootedEscapeLabels G hloc γ n hdiam center ep neg L m x
  let R := rootedLabelEquiv G hloc γ n hdiam center ep neg L m x
  rw [←R.symm.tsum_eq]
  simp only [R,rootedLabelEquiv,Equiv.coe_fn_symm_mk,labelFromCode_mass]
  unfold RootedLabelCode at *
  simp only [tsum_fintype,Fintype.sum_sigma,labelFromCode_anchor_event]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro mid _
  apply Finset.sum_congr rfl
  intro h _
  by_cases hb : B s.val h.val
  · simp only [hb,if_true,Fintype.sum_prod_type,mul_assoc,←Finset.mul_sum,←Finset.sum_mul]
    have hl := rawFrom_probability_sum G hloc a m (s.val neg)
    have hr := rawFrom_probability_sum G hloc a m (h.val neg)
    simp only [tsum_fintype] at hl hr
    rw [hl,hr]
    ring
  · simp only [hb,if_false,Finset.sum_const_zero]

end SpineMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section EndpointMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
theorem rooted_label_endpoint_marginal (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (S : Finset V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ S then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) =
    (∑' s : segmentAnchors G hloc γ n hdiam center x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if h.val center ∈ S then mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
      (((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ)*
        segmentReturnMass G hloc a γ ep L (γ ep)) := by
  simp only [escapeLabelProbability,tsum_indicator_div,tsum_div_const]
  rw [rooted_label_anchor_event_marginal G hloc a γ n hdiam center ep neg L m x (fun _ h => h center ∈ S)]
  ring

end EndpointMarginal
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section ActualEndpointSeparation
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 

theorem rooted_label_endpoint_hit_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (m L : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (S : Finset V) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ S then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(S.card:ℝ)*Real.sqrt c*‖P‖^L := by
  rw [rooted_label_endpoint_marginal G hloc a γ n hdiam center ep neg L m x S]
  have hN : 0 < ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((segmentAnchors_nonempty_iff G hloc γ n hdiam center (γ center)).mpr
      ⟨Equiv.refl V,Equiv.refl E,isAut_refl G,rfl⟩)
  have hq := segmentReturnMass_uniform_lower G hloc a root weight Γ hΓ htr hcov hw hw1 c hc hmin
    P hpos hsym hP hdiag γ ep L
  have hqp : 0 < segmentReturnMass G hloc a γ ep L (γ ep) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hc)).trans_le hq
  apply (div_le_iff₀ (mul_pos hN hqp)).mpr
  have hb (s : segmentAnchors G hloc γ n hdiam center x) :
      (∑' mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if h.val center ∈ S then mid.2.mass (walkKernel G hloc a)/
            (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) ≤
      (S.card:ℝ)*Real.sqrt c*‖P‖^L := by
    have hh := raw_anchor_finite_collision_bound G hloc a root weight Γ hΓ htr (fun r => (hw r).le)
      hw1 hcov c hc.le hmin γ n hdiam ep (fun _ : PUnit.{1} => center) (fun z : S => z.val)
      P hpos hP L (s.val ep)
    simpa [Subtype.exists] using hh
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hb s)
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at hu ⊢
  rw [segmentAnchors_card_on_orbit G hloc γ n hdiam center x hx] at hu
  apply hu.trans
  have he : 1 ≤ 2*c*segmentReturnMass G hloc a γ ep L (γ ep) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*c)).mp hq
    nlinarith
  have hp : 0 ≤ ((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ)*
      (S.card:ℝ)*Real.sqrt c*‖P‖^L := by positivity
  nlinarith [mul_le_mul_of_nonneg_left he hp]

end ActualEndpointSeparation
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section EndpointBallBound
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I] {ι : Type*} [Fintype ι]

 
theorem rooted_label_endpoint_ball_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (center ep neg : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (m L : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (r : ℕ) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if ξ.1.last center ∈ reachBall G x r then escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      2*c*(((d+1)^r:ℕ):ℝ)*Real.sqrt c*‖P‖^L := by
  have hh := rooted_label_endpoint_hit_bound G hloc a root weight Γ hΓ htr hw hw1 hcov c hc hmin
    γ n hdiam center ep neg P hpos hsym hP hdiag m L x hx (finite_reachBall hloc x r).toFinset
  have hb : ((finite_reachBall hloc x r).toFinset.card : ℝ) ≤ (((d+1)^r:ℕ):ℝ) := by
    exact_mod_cast (by
      simpa only [←Set.ncard_eq_toFinset_card] using reachBall_ncard_le_pow G hloc d hd x r)
  calc
    _ ≤ 2*c*((finite_reachBall hloc x r).toFinset.card:ℝ)*Real.sqrt c*‖P‖^L := by
      simpa only [Set.Finite.mem_toFinset] using hh
    _ ≤ _ := by gcongr

end EndpointBallBound
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_PathSelection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

namespace HoldingWalk
variable {H : SimpleGraph V}

theorem mem_vertices_append {k l : ℕ} {x y z b : V}
    (w : HoldingWalk H k x y) (v : HoldingWalk H l y z) :
    b ∈ (w.append v).vertices ↔ b ∈ w.vertices ∨ b ∈ v.vertices := by
  induction w with
  | nil x =>
    have hx : x ∈ v.vertices := by simpa using v.position_mem_vertices 0
    simp only [append, vertices, List.mem_singleton]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun he => he ▸ hx) id⟩
  | hold w ih => simp only [append, vertices, List.mem_cons, ih, or_assoc]
  | step h w ih => simp only [append, vertices, List.mem_cons, ih, or_assoc]

theorem mem_vertices_fromPositions (k : ℕ) (f : Fin (k+1) → V)
    (h : ∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) (b : V) :
    b ∈ (fromPositions k f h).vertices ↔ ∃ i, f i = b := by
  rw [mem_vertices_iff_position]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i,by omega⟩, (position_fromPositions k f h i hi).symm.trans he⟩
  · rintro ⟨i,hi⟩
    exact ⟨i.val,by omega,(position_fromPositions k f h i.val (by omega)).trans hi⟩

end HoldingWalk


theorem positiveStem_vertices (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) (z : V) :
    z ∈ (positiveStem H J s hs).vertices ↔ ∃ i : Fin (J+1), s ⟨J+i.val,by omega⟩ = z := by
  exact HoldingWalk.mem_vertices_fromPositions J _ _ z

theorem negativeStem_vertices (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) (z : V) :
    z ∈ (negativeStem H J s hs).vertices ↔ ∃ i : Fin (J+1), s ⟨i.val,by omega⟩ = z := by
  let w := HoldingWalk.fromPositions J (fun i : Fin (J+1) => s ⟨i.val,by omega⟩)
    (fun i : Fin J => hs ⟨i.val,by omega⟩)
  have he : z ∈ w.reverse.vertices ↔ z ∈ w.vertices := by
    rw [HoldingWalk.vertices_reverse, List.mem_reverse]
  exact he.trans (HoldingWalk.mem_vertices_fromPositions J _ _ z)


theorem segmentOrbit_injective {I : Type*} (G : BondGraph V E) (γ s : I → V)
    (hγ : Function.Injective γ) (hs : s ∈ segmentOrbit G γ) : Function.Injective s := by
  obtain ⟨a,b,hab,rfl⟩ := hs
  exact a.injective.comp hγ

 

theorem labelLeftEscape_raw_intersection (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m)
    (hgood : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ)
    (z : V) (hz : z ∈ (labelLeftEscape G J L m γ hγ ξ).vertices)
    (hr : z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices) :
    z = ξ.first (segmentCenter J) := by
  have hfirst := segmentOrbit_injective G γ ξ.first hinj ξ.first_mem
  have hfail := hgood
  unfold labelFirstEscapeCollision firstEscapeCollision at hfail
  have hraw : (∃ i : Fin (J+1), ξ.first (segmentPositiveIndex J i) = z) ∨
      z ∈ ξ.middle.vertices ∨ (∃ i : Fin (J+1), ξ.last (segmentPositiveIndex J i) = z) := by
    simpa only [escapeLabelRaw, HoldingWalk.mem_vertices_append,
      HoldingWalk.vertices_reverse, List.mem_reverse, positiveStem_vertices,
      segmentPositiveIndex] using hr
  have hleft : (∃ i : Fin (J+1), ξ.first (segmentNegativeIndex J i) = z) ∨
      z ∈ ξ.leftTail.2.vertices := by
    simpa only [labelLeftEscape, HoldingWalk.mem_vertices_append,
      negativeStem_vertices, segmentNegativeIndex] using hz
  rcases hleft with ⟨i,hi⟩ | ht
  · rcases hraw with ⟨j,hj⟩ | hm | ⟨j,hj⟩
    · have he := congrArg Fin.val (hfirst (hi.trans hj.symm))
      change i.val = J+j.val at he
      have hiJ : i.val = J := by omega
      rw [←hi]
      congr 1
      apply Fin.ext
      exact hiJ
    · exact False.elim (hfail (Or.inl (Or.inl (Or.inr ⟨i,by simpa only [hi] using hm⟩))))
    · exact False.elim (hfail (Or.inr (Or.inl ⟨(j,i),hj.trans hi.symm⟩)))
  · rcases hraw with ⟨i,hi⟩ | hm | ⟨i,hi⟩
    · exact False.elim (hfail (Or.inl (Or.inl (Or.inl ⟨i,by simpa only [hi] using ht⟩))))
    · exact False.elim (hfail (Or.inl (Or.inr ⟨z,ht,hm⟩)))
    · obtain ⟨l,hl,he⟩ := ξ.leftTail.2.mem_vertices_iff_position.mp ht
      exact False.elim (hfail (Or.inr (Or.inr ⟨(⟨l,by omega⟩,i),he.trans hi.symm⟩)))

 
theorem labelRaw_reverse_vertices (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (z : V) :
    z ∈ (escapeLabelRaw G J L m γ hγ ξ.reverse).vertices ↔
      z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices := by
  simp only [escapeLabelRaw, HoldingWalk.mem_vertices_append,
    HoldingWalk.vertices_reverse, List.mem_reverse, EscapeLabel.reverse]
  tauto

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem interior_mem_raw (w : RawCorridor G k) {z : V} (hz : z ∈ w.interior) :
    z ∈ w.2.2.vertices := by
  have hp : z ∈ w.path.support := List.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1
  exact w.2.2.erase_support.subset hp


theorem coe_neighborhood (hloc : LocallyFinite G) (w : RawCorridor G k) :
    (w.neighborhood hloc : Set V) = closedBondNeighborhood G (w.interior : Set V) :=
  (closedBondNeighborhood_finset G hloc w.interior).symm


end RawCorridor



theorem mem_spineVertices (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (z : V) :
    z ∈ spineVertices G J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last ↔
      z ∈ (escapeLabelRaw G J L m γ hγ ξ).vertices := by
  simp only [spineVertices, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, Function.comp_apply, List.mem_toFinset, escapeLabelRaw,
    HoldingWalk.mem_vertices_append, HoldingWalk.vertices_reverse, List.mem_reverse,
    positiveStem_vertices, segmentPositiveIndex]
  tauto

theorem labelCorridor_neighborhood_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    (labelCorridor G J L m γ hγ ξ).neighborhood hloc ⊆
      spineNeighborhood G hloc J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last := by
  have hi : (labelCorridor G J L m γ hγ ξ).interior ⊆
      spineVertices G J L ξ.first ⟨ξ.last (Fin.last (J+J)),ξ.middle⟩ ξ.last := by
    intro z hz
    exact (mem_spineVertices G J L m γ hγ ξ z).mpr
      ((labelCorridor G J L m γ hγ ξ).interior_mem_raw hz)
  exact Finset.union_subset_union hi (Finset.biUnion_subset_biUnion_of_subset_left _ hi)

theorem neighborhood_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (W : Finset V) :
    (W ∪ W.biUnion (neighbors G hloc)).card ≤ (d+1)*W.card := by
  have hb : (W.biUnion (neighbors G hloc)).card ≤ W.card*d :=
    Finset.card_biUnion_le_card_mul _ _ _
      (fun x _ => (neighbors_card_le_degree G hloc x).trans (hd x))
  calc
    _ ≤ W.card + (W.biUnion (neighbors G hloc)).card := Finset.card_union_le _ _
    _ ≤ W.card + W.card*d := Nat.add_le_add_left hb _
    _ = _ := by ring

theorem spineVertices_card_le (G : BondGraph V E) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) :
    (spineVertices G J L s mid h).card ≤ ((J+L)+J)+3 := by
  have h₁ : (Finset.univ.image (s ∘ segmentPositiveIndex J)).card ≤ J+1 :=
    (Finset.card_image_le).trans (by simp)
  have h₂ : mid.2.vertices.toFinset.card ≤ L+1 :=
    (List.toFinset_card_le _).trans (le_of_eq mid.2.length_vertices)
  have h₃ : (Finset.univ.image (h ∘ segmentPositiveIndex J)).card ≤ J+1 :=
    (Finset.card_image_le).trans (by simp)
  have hauto := (Finset.card_union_le
    (Finset.univ.image (s ∘ segmentPositiveIndex J)) mid.2.vertices.toFinset)
  have hauto' := (Finset.card_union_le
    (Finset.univ.image (s ∘ segmentPositiveIndex J) ∪ mid.2.vertices.toFinset)
    (Finset.univ.image (h ∘ segmentPositiveIndex J)))
  unfold spineVertices
  omega

theorem spineNeighborhood_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) :
    ((spineNeighborhood G hloc J L s mid h).card : ℝ) ≤
      (3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1) := by
  have hn := neighborhood_card_le G hloc d hd (spineVertices G J L s mid h)
  have hs := spineVertices_card_le G J L s mid h
  have hb : (spineNeighborhood G hloc J L s mid h).card ≤ (d+1)*(((J+L)+J)+3) :=
    hn.trans (Nat.mul_le_mul_left _ hs)
  have hb' : ((spineNeighborhood G hloc J L s mid h).card : ℝ) ≤
      ((d:ℝ)+1)*((((J+L)+J):ℕ)+3) := by exact_mod_cast hb
  have hk : (0:ℝ) ≤ (((J+L)+J):ℕ) := Nat.cast_nonneg _
  nlinarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d]

 

theorem selected_of_good_label (G : BondGraph V E) (hloc : LocallyFinite G)
    (J L m : ℕ) (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) (p : unitInterval) (t : ℝ)
    (hleft : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ)
    (hright : ¬labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
      (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.reverse)
    (hdist : ξ.last (segmentCenter J) ∉ reachBall G (ξ.first (segmentCenter J)) 2)
    (hpot : ¬labelPotentialFailure G p γ (Fin.last (J+J)) 0 L m
      (spineNeighborhood G hloc J L) t ξ) :
    (labelCorridor G J L m γ hγ ξ).Selected hloc p (J+m) t := by
  let w := labelCorridor G J L m γ hγ ξ
  have hlength : 3 ≤ w.path.length := by
    by_contra h
    have hx : w.endpoint ∈ reachBall G w.base w.path.length := by
      simpa only [Nat.zero_add] using walk_mem_reachBall G Set.univ w.path 0 rfl
    exact hdist (reachBall_mono_local G w.base (by omega : w.path.length ≤ 2) hx)
  have hn := labelCorridor_neighborhood_subset G hloc J L m γ hγ ξ
  have hp := not_or.mp hpot
  have hp₁ : (∑ b ∈ w.neighborhood hloc, twoPoint G p ξ.leftTail.1 b) ≤ t := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hn (fun b _ _ => twoPoint_nonneg G p _ b))
    exact le_of_not_gt hp.1
  have hp₂ : (∑ b ∈ w.neighborhood hloc, twoPoint G p ξ.rightTail.1 b) ≤ t := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hn (fun b _ _ => twoPoint_nonneg G p _ b))
    exact le_of_not_gt hp.2
  refine ⟨hlength, ?_, ?_⟩
  · let e := labelLeftEscape G J L m γ hγ ξ
    refine ⟨ξ.leftTail.1, e.erase, e.erase_isPath, ?_, ?_, hp₁⟩
    · exact e.erase_length.trans (by omega)
    · intro z hz hzI
      have hr := w.interior_mem_raw hzI
      have he := labelLeftEscape_raw_intersection G J L m γ hinj hγ ξ hleft z
        (e.erase_support.subset hz) hr
      change z = w.base at he
      apply w.base_not_interior
      simpa only [he] using hzI
  · let e := labelLeftEscape G J L m γ hγ ξ.reverse
    refine ⟨ξ.rightTail.1, e.erase, e.erase_isPath, ?_, ?_, hp₂⟩
    · exact e.erase_length.trans (by omega)
    · intro z hz hzI
      have hr := w.interior_mem_raw hzI
      have he := labelLeftEscape_raw_intersection G J L m γ hinj hγ ξ.reverse hright z
        (e.erase_support.subset hz) ((labelRaw_reverse_vertices G J L m γ hγ ξ z).mpr hr)
      change z = w.endpoint at he
      apply w.endpoint_not_interior
      simpa only [he] using hzI

end EscapeGeometry
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SelectedLabelMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem rooted_selected_label_mass_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (J L m : ℕ) (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) (J+J))
    (x : V) (hx : x ∈ vertexOrbit G (γ (segmentCenter J))) (hρ : ‖P‖ < 1)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (segmentPositiveIndex J i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s (Fin.last (J+J))) (s (segmentNegativeIndex J i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (Fin.last (J+J))))
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (t : ℝ) (ht : 0 < t) :
    1 - (4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
      2*((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)*Real.sqrt c*‖P‖^m)/t +
      2*c*(((d+1)^2:ℕ):ℝ)*Real.sqrt c*‖P‖^L) ≤
    ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if (labelCorridor G J L m γ hγ ξ.1).Selected hloc p (J+m) t then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0 := by
  let F := spineNeighborhood G hloc J L
  let μ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1
  let B₁ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    (labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
        (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.1 ∨
      labelFirstEscapeCollision G γ (Fin.last (J+J)) 0 J L m
        (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) ξ.1.reverse) ∨
      labelPotentialFailure G p γ (Fin.last (J+J)) 0 L m F t ξ.1
  let B₂ := fun ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x} =>
    ξ.1.last (segmentCenter J) ∈ reachBall G x 2
  have hb := rooted_label_collision_potential_failure_bound G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x hx hρ
    J (segmentPositiveIndex J) (segmentNegativeIndex J) (segmentPositiveIndex J) hsep F
    ((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)) (spineNeighborhood_card_le G hloc d hd J L) t ht
  have he := rooted_label_endpoint_ball_bound G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hw hw1 hcov c hc hmin γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0
    P hpos hsym hP hdiag m L x hx d hd 2
  have hs := (rooted_label_probability_hasSum G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ (J+J) hdiam
    (segmentCenter J) (Fin.last (J+J)) 0 L m x hx).tsum_eq
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  let := finite_rootedEscapeLabels G hloc γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m x
  let := Fintype.ofFinite {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}
  have hμ (ξ) : 0 ≤ μ ξ := escapeLabelProbability_nonneg G hloc a hK γ (J+J) hdiam
    (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1
  simp only [tsum_fintype] at hs hb he ⊢
  have hu := (finite_weighted_event_or μ hμ B₁ B₂).trans (add_le_add hb he)
  have hl := finite_weighted_success_lower μ hs (fun ξ => B₁ ξ ∨ B₂ ξ) _ hu
  apply hl.trans
  apply Finset.sum_le_sum
  intro ξ _
  by_cases h : B₁ ξ ∨ B₂ ξ
  · simp only [h,not_true_eq_false,if_false]
    split_ifs <;> first | exact hμ ξ | rfl
  · have h₁ := not_or.mp (not_or.mp h).1
    have h₂ := not_or.mp h₁.1
    have hdist : ξ.1.last (segmentCenter J) ∉ reachBall G (ξ.1.first (segmentCenter J)) 2 := by
      simpa only [ξ.2] using (not_or.mp h).2
    have hsel := selected_of_good_label G hloc J L m γ hinj hγ ξ.1 p t h₂.1 h₂.2 hdist h₁.2
    simp only [h,not_false_eq_true,hsel,if_true]
    exact le_rfl

end SelectedLabelMass
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SelectedRawMass
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootedEscapeLabelRaw_corridor (G : BondGraph V E) (J L m : ℕ)
    (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    (⟨x,rootedEscapeLabelRaw G J L m γ hγ x ξ⟩ : RawCorridor G ((J+L)+J)) =
      labelCorridor G J L m γ hγ ξ.1 := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  rfl

 

theorem selected_raw_mass_of_label_mass (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (ha : 0 < a) (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) (J+J)) (x : V)
    (hx : x ∈ vertexOrbit G (γ (segmentCenter J)))
    (q : ℝ) (hq : 0 < q) (hqle : q ≤ segmentReturnMass G hloc a γ (Fin.last (J+J)) L (γ (Fin.last (J+J))))
    (p : unitInterval) (t b : ℝ)
    (hb : b ≤ ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if (labelCorridor G J L m γ hγ ξ.1).Selected hloc p (J+m) t then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0) :
    b*(a^(J+J)*q) ≤ ∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x,
      if RawCorridor.Selected hloc p (J+m) t (⟨x,w⟩ : RawCorridor G ((J+L)+J)) then
        w.2.mass (walkKernel G hloc a) else 0 := by
  have hh := rooted_label_raw_event_bound G hloc a ha hK J L m γ hγ (J+J) hdiam x hx
    q hq hqle (fun w => RawCorridor.Selected hloc p (J+m) t (⟨x,w⟩ : RawCorridor G ((J+L)+J)))
  simp only [rootedEscapeLabelRaw_corridor] at hh
  exact (le_div_iff₀ (mul_pos (pow_pos ha _) hq)).mp (hb.trans hh)

end SelectedRawMass

section FullSelectionCutoffs
 

theorem exists_full_selection_cutoffs (ρ c d τ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hd : 0 ≤ d) (hτ : 0 < τ) :
    ∃ J : ℕ, 0 < J ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ k₀ : ℕ, J+J ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        4*c*(earlyCollisionCost ρ J + suffixCollisionCost ρ c J*ρ^(k-(J+J))) +
          2*((3*d+3)*((k:ℝ)+1)*Real.sqrt c*ρ^⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊)/(τ/R) +
          2*c*(d+1)^2*Real.sqrt c*ρ^(k-(J+J)) ≤ 1/2 := by
  obtain ⟨J,hJ,L₀,C₁,hC₁,_,k₀,hk₀,hk⟩ :=
    exists_joint_collision_potential_cutoffs ρ c (3*d+2) τ hρ hρ1 hc (by linarith) hτ
  have ht : Filter.Tendsto (fun L : ℕ => 2*c*(d+1)^2*Real.sqrt c*ρ^L) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul
      (2*c*(d+1)^2*Real.sqrt c)
  obtain ⟨L₁,hL₁⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1/8 by norm_num)))
  refine ⟨J,hJ,C₁,hC₁,max k₀ (J+J+L₁),by omega,fun k hk' R hR => ?_⟩
  have h₁ := hk k (le_trans (le_max_left _ _) hk') R hR
  have h₂ := hL₁ (k-(J+J)) (by omega)
  have he : 3*d+2+1 = 3*d+3 := by ring
  rw [he] at h₁
  linarith
end FullSelectionCutoffs
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FullPathSelection
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem exists_selected_path_mass [Countable V] [Countable E] [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (τ : ℝ) (hτ : 0 < τ) :
    ∃ J : ℕ, ∃ C₁ : ℝ, ∃ k₀ : ℕ, ∃ b : ℝ,
      0 < J ∧ 0 < C₁ ∧ 3 ≤ k₀ ∧ 0 < b ∧
      ∀ p : unitInterval, (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        b ≤ rawPathAverage G (walkKernel G hloc a) k root weight
          (fun w => if w.Selected hloc p (J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊) (τ/R) then 1 else 0) := by
  let x₀ : V := Classical.arbitrary V
  have hρpos : 0 < ‖P‖ := by
    have hh := (hdiag x₀).trans ((Complex.re_le_norm _).trans (matrixCoeff_norm_le P x₀ x₀))
    linarith
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  obtain ⟨J,hJ,C₁,hC₁,k₀,hJk,hcut⟩ := exists_full_selection_cutoffs ‖P‖ c d τ hρpos hρ hc (Nat.cast_nonneg d) hτ
  obtain ⟨y,q,hqN,hq⟩ := exists_geodesic_length G hloc hconn x₀ (J+J)
  let γ := geodesicSegment G q (J+J)
  have hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ) :=
    fun i => geodesicSegment_adj G q (J+J) hqN i.val i.isLt
  have hinj : Function.Injective γ := geodesicSegment_injective G q (J+J) hqN hq
  have hdiam := geodesicSegment_diameter G q (J+J) hqN
  have hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (segmentPositiveIndex J i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s (Fin.last (J+J))) (s (segmentNegativeIndex J i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (Fin.last (J+J))) := by
    rintro s ⟨g,e,hge,rfl⟩
    constructor
    · intro i
      change J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert 0)) (g (q.getVert (J+i.val)))
      rw [graph_dist_aut G hconn hge,geodesic_getVert_dist _ q hq 0 (J+i.val) (by omega) (by omega)]
      omega
    constructor
    · intro i
      change J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert (J+J))) (g (q.getVert i.val))
      rw [graph_dist_aut G hconn hge,SimpleGraph.dist_comm,
        geodesic_getVert_dist _ q hq i.val (J+J) (by omega) (by omega)]
      omega
    · change 2*J ≤ (openSimpleGraph G Set.univ).dist (g (q.getVert 0)) (g (q.getVert (J+J)))
      rw [graph_dist_aut G hconn hge,geodesic_getVert_dist _ q hq 0 (J+J) (by omega) (by omega)]
      omega
  obtain ⟨i,g,hg,hgx⟩ := hcov (γ (segmentCenter J))
  obtain ⟨e,he⟩ := hg
  have hx : root i ∈ vertexOrbit G (γ (segmentCenter J)) :=
    ⟨g.symm,e.symm,isAut_symm G he,by rw [←hgx,g.symm_apply_apply]⟩
  let b : ℝ := weight i * ((1/2)*(a^(J+J)*(1/(2*c))))
  have hb : 0 < b := mul_pos (hw i) (mul_pos (by norm_num)
    (mul_pos (pow_pos ha _) (by positivity)))
  refine ⟨J,C₁,max k₀ 3,b,hJ,hC₁,le_max_right _ _,hb,?_⟩
  intro p _hpnear hp k hk R hR
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hJk' : J+J ≤ k := hJk.trans hk₀
  obtain ⟨L,rfl⟩ : ∃ L : ℕ, (J+L)+J = k := ⟨k-(J+J),by omega⟩
  let m' := ⌈C₁*Real.log ((((((J+L)+J):ℕ):ℝ)+1)*R)⌉₊
  obtain ⟨A,hA⟩ := operatorBounded_of_lt_pc G hloc hqt p hp
  have hcost := hcut ((J+L)+J) hk₀ R hR
  have hL : (J+L)+J-(J+J) = L := by omega
  rw [hL] at hcost
  have hcost' :
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
      2*((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)*Real.sqrt c*‖P‖^m')/(τ/R) +
      2*c*(((d+1)^2:ℕ):ℝ)*Real.sqrt c*‖P‖^L ≤ 1/2 := by
    simpa only [m',Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hcost
  have hl := rooted_selected_label_mass_lower G hloc a root weight htr hcov hw hw1 c hc hmin
    P A hpos hsym hP hdiag p hA J L m' γ hinj hγ hdiam (root i) hx hρ hsep d hd (τ/R)
    (div_pos hτ (lt_of_lt_of_le zero_lt_one hR))
  have hhalf : (1/2:ℝ) ≤ ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m' // ξ.first (segmentCenter J) = root i},
      if (labelCorridor G J L m' γ hγ ξ.1).Selected hloc p (J+m') (τ/R) then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m' ξ.1 else 0 := by
    linarith
  have hqreturn := segmentReturnMass_uniform_lower G hloc a root weight (vertexAut G) (Set.Subset.refl _)
    htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag γ (Fin.last (J+J)) L
  have hmraw := selected_raw_mass_of_label_mass G hloc a ha hK J L m' γ hγ hdiam (root i) hx
    (1/(2*c)) (by positivity) hqreturn p (τ/R) (1/2) hhalf
  have hroot := mul_le_mul_of_nonneg_left hmraw (hw i).le
  apply hroot.trans
  unfold rawPathAverage
  have hall (r : ι) : 0 ≤ weight r * ∑' w : RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) (root r),
      w.2.mass (walkKernel G hloc a) *
        (if RawCorridor.Selected hloc p (J+m') (τ/R) ⟨root r,w⟩ then 1 else 0) := by
    apply mul_nonneg (hw r).le
    apply tsum_nonneg
    intro w
    apply mul_nonneg (w.2.mass_nonneg _ hK)
    split_ifs <;> norm_num
  have hi := Finset.single_le_sum (s := Finset.univ) (fun r _ => hall r) (Finset.mem_univ i)
  simpa only [mul_ite,mul_one,mul_zero] using hi

end FullPathSelection
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_FiniteScale
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deformed susceptibility, finite-scale estimates and the Riccati contradiction. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section EscapeSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

omit [Countable V] [Countable E] [Nonempty V] in
 

theorem deformed_move_of_walk (G : BondGraph V E) (hloc : LocallyFinite G)
    (a C : ℝ) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmove : ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b)
    (D : Set V) (b z : V) (q : (openSimpleGraph G Set.univ).Walk b z)
    (j : ℕ) (hj : q.length ≤ j) (hD : ∀ x ∈ q.support, x ∈ D) :
    Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^j *
      deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t D b := by
  obtain ⟨l,hl,he,_⟩ := walk_lift_bonds G Set.univ q
  have hlen : l.length = q.length := by
    have hh := congrArg List.length he
    simpa only [List.length_map,SimpleGraph.Walk.length_edges] using hh
  have hle : l.length ≤ j := hlen.trans_le hj
  have hcomp := hmove D b z l (hD b q.start_mem_support) hl (by
    intro e hel x hxe
    exact hD x (SimpleGraph.Walk.mem_support_of_mem_edges
      (he ▸ List.mem_map_of_mem hel) hxe))
  have he' : Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ)))) ≤
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (Real.exp_pos _).le) (neg_nonpos.mpr ht)
  have hpw : (p:ℝ)^j ≤ (p:ℝ)^l.length := pow_le_pow_of_le_one p.2.1 p.2.2 hle
  exact (mul_le_mul_of_nonneg_right (mul_le_mul he' hpw (pow_nonneg p.2.1 _) (Real.exp_pos _).le)
    (deformedSusceptibility_nonneg G _ p k t D z)).trans hcomp

 
theorem deformedSusceptibility_delete_interior (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (w : RawCorridor G k) (x : V) :
    deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x -
      maxSusceptibility G p * (∑ z ∈ w.neighborhood hloc, twoPoint G p x z) ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ x := by
  have hh := deformedSusceptibility_deletion G hloc hqt _ hP p hp k t ht Set.univ (w.interior : Set V) x
  rw [←w.coe_neighborhood hloc,Finset.tsum_subtype'] at hh
  have he : Set.univ \ (w.interior : Set V) = (w.interior : Set V)ᶜ := by ext z; simp
  rw [he] at hh
  exact hh

 

theorem selected_retained_product_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (j : ℕ) (s C cf χ : ℝ) (hcf : 0 ≤ cf) (hχ : 0 ≤ χ)
    (hrow : ∀ x, cf*χ ≤ deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x)
    (hcost : maxSusceptibility G p*s ≤ (cf/2)*χ)
    (hmove : ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b)
    (w : RawCorridor G k) (hw : w.Selected hloc p j s) :
    Real.exp (-2*t*(j:ℝ)*Real.exp (C*(k:ℝ))) * (p:ℝ)^(2*j) * ((cf/2)*χ)^2 ≤
      retainedSusceptibilityProduct G (walkKernel G hloc a) p t w := by
  have hx (x : V) (he : w.HasEscape hloc p j s x) :
      Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ))))*(p:ℝ)^j*((cf/2)*χ) ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ x := by
    obtain ⟨z,q,_hq,hj,havoid,hs⟩ := he
    have hd := deformedSusceptibility_delete_interior G hloc hqt a hP p hp k t ht w z
    have hδ : (cf/2)*χ ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ z := by
      have hb := mul_le_mul_of_nonneg_left hs (zero_le_one.trans (maxSusceptibility_one_le G hloc hqt p hp))
      have hr := hrow z
      linarith
    exact (mul_le_mul_of_nonneg_left hδ
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg p.2.1 _))).trans
        (deformed_move_of_walk G hloc a C p k t ht hmove (w.interior : Set V)ᶜ x z q j hj havoid)
  have h₁ := hx w.base hw.2.1
  have h₂ := hx w.endpoint hw.2.2
  have hfactor : 0 ≤ Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ))))*(p:ℝ)^j*((cf/2)*χ) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg p.2.1 _))
      (mul_nonneg (div_nonneg hcf (by norm_num)) hχ)
  have hh := mul_le_mul h₁ h₂ hfactor
    (deformedSusceptibility_nonneg G _ p k t (w.interior : Set V)ᶜ w.base)
  rw [retainedSusceptibilityProduct,ite_eq_left hw.1]
  apply le_trans (le_of_eq ?_) hh
  have he : -2*t*(j:ℝ)*Real.exp (C*(k:ℝ)) =
      -t*((j:ℝ)*Real.exp (C*(k:ℝ))) + -t*((j:ℝ)*Real.exp (C*(k:ℝ))) := by ring
  rw [he,Real.exp_add,show 2*j=j+j by omega,pow_add]
  ring

end EscapeSusceptibility
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedRetention
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

omit [Countable V] [Countable E] [Nonempty V] in
theorem averagedDeformedSusceptibility_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (t : ℝ) :
    0 ≤ averagedDeformedSusceptibility G P p k root weight t :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (deformedSusceptibility_nonneg G P p k t Set.univ (root i)))

omit [Countable V] [Countable E] [Nonempty V] in
theorem deformedKernel_symm (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) :
    deformedKernel G P p k t D x y = deformedKernel G P p k t D y x := by
  simp only [deformedKernel,deformedConnection_symm G P p k t D _ x y]

omit [Nonempty V] in
 

theorem deformed_row_le_root_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (p : unitInterval) (k : ℕ) (t : ℝ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i) (x : V) :
    deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x ≤
      c*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
  obtain ⟨i,g,⟨e,he⟩,rfl⟩ := hcov x
  rw [deformedSusceptibility_aut G he _ (walkKernel_covariant G hloc a he)]
  simp only [Set.preimage_univ]
  have hs := deformedSusceptibility_nonneg G (walkKernel G hloc a) p k t Set.univ
  have hi := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun r => weight r * deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root r))
    (fun r _ => mul_nonneg (hw r) (hs (root r))) (Finset.mem_univ i)
  have hi' := mul_le_mul_of_nonneg_left hi hc
  have hh := mul_le_mul_of_nonneg_right (hmin i) (hs (root i))
  change _ ≤ c*∑ r, weight r * deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root r)
  nlinarith

 

theorem deformed_norm_le_root_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (B : Hilbert V →L[ℂ] Hilbert V)
    (hB : ∀ x y, matrixCoeff B x y = (deformedKernel G (walkKernel G hloc a) p k t Set.univ x y : ℂ)) :
    ‖B‖ ≤ c*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
  have hs (x : V) (F : Finset V) :
      (∑ y ∈ F, |deformedKernel G (walkKernel G hloc a) p k t Set.univ x y|) ≤
        c*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
    simp only [abs_of_nonneg (deformedKernel_nonneg G _ p k t _ _ _)]
    exact ((summable_deformedKernel G hloc hqt _ hP p hp k t ht Set.univ x).sum_le_tsum F
      (fun y _ => deformedKernel_nonneg G _ p k t _ x y)).trans
        (deformed_row_le_root_sum G hloc a p k t root weight hw hcov c hc hmin x)
  exact operator_norm_le_absolute_sums _ _
    (mul_nonneg hc (averagedDeformedSusceptibility_nonneg G _ p k root weight hw t)) hs
    (fun y F => by simpa only [deformedKernel_symm G _ p k t Set.univ] using hs y F) B hB

 

theorem deformed_root_sum_retained (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hA : HasKernel G p A) (k : ℕ) (t B : ℝ) (ht : 0 ≤ t)
    (htB : t*‖A‖ ≤ B) (hB : B*‖P‖^k ≤ 1/4) :
    ‖A‖/(2*c) ≤ averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  obtain ⟨T,hT,_,_,hret⟩ := exists_deformedOperator_small_change G hG hloc p hp0
    ((show (p:ℝ)<(pc G:ℝ) from hp).trans_le (pc G).2.2) a P hpos hPs hP
    A (hA.positiveRealMatrix G p A) (hA.isPositive G p A).isSelfAdjoint hA k t ht
  have hn := deformed_norm_le_root_sum G hloc hqt a hK p hp k t ht root weight hw hcov c hc.le hmin T hT
  have hsmall := (mul_le_mul_of_nonneg_right htB (pow_nonneg (norm_nonneg P) k)).trans hB
  have hh := mul_le_mul_of_nonneg_right hsmall (norm_nonneg A)
  apply (div_le_iff₀ (by positivity : 0 < 2*c)).mpr
  nlinarith

end AveragedRetention
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AveragePositiveTerm
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

omit [Countable V] [Countable E] [Nonempty V] in
 
theorem selected_average_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (j : ℕ) (s b F : ℝ) (hF : 0 ≤ F)
    (hm : b ≤ rawPathAverage G P k root weight
      (fun w => if w.Selected hloc p j s then 1 else 0))
    (hgood : ∀ w : RawCorridor G k, w.Selected hloc p j s →
      F ≤ retainedSusceptibilityProduct G P p t w) :
    F*b ≤ rawPathAverage G P k root weight (retainedSusceptibilityProduct G P p t) := by
  have hh := rawPathAverage_mono G hloc P hP k root weight hw
    (fun w => F*(if w.Selected hloc p j s then 1 else 0))
    (retainedSusceptibilityProduct G P p t) (by
      intro w
      by_cases hs : w.Selected hloc p j s
      · simpa only [hs,if_true,mul_one] using hgood w hs
      · simp only [hs,if_false,mul_zero,retainedSusceptibilityProduct]
        split_ifs
        · exact mul_nonneg (deformedSusceptibility_nonneg G P p k t _ w.base)
            (deformedSusceptibility_nonneg G P p k t _ w.endpoint)
        · exact le_rfl)
  rw [rawPathAverage_const_mul] at hh
  exact (mul_le_mul_of_nonneg_left hm hF).trans hh
end AveragePositiveTerm

section RiccatiContradiction
 

theorem riccati_retention_bound (χ D : ℝ → ℝ) (T m c h : ℝ)
    (hT : 0 < T) (hm : 0 < m) (hc : 0 < c) (_hh : 0 ≤ h)
    (hret : ∀ t ∈ Set.Icc (T/2) T, m/(2*c) ≤ χ t)
    (hder : ∀ t ∈ Set.Icc (T/2) T, HasDerivAt χ (-D t) t)
    (hdec : ∀ t ∈ Set.Icc (T/2) T, h*(χ t)^2 ≤ D t) :
    h*T*m ≤ 4*c := by
  have hpos (t) (ht : t ∈ Set.Icc (T/2) T) : 0 < χ t :=
    (div_pos hm (by positivity)).trans_le (hret t ht)
  have hd (t) (ht : t ∈ Set.Icc (T/2) T) :
      HasDerivAt (fun s => (χ s)⁻¹) (D t/(χ t)^2) t := by
    convert! (hder t ht).inv (hpos t ht).ne' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [neg_neg]
  have hcχ : ContinuousOn (fun s => (χ s)⁻¹) (Set.Icc (T/2) T) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => (χ s)⁻¹) (interior (Set.Icc (T/2) T)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hdl (t) (ht : t ∈ interior (Set.Icc (T/2) T)) :
      h ≤ deriv (fun s => (χ s)⁻¹) t := by
    rw [(hd t (interior_subset ht)).deriv]
    exact (le_div_iff₀ (sq_pos_of_pos (hpos t (interior_subset ht)))).mpr (hdec t (interior_subset ht))
  have hs := (convex_Icc (T/2) T).mul_sub_le_image_sub_of_le_deriv hcχ hdiff hdl
    (T/2) ⟨le_rfl,by linarith⟩ T ⟨by linarith,le_rfl⟩ (by linarith)
  have hstart : 0 ≤ (χ (T/2))⁻¹ := (inv_pos.mpr (hpos _ ⟨le_rfl,by linarith⟩)).le
  have hend : (χ T)⁻¹ ≤ 2*c/m := by
    have hb := one_div_le_one_div_of_le (div_pos hm (by positivity)) (hret T ⟨by linarith,le_rfl⟩)
    simpa only [one_div,inv_div] using hb
  have hs' : h*(T/2) ≤ 2*c/m := by linarith
  have hs'' := (le_div_iff₀ hm).mp hs'
  nlinarith
end RiccatiContradiction
end Percolation

 

 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteScale
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Infinite V]
variable {ι : Type*} [Fintype ι]

 

theorem exists_finite_scale_obstruction_bs_oai
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, 0 < J ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (A : Hilbert V →L[ℂ] Hilbert V), HasKernel G p A →
      ∀ k : ℕ, k₀ ≤ k → ∀ B : ℝ, 0 < B →
      let R := maxSusceptibility G p/‖A‖
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊
      B*‖P‖^k ≤ 1/4 →
      B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ ‖A‖ →
      R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k ≤ ε*((pc G:ℝ)/2)^(2*j) →
      M < B*((pc G:ℝ)/2)^(2*j) → False := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hw₀ (i) := (hw i).le
  obtain ⟨Cr,cf,hCr,hcf,hrow⟩ := exists_uniform_deformed_row_comparison G hconn hloc hqt
    root weight hw₀ hw1 (fun x => by
      obtain ⟨i,g,⟨e,he⟩,hx⟩ := hcov x
      exact ⟨i,g,e,he,hx⟩) d hd a hK hpcrit hpcrit₁
  obtain ⟨Cm,hCm,hmove⟩ := exists_uniform_deformed_endpoint_comparison G hloc hqt d hd a hK hpcrit hpcrit₁
  obtain ⟨Cd,hCd,hdecrease⟩ := exists_uniform_averaged_decrease_bs G hG hloc hqt
    root weight hw₀ (vertexAut G) (Set.Subset.refl _) htr d hd a hK hpcrit hpcrit₁ P hpos hP hsym
  let τ := cf/(8*c)
  have hτ : 0 < τ := div_pos hcf (by positivity)
  obtain ⟨J,C₁,k₀,b,hJ,hC₁,hk₀,hb,hselected⟩ := exists_selected_path_mass G hconn hloc hqt
    a ha root weight htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag hρ d hd τ hτ
  let C := Cr+Cm+Cd
  let q := b*Real.exp (-2)*(cf/2)^2
  let H := (1+2*(d:ℝ)/(pc G:ℝ))*(2*c)^2
  let ε := q/(2*H)
  let h₀ := Real.exp (-1)*q/2
  let M := 4*c/h₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hε : 0 < ε := div_pos hq (by positivity)
  have hh₀ : 0 < h₀ := by dsimp [h₀]; positivity
  have hM : 0 < M := div_pos (by positivity) hh₀
  refine ⟨C,by dsimp [C]; positivity,J,hJ,C₁,hC₁,k₀,hk₀,ε,M,hε,hM,?_⟩
  intro p hpnear hp A hA k hk B hB
  dsimp only
  let m := ‖A‖
  let R := maxSusceptibility G p/m
  let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊
  let β := ((pc G:ℝ)/2)^(2*j)
  let T := B/m
  let χ := averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight
  let D := fun t => ∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p
  change B*‖P‖^k ≤ 1/4 → B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m →
    R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k ≤ ε*β → M < B*β → False
  intro hsmall htime herrscale hlarge
  have hm : 0 < m := zero_lt_one.trans_le (hA.norm_one_le G p A)
  have hR : 1 ≤ R := (one_le_div hm).mpr (hA.norm_le_maxSusceptibility G hloc hqt p hp A)
  have hβ : 0 < β := pow_pos (half_pos hpcrit) _
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjr : (1:ℝ) ≤ (j:ℝ) := Nat.one_le_cast.mpr hj
  have hk3 : 3 ≤ k := hk₀.trans hk
  have hpzero : 0 < (p:ℝ) := (half_pos hpcrit).trans_le hpnear
  have hT : 0 < T := div_pos hB hm
  have hTb (t : ℝ) (ht : t ≤ T) : t*m ≤ B := (le_div_iff₀ hm).mp ht
  have htim (t : ℝ) (ht : t ≤ T) : t*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ 1 := by
    have hm' := mul_le_mul_of_nonneg_right (hTb t ht)
      (mul_nonneg (Nat.cast_nonneg j) (Real.exp_pos (C*(k:ℝ))).le)
    nlinarith only [hm',htime,hm]
  have hCbound (C' : ℝ) (hC' : C' ≤ C) : Real.exp (C'*(k:ℝ)) ≤ Real.exp (C*(k:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC' (Nat.cast_nonneg k))
  have htim' (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (C' : ℝ) (hC' : C' ≤ C) :
      t*Real.exp (C'*(k:ℝ)) ≤ 1 := by
    have he := mul_le_mul_of_nonneg_left (hCbound C' hC') ht
    have hj' := mul_le_mul_of_nonneg_left hjr (mul_nonneg ht (Real.exp_pos (C*(k:ℝ))).le)
    nlinarith only [he,hj',htim t htT]
  have hret (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) : m/(2*c) ≤ χ t :=
    deformed_root_sum_retained G hG hloc hqt a p hpzero hp root weight hw₀ hcov c hc hmin
      P A hpos hsym hP hA k t B ht (hTb t htT) hsmall
  have hdec (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) : (h₀*β)*(χ t)^2 ≤ D t := by
    have hχ : 0 ≤ χ t := averagedDeformedSusceptibility_nonneg G _ p k root weight hw₀ t
    have hret' := (div_le_iff₀ (by positivity : 0 < 2*c)).mp (hret t ht htT)
    have hrow' := hrow p hpnear hp k hk3 t ht (htim' t ht htT Cr (by dsimp [C]; linarith only [hCr,hCm,hCd]))
    have hcost : maxSusceptibility G p*(τ/R) ≤ (cf/2)*χ t := by
      have hmax : maxSusceptibility G p ≠ 0 :=
        (zero_lt_one.trans_le (maxSusceptibility_one_le G hloc hqt p hp)).ne'
      have he : maxSusceptibility G p*(τ/R) = τ*m := by dsimp [R]; field_simp [hmax]
      rw [he]
      have hh := mul_le_mul_of_nonneg_left hret' hτ.le
      have hτcf : τ*(2*c) = cf/4 := by dsimp [τ]; field_simp; ring
      rw [mul_left_comm τ (χ t) (2*c),hτcf,mul_comm (χ t)] at hh
      nlinarith only [hh,hcf,hχ]
    have hprod (w : RawCorridor G k) (hwsel : w.Selected hloc p j (τ/R)) :
        Real.exp (-2)*β*((cf/2)*χ t)^2 ≤ retainedSusceptibilityProduct G (walkKernel G hloc a) p t w := by
      have hbnd := selected_retained_product_lower G hloc hqt a hK p hp k t ht j (τ/R) Cm cf (χ t)
        hcf.le hχ hrow' hcost (hmove p hpnear hp k hk3 t ht) w hwsel
      have he : Real.exp (-2) ≤ Real.exp (-2*t*(j:ℝ)*Real.exp (Cm*(k:ℝ))) := by
        apply Real.exp_le_exp.mpr
        have he' := mul_le_mul_of_nonneg_left (hCbound Cm (by dsimp [C]; linarith only [hCr,hCm,hCd]))
          (mul_nonneg ht (Nat.cast_nonneg j))
        linarith only [he',htim t htT]
      have hpw : β ≤ (p:ℝ)^(2*j) := pow_le_pow_left₀ (half_pos hpcrit).le hpnear _
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul he hpw hβ.le (Real.exp_pos _).le) (sq_nonneg _)).trans hbnd
    have hsel := hselected p hpnear hp k hk R hR
    have hpositive := selected_average_lower G hloc _ hK p k t root weight hw₀ j (τ/R) b
      (Real.exp (-2)*β*((cf/2)*χ t)^2) (by positivity) hsel hprod
    have hpositive' : q*β*(χ t)^2 ≤ rawPathAverage G (walkKernel G hloc a) k root weight
        (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) := by
      convert hpositive using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [q]
      ring
    have ha₃ : 0 ≤ rootTriangle G root weight (p:ℝ) :=
      zero_le_one.trans (rootTriangle_one_le G hloc hqt root weight hw₀ hw1 p hp)
    have herror : (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
        (‖P‖^k*(rootTrace root weight (A^3)).re) ≤ (q/2)*β*(χ t)^2 := by
      rw [←rootTriangle_eq_trace G p root weight A hA]
      have hx : maxSusceptibility G p = R*m := by dsimp [R]; field_simp
      rw [hx]
      have hcoeff : 0 ≤ (1+2*(d:ℝ)/(pc G:ℝ)) := by positivity
      have hm2 : m^2 ≤ (2*c)^2*(χ t)^2 := by
        calc
          m^2 ≤ (χ t*(2*c))^2 := pow_le_pow_left₀ hm.le hret' 2
          _ = _ := by ring
      have h₁ := mul_le_mul_of_nonneg_left hm2
        (mul_nonneg (mul_nonneg hcoeff (sq_nonneg R)) (mul_nonneg ha₃ (pow_nonneg (norm_nonneg P) k)))
      have h₂ := mul_le_mul_of_nonneg_left herrscale (mul_nonneg hH.le (sq_nonneg (χ t)))
      have he : H*ε = q/2 := by dsimp [ε]; field_simp
      calc
        _ ≤ H*(R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k)*(χ t)^2 := by dsimp [H]; nlinarith only [h₁]
        _ ≤ H*(ε*β)*(χ t)^2 := by nlinarith only [h₂]
        _ = _ := by rw [←mul_assoc H ε β,he]
    have hdiff : (q/2)*β*(χ t)^2 ≤
        rawPathAverage G (walkKernel G hloc a) k root weight
          (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) -
        (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
          (‖P‖^k*(rootTrace root weight (A^3)).re) := by linarith only [hpositive',herror]
    have hexp : Real.exp (-1) ≤ Real.exp (-t*Real.exp (Cd*(k:ℝ))) :=
      Real.exp_le_exp.mpr (by linarith only [htim' t ht htT Cd (by dsimp [C]; linarith only [hCr,hCm]) ])
    have hh := mul_le_mul hexp hdiff (by positivity) (Real.exp_pos _).le
    have hdecr := hdecrease p hpnear hp A hA k hk3 t ht
    apply le_trans _ hdecr
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [h₀]
    ring
  have hb := riccati_retention_bound χ D T m c (h₀*β) hT hm hc (mul_pos hh₀ hβ).le
    (fun t ht => hret t (by linarith only [ht.1,hT]) ht.2)
    (fun t ht => hasDerivAt_averagedDeformedSusceptibility G hloc hqt root weight d hd a hK p hpzero hp k t
      (by linarith only [ht.1,hT]))
    (fun t ht => hdec t (by linarith only [ht.1,hT]) ht.2)
  have he : h₀*β*T*m = h₀*(B*β) := by dsimp [T]; field_simp
  rw [he] at hb
  have hg := (div_lt_iff₀ hh₀).mp hlarge
  nlinarith only [hg,hb]

end FiniteScale
end Percolation

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.exists_finite_scale_obstruction_bs_oai.{u, v, u_1} := @OAI.Percolation.exists_finite_scale_obstruction_bs_oai.{u, v, u_1}
