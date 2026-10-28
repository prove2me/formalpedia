-- Prove2me | solution 1 for OAI.Percolation.critical_bounded_of_transport_finiteness_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:32:38.584934+00:00
-- url     : https://prove2.me/submissions/a414b3cc-fc05-4a1a-b171-ed4223dd33ab

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_critical_rootTriangleSqrt_derivative_bs
import Theorems.Thm_OAI_Percolation_efficient_endpoint_profiles_of_divergent_moment_bs
import Theorems.Thm_OAI_Percolation_exists_finite_scale_obstruction_bs

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

theorem HasKernel.unique {G : BondGraph V E} {p : unitInterval}
    {A B : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G p A) (hB : HasKernel G p B) :
    A = B := kernel_extension_unique hA hB


end Kernel

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

 

theorem exists_operator_of_matrix_tendsto
    (A : ℕ → Hilbert V →L[ℂ] Hilbert V) (K : V → V → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ n, ‖A n‖ ≤ M)
    (hlim : ∀ x y, Tendsto (fun n => A n (lp.single 2 y (1 : ℂ)) x)
      atTop (𝓝 (K x y))) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V,
      ‖B‖ ≤ M ∧ ∀ x y, B (lp.single 2 y (1 : ℂ)) x = K x y := by
  have hn (n : ℕ) (f : Hilbert V) : ‖A n f‖ ≤ M * ‖f‖ :=
    (A n).le_opNorm f |>.trans (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _))
  have hcol (y : V) : Memℓp (fun x => K x y) 2 := by
    apply lp.memℓp_of_tendsto (l := atTop) (F := fun n => A n (lp.single 2 y (1 : ℂ)))
    · apply isBounded_iff_forall_norm_le.mpr
      refine ⟨M, ?_⟩
      rintro _ ⟨n, rfl⟩
      simpa [lp.norm_single] using hn n (lp.single 2 y (1 : ℂ))
    · exact tendsto_pi_nhds.mpr (fun x => hlim x y)
  let col (y : V) : Hilbert V := ⟨fun x => K x y, hcol y⟩
  let L : (V →₀ ℂ) →ₗ[ℂ] Hilbert V := Finsupp.linearCombination ℂ col
  have hLlim (f : V →₀ ℂ) :
      Tendsto (fun n => (A n (finiteEmbedding f) : V → ℂ)) atTop
        (𝓝 (L f : V → ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    simp only [finiteEmbedding, L, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
    exact tendsto_finsetSum _ (fun y _ => (hlim x y).const_mul (f y))
  have hLn (f : V →₀ ℂ) : ‖L f‖ ≤ M * ‖finiteEmbedding f‖ := by
    exact lp.norm_le_of_tendsto (Eventually.of_forall (fun n => hn n _)) (hLlim f)
  refine ⟨L.extendOfNorm finiteEmbedding,
    LinearMap.opNorm_extendOfNorm_le finiteEmbedding_dense hM hLn, ?_⟩
  intro x y
  have h := LinearMap.extendOfNorm_eq (f := L) finiteEmbedding_dense ⟨M, hLn⟩
    (Finsupp.single y (1 : ℂ))
  simp only [finiteEmbedding_single] at h
  rw [h]
  simp [L, col]

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

section NormOrder
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E] (G : BondGraph V E)

theorem operatorBounded_of_le {p q : unitInterval} (hpq : p ≤ q)
    (hq : OperatorBounded G q) : OperatorBounded G p := by
  obtain ⟨B, hB⟩ := hq
  obtain ⟨A, _, hA⟩ := exists_operator_of_matrix_domination
    (twoPoint G q) (twoPoint G p) (twoPoint_nonneg G q)
    (fun x y => (abs_of_nonneg (twoPoint_nonneg G p x y)).le.trans
      (twoPoint_mono G x y hpq)) B hB
  exact ⟨A, hA⟩

end NormOrder

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

 
theorem conn_first_outside (G : BondGraph V E) (S : Set E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    Conn G (ω ∩ S) x y ∨ ∃ a b e, G e = s(a,b) ∧ e ∉ S ∧
      ω ∈ DisjointOccurrence {η | Conn G (η ∩ S) x a}
        (DisjointOccurrence {η | e ∈ η} {η | Conn G η b y}) := by
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G h
  rcases hl.first_outside S with hall | ⟨a,b,e,l₁,l₂,heq,h₁,he,h₂,hfirst,hnot⟩
  · exact Or.inl (hl.conn fun e he => ⟨ho e he,hall e he⟩)
  · subst l
    have hnod := List.nodup_append.mp hn
    have hen : e ∉ l₂ := (List.nodup_cons.mp hnod.2.1).1
    right
    refine ⟨a,b,e,he,hnot,l₁.toFinset,(e::l₂).toFinset,?_,?_,?_,?_,?_⟩
    · intro d hd
      exact ho d (List.mem_append_left _ (List.mem_toFinset.mp hd))
    · intro d hd
      exact ho d (List.mem_append_right _ (List.mem_toFinset.mp hd))
    · apply Finset.disjoint_left.mpr
      intro d hd hd'
      exact hnod.2.2 d (List.mem_toFinset.mp hd) d (List.mem_toFinset.mp hd') rfl
    · exact h₁.conn (fun d hd => ⟨by simpa using hd, hfirst d hd⟩)
    · refine ⟨{e},l₂.toFinset,?_,?_,?_,by simp,?_⟩
      · simp
      · simp
      · simpa using hen
      · exact h₂.conn (fun d hd => by simpa using hd)

 
theorem law_map_preimage_embedding {F : Type*} (p : unitInterval) (f : F ↪ E) :
    (law p : Measure (Set E)).map (fun ω => f ⁻¹' ω) = law p := by
  have hm : Measurable (fun ω : Set E => f ⁻¹' ω) :=
    measurable_setOfPred.comp (Measurable.of_eval
      (fun e => (measurable_pi_apply (f e)).comp MeasurableEquiv.setOfPred.symm.measurable))
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => f ⁻¹' ω) ∘ (fun g => {e | g e}) =
      (fun g : F → Prop => {e | g e}) ∘ (fun g : E → Prop => fun e => g (f e)) := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop)]
  simp only [Set.mem_univ]
  have hi := (iIndepFun_infinitePi (P := fun _ : E => bernoulliMeasure True False p)
    (X := fun (_ : E) (b : Prop) => b) (fun _ => measurable_id)).precomp f.injective
  have hh := hi.map_fun_eq_infinitePi_map (fun _ => measurable_pi_apply _)
  simp only [Measure.infinitePi_map_eval] at hh
  erw [hh, setBernoulli_eq_map]
  rfl

 

theorem exists_orParameter_small (p : unitInterval) (hp : p < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ m : ℕ, ∃ q : unitInterval, (q : ℝ) ≤ ε ∧ orParameter q m = p := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - (p : ℝ) by exact sub_pos.mpr hp)
    (show 1-ε < 1 by linarith)
  let f := fun x : ℝ => 1 - (1-x)^m
  have hf : Continuous f := by fun_prop
  have h0 : f 0 = 0 := by simp [f]
  have hp' : (p : ℝ) ∈ Set.Icc (f 0) (f ε) := by
    rw [h0]
    exact ⟨p.2.1, by dsimp [f]; linarith⟩
  obtain ⟨q,hq,hqp⟩ := intermediate_value_Icc hε.le hf.continuousOn hp'
  exact ⟨m,⟨q,hq.1,hq.2.trans hε1⟩,hq.2,Subtype.ext hqp⟩

end SprinklingPaths

section ColoredSprinkling
attribute [local instance] Classical.propDecidable

 theorem conn_map_edges {F : Type*} (G : BondGraph V E) (f : F → E)
    (ω : Set F) (x y : V) : Conn (G ∘ f) ω x y ↔ Conn G (f '' ω) x y := by
  constructor <;> intro h
  · induction h with
    | refl => exact conn_refl _ _ _
    | @tail a b hab he ih =>
      rcases he with ⟨e,he,heq⟩
      exact ih.tail ⟨f e,Set.mem_image_of_mem _ he,heq⟩
  · induction h with
    | refl => exact conn_refl _ _ _
    | @tail a b hab he ih =>
      rcases he with ⟨e,⟨d,hd,rfl⟩,heq⟩
      exact ih.tail ⟨d,hd,heq⟩

 theorem finiteWitness_inter (A : Set (Set E)) (hA : FiniteWitness A) (S : Set E) :
    FiniteWitness {ω | ω ∩ S ∈ A} := by
  intro ω h
  obtain ⟨s,hs,hsa⟩ := hA (ω ∩ S) h
  refine ⟨s,hs.trans Set.inter_subset_left,?_⟩
  have he : (s : Set E) ∩ S = s := Set.inter_eq_left.mpr (hs.trans Set.inter_subset_right)
  change (s : Set E) ∩ S ∈ A
  rwa [he]

 theorem not_mem_baseColors (m : ℕ) (e : E) (j : Fin (m+1)) :
    (e,j) ∉ baseColors m ↔ j = Fin.last m := by
  constructor
  · intro h
    apply Fin.eq_last_of_not_lt
    intro hj
    apply h
    exact ⟨(e,⟨j.val,hj⟩),Prod.ext rfl (Fin.ext rfl)⟩
  · rintro rfl ⟨⟨e',i⟩,hi⟩
    exact Fin.castSucc_ne_last i (congrArg Prod.snd hi)

 theorem fst_inter_baseColors (m : ℕ) (ω : Set (E × Fin (m+1))) :
    Prod.fst '' (ω ∩ baseColors m) = baseField m ω := by
  ext e
  constructor
  · rintro ⟨⟨e',j⟩,⟨ho,⟨⟨f,i⟩,he⟩⟩,rfl⟩
    refine ⟨(f,i),?_,?_⟩
    · change colorInclusion m (f,i) ∈ ω
      rwa [he]
    · exact congrArg Prod.fst he
  · rintro ⟨⟨e',i⟩,ho,rfl⟩
    exact ⟨colorInclusion m (e',i),⟨ho,Set.mem_range_self _⟩,rfl⟩

 theorem measurable_baseField (m : ℕ) : Measurable (baseField (E := E) m) := by
  apply (measurable_image_fst (Fin m)).comp
  exact measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply (colorInclusion m e)).comp
      MeasurableEquiv.setOfPred.symm.measurable))

 theorem law_map_baseField (q : unitInterval) (m : ℕ) :
    (law q : Measure (Set (E × Fin (m+1)))).map (baseField m) = law (orParameter q m) := by
  have hm : Measurable (fun ω : Set (E × Fin (m+1)) => colorInclusion m ⁻¹' ω) :=
    measurable_setOfPred.comp (Measurable.of_eval
      (fun e => (measurable_pi_apply (colorInclusion m e)).comp
        MeasurableEquiv.setOfPred.symm.measurable))
  change (law q).map ((fun ω : Set (E × Fin m) => Prod.fst '' ω) ∘
    (fun ω => colorInclusion m ⁻¹' ω)) = _
  rw [← Measure.map_map (measurable_image_fst (Fin m)) hm,
    law_map_preimage_embedding, law_map_image_fst, Fintype.card_fin]

 theorem exists_dart (G : BondGraph V E) {e : E} {a b : V} (h : G e = s(a,b)) :
    ∃ j : Bool, dartSource G (e,j) = a ∧ dartTarget G (e,j) = b := by
  have he : s((G e).out.1, (G e).out.2) = s(a,b) := (G e).out_eq.trans h
  rcases Sym2.eq_iff.mp he with h | h
  · exact ⟨true,h⟩
  · exact ⟨false,h.2,h.1⟩

 theorem colored_conn_probability [Countable V] [Countable E] (G : BondGraph V E)
    (q : unitInterval) (m : ℕ) (x y : V) :
    (law q).real {ω : Set (E × Fin m) | Conn (G ∘ Prod.fst) ω x y} =
      twoPoint G (orParameter q m) x y := by
  have h := law_map_image_fst (E := E) q (Fin m)
  simp only [Fintype.card_fin] at h
  rw [twoPoint, ← h, Measure.map_apply (measurable_image_fst (Fin m))
    (measurableSet_conn G x y)]
  congr 1
  ext ω
  exact conn_map_edges G Prod.fst ω x y

 theorem base_conn_probability [Countable V] [Countable E] (G : BondGraph V E)
    (q : unitInterval) (m : ℕ) (x y : V) :
    (law q).real {ω : Set (E × Fin (m+1)) |
      Conn (G ∘ Prod.fst) (ω ∩ baseColors m) x y} =
      twoPoint G (orParameter q m) x y := by
  rw [twoPoint, ← law_map_baseField (E := E) q m,
    Measure.map_apply (measurable_baseField m) (measurableSet_conn G x y)]
  congr 1
  ext ω
  change Conn (G ∘ Prod.fst) (ω ∩ baseColors m) x y ↔ Conn G (baseField m ω) x y
  rw [conn_map_edges, fst_inter_baseColors]

 

 theorem twoPoint_or_succ_le [Countable V] [Fintype E] (G : BondGraph V E) (q : unitInterval)
    (m : ℕ) (x y : V) :
    twoPoint G (orParameter q (m+1)) x y ≤ twoPoint G (orParameter q m) x y +
      (q : ℝ) * ∑ d : E × Bool,
        twoPoint G (orParameter q m) x (dartSource G d) *
        twoPoint G (orParameter q (m+1)) (dartTarget G d) y := by
  let H : BondGraph V (E × Fin (m+1)) := G ∘ Prod.fst
  let A (a : V) : Set (Set (E × Fin (m+1))) :=
    {ω | Conn H (ω ∩ baseColors m) x a}
  let B (b : V) : Set (Set (E × Fin (m+1))) := {ω | Conn H ω b y}
  let C (d : E × Bool) := DisjointOccurrence (A (dartSource G d))
    (DisjointOccurrence {ω | (d.1,Fin.last m) ∈ ω} (B (dartTarget G d)))
  have huA (a : V) : IsUpperSet (A a) :=
    fun _ _ h hω => conn_mono H (Set.inter_subset_inter_left _ h) hω
  have hfA (a : V) : FiniteWitness (A a) :=
    finiteWitness_inter _ (finiteWitness_conn H x a) _
  have huB (b : V) : IsUpperSet (B b) := fun _ _ h hω => conn_mono H h hω
  have hfB (b : V) : FiniteWitness (B b) := finiteWitness_conn H b y
  have hsub : {ω | Conn H ω x y} ⊆ A y ∪ ⋃ d : E × Bool, C d := by
    intro ω hω
    rcases conn_first_outside H (baseColors m) hω with ha | ⟨a,b,⟨e,j⟩,he,hj,hc⟩
    · exact Or.inl ha
    · have hj' := (not_mem_baseColors m e j).mp hj
      subst j
      obtain ⟨k,hk₁,hk₂⟩ := exists_dart G he
      right
      refine Set.mem_iUnion.mpr ⟨(e,k),?_⟩
      simpa only [C,hk₁,hk₂] using hc
  calc
    twoPoint G (orParameter q (m+1)) x y = (law q).real {ω | Conn H ω x y} :=
      (colored_conn_probability G q (m+1) x y).symm
    _ ≤ (law q).real (A y ∪ ⋃ d : E × Bool, C d) := measureReal_mono hsub
    _ ≤ (law q).real (A y) + (law q).real (⋃ d : E × Bool, C d) := measureReal_union_le _ _
    _ ≤ (law q).real (A y) + ∑ d : E × Bool, (law q).real (C d) :=
      add_le_add_right (measureReal_iUnion_fintype_le _) _
    _ ≤ twoPoint G (orParameter q m) x y +
        ∑ d : E × Bool, twoPoint G (orParameter q m) x (dartSource G d) *
          ((q : ℝ) * twoPoint G (orParameter q (m+1)) (dartTarget G d) y) := by
      rw [show (law q).real (A y) = twoPoint G (orParameter q m) x y from
        base_conn_probability G q m x y]
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro d _
      have hb := bk q {ω | (d.1,Fin.last m) ∈ ω} (B (dartTarget G d))
        (fun _ _ hh he => hh he) (huB _) (finiteWitness_edge _) (hfB _)
      have heq : (law q).real {ω : Set (E × Fin (m+1)) | (d.1,Fin.last m) ∈ ω} =
          (q : ℝ) := by simpa using finite_open_probability q {(d.1,Fin.last m)}
      rw [heq, show (law q).real (B (dartTarget G d)) =
        twoPoint G (orParameter q (m+1)) (dartTarget G d) y from
        colored_conn_probability G q (m+1) _ _] at hb
      have ha := bk q (A (dartSource G d))
        (DisjointOccurrence {ω | (d.1,Fin.last m) ∈ ω} (B (dartTarget G d)))
        (huA _) (disjointOccurrence_upper _ _) (hfA _) (finiteWitness_disjointOccurrence _ _)
      rw [show (law q).real (A (dartSource G d)) =
        twoPoint G (orParameter q m) x (dartSource G d) from base_conn_probability G q m _ _] at ha
      exact ha.trans (mul_le_mul_of_nonneg_left hb (twoPoint_nonneg G _ _ _))
    _ = _ := by rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro d _; ring

end ColoredSprinkling

section FiniteGraphOperators
attribute [local instance] Classical.propDecidable

 theorem mem_edgeVertices [Fintype E] (G : BondGraph V E) (x : V) :
    x ∈ edgeVertices G ↔ ∃ e, x ∈ G e := by simp [edgeVertices]

 theorem conn_eq_or_mem_edgeVertices [Fintype E] (G : BondGraph V E)
    {ω : Set E} {x y : V} (h : Conn G ω x y) : x = y ∨ y ∈ edgeVertices G := by
  cases h with
  | refl => exact Or.inl rfl
  | @tail a b hab he =>
    rcases he with ⟨e,_,he⟩
    exact Or.inr ((mem_edgeVertices G y).mpr ⟨e,by rw [he]; simp⟩)

 theorem operatorBounded_finite_edges [Fintype E] (G : BondGraph V E) (p : unitInterval) :
    OperatorBounded G p := by
  have hr (x : V) (s : Finset V) : ∑ y ∈ s, twoPoint G p x y ≤
      (edgeVertices G).card + (1 : ℝ) := by
    let F := insert x (edgeVertices G)
    have bound (y : V) : twoPoint G p x y ≤ if y ∈ F then 1 else 0 := by
      split_ifs with hy
      · exact twoPoint_le_one G p x y
      · have he : {ω | Conn G ω x y} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω h
          rcases conn_eq_or_mem_edgeVertices G h with rfl | hmem
          · exact hy (by simp [F])
          · exact hy (by simp [F,hmem])
        simp [twoPoint,he]
    calc
      ∑ y ∈ s, twoPoint G p x y ≤ ∑ y ∈ s, if y ∈ F then (1:ℝ) else 0 :=
        Finset.sum_le_sum (fun y _ => bound y)
      _ = ((s ∩ F).card : ℝ) := by simp
      _ ≤ (F.card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      _ ≤ (edgeVertices G).card + (1 : ℝ) := by
        exact_mod_cast Finset.card_insert_le x (edgeVertices G)
  obtain ⟨A,_,hA⟩ := exists_operator_of_row_column_bound (twoPoint G p)
    ((edgeVertices G).card+1) (by positivity) (twoPoint_nonneg G p) hr
    (fun y s => by simpa only [twoPoint_symm G p] using hr y s)
  exact ⟨A,hA⟩

 theorem dart_edge (G : BondGraph V E) (d : E × Bool) :
    G d.1 = s(dartSource G d, dartTarget G d) := by
  rcases d with ⟨e,j⟩
  cases j
  · exact (G e).out_eq.symm.trans (Sym2.eq_swap ..)
  · exact (G e).out_eq.symm

 theorem card_darts_at_source [Fintype E] (G : BondGraph V E) (x : V) :
    Fintype.card {d : E × Bool // dartSource G d = x} ≤ 2 * degree G x := by
  let : Fintype (Step G x) := (finite_steps G (fun _ => Set.toFinite _) x).fintype
  let f : {d : E × Bool // dartSource G d = x} → Step G x × Bool := fun d =>
    (⟨(d.val.1,dartTarget G d.val), by rw [dart_edge G d.val,d.property]⟩,d.val.2)
  have hf : Function.Injective f := by
    intro d d' h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun t : Step G x × Bool => t.1.val.1) h
    · exact congrArg (fun t : Step G x × Bool => t.2) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod,Fintype.card_bool,degree,Nat.card_eq_fintype_card,Nat.mul_comm] using hc

 theorem card_darts_at_target [Fintype E] (G : BondGraph V E) (x : V) :
    Fintype.card {d : E × Bool // dartTarget G d = x} ≤ 2 * degree G x := by
  let : Fintype (Step G x) := (finite_steps G (fun _ => Set.toFinite _) x).fintype
  let f : {d : E × Bool // dartTarget G d = x} → Step G x × Bool := fun d =>
    (⟨(d.val.1,dartSource G d.val), by
      rw [dart_edge G d.val,d.property]; exact Sym2.eq_swap ..⟩,d.val.2)
  have hf : Function.Injective f := by
    intro d d' h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun t : Step G x × Bool => t.1.val.1) h
    · exact congrArg (fun t : Step G x × Bool => t.2) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod,Fintype.card_bool,degree,Nat.card_eq_fintype_card,Nat.mul_comm] using hc

 theorem adjacencyOperator_apply [Fintype E] (G : BondGraph V E) (f : Hilbert V) :
    adjacencyOperator G f = ∑ d : E × Bool, lp.single 2 (dartSource G d) (f (dartTarget G d)) := by
  simp [adjacencyOperator,lp.singleContinuousLinearMap_apply,
    lp.evalCLM,lp.evalₗ]
  rfl

 theorem adjacencyOperator_norm_le [Fintype E] (G : BondGraph V E)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) : ‖adjacencyOperator G‖ ≤ 2 * (D : ℝ) := by
  let U (x y : V) : ℝ := ∑ d : E × Bool,
    if dartSource G d = x ∧ dartTarget G d = y then 1 else 0
  have hU : ∀ x y, 0 ≤ U x y := by intro x y; apply Finset.sum_nonneg; intro d _; positivity
  have hmat : ∀ x y, adjacencyOperator G (lp.single 2 y (1:ℂ)) x = (U x y : ℂ) := by
    intro x y
    rw [adjacencyOperator_apply]
    simp only [lp.coeFn_sum,Finset.sum_apply,U,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [lp.single_apply]
    by_cases hx : dartSource G d = x <;> by_cases hy : dartTarget G d = y <;>
      simp [hx,hy]
  have hrow (x : V) (s : Finset V) : ∑ y ∈ s, U x y ≤ 2 * (D : ℝ) := by
    calc
      ∑ y ∈ s, U x y = ∑ d : E × Bool,
          ∑ y ∈ s, if dartSource G d = x ∧ dartTarget G d = y then (1:ℝ) else 0 :=
        Finset.sum_comm
      _ ≤ ∑ d : E × Bool, if dartSource G d = x then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hx : dartSource G d = x
        · simp only [hx,true_and,if_true]
          rw [Finset.sum_ite_eq]
          split_ifs <;> norm_num
        · simp [hx]
      _ = (Fintype.card {d : E × Bool // dartSource G d = x} : ℝ) := by simp [Fintype.card_subtype]
      _ ≤ 2 * (D : ℝ) := by exact_mod_cast (card_darts_at_source G x).trans (Nat.mul_le_mul_left 2 (hD x))
  have hcol (y : V) (s : Finset V) : ∑ x ∈ s, U x y ≤ 2 * (D : ℝ) := by
    calc
      ∑ x ∈ s, U x y = ∑ d : E × Bool,
          ∑ x ∈ s, if dartSource G d = x ∧ dartTarget G d = y then (1:ℝ) else 0 :=
        Finset.sum_comm
      _ ≤ ∑ d : E × Bool, if dartTarget G d = y then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hy : dartTarget G d = y
        · simp only [hy,and_true,if_true]
          rw [Finset.sum_ite_eq]
          split_ifs <;> norm_num
        · simp [hy]
      _ = (Fintype.card {d : E × Bool // dartTarget G d = y} : ℝ) := by simp [Fintype.card_subtype]
      _ ≤ 2 * (D : ℝ) := by exact_mod_cast (card_darts_at_target G y).trans (Nat.mul_le_mul_left 2 (hD y))
  obtain ⟨A,hn,hA⟩ := exists_operator_of_row_column_bound U (2*D) (by positivity) hU hrow hcol
  rwa [kernel_extension_unique hmat hA]

end FiniteGraphOperators

section FiniteSprinklingBound
attribute [local instance] Classical.propDecidable
variable [Countable V] [Fintype E]

 theorem finite_sprinkling_bound (G : BondGraph V E) (q : unitInterval) (m D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : HasKernel G (orParameter q m) A) (M : ℝ) (hM : ‖A‖ ≤ M)
    (hq : (q : ℝ) * (2*D) * M < 1) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V, HasKernel G (orParameter q (m+1)) B ∧
      ‖B‖ ≤ M / (1-(q:ℝ)*(2*D)*M) := by
  obtain ⟨B,hB⟩ := operatorBounded_finite_edges G (orParameter q (m+1))
  let R := (adjacencyOperator G).comp B
  let C := A + (q : ℂ) • A.comp R
  let U (x y : V) := twoPoint G (orParameter q m) x y + (q:ℝ) *
    ∑ d : E × Bool, twoPoint G (orParameter q m) x (dartSource G d) *
      twoPoint G (orParameter q (m+1)) (dartTarget G d) y
  have hU : ∀ x y, 0 ≤ U x y := by
    intro x y
    exact add_nonneg (twoPoint_nonneg G _ _ _)
      (mul_nonneg q.2.1 (Finset.sum_nonneg fun d _ =>
        mul_nonneg (twoPoint_nonneg G _ _ _) (twoPoint_nonneg G _ _ _)))
  have hC : ∀ x y, C (lp.single 2 y (1:ℂ)) x = (U x y : ℂ) := by
    intro x y
    simp only [C,add_apply,smul_apply,
      ContinuousLinearMap.comp_apply,R,adjacencyOperator_apply,map_sum,lp.coeFn_add,Pi.add_apply,
      lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_sum,Finset.sum_apply,U,
      Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sum]
    rw [hA x y]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    have hs (c : ℂ) : (lp.single 2 (dartSource G d) c : Hilbert V) = c • lp.single 2 (dartSource G d) (1:ℂ) := by
      rw [← lp.single_smul]; simp
    rw [hs,map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hA,hB]
    ring
  obtain ⟨B',hn,hB'⟩ := exists_operator_of_matrix_domination U
    (twoPoint G (orParameter q (m+1))) hU
    (fun x y => by rw [abs_of_nonneg (twoPoint_nonneg G _ _ _)]; exact twoPoint_or_succ_le G q m x y)
    C hC
  have he : B' = B := kernel_extension_unique hB' hB
  rw [he] at hn
  have hqn : ‖(q : ℂ)‖ = (q : ℝ) := by simp [abs_of_nonneg q.2.1]
  have hcoef : (q : ℝ) * ‖A‖ * (2*D) * ‖B‖ ≤ (q : ℝ) * M * (2*D) * ‖B‖ := by
    gcongr
    exact q.2.1
  have hbnd : ‖B‖ ≤ M + (q : ℝ) * (2*D) * M * ‖B‖ := by
    calc
      ‖B‖ ≤ ‖C‖ := hn
      _ ≤ ‖A‖ + ‖(q : ℂ) • A.comp R‖ := norm_add_le _ _
      _ = ‖A‖ + (q : ℝ) * ‖A.comp R‖ := by rw [norm_smul,hqn]
      _ ≤ ‖A‖ + (q : ℝ) * (‖A‖ * (‖adjacencyOperator G‖ * ‖B‖)) := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ q.2.1
        exact (A.opNorm_comp_le R).trans
          (mul_le_mul_of_nonneg_left ((adjacencyOperator G).opNorm_comp_le B) (norm_nonneg _))
      _ ≤ ‖A‖ + (q : ℝ) * (‖A‖ * ((2*D) * ‖B‖)) := by
        gcongr
        · exact q.2.1
        · exact adjacencyOperator_norm_le G D hD
      _ ≤ M + (q : ℝ) * M * (2*D) * ‖B‖ := by
        rw [show (q : ℝ) * (‖A‖ * ((2*D) * ‖B‖)) = (q : ℝ) * ‖A‖ * (2*D) * ‖B‖ by ring]
        exact add_le_add hM hcoef
      _ = _ := by ring
  refine ⟨B,hB,?_⟩
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  nlinarith

end FiniteSprinklingBound

section ExhaustionSprinkling
attribute [local instance] Classical.propDecidable
open Filter Topology
variable [Countable V] [Countable E]

 theorem twoPoint_restrict_edges (G : BondGraph V E) (p : unitInterval) (S : Set E) (x y : V) :
    twoPoint (G ∘ (Subtype.val : S → E)) p x y =
      (law p).real {ω : Set E | Conn G (ω ∩ S) x y} := by
  unfold twoPoint
  rw [← law_map_restrict p S, Measure.map_apply (measurable_set_restrict S)
    (measurableSet_conn (G ∘ Subtype.val) x y)]
  apply congrArg ENNReal.toReal
  congr 1
  ext ω
  change Conn (G ∘ Subtype.val) (Subtype.val ⁻¹' ω) x y ↔ _
  rw [conn_map_edges]
  have he : (Subtype.val '' (Subtype.val ⁻¹' ω : Set S)) = ω ∩ S := by
    ext e
    simp only [Set.mem_image,Set.mem_preimage,Set.mem_inter_iff]
    constructor
    · rintro ⟨d,hd,rfl⟩; exact ⟨hd,d.property⟩
    · rintro ⟨ho,hs⟩; exact ⟨⟨e,hs⟩,ho,rfl⟩
  rw [he]
  rfl

 theorem twoPoint_restrict_le (G : BondGraph V E) (p : unitInterval) (S : Set E) (x y : V) :
    twoPoint (G ∘ (Subtype.val : S → E)) p x y ≤ twoPoint G p x y := by
  rw [twoPoint_restrict_edges]
  exact measureReal_mono (fun ω h => conn_mono G Set.inter_subset_left h) (measure_ne_top _ _)

 omit [Countable V] [Countable E] in
 theorem degree_restrict_le (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V) :
    degree (G ∘ (Subtype.val : S → E)) x ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  let f : Step (G ∘ (Subtype.val : S → E)) x → Step G x :=
    fun d => ⟨(d.val.1.val,d.val.2),d.property⟩
  apply Nat.card_le_card_of_injective f
  intro d d' h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun t : Step G x => t.val.1) h
  · exact congrArg (fun t : Step G x => t.val.2) h

 theorem sprinkling_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (q : unitInterval) (m D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G (orParameter q m) A)
    (hq : (q : ℝ) * (2*D) * ‖A‖ < 1) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V, HasKernel G (orParameter q (m+1)) B ∧
      ‖B‖ ≤ ‖A‖ / (1-(q:ℝ)*(2*D)*‖A‖) := by
  let := Encodable.ofCountable E
  let F (n : ℕ) := edgeExhaustion (E := E) n
  let H (n : ℕ) : BondGraph V (F n) := G ∘ Subtype.val
  have hb (n : ℕ) : ∃ B : Hilbert V →L[ℂ] Hilbert V,
      HasKernel (H n) (orParameter q (m+1)) B ∧
      ‖B‖ ≤ ‖A‖ / (1-(q:ℝ)*(2*D)*‖A‖) := by
    obtain ⟨A',hn,hA'⟩ := exists_operator_of_matrix_domination
      (twoPoint G (orParameter q m)) (twoPoint (H n) (orParameter q m))
      (twoPoint_nonneg G _) (fun x y => by
        rw [abs_of_nonneg (twoPoint_nonneg (H n) _ _ _)]
        exact twoPoint_restrict_le G _ (F n) x y) A hA
    exact finite_sprinkling_bound (H n) q m D
      (fun x => (degree_restrict_le G hloc (F n) x).trans (hD x)) A' hA' ‖A‖ hn hq
  choose B hB hn using hb
  have hlim (x y : V) : Tendsto (fun n => twoPoint (H n) (orParameter q (m+1)) x y)
      atTop (𝓝 (twoPoint G (orParameter q (m+1)) x y)) := by
    have hm : Monotone (fun n => {ω : Set E | Conn G (ω ∩ (F n : Set E)) x y}) := by
      intro m n h ω hω
      exact conn_mono G (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law (orParameter q (m+1))) hm
    have he := witness_eq_union {ω | Conn G ω x y} (fun _ _ h hc => conn_mono G h hc)
      (finiteWitness_conn G x y)
    change {ω : Set E | Conn G ω x y} = ⋃ n, {ω | Conn G (ω ∩ (F n : Set E)) x y} at he
    rw [← he] at h
    have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
    apply hr.congr'
    apply Filter.Eventually.of_forall
    intro n
    exact (twoPoint_restrict_edges G (orParameter q (m+1)) (F n) x y).symm
  obtain ⟨C,hCn,hC⟩ := exists_operator_of_matrix_tendsto B
    (fun x y => (twoPoint G (orParameter q (m+1)) x y : ℂ))
    (div_nonneg (norm_nonneg _) (sub_pos.mpr hq).le) hn (fun x y => by
      have hBm : ∀ n x y, B n (lp.single 2 y (1:ℂ)) x = (twoPoint (H n) (orParameter q (m+1)) x y : ℂ) := hB
      simp only [hBm]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim x y))
  exact ⟨C,hC,hCn⟩

end ExhaustionSprinkling

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

 
theorem walk_operator_apply (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ))
    (f : Hilbert V) (x : V) :
    P f x = ∑ y ∈ insert x (neighbors G hloc x), (walkKernel G hloc a x y : ℂ)*f y := by
  have hz (y : V) (hy : y ∉ insert x (neighbors G hloc x)) : matrixCoeff P x y*f y = 0 := by
    have hxy : x ≠ y := by intro h; subst y; exact hy (Finset.mem_insert_self _ _)
    have hAdj : ¬Adj G x y := fun h => hy (Finset.mem_insert_of_mem ((mem_neighbors ..).mpr h))
    simp only [matrixCoeff,hP,walkKernel,ite_eq_right hxy,ite_eq_right hAdj,add_zero,Complex.ofReal_zero,zero_mul]
  have hsum := (operator_kernel_hasSum P f x).unique (hasSum_sum_of_ne_finset_zero hz)
  simpa only [matrixCoeff,hP] using hsum

 

theorem parameter_le_walk_norm [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hp : OperatorBounded G p) : (p:ℝ) ≤ ‖P‖ := by
  obtain ⟨T,hT⟩ := hp
  let z := Classical.arbitrary V
  let f := T (lp.single 2 z (1:ℂ))
  have hf (x : V) : f x = (twoPoint G p x z : ℂ) := hT x z
  have hf0 : 0 < ‖f‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hval := congrArg (fun g : Hilbert V => g z) h
    simp [hf] at hval
  have hrow (x : V) : (p:ℝ)*twoPoint G p x z ≤
      ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y*twoPoint G p y z := by
    calc
      _ = ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y*((p:ℝ)*twoPoint G p x z) := by
        rw [← Finset.sum_mul,walkKernel_row_sum,one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y hy
        apply mul_le_mul_of_nonneg_left _ (walkKernel_nonneg G hloc D hD a ha haD x y)
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact mul_le_of_le_one_left (twoPoint_nonneg G p y z) p.2.2
        · simpa only [twoPoint_symm G p] using twoPoint_adj_lower G p z x y ((mem_neighbors ..).mp hy)
  have hpoint (x : V) : ‖((p:ℂ) • f) x‖ ≤ ‖P f x‖ := by
    rw [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hf,← Complex.ofReal_mul,
      Complex.norm_of_nonneg (mul_nonneg p.2.1 (twoPoint_nonneg G p x z)),
      walk_operator_apply G hloc a P hP]
    simp only [hf,← Complex.ofReal_mul,← Complex.ofReal_sum]
    rw [Complex.norm_of_nonneg (le_trans (mul_nonneg p.2.1 (twoPoint_nonneg G p x z)) (hrow x))]
    exact hrow x
  have hn := (lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) hpoint).trans (P.le_opNorm f)
  rw [norm_smul,Complex.norm_of_nonneg p.2.1] at hn
  exact (mul_le_mul_iff_left₀ hf0).mp hn

 
theorem pc_lt_one_of_nonamenable [Nonempty V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) : pc G < 1 := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  obtain ⟨D,P,hD0,hD,hPn,_,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  have hDr : 0 < (D:ℝ) := by exact_mod_cast hD0
  let p : unitInterval := ⟨(‖P‖+1)/2,by constructor <;> linarith [norm_nonneg P]⟩
  have hp1 : p < 1 := by change (‖P‖+1)/2 < 1; linarith
  have ha : 0 ≤ (1:ℝ)/(2*D) := by positivity
  have haD : (1:ℝ)/(2*D)*D ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  apply lt_of_le_of_ne (show pc G ≤ 1 from (pc G).2.2)
  intro he
  have hb := operatorBounded_of_lt_pc G hloc hqt p (he ▸ hp1)
  have hle := parameter_le_walk_norm G hloc D hD _ ha haD P hP p hb
  change (‖P‖+1)/2 ≤ ‖P‖ at hle
  linarith

end CriticalParameter

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

 

theorem almost_linear_susceptibility
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

 

theorem critical_rootTriangle_subpower
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
  obtain ⟨C₀,hC₀,hder⟩ := critical_rootTriangleSqrt_derivative_bs G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
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

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section QuantitativeSprinkling
attribute [local instance] Classical.propDecidable Classical.decEq

lemma riccati_step (a M n x : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) (_hn : 0 ≤ n)
    (_hx : 0 ≤ x) (hb : x ≤ M/(1-a*n*M)) (hh : a*(n+1)*M < 1) :
    a*x < 1 ∧ x/(1-a*x) ≤ M/(1-a*(n+1)*M) := by
  have haM : 0 ≤ a*M := mul_nonneg ha hM
  have hp : 0 < 1-a*n*M := by nlinarith
  have hb' := (le_div_iff₀ hp).mp hb
  have hs : a*(M/(1-a*n*M)) < 1 := by
    rw [←mul_div_assoc,div_lt_one hp]
    nlinarith
  have hax : a*x < 1 := (mul_le_mul_of_nonneg_left hb ha).trans_lt hs
  refine ⟨hax,?_⟩
  apply (div_le_div_iff₀ (sub_pos.mpr hax) (sub_pos.mpr hh)).mpr
  nlinarith

 

theorem sprinkling_iterated_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) (m D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : HasKernel G (orParameter q m) A) (n : ℕ)
    (hn : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1) :
    ∃ B : Hilbert V →L[ℂ] Hilbert V, HasKernel G (orParameter q (m+n)) B ∧
      ‖B‖ ≤ ‖A‖/(1-(q:ℝ)*(2*D)*(n:ℝ)*‖A‖) := by
  induction n with
  | zero => exact ⟨A,by simpa using hA,by simp⟩
  | succ n ih =>
    have ha : 0 ≤ (q:ℝ)*(2*D) := mul_nonneg q.2.1 (by positivity)
    have hnext : (q:ℝ)*(2*D)*((n:ℝ)+1)*‖A‖ < 1 := by simpa using hn
    have hprev : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1 := by
      nlinarith [mul_nonneg ha (norm_nonneg A)]
    obtain ⟨B,hB,hBn⟩ := ih hprev
    obtain ⟨hs,hbound⟩ := riccati_step ((q:ℝ)*(2*D)) ‖A‖ n ‖B‖ ha (norm_nonneg _) (Nat.cast_nonneg _) (norm_nonneg _) hBn hnext
    obtain ⟨C,hC,hCn⟩ := sprinkling_bound G hloc q (m+n) D hD B hB hs
    exact ⟨C,by simpa [Nat.add_assoc] using hC,by simpa using hCn.trans hbound⟩

lemma closed_power_bound (q : unitInterval) (n : ℕ) :
    (1-(q:ℝ))^n * (1+(n:ℝ)*(q:ℝ)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1-(q:ℝ))^n := pow_nonneg (sub_nonneg.mpr q.2.2) _
    have hn : 0 ≤ (n:ℝ)*(q:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg hp hn,mul_nonneg hp (sq_nonneg (q:ℝ))]

lemma orParameter_gap_bound (p q : unitInterval) (m n : ℕ) (hm : orParameter q m = p) :
    (1+(n:ℝ)*(q:ℝ))*(1-(orParameter q (m+n):ℝ)) ≤ 1-(p:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (closed_power_bound q n) (sub_nonneg.mpr p.2.2)
  have he : 1-(p:ℝ) = (1-(q:ℝ))^m := by rw [←hm]; simp [orParameter]
  rw [he] at hh ⊢
  change (1+(n:ℝ)*(q:ℝ))*(1-(1-(1-(q:ℝ))^(m+n))) ≤ _
  rw [sub_sub_cancel,pow_add]
  nlinarith

end QuantitativeSprinkling
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section QuantitativeOpenness
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem operatorBounded_of_quantitative_gap [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (p r : unitInterval)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hsmall : ((r:ℝ)-(p:ℝ))*(4*D)*‖A‖ < 1-(r:ℝ)) : OperatorBounded G r := by
  let a := ((r:ℝ)-(p:ℝ))/(1-(r:ℝ))
  have hden : 0 < 1-(r:ℝ) := sub_pos.mpr hr
  have ha : 0 < a := div_pos (sub_pos.mpr hpr) hden
  obtain ⟨m,q,hq,hqp⟩ := exists_orParameter_small p (hpr.trans hr) (min a 1)
    (lt_min ha zero_lt_one) (min_le_right _ _)
  have hq0 : (0:ℝ) < q := by
    by_contra hn
    have hqe : q = 0 := Subtype.ext ((le_of_not_gt hn).antisymm q.2.1)
    have hpe : p = 0 := by rw [←hqp,hqe]; apply Subtype.ext; simp [orParameter]
    exact (ne_of_gt hp) hpe
  let n := ⌈a/(q:ℝ)⌉₊
  have hna : a ≤ (n:ℝ)*(q:ℝ) := (div_le_iff₀ hq0).mp (Nat.le_ceil _)
  have han : (n:ℝ)*(q:ℝ) < a+(q:ℝ) := by
    have hn := Nat.ceil_lt_add_one (div_nonneg ha.le hq0.le)
    have hh := mul_lt_mul_of_pos_right hn hq0
    dsimp only [n] at *
    field_simp at hh
    nlinarith
  have hn2 : (n:ℝ)*(q:ℝ) < 2*a := by linarith [hq.trans (min_le_left _ _)]
  have hbase : (2*a)*(2*D)*‖A‖ < 1 := by
    rw [show (2*a)*(2*D)*‖A‖ = (((r:ℝ)-(p:ℝ))*(4*D)*‖A‖)/(1-(r:ℝ)) by dsimp [a]; ring]
    exact (div_lt_one hden).mpr hsmall
  have hnsmall : (q:ℝ)*(2*D)*(n:ℝ)*‖A‖ < 1 := by
    have hs := mul_le_mul_of_nonneg_right hn2.le (show 0 ≤ (2*(D:ℝ))*‖A‖ by positivity)
    nlinarith
  obtain ⟨B,hB,_⟩ := sprinkling_iterated_bound G hloc q m D hD A (hqp ▸ hA) n hnsmall
  apply operatorBounded_of_le G (q := orParameter q (m+n)) ?_ ⟨B,hB⟩
  have hgap := orParameter_gap_bound p q m n hqp
  have hae : a*(1-(r:ℝ)) = (r:ℝ)-(p:ℝ) := div_mul_cancel₀ _ (ne_of_gt hden)
  have hs := mul_le_mul_of_nonneg_right hna hden.le
  change (r:ℝ) ≤ (orParameter q (m+n):ℝ)
  nlinarith [mul_nonneg (Nat.cast_nonneg n) q.2.1]

 

theorem norm_gap_lower_of_endpoint_unbounded [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ)
    (hD : ∀ x, degree G x ≤ D) (p r : unitInterval)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hu : ¬OperatorBounded G r) :
    1-(r:ℝ) ≤ ((r:ℝ)-(p:ℝ))*(4*D)*‖A‖ := by
  by_contra h
  exact hu (operatorBounded_of_quantitative_gap G hloc D hD p r hp hpr hr A hA (lt_of_not_ge h))

end QuantitativeOpenness
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

theorem maxSusceptibility_le [Nonempty V] (G : BondGraph V E) (p : unitInterval)
    (C : ℝ) (hC : ∀ x, susceptibility G p x ≤ C) : maxSusceptibility G p ≤ C := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x,rfl⟩
  exact hC x

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
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SourceNormRatio
attribute [local instance] Classical.propDecidable Classical.decEq

theorem critical_norm_inverse_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hp₁ : (pc G:ℝ) < 1) (hu : ¬OperatorBounded G (pc G)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : unitInterval), 0 < p → p < pc G →
      ∀ T : Hilbert V →L[ℂ] Hilbert V, HasKernel G p T →
        c/((pc G:ℝ)-(p:ℝ)) ≤ ‖T‖ := by
  obtain ⟨D,hDp,hD⟩ := exists_degree_bound G hqt
  have hDpos : 0 < (4*(D:ℝ)) := by positivity
  refine ⟨(1-(pc G:ℝ))/(4*D),div_pos (sub_pos.mpr hp₁) hDpos,?_⟩
  intro p hp hpq T hT
  have hh := norm_gap_lower_of_endpoint_unbounded G hloc D hD p (pc G) hp hpq hp₁ T hT hu
  apply (div_le_iff₀ (sub_pos.mpr (show (p:ℝ)<(pc G:ℝ) from hpq))).mpr
  apply (div_le_iff₀ hDpos).mpr
  nlinarith

 

theorem critical_normRatio_subpower
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (hu : ¬OperatorBounded G (pc G)) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ T : Hilbert V →L[ℂ] Hilbert V, HasKernel G p T →
      1 ≤ maxSusceptibility G p/‖T‖ ∧
      maxSusceptibility G p/‖T‖ ≤ K*((pc G:ℝ)-(p:ℝ))^(-η) := by
  obtain ⟨c,hc,hm⟩ := critical_norm_inverse_lower G hloc hqt hp₁ hu
  obtain ⟨D,hD,hχ⟩ := almost_linear_susceptibility G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin η hη
  refine ⟨D/c,div_pos hD hc,?_⟩
  intro p hp hpq T hT
  have hδ : 0 < (pc G:ℝ)-(p:ℝ) := sub_pos.mpr hpq
  have hnorm : 0 < ‖T‖ := zero_lt_one.trans_le (hT.norm_one_le G p T)
  have hM := hm p ((half_pos hp₀).trans_le hp) hpq T hT
  have hχb := maxSusceptibility_le G p _ (hχ p hpq)
  have he : ((pc G:ℝ)-(p:ℝ))^(-1-η)*((pc G:ℝ)-(p:ℝ)) = ((pc G:ℝ)-(p:ℝ))^(-η) := by
    calc
      _ = ((pc G:ℝ)-(p:ℝ))^(-1-η)*((pc G:ℝ)-(p:ℝ))^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hδ]; congr 1; ring
  refine ⟨(one_le_div hnorm).mpr (hT.norm_le_maxSusceptibility G hloc hqt p hpq T),?_⟩
  calc
    maxSusceptibility G p/‖T‖ ≤ (D*((pc G:ℝ)-(p:ℝ))^(-1-η))/(c/((pc G:ℝ)-(p:ℝ))) :=
      div_le_div₀ (mul_nonneg hD.le (Real.rpow_nonneg hδ.le _)) hχb (div_pos hc hδ) hM
    _ = (D/c)*((pc G:ℝ)-(p:ℝ))^(-η) := by rw [←he]; field_simp

end SourceNormRatio
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_ScaleLimits
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic scale limits and quantitative parameter estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open Filter
open scoped Topology

 

theorem log_sublinear_of_subexp (f : ℕ → ℝ) (hf : ∀ n, 1 ≤ f n)
    (hb : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧ ∀ n, f n ≤ K*Real.exp (η*(n:ℝ))) :
    Tendsto (fun n => Real.log (f n)/(n:ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,hbK⟩ := hb (ε/2) (half_pos hε)
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (Real.log K)
  filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlog := Real.log_le_log (zero_lt_one.trans_le (hf n)) (hbK n)
  rw [Real.log_mul hK.ne' (Real.exp_pos _).ne',Real.log_exp] at hlog
  have hdiv := (div_le_div_of_nonneg_right hlog hnpos.le)
  rw [add_div,mul_div_cancel_right₀ _ hnpos.ne'] at hdiv
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Real.log_nonneg (hf n)) hnpos.le)]
  linarith only [hdiv,hn]

 
theorem tendsto_atTop_of_div_nat_pos (f : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : Tendsto (fun n => f n/(n:ℝ)) atTop (𝓝 L)) : Tendsto f atTop atTop := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos hL hf
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact mul_div_cancel₀ (f n) (by exact_mod_cast (show n ≠ 0 by omega))

 
theorem tendsto_exp_of_div_nat_neg (f : ℕ → ℝ) (L : ℝ) (hL : L < 0)
    (hf : Tendsto (fun n => f n/(n:ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n => Real.exp (f n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => -f n/(n:ℝ)) atTop (𝓝 (-L)) := by
    simpa only [neg_div] using hf.neg
  have ht := tendsto_atTop_of_div_nat_pos (fun n => -f n) (-L) (neg_pos.mpr hL) hn
  simpa only [Function.comp_def,neg_neg] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht

 

theorem corridor_scale_limits (r C₁ : ℝ) (J : ℕ) (hr : 0 < r) (hC₁ : 0 < C₁) (hJ : 0 < J)
    (R : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0)) :
    let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
    let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
    Tendsto k atTop atTop ∧
    Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) ∧
    Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => Real.log (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  dsimp only
  let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
  let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
  have hkt : Tendsto k atTop atTop :=
    tendsto_nat_ceil_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hr)
  have hk : Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) :=
    (tendsto_nat_ceil_mul_div_atTop hr.le).comp tendsto_natCast_atTop_atTop
  have hkplus : Tendsto (fun n => ((k n:ℝ)+1)/(n:ℝ)) atTop (𝓝 r) := by
    simpa only [add_div,add_zero] using hk.add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  have hkTop : Tendsto (fun n => (k n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num))
      (tendsto_natCast_atTop_atTop.comp hkt)
  have hlogk : Tendsto (fun n => Real.log ((k n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) := by
    have hl : Tendsto (fun n => Real.log ((k n:ℝ)+1)/((k n:ℝ)+1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
        (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hkTop
    have hh := hl.mul hkplus
    rw [zero_mul] at hh
    apply hh.congr
    intro n
    have hn : (k n:ℝ)+1 ≠ 0 := by positivity
    field_simp
  have hupper : Tendsto (fun n : ℕ => ((J:ℝ)+1)/(n:ℝ) + C₁*(Real.log ((k n:ℝ)+1)/(n:ℝ) + Real.log (R n)/(n:ℝ))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat ((J:ℝ)+1)).add ((hlogk.add hlogR).const_mul C₁)
  have hjlim : Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hprod : 1 ≤ ((k n:ℝ)+1)*R n := by nlinarith only [hR n,(Nat.cast_nonneg (k n) : (0:ℝ) ≤ _)]
    have harg : 0 ≤ C₁*Real.log (((k n:ℝ)+1)*R n) := mul_nonneg hC₁.le (Real.log_nonneg hprod)
    have hceil := (Nat.ceil_lt_add_one harg).le
    have he : Real.log (((k n:ℝ)+1)*R n) = Real.log ((k n:ℝ)+1)+Real.log (R n) :=
      Real.log_mul (by positivity) (zero_lt_one.trans_le (hR n)).ne'
    dsimp only [j]
    push_cast
    rw [←add_div,←mul_div_assoc,←add_div,←he]
    exact (div_le_div_of_nonneg_right (by linarith only [hceil]) hnpos.le)
  refine ⟨hkt,hk,hjlim,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjlim
  · exact Eventually.of_forall (fun n => div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (show 1 ≤ j n by dsimp [j]; omega))) (Nat.cast_nonneg n))
  · exact Eventually.of_forall (fun n => div_le_div_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg (j n))) (Nat.cast_nonneg n))

 

theorem exists_corridor_scales_of_slopes
    (ρ p₀ C C₁ ε M cm r z : ℝ) (J k₀ : ℕ)
    (hρ : 0 < ρ) (hp₀ : 0 < p₀) (hC₁ : 0 < C₁) (hε : 0 < ε) (hcm : 0 < cm)
    (hJ : 0 < J) (hr : 0 < r) (hz : 0 < z)
    (hzρ : z+r*Real.log ρ < 0) (hzC : z+C*r < 1)
    (m R Q : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n) (hQ : ∀ n, 1 ≤ Q n)
    (hm : ∀ n : ℕ, cm*Real.exp (n:ℝ) ≤ m n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0))
    (hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0)) :
    ∃ (n k : ℕ) (B : ℝ), k₀ ≤ k ∧ 0 < B ∧
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R n)⌉₊
      B*ρ^k ≤ 1/4 ∧ B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^k ≤ ε*p₀^(2*j) ∧ M < B*p₀^(2*j) := by
  let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
  let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
  let B := fun n : ℕ => Real.exp (z*(n:ℝ))
  obtain ⟨hkt,hk,hj,hlogj⟩ := corridor_scale_limits r C₁ J hr hC₁ hJ R hR hlogR
  change Tendsto k atTop atTop at hkt
  change Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) at hk
  change Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) at hj
  change Tendsto (fun n => Real.log (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) at hlogj
  have hn : Tendsto (fun n : ℕ => (n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_natCast_div_add_atTop (0:ℝ)
  have hβ (n) : Real.exp ((j n:ℝ)*(2*Real.log p₀)) = p₀^(2*j n) := by
    rw [show (j n:ℝ)*(2*Real.log p₀) = ((2*j n:ℕ):ℝ)*Real.log p₀ by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log hp₀]
  have hjpos (n) : (0:ℝ) < j n := Nat.cast_pos.mpr (by dsimp [j]; omega)
  have hlim₁ : Tendsto (fun n : ℕ => (z*(n:ℝ)+(k n:ℝ)*Real.log ρ)/(n:ℝ)) atTop (𝓝 (z+r*Real.log ρ)) := by
    simpa only [mul_one,div_mul_eq_mul_div,←mul_div_assoc,←add_div] using
      (hn.const_mul z).add (hk.mul_const (Real.log ρ))
  have hdec₁ := tendsto_exp_of_div_nat_neg _ _ hzρ hlim₁
  have hlim₂ : Tendsto (fun n : ℕ =>
      (2*Real.log (R n)+Real.log (Q n)+(k n:ℝ)*Real.log ρ-(j n:ℝ)*(2*Real.log p₀))/(n:ℝ))
      atTop (𝓝 (r*Real.log ρ)) := by
    simpa only [mul_zero,zero_add,zero_mul,sub_zero,div_mul_eq_mul_div,←mul_div_assoc,←add_div,←sub_div] using
      (((hlogR.const_mul 2).add hlogQ).add (hk.mul_const (Real.log ρ))).sub (hj.mul_const (2*Real.log p₀))
  have hsl₂ : r*Real.log ρ < 0 := by linarith only [hz,hzρ]
  have hdec₂ := tendsto_exp_of_div_nat_neg _ _ hsl₂ hlim₂
  have hlim₃ : Tendsto (fun n : ℕ =>
      (z*(n:ℝ)+Real.log (j n:ℝ)+C*(k n:ℝ)-(n:ℝ))/(n:ℝ)) atTop (𝓝 (z+C*r-1)) := by
    simpa only [mul_one,add_zero,←mul_div_assoc,←add_div,←sub_div] using
      (((hn.const_mul z).add hlogj).add (hk.const_mul C)).sub hn
  have hdec₃ := tendsto_exp_of_div_nat_neg _ _ (sub_neg.mpr hzC) hlim₃
  have hlim₄ : Tendsto (fun n : ℕ =>
      (z*(n:ℝ)+(j n:ℝ)*(2*Real.log p₀))/(n:ℝ)) atTop (𝓝 z) := by
    simpa only [mul_one,zero_mul,add_zero,div_mul_eq_mul_div,←mul_div_assoc,←add_div] using
      (hn.const_mul z).add (hj.mul_const (2*Real.log p₀))
  have hgrow := Real.tendsto_exp_atTop.comp (tendsto_atTop_of_div_nat_pos _ _ hz hlim₄)
  have hfinal : ∀ᶠ n : ℕ in atTop,
      k₀ ≤ k n ∧ B n*ρ^(k n) ≤ 1/4 ∧
      B n*(j n:ℝ)*Real.exp (C*(k n:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^(k n) ≤ ε*p₀^(2*j n) ∧ M < B n*p₀^(2*j n) := by
    filter_upwards [hkt.eventually_ge_atTop k₀,
      hdec₁.eventually_lt_const (show (0:ℝ) < 1/4 by norm_num),
      hdec₂.eventually_lt_const hε,hdec₃.eventually_lt_const hcm,
      hgrow.eventually_gt_atTop M] with n hk₀ h₁ h₂ h₃ h₄
    have heρ : Real.exp ((k n:ℝ)*Real.log ρ) = ρ^(k n) := by rw [Real.exp_nat_mul,Real.exp_log hρ]
    have heR : Real.exp (2*Real.log (R n)) = (R n)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log (zero_lt_one.trans_le (hR n))] using Real.exp_nat_mul (Real.log (R n)) 2
    simp only [Real.exp_add,heρ] at h₁
    simp only [Real.exp_sub,Real.exp_add,heR,Real.exp_log (zero_lt_one.trans_le (hQ n)),heρ,hβ n] at h₂
    simp only [Real.exp_sub,Real.exp_add,Real.exp_log (hjpos n)] at h₃
    change M < Real.exp (z*(n:ℝ)+(j n:ℝ)*(2*Real.log p₀)) at h₄
    rw [Real.exp_add,hβ n] at h₄
    refine ⟨hk₀,h₁.le,?_,(div_le_iff₀ (pow_pos hp₀ _)).mp h₂.le,h₄⟩
    exact ((div_le_iff₀ (Real.exp_pos _)).mp h₃.le).trans (hm n)
  obtain ⟨n,hn⟩ := hfinal.exists
  exact ⟨n,k n,B n,hn.1,Real.exp_pos _,hn.2⟩

 

theorem exists_corridor_scales
    (ρ p₀ C C₁ ε M cm : ℝ) (J k₀ : ℕ)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hp₀ : 0 < p₀) (hC : 0 < C)
    (hC₁ : 0 < C₁) (hε : 0 < ε) (hcm : 0 < cm) (hJ : 0 < J)
    (m R Q : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n) (hQ : ∀ n, 1 ≤ Q n)
    (hm : ∀ n : ℕ, cm*Real.exp (n:ℝ) ≤ m n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0))
    (hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0)) :
    ∃ (n k : ℕ) (B : ℝ), k₀ ≤ k ∧ 0 < B ∧
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R n)⌉₊
      B*ρ^k ≤ 1/4 ∧ B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^k ≤ ε*p₀^(2*j) ∧ M < B*p₀^(2*j) := by
  let r := 1/(4*(C+1))
  let z := min (1/4) (-(r*Real.log ρ)/2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hlog : Real.log ρ < 0 := by simpa only [Real.log_one] using Real.log_lt_log hρ hρ₁
  have hz : 0 < z := lt_min (by norm_num) (half_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hr hlog)))
  have hzr : z+r*Real.log ρ < 0 := by
    have hh : z ≤ -(r*Real.log ρ)/2 := min_le_right _ _
    linarith only [hh,mul_neg_of_pos_of_neg hr hlog]
  have hzc : z+C*r < 1 := by
    have hz' : z ≤ 1/4 := min_le_left _ _
    have hr' : r*(4*(C+1)) = 1 := div_mul_cancel₀ 1 (by positivity)
    nlinarith only [hz',hr',hr]
  exact exists_corridor_scales_of_slopes ρ p₀ C C₁ ε M cm r z J k₀
    hρ hp₀ hC₁ hε hcm hJ hr hz hzr hzc m R Q hR hQ hm hlogR hlogQ

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
universe u v
variable {V : Type u} {E : Type v}
section LazyOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_lazy (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1/2)
    (x : V) : 1/2 ≤ walkKernel G hloc a x x := by
  have hn : ((neighbors G hloc x).card : ℝ) ≤ D := by
    exact_mod_cast (neighbors_card_le_degree G hloc x).trans (hD x)
  have hh := mul_le_mul_of_nonneg_left hn ha
  simp only [walkKernel,if_true]
  split_ifs <;> linarith

end LazyOrbitReturn
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_CollisionTails
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
section IndependentRawCollisions
attribute [local instance] Classical.propDecidable Classical.decEq



theorem matrixCoeff_norm_le (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ ‖A‖ := by
  apply (lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) (A (lp.single 2 y (1:ℂ))) x).trans
  simpa using A.le_opNorm (lp.single 2 y (1:ℂ))

end IndependentRawCollisions
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical boundedness of the percolation operator under unimodularity and simple edge indexing. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Filter
open scoped Topology


theorem criticalApproach_half (q : unitInterval) (n : ℕ) :
    (q:ℝ)/2 ≤ (criticalApproach q n : ℝ) := by
  have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
  change _ ≤ (q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ))
  nlinarith only [he,q.2.1]

theorem criticalApproach_lt (q : unitInterval) (hq : 0 < (q:ℝ)) (n : ℕ) :
    criticalApproach q n < q := by
  change (q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ)) < q
  exact sub_lt_self _ (mul_pos (half_pos hq) (Real.exp_pos _))

theorem criticalApproach_gap (q : unitInterval) (n : ℕ) :
    (q:ℝ)-(criticalApproach q n:ℝ) = (q:ℝ)/2*Real.exp (-(n:ℝ)) := by
  change (q:ℝ)-((q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ))) = _
  ring

 

theorem log_sublinear_of_geometric_gap (f : ℕ → ℝ) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hf : ∀ n, 1 ≤ f n)
    (hb : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, f n ≤ K*(p₀*Real.exp (-(n:ℝ)))^(-η)) :
    Tendsto (fun n => Real.log (f n)/(n:ℝ)) atTop (𝓝 0) := by
  apply log_sublinear_of_subexp f hf
  intro η hη
  obtain ⟨K,hK,hbK⟩ := hb η hη
  refine ⟨K*p₀^(-η),mul_pos hK (Real.rpow_pos_of_pos hp₀ _),fun n => ?_⟩
  have he : (p₀*Real.exp (-(n:ℝ)))^(-η) = p₀^(-η)*Real.exp (η*(n:ℝ)) := by
    rw [Real.mul_rpow hp₀.le (Real.exp_pos _).le,←Real.exp_mul]
    congr 2
    ring
  simpa only [he,mul_assoc] using hbK n

universe u v
variable {V : Type u} {E : Type v}
section AnalyticCritical
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Infinite V] [Nonempty E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

 

theorem critical_bounded_of_fixed_data
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite) :
    OperatorBounded G (pc G) := by
  by_contra hu
  obtain ⟨C,hC,J,hJ,C₁,hC₁,k₀,hk₀,ε,M,hε,_,hbad⟩ :=
    exists_finite_scale_obstruction_bs G hG hconn hloc hqt a ha root weight htr hcov hw hw1 c hc hmin
      P hpos hsym hP hdiag hρ d hd hpcrit hpcrit₁
  let p := criticalApproach (pc G)
  have hpnear (n) : (pc G:ℝ)/2 ≤ (p n:ℝ) := criticalApproach_half (pc G) n
  have hp (n) : p n < pc G := criticalApproach_lt (pc G) hpcrit n
  have hpzero (n) : 0 < (p n:ℝ) := (half_pos hpcrit).trans_le (hpnear n)
  let A := fun n => Classical.choose (operatorBounded_of_lt_pc G hloc hqt (p n) (hp n))
  have hA (n) : HasKernel G (p n) (A n) := Classical.choose_spec (operatorBounded_of_lt_pc G hloc hqt (p n) (hp n))
  let m := fun n => ‖A n‖
  let R := fun n => maxSusceptibility G (p n)/m n
  let Q := fun n => rootTriangle G root weight (p n:ℝ)
  have hR (n) : 1 ≤ R n := (one_le_div (zero_lt_one.trans_le ((hA n).norm_one_le G (p n) (A n)))).mpr
    ((hA n).norm_le_maxSusceptibility G hloc hqt (p n) (hp n) (A n))
  have hQ (n) : 1 ≤ Q n := rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 (p n) (hp n)
  have hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0) := by
    apply log_sublinear_of_geometric_gap R ((pc G:ℝ)/2) (half_pos hpcrit) hR
    intro η hη
    obtain ⟨K,hK,hRK⟩ := critical_normRatio_subpower G hloc hconn hqt hh root weight (vertexAut G)
      (Set.Subset.refl _) htr hcov hw hw1 hpcrit hpcrit₁ hfin hu η hη
    refine ⟨K,hK,fun n => ?_⟩
    simpa only [p,criticalApproach_gap] using (hRK (p n) (hpnear n) (hp n) (A n) (hA n)).2
  have hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0) := by
    apply log_sublinear_of_geometric_gap Q ((pc G:ℝ)/2) (half_pos hpcrit) hQ
    intro η hη
    obtain ⟨K,hK,hQK⟩ := critical_rootTriangle_subpower G hloc hconn hqt hh root weight (vertexAut G)
      (Set.Subset.refl _) htr hcov hw hw1 hpcrit hpcrit₁ hfin η hη
    refine ⟨K,hK,fun n => ?_⟩
    simpa only [p,criticalApproach_gap] using hQK (p n) (hpnear n) (hp n)
  obtain ⟨cm,hcm,hm⟩ := critical_norm_inverse_lower G hloc hqt hpcrit₁ hu
  have hmlower (n : ℕ) : (cm/((pc G:ℝ)/2))*Real.exp (n:ℝ) ≤ m n := by
    have hh := hm (p n) (hpzero n) (hp n) (A n) (hA n)
    rw [show (pc G:ℝ)-(p n:ℝ) = (pc G:ℝ)/2*Real.exp (-(n:ℝ)) from criticalApproach_gap (pc G) n,
      Real.exp_neg,div_mul_eq_div_div,div_inv_eq_mul] at hh
    exact hh
  have hρpos : 0 < ‖P‖ := by
    let x : V := Classical.arbitrary V
    have hh := (hdiag x).trans ((Complex.re_le_norm _).trans (matrixCoeff_norm_le P x x))
    linarith only [hh]
  obtain ⟨n,k,B,hk,hB,hsmall,htime,herror,hlarge⟩ := exists_corridor_scales
    ‖P‖ ((pc G:ℝ)/2) C C₁ ε M (cm/((pc G:ℝ)/2)) J k₀ hρpos hρ (half_pos hpcrit) hC hC₁ hε
    (div_pos hcm (half_pos hpcrit)) hJ m R Q hR hQ hmlower hlogR hlogQ
  exact hbad (p n) (hpnear n) (hp n) (A n) (hA n) k hk B hB hsmall htime herror hlarge

end AnalyticCritical

 

theorem nonempty_bonds_of_connected [Infinite V] (G : BondGraph V E) (hconn : Connected G) : Nonempty E := by
  classical
  by_contra he
  let : IsEmpty E := not_nonempty_iff.mp he
  obtain ⟨x,y,hxy⟩ := exists_pair_ne V
  have hh := conn_univ_of_connected G hconn x y
  have heq : (Set.univ : Set E) = ∅ := Set.eq_empty_of_isEmpty _
  rw [heq,conn_empty_iff] at hh
  exact hxy hh

 

theorem critical_bounded_of_transport_finiteness_bs_oai [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite) :
    OperatorBounded G (pc G) := by
  classical
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  let : Nonempty E := nonempty_bonds_of_connected G hconn
  let : Nonempty ι := ⟨(hcov (Classical.arbitrary V)).choose⟩
  let c := ∑ i, (weight i)⁻¹
  have hc : 0 < c := Finset.sum_pos (fun i _ => inv_pos.mpr (hw i)) Finset.univ_nonempty
  have hmin (i) : 1 ≤ c*weight i := by
    have hi : (weight i)⁻¹ ≤ c := Finset.single_le_sum
      (fun j _ => (inv_pos.mpr (hw j)).le) (Finset.mem_univ i)
    simpa only [inv_mul_cancel₀ (hw i).ne'] using mul_le_mul_of_nonneg_right hi (hw i).le
  obtain ⟨d,P,hdpos,hd,hρ,hPs,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  let a := (1:ℝ)/(2*d)
  have hdr : (0:ℝ) < d := Nat.cast_pos.mpr hdpos
  have ha : 0 < a := by dsimp [a]; positivity
  have had : a*d = 1/2 := by dsimp [a]; field_simp
  have hPe : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ) := hP
  have hPpos : PositiveRealMatrix P := by
    intro x y
    rw [hPe]
    refine ⟨rfl,?_⟩
    exact walkKernel_nonneg G hloc d hd a ha.le (by rw [had]; norm_num) x y
  have hdiag (x) : 1/2 ≤ (matrixCoeff P x x).re := by
    rw [hPe,Complex.ofReal_re]
    exact walkKernel_lazy G hloc d hd a ha.le had.le x
  exact critical_bounded_of_fixed_data G hG hconn hloc hqt hh a ha root weight htr hcov hw hw1 c hc hmin
    P hPpos hPs.isSelfAdjoint hPe hdiag hρ d hd (pc_pos G hloc hqt)
    (pc_lt_one_of_nonamenable G hconn hloc hqt hh) hfin

end Percolation





end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Percolation.critical_bounded_of_transport_finiteness_bs_oai.{u, v, u_1} := @OAI.Percolation.critical_bounded_of_transport_finiteness_bs_oai.{u, v, u_1}
