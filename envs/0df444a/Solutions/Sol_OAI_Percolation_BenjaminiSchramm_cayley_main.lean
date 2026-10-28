-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.cayley_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:15:56.87259+00:00
-- url     : https://prove2.me/submissions/aec79b74-080f-44c8-b61d-2a4eec62e8ce

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_Percolation_critical_bounded_of_transport_finiteness_bs

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

theorem twoPoint_one (h : Connected G) (x y : V) : twoPoint G 1 x y = 1 := by
  have hv : law (E := E) 1 {ω | Conn G ω x y} = 1 := by
    rw [law_one]
    exact Measure.dirac_apply_of_mem (conn_univ_of_connected G h x y)
  change (law 1 {ω | Conn G ω x y}).toReal = 1
  rw [hv]
  norm_num

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

 
theorem operatorNorm_of_hasKernel {G : BondGraph V E} {p : unitInterval}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G p A) :
    operatorNorm G p = ENNReal.ofReal ‖A‖ := by
  have he : {r | ∃ B : Hilbert V →L[ℂ] Hilbert V,
      HasKernel G p B ∧ r = ENNReal.ofReal ‖B‖} = {ENNReal.ofReal ‖A‖} := by
    ext r
    constructor
    · rintro ⟨B, hB, rfl⟩
      rw [hB.unique hA]
      exact Set.mem_singleton _
    · intro hr
      exact ⟨A, hA, Set.mem_singleton_iff.mp hr⟩
  change sInf _ = _
  rw [he, sInf_singleton]

theorem operatorNorm_eq_top_iff (G : BondGraph V E) (p : unitInterval) :
    operatorNorm G p = ⊤ ↔ ¬ OperatorBounded G p := by
  constructor
  · intro h ⟨A, hA⟩
    rw [operatorNorm_of_hasKernel hA] at h
    exact ENNReal.ofReal_ne_top h
  · intro h
    unfold operatorNorm
    have he : {r | ∃ A : Hilbert V →L[ℂ] Hilbert V,
        HasKernel G p A ∧ r = ENNReal.ofReal ‖A‖} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨A, hA, _⟩
      exact h ⟨A, hA⟩
    rw [he, sInf_empty]

theorem operatorNorm_lt_top_iff (G : BondGraph V E) (p : unitInterval) :
    operatorNorm G p < ⊤ ↔ OperatorBounded G p := by
  rw [lt_top_iff_ne_top, ne_eq, operatorNorm_eq_top_iff, not_not]

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

section PositiveColumn
attribute [local instance] Classical.propDecidable

 

theorem no_positive_lower_bound [Infinite V] (f : Hilbert V) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) : False := by
  have hs : Summable (fun x => ‖f x‖ ^ (2 : ℕ)) := by
    simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f).summable
  have hconst : Summable (fun _ : V => c ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg c)
      (fun x => pow_le_pow_left₀ hc.le (hf x) 2) hs
  have hz : c ^ 2 = 0 := (summable_const_iff _).mp hconst
  nlinarith

 

theorem not_operatorBounded_of_positive_column [Infinite V]
    (G : BondGraph V E) (p : unitInterval) (y : V) {c : ℝ}
    (hc : 0 < c) (hcol : ∀ x, c ≤ twoPoint G p x y) :
    ¬ OperatorBounded G p := by
  rintro ⟨A, hA⟩
  apply no_positive_lower_bound (A (lp.single 2 y (1 : ℂ))) hc
  intro x
  rw [hA x y, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (twoPoint_nonneg G p x y)]
  exact hcol x

@[simp] theorem not_operatorBounded_one [Infinite V] (G : BondGraph V E)
    (h : Connected G) : ¬ OperatorBounded G 1 := by
  apply not_operatorBounded_of_positive_column G 1 (Classical.arbitrary V)
    (c := 1) (by norm_num)
  intro x
  rw [twoPoint_one G h]

@[simp] theorem operatorNorm_one [Infinite V] (G : BondGraph V E)
    (h : Connected G) : operatorNorm G 1 = ⊤ :=
  (operatorNorm_eq_top_iff G 1).mpr (not_operatorBounded_one G h)

end PositiveColumn

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

theorem operatorNorm_mono : Monotone (operatorNorm G) := by
  intro p q hpq
  by_cases hq : OperatorBounded G q
  · obtain ⟨B, hB⟩ := hq
    obtain ⟨A, hnorm, hA⟩ := exists_operator_of_matrix_domination
      (twoPoint G q) (twoPoint G p) (twoPoint_nonneg G q)
      (fun x y => (abs_of_nonneg (twoPoint_nonneg G p x y)).le.trans
        (twoPoint_mono G x y hpq)) B hB
    rw [operatorNorm_of_hasKernel hA, operatorNorm_of_hasKernel hB]
    exact ENNReal.ofReal_le_ofReal hnorm
  · rw [(operatorNorm_eq_top_iff G q).mpr hq]
    exact le_top

end NormOrder

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

section Endpoint
open Filter Topology
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E] (G : BondGraph V E)

 

theorem operatorNorm_eq_sup_below (q : unitInterval) (hq : 0 < q) :
    operatorNorm G q = sSup {r | ∃ p : unitInterval, p < q ∧ r = operatorNorm G p} := by
  let S : ℝ≥0∞ := sSup {r | ∃ p : unitInterval, p < q ∧ r = operatorNorm G p}
  change operatorNorm G q = S
  apply le_antisymm
  · by_cases hS : S = ⊤
    · rw [hS]
      exact le_top
    obtain ⟨p, hp, hpq, hlim⟩ := exists_seq_strictMono_tendsto' hq
    have hbound (n : ℕ) : operatorNorm G (p n) ≤ S :=
      le_sSup ⟨p n, (hpq n).2, rfl⟩
    have hbounded (n : ℕ) : OperatorBounded G (p n) :=
      (operatorNorm_lt_top_iff G (p n)).mp ((hbound n).trans_lt (lt_top_iff_ne_top.mpr hS))
    choose A hA using hbounded
    have hnorm (n : ℕ) : ‖A n‖ ≤ S.toReal := by
      apply (ENNReal.ofReal_le_iff_le_toReal hS).mp
      rw [← operatorNorm_of_hasKernel (hA n)]
      exact hbound n
    have hmatrix (x y : V) : Tendsto (fun n => A n (lp.single 2 y (1 : ℂ)) x)
        atTop (𝓝 (twoPoint G q x y : ℂ)) := by
      have ht := (Complex.continuous_ofReal.tendsto (twoPoint G q x y)).comp
        (twoPoint_tendsto_of_monotone G p hp.monotone q (fun n => (hpq n).2.le) hlim x y)
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      funext n
      exact hA n x y
    obtain ⟨B, hBn, hB⟩ := exists_operator_of_matrix_tendsto A
      (fun x y => (twoPoint G q x y : ℂ)) ENNReal.toReal_nonneg hnorm hmatrix
    rw [operatorNorm_of_hasKernel hB]
    exact (ENNReal.ofReal_le_iff_le_toReal hS).mpr hBn
  · apply sSup_le
    rintro r ⟨p, hp, rfl⟩
    exact operatorNorm_mono G hp.le

end Endpoint

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

theorem measurableSet_infinite_cluster [Countable E] (G : BondGraph V E) (x : V) :
    MeasurableSet {ω | (cluster G ω x).Infinite} := by
  rw [infinite_cluster_eq_iInter]
  exact MeasurableSet.iInter (measurableSet_clusterLarge G x)

 
theorem association_decreasing [Countable E] (p : unitInterval)
    (A B : ℕ → Set (Set E)) (hA : Antitone A) (hB : Antitone B)
    (huA : ∀ n, IsUpperSet (A n)) (huB : ∀ n, IsUpperSet (B n))
    (hfA : ∀ n, FiniteWitness (A n)) (hfB : ∀ n, FiniteWitness (B n)) :
    (law p).real (⋂ n, A n) * (law p).real (⋂ n, B n) ≤
      (law p).real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
  have hlim (C : ℕ → Set (Set E)) (hm : Antitone C) (hC : ∀ n, MeasurableSet (C n)) :
      Tendsto (fun n => (law p).real (C n)) atTop (𝓝 ((law p).real (⋂ n, C n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_measure_iInter_atTop (fun n => (hC n).nullMeasurableSet) hm
        ⟨0, measure_ne_top _ _⟩)
  have hmA n := measurableSet_finiteWitness (A n) (huA n) (hfA n)
  have hmB n := measurableSet_finiteWitness (B n) (huB n) (hfB n)
  have h := le_of_tendsto_of_tendsto ((hlim A hA hmA).mul (hlim B hB hmB))
    (hlim (fun n => A n ∩ B n) (fun m n h => Set.inter_subset_inter (hA h) (hB h))
      (fun n => (hmA n).inter (hmB n)))
    (Filter.Eventually.of_forall fun n =>
      association_finiteWitness p (A n) (B n) (huA n) (huB n) (hfA n) (hfB n))
  simpa only [Set.iInter_inter_distrib] using h

 

theorem association_infinite_cluster [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (law p).real {ω | (cluster G ω x).Infinite} *
      (law p).real {ω | (cluster G ω y).Infinite} ≤
      (law p).real {ω | (cluster G ω x).Infinite ∧ (cluster G ω y).Infinite} := by
  rw [infinite_cluster_eq_iInter, infinite_cluster_eq_iInter]
  change _ ≤ (law p).real ({ω | (cluster G ω x).Infinite} ∩
    {ω | (cluster G ω y).Infinite})
  rw [infinite_cluster_eq_iInter, infinite_cluster_eq_iInter]
  exact association_decreasing p _ _ (clusterLarge_antitone G x) (clusterLarge_antitone G y)
    (clusterLarge_upper G x) (clusterLarge_upper G y)
    (finiteWitness_clusterLarge G x) (finiteWitness_clusterLarge G y)

end ClusterEvents

section Automorphisms
attribute [local instance] Classical.propDecidable

theorem infinite_cluster_aut [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x : V) :
    (law p).real {ω | (cluster G ω (a x)).Infinite} =
      (law p).real {ω | (cluster G ω x).Infinite} := by
  have he : {ω | (cluster G ω (a x)).Infinite} =
      (fun ω => b ⁻¹' ω) ⁻¹' {ω | (cluster G ω x).Infinite} := by
    ext ω
    change (cluster G ω (a x)).Infinite ↔ (cluster G (b ⁻¹' ω) x).Infinite
    rw [← cluster_aut G h]
    exact Set.infinite_image_iff (fun _ _ _ _ hab => a.injective hab)
  unfold Measure.real
  rw [he, ← Measure.map_apply (measurable_set_preimage b)
    (measurableSet_infinite_cluster G x), law_map_preimage_equiv]

 
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

theorem twoPoint_pos [Countable E] (G : BondGraph V E) (hG : Connected G)
    (p : unitInterval) (hp : 0 < p) (x y : V) : 0 < twoPoint G p x y := by
  obtain ⟨s, _, hs⟩ := finiteWitness_conn G x y Set.univ (conn_univ_of_connected G hG x y)
  have hpos : 0 < (law p).real {ω | (s : Set E) ⊆ ω} := by
    rw [finite_open_probability]
    exact pow_pos hp _
  apply lt_of_lt_of_le hpos
  exact measureReal_mono (fun _ hω => conn_mono G hω hs)

end Automorphisms

section UniquenessThreshold
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] in
 
theorem association_infinite_conn (G : BondGraph V E) (p : unitInterval) (x y z : V) :
    (law p).real {ω | (cluster G ω x).Infinite} * twoPoint G p y z ≤
      (law p).real {ω | (cluster G ω x).Infinite ∧ Conn G ω y z} := by
  have h := association_decreasing p (clusterLarge G x) (fun _ => {ω | Conn G ω y z})
    (clusterLarge_antitone G x) antitone_const (clusterLarge_upper G x)
    (fun _ _ _ hsub hconn => conn_mono G hsub hconn) (finiteWitness_clusterLarge G x)
    (fun _ => finiteWitness_conn G y z)
  simpa only [← infinite_cluster_eq_iInter, Set.iInter_const, twoPoint, Measure.real, Set.inter_def, Set.mem_ofPred_eq] using h

omit [Countable V] in
theorem survival_pos_of_survival_pos (G : BondGraph V E) (hG : Connected G)
    (p : unitInterval) (hp : 0 < p) {x : V}
    (hx : 0 < (law p).real {ω | (cluster G ω x).Infinite}) (y : V) :
    0 < (law p).real {ω | (cluster G ω y).Infinite} := by
  apply lt_of_lt_of_le (mul_pos hx (twoPoint_pos G hG p hp x y))
  refine (association_infinite_conn G p x x y).trans (measureReal_mono ?_)
  rintro ω ⟨hi, hc⟩
  change (cluster G ω y).Infinite
  rwa [← cluster_eq_of_conn G ω hc]

omit [Countable V] [Countable E] in
theorem exists_infinite_cluster_iff (G : BondGraph V E) (ω : Set E) :
    (infiniteClusters G ω).Nonempty ↔ ∃ x, (cluster G ω x).Infinite := by
  constructor
  · rintro ⟨C, hi, x, rfl⟩
    exact ⟨x, hi⟩
  · rintro ⟨x, hx⟩
    exact ⟨cluster G ω x, hx, x, rfl⟩

omit [Countable V] [Countable E] in
theorem unique_infinite_cluster_iff (G : BondGraph V E) (ω : Set E) :
    (∃! C, C ∈ infiniteClusters G ω) ↔
      ∃ x, (cluster G ω x).Infinite ∧ ∀ y, (cluster G ω y).Infinite → Conn G ω x y := by
  constructor
  · rintro ⟨C, ⟨hi, x, rfl⟩, hu⟩
    refine ⟨x, hi, fun y hy => ?_⟩
    have he := hu (cluster G ω y) ⟨hy, y, rfl⟩
    have hm := mem_cluster_self G ω y
    rwa [he] at hm
  · rintro ⟨x, hx, hu⟩
    refine ⟨cluster G ω x, ⟨hx, x, rfl⟩, ?_⟩
    rintro C ⟨hi, y, rfl⟩
    exact (cluster_eq_of_conn G ω (hu y hi)).symm

theorem measurableSet_unique_infinite_cluster (G : BondGraph V E) :
    MeasurableSet {ω | ∃! C, C ∈ infiniteClusters G ω} := by
  have he : {ω | ∃! C, C ∈ infiniteClusters G ω} =
      ⋃ x, ({ω | (cluster G ω x).Infinite} ∩
        ⋂ y, ({ω | (cluster G ω y).Infinite}ᶜ ∪ {ω | Conn G ω x y})) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, unique_infinite_cluster_iff,
      imp_iff_not_or]
  rw [he]
  exact MeasurableSet.iUnion fun x => (measurableSet_infinite_cluster G x).inter
    (MeasurableSet.iInter fun y =>
      (measurableSet_infinite_cluster G y).compl.union (measurableSet_conn G x y))

theorem uniform_survival_pos (G : BondGraph V E) (hconn : Connected G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : 0 < p)
    (hpos : 0 < law p {ω | (infiniteClusters G ω).Nonempty}) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x, θ ≤ (law p).real {ω | (cluster G ω x).Infinite} := by
  have hunion : {ω | (infiniteClusters G ω).Nonempty} =
      ⋃ x, {ω | (cluster G ω x).Infinite} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_infinite_cluster_iff]
  rw [hunion] at hpos
  obtain ⟨x, hx⟩ := exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hpos)
  have hxp : 0 < (law p).real {ω | (cluster G ω x).Infinite} :=
    ENNReal.toReal_pos hx.ne' (measure_ne_top _ _)
  have hroot := survival_pos_of_survival_pos G hconn p hp hxp
  obtain ⟨s, hs⟩ := hqt
  have hsn : s.Nonempty := by obtain ⟨o, ho, _⟩ := hs x; exact ⟨o, ho⟩
  let vals := s.image (fun o => (law p).real {ω | (cluster G ω o).Infinite})
  have hv : vals.Nonempty := hsn.image _
  refine ⟨vals.min' hv, ?_, fun y => ?_⟩
  · obtain ⟨o, _, he⟩ := Finset.mem_image.mp (Finset.min'_mem vals hv)
    rw [← he]
    exact hroot o
  · obtain ⟨o, ho, a, b, ha, hay⟩ := hs y
    rw [← hay, infinite_cluster_aut G p ha]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨o, ho, rfl⟩)

 

theorem not_operatorBounded_of_unique [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hqt : QuasiTransitive G) (p : unitInterval)
    (hu : law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1) : ¬ OperatorBounded G p := by
  have hp : 0 < p := by
    by_contra h
    have hp0 : p = 0 := le_antisymm (not_lt.mp h) (bot_le)
    subst p
    simp [law] at hu
  have hpos : 0 < law p {ω | (infiniteClusters G ω).Nonempty} := by
    exact lt_of_lt_of_le (show 0 < law p {ω | ∃! C, C ∈ infiniteClusters G ω} by rw [hu]; exact zero_lt_one)
      (measure_mono fun ω hω => ⟨hω.choose, hω.choose_spec.1⟩)
  obtain ⟨θ, hθ, hroot⟩ := uniform_survival_pos G hconn hqt p hp hpos
  have hue : ∀ᵐ ω ∂law p, ∃! C, C ∈ infiniteClusters G ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_unique_infinite_cluster G)).mpr hu
  refine not_operatorBounded_of_positive_column G p (Classical.arbitrary V) (mul_pos hθ hθ)
    (fun x => ?_)
  refine (mul_le_mul (hroot x) (hroot (Classical.arbitrary V)) hθ.le measureReal_nonneg).trans
    ((association_infinite_cluster G p x (Classical.arbitrary V)).trans ?_)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hue] with ω hω
  intro hi
  obtain ⟨r, _, hconnr⟩ := (unique_infinite_cluster_iff G ω).mp hω
  exact conn_trans G ω (conn_symm G ω (hconnr x hi.1)) (hconnr _ hi.2)

 

theorem ptwo_le_pu [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hqt : QuasiTransitive G) : ptwo G ≤ pu G := by
  unfold pu ptwo
  apply le_sInf
  intro p hp
  apply sSup_le
  intro q hq
  by_contra hqp
  have hb := operatorBounded_of_le G (le_of_lt (not_le.mp hqp)) hq
  exact not_operatorBounded_of_unique G hconn hqt p hp hb

end UniquenessThreshold

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

section InfiniteOrbits
attribute [local instance] Classical.propDecidable



theorem vertexOrbit_infinite [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (x : V) :
    (vertexOrbit G x).Infinite := by
  intro hfin
  obtain ⟨R, hR⟩ := hqt
  choose n hn using (fun y => exists_mem_reachBall (hconn x y))
  have hS : (⋃ o ∈ (R : Set V), ⋃ z ∈ vertexOrbit G x, reachBall G z (n o)).Finite :=
    R.finite_toSet.biUnion fun o _ => hfin.biUnion fun z _ => finite_reachBall hloc z (n o)
  have he : Set.univ ⊆ ⋃ o ∈ (R : Set V), ⋃ z ∈ vertexOrbit G x, reachBall G z (n o) := by
    intro y _
    obtain ⟨o, ho, a, b, hab, hay⟩ := hR y
    simp only [Set.mem_iUnion]
    exact ⟨o, ho, a x, ⟨a, b, hab, rfl⟩, hay ▸ mem_reachBall_aut G hab (hn o)⟩
  exact Set.infinite_univ (hS.subset he)

end InfiniteOrbits

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

 
theorem sum_twoPoint_le_norm_card (G : BondGraph V E) (p : unitInterval)
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G p A) (F : Finset V) :
    ∑ x ∈ F, ∑ y ∈ F, twoPoint G p x y ≤ ‖A‖ * F.card := by
  have he : inner ℂ (deltaSum F) (A (deltaSum F)) =
      ((∑ x ∈ F, ∑ y ∈ F, twoPoint G p x y : ℝ) : ℂ) := by
    rw [inner_deltaSum]
    simp only [deltaSum, map_sum]
    simp only [lp.coeFn_sum, Finset.sum_apply, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hA x y
  have h := (Complex.re_le_norm (inner ℂ (deltaSum F) (A (deltaSum F)))).trans
    ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)))
  rw [he, Complex.ofReal_re] at h
  calc
    _ ≤ ‖deltaSum F‖ * (‖A‖ * ‖deltaSum F‖) := h
    _ = ‖A‖ * ‖deltaSum F‖ ^ 2 := by ring
    _ = _ := by rw [norm_deltaSum_sq]

end FinitePairBound

section PairCounting
attribute [local instance] Classical.propDecidable

 
theorem card_sq_le_image_card_mul_pairs {W : Type*} (S : Finset V) (c : V → W) :
    (S.card : ℝ) ^ 2 ≤ ((S.image c).card : ℝ) *
      ∑ x ∈ S, ∑ y ∈ S, if c x = c y then (1 : ℝ) else 0 := by
  let t := S.image c
  let f := fun w => ((S.filter (fun x => c x = w)).card : ℝ)
  have hsum : ∑ w ∈ t, f w = (S.card : ℝ) := by
    have h := Finset.sum_fiberwise_of_maps_to
      (fun x (hx : x ∈ S) => Finset.mem_image_of_mem c hx) (fun _ => (1 : ℝ))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, t, f] using h
  have hsq : ∑ w ∈ t, f w ^ 2 =
      ∑ x ∈ S, ∑ y ∈ S, if c x = c y then (1 : ℝ) else 0 := by
    calc
      ∑ w ∈ t, f w ^ 2 = ∑ w ∈ t, ∑ x ∈ S with c x = w, f (c x) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [show ∑ x ∈ S with c x = w, f (c x) =
            ∑ _x ∈ S with c _x = w, f w from
          Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
        simp only [Finset.sum_const, nsmul_eq_mul, f]
        ring
      _ = ∑ x ∈ S, f (c x) := Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image_of_mem c hx) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, f]
        congr 2
        ext y
        simp [eq_comm]
  have h := Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) f
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, hsq, t] using h

end PairCounting

section PairIntegral
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

 
theorem square_sum_probability_le (F : Finset V) (S : V → Set Ω)
    (C : V → V → Set Ω) (hS : ∀ x, MeasurableSet (S x))
    (hC : ∀ x y, MeasurableSet (C x y)) (n : ℝ)
    (hpoint : ∀ ω, (∑ x ∈ F, (S x).indicator (fun _ => (1 : ℝ)) ω) ^ 2 ≤
      n * ∑ x ∈ F, ∑ y ∈ F, (C x y).indicator (fun _ => (1 : ℝ)) ω) :
    (∑ x ∈ F, μ.real (S x)) ^ 2 ≤ n * ∑ x ∈ F, ∑ y ∈ F, μ.real (C x y) := by
  let X := fun ω => ∑ x ∈ F, (S x).indicator (fun _ => (1 : ℝ)) ω
  have hX : MemLp X 2 μ := memLp_finsetSum F
    (fun x _ => (memLp_const (1 : ℝ)).indicator (hS x))
  have hCi (x y) : Integrable ((C x y).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hC x y)
  have hY : Integrable (fun ω => ∑ x ∈ F, ∑ y ∈ F,
      (C x y).indicator (fun _ => (1 : ℝ)) ω) μ :=
    integrable_finsetSum F (fun x _ => integrable_finsetSum F (fun y _ => hCi x y))
  have hv := variance_nonneg X μ
  rw [variance_eq_sub hX] at hv
  have hi := integral_mono hX.integrable_sq (hY.const_mul n) hpoint
  have hx : (∫ ω, X ω ∂μ) = ∑ x ∈ F, μ.real (S x) := by
    dsimp only [X]
    rw [integral_finsetSum F (fun x _ => (integrable_const (1 : ℝ)).indicator (hS x))]
    simp only [integral_indicator_const _ (hS _), smul_eq_mul, mul_one]
  have hy : (∫ ω, n * ∑ x ∈ F, ∑ y ∈ F,
      (C x y).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      n * ∑ x ∈ F, ∑ y ∈ F, μ.real (C x y) := by
    rw [integral_const_mul, integral_finsetSum F
      (fun x _ => integrable_finsetSum F (fun y _ => hCi x y))]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum F (fun y _ => hCi x y)]
    simp only [integral_indicator_const _ (hC x _), smul_eq_mul, mul_one]
  rw [hx] at hv
  rw [hy] at hi
  exact (sub_nonneg.mp hv).trans hi

end PairIntegral

section CoupledCovers
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] [Countable E] in
theorem cluster_eq_iff_conn (G : BondGraph V E) (ω : Set E) (x y : V) :
    cluster G ω x = cluster G ω y ↔ Conn G ω x y := by
  constructor
  · intro h
    have hh := mem_cluster_self G ω y
    rwa [← h] at hh
  · exact cluster_eq_of_conn G ω


theorem measurableSet_touchedCover (G : BondGraph V E) (p q : unitInterval) (n : ℕ) :
    MeasurableSet {labels | TouchedCover G p q n labels} := by
  have he : {labels | TouchedCover G p q n labels} =
      ⋃ f : Fin n → V, ⋂ x : V, ({labels | (cluster G (openEdges labels p) x).Infinite}ᶜ ∪
        ⋃ i : Fin n, {labels | Conn G (openEdges labels q) x (f i)}) := by
    ext labels
    simp only [TouchedCover, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    simp only [← imp_iff_not_or]
  rw [he]
  apply MeasurableSet.iUnion
  intro f
  apply MeasurableSet.iInter
  intro x
  exact ((measurableSet_infinite_cluster G x).preimage (measurable_openEdges p)).compl.union
    (MeasurableSet.iUnion fun i => (measurableSet_conn G x (f i)).preimage (measurable_openEdges q))

omit [Countable V] [Countable E] in
 
theorem survivor_count_sq_le (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    (F : Finset V) (labels : E → unitInterval) (h : TouchedCover G p q n labels) :
    ((F.filter fun x => (cluster G (openEdges labels p) x).Infinite).card : ℝ) ^ 2 ≤
      n * ∑ x ∈ F, ∑ y ∈ F, if Conn G (openEdges labels q) x y then (1 : ℝ) else 0 := by
  obtain ⟨f, hf⟩ := h
  let S := F.filter fun x => (cluster G (openEdges labels p) x).Infinite
  let c := cluster G (openEdges labels q)
  have hsub : S.image c ⊆ Finset.univ.image (fun i : Fin n => c (f i)) := by
    intro C hC
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨i, hi⟩ := hf x (Finset.mem_filter.mp hx).2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (cluster_eq_of_conn G _ hi).symm⟩
  have hcard : (S.image c).card ≤ n :=
    (Finset.card_le_card hsub).trans (by simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => c (f i))))
  have hpair := card_sq_le_image_card_mul_pairs S c
  have hpairs : ∑ x ∈ S, ∑ y ∈ S, (if c x = c y then (1 : ℝ) else 0) ≤
      ∑ x ∈ F, ∑ y ∈ F, if Conn G (openEdges labels q) x y then (1 : ℝ) else 0 := by
    simp only [c, cluster_eq_iff_conn] 
    calc
      _ ≤ ∑ x ∈ S, ∑ y ∈ F, if Conn G (openEdges labels q) x y then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro x _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by split_ifs <;> positivity)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)
  exact hpair.trans ((mul_le_mul_of_nonneg_left hpairs (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)))

end CoupledCovers

section CoverInvariance
attribute [local instance] Classical.propDecidable

 
theorem labelLaw_map_precomp (b : E ≃ E) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => labels ∘ b) = labelLaw := by
  have he : (fun labels : E → unitInterval => labels ∘ b) =
      MeasurableEquiv.piCongrLeft (fun _ : E => unitInterval) b.symm := by
    funext labels e
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : E => unitInterval)
      b.symm labels (b e)
    simpa only [Equiv.symm_apply_apply, Function.comp_apply] using h.symm
  unfold labelLaw
  rw [he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : E => (volume : Measure unitInterval)) b.symm

theorem infinite_cluster_precomp (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (labels : E → unitInterval) (p : unitInterval) (x : V) :
    (cluster G (openEdges (labels ∘ b) p) x).Infinite ↔
      (cluster G (openEdges labels p) (a x)).Infinite := by
  change (cluster G (b ⁻¹' openEdges labels p) x).Infinite ↔ _
  rw [← cluster_aut G h]
  exact (Set.infinite_image_iff (fun _ _ _ _ hab => a.injective hab)).symm

variable [Countable V] [Countable E]

omit [Countable V] [Countable E] in
theorem touchedCover_precomp (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (labels : E → unitInterval) (p q : unitInterval) (n : ℕ) :
    TouchedCover G p q n (labels ∘ b) ↔ TouchedCover G p q n labels := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => a (f i), fun x hx => ?_⟩
    have hs : (cluster G (openEdges (labels ∘ b) p) (a.symm x)).Infinite :=
      (infinite_cluster_precomp G h labels p (a.symm x)).mpr (by simpa using hx)
    obtain ⟨i, hi⟩ := hf _ hs
    exact ⟨i, by simpa using (conn_aut_iff G h (openEdges labels q) (a.symm x) (f i)).mp hi⟩
  · rintro ⟨f, hf⟩
    refine ⟨fun i => a.symm (f i), fun x hx => ?_⟩
    obtain ⟨i, hi⟩ := hf (a x) ((infinite_cluster_precomp G h labels p x).mp hx)
    exact ⟨i, (conn_aut_iff G h (openEdges labels q) x (a.symm (f i))).mpr (by simpa using hi)⟩

theorem cover_survival_aut (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x : V) :
    (labelLaw : Measure (E → unitInterval)).real
      {labels | TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) (a x)).Infinite} =
    labelLaw.real {labels | TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) x).Infinite} := by
  have hm : Measurable (fun labels : E → unitInterval => labels ∘ b) :=
    Measurable.of_eval (fun e => measurable_pi_apply (b e))
  have hs : MeasurableSet {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) x).Infinite} :=
    (measurableSet_touchedCover G p q n).inter
      ((measurableSet_infinite_cluster G x).preimage (measurable_openEdges p))
  have he : {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) (a x)).Infinite} =
      (fun labels : E → unitInterval => labels ∘ b) ⁻¹'
        {labels | TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) x).Infinite} := by
    ext labels
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, touchedCover_precomp G h,
      infinite_cluster_precomp G h]
  simp only [Measure.real]
  rw [he, ← Measure.map_apply hm hs, labelLaw_map_precomp]

end CoverInvariance

section CoverObstruction
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

theorem cover_survival_square_sum_le (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G q A) (F : Finset V) :
    (∑ x ∈ F, (labelLaw : Measure (E → unitInterval)).real {labels |
      TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) x).Infinite}) ^ 2 ≤
      n * ‖A‖ * F.card := by
  let S := fun x => {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) x).Infinite}
  let C := fun x y => {labels | Conn G (openEdges labels q) x y}
  have hS (x) : MeasurableSet (S x) :=
    (measurableSet_touchedCover G p q n).inter
      ((measurableSet_infinite_cluster G x).preimage (measurable_openEdges p))
  have hC (x y) : MeasurableSet (C x y) :=
    (measurableSet_conn G x y).preimage (measurable_openEdges q)
  have hpoint (labels : E → unitInterval) :
      (∑ x ∈ F, (S x).indicator (fun _ => (1 : ℝ)) labels) ^ 2 ≤
      (n : ℝ) * ∑ x ∈ F, ∑ y ∈ F, (C x y).indicator (fun _ => (1 : ℝ)) labels := by
    by_cases hc : TouchedCover G p q n labels
    · have he : ∑ x ∈ F, (S x).indicator (fun _ => (1 : ℝ)) labels =
          ((F.filter fun x => (cluster G (openEdges labels p) x).Infinite).card : ℝ) := by
        simp only [S, Set.indicator, Set.mem_ofPred_eq, hc, true_and]
        rw [← Finset.sum_filter]
        simp
      rw [he]
      simpa only [C, Set.indicator, Set.mem_ofPred_eq] using
        survivor_count_sq_le G p q n F labels hc
    · simp only [S, Set.indicator, Set.mem_ofPred_eq, hc, false_and, if_false,
        Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have h := square_sum_probability_le (labelLaw : Measure (E → unitInterval)) F S C hS hC
    (n : ℝ) hpoint
  have he (x y) : labelLaw.real (C x y) = twoPoint G q x y :=
    (twoPoint_eq_labelLaw G q x y).symm
  simp only [he] at h
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (sum_twoPoint_le_norm_card G q hA F) (Nat.cast_nonneg n))

 

theorem measure_cover_survival_eq_zero [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p q : unitInterval) (hq : OperatorBounded G q) (n : ℕ) (x : V) :
    (labelLaw : Measure (E → unitInterval)) {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) x).Infinite} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  by_contra hnz
  let θ := (labelLaw : Measure (E → unitInterval)).real {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) x).Infinite}
  have hθ : 0 < θ := lt_of_le_of_ne measureReal_nonneg (Ne.symm hnz)
  obtain ⟨A, hA⟩ := hq
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ) * ‖A‖ / θ ^ 2 + 1)
  obtain ⟨F, hF, hcard⟩ := (vertexOrbit_infinite G hconn hloc hqt x).exists_subset_card_eq m
  have he (y : V) (hy : y ∈ F) : (labelLaw : Measure (E → unitInterval)).real
      {labels | TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) y).Infinite} = θ := by
    obtain ⟨a, b, hab, hay⟩ := hF hy
    rw [← hay]
    exact cover_survival_aut G p q n hab x
  have hh := cover_survival_square_sum_le G p q n hA F
  rw [Finset.sum_congr rfl he] at hh
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hh
  have hθsq : 0 < θ ^ 2 := sq_pos_of_pos hθ
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity : (0 : ℝ) < (n : ℝ) * ‖A‖ / θ ^ 2 + 1) hm
  have hlt : (n : ℝ) * ‖A‖ < (m : ℝ) * θ ^ 2 := by
    apply (div_lt_iff₀ hθsq).mp
    linarith
  nlinarith

end CoverObstruction

section FiniteChanges
attribute [local instance] Classical.propDecidable

 
theorem cluster_union_subset (G : BondGraph V E) (ω : Set E) (F : Set E) (x : V) :
    cluster G (ω ∪ F) x ⊆ cluster G ω x ∪ ⋃ e ∈ F, ⋃ z ∈ {z | z ∈ G e}, cluster G ω z := by
  intro y hy
  induction hy with
  | refl => exact Or.inl (mem_cluster_self G ω x)
  | @tail y z hy hed ih =>
    obtain ⟨e, he, heq⟩ := hed
    rcases he with he | he
    · have hyz : Conn G ω y z := (conn_refl G ω y).tail ⟨e, he, heq⟩
      rcases ih with ih | ih
      · exact Or.inl (conn_trans G ω ih hyz)
      · right
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at ih ⊢
        obtain ⟨e', he', w, hw, hwy⟩ := ih
        exact ⟨e', he', w, hw, conn_trans G ω hwy hyz⟩
    · right
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨e, he, z, heq ▸ by simp, conn_refl G ω z⟩

theorem exists_infinite_cluster_mono (G : BondGraph V E) {ω ω' : Set E} (h : ω ⊆ ω') :
    (∃ x, (cluster G ω x).Infinite) → ∃ x, (cluster G ω' x).Infinite := by
  rintro ⟨x, hx⟩
  exact ⟨x, hx.mono (fun _ hy => conn_mono G h hy)⟩

 
theorem exists_infinite_cluster_sdiff (G : BondGraph V E) (ω : Set E)
    {F : Set E} (hF : F.Finite) :
    (∃ x, (cluster G (ω \ F) x).Infinite) ↔ ∃ x, (cluster G ω x).Infinite := by
  constructor
  · exact exists_infinite_cluster_mono G Set.sdiff_subset
  · contrapose!
    intro h x
    have hs : (cluster G (ω \ F) x ∪
        ⋃ e ∈ F, ⋃ z ∈ {z | z ∈ G e}, cluster G (ω \ F) z).Finite := by
      apply (h x).union
      apply hF.biUnion
      intro e _
      have he : {z | z ∈ G e}.Finite := by
        exact (G e).toFinset.finite_toSet.subset (fun z hz => by simpa using hz)
      exact he.biUnion (fun z _ => h z)
    apply hs.subset
    apply Set.Subset.trans (fun y hy => conn_mono G (Set.subset_sdiff_union _ _) hy)
    exact cluster_union_subset G (ω \ F) F x

end FiniteChanges

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

 theorem measurableSet_exists_infinite_cluster (G : BondGraph V E) :
    MeasurableSet {ω : Set E | ∃ x, (cluster G ω x).Infinite} := by
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion (fun x => measurableSet_infinite_cluster G x)

 theorem infinite_cluster_zero_one (G : BondGraph V E) (p : unitInterval) :
    (labelLaw : Measure (E → unitInterval))
      {labels | ∃ x, (cluster G (openEdges labels p) x).Infinite} = 0 ∨
    (labelLaw : Measure (E → unitInterval))
      {labels | ∃ x, (cluster G (openEdges labels p) x).Infinite} = 1 := by
  let σ : E → MeasurableSpace (E → unitInterval) := fun e =>
    MeasurableSpace.comap (fun labels : E → unitInterval => labels e) inferInstance
  have hle (e) : σ e ≤ (inferInstance : MeasurableSpace (E → unitInterval)) := (measurable_pi_apply e).comap_le
  have hi : iIndep σ (labelLaw : Measure (E → unitInterval)) :=
    iIndepFun_infinitePi (X := fun (_ : E) (x : unitInterval) => x) (fun _ => measurable_id)
  have htail : MeasurableSet[Filter.limsup σ Filter.cofinite]
      {labels | ∃ x, (cluster G (openEdges labels p) x).Infinite} := by
    rw [Filter.limsup_eq_iInf_iSup]
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro s
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro hs
    have hfin : sᶜ.Finite := Filter.mem_cofinite.mp hs
    let m := ⨆ e ∈ s, σ e
    have hm : @Measurable (E → unitInterval) (Set E) m inferInstance
        (fun labels => openEdges labels p ∩ s) := by
      apply measurable_setOfPred.comp
      apply Measurable.of_eval
      intro e
      change @Measurable (E → unitInterval) Prop m inferInstance (fun labels => labels e ≤ p ∧ e ∈ s)
      by_cases he : e ∈ s
      · have hev : @Measurable (E → unitInterval) unitInterval m inferInstance
            (fun labels => labels e) :=
          Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
        simpa only [he, and_true, Function.comp_def]
          using (measurable_threshold p).comp hev
      · simpa only [he, and_false]
          using (measurable_const : @Measurable (E → unitInterval) Prop m inferInstance
            (fun _ => False))
    have heq : {labels : E → unitInterval | ∃ x, (cluster G (openEdges labels p) x).Infinite} =
        {labels | ∃ x, (cluster G (openEdges labels p ∩ s) x).Infinite} := by
      ext labels
      simpa only [Set.sdiff_compl, Set.mem_ofPred_eq] using
        (exists_infinite_cluster_sdiff G (openEdges labels p) hfin).symm
    rw [heq]
    exact (measurableSet_exists_infinite_cluster G).preimage hm
  exact measure_zero_or_one_of_measurableSet_limsup
    (s := σ) (f := Filter.cofinite) (p := Set.Finite)
    (ns := fun F : Finset E => (F : Set E)) hle hi
    (fun t ht => by simpa using ht)
    (fun F H => ⟨F ∪ H, Finset.coe_subset.mpr Finset.subset_union_left,
      Finset.coe_subset.mpr Finset.subset_union_right⟩)
    (fun F => F.finite_toSet) (fun e => ⟨{e}, by simp⟩) htail

end PercolationZeroOne

section CoupledInterval
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

 theorem exists_infinite_cluster_probability_mono (G : BondGraph V E) {p q : unitInterval}
    (hpq : p ≤ q) :
    law p {ω | (infiniteClusters G ω).Nonempty} ≤
      law q {ω | (infiniteClusters G ω).Nonempty} := by
  have hm : MeasurableSet {ω : Set E | (infiniteClusters G ω).Nonempty} := by
    simpa only [infiniteClusters_nonempty_iff] using measurableSet_exists_infinite_cluster G
  rw [← map_openEdges p, ← map_openEdges q,
    Measure.map_apply (measurable_openEdges p) hm,
    Measure.map_apply (measurable_openEdges q) hm]
  apply measure_mono
  intro labels h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, infiniteClusters_nonempty_iff] at h ⊢
  exact exists_infinite_cluster_mono G (openEdges_mono labels hpq) h

 theorem ae_exists_infinite_cluster_of_pc_lt (G : BondGraph V E) (p : unitInterval)
    (hp : pc G < p) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      ∃ x, (cluster G (openEdges labels p) x).Infinite := by
  obtain ⟨q, hq, hqp⟩ := sInf_lt_iff.mp hp
  have hpos : 0 < law p {ω | (infiniteClusters G ω).Nonempty} :=
    lt_of_lt_of_le hq (exists_infinite_cluster_probability_mono G hqp.le)
  have hm : MeasurableSet {ω : Set E | (infiniteClusters G ω).Nonempty} := by
    simpa only [infiniteClusters_nonempty_iff] using measurableSet_exists_infinite_cluster G
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p) hm] at hpos
  simp only [Set.preimage_ofPred_eq, infiniteClusters_nonempty_iff] at hpos
  have hpone := (infinite_cluster_zero_one G p).resolve_left (ne_of_gt hpos)
  exact (mem_ae_iff_prob_eq_one
    ((measurableSet_exists_infinite_cluster G).preimage (measurable_openEdges p))).mpr hpone

omit [Countable V] [Countable E] in
 theorem touchedCover_of_finite_infiniteClusters (G : BondGraph V E)
    (labels : E → unitInterval) {p r q : unitInterval} (hpr : p ≤ r) (hrq : r ≤ q)
    (hfinite : (infiniteClusters G (openEdges labels r)).Finite) :
    ∃ n, TouchedCover G p q n labels := by
  let C := infiniteClusters G (openEdges labels r)
  let : Fintype C := hfinite.fintype
  let f : C → V := fun c => Classical.choose c.property.2
  have hf (c : C) : c.val = cluster G (openEdges labels r) (f c) :=
    Classical.choose_spec c.property.2
  refine ⟨Fintype.card C, fun i => f ((Fintype.equivFin C).symm i), ?_⟩
  intro x hx
  have hx' : (cluster G (openEdges labels r) x).Infinite :=
    hx.mono (fun _ hy => conn_mono G (openEdges_mono labels hpr) hy)
  let c : C := ⟨cluster G (openEdges labels r) x, hx', x, rfl⟩
  refine ⟨Fintype.equivFin C c, ?_⟩
  simp only [Equiv.symm_apply_apply]
  apply conn_mono G (openEdges_mono labels hrq)
  change f c ∈ cluster G (openEdges labels r) x
  change f c ∈ c.val
  rw [hf c]
  exact mem_cluster_self G _ _

 

 theorem coupled_interval [Infinite V] (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p q : unitInterval) (hp : pc G < p) (hq : OperatorBounded G q) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      ∀ r ∈ Set.Icc p q, (infiniteClusters G (openEdges labels r)).Infinite := by
  have hall : ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), ∀ n x,
      ¬(TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) x).Infinite) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro x
    apply ae_iff.mpr
    simpa only [not_not] using measure_cover_survival_eq_zero G hconn hloc hqt p q hq n x
  filter_upwards [hall, ae_exists_infinite_cluster_of_pc_lt G p hp] with labels hlabels hex
  intro r hr
  by_contra hfinite
  obtain ⟨n, hn⟩ := touchedCover_of_finite_infiniteClusters G labels hr.1 hr.2
    (Set.not_infinite.mp hfinite)
  obtain ⟨x, hx⟩ := hex
  exact hlabels n x ⟨hn, hx⟩

end CoupledInterval

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

section MainBridge
attribute [local instance] Classical.propDecidable

 

theorem mainConclusion_of_strict_gap [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hgap : pc G < ptwo G) : MainConclusion G := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  obtain ⟨q, hq, hpq⟩ := lt_sSup_iff.mp hgap
  obtain ⟨p₂, hp₂, hp₂q⟩ := exists_between hpq
  obtain ⟨p₁, hp₁, hp₁₂⟩ := exists_between hp₂
  have hc : OperatorBounded G (pc G) := operatorBounded_of_le G hpq.le hq
  refine ⟨(operatorNorm_eq_sup_below G (pc G) (pc_pos G hloc hqt)).symm,
    (operatorNorm_lt_top_iff G (pc G)).mpr hc, hgap, ptwo_le_pu G hconn hqt, ?_⟩
  refine ⟨p₁, p₂, hp₁, hp₁₂, hp₂q.trans_le (show q ≤ 1 from q.2.2), ?_⟩
  exact coupled_interval G hconn hloc hqt p₁ p₂ hp₁
    (operatorBounded_of_le G hp₂q.le hq)

end MainBridge

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

section Openness
attribute [local instance] Classical.propDecidable

 theorem operatorBounded_open_right [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp0 : 0 < p) (hp1 : p < 1) (hb : OperatorBounded G p) :
    ∃ r : unitInterval, p < r ∧ OperatorBounded G r := by
  obtain ⟨A,hA⟩ := hb
  let c : ℝ := (2*D)*‖A‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨m,q,hq,hqp⟩ := exists_orParameter_small p hp1 (1/(c+1))
    (by positivity) (by apply (div_le_one (by positivity)).mpr; linarith)
  have hq0 : (0:ℝ) < q := by
    by_contra h
    have hqe : q = 0 := Subtype.ext ((le_of_not_gt h).antisymm q.2.1)
    have hpe : p = 0 := by rw [← hqp,hqe]; apply Subtype.ext; simp [orParameter]
    exact (ne_of_gt hp0) hpe
  have hsmall : (q:ℝ)*(2*D)*‖A‖ < 1 := by
    have hm := mul_le_mul_of_nonneg_right hq hc
    have hh : c/(c+1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    calc
      (q:ℝ)*(2*D)*‖A‖ = (q:ℝ)*c := by dsimp [c]; ring
      _ ≤ 1/(c+1)*c := hm
      _ = c/(c+1) := by ring
      _ < 1 := hh
  obtain ⟨B,hB,_⟩ := sprinkling_bound G hloc q m D hD A (hqp ▸ hA) hsmall
  refine ⟨orParameter q (m+1),?_,B,hB⟩
  change (p:ℝ) < (orParameter q (m+1):ℝ)
  have he : (orParameter q (m+1):ℝ) = (p:ℝ)+(1-p)*q := by
    rw [← hqp]
    simp only [orParameter,pow_succ]
    ring
  rw [he]
  have ht := mul_pos (show (0:ℝ) < 1-p from sub_pos.mpr hp1) hq0
  linarith

 

 theorem mainConclusion_of_critical_bounded [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hc : OperatorBounded G (pc G)) : MainConclusion G := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  have hpc1 : pc G < 1 := by
    apply lt_of_le_of_ne (show pc G ≤ 1 from (pc G).2.2)
    intro he
    exact not_operatorBounded_one G hconn (he ▸ hc)
  obtain ⟨D,_,hD⟩ := exists_degree_bound G hqt
  obtain ⟨q,hq,hb⟩ := operatorBounded_open_right G hloc D hD (pc G)
    (pc_pos G hloc hqt) hpc1 hc
  exact mainConclusion_of_strict_gap G hconn hloc hqt
    (hq.trans_le (le_sSup hb))

end Openness

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

end IsoperimetricEnergy

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

end SubcriticalMoments
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

end PivotalSprinklingGain
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

end EdgeQueryTree
end QueryTranscriptLaw
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

end IncidenceCompletion
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
open MeasureTheory Filter
section ContactMeasurability
attribute [local instance] Classical.propDecidable Classical.decEq

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


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Corridors
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

end CorridorIndependence
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_TwoCluster_Score
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decision-tree scores and influences for two-cluster events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
namespace ProbeTree

 
theorem score_mean_zero (p h : ℝ) (t : ProbeTree) :
    ∑ l, weight p h t l * score p t l = 0 := by
  induction t with
  | done b => simp [weight,score]
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 0
    simp only [Fintype.sum_sum_type,weight,score]
    have h₀ (l : t₀.Leaf) : (1-p)*weight p h t₀ l*(score p t₀ l-p) =
        (1-p)*(weight p h t₀ l*score p t₀ l)-p*(1-p)*weight p h t₀ l := by ring
    have h₁ (l : t₁.Leaf) : p*weight p h t₁ l*(score p t₁ l+(1-p)) =
        p*(weight p h t₁ l*score p t₁ l)+p*(1-p)*weight p h t₁ l := by ring
    simp_rw [h₀,h₁]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
      sum_weight,ih₀,ih₁]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 0
    simp only [Fintype.sum_sum_type,weight,score,mul_assoc,←Finset.mul_sum,ih₀,ih₁,mul_zero,add_zero]

 

theorem score_second_moment (p h : ℝ) (t : ProbeTree) :
    ∑ l, weight p h t l * score p t l ^ 2 =
      p*(1-p) * ∑ l, weight p h t l * (queries t l : ℝ) := by
  induction t with
  | done b => simp [weight,score,queries]
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = p*(1-p)*(∑ l : t₀.Leaf ⊕ t₁.Leaf, _)
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    have h₀ : ∀ l : t₀.Leaf, weight p h (.edge t₀ t₁) (.inl l) * score p (.edge t₀ t₁) (.inl l)^2 =
        (1-p)*(weight p h t₀ l*score p t₀ l^2) -
        (2*p*(1-p))*(weight p h t₀ l*score p t₀ l) + p^2*(1-p)*weight p h t₀ l := by
      intro l; simp only [weight,score]; ring
    have h₁ : ∀ l : t₁.Leaf, weight p h (.edge t₀ t₁) (.inr l) * score p (.edge t₀ t₁) (.inr l)^2 =
        p*(weight p h t₁ l*score p t₁ l^2) +
        (2*p*(1-p))*(weight p h t₁ l*score p t₁ l) + p*(1-p)^2*weight p h t₁ l := by
      intro l; simp only [weight,score]; ring
    simp_rw [h₀,h₁]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
      score_mean_zero,sum_weight,mul_zero,mul_one,sub_zero,add_zero,ih₀,ih₁,
      weight,queries,Nat.cast_add,Nat.cast_one]
    simp only [mul_add,mul_one,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum,sum_weight]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = p*(1-p)*(∑ l : t₀.Leaf ⊕ t₁.Leaf, _)
    simp only [Fintype.sum_sum_type,weight,score,queries,mul_assoc,←Finset.mul_sum,ih₀,ih₁]
    ring

 
theorem score_abs_mean_le_sqrt (p h : unitInterval) (t : ProbeTree)
    (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∑ l, weight p h t l*(queries t l:ℝ) ≤ N) :
    ∑ l, weight p h t l * |score p t l| ≤ Real.sqrt N := by
  have hw := weight_nonneg p h t
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun l => Real.sqrt (weight p h t l))
    (fun l => Real.sqrt (weight p h t l)*|score p t l|)
  have he : (∑ l, weight p h t l * |score p t l|)^2 ≤
      ∑ l, weight p h t l * score p t l ^2 := by
    simpa only [mul_pow,Real.sq_sqrt (hw _),sq_abs,
      ←mul_assoc,Real.mul_self_sqrt (hw _),sum_weight,one_mul] using hc
  have hp : 0 ≤ (p:ℝ)*(1-p) := mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)
  have hp1 : (p:ℝ)*(1-p) ≤ 1 := by nlinarith [p.2.1,p.2.2]
  rw [score_second_moment] at he
  have hnon : 0 ≤ ∑ l, weight p h t l*|score p t l| :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hw l) (abs_nonneg _)
  apply (Real.le_sqrt hnon hN0).mpr
  exact he.trans ((mul_le_mul_of_nonneg_left hN hp).trans (by nlinarith [hN0]))

end ProbeTree
namespace EdgeQueryTree
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem capped_score_abs_mean_le (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (N : ℕ) (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => |t.score p ω|) p ≤ Real.sqrt (N:ℝ) := by
  have hq : ∑ l, ProbeTree.weight p 0 t.forget l*(ProbeTree.queries t.forget l:ℝ) ≤ N := by
    rw [←t.leaf_expectation ht p (fun l => (ProbeTree.queries t.forget l:ℝ))]
    calc
      _ ≤ bernoulliPolynomial Q (fun _ => (N:ℝ)) p := by
        apply bernoulliPolynomial_mono _ _ _ p p.2
        intro ω hω
        exact_mod_cast hN ω hω
      _ = N := bernoulliPolynomial_const Q (N:ℝ) p
  change bernoulliPolynomial Q (fun ω => |ProbeTree.score p t.forget (t.leaf ω)|) p ≤ _
  rw [t.leaf_expectation ht p (fun l => |ProbeTree.score p t.forget l|)]
  exact ProbeTree.score_abs_mean_le_sqrt p 0 t.forget N (Nat.cast_nonneg N) hq

end EdgeQueryTree

theorem incidenceSearch_abs_mean_le (G : BondGraph V E) (N : ℕ) (Q : Finset E)
    (R : Finset V) (p : unitInterval) :
    bernoulliPolynomial Q (fun ω => |(incidenceSearch G N Q R).score p ω|) p ≤
      Real.sqrt (N:ℝ) := by
  classical
  exact EdgeQueryTree.capped_score_abs_mean_le _ (incidenceSearch_valid ..) p N
    (fun ω _ => incidenceSearch_cap G N Q R ω)

end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cappedDensity_nonneg (n s : ℕ) : 0 ≤ cappedDensity n s := by
  unfold cappedDensity
  positivity

theorem cappedDensity_le_one (n s : ℕ) : cappedDensity n s ≤ 1 := by
  unfold cappedDensity
  by_cases hs : s = 0
  · simp [hs]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs))).mpr (min_le_right ..)

private theorem exists_four_scale (n s K : ℕ) (hs : n < s) (hK : s ≤ n*4^K) :
    ∃ j < K, n*4^j < s ∧ s ≤ n*4^(j+1) := by
  induction K with
  | zero => simp only [pow_zero,mul_one] at hK; omega
  | succ K ih =>
    by_cases h : s ≤ n*4^K
    · obtain ⟨j,hj,hj₁,hj₂⟩ := ih h
      exact ⟨j,by omega,hj₁,hj₂⟩
    · exact ⟨K,by omega,by omega,hK⟩

private theorem nat_le_four_pow (k : ℕ) : k ≤ 4^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; have := Nat.one_le_pow k 4 (by omega); omega

private theorem cappedDensity_le_four_scale (n s j : ℕ) (hn : 0 < n)
    (hs : n*4^j < s) : cappedDensity n s ≤ (1/4:ℝ)^j := by
  have hpow : 1 ≤ 4^j := Nat.one_le_pow j 4 (by omega)
  have hns : n ≤ s := le_trans (by nlinarith : n ≤ n*4^j) hs.le
  have hs0 : 0 < (s:ℝ) := by exact_mod_cast (lt_of_lt_of_le hn hns)
  have hden : 0 < (n:ℝ)*4^j := mul_pos (Nat.cast_pos.mpr hn) (pow_pos (by norm_num) _)
  unfold cappedDensity
  rw [min_eq_left (by exact_mod_cast hns)]
  calc
    (n:ℝ)/s ≤ n/(n*4^j) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden (by exact_mod_cast hs.le)
    _ = (1/4:ℝ)^j := by rw [div_pow,one_pow]; field_simp

 

theorem cappedDensity_score_le_stopped (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : ℝ) (d n K : ℕ) (hn : 0 < n)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d)
    (ω : Finset E) (hω : ω ⊆ Q)
    (hK : (finiteRootComponent G ω x).card ≤ n*4^K) :
    cappedDensity n (finiteRootComponent G ω x).card * |finiteClusterScore G Q x p ω| ≤
      |(incidenceSearch G (d*n) Q {x}).score p ω| +
        ∑ j ∈ Finset.range K, (1/4:ℝ)^j *
          |(incidenceSearch G (d*(n*4^(j+1))) Q {x}).score p ω| := by
  let s := (finiteRootComponent G ω x).card
  have hcomplete (N : ℕ) (hN : s ≤ N) :
      (incidenceSearch G (d*N) Q {x}).score p ω = finiteClusterScore G Q x p ω := by
    exact incidenceSearch_completed_score G (d*N) Q ω hω x p
      ((incidentBonds_card_le G Q _ d hdeg).trans (Nat.mul_le_mul_left d hN))
  have hterms : ∀ j, 0 ≤ (1/4:ℝ)^j *
      |(incidenceSearch G (d*(n*4^(j+1))) Q {x}).score p ω| := fun j => by positivity
  by_cases hs : s ≤ n
  · have he := hcomplete n hs
    rw [he]
    exact (mul_le_of_le_one_left (abs_nonneg _) (cappedDensity_le_one n s)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hterms j))
  · obtain ⟨j,hj,hlo,hhi⟩ := exists_four_scale n s K (by omega) hK
    have he := hcomplete (n*4^(j+1)) hhi
    calc
      _ ≤ (1/4:ℝ)^j * |finiteClusterScore G Q x p ω| :=
        mul_le_mul_of_nonneg_right (cappedDensity_le_four_scale n s j hn hlo) (abs_nonneg _)
      _ = (1/4:ℝ)^j * |(incidenceSearch G (d*(n*4^(j+1))) Q {x}).score p ω| := by rw [he]
      _ ≤ ∑ j ∈ Finset.range K, (1/4:ℝ)^j *
          |(incidenceSearch G (d*(n*4^(j+1))) Q {x}).score p ω| :=
        Finset.single_le_sum (fun j _ => hterms j) (Finset.mem_range.mpr hj)
      _ ≤ _ := le_add_of_nonneg_left (abs_nonneg _)

private theorem sqrt_four_cap (d n j : ℕ) :
    Real.sqrt (d*(n*4^(j+1)):ℕ) = (2:ℝ)^(j+1)*Real.sqrt (d*n:ℕ) := by
  have he : (d*(n*4^(j+1)):ℕ) = (d*n)*4^(j+1) := by ring
  rw [he,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg _)]
  rw [Nat.cast_pow,Nat.cast_ofNat,show (4:ℝ) = 2^2 by norm_num,←pow_mul,pow_mul',Real.sqrt_sq_eq_abs,
    abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
  ring

theorem cappedDensity_score_expectation_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (d n : ℕ) (hn : 0 < n)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    bernoulliPolynomial Q (fun ω => cappedDensity n (finiteRootComponent G ω x).card *
      |finiteClusterScore G Q x p ω|) p ≤ 5*Real.sqrt (d*n:ℕ) := by
  let K := (insert x (searchVertices G Q)).card
  have hK (ω : Finset E) (hω : ω ⊆ Q) : (finiteRootComponent G ω x).card ≤ n*4^K := by
    have hs : (finiteRootComponent G ω x).card ≤ K :=
      Finset.card_le_card (finiteRootComponent_subset G Q _ x ω hω le_rfl)
    exact hs.trans ((nat_le_four_pow K).trans (by nlinarith [Nat.one_le_pow K 4 (by omega)]))
  have hp := bernoulliPolynomial_mono Q _ _ p p.2 (fun ω hω =>
    cappedDensity_score_le_stopped G Q x p d n K hn hdeg ω hω (hK ω hω))
  rw [bernoulliPolynomial_add,bernoulliPolynomial_sum] at hp
  simp_rw [bernoulliPolynomial_const_mul] at hp
  have hh := hp.trans (add_le_add (incidenceSearch_abs_mean_le G (d*n) Q {x} p)
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (incidenceSearch_abs_mean_le G (d*(n*4^(j+1))) Q {x} p) (by positivity)))
  simp_rw [sqrt_four_cap] at hh
  have he (j : ℕ) : (1/4:ℝ)^j*((2:ℝ)^(j+1)*Real.sqrt (d*n:ℕ)) =
      2*(1/2:ℝ)^j*Real.sqrt (d*n:ℕ) := by
    rw [pow_succ]
    calc
      _ = 2*((1/4:ℝ)^j*2^j)*Real.sqrt (d*n:ℕ) := by ring
      _ = _ := by rw [←mul_pow]; norm_num
  simp_rw [he] at hh
  rw [←Finset.sum_mul,←Finset.mul_sum] at hh
  have hg : ∑ j ∈ Finset.range K, (1/2:ℝ)^j ≤ 2 := by
    have hid : ∑ j ∈ Finset.range K, (1/2:ℝ)^j = 2-2*(1/2:ℝ)^K := by
      induction K with
      | zero => simp
      | succ K ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
    rw [hid]
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) K]
  exact hh.trans (by nlinarith [Real.sqrt_nonneg (d*n:ℕ)])

end Percolation

 

 

open MeasureTheory ProbabilityTheory
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incident_cluster_insert_iff (G : BondGraph V E) (ω : Set E) (x : V) (e : E) :
    (∃ a, Conn G (insert e ω) x a ∧ a ∈ G e) ↔
      ∃ a, Conn G ω x a ∧ a ∈ G e := by
  obtain ⟨a,b,hab⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  constructor
  · rintro ⟨z,hz,hze⟩
    rcases (conn_insert_iff G ω e a b x z hab).mp hz with hz | ⟨hxa,_⟩ | ⟨hxb,_⟩
    · exact ⟨z,hz,hze⟩
    · exact ⟨a,hxa,hab ▸ by simp⟩
    · exact ⟨b,hxb,hab ▸ by simp⟩
  · rintro ⟨z,hz,hze⟩
    exact ⟨z,conn_mono G (Set.subset_insert e ω) hz,hze⟩

theorem cluster_insert_eq_of_not_incident (G : BondGraph V E) (ω : Set E) (x : V) (e : E)
    (hn : ¬∃ a, Conn G ω x a ∧ a ∈ G e) :
    cluster G (insert e ω) x = cluster G ω x := by
  obtain ⟨a,b,hab⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  ext z
  constructor
  · intro hz
    rcases (conn_insert_iff G ω e a b x z hab).mp hz with hz | ⟨hxa,_⟩ | ⟨hxb,_⟩
    · exact hz
    · exact (hn ⟨a,hxa,hab ▸ by simp⟩).elim
    · exact (hn ⟨b,hxb,hab ▸ by simp⟩).elim
  · exact conn_mono G (Set.subset_insert e ω)

theorem finite_incident_insert_iff (G : BondGraph V E) (Q ω : Finset E) (x : V) (e : E) :
    e ∈ incidentBonds G Q (finiteRootComponent G (insert e ω) x) ↔
      e ∈ incidentBonds G Q (finiteRootComponent G ω x) := by
  simp only [mem_incidentBonds]
  have hc (η : Finset E) (a : V) : a ∈ finiteRootComponent G η x ↔ Conn G (η:Set E) x a := by
    change a ∈ (finiteRootComponent G η x:Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  simp only [hc,Finset.coe_insert,incident_cluster_insert_iff]

theorem finiteRootComponent_insert_eq_of_not_incident (G : BondGraph V E)
    (Q ω : Finset E) (x : V) (e : E) (he : e ∈ Q)
    (hn : e ∉ incidentBonds G Q (finiteRootComponent G ω x)) :
    finiteRootComponent G (insert e ω) x = finiteRootComponent G ω x := by
  apply Finset.coe_injective
  rw [coe_finiteRootComponent,coe_finiteRootComponent,Finset.coe_insert]
  apply cluster_insert_eq_of_not_incident
  rintro ⟨a,ha,hae⟩
  apply hn
  apply (mem_incidentBonds G Q _ e).mpr
  refine ⟨he,a,?_,hae⟩
  change a ∈ (finiteRootComponent G ω x:Set V)
  rw [coe_finiteRootComponent]
  exact ha

theorem finiteRootComponent_card_pos (G : BondGraph V E) (ω : Finset E) (x : V) :
    0 < (finiteRootComponent G ω x).card := by
  apply Finset.card_pos.mpr
  refine ⟨x,?_⟩
  change x ∈ (finiteRootComponent G ω x:Set V)
  rw [coe_finiteRootComponent]
  exact mem_cluster_self G _ x

theorem cappedDensity_antitone (n : ℕ) {s t : ℕ} (hs : 0 < s) (hst : s ≤ t) :
    cappedDensity n t ≤ cappedDensity n s := by
  by_cases hn : s ≤ n
  · have he : cappedDensity n s = 1 := by
      unfold cappedDensity
      rw [min_eq_right (by exact_mod_cast hn),div_self (by exact_mod_cast Nat.ne_of_gt hs)]
    rw [he]
    exact cappedDensity_le_one n t
  · have hs' : (n:ℝ) ≤ s := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hn))
    have ht' : (n:ℝ) ≤ t := hs'.trans (by exact_mod_cast hst)
    unfold cappedDensity
    rw [min_eq_left ht',min_eq_left hs']
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (Nat.cast_pos.mpr hs) (by exact_mod_cast hst)

theorem finiteDensityInfluence_nonneg (G : BondGraph V E) (n : ℕ) (x : V)
    (e : E) (ω : Finset E) : 0 ≤ finiteDensityInfluence G n x e ω := by
  unfold finiteDensityInfluence
  split_ifs
  · rfl
  · apply sub_nonneg.mpr
    apply cappedDensity_antitone n (finiteRootComponent_card_pos G ω x)
    apply Finset.card_le_card
    intro y hy
    have hm (η : Finset E) : y ∈ finiteRootComponent G η x ↔ Conn G (η:Set E) x y := by
      change y ∈ (finiteRootComponent G η x:Set V) ↔ _
      rw [coe_finiteRootComponent]
      rfl
    rw [hm] at hy ⊢
    exact conn_mono G (by simp) hy

theorem finiteDensityInfluence_le_one (G : BondGraph V E) (n : ℕ) (x : V)
    (e : E) (ω : Finset E) : finiteDensityInfluence G n x e ω ≤ 1 := by
  unfold finiteDensityInfluence finiteDensity
  split_ifs
  · norm_num
  · exact (sub_le_self _ (cappedDensity_nonneg ..)).trans (cappedDensity_le_one ..)

 
theorem finiteDensity_score_one_bit (G : BondGraph V E) (Q : Finset E) (n : ℕ)
    (x : V) (p : ℝ) (e : E) (he : e ∈ Q) :
    bernoulliPolynomial Q (fun ω => if e ∈ incidentBonds G Q (finiteRootComponent G ω x)
      then ((if e ∈ ω then 1 else 0)-p)*finiteDensity G n x ω else 0) p =
      -p*bernoulliPolynomial Q (finiteDensityInfluence G n x e) p := by
  let f := finiteDensity G n x
  let I := fun ω : Finset E => e ∈ incidentBonds G Q (finiteRootComponent G ω x)
  let R := Q.erase e
  have heR : e ∉ R := Finset.notMem_erase e Q
  have hQ : insert e R = Q := Finset.insert_erase he
  rw [←hQ,bernoulliPolynomial_insert R e heR,bernoulliPolynomial_insert R e heR]
  rw [hQ]
  have hclosed (ω : Finset E) (hω : ω ⊆ R) : e ∉ ω := fun h => heR (hω h)
  have hc : bernoulliPolynomial R (fun ω => if I ω then ((if e ∈ ω then 1 else 0)-p)*f ω else 0) p =
      -p*bernoulliPolynomial R (fun ω => if I ω then f ω else 0) p := by
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [ite_eq_right (hclosed ω hω),zero_sub]
    split_ifs <;> ring
  have ho : bernoulliPolynomial R (fun ω => if I (insert e ω) then
      ((if e ∈ insert e ω then 1 else 0)-p)*f (insert e ω) else 0) p =
      (1-p)*bernoulliPolynomial R (fun ω => if I ω then f (insert e ω) else 0) p := by
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro ω _
    simp only [I,finite_incident_insert_iff,Finset.mem_insert_self,if_true]
    split_ifs <;> ring
  have hi : bernoulliPolynomial R (finiteDensityInfluence G n x e) p =
      bernoulliPolynomial R (fun ω => if I ω then f ω else 0) p -
        bernoulliPolynomial R (fun ω => if I ω then f (insert e ω) else 0) p := by
    rw [←bernoulliPolynomial_sub]
    apply bernoulliPolynomial_congr
    intro ω hω
    unfold finiteDensityInfluence
    rw [ite_eq_right (hclosed ω hω)]
    by_cases hi : I ω
    · simp only [ite_eq_left hi,f]
    · have heq : f (insert e ω) = f ω := by
        unfold f finiteDensity
        rw [finiteRootComponent_insert_eq_of_not_incident G Q ω x e he hi]
      simp only [ite_eq_right hi,heq,sub_self,f]
  have hz : bernoulliPolynomial R (fun ω => finiteDensityInfluence G n x e (insert e ω)) p = 0 := by
    simp only [finiteDensityInfluence,Finset.mem_insert_self,if_true,bernoulliPolynomial_zero]
  change _ = -p*((1-p)*bernoulliPolynomial R (finiteDensityInfluence G n x e) p+
    p*bernoulliPolynomial R (fun ω => finiteDensityInfluence G n x e (insert e ω)) p)
  rw [hc,ho,hi,hz]
  ring

 
theorem finiteDensity_score_identity (G : BondGraph V E) (Q : Finset E) (n : ℕ)
    (x : V) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => finiteDensity G n x ω * finiteClusterScore G Q x p ω) p =
      -p * ∑ e ∈ Q, bernoulliPolynomial Q (finiteDensityInfluence G n x e) p := by
  have hf (ω : Finset E) : finiteDensity G n x ω * finiteClusterScore G Q x p ω =
      ∑ e ∈ Q, if e ∈ incidentBonds G Q (finiteRootComponent G ω x)
        then ((if e ∈ ω then 1 else 0)-p)*finiteDensity G n x ω else 0 := by
    unfold finiteClusterScore
    rw [Finset.mul_sum]
    symm
    rw [←Finset.sum_filter]
    have hs : Q.filter (fun e => e ∈ incidentBonds G Q (finiteRootComponent G ω x)) =
        incidentBonds G Q (finiteRootComponent G ω x) := by
      ext e
      simp only [Finset.mem_filter,mem_incidentBonds]
      tauto
    rw [hs]
    apply Finset.sum_congr rfl
    intro e _
    ring
  simp_rw [hf]
  rw [bernoulliPolynomial_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun e he => finiteDensity_score_one_bit G Q n x p e he

 

theorem finiteDensityInfluence_sum_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (d n : ℕ) (hn : 0 < n)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    (p:ℝ) * ∑ e ∈ Q, bernoulliPolynomial Q (finiteDensityInfluence G n x e) p ≤
      5*Real.sqrt (d*n:ℕ) := by
  have hid := finiteDensity_score_identity G Q n x p
  have hle := bernoulliPolynomial_mono Q
    (fun ω => -(finiteDensity G n x ω * finiteClusterScore G Q x p ω))
    (fun ω => cappedDensity n (finiteRootComponent G ω x).card * |finiteClusterScore G Q x p ω|)
    p p.2 (fun ω _ => by
      rw [←mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (cappedDensity_nonneg ..))
  have hneg : bernoulliPolynomial Q
      (fun ω => -(finiteDensity G n x ω * finiteClusterScore G Q x p ω)) p =
      -bernoulliPolynomial Q (fun ω => finiteDensity G n x ω * finiteClusterScore G Q x p ω) p := by
    simpa using bernoulliPolynomial_const_mul Q
      (fun ω => finiteDensity G n x ω * finiteClusterScore G Q x p ω) (-1) (p:ℝ)
  rw [hneg,hid] at hle
  have hb := cappedDensity_score_expectation_bound G Q x p d n hn hdeg
  linarith

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_TwoCluster_Transport
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite-volume two-cluster limits and transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterDensity_nonneg (G : BondGraph V E) (n : ℕ) (x : V) (ω : Set E) :
    0 ≤ clusterDensity G n x ω := cappedDensity_nonneg ..

theorem clusterDensity_le_one (G : BondGraph V E) (n : ℕ) (x : V) (ω : Set E) :
    clusterDensity G n x ω ≤ 1 := cappedDensity_le_one ..

theorem clusterDensity_antitone (G : BondGraph V E) (n : ℕ) (x : V)
    {ω η : Set E} (h : ω ⊆ η) : clusterDensity G n x η ≤ clusterDensity G n x ω := by
  by_cases hη : (cluster G η x).Finite
  · have hω : (cluster G ω x).Finite := hη.subset (fun y hy => conn_mono G h hy)
    exact cappedDensity_antitone n ((Set.ncard_pos hω).mpr ⟨x,mem_cluster_self G ω x⟩)
      (Set.ncard_le_ncard (fun y hy => conn_mono G h hy) hη)
  · rw [clusterDensity,Set.Infinite.ncard hη]
    simpa [cappedDensity] using clusterDensity_nonneg G n x ω

theorem densityInfluence_nonneg (G : BondGraph V E) (n : ℕ) (x : V) (e : E) (ω : Set E) :
    0 ≤ densityInfluence G n x e ω := by
  unfold densityInfluence
  split_ifs
  · exact le_rfl
  · exact sub_nonneg.mpr (clusterDensity_antitone G n x (Set.subset_insert e ω))

theorem densityInfluence_le_one (G : BondGraph V E) (n : ℕ) (x : V) (e : E) (ω : Set E) :
    densityInfluence G n x e ω ≤ 1 := by
  unfold densityInfluence
  split_ifs
  · norm_num
  · exact (sub_le_self _ (clusterDensity_nonneg ..)).trans (clusterDensity_le_one ..)

theorem measurable_clusterDensity (G : BondGraph V E) (hloc : LocallyFinite G) (n : ℕ) (x : V) :
    Measurable (clusterDensity G n x) :=
  (measurable_of_countable (cappedDensity n)).comp (measurable_cluster_ncard G hloc x)

theorem measurable_densityInfluence (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (x : V) (e : E) : Measurable (densityInfluence G n x e) := by
  exact measurable_const.ite (measurableSet_mem e)
    ((measurable_clusterDensity G hloc n x).sub
      ((measurable_clusterDensity G hloc n x).comp (measurable_set_insert e)))

theorem integrable_densityInfluence (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (x : V) (e : E) (p : unitInterval) :
    Integrable (densityInfluence G n x e) (law p) := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (measurable_densityInfluence G hloc n x e).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (densityInfluence_nonneg ..)]
    exact densityInfluence_le_one ..

theorem cluster_insert_finite (G : BondGraph V E) (ω : Set E) (e : E) (x a b : V)
    (he : G e = s(a,b)) (hx : (cluster G ω x).Finite)
    (ha : (cluster G ω a).Finite) (hb : (cluster G ω b).Finite) :
    (cluster G (insert e ω) x).Finite := by
  apply (hx.union (ha.union hb)).subset
  intro y hy
  rcases (conn_insert_iff G ω e a b x y he).mp hy with hy | ⟨_,hy⟩ | ⟨_,hy⟩
  · exact Or.inl hy
  · exact Or.inr (Or.inr hy)
  · exact Or.inr (Or.inl hy)

theorem cluster_insert_finite_ae (G : BondGraph V E) (p : unitInterval)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (x : V) (e : E) :
    ∀ᵐ ω ∂law p, (cluster G (insert e ω) x).Finite := by
  obtain ⟨a,b,he⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  filter_upwards [hfin x,hfin a,hfin b] with ω hx ha hb
  exact cluster_insert_finite G ω e x a b he hx ha hb

theorem finiteDensity_eq_clusterDensity (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (x : V) (ω : Set E) (hx : (cluster G ω x).Finite)
    (Q : Finset E) (hQ : incidentSupport G hloc hx.toFinset ⊆ Q) :
    finiteDensity G n x (domainBits Q ω) = clusterDensity G n x ω := by
  have hc : cluster G (domainBits Q ω:Set E) x = cluster G ω x := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hx.toFinset Q hQ ω x).mpr
      (Set.Finite.coe_toFinset hx).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  unfold finiteDensity clusterDensity
  rw [←Set.ncard_coe_finset,coe_finiteRootComponent,hc]

theorem domainBits_insert (Q : Finset E) (e : E) (he : e ∈ Q) (ω : Set E) :
    domainBits Q (insert e ω) = insert e (domainBits Q ω) := by
  ext f
  simp only [mem_domainBits,Set.mem_insert_iff,Finset.mem_insert]
  aesop

theorem densityInfluence_tendsto_finite [Encodable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (x : V) (e : E) (ω : Set E) (hx : (cluster G ω x).Finite)
    (he : (cluster G (insert e ω) x).Finite) (F : Finset E) :
    Tendsto (fun j => finiteDensityInfluence G n x e
      (domainBits (F ∪ vertexExhaustion (V := E) j) ω)) atTop
      (nhds (densityInfluence G n x e ω)) := by
  obtain ⟨jx,hjx⟩ := subset_vertexExhaustion (incidentSupport G hloc hx.toFinset)
  obtain ⟨je,hje⟩ := subset_vertexExhaustion (incidentSupport G hloc he.toFinset)
  obtain ⟨j₀,hj₀'⟩ := subset_vertexExhaustion ({e}:Finset E)
  have hj₀ : e ∈ vertexExhaustion (V := E) j₀ := hj₀' (by simp)
  have hev : (fun j => finiteDensityInfluence G n x e
      (domainBits (F ∪ vertexExhaustion (V := E) j) ω)) =ᶠ[atTop]
      (fun _ => densityInfluence G n x e ω) := by
    filter_upwards [eventually_ge_atTop (max jx (max je j₀))] with j hj
    let Q := F ∪ vertexExhaustion (V := E) j
    have hxQ : incidentSupport G hloc hx.toFinset ⊆ Q := fun z hz =>
      Finset.mem_union_right _ (vertexExhaustion_mono (by omega) (hjx hz))
    have heQ : incidentSupport G hloc he.toFinset ⊆ Q := fun z hz =>
      Finset.mem_union_right _ (vertexExhaustion_mono (by omega) (hje hz))
    have heQ' : e ∈ Q := Finset.mem_union_right _ (vertexExhaustion_mono (by omega) hj₀)
    change finiteDensityInfluence G n x e (domainBits Q ω) = _
    unfold finiteDensityInfluence densityInfluence
    simp only [mem_domainBits,heQ',true_and]
    split_ifs
    · rfl
    · rw [finiteDensity_eq_clusterDensity G hloc n x ω hx Q hxQ,
        ←domainBits_insert Q e heQ' ω,finiteDensity_eq_clusterDensity G hloc n x (insert e ω) he Q heQ]
  exact tendsto_const_nhds.congr' hev.symm

theorem densityInfluence_integral_tendsto [Encodable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (n : ℕ) (x : V) (e : E) (p : unitInterval)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (F : Finset E) :
    Tendsto (fun j => bernoulliPolynomial (F ∪ vertexExhaustion (V := E) j)
      (finiteDensityInfluence G n x e) p) atTop
      (nhds (∫ ω, densityInfluence G n x e ω ∂law p)) := by
  let Q := fun j => F ∪ vertexExhaustion (V := E) j
  let f := fun j ω => finiteDensityInfluence G n x e (domainBits (Q j) ω)
  have hfi (j : ℕ) : Integrable (f j) (law p) :=
    integrable_finite_local (Q j) p (f j) (fun ω => by dsimp [f]; rw [domainBits_local])
  have ht : ∀ᵐ ω ∂law p, Tendsto (fun j => f j ω) atTop (nhds (densityInfluence G n x e ω)) := by
    filter_upwards [hfin x,cluster_insert_finite_ae G p hfin x e] with ω hx he
    exact densityInfluence_tendsto_finite G hloc n x e ω hx he F
  have hd := tendsto_integral_of_dominated_convergence (fun _ : Set E => (1:ℝ))
    (fun j => (hfi j).aestronglyMeasurable) (integrable_const _)
    (fun j => Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (finiteDensityInfluence_nonneg ..)]
      exact finiteDensityInfluence_le_one ..)) ht
  simpa only [f,integral_domainBits,Q] using hd

 
theorem densityInfluence_finite_sum_bound [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d)
    (n : ℕ) (hn : 0 < n) (x : V) (p : unitInterval)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (F : Finset E) :
    (p:ℝ) * ∑ e ∈ F, (∫ ω, densityInfluence G n x e ω ∂law p) ≤
      5*Real.sqrt (d*n:ℕ) := by
  let : Encodable E := Encodable.ofCountable E
  let Q := fun j => F ∪ vertexExhaustion (V := E) j
  have ht := (tendsto_const_nhds (x := (p:ℝ)) (f := atTop)).mul (tendsto_finsetSum F
    (fun e _ => densityInfluence_integral_tendsto G hloc n x e p hfin F))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro j
  have hdeg (y : V) : ((Q j).filter fun e => y ∈ G e).card ≤ d := by
    calc
      _ = (((Q j).filter fun e => y ∈ G e):Set E).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ {e | y ∈ G e}.ncard := Set.ncard_le_ncard (fun e he => (Finset.mem_filter.mp he).2) (hloc y)
      _ ≤ d := hd y
  have hs : (∑ e ∈ F, bernoulliPolynomial (Q j) (finiteDensityInfluence G n x e) p) ≤
      ∑ e ∈ Q j, bernoulliPolynomial (Q j) (finiteDensityInfluence G n x e) p := by
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun e _ _ => bernoulliPolynomial_nonneg (Q j) _ p p.2 (fun ω _ => finiteDensityInfluence_nonneg ..))
  exact (mul_le_mul_of_nonneg_left hs p.2.1).trans
    (finiteDensityInfluence_sum_bound G (Q j) x p d n hn hdeg)

 
theorem densityInfluence_lintegral_sum_bound [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d)
    (n : ℕ) (hn : 0 < n) (x : V) (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) :
    (∑' e, ∫⁻ ω, ENNReal.ofReal (densityInfluence G n x e ω) ∂law p) ≤
      ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  simp_rw [←ofReal_integral_eq_lintegral_ofReal (integrable_densityInfluence G hloc n x _ p)
    (Eventually.of_forall (densityInfluence_nonneg G n x _))]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun e _ => integral_nonneg (densityInfluence_nonneg G n x e))]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using densityInfluence_finite_sum_bound G hloc d hd n hn x p hfin F

end Percolation

 

 

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_boundaryDensityInfluence [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (n : ℕ) (y : V) :
    Measurable (fun ω => boundaryDensityInfluence G n ω y) := by
  apply Measurable.tsum
  intro e
  by_cases h : y ∈ G e
  · simpa only [ite_eq_left h] using (measurable_densityInfluence G hloc n y e).ennreal_ofReal
  · simp only [ite_eq_right h]; exact measurable_const

theorem measurable_localDensityLoss [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (n : ℕ) (y : V) :
    Measurable (fun ω => localDensityLoss G n ω y) := by
  exact ((measurable_of_countable (fun k : ℕ => (k:ℝ≥0∞))).comp
    (measurable_cluster_ncard G hloc y)).mul (measurable_boundaryDensityInfluence G hloc n y)

theorem densityInfluence_eq_of_conn (G : BondGraph V E) (n : ℕ) (ω : Set E)
    (x y : V) (hxy : Conn G ω x y) (e : E) :
    densityInfluence G n x e ω = densityInfluence G n y e ω := by
  unfold densityInfluence clusterDensity
  rw [cluster_eq_of_conn G ω hxy,
    cluster_eq_of_conn G (insert e ω) (conn_mono G (Set.subset_insert e ω) hxy)]

theorem densityInfluence_aut (G : BondGraph V E) (n : ℕ) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (e : E) :
    densityInfluence G n x e (b ⁻¹' ω) = densityInfluence G n (a x) (b e) ω := by
  have hins : insert e (b ⁻¹' ω) = b ⁻¹' (insert (b e) ω) := by
    ext f
    simp only [Set.mem_insert_iff,Set.mem_preimage,b.injective.eq_iff]
  simp only [densityInfluence,Set.mem_preimage,clusterDensity,hins,
    cluster_ncard_covariant G hab]

theorem localDensityLoss_aut (G : BondGraph V E) (n : ℕ) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    localDensityLoss G n (b ⁻¹' ω) x = localDensityLoss G n ω (a x) := by
  unfold localDensityLoss boundaryDensityInfluence
  rw [cluster_ncard_covariant G hab,←b.tsum_eq (fun e =>
    if a x ∈ G e then ENNReal.ofReal (densityInfluence G n (a x) e ω) else 0)]
  congr 1
  apply tsum_congr
  intro e
  have hm : a x ∈ G (b e) ↔ x ∈ G e := by
    rw [hab e,Sym2.mem_map]
    constructor
    · rintro ⟨z,hz,hzx⟩
      exact a.injective hzx ▸ hz
    · intro h; exact ⟨x,h,rfl⟩
  simp only [hm,densityInfluence_aut G n hab]

 
theorem tsum_bond_endpoints_le_two (G : BondGraph V E) (e : E) (c : ℝ≥0∞) :
    (∑' y, if y ∈ G e then c else 0) ≤ 2*c := by
  obtain ⟨a,b,he⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  calc
    _ ≤ ∑' y, ((if y = a then c else 0)+(if y = b then c else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases h : y ∈ G e
      · rw [ite_eq_left h]
        rw [he,Sym2.mem_iff] at h
        rcases h with rfl | rfl <;> simp
      · rw [ite_eq_right h]; exact zero_le
    _ = 2*c := by rw [ENNReal.tsum_add]; simp; ring

 

theorem clusterAveraged_localDensityLoss_le (G : BondGraph V E) (n : ℕ)
    (ω : Set E) (x : V) (hx : (cluster G ω x).Finite) :
    (∑' y, clusterAveragingKernel G ω x y * localDensityLoss G n ω y) ≤
      2 * ∑' e, ENNReal.ofReal (densityInfluence G n x e ω) := by
  have hf (y : V) : clusterAveragingKernel G ω x y * localDensityLoss G n ω y ≤
      ∑' e, if y ∈ G e then ENNReal.ofReal (densityInfluence G n x e ω) else 0 := by
    by_cases hxy : Conn G ω x y
    · have hc := cluster_eq_of_conn G ω hxy
      have hpos : ((cluster G ω x).ncard:ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (cluster_ncard_pos G ω x hx).ne'
      unfold clusterAveragingKernel localDensityLoss
      rw [ite_eq_left hxy,←hc,←mul_assoc,ENNReal.inv_mul_cancel hpos (ENNReal.natCast_ne_top _),one_mul]
      unfold boundaryDensityInfluence
      simp_rw [densityInfluence_eq_of_conn G n ω x y hxy]
      exact le_rfl
    · simp only [clusterAveragingKernel,ite_eq_right hxy,zero_mul]; exact zero_le
  calc
    _ ≤ ∑' y, ∑' e, if y ∈ G e then ENNReal.ofReal (densityInfluence G n x e ω) else 0 :=
      ENNReal.tsum_le_tsum hf
    _ = ∑' e, ∑' y, if y ∈ G e then ENNReal.ofReal (densityInfluence G n x e ω) else 0 :=
      ENNReal.tsum_comm
    _ ≤ ∑' e, 2*ENNReal.ofReal (densityInfluence G n x e ω) :=
      ENNReal.tsum_le_tsum (fun e => tsum_bond_endpoints_le_two G e _)
    _ = _ := ENNReal.tsum_mul_left

theorem clusterAveraged_localDensityLoss_integral_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d) (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (x : V) :
    (∫⁻ ω, ∑' y, clusterAveragingKernel G ω x y * localDensityLoss G n ω y ∂law p) ≤
      2 * ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ)) := by
  calc
    _ ≤ ∫⁻ ω, 2 * ∑' e, ENNReal.ofReal (densityInfluence G n x e ω) ∂law p := by
      apply lintegral_mono_ae
      filter_upwards [hfin x] with ω hω
      exact clusterAveraged_localDensityLoss_le G n ω x hω
    _ = 2 * ∑' e, ∫⁻ ω, ENNReal.ofReal (densityInfluence G n x e ω) ∂law p := by
      rw [lintegral_const_mul _ (Measurable.tsum (fun e =>
        (measurable_densityInfluence G hloc n x e).ennreal_ofReal)),lintegral_tsum]
      exact fun e => (measurable_densityInfluence G hloc n x e).ennreal_ofReal.aemeasurable
    _ ≤ _ := mul_le_mul_right (densityInfluence_lintegral_sum_bound G hloc d hd n hn x p hp hfin) 2

 
theorem weighted_localDensityLoss_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d) (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) ≤
      2 * ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ)) := by
  rw [←root_cluster_average G hconn hloc root weight Γ hΓ htr hw p hfin
    (localDensityLoss G n) (measurable_localDensityLoss G hloc n)
    (fun a ha b hab ω x => localDensityLoss_aut G n hab ω x)]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (weight i) * (2 * ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ))) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_right
        (clusterAveraged_localDensityLoss_integral_bound G hloc d hd n hn p hp hfin (root i)) _
    _ = _ := by
      rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hw1]
      simp

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_TwoCluster_Bounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative two-cluster probability bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem localDensityLoss_integral_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d) (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (y : V) :
    (∫⁻ ω, localDensityLoss G n ω y ∂law p) ≤
      ENNReal.ofReal (10*c*Real.sqrt (d*n:ℕ)/(p:ℝ)) := by
  obtain ⟨i,a,ha,hai⟩ := hcov y
  obtain ⟨b,hab⟩ := hΓ ha
  have he : (∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) =
      ∫⁻ ω, localDensityLoss G n ω y ∂law p := by
    have ht := lintegral_map (μ := law p) (measurable_localDensityLoss G hloc n (root i))
      (measurable_set_preimage b)
    rw [law_map_preimage_equiv] at ht
    rw [ht]
    apply lintegral_congr
    intro ω
    rw [localDensityLoss_aut G n hab,hai]
  have hwi : (1:ℝ≥0∞) ≤ ENNReal.ofReal c * ENNReal.ofReal (weight i) := by
    rw [←ENNReal.ofReal_mul hc]
    exact_mod_cast ENNReal.ofReal_le_ofReal (hmin i)
  have hsingle : ENNReal.ofReal (weight i) * (∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) ≤
      ∑ j, ENNReal.ofReal (weight j) * ∫⁻ ω, localDensityLoss G n ω (root j) ∂law p :=
    Finset.single_le_sum (f := fun j => ENNReal.ofReal (weight j) *
      ∫⁻ ω, localDensityLoss G n ω (root j) ∂law p) (fun j _ => zero_le) (Finset.mem_univ i)
  calc
    _ = 1 * (∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) := by rw [he,one_mul]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (weight i) *
      ∫⁻ ω, localDensityLoss G n ω (root i) ∂law p) := by
      rw [←mul_assoc]
      exact mul_le_mul_left hwi _
    _ ≤ ENNReal.ofReal c * (∑ j, ENNReal.ofReal (weight j) *
      ∫⁻ ω, localDensityLoss G n ω (root j) ∂law p) := mul_le_mul_right hsingle _
    _ ≤ ENNReal.ofReal c * (2 * ENNReal.ofReal (5*Real.sqrt (d*n:ℕ)/(p:ℝ))) :=
      mul_le_mul_right (weighted_localDensityLoss_bound G hconn hloc root weight Γ hΓ htr hw hw1
        d hd n hn p hp hfin) _
    _ = _ := by
      rw [←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num),←ENNReal.ofReal_mul hc]
      congr 1
      ring

 
theorem cluster_insert_left_eq_union (G : BondGraph V E) (ω : Set E)
    (e : E) (a b : V) (he : G e = s(a,b)) :
    cluster G (insert e ω) a = cluster G ω a ∪ cluster G ω b := by
  ext y
  change Conn G (insert e ω) a y ↔ Conn G ω a y ∨ Conn G ω b y
  rw [conn_insert_iff G ω e a b a y he]
  constructor
  · rintro (h | ⟨_,h⟩ | ⟨_,h⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨conn_refl G ω a,h⟩)

theorem endpoint_density_defect (G : BondGraph V E) (ω : Set E)
    (e : E) (a b : V) (he : G e = s(a,b)) (hab : ¬Conn G ω a b)
    (ha : (cluster G ω a).Finite) (hb : (cluster G ω b).Finite)
    (n : ℕ) (hna : n ≤ (cluster G ω a).ncard) (hnb : n ≤ (cluster G ω b).ncard) :
    ((cluster G ω a).ncard:ℝ)*densityInfluence G n a e ω +
      ((cluster G ω b).ncard:ℝ)*densityInfluence G n b e ω = n := by
  have hc : e ∉ ω := fun h => hab (.single ⟨e,h,he⟩)
  have hdis : Disjoint (cluster G ω a) (cluster G ω b) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hab (conn_trans G ω hz (conn_symm G ω hz'))
  have hins : Conn G (insert e ω) a b := .single ⟨e,Set.mem_insert e ω,he⟩
  have hs : (cluster G (insert e ω) a).ncard = (cluster G ω a).ncard+(cluster G ω b).ncard := by
    rw [cluster_insert_left_eq_union G ω e a b he,Set.ncard_union_eq hdis ha hb]
  have hsa : 0 < ((cluster G ω a).ncard:ℝ) := by exact_mod_cast cluster_ncard_pos G ω a ha
  have hsb : 0 < ((cluster G ω b).ncard:ℝ) := by exact_mod_cast cluster_ncard_pos G ω b hb
  have hna' : (n:ℝ) ≤ (cluster G ω a).ncard := by exact_mod_cast hna
  have hnb' : (n:ℝ) ≤ (cluster G ω b).ncard := by exact_mod_cast hnb
  unfold densityInfluence clusterDensity cappedDensity
  rw [ite_eq_right hc,ite_eq_right hc,←cluster_eq_of_conn G (insert e ω) hins,hs,Nat.cast_add,
    min_eq_left hna',min_eq_left hnb',min_eq_left (by linarith : (n:ℝ) ≤
      (cluster G ω a).ncard+(cluster G ω b).ncard)]
  field_simp
  ring

theorem localDensityLoss_ge_edge (G : BondGraph V E) (n : ℕ) (ω : Set E)
    (e : E) (a : V) (ha : a ∈ G e) :
    ((cluster G ω a).ncard:ℝ≥0∞)*ENNReal.ofReal (densityInfluence G n a e ω) ≤
      localDensityLoss G n ω a := by
  apply mul_le_mul_right
  exact (le_of_eq (ite_eq_left ha).symm).trans
    (ENNReal.le_tsum (f := fun edge =>
      if a ∈ G edge then ENNReal.ofReal (densityInfluence G n a edge ω) else 0) e)

theorem two_large_endpoint_loss (G : BondGraph V E) (ω : Set E)
    (e : E) (a b : V) (he : G e = s(a,b)) (ha : (cluster G ω a).Finite)
    (hb : (cluster G ω b).Finite) (n : ℕ)
    (h : ¬Conn G ω a b ∧ ω ∈ clusterLarge G a n ∧ ω ∈ clusterLarge G b n) :
    (n:ℝ≥0∞) ≤ localDensityLoss G n ω a + localDensityLoss G n ω b := by
  have hsz (v : V) (hv : (cluster G ω v).Finite) (hh : ω ∈ clusterLarge G v n) :
      n ≤ (cluster G ω v).ncard := by
    obtain ⟨t,ht,hct⟩ := hh
    exact ht.trans (by rw [←Set.ncard_coe_finset]; exact Set.ncard_le_ncard hct hv)
  have hid := endpoint_density_defect G ω e a b he h.1 ha hb n (hsz a ha h.2.1) (hsz b hb h.2.2)
  have hid' := congrArg ENNReal.ofReal hid
  rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) (densityInfluence_nonneg ..))
    (mul_nonneg (Nat.cast_nonneg _) (densityInfluence_nonneg ..)),
    ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hid'
  simp only [ENNReal.ofReal_natCast] at hid'
  rw [←hid']
  exact add_le_add (localDensityLoss_ge_edge G n ω e a (by rw [he]; simp))
    (localDensityLoss_ge_edge G n ω e b (by rw [he]; simp))

end Percolation

 

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq



theorem measurableSet_twoLargeEvent [Countable V] [Countable E] (G : BondGraph V E) (a b : V) (n : ℕ) :
    MeasurableSet (twoLargeEvent G a b n) :=
  (measurableSet_conn G a b).compl.inter
    ((measurableSet_clusterLarge G a n).inter (measurableSet_clusterLarge G b n))

theorem twoLarge_probability_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d) (n : ℕ) (hn : 0 < n)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (e : E) (a b : V) (he : G e = s(a,b)) :
    (n:ℝ) * (law p).real (twoLargeEvent G a b n) ≤
      20*c*Real.sqrt (d*n:ℕ)/(p:ℝ) := by
  have hpoint : ∀ᵐ ω ∂law p,
      (twoLargeEvent G a b n).indicator (fun _ => (n:ℝ≥0∞)) ω ≤
        localDensityLoss G n ω a + localDensityLoss G n ω b := by
    filter_upwards [hfin a,hfin b] with ω ha hb
    by_cases h : ω ∈ twoLargeEvent G a b n
    · rw [Set.indicator_of_mem h]
      exact two_large_endpoint_loss G ω e a b he ha hb n h
    · rw [Set.indicator_of_notMem h]
      exact zero_le
  have hi := lintegral_mono_ae hpoint
  rw [lintegral_indicator (measurableSet_twoLargeEvent G a b n),lintegral_const,
    lintegral_add_left (measurable_localDensityLoss G hloc n a)] at hi
  have hbnd (y : V) := localDensityLoss_integral_bound G hconn hloc root weight Γ hΓ htr
    hcov hw hw1 c hc hmin d hd n hn p hp hfin y
  have hi' := hi.trans (add_le_add (hbnd a) (hbnd b))
  rw [←ENNReal.ofReal_add (by positivity : 0 ≤ 10*c*Real.sqrt (d*n:ℕ)/(p:ℝ))
    (by positivity : 0 ≤ 10*c*Real.sqrt (d*n:ℕ)/(p:ℝ))] at hi'
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi'
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity)] at ht
  simp only [Measure.restrict_apply_univ] at ht
  dsimp [Measure.real] at ht ⊢
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

 

theorem finiteWitness_eventually_iff (A : Set (Set E)) (hu : IsUpperSet A)
    (hf : FiniteWitness A) (ω : ℕ → Set E) (hm : Monotone ω) :
    ∀ᶠ j in atTop, ω j ∈ A ↔ (⋃ k, ω k) ∈ A := by
  by_cases h : (⋃ k, ω k) ∈ A
  · obtain ⟨t,ht,htA⟩ := hf _ h
    have ht' : ∀ e ∈ t, ∃ k, e ∈ ω k := by
      intro e he
      exact Set.mem_iUnion.mp (ht he)
    choose k hk using fun e : t => ht' e e.property
    let N := t.attach.sup k
    have hN : (t : Set E) ⊆ ω N := by
      intro e he
      exact hm (Finset.le_sup (f := k) (Finset.mem_attach t ⟨e,he⟩)) (hk ⟨e,he⟩)
    filter_upwards [eventually_ge_atTop N] with j hj
    exact iff_of_true (hu (hN.trans (hm hj)) htA) h
  · exact Eventually.of_forall (fun j => iff_of_false
      (fun hj => h (hu (Set.subset_iUnion ω j) hj)) h)

theorem twoLarge_probability_tendsto [Countable V] [Countable E] (G : BondGraph V E)
    (p : ℕ → unitInterval) (hp : Monotone p) (q : unitInterval)
    (hle : ∀ j, p j ≤ q) (hlim : Tendsto p atTop (𝓝 q)) (a b : V) (n : ℕ) :
    Tendsto (fun j => (law (p j)).real (twoLargeEvent G a b n)) atTop
      (𝓝 ((law q).real (twoLargeEvent G a b n))) := by
  let A := twoLargeEvent G a b n
  let f := fun r labels => A.indicator (fun _ => (1:ℝ)) (openEdges labels r)
  have hfi (r : unitInterval) : Integrable (f r) labelLaw := by
    have hi : Integrable (A.indicator (fun _ => (1:ℝ))) (law r) :=
      (integrable_const _).indicator (measurableSet_twoLargeEvent G a b n)
    rw [←map_openEdges r] at hi
    exact hi.comp_measurable (measurable_openEdges r)
  have ht : ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      Tendsto (fun j => f (p j) labels) atTop (𝓝 (f q labels)) := by
    filter_upwards [ae_labels_ne (E := E) q] with labels hlabels
    have hm : Monotone (fun j => openEdges labels (p j)) :=
      fun j k hjk => openEdges_mono labels (hp hjk)
    have he := openEdges_eq_iUnion_of_tendsto labels q hlabels p hle hlim
    have hC := finiteWitness_eventually_iff {ω | Conn G ω a b}
      (fun _ _ hω h => conn_mono G hω h) (finiteWitness_conn G a b) _ hm
    have ha := finiteWitness_eventually_iff (clusterLarge G a n)
      (clusterLarge_upper G a n) (finiteWitness_clusterLarge G a n) _ hm
    have hb := finiteWitness_eventually_iff (clusterLarge G b n)
      (clusterLarge_upper G b n) (finiteWitness_clusterLarge G b n) _ hm
    rw [←he] at hC ha hb
    apply tendsto_const_nhds.congr'
    filter_upwards [hC,ha,hb] with j hC ha hb
    have hi : openEdges labels (p j) ∈ A ↔ openEdges labels q ∈ A := by
      exact and_congr (not_congr hC) (and_congr ha hb)
    simp only [f,Set.indicator_apply]
    rw [hi]
  have ht' := tendsto_integral_of_dominated_convergence (fun _ : E → unitInterval => (1:ℝ))
    (fun j => (hfi (p j)).aestronglyMeasurable) (integrable_const _)
    (fun j => Eventually.of_forall (fun labels => by
      simp only [f,Set.indicator_apply]
      split <;> norm_num)) ht
  have heq (r : unitInterval) : (∫ labels, f r labels ∂labelLaw) = (law r).real A := by
    calc
      _ = ∫ ω, A.indicator (fun _ => (1:ℝ)) ω ∂law r := by
        rw [←map_openEdges r]
        exact (integral_map (measurable_openEdges r).aemeasurable
          ((measurable_const.indicator (measurableSet_twoLargeEvent G a b n)).aestronglyMeasurable)).symm
      _ = _ := by rw [integral_indicator_const _ (measurableSet_twoLargeEvent G a b n)]; simp [A]
  simpa only [heq] using ht'

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Finiteness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical two-cluster estimates, finite opening and almost-sure finite clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

section RootData
variable [Countable V] [Countable E] [Nonempty V]
variable (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
  (hqt : QuasiTransitive G)
  {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
  (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
  (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
  (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
  (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
  (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d)

include hconn hloc hqt hΓ htr hcov hw hw1 hc hmin hd

 

omit [Nonempty V] in
theorem critical_twoLarge_probability_bound
    (n : ℕ) (hn : 0 < n) (e : E) (a b : V) (he : G e = s(a,b)) :
    (pc G:ℝ) * ((n:ℝ) * (law (pc G)).real (twoLargeEvent G a b n)) ≤
      20*c*Real.sqrt (d*n:ℕ) := by
  obtain ⟨p,hp,hpc,hlim⟩ := exists_seq_strictMono_tendsto' (pc_pos G hloc hqt)
  have ht := (continuous_subtype_val.tendsto (pc G) |>.comp hlim).mul
    ((tendsto_const_nhds (x := (n:ℝ))).mul (twoLarge_probability_tendsto G p hp.monotone (pc G)
      (fun j => (hpc j).2.le) hlim a b n))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro j
  have hb := twoLarge_probability_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1
    c hc hmin d hd n hn (p j) (hpc j).1
      (subcritical_cluster_finite_ae G (p j) (hpc j).2) e a b he
  change (p j:ℝ) * ((n:ℝ) * (law (p j)).real (twoLargeEvent G a b n)) ≤ _
  rw [mul_comm (p j:ℝ)]
  exact (le_div_iff₀ (hpc j).1).mp hb

 

omit [Nonempty V] in
theorem critical_adjacent_infinite_connected (e : E) (a b : V) (he : G e = s(a,b)) :
    ∀ᵐ ω ∂law (pc G), (cluster G ω a).Infinite → (cluster G ω b).Infinite → Conn G ω a b := by
  let A : Set (Set E) := {ω | ¬Conn G ω a b ∧
    (cluster G ω a).Infinite ∧ (cluster G ω b).Infinite}
  have hA : MeasurableSet A := (measurableSet_conn G a b).compl.inter
    ((measurableSet_infinite_cluster G a).inter (measurableSet_infinite_cluster G b))
  have hp : 0 < (pc G:ℝ) := pc_pos G hloc hqt
  have hzero : (law (pc G)).real A = 0 := by
    by_contra hne
    have hθ : 0 < (law (pc G)).real A := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    have hb (n : ℕ) (hn : 0 < n) :
        (pc G:ℝ)*((n:ℝ)*(law (pc G)).real A) ≤ 20*c*Real.sqrt (d*n:ℕ) := by
      have hs : A ⊆ twoLargeEvent G a b n := by
        intro ω h
        refine ⟨h.1,?_,?_⟩
        · have hx : ω ∈ {ω | (cluster G ω a).Infinite} := h.2.1
          rw [infinite_cluster_eq_iInter G a] at hx
          exact Set.mem_iInter.mp hx n
        · have hx : ω ∈ {ω | (cluster G ω b).Infinite} := h.2.2
          rw [infinite_cluster_eq_iInter G b] at hx
          exact Set.mem_iInter.mp hx n
      exact (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (measureReal_mono hs) (Nat.cast_nonneg n)) hp.le).trans
          (critical_twoLarge_probability_bound G hconn hloc hqt root weight Γ hΓ htr hcov
            hw hw1 c hc hmin d hd n hn e a b he)
    let B := 20*c*Real.sqrt (d:ℝ)
    obtain ⟨m,hm⟩ := exists_nat_gt (B / ((pc G:ℝ)*(law (pc G)).real A) + 1)
    have hmpos : 0 < (m:ℝ) := lt_trans (by dsimp [B]; positivity) hm
    have hmn : 0 < m := by exact_mod_cast hmpos
    have hb' := hb (m^2) (pow_pos hmn _)
    have hsqrt : Real.sqrt (d*(m^2):ℕ) = Real.sqrt (d:ℝ)*(m:ℝ) := by
      rw [Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (Nat.cast_nonneg d),Real.sqrt_sq (Nat.cast_nonneg m)]
    rw [hsqrt,Nat.cast_pow] at hb'
    have hcancel : (pc G:ℝ)*(law (pc G)).real A*(m:ℝ) ≤ B := by
      apply (mul_le_mul_iff_left₀ hmpos).mp
      change ((pc G:ℝ)*(law (pc G)).real A*(m:ℝ))*(m:ℝ) ≤ B*(m:ℝ)
      dsimp only [B]
      nlinarith only [hb']
    have hlt : B < (pc G:ℝ)*(law (pc G)).real A*(m:ℝ) := by
      have hdiv : B / ((pc G:ℝ)*(law (pc G)).real A) < (m:ℝ) := by linarith
      have hh := (div_lt_iff₀ (mul_pos hp hθ)).mp hdiv
      nlinarith
    exact (not_lt_of_ge hcancel) hlt
  have hn : law (pc G) A = 0 := (measureReal_eq_zero_iff).mp hzero
  have hae : ∀ᵐ ω ∂law (pc G), ω ∉ A := by
    rw [ae_iff]; simpa using hn
  filter_upwards [hae] with ω hω ha hb
  by_contra hc
  exact hω ⟨hc,ha,hb⟩

end RootData
end Percolation

 

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem measure_union_finset_null [Countable E] (p : unitInterval) (hp : 0 < (p:ℝ))
    (A : Set (Set E)) (hA : MeasurableSet A) (hzero : law p A = 0) (F : Finset E) :
    law p {ω | ω ∪ (F:Set E) ∈ A} = 0 := by
  let B : Set (Set E) := {ω | ω ∪ (F:Set E) ∈ A}
  let C : Set (Set E) := {ω | (F:Set E) ⊆ ω}
  have hB : MeasurableSet B := hA.preimage
    (measurable_set_union_pair.comp (measurable_id.prodMk measurable_const))
  have hC : MeasurableSet C := by
    change MeasurableSet {ω | ∀ e ∈ F, e ∈ ω}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun _ => measurableSet_mem e
  have heB : (fun ω : Set E => ω ∩ (F:Set E)ᶜ) ⁻¹' B = B := by
    ext ω
    have he : (ω ∩ (F:Set E)ᶜ) ∪ (F:Set E) = ω ∪ (F:Set E) := by
      ext t
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
      tauto
    simp only [Set.mem_preimage,B,Set.mem_ofPred_eq,he]
  have heC : (fun ω : Set E => ω ∩ (F:Set E)) ⁻¹' C = C := by
    ext ω
    simp [C]
  have hi := restriction_events_independent p (F:Set E)ᶜ (F:Set E)
    (Set.disjoint_left.mpr (fun _ hx hy => hx hy)) B C hB hC
  rw [heB,heC] at hi
  have hBC : law p (B ∩ C) = 0 := measure_mono_null (by
    intro ω h
    have he : ω ∪ (F:Set E) = ω := Set.union_eq_left.mpr h.2
    simpa only [B,Set.mem_ofPred_eq,he] using h.1) hzero
  have hCp : 0 < (law p).real C := by
    rw [show C = {ω | (F:Set E) ⊆ ω} from rfl,finite_open_probability]
    exact pow_pos hp _
  exact (mul_eq_zero.mp (hi.symm.trans hBC)).resolve_right
    (fun h => by simp [Measure.real,h] at hCp)

theorem ae_union_finset [Countable E] (p : unitInterval) (hp : 0 < (p:ℝ))
    (A : Set (Set E)) (hA : MeasurableSet A) (hae : ∀ᵐ ω ∂law p, ω ∈ A) (F : Finset E) :
    ∀ᵐ ω ∂law p, ω ∪ (F:Set E) ∈ A := by
  rw [ae_iff] at hae ⊢
  exact measure_union_finset_null p hp Aᶜ hA.compl hae F

 

theorem atMostOne_of_finite_openings (G : BondGraph V E) (hconn : Connected G) (ω : Set E)
    (h : ∀ F : Finset E, ∀ a b, Adj G a b →
      (cluster G (ω ∪ (F:Set E)) a).Infinite →
      (cluster G (ω ∪ (F:Set E)) b).Infinite → Conn G (ω ∪ (F:Set E)) a b) :
    ∀ x y, (cluster G ω x).Infinite → (cluster G ω y).Infinite → Conn G ω x y := by
  intro x y hx hy
  by_contra hxy
  have hF : ∀ F : Finset E, ¬Conn G (ω ∪ (F:Set E)) x y := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa only [Finset.coe_empty,Set.union_empty] using hxy
    | @insert e F he ih =>
      have heq : ω ∪ ((insert e F : Finset E):Set E) = insert e (ω ∪ (F:Set E)) := by
        ext t; simp only [Finset.coe_insert,Set.mem_union,Set.mem_insert_iff]; tauto
      rw [heq]
      obtain ⟨⟨a,b⟩,hab'⟩ := Sym2.mk_surjective (G e)
      have hab : G e = s(a,b) := hab'.symm
      rw [conn_insert_iff G _ e a b x y hab]
      rintro (hc | ⟨hxa,hby⟩ | ⟨hxb,hay⟩)
      · exact ih hc
      · have ha : (cluster G (ω ∪ (F:Set E)) a).Infinite := by
          rw [←cluster_eq_of_conn G _ hxa]
          exact hx.mono (fun z hz => conn_mono G Set.subset_union_left hz)
        have hb : (cluster G (ω ∪ (F:Set E)) b).Infinite := by
          rw [cluster_eq_of_conn G _ hby]
          exact hy.mono (fun z hz => conn_mono G Set.subset_union_left hz)
        exact ih (conn_trans G _ hxa (conn_trans G _ (h F a b ⟨e,hab⟩ ha hb) hby))
      · have hb : (cluster G (ω ∪ (F:Set E)) b).Infinite := by
          rw [←cluster_eq_of_conn G _ hxb]
          exact hx.mono (fun z hz => conn_mono G Set.subset_union_left hz)
        have ha : (cluster G (ω ∪ (F:Set E)) a).Infinite := by
          rw [cluster_eq_of_conn G _ hay]
          exact hy.mono (fun z hz => conn_mono G Set.subset_union_left hz)
        exact ih (conn_trans G _ hxb (conn_trans G _
          (conn_symm G _ (h F a b ⟨e,hab⟩ ha hb)) hay))
  obtain ⟨F,_,hFc⟩ := finiteWitness_conn G x y Set.univ (conn_univ_of_connected G hconn x y)
  exact hF F (conn_mono G Set.subset_union_right hFc)

end Percolation

 

 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
open scoped ENNReal

 
theorem twoPoint_mul_le [Countable E] (G : BondGraph V E) (p : unitInterval)
    (x y z : V) : twoPoint G p x y * twoPoint G p y z ≤ twoPoint G p x z := by
  have h := association_finiteWitness p {ω : Set E | Conn G ω x y}
    {ω : Set E | Conn G ω y z}
    (fun _ _ hω h => conn_mono G hω h) (fun _ _ hω h => conn_mono G hω h)
    (finiteWitness_conn G x y) (finiteWitness_conn G y z)
  exact h.trans (measureReal_mono (fun ω hω => conn_trans G ω hω.1 hω.2))

 
theorem reachBall_add_split (G : BondGraph V E) (x : V) (n m : ℕ) {y : V}
    (hy : y ∈ reachBall G x (n+m)) :
    ∃ z ∈ reachBall G x n, y ∈ reachBall G z m := by
  induction m generalizing y with
  | zero => exact ⟨y,hy,Set.mem_singleton y⟩
  | succ m ih =>
    rcases hy with hy | hy
    · obtain ⟨z,hz,hyz⟩ := ih hy
      exact ⟨z,hz,Or.inl hyz⟩
    · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy
      obtain ⟨w,hw,hwy⟩ := hy
      obtain ⟨z,hz,hwz⟩ := ih hw
      refine ⟨z,hz,Or.inr ?_⟩
      exact Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨hwz,hwy⟩⟩

 
theorem twoPoint_lower_on_multiples [Countable E] (G : BondGraph V E)
    (p : unitInterval) (n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hball : ∀ x y, y ∈ reachBall G x n → c ≤ twoPoint G p x y)
    (k : ℕ) (x y : V) (hy : y ∈ reachBall G x (n*k)) :
    c^k ≤ twoPoint G p x y := by
  induction k generalizing x y with
  | zero =>
    have he : y = x := by simpa [reachBall] using hy
    subst y
    simp [twoPoint_self]
  | succ k ih =>
    rw [Nat.mul_succ] at hy
    obtain ⟨z,hz,hyz⟩ := reachBall_add_split G x (n*k) n hy
    calc
      c^(k+1) = c^k*c := pow_succ _ _
      _ ≤ twoPoint G p x z * twoPoint G p z y :=
        mul_le_mul (ih x z hz) (hball z y hyz) hc (twoPoint_nonneg G p x z)
      _ ≤ twoPoint G p x y := twoPoint_mul_le G p x z y

 
theorem reachBall_exponential_growth (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 ≤ hV G) (x : V) (n : ℕ) :
    (1+hV G)^n ≤ ((reachBall G x n).ncard : ℝ) := by
  classical
  induction n with
  | zero => simp [reachBall]
  | succ n ih =>
    let A := (finite_reachBall hloc x n).toFinset
    have he : reachBall G x (n+1) = (A : Set V) ∪ vertexBoundary G A := by
      ext y
      simp only [reachBall,Set.mem_union,Finset.mem_coe,
        vertexBoundary,Set.mem_ofPred_eq,Set.mem_iUnion]
      simp only [A,Set.Finite.mem_toFinset]
      constructor
      · rintro (hy | ⟨z,hz,hzy⟩)
        · exact Or.inl hy
        · by_cases hy : y ∈ reachBall G x n
          · exact Or.inl hy
          · exact Or.inr ⟨hy,z,hz,hzy⟩
      · rintro (hy | ⟨_,z,hz,hzy⟩)
        · exact Or.inl hy
        · exact Or.inr ⟨z,hz,hzy⟩
    have hd : Disjoint (A : Set V) (vertexBoundary G A) := by
      exact Set.disjoint_left.mpr (fun y hy hb => hb.1 hy)
    have hc : (reachBall G x (n+1)).ncard = A.card + (vertexBoundary G A).ncard := by
      rw [he,Set.ncard_union_eq hd A.finite_toSet (finite_vertexBoundary G hloc A),Set.ncard_coe_finset]
    have hcard : A.card = (reachBall G x n).ncard :=
      (Set.ncard_eq_toFinset_card _ (finite_reachBall hloc x n)).symm
    have hs := hV_mul_card_le G A
    rw [hcard] at hs
    rw [hc,hcard,Nat.cast_add,pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+hV G by linarith)]

 

theorem exists_subcritical_ball_lower [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (c : ℝ) (hc : 0 < c) (hcrit : ∀ x y, c ≤ twoPoint G (pc G) x y)
    (n : ℕ) : ∃ p : unitInterval, p < pc G ∧
      ∀ x y, y ∈ reachBall G x n → c/2 ≤ twoPoint G p x y := by
  classical
  obtain ⟨p,hp,hpc,hlim⟩ := exists_seq_strictMono_tendsto' (pc_pos G hloc hqt)
  obtain ⟨s,hs⟩ := hqt
  have hev : ∀ᶠ k in atTop, ∀ x ∈ s, ∀ y ∈ reachBall G x n,
      c/2 ≤ twoPoint G (p k) x y := by
    apply (eventually_all_finset s).mpr
    intro x hx
    apply (finite_reachBall hloc x n).eventually_all.mpr
    intro y hy
    have ht := twoPoint_tendsto_of_monotone G p hp.monotone (pc G)
      (fun k => (hpc k).2.le) hlim x y
    have hlt : c/2 < twoPoint G (pc G) x y := lt_of_lt_of_le (by linarith) (hcrit x y)
    exact (ht.eventually (eventually_gt_nhds hlt)).mono (fun k hk => hk.le)
  obtain ⟨k,hk⟩ := hev.exists
  refine ⟨p k,(hpc k).2,?_⟩
  intro x y hy
  obtain ⟨o,ho,a,b,ha,hax⟩ := hs x
  have hy' : a.symm y ∈ reachBall G o n := by
    have hi := mem_reachBall_aut G (isAut_symm G ha) hy
    simpa [←hax] using hi
  have he := twoPoint_aut G (p k) ha o (a.symm y)
  rw [hax,a.apply_symm_apply] at he
  rw [he]
  exact hk o ho (a.symm y) hy'

 

theorem no_uniform_positive_twoPoint_critical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x y, c ≤ twoPoint G (pc G) x y := by
  rintro ⟨c,hc,hcrit⟩
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2/c) (show 1 < 1+hV G by linarith)
  have hn' : 1 < (c/2)*(1+hV G)^n := by
    have := (div_lt_iff₀ hc).mp hn
    nlinarith
  obtain ⟨p,hp,hball⟩ := exists_subcritical_ball_lower G hloc hqt c hc hcrit n
  obtain ⟨C,hC,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt C hn'
  let x : V := Classical.arbitrary V
  let A := (finite_reachBall hloc x (n*k)).toFinset
  have hcard : (reachBall G x (n*k)).ncard = A.card := Set.ncard_eq_toFinset_card _ _
  have hsum : (A.card:ℝ)*(c/2)^k ≤ ∑ y ∈ A, twoPoint G p x y := by
    calc
      _ = ∑ y ∈ A, (c/2)^k := by simp
      _ ≤ _ := Finset.sum_le_sum fun y hy =>
        twoPoint_lower_on_multiples G p n (c/2) (by linarith) hball k x y
          (by simpa [A] using hy)
  have hg := reachBall_exponential_growth G hloc hh.le x (n*k)
  rw [hcard] at hg
  have hpow : ((c/2)*(1+hV G)^n)^k ≤ (A.card:ℝ)*(c/2)^k := by
    calc
      _ = (1+hV G)^(n*k)*(c/2)^k := by rw [mul_pow,pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hg (pow_nonneg (half_pos hc).le k)
  exact (not_lt_of_ge (hpow.trans (hsum.trans (hrow x A)))) hk

 

theorem not_unique_infinite_cluster_critical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) :
    law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} ≠ 1 := by
  intro hu
  have hp := pc_pos G hloc hqt
  have hpos : 0 < law (pc G) {ω | (infiniteClusters G ω).Nonempty} :=
    lt_of_lt_of_le (show 0 < law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} by
      rw [hu]; exact zero_lt_one)
      (measure_mono fun ω hω => ⟨hω.choose,hω.choose_spec.1⟩)
  obtain ⟨θ,hθ,hroot⟩ := uniform_survival_pos G hconn hqt (pc G) hp hpos
  have hue : ∀ᵐ ω ∂law (pc G), ∃! C, C ∈ infiniteClusters G ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_unique_infinite_cluster G)).mpr hu
  apply no_uniform_positive_twoPoint_critical G hloc hqt hh
  refine ⟨θ*θ,mul_pos hθ hθ,fun x y => ?_⟩
  refine (mul_le_mul (hroot x) (hroot y) hθ.le measureReal_nonneg).trans
    ((association_infinite_cluster G (pc G) x y).trans ?_)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hue] with ω hω
  intro hi
  obtain ⟨r,_,hconnr⟩ := (unique_infinite_cluster_iff G ω).mp hω
  exact conn_trans G ω (conn_symm G ω (hconnr x hi.1)) (hconnr y hi.2)

end Percolation

 

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_finite_of_transport [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1) :
    ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hw i)).le)
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  have hdn (x : V) := (incident_ncard_le_degree G hloc x).trans (hd x)
  let A : Set (Set E) := {ω | ∀ a b, Adj G a b →
    (cluster G ω a).Infinite → (cluster G ω b).Infinite → Conn G ω a b}
  have hA : MeasurableSet A := by
    simp only [A,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro _
    simp only [imp_iff_not_or,Set.ofPred_or]
    exact (measurableSet_infinite_cluster G a).compl.union
      ((measurableSet_infinite_cluster G b).compl.union (measurableSet_conn G a b))
  have hae : ∀ᵐ ω ∂law (pc G), ω ∈ A := by
    change ∀ᵐ ω ∂law (pc G), ∀ a b, Adj G a b →
      (cluster G ω a).Infinite → (cluster G ω b).Infinite → Conn G ω a b
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    rw [ae_all_iff]
    rintro ⟨e,he⟩
    exact critical_adjacent_infinite_connected G hconn hloc hqt root weight Γ hΓ htr hcov
      (fun i => (hw i).le) hw1 c hc hmin d hdn e a b he
  have haeF : ∀ᵐ ω ∂law (pc G), ∀ F : Finset E, ω ∪ (F:Set E) ∈ A := by
    rw [ae_all_iff]
    intro F
    exact ae_union_finset (pc G) (pc_pos G hloc hqt) A hA hae F
  have hat : ∀ᵐ ω ∂law (pc G), ∀ x y,
      (cluster G ω x).Infinite → (cluster G ω y).Infinite → Conn G ω x y := by
    filter_upwards [haeF] with ω hω
    exact atMostOne_of_finite_openings G hconn ω hω
  have hex := infinite_cluster_zero_one G (pc G)
  have he : (labelLaw : Measure (E → unitInterval))
      {labels | ∃ x, (cluster G (openEdges labels (pc G)) x).Infinite} =
      law (pc G) {ω | ∃ x, (cluster G ω x).Infinite} := by
    rw [←map_openEdges (pc G),Measure.map_apply (measurable_openEdges (pc G))
      (measurableSet_exists_infinite_cluster G)]
    rfl
  rw [he] at hex
  have hz : law (pc G) {ω | ∃ x, (cluster G ω x).Infinite} = 0 := by
    rcases hex with hzero | hone
    · exact hzero
    · exfalso
      apply not_unique_infinite_cluster_critical G hconn hloc hqt hh
      apply (mem_ae_iff_prob_eq_one (measurableSet_unique_infinite_cluster G)).mp
      have haex : ∀ᵐ ω ∂law (pc G), ∃ x, (cluster G ω x).Infinite :=
        (mem_ae_iff_prob_eq_one (measurableSet_exists_infinite_cluster G)).mpr hone
      filter_upwards [hat,haex] with ω hω hex
      obtain ⟨x,hx⟩ := hex
      exact (unique_infinite_cluster_iff G ω).mpr ⟨x,hx,fun y hy => hω x y hx hy⟩
  intro x
  rw [ae_iff]
  apply measure_mono_null (t := {ω | ∃ y, (cluster G ω y).Infinite}) ?_ hz
  intro ω hω
  exact ⟨x,hω⟩

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_Cayley
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

theorem cayleyBond_adj (S : Finset Λ) (x y : Λ) :
    Adj (cayleyBond S) x y ↔ (SimpleGraph.mulCayley (S : Set Λ)).Adj x y :=
  (SimpleGraph.adj_iff_exists_edge_coe).symm

theorem cayleyLeft_isAut (S : Finset Λ) (a : Λ) :
    IsAut (cayleyBond S) (Equiv.mulLeft a) (cayleyLeftIso S a).mapEdgeSet := by
  intro e
  rfl

theorem cayleyBond_quasiTransitive (S : Finset Λ) : QuasiTransitive (cayleyBond S) := by
  classical
  refine ⟨{1}, ?_⟩
  intro x
  exact ⟨1, by simp, Equiv.mulLeft x, (cayleyLeftIso S x).mapEdgeSet,
    cayleyLeft_isAut S x, mul_one x⟩

theorem cayleyBond_locallyFinite (S : Finset Λ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) : LocallyFinite (cayleyBond S) := by
  classical
  let H := SimpleGraph.mulCayley (S : Set Λ)
  intro x
  have hn : (H.neighborSet x).Finite := by
    apply (S.finite_toSet.image (fun s => x * s)).subset
    intro y hy
    obtain ⟨_, s, hs, h | h⟩ := (SimpleGraph.mulCayley_adj' (S : Set Λ) x y).mp hy
    · exact ⟨s, hs, h⟩
    · exact ⟨s⁻¹, hsym s hs, by simp only [h, mul_inv_cancel_right]⟩
  have hi : (H.incidenceSet x).Finite := by
    apply (hn.image (fun y => s(x, y))).subset
    intro e he
    exact ⟨H.otherVertexOfIncident he, H.incidence_other_prop he,
      Sym2.other_spec' he.2⟩
  apply Set.Finite.of_finite_image (f := fun e : CayleyEdge S => e.val)
  · apply hi.subset
    rintro e ⟨f, hf, rfl⟩
    exact ⟨f.property, hf⟩
  · exact Subtype.val_injective.injOn

theorem cayleyBond_connected (S : Finset Λ)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) : Connected (cayleyBond S) := by
  have htranslate (a : Λ) {x y : Λ}
      (h : Relation.ReflTransGen (Adj (cayleyBond S)) x y) :
      Relation.ReflTransGen (Adj (cayleyBond S)) (a * x) (a * y) := by
    induction h with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (adj_aut _ (cayleyLeft_isAut S a) h)
  have hreverse {x y : Λ} (h : Relation.ReflTransGen (Adj (cayleyBond S)) x y) :
      Relation.ReflTransGen (Adj (cayleyBond S)) y x := by
    induction h with
    | refl => exact .refl
    | tail _ h ih => exact (Relation.ReflTransGen.single (adj_symm _ h)).trans ih
  have hroot (y : Λ) : Relation.ReflTransGen (Adj (cayleyBond S)) 1 y := by
    have hy : y ∈ Subgroup.closure (S : Set Λ) := by rw [hgen]; trivial
    induction hy using Subgroup.closure_induction with
    | mem s hs =>
      by_cases h : (1 : Λ) = s
      · simpa only [← h] using (Relation.ReflTransGen.refl (a := (1 : Λ)))
      · exact .single ((cayleyBond_adj S 1 s).mpr
          ((SimpleGraph.mulCayley_adj' (S : Set Λ) 1 s).mpr
            ⟨h, s, hs, Or.inl (one_mul s)⟩))
    | one => exact .refl
    | mul a b _ _ ha hb => exact ha.trans (by simpa using htranslate a hb)
    | inv a _ ha => simpa using htranslate a⁻¹ (hreverse ha)
  intro x y
  simpa using htranslate x (hroot (x⁻¹ * y))

theorem folnerAmenable_of_finite [Finite Λ] : FolnerAmenable Λ := by
  classical
  let : Fintype Λ := Fintype.ofFinite Λ
  intro K ε hε
  refine ⟨Finset.univ, Finset.univ_nonempty, ?_⟩
  intro k _hk
  simpa using
    mul_pos hε (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card Λ))

theorem infinite_of_not_folnerAmenable (hna : ¬ FolnerAmenable Λ) : Infinite Λ := by
  by_contra h
  let : Finite Λ := not_infinite_iff_finite.mp h
  exact hna folnerAmenable_of_finite

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CayleyInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

theorem rightDefect_mul (A : Finset Λ) (a b : Λ) :
    rightDefect A (a * b) ≤ rightDefect A a + rightDefect A b := by
  have hsub : A.image (fun x => x * (a * b)) \ A ⊆
      ((A.image (fun x => x * a) \ A).image (fun x => x * b)) ∪
        (A.image (fun x => x * b) \ A) := by
    intro x hx
    obtain ⟨hx, hnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    by_cases hya : y * a ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_image.mpr ⟨y * a, hya, mul_assoc y a b⟩, hnot⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨y * a, Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩, hya⟩,
          mul_assoc y a b⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le) le_rfl))

theorem rightDefect_inv (A : Finset Λ) (a : Λ) : rightDefect A a⁻¹ = rightDefect A a := by
  have hinj : Function.Injective (fun x : Λ => x * a) := mul_left_injective a
  have himage : (A.image (fun x => x * a⁻¹) \ A).image (fun x => x * a) =
      A \ A.image (fun x => x * a) := by
    rw [Finset.image_sdiff _ _ hinj, Finset.image_image]
    simp only [Function.comp_def, inv_mul_cancel_right, Finset.image_id']
  calc
    rightDefect A a⁻¹ = ((A.image (fun x => x * a⁻¹) \ A).image (fun x => x * a)).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = (A \ A.image (fun x => x * a)).card := congrArg Finset.card himage
    _ = rightDefect A a := Finset.card_sdiff_comm
      (Finset.card_image_of_injective A hinj).symm

theorem rightDefect_generator (S A : Finset Λ) (s : Λ) (hs : s ∈ S)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) :
    rightDefect A s ≤ (vertexBoundary (cayleyBond S) A).ncard := by
  have hf := finite_vertexBoundary (cayleyBond S) (cayleyBond_locallyFinite S hsym) A
  change (A.image (fun x => x * s) \ A).card ≤ _
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ hf
  intro y hy
  obtain ⟨hy, hnot⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  refine ⟨hnot, x, hx, (cayleyBond_adj S x (x * s)).mpr ?_⟩
  apply (SimpleGraph.mulCayley_adj' (S : Set Λ) x (x * s)).mpr
  exact ⟨fun h => hnot (h ▸ hx), s, hs, Or.inl rfl⟩

theorem rightDefect_word_bound (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (g : Λ) :
    ∃ L : ℕ, ∀ A : Finset Λ,
      rightDefect A g ≤ L * (vertexBoundary (cayleyBond S) A).ncard := by
  have hg : g ∈ Subgroup.closure (S : Set Λ) := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, fun A => by simpa using rightDefect_generator S A s hs hsym⟩
  | one => exact ⟨0, fun A => by simp [rightDefect]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨La, ha⟩ := ha
    obtain ⟨Lb, hb⟩ := hb
    exact ⟨La + Lb, fun A => (rightDefect_mul A a b).trans
      (by simpa only [Nat.add_mul] using Nat.add_le_add (ha A) (hb A))⟩
  | inv a _ ha =>
    obtain ⟨L, ha⟩ := ha
    exact ⟨L, fun A => by rw [rightDefect_inv]; exact ha A⟩

theorem folnerAmenable_of_cayley_hV_nonpos (S : Finset Λ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤)
    (hh : hV (cayleyBond S) ≤ 0) : FolnerAmenable Λ := by
  intro K ε hε
  choose L hL using rightDefect_word_bound S hsym hgen
  let M : ℕ := (∑ k ∈ K, L k) + 1
  have hM : (0 : ℝ) < M := by dsimp [M]; positivity
  have hset : {r : ℝ | ∃ A : Finset Λ, A.Nonempty ∧
      r = (vertexBoundary (cayleyBond S) A).ncard / (A.card : ℝ)}.Nonempty :=
    ⟨_, {1}, by simp, rfl⟩
  obtain ⟨r, ⟨A, hA, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hset
    (hh.trans_lt (div_pos hε hM))
  have hcard : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hbound : (M : ℝ) * (vertexBoundary (cayleyBond S) A).ncard < ε * A.card := by
    have ht := (div_lt_iff₀ hcard).mp hr
    have hh' : ((vertexBoundary (cayleyBond S) A).ncard : ℝ) * M < ε * A.card :=
      (lt_div_iff₀ hM).mp (by simpa only [div_mul_eq_mul_div] using ht)
    calc
      (M : ℝ) * (vertexBoundary (cayleyBond S) A).ncard =
          (vertexBoundary (cayleyBond S) A).ncard * (M : ℝ) := mul_comm _ _
      _ < ε * A.card := hh'
  refine ⟨A, hA, ?_⟩
  intro k hk
  have hkM : L k ≤ M := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk).trans
    (Nat.le_add_right _ 1)
  have hd : rightDefect A k ≤ M * (vertexBoundary (cayleyBond S) A).ncard :=
    (hL k A).trans (Nat.mul_le_mul_right _ hkM)
  exact lt_of_le_of_lt (by exact_mod_cast hd) hbound

theorem cayleyFolnerInput_proved : CayleyFolnerInput Λ := by
  intro hna S hsym hgen
  by_contra hh
  exact hna (folnerAmenable_of_cayley_hV_nonpos S hsym hgen (le_of_not_gt hh))

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CayleyCritical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]

theorem cayleyRootTransport (S : Finset Λ) :
    RootTransport (fun _ : Unit => (1 : Λ)) (fun _ => (1 : ℝ))
      (vertexAut (cayleyBond S)) := by
  intro m hm _hrow _hcol
  simp only [Complex.ofReal_one, one_mul, Finset.univ_unique, Finset.sum_singleton]
  calc
    ∑' y, m 1 y = ∑' y, m y⁻¹ 1 := by
      apply tsum_congr
      intro y
      have h := hm (Equiv.mulLeft y⁻¹)
        ⟨(cayleyLeftIso S y⁻¹).mapEdgeSet, cayleyLeft_isAut S y⁻¹⟩ 1 y
      simpa using h.symm
    _ = ∑' x, m x 1 := (Equiv.inv Λ).tsum_eq (fun x => m x 1)

theorem cayleyRootCover (S : Finset Λ) :
    ∀ x : Λ, ∃ _i : Unit, ∃ a ∈ vertexAut (cayleyBond S), a 1 = x := by
  intro x
  exact ⟨(), Equiv.mulLeft x,
    ⟨(cayleyLeftIso S x).mapEdgeSet, cayleyLeft_isAut S x⟩, mul_one x⟩

theorem cayley_critical_bounded
    (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (_hone : 1 ∉ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (hna : ¬ FolnerAmenable Λ) :
    OperatorBounded (cayleyBond S) (pc (cayleyBond S)) := by
  classical
  let : Infinite Λ := infinite_of_not_folnerAmenable hna
  have hconn := cayleyBond_connected S hgen
  have hloc := cayleyBond_locallyFinite S hsym
  have hqt := cayleyBond_quasiTransitive S
  have hh := cayleyFolnerInput_proved hna S hsym hgen
  let : Countable Λ := countable_vertices hloc hconn
  let : Countable (CayleyEdge S) := countable_edges hloc
  have htr := cayleyRootTransport S
  have hcov := cayleyRootCover S
  have hw : ∀ _ : Unit, (0 : ℝ) < 1 := fun _ => zero_lt_one
  have hw1 : ∑ _ : Unit, (1 : ℝ) = 1 := by simp
  have hf := critical_finite_of_transport (cayleyBond S) hconn hloc hqt hh
    (fun _ : Unit => (1 : Λ)) (fun _ => (1 : ℝ))
    (vertexAut (cayleyBond S)) (Set.Subset.refl _) htr hcov hw hw1
  have hb := critical_bounded_of_transport_finiteness_bs (cayleyBond S)
    Subtype.val_injective hconn hloc hqt hh
    (fun _ : Unit => (1 : Λ)) (fun _ => (1 : ℝ)) htr hcov hw hw1 (fun _ => hf 1)
  exact hb

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)

theorem countable_vertices (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable V := by
  obtain ⟨o⟩ := hconnected.nonempty
  have hc : (⋃ n : ℕ, G.vertexBall o n).Countable :=
    Set.countable_iUnion fun n => (G.vertexBall_finite hlocal o n).countable
  have heq : (⋃ n : ℕ, G.vertexBall o n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n, hn⟩ := G.reachable_mem_vertexBall (hconnected o v)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

theorem countable_bonds (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable E := by
  let := G.countable_vertices hconnected hlocal
  have hc : (⋃ v : V, {e : E | v ∈ G.ends e}).Countable :=
    Set.countable_iUnion fun v => (hlocal v).countable
  have heq : (⋃ v : V, {e : E | v ∈ G.ends e}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    exact Set.mem_iUnion.mpr ⟨(G.ends e).out.1, Sym2.out_fst_mem _⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

lemma measurable_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact Measurable.of_eval fun vertex => G.measurable_reachable v vertex

lemma measurable_infinite_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => (G.cluster ω v).Infinite) := by
  simp_rw [← Set.encard_eq_top_iff]
  exact (measurable_encard.comp (G.measurable_cluster v)).eq_const ⊤

lemma mem_cluster_finite_witness {ω : Set E} {v w : V} (h : w ∈ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v := by
  classical
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp h
  clear h
  induction hr with
  | refl => exact ⟨∅, Set.finite_empty, Set.empty_subset _, .refl _⟩
  | @tail u w hr huw ih =>
      obtain ⟨s, hs, hsω, hvs⟩ := ih
      obtain ⟨⟨e, heω, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      refine ⟨insert e s, hs.insert e, Set.insert_subset heω hsω, ?_⟩
      have hvu : (G.openGraph (insert e s)).Reachable v u :=
        hvs.mono (G.openGraph_mono (Set.subset_insert _ _))
      apply hvu.trans
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, Set.mem_insert _ _, heq⟩, hne⟩

lemma finite_subset_cluster_finite_witness {ω : Set E} {v : V} {K : Set V}
    (hK : K.Finite) (hKv : K ⊆ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ K ⊆ G.cluster s v := by
  classical
  have h : ∀ w ∈ K, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v :=
    fun w hw => G.mem_cluster_finite_witness (hKv hw)
  choose s hs hsω hws using h
  let := hK.fintype
  refine ⟨⋃ w : K, s w w.property, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun w => hs w w.property
  · exact Set.iUnion_subset fun w => hsω w w.property
  · intro w hw
    exact G.cluster_mono (Set.subset_iUnion (fun w : K => s w w.property) ⟨w, hw⟩)
      v (hws w hw)

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BernoulliProduct

lemma bitMeasure_real_singleton (p : unitInterval) (b : Prop) :
    (bitMeasure p).real {b} = bitWeight p b := by
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]

variable {E : Type*}

lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_image_equiv (e : E ≃ E) :
    Measurable (fun ω : Set E => e '' ω) := by
  have he : (fun ω : Set E => e '' ω) = (fun ω => e.symm ⁻¹' ω) := by
    funext ω
    ext i
    simp
  rw [he]
  exact Measurable.of_eval (fun index => measurable_set_mem (e.symm index))

lemma law_map_equiv (p : unitInterval) (e : E ≃ E) :
    (law (fun _ : E => p)).map (fun ω : Set E => e '' ω) = law (fun _ : E => p) := by
  unfold law
  rw [Measure.map_map (measurable_image_equiv e) MeasurableEquiv.setOfPred.measurable]
  have he : (fun ω : Set E => e '' ω) ∘ MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ MeasurableEquiv.piCongrLeft (fun _ : E => Prop) e := by
    funext ω
    ext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_piCongrLeft (fun _ : E => bitMeasure p) e]

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.cluster_image (φ : G.Aut) (ω : Set E) (o : V) :
    φ.vertex '' G.cluster ω o = G.cluster (φ.edge '' ω) (φ.vertex o) := by
  ext v
  obtain ⟨w, rfl⟩ := φ.vertex.surjective v
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]
  change (G.openGraph ω).Reachable o w ↔
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex o) (φ.vertex w)
  exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := o) (v := w)).symm

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphBalls
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.vertexBall_image (φ : G.Aut) (o : V) (n : ℕ) :
    φ.vertex '' G.vertexBall o n = G.vertexBall (φ.vertex o) n := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using
    (Aut.vertexBall_mem G φ o w n).symm

lemma orbit_density_radius (hconnected : G.fullGraph.Connected)
    (hquasi : G.QuasiTransitive) (u : V) :
    ∃ C : ℕ, ∀ v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  have hpath : ∀ z : S, ∃ n, u ∈ G.vertexBall z.val n :=
    fun z => G.reachable_mem_vertexBall (hconnected z u)
  choose n hn using hpath
  let := hS.fintype
  let C := ∑ z : S, n z
  refine ⟨C,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  refine ⟨φ,(Aut.vertexBall_mem G φ z u C).mpr ?_⟩
  exact G.vertexBall_mono z (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨z,hz⟩ : S))) (hn ⟨z,hz⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BallIncidence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.inducedEdges_map (φ : G.Aut) {K : Set E} {S : Set V}
    (hKS : K⊆G.inducedEdges S) : φ.edge '' K ⊆ G.inducedEdges (φ.vertex '' S) := by
  rintro e ⟨a,ha,rfl⟩ v hv
  rw [φ.preserves] at hv
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨w,hKS ha w hw,rfl⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_InfiniteUniquenessGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_distinctInfiniteEvent [Countable V] [Countable E] (x y : V) :
    MeasurableSet (G.distinctInfiniteEvent x y) :=
  ((G.measurable_infinite_cluster x).and
    ((G.measurable_infinite_cluster y).and (G.measurable_reachable x y).not)).setOf

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_TailProduct
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_eq_infinitePi (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id

lemma independent_coordinates (q : E → unitInterval) :
    iIndep coordinateSigma (law q) := by
  rw [law_eq_infinitePi]
  exact iIndepFun_infinitePi (X := fun _ (b : Prop) => b) (fun _ => measurable_id)

lemma independent_blocks (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl coordinateSigma_le (independent_coordinates q) S

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_PercolationTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_union_subset (ω S : Set E) (o : V) :
    G.cluster (ω ∪ S) o ⊆ G.cluster ω o ∪
      ⋃ e ∈ S, ⋃ v ∈ (G.ends e).toFinset, G.cluster ω v := by
  intro z hz
  have hr := ((G.openGraph (ω ∪ S)).reachable_iff_reflTransGen o z).mp hz
  clear hz
  induction hr with
  | refl => exact Or.inl (.refl _)
  | @tail x y hr hxy ih =>
    obtain ⟨⟨e, he, heq⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    rcases he with he | he
    · have hadj : (G.openGraph ω).Adj x y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩
      rcases ih with ho | h
      · exact Or.inl (ho.trans hadj.reachable)
      · obtain ⟨f,hf,h⟩ := Set.mem_iUnion₂.mp h
        obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp h
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,Set.mem_iUnion₂.mpr
          ⟨v,hv,hh.trans hadj.reachable⟩⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr
        ⟨y,by simp [heq], .refl _⟩⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteEnergy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_coordinate (q : E → unitInterval) (e : E) (b : Prop) :
    law q {ω : Set E | (e ∈ ω) = b} = bitMeasure (q e) {b} := by
  rw [law_eq_infinitePi]
  have h := congrArg (fun μ : Measure Prop => μ {b})
    (Measure.infinitePi_map_eval (fun e => bitMeasure (q e)) e)
  rw [Measure.map_apply (measurable_pi_apply e) (MeasurableSet.singleton b)] at h
  exact h

lemma force_singleton_preimage_null (q : E → unitInterval) (e : E) (σ : Set E)
    (hb : bitMeasure (q e) {e ∈ σ} ≠ 0)
    (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q (forceOn {e} σ ⁻¹' A) = 0 := by
  let B := forceOn {e} σ ⁻¹' A
  let C := {ω : Set E | (e ∈ ω) = (e ∈ σ)}
  have hmC : MeasurableSet[blockSigma {e}] C := by
    have hc : MeasurableSet[coordinateSigma e] C :=
      ⟨{e ∈ σ}, MeasurableSet.singleton _, rfl⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Set.mem_singleton e) le_rfl) :
      coordinateSigma e ≤ blockSigma {e}) _ hc
  have hmB : MeasurableSet[blockSigma ({e} : Set E)ᶜ] B :=
    hA.preimage (measurable_forceOn_block {e} σ)
  have hmul := ((independent_blocks q {e}).indepSet_of_measurableSet hmC hmB).measure_inter_eq_mul
  have hsub : C ∩ B ⊆ A := by
    intro ω hω
    have heq : forceOn {e} σ ω = ω := by
      ext f
      change (if f ∈ ({e} : Set E) then f ∈ σ else f ∈ ω) ↔ f ∈ ω
      by_cases hf : f = e
      · subst f
        simpa only [Set.mem_singleton_iff, ↓reduceIte] using (Iff.of_eq hω.1.symm)
      · simp only [Set.mem_singleton_iff, ite_eq_right hf]
    have hh : forceOn {e} σ ω ∈ A := hω.2
    rwa [heq] at hh
  have hz : law q (C ∩ B) = 0 := measure_mono_null hsub hnull
  rw [hz, law_coordinate] at hmul
  exact (mul_eq_zero.mp hmul.symm).resolve_left hb

lemma bitMeasure_true_ne_zero (p : unitInterval) (hp : (0:ℝ) < p) :
    bitMeasure p {True} ≠ 0 := by
  have hh := bitMeasure_real_singleton p True
  simp only [bitWeight, if_true] at hh
  intro hz
  have : (bitMeasure p).real {True} = 0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  rw [hh] at this
  exact (ne_of_gt hp) this

lemma insert_preimage_null (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (e : E) (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q ((fun ω => insert e ω) ⁻¹' A) = 0 := by
  have hh := force_singleton_preimage_null q e Set.univ (bitMeasure_true_ne_zero (q e) (hq e))
    A hA hnull
  have heq : forceOn {e} Set.univ = (fun ω : Set E => insert e ω) := by
    funext ω
    ext f
    change (if f ∈ ({e} : Set E) then True else f ∈ ω) ↔ (f = e ∨ f ∈ ω)
    simp only [Set.mem_singleton_iff]
    split_ifs <;> tauto
  rwa [heq] at hh

lemma measurable_union_left (S : Set E) : Measurable (fun ω : Set E => S ∪ ω) :=
  Measurable.of_eval (fun edge => measurable_const.or (measurable_set_mem edge))

lemma finite_union_preimage_null (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (S : Set E) (hS : S.Finite) (A : Set (Set E)) (hA : MeasurableSet A)
    (hnull : law q A = 0) : law q ((fun ω => S ∪ ω) ⁻¹' A) = 0 := by
  induction S,hS using Set.Finite.induction_on generalizing A with
  | empty =>
    have hh : (fun ω : Set E => (∅ : Set E) ∪ ω) = id := funext (fun _ => Set.empty_union _)
    rw [hh,Set.preimage_id_eq]
    exact hnull
  | @insert e S he hS ih =>
    have hi := insert_preimage_null q hq e A hA hnull
    have hm : Measurable (fun ω : Set E => insert e ω) := by
      simpa only [Set.singleton_union] using measurable_union_left ({e} : Set E)
    have hh := ih ((fun ω => insert e ω) ⁻¹' A) (hA.preimage hm) hi
    simpa only [Set.preimage_preimage,Function.comp_def,Set.insert_union] using hh

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_InfiniteUniqueness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurableSet_atMostOneInfinite : MeasurableSet G.atMostOneInfinite := by
  have heq : G.atMostOneInfinite = ⋂ x, ⋂ y, (G.distinctInfiniteEvent x y)ᶜ := by
    ext ω
    simp only [atMostOneInfinite,distinctInfiniteEvent,Set.mem_ofPred_eq,Set.mem_iInter,
      Set.mem_compl_iff]
    constructor
    · intro h x y hh
      exact hh.2.2 (h x y hh.1 hh.2.1)
    · intro h x y hx hy
      by_contra hr
      exact h x y ⟨hx,hy,hr⟩
  rw [heq]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
    (G.measurableSet_distinctInfiniteEvent x y).compl

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_FiniteClusterCover
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infinite_cluster_union_has_old (ω J : Set E) (hJ : J.Finite) (o : V)
    (ho : (G.cluster (ω ∪ J) o).Infinite) :
    ∃ v, (G.openGraph (ω ∪ J)).Reachable o v ∧ (G.cluster ω v).Infinite := by
  by_contra h
  have hf (v : V) (hv : (G.openGraph (ω ∪ J)).Reachable o v) :
      (G.cluster ω v).Finite := by
    apply Set.not_infinite.mp
    intro hi
    exact h ⟨v,hv,hi⟩
  have hσ (v : V) : (G.cluster ω v ∩ G.cluster (ω ∪ J) o).Finite := by
    by_cases hv : (G.openGraph (ω ∪ J)).Reachable o v
    · exact (hf v hv).inter_of_left _
    · have he : G.cluster ω v ∩ G.cluster (ω ∪ J) o = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx,hox⟩
        exact hv (hox.trans (G.cluster_mono Set.subset_union_left v hx).symm)
      rw [he]
      exact Set.finite_empty
  apply ho
  apply ((hf o (.refl _)).union (hJ.biUnion fun e _ =>
      (G.ends e).toFinset.finite_toSet.biUnion fun v _ => hσ v)).subset
  intro z hz
  rcases G.cluster_union_subset ω J o hz with hh | hh
  · exact Or.inl hh
  · obtain ⟨e,he,hh⟩ := Set.mem_iUnion₂.mp hh
    obtain ⟨v,hv,hvz⟩ := Set.mem_iUnion₂.mp hh
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr ⟨v,hv,hvz,hz⟩⟩)

lemma finite_bonds_connect_set (hc : G.fullGraph.Connected) (o : V)
    (S : Set V) (hS : S.Finite) :
    ∃ J : Set E, J.Finite ∧ ∀ s ∈ S, (G.openGraph J).Reachable o s := by
  obtain ⟨J,hJ,_,hconn⟩ := G.finite_subset_cluster_finite_witness hS
    (show S ⊆ G.cluster Set.univ o from fun s _ => hc o s)
  exact ⟨J,hJ,fun s hs => hconn hs⟩

lemma atMostOneInfinite_union_of_cover (ω J : Set E) (hJ : J.Finite)
    (o : V) (S : Set V) (hconn : ∀ s ∈ S, (G.openGraph J).Reachable o s)
    (hcover : G.infiniteClusterCover ω S) : ω ∪ J ∈ G.atMostOneInfinite := by
  have hroot (x : V) (hx : (G.cluster (ω ∪ J) x).Infinite) :
      (G.openGraph (ω ∪ J)).Reachable x o := by
    obtain ⟨v,hxv,hv⟩ := G.infinite_cluster_union_has_old ω J hJ x hx
    obtain ⟨s,hs,hvs⟩ := hcover v hv
    exact hxv.trans ((G.cluster_mono Set.subset_union_left v hvs).trans
      (G.cluster_mono Set.subset_union_right o (hconn s hs)).symm)
  intro x y hx hy
  exact (hroot x hx).trans (hroot y hy).symm

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_OpenTrialBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexBalls_disjoint {v w : V} {n : ℕ} (h : w∉G.vertexBall v (n+n)) :
    Disjoint (G.vertexBall v n) (G.vertexBall w n) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact h (G.vertexBall_add hz n (G.vertexBall_comm.mp hz'))

lemma inducedEdges_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (G.inducedEdges S) (G.inducedEdges T) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
  have hx : x∈G.ends e := by rw [← hxy]; simp
  exact Set.disjoint_left.mp h (he x hx) (he' x hx)

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_AutDisplacement
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma aut_moves_vertex_outside_ball [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (R : ℕ) :
    ∃ φ : G.Aut, φ.vertex o ∉ G.vertexBall o R := by
  obtain ⟨C,hC⟩ := G.orbit_density_radius hc hq o
  obtain ⟨v,hv⟩ := (G.vertexBall_finite hl o (R+C)).exists_notMem
  obtain ⟨φ,hφ⟩ := hC v
  refine ⟨φ,fun h => hv ?_⟩
  exact G.vertexBall_add h C (G.vertexBall_comm.mp hφ)

lemma aut_displaces_finite_bonds [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (S : Set E) (hS : S.Finite) :
    ∃ φ : G.Aut, Disjoint S (φ.edge '' S) := by
  obtain ⟨o⟩ := hc.nonempty
  obtain ⟨R,hR⟩ := G.finite_bonds_in_ball hc o hS
  obtain ⟨φ,hφ⟩ := G.aut_moves_vertex_outside_ball hc hl hq o (R+R)
  refine ⟨φ,(G.inducedEdges_disjoint (G.vertexBalls_disjoint hφ)).mono hR ?_⟩
  have hm := Aut.inducedEdges_map G φ hR
  rwa [Aut.vertexBall_image] at hm

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BlockIndependence
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma blockSigma_mono {S T : Set E} (h : S ⊆ T) : blockSigma S ≤ blockSigma T := by
  apply iSup₂_le
  intro e he
  exact le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)

lemma independent_disjoint_blocks (q : E → unitInterval) (S T : Set E)
    (h : Disjoint S T) : Indep (blockSigma S) (blockSigma T) (law q) :=
  indep_iSup_of_disjoint coordinateSigma_le (independent_coordinates q) h

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_CylinderApproximation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma finiteCoordinateEvents_ring : IsSetRing (finiteCoordinateEvents (E := E)) where
  empty_mem := ⟨∅,@MeasurableSet.empty (Set E) (blockSigma ((∅ : Finset E) : Set E))⟩
  union_mem := by
    rintro A B ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,?_⟩
    exact @MeasurableSet.union (Set E) (blockSigma ((S ∪ T : Finset E) : Set E)) _ _
      (blockSigma_mono (by simp) _ hS) (blockSigma_mono (by simp) _ hT)
  sdiff_mem := by
    rintro A B ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,?_⟩
    exact @MeasurableSet.diff (Set E) (blockSigma ((S ∪ T : Finset E) : Set E)) _ _
      (blockSigma_mono (by simp) _ hS) (blockSigma_mono (by simp) _ hT)

lemma generateFrom_finiteCoordinateEvents :
    MeasurableSpace.generateFrom (finiteCoordinateEvents (E := E)) =
      (Set.instMeasurableSpace : MeasurableSpace (Set E)) := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun A ⟨S,hS⟩ => blockSigma_le _ _ hS
  · change (⨆ e : E, coordinateSigma e) ≤ _
    refine iSup_le fun e => ?_
    intro A hA
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{e},?_⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Finset.mem_singleton_self e) le_rfl) :
      coordinateSigma e ≤ blockSigma (({e} : Finset E) : Set E)) _ hA

lemma exists_finiteCoordinate_approx (q : E → unitInterval)
    {A : Set (Set E)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (S : Finset E) (B : Set (Set E)), MeasurableSet[blockSigma (S : Set E)] B ∧
      law q (B ∆ A) < ε := by
  obtain ⟨B,⟨S,hB⟩,h⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    finiteCoordinateEvents_ring (μ := law q)
    (show ∃ D : Set (Set (Set E)), D.Countable ∧ D ⊆ finiteCoordinateEvents ∧
        law q (⋃₀ D)ᶜ = 0 from
      ⟨{Set.univ},by simp,by rintro A rfl; exact ⟨∅,@MeasurableSet.univ (Set E) (blockSigma ((∅ : Finset E) : Set E))⟩,by simp⟩)
    generateFrom_finiteCoordinateEvents.symm hA hε
  exact ⟨S,B,hB,h⟩

lemma measurable_image_equiv_blocks (e : E ≃ E) (S : Set E) :
    @Measurable (Set E) (Set E) (blockSigma (e.symm '' S)) (blockSigma S)
      (fun ω => e '' ω) := by
  apply measurable_iff_comap_le.mpr
  simp only [blockSigma, MeasurableSpace.comap_iSup]
  refine iSup₂_le fun x hx => ?_
  have hm : @Measurable (Set E) Prop (coordinateSigma (e.symm x)) inferInstance
      (fun ω => x ∈ e '' ω) := by
    have hh : (fun ω : Set E => x ∈ e '' ω) = (fun ω => e.symm x ∈ ω) := by
      funext ω
      exact propext (by simp)
    rw [hh]
    exact measurable_iff_comap_le.mpr le_rfl
  have hc := hm.comap_le
  rw [coordinateSigma,MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun ω : Set E => x ∈ e '' ω) inferInstance ≤ _
  exact hc.trans (le_iSup_of_le (e.symm x) (le_iSup_of_le ⟨x,hx,rfl⟩ le_rfl))

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BernoulliErgodicity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma invariant_zero_one (p : unitInterval) (ρ : I → E ≃ E)
    (hdisp : ∀ S : Finset E, ∃ i, Disjoint (S : Set E) ((ρ i).symm '' (S : Set E)))
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinv : ∀ i, (fun ω : Set E => ρ i '' ω) ⁻¹' A = A) :
    law (fun _ : E => p) A = 0 ∨ law (fun _ : E => p) A = 1 := by
  let μ := law (fun _ : E => p)
  have hsq : μ.real A ≤ (μ.real A)^2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hδ : 0 < ε/4 := by positivity
    obtain ⟨S,B,hB,happrox⟩ := exists_finiteCoordinate_approx (fun _ : E => p) hA
      (ENNReal.ofReal_pos.mpr hδ)
    have hBm : MeasurableSet B := blockSigma_le _ _ hB
    obtain ⟨i,hi⟩ := hdisp S
    let f : Set E → Set E := fun ω => ρ i '' ω
    let C := f ⁻¹' B
    have hf : Measurable f := measurable_image_equiv (ρ i)
    have hC : MeasurableSet[blockSigma ((ρ i).symm '' (S : Set E))] C :=
      (measurable_image_equiv_blocks (ρ i) (S : Set E)) hB
    have hCm : MeasurableSet C := hBm.preimage hf
    have hind : IndepSet B C μ :=
      (independent_disjoint_blocks (fun _ => p) (S : Set E) _ hi).indepSet_of_measurableSet hB hC
    have hpres (D : Set (Set E)) (hD : MeasurableSet D) : μ.real (f ⁻¹' D) = μ.real D := by
      change (μ (f ⁻¹' D)).toReal = (μ D).toReal
      rw [← Measure.map_apply hf hD]
      change ((law (fun _ : E => p)).map (fun ω => ρ i '' ω) D).toReal = _
      rw [law_map_equiv]
    have hCeq : μ.real C = μ.real B := hpres B hBm
    have hAB : μ.real (B ∆ A) ≤ ε/4 := by
      apply le_of_lt
      have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr happrox
      change (μ (B ∆ A)).toReal < ε/4
      rwa [ENNReal.toReal_ofReal hδ.le] at hh
    have hAC : μ.real (C ∆ A) ≤ ε/4 := by
      have he : C ∆ A = f ⁻¹' (B ∆ A) := by
        rw [Set.preimage_symmDiff,hinv]
      rw [he,hpres _ (hBm.symmDiff hA)]
      exact hAB
    have hcover : A ⊆ (B ∩ C) ∪ ((B ∆ A) ∪ (C ∆ A)) := by
      intro ω hω
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_symmDiff]
      tauto
    have hinter : μ.real (B ∩ C) = (μ.real B)^2 := by
      rw [measureReal_def,hind.measure_inter_eq_mul,ENNReal.toReal_mul]
      change μ.real B * μ.real C = _
      rw [hCeq,pow_two]
    have hbound : μ.real A ≤ (μ.real B)^2 + ε/2 := by
      have hh := (measureReal_mono hcover (μ := μ)).trans
        (measureReal_union_le (B ∩ C) ((B ∆ A) ∪ (C ∆ A)))
      have hu := measureReal_union_le (B ∆ A) (C ∆ A) (μ := μ)
      rw [hinter] at hh
      linarith
    have hdif : μ.real B - μ.real A ≤ ε/4 :=
      (le_abs_self _).trans ((abs_measureReal_sub_le_measureReal_symmDiff
        hBm.nullMeasurableSet hA.nullMeasurableSet).trans hAB)
    have hfac : (μ.real B - μ.real A)*(μ.real A + μ.real B) ≤ (ε/4)*2 := by
      apply (mul_le_mul_of_nonneg_right hdif (add_nonneg measureReal_nonneg measureReal_nonneg)).trans
      exact mul_le_mul_of_nonneg_left (by
        have ha := measureReal_le_one (μ := μ) (s := A)
        have hb := measureReal_le_one (μ := μ) (s := B)
        linarith) hδ.le
    nlinarith only [hbound,hfac]
  have ha0 : 0 ≤ μ.real A := measureReal_nonneg
  have ha1 : μ.real A ≤ 1 := measureReal_le_one
  have heq : μ.real A = 0 ∨ μ.real A = 1 := by
    have h : μ.real A * (μ.real A - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases heq with h | h
  · left
    exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (measure_ne_top μ A)
  · right
    exact (ENNReal.toReal_eq_one_iff _).mp h

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_GraphErgodicity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem invariant_event_zero_one [Infinite V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (p : unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinv : ∀ φ : G.Aut, (fun ω : Set E => φ.edge '' ω) ⁻¹' A = A) :
    G.law p A = 0 ∨ G.law p A = 1 := by
  have hh := BernoulliProduct.invariant_zero_one p (fun φ : G.Aut => (Aut.symm G φ).edge)
    (fun S => by
      obtain ⟨φ,hφ⟩ := G.aut_displaces_finite_bonds hc hl hq (S : Set E) S.finite_toSet
      exact ⟨φ,hφ⟩) A hA (fun φ => hinv (Aut.symm G φ))
  simpa only [BernoulliProduct.law_const,law] using hh

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterNumber
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.atMostOneInfinite_image_iff (φ : G.Aut) (ω : Set E) :
    φ.edge '' ω ∈ G.atMostOneInfinite ↔ ω ∈ G.atMostOneInfinite := by
  have hi (x : V) : (G.cluster (φ.edge '' ω) (φ.vertex x)).Infinite ↔
      (G.cluster ω x).Infinite := by
    rw [←φ.cluster_image]
    exact Set.infinite_image_iff φ.vertex.injective.injOn
  have hr (x y : V) := SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)
    (u := x) (v := y)
  constructor
  · intro h x y hx hy
    exact (hr x y).mp (h (φ.vertex x) (φ.vertex y) ((hi x).mpr hx) ((hi y).mpr hy))
  · intro h x y hx hy
    obtain ⟨a,rfl⟩ := φ.vertex.surjective x
    obtain ⟨b,rfl⟩ := φ.vertex.surjective y
    exact (hr a b).mpr (h a b ((hi a).mp hx) ((hi b).mp hy))

lemma atMostOneInfinite_zero_one [Infinite V] [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) : G.law p G.atMostOneInfinite = 0 ∨
      G.law p G.atMostOneInfinite = 1 :=
  G.invariant_event_zero_one hc hl hq p G.atMostOneInfinite G.measurableSet_atMostOneInfinite
    (fun φ => Set.ext fun ω => Aut.atMostOneInfinite_image_iff G φ ω)

lemma no_finite_infiniteClusterCover_ae_of_unique_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : (0:ℝ) < p)
    (hnull : G.law p G.atMostOneInfinite = 0) :
    ∀ᵐ ω ∂G.law p, ∀ S : Finset V, ¬ G.infiniteClusterCover ω (S : Set V) := by
  apply ae_all_iff.mpr
  intro S
  obtain ⟨o⟩ := hc.nonempty
  obtain ⟨J,hJ,hconn⟩ := G.finite_bonds_connect_set hc o (S : Set V) S.finite_toSet
  have hn := BernoulliProduct.finite_union_preimage_null (fun _ : E => p) (fun _ => hp)
    J hJ G.atMostOneInfinite G.measurableSet_atMostOneInfinite
    (by simpa only [BernoulliProduct.law_const,law] using hnull)
  have hn' : G.law p ((fun ω : Set E => J ∪ ω) ⁻¹' G.atMostOneInfinite) = 0 := by
    simpa only [BernoulliProduct.law_const,law] using hn
  rw [ae_iff]
  apply measure_mono_null _ hn'
  intro ω hω
  change J ∪ ω ∈ G.atMostOneInfinite
  rw [Set.union_comm]
  exact G.atMostOneInfinite_union_of_cover ω J hJ o (S : Set V) hconn (not_not.mp hω)

lemma infinitelyManyInfiniteClusters_iff_no_finite_cover (ω : Set E) :
    G.infinitelyManyInfiniteClusters ω ↔
      ∀ S : Finset V, ¬ G.infiniteClusterCover ω (S : Set V) := by
  simp only [infinitelyManyInfiniteClusters,infiniteClusterCover]
  push Not
  rfl

theorem unique_or_infinitely_many_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : (0:ℝ) < p) :
    (∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite) ∨
    (∀ᵐ ω ∂G.law p, G.infinitelyManyInfiniteClusters ω) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  rcases G.atMostOneInfinite_zero_one hc hl hq p with hz | ho
  · right
    filter_upwards [G.no_finite_infiniteClusterCover_ae_of_unique_null hc p hp hz] with ω hω
    exact (G.infinitelyManyInfiniteClusters_iff_no_finite_cover ω).mpr hω
  · left
    rw [ae_iff]
    change G.law p G.atMostOneInfiniteᶜ = 0
    rw [measure_compl G.measurableSet_atMostOneInfinite (measure_ne_top _ _),ho,
      measure_univ,tsub_self]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PhaseInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_openGraph (G : BondGraph V E) (ω : Set E) :
    (criticalModel G).openGraph ω = openSimpleGraph G ω := by
  ext x y
  simp only [CriticalPercolation.BondGraph.openGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_image, openSimpleGraph, criticalModel]
  tauto

theorem criticalModel_cluster (G : BondGraph V E) (ω : Set E) (x : V) :
    (criticalModel G).cluster ω x = cluster G ω x := by
  ext y
  simp only [CriticalPercolation.BondGraph.cluster, criticalModel_openGraph,
    Set.mem_ofPred_eq, cluster]
  exact (conn_iff_reachable G ω x y).symm

theorem criticalModel_connected [Nonempty V] (G : BondGraph V E) (hconn : Connected G) :
    (criticalModel G).fullGraph.Connected := by
  rw [CriticalPercolation.BondGraph.fullGraph, criticalModel_openGraph]
  exact ⟨fun x y => (conn_iff_reachable G Set.univ x y).mp (conn_univ_of_connected G hconn x y)⟩

theorem ae_exists_infinite_cluster_law [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : pc G < p) :
    ∀ᵐ ω ∂law p, ∃ x, (cluster G ω x).Infinite := by
  have h := ae_exists_infinite_cluster_of_pc_lt G p hp
  rw [ae_iff] at h ⊢
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p)
    (show MeasurableSet {ω : Set E | ¬ ∃ x, (cluster G ω x).Infinite} from
      (measurableSet_exists_infinite_cluster G).compl)]
  exact h

theorem infiniteClusters_infinite_of_criticalModel (G : BondGraph V E) (ω : Set E)
    (h : (criticalModel G).infinitelyManyInfiniteClusters ω) :
    (infiniteClusters G ω).Infinite := by
  classical
  intro hf
  let C := infiniteClusters G ω
  let : Fintype C := hf.fintype
  let root : C → V := fun c => Classical.choose c.property.2
  let S : Finset V := Finset.univ.image root
  obtain ⟨v, hv, havoid⟩ := h S
  rw [criticalModel_cluster] at hv
  let c : C := ⟨cluster G ω v, hv, v, rfl⟩
  have hc : cluster G ω v = cluster G ω (root c) := Classical.choose_spec c.property.2
  have hr : root c ∈ S := Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
  apply havoid (root c) hr
  rw [criticalModel_openGraph]
  apply (conn_iff_reachable G ω v (root c)).mp
  change root c ∈ cluster G ω v
  rw [hc]
  exact mem_cluster_self G ω (root c)

theorem publishedPhaseInput_proved [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) : PublishedPhaseInput G := by
  classical
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  intro p hp hpu
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (pc G).2.1 hp
  have hc := criticalModel_connected G hconn
  have hq := criticalModel_quasiTransitive G hqt
  rcases (criticalModel G).unique_or_infinitely_many_ae hc hloc hq p hp0 with hu | hi
  · have hex := ae_exists_infinite_cluster_law G p hp
    have hunique : ∀ᵐ ω ∂law p, ∃! C, C ∈ infiniteClusters G ω := by
      filter_upwards [hu, hex] with ω hω hωinf
      obtain ⟨x, hx⟩ := hωinf
      refine ⟨cluster G ω x, ⟨hx, x, rfl⟩, ?_⟩
      rintro C ⟨hC, y, rfl⟩
      apply cluster_eq_of_conn G ω
      apply (conn_iff_reachable G ω y x).mpr
      rw [← criticalModel_openGraph]
      apply hω y x
      · rwa [criticalModel_cluster]
      · rwa [criticalModel_cluster]
    have hprob : law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1 := by
      calc
        _ = (law p : Measure (Set E)) Set.univ := by
          apply measure_congr
          filter_upwards [hunique] with ω hω
          exact propext (iff_true_intro hω)
        _ = 1 := measure_univ
    exact False.elim (not_le_of_gt hpu (sInf_le hprob))
  · exact hi.mono (fun ω hω => infiniteClusters_infinite_of_criticalModel G ω hω)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CayleyTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]

theorem cayley_main_oai
    (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (_hone : 1 ∉ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (hna : ¬ FolnerAmenable Λ) :
    OperatorBounded (cayleyBond S) (pc (cayleyBond S)) ∧
      MainConclusion (cayleyBond S) ∧
      ∀ p : unitInterval, pc (cayleyBond S) < p → p < pu (cayleyBond S) →
        ∀ᵐ ω ∂law p, (infiniteClusters (cayleyBond S) ω).Infinite := by
  let : Infinite Λ := infinite_of_not_folnerAmenable hna
  have hconn := cayleyBond_connected S hgen
  have hloc := cayleyBond_locallyFinite S hsym
  have hqt := cayleyBond_quasiTransitive S
  have hb := cayley_critical_bounded S hsym _hone hgen hna
  exact ⟨hb, mainConclusion_of_critical_bounded (cayleyBond S) hconn hloc hqt hb,
    publishedPhaseInput_proved (cayleyBond S) hconn hloc hqt⟩

end Percolation.BenjaminiSchramm

end OAI
end

theorem solution.{u} : type_of% @OAI.Percolation.BenjaminiSchramm.cayley_main_oai.{u} := @OAI.Percolation.BenjaminiSchramm.cayley_main_oai.{u}
