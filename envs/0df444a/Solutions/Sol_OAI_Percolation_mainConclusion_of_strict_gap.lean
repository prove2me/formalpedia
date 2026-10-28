-- Prove2me | solution 1 for OAI.Percolation.mainConclusion_of_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T00:52:51.871969+00:00
-- url     : https://prove2.me/submissions/a72a4c96-0ea9-4b19-b35d-185c731e7bb5

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


theorem exists_mem_reachBall {G : BondGraph V E} {x y : V}
    (h : Relation.ReflTransGen (Adj G) x y) : ∃ n, y ∈ reachBall G x n := by
  induction h with
  | refl => exact ⟨0, Set.mem_singleton _⟩
  | @tail y z _ hyz ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, Or.inr ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨y, hn, hyz⟩

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
    · simp only [S, Set.indicator, Set.mem_ofPred_eq, hc, false_and, ite_false,
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

 

theorem mainConclusion_of_strict_gap_oai [Infinite V] (G : BondGraph V E)
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

theorem solution.{u, v} : type_of% @OAI.Percolation.mainConclusion_of_strict_gap_oai.{u, v} := @OAI.Percolation.mainConclusion_of_strict_gap_oai.{u, v}
