-- Prove2me | solution 1 for JHolomorphic.exists_memLp_eq_integral_inner
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T20:43:11.756378+00:00
-- url     : https://prove2.me/submissions/bde694cf-7710-456b-a613-e4f77edb8406

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.ENNReal.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner



/-! Duality for `L^p(μ; E)`: helper layer 1 (dominated convergence in `L^p`, a positive weight
in `L^p`). -/

namespace CauchyRiemannIndex.LpDual

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

lemma enorm_le_enorm_of_le' {a : E} {b : ℝ} (h : ‖a‖ ≤ b) : ‖a‖ₑ ≤ ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (h.trans (le_abs_self b))

/-- Dominated convergence in `L^p`, `p < ∞`. -/
lemma tendsto_eLpNorm_zero_of_dominated {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {F : ℕ → α → E}
    {bound : α → ℝ} (hb : MemLp bound p μ) (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hle : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (F k) p μ) atTop (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hp]
  have h1 : Tendsto (fun k => ∫⁻ x, ‖F k x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖bound x‖ₑ ^ p.toReal)
      (fun k => ((hF k).enorm.pow_const _)) (fun k => ?_) ?_ ?_
    · filter_upwards [hle k] with x hx
      gcongr
      exact enorm_le_enorm_of_le' hx
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hb.2).ne
    · filter_upwards [hlim] with x hx
      have : Tendsto (fun k => ‖F k x‖ₑ) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : E)).comp hx
      have h2 := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0 |>.comp this
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hr] using h2
  rw [lintegral_zero] at h1
  have h3 := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp h1
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.2 hr)] using h3

/-- A positive measurable weight in `L^p` of a σ-finite measure. -/
lemma exists_pos_weight (μ : Measure α) [SigmaFinite μ] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) :
    ∃ w : α → ℝ, (∀ x, 0 < w x) ∧ Measurable w ∧ MemLp w p μ := by
  obtain ⟨g, gpos, gmeas, gint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ (ε := 1) one_ne_zero
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine ⟨fun x => (g x : ℝ) ^ (1 / p.toReal), fun x => Real.rpow_pos_of_pos (gpos x) _,
    (measurable_coe_nnreal_real.comp gmeas).pow_const _, ?_⟩
  refine ⟨((measurable_coe_nnreal_real.comp gmeas).pow_const _).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hp]
  have e : ∀ x, ‖(g x : ℝ) ^ (1 / p.toReal)‖ₑ ^ p.toReal = (g x : ℝ≥0∞) := by
    intro x
    have h0 : (0 : ℝ) ≤ (g x : ℝ) ^ (1 / p.toReal) := Real.rpow_nonneg (g x).coe_nonneg _
    rw [Real.enorm_of_nonneg h0]
    rw [ENNReal.ofReal_rpow_of_nonneg h0 hr.le]
    rw [← Real.rpow_mul (g x).coe_nonneg, one_div_mul_cancel hr.ne', Real.rpow_one, ENNReal.ofReal_coe_nnreal]
  simp_rw [e]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (gint.trans ENNReal.one_lt_top).ne

end CauchyRiemannIndex.LpDual

/-! Duality for `L^p(μ; E)`: helper layer 2 (the signed measures `A ↦ ℓ(1_A w e)` and their
densities). -/

namespace CauchyRiemannIndex.LpDual

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {w : α → ℝ}

lemma memLp_smul_const (hw : MemLp w p μ) (e : E) : MemLp (fun x => w x • e) p μ :=
  (hw.const_mul ‖e‖).of_le (hw.aestronglyMeasurable.smul aestronglyMeasurable_const)
    (Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg e),
        mul_comm])

/-- `1_A w e` in `L^p`. -/
def indLp (hw : MemLp w p μ) (e : E) {A : Set α} (hA : MeasurableSet A) : Lp E p μ :=
  ((memLp_smul_const hw e).indicator hA).toLp _

lemma coeFn_indLp (hw : MemLp w p μ) (e : E) {A : Set α} (hA : MeasurableSet A) :
    (indLp hw e hA : α → E) =ᵐ[μ] A.indicator (fun x => w x • e) :=
  MemLp.coeFn_toLp _

lemma indLp_empty (hw : MemLp w p μ) (e : E) : indLp hw e MeasurableSet.empty = 0 := by
  unfold indLp
  simp only [Set.indicator_empty]
  exact MemLp.toLp_zero _

lemma indLp_union (hw : MemLp w p μ) (e : E) {A B : Set α} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) :
    indLp hw e (hA.union hB) = indLp hw e hA + indLp hw e hB := by
  unfold indLp
  rw [← MemLp.toLp_add]
  congr 1
  exact Set.indicator_union_of_disjoint hAB _

lemma indLp_diff (hw : MemLp w p μ) (e : E) {A B : Set α} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBA : B ⊆ A) :
    indLp hw e (hA.diff hB) = indLp hw e hA - indLp hw e hB := by
  unfold indLp
  rw [← MemLp.toLp_sub]
  congr 1
  funext x
  by_cases hx : x ∈ B
  · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hBA hx), hx]
  · by_cases hxA : x ∈ A
    · simp [Set.indicator_of_mem hxA, hx, hxA]
    · simp [hx, hxA]

lemma indLp_finset (hw : MemLp w p μ) (e : E) {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) (s : Finset ℕ) :
    ∑ i ∈ s, indLp hw e (hf i) = indLp hw e (Finset.measurableSet_biUnion s fun i _ => hf i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : (⋃ i ∈ (∅ : Finset ℕ), f i) = ∅ := by simp
    unfold indLp
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.indicator_empty]
    exact (MemLp.toLp_zero _).symm
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih]
    have hU : (⋃ i ∈ insert a s, f i) = f a ∪ ⋃ i ∈ s, f i := Finset.set_biUnion_insert _ _ _
    have hdis : Disjoint (f a) (⋃ i ∈ s, f i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hd (fun h => ha (h ▸ hi))
    rw [← indLp_union hw e (hf a) (Finset.measurableSet_biUnion s fun i _ => hf i) hdis]
    unfold indLp
    congr 2
    rw [hU]

lemma norm_indLp_le (hw : MemLp w p μ) (e : E) {A B : Set α} (hA : MeasurableSet A)
    (hAB : A ⊆ B) :
    ‖indLp hw e hA‖ ≤ (eLpNorm (B.indicator fun x => w x • e) p μ).toReal := by
  unfold indLp
  rw [Lp.norm_toLp]
  refine ENNReal.toReal_mono ?_ (eLpNorm_mono fun x => ?_)
  · exact (lt_of_le_of_lt (eLpNorm_mono fun x => norm_indicator_le_norm_self _ _)
      (memLp_smul_const hw e).2).ne
  · by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hAB hx)]
    · simp [Set.indicator_of_notMem hx]

/-- Countable additivity of `A ↦ 1_A w e` in `L^p`, `p < ∞`. -/
lemma hasSum_indLp (hp : p ≠ ⊤) (hw : MemLp w p μ) (e : E) {f : ℕ → Set α}
    (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun i => indLp hw e (hf i)) (indLp hw e (MeasurableSet.iUnion hf)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  set T : ℕ → Set α := fun N => ⋃ i, ⋃ (_ : N ≤ i), f i with hT
  -- the tails go to zero in `L^p`
  have htail : Tendsto (fun N => eLpNorm ((T N).indicator fun x => w x • e) p μ) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_zero_of_dominated hp0 hp (hw.norm.const_mul ‖e‖)
      (fun N => ?_) (fun N => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact ((hw.aestronglyMeasurable.smul aestronglyMeasurable_const).indicator
        (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hf i))
    · refine (norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)
      rw [norm_smul, mul_comm]
    · by_cases hx : ∃ j, x ∈ f j
      · obtain ⟨j, hj⟩ := hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop j] with N hN
        refine (Set.indicator_of_notMem ?_ _).symm
        simp only [hT, Set.mem_iUnion, not_exists]
        intro i hi hxi
        exact Set.disjoint_left.1 (hd (show j ≠ i by omega)) hj hxi
      · push_neg at hx
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
        refine (Set.indicator_of_notMem ?_ _).symm
        simp only [hT, Set.mem_iUnion, not_exists]
        exact fun i _ => hx i
  unfold HasSum
  rw [SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  have htail' : Tendsto (fun N => (eLpNorm ((T N).indicator fun x => w x • e) p μ).toReal) atTop
      (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htail') ε hε
  refine ⟨Finset.range N, fun s hs => ?_⟩
  rw [indLp_finset hw e hf hd s, dist_eq_norm, norm_sub_rev, ← indLp_diff]
  · refine (norm_indLp_le hw e _ (B := T N) ?_).trans_lt ?_
    · intro x hx
      simp only [Set.mem_diff, Set.mem_iUnion] at hx
      obtain ⟨⟨j, hj⟩, hns⟩ := hx
      simp only [hT, Set.mem_iUnion]
      refine ⟨j, ?_, hj⟩
      by_contra hjN
      exact hns ⟨j, hs (Finset.mem_range.2 (by omega)), hj⟩
    · have := hN N le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at this
      exact this
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, -, hi⟩ := hx
    exact ⟨i, hi⟩

variable (ℓ : Lp E p μ →L[ℝ] ℝ)

open Classical in
/-- The signed measure `A ↦ ℓ(1_A w e)`. -/
def nu (hp : p ≠ ⊤) (hw : MemLp w p μ) (e : E) : SignedMeasure α where
  measureOf' A := if hA : MeasurableSet A then ℓ (indLp hw e hA) else 0
  empty' := by simp [indLp_empty]
  not_measurable' A hA := by simp [hA]
  m_iUnion' f hf hd := by
    simp only [hf, MeasurableSet.iUnion hf, dite_true]
    exact ℓ.hasSum (hasSum_indLp hp hw e hf hd)

open Classical in
lemma nu_apply (hp : p ≠ ⊤) (hw : MemLp w p μ) (e : E) {A : Set α} (hA : MeasurableSet A) :
    nu ℓ hp hw e A = ℓ (indLp hw e hA) := by
  change (if hA : MeasurableSet A then ℓ (indLp hw e hA) else 0) = _
  rw [dif_pos hA]

lemma nu_ac (hp : p ≠ ⊤) (hw : MemLp w p μ) (e : E) :
    nu ℓ hp hw e ≪ᵥ μ.toENNRealVectorMeasure := by
  intro A hA0
  by_cases hA : MeasurableSet A
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hA0
    rw [nu_apply ℓ hp hw e hA]
    have : indLp hw e hA = 0 := by
      refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
      refine (coeFn_indLp hw e hA).trans ?_
      exact indicator_ae_eq_zero_of_restrict_ae_eq_zero hA (by rw [Measure.restrict_eq_zero.2 hA0]; simp [Filter.EventuallyEq])
    rw [this, map_zero]
  · exact (nu ℓ hp hw e).not_measurable hA

lemma ell_indLp_eq_integral [SigmaFinite μ] (hp : p ≠ ⊤) (hw : MemLp w p μ) (e : E) {A : Set α}
    (hA : MeasurableSet A) :
    ℓ (indLp hw e hA) = ∫ x in A, (nu ℓ hp hw e).rnDeriv μ x ∂μ := by
  rw [← nu_apply ℓ hp hw e hA, ← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hA,
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ (nu_ac ℓ hp hw e)]

end

end CauchyRiemannIndex.LpDual

/-! Duality for `L^p(μ; E)`: helper layer 3 (from indicators to bounded measurable multipliers). -/

namespace CauchyRiemannIndex.LpDual

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {w : α → ℝ}

variable (ℓ : Lp E p μ →L[ℝ] ℝ)

open Classical in
/-- `ℓ` evaluated on functions (zero off `L^p`). -/
def Lf (F : α → E) : ℝ := if h : MemLp F p μ then ℓ (h.toLp F) else 0

omit [Fact (1 ≤ p)] in
lemma memLp_bdd_smul {F : α → E} (hF : MemLp F p μ) {ψ : α → ℝ}
    (hψ : AEStronglyMeasurable ψ μ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) :
    MemLp (fun x => ψ x • F x) p μ :=
  (hF.norm.const_mul C).of_le (hψ.smul hF.aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_norm]
      have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
      rw [abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

lemma Lf_eq {F : α → E} (h : MemLp F p μ) : Lf ℓ F = ℓ (h.toLp F) := by
  unfold Lf; rw [dif_pos h]

lemma Lf_add {F G : α → E} (hF : MemLp F p μ) (hG : MemLp G p μ) :
    Lf ℓ (F + G) = Lf ℓ F + Lf ℓ G := by
  rw [Lf_eq ℓ (hF.add hG), Lf_eq ℓ hF, Lf_eq ℓ hG, MemLp.toLp_add hF hG, map_add]

lemma Lf_smul {F : α → E} (hF : MemLp F p μ) (c : ℝ) : Lf ℓ (c • F) = c * Lf ℓ F := by
  rw [Lf_eq ℓ (hF.const_smul c), Lf_eq ℓ hF, MemLp.toLp_const_smul c hF, map_smul, smul_eq_mul]

lemma Lf_sum {ι : Type*} (s : Finset ι) {F : ι → α → E} (hF : ∀ i, MemLp (F i) p μ) :
    Lf ℓ (∑ i ∈ s, F i) = ∑ i ∈ s, Lf ℓ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Lf_eq ℓ (MemLp.zero : MemLp (0 : α → E) p μ), MemLp.toLp_zero, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      Lf_add ℓ (hF a) (memLp_finset_sum' s fun i _ => hF i), ih]

lemma tendsto_Lf {F : ℕ → α → E} {G : α → E} (hF : ∀ k, MemLp (F k) p μ) (hG : MemLp G p μ)
    (h : Tendsto (fun k => eLpNorm (F k - G) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => Lf ℓ (F k)) atTop (𝓝 (Lf ℓ G)) := by
  simp_rw [Lf_eq ℓ (hF _), Lf_eq ℓ hG]
  refine (ℓ.continuous.tendsto _).comp ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have : ∀ k, ‖(hF k).toLp (F k) - hG.toLp G‖ = (eLpNorm (F k - G) p μ).toReal := by
    intro k
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
  simp_rw [this]
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- `ℓ(ψ w e) = ∫ ψ ρₑ` for simple `ψ`. -/
lemma Lf_simple [SigmaFinite μ] (hp : p ≠ ⊤) (hw : MemLp w p μ) (e : E) (ψ : SimpleFunc α ℝ) :
    Lf ℓ (fun x => ψ x • (w x • e)) = ∫ x, ψ x * (nu ℓ hp hw e).rnDeriv μ x ∂μ := by
  set ρ := (nu ℓ hp hw e).rnDeriv μ
  have hρ : Integrable ρ μ := SignedMeasure.integrable_rnDeriv _ _
  have hmem : ∀ ψ : SimpleFunc α ℝ, MemLp (fun x => ψ x • (w x • e)) p μ := fun ψ => by
    obtain ⟨C, hC⟩ := ψ.exists_forall_norm_le
    exact memLp_bdd_smul (memLp_smul_const hw e) ψ.aestronglyMeasurable
      (C := C) fun x => (Real.norm_eq_abs _).symm.le.trans (hC x)
  have hint : ∀ ψ : SimpleFunc α ℝ, Integrable (fun x => ψ x * ρ x) μ := fun ψ => by
    obtain ⟨C, hC⟩ := ψ.exists_forall_norm_le
    exact hρ.bdd_mul ψ.aestronglyMeasurable (Eventually.of_forall hC)
  induction ψ using SimpleFunc.induction with
  | @const c s hs =>
    have e1 : (fun x => (SimpleFunc.piecewise s hs (SimpleFunc.const α c)
        (SimpleFunc.const α 0)) x • (w x • e)) = c • s.indicator (fun x => w x • e) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    have e2 : (fun x => (SimpleFunc.piecewise s hs (SimpleFunc.const α c)
        (SimpleFunc.const α 0)) x * ρ x) = s.indicator (fun x => c * ρ x) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [e1, e2, Lf_smul ℓ ((memLp_smul_const hw e).indicator hs), Lf_eq ℓ
      ((memLp_smul_const hw e).indicator hs), integral_indicator hs, integral_const_mul]
    change c * ℓ (indLp hw e hs) = _
    rw [ell_indLp_eq_integral ℓ hp hw e hs]
  | @add f g _ hf hg =>
    have e1 : (fun x => (f + g) x • (w x • e)) =
        (fun x => f x • (w x • e)) + (fun x => g x • (w x • e)) := by
      funext x; simp [add_smul]
    have e2 : (fun x => (f + g) x * ρ x) = fun x => f x * ρ x + g x * ρ x := by
      funext x; simp [add_mul]
    rw [e1, e2, Lf_add ℓ (hmem f) (hmem g), hf, hg, integral_add (hint f) (hint g)]

/-- `ℓ(ψ w e) = ∫ ψ ρₑ` for bounded strongly measurable `ψ`. -/
lemma Lf_bdd [SigmaFinite μ] (hp : p ≠ ⊤) (hw : MemLp w p μ) (e : E) {ψ : α → ℝ}
    (hψ : StronglyMeasurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, |ψ x| ≤ C) :
    Lf ℓ (fun x => ψ x • (w x • e)) = ∫ x, ψ x * (nu ℓ hp hw e).rnDeriv μ x ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  set ρ := (nu ℓ hp hw e).rnDeriv μ
  have hρ : Integrable ρ μ := SignedMeasure.integrable_rnDeriv _ _
  set ψk : ℕ → SimpleFunc α ℝ := fun k => hψ.approxBounded C k with hψk
  have hbd : ∀ k x, |ψk k x| ≤ C := fun k x => by
    rw [← Real.norm_eq_abs]; exact hψ.norm_approxBounded_le hC0 k x
  have hconv : ∀ x, Tendsto (fun k => ψk k x) atTop (𝓝 (ψ x)) := fun x =>
    hψ.tendsto_approxBounded_of_norm_le (by rw [Real.norm_eq_abs]; exact hC x)
  have hmemk : ∀ k, MemLp (fun x => ψk k x • (w x • e)) p μ := fun k =>
    memLp_bdd_smul (memLp_smul_const hw e) (ψk k).aestronglyMeasurable (hbd k)
  have hmem : MemLp (fun x => ψ x • (w x • e)) p μ :=
    memLp_bdd_smul (memLp_smul_const hw e) hψ.aestronglyMeasurable hC
  have hL : Tendsto (fun k => Lf ℓ (fun x => ψk k x • (w x • e))) atTop
      (𝓝 (Lf ℓ (fun x => ψ x • (w x • e)))) := by
    refine tendsto_Lf ℓ hmemk hmem ?_
    refine tendsto_eLpNorm_zero_of_dominated hp0 hp (hw.norm.const_mul (2 * C * ‖e‖))
      (fun k => (hmemk k).aestronglyMeasurable.sub hmem.aestronglyMeasurable)
      (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [Pi.sub_apply, ← sub_smul, norm_smul, Real.norm_eq_abs]
      have h1 : |ψk k x - ψ x| ≤ 2 * C := by
        have := abs_sub (ψk k x) (ψ x)
        linarith [hbd k x, hC x]
      calc |ψk k x - ψ x| * (|w x| * ‖e‖) ≤ (2 * C) * (|w x| * ‖e‖) := by gcongr
        _ = 2 * C * ‖e‖ * ‖w x‖ := by rw [Real.norm_eq_abs]; ring
    · have : Tendsto (fun k => (ψk k x - ψ x) • (w x • e)) atTop (𝓝 ((ψ x - ψ x) • (w x • e))) :=
        ((hconv x).sub tendsto_const_nhds).smul_const _
      simpa [sub_smul] using this
  have hR : Tendsto (fun k => ∫ x, ψk k x * ρ x ∂μ) atTop (𝓝 (∫ x, ψ x * ρ x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => C * ‖ρ x‖)
      (fun k => ((ψk k).aestronglyMeasurable.mul hρ.aestronglyMeasurable))
      (hρ.norm.const_mul C) (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ((hconv x).mul tendsto_const_nhds))
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbd k x) (norm_nonneg _)
  have hk : ∀ k, Lf ℓ (fun x => ψk k x • (w x • e)) = ∫ x, ψk k x * ρ x ∂μ := fun k =>
    Lf_simple ℓ hp hw e (ψk k)
  simp_rw [hk] at hL
  exact tendsto_nhds_unique hL hR

end

end CauchyRiemannIndex.LpDual

/-! Duality for `L^p(μ; E)`: helper layer 4 (the vector density `G` and the representation of
`ℓ` once `G ∈ L^q`). -/

namespace CauchyRiemannIndex.LpDual

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {w : α → ℝ}

variable (ℓ : Lp E p μ →L[ℝ] ℝ)

/-- The density of `ℓ` with respect to `w μ`: `G = ∑ᵢ (ρᵢ / w) bᵢ`. -/
def dens (hp : p ≠ ⊤) (hw : MemLp w p μ) (x : α) : E :=
  ∑ i, ((nu ℓ hp hw (stdOrthonormalBasis ℝ E i)).rnDeriv μ x / w x) •
    stdOrthonormalBasis ℝ E i

lemma stronglyMeasurable_dens (hp : p ≠ ⊤) (hw : MemLp w p μ) (hwm : Measurable w) :
    StronglyMeasurable (dens ℓ hp hw) := by
  unfold dens
  refine Finset.stronglyMeasurable_fun_sum (f := fun i x =>
    ((nu ℓ hp hw (stdOrthonormalBasis ℝ E i)).rnDeriv μ x / w x) • stdOrthonormalBasis ℝ E i)
    _ fun i _ => ?_
  exact ((SignedMeasure.measurable_rnDeriv _ _).div hwm).stronglyMeasurable.smul_const _

/-- `ℓ(w φ) = ∫ w ⟨φ, G⟩` for bounded strongly measurable `φ`. -/
lemma Lf_vec [SigmaFinite μ] (hp : p ≠ ⊤) (hw : MemLp w p μ) (hwpos : ∀ x, 0 < w x)
    {φ : α → E} (hφ : StronglyMeasurable φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) :
    Lf ℓ (fun x => w x • φ x) = ∫ x, w x * ⟪φ x, dens ℓ hp hw x⟫ ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  set ρ := fun i => (nu ℓ hp hw (b i)).rnDeriv μ
  have hψ : ∀ i, StronglyMeasurable fun x => ⟪b i, φ x⟫ := fun i =>
    (continuous_const.inner continuous_id).comp_stronglyMeasurable hφ
  have hψC : ∀ i x, |⟪b i, φ x⟫| ≤ C := fun i x => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [b.orthonormal.1 i, one_mul]; exact hC x
  have e1 : (fun x => w x • φ x) = ∑ i, fun x => ⟪b i, φ x⟫ • (w x • b i) := by
    funext x
    rw [Finset.sum_apply]
    conv_lhs => rw [← b.sum_repr' (φ x)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  rw [e1, Lf_sum ℓ _ fun i => memLp_bdd_smul (memLp_smul_const hw (b i))
    (hψ i).aestronglyMeasurable (hψC i)]
  rw [Finset.sum_congr rfl fun i _ => Lf_bdd ℓ hp hw (b i) (hψ i) hC0 (hψC i)]
  rw [← integral_finset_sum]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dens, inner_sum, real_inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hw0 : w x ≠ 0 := (hwpos x).ne'
    simp only [real_inner_comm (φ x)]
    field_simp
    try ring
  · intro i _
    exact (SignedMeasure.integrable_rnDeriv _ _).bdd_mul (hψ i).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hψC i x)

end

end CauchyRiemannIndex.LpDual

/-! Duality for `L^p(μ; E)`: helper layer 5 (representation of `ℓ` once `G ∈ L^q`). -/

namespace CauchyRiemannIndex.LpDual

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {w : α → ℝ}

variable (ℓ : Lp E p μ →L[ℝ] ℝ)

lemma eventually_le_mul (hwpos : ∀ x, 0 < w x) (a : ℝ) (x : α) :
    ∀ᶠ k : ℕ in atTop, a ≤ (k : ℝ) * w x := by
  obtain ⟨N, hN⟩ := exists_nat_ge (a / w x)
  filter_upwards [eventually_ge_atTop N] with k hk
  have : a / w x ≤ k := hN.trans (by exact_mod_cast hk)
  exact (div_le_iff₀ (hwpos x)).1 this

/-- `ℓ h = ∫ ⟨h, G⟩` once `G ∈ L^q`. -/
lemma ell_eq_integral [SigmaFinite μ] (hp : p ≠ ⊤) (hw : MemLp w p μ) (hwm : Measurable w)
    (hwpos : ∀ x, 0 < w x) {q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    (hG : MemLp (dens ℓ hp hw) q μ) (h : Lp E p μ) :
    ℓ h = ∫ x, ⟪h x, dens ℓ hp hw x⟫ ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  set G := dens ℓ hp hw
  have hhm : StronglyMeasurable h := Lp.stronglyMeasurable h
  set B : ℕ → Set α := fun k => {x | ‖h x‖ ≤ (k : ℝ) * w x} with hB
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    measurableSet_le hhm.norm.measurable (measurable_const.mul hwm)
  set φ : ℕ → α → E := fun k => (B k).indicator fun x => (w x)⁻¹ • h x with hφ
  have hφm : ∀ k, StronglyMeasurable (φ k) := fun k =>
    (hwm.inv.stronglyMeasurable.smul hhm).indicator (hBm k)
  have hφC : ∀ k x, ‖φ k x‖ ≤ k := by
    intro k x
    show ‖(B k).indicator (fun x => (w x)⁻¹ • h x) x‖ ≤ k
    by_cases hx : x ∈ B k
    · rw [Set.indicator_of_mem hx, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (hwpos x)), inv_mul_le_iff₀ (hwpos x), mul_comm]
      exact hx
    · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
  have hwφ : ∀ k, (fun x => w x • φ k x) = (B k).indicator h := by
    intro k; funext x
    by_cases hx : x ∈ B k
    · simp [hφ, Set.indicator_of_mem hx, smul_smul, (hwpos x).ne']
    · simp [hφ, Set.indicator_of_notMem hx]
  have hval : ∀ k, Lf ℓ ((B k).indicator h) = ∫ x, (B k).indicator (fun x => ⟪h x, G x⟫) x ∂μ := by
    intro k
    rw [← hwφ k, Lf_vec ℓ hp hw hwpos (hφm k) (Nat.cast_nonneg k) (hφC k)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ B k
    · simp only [hφ, Set.indicator_of_mem hx, real_inner_smul_left]
      field_simp [(hwpos x).ne']
      try rfl
    · simp [hφ, Set.indicator_of_notMem hx]
  have hmem : MemLp (h : α → E) p μ := Lp.memLp h
  have hL : Tendsto (fun k => Lf ℓ ((B k).indicator h)) atTop (𝓝 (Lf ℓ h)) := by
    refine tendsto_Lf ℓ (fun k => hmem.indicator (hBm k)) hmem ?_
    refine tendsto_eLpNorm_zero_of_dominated hp0 hp hmem.norm
      (fun k => (hmem.indicator (hBm k)).aestronglyMeasurable.sub hmem.aestronglyMeasurable)
      (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ B k
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_le_mul hwpos ‖h x‖ x] with k hk
      have hx : x ∈ B k := hk
      simp [Set.indicator_of_mem hx]
  have hR : Tendsto (fun k => ∫ x, (B k).indicator (fun x => ⟪h x, G x⟫) x ∂μ) atTop
      (𝓝 (∫ x, ⟪h x, G x⟫ ∂μ)) := by
    have hint : Integrable (fun x => ‖h x‖ * ‖G x‖) μ := hmem.norm.integrable_mul hG.norm
    refine tendsto_integral_of_dominated_convergence (fun x => ‖h x‖ * ‖G x‖)
      (fun k => ((AEStronglyMeasurable.inner hmem.aestronglyMeasurable hG.aestronglyMeasurable).indicator (hBm k)))
      hint (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · refine (norm_indicator_le_norm_self _ _).trans ?_
      exact norm_inner_le_norm _ _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_le_mul hwpos ‖h x‖ x] with k hk
      have hx : x ∈ B k := hk
      simp [Set.indicator_of_mem hx]
  simp_rw [hval] at hL
  rw [Lf_eq ℓ hmem, Lp.toLp_coeFn] at hL
  exact tendsto_nhds_unique hL hR

end

end CauchyRiemannIndex.LpDual

/-! Duality for `L^p(μ; E)`: helper layer 6 (`G ∈ L^q`). -/

namespace CauchyRiemannIndex.LpDual

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

lemma ennreal_le_rpow_of_le_mul_rpow {J c : ℝ≥0∞} {r s : ℝ} (hrs : r.HolderConjugate s)
    (hJ : J ≠ ⊤) (h : J ≤ c * J ^ (1 / r)) : J ≤ c ^ s := by
  have hr : 0 < r := hrs.pos
  have hs : 0 < s := hrs.symm.pos
  by_cases hJ0 : J = 0
  · rw [hJ0]; exact bot_le
  have hsplit : J = J ^ (1 / r) * J ^ (1 / s) := by
    rw [← ENNReal.rpow_add _ _ hJ0 hJ, one_div, one_div, hrs.inv_add_inv_eq_one, ENNReal.rpow_one]
  have h1 : J ^ (1 / s) ≤ c := by
    have hne0 : J ^ (1 / r) ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hJ0, hJ]
    have hnet : J ^ (1 / r) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hJ
    nth_rewrite 1 [hsplit] at h
    rw [mul_comm c] at h
    exact (ENNReal.mul_le_mul_iff_right hne0 hnet).1 h
  calc J = (J ^ (1 / s)) ^ s := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hs.ne', ENNReal.rpow_one]
    _ ≤ c ^ s := ENNReal.rpow_le_rpow h1 hs.le

lemma rpow_sub_two_mul {s : ℝ} (hs : 1 < s) {a : ℝ} (ha : 0 ≤ a) :
    a ^ (s - 2) * a = a ^ (s - 1) := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, mul_zero, Real.zero_rpow (by linarith : s - 1 ≠ 0)]
  · rw [← Real.rpow_add_one h.ne']; ring_nf

lemma rpow_sub_two_mul_sq {s : ℝ} (hs : 1 < s) {a : ℝ} (ha : 0 ≤ a) :
    a ^ (s - 2) * a ^ 2 = a ^ s := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, zero_pow two_ne_zero, mul_zero, Real.zero_rpow (by linarith : s ≠ 0)]
  · rw [← Real.rpow_natCast, ← Real.rpow_add h]; norm_num

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {w : α → ℝ}

variable (ℓ : Lp E p μ →L[ℝ] ℝ)

lemma Lf_le {F : α → E} (hF : MemLp F p μ) : Lf ℓ F ≤ ‖ℓ‖ * (eLpNorm F p μ).toReal := by
  rw [Lf_eq ℓ hF, ← Lp.norm_toLp F hF]
  exact (le_abs_self _).trans (ℓ.le_opNorm _)

/-- The density lies in `L^q`. -/
lemma memLp_dens [SigmaFinite μ] (hp : p ≠ ⊤) (hw : MemLp w p μ) (hwm : Measurable w)
    (hwpos : ∀ x, 0 < w x) {q : ℝ≥0∞} [hpq : p.HolderConjugate q] (hp1 : 1 < p) :
    MemLp (dens ℓ hp hw) q μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1.le).ne'
  have hqt : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp1.ne'
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  set r := p.toReal
  set s := q.toReal
  have hrs : r.HolderConjugate s := ENNReal.HolderConjugate.toReal_of_ne_top hp hqt
  have hr : 0 < r := hrs.pos
  have hs1 : 1 < s := hrs.symm.lt
  have hsr : (s - 1) * r = s := hrs.symm.sub_one_mul_conj
  set G := dens ℓ hp hw
  have hGm : StronglyMeasurable G := stronglyMeasurable_dens ℓ hp hw hwm
  set B : ℕ → Set α := fun N => {x | ‖G x‖ ≤ N ∧ 1 ≤ (N : ℝ) * w x} with hB
  have hBm : ∀ N, MeasurableSet (B N) := fun N =>
    (measurableSet_le hGm.norm.measurable measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.mul hwm))
  -- the test functions
  set φ : ℕ → α → E := fun N => (B N).indicator fun x => (‖G x‖ ^ (s - 2) / w x) • G x with hφ
  set F : ℕ → α → E := fun N => (B N).indicator fun x => ‖G x‖ ^ (s - 2) • G x with hF
  have hnormF : ∀ N x, ‖F N x‖ = (B N).indicator (fun x => ‖G x‖ ^ (s - 1)) x := by
    intro N x
    by_cases hx : x ∈ B N
    · simp only [hF, Set.indicator_of_mem hx, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact rpow_sub_two_mul hs1 (norm_nonneg _)
    · simp [hF, Set.indicator_of_notMem hx]
  have hφm : ∀ N, StronglyMeasurable (φ N) := fun N =>
    ((hGm.norm.measurable.pow_const _).div hwm).stronglyMeasurable.smul hGm |>.indicator (hBm N)
  have hφC : ∀ N x, ‖φ N x‖ ≤ (N : ℝ) ^ (s - 1) * N := by
    intro N x
    show ‖(B N).indicator (fun x => (‖G x‖ ^ (s - 2) / w x) • G x) x‖ ≤ _
    by_cases hx : x ∈ B N
    · rw [Set.indicator_of_mem hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hwpos x).le), div_mul_eq_mul_div,
        rpow_sub_two_mul hs1 (norm_nonneg _), div_le_iff₀ (hwpos x)]
      have h1 : ‖G x‖ ^ (s - 1) ≤ (N : ℝ) ^ (s - 1) :=
        Real.rpow_le_rpow (norm_nonneg _) hx.1 (by linarith)
      have h2 : 0 ≤ (N : ℝ) ^ (s - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      nlinarith [hx.2]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  have hwφ : ∀ N, (fun x => w x • φ N x) = F N := by
    intro N; funext x
    by_cases hx : x ∈ B N
    · simp only [hφ, hF, Set.indicator_of_mem hx, smul_smul]
      congr 1
      field_simp [(hwpos x).ne']
    · simp [hφ, hF, Set.indicator_of_notMem hx]
  have hφmem : ∀ N, MemLp (fun x => w x • φ N x) p μ := fun N =>
    (hw.norm.const_mul ((N : ℝ) ^ (s - 1) * N)).of_le
      (hwm.aestronglyMeasurable.smul (hφm N).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        have hK : 0 ≤ (N : ℝ) ^ (s - 1) * N :=
          mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
        calc ‖w x • φ N x‖ = ‖φ N x‖ * |w x| := by rw [norm_smul, Real.norm_eq_abs, mul_comm]
          _ ≤ ((N : ℝ) ^ (s - 1) * N) * |w x| :=
            mul_le_mul_of_nonneg_right (hφC N x) (abs_nonneg _)
          _ = ‖((N : ℝ) ^ (s - 1) * N) * ‖w x‖‖ := by
            rw [Real.norm_eq_abs, abs_mul, abs_norm, abs_of_nonneg hK, Real.norm_eq_abs])
  set J : ℕ → ℝ≥0∞ := fun N => ∫⁻ x, (B N).indicator (fun x => ENNReal.ofReal (‖G x‖ ^ s)) x ∂μ
    with hJ
  -- (A) the value of `ℓ`
  have hA : ∀ N, Lf ℓ (fun x => w x • φ N x) = (J N).toReal := by
    intro N
    rw [Lf_vec ℓ hp hw hwpos (hφm N) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Nat.cast_nonneg _)) (hφC N)]
    have e : (fun x => w x * ⟪φ N x, G x⟫) = (B N).indicator (fun x => ‖G x‖ ^ s) := by
      funext x
      by_cases hx : x ∈ B N
      · simp only [hφ, Set.indicator_of_mem hx, real_inner_smul_left, real_inner_self_eq_norm_sq]
        rw [← rpow_sub_two_mul_sq hs1 (norm_nonneg (G x))]
        field_simp [(hwpos x).ne']
      · simp [hφ, Set.indicator_of_notMem hx]
    rw [show (fun x => w x * ⟪φ N x, dens ℓ hp hw x⟫) = (B N).indicator (fun x => ‖G x‖ ^ s)
      from e, integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      refine lintegral_congr fun x => ?_
      by_cases hx : x ∈ B N <;> simp [hx]
    · exact Eventually.of_forall fun x => Set.indicator_nonneg
        (fun x _ => Real.rpow_nonneg (norm_nonneg _) _) x
    · exact ((hGm.norm.measurable.pow_const _).indicator (hBm N)).aestronglyMeasurable
  -- (C) the norm of the test function
  have hC : ∀ N, eLpNorm (fun x => w x • φ N x) p μ = J N ^ (1 / r) := by
    intro N
    rw [hwφ N, eLpNorm_eq_lintegral_rpow_enorm hp0 hp]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, hnormF N x]
    by_cases hx : x ∈ B N
    · simp only [Set.indicator_of_mem hx]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hr.le,
        ← Real.rpow_mul (norm_nonneg _), hsr]
    · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
      exact ENNReal.zero_rpow_of_pos hr
  -- (E) finiteness
  have hfin : ∀ N, J N ≠ ⊤ := by
    intro N
    have hwr : ∫⁻ x, ‖w x‖ₑ ^ r ∂μ < ⊤ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hw.2
    have hbound : ∀ x, (B N).indicator (fun x => ENNReal.ofReal (‖G x‖ ^ s)) x ≤
        ENNReal.ofReal ((N : ℝ) ^ s * (N : ℝ) ^ r) * ‖w x‖ₑ ^ r := by
      intro x
      by_cases hx : x ∈ B N
      · simp only [Set.indicator_of_mem hx]
        rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ‖G x‖ ^ s ≤ (N : ℝ) ^ s :=
          Real.rpow_le_rpow (norm_nonneg _) hx.1 (by linarith)
        have h2 : (1 : ℝ) ≤ ((N : ℝ) * w x) ^ r := Real.one_le_rpow hx.2 hr.le
        rw [Real.mul_rpow (Nat.cast_nonneg _) (hwpos x).le] at h2
        rw [Real.norm_eq_abs, abs_of_pos (hwpos x)]
        have h3 : 0 ≤ (N : ℝ) ^ s := Real.rpow_nonneg (Nat.cast_nonneg _) _
        nlinarith
      · simp only [Set.indicator_of_notMem hx]; exact bot_le
    refine (lt_of_le_of_lt (lintegral_mono hbound) ?_).ne
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hwr
  -- the bound for each `N`
  have hJle : ∀ N, J N ≤ ENNReal.ofReal ‖ℓ‖ ^ s := by
    intro N
    refine ennreal_le_rpow_of_le_mul_rpow hrs (hfin N) ?_
    have h1 := Lf_le ℓ (hφmem N)
    rw [hA N, hC N] at h1
    have hfin' : J N ^ (1 / r) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (hfin N)
    calc J N = ENNReal.ofReal (J N).toReal := (ENNReal.ofReal_toReal (hfin N)).symm
      _ ≤ ENNReal.ofReal (‖ℓ‖ * (J N ^ (1 / r)).toReal) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal ‖ℓ‖ * J N ^ (1 / r) := by
        rw [ENNReal.ofReal_mul (norm_nonneg ℓ), ENNReal.ofReal_toReal hfin']
  -- (F) monotone limit
  have hlim : ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ s) ∂μ ≤ ENNReal.ofReal ‖ℓ‖ ^ s := by
    have ht : Tendsto J atTop (𝓝 (∫⁻ x, ENNReal.ofReal (‖G x‖ ^ s) ∂μ)) := by
      refine lintegral_tendsto_of_tendsto_of_monotone (fun N => ?_) ?_ ?_
      · exact ((ENNReal.measurable_ofReal.comp (hGm.norm.measurable.pow_const _)).indicator
          (hBm N)).aemeasurable
      · refine Eventually.of_forall fun x => monotone_nat_of_le_succ fun N => ?_
        by_cases hx : x ∈ B N
        · have hx' : x ∈ B (N + 1) := by
            refine ⟨hx.1.trans (by push_cast; linarith), hx.2.trans ?_⟩
            push_cast
            nlinarith [hwpos x]
          simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
        · simp only [Set.indicator_of_notMem hx]; exact bot_le
      · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
        obtain ⟨N₁, hN₁⟩ := exists_nat_ge ‖G x‖
        filter_upwards [eventually_ge_atTop N₁, eventually_le_mul hwpos 1 x] with N hN h1
        have hx : x ∈ B N := ⟨hN₁.trans (by exact_mod_cast hN), h1⟩
        simp [Set.indicator_of_mem hx]
    exact le_of_tendsto' ht hJle
  -- (G) conclusion
  refine ⟨hGm.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqt]
  have e : ∀ x, ‖G x‖ₑ ^ s = ENNReal.ofReal (‖G x‖ ^ s) := fun x => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]
  have e2 : ∫⁻ x, ‖G x‖ₑ ^ q.toReal ∂μ = ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ s) ∂μ := lintegral_congr e
  rw [e2]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
    (ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top) hlim)

end

end CauchyRiemannIndex.LpDual

namespace JHolomorphic

open MeasureTheory
open scoped ENNReal

theorem exists_memLp_eq_integral_inner_aux {α E : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [p.HolderConjugate q] (hp : 1 < p) (hp' : p ≠ ⊤)
    (ℓ : Lp E p μ →L[ℝ] ℝ) :
    ∃ G : α → E, MemLp G q μ ∧ ∀ h : Lp E p μ, ℓ h = ∫ x, inner ℝ (h x) (G x) ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp.le).ne'
  obtain ⟨w, hwpos, hwm, hw⟩ := CauchyRiemannIndex.LpDual.exists_pos_weight μ hp0 hp'
  have hG := CauchyRiemannIndex.LpDual.memLp_dens ℓ hp' hw hwm hwpos (q := q) hp
  exact ⟨_, hG, CauchyRiemannIndex.LpDual.ell_eq_integral ℓ hp' hw hwm hwpos hG⟩

end JHolomorphic

open JHolomorphic

open MeasureTheory
open scoped ENNReal

theorem solution {α E : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [p.HolderConjugate q] (hp : 1 < p) (hp' : p ≠ ⊤)
    (ℓ : Lp E p μ →L[ℝ] ℝ) :
    ∃ G : α → E, MemLp G q μ ∧ ∀ h : Lp E p μ, ℓ h = ∫ x, inner ℝ (h x) (G x) ∂μ :=
  exists_memLp_eq_integral_inner_aux μ p q hp hp' ℓ
