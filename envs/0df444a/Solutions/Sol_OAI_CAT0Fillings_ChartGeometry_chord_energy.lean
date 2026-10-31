-- Prove2me | solution 1 for OAI.CAT0Fillings.ChartGeometry.chord_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:03:41.292273+00:00
-- url     : https://prove2.me/submissions/b6014038-dc15-4765-81f0-daabc12770cd

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_closed_added_tests

section
-- module Solutions.OAIQ29_C0.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ProductRule
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma IntegerRectifiable.cycle_product_rule {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hz : IsCycle T) {b f : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    T b (Matrix.vecCons f π) = -T f (Matrix.vecCons b π) := by
  have h := IntegerRectifiable.product_rule hT hb hf π hπ
  have hz' : boundarySucc T = fun _ _ => 0 := hz
  rw [hz'] at h
  exact eq_neg_of_add_eq_zero_left h

end Foundations
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_SpatialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma det_updateRow_identity (j : ι) (v : ι → ℝ) :
    (Matrix.updateRow (1 : Matrix ι ι ℝ) j v).det = v j := by
  have he : (∑ i : ι, v i • (1 : Matrix ι ι ℝ) i) = v := by
    ext l
    simp [Matrix.one_apply]
  rw [←he,Matrix.det_updateRow_sum]
  simp [Matrix.one_apply]

end CAT0Fillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_RadialChart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma scalar_paramExtended_eqOn (b : X → ℝ) :
    EqOn (fun z => b (C.paramExtended z)) (C.scalar b) C.domain := by
  intro z hz; simp only [paramExtended,scalar,dite_eq_left hz]

end IntegerChart
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Chart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators Matrix.Norms.L2Operator

namespace CAT0Fillings

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_duNorm_bounds (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      0 ≤ q.duNorm i u z ∧ q.duNorm i u z ≤ (K : ℝ) ∧
      q.duNorm i u z ^2 = q.normSq i u z := by
  filter_upwards [q.ae_normSq_bounds i hu] with z hz
  exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left K.coe_nonneg).mpr hz.2, Real.sq_sqrt hz.1⟩

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators MatrixOrder

namespace CAT0Fillings

lemma abs_det_le_prod_dual_norm {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    |L.det| ≤ (∏ i, Real.sqrt (L i ⬝ᵥ P⁻¹.mulVec (L i))) * Real.sqrt P.det := by
  let Q := CFC.sqrt P⁻¹
  have hQsym : Q.transpose = Q :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P⁻¹).posSemidef.isHermitian).eq
  have hQdet : Q.det = (Real.sqrt P.det)⁻¹ := by
    have hh := hP.inv.posSemidef.det_sqrt
    simpa only [Q,RCLike.sqrt_real,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,
      Real.sqrt_inv] using hh
  have hJ : 0 < Real.sqrt P.det := Real.sqrt_pos.mpr hP.det_pos
  have hrow (i : Fin n) : (L * Q) i = Q.mulVec (L i) := by
    ext j
    change (∑ t, L i t * Q t j) = ∑ t, Q j t * L i t
    apply Finset.sum_congr rfl
    intro t ht
    have hs : Q t j = Q j t := congrFun (congrFun hQsym j) t
    rw [hs,mul_comm]
  have hnorm (i : Fin n) :
      ‖(WithLp.toLp 2 ((L*Q) i) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (L i ⬝ᵥ P⁻¹.mulVec (L i)) := by
    have hn : ‖(WithLp.toLp 2 ((L*Q) i) : EuclideanSpace ℝ (Fin n))‖^2 =
        L i ⬝ᵥ P⁻¹.mulVec (L i) := by
      rw [←real_inner_self_eq_norm_sq]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,hrow]
      exact (dot_mulVec_sqrt P⁻¹ hP.inv.posSemidef (L i)).symm
    rw [←hn,Real.sqrt_sq (norm_nonneg _)]
  have heq : |L.det| = |(L*Q).det| * Real.sqrt P.det := by
    rw [Matrix.det_mul,abs_mul,hQdet,abs_of_pos (inv_pos.mpr hJ)]
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ hJ.le
  simpa only [hnorm] using abs_det_le_prod_row_norm (L*Q)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Coordinates
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma measurableSet_atlasDomain : MeasurableSet q.atlasDomain := by
  have he : q.atlasDomain = ⋃ i : ℕ, {i} ×ˢ (q.chart i).domain := by
    ext w
    simp only [atlasDomain,mem_ofPred_eq,mem_iUnion,mem_prod,mem_singleton_iff]
    constructor
    · exact fun h => ⟨w.1,rfl,h⟩
    · rintro ⟨i,hi,h⟩
      simpa only [hi] using h
  rw [he]
  exact MeasurableSet.iUnion (fun i => (measurableSet_singleton i).prod (q.chart i).borel)

lemma ae_mem_atlasDomain : ∀ᵐ w ∂q.atlasMeasure, w ∈ q.atlasDomain := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (q.chart i).borel)

lemma measurableEmbedding_atlas : MeasurableEmbedding (fun w : q.atlasDomain => q.atlasParam w) := by
  let := q.measurableSet_atlasDomain.standardBorel
  apply (q.measurable_atlasParam.comp measurable_subtype_coe).measurableEmbedding
  rintro ⟨⟨i,z⟩,hz⟩ ⟨⟨j,w⟩,hw⟩ h
  change z ∈ (q.chart i).domain at hz
  change w ∈ (q.chart j).domain at hw
  change (q.chart i).paramExtended z = (q.chart j).paramExtended w at h
  simp only [IntegerChart.paramExtended,dite_eq_left hz,dite_eq_left hw] at h
  have hi : i = j := by
    by_contra hn
    apply Set.disjoint_left.mp (q.disjoint hn) (show (q.chart i).param ⟨z,hz⟩ ∈
      (q.chart i).image from ⟨⟨z,hz⟩,rfl⟩)
    rw [h]
    exact ⟨⟨w,hw⟩,rfl⟩
  subst j
  have he := congrArg Subtype.val ((q.chart i).measurableEmbedding_param.injective h)
  change z = w at he
  subst w
  rfl

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Multiplier
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradientFunction_chain {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) :
    q.gradientFunction (F ∘ u) =ᵐ[q.atlasMeasure]
      (fun w => F' (u (q.atlasParam w)) • q.gradientFunction u w) := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  let C := q.chart i
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨f,hf,hef⟩ := (C.scalar_lipschitzOn hL hu).extend_real
  have hecomp : EqOn (C.scalar (F ∘ u)) (F ∘ f) C.domain := by
    intro z hz
    simp only [IntegerChart.scalar,dite_eq_left hz,Function.comp_apply]
    rw [←hef hz]
    simp only [IntegerChart.scalar,dite_eq_left hz]
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hf hef,
    ae_fderivWithin_eq_fderiv_extension volume C.borel (hF.comp hf) hecomp,
    hf.ae_differentiableAt.filter_mono ae_restrict_le,ae_restrict_mem C.borel] with z hu hcomp hdz hz
  change z ∈ C.domain at hz
  change q.normalizedCovector i (F ∘ u) z =
    F' (u (C.paramExtended z)) • q.normalizedCovector i u z
  have hname : f z = u (C.paramExtended z) := by
    rw [←hef hz]
    simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz]
  have hd := (hdF (f z)).comp_hasFDerivAt z hdz.hasFDerivAt
  dsimp only [normalizedCovector,covector]
  rw [hcomp,hd.fderiv,hu,hname]
  have he : differentialRow (F' (u (C.paramExtended z)) • fderiv ℝ f z) =
      F' (u (C.paramExtended z)) • differentialRow (fderiv ℝ f z) := rfl
  rw [he,Matrix.mulVec_smul,WithLp.toLp_smul]

lemma gradient_chain_ae {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) :
    q.gradient (hF.comp hu) =ᵐ[q.atlasMeasure]
      (fun w => F' (u (q.atlasParam w)) • q.gradient hu w) := by
  filter_upwards [(q.memLp_gradientFunction (hF.comp hu)).coeFn_toLp,
    (q.memLp_gradientFunction hu).coeFn_toLp,q.gradientFunction_chain hu hF hdF] with w h1 h2 h3
  exact h1.trans (h3.trans (congrArg (F' (u (q.atlasParam w)) • ·) h2.symm))

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma l2_norm_sq (g : Lp E 2 μ) : ‖g‖^2 = ∫ x, ‖g x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma l2_tendsto_zero_of_bound (f : ℕ → Lp E 2 μ) (g : α → ℝ)
    (hg : Integrable (fun x => (g x)^2) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ g x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hh : Tendsto (fun j => ∫ x, ‖f j x‖^2 ∂μ) atTop (𝓝 (∫ _ : α, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => g x^2)
      (fun j => (Lp.aestronglyMeasurable (f j)).norm.pow 2) hg
    · intro j
      filter_upwards [hb j] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hx)).mpr hx
    · filter_upwards [hl] with x hx
      simpa only [Pi.pow_apply,norm_zero,zero_pow (by decide : 2 ≠ 0)] using hx.norm.pow 2
  simp only [integral_zero,←l2_norm_sq] at hh
  have hn := hh.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

lemma mulLp_ae {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g : Lp E 2 μ) :
    mulLp hb hC g =ᵐ[μ] (fun x => b x • g x) := (memLp_smul_bounded hb hC g).coeFn_toLp

lemma mulLp_sub_bound {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g h : Lp E 2 μ) :
    ‖mulLp hb hC g-mulLp hb hC h‖ ≤ C*‖g-h‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (mulLp hb hC g) (mulLp hb hC h),mulLp_ae hb hC g,
    mulLp_ae hb hC h,Lp.coeFn_sub g h,hC] with x hs hg hh hd hCx
  rw [hs,hd,Pi.sub_apply,hg,hh,←smul_sub,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hCx (norm_nonneg _)

lemma mulLp_tendsto {b : ℕ → α → ℝ} {c : α → ℝ}
    (hb : ∀ j, AEStronglyMeasurable (b j) μ) (hc : AEStronglyMeasurable c μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ j, ∀ᵐ x ∂μ, |b j x| ≤ C) (hcC : ∀ᵐ x ∂μ, |c x| ≤ C)
    (hbc : ∀ᵐ x ∂μ, Tendsto (fun j => b j x) atTop (𝓝 (c x)))
    {g : ℕ → Lp E 2 μ} {h : Lp E 2 μ} (hgh : Tendsto g atTop (𝓝 h)) :
    Tendsto (fun j => mulLp (hb j) (hbC j) (g j)) atTop (𝓝 (mulLp hc hcC h)) := by
  have hfixed : Tendsto (fun j => mulLp (hb j) (hbC j) h-mulLp hc hcC h) atTop (𝓝 0) := by
    apply l2_tendsto_zero_of_bound _ (fun x => 2*C*‖h x‖)
    · have hi := (Lp.memLp h).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
      convert hi.const_mul ((2*C)^2) using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      ring
    · intro j
      filter_upwards [Lp.coeFn_sub (mulLp (hb j) (hbC j) h) (mulLp hc hcC h),
        mulLp_ae (hb j) (hbC j) h,mulLp_ae hc hcC h,hbC j,hcC] with x hs hb hc hbC hcC
      rw [hs,Pi.sub_apply,hb,hc,←sub_smul,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((abs_sub (b j x) (c x)).trans (by linarith)) (norm_nonneg _)
    · have hall : ∀ᵐ x ∂μ, ∀ j, (mulLp (hb j) (hbC j) h-mulLp hc hcC h) x =
          (b j x-c x) • h x := by
        apply ae_all_iff.mpr
        intro j
        filter_upwards [Lp.coeFn_sub (mulLp (hb j) (hbC j) h) (mulLp hc hcC h),
          mulLp_ae (hb j) (hbC j) h,mulLp_ae hc hcC h] with x hs hb hc
        rw [hs,Pi.sub_apply,hb,hc,sub_smul]
      filter_upwards [hall,hbc] with x he hx
      simp_rw [he]
      simpa only [sub_self,zero_smul] using (hx.sub_const (c x)).smul_const (h x)
  have hpert : Tendsto (fun j => mulLp (hb j) (hbC j) (g j)-mulLp (hb j) (hbC j) h)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun j => mulLp_sub_bound (hb j) (hbC j) (g j) h)
    simpa only [Real.norm_of_nonneg hC,sub_self,norm_zero,mul_zero] using
      ((hgh.sub_const h).norm).const_mul ‖C‖
  have hh := hpert.add hfixed
  simp only [sub_add_sub_cancel,add_zero] at hh
  have hf := hh.add_const (mulLp hc hcC h)
  simpa only [sub_add_cancel,zero_add] using hf

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Determinant
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

namespace CAT0Fillings

lemma sqrt_inverse_matrix_det_ne_zero {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) : (CFC.sqrt P⁻¹).det ≠ 0 := by
  have hh := hP.inv.posSemidef.det_sqrt
  rw [hh,RCLike.sqrt_real]
  exact (Real.sqrt_pos.mpr hP.inv.det_pos).ne'

lemma normalize_rawCovector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (v : Euc n) :
    (CFC.sqrt P⁻¹).mulVec (rawCovector P v) = WithLp.ofLp v := by
  rw [rawCovector,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (sqrt_inverse_matrix_det_ne_zero P hP)),Matrix.one_mulVec]

lemma raw_normalizedCovector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (a : Fin n → ℝ) :
    rawCovector P (WithLp.toLp 2 ((CFC.sqrt P⁻¹).mulVec a)) = a := by
  rw [rawCovector,WithLp.ofLp_toLp,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (sqrt_inverse_matrix_det_ne_zero P hP)),Matrix.one_mulVec]

lemma rawCovector_norm {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (v : Euc n) :
    Real.sqrt (rawCovector P v ⬝ᵥ P⁻¹.mulVec (rawCovector P v)) = ‖v‖ := by
  rw [dot_mulVec_sqrt P⁻¹ hP.inv.posSemidef,normalize_rawCovector P hP]
  have he : (WithLp.ofLp v) ⬝ᵥ (WithLp.ofLp v) = ‖v‖^2 := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  rw [he,Real.sqrt_sq (norm_nonneg _)]

lemma normalizedDet_bound_prod {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hP : P.PosDef) (R : Fin n → Fin (n+1) → ℝ) (K : Fin n → ℝ≥0)
    (hR : ∀ i, Real.sqrt (R i ⬝ᵥ P⁻¹.mulVec (R i)) ≤ K i) (v : Euc (n+1)) :
    |normalizedDet P R v| ≤ ‖v‖ * ∏ i, (K i : ℝ) := by
  have h := abs_det_le_prod_dual_norm (Matrix.vecCons (rawCovector P v) R) P hP
  rw [Fin.prod_univ_succ] at h
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] at h
  rw [rawCovector_norm P hP] at h
  have hprod := Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => Real.sqrt_nonneg
    (R i ⬝ᵥ P⁻¹.mulVec (R i))) (fun i _ => hR i)
  have hh := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprod (norm_nonneg v)) (Real.sqrt_nonneg _))
  rw [normalizedDet,abs_div,abs_of_pos (Real.sqrt_pos.mpr hP.det_pos)]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hP.det_pos)).mpr hh

lemma normalizedDet_sub {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (R : Fin n → Fin (n+1) → ℝ) (v w : Euc (n+1)) :
    normalizedDet P R (v-w) = normalizedDet P R v-normalizedDet P R w := by
  have hr : rawCovector P (v-w) = rawCovector P v-rawCovector P w := by
    simp [rawCovector,Matrix.mulVec_sub]
  unfold normalizedDet
  rw [hr,←sub_div]
  congr 1
  have he (a : Fin (n+1) → ℝ) : Matrix.vecCons a R =
      Matrix.updateRow (Matrix.vecCons (0 : Fin (n+1) → ℝ) R) 0 a := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [Matrix.updateRow]
  have ha := Matrix.det_updateRow_add (Matrix.vecCons (0 : Fin (n+1) → ℝ) R) 0
    (rawCovector P v) ((-1:ℝ) • rawCovector P w)
  rw [Matrix.det_updateRow_smul (Matrix.vecCons (0 : Fin (n+1) → ℝ) R) 0 (-1:ℝ)
    (rawCovector P w)] at ha
  simpa only [←he,neg_one_smul,sub_eq_add_neg,neg_one_mul] using ha

attribute [local instance] OAI.CAT0Fillings.instMeasurableSpaceMatrixFinReal_solutions_2
local instance instBorelSpaceMatrixFinReal_solutions_2 {n : ℕ} : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma aestronglyMeasurable_normalizedDet {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {n : ℕ} {P : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    {R : α → Fin n → Fin (n+1) → ℝ} {v : α → Euc (n+1)}
    (hP : Measurable P) (hR : AEStronglyMeasurable R μ) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => normalizedDet (P x) (R x) (v x)) μ := by
  have hQ := measurable_matrix_inverse _
    (measurable_matrix_sqrt.comp (measurable_matrix_inverse _ hP))
  have hc : Continuous (fun w : Matrix (Fin (n+1)) (Fin (n+1)) ℝ ×
      (Fin n → Fin (n+1) → ℝ) × Euc (n+1) =>
      Matrix.det (Matrix.vecCons (w.1.mulVec (WithLp.ofLp w.2.2)) w.2.1)) := by
    fun_prop
  have hh := hc.comp_aestronglyMeasurable (hQ.aestronglyMeasurable.prodMk (hR.prodMk hv))
  have hJ : Measurable (fun x => Real.sqrt (P x).det) := by fun_prop
  exact (hh.aemeasurable.div hJ.aemeasurable).aestronglyMeasurable

lemma orientation_bound (a : ℝ) : abs (a/abs a) ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [abs_div,abs_abs,div_self (abs_ne_zero.mpr ha)]

lemma orientation_density (a : ℝ) : abs a*(a/abs a) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · field_simp

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Pairing
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators MatrixOrder

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma aestronglyMeasurable_testWeight (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : AEStronglyMeasurable L q.atlasMeasure) :
    AEStronglyMeasurable (q.testWeight π L) q.atlasMeasure := by
  apply aestronglyMeasurable_sum_measure_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mpr
  have hLi := (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mp
    (aestronglyMeasurable_sum_measure_iff.mp hL i)
  have ha := (q.chart i).integrable.aestronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous (volume.restrict (q.chart i).domain)
      (fun z => ENNReal.ofReal (q.density i z)))
  have hR : AEStronglyMeasurable (fun z j => q.covector i (π j) z) (q.coordinateMeasure i) := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.of_eval (fun j =>
      ((q.aestronglyMeasurable_covector i (hπ j)).mono_ac
        (withDensity_absolutelyContinuous _ _)).aemeasurable)
  exact ((ha.aemeasurable.div ha.aemeasurable.abs).aestronglyMeasurable).mul
    (aestronglyMeasurable_normalizedDet _ (q.measurable_gram i) hR hLi)

lemma ae_testWeight_bound (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) (L : ℕ × Euc (k+1) → Euc (k+1)) :
    ∀ᵐ w ∂q.atlasMeasure, |q.testWeight π L w| ≤ ‖L w‖ * ∏ j, (K j : ℝ) := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  have hR : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      ∀ j, q.duNorm i (π j) z ≤ K j := by
    rw [eventually_all]
    intro j
    exact (q.ae_duNorm_bounds i (hπ j)).mono (fun z hz => hz.2.1)
  filter_upwards [q.differential i,hR] with z hz hRz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  change abs ((_ / abs _) * normalizedDet _ _ _) ≤ _
  rw [abs_mul]
  have hh := normalizedDet_bound_prod (q.gram i z) hG
    (fun j => q.covector i (π j) z) K hRz (L (i,z))
  exact (mul_le_mul_of_nonneg_right (orientation_bound _) (abs_nonneg _)).trans
    (by simpa only [one_mul] using hh)

lemma memLp_testWeight (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : MemLp L 2 q.atlasMeasure) : MemLp (q.testWeight π L) 2 q.atlasMeasure := by
  apply (hL.norm.mul_const (∏ j, (K j : ℝ))).mono'
    (q.aestronglyMeasurable_testWeight π K hπ hL.aestronglyMeasurable)
  simpa only [Real.norm_eq_abs] using q.ae_testWeight_bound π K hπ L

lemma integrable_testWeight_mul (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : MemLp L 2 q.atlasMeasure) {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun w => q.testWeight π L w*b (q.atlasParam w)) q.atlasMeasure := by
  obtain ⟨Kb,hbK⟩ := hb.1
  obtain ⟨M,hM⟩ := hb.2
  have hm : MemLp (fun w => b (q.atlasParam w)) 2 q.atlasMeasure :=
    MemLp.of_bound (hbK.continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable M
      (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hM (q.atlasParam w))
  exact (q.memLp_testWeight π K hπ hL).integrable_mul hm

lemma testWeight_gradient (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {u b : X → ℝ} {Ku : ℝ≥0}
    (hu : LipschitzWith Ku u) (hb : BoundedLip b) :
    (∫ w, q.testWeight π (q.gradientFunction u) w*b (q.atlasParam w) ∂q.atlasMeasure) =
      T b (Fin.cons u π) := by
  have hi := q.integrable_testWeight_mul π K hπ (q.memLp_gradientFunction hu) hb
  rw [atlasMeasure,integral_sum_measure hi,q.action]
  apply tsum_congr
  intro i
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have ha : Admissible b (Fin.cons u π) := Foundations.admissible_vecCons hb
    ⟨Ku,hu⟩ (fun j => ⟨K j,hπ j⟩)
  rw [IntegerChart.action,ite_eq_left ha]
  apply integral_congr_ae
  filter_upwards [q.differential i,ae_restrict_mem (q.chart i).borel] with z hz hzi
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i z),smul_eq_mul,
    testWeight,gradientFunction,normalizedDet,normalizedCovector,raw_normalizedCovector _ hG]
  have hd : Matrix.det (Matrix.vecCons (q.covector i u z) (fun j => q.covector i (π j) z)) =
      (q.chart i).jacobian (Fin.cons u π) z := by
    congr 1
    ext a j
    refine Fin.cases ?_ (fun a => ?_) a <;> rfl
  rw [hd]
  have hbz : b (q.atlasParam (i,z)) = (q.chart i).scalar b z := by
    simp only [atlasParam,IntegerChart.paramExtended,IntegerChart.scalar,dite_eq_left hzi]
  rw [hbz]
  unfold density
  have ho := orientation_density ((q.chart i).multiplicity z : ℝ)
  have hJ : Real.sqrt (q.gram i z).det ≠ 0 := (Real.sqrt_pos.mpr hG.det_pos).ne'
  calc
    _ = (abs ((q.chart i).multiplicity z : ℝ)*
        (((q.chart i).multiplicity z : ℝ)/abs ((q.chart i).multiplicity z : ℝ)))*
        (q.chart i).jacobian (Fin.cons u π) z*(q.chart i).scalar b z := by field_simp [hJ]
    _ = _ := by rw [ho]; ring

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

lemma integral_norm_le_lpNorm_two {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → E} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ lpNorm f 2 μ * Real.sqrt (μ.real univ) := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using hf.norm)
    (show MemLp (fun _ : α => (1:ℝ)) (ENNReal.ofReal 2) μ from memLp_const 1)
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  simpa only [norm_one,mul_one,Real.one_rpow,integral_const,smul_eq_mul,
    mul_one,ENNReal.toReal_ofNat,one_div,Real.sqrt_eq_rpow,norm_norm] using hh

lemma lpNorm_Lp {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} (f : Lp E p μ) : lpNorm f p μ = ‖f‖ := by
  rw [Lp.norm_def,toReal_eLpNorm (Lp.aestronglyMeasurable f)]

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma pairing_sub (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b : X → ℝ} (hb : BoundedLip b)
    (L M : Lp (Euc (k+1)) 2 q.atlasMeasure) :
    q.pairing π b (L-M) = q.pairing π b L-q.pairing π b M := by
  calc
    _ = ∫ w, (q.testWeight π L w-q.testWeight π M w)*b (q.atlasParam w)
        ∂q.atlasMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub L M] with w hw
      simp only [testWeight] at *
      rw [hw]
      simp only [Pi.sub_apply,normalizedDet_sub,mul_sub]
    _ = _ := by
      simp only [sub_mul]
      rw [integral_sub (q.integrable_testWeight_mul π K hπ (Lp.memLp L) hb)
        (q.integrable_testWeight_mul π K hπ (Lp.memLp M) hb)]
      rfl

lemma abs_pairing_le (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b : X → ℝ} (hb : BoundedLip b)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x, |b x| ≤ B)
    (L : Lp (Euc (k+1)) 2 q.atlasMeasure) :
    |q.pairing π b L| ≤ ((∏ j, (K j : ℝ))*B*Real.sqrt (q.atlasMeasure.real univ))*‖L‖ := by
  have hi : Integrable (fun w => ‖L w‖*((∏ j, (K j : ℝ))*B)) q.atlasMeasure :=
    ((Lp.memLp L).integrable (by norm_num)).norm.mul_const _
  have hbound : ∀ᵐ w ∂q.atlasMeasure,
      ‖q.testWeight π L w*b (q.atlasParam w)‖ ≤ ‖L w‖*((∏ j, (K j : ℝ))*B) := by
    filter_upwards [q.ae_testWeight_bound π K hπ L] with w hw
    rw [Real.norm_eq_abs,abs_mul]
    have hh := mul_le_mul hw (hbB (q.atlasParam w)) (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _ => (K j).coe_nonneg))
    exact hh.trans_eq (by ring)
  have hh := (norm_integral_le_integral_norm
    (fun w => q.testWeight π L w*b (q.atlasParam w))).trans
      (integral_mono_ae
        (q.integrable_testWeight_mul π K hπ (Lp.memLp L) hb).norm hi hbound)
  change |q.pairing π b L| ≤ _ at hh
  rw [integral_mul_const] at hh
  have hc := mul_le_mul_of_nonneg_right (integral_norm_le_lpNorm_two (Lp.memLp L))
    (show 0 ≤ (∏ j, (K j : ℝ))*B from mul_nonneg (Finset.prod_nonneg fun j _ => (K j).coe_nonneg) hB)
  rw [lpNorm_Lp] at hc
  exact (hh.trans hc).trans_eq (by ring)

lemma continuous_pairing (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b : X → ℝ} (hb : BoundedLip b) :
    Continuous (q.pairing π b) := by
  obtain ⟨B,hB⟩ := hb.2
  have hB0 : 0 ≤ B := (abs_nonneg (b (Classical.arbitrary X))).trans (hB _)
  let C : ℝ≥0 := ⟨(∏ j, (K j : ℝ))*B*Real.sqrt (q.atlasMeasure.real univ),by positivity⟩
  apply LipschitzWith.continuous (K := C)
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro L M
  rw [Real.dist_eq,←q.pairing_sub π K hπ hb,dist_eq_norm]
  exact q.abs_pairing_le π K hπ hb hB0 hB (L-M)

lemma pairing_gradient (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {u b : X → ℝ} {Ku : ℝ≥0}
    (hu : LipschitzWith Ku u) (hb : BoundedLip b) :
    q.pairing π b (q.gradient hu) = T b (Fin.cons u π) := by
  rw [←q.testWeight_gradient π K hπ hu hb]
  apply integral_congr_ae
  filter_upwards [(q.memLp_gradientFunction hu).coeFn_toLp] with w hw
  simp only [gradient,testWeight]
  rw [hw]

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_CyclePairing
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

include q in
lemma integerRectifiable : IntegerRectifiable T :=
  ⟨q.chart,q.disjoint,q.current,q.summable,q.action⟩

lemma abs_pairing_gradient_cycle_le (hz : IsCycle T)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b u : X → ℝ} {Kb Ku : ℝ≥0}
    (hb : LipschitzWith Kb b) (hu : LipschitzWith Ku u) :
    |q.pairing π b (q.gradient hu)| ≤
      ((Kb : ℝ)*(∏ j, (K j : ℝ))*Real.sqrt ((MassMeasure.currentMassMeasure hT).real univ))*
        lpNorm u 2 (MassMeasure.currentMassMeasure hT) := by
  have hb' := Foundations.boundedLip_of_lipschitz hb
  have hu' := Foundations.boundedLip_of_lipschitz hu
  rw [q.pairing_gradient π K hπ hu hb']
  change |T b (Matrix.vecCons u π)| ≤ _
  rw [Foundations.IntegerRectifiable.cycle_product_rule q.integerRectifiable hz hb' hu' π
      (fun j => ⟨K j,hπ j⟩),abs_neg]
  have hKs : ∀ j, LipschitzWith (Matrix.vecCons Kb K j) (Matrix.vecCons b π j) := by
    intro j
    refine Fin.cases ?_ (fun a => ?_) j
    · exact hb
    · exact hπ a
  have hh := hT.mass_bound (MassMeasure.currentMassMeasure_controls hT) hu' (Matrix.vecCons Kb K) hKs
  have hm : (∏ j, ((Matrix.vecCons Kb K j : ℝ≥0) : ℝ)) = (Kb : ℝ)*∏ j, (K j : ℝ) := by
    rw [Fin.prod_univ_succ]; rfl
  rw [hm] at hh
  have h1 := integral_norm_le_lpNorm_two (hu'.memLp (μ := MassMeasure.currentMassMeasure hT) 2)
  simp only [Real.norm_eq_abs] at h1
  exact (hh.trans (mul_le_mul_of_nonneg_left h1
    (mul_nonneg Kb.coe_nonneg (Finset.prod_nonneg fun j _ => (K j).coe_nonneg)))).trans_eq (by ring)

lemma pairing_eq_zero_of_gradient_limit (hz : IsCycle T)
    (u : ℕ → X → ℝ) (Ku : ℕ → ℝ≥0) (hu : ∀ j, LipschitzWith (Ku j) (u j))
    (hu0 : Tendsto (fun j => lpNorm (u j) 2 (MassMeasure.currentMassMeasure hT)) atTop (𝓝 0))
    (L : Lp (Euc (k+1)) 2 q.atlasMeasure)
    (hL : Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 L))
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b : X → ℝ} (hb : BoundedLip b) :
    q.pairing π b L = 0 := by
  obtain ⟨Kb,hbK⟩ := hb.1
  have hh : Tendsto (fun j => q.pairing π b (q.gradient (hu j))) atTop (𝓝 0) := by
    have hbound (j : ℕ) : ‖q.pairing π b (q.gradient (hu j))‖ ≤
        ((Kb : ℝ)*(∏ i, (K i : ℝ))*Real.sqrt ((MassMeasure.currentMassMeasure hT).real univ))*
          lpNorm (u j) 2 (MassMeasure.currentMassMeasure hT) := by
      exact q.abs_pairing_gradient_cycle_le hz π K hπ hbK (hu j)
    apply squeeze_zero_norm hbound
    simpa only [mul_zero] using hu0.const_mul
      ((Kb : ℝ)*(∏ j, (K j : ℝ))*Real.sqrt ((MassMeasure.currentMassMeasure hT).real univ))
  exact tendsto_nhds_unique ((q.continuous_pairing π K hπ hb).tendsto L |>.comp hL) hh

lemma testWeight_eq_zero_of_pairings (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) (L : Lp (Euc (k+1)) 2 q.atlasMeasure)
    (hnull : ∀ b, BoundedLip b → q.pairing π b L = 0) :
    q.testWeight π L =ᵐ[q.atlasMeasure] 0 := by
  have hi := (q.memLp_testWeight π K hπ (Lp.memLp L)).integrable (by norm_num)
  have hdom := signed_chart_control_dominates_on q.atlasMeasure (0 : Measure X)
    q.measurable_atlasParam q.ae_mem_atlasDomain q.measurableEmbedding_atlas hi
    (fun b hb => by change |q.pairing π b L| ≤ _; simp [hnull b hb])
  have he : densityPush q.atlasMeasure q.atlasParam (fun w => |q.testWeight π L w|) = 0 :=
    le_antisymm hdom bot_le
  have ht := congrArg (fun μ : Measure X => μ univ) he
  simp only [densityPush,Measure.map_apply q.measurable_atlasParam MeasurableSet.univ,
    preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.coe_zero,Pi.zero_apply,Measure.restrict_univ] at ht
  have hw := (lintegral_eq_zero_iff' hi.aestronglyMeasurable.aemeasurable.abs.ennreal_ofReal).mp ht
  filter_upwards [hw] with w hw
  simpa only [Pi.zero_apply,ENNReal.ofReal_eq_zero,abs_nonpos_iff] using hw

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

lemma vecCons_omitted_rows {n : ℕ} (v : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    Matrix.vecCons v (fun a => (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
      (Equiv.swap 0 j a.succ)) =
    (((1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).updateRow j v).submatrix
      (Equiv.swap 0 j) id) := by
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a
  · simp [Matrix.submatrix_apply,Matrix.updateRow_apply]
  · have hne : Equiv.swap 0 j a.succ ≠ j := by
      intro h
      have he : Equiv.swap 0 j a.succ = Equiv.swap 0 j 0 := by simpa using h
      exact Fin.succ_ne_zero a ((Equiv.swap 0 j).injective he)
    simp [Matrix.submatrix_apply,Matrix.updateRow_apply,hne]

lemma component_zero_of_omitted_det {n : ℕ} (v : Fin (n+1) → ℝ) (j : Fin (n+1))
    (h : Matrix.det (Matrix.vecCons v (fun a =>
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (Equiv.swap 0 j a.succ))) = 0) : v j = 0 := by
  rw [vecCons_omitted_rows,Matrix.det_permute,det_updateRow_identity] at h
  have hh := congrArg abs h
  simp only [abs_mul,abs_unit_intCast,one_mul,abs_zero] at hh
  exact abs_eq_zero.mp hh

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_ClosedLinear
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma exists_inverse_coordinates (i : ℕ) :
    ∃ (F : Fin n → X → ℝ) (K : ℝ≥0), (∀ a, LipschitzWith K (F a)) ∧
      ∀ᵐ z ∂volume.restrict (q.chart i).domain,
        ∀ a, q.covector i (F a) z = (1 : Matrix (Fin n) (Fin n) ℝ) a := by
  obtain ⟨K₁,K₂,hK₁,hK₂⟩ := (q.chart i).bilipschitz
  have hrow : ∀ a y (hy : y ∈ (q.chart i).domain) z (hz : z ∈ (q.chart i).domain),
      |EuclideanSpace.proj a y-EuclideanSpace.proj a z| ≤
        (K₂ : ℝ)*dist ((q.chart i).param ⟨y,hy⟩) ((q.chart i).param ⟨z,hz⟩) := by
    intro a y hy z hz
    have h := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (y-z) a
    have he : |EuclideanSpace.proj a y-EuclideanSpace.proj a z| ≤ dist y z := by
      change |y.ofLp a-z.ofLp a| ≤ ‖y-z‖
      simpa only [Real.norm_eq_abs,PiLp.sub_apply] using h
    exact he.trans (hK₂.le_mul_dist ⟨y,hy⟩ ⟨z,hz⟩)
  obtain ⟨F,hF,hFeq,_⟩ := (q.chart i).exists_inverse_coordinate_tests
    (q.chart i).borel subset_rfl (fun a => EuclideanSpace.proj a) K₂ hrow
  refine ⟨F,K₂,hF,?_⟩
  rw [eventually_all]
  intro a
  have h := (q.chart i).ae_fderivWithin_scalar_eq_linear (q.chart i).borel subset_rfl
    (hF a) (EuclideanSpace.proj a) (hFeq a)
  filter_upwards [h] with z hz
  ext b
  unfold covector
  rw [hz]
  change (EuclideanSpace.single b (1 : ℝ)).ofLp a = (1 : Matrix (Fin n) (Fin n) ℝ) a b
  simp [Matrix.one_apply]

lemma ae_coordinate_density_pos (i : ℕ) :
    ∀ᵐ z ∂q.coordinateMeasure i, 0 < q.density i z := by
  apply (ae_withDensity_iff' (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal).mpr
  exact Eventually.of_forall fun z hz => lt_of_not_ge (fun h => hz (ENNReal.ofReal_eq_zero.mpr h))

lemma ae_multiplicity_ne_zero (i : ℕ) :
    ∀ᵐ z ∂q.coordinateMeasure i, ((q.chart i).multiplicity z : ℝ) ≠ 0 := by
  filter_upwards [q.ae_coordinate_density_pos i] with z hz
  intro he
  simp only [density,he,abs_zero,zero_mul] at hz
  exact lt_irrefl 0 hz

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma eq_zero_of_pairing_null (L : Lp (Euc (k+1)) 2 q.atlasMeasure)
    (hnull : ∀ (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0),
      (∀ j, LipschitzWith (K j) (π j)) → ∀ b, BoundedLip b → q.pairing π b L = 0) :
    L = 0 := by
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_zero (Euc (k+1)) 2 q.atlasMeasure).symm
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  obtain ⟨F,K,hF,hrows⟩ := q.exists_inverse_coordinates i
  have hzero : ∀ᵐ z ∂q.coordinateMeasure i, ∀ a : Fin (k+1),
      q.testWeight (fun j => F (Equiv.swap 0 a j.succ)) L (i,z) = 0 := by
    rw [eventually_all]
    intro a
    have hh := q.testWeight_eq_zero_of_pairings (fun j => F (Equiv.swap 0 a j.succ))
      (fun _ => K) (fun j => hF _) L (hnull _ _ (fun j => hF _))
    exact (measurableEmbedding_prodMk_left i).ae_map_iff.mp (Measure.ae_sum_iff.mp hh i)
  have hrows' := (withDensity_absolutelyContinuous _ (fun z => ENNReal.ofReal (q.density i z))).ae_le hrows
  have hdiff := (withDensity_absolutelyContinuous _ (fun z => ENNReal.ofReal (q.density i z))).ae_le (q.differential i)
  filter_upwards [hzero,hrows',hdiff,q.ae_multiplicity_ne_zero i] with z hz hr hd hθ
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hd.2.2 hd.2.1
  have hJ : Real.sqrt (q.gram i z).det ≠ 0 := (Real.sqrt_pos.mpr hG.det_pos).ne'
  have hraw : rawCovector (q.gram i z) (L (i,z)) = 0 := by
    funext a
    apply component_zero_of_omitted_det _ a
    have hh := hz a
    change ((_ : ℝ)/abs _) * normalizedDet _ _ _ = 0 at hh
    have hh' := (mul_eq_zero.mp hh).resolve_left (div_ne_zero hθ (abs_ne_zero.mpr hθ))
    unfold normalizedDet at hh'
    have he : (fun j : Fin k => q.covector i (F (Equiv.swap 0 a j.succ)) z) =
        fun j => (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (Equiv.swap 0 a j.succ) := by
      funext j
      exact hr _
    rw [he] at hh'
    exact (div_eq_zero_iff.mp hh').resolve_right hJ
  have he := normalize_rawCovector (q.gram i z) hG (L (i,z))
  rw [hraw,Matrix.mulVec_zero] at he
  apply (WithLp.equiv 2 (Fin (k+1) → ℝ)).injective
  exact he.symm

theorem gradient_closable (hz : IsCycle T)
    (u : ℕ → X → ℝ) (Ku : ℕ → ℝ≥0) (hu : ∀ j, LipschitzWith (Ku j) (u j))
    (hu0 : Tendsto (fun j => lpNorm (u j) 2 (MassMeasure.currentMassMeasure hT)) atTop (𝓝 0))
    (L : Lp (Euc (k+1)) 2 q.atlasMeasure)
    (hL : Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 L)) : L = 0 := by
  apply q.eq_zero_of_pairing_null L
  intro π K hπ b hb
  exact q.pairing_eq_zero_of_gradient_limit hz u Ku hu hu0 L hL π K hπ hb

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma norm_value {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ‖value (hT := hT) hu‖ = lpNorm u 2 (MassMeasure.currentMassMeasure hT) := by
  rw [value,Lp.norm_toLp,toReal_eLpNorm hu.continuous.aestronglyMeasurable]

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Completion
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closedGraph_isClosed : IsClosed (q.closedGraph : Set q.GraphAmbient) :=
  q.lipschitzGraph.isClosed_topologicalClosure

instance instCompleteSpaceSubtypeGraphAmbientMemSubmoduleRealSobolev : CompleteSpace q.Sobolev := q.closedGraph_isClosed.completeSpace_coe

lemma exists_lipschitz_approximants (P : q.Sobolev) :
    ∃ (u : ℕ → X → ℝ) (K : ℕ → ℝ≥0) (hu : ∀ j, LipschitzWith (K j) (u j)),
      Tendsto (fun j => q.graphPoint (hu j)) atTop (𝓝 (P : q.GraphAmbient)) := by
  have hp : (P : q.GraphAmbient) ∈ closure (q.lipschitzGraph : Set q.GraphAmbient) := P.property
  obtain ⟨p,hp,hlim⟩ := mem_closure_iff_seq_limit.mp hp
  choose u K hu he using hp
  refine ⟨u,K,hu,?_⟩
  have heq : p = fun j => q.graphPoint (hu j) := funext he
  rw [←heq]
  exact hlim

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closedGraph_zero_value (hz : IsCycle T) (P : q.Sobolev)
    (hP : q.valueProjection P = 0) : q.gradientProjection P = 0 := by
  obtain ⟨u,K,hu,hlim⟩ := q.exists_lipschitz_approximants P
  have hv := (q.valueProjection.continuous.tendsto (P : q.GraphAmbient)).comp hlim
  have hg := (q.gradientProjection.continuous.tendsto (P : q.GraphAmbient)).comp hlim
  simp only [Function.comp_def,q.valueProjection_graphPoint,hP] at hv
  simp only [Function.comp_def,q.gradientProjection_graphPoint] at hg
  have hn := hv.norm
  simp only [norm_zero,norm_value] at hn
  exact q.gradient_closable hz u K hu hn _ hg

lemma closedGraph_value_injective (hz : IsCycle T) :
    Function.Injective (fun P : q.Sobolev => q.valueProjection P) := by
  intro P Q he
  change q.valueProjection P = q.valueProjection Q at he
  have hd : q.valueProjection (↑(P-Q) : q.GraphAmbient) = 0 := by
    change q.valueProjection ((P : q.GraphAmbient)-(Q : q.GraphAmbient)) = 0
    rw [map_sub,he,sub_self]
  have hg := q.closedGraph_zero_value hz (P-Q) hd
  have heq : (↑(P-Q) : q.GraphAmbient) = 0 := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact hd
    · exact hg
  exact sub_eq_zero.mp (Subtype.ext heq)

lemma inclusion_injective (hz : IsCycle T) : Function.Injective q.inclusion :=
  q.closedGraph_value_injective hz

lemma closedGradient_closed (u : Lp ℝ 2 (MassMeasure.currentMassMeasure hT))
    (G : Lp (Euc (k+1)) 2 q.atlasMeasure) (P : ℕ → q.Sobolev)
    (hu : Tendsto (fun j => q.inclusion (P j)) atTop (𝓝 u))
    (hG : Tendsto (fun j => q.closedGradient (P j)) atTop (𝓝 G)) :
    ∃ Q : q.Sobolev, q.inclusion Q = u ∧ q.closedGradient Q = G := by
  have hpair := hu.prodMk_nhds hG
  have hh := ((WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) (Lp (Euc (k+1)) 2 q.atlasMeasure)).symm.continuous.tendsto (u,G)).comp hpair
  have hh' : Tendsto (fun j => (P j : q.GraphAmbient)) atTop
      (𝓝 (WithLp.toLp 2 (u,G))) := hh
  have hm : WithLp.toLp 2 (u,G) ∈ q.closedGraph :=
    q.closedGraph_isClosed.mem_of_tendsto hh' (Eventually.of_forall fun j => (P j).property)
  exact ⟨⟨_,hm⟩,rfl,rfl⟩

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_ClosedChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma composeValue_ae {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) :
    q.composeValue hF f =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => F (f x)) := by
  filter_upwards [Lp.coeFn_add ((hF.sub (LipschitzWith.const (F 0))).compLp (by simp) f)
    (value (hT := hT) (LipschitzWith.const (F 0))),
    (hF.sub (LipschitzWith.const (F 0))).coeFn_compLp (by simp) f,
    ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const (F 0))).memLp
      (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x ha hb hc
  rw [composeValue,constant,q.inclusion_lipSobolev,ha]
  change ((hF.sub (LipschitzWith.const (F 0))).compLp (by simp) f) x + (value (hT := hT) (LipschitzWith.const (F 0))) x = _
  change (value (hT := hT) (LipschitzWith.const (F 0))) x = F 0 at hc
  rw [hb,hc]
  simp only [Function.comp_apply,sub_add_cancel]

lemma continuous_composeValue {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F) :
    Continuous (q.composeValue hF) :=
  ((hF.sub (LipschitzWith.const (F 0))).continuous_compLp (by simp)).add continuous_const

lemma composeValue_value {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.composeValue hF (value hu) = value (hF.comp hu) := by
  apply Lp.ext
  filter_upwards [q.composeValue_ae hF (value hu),
    ((Foundations.boundedLip_of_lipschitz hu).memLp (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp,
    ((Foundations.boundedLip_of_lipschitz (hF.comp hu)).memLp
      (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x ha hb hc
  exact ha.trans ((congrArg F hb).trans hc.symm)

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_AbsoluteValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

lemma absApprox_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (absApprox ε) (absApproxDeriv ε t) t := by
  have hh : 0 < t^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have hd := (((hasDerivAt_id t).pow 2).add_const (ε^2)).sqrt hh.ne'
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp [absApproxDeriv]
    norm_num
    ring

lemma absApproxDeriv_bound {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |absApproxDeriv ε t| ≤ 1 := by
  have hh : 0 < t^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  dsimp [absApproxDeriv]
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_one (Real.sqrt_pos.mpr hh)).mpr
  rw [←Real.sqrt_sq_eq_abs t]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

lemma absApprox_lipschitz {ε : ℝ} (hε : 0 < ε) : LipschitzWith 1 (absApprox ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (absApprox_hasDerivAt hε t).differentiableAt)
  intro t
  rw [←NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_one,(absApprox_hasDerivAt hε t).deriv,Real.norm_eq_abs]
  exact absApproxDeriv_bound hε t

lemma continuous_absApproxDeriv {ε : ℝ} (hε : 0 < ε) : Continuous (absApproxDeriv ε) := by
  change Continuous (fun t : ℝ => t / Real.sqrt (t^2+ε^2))
  apply continuous_id.div (Real.continuous_sqrt.comp (continuous_id.pow 2 |>.add continuous_const))
  intro t
  exact (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))).ne'

lemma absApprox_error {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : abs (absApprox ε t-|t|) ≤ ε := by
  have hl : |t| ≤ absApprox ε t := by
    rw [←Real.sqrt_sq_eq_abs t]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  have hu : absApprox ε t ≤ |t|+ε := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [add_sq,sq_abs]
    nlinarith [abs_nonneg t]
  linarith

lemma absApproxDeriv_tendsto {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hepos : ∀ j, 0 < e j) (t : ℝ) :
    Tendsto (fun j => absApproxDeriv (e j) t) atTop (𝓝 (t / |t|)) := by
  by_cases ht : t = 0
  · subst t
    rw [zero_div]
    apply tendsto_const_nhds.congr
    intro index
    dsimp [absApproxDeriv]
    rw [zero_pow (by decide : 2 ≠ 0),zero_add,Real.sqrt_sq (hepos index).le,zero_div]
  have hab : 0 < |t| := abs_pos.mpr ht
  have hh := (tendsto_const_nhds (x := t) (f := (atTop : Filter ℕ))).div ((tendsto_const_nhds.add (he.pow 2)).sqrt)
    (show Real.sqrt (t^2+(0:ℝ)^2) ≠ 0 by simpa only [zero_pow (by decide : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs] using hab.ne')
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs] at hh
  exact hh

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Atlas
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.instCompleteSpaceSubtypeGraphAmbientMemSubmoduleRealSobolev _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma integral_atlas {f : ℕ × Euc n → ℝ} (hf : Integrable f q.atlasMeasure) :
    ∫ w, f w ∂q.atlasMeasure = ∑' i, ∫ z, q.density i z*f (i,z) ∂volume.restrict (q.chart i).domain := by
  rw [atlasMeasure,integral_sum_measure hf]
  apply tsum_congr
  intro i
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i _),smul_eq_mul]

end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings
lemma dot_mulVec_sqrt_cross {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (u v : Fin n → ℝ) :
    u ⬝ᵥ P.mulVec v = (CFC.sqrt P).mulVec u ⬝ᵥ (CFC.sqrt P).mulVec v := by
  have hsym : (CFC.sqrt P).transpose = CFC.sqrt P :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P).posSemidef.isHermitian).eq
  conv_lhs => rw [← CFC.sq_sqrt P hP.nonneg,pow_two, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma ae_normalizedCovector_inner (i : ℕ) (u v : X → ℝ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      inner ℝ (q.normalizedCovector i u z) (q.normalizedCovector i v z) =
        q.covector i u z ⬝ᵥ (q.gram i z)⁻¹.mulVec (q.covector i v z) := by
  filter_upwards [q.differential i] with z hz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  simp only [normalizedCovector,EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  rw [dotProduct_comm]
  exact (dot_mulVec_sqrt_cross _ hG.inv.posSemidef _ _).symm
end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_ChainSet
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma sobolev_tendsto {P : ℕ → q.Sobolev} {Q : q.Sobolev}
    (hv : Tendsto (fun j => q.inclusion (P j)) atTop (𝓝 (q.inclusion Q)))
    (hg : Tendsto (fun j => q.closedGradient (P j)) atTop (𝓝 (q.closedGradient Q))) :
    Tendsto P atTop (𝓝 Q) := by
  apply tendsto_subtype_rng.mpr
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) (Lp (Euc (k+1)) 2 q.atlasMeasure)).symm.continuous.tendsto
      (q.inclusion Q,q.closedGradient Q)).comp (hv.prodMk_nhds hg)

lemma closed_chain_in_closed {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) (hcF : Continuous F')
    {C : ℝ} (hC : 0 ≤ C) (hbF : ∀ t, |F' t| ≤ C) (P : q.Sobolev)
    {S : Set q.Sobolev} (hS : IsClosed S)
    (hmem : ∀ (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u), q.lipSobolev (hF.comp hu) ∈ S) :
    ∃ Q : q.Sobolev, Q ∈ S ∧
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => F' ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  obtain ⟨u,K,hu,hl⟩ := q.exists_lipschitz_approximants P
  have hv := (q.valueProjection.continuous.tendsto (P : q.GraphAmbient)).comp hl
  have hg := (q.gradientProjection.continuous.tendsto (P : q.GraphAmbient)).comp hl
  change Tendsto (fun j => value (hu j)) atTop (𝓝 (q.inclusion P)) at hv
  change Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 (q.closedGradient P)) at hg
  obtain ⟨s,hs,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hnames : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ∀ j,
      (value (hT := hT) (hu (s j))) x = u (s j) x := by
    apply ae_all_iff.mpr
    intro j
    exact ((Foundations.boundedLip_of_lipschitz (hu (s j))).memLp 2).coeFn_toLp
  have hae' : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT,
      Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x)) := by
    filter_upwards [hae,hnames] with x hx he
    simpa only [he] using hx
  let b (j : ℕ) (w : ℕ × Euc (k+1)) := F' (u (s j) (q.atlasParam w))
  let c (w : ℕ × Euc (k+1)) := F' ((q.inclusion P) (q.atlasParam w))
  have hb (j : ℕ) : AEStronglyMeasurable (b j) q.atlasMeasure :=
    (hcF.measurable.comp ((hu (s j)).continuous.measurable.comp q.measurable_atlasParam)).aestronglyMeasurable
  have hc : AEStronglyMeasurable c q.atlasMeasure :=
    hcF.comp_aestronglyMeasurable ((Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving)
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C :=
    Eventually.of_forall fun point => hbF (u (s j) (q.atlasParam point))
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C :=
    Eventually.of_forall fun point => hbF ((q.inclusion P) (q.atlasParam point))
  have hbc : ∀ᵐ w ∂q.atlasMeasure, Tendsto (fun j => b j w) atTop (𝓝 (c w)) := by
    have ha : ∀ᵐ w ∂q.atlasMeasure,
        Tendsto (fun j => u (s j) (q.atlasParam w)) atTop (𝓝 ((q.inclusion P) (q.atlasParam w))) := by
      apply ae_of_ae_map (μ := q.atlasMeasure) (p := fun x =>
        Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x))) q.measurable_atlasParam.aemeasurable
      rwa [q.map_atlasMeasure]
    filter_upwards [ha] with w hw
    exact (hcF.tendsto _).comp hw
  have hgl := ClosedCalculus.mulLp_tendsto hb hc hC hbC hcC hbc (hg.comp hs.tendsto_atTop)
  have he (j : ℕ) : ClosedCalculus.mulLp (hb j) (hbC j) (q.gradient (hu (s j))) =
      q.gradient (hF.comp (hu (s j))) := by
    apply Lp.ext
    exact (ClosedCalculus.mulLp_ae (hb j) (hbC j) _).trans (q.gradient_chain_ae (hu (s j)) hF hdF).symm
  simp only [Function.comp_apply,he] at hgl
  have hvl := (q.continuous_composeValue hF).tendsto (q.inclusion P) |>.comp (hv.comp hs.tendsto_atTop)
  simp only [Function.comp_def,q.composeValue_value] at hvl
  obtain ⟨Q,hQ,hG⟩ := q.closedGradient_closed (q.composeValue hF (q.inclusion P))
    (ClosedCalculus.mulLp hc hcC (q.closedGradient P))
    (fun j => q.lipSobolev (hF.comp (hu (s j)))) hvl hgl
  refine ⟨Q,?_,?_,?_⟩
  · apply hS.mem_of_tendsto (q.sobolev_tendsto (P := fun j => q.lipSobolev (hF.comp (hu (s j)))) (by simpa only [q.inclusion_lipSobolev,hQ] using hvl) (by simpa only [q.closedGradient_lipSobolev,hG] using hgl))
    exact Eventually.of_forall fun j => hmem _ _ (hu (s j))
  · rw [hQ]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_chain_uniform_in_closed {F D : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hD : Measurable D) {C : ℝ} (hC : 0 ≤ C) (hbD : ∀ t, |D t| ≤ C)
    (Fj Dj : ℕ → ℝ → ℝ) (K : ℕ → ℝ≥0)
    (hFj : ∀ j, LipschitzWith (K j) (Fj j))
    (hdj : ∀ j t, HasDerivAt (Fj j) (Dj j t) t)
    (hcj : ∀ j, Continuous (Dj j)) (hbj : ∀ j t, |Dj j t| ≤ C)
    (hdlim : ∀ t, Tendsto (fun j => Dj j t) atTop (𝓝 (D t)))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (he : ∀ j t, |Fj j t-F t| ≤ a j) (P : q.Sobolev)
    {S : Set q.Sobolev} (hclosed : IsClosed S)
    (hmem : ∀ j (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u), q.lipSobolev ((hFj j).comp hu) ∈ S) :
    ∃ Q : q.Sobolev, Q ∈ S ∧
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => D ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  choose Q hQS hQ hG using (fun j => q.closed_chain_in_closed (hFj j) (hdj j) (hcj j) hC (hbj j) P hclosed (hmem j))
  let b (j : ℕ) (w : ℕ × Euc (k+1)) := Dj j ((q.inclusion P) (q.atlasParam w))
  let c (w : ℕ × Euc (k+1)) := D ((q.inclusion P) (q.atlasParam w))
  have hpm := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hb (j : ℕ) : AEStronglyMeasurable (b j) q.atlasMeasure := (hcj j).comp_aestronglyMeasurable hpm
  have hc : AEStronglyMeasurable c q.atlasMeasure := (hD.comp_aemeasurable hpm.aemeasurable).aestronglyMeasurable
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C := Eventually.of_forall fun _ => hbj j _
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C := Eventually.of_forall fun _ => hbD _
  have hgl := ClosedCalculus.mulLp_tendsto hb hc hC hbC hcC
    (Eventually.of_forall fun point => hdlim ((q.inclusion P) (q.atlasParam point)))
    (tendsto_const_nhds (x := q.closedGradient P))
  have heG (j : ℕ) : ClosedCalculus.mulLp (hb j) (hbC j) (q.closedGradient P) = q.closedGradient (Q j) := by
    apply Lp.ext
    exact (ClosedCalculus.mulLp_ae (hb j) (hbC j) _).trans (hG j).symm
  simp only [heG] at hgl
  let V := q.composeValue hF (q.inclusion P)
  have hv : Tendsto (fun j => q.inclusion (Q j)) atTop (𝓝 V) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (g := fun j => a j*‖value (hT := hT) (LipschitzWith.const (1:ℝ))‖)
    · intro j
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (q.inclusion (Q j)) V,hQ j,q.composeValue_ae hF (q.inclusion P),
        ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const (1:ℝ))).memLp
          (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x hs hq hv h1
      change (value (hT := hT) (LipschitzWith.const (1:ℝ)) : X → ℝ) x = 1 at h1
      rw [hs,Pi.sub_apply,hq,hv,h1,Real.norm_eq_abs,norm_one,mul_one]
      exact he j _
    · simpa only [zero_mul] using ha.mul_const ‖value (hT := hT) (LipschitzWith.const (1:ℝ))‖
  obtain ⟨R,hR,hRG⟩ := q.closedGradient_closed V (ClosedCalculus.mulLp hc hcC (q.closedGradient P)) Q hv hgl
  refine ⟨R,?_,?_,?_⟩
  · apply hclosed.mem_of_tendsto (q.sobolev_tendsto (P := Q) (by simpa only [hR] using hv) (by simpa only [hRG] using hgl))
    exact Eventually.of_forall hQS
  · rw [hR]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hRG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_SpatialVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma nonnegative_mem_closed (hz : IsCycle T) {S : Set q.Sobolev} (hS : IsClosed S)
    (hmem : ∀ (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u),
      (∀ x, 0 ≤ u x) → q.lipSobolev hu ∈ S)
    (P : q.Sobolev) (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x) :
    P ∈ S := by
  let e (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hepos (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (t : ℝ) : abs (t/|t|) ≤ 1 := by
    rw [abs_div,abs_abs]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_self (abs_pos.mpr ht).ne']
  obtain ⟨Q,hQS,hQ,_⟩ := q.closed_chain_uniform_in_closed (F := abs) (D := fun t => t/|t|)
    (show LipschitzWith 1 abs from LipschitzWith.of_dist_le_mul (fun x y => by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y))
    (measurable_id.div measurable_id.abs) (by norm_num : (0:ℝ) ≤ 1) hb
    (fun j => absApprox (e j)) (fun j => absApproxDeriv (e j)) (fun _ => 1)
    (fun j => absApprox_lipschitz (hepos j)) (fun j => absApprox_hasDerivAt (hepos j))
    (fun j => continuous_absApproxDeriv (hepos j)) (fun j => absApproxDeriv_bound (hepos j))
    (absApproxDeriv_tendsto he hepos) e he (fun j => absApprox_error (hepos j).le) P hS
    (fun j u K hu => hmem _ _ _ (fun x => Real.sqrt_nonneg _))
  have hQP : Q = P := q.inclusion_injective hz (Lp.ext (by
    filter_upwards [hQ,hP] with x hx hp
    exact hx.trans (abs_of_nonneg hp)))
  rwa [hQP] at hQS

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_ClosedInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma continuous_radialDefect (o : X) : Continuous (q.radialDefect o) := by
  apply Continuous.add
  · exact continuous_const.inner ((Lp.isometry_compMeasurePreserving q.atlas_preserving).continuous.comp q.inclusion.continuous)
  · exact continuous_const.inner q.closedGradient.continuous

lemma radialDefect_eq_integral (o : X) (P : q.Sobolev) :
    q.radialDefect o P = ∫ w, q.radialA o w*q.inclusion P (q.atlasParam w)+
      inner ℝ (q.radialB o w) (q.closedGradient P w) ∂q.atlasMeasure := by
  unfold radialDefect
  rw [L2.inner_def,L2.inner_def,←integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [(q.memLp_radialA o).coeFn_toLp,(q.memLp_radialB o).coeFn_toLp,
    Lp.coeFn_compMeasurePreserving (q.inclusion P) q.atlas_preserving] with w ha hb hp
  rw [ha,hb,hp,Function.comp_apply]
  simp only [RCLike.inner_apply,conj_trivial,mul_comm]
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_RadialIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma radial_completed_pointwise {n g r d h : ℝ} (hn : 0 ≤ n) (hg : 0 ≤ g)
    (hd : d ≤ 1) :
    n*g*d+r*h-n/4*r^2*g ≤ n*(1-r*Real.sqrt (1-d))*g+r*h := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hd)
  have he : n*(1-r*Real.sqrt (1-d))*g+r*h -
      (n*g*d+r*h-n/4*r^2*g) = n*g*(Real.sqrt (1-d)-r/2)^2 := by
    nlinarith [congrArg (fun x : ℝ => n*g*x) hs]
  exact sub_nonneg.mp (he.symm ▸ mul_nonneg (mul_nonneg hn hg) (sq_nonneg _))

lemma memLp_radialCompletedA (o : X) :
    MemLp (fun w => (k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) w‖^2-
      (k+1:ℝ)/4*dist o (q.atlasParam w)^2) 2 q.atlasMeasure := by
  have hd := (Lp.aestronglyMeasurable (q.gradient (LipschitzWith.dist_right o))).norm.pow 2
  have hr : AEStronglyMeasurable (fun w => dist o (q.atlasParam w)) q.atlasMeasure :=
    ((LipschitzWith.dist_right o).continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable
  apply MemLp.of_bound ((aestronglyMeasurable_const.mul hd).sub (aestronglyMeasurable_const.mul (hr.pow 2)))
    ((k+1:ℝ)+(k+1:ℝ)/4*(Metric.diam (univ : Set X))^2)
  filter_upwards [q.ae_gradient_bound (LipschitzWith.dist_right o)] with w hw
  rw [Real.norm_eq_abs]
  apply (abs_sub _ _).trans
  simp only [Pi.mul_apply,Pi.pow_apply] at *
  rw [abs_of_nonneg (by positivity : 0 ≤ (k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) w‖^2),
    abs_of_nonneg (by positivity : 0 ≤ (k+1:ℝ)/4*dist o (q.atlasParam w)^2)]
  have hm := radius_bound o (q.atlasParam w)
  have hs : ‖q.gradient (LipschitzWith.dist_right o) w‖^2 ≤ 1 := by
      norm_num only [NNReal.coe_one] at hw
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hw
  apply add_le_add
  · calc
      _ ≤ (k+1:ℝ)*1 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := mul_one _
  · gcongr

lemma completed_radial (o : X) (P : q.Sobolev)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hr : q.radialDefect o P ≤ 0) :
    (∫ w, ((k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) w‖^2-
      (k+1:ℝ)/4*dist o (q.atlasParam w)^2)*q.inclusion P (q.atlasParam w)+
      dist o (q.atlasParam w)*inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient P w) ∂q.atlasMeasure) ≤ 0 := by
  have hp := (Lp.memLp (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hB : Integrable (fun w => inner ℝ (q.radialB o w) (q.closedGradient P w)) q.atlasMeasure := by
    apply (L2.integrable_inner (𝕜 := ℝ) ((q.memLp_radialB o).toLp _) (q.closedGradient P)).congr
    filter_upwards [(q.memLp_radialB o).coeFn_toLp] with w hw
    rw [hw]
  have hB' : Integrable (fun w => dist o (q.atlasParam w)*inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient P w)) q.atlasMeasure := by
    simpa only [radialB,real_inner_smul_left] using hB
  apply le_trans (integral_mono_ae (((q.memLp_radialCompletedA o).integrable_mul hp).add hB')
    (((q.memLp_radialA o).integrable_mul hp).add hB) ?_) ?_
  · filter_upwards [q.atlas_preserving.quasiMeasurePreserving.ae hP,q.ae_gradient_bound (LipschitzWith.dist_right o)] with w hw hb
    have hd : ‖q.gradient (LipschitzWith.dist_right o) w‖^2 ≤ 1 := by
      norm_num only [NNReal.coe_one] at hb
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hb
    dsimp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,radialA,radialB]
    rw [real_inner_smul_left]
    convert radial_completed_pointwise (n := (k+1:ℝ)) (r := dist o (q.atlasParam w))
      (h := inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient P w)) (by positivity) hw hd using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply]
    rw [←q.radialDefect_eq_integral]
    exact hr
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
lemma scalar_added_cancel {A B C D κ β n : ℝ} (hr : A ≤ 0)
    (he : 4*β*B+n*C=n*D) : κ^2*(A+β*B+n/4*C) ≤ κ^2*n/4*D := by
  have hh : β*B+n/4*C=n/4*D := by linarith
  calc
    _ = κ^2*(A+(β*B+n/4*C)) := by ring
    _ ≤ κ^2*(n/4*D) := by rw [hh]; exact mul_le_mul_of_nonneg_left (add_le_of_nonpos_left hr) (sq_nonneg κ)
    _ = _ := by ring
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma integrable_completedExpression (o : X) (G : q.Sobolev) :
    Integrable (q.completedExpression o G) q.atlasMeasure := by
  have hp := (Lp.memLp (q.inclusion G)).comp_measurePreserving q.atlas_preserving
  have hB : Integrable (fun z => inner ℝ (q.radialB o z) (q.closedGradient G z)) q.atlasMeasure := by
    apply (L2.integrable_inner (𝕜 := ℝ) ((q.memLp_radialB o).toLp _) (q.closedGradient G)).congr
    filter_upwards [(q.memLp_radialB o).coeFn_toLp] with z hz
    rw [hz]
  have hB' : Integrable (fun z => dist o (q.atlasParam z)*inner ℝ (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient G z)) q.atlasMeasure := by
    simpa only [radialB,real_inner_smul_left] using hB
  exact ((q.memLp_radialCompletedA o).integrable_mul hp).add hB'

lemma added_energy_integral (o : X) (v G Q : q.Sobolev) {β κ : ℝ}
    {E : ℕ × Euc (k+1) → ℝ}
    (hE : E =ᵐ[q.atlasMeasure] (fun z => κ^2*(q.completedExpression o G z+
      β*inner ℝ (q.closedGradient v z) (q.closedGradient Q z)+
      (k+1:ℝ)/4*(q.inclusion v (q.atlasParam z)*q.inclusion Q (q.atlasParam z)))))
    (hr : (∫ z, q.completedExpression o G z ∂q.atlasMeasure) ≤ 0)
    (heuler : 4*β*inner ℝ (q.closedGradient v) (q.closedGradient Q)+
      (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion Q) =
      (k+1:ℝ)*(∫ x, (q.inclusion v x)^(1+4*β)*q.inclusion Q x ∂MassMeasure.currentMassMeasure hT)) :
    Integrable E q.atlasMeasure ∧
      (∫ z, E z ∂q.atlasMeasure) ≤ κ^2*(k+1:ℝ)/4*
        (∫ x, (q.inclusion v x)^(1+4*β)*q.inclusion Q x ∂MassMeasure.currentMassMeasure hT) := by
  have hpair := L2.integrable_inner (𝕜 := ℝ) (q.closedGradient v) (q.closedGradient Q)
  have hval : Integrable (fun x => q.inclusion v x*q.inclusion Q x) (MassMeasure.currentMassMeasure hT) :=
    (Lp.memLp (q.inclusion v)).integrable_mul (Lp.memLp (q.inclusion Q))
  have hm := q.atlas_preserving.integrable_comp_of_integrable hval
  change Integrable (fun z => q.inclusion v (q.atlasParam z)*q.inclusion Q (q.atlasParam z)) q.atlasMeasure at hm
  have hi := (((q.integrable_completedExpression o G).add (hpair.const_mul β)).add
    (hm.const_mul ((k+1:ℝ)/4))).const_mul (κ^2)
  refine ⟨hi.congr hE.symm,?_⟩
  have hi1 : Integrable (fun z => q.completedExpression o G z+
      β*inner ℝ (q.closedGradient v z) (q.closedGradient Q z)) q.atlasMeasure :=
    (q.integrable_completedExpression o G).add (hpair.const_mul β)
  rw [integral_congr_ae hE,integral_const_mul,integral_add hi1 (hm.const_mul _),
    integral_add (q.integrable_completedExpression o G) (hpair.const_mul β),
    integral_const_mul,integral_const_mul,←L2.inner_def]
  have hmap : (∫ z, q.inclusion v (q.atlasParam z)*q.inclusion Q (q.atlasParam z) ∂q.atlasMeasure) =
      inner ℝ (q.inclusion v) (q.inclusion Q) := by
    have hmap := integral_map (μ := q.atlasMeasure)
      (f := fun x => q.inclusion v x*q.inclusion Q x)
      q.atlas_preserving.measurable.aemeasurable
      (by rw [q.atlas_preserving.map_eq]; exact hval.aestronglyMeasurable)
    rw [q.atlas_preserving.map_eq] at hmap
    rw [←hmap,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [RCLike.inner_apply,conj_trivial]
    exact mul_comm _ _
  rw [hmap]
  exact scalar_added_cancel hr heuler
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Profile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped RealInnerProductSpace

namespace CAT0Fillings.ChartGeometry

lemma chord_added_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R V : E) (n β κ r u A f df : ℝ) (hn : n*β = 1+2*β) :
    κ^2*(n*(u^2*A^2*f)*‖R‖^2+
      r*inner ℝ R ((κ*u^2*A^3*df) • R+(u*A^2*((2+2*β)*f+β*(κ*r*A)*df)) • V)+
      inner ℝ V ((β*(2*r*u*A^2*f+κ*r^2*u*A^3*df)) • R+
        (β*r^2*A^2*((1+2*β)*f+β*(κ*r*A)*df)) • V)) =
      (n*f+(κ*r*A)*df)*‖(κ*u*A) • R+(κ*β*r*A) • V‖^2 := by
  rw [norm_add_sq_real]
  simp only [inner_add_right,real_inner_smul_right,real_inner_smul_left,
    real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simp only [real_inner_comm V R]
  linear_combination (norm := (simp only [real_inner_comm V R]; ring)) -(κ^2*r*A^2*f*(2*u*inner ℝ R V+β*r*‖V‖^2))*hn

lemma profile_powers {u β : ℝ} (hu : 0 < u) :
    u^(1+β) = u*u^β ∧ u^(2+2*β) = u^2*(u^β)^2 ∧
    u^(2+3*β) = u^2*(u^β)^3 ∧ u^(1+2*β) = u*(u^β)^2 ∧
    u^(1+3*β) = u*(u^β)^3 ∧ u^(2*β) = (u^β)^2 := by
  have h2 : u^(2*β) = (u^β)^2 := by rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  have h3 : u^(3*β) = (u^β)^3 := by rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  simp only [Real.rpow_add hu,Real.rpow_one,Real.rpow_two,h2,h3,and_self]
end CAT0Fillings.ChartGeometry
end

section
open scoped RealInnerProductSpace

namespace CAT0Fillings.Conformal
lemma radial_profile_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R V : E) {n β κ r u : ℝ} (f : ℝ → ℝ) (hu : 0 < u) (hn : n*β = 1+2*β) :
    κ^2*(n*(u^(2+2*β)*f (κ*r*u^β))*‖R‖^2+
      r*inner ℝ R (profileRD 0 (2+2*β) β κ f r u • R+profileZD 0 (2+2*β) β κ f r u • V)+
      β*inner ℝ V (profileRD 2 (1+2*β) β κ f r u • R+profileZD 2 (1+2*β) β κ f r u • V)) =
      (n*f (κ*r*u^β)+(κ*r*u^β)*deriv f (κ*r*u^β))*
        ‖(κ*u^(1+β)) • R+(κ*β*r*u^β) • V‖^2 := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := ChartGeometry.profile_powers (β := β) hu
  have h7 : u^(3*β) = (u^β)^3 := by rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  have hg : profileRD 0 (2+2*β) β κ f r u • R+profileZD 0 (2+2*β) β κ f r u • V =
      (κ*u^2*(u^β)^3*deriv f (κ*r*u^β)) • R+
      (u*(u^β)^2*((2+2*β)*f (κ*r*u^β)+β*(κ*r*u^β)*deriv f (κ*r*u^β))) • V := by
    simp only [profileRD,profileZD,Nat.cast_zero,pow_zero,zero_mul,zero_add,
      mul_one,show (2:ℝ)+2*β+β=2+3*β by ring,
      show (2:ℝ)+2*β-1=1+2*β by ring,show (2:ℝ)+3*β-1=1+3*β by ring,h3,h4,h5]
    congr 1 <;> congr 1 <;> ring
  have hp : β • (profileRD 2 (1+2*β) β κ f r u • R+profileZD 2 (1+2*β) β κ f r u • V) =
      (β*(2*r*u*(u^β)^2*f (κ*r*u^β)+κ*r^2*u*(u^β)^3*deriv f (κ*r*u^β))) • R+
      (β*r^2*(u^β)^2*((1+2*β)*f (κ*r*u^β)+β*(κ*r*u^β)*deriv f (κ*r*u^β))) • V := by
    simp only [profileRD,profileZD,Nat.cast_ofNat,show 2-1=(1:ℕ) by rfl,pow_one,
      show (1:ℝ)+2*β+β=1+3*β by ring,show (1:ℝ)+2*β-1=2*β by ring,
      show (1:ℝ)+3*β-1=3*β by ring,h4,h5,h6,h7,smul_add,smul_smul]
    congr 1 <;> congr 1 <;> ring
  rw [hg]
  have hi := real_inner_smul_right V
    (profileRD 2 (1+2*β) β κ f r u • R+profileZD 2 (1+2*β) β κ f r u • V) β
  rw [←hi,hp,h1,h2]
  simpa only [mul_assoc] using ChartGeometry.chord_added_pointwise R V n β κ r u (u^β)
    (f (κ*r*u^β)) (deriv f (κ*r*u^β)) hn
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_TestIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Conformal
lemma radial_profile_complete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R V : E) {n β κ r u : ℝ} (f : ℝ → ℝ) (hu : 0 ≤ u) (hb : 0 < β)
    (hn : n*β = 1+2*β) :
    κ^2*(n*(u^(2+2*β)*f (κ*r*u^β))*‖R‖^2+
      r*inner ℝ R (profileGradient 0 (2+2*β) β κ f r u R V)+
      β*inner ℝ V (profileGradient 2 (1+2*β) β κ f r u R V)) =
      (n*f (κ*r*u^β)+(κ*r*u^β)*deriv f (κ*r*u^β))*
        ‖(κ*u^(1+β)) • R+(κ*β*r*u^β) • V‖^2 := by
  rcases hu.eq_or_lt with hu|hu
  · subst u
    simp [profileGradient,Real.zero_rpow hb.ne',Real.zero_rpow (by linarith : 1+β ≠ 0),
      Real.zero_rpow (by linarith : 2+2*β ≠ 0)]
  · simp only [profileGradient,ite_eq_left hu]
    exact radial_profile_algebra R V f hu hn
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Conformal
lemma radial_value_cancel {u β r f : ℝ} (hu : 0 ≤ u) (hb : 0 < β) :
    u*(r^2*u^(1+2*β)*f) = r^2*(u^(2+2*β)*f) := by
  have he : u*u^(1+2*β) = u^(2+2*β) := by
    conv_lhs => lhs; rw [←Real.rpow_one u]
    rw [←Real.rpow_add' hu (by linarith : 1+(1+2*β) ≠ 0)]
    congr 1
    ring
  calc
    _ = r^2*(u*u^(1+2*β))*f := by ring
    _ = _ := by rw [he]; ring
lemma completed_profile_cancel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R V : E) {n β κ r u : ℝ} (f : ℝ → ℝ) (hu : 0 ≤ u) (hb : 0 < β)
    (hn : n*β = 1+2*β) :
    (n*f (κ*r*u^β)+(κ*r*u^β)*deriv f (κ*r*u^β))*
        ‖(κ*u^(1+β)) • R+(κ*β*r*u^β) • V‖^2 =
    κ^2*((n*‖R‖^2-n/4*r^2)*(u^(2+2*β)*f (κ*r*u^β))+
      r*inner ℝ R (profileGradient 0 (2+2*β) β κ f r u R V)+
      β*inner ℝ V (profileGradient 2 (1+2*β) β κ f r u R V)+
      n/4*(u*(r^2*u^(1+2*β)*f (κ*r*u^β)))) := by
  rw [←radial_profile_complete R V f hu hb hn,radial_value_cancel hu hb]
  ring
end CAT0Fillings.Conformal
namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma added_tests_identity (o : X) (v G Q : q.Sobolev) {κ β : ℝ} {f : ℝ → ℝ}
    (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hG : (q.inclusion G : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => (q.inclusion v x)^(2+2*β)*f (κ*dist o x*(q.inclusion v x)^β)))
    (hQ : (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => dist o x^2*(q.inclusion v x)^(1+2*β)*f (κ*dist o x*(q.inclusion v x)^β)))
    (hDG : (q.closedGradient G : _ → _) =ᵐ[q.atlasMeasure]
      (fun z => Conformal.profileGradient 0 (2+2*β) β κ f (dist o (q.atlasParam z))
        (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)))
    (hDQ : (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
      (fun z => Conformal.profileGradient 2 (1+2*β) β κ f (dist o (q.atlasParam z))
        (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z))) :
    (fun z => ((k+1:ℝ)*f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)+
      (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)*
        deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))*‖q.chordXi o v κ β z‖^2)
      =ᵐ[q.atlasMeasure] (fun z => κ^2*(((k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) z‖^2-
        (k+1:ℝ)/4*dist o (q.atlasParam z)^2)*q.inclusion G (q.atlasParam z)+
        dist o (q.atlasParam z)*inner ℝ (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient G z)+
        β*inner ℝ (q.closedGradient v z) (q.closedGradient Q z)+
        (k+1:ℝ)/4*(q.inclusion v (q.atlasParam z)*q.inclusion Q (q.atlasParam z)))) := by
  filter_upwards [hDG,hDQ,q.atlas_preserving.quasiMeasurePreserving.ae hv,
    q.atlas_preserving.quasiMeasurePreserving.ae hG,q.atlas_preserving.quasiMeasurePreserving.ae hQ]
    with z hDG hDQ hv hG hQ
  rw [hDG,hDQ,hG,hQ]
  exact Conformal.completed_profile_cancel (q.gradient (LipschitzWith.dist_right o) z)
    (q.closedGradient v z) f hv hb hn
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma integrable_radialPair (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    Integrable (fun w => dist o (q.atlasParam w)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.gradient hg w)) q.atlasMeasure := by
  have h := L2.integrable_inner (𝕜 := ℝ) ((q.memLp_radialB o).toLp _) (q.gradient hg)
  apply h.congr
  filter_upwards [(q.memLp_radialB o).coeFn_toLp] with w hw
  rw [hw,radialB,real_inner_smul_left]

lemma integrable_radialVariation (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    Integrable (fun w => (k+1:ℝ)*g (q.atlasParam w)+dist o (q.atlasParam w)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.gradient hg w)) q.atlasMeasure := by
  have hgI : Integrable (fun w => g (q.atlasParam w)) q.atlasMeasure :=
    (((Foundations.boundedLip_of_lipschitz hg).memLp (μ := MassMeasure.currentMassMeasure hT) 1).comp_measurePreserving q.atlas_preserving).integrable le_rfl
  exact (hgI.const_mul (k+1:ℝ)).add (q.integrable_radialPair o hg)

lemma radialVariation_eq_integral (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    q.radialVariation o g = ∫ w, (k+1:ℝ)*g (q.atlasParam w)+dist o (q.atlasParam w)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.gradient hg w) ∂q.atlasMeasure := by
  let f (w : ℕ × Euc (k+1)) := (k+1:ℝ)*g (q.atlasParam w)+dist o (q.atlasParam w)*
      inner ℝ (q.normalizedCovector w.1 (dist o) w.2) (q.normalizedCovector w.1 g w.2)
  have he : (fun w => (k+1:ℝ)*g (q.atlasParam w)+dist o (q.atlasParam w)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.gradient hg w)) =ᵐ[q.atlasMeasure] f := by
    filter_upwards [q.ae_gradient_eq (LipschitzWith.dist_right o),q.ae_gradient_eq hg] with w hr he
    rw [hr,he]
  rw [integral_congr_ae he,q.integral_atlas ((q.integrable_radialVariation o hg).congr he)]
  apply tsum_congr
  intro i
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (q.chart i).borel,q.ae_normalizedCovector_inner i (dist o) g] with z hz hi
  dsimp only [radialVariationChart,f,atlasParam]
  have hsg : g ((q.chart i).paramExtended z) = (q.chart i).scalar g z := (q.chart i).scalar_paramExtended_eqOn g hz
  have hsr : dist o ((q.chart i).paramExtended z) = (q.chart i).scalar (dist o) z := (q.chart i).scalar_paramExtended_eqOn (dist o) hz
  rw [hi,hsg,hsr]
  simp only [Nat.cast_add,Nat.cast_one,covector]

lemma memLp_sweptCoefficient (o : X) :
    MemLp (fun w => dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)) 2 q.atlasMeasure := by
  have hn : (k+1:ℝ) ≠ 0 := by positivity
  have h := (memLp_const (1:ℝ) : MemLp (fun _ : ℕ × Euc (k+1) => (1:ℝ)) 2 q.atlasMeasure).sub
    ((q.memLp_radialA o).const_mul (k+1:ℝ)⁻¹)
  apply (memLp_congr_ae ?_).mp h
  filter_upwards [] with w
  dsimp only [Pi.sub_apply,radialA]
  field_simp
  ring

lemma sweptMass_eq_integral (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    q.sweptMass o g = ∫ w, dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)*
      g (q.atlasParam w) ∂q.atlasMeasure := by
  let f (w : ℕ × Euc (k+1)) := dist o (q.atlasParam w)*
      Real.sqrt (1-‖q.normalizedCovector w.1 (dist o) w.2‖^2)*g (q.atlasParam w)
  have he : (fun w => dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)*g (q.atlasParam w)) =ᵐ[q.atlasMeasure] f := by
    filter_upwards [q.ae_gradient_eq (LipschitzWith.dist_right o)] with w hw
    rw [hw]
  have hgI : MemLp (fun w => g (q.atlasParam w)) 2 q.atlasMeasure :=
    ((Foundations.boundedLip_of_lipschitz hg).memLp 2).comp_measurePreserving q.atlas_preserving
  have hi := (q.memLp_sweptCoefficient o).integrable_mul hgI
  rw [integral_congr_ae he,q.integral_atlas (hi.congr he)]
  apply tsum_congr
  intro i
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (q.chart i).borel,q.ae_normalizedCovector_norm_sq i (dist o)] with z hz hn
  dsimp only [f,atlasParam]
  have hsg : g ((q.chart i).paramExtended z) = (q.chart i).scalar g z := (q.chart i).scalar_paramExtended_eqOn g hz
  have hsr : dist o ((q.chart i).paramExtended z) = (q.chart i).scalar (dist o) z := (q.chart i).scalar_paramExtended_eqOn (dist o) hz
  rw [hn,hsg,hsr]
  dsimp only [IntegerChart.sweptWeight,density,gram,normSq,covector]
  ring
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma radialDefect_lip (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    q.radialDefect o (q.lipSobolev hg) = q.radialVariation o g-(k+1:ℝ)*q.sweptMass o g := by
  have hI : Integrable (fun w => (k+1:ℝ)*(dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)*g (q.atlasParam w))) q.atlasMeasure := by
    exact ((q.memLp_sweptCoefficient o).integrable_mul
      (((Foundations.boundedLip_of_lipschitz hg).memLp 2).comp_measurePreserving q.atlas_preserving)).const_mul (k+1:ℝ)
  rw [q.radialDefect_eq_integral,q.radialVariation_eq_integral o hg,q.sweptMass_eq_integral o hg,
    ←integral_const_mul,←integral_sub (q.integrable_radialVariation o hg) hI]
  apply integral_congr_ae
  simp only [q.inclusion_lipSobolev,q.closedGradient_lipSobolev]
  filter_upwards [q.atlas_preserving.quasiMeasurePreserving.ae ((Foundations.boundedLip_of_lipschitz hg).memLp 2).coeFn_toLp] with w hg'
  change value (hT := hT) hg (q.atlasParam w) = g (q.atlasParam w) at hg'
  rw [hg']
  dsimp only [radialA,radialB]
  rw [real_inner_smul_left]
  ring

lemma radialDefect_smul (o : X) (P : q.Sobolev) (c : ℝ) :
    q.radialDefect o (c • P) = c*q.radialDefect o P := by
  have hcomp : Lp.compMeasurePreserving q.atlasParam q.atlas_preserving (c • q.inclusion P) = c • Lp.compMeasurePreserving q.atlasParam q.atlas_preserving (q.inclusion P) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • q.inclusion P) q.atlas_preserving,
      q.atlas_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul c (q.inclusion P)),
      Lp.coeFn_smul c (Lp.compMeasurePreserving q.atlasParam q.atlas_preserving (q.inclusion P)),
      Lp.coeFn_compMeasurePreserving (q.inclusion P) q.atlas_preserving] with w h1 h2 h3 h4
    simp only [Function.comp_apply] at *
    rw [h1,h2,h3]
    simp only [Pi.smul_apply,h4]
  simp only [radialDefect,map_smul,hcomp,real_inner_smul_right]
  ring

lemma lipSobolev_smul {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (c : ℝ) :
    q.lipSobolev ((lipschitzWith_smul c).comp hg) = c • q.lipSobolev hg := by
  apply Subtype.ext
  exact q.graphPoint_smul hg c

lemma radialDefect_nonpos_lip (o : X)
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (hg0 : ∀ x, 0 ≤ g x) :
    q.radialDefect o (q.lipSobolev hg) ≤ 0 := by
  obtain ⟨C,hC⟩ := (isCompact_range hg.continuous).isBounded.exists_norm_le
  have hpos : 0 < |C|+1 := by positivity
  let c : ℝ := (|C|+1)⁻¹
  have hc : 0 < c := inv_pos.mpr hpos
  have hscaled := hr (fun x => c • g x) _ ((lipschitzWith_smul c).comp hg)
    (fun x => mul_nonneg hc.le (hg0 x)) (fun x => ?_)
  · have hh : q.radialDefect o (q.lipSobolev ((lipschitzWith_smul c).comp hg)) ≤ 0 := by
      rw [q.radialDefect_lip o ((lipschitzWith_smul c).comp hg)]
      exact sub_nonpos.mpr hscaled
    rw [q.lipSobolev_smul hg c,q.radialDefect_smul] at hh
    exact nonpos_of_mul_nonpos_right hh hc
  · change c*g x ≤ 1
    change (|C|+1)⁻¹*g x ≤ 1
    rw [inv_mul_eq_div]
    apply (div_le_one hpos).mpr
    exact (le_abs_self (g x)).trans ((hC _ (mem_range_self x)).trans (by linarith [le_abs_self C]))

lemma radialDefect_nonpos (hz : IsCycle T) (o : X)
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (P : q.Sobolev) (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x) :
    q.radialDefect o P ≤ 0 :=
  q.nonnegative_mem_closed hz (isClosed_le (q.continuous_radialDefect o) continuous_const)
    (fun _ _ hg hg0 => q.radialDefect_nonpos_lip o hr hg hg0) P hP
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_AverageProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chord_energy_oai (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
    {f : ℝ → ℝ} (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
    (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f) (hf0 : ∀ t, 0 ≤ f t)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0) (_hg : LipschitzWith K g),
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g) :
    Integrable (fun z => ((k+1:ℝ)*f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)+
      (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)*
        deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))*‖q.chordXi o v κ β z‖^2) q.atlasMeasure ∧
    (∫ z, ((k+1:ℝ)*f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)+
      (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)*
        deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))*‖q.chordXi o v κ β z‖^2 ∂q.atlasMeasure) ≤
      (k+1:ℝ)/4*(∫ x, (κ*dist o x*(q.inclusion v x)^β)^2*
        f (κ*dist o x*(q.inclusion v x)^β)*(q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT) := by
  obtain ⟨G,Q,hG,hQ,hDG,hDQ⟩ := q.closed_added_tests hz o v (κ := κ) hb hB hf hfB hv hm hpow
  have hG0 : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion G x := by
    filter_upwards [hv,hG] with x hv hG
    rw [hG]
    exact mul_nonneg (Real.rpow_nonneg hv _) (hf0 _)
  have hrG := q.completed_radial o G hG0 (q.radialDefect_nonpos hz o hr G hG0)
  obtain ⟨hE,hbound⟩ := q.added_energy_integral o v G Q
    (q.added_tests_identity o v G Q hb hn hv hG hQ hDG hDQ) hrG (heuler Q)
  refine ⟨hE,hbound.trans_eq ?_⟩
  rw [show κ^2*(k+1:ℝ)/4 = (k+1:ℝ)/4*κ^2 by ring, mul_assoc,←integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [hv,hQ] with x hv hQ
  rw [hQ]
  have hp : (q.inclusion v x)^(1+4*β)*(q.inclusion v x)^(1+2*β) =
      ((q.inclusion v x)^β)^2*(q.inclusion v x)^(2+4*β) := by
    rw [←Real.rpow_add' hv (by linarith : 1+4*β+(1+2*β) ≠ 0),←Real.rpow_mul_natCast hv,Nat.cast_ofNat,
      ←Real.rpow_add' hv (by linarith : β*(2:ℝ)+(2+4*β) ≠ 0)]
    congr 1
    ring
  calc
    _ = κ^2*dist o x^2*((q.inclusion v x)^(1+4*β)*(q.inclusion v x)^(1+2*β))*f (κ*dist o x*(q.inclusion v x)^β) := by ring
    _ = _ := by rw [hp]; ring
end CAT0Fillings.ChartGeometry
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.ChartGeometry.chord_energy_oai.{u_1} := @OAI.CAT0Fillings.ChartGeometry.chord_energy_oai.{u_1}
