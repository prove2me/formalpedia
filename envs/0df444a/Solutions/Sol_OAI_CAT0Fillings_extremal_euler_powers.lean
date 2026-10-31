-- Prove2me | solution 1 for OAI.CAT0Fillings.extremal_euler_powers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:09:37.448979+00:00
-- url     : https://prove2.me/submissions/2f6f09ef-4617-4da2-847a-b539a4978a68

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_extremal_closed_sobolev

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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Bubble_Euclidean
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma omega_gamma {k : ℕ} (hk : 0 < k) :
    omega k = Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2+1) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [omega, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  apply ENNReal.toReal_ofReal
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le

end CAT0Fillings.RadialSobolev
end

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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_CriticalNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer

lemma lpNorm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p : ℝ} (hp : 0 < p) (hf : AEStronglyMeasurable f μ) :
    lpNorm f (ENNReal.ofReal p) μ ^ 2 = (∫ x, |f x|^p ∂μ)^(2/p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs]
  rw [←Real.rpow_mul_natCast (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) ]
  congr 1
  simp only [Nat.cast_ofNat]
  ring

end CAT0Fillings.AnalyticMinimizer
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

lemma closed_chain {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) (hcF : Continuous F')
    {C : ℝ} (hC : 0 ≤ C) (hbF : ∀ t, |F' t| ≤ C) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
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
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C := Eventually.of_forall fun w => hbF _
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C := Eventually.of_forall fun w => hbF _
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
  refine ⟨Q,?_,?_⟩
  · rw [hQ]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_ClosedLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

lemma levelApprox_hasDerivAt {ε : ℝ} (hε : 0 < ε) (a t : ℝ) :
    HasDerivAt (levelApprox a ε) (levelApproxDeriv a ε t) t := by
  have hd := ((((hasDerivAt_id t).sub_const a).div_const ε).arctan).const_mul ε
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  dsimp [levelApproxDeriv]
  field_simp [hε.ne']

lemma levelApproxDeriv_bound {ε : ℝ} (hε : 0 < ε) (a t : ℝ) : |levelApproxDeriv a ε t| ≤ 1 := by
  have hp := add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg (t-a))
  dsimp [levelApproxDeriv]
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hp.le)]
  exact (div_le_one hp).mpr (le_add_of_nonneg_right (sq_nonneg _))

lemma levelApprox_lipschitz {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    LipschitzWith 1 (levelApprox a ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (levelApprox_hasDerivAt hε a t).differentiableAt)
  intro t
  rw [←NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_one,(levelApprox_hasDerivAt hε a t).deriv,Real.norm_eq_abs]
  exact levelApproxDeriv_bound hε a t

lemma continuous_levelApproxDeriv {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Continuous (levelApproxDeriv a ε) := by
  change Continuous (fun t : ℝ => ε^2/(ε^2+(t-a)^2))
  exact continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun t => (add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg (t-a))).ne')

lemma levelApprox_error {ε : ℝ} (hε : 0 ≤ ε) (a t : ℝ) :
    |levelApprox a ε t| ≤ ε*(Real.pi/2) := by
  dsimp [levelApprox]
  rw [abs_mul,abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr
    ⟨(Real.neg_pi_div_two_lt_arctan _).le,(Real.arctan_lt_pi_div_two _).le⟩) hε

lemma levelApproxDeriv_tendsto {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hep : ∀ j, 0 < e j) (a t : ℝ) :
    Tendsto (fun j => levelApproxDeriv a (e j) t) atTop (𝓝 (if t = a then 1 else 0)) := by
  by_cases ht : t = a
  · subst t
    simp only [levelApproxDeriv,sub_self,zero_pow (by decide : 2 ≠ 0),add_zero,
      div_self (pow_ne_zero 2 (hep _).ne'),ite_true, if_true]
    exact tendsto_const_nhds
  · rw [ite_eq_right ht]
    have hta : t-a ≠ 0 := sub_ne_zero.mpr ht
    have hh := (he.pow 2).div ((he.pow 2).add_const ((t-a)^2))
      (by simpa using pow_ne_zero 2 hta)
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [levelApproxDeriv,zero_pow (by decide : 2 ≠ 0),zero_add,zero_div])
    rfl

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_chain_uniform {F D : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hD : Measurable D) {C : ℝ} (hC : 0 ≤ C) (hbD : ∀ t, |D t| ≤ C)
    (Fj Dj : ℕ → ℝ → ℝ) (K : ℕ → ℝ≥0)
    (hFj : ∀ j, LipschitzWith (K j) (Fj j))
    (hdj : ∀ j t, HasDerivAt (Fj j) (Dj j t) t)
    (hcj : ∀ j, Continuous (Dj j)) (hbj : ∀ j t, |Dj j t| ≤ C)
    (hdlim : ∀ t, Tendsto (fun j => Dj j t) atTop (𝓝 (D t)))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (he : ∀ j t, |Fj j t-F t| ≤ a j) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => D ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  choose Q hQ hG using (fun j => q.closed_chain (hFj j) (hdj j) (hcj j) hC (hbj j) P)
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
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hRG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closedGradient_level_zero (hz : IsCycle T) (P : q.Sobolev) (a : ℝ) :
    ∀ᵐ w ∂q.atlasMeasure, (q.inclusion P) (q.atlasParam w) = a →
      (q.closedGradient P) w = 0 := by
  let e (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hep (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hD : Measurable (fun t : ℝ => if t = a then (1:ℝ) else 0) := by
    convert (show Measurable (({a} : Set ℝ).indicator (fun _ : ℝ => (1:ℝ))) from
      measurable_const.indicator (measurableSet_singleton a)) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    simp only [Set.indicator_apply,Set.mem_singleton_iff]

  have hb (t : ℝ) : |if t = a then (1:ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  obtain ⟨R,hR,hG⟩ := q.closed_chain_uniform (F := fun _ => (0:ℝ))
    (D := fun t => if t = a then (1:ℝ) else 0) (LipschitzWith.const (0:ℝ))
    hD (by norm_num : (0:ℝ) ≤ 1) hb
    (fun j => levelApprox a (e j)) (fun j => levelApproxDeriv a (e j)) (fun _ => 1)
    (fun j => levelApprox_lipschitz (hep j) a) (fun j => levelApprox_hasDerivAt (hep j) a)
    (fun j => continuous_levelApproxDeriv (hep j) a) (fun j => levelApproxDeriv_bound (hep j) a)
    (levelApproxDeriv_tendsto he hep a) (fun j => e j*(Real.pi/2))
    (by simpa only [zero_mul] using he.mul_const (Real.pi/2))
    (fun j t => by simpa only [sub_zero] using levelApprox_error (hep j).le a t) P
  have hR0 : q.inclusion R = 0 := Lp.ext (hR.trans (Lp.coeFn_zero ℝ 2 (MassMeasure.currentMassMeasure hT)).symm)
  have hRz : R = 0 := q.inclusion_injective hz (hR0.trans (map_zero q.inclusion).symm)
  rw [hRz,map_zero] at hG
  filter_upwards [hG,(Lp.coeFn_zero (Euc (k+1)) 2 q.atlasMeasure)] with w hw hz
  intro ha
  simpa only [hz,ha,ite_true, if_true,one_smul,Pi.zero_apply] using hw.symm

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_VectorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mulLp_tendsto_smul {b : ℕ → α → ℝ} {c : α → ℝ}
    (hb : ∀ j, AEStronglyMeasurable (b j) μ) (hc : AEStronglyMeasurable c μ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hbC : ∀ j, ∀ᵐ x ∂μ, |b j x| ≤ C) (hcC : ∀ᵐ x ∂μ, |c x| ≤ C)
    (h : Lp E 2 μ)
    (hbc : ∀ᵐ x ∂μ, Tendsto (fun j => b j x • h x) atTop (𝓝 (c x • h x))) :
    Tendsto (fun j => mulLp (hb j) (hbC j) h) atTop (𝓝 (mulLp hc hcC h)) := by
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
      simp_rw [he,sub_smul]
      simpa only [sub_self] using hx.sub_const (c x • h x)
  have hf := hfixed.add_const (mulLp hc hcC h)
  simpa only [sub_add_cancel,zero_add] using hf

end CAT0Fillings.ClosedCalculus
namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_chain_uniform_smul {F D : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hD : Measurable D) {C : ℝ} (hC : 0 ≤ C) (hbD : ∀ t, |D t| ≤ C)
    (Fj Dj : ℕ → ℝ → ℝ) (K : ℕ → ℝ≥0)
    (hFj : ∀ j, LipschitzWith (K j) (Fj j))
    (hdj : ∀ j t, HasDerivAt (Fj j) (Dj j t) t)
    (hcj : ∀ j, Continuous (Dj j)) (hbj : ∀ j t, |Dj j t| ≤ C)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (he : ∀ j t, |Fj j t-F t| ≤ a j) (P : q.Sobolev)
    (hdlim : ∀ᵐ w ∂q.atlasMeasure, Tendsto
      (fun j => Dj j ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) atTop
      (𝓝 (D ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w))) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => D ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  choose Q hQ hG using (fun j => q.closed_chain (hFj j) (hdj j) (hcj j) hC (hbj j) P)
  let b (j : ℕ) (w : ℕ × Euc (k+1)) := Dj j ((q.inclusion P) (q.atlasParam w))
  let c (w : ℕ × Euc (k+1)) := D ((q.inclusion P) (q.atlasParam w))
  have hpm := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hb (j : ℕ) : AEStronglyMeasurable (b j) q.atlasMeasure := (hcj j).comp_aestronglyMeasurable hpm
  have hc : AEStronglyMeasurable c q.atlasMeasure := (hD.comp_aemeasurable hpm.aemeasurable).aestronglyMeasurable
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C := Eventually.of_forall fun _ => hbj j _
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C := Eventually.of_forall fun _ => hbD _
  have hgl := ClosedCalculus.mulLp_tendsto_smul hb hc hC hbC hcC (q.closedGradient P) hdlim
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
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hRG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Piecewise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

lemma scalarAverage_hasDerivAt {F : ℝ → ℝ} (hF : Continuous F) (ε t : ℝ) :
    HasDerivAt (scalarAverage F ε) (scalarAverageDeriv F ε t) t := by
  have hd (s : ℝ) : HasDerivAt (fun y : ℝ => ∫ z in (0:ℝ)..y, F z) (F s) s :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 s)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hh := (((hd (t+ε)).comp t ((hasDerivAt_id t).add_const ε)).sub
    ((hd (t-ε)).comp t ((hasDerivAt_id t).sub_const ε))).div_const (2*ε)
  simp only [Function.comp_def,id_eq,mul_one,Pi.sub_apply] at hh
  convert hh using 1 <;> rfl

lemma continuous_scalarAverageDeriv {F : ℝ → ℝ} (hF : Continuous F) (ε : ℝ) :
    Continuous (scalarAverageDeriv F ε) :=
  ((hF.comp (continuous_id.add continuous_const)).sub
    (hF.comp (continuous_id.sub continuous_const))).div_const _

lemma scalarAverageDeriv_bound {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |scalarAverageDeriv F ε t| ≤ K := by
  have hh := hF.dist_le_mul (t+ε) (t-ε)
  rw [Real.dist_eq,Real.dist_eq,show t+ε-(t-ε) = 2*ε by ring,
    abs_of_pos (show 0 < 2*ε by positivity)] at hh
  dsimp [scalarAverageDeriv]
  rw [abs_div,abs_of_pos (show 0 < 2*ε by positivity)]
  exact (div_le_iff₀ (mul_pos (by norm_num) hε)).mpr hh

lemma scalarAverage_lipschitz {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {ε : ℝ} (hε : 0 < ε) : LipschitzWith K (scalarAverage F ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (scalarAverage_hasDerivAt hF.continuous ε t).differentiableAt)
  intro t
  rw [←NNReal.coe_le_coe,coe_nnnorm,(scalarAverage_hasDerivAt hF.continuous ε t).deriv,Real.norm_eq_abs]
  exact scalarAverageDeriv_bound hF hε t

lemma scalarAverage_integral {F : ℝ → ℝ} (hF : Continuous F) (ε t : ℝ) :
    scalarAverage F ε t = (∫ z in (t-ε)..(t+ε), F z)/(2*ε) := by
  dsimp [scalarAverage]
  congr 1
  exact intervalIntegral.integral_interval_sub_left (hF.intervalIntegrable 0 (t+ε))
    (hF.intervalIntegrable 0 (t-ε))

lemma scalarAverage_error {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |scalarAverage F ε t-F t| ≤ K*ε := by
  have hab : t-ε ≤ t+ε := by linarith
  have hh : |∫ z in (t-ε)..(t+ε), (F z-F t)| ≤ (K*ε)*(2*ε) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := t-ε) (b := t+ε)
      (f := fun z => F z-F t) (C := K*ε) (fun z hz => by
        rw [uIoc_of_le hab] at hz
        have hd : |z-t| ≤ ε := abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
        have hf := hF.dist_le_mul z t
        rw [Real.dist_eq,Real.dist_eq] at hf
        rw [Real.norm_eq_abs]
        exact hf.trans (mul_le_mul_of_nonneg_left hd K.coe_nonneg))
    simpa only [Real.norm_eq_abs,show t+ε-(t-ε) = 2*ε by ring,
      abs_of_pos (show 0 < 2*ε by positivity)] using hb
  have he : scalarAverage F ε t-F t = (∫ z in (t-ε)..(t+ε), (F z-F t))/(2*ε) := by
    rw [scalarAverage_integral hF.continuous,intervalIntegral.integral_sub
      (hF.continuous.intervalIntegrable _ _) intervalIntegrable_const,intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [he,abs_div,abs_of_pos (show 0 < 2*ε by positivity)]
  exact (div_le_iff₀ (mul_pos (by norm_num) hε)).mpr hh

lemma scalarAverageDeriv_tendsto {F : ℝ → ℝ} {D t : ℝ} (hd : HasDerivAt F D t)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (hep : ∀ j, 0 < e j) :
    Tendsto (fun j => scalarAverageDeriv F (e j) t) atTop (𝓝 D) := by
  have he' : Tendsto e atTop (𝓝[≠] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨he,Eventually.of_forall fun j => (hep j).ne'⟩
  have hen : Tendsto (fun j => -e j) atTop (𝓝[≠] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [neg_zero] using he.neg,Eventually.of_forall fun j => neg_ne_zero.mpr (hep j).ne'⟩
  have hh := ((hd.tendsto_slope_zero.comp he').add (hd.tendsto_slope_zero.comp hen)).div_const (2:ℝ)
  have heq (j : ℕ) : scalarAverageDeriv F (e j) t =
      ((e j)⁻¹ • (F (t+e j)-F t) + (-e j)⁻¹ • (F (t+-e j)-F t))/2 := by
    dsimp [scalarAverageDeriv]
    simp only [←sub_eq_add_neg]
    field_simp
    ring
  simp only [Function.comp_def] at hh
  convert hh using 1
  · funext j
    exact heq j
  · congr 1
    ring

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_chain_countable {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {S : Set ℝ} (hS : S.Countable) (hd : ∀ t ∉ S, DifferentiableAt ℝ F t)
    (hz : IsCycle T) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => deriv F ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  let e (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hep (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (t : ℝ) : |deriv F t| ≤ K := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hF (x₀ := t)
  have hlevel : ∀ᵐ w ∂q.atlasMeasure, ∀ a ∈ S,
      (q.inclusion P) (q.atlasParam w) = a → (q.closedGradient P) w = 0 := by
    exact (ae_ball_iff hS).mpr fun a _ => q.closedGradient_level_zero hz P a
  apply q.closed_chain_uniform_smul hF (measurable_deriv F) K.coe_nonneg hb
    (fun j => scalarAverage F (e j)) (fun j => scalarAverageDeriv F (e j)) (fun _ => K)
    (fun j => scalarAverage_lipschitz hF (hep j))
    (fun j => scalarAverage_hasDerivAt hF.continuous (e j))
    (fun j => continuous_scalarAverageDeriv hF.continuous (e j))
    (fun j => scalarAverageDeriv_bound hF (hep j)) (fun j => K*e j)
    (by simpa only [mul_zero] using he.const_mul (K:ℝ))
    (fun j => scalarAverage_error hF (hep j)) P
  filter_upwards [hlevel] with w hw
  by_cases hs : (q.inclusion P) (q.atlasParam w) ∈ S
  · rw [hw _ hs rfl]
    simp only [smul_zero]
    exact tendsto_const_nhds
  · exact (scalarAverageDeriv_tendsto (hd _ hs).hasDerivAt he hep).smul_const _

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_Truncated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

lemma truncatedPower_nonneg {γ N t : ℝ} (hN : 0 ≤ N) : 0 ≤ truncatedPower γ N t :=
  mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (le_min (le_max_right _ _) hN) _)

lemma truncatedPower_of_nonneg {γ N t : ℝ} (ht : 0 ≤ t) :
    truncatedPower γ N t = t*(min t N)^(γ-1) := by
  simp only [truncatedPower,max_eq_left ht]

lemma truncatedPower_of_le {γ N t : ℝ} (hγ : 1 < γ) (ht : 0 ≤ t) (htN : t ≤ N) :
    truncatedPower γ N t = t^γ := by
  rw [truncatedPower_of_nonneg ht,min_eq_left htN]
  by_cases ht0 : t = 0
  · simp only [ht0,zero_mul,Real.zero_rpow (by linarith : γ ≠ 0)]
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    calc
      t*t^(γ-1) = t^(1:ℝ)*t^(γ-1) := by rw [Real.rpow_one]
      _ = t^(1+(γ-1)) := (Real.rpow_add htp _ _).symm
      _ = t^γ := by congr 1; ring

lemma truncatedPower_of_ge {γ N t : ℝ} (ht : 0 ≤ t) (hNt : N ≤ t) :
    truncatedPower γ N t = t*N^(γ-1) := by
  rw [truncatedPower_of_nonneg ht,min_eq_right hNt]

lemma truncatedPower_lipschitz {γ N : ℝ} (hγ : 1 < γ) (hN : 0 < N) :
    ∃ K : ℝ≥0, LipschitzWith K (truncatedPower γ N) := by
  let C : ℝ≥0 := ⟨γ*N^(γ-1),mul_nonneg (by linarith) (Real.rpow_nonneg hN.le _)⟩
  have hp : LipschitzOnWith C (fun t : ℝ => t^γ) (Icc 0 N) := by
    apply (convex_Icc (0:ℝ) N).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (Real.hasDerivAt_rpow_const (Or.inr (by linarith : 1 ≤ γ))).differentiableAt
    · intro t ht
      rw [←NNReal.coe_le_coe,coe_nnnorm,
        (Real.hasDerivAt_rpow_const (x := t) (Or.inr (by linarith : 1 ≤ γ))).deriv,
        Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1 _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 (by linarith)) (by linarith)
  let b (t : ℝ) := min (max t 0) N
  have hb : LipschitzWith 1 b := (LipschitzWith.id.max_const (0:ℝ)).min_const N
  have hbS (t : ℝ) : b t ∈ Icc 0 N := ⟨le_min (le_max_right _ _) hN.le,min_le_right _ _⟩
  have hbp : LipschitzWith C (fun t => (b t)^γ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hp.dist_le_mul (b x) (hbS x) (b y) (hbS y)).trans
      (mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one,one_mul] using hb.dist_le_mul x y) C.coe_nonneg)
  have hr := (LipschitzWith.id.max_const (0:ℝ)).sub hb
  have hl := hbp.add ((lipschitzWith_smul (N^(γ-1))).comp hr)
  refine ⟨C + ‖N ^ (γ - 1)‖₊ * (1 + 1),?_⟩
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  symm
  dsimp [Function.comp_def,b,id_eq]
  by_cases htN : max t 0 ≤ N
  · rw [min_eq_left htN,sub_self,mul_zero,add_zero]
    exact (truncatedPower_of_le hγ (le_max_right t 0) htN).symm.trans (by simp only [truncatedPower,max_eq_left (le_max_right t 0)])
  · rw [min_eq_right (le_of_not_ge htN)]
    dsimp [truncatedPower]
    rw [min_eq_right (le_of_not_ge htN)]
    have hpN : N^γ = N*N^(γ-1) := (truncatedPower_of_le hγ hN.le le_rfl).symm.trans (by rw [truncatedPower_of_nonneg hN.le,min_self])
    rw [hpN]
    ring

lemma truncatedPower_hasDerivAt_low {γ N t : ℝ} (hγ : 1 < γ) (ht : 0 < t) (htN : t < N) :
    HasDerivAt (truncatedPower γ N) (γ*t^(γ-1)) t := by
  have he : truncatedPower γ N =ᶠ[𝓝 t] (fun s : ℝ => s^γ) := by
    filter_upwards [Ioo_mem_nhds ht htN] with s hs
    exact truncatedPower_of_le hγ hs.1.le hs.2.le
  exact (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).congr_of_eventuallyEq he

lemma truncatedPower_hasDerivAt_high {γ N t : ℝ} (hN : 0 < N) (ht : N < t) :
    HasDerivAt (truncatedPower γ N) (N^(γ-1)) t := by
  have he : truncatedPower γ N =ᶠ[𝓝 t] (fun s : ℝ => s*N^(γ-1)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact truncatedPower_of_ge (hN.trans hs).le hs.le
  simpa only [one_mul] using ((hasDerivAt_id t).mul_const (N^(γ-1))).congr_of_eventuallyEq he

lemma truncatedPower_hasDerivAt_neg {γ N t : ℝ} (ht : t < 0) :
    HasDerivAt (truncatedPower γ N) 0 t := by
  have he : truncatedPower γ N =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    simp only [truncatedPower,max_eq_right hs.le,zero_mul]
  exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he

lemma truncatedPower_differentiable {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N)
    (ht : t ∉ ({0,N} : Set ℝ)) : DifferentiableAt ℝ (truncatedPower γ N) t := by
  simp only [mem_insert_iff,mem_singleton_iff,not_or] at ht
  rcases lt_or_gt_of_ne ht.1 with h | h
  · exact (truncatedPower_hasDerivAt_neg h).differentiableAt
  · rcases lt_or_gt_of_ne ht.2 with h' | h'
    · exact (truncatedPower_hasDerivAt_low hγ h h').differentiableAt
    · exact (truncatedPower_hasDerivAt_high hN h').differentiableAt

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
lemma truncatedPower_deriv_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) (v : E)
    (h0 : t = 0 → v = 0) (hNs : t = N → v = 0) :
    deriv (truncatedPower γ N) t • v = truncatedPowerSlope γ N t • v := by
  by_cases ht0 : t = 0
  · rw [h0 ht0,smul_zero,smul_zero]
  by_cases htN : t = N
  · rw [hNs htN,smul_zero,smul_zero]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  rcases lt_or_gt_of_ne htN with hlt | hgt
  · rw [(truncatedPower_hasDerivAt_low hγ htpos hlt).deriv,truncatedPowerSlope,ite_eq_left hlt]
  · rw [(truncatedPower_hasDerivAt_high hN hgt).deriv,truncatedPowerSlope,ite_eq_right hgt.not_gt]

end CAT0Fillings.ClosedCalculus

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma truncated_deriv_ae (hz : IsCycle T) (P : q.Sobolev)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    {γ N : ℝ} (hγ : 1 < γ) (hN : 0 < N) :
    (fun w => deriv (truncatedPower γ N) (q.inclusion P (q.atlasParam w)) • q.closedGradient P w) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope γ N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w) := by
  have hp : ∀ᵐ w ∂q.atlasMeasure, 0 ≤ q.inclusion P (q.atlasParam w) :=
    q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => 0 ≤ q.inclusion P x) hP
  filter_upwards [hp,q.closedGradient_level_zero hz P 0,q.closedGradient_level_zero hz P N]
    with w hp hz0 hzN
  exact truncatedPower_deriv_smul hγ hN hp _ hz0 hzN

lemma closed_truncated_power (hz : IsCycle T) (P : q.Sobolev)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    {γ N : ℝ} (hγ : 1 < γ) (hN : 0 < N) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => truncatedPower γ N (q.inclusion P x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => truncatedPowerSlope γ N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w) := by
  obtain ⟨K,hK⟩ := truncatedPower_lipschitz hγ hN
  obtain ⟨Q,hQ,hG⟩ := q.closed_chain_countable hK (((Set.finite_singleton N).insert 0).to_countable)
    (fun t ht => truncatedPower_differentiable hγ hN ht) hz P
  exact ⟨Q,hQ,hG.trans (q.truncated_deriv_ae hz P hP hγ hN)⟩

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_Slope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

lemma truncatedPower_le_power {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    truncatedPower γ N t ≤ t^γ := by
  by_cases htN : t ≤ N
  · exact le_of_eq (truncatedPower_of_le hγ ht htN)
  · have htpos : 0 < t := hN.trans (lt_of_not_ge htN)
    rw [truncatedPower_of_ge ht (le_of_not_ge htN)]
    have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN.le (le_of_not_ge htN) (by linarith : 0 ≤ γ-1)) ht
    apply hh.trans_eq
    simpa only [truncatedPower,max_eq_left ht,min_self] using (truncatedPower_of_le hγ ht (le_refl t))

lemma truncatedPower_product {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    t*truncatedPower (2*γ-1) N t = (truncatedPower γ N t)^2 := by
  rw [truncatedPower_of_nonneg ht,truncatedPower_of_nonneg ht]
  have he : 2*γ-1-1 = (γ-1)+(γ-1) := by ring
  rw [he, Real.rpow_add_of_nonneg (le_min ht hN.le)
    (sub_nonneg.mpr hγ.le) (sub_nonneg.mpr hγ.le)]
  ring

lemma truncatedPower_rhs {γ N t p : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) (hp : 2 < p) :
    t^(p-1)*truncatedPower (2*γ-1) N t = t^(p-2)*(truncatedPower γ N t)^2 := by
  rw [←truncatedPower_product hγ hN ht]
  by_cases ht0 : t = 0
  · simp only [ht0,Real.zero_rpow (by linarith : p-1 ≠ 0),zero_mul,mul_zero]
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have he : t^(p-1) = t^(p-2)*t := by
      calc
        t^(p-1) = t^((p-2)+1) := by congr 1; ring
        _ = t^(p-2)*t^(1:ℝ) := Real.rpow_add htp _ _
        _ = t^(p-2)*t := by rw [Real.rpow_one]
    rw [he,mul_assoc]

lemma power_ratio_pos {γ : ℝ} (hγ : 1 < γ) : 0 < (2*γ-1)/γ^2 :=
  div_pos (by linarith) (sq_pos_of_pos (by linarith))

lemma power_ratio_le_one {γ : ℝ} (hγ : 1 < γ) : (2*γ-1)/γ^2 ≤ 1 := by
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < γ))).mpr
  nlinarith [sq_nonneg (γ-1)]

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus

lemma truncatedPowerSlope_nonneg {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    0 ≤ truncatedPowerSlope γ N t := by
  dsimp [truncatedPowerSlope]
  split_ifs
  · exact mul_nonneg (by linarith) (Real.rpow_nonneg ht _)
  · exact Real.rpow_nonneg hN.le _

lemma truncatedPowerSlope_le {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    truncatedPowerSlope γ N t ≤ γ*t^(γ-1) := by
  dsimp [truncatedPowerSlope]
  split_ifs with h
  · exact le_rfl
  · have hh := Real.rpow_le_rpow hN.le (le_of_not_gt h) (by linarith : 0 ≤ γ-1)
    have hp := Real.rpow_nonneg ht (γ-1)
    nlinarith

lemma truncatedPowerSlope_ratio {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) :
    (2*γ-1)/γ^2*(truncatedPowerSlope γ N t)^2 ≤ truncatedPowerSlope (2*γ-1) N t := by
  have he : 2*γ-1-1 = (γ-1)*2 := by ring
  have hg0 : γ ≠ 0 := by linarith
  dsimp [truncatedPowerSlope]
  split_ifs with h
  · rw [he,Real.rpow_mul ht,Real.rpow_two,mul_pow]
    have hg2 : γ^2 ≠ 0 := pow_ne_zero _ hg0
    rw [←mul_assoc,div_mul_cancel₀ _ hg2]
  · rw [he,Real.rpow_mul hN.le,Real.rpow_two]
    exact mul_le_of_le_one_left (sq_nonneg _) (power_ratio_le_one hγ)

lemma truncatedPower_tendsto {γ t : ℝ} (hγ : 1 < γ) (ht : 0 ≤ t) :
    Tendsto (fun j : ℕ => truncatedPower γ ((j:ℝ)+1) t) atTop (𝓝 (t^γ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop).eventually (eventually_ge_atTop t)] with j hj
  exact (truncatedPower_of_le hγ ht (by linarith)).symm

lemma truncatedPowerSlope_tendsto {γ t : ℝ} :
    Tendsto (fun j : ℕ => truncatedPowerSlope γ ((j:ℝ)+1) t) atTop (𝓝 (γ*t^(γ-1))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop).eventually (eventually_ge_atTop t)] with j hj
  rw [truncatedPowerSlope,ite_eq_left (by linarith)]

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_abs_rpow {f : α → ℝ} {p r : ℝ} (hr : 0 < r)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x => |f x|^r) (ENNReal.ofReal (p/r)) μ := by
  simpa only [Real.norm_eq_abs,ENNReal.toReal_ofReal hr.le,ENNReal.ofReal_div_of_pos hr]
    using hf.norm_rpow_div (ENNReal.ofReal r)

lemma potential_holder_conjugate {p : ℝ} (hp : 2 < p) :
    (p/(p-2)).HolderConjugate (p/2) := by
  apply Real.holderConjugate_iff.mpr
  refine ⟨(lt_div_iff₀ (by linarith : 0 < p-2)).mpr (by linarith),?_⟩
  field_simp
  ring

lemma potential_integrable {f g : α → ℝ} {p : ℝ} (hp : 2 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    Integrable (fun x => |f x|^(p-2)*(g x)^2) μ := by
  have := (potential_holder_conjugate hp).ennrealOfReal
  have hh := (memLp_abs_rpow (by linarith : 0 < p-2) hf).integrable_mul
    (memLp_abs_rpow (by norm_num : (0:ℝ) < 2) hg)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Pi.mul_apply,Real.rpow_two,sq_abs]

lemma potential_holder {f g : α → ℝ} {p : ℝ} (hp : 2 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x, |f x|^(p-2)*(g x)^2 ∂μ) ≤
      (∫ x, |f x|^p ∂μ)^((p-2)/p) * (lpNorm g (ENNReal.ofReal p) μ)^2 := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (potential_holder_conjugate hp)
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (f x)) (p-2))
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (g x)) (2:ℝ))
    (memLp_abs_rpow hpm hf) (memLp_abs_rpow (by norm_num : (0:ℝ) < 2) hg)
  have he1 : (p-2)*(p/(p-2)) = p := by field_simp
  have he2 : (2:ℝ)*(p/2) = p := by ring
  have he3 : (1:ℝ)/(p/(p-2)) = (p-2)/p := by field_simp
  have he4 : (1:ℝ)/(p/2) = 2/p := by field_simp
  change (∫ x, |f x|^(p-2)*|g x|^(2:ℝ) ∂μ) ≤
    (∫ x, (|f x|^(p-2))^(p/(p-2)) ∂μ)^(1/(p/(p-2))) *
    (∫ x, (|g x|^(2:ℝ))^(p/2) ∂μ)^(1/(p/2)) at hh
  simp only [←Real.rpow_mul (abs_nonneg _),he1,he2,he3,he4] at hh
  simp only [Real.rpow_two,sq_abs] at hh
  rw [AnalyticMinimizer.lpNorm_sq_eq_integral hp0 hg.aestronglyMeasurable]
  exact hh

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma truncated_gradient_energy (P Q R : q.Sobolev) {γ N : ℝ}
    (hγ : 1 < γ) (hN : 0 < N)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hQ : (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope γ N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w))
    (hR : (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope (2*γ-1) N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w)) :
    (2*γ-1)/γ^2*‖q.closedGradient Q‖^2 ≤ inner ℝ (q.closedGradient P) (q.closedGradient R) := by
  rw [l2_norm_sq,L2.inner_def,←integral_const_mul]
  apply integral_mono_ae (((Lp.memLp (q.closedGradient Q)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul _)
    (L2.integrable_inner _ _)
  filter_upwards [hQ,hR,q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => 0 ≤ q.inclusion P x) hP] with w hQ hR hP
  rw [hQ,hR,inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (truncatedPowerSlope_ratio hγ hN hP)
    (sq_nonneg ‖q.closedGradient P w‖)

lemma truncated_power_energy (_hz : IsCycle T) (P Q R : q.Sobolev) {γ N p A n : ℝ}
    (hγ : 1 < γ) (hN : 0 < N) (hp : 2 < p) (hA : 0 ≤ A) (hn : 0 ≤ n)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hQv : (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => truncatedPower γ N (q.inclusion P x)))
    (hRv : (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => truncatedPower (2*γ-1) N (q.inclusion P x)))
    (hQ : (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope γ N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w))
    (hR : (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope (2*γ-1) N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w))
    (heuler : A*inner ℝ (q.closedGradient P) (q.closedGradient R) + n*inner ℝ (q.inclusion P) (q.inclusion R) =
      n*(∫ x, (q.inclusion P x)^(p-1)*q.inclusion R x ∂MassMeasure.currentMassMeasure hT)) :
    A*((2*γ-1)/γ^2)*‖q.closedGradient Q‖^2 ≤
      n*(∫ x, |q.inclusion P x|^(p-2)*(q.inclusion Q x)^2 ∂MassMeasure.currentMassMeasure hT) := by
  have hgrad := mul_le_mul_of_nonneg_left (q.truncated_gradient_energy P Q R hγ hN hP hQ hR) hA
  have hzI : 0 ≤ inner ℝ (q.inclusion P) (q.inclusion R) := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hP,hRv] with x hx hR
    rw [hR,real_inner_comm]
    exact mul_nonneg hx (truncatedPower_nonneg hN.le)
  have he : (∫ x, (q.inclusion P x)^(p-1)*q.inclusion R x ∂MassMeasure.currentMassMeasure hT) =
      (∫ x, |q.inclusion P x|^(p-2)*(q.inclusion Q x)^2 ∂MassMeasure.currentMassMeasure hT) := by
    apply integral_congr_ae
    filter_upwards [hP,hRv,hQv] with x hx hR hQ
    rw [hR,hQ,abs_of_nonneg hx]
    exact truncatedPower_rhs hγ hN hx hp
  rw [he] at heuler
  have hzprod := mul_nonneg hn hzI
  nlinarith

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_Absorption
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma power_tail_tendsto {f : α → ℝ} {p : ℝ} (hp : 0 < p)
    (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) μ) :
    Tendsto (fun j : ℕ => ∫ x, if (j:ℝ)+1 < |f x| then |f x|^p else 0 ∂μ) atTop (𝓝 0) := by
  classical
  have hi : Integrable (fun x => |f x|^p) μ := by
    simpa only [Real.norm_eq_abs,ENNReal.toReal_ofReal hp.le] using
      hf.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  have hh := tendsto_integral_of_dominated_convergence (F := fun j : ℕ => fun x => if (j:ℝ)+1 < |f x| then |f x|^p else 0)
    (f := fun _ => (0:ℝ)) (fun x => |f x|^p)
    (fun j => ((hfm.abs.pow_const p).ite (measurableSet_lt measurable_const hfm.abs) measurable_const).aestronglyMeasurable)
    hi (fun j => Eventually.of_forall (fun x => by
      split_ifs
      · simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),le_refl]
      · simpa only [norm_zero] using Real.rpow_nonneg (abs_nonneg (f x)) p))
    (Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      have he : ∀ᶠ j : ℕ in atTop, |f x| ≤ (j:ℝ)+1 :=
        ((tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop).eventually
          (eventually_ge_atTop (|f x|))).mono (fun j hj => by linarith)
      filter_upwards [he] with j hj
      rw [ite_eq_right (not_lt_of_ge hj)]))
  simpa only [integral_zero] using hh

lemma lpNorm_two_sq_integral {g : α → ℝ} (hg : AEStronglyMeasurable g μ) :
    lpNorm g 2 μ ^2 = ∫ x, (g x)^2 ∂μ := by
  have hh := AnalyticMinimizer.lpNorm_sq_eq_integral (by norm_num : (0:ℝ) < 2) hg
  simpa only [ENNReal.ofReal_ofNat,Real.rpow_two,sq_abs,div_self (by norm_num : (2:ℝ) ≠ 0),Real.rpow_one] using hh

lemma potential_split {f g : α → ℝ} {p K : ℝ} (hp : 2 < p) (hK : 0 < K)
    (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal p) μ) (hg2 : MemLp g 2 μ) :
    (∫ x, |f x|^(p-2)*(g x)^2 ∂μ) ≤
      K^(p-2)*(lpNorm g 2 μ)^2 +
        (∫ x, if K < |f x| then |f x|^p else 0 ∂μ)^((p-2)/p) *
          (lpNorm g (ENNReal.ofReal p) μ)^2 := by
  let s : Set α := {x | K < |f x|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hfm.abs
  have hft := hf.indicator hs
  have hgi : Integrable (fun x => (g x)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using hg2.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hb : (∫ x, |f x|^(p-2)*(g x)^2 ∂μ) ≤
      (∫ x, K^(p-2)*(g x)^2 + |s.indicator f x|^(p-2)*(g x)^2 ∂μ) := by
    apply integral_mono (potential_integrable hp hf hg)
      ((hgi.const_mul _).add (potential_integrable hp hft hg))
    intro x
    change |f x|^(p-2)*(g x)^2 ≤ K^(p-2)*(g x)^2+|s.indicator f x|^(p-2)*(g x)^2
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hK.le _) (sq_nonneg _))
    · rw [Set.indicator_of_notMem hx,abs_zero,Real.zero_rpow (by linarith : p-2 ≠ 0),zero_mul,add_zero]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) (le_of_not_gt hx) (by linarith)) (sq_nonneg _)
  rw [integral_add (hgi.const_mul _) (potential_integrable hp hft hg),integral_const_mul,
    ←lpNorm_two_sq_integral hg2.aestronglyMeasurable] at hb
  apply hb.trans
  apply add_le_add_right
  have hh := potential_holder hp hft hg
  have he : (∫ x, |s.indicator f x|^p ∂μ) =
      (∫ x, if K < |f x| then |f x|^p else 0 ∂μ) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change |s.indicator f x|^p = if K < |f x| then |f x|^p else 0
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx,ite_eq_left (show K < |f x| from hx)]
      · rw [Set.indicator_of_notMem hx,ite_eq_right (show ¬K < |f x| from hx),abs_zero,Real.zero_rpow (by linarith : p ≠ 0)]
  simpa only [he] using hh

lemma potential_small {f : α → ℝ} {p : ℝ} (hp : 2 < p)
    (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : α → ℝ, MemLp g (ENNReal.ofReal p) μ → MemLp g 2 μ →
      (∫ x, |f x|^(p-2)*(g x)^2 ∂μ) ≤
        δ*(lpNorm g (ENNReal.ofReal p) μ)^2+B*(lpNorm g 2 μ)^2 := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < (p-2)/p := div_pos (by linarith) hp0
  have ht := (Real.continuous_rpow_const hq.le).continuousAt.tendsto.comp
    (power_tail_tendsto hp0 hfm hf)
  rw [Real.zero_rpow hq.ne'] at ht
  obtain ⟨j,hj⟩ := Filter.Eventually.exists (ht.eventually (eventually_lt_nhds hδ))
  refine ⟨((j:ℝ)+1)^(p-2),Real.rpow_nonneg (by positivity) _,?_⟩
  intro g hg hg2
  have hh := potential_split hp (by positivity : 0 < (j:ℝ)+1) hfm hf hg hg2
  dsimp only [Function.comp_apply] at hj
  have hb := mul_le_mul_of_nonneg_right hj.le (sq_nonneg (lpNorm g (ENNReal.ofReal p) μ))
  linarith

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma power_absorption {p A n d S C M : ℝ} (hp : 2 < p) (hA : 0 < A) (hn : 0 < n)
    (hd : 0 < d) (hS : 0 < S) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (v : Lp ℝ 2 μ) (hv : MemLp (v : α → ℝ) (ENNReal.ofReal p) μ)
    (f : ℕ → Lp ℝ 2 μ) (E : ℕ → ℝ)
    (hf : ∀ j, MemLp (f j : α → ℝ) (ENNReal.ofReal p) μ)
    (_hEv : ∀ j, 0 ≤ E j) (hMv : ∀ j, ‖f j‖^2 ≤ M)
    (hs : ∀ j, S*(lpNorm (f j : α → ℝ) (ENNReal.ofReal p) μ)^2 ≤ A*E j+C*‖f j‖^2)
    (he : ∀ j, A*d*E j ≤ n*(∫ x, |v x|^(p-2)*(f j x)^2 ∂μ)) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
      (∀ j, (lpNorm (f j : α → ℝ) (ENNReal.ofReal p) μ)^2 ≤ L) ∧
      (∀ j, E j ≤ B) := by
  have hδ : 0 < d*S/(2*n) := div_pos (mul_pos hd hS) (by positivity)
  obtain ⟨K,hK,hpot⟩ := potential_small hp (Lp.stronglyMeasurable v).measurable hv hδ
  let L := 2*(n*K+d*C)*M/(d*S)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbound (j : ℕ) : (lpNorm (f j : α → ℝ) (ENNReal.ofReal p) μ)^2 ≤ L := by
    have ht := hpot (f j) (hf j) (Lp.memLp (f j))
    have hnorm : lpNorm (f j : α → ℝ) 2 μ = ‖f j‖ := by
      rw [Lp.norm_def,toReal_eLpNorm (Lp.aestronglyMeasurable _)]
    rw [hnorm] at ht
    have ht' := mul_le_mul_of_nonneg_left ht hn.le
    have hs' := mul_le_mul_of_nonneg_left (hs j) hd.le
    have hcoef : n*(d*S/(2*n)) = d*S/2 := by field_simp
    have hm' := mul_le_mul_of_nonneg_left (hMv j) (show 0 ≤ n*K+d*C by positivity)
    have habs : d*S*(lpNorm (f j : α → ℝ) (ENNReal.ofReal p) μ)^2 ≤ 2*(n*K+d*C)*M := by
      have he' := he j
      rw [mul_add] at ht'
      rw [←mul_assoc,hcoef] at ht'
      nlinarith
    exact (le_div_iff₀ (mul_pos hd hS)).mpr (by nlinarith)
  let V := (∫ x, |v x|^p ∂μ)^((p-2)/p)
  have hV : 0 ≤ V := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _
  refine ⟨L,n*V*L/(A*d),hL,by positivity,hbound,?_⟩
  intro j
  have ht := mul_le_mul_of_nonneg_left (potential_holder hp hv (hf j)) hn.le
  have hb := mul_le_mul_of_nonneg_left (hbound j) (show 0 ≤ n*V by positivity)
  apply (le_div_iff₀ (mul_pos hA hd)).mpr
  have he' := he j
  dsimp [V] at hb
  nlinarith

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_ClosedLimit
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E]

lemma memLp_of_ae_tendsto_bounded [InnerProductSpace ℝ E] (f : ℕ → Lp E 2 μ) {g : α → E}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} (hC : ∀ j, ‖f j‖ ≤ C)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x))) : MemLp g 2 μ := by
  refine ⟨hg, lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto (C := ENNReal.ofReal C) ?_ (fun j => Lp.aestronglyMeasurable (f j)) hl) ENNReal.ofReal_lt_top⟩
  apply Eventually.of_forall
  intro j
  rw [←ENNReal.ofReal_toReal (Lp.memLp (f j)).eLpNorm_ne_top]
  change ENNReal.ofReal ‖f j‖ ≤ ENNReal.ofReal C
  exact ENNReal.ofReal_le_ofReal (hC j)

variable [InnerProductSpace ℝ E]

lemma l2_tendsto_of_domination (f : ℕ → Lp E 2 μ) (g : Lp E 2 μ)
    (b : α → ℝ) (hb : Integrable (fun x => b x^2) μ)
    (hf : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ b x) (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ b x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  have hh : Tendsto (fun j => f j-g) atTop (𝓝 0) := by
    apply l2_tendsto_zero_of_bound _ (fun x => 2*b x)
    · convert hb.const_mul (4:ℝ) using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      ring
    · intro j
      filter_upwards [Lp.coeFn_sub (f j) g,hf j,hg] with x hs hf hg
      rw [hs,Pi.sub_apply]
      exact (norm_sub_le _ _).trans (by linarith)
    · have ha : ∀ᵐ x ∂μ, ∀ j, (f j-g) x = f j x-g x :=
        ae_all_iff.mpr (fun j => Lp.coeFn_sub (f j) g)
      filter_upwards [ha,hl] with x hx hl
      simp_rw [hx]
      simpa only [sub_self] using hl.sub_const (g x)
  simpa only [sub_add_cancel,zero_add] using hh.add_const g

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_power_of_truncated_bound (P : q.Sobolev) {γ : ℝ} (hγ : 1 < γ)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hv : MemLp (fun x => (q.inclusion P x)^γ) 2 (MassMeasure.currentMassMeasure hT))
    (Q : ℕ → q.Sobolev)
    (hQv : ∀ j, (q.inclusion (Q j) : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => truncatedPower γ ((j:ℝ)+1) (q.inclusion P x)))
    (hQG : ∀ j, (q.closedGradient (Q j) : _ → _) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope γ ((j:ℝ)+1) (q.inclusion P (q.atlasParam w)) • q.closedGradient P w))
    {B : ℝ} (hB : ∀ j, ‖q.closedGradient (Q j)‖ ≤ B) :
    ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion P x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w) := by
  let g (w : ℕ × Euc (k+1)) := (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w
  have hp : ∀ᵐ w ∂q.atlasMeasure, 0 ≤ q.inclusion P (q.atlasParam w) :=
    q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => 0 ≤ q.inclusion P x) hP
  have hpm := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hgm : AEStronglyMeasurable g q.atlasMeasure :=
    (aestronglyMeasurable_const.mul ((Real.continuous_rpow_const (by linarith : 0 ≤ γ-1)).comp_aestronglyMeasurable hpm)).smul
      (Lp.aestronglyMeasurable (q.closedGradient P))
  have hGl : ∀ᵐ w ∂q.atlasMeasure, Tendsto (fun j => q.closedGradient (Q j) w) atTop (𝓝 (g w)) := by
    filter_upwards [ae_all_iff.mpr hQG] with w hw
    simp_rw [hw]
    exact truncatedPowerSlope_tendsto.smul_const _
  have hg : MemLp g 2 q.atlasMeasure := memLp_of_ae_tendsto_bounded _ hgm hB hGl
  let G := hg.toLp g
  have hGa : (G : _ → _) =ᵐ[q.atlasMeasure] g := hg.coeFn_toLp
  have hGt : Tendsto (fun j => q.closedGradient (Q j)) atTop (𝓝 G) := by
    apply l2_tendsto_of_domination _ G (fun w => ‖g w‖)
      (hg.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
    · intro j
      filter_upwards [hQG j,hp] with w hw hp
      rw [hw,norm_smul,Real.norm_eq_abs,abs_of_nonneg (truncatedPowerSlope_nonneg hγ (by positivity) hp)]
      dsimp [g]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hp _))]
      exact mul_le_mul_of_nonneg_right (truncatedPowerSlope_le hγ (by positivity) hp) (norm_nonneg _)
    · filter_upwards [hGa] with w hw
      rw [hw]
    · filter_upwards [hGa,hGl] with w hw hl
      rw [hw]
      exact hl
  let V := hv.toLp (fun x => (q.inclusion P x)^γ)
  have hVa : (V : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion P x)^γ) := hv.coeFn_toLp
  have hVt : Tendsto (fun j => q.inclusion (Q j)) atTop (𝓝 V) := by
    apply l2_tendsto_of_domination _ V (fun x => (q.inclusion P x)^γ)
    · simpa only [Real.norm_eq_abs,sq_abs] using hv.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
    · intro j
      filter_upwards [hQv j,hP] with x hx hp
      rw [hx,Real.norm_eq_abs,abs_of_nonneg (truncatedPower_nonneg (by positivity))]
      exact truncatedPower_le_power hγ (by positivity) hp
    · filter_upwards [hVa,hP] with x hx hp
      rw [hx,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp _)]
    · filter_upwards [ae_all_iff.mpr hQv,hVa,hP] with x hx hv hp
      simp_rw [hx,hv]
      exact truncatedPower_tendsto hγ hp
  obtain ⟨R,hR,hRG⟩ := q.closedGradient_closed V G Q hVt hGt
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact hVa
  · rw [hRG]
    exact hGa

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_EulerMoments
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
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_euler_power (hz : IsCycle T) (P : q.Sobolev) {γ p A n S C : ℝ}
    (hγ : 1 < γ) (hp : 2 < p) (hA : 0 < A) (hn : 0 < n) (hS : 0 < S) (hC : 0 ≤ C)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hv : MemLp (fun x => (q.inclusion P x)^γ) 2 (MassMeasure.currentMassMeasure hT))
    (hs : ∀ R : q.Sobolev,
      MemLp (q.inclusion R) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ∧
      S*(lpNorm (q.inclusion R) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT))^2 ≤
        A*‖q.closedGradient R‖^2+C*‖q.inclusion R‖^2)
    (heuler : ∀ R : q.Sobolev,
      A*inner ℝ (q.closedGradient P) (q.closedGradient R)+n*inner ℝ (q.inclusion P) (q.inclusion R) =
      n*(∫ x, (q.inclusion P x)^(p-1)*q.inclusion R x ∂MassMeasure.currentMassMeasure hT)) :
    ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion P x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w) := by
  classical
  have hQ (j : ℕ) := q.closed_truncated_power hz P hP hγ (show 0 < (j:ℝ)+1 by positivity)
  choose Q hQv hQG using hQ
  have hR (j : ℕ) := q.closed_truncated_power hz P hP (show 1 < 2*γ-1 by linarith)
    (show 0 < (j:ℝ)+1 by positivity)
  choose R hRv hRG using hR
  let M := ∫ x, ((q.inclusion P x)^γ)^2 ∂MassMeasure.currentMassMeasure hT
  have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hvI : Integrable (fun x => ((q.inclusion P x)^γ)^2) (MassMeasure.currentMassMeasure hT) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hv.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hMj (j : ℕ) : ‖q.inclusion (Q j)‖^2 ≤ M := by
    rw [l2_norm_sq]
    simp only [Real.norm_eq_abs,sq_abs]
    apply integral_mono_ae (by simpa only [Real.norm_eq_abs,sq_abs] using
      (Lp.memLp (q.inclusion (Q j))).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)) hvI
    filter_upwards [hQv j,hP] with x hx hp
    rw [hx]
    exact (sq_le_sq₀ (truncatedPower_nonneg (by positivity)) (Real.rpow_nonneg hp _)).mpr
      (truncatedPower_le_power hγ (by positivity) hp)
  obtain ⟨L,B,hL,hB,hLj,hBj⟩ := power_absorption hp hA hn (power_ratio_pos hγ) hS hC hM
    (q.inclusion P) (hs P).1 (fun j => q.inclusion (Q j)) (fun j => ‖q.closedGradient (Q j)‖^2)
    (fun j => (hs (Q j)).1) (fun j => sq_nonneg _) hMj (fun j => (hs (Q j)).2)
    (fun j => q.truncated_power_energy hz P (Q j) (R j) hγ (by positivity) hp hA.le hn.le hP
      (hQv j) (hRv j) (hQG j) (hRG j) (heuler (R j)))
  apply q.closed_power_of_truncated_bound P hγ hP hv Q hQv hQG
  intro j
  exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hBj j)

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_power_iff {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ f x) {a b : ℝ} (ha : 0 < a) :
    MemLp (fun x => (f x)^a) (ENNReal.ofReal b) μ ↔ MemLp f (ENNReal.ofReal (a*b)) μ := by
  have he : ENNReal.ofReal (a*b) / ENNReal.ofReal a = ENNReal.ofReal b := by
    rw [←ENNReal.ofReal_div_of_pos ha]
    congr 1
    field_simp
  have hh := memLp_norm_rpow_iff (p := ENNReal.ofReal (a*b)) hf
    (show ENNReal.ofReal a ≠ 0 by positivity) ENNReal.ofReal_ne_top
  rw [he,ENNReal.toReal_ofReal ha.le] at hh
  have hae : (fun x => ‖f x‖^a) =ᵐ[μ] (fun x => (f x)^a) := by
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg hx]
  exact (memLp_congr_ae hae).symm.trans hh

lemma all_moments_of_power_gain [IsFiniteMeasure μ] {f : α → ℝ} {p : ℝ}
    (hp : 2 < p) (hpos : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hfp : MemLp f (ENNReal.ofReal p) μ)
    (hgain : ∀ a : ℝ, 1 < a → MemLp (fun x => (f x)^a) 2 μ →
      MemLp (fun x => (f x)^a) (ENNReal.ofReal p) μ) :
    ∀ b : ℝ, 0 < b → MemLp f (ENNReal.ofReal b) μ := by
  let l (j : ℕ) : ℝ := p*(p/2)^j
  have hl (j : ℕ) : p ≤ l j := by
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by linarith : 1 ≤ p/2))
  have hlj : ∀ j, MemLp f (ENNReal.ofReal (l j)) μ := by
    intro j
    induction j with
    | zero => simpa only [l,pow_zero,mul_one] using hfp
    | succ j hj =>
      have ha : 1 < l j/2 := by have := hl j; linarith
      have hi : MemLp (fun x => (f x)^(l j/2)) 2 μ := by
        have hb := (memLp_power_iff hfp.aestronglyMeasurable hpos (show 0 < l j/2 by linarith) (b := 2)).mpr
          (show MemLp f (ENNReal.ofReal (l j/2*2)) μ by simpa only [div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hj)
        simpa using hb
      have hh := (memLp_power_iff hfp.aestronglyMeasurable hpos (show 0 < l j/2 by linarith) (b := p)).mp
        (hgain (l j/2) ha hi)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [l]
      rw [pow_succ]
      ring_nf
  have ht : Tendsto l atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < p/2)).const_mul_atTop (by linarith : 0 < p)
  intro b hb
  obtain ⟨j,hj⟩ := Filter.Eventually.exists (ht.eventually (eventually_ge_atTop b))
  exact (hlj j).mono_exponent (ENNReal.ofReal_le_ofReal hj)

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_PolynomialBound
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

lemma closed_all_powers (hz : IsCycle T) (P : q.Sobolev) {p A n S C : ℝ}
    (hp : 2 < p) (hA : 0 < A) (hn : 0 < n) (hS : 0 < S) (hC : 0 ≤ C)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hs : ∀ R : q.Sobolev,
      MemLp (q.inclusion R) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ∧
      S*(lpNorm (q.inclusion R) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT))^2 ≤
        A*‖q.closedGradient R‖^2+C*‖q.inclusion R‖^2)
    (heuler : ∀ R : q.Sobolev,
      A*inner ℝ (q.closedGradient P) (q.closedGradient R)+n*inner ℝ (q.inclusion P) (q.inclusion R) =
      n*(∫ x, (q.inclusion P x)^(p-1)*q.inclusion R x ∂MassMeasure.currentMassMeasure hT)) :
    (∀ b : ℝ, 0 < b → MemLp (q.inclusion P) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT)) ∧
    (∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion P x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w)) := by
  have hgain (a : ℝ) (ha : 1 < a)
      (hv : MemLp (fun x => (q.inclusion P x)^a) 2 (MassMeasure.currentMassMeasure hT)) :
      MemLp (fun x => (q.inclusion P x)^a) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) := by
    obtain ⟨R,hRv,hRG⟩ := q.closed_euler_power hz P ha hp hA hn hS hC hP hv hs heuler
    exact MemLp.ae_eq hRv (hs R).1
  have hm := all_moments_of_power_gain hp hP (hs P).1 hgain
  refine ⟨hm,?_⟩
  intro γ hγ
  rcases hγ.eq_or_lt with hγ | hγ
  · subst γ
    refine ⟨P,?_,?_⟩
    · exact Eventually.of_forall fun _ => (Real.rpow_one _).symm
    · filter_upwards [] with w
      simp only [sub_self,Real.rpow_zero,mul_one,one_smul]
  · have hv := (memLp_power_iff (Lp.aestronglyMeasurable (q.inclusion P)) hP
      (by linarith : 0 < γ) (b := 2)).mpr (hm (γ*2) (by positivity))
    have hv' : MemLp (fun x => (q.inclusion P x)^γ) 2 (MassMeasure.currentMassMeasure hT) := by simpa using hv
    exact q.closed_euler_power hz P hγ hp hA hn hS hC hP hv' hs heuler

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Sharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma omega_pos {n : ℕ} (hn : 0 < n) : 0 < omega n := by
  rw [omega_gamma hn]
  have h : (0:ℝ) < n := by exact_mod_cast hn
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Euler_NormalizedContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_euler_powers_oai {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
    (v : q.Sobolev)
    (hv : ∀ᵐ x ∂currentMassMeasure hT.1, 0 ≤ q.inclusion v x)
    (heuler : ∀ ψ : q.Sobolev,
      (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) :
    (∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (currentMassMeasure hT.1)) ∧
    (∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[currentMassMeasure hT.1] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w)) := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  have hB : 0 < (k+2:ℝ) := by positivity
  have hsphere : 0 < sphereArea (k+2) := by
    unfold sphereArea
    exact mul_pos (by positivity) (omega_pos (by omega))
  let S := (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))
  have hS : 0 < S := mul_pos hB (Real.rpow_pos_of_pos hsphere _)
  obtain ⟨C,hC,hb⟩ := extremal_closed_sobolev hk hX hT hz hm q hd hr hfill hext
    (show 0 < S/2 by positivity) (show S/2 < S by linarith)
  exact q.closed_all_powers hz v hp (div_pos (by norm_num) hk0) hB
    (show 0 < S-S/2 by linarith) hC hv hb heuler

end CAT0Fillings
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.extremal_euler_powers_oai.{u_1} := @OAI.CAT0Fillings.extremal_euler_powers_oai.{u_1}
