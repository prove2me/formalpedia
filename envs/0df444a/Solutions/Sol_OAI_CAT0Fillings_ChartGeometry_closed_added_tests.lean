-- Prove2me | solution 1 for OAI.CAT0Fillings.ChartGeometry.closed_added_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:59:10.82899+00:00
-- url     : https://prove2.me/submissions/809dd0fe-d95d-4457-acc7-a13a71c3398c

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Bivariate
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
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma bivariateValue_ae {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) :
    q.bivariateValue hr hF f =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => F (r x,f x)) :=
  (q.memLp_bivariate hr hF f).coeFn_toLp

lemma lipschitz_bivariateValue {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F) :
    LipschitzWith B (q.bivariateValue hr hF) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (q.bivariateValue hr hF f) (q.bivariateValue hr hF g),
    Lp.coeFn_sub f g,q.bivariateValue_ae hr hF f,q.bivariateValue_ae hr hF g] with x h1 h2 h3 h4
  rw [h1,h2,Pi.sub_apply,Pi.sub_apply,h3,h4]
  simpa only [←dist_eq_norm,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using
    hF.dist_le_mul (r x,f x) (r x,g x)

lemma bivariateValue_value {r u : X → ℝ} {K J : ℝ≥0}
    (hr : LipschitzWith K r) (hu : LipschitzWith J u)
    {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F) :
    q.bivariateValue hr hF (value hu) = value (hF.comp (hr.prodMk hu)) := by
  apply Lp.ext
  filter_upwards [q.bivariateValue_ae hr hF (value hu),
    ((Foundations.boundedLip_of_lipschitz hu).memLp (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp,
    ((Foundations.boundedLip_of_lipschitz (hF.comp (hr.prodMk hu))).memLp
      (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x h1 h2 h3
  change q.bivariateValue hr hF (value hu) x = _ at h1
  change value (hT := hT) hu x = _ at h2
  change value (hT := hT) (hF.comp (hr.prodMk hu)) x = _ at h3
  rw [h1,h2,h3]
  rfl

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
lemma binaryDerivative_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (L M : E →L[ℝ] ℝ) :
    (binaryDerivative a b).comp (L.prod M) = a • L+b • M := by
  ext z
  simp [binaryDerivative]
end CAT0Fillings.ClosedCalculus

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradientFunction_bivariate {r u : X → ℝ} {K J : ℝ≥0}
    (hr : LipschitzWith K r) (hu : LipschitzWith J u)
    {F F₁ F₂ : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (hdF : ∀ t, HasFDerivAt F (binaryDerivative (F₁ t) (F₂ t)) t) :
    q.gradientFunction (fun x => F (r x,u x)) =ᵐ[q.atlasMeasure]
      (fun w => F₁ (r (q.atlasParam w),u (q.atlasParam w)) • q.gradientFunction r w +
        F₂ (r (q.atlasParam w),u (q.atlasParam w)) • q.gradientFunction u w) := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  let C := q.chart i
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨f,hf,hef⟩ := (C.scalar_lipschitzOn hL hr).extend_real
  obtain ⟨g,hg,heg⟩ := (C.scalar_lipschitzOn hL hu).extend_real
  have hecomp : EqOn (C.scalar (fun x => F (r x,u x))) (fun z => F (f z,g z)) C.domain := by
    intro z hz
    simp only [IntegerChart.scalar,dite_eq_left hz]
    rw [←hef hz,←heg hz]
    simp only [IntegerChart.scalar,dite_eq_left hz]
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hf hef,
    ae_fderivWithin_eq_fderiv_extension volume C.borel hg heg,
    ae_fderivWithin_eq_fderiv_extension volume C.borel (hF.comp (hf.prodMk hg)) hecomp,
    hf.ae_differentiableAt.filter_mono ae_restrict_le,
    hg.ae_differentiableAt.filter_mono ae_restrict_le,ae_restrict_mem C.borel]
    with z hr' hu' hcomp hdf hdg hz
  change z ∈ C.domain at hz
  change q.normalizedCovector i (fun x => F (r x,u x)) z =
    F₁ (r (C.paramExtended z),u (C.paramExtended z)) • q.normalizedCovector i r z +
    F₂ (r (C.paramExtended z),u (C.paramExtended z)) • q.normalizedCovector i u z
  have hnf : f z = r (C.paramExtended z) := by
    rw [←hef hz]
    simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz]
  have hng : g z = u (C.paramExtended z) := by
    rw [←heg hz]
    simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz]
  have hd := (hdF (f z,g z)).comp z (hdf.hasFDerivAt.prodMk hdg.hasFDerivAt)
  rw [binaryDerivative_comp] at hd
  dsimp only [normalizedCovector,covector]
  rw [hcomp,hd.fderiv,hr',hu',hnf,hng]
  have he (a b : ℝ) (L M : Euc n →L[ℝ] ℝ) :
      differentialRow (a • L+b • M) = a • differentialRow L+b • differentialRow M := rfl
  rw [he,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,
    WithLp.toLp_add,WithLp.toLp_smul,WithLp.toLp_smul]

lemma gradient_bivariate_ae {r u : X → ℝ} {K J : ℝ≥0}
    (hr : LipschitzWith K r) (hu : LipschitzWith J u)
    {F F₁ F₂ : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (hdF : ∀ t, HasFDerivAt F (binaryDerivative (F₁ t) (F₂ t)) t) :
    q.gradient (hF.comp (hr.prodMk hu)) =ᵐ[q.atlasMeasure]
      (fun w => F₁ (r (q.atlasParam w),u (q.atlasParam w)) • q.gradient hr w +
        F₂ (r (q.atlasParam w),u (q.atlasParam w)) • q.gradient hu w) := by
  filter_upwards [(q.memLp_gradientFunction (hF.comp (hr.prodMk hu))).coeFn_toLp,
    (q.memLp_gradientFunction hr).coeFn_toLp,(q.memLp_gradientFunction hu).coeFn_toLp,
    q.gradientFunction_bivariate hr hu hF hdF] with w h1 h2 h3 h4
  change q.gradient (hF.comp (hr.prodMk hu)) w = _ at h1
  change q.gradient hr w = _ at h2
  change q.gradient hu w = _ at h3
  simp only [Function.comp_def] at h1
  rw [h1,h4,h2,h3]

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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_ClosedBivariate
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

lemma closed_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F F₁ F₂ : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (hdF : ∀ t, HasFDerivAt F (binaryDerivative (F₁ t) (F₂ t)) t)
    (hc₁ : Continuous F₁) (hc₂ : Continuous F₂) {C : ℝ} (hC : 0 ≤ C)
    (hb₁ : ∀ t, |F₁ t| ≤ C) (hb₂ : ∀ t, |F₂ t| ≤ C) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => F₁ (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) • q.gradient hr w +
          F₂ (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) • q.closedGradient P w) := by
  obtain ⟨u,J,hu,hl⟩ := q.exists_lipschitz_approximants P
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
  have ha : ∀ᵐ w ∂q.atlasMeasure,
      Tendsto (fun j => u (s j) (q.atlasParam w)) atTop (𝓝 ((q.inclusion P) (q.atlasParam w))) :=
    q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X =>
      Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x))) hae'
  let b (D : ℝ × ℝ → ℝ) (j : ℕ) (w : ℕ × Euc (k+1)) := D (r (q.atlasParam w),u (s j) (q.atlasParam w))
  let c (D : ℝ × ℝ → ℝ) (w : ℕ × Euc (k+1)) := D (r (q.atlasParam w),q.inclusion P (q.atlasParam w))
  have hb (D : ℝ × ℝ → ℝ) (hD : Continuous D) (j : ℕ) : AEStronglyMeasurable (b D j) q.atlasMeasure :=
    (hD.measurable.comp ((hr.continuous.measurable.comp q.measurable_atlasParam).prodMk
      ((hu (s j)).continuous.measurable.comp q.measurable_atlasParam))).aestronglyMeasurable
  have hc (D : ℝ × ℝ → ℝ) (hD : Continuous D) : AEStronglyMeasurable (c D) q.atlasMeasure :=
    hD.comp_aestronglyMeasurable (((hr.continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable).prodMk
      ((Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving))
  have hbC (D : ℝ × ℝ → ℝ) (hD : ∀ t, |D t| ≤ C) (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b D j w| ≤ C :=
    Eventually.of_forall fun _ => hD _
  have hcC (D : ℝ × ℝ → ℝ) (hD : ∀ t, |D t| ≤ C) : ∀ᵐ w ∂q.atlasMeasure, |c D w| ≤ C :=
    Eventually.of_forall fun _ => hD _
  have hbc (D : ℝ × ℝ → ℝ) (hD : Continuous D) :
      ∀ᵐ w ∂q.atlasMeasure, Tendsto (fun j => b D j w) atTop (𝓝 (c D w)) := by
    filter_upwards [ha] with w hw
    exact (hD.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hw)
  have hgl₁ := mulLp_tendsto (hb F₁ hc₁) (hc F₁ hc₁) hC (hbC F₁ hb₁) (hcC F₁ hb₁)
    (hbc F₁ hc₁) (tendsto_const_nhds (x := q.gradient hr))
  have hgl₂ := mulLp_tendsto (hb F₂ hc₂) (hc F₂ hc₂) hC (hbC F₂ hb₂) (hcC F₂ hb₂)
    (hbc F₂ hc₂) (hg.comp hs.tendsto_atTop)
  have he (j : ℕ) : mulLp (hb F₁ hc₁ j) (hbC F₁ hb₁ j) (q.gradient hr) +
      mulLp (hb F₂ hc₂ j) (hbC F₂ hb₂ j) (q.gradient (hu (s j))) =
      q.gradient (hF.comp (hr.prodMk (hu (s j)))) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (mulLp (hb F₁ hc₁ j) (hbC F₁ hb₁ j) (q.gradient hr))
      (mulLp (hb F₂ hc₂ j) (hbC F₂ hb₂ j) (q.gradient (hu (s j)))),
      mulLp_ae (hb F₁ hc₁ j) (hbC F₁ hb₁ j) (q.gradient hr),
      mulLp_ae (hb F₂ hc₂ j) (hbC F₂ hb₂ j) (q.gradient (hu (s j))),
      q.gradient_bivariate_ae hr (hu (s j)) hF hdF] with w h1 h2 h3 h4
    rw [h1,Pi.add_apply,h2,h3,h4]
  have hgl := hgl₁.add hgl₂
  simp only [Function.comp_def,he] at hgl
  have hvl := (q.lipschitz_bivariateValue hr hF).continuous.tendsto (q.inclusion P) |>.comp (hv.comp hs.tendsto_atTop)
  simp only [Function.comp_def,q.bivariateValue_value] at hvl
  obtain ⟨Q,hQ,hG⟩ := q.closedGradient_closed (q.bivariateValue hr hF (q.inclusion P))
    (mulLp (hc F₁ hc₁) (hcC F₁ hb₁) (q.gradient hr) + mulLp (hc F₂ hc₂) (hcC F₂ hb₂) (q.closedGradient P))
    (fun j => q.lipSobolev (hF.comp (hr.prodMk (hu (s j))))) hvl hgl
  refine ⟨Q,?_,?_⟩
  · rw [hQ]
    exact q.bivariateValue_ae hr hF _
  · rw [hG]
    filter_upwards [Lp.coeFn_add (mulLp (hc F₁ hc₁) (hcC F₁ hb₁) (q.gradient hr))
      (mulLp (hc F₂ hc₂) (hcC F₂ hb₂) (q.closedGradient P)),
      mulLp_ae (hc F₁ hc₁) (hcC F₁ hb₁) (q.gradient hr),
      mulLp_ae (hc F₂ hc₂) (hcC F₂ hb₂) (q.closedGradient P)] with w h1 h2 h3
    rw [h1,Pi.add_apply,h2,h3]

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
lemma binaryDerivative_eq (L : (ℝ × ℝ) →L[ℝ] ℝ) :
    binaryDerivative (L (1,0)) (L (0,1)) = L := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = z.1 • ((1:ℝ),0)+z.2 • ((0:ℝ),1) := by ext <;> simp
  calc
    _ = z.1*L (1,0)+z.2*L (0,1) := by simp [binaryDerivative,mul_comm]
    _ = L (z.1 • ((1:ℝ),0)+z.2 • ((0:ℝ),1)) := by rw [map_add,map_smul,map_smul]; rfl
    _ = L z := congrArg L hz.symm

lemma binary_coeff_bound {F : ℝ × ℝ → ℝ} {B : ℝ≥0} (hF : LipschitzWith B F)
    (t : ℝ × ℝ) :
    |fderiv ℝ F t (1,0)| ≤ B ∧ |fderiv ℝ F t (0,1)| ≤ B := by
  have hb := norm_fderiv_le_of_lipschitz ℝ hF (x₀ := t)
  constructor
  · calc
      |fderiv ℝ F t (1,0)| ≤ ‖fderiv ℝ F t‖*‖((1:ℝ),0)‖ := (fderiv ℝ F t).le_opNorm _
      _ ≤ B := by simpa using hb
  · calc
      |fderiv ℝ F t (0,1)| ≤ ‖fderiv ℝ F t‖*‖((0:ℝ),1)‖ := (fderiv ℝ F t).le_opNorm _
      _ ≤ B := by simpa using hb

lemma hasFDerivAt_binary {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (t : ℝ × ℝ) :
    HasFDerivAt F (binaryDerivative (fderiv ℝ F t (1,0)) (fderiv ℝ F t (0,1))) t := by
  rw [binaryDerivative_eq]
  exact (hF t).hasFDerivAt

end CAT0Fillings.ClosedCalculus
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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_PositiveExtension
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

lemma closed_compact_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w) := by
  obtain ⟨B,hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hF one_ne_zero
  exact q.closed_bivariate hr hB (hasFDerivAt_binary (hF.differentiable one_ne_zero))
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    B.coe_nonneg (fun t => (binary_coeff_bound hB t).1) (fun t => (binary_coeff_bound hB t).2) P

lemma closed_bounded_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (P : q.Sobolev) {M : ℝ}
    (hb : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ‖(r x,q.inclusion P x)‖ ≤ M) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w) := by
  let η : ContDiffBump (0 : ℝ × ℝ) :=
    { rIn := max M 0+1, rOut := max M 0+2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let G (t : ℝ × ℝ) := η t * F t
  have hG : ContDiff ℝ 1 G := η.contDiff.mul hF
  have he (t : ℝ × ℝ) (ht : ‖t‖ ≤ M) : G =ᶠ[𝓝 t] F := by
    have hball : t ∈ Metric.ball 0 η.rIn := by
      simp only [Metric.mem_ball,dist_zero_right]
      dsimp [η]
      exact lt_of_le_of_lt (ht.trans (le_max_left _ _)) (lt_add_one _)
    filter_upwards [η.eventuallyEq_one_of_mem_ball hball] with z hz
    dsimp [G]
    rw [hz,Pi.one_apply,one_mul]
  obtain ⟨Q,hQ,hQG⟩ := q.closed_compact_bivariate hr hG (η.hasCompactSupport.mul_right) P
  refine ⟨Q,?_,?_⟩
  · filter_upwards [hQ,hb] with x hx hb
    rw [hx,(he _ hb).eq_of_nhds]
  · have ha : ∀ᵐ w ∂q.atlasMeasure, ‖(r (q.atlasParam w),q.inclusion P (q.atlasParam w))‖ ≤ M :=
      q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => ‖(r x,q.inclusion P x)‖ ≤ M) hb
    filter_upwards [hQG,ha] with w hw ha
    rw [hw,(he _ ha).fderiv_eq]

end CAT0Fillings.ChartGeometry
end

section

open Set Filter
open scoped Topology

namespace CAT0Fillings.ClosedCalculus

lemma positive_strip_extension {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F {z | 0 < z.2}) {ε N : ℝ}
    (he : 0 < ε) (hN : ε ≤ N) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 1 G ∧
      ∀ z : ℝ × ℝ, z.2 ∈ Icc ε N → G =ᶠ[𝓝 z] F := by
  let c : ℝ := (N+ε)/2
  let η : ContDiffBump c :=
    { rIn := (N-ε)/2+ε/4, rOut := (N-ε)/2+ε/2,
      rIn_pos := by nlinarith, rIn_lt_rOut := by nlinarith }
  let G (z : ℝ × ℝ) := η z.2 * F z
  have hs (z : ℝ × ℝ) (hz : z.2 ≤ 0) : G =ᶠ[𝓝 z] 0 := by
    have ho : z.2 ∉ Metric.closedBall c η.rOut := by
      rw [Metric.mem_closedBall,Real.dist_eq]
      dsimp [c,η]
      have hneg : z.2-(N+ε)/2 < 0 := by nlinarith
      rw [abs_of_neg hneg]
      nlinarith
    have ht : z.2 ∉ tsupport η := by simpa only [η.tsupport_eq] using ho
    have hzero := notMem_tsupport_iff_eventuallyEq.mp ht
    filter_upwards [hzero.comp_tendsto continuous_snd.continuousAt] with w hw
    change η w.2 * F w = 0
    change η w.2 = 0 at hw
    rw [hw,zero_mul]
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : 0 < z.2
    · exact ((η.contDiff.comp contDiff_snd).contDiffAt).mul
        (hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hz))
    · exact contDiffAt_const.congr_of_eventuallyEq (hs z (le_of_not_gt hz))
  refine ⟨G,hG,?_⟩
  intro z hz
  have hb : z.2 ∈ Metric.ball c η.rIn := by
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [c,η]
    constructor <;> nlinarith [hz.1,hz.2]
  have hone := η.eventuallyEq_one_of_mem_ball hb
  filter_upwards [hone.comp_tendsto continuous_snd.continuousAt] with w hw
  dsimp [G]
  change η w.2 = 1 at hw
  rw [hw,one_mul]
end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
lemma min_const_deriv_low {N t : ℝ} (ht : t < N) :
    HasDerivAt (fun z => min z N) 1 t := by
  apply (hasDerivAt_id t).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds ht] with z hz
  exact min_eq_left hz.le
lemma min_const_deriv_high {N t : ℝ} (ht : N < t) :
    HasDerivAt (fun z => min z N) 0 t := by
  apply (hasDerivAt_const t N).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with z hz
  exact min_eq_right hz.le
lemma min_const_lipschitz (N : ℝ) : LipschitzWith 1 (fun z : ℝ => min z N) := by
  simpa using (LipschitzWith.id.min (LipschitzWith.const N))
end CAT0Fillings.ClosedCalculus
namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma closed_min_const (hz : IsCycle T) (P : q.Sobolev) (N : ℝ) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => min (q.inclusion P x) N) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if q.inclusion P (q.atlasParam w) < N then q.closedGradient P w else 0) := by
  have hd (t : ℝ) (ht : t ∉ ({N} : Set ℝ)) : DifferentiableAt ℝ (fun z => min z N) t := by
    rcases lt_or_gt_of_ne (show t ≠ N from ht) with h | h
    · exact (min_const_deriv_low h).differentiableAt
    · exact (min_const_deriv_high h).differentiableAt
  obtain ⟨Q,hQ,hG⟩ := q.closed_chain_countable (min_const_lipschitz N) (countable_singleton N) hd hz P
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hG,q.closedGradient_level_zero hz P N] with w hw hzN
  rw [hw]
  by_cases h : q.inclusion P (q.atlasParam w) < N
  · rw [ite_eq_left h,(min_const_deriv_low h).deriv,one_smul]
  · rw [ite_eq_right h]
    rcases (le_of_not_gt h).eq_or_lt with he | he
    · rw [hzN he.symm,smul_zero]
    · rw [(min_const_deriv_high he).deriv,zero_smul]
end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
lemma max_const_deriv_low {N t : ℝ} (ht : t < N) :
    HasDerivAt (fun z => max z N) 0 t := by
  apply (hasDerivAt_const t N).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds ht] with z hz
  exact max_eq_right hz.le
lemma max_const_deriv_high {N t : ℝ} (ht : N < t) :
    HasDerivAt (fun z => max z N) 1 t := by
  apply (hasDerivAt_id t).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with z hz
  exact max_eq_left hz.le
lemma max_const_lipschitz (N : ℝ) : LipschitzWith 1 (fun z : ℝ => max z N) := by
  simpa using (LipschitzWith.id.max (LipschitzWith.const N))
end CAT0Fillings.ClosedCalculus
namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma closed_max_const (hz : IsCycle T) (P : q.Sobolev) (N : ℝ) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => max (q.inclusion P x) N) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if N < q.inclusion P (q.atlasParam w) then q.closedGradient P w else 0) := by
  have hd (t : ℝ) (ht : t ∉ ({N} : Set ℝ)) : DifferentiableAt ℝ (fun z => max z N) t := by
    rcases lt_or_gt_of_ne (show t ≠ N from ht) with h | h
    · exact (max_const_deriv_low h).differentiableAt
    · exact (max_const_deriv_high h).differentiableAt
  obtain ⟨Q,hQ,hG⟩ := q.closed_chain_countable (max_const_lipschitz N) (countable_singleton N) hd hz P
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hG,q.closedGradient_level_zero hz P N] with w hw hzN
  rw [hw]
  by_cases h : N < q.inclusion P (q.atlasParam w)
  · rw [ite_eq_left h,(max_const_deriv_high h).deriv,one_smul]
  · rw [ite_eq_right h]
    rcases (le_of_not_gt h).eq_or_lt with he | he
    · rw [hzN he,smul_zero]
    · rw [(max_const_deriv_low he).deriv,zero_smul]
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_PositiveBivariate
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

lemma clamp_gradient_scalar {E : Type*} [Zero E] {t ε N : ℝ} (hεN : ε < N) (v : E) :
    (if ε < min t N then (if t < N then v else 0) else 0) =
      (if ε < t ∧ t < N then v else 0) := by
  by_cases he : ε < t <;> by_cases ht : t < N <;> simp [lt_min_iff,he,ht,hεN]
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma closed_clamp (hz : IsCycle T) (P : q.Sobolev) {ε N : ℝ} (hεN : ε < N) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => max (min (q.inclusion P x) N) ε) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if ε < q.inclusion P (q.atlasParam w) ∧ q.inclusion P (q.atlasParam w) < N
          then q.closedGradient P w else 0) := by
  obtain ⟨U,hU,hUG⟩ := q.closed_min_const hz P N
  obtain ⟨V,hV,hVG⟩ := q.closed_max_const hz U ε
  refine ⟨V,?_,?_⟩
  · filter_upwards [hU,hV] with x hu hv
    rw [hv,hu]
  · have hau := q.atlas_preserving.quasiMeasurePreserving.ae
      (p := fun x : X => q.inclusion U x = min (q.inclusion P x) N) hU
    filter_upwards [hau,hUG,hVG] with w hu hug hvg
    rw [hvg,hu,hug]
    exact clamp_gradient_scalar hεN _

lemma closed_positive_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {R : ℝ} (hrange : ∀ x, 0 ≤ r x ∧ r x ≤ R)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F {z | 0 < z.2})
    (P : q.Sobolev) {ε N : ℝ} (he : 0 < ε) (hN : ε ≤ N)
    (hb : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, q.inclusion P x ∈ Icc ε N) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w) := by
  obtain ⟨G,hG,heq⟩ := positive_strip_extension hF he hN
  have hbound : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ‖(r x,q.inclusion P x)‖ ≤ max R N := by
    filter_upwards [hb] with x hx
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (hrange x).1,abs_of_nonneg (he.le.trans hx.1)]
    exact max_le_max (hrange x).2 hx.2
  obtain ⟨Q,hQ,hQG⟩ := q.closed_bounded_bivariate hr hG P hbound
  refine ⟨Q,?_,?_⟩
  · filter_upwards [hQ,hb] with x hx hb
    rw [hx,(heq _ hb).eq_of_nhds]
  · have ha := q.atlas_preserving.quasiMeasurePreserving.ae
      (p := fun x : X => q.inclusion P x ∈ Icc ε N) hb
    filter_upwards [hQG,ha] with w hw ha
    rw [hw,(heq _ ha).fderiv_eq]

lemma closed_positive_clamped_bivariate (hz : IsCycle T)
    {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {R : ℝ} (hrange : ∀ x, 0 ≤ r x ∧ r x ≤ R)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F {z | 0 < z.2})
    (P : q.Sobolev) {ε N : ℝ} (he : 0 < ε) (hN : ε < N) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,max (min (q.inclusion P x) N) ε)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => fderiv ℝ F (r (q.atlasParam w),max (min (q.inclusion P (q.atlasParam w)) N) ε) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),max (min (q.inclusion P (q.atlasParam w)) N) ε) (0,1) •
            (if ε < q.inclusion P (q.atlasParam w) ∧ q.inclusion P (q.atlasParam w) < N
              then q.closedGradient P w else 0)) := by
  obtain ⟨U,hU,hUG⟩ := q.closed_clamp hz P hN
  have hbound : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, q.inclusion U x ∈ Icc ε N := by
    filter_upwards [hU] with x hx
    rw [hx]
    exact ⟨le_max_right _ _,max_le (min_le_right _ _) hN.le⟩
  obtain ⟨Q,hQ,hG⟩ := q.closed_positive_bivariate hr hrange hF U he hN.le hbound
  refine ⟨Q,?_,?_⟩
  · filter_upwards [hQ,hU] with x hq hu
    rw [hq,hu]
  · have hau := q.atlas_preserving.quasiMeasurePreserving.ae
      (p := fun x : X => q.inclusion U x = max (min (q.inclusion P x) N) ε) hU
    filter_upwards [hG,hau,hUG] with w hq hu hug
    simp only [hq,hu,hug]
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_ClosedLimit
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

lemma closed_of_ae_domination (Q : ℕ → q.Sobolev) (f : X → ℝ)
    (g : (ℕ × Euc (k+1)) → Euc (k+1))
    (hf : AEStronglyMeasurable f (MassMeasure.currentMassMeasure hT))
    (hg : AEStronglyMeasurable g q.atlasMeasure)
    (b : X → ℝ) (c : (ℕ × Euc (k+1)) → ℝ)
    (hb : MemLp b 2 (MassMeasure.currentMassMeasure hT)) (hc : MemLp c 2 q.atlasMeasure)
    (hfb : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ‖f x‖ ≤ ‖b x‖)
    (hgc : ∀ᵐ w ∂q.atlasMeasure, ‖g w‖ ≤ ‖c w‖)
    (hQb : ∀ j, ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ‖q.inclusion (Q j) x‖ ≤ ‖b x‖)
    (hQc : ∀ j, ∀ᵐ w ∂q.atlasMeasure, ‖q.closedGradient (Q j) w‖ ≤ ‖c w‖)
    (hQf : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT,
      Tendsto (fun j => q.inclusion (Q j) x) atTop (𝓝 (f x)))
    (hQg : ∀ᵐ w ∂q.atlasMeasure,
      Tendsto (fun j => q.closedGradient (Q j) w) atTop (𝓝 (g w))) :
    ∃ R : q.Sobolev, (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] f ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure] g := by
  have hf' := hb.of_le hf hfb
  have hg' := hc.of_le hg hgc
  let V := hf'.toLp f
  let G := hg'.toLp g
  have hv : Tendsto (fun j => q.inclusion (Q j)) atTop (𝓝 V) := by
    apply l2_tendsto_of_domination _ V (fun x => ‖b x‖)
      (hb.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)) hQb
    · filter_upwards [hf'.coeFn_toLp,hfb] with x hx hb
      rw [hx]
      exact hb
    · filter_upwards [hf'.coeFn_toLp,hQf] with x hx hl
      rw [hx]
      exact hl
  have hgT : Tendsto (fun j => q.closedGradient (Q j)) atTop (𝓝 G) := by
    apply l2_tendsto_of_domination _ G (fun w => ‖c w‖)
      (hc.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)) hQc
    · filter_upwards [hg'.coeFn_toLp,hgc] with w hw hc
      rw [hw]
      exact hc
    · filter_upwards [hg'.coeFn_toLp,hQg] with w hw hl
      rw [hw]
      exact hl
  obtain ⟨R,hR,hRG⟩ := q.closedGradient_closed V G Q hv hgT
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact hf'.coeFn_toLp
  · rw [hRG]
    exact hg'.coeFn_toLp
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_EulerMoments
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

lemma weighted_gradient_memLp (P : q.Sobolev)
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w))
    {a : ℝ} (ha : 0 ≤ a) :
    MemLp (fun w => ((q.inclusion P (q.atlasParam w))^a) • q.closedGradient P w) 2 q.atlasMeasure := by
  obtain ⟨R,hR⟩ := hpow (a+1) (by linarith)
  have hr := (MemLp.ae_eq hR (Lp.memLp (q.closedGradient R))).const_smul ((a+1)⁻¹)
  apply (memLp_congr_ae ?_).mp hr
  filter_upwards [] with w
  simp only [Pi.smul_apply,add_sub_cancel_right,smul_smul]
  rw [←mul_assoc,inv_mul_cancel₀ (by linarith : a+1 ≠ 0),one_mul]

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} [IsFiniteMeasure μ]
lemma power_memLp_two {f : α → ℝ} (hp : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hm : ∀ b : ℝ, 0 < b → MemLp f (ENNReal.ofReal b) μ) {a : ℝ} (ha : 0 ≤ a) :
    MemLp (fun x => (f x)^a) 2 μ := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    simpa only [Real.rpow_zero] using (memLp_const (1:ℝ) : MemLp (fun _ : α => (1:ℝ)) 2 μ)
  · have h := (memLp_power_iff (hm 2 (by norm_num)).aestronglyMeasurable hp ha (b := 2)).mpr
      (hm (a*2) (by positivity))
    simpa using h

lemma polynomial_domination_memLp {f : α → ℝ} {G : α → E} {a : ℝ}
    (hp : ∀ᵐ x ∂μ, 0 ≤ f x) (hf : MemLp (fun x => (f x)^a) 2 μ)
    (hG : MemLp G 2 μ) (hfg : MemLp (fun x => (f x)^a • G x) 2 μ) (C K : ℝ) :
    MemLp (fun x => C*(1+(f x)^a)*(K+‖G x‖)) 2 μ := by
  have hh := (((memLp_const (1:ℝ)).add hf).const_mul (C*K)).add
    ((hG.norm.add hfg.norm).const_mul C)
  apply (memLp_congr_ae ?_).mp hh
  filter_upwards [hp] with x hx
  simp only [Pi.add_apply,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx a)]
  ring
end CAT0Fillings.ClosedCalculus
end

section
open scoped NNReal

namespace CAT0Fillings.ClosedCalculus
lemma norm_binary_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b C K Z : ℝ} {u v : E} (hC : 0 ≤ C) (ha : |a| ≤ C) (hb : |b| ≤ C)
    (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ Z) : ‖a • u+b • v‖ ≤ C*(K+Z) := by
  calc
    _ ≤ ‖a • u‖+‖b • v‖ := norm_add_le _ _
    _ = |a| *‖u‖+|b| *‖v‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ C*K+C*Z := add_le_add (mul_le_mul ha hu (norm_nonneg _) hC)
      (mul_le_mul hb hv (norm_nonneg _) hC)
    _ = _ := by ring
end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter
open scoped Topology

namespace CAT0Fillings.ClosedCalculus
lemma lowerCut_pos (j : ℕ) : 0 < lowerCut j := by unfold lowerCut; positivity
lemma lowerCut_le_one (j : ℕ) : lowerCut j ≤ 1 := by
  rw [lowerCut,div_le_iff₀ (by positivity : 0 < (j:ℝ)+2)]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith
lemma lowerCut_lt_upperCut (j : ℕ) : lowerCut j < upperCut j := by
  apply (lowerCut_le_one j).trans_lt
  dsimp [upperCut]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith
lemma lowerCut_tendsto : Tendsto lowerCut atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0)
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  simpa only [lowerCut,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h
lemma upperCut_tendsto : Tendsto upperCut atTop atTop := by
  exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
lemma cut_eventually {t : ℝ} (ht : 0 < t) :
    ∀ᶠ j in atTop, lowerCut j < t ∧ t < upperCut j :=
  (lowerCut_tendsto.eventually (eventually_lt_nhds ht)).and
    (upperCut_tendsto.eventually (eventually_gt_atTop t))
lemma clamp_pos (j : ℕ) (t : ℝ) : 0 < max (min t (upperCut j)) (lowerCut j) :=
  (lowerCut_pos j).trans_le (le_max_right _ _)
lemma clamp_power_bound {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (j : ℕ) :
    1+(max (min t (upperCut j)) (lowerCut j))^a ≤ 2*(1+t^a) := by
  have hy : max (min t (upperCut j)) (lowerCut j) ≤ max t 1 :=
    max_le_max (min_le_left _ _) (lowerCut_le_one j)
  have hp : (max (min t (upperCut j)) (lowerCut j))^a ≤ 1+t^a := by
    apply (Real.rpow_le_rpow (clamp_pos j t).le hy ha).trans
    rcases le_total t 1 with h | h
    · rw [max_eq_right h,Real.one_rpow]
      exact le_add_of_nonneg_right (Real.rpow_nonneg ht _)
    · rw [max_eq_left h]
      linarith
  nlinarith [Real.rpow_nonneg ht a]
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

lemma closed_positive_polynomial (hz : IsCycle T)
    {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r) {R : ℝ}
    (hrange : ∀ x, 0 ≤ r x ∧ r x ≤ R)
    {F : ℝ × ℝ → ℝ} (hFm : Measurable F)
    (hF : ContDiffOn ℝ 1 F {z | 0 < z.2})
    (hF0 : ∀ z ∈ Icc (0:ℝ) R, F (z,0) = 0)
    (hFcont : ∀ z ∈ Icc (0:ℝ) R,
      Tendsto (fun t => F (z,t)) (𝓝[>] (0:ℝ)) (𝓝 0))
    (hDcont : ∀ z ∈ Icc (0:ℝ) R,
      Tendsto (fun t => fderiv ℝ F (z,t) (1,0)) (𝓝[>] (0:ℝ)) (𝓝 0))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hgrowth : ∀ z ∈ Icc (0:ℝ) R, ∀ t : ℝ, 0 < t →
      |F (z,t)| ≤ C*(1+t^a) ∧
      |fderiv ℝ F (z,t) (1,0)| ≤ C*(1+t^a) ∧
      |fderiv ℝ F (z,t) (0,1)| ≤ C*(1+t^a))
    (P : q.Sobolev)
    (hp : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion P) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hw : MemLp (fun w => (q.inclusion P (q.atlasParam w))^a • q.closedGradient P w) 2 q.atlasMeasure) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if 0 < q.inclusion P (q.atlasParam w) then
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w else 0) := by
  choose Q hQ hG using (fun j : ℕ => q.closed_positive_clamped_bivariate hz hr hrange hF P
    (lowerCut_pos j) (lowerCut_lt_upperCut j))
  let b (x : X) := (2*C)*(1+(q.inclusion P x)^a)
  let c (w : ℕ × Euc (k+1)) := (2*C)*(1+(q.inclusion P (q.atlasParam w))^a)*(K+‖q.closedGradient P w‖)
  let f (x : X) := F (r x,q.inclusion P x)
  let g (w : ℕ × Euc (k+1)) := if 0 < q.inclusion P (q.atlasParam w) then
    fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
    fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w else 0
  have hpair := hr.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable (q.inclusion P))
  have hpairA := hpair.comp_measurePreserving q.atlas_preserving
  have hPA := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hf : AEStronglyMeasurable f (MassMeasure.currentMassMeasure hT) :=
    (hFm.comp_aemeasurable hpair.aemeasurable).aestronglyMeasurable
  have hg : AEStronglyMeasurable g q.atlasMeasure := by
    apply AEStronglyMeasurable.indicator₀
    · exact (((measurable_fderiv_apply_const ℝ F (1,0)).comp_aemeasurable hpairA.aemeasurable).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable (q.gradient hr))).add
        (((measurable_fderiv_apply_const ℝ F (0,1)).comp_aemeasurable hpairA.aemeasurable).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable (q.closedGradient P)))
    · exact aestronglyMeasurable_const.nullMeasurableSet_lt hPA
  have hpa := q.atlas_preserving.quasiMeasurePreserving.ae
    (p := fun x : X => 0 ≤ q.inclusion P x) hp
  have hscalar := power_memLp_two hp hm ha
  have hb : MemLp b 2 (MassMeasure.currentMassMeasure hT) := ((memLp_const (1:ℝ)).add hscalar).const_mul (2*C)
  have hc : MemLp c 2 q.atlasMeasure := polynomial_domination_memLp hpa
    (hscalar.comp_measurePreserving q.atlas_preserving) (Lp.memLp (q.closedGradient P)) hw (2*C) K
  have hdr : ∀ᵐ w ∂q.atlasMeasure, ‖q.gradient hr w‖ ≤ K := by
    filter_upwards [(q.memLp_gradientFunction hr).coeFn_toLp,q.ae_gradientFunction_bound hr] with w he hb
    change q.gradient hr w = _ at he
    rw [he]
    exact hb
  have hdom {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : 0 < s)
      (ha' : 1+s^a ≤ 2*(1+t^a)) : C*(1+s^a) ≤ (2*C)*(1+t^a) := by
    nlinarith [mul_le_mul_of_nonneg_left ha' hC]
  have hbound {w : ℕ × Euc (k+1)} {t : ℝ} {U : Euc (k+1)}
      (hpw : 0 ≤ q.inclusion P (q.atlasParam w)) (ht : 0 < t)
      (hle : 1+t^a ≤ 2*(1+(q.inclusion P (q.atlasParam w))^a))
      (hd : ‖q.gradient hr w‖ ≤ K) (hU : ‖U‖ ≤ ‖q.closedGradient P w‖) :
      ‖fderiv ℝ F (r (q.atlasParam w),t) (1,0) • q.gradient hr w +
        fderiv ℝ F (r (q.atlasParam w),t) (0,1) • U‖ ≤ c w := by
    have hh := hgrowth (r (q.atlasParam w)) (hrange _) t ht
    exact norm_binary_bound (mul_nonneg (mul_nonneg (by norm_num) hC)
      (add_nonneg zero_le_one (Real.rpow_nonneg hpw _)))
      (hh.2.1.trans (hdom hpw ht hle)) (hh.2.2.trans (hdom hpw ht hle)) hd hU
  apply q.closed_of_ae_domination Q f g hf hg b c hb hc
  · filter_upwards [hp] with x hx
    by_cases hx0 : 0 < q.inclusion P x
    · exact ((hgrowth (r x) (hrange x) _ hx0).1.trans
        (hdom hx hx0 (by nlinarith [Real.rpow_nonneg hx a]))).trans (le_abs_self _)
    · have he : q.inclusion P x = 0 := le_antisymm (le_of_not_gt hx0) hx
      simp only [f,he,hF0 _ (hrange x),norm_zero]
      exact norm_nonneg _
  · filter_upwards [hpa,hdr] with w hp hd
    dsimp [g]
    split_ifs with ht
    · exact (hbound hp ht (by nlinarith [Real.rpow_nonneg hp a]) hd le_rfl).trans (le_abs_self (c w))
    · simpa only [norm_zero] using (abs_nonneg (c w))
  · intro j
    filter_upwards [hp,hQ j] with x hx hq
    rw [hq,Real.norm_eq_abs]
    exact ((hgrowth (r x) (hrange x) _ (clamp_pos j _)).1.trans
      (hdom hx (clamp_pos j _) (clamp_power_bound hx ha j))).trans (le_abs_self _)
  · intro j
    filter_upwards [hpa,hdr,hG j] with w hp hd hg
    rw [hg]
    apply (hbound hp (clamp_pos j _) (clamp_power_bound hp ha j) hd ?_).trans (le_abs_self (c w))
    split_ifs
    · exact le_rfl
    · simp
  · filter_upwards [ae_all_iff.mpr hQ,hp] with x hx hp
    by_cases ht : 0 < q.inclusion P x
    · apply (tendsto_congr' ((cut_eventually ht).mono fun j hj => ?_)).mpr tendsto_const_nhds
      rw [hx j,min_eq_left hj.2.le,max_eq_left hj.1.le]
    · have he : q.inclusion P x = 0 := le_antisymm (le_of_not_gt ht) hp
      have hl : Tendsto lowerCut atTop (𝓝[>] (0:ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨lowerCut_tendsto,Eventually.of_forall lowerCut_pos⟩
      have hh := (hFcont (r x) (hrange x)).comp hl
      simpa only [f,he,hF0 _ (hrange x)] using
        (tendsto_congr (fun j => by rw [hx j,he,min_eq_left (show 0 ≤ upperCut j from (lowerCut_pos j).le.trans (lowerCut_lt_upperCut j).le),max_eq_right (lowerCut_pos j).le]; rfl)).mpr hh
  · filter_upwards [ae_all_iff.mpr hG,hpa] with w hw hp
    by_cases ht : 0 < q.inclusion P (q.atlasParam w)
    · apply (tendsto_congr' ((cut_eventually ht).mono fun j hj => ?_)).mpr tendsto_const_nhds
      rw [hw j,min_eq_left hj.2.le,max_eq_left hj.1.le,ite_eq_left hj]
      simp only [g,ite_eq_left ht]
    · have he : q.inclusion P (q.atlasParam w) = 0 := le_antisymm (le_of_not_gt ht) hp
      have hl : Tendsto lowerCut atTop (𝓝[>] (0:ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨lowerCut_tendsto,Eventually.of_forall lowerCut_pos⟩
      have hh := ((hDcont (r (q.atlasParam w)) (hrange _)).comp hl).smul_const (q.gradient hr w)
      simp only [zero_smul] at hh
      simp only [g,ite_eq_right ht]
      apply (tendsto_congr (fun j => ?_)).mpr hh
      rw [hw j,he,min_eq_left (show 0 ≤ upperCut j from (lowerCut_pos j).le.trans (lowerCut_lt_upperCut j).le),max_eq_right (lowerCut_pos j).le]
      simp only [not_lt.mpr (lowerCut_pos j).le,false_and,ite_false, if_false,smul_zero,add_zero]
      rfl
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Conformal_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter
open scoped Topology

namespace CAT0Fillings.Conformal

lemma profile_contDiffOn {m : ℕ} {α β κ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiffOn ℝ 1 (profile m α β κ f) {z | 0 < z.2} := by
  apply ContDiffOn.mul
  · exact (contDiffOn_fst.pow m).mul (contDiffOn_snd.rpow_const_of_ne (fun z hz => ne_of_gt hz))
  · exact hf.contDiffOn.comp ((contDiffOn_const.mul contDiffOn_fst).mul
      (contDiffOn_snd.rpow_const_of_ne (fun z hz => ne_of_gt hz))) (mapsTo_univ _ _)

lemma profile_fderiv {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) (h : ℝ × ℝ) :
    fderiv ℝ (profile m α β κ f) (r,z) h =
      ((m:ℝ)*r^(m-1)*h.1*z^α+r^m*(α*z^(α-1)*h.2))*f (κ*r*z^β)+
      (r^m*z^α)*(deriv f (κ*r*z^β)*(κ*h.1*z^β+(κ*r)*(β*z^(β-1)*h.2))) := by
  have hr := (hasFDerivAt_fst : HasFDerivAt (𝕜 := ℝ) (Prod.fst : ℝ × ℝ → ℝ) _ (r,z))
  have hz' := (hasFDerivAt_snd : HasFDerivAt (𝕜 := ℝ) (Prod.snd : ℝ × ℝ → ℝ) _ (r,z))
  have hp := hr.pow m
  have hα := hz'.rpow_const (p := α) (Or.inl hz.ne')
  have hβ := hz'.rpow_const (p := β) (Or.inl hz.ne')
  have ht := (hr.const_mul κ).mul hβ
  have hf' := (hf (κ*r*z^β)).hasDerivAt.comp_hasFDerivAt (r,z) ht
  have hF := (hp.mul hα).mul hf'
  change HasFDerivAt (profile m α β κ f) _ (r,z) at hF
  rw [hF.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.fst,ContinuousLinearMap.snd,smul_eq_mul,Function.comp_def,Pi.mul_apply,
    nsmul_eq_mul]
  dsimp
  ring

lemma profile_partial_r {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) :
    fderiv ℝ (profile m α β κ f) (r,z) (1,0) =
      (m:ℝ)*r^(m-1)*z^α*f (κ*r*z^β)+κ*r^m*z^(α+β)*deriv f (κ*r*z^β) := by
  rw [profile_fderiv hf hz,Real.rpow_add hz]
  norm_num only [mul_one,mul_zero,add_zero,zero_add,Prod.fst,Prod.snd]
  ring

lemma profile_partial_z {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) :
    fderiv ℝ (profile m α β κ f) (r,z) (0,1) =
      α*r^m*z^(α-1)*f (κ*r*z^β)+β*κ*r^(m+1)*z^(α+β-1)*deriv f (κ*r*z^β) := by
  have he : z^(α+β-1) = z^α*z^(β-1) := by rw [←Real.rpow_add hz]; congr 1; ring
  rw [profile_fderiv hf hz,he,pow_succ]
  norm_num only [mul_one,mul_zero,add_zero,zero_add,Prod.fst,Prod.snd]
  ring

lemma profile_measurable {m : ℕ} {α β κ : ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (profile m α β κ f) := by
  exact (measurable_fst.pow_const m |>.mul (measurable_snd.pow measurable_const)).mul
    (hf.comp ((measurable_const.mul measurable_fst).mul (measurable_snd.pow measurable_const)))

lemma profile_zero {m : ℕ} {α β κ : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (r : ℝ) :
    profile m α β κ f (r,0) = 0 := by simp [profile,Real.zero_rpow hα.ne']

lemma profile_tendsto_zero {m : ℕ} {α β κ r : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun z => profile m α β κ f (r,z)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hpow (q : ℝ) (hq : 0 < q) : Tendsto (fun z : ℝ => z^q) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.zero_rpow hq.ne'] using
      (Real.continuousAt_rpow_const (0:ℝ) q (Or.inr hq.le)).tendsto.mono_left nhdsWithin_le_nhds
  have ht := (hpow β hβ).const_mul (κ*r)
  simp only [mul_zero] at ht
  have h := ((hpow α hα).const_mul (r^m)).mul (hf.continuousAt.tendsto.comp ht)
  simpa only [profile,mul_zero,zero_mul,Function.comp_def] using h

lemma profile_partial_r_tendsto_zero {m : ℕ} {α β κ r : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun z => fderiv ℝ (profile m α β κ f) (r,z) (1,0)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have h1 := (profile_tendsto_zero (m := 0) (κ := κ) (r := r) hf.continuous hα hβ).const_mul ((m:ℝ)*r^(m-1))
  have h2 := (profile_tendsto_zero (m := 0) (κ := κ) (r := r) hd (add_pos hα hβ) hβ).const_mul (κ*r^m)
  have h := h1.add h2
  simp only [mul_zero,add_zero] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [profile_partial_r (hf.differentiable (by norm_num)) hz]
  simp only [profile,pow_zero,one_mul]
  ring
end CAT0Fillings.Conformal
end

section
open Set Filter
open scoped Topology

namespace CAT0Fillings.Conformal

lemma power_domination {z q a : ℝ} (hz : 0 ≤ z) (hq : 0 ≤ q) (hqa : q ≤ a) :
    z^q ≤ 1+z^a := by
  by_cases h : z ≤ 1
  · have hle : z^q ≤ 1 := Real.rpow_le_one hz h hq
    exact hle.trans (le_add_of_nonneg_right (Real.rpow_nonneg hz _))
  · have hz1 : 1 ≤ z := (lt_of_not_ge h).le
    have hle := Real.rpow_le_rpow_of_exponent_le hz1 hqa
    linarith

lemma monomial_bound {r z R B q a c : ℝ} {m : ℕ} {f : ℝ → ℝ}
    (hr : r ∈ Icc (0:ℝ) R) (hz : 0 ≤ z) (hq : 0 ≤ q) (hqa : q ≤ a)
    (hB : 0 ≤ B) (hf : |f c| ≤ B) :
    |r^m*z^q*f c| ≤ (R^m*B)*(1+z^a) := by
  have hR : 0 ≤ R := hr.1.trans hr.2
  rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hr.1 _),abs_of_nonneg (Real.rpow_nonneg hz _)]
  have h1 := mul_le_mul (pow_le_pow_left₀ hr.1 hr.2 m) (power_domination hz hq hqa)
    (Real.rpow_nonneg hz q) (pow_nonneg hR m)
  have h2 := (mul_le_mul_of_nonneg_left hf
    (mul_nonneg (pow_nonneg hr.1 m) (Real.rpow_nonneg hz q))).trans
    (mul_le_mul_of_nonneg_right h1 hB)
  nlinarith [h2]

lemma profile_polynomial_growth {m : ℕ} {α β κ R B : ℝ} {f : ℝ → ℝ}
    (hα : 1 ≤ α) (hβ : 0 < β) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hf : Differentiable ℝ f) (hb : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) R, ∀ z : ℝ, 0 < z →
      |profile m α β κ f (r,z)| ≤ C*(1+z^(α+β)) ∧
      |fderiv ℝ (profile m α β κ f) (r,z) (1,0)| ≤ C*(1+z^(α+β)) ∧
      |fderiv ℝ (profile m α β κ f) (r,z) (0,1)| ≤ C*(1+z^(α+β)) := by
  let C0 := R^m*B
  let C1 := (m:ℝ)*(R^(m-1)*B)+|κ| *(R^m*B)
  let C2 := |α| *(R^m*B)+|β*κ| *(R^(m+1)*B)
  have h0 : 0 ≤ C0 := mul_nonneg (pow_nonneg hR _) hB
  have h1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have h2 : 0 ≤ C2 := by dsimp [C2]; positivity
  refine ⟨C0+C1+C2,by positivity,fun r hr z hz => ?_⟩
  have hs : 0 ≤ 1+z^(α+β) := by positivity
  have hf0 := monomial_bound (m := m) hr hz.le (by linarith : 0 ≤ α) (by linarith : α ≤ α+β)
    hB (hb (κ*r*z^β)).1
  have hf1 := monomial_bound (m := m-1) hr hz.le (by linarith : 0 ≤ α) (by linarith : α ≤ α+β)
    hB (hb (κ*r*z^β)).1
  have hd1 := monomial_bound (m := m) hr hz.le (by linarith : 0 ≤ α+β) le_rfl hB (hb (κ*r*z^β)).2
  have hf2 := monomial_bound (m := m) hr hz.le (by linarith : 0 ≤ α-1) (by linarith : α-1 ≤ α+β)
    hB (hb (κ*r*z^β)).1
  have hd2 := monomial_bound (m := m+1) hr hz.le (by linarith : 0 ≤ α+β-1) (by linarith : α+β-1 ≤ α+β)
    hB (hb (κ*r*z^β)).2
  have hrb : |fderiv ℝ (profile m α β κ f) (r,z) (1,0)| ≤ C1*(1+z^(α+β)) := by
    rw [profile_partial_r hf hz]
    apply (abs_add_le _ _).trans
    have he1 : (m:ℝ)*r^(m-1)*z^α*f (κ*r*z^β) = (m:ℝ)*(r^(m-1)*z^α*f (κ*r*z^β)) := by ring
    have he2 : κ*r^m*z^(α+β)*deriv f (κ*r*z^β) = κ*(r^m*z^(α+β)*deriv f (κ*r*z^β)) := by ring
    rw [he1,he2,abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg m)]
    have H1 := mul_le_mul_of_nonneg_left hf1 (Nat.cast_nonneg (α := ℝ) m)
    have H2 := mul_le_mul_of_nonneg_left hd1 (abs_nonneg κ)
    dsimp [C1]
    simp only [abs_mul] at H1 H2 ⊢
    nlinarith
  have hzb : |fderiv ℝ (profile m α β κ f) (r,z) (0,1)| ≤ C2*(1+z^(α+β)) := by
    rw [profile_partial_z hf hz]
    apply (abs_add_le _ _).trans
    have he1 : α*r^m*z^(α-1)*f (κ*r*z^β) = α*(r^m*z^(α-1)*f (κ*r*z^β)) := by ring
    have he2 : β*κ*r^(m+1)*z^(α+β-1)*deriv f (κ*r*z^β) = (β*κ)*(r^(m+1)*z^(α+β-1)*deriv f (κ*r*z^β)) := by ring
    rw [he1,he2,abs_mul,abs_mul]
    have H1 := mul_le_mul_of_nonneg_left hf2 (abs_nonneg α)
    have H2 := mul_le_mul_of_nonneg_left hd2 (abs_nonneg (β*κ))
    dsimp [C2]
    simp only [abs_mul] at H1 H2 ⊢
    nlinarith
  refine ⟨hf0.trans ?_,hrb.trans ?_,hzb.trans ?_⟩ <;>
    apply mul_le_mul_of_nonneg_right _ hs <;> linarith
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Conformal_Closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Conformal
lemma profileRD_eq {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) :
    fderiv ℝ (profile m α β κ f) (r,z) (1,0) = profileRD m α β κ f r z :=
  profile_partial_r hf hz
lemma profileZD_eq {m : ℕ} {α β κ r z : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : 0 < z) :
    fderiv ℝ (profile m α β κ f) (r,z) (0,1) = profileZD m α β κ f r z :=
  profile_partial_z hf hz
end CAT0Fillings.Conformal
namespace CAT0Fillings.ChartGeometry
open _root_.OAI.CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_conformal (hz : IsCycle T)
    {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r) {R : ℝ}
    (hrange : ∀ x, 0 ≤ r x ∧ r x ≤ R)
    {m : ℕ} {α β κ B : ℝ} {f : ℝ → ℝ}
    (hα : 1 ≤ α) (hβ : 0 < β) (hB : 0 ≤ B)
    (hf : ContDiff ℝ 1 f) (hb : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (P : q.Sobolev)
    (hp : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion P) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w)) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => profile m α β κ f (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if 0 < q.inclusion P (q.atlasParam w) then
          profileRD m α β κ f (r (q.atlasParam w)) (q.inclusion P (q.atlasParam w)) • q.gradient hr w +
          profileZD m α β κ f (r (q.atlasParam w)) (q.inclusion P (q.atlasParam w)) • q.closedGradient P w else 0) := by
  have hR : 0 ≤ R := (hrange (Classical.choice ‹Nonempty X›)).1.trans (hrange _).2
  have hα0 : 0 < α := by linarith
  have ha : 0 ≤ α+β := by linarith
  have hd := hf.differentiable (by norm_num)
  obtain ⟨C,hC,hgrowth⟩ := profile_polynomial_growth (m := m) (κ := κ) hα hβ hR hB hd hb
  obtain ⟨Q,hQ,hG⟩ := q.closed_positive_polynomial hz hr hrange
    (profile_measurable hf.continuous.measurable) (profile_contDiffOn hf)
    (fun z _ => profile_zero hα0 z) (fun _ _ => profile_tendsto_zero hf.continuous hα0 hβ)
    (fun _ _ => profile_partial_r_tendsto_zero hf hα0 hβ) hC ha hgrowth P hp hm
    (q.weighted_gradient_memLp P hpow ha)
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hG] with w hw
  rw [hw]
  split_ifs with ht
  · rw [profileRD_eq hd ht,profileZD_eq hd ht]
  · rfl
end CAT0Fillings.ChartGeometry
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

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_added_tests_oai (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
    {f : ℝ → ℝ} (hb : 0 < β) (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z)) :
    ∃ G Q : q.Sobolev,
      (q.inclusion G : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion v x)^(2+2*β)*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => dist o x^2*(q.inclusion v x)^(1+2*β)*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      (q.closedGradient G : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => Conformal.profileGradient 0 (2+2*β) β κ f (dist o (q.atlasParam z))
          (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => Conformal.profileGradient 2 (1+2*β) β κ f (dist o (q.atlasParam z))
          (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)) := by
  have hr (x : X) : 0 ≤ dist o x ∧ dist o x ≤ Metric.diam (univ : Set X) :=
    ⟨dist_nonneg,Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)⟩
  obtain ⟨G,hG,hDG⟩ := q.closed_conformal hz (LipschitzWith.dist_right o) hr
    (m := 0) (α := 2+2*β) (κ := κ) (by linarith) hb hB hf hfB v hv hm hpow
  obtain ⟨Q,hQ,hDQ⟩ := q.closed_conformal hz (LipschitzWith.dist_right o) hr
    (m := 2) (α := 1+2*β) (κ := κ) (by linarith) hb hB hf hfB v hv hm hpow
  refine ⟨G,Q,?_,?_,hDG,hDQ⟩
  · simpa only [Conformal.profile,pow_zero,one_mul] using hG
  · exact hQ
end CAT0Fillings.ChartGeometry
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.ChartGeometry.closed_added_tests_oai.{u_1} := @OAI.CAT0Fillings.ChartGeometry.closed_added_tests_oai.{u_1}
