-- Prove2me | solution 1 for OAI.Falconer.prepared_pair_of_lower_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:28:34.053739+00:00
-- url     : https://prove2.me/submissions/41a60c27-f8d3-43cd-b0fd-2a9dab5d2f88

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_TwoProjectionPieces_odd_original_caps_partition

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ProjectedDirections
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lifting auxiliary radial directions

The integer-cap argument in `prep:integer-caps` uses the map
`w ↦ P w / ‖P w‖` only where projected separation bounds `‖P w‖`
away from zero. These elementary facts keep the auxiliary direction
map separate from the original Euclidean distance map.
-/

namespace Falconer
open NormedSpace

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalization is Lipschitz on vectors whose norms are bounded below. -/
theorem normalize_dist_le {v w : E} {c : ℝ} (hc : 0 < c)
    (hv : c ≤ ‖v‖) (hw : c ≤ ‖w‖) :
    dist (normalize v) (normalize w) ≤ (2 / c) * dist v w := by
  have hvpos : 0 < ‖v‖ := hc.trans_le hv
  have hwne : w ≠ 0 := norm_pos_iff.mp (hc.trans_le hw)
  have hscale : ‖v‖ * dist (normalize v) (normalize w) ≤ 2 * dist v w := by
    calc
      ‖v‖ * dist (normalize v) (normalize w) =
          dist (‖v‖ • normalize v) (‖v‖ • normalize w) := by
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ dist (‖v‖ • normalize v) (‖w‖ • normalize w) +
          dist (‖w‖ • normalize w) (‖v‖ • normalize w) := dist_triangle _ _ _
      _ = dist v w + |‖w‖ - ‖v‖| := by
        have he : dist (‖w‖ • normalize w) (‖v‖ • normalize w) = |‖w‖ - ‖v‖| := by
          rw [dist_eq_norm, ← sub_smul, norm_smul, norm_normalize hwne,
            Real.norm_eq_abs, mul_one]
        rw [he, norm_smul_normalize, norm_smul_normalize]
      _ ≤ dist v w + dist w v :=
        add_le_add le_rfl (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le w v)
      _ = 2 * dist v w := by rw [dist_comm w v]; ring
  calc
    dist (normalize v) (normalize w) ≤ (2 * dist v w) / ‖v‖ := by
      apply (le_div_iff₀ hvpos).mpr
      simpa only [mul_comm] using hscale
    _ ≤ (2 * dist v w) / c :=
      div_le_div_of_nonneg_left (by positivity) hc hv
    _ = (2 / c) * dist v w := by ring

/-- A linear map commutes with radial directions after re-normalization. -/
theorem normalize_map_radial (P : E →L[ℝ] F) {x y : E} (hxy : y ≠ x) :
    normalize (P (normalize (y - x))) = normalize (P y - P x) := by
  change normalize (P (‖y - x‖⁻¹ • (y - x))) = _
  rw [map_smul, normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))), map_sub]

/-- The auxiliary normalized projection has a uniform Lipschitz bound on the
part of the sphere on which projected separation is available. -/
theorem normalized_projection_dist_le (P : E →L[ℝ] F) {c : ℝ} (hc : 0 < c)
    (hP : ‖P‖ ≤ 1) {v w : E} (hv : c ≤ ‖P v‖) (hw : c ≤ ‖P w‖) :
    dist (normalize (P v)) (normalize (P w)) ≤ (2 / c) * dist v w := by
  apply (normalize_dist_le hc hv hw).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    dist (P v) (P w) ≤ ‖P‖ * dist v w := by
      simpa only [dist_eq_norm, map_sub] using P.le_opNorm (v - w)
    _ ≤ 1 * dist v w := mul_le_mul_of_nonneg_right hP dist_nonneg
    _ = dist v w := one_mul _

end
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensions
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The all-dimensional Falconer statement and the final measure argument

The Falconer distance conjecture concerns compact subsets of Euclidean
space with Hausdorff dimension greater than half the ambient dimension.
The dimension-independent final measure argument reduces positivity of
the original distance set to absolute continuity of a weighted distance
pushforward.
-/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

section Geometry
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem distanceSet_mono {E F : Set X} (h : E ⊆ F) :
    distanceSet E ⊆ distanceSet F := by
  rintro r ⟨x, hx, y, hy, hr⟩
  exact ⟨x, h hx, y, h hy, hr⟩

/-- Isometries, unlike auxiliary orthogonal projections, preserve distances. -/
theorem distanceSet_image_isometry {f : X → Y} (hf : Isometry f) (E : Set X) :
    distanceSet (f '' E) = distanceSet E := by
  ext r
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hr⟩
    exact ⟨x, hx, y, hy, (hf.dist_eq x y).symm.trans hr⟩
  · rintro ⟨x, hx, y, hy, hr⟩
    exact ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy,
      (hf.dist_eq x y).trans hr⟩

/-- Transport a distance theorem through an isometric coordinate chart. -/
theorem positive_distance_of_isometric_model {E : Set X} {F : Set Y}
    {f : Y → X} (hf : Isometry f) (hFE : f '' F ⊆ E)
    (hF : 0 < volume (distanceSet F)) : 0 < volume (distanceSet E) := by
  rw [← distanceSet_image_isometry hf F] at hF
  exact hF.trans_le (measure_mono (distanceSet_mono hFE))

end Geometry

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Availability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Available radial exponents in the original product measure

These definitions record `prep:availability`. A bad set is a measurable
set of original pairs, and each remaining radial fiber is measured using
the original opposite marginal. No fiber is renormalized.
The closure and bootstrap express parts of `prep:thin-upgrade`.
-/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

/-- Restricting a pair relation can only decrease each original radial fiber. -/
theorem RadialCapBound.mono {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G H : Set (Space d × Space d)} {e q : ℝ}
    (h : RadialCapBound μ ν G N e q) (hHG : H ⊆ G) :
    RadialCapBound μ ν H N e q := by
  constructor
  · intro x hx w hw u hu hu1
    have hsets : {y | (x, y) ∈ H ∧ dist (radialDirection x y) w < u} ⊆
        {y | (x, y) ∈ G ∧ dist (radialDirection x y) w < u} := by
      rintro y ⟨hy, hd⟩
      exact ⟨hHG hy, hd⟩
    exact (measure_mono hsets).trans (h.1 x hx w hw u hu hu1)
  · intro y hy w hw u hu hu1
    have hsets : {x | (x, y) ∈ H ∧ dist (radialDirection y x) w < u} ⊆
        {x | (x, y) ∈ G ∧ dist (radialDirection y x) w < u} := by
      rintro x ⟨hx, hd⟩
      exact ⟨hHG hx, hd⟩
    exact (measure_mono hsets).trans (h.2 y hy w hw u hu hu1)

/-- Integer cap bounds continue to hold after the coarse pair filters of
`prep:coarse-filter` are imposed. Only the original bad pairs still lying
inside the new filter need to be deleted. -/
theorem CapAvailable.restrict {d : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {Γ Γ' : ℕ → Set (Space d × Space d)} {q : ℝ}
    (hq : CapAvailable μ ν Γ q) (hΓ' : ∀ N, MeasurableSet (Γ' N))
    (hsub : ∀ N, Γ' N ⊆ Γ N) : CapAvailable μ ν Γ' q := by
  intro e he
  obtain ⟨c, C, hc, hC, K, hK⟩ := hq e he
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  obtain ⟨B, hB, _, hmass, hcap⟩ := hK N hN
  refine ⟨B ∩ Γ' N, hB.inter (hΓ' N), inter_subset_right,
    (measure_mono inter_subset_left).trans hmass, hcap.mono ?_⟩
  intro z hz
  exact ⟨hsub N hz.1, fun hb => hz.2 ⟨hb, hz.1⟩⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of cap bounds from auxiliary projections

The fixed factor in the cap radius can be absorbed in an arbitrarily small
power of the resolution. The center of an original cap need not be in the
domain where normalized projection is Lipschitz; we choose an actual
source direction in a nonempty cap, and double its radius before projecting.
This is the lifting step of `prep:integer-caps`.
-/

namespace Falconer
open Set MeasureTheory Filter NormedSpace
open scoped ENNReal Topology

private theorem radial_ne_diagonal {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    y ≠ x := by
  intro heq
  subst y
  simp [radialDirection] at h
  linarith

private theorem projected_radial_identity {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    NormedSpace.normalize (P (radialDirection x y)) = radialDirection (P x) (P y) := by
  simpa only [radialDirection, NormedSpace.normalize] using
    normalize_map_radial P (radial_ne_diagonal P hc h)

private theorem projected_radial_norm {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    ‖radialDirection (P x) (P y)‖ = 1 := by
  rw [← projected_radial_identity P hc h]
  exact norm_normalize (norm_pos_iff.mp (hc.trans_le h))

/-- Every actual direction in an original radius-`u` cap maps into a radius
`max 1 (4/c) * u` cap about any chosen actual direction in the first cap. -/
theorem projected_radial_cap {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y y₀ w : Space d} {c u : ℝ} (hc : 0 < c) (hP : ‖P‖ ≤ 1)
    (hy : c ≤ ‖P (radialDirection x y)‖)
    (hy₀ : c ≤ ‖P (radialDirection x y₀)‖)
    (hcap : dist (radialDirection x y) w < u)
    (hcap₀ : dist (radialDirection x y₀) w < u) :
    dist (radialDirection (P x) (P y)) (radialDirection (P x) (P y₀)) <
      max 1 (4 / c) * u := by
  have hu : 0 < u := dist_nonneg.trans_lt hcap
  have hL : 0 < 2 / c := div_pos (by norm_num) hc
  have hdist : dist (radialDirection x y) (radialDirection x y₀) < 2 * u := by
    have ht := dist_triangle (radialDirection x y) w (radialDirection x y₀)
    rw [dist_comm w (radialDirection x y₀)] at ht
    linarith
  calc
    dist (radialDirection (P x) (P y)) (radialDirection (P x) (P y₀)) =
        dist (NormedSpace.normalize (P (radialDirection x y))) (NormedSpace.normalize (P (radialDirection x y₀))) := by
      rw [projected_radial_identity P hc hy, projected_radial_identity P hc hy₀]
    _ ≤ (2 / c) * dist (radialDirection x y) (radialDirection x y₀) :=
      normalized_projection_dist_le P hc hP hy hy₀
    _ < (2 / c) * (2 * u) := mul_lt_mul_of_pos_left hdist hL
    _ = (4 / c) * u := by ring
    _ ≤ max 1 (4 / c) * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu.le

/-- A fixed radius enlargement is absorbed into the permitted scale loss. -/
theorem eventually_radius_factor_absorbed {K q a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, K ^ q ≤ ((2 : ℝ) ^ N) ^ a := by
  have ht : Tendsto (fun N : ℕ => ((2 : ℝ) ^ N) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact ht.eventually (eventually_ge_atTop (K ^ q))

private theorem enlarged_cap_scalar {R K u e a q : ℝ}
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hu : 0 ≤ u) (hconstant : K ^ q ≤ R ^ a) :
    R ^ e * (K * u) ^ q ≤ R ^ (e + a) * u ^ q := by
  rw [Real.mul_rpow hK hu, Real.rpow_add (zero_lt_one.trans_le hR)]
  calc
    R ^ e * (K ^ q * u ^ q) = (R ^ e * u ^ q) * K ^ q := by ring
    _ ≤ (R ^ e * u ^ q) * R ^ a := mul_le_mul_of_nonneg_left hconstant
      (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le hR).le e) (Real.rpow_nonneg hu q))
    _ = R ^ e * R ^ a * u ^ q := by ring

/-- A cap estimate for the projected source law bounds a fiber of the
original law. Source labels remain distinct even when their images coincide. -/
theorem projected_fiber_cap_bound {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (ν : ProbabilityMeasure (Space d)) (H : Set (Space d)) (J : Set (Space k))
    (x : Space d) {R c e a q : ℝ}
    (hR : 1 ≤ R) (hc : 0 < c) (hP : ‖P‖ ≤ 1) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hconstant : (max 1 (4 / c)) ^ q ≤ R ^ a)
    (himage : ∀ y ∈ H, P y ∈ J)
    (hlower : ∀ y ∈ H, c ≤ ‖P (radialDirection x y)‖)
    (hcap : ∀ w : Space k, ‖w‖ = 1 → ∀ u : ℝ, R⁻¹ ≤ u → u ≤ 1 →
      ((ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure (Space k)) : Measure (Space k))
        {y | y ∈ J ∧ dist (radialDirection (P x) y) w < u} ≤
          ENNReal.ofReal (R ^ e * u ^ q)) :
    ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, R⁻¹ ≤ u → u ≤ 1 →
      (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ (e + a) * u ^ q) := by
  intro w _ u hu _
  have hupos : 0 < u := (inv_pos.mpr (zero_lt_one.trans_le hR)).trans_le hu
  let K : ℝ := max 1 (4 / c)
  have hK : 1 ≤ K := le_max_left _ _
  have hscalar := enlarged_cap_scalar (e := e) hR (zero_le_one.trans hK) hupos.le hconstant
  by_cases hsmall : K * u ≤ 1
  · by_cases hex : Set.Nonempty {y | y ∈ H ∧ dist (radialDirection x y) w < u}
    · obtain ⟨y₀, hy₀, hcap₀⟩ := hex
      have hset : {y | y ∈ H ∧ dist (radialDirection x y) w < u} ⊆
          P ⁻¹' {y | y ∈ J ∧ dist (radialDirection (P x) y)
            (radialDirection (P x) (P y₀)) < K * u} := by
        rintro y ⟨hy, hycap⟩
        exact ⟨himage y hy, projected_radial_cap P hc hP (hlower y hy)
          (hlower y₀ hy₀) hycap hcap₀⟩
      have hpre := (measure_mono (μ := (ν : Measure (Space d))) hset).trans
        (Measure.le_map_apply P.continuous.measurable.aemeasurable _)
      have hrad : R⁻¹ ≤ K * u := hu.trans (le_mul_of_one_le_left hupos.le hK)
      exact hpre.trans ((hcap _ (projected_radial_norm P hc (hlower y₀ hy₀))
        _ hrad hsmall).trans (ENNReal.ofReal_le_ofReal hscalar))
    · simp only [Set.not_nonempty_iff_eq_empty.mp hex, measure_empty]
      exact bot_le
  · have hmass : (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤ 1 := by
      exact (measure_mono (subset_univ _)).trans_eq (measure_univ : (ν : Measure (Space d)) univ = 1)
    have hpow : 1 ≤ (K * u) ^ q := Real.one_le_rpow (le_of_not_ge hsmall) hq
    have hepow : 1 ≤ R ^ e := Real.one_le_rpow hR he
    have hone : 1 ≤ R ^ (e + a) * u ^ q := by
      have : 1 ≤ R ^ e * (K * u) ^ q := by nlinarith
      exact this.trans hscalar
    exact hmass.trans (by simpa using (ENNReal.ofReal_le_ofReal hone))

private theorem map_mem_support {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (μ : ProbabilityMeasure (Space d)) {x : Space d}
    (hx : x ∈ (μ : Measure (Space d)).support) :
    P x ∈ ((μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure (Space k)) : Measure (Space k)).support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  have hpre : P ⁻¹' U ∈ 𝓝 x := P.continuous.continuousAt.preimage_mem_nhds hU
  exact ((Measure.mem_support_iff_forall _).mp hx _ hpre).trans_le
    (Measure.le_map_apply P.continuous.measurable.aemeasurable U)

/-- Pull back both cap estimates through a fixed auxiliary projection. -/
theorem RadialCapBound.pullback {d k N : ℕ} (P : Space d →L[ℝ] Space k)
    (μ ν : ProbabilityMeasure (Space d))
    {G : Set (Space d × Space d)} {G' : Set (Space k × Space k)} {c e a q : ℝ}
    (hc : 0 < c) (hP : ‖P‖ ≤ 1) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hconstant : (max 1 (4 / c)) ^ q ≤ ((2 : ℝ) ^ N) ^ a)
    (hG : G ⊆ Prod.map P P ⁻¹' G')
    (hlower : ∀ z ∈ G, c ≤ ‖P (radialDirection z.1 z.2)‖ ∧
      c ≤ ‖P (radialDirection z.2 z.1)‖)
    (hcap : RadialCapBound (μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) G' N e q) :
    RadialCapBound μ ν G N (e + a) q := by
  have hR : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  constructor
  · intro x hx
    exact projected_fiber_cap_bound P ν {y | (x, y) ∈ G} {y | (P x, y) ∈ G'} x
      hR hc hP he hq hconstant
      (fun y hy => hG hy) (fun y hy => (hlower (x, y) hy).1)
      (hcap.1 (P x) (map_mem_support P μ hx))
  · intro y hy
    exact projected_fiber_cap_bound P μ {x | (x, y) ∈ G} {x | (x, P y) ∈ G'} y
      hR hc hP he hq hconstant
      (fun x hx => hG hx) (fun x hx => (hlower (x, y) hx).2)
      (hcap.2 (P y) (map_mem_support P ν hy))

/-- Auxiliary projected cap estimates lift to the original pair law.
The deletion is the preimage of the projected bad set intersected with the
original pair filter; its mass is bounded by the projected product mass. -/
theorem CapAvailable.pullback {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (μ ν : ProbabilityMeasure (Space d))
    {Γ : ℕ → Set (Space d × Space d)} {Γ' : ℕ → Set (Space k × Space k)} {c q : ℝ}
    (hc : 0 < c) (hP : ‖P‖ ≤ 1) (hq : 0 ≤ q)
    (hΓ : ∀ N, MeasurableSet (Γ N))
    (hΓsub : ∀ N, Γ N ⊆ Prod.map P P ⁻¹' Γ' N)
    (hlower : ∀ N, ∀ z ∈ Γ N, c ≤ ‖P (radialDirection z.1 z.2)‖ ∧
      c ≤ ‖P (radialDirection z.2 z.1)‖)
    (hcap : CapAvailable (μ.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := P) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Γ' q) :
    CapAvailable μ ν Γ q := by
  intro e he
  obtain ⟨c₀, C, hc₀, hC, N₀, hN₀⟩ := hcap (e / 2) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (eventually_radius_factor_absorbed (K := max 1 (4 / c)) (q := q)
      (by linarith : (0 : ℝ) < e / 2))
  refine ⟨c₀, C, hc₀, hC, max N₀ N₁, ?_⟩
  intro N hN
  obtain ⟨B', hB', hB'sub, hmass, hgood⟩ := hN₀ N ((le_max_left _ _).trans hN)
  let B := Γ N ∩ Prod.map P P ⁻¹' B'
  have hPmeas : Measurable (P : Space d → Space k) := P.continuous.measurable
  have hB : MeasurableSet B := (hΓ N).inter (hB'.preimage (hPmeas.prodMap hPmeas))
  have hpre := Measure.le_map_apply
    (μ := (μ : Measure (Space d)).prod (ν : Measure (Space d)))
    (hPmeas.prodMap hPmeas).aemeasurable B'
  rw [← Measure.map_prod_map _ _ hPmeas hPmeas] at hpre
  have hmassB : ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ N) ^ (-c₀)) :=
    (measure_mono inter_subset_right).trans (hpre.trans hmass)
  refine ⟨B, hB, inter_subset_left, hmassB, ?_⟩
  have hgoodsub : Γ N \ B ⊆ Prod.map P P ⁻¹' (Γ' N \ B') := by
    intro z hz
    exact ⟨hΓsub N hz.1, fun hb => hz.2 ⟨hz.1, hb⟩⟩
  have hbound := hgood.pullback P μ ν hc hP (by linarith) hq
    (hN₁ N ((le_max_right _ _).trans hN)) hgoodsub
    (fun z hz => hlower N z hz.1)
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereRotations
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance of the actual sphere measure

The sphere measure used by the energy is defined from Euclidean volume.
Its invariance follows directly by transporting its defining truncated
cones through a linear isometry.
-/

namespace Falconer
open Set MeasureTheory
open scoped Pointwise

theorem sphereMap_cone_preimage {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (s : Set (Sphere d)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereMap e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨r,hr,e w,⟨sphereMap e w,hw,rfl⟩,by simp⟩
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,heq⟩
    refine ⟨r,hr,e.symm w,⟨sphereMap e.symm w,?_,rfl⟩,?_⟩
    · change sphereMap e (sphereMap e.symm w) ∈ s
      convert hw using 1
      all_goals try with_reducible_and_instances rfl
      apply Subtype.ext
      simp [sphereMap]
    · have hh := congrArg e.symm heq
      simpa using hh

theorem sphereMap_measurePreserving {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) :
    MeasurePreserving (sphereMap e) (sphereMeasure d) (sphereMeasure d) := by
  have hm := (continuous_sphereMap e).measurable
  refine ⟨hm,Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs]
  unfold sphereMeasure
  rw [Measure.toSphere_apply' _ (hm hs),Measure.toSphere_apply' _ hs,sphereMap_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric Euclidean coordinates on the actual finite-dimensional slice -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem slicePointCoordinates_continuous (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) : Continuous (slicePointCoordinates V hm) :=
  (sliceCoordinates V hm).continuous.comp V.orthogonalProjectionOnto.continuous

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-vector Gaussian band estimates for the angular slicing construction -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianBandConstant_pos : 0 < gaussianBandConstant := by
  unfold gaussianBandConstant
  positivity

theorem standard_gaussian_density_bound :
    gaussianReal 0 1 ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) • (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards with x
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  have he : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem standard_gaussian_band {r : ℝ} (_hr : 0 ≤ r) :
    gaussianReal 0 1 (Icc (-r) r) ≤ ENNReal.ofReal (gaussianBandConstant*r) := by
  calc
    _ ≤ (ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) • (volume : Measure ℝ)) (Icc (-r) r) :=
      standard_gaussian_density_bound _
    _ = _ := by
      rw [Measure.smul_apply,smul_eq_mul,Real.volume_Icc,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold gaussianBandConstant
      ring

theorem gaussian_unit_inner_law {w : Space d} (hw : ‖w‖ = 1) :
    (stdGaussian (Space d)).map (innerSL ℝ w) = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,
    innerSL_apply_norm,hw]
  norm_num

theorem gaussian_unit_inner_band {w : Space d} (hw : ‖w‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space d) {x | |inner ℝ w x| ≤ r} ≤ ENNReal.ofReal (gaussianBandConstant*r) := by
  have he : {x : Space d | |inner ℝ w x| ≤ r} = (innerSL ℝ w) ⁻¹' Icc (-r) r := by
    ext x
    simp only [mem_ofPred_eq,mem_preimage,mem_Icc,innerSL_apply_apply,abs_le]
  rw [he,← Measure.map_apply (innerSL ℝ w).continuous.measurable measurableSet_Icc,
    gaussian_unit_inner_law hw]
  exact standard_gaussian_band hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Gaussian rows used for the random-subspace estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRows_one_band {w : Space d} (hw : ‖w‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    gaussianRows d h {A | ∀ i, |inner ℝ w (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianBandConstant*r)^h) := by
  have he : {A : Fin h → Space d | ∀ i, |inner ℝ w (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | |inner ℝ w x| ≤ r}) := by ext A; simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal (gaussianBandConstant*r) :=
      Finset.prod_le_prod' (fun _ _ => gaussian_unit_inner_band hw hr)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ← ENNReal.ofReal_pow (mul_nonneg gaussianBandConstant_pos.le hr)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_Energy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem energyScale_pos (n : ℕ) : 0 < energyScale n := by
  unfold energyScale
  positivity

theorem energy_scale_identity (n : ℕ) (u s C : ℝ) :
    (energyScale n/2)^(-u) * (C*(2*energyScale n)^s) =
      ((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n := by
  have ha : (0 : ℝ) < 1/2 := by norm_num
  have hn := energyScale_pos n
  have hadd : (energyScale n)^(-u)*(energyScale n)^s = (energyScale n)^(s-u) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hpow : (energyScale n)^(s-u) = ((1/2 : ℝ)^(s-u))^n := by
    rw [energyScale, ← Real.rpow_natCast_mul ha.le, mul_comm,
      Real.rpow_mul_natCast ha.le]
  rw [show energyScale n/2 = energyScale n*(1/2) by ring,
    Real.mul_rpow hn.le ha.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le]
  calc
    _ = ((1/2 : ℝ)^(-u)*C*2^s) * ((energyScale n)^(-u)*(energyScale n)^s) := by ring
    _ = _ := by rw [hadd,hpow]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianProjection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Gaussian law of an orthogonal projection -/

namespace Falconer
open MeasureTheory ProbabilityTheory
variable {d : ℕ}

theorem gaussian_orthogonal_projection (V : Submodule ℝ (Space d)) :
    (stdGaussian (Space d)).map V.orthogonalProjectionOnto = stdGaussian V := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply,integral_map V.orthogonalProjectionOnto.continuous.measurable.aemeasurable
    (by fun_prop)]
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← charFun_apply,charFun_stdGaussian,charFun_stdGaussian]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapBox
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rectangular bound for the cone under a spherical cap -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

theorem mem_northCapBox {n : ℕ} {r : ℝ} {z : Space (n+1)} :
    z ∈ northCapBox n r ↔ |z 0| ≤ 1 ∧ ∀ i : Fin n, |z i.succ| ≤ r := by
  simp only [northCapBox,mem_preimage,mem_Icc,Pi.le_def,Fin.forall_fin_succ,
    Fin.cons_zero,Fin.cons_succ,abs_le]
  aesop

theorem northCapBox_volume (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space (n+1))) (northCapBox n r) =
      ENNReal.ofReal (2*(2*r)^n) := by
  unfold northCapBox
  rw [← Measure.map_apply (PiLp.volume_preserving_ofLp (Fin (n+1))).measurable measurableSet_Icc,
    (PiLp.volume_preserving_ofLp (Fin (n+1))).map_eq,Real.volume_Icc_pi,Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,sub_neg_eq_add,← two_mul,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hr),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem north_cap_cone_subset {n : ℕ} {r : ℝ} :
    Ioo (0:ℝ) 1 • ((↑) '' (ball (gnomonicChart (0 : Space n)) r)) ⊆ northCapBox n r := by
  rintro z ⟨t,ht,y,⟨w,hw,rfl⟩,rfl⟩
  rw [mem_northCapBox]
  have hw0 : |(w:Space (n+1)) 0| ≤ 1 := by
    simpa only [sphere_norm,Real.norm_eq_abs] using PiLp.norm_apply_le (w:Space (n+1)) 0
  constructor
  · change |t*(w:Space (n+1)) 0| ≤ 1
    rw [abs_mul,abs_of_pos ht.1]
    exact (mul_le_mul_of_nonneg_left hw0 ht.1.le).trans (by simpa only [mul_one] using ht.2.le)
  · intro i
    have hd : ‖(w:Space (n+1))-northLift (0:Space n)‖ < r := by
      simpa only [mem_ball,Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
    have hi : |(w:Space (n+1)) i.succ| < r := by
      have hh := (PiLp.norm_apply_le ((w:Space (n+1))-northLift (0:Space n)) i.succ).trans_lt hd
      simpa [northLift] using hh
    change |t*(w:Space (n+1)) i.succ| ≤ r
    rw [abs_mul,abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans hi.le

theorem north_sphere_cap_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) (ball (gnomonicChart (0:Space n)) r) ≤
      ENNReal.ofReal (((n+1:ℕ):ℝ)*2*(2*r)^n) := by
  rw [sphereMeasure,Measure.toSphere_apply' _ measurableSet_ball]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  apply (mul_le_mul_right (measure_mono north_cap_cone_subset) _).trans_eq
  rw [northCapBox_volume n hr,← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedLaws
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotation transport of the original point and direction laws -/

namespace Falconer
open Set Metric MeasureTheory
variable {d : ℕ}

theorem sphereMap_distance (e : Space d ≃ₗᵢ[ℝ] Space d) (v w : Sphere d) :
    dist (sphereMap e v) (sphereMap e w) = dist v w := e.dist_map v w

theorem sphereMap_symm_apply (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e (sphereMap e.symm w) = w := by
  apply Subtype.ext
  exact e.apply_symm_apply w

theorem sphereMap_apply_symm (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e.symm (sphereMap e w) = w := by
  apply Subtype.ext
  exact e.symm_apply_apply w

theorem sphereMap_ball_preimage (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    sphereMap e ⁻¹' ball w r = ball (sphereMap e.symm w) r := by
  rw [← sphereMap_symm_apply e w]
  ext v
  simp only [mem_preimage,mem_ball,sphereMap_distance]
  rw [sphereMap_apply_symm e]

theorem rotated_direction_ball (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) (ball w r) = ν (ball (sphereMap e.symm w) r) := by
  rw [Measure.map_apply (continuous_sphereMap e).measurable measurableSet_ball,
    sphereMap_ball_preimage]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual spherical surface measure has its dimensional cap bound -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem sphere_cap_bound (n : ℕ) (w : Sphere (n+1)) {r : ℝ} (hr : 0 ≤ r) :
    sphereMeasure (n+1) (ball w r) ≤
      ENNReal.ofReal ((((n+1:ℕ):ℝ)*(2:ℝ)^(n+1))*r^n) := by
  let north := gnomonicChart (0 : Space n)
  let e := (ℝ ∙ ((north:Space (n+1))-(w:Space (n+1))))ᗮ.reflection
  have he : e (north:Space (n+1)) = (w:Space (n+1)) :=
    Submodule.reflection_sub ((sphere_norm north).trans (sphere_norm w).symm)
  have he' : sphereMap e north = w := Subtype.ext he
  have hrw := rotated_direction_ball (sphereMeasure (n+1)) e w r
  rw [(sphereMap_measurePreserving e).map_eq] at hrw
  have hn : sphereMap e.symm w = north := by rw [← he',sphereMap_apply_symm]
  rw [hn] at hrw
  rw [hrw]
  apply (north_sphere_cap_bound n hr).trans_eq
  congr 1
  rw [mul_pow,pow_succ]
  ring

theorem surfaceMeasure_ball_bound (n : ℕ) (w : Space (n+1)) (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    surfaceMeasure (n+1) (ball w r) ≤
      ENNReal.ofReal ((((n+1:ℕ):ℝ)*(2:ℝ)^(n+1))*r^n) := by
  let w' : Sphere (n+1) := ⟨w,by simpa only [mem_sphere,dist_zero_right] using hw⟩
  rw [surfaceMeasure,Measure.map_apply measurable_subtype_coe measurableSet_ball]
  exact sphere_cap_bound n w' hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_StartingMeasures
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Starting measures in all dimensions

The published input is Frostman's lemma, Mattila, *Geometry of Sets and
Measures in Euclidean Spaces* (Cambridge, 1995), Theorem 8.8, p. 112.
Only compact sets above the critical half-dimensional threshold are used.
Selecting an exponent strictly between the threshold and the Hausdorff
dimension, and normalizing the nonzero finite measure, gives the exact
specialization below, stated as a hypothesis for the conditional argument.

The separation and restriction arguments are proved here in the original
ambient dimension. They do not use a projection of the distance set.
-/

namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

theorem noAtoms_of_frostman {d : ℕ} (μ : Measure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hb : FrostmanBallBound (μ : Measure (Space d)) s C) : NullSingletonClass μ := by
  constructor
  intro x
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C * r^s)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa only [Real.zero_rpow hs.ne', mul_zero, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb x r hr)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanRieszEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Riesz energies from the original all-dimensional Frostman bounds

The dyadic potential argument and its scalar scale identity are dimension
independent.
-/

namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

theorem euclidean_riesz_kernel_majorant (x y : Space d) {u : ℝ} (hu : 0 < u) (hxy : x ≠ y) :
    (edist x y)^(-u) ≤ 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have heq : (edist x y)^(-u) = ENNReal.ofReal ((dist x y)^(-u)) := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_pos hd]
  rw [heq]
  by_cases hlarge : 1 ≤ dist x y
  · have hle : (dist x y)^(-u) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        hlarge (neg_nonpos.mpr hu.le)
    exact (show ENNReal.ofReal ((dist x y)^(-u)) ≤ 1 by
      simpa using ENNReal.ofReal_le_ofReal hle).trans (le_add_right le_rfl)
  · obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hd (le_of_not_ge hlarge)
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
    have hlo' : energyScale n/2 < dist x y := by
      simpa [energyScale,pow_succ,div_eq_mul_inv] using hlo
    have hball : y ∈ ball x (2*energyScale n) := by
      rw [mem_ball, dist_comm]
      have hpos := energyScale_pos n
      change dist x y ≤ energyScale n at hhi
      linarith
    have hpoint : (edist x y)^(-u) ≤ euclideanEnergyMajorant x u n y := by
      rw [heq, euclideanEnergyMajorant, indicator_of_mem hball]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
        (div_pos (energyScale_pos n) (by norm_num)) hlo'.le (by linarith))
    rw [heq] at hpoint
    exact hpoint.trans ((ENNReal.le_tsum (f := fun index : ℕ =>
      euclideanEnergyMajorant x u index y) n).trans (le_add_left le_rfl))

theorem euclidean_energy_term_integral_le (μ : Measure (Space d)) {s C : ℝ}
    (hb : FrostmanBallBound μ s C) (x : Space d) (u : ℝ) (n : ℕ) :
    (∫⁻ y, euclideanEnergyMajorant x u n y ∂μ) ≤
      ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s) *
        (ENNReal.ofReal ((1/2 : ℝ)^(s-u)))^n := by
  rw [euclideanEnergyMajorant, lintegral_indicator_const measurableSet_ball]
  calc
    _ ≤ ENNReal.ofReal ((energyScale n/2)^(-u)) *
        ENNReal.ofReal (C*(2*energyScale n)^s) :=
      mul_le_mul_right (hb x _ (mul_pos (by norm_num) (energyScale_pos n))) _
    _ = ENNReal.ofReal (((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (energyScale_pos n).le (by norm_num)) _), energy_scale_identity]
    _ = _ := by
      rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem euclidean_riesz_potential_uniform_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : FrostmanBallBound μ s C) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, euclideanRieszPotential μ u x ≤ B := by
  let := noAtoms_of_frostman μ (hu.trans hus) hb
  let a : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(s-u))
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s)
  have ha : a < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hus))
  have hsum : (∑' n : ℕ, a^n) < ∞ := tsum_geometric_lt_top.mpr ha
  refine ⟨μ univ + D * ∑' n : ℕ, a^n,
    ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum⟩,?_⟩
  intro x
  have hm (n : ℕ) : Measurable (euclideanEnergyMajorant x u n) :=
    measurable_const.indicator measurableSet_ball
  have hxy : ∀ᵐ y ∂μ, x ≠ y := by
    rw [ae_iff]
    simp
  calc
    euclideanRieszPotential μ u x ≤ ∫⁻ y, 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hxy] with y hy
      exact euclidean_riesz_kernel_majorant x y hu hy
    _ = μ univ + ∑' n : ℕ, ∫⁻ y, euclideanEnergyMajorant x u n y ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hm n).aemeasurable)]
      simp
    _ ≤ μ univ + ∑' n : ℕ, D*a^n :=
      add_le_add_right (ENNReal.tsum_le_tsum (fun n => euclidean_energy_term_integral_le μ hb x u n)) _
    _ = _ := by rw [ENNReal.tsum_mul_left]

theorem rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : FrostmanBallBound μ s C) :
    PlanarFalconer.rieszEnergyOn μ u < ∞ := by
  obtain ⟨B,hB,hpot⟩ := euclidean_riesz_potential_uniform_bound μ hu hus hb
  rw [PlanarFalconer.rieszEnergyOn,lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ _ : Space d, B ∂μ := lintegral_mono hpot
    _ = B*μ univ := lintegral_const B
    _ < ∞ := ENNReal.mul_lt_top hB (measure_lt_top μ univ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DensityTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Truncation of radial densities

The integer-cap step `prep:integer-caps` deletes pairs on which either
radial density exceeds a threshold. These lemmas estimate the deleted
original product mass by the Lp moments and bound every remaining fiber
by the threshold times the angular reference measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

private theorem ennreal_le_threshold_tail {t T : ℝ≥0∞} {p : ℝ}
    (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) (ht : T ≤ t) :
    t ≤ T ^ (1 - p) * t ^ p := by
  have hpow := ENNReal.rpow_le_rpow ht (by linarith : 0 ≤ p - 1)
  have hprod : T ^ (p - 1) * t ≤ t ^ p := by
    calc
      T ^ (p - 1) * t ≤ t ^ (p - 1) * t := mul_le_mul_left hpow t
      _ = t ^ ((p - 1) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
      _ = t ^ p := by congr 1; ring
  have hcancel : T ^ (1 - p) * T ^ (p - 1) = 1 := by
    rw [← ENNReal.rpow_add _ _ hT.ne' hTtop]
    convert (ENNReal.rpow_zero : T ^ (0 : ℝ) = 1) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  calc
    t = (T ^ (1 - p) * T ^ (p - 1)) * t := by rw [hcancel, one_mul]
    _ = T ^ (1 - p) * (T ^ (p - 1) * t) := mul_assoc _ _ _
    _ ≤ T ^ (1 - p) * t ^ p := mul_le_mul_right hprod _

/-- The density mass above `T` is bounded by `T^(1-p)` times its pth moment. -/
theorem density_tail_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (σ.withDensity f) {a | T < f a} ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ := by
  have hS : MeasurableSet {a | T < f a} := measurableSet_lt measurable_const hf
  rw [withDensity_apply _ hS]
  calc
    (∫⁻ a in {a | T < f a}, f a ∂σ) ≤
        ∫⁻ a in {a | T < f a}, T ^ (1 - p) * f a ^ p ∂σ := by
      apply setLIntegral_mono' hS
      intro a ha
      exact ennreal_le_threshold_tail hT hTtop hp ha.le
    _ = T ^ (1 - p) * ∫⁻ a in {a | T < f a}, f a ^ p ∂σ :=
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)
    _ ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ :=
      mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- Truncation leaves a density bounded by the threshold on every cap. -/
theorem truncated_density_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    (T : ℝ≥0∞) (S : Set A) (hS : MeasurableSet S) :
    (σ.withDensity f) (S ∩ {a | f a ≤ T}) ≤ T * σ S := by
  have hlow : MeasurableSet {a | f a ≤ T} := measurableSet_le hf measurable_const
  rw [withDensity_apply _ (hS.inter hlow)]
  calc
    (∫⁻ a in S ∩ {a | f a ≤ T}, f a ∂σ) ≤
        ∫⁻ _ in S ∩ {a | f a ≤ T}, T ∂σ := by
      apply setLIntegral_mono' (hS.inter hlow)
      intro a ha
      exact ha.2
    _ = T * σ (S ∩ {a | f a ≤ T}) := by simp
    _ ≤ T * σ S := mul_le_mul_right (measure_mono inter_subset_left) T

theorem measurableSet_densityFailure {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    {f : X × A → ℝ≥0∞} {r : X × Y → A} (hf : Measurable f) (hr : Measurable r)
    (T : ℝ≥0∞) : MeasurableSet (densityFailure f r T) :=
  measurableSet_lt measurable_const (hf.comp (measurable_fst.prodMk hr))

/-- Fubini measures failure using the original source marginal and the
original pin marginal. There is no normalization of individual fibers. -/
theorem density_failure_product_mass {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (σ : Measure A)
    (f : X × A → ℝ≥0∞) (r : X × Y → A) (hf : Measurable f) (hr : Measurable r)
    (hdensity : ∀ᵐ x ∂μ, ν.map (fun y => r (x, y)) = σ.withDensity (fun a => f (x, a)))
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (μ.prod ν) (densityFailure f r T) ≤
      T ^ (1 - p) * ∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ := by
  rw [Measure.prod_apply (measurableSet_densityFailure hf hr T)]
  calc
    (∫⁻ x, ν (Prod.mk x ⁻¹' densityFailure f r T) ∂μ) ≤
        ∫⁻ x, T ^ (1 - p) * ∫⁻ a, f (x, a) ^ p ∂σ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hdensity] with x hx
      have hfx : Measurable (fun a => f (x, a)) := hf.comp (measurable_const.prodMk measurable_id)
      have hrx : Measurable (fun y => r (x, y)) := hr.comp (measurable_const.prodMk measurable_id)
      change ν ((fun y => r (x, y)) ⁻¹' {a | T < f (x, a)}) ≤ _
      rw [← Measure.map_apply hrx (measurableSet_lt measurable_const hfx), hx]
      exact density_tail_mass σ _ hfx hT hTtop hp
    _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)

/-- Any additional pair restriction preserves the truncated fiber bound. -/
theorem truncated_radial_fiber {Y A : Type*} [MeasurableSpace Y] [MeasurableSpace A]
    (ν : Measure Y) (σ : Measure A) (f : A → ℝ≥0∞) (r : Y → A)
    (hf : Measurable f) (hr : Measurable r) (hdensity : ν.map r = σ.withDensity f)
    (T : ℝ≥0∞) (H : Set Y) (hH : ∀ y ∈ H, f (r y) ≤ T)
    (S : Set A) (hS : MeasurableSet S) :
    ν (H ∩ r ⁻¹' S) ≤ T * σ S := by
  have hset : H ∩ r ⁻¹' S ⊆ r ⁻¹' (S ∩ {a | f a ≤ T}) := by
    rintro y ⟨hy, hSy⟩
    exact ⟨hSy, hH y hy⟩
  calc
    ν (H ∩ r ⁻¹' S) ≤ ν (r ⁻¹' (S ∩ {a | f a ≤ T})) := measure_mono hset
    _ = (σ.withDensity f) (S ∩ {a | f a ≤ T}) := by
      rw [← hdensity, Measure.map_apply hr (hS.inter (measurableSet_le hf measurable_const))]
    _ ≤ T * σ S := truncated_density_mass σ f hf T S hS

/-- Deleting the failures in both orientations costs the sum of the two
integrated radial pth moments. -/
theorem bilateral_density_failure_mass {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (σ : Measure A)
    (f : X × A → ℝ≥0∞) (r : X × Y → A) (g : Y × A → ℝ≥0∞) (s : Y × X → A)
    (hf : Measurable f) (hr : Measurable r) (hg : Measurable g) (hs : Measurable s)
    (hfdensity : ∀ᵐ x ∂μ, ν.map (fun y => r (x, y)) = σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂ν, μ.map (fun x => s (y, x)) = σ.withDensity (fun a => g (y, a)))
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (μ.prod ν) (densityFailure f r T ∪ Prod.swap ⁻¹' densityFailure g s T) ≤
      T ^ (1 - p) * ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ) +
        ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂ν) := by
  have hswap : (μ.prod ν) (Prod.swap ⁻¹' densityFailure g s T) =
      (ν.prod μ) (densityFailure g s T) := by
    rw [← Measure.map_apply measurable_swap (measurableSet_densityFailure hg hs T), Measure.prod_swap]
  calc
    _ ≤ (μ.prod ν) (densityFailure f r T) + (μ.prod ν) (Prod.swap ⁻¹' densityFailure g s T) :=
      measure_union_le _ _
    _ = (μ.prod ν) (densityFailure f r T) + (ν.prod μ) (densityFailure g s T) := by rw [hswap]
    _ ≤ T ^ (1 - p) * (∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ) +
        T ^ (1 - p) * ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂ν :=
      add_le_add (density_failure_product_mass μ ν σ f r hf hr hfdensity hT hTtop hp)
        (density_failure_product_mass ν μ σ g s hg hs hgdensity hT hTtop hp)
    _ = _ := (mul_add _ _ _).symm

/-- The threshold `R^(e/2)` gives a positive power saving in deleted mass
for every `p > 1`; its exponent is exactly `e * (p - 1) / 2`. -/
theorem exists_density_tail_power_bound (M : ℝ≥0∞) (hM : M ≠ ∞)
    {e p : ℝ} (he : 0 < e) (hp : 1 < p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ R : ℝ, 0 < R →
      (ENNReal.ofReal (R ^ (e / 2))) ^ (1 - p) * M ≤
        ENNReal.ofReal (C * R ^ (-c)) := by
  refine ⟨e * (p - 1) / 2, M.toReal + 1, by positivity, by positivity, ?_⟩
  intro R hR
  have hpow : (e / 2) * (1 - p) = -(e * (p - 1) / 2) := by ring
  calc
    (ENNReal.ofReal (R ^ (e / 2))) ^ (1 - p) * M =
        ENNReal.ofReal (M.toReal * R ^ (-(e * (p - 1) / 2))) := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hR _),
        ← Real.rpow_mul hR.le, hpow]
      conv_lhs => rw [← ENNReal.ofReal_toReal hM]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((M.toReal + 1) * R ^ (-(e * (p - 1) / 2))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hR.le _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_IntegerCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer cap availability from radial densities

This is the measure-theoretic truncation step of `prep:integer-caps`.
An angular reference measure with cap exponent `q` and integrable radial
`p`th density moments give availability of `q` for the original pair law.
The radial density hypothesis is the input supplied by the radial
projection theorem.
-/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

private theorem density_threshold_cap_scalar {R A e q u : ℝ}
    (hR : 0 < R) (hu : 0 < u) (hconstant : A ≤ R ^ (e / 2)) :
    R ^ (e / 2) * (A * u ^ q) ≤ R ^ e * u ^ q := by
  calc
    R ^ (e / 2) * (A * u ^ q) = A * (R ^ (e / 2) * u ^ q) := by ring
    _ ≤ R ^ (e / 2) * (R ^ (e / 2) * u ^ q) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = R ^ e * u ^ q := by
      rw [← mul_assoc, ← Real.rpow_add hR]
      congr 2
      ring

private theorem truncated_radial_cap_of_density {d : ℕ}
    (ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f : Space d → ℝ≥0∞) (x : Space d) (hf : Measurable f)
    (hdensity : (ν : Measure (Space d)).map (radialDirection x) = σ.withDensity f)
    {R A e q : ℝ} (hR : 0 < R) (_hA : 0 < A)
    (hconstant : A ≤ R ^ (e / 2))
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (H : Set (Space d))
    (hH : ∀ y ∈ H, f (radialDirection x y) ≤ ENNReal.ofReal (R ^ (e / 2))) :
    ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ e * u ^ q) := by
  intro w hw u hu hu1
  have hr : Measurable (radialDirection x) := by
    unfold radialDirection
    fun_prop
  have htrunc := truncated_radial_fiber (ν : Measure (Space d)) σ f
    (radialDirection x) hf hr hdensity (ENNReal.ofReal (R ^ (e / 2))) H hH
    (Metric.ball w u) measurableSet_ball
  calc
    (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ (e / 2)) * σ (Metric.ball w u) := by
      exact htrunc
    _ ≤ ENNReal.ofReal (R ^ (e / 2)) * ENNReal.ofReal (A * u ^ q) :=
      mul_le_mul_right (hσ w hw u hu hu1) _
    _ = ENNReal.ofReal (R ^ (e / 2) * (A * u ^ q)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    _ ≤ ENNReal.ofReal (R ^ e * u ^ q) :=
      ENNReal.ofReal_le_ofReal (density_threshold_cap_scalar hR hu hconstant)

/-- Bilateral radial densities with finite integrated `p`th moments make
the reference cap exponent available in the original product measure.
The deleted mass has a positive power saving for every requested loss.
Null strips of exceptional pins make the resulting bounds valid at every
support pin, although the radial density identities hold only almost everywhere. -/
theorem capAvailable_of_bilateral_radial_densities {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f g : Space d × Space d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfdensity : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) =
        σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) =
        σ.withDensity (fun a => g (y, a)))
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂(ν : Measure (Space d))) ≠ ∞) :
    CapAvailable μ ν (fun _ => Set.univ) q := by
  obtain ⟨Xbad, hXsub, hXm, hXnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hfdensity)
  obtain ⟨Ybad, hYsub, hYm, hYnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hgdensity)
  intro e he
  obtain ⟨c, C, hc, hC, htail⟩ := exists_density_tail_power_bound _ hmoment he hp
  have hconstant : ∀ᶠ N : ℕ in atTop, A ≤ ((2 : ℝ) ^ N) ^ (e / 2) := by
    simpa using (eventually_radius_factor_absorbed (K := A) (q := 1)
      (a := e / 2) (by linarith))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hconstant
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  let R : ℝ := (2 : ℝ) ^ N
  let T : ℝ≥0∞ := ENNReal.ofReal (R ^ (e / 2))
  let r : Space d × Space d → Space d := fun z => radialDirection z.1 z.2
  let B₀ : Set (Space d × Space d) := densityFailure f r T ∪
    Prod.swap ⁻¹' densityFailure g r T
  let Z : Set (Space d × Space d) := (Xbad ×ˢ Set.univ) ∪ (Set.univ ×ˢ Ybad)
  let B : Set (Space d × Space d) := B₀ ∪ Z
  have hR : 0 < R := by dsimp [R]; positivity
  have hT : 0 < T := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR _)
  have hTtop : T ≠ ∞ := ENNReal.ofReal_ne_top
  have hB₀ : MeasurableSet B₀ :=
    (measurableSet_densityFailure hf measurable_radialDirection_joint T).union
      ((measurableSet_densityFailure hg measurable_radialDirection_joint T).preimage
        measurable_swap)
  have hZ : MeasurableSet Z :=
    (hXm.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hYm)
  have hZnull : ((μ : Measure (Space d)).prod (ν : Measure (Space d))) Z = 0 := by
    apply measure_union_null <;> simp only [Measure.prod_prod, hXnull, hYnull, zero_mul, mul_zero]
  have hB : MeasurableSet B := hB₀.union hZ
  refine ⟨B, hB, subset_univ _, ?_, ?_⟩
  · calc
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B ≤
          ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B₀ +
          ((μ : Measure (Space d)).prod (ν : Measure (Space d))) Z := measure_union_le _ _
      _ = ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B₀ := by rw [hZnull, add_zero]
      _ ≤ ENNReal.ofReal (C * R ^ (-c)) :=
        (bilateral_density_failure_mass (μ : Measure (Space d))
          (ν : Measure (Space d)) σ f r g r hf measurable_radialDirection_joint hg
          measurable_radialDirection_joint hfdensity hgdensity hT hTtop hp).trans (htail R hR)
  · constructor
    · intro x _ w hw u hu hu1
      by_cases hxb : x ∈ Xbad
      · have hempty : {y | (x, y) ∈ Set.univ \ B ∧
              dist (radialDirection x y) w < u} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro y hy
          exact hy.1.2 (Or.inr (Or.inl ⟨hxb, Set.mem_univ y⟩))
        rw [hempty, measure_empty]
        exact bot_le
      have hdensity : (ν : Measure (Space d)).map (radialDirection x) =
          σ.withDensity (fun a => f (x, a)) := by
        by_contra h
        exact hxb (hXsub h)
      have hupos : 0 < u := (inv_pos.mpr hR).trans_le hu
      have hlow : ∀ y ∈ {y | (x, y) ∈ Set.univ \ B},
          f (x, radialDirection x y) ≤ T := by
        intro y hy
        by_contra h
        have hbad : (x, y) ∈ B := Or.inl (Or.inl (lt_of_not_ge h))
        exact hy.2 hbad
      exact truncated_radial_cap_of_density ν σ (fun a => f (x, a)) x
        (hf.comp (measurable_const.prodMk measurable_id)) hdensity hR hA
        (hK N hN) hσ {y | (x, y) ∈ Set.univ \ B} hlow w hw u hupos hu1
    · intro y _ w hw u hu hu1
      by_cases hyb : y ∈ Ybad
      · have hempty : {x | (x, y) ∈ Set.univ \ B ∧
              dist (radialDirection y x) w < u} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro x hx
          exact hx.1.2 (Or.inr (Or.inr ⟨Set.mem_univ x, hyb⟩))
        rw [hempty, measure_empty]
        exact bot_le
      have hdensity : (μ : Measure (Space d)).map (radialDirection y) =
          σ.withDensity (fun a => g (y, a)) := by
        by_contra h
        exact hyb (hYsub h)
      have hupos : 0 < u := (inv_pos.mpr hR).trans_le hu
      have hlow : ∀ x ∈ {x | (x, y) ∈ Set.univ \ B},
          g (y, radialDirection y x) ≤ T := by
        intro x hx
        by_contra h
        have hbad : (x, y) ∈ B := Or.inl (Or.inr (lt_of_not_ge h))
        exact hx.2 hbad
      exact truncated_radial_cap_of_density μ σ (fun a => g (y, a)) y
        (hg.comp (measurable_const.prodMk measurable_id)) hdensity hR hA
        (hK N hN) hσ {x | (x, y) ∈ Set.univ \ B} hlow w hw u hupos hu1

/-- The same density truncation works inside every measurable coarse pair
filter; its fibers continue to use the original source marginals. -/
theorem capAvailable_of_bilateral_radial_densities_restrict {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f g : Space d × Space d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfdensity : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) =
        σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) =
        σ.withDensity (fun a => g (y, a)))
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂(ν : Measure (Space d))) ≠ ∞)
    (Γ : ℕ → Set (Space d × Space d)) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ q :=
  (capAvailable_of_bilateral_radial_densities μ ν σ f g hf hg hfdensity hgdensity hp
    hA hσ hmoment).restrict hΓ (fun _ => subset_univ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMoments
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From radial projection moments to integer cap availability

The radial pushforwards form a Markov kernel. Mathlib's kernel
Radon--Nikodym derivative supplies a jointly measurable version of all
their angular densities, so separate choices of densities are unnecessary.
This connects the published radial-moment input to the truncation step.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

theorem radialKernel_apply {d : ℕ} (ν : ProbabilityMeasure (Space d)) (x : Space d) :
    radialKernel ν x = (ν : Measure (Space d)).map (radialDirection x) := by
  have hr : Measurable (radialDirection x) := by
    unfold radialDirection
    fun_prop
  ext S hS
  rw [radialKernel, Kernel.map_apply' _ measurable_radialDirection_joint _ hS,
    Kernel.id_prod_apply' _ _ (hS.preimage measurable_radialDirection_joint),
    Kernel.const_apply, Measure.map_apply hr hS]
  rfl

theorem radialKernelDensity_withDensity {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) [IsFiniteMeasure σ] (x : Space d)
    (h : (ν : Measure (Space d)).map (radialDirection x) ≪ σ) :
    (ν : Measure (Space d)).map (radialDirection x) =
      σ.withDensity (fun a => radialKernelDensity ν σ (x, a)) := by
  have hker : radialKernel ν x ≪ Kernel.const (Space d) σ x := by
    simpa only [radialKernel_apply, Kernel.const_apply] using h
  have heq := Kernel.withDensity_rnDeriv_eq hker
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _),
    Kernel.const_apply, radialKernel_apply] at heq
  exact heq.symm

theorem radialKernelDensity_moment {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) [IsFiniteMeasure σ] (x : Space d) (p : ℝ) :
    (∫⁻ a, radialKernelDensity ν σ (x, a) ^ p ∂σ) =
      ∫⁻ a, ((ν : Measure (Space d)).map (radialDirection x)).rnDeriv σ a ^ p ∂σ := by
  apply lintegral_congr_ae
  have heq := Kernel.rnDeriv_eq_rnDeriv_measure (κ := radialKernel ν)
    (η := Kernel.const (Space d) σ) (a := x)
  simp only [Kernel.const_apply, radialKernel_apply] at heq
  filter_upwards [heq] with a ha
  exact congrArg (fun t : ℝ≥0∞ => t ^ p) ha

/-- A.e. absolute continuity and integrated radial `p`th moments imply the
integer cap conclusion. These are precisely the density data used from
the radial projection input; the geometric cap bound on `σ` is explicit. -/
theorem capAvailable_of_radial_moments {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d)) [IsFiniteMeasure σ]
    (hν : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) ≪ σ)
    (hμ : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) ≪ σ)
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a,
      ((ν : Measure (Space d)).map (radialDirection x)).rnDeriv σ a ^ p ∂σ
        ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a,
        ((μ : Measure (Space d)).map (radialDirection y)).rnDeriv σ a ^ p ∂σ
          ∂(ν : Measure (Space d))) ≠ ∞)
    (Γ : ℕ → Set (Space d × Space d)) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ q := by
  apply capAvailable_of_bilateral_radial_densities_restrict μ ν σ
    (radialKernelDensity ν σ) (radialKernelDensity μ σ)
    (measurable_radialKernelDensity ν σ) (measurable_radialKernelDensity μ σ)
    _ _ hp hA hσ _ Γ hΓ
  · filter_upwards [hν] with x hx
    exact radialKernelDensity_withDensity ν σ x hx
  · filter_upwards [hμ] with y hy
    exact radialKernelDensity_withDensity μ σ y hy
  · simpa only [radialKernelDensity_moment] using hmoment

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMomentParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed exponents used in Orponen's published radial moment estimate -/

namespace Falconer

theorem radial_moment_parameters {h δ : ℝ} (hh : 1 ≤ h) (hδ : 0 < δ) (hδ1 : δ < 1) :
    h < h+δ/2 ∧ h+δ/2 < h+1 ∧ 0 < h-δ/4 ∧ h-δ/4 < h ∧
    2*h-(h+δ/2) < h-δ/4 ∧ 1 < 1+δ/(8*h) ∧
    1+δ/(8*h) < 2-(h-δ/4)/h ∧
    1+δ/(8*h) < (h-δ/4)/(2*h-(h+δ/2)) := by
  have hh0 : 0 < h := by linarith only [hh]
  have hden : 0 < 2*h-(h+δ/2) := by linarith only [hh,hδ1]
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,?_,?_,?_⟩
  · have := div_pos hδ (mul_pos (by norm_num : (0:ℝ) < 8) hh0)
    linarith
  · have he : 2-(h-δ/4)/h = 1+δ/(4*h) := by
      field_simp
      ring
    rw [he]
    have hd := div_lt_div_of_pos_left hδ
      (by positivity : 0 < 4*h) (by linarith : 4*h < 8*h)
    linarith only [hd]
  · apply (lt_div_iff₀ hden).mpr
    have he : (1+δ/(8*h))*(2*h-(h+δ/2)) = h-3*δ/8-δ^2/(16*h) := by
      field_simp
      ring
    rw [he]
    have hn : 0 ≤ δ^2/(16*h) := by positivity
    linarith only [hδ,hn]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_PublishedIntegerCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer cap availability from the precise published radial moment -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem integer_caps_of_published_radial (hpublished : PublishedRadialMoment)
    (h : ℕ) (hh : 1 ≤ h) (μ ν : ProbabilityMeasure (Space (h+1)))
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hμK : IsCompact (μ : Measure (Space (h+1))).support)
    (hνK : IsCompact (ν : Measure (Space (h+1))).support)
    (hsep : Disjoint (μ : Measure (Space (h+1))).support (ν : Measure (Space (h+1))).support)
    (hμfrost : FrostmanBallBound (μ : Measure (Space (h+1))) ((h:ℝ)+δ) C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space (h+1))) ((h:ℝ)+δ) C)
    (Γ : ℕ → Set (Space (h+1) × Space (h+1))) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ (h:ℝ) := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  obtain ⟨hs,_,ht0,ht,_,hp,_,_⟩ := radial_moment_parameters hh' hδ hδ1
  have hsrc : (h:ℝ)+δ/2 < (h:ℝ)+δ := by linarith only [hδ]
  have hpin : (h:ℝ)-δ/4 < (h:ℝ)+δ := by linarith only [hδ]
  have hμs := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space (h+1)))
    (show 0 < (h:ℝ)+δ/2 by linarith only [hh',hs]) hsrc hμfrost
  have hνs := rieszEnergyOn_lt_top_of_frostman (ν : Measure (Space (h+1)))
    (show 0 < (h:ℝ)+δ/2 by linarith only [hh',hs]) hsrc hνfrost
  have hμt := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space (h+1))) ht0 hpin hμfrost
  have hνt := rieszEnergyOn_lt_top_of_frostman (ν : Measure (Space (h+1))) ht0 hpin hνfrost
  have hμν := hpublished h hh μ ν δ hδ hδ1 hμK hνK hsep hμs hνt
  have hνμ := hpublished h hh ν μ δ hδ hδ1 hνK hμK hsep.symm hνs hμt
  apply capAvailable_of_radial_moments μ ν (surfaceMeasure (h+1)) hνμ.1 hμν.1 hp
    (show 0 < (((h+1:ℕ):ℝ)*(2:ℝ)^(h+1)) by positivity) _
    (ENNReal.add_lt_top.mpr ⟨hνμ.2,hμν.2⟩).ne Γ hΓ
  intro w hw r hr _
  simpa only [Real.rpow_natCast] using surfaceMeasure_ball_bound h w hw hr.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectedSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated projected supports give the directional lower bound for cap lifting -/
namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem projected_direction_lower_of_dist (P : Space d →L[ℝ] Space m)
    (x y : Space d) {a b : ℝ} (ha : 0 < a)
    (hprojected : a ≤ dist (P x) (P y)) (hsource : dist x y ≤ b) :
    a/b ≤ ‖P (radialDirection x y)‖ := by
  have hne : x ≠ y := by
    intro h
    rw [h,dist_self] at hprojected
    exact (not_le_of_gt ha) hprojected
  have hd : 0 < dist x y := dist_pos.mpr hne
  have hid : ‖P (radialDirection x y)‖ = dist (P x) (P y) / dist x y := by
    rw [radialDirection,map_smul,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_norm]
    rw [map_sub,← dist_eq_norm,← dist_eq_norm,dist_comm y x,dist_comm (P y) (P x)]
    rw [div_eq_mul_inv,mul_comm]
  rw [hid]
  calc
    a/b ≤ a/dist x y := div_le_div_of_nonneg_left ha.le hd hsource
    _ ≤ dist (P x) (P y) / dist x y := (div_le_div_iff_of_pos_right hd).mpr hprojected

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PointRieszPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Riesz potential bound from small balls at one fixed center -/
namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

theorem rieszSmallBallBound_lt_top {s C u : ℝ} (hus : u < s) :
    rieszSmallBallBound s C u < ∞ := by
  have ha : ENNReal.ofReal ((1/2:ℝ)^(s-u)) < 1 :=
    ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hus))
  exact ENNReal.add_lt_top.mpr ⟨by simp,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (tsum_geometric_lt_top.mpr ha)⟩

theorem singleton_eq_zero_of_point_frostman (μ : Measure (Space d)) (x : Space d)
    {s C : ℝ} (hs : 0 < s)
    (hb : ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) : μ {x} = 0 := by
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C * r^s)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa only [Real.zero_rpow hs.ne', mul_zero, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb r hr)

theorem point_energy_term_integral_le (μ : Measure (Space d)) {s C : ℝ}
    (x : Space d) (hb : ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) (u : ℝ) (n : ℕ) :
    (∫⁻ y, euclideanEnergyMajorant x u n y ∂μ) ≤
      ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s) *
        (ENNReal.ofReal ((1/2 : ℝ)^(s-u)))^n := by
  rw [euclideanEnergyMajorant, lintegral_indicator_const measurableSet_ball]
  calc
    _ ≤ ENNReal.ofReal ((energyScale n/2)^(-u)) *
        ENNReal.ofReal (C*(2*energyScale n)^s) :=
      mul_le_mul_right (hb _ (mul_pos (by norm_num) (energyScale_pos n))) _
    _ = ENNReal.ofReal (((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (energyScale_pos n).le (by norm_num)) _), energy_scale_identity]
    _ = _ := by
      rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem point_riesz_potential_bound (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (x : Space d) {s C u : ℝ} (hu : 0 < u) (hus : u < s)
    (hb : ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    euclideanRieszPotential μ u x ≤ rieszSmallBallBound s C u := by
  let a : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(s-u))
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s)
  have hm (n : ℕ) : Measurable (euclideanEnergyMajorant x u n) :=
    measurable_const.indicator measurableSet_ball
  have hxy : ∀ᵐ y ∂μ, x ≠ y := by
    rw [ae_iff]
    simpa using singleton_eq_zero_of_point_frostman μ x (hu.trans hus) hb
  calc
    euclideanRieszPotential μ u x ≤ ∫⁻ y, 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hxy] with y hy
      exact euclidean_riesz_kernel_majorant x y hu hy
    _ = μ univ + ∑' n : ℕ, ∫⁻ y, euclideanEnergyMajorant x u n y ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hm n).aemeasurable)]
      simp
    _ ≤ μ univ + ∑' n : ℕ, D*a^n :=
      add_le_add_right (ENNReal.tsum_le_tsum (fun n => point_energy_term_integral_le μ x hb u n)) _
    _ = _ := by rw [ENNReal.tsum_mul_left, measure_univ]; rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BoundedPotentialCompact
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive compact restriction with bounded measurable potential -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem positive_compact_bounded_function (μ : ProbabilityMeasure (Space d))
    (F : Space d → ℝ≥0∞) (hF : Measurable F) (hfinite : ∀ᵐ x ∂(μ : Measure (Space d)), F x < ∞) :
    ∃ K : Set (Space d), IsCompact K ∧ 0 < (μ : Measure (Space d)) K ∧
      ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, F x ≤ ENNReal.ofReal B := by
  let S (n : ℕ) : Set (Space d) := {x | F x ≤ ENNReal.ofReal (n+1 : ℝ)}
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le hF measurable_const
  have hfull : (⋃ n, S n) =ᵐ[(μ : Measure (Space d))] univ := by
    filter_upwards [hfinite] with x hx
    apply propext
    change x ∈ (⋃ n, S n) ↔ x ∈ (univ : Set (Space d))
    simp only [mem_iUnion,mem_univ,iff_true]
    obtain ⟨n,hn⟩ := exists_nat_gt (F x).toReal
    refine ⟨n,?_⟩
    change F x ≤ ENNReal.ofReal (n+1 : ℝ)
    rw [← ENNReal.ofReal_toReal hx.ne]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hn])
  have hmass : (μ : Measure (Space d)) (⋃ n, S n) ≠ 0 := by
    rw [measure_congr hfull,measure_univ]
    exact one_ne_zero
  obtain ⟨n,hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hmass
  obtain ⟨K,hKS,hK,hKm⟩ := (hS n).exists_lt_isCompact hn
  refine ⟨K,hK,hKm,(n:ℝ)+1,by positivity,?_⟩
  intro x hx
  exact hKS hx

theorem integrated_pulled_potential (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {m : ℕ} (P : Space d →L[ℝ] Space m) (u : ℝ) :
    (∫⁻ x, euclideanRieszPotential (μ.map P) u (P x) ∂μ) =
      PlanarFalconer.rieszEnergyOn (μ.map P) u := by
  rw [← lintegral_map (euclideanRieszPotential_measurable (μ.map P) u) P.measurable,
    PlanarFalconer.rieszEnergyOn,lintegral_prod _ (by fun_prop)]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialBallBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Riesz potentials give all-center Frostman bounds -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem ball_mass_le_potential (μ : Measure (Space d)) (x : Space d)
    {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    μ (ball x r) ≤ ENNReal.ofReal (r^u) * euclideanRieszPotential μ u x := by
  have hcancel : ENNReal.ofReal (r^u) * (ENNReal.ofReal r)^(-u) = 1 := by
    rw [← ENNReal.ofReal_rpow_of_pos hr,
      ← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top]
    simp
  have hpoint (y : Space d) (hy : y ∈ ball x r) :
      1 ≤ ENNReal.ofReal (r^u) * (edist x y)^(-u) := by
    have hd : edist x y ≤ ENNReal.ofReal r := by
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      exact (by simpa [mem_ball,dist_comm] using hy : dist x y < r).le
    have hp : (ENNReal.ofReal r)^(-u) ≤ (edist x y)^(-u) := by
      rw [ENNReal.rpow_neg,ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hd hu.le)
    rw [← hcancel]
    exact mul_le_mul_right hp _
  calc
    _ = ∫⁻ _ in ball x r, (1:ℝ≥0∞) ∂μ := by simp
    _ ≤ ∫⁻ y in ball x r, ENNReal.ofReal (r^u) * (edist x y)^(-u) ∂μ :=
      setLIntegral_mono' measurableSet_ball hpoint
    _ ≤ ∫⁻ y, ENNReal.ofReal (r^u) * (edist x y)^(-u) ∂μ :=
      setLIntegral_le_lintegral _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem frostman_of_ae_bounded_potential (η μ : Measure (Space d))
    (hdom : η ≤ μ) {u B : ℝ} (hu : 0 < u)
    (hpotential : ∀ᵐ x ∂η, euclideanRieszPotential μ u x ≤ ENNReal.ofReal B) :
    FrostmanBallBound η u (2^u*B) := by
  intro x r hr
  by_cases hzero : η (ball x r) = 0
  · rw [hzero]
    exact bot_le
  · obtain ⟨y,hy,hpot⟩ := (Measure.exists_mem_of_measure_ne_zero_of_ae hzero (ae_restrict_of_ae hpotential))
    have hsub : ball x r ⊆ ball y (2*r) := by
      intro z hz
      apply mem_ball.mpr
      have hd := dist_triangle z x y
      have hz' := mem_ball.mp hz
      have hy' := mem_ball.mp hy
      rw [dist_comm x y] at hd
      linarith
    calc
      η (ball x r) ≤ η (ball y (2*r)) := measure_mono hsub
      _ ≤ μ (ball y (2*r)) := hdom _
      _ ≤ ENNReal.ofReal ((2*r)^u) * euclideanRieszPotential μ u y :=
        ball_mass_le_potential μ y hu (by positivity)
      _ ≤ ENNReal.ofReal ((2*r)^u) * ENNReal.ofReal B := mul_le_mul_right hpot _
      _ = ENNReal.ofReal ((2^u*B)*r^u) := by
        rw [← ENNReal.ofReal_mul (by positivity),Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le]
        congr 1
        ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SimultaneousProjectedFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous Frostman bounds on one positive compact restriction -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem simultaneous_projected_frostman (μ : ProbabilityMeasure (Space d))
    (n : ι → ℕ) (P : ∀ i, Space d →L[ℝ] Space (n i))
    {u : ℝ} (hu : 0 < u)
    (henergy : ∀ i, PlanarFalconer.rieszEnergyOn ((μ : Measure (Space d)).map (P i)) u < ∞) :
    ∃ K : Set (Space d), IsCompact K ∧ 0 < (μ : Measure (Space d)) K ∧
      ∃ C : ℝ, 0 < C ∧ ∀ i,
        FrostmanBallBound (((μ : Measure (Space d)).restrict K).map (P i)) u C := by
  classical
  let f (i : ι) (x : Space d) :=
    euclideanRieszPotential ((μ : Measure (Space d)).map (P i)) u (P i x)
  let F (x : Space d) := ∑ i : ι, f i x
  have hf (i : ι) : Measurable (f i) :=
    (euclideanRieszPotential_measurable _ u).comp (P i).continuous.measurable
  have hF : Measurable F := Finset.measurable_sum _ (fun i _ => hf i)
  have hfinite : (∫⁻ x, F x ∂(μ : Measure (Space d))) < ∞ := by
    rw [show F = (fun x => ∑ i : ι, f i x) from rfl,
      lintegral_finsetSum _ (fun i _ => hf i)]
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact (integrated_pulled_potential (μ : Measure (Space d)) (P i) u).trans_lt (henergy i)
  obtain ⟨K,hK,hKm,B,hB,hbound⟩ := positive_compact_bounded_function μ F hF
    (ae_lt_top hF hfinite.ne)
  refine ⟨K,hK,hKm,2^u*B,mul_pos (by positivity) hB,?_⟩
  intro i
  apply frostman_of_ae_bounded_potential _ ((μ : Measure (Space d)).map (P i))
    (Measure.map_mono Measure.restrict_le_self (P i).continuous.measurable) hu
  apply (ae_map_iff (P i).continuous.measurable.aemeasurable
    (measurableSet_le (euclideanRieszPotential_measurable _ u) measurable_const)).mpr
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact (Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans (hbound x hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_NormalizedProjectedFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalize the common compact restriction while preserving every projection -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem normalized_projected_frostman (μ : ProbabilityMeasure (Space d))
    (n : ι → ℕ) (P : ∀ i, Space d →L[ℝ] Space (n i))
    {u : ℝ} (hu : 0 < u)
    (henergy : ∀ i, PlanarFalconer.rieszEnergyOn ((μ : Measure (Space d)).map (P i)) u < ∞) :
    ∃ ν : ProbabilityMeasure (Space d),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ i,
        FrostmanBallBound ((ν : Measure (Space d)).map (P i)) u C := by
  obtain ⟨K,hK,hKm,C,hC,hfrost⟩ := simultaneous_projected_frostman μ n P hu henergy
  let ρ := (μ : Measure (Space d)).restrict K
  have hρ : ρ univ ≠ 0 := by simpa [ρ] using hKm.ne'
  let ν := normalizedSliceLaw ρ hρ
  have hmass : 0 < (ρ univ).toReal := ENNReal.toReal_pos hρ (measure_ne_top ρ univ)
  have heq : (ν : Measure (Space d)) = ENNReal.ofReal (((ρ univ).toReal)⁻¹) • ρ := by
    rw [ENNReal.ofReal_inv_of_pos hmass,ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
    rfl
  refine ⟨ν,?_,?_,((ρ univ).toReal)⁻¹*C,mul_pos (inv_pos.mpr hmass) hC,?_⟩
  · apply hK.of_isClosed_subset Measure.isClosed_support
    apply (ν : Measure (Space d)).support_subset_of_isClosed hK.isClosed
    change (ν : Measure (Space d)) Kᶜ = 0
    simp only [heq,Measure.smul_apply,ρ,Measure.restrict_apply hK.measurableSet.compl,
      compl_inter_self,measure_empty,smul_zero]
  · rw [heq]
    exact Measure.smul_absolutelyContinuous.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · intro i x r hr
    rw [heq,Measure.map_smul,
      Measure.smul_apply,smul_eq_mul]
    calc
      _ ≤ ENNReal.ofReal (((ρ univ).toReal)⁻¹) * ENNReal.ofReal (C*r^u) :=
        mul_le_mul_right (hfrost i x r hr) _
      _ = ENNReal.ofReal ((((ρ univ).toReal)⁻¹*C)*r^u) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRieszKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian projection of a fixed vector: small balls and inverse moments -/
namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d m : ℕ}

theorem gaussianRowMap_parameter_measurable (z : Space d) :
    Measurable (fun A : Fin m → Space d => gaussianRowMap A z) :=
  (gaussianRowMap_joint_continuous.comp (continuous_id.prodMk continuous_const)).measurable

theorem gaussianRows_image_small_ball {w : Space d} (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    gaussianRows d m {A | gaussianRowMap A w ∈ ball 0 r} ≤
      ENNReal.ofReal ((gaussianBandConstant^m)*r^(m:ℝ)) := by
  calc
    _ ≤ gaussianRows d m {A | ∀ i, |inner ℝ w (A i)| ≤ r} := by
      apply measure_mono
      intro A hA i
      have hb : ‖gaussianRowMap A w‖ < r := by simpa using hA
      have hi := PiLp.norm_apply_le (gaussianRowMap A w) i
      simpa only [gaussianRowMap_apply,Real.norm_eq_abs] using hi.trans hb.le
    _ ≤ ENNReal.ofReal ((gaussianBandConstant*r)^m) := gaussianRows_one_band hw hr.le
    _ = _ := by rw [mul_pow,Real.rpow_natCast]

theorem gaussianRows_unit_inverse_moment {w : Space d} (hw : ‖w‖ = 1)
    {u : ℝ} (hu : 0 < u) (hum : u < (m:ℝ)) :
    (∫⁻ A, (edist (0:Space m) (gaussianRowMap A w))^(-u) ∂gaussianRows d m) ≤
      rieszSmallBallBound m (gaussianBandConstant^m) u := by
  let η := (gaussianRows d m).map (fun A => gaussianRowMap A w)
  have hm := gaussianRowMap_parameter_measurable (m := m) w
  have hball : ∀ r > 0, η (ball 0 r) ≤
      ENNReal.ofReal ((gaussianBandConstant^m)*r^(m:ℝ)) := by
    intro r hr
    rw [show η = _ from rfl,Measure.map_apply hm measurableSet_ball]
    exact gaussianRows_image_small_ball hw hr
  have : IsProbabilityMeasure η := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hh := point_riesz_potential_bound η 0 hu hum hball
  unfold euclideanRieszPotential at hh
  rw [show η = _ from rfl,lintegral_map (by fun_prop) hm] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRieszScaling
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneous inverse-moment bound for every projected difference -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem gaussianRows_inverse_moment {u : ℝ} (hu : 0 < u) (hum : u < (m:ℝ))
    (z : Space d) :
    (∫⁻ A, (edist (0:Space m) (gaussianRowMap A z))^(-u) ∂gaussianRows d m) ≤
      rieszSmallBallBound m (gaussianBandConstant^m) u * (edist (0:Space d) z)^(-u) := by
  let B := rieszSmallBallBound m (gaussianBandConstant^m) u
  by_cases hz : z = 0
  · subst z
    have hB : B ≠ 0 := by
      have : 1 ≤ B := le_add_right le_rfl
      exact ne_of_gt (zero_lt_one.trans_le this)
    simp only [edist_self,ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hu)]
    rw [ENNReal.mul_top hB]
    exact le_top
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let w : Space d := ‖z‖⁻¹ • z
    have hw : ‖w‖ = 1 := by simp [w,norm_smul,hn.ne']
    have hzw : z = ‖z‖ • w := by simp [w,smul_smul,hn.ne']
    have hfactor (A : Fin m → Space d) :
        (edist (0:Space m) (gaussianRowMap A z))^(-u) =
        (edist (0:Space d) z)^(-u) * (edist (0:Space m) (gaussianRowMap A w))^(-u) := by
      have he : edist (0:Space m) (gaussianRowMap A z) =
          edist (0:Space d) z * edist (0:Space m) (gaussianRowMap A w) := by
        rw [hzw,ContinuousLinearMap.map_smul]
        simp only [edist_dist,dist_zero_left,norm_smul,Real.norm_eq_abs,abs_norm,hw,mul_one]
        rw [ENNReal.ofReal_mul (norm_nonneg _)]
      rw [he,ENNReal.mul_rpow_of_ne_top (edist_ne_top _ _) (edist_ne_top _ _)]
    calc
      _ = (edist (0:Space d) z)^(-u) *
          ∫⁻ A, (edist (0:Space m) (gaussianRowMap A w))^(-u) ∂gaussianRows d m := by
        simp_rw [hfactor]
        apply lintegral_const_mul' _ _
        exact ENNReal.rpow_ne_top_of_ne_zero (by simpa [edist_eq_zero] using hz) (edist_ne_top _ _)
      _ ≤ (edist (0:Space d) z)^(-u) * B :=
        mul_le_mul_right (gaussianRows_unit_inverse_moment hw hu hum) _
      _ = _ := mul_comm _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianProjectionEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite energy survives almost every Gaussian linear projection

This is proved from Gaussian small balls and Tonelli; no projection theorem
is included among the conditional published inputs.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem gaussianRowMap_difference_continuous :
    Continuous (fun p : (Fin m → Space d) × (Space d × Space d) =>
      gaussianRowMap p.1 (p.2.1-p.2.2)) := by
  change Continuous (fun p : (Fin m → Space d) × (Space d × Space d) =>
    WithLp.toLp 2 (fun i => inner ℝ (p.1 i) (p.2.1-p.2.2)))
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i => ((continuous_apply i).comp continuous_fst).inner
    ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))

theorem gaussian_projected_energy_formula (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Fin m → Space d) (u : ℝ) :
    PlanarFalconer.rieszEnergyOn (μ.map (gaussianRowMap A)) u =
      ∫⁻ z : Space d × Space d,
        (edist (0:Space m) (gaussianRowMap A (z.1-z.2)))^(-u) ∂μ.prod μ := by
  have hm := (gaussianRowMap A).continuous.measurable
  rw [PlanarFalconer.rieszEnergyOn,Measure.map_prod_map μ μ hm hm,
    lintegral_map (by fun_prop) (hm.prodMap hm)]
  apply lintegral_congr
  intro z
  simp only [Prod.map,edist_dist,dist_eq_norm,map_sub,zero_sub,norm_neg]

theorem gaussian_projected_energy_measurable (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (u : ℝ) :
    Measurable (fun A : Fin m → Space d =>
      PlanarFalconer.rieszEnergyOn (μ.map (gaussianRowMap A)) u) := by
  simp_rw [gaussian_projected_energy_formula]
  apply Measurable.lintegral_prod_right
  exact (measurable_const.edist
    (gaussianRowMap_difference_continuous (d := d) (m := m)).measurable).pow_const _

theorem gaussian_projected_energy_average (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hum : u < (m:ℝ)) :
    (∫⁻ A : Fin m → Space d,
      PlanarFalconer.rieszEnergyOn (μ.map (gaussianRowMap A)) u ∂gaussianRows d m) ≤
      rieszSmallBallBound m (gaussianBandConstant^m) u * PlanarFalconer.rieszEnergyOn μ u := by
  let F : (Fin m → Space d) → (Space d × Space d) → ℝ≥0∞ :=
    fun A z => (edist (0:Space m) (gaussianRowMap A (z.1-z.2)))^(-u)
  have hF : Measurable (Function.uncurry F) := by
    exact (measurable_const.edist
      (gaussianRowMap_difference_continuous (d := d) (m := m)).measurable).pow_const _
  simp_rw [gaussian_projected_energy_formula]
  change (∫⁻ A, ∫⁻ z, F A z ∂μ.prod μ ∂gaussianRows d m) ≤ _
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc
    _ ≤ ∫⁻ z : Space d × Space d,
        rieszSmallBallBound m (gaussianBandConstant^m) u * (edist z.1 z.2)^(-u) ∂μ.prod μ := by
      apply lintegral_mono
      intro z
      simpa only [F,edist_dist,dist_eq_norm,zero_sub,norm_neg] using
        gaussianRows_inverse_moment hu hum (z.1-z.2)
    _ = _ := lintegral_const_mul' _ _ (rieszSmallBallBound_lt_top hum).ne

theorem gaussian_projected_energy_finite_ae (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hum : u < (m:ℝ))
    (henergy : PlanarFalconer.rieszEnergyOn μ u < ∞) :
    ∀ᵐ A : Fin m → Space d ∂gaussianRows d m,
      PlanarFalconer.rieszEnergyOn (μ.map (gaussianRowMap A)) u < ∞ := by
  apply ae_lt_top (gaussian_projected_energy_measurable μ u)
  exact ((gaussian_projected_energy_average μ hu hum).trans_lt
    (ENNReal.mul_lt_top (rieszSmallBallBound_lt_top hum) henergy)).ne

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ChooseProjectedFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact original law and one projected law with the same Frostman exponent -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem choose_projected_frostman (μ : ProbabilityMeasure (Space d))
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hum : u < (m:ℝ))
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ∃ P : Space d →L[ℝ] Space m, ∃ ν : ProbabilityMeasure (Space d),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      ∃ D : ℝ, 0 < D ∧ FrostmanBallBound (ν : Measure (Space d)) u D ∧
        FrostmanBallBound ((ν : Measure (Space d)).map P) u D := by
  have hsource := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space d)) hu hus hfrost
  obtain ⟨A,hA⟩ := (gaussian_projected_energy_finite_ae (m := m)
    (μ : Measure (Space d)) hu hum hsource).exists
  let P := gaussianRowMap A
  let dims : Bool → ℕ | false => d | true => m
  let maps : ∀ b, Space d →L[ℝ] Space (dims b)
    | false => ContinuousLinearMap.id ℝ (Space d)
    | true => P
  have henergy : ∀ b, PlanarFalconer.rieszEnergyOn
      ((μ : Measure (Space d)).map (maps b)) u < ∞ := by
    intro b
    cases b with
    | false => simpa [maps,dims] using hsource
    | true => exact hA
  obtain ⟨ν,hK,hdom,D,hD,hbounds⟩ := normalized_projected_frostman μ dims maps hu henergy
  refine ⟨P,ν,hK,hdom,D,hD,?_,hbounds true⟩
  simpa [maps,dims] using hbounds false

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ProjectedSupportPoints
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original support points separated by a nonatomic projected law -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem distinct_projected_support_points (μ : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space m)
    [NullSingletonClass ((μ : Measure (Space d)).map P)] :
    ∃ x ∈ (μ : Measure (Space d)).support,
      ∃ y ∈ (μ : Measure (Space d)).support, P x ≠ P y := by
  obtain ⟨x,hx⟩ := (μ : Measure (Space d)).nonempty_support (by
    intro h
    have hh := congrArg (fun η : Measure (Space d) => η univ) h
    simp at hh)
  let F : Set (Space d) := P ⁻¹' {P x}
  have hFm : MeasurableSet F := (measurableSet_singleton _).preimage P.continuous.measurable
  have hF : (μ : Measure (Space d)) F = 0 := by
    rw [show F = P ⁻¹' {P x} from rfl,
      ← Measure.map_apply P.continuous.measurable (measurableSet_singleton _)]
    exact measure_singleton _
  have hFc : (μ : Measure (Space d)) Fᶜ = 1 := by
    rw [measure_compl hFm (measure_ne_top _ _),hF,measure_univ,tsub_zero]
  obtain ⟨y,hy,hyS⟩ := (μ : Measure (Space d)).nonempty_inter_support_of_pos
    (s := Fᶜ) (by rw [hFc]; exact zero_lt_one)
  refine ⟨x,hx,y,hyS,?_⟩
  intro he
  exact hy (by simpa only [F,mem_preimage,mem_singleton_iff] using he.symm)

theorem positive_compact_support_ball (μ : ProbabilityMeasure (Space d))
    (hK : IsCompact (μ : Measure (Space d)).support)
    {x : Space d} (hx : x ∈ (μ : Measure (Space d)).support) {r : ℝ} (hr : 0 < r) :
    IsCompact ((μ : Measure (Space d)).support ∩ closedBall x r) ∧
      0 < (μ : Measure (Space d)) ((μ : Measure (Space d)).support ∩ closedBall x r) := by
  refine ⟨hK.inter_right isClosed_closedBall,?_⟩
  have hp := ((μ : Measure (Space d)).mem_support_iff_forall x).mp hx
    (ball x r) (ball_mem_nhds x hr)
  have hsub : ball x r ⊆ ((μ : Measure (Space d)).support ∩ closedBall x r) ∪
      (μ : Measure (Space d)).supportᶜ := by
    intro y hy
    by_cases hs : y ∈ (μ : Measure (Space d)).support
    · exact Or.inl ⟨hs,ball_subset_closedBall hy⟩
    · exact Or.inr hs
  have hh := (measure_mono (μ := (μ : Measure (Space d))) hsub).trans
    (measure_union_le _ _)
  rw [Measure.measure_compl_support,add_zero] at hh
  exact hp.trans_le hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ProjectedCompactPieces
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive compact pieces separated in the original and projected spaces -/
namespace Falconer
open Set Metric MeasureTheory Filter NormedSpace
open scoped ENNReal Topology
variable {d m : ℕ}

theorem continuousAt_radialDirection_pair {x y : Space d} (hne : y ≠ x) :
    ContinuousAt (fun z : Space d × Space d => radialDirection z.1 z.2) (x,y) := by
  have hd : ContinuousAt (fun z : Space d × Space d => z.2-z.1) (x,y) :=
    (continuous_snd.sub continuous_fst).continuousAt
  exact (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))).smul hd

theorem projected_compact_pieces (μ : ProbabilityMeasure (Space d))
    (hK : IsCompact (μ : Measure (Space d)).support)
    (P : Space d →L[ℝ] Space m)
    [NullSingletonClass ((μ : Measure (Space d)).map P)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : Set (Space d), IsCompact A ∧ IsCompact B ∧
      A ⊆ (μ : Measure (Space d)).support ∧ B ⊆ (μ : Measure (Space d)).support ∧
      0 < (μ : Measure (Space d)) A ∧ 0 < (μ : Measure (Space d)) B ∧
      ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∃ w : Space d, ‖w‖ = 1 ∧
        ∀ a ∈ A, ∀ b ∈ B, r/2 ≤ dist a b ∧ dist a b ≤ 2*r ∧
          c ≤ ‖P (radialDirection a b)‖ ∧ c ≤ ‖P (radialDirection b a)‖ ∧
          dist (radialDirection a b) w < ε := by
  obtain ⟨x,hx,y,hy,hxyP⟩ := distinct_projected_support_points μ P
  have hxy : x ≠ y := fun h => hxyP (congrArg P h)
  let r := dist x y
  let a := dist (P x) (P y)
  have hr : 0 < r := dist_pos.mpr hxy
  have ha : 0 < a := dist_pos.mpr hxyP
  have hlo : ∀ᶠ z : Space d × Space d in 𝓝 (x,y), r/2 < dist z.1 z.2 :=
    (isOpen_lt continuous_const (continuous_fst.dist continuous_snd)).mem_nhds (by
      change r/2 < r
      linarith)
  have hup : ∀ᶠ z : Space d × Space d in 𝓝 (x,y), dist z.1 z.2 < 2*r :=
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const).mem_nhds (by
      change r < 2*r
      linarith)
  have hp : ∀ᶠ z : Space d × Space d in 𝓝 (x,y), a/2 < dist (P z.1) (P z.2) :=
    (isOpen_lt continuous_const
      ((P.continuous.comp continuous_fst).dist (P.continuous.comp continuous_snd))).mem_nhds (by
        change a/2 < a
        linarith)
  have hw : ∀ᶠ z : Space d × Space d in 𝓝 (x,y),
      dist (radialDirection z.1 z.2) (radialDirection x y) < ε :=
    (continuousAt_radialDirection_pair (Ne.symm hxy)).tendsto (ball_mem_nhds _ hε)
  have hall : ∀ᶠ z : Space d × Space d in 𝓝 (x,y),
      r/2 < dist z.1 z.2 ∧ dist z.1 z.2 < 2*r ∧
        a/2 < dist (P z.1) (P z.2) ∧
          dist (radialDirection z.1 z.2) (radialDirection x y) < ε := by
    filter_upwards [hlo,hup,hp,hw] with z hz1 hz2 hz3 hz4
    exact ⟨hz1,hz2,hz3,hz4⟩
  obtain ⟨δ,hδ,hδgood⟩ := Metric.eventually_nhds_iff_ball.mp hall
  let A := (μ : Measure (Space d)).support ∩ closedBall x (δ/2)
  let B := (μ : Measure (Space d)).support ∩ closedBall y (δ/2)
  obtain ⟨hAc,hAm⟩ := positive_compact_support_ball μ hK hx (by positivity : 0 < δ/2)
  obtain ⟨hBc,hBm⟩ := positive_compact_support_ball μ hK hy (by positivity : 0 < δ/2)
  refine ⟨A,B,hAc,hBc,inter_subset_left,inter_subset_left,hAm,hBm,
    r,(a/2)/(2*r),hr,by positivity,radialDirection x y,?_,?_⟩
  · exact norm_normalize (sub_ne_zero.mpr (Ne.symm hxy))
  · intro x' hx' y' hy'
    have hd : dist (x',y') (x,y) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (lt_of_le_of_lt hx'.2 (by linarith)) (lt_of_le_of_lt hy'.2 (by linarith))
    obtain ⟨h1,h2,h3,h4⟩ := hδgood _ (mem_ball.mpr hd)
    refine ⟨h1.le,h2.le,projected_direction_lower_of_dist P x' y' (by positivity) h3.le h2.le,?_,h4⟩
    apply projected_direction_lower_of_dist P y' x' (by positivity)
    · simpa only [dist_comm] using h3.le
    · simpa only [dist_comm] using h2.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PiCoordinateSections
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product-measure bounds from a single coordinate's sections -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

theorem pi_measure_le_of_coordinate_sections (μ : Measure X) [IsFiniteMeasure μ]
    (i : Fin (n+1)) (E : Set (Fin (n+1) → X)) (hE : MeasurableSet E) (C : ℝ≥0∞)
    (hsec : ∀ y : Fin n → X, μ {x | i.insertNth x y ∈ E} ≤ C) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) E ≤ C*(μ univ)^n := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) i
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
  have he : (Measure.pi (fun _ : Fin (n+1) => μ)) E =
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) (e.symm ⁻¹' E) := by
    rw [← hm.map_eq,Measure.map_apply hm.measurable hE]
  rw [he,Measure.prod_apply_symm (hE.preimage e.symm.measurable)]
  calc
    _ ≤ ∫⁻ _y : Fin n → X, C ∂Measure.pi (fun _ => μ) := by
      apply lintegral_mono
      intro y
      exact hsec y
    _ = _ := by simp only [lintegral_const,Measure.pi_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GeneralColumns
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual coordinate isomorphisms for a transverse tuple in arbitrary dimension -/

namespace Falconer
open scoped BigOperators Matrix
variable {d : ℕ}

theorem euclideanColumnMatrix_gram (v : Fin d → Space d) :
    Matrix.gram ℝ v = (euclideanColumnMatrix v)ᵀ * euclideanColumnMatrix v := by
  ext i j
  simp only [Matrix.gram_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    Matrix.mul_apply,Matrix.transpose_apply,euclideanColumnMatrix,Matrix.of_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem euclideanColumnMatrix_gram_sqrt (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = |(euclideanColumnMatrix v).det| := by
  rw [euclideanColumnMatrix_gram,Matrix.det_mul,Matrix.det_transpose,← pow_two,Real.sqrt_sq_eq_abs]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GramSchmidtMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable Gram--Schmidt residuals with exact prefix dependence -/

namespace Falconer
open Set Submodule InnerProductSpace
variable {d : ℕ}

theorem gramSchmidt_measurable (i : Fin d) :
    Measurable (fun v : Fin d → Space d => gramSchmidt ℝ v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have he : (fun v : Fin d → Space d => gramSchmidt ℝ v i) =
        fun v => v i - ∑ j ∈ Finset.Iio i, (ℝ ∙ gramSchmidt ℝ v j).starProjection (v i) :=
      funext (fun v => gramSchmidt_def ℝ v i)
    rw [he]
    simp_rw [starProjection_singleton]
    apply (measurable_pi_apply i).sub
    apply Finset.measurable_sum
    intro j hj
    have hg := ih j (Finset.mem_Iio.mp hj)
    change Measurable (fun v : Fin d → Space d =>
      (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖^2) • gramSchmidt ℝ v j)
    exact ((hg.inner (measurable_pi_apply i)).div (hg.norm.pow_const 2)).smul hg

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GramSchmidtSlab
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small Gram--Schmidt residual lies in a fixed thin slab -/

namespace Falconer
open Set Submodule InnerProductSpace NormedSpace
open scoped BigOperators
variable {d : ℕ}

theorem inner_gramSchmidt_of_prefix_orthogonal (u : Space d) (v : Fin d → Space d)
    (i : Fin d) (h : ∀ j < i, inner ℝ u (v j) = 0) :
    inner ℝ u (gramSchmidt ℝ v i) = inner ℝ u (v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [gramSchmidt_def]
    simp only [inner_sub_right, inner_sum, starProjection_singleton, inner_smul_right,
      RCLike.ofReal_real_eq_id, id_eq]
    have hz : (∑ j ∈ Finset.Iio i,
        (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖ ^ 2) *
          inner ℝ u (gramSchmidt ℝ v j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ih j (Finset.mem_Iio.mp hj) (fun k hk => h k (hk.trans (Finset.mem_Iio.mp hj))),
        h j (Finset.mem_Iio.mp hj), mul_zero]
    rw [hz, sub_zero]

theorem exists_unit_prefix_normal (v : Fin d → Space d) (i : Fin d) :
    ∃ u : Space d, ‖u‖ = 1 ∧ ∀ j < i, inner ℝ u (v j) = 0 := by
  let b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) (E := Space d)
    (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v
  exact ⟨b i, b.orthonormal.1 i, fun j hj =>
    gramSchmidtOrthonormalBasis_inv_triangular _ v hj⟩

theorem small_residual_fixed_slab (v : Fin d → Space d) (i : Fin d) :
    ∃ u : Space d, ‖u‖ = 1 ∧ ∀ w : Fin d → Space d,
      (∀ j < i, w j = v j) → |inner ℝ u (w i)| ≤ ‖gramSchmidt ℝ w i‖ := by
  obtain ⟨u,hu,horth⟩ := exists_unit_prefix_normal v i
  refine ⟨u,hu,fun w hw => ?_⟩
  have he := inner_gramSchmidt_of_prefix_orthogonal u w i (fun j hj => by rw [hw j hj]; exact horth j hj)
  rw [← he]
  simpa only [hu,one_mul] using abs_real_inner_le_norm u (gramSchmidt ℝ w i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GramSchmidtVolume
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Gram volume is the product of successive residual lengths -/

namespace Falconer
open InnerProductSpace
open scoped BigOperators Matrix
variable {d : ℕ}

theorem gram_volume_eq_abs_basis_det (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = |b.toBasis.det v| := by
  rw [Matrix.gram_eq_conjTranspose_mul b v, Matrix.det_mul, Matrix.det_conjTranspose]
  change Real.sqrt ((b.toBasis.det v)*(b.toBasis.det v)) = _
  rw [← pow_two, Real.sqrt_sq_eq_abs]

theorem gramSchmidt_basis_diagonal_abs (v : Fin d → Space d) (i : Fin d) :
    |inner ℝ (gramSchmidtOrthonormalBasis
      (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v i) (v i)| =
      ‖gramSchmidt ℝ v i‖ := by
  let w := gramSchmidt ℝ v i
  have he : inner ℝ w (v i) = ‖w‖^2 := by
    have hh := inner_gramSchmidt_of_prefix_orthogonal w v i
      (fun j hj => gramSchmidt_inv_triangular ℝ v hj)
    rw [← hh,real_inner_self_eq_norm_sq]
  by_cases hw : w = 0
  · have hz : gramSchmidtNormed ℝ v i = 0 := by
      simp [gramSchmidtNormed, show gramSchmidt ℝ v i = 0 from hw]
    rw [inner_gramSchmidtOrthonormalBasis_eq_zero _ hz]
    change |(0:ℝ)| = ‖w‖
    simp only [hw,abs_zero,norm_zero]
  · have hz : gramSchmidtNormed ℝ v i ≠ 0 := by
      simp only [gramSchmidtNormed]
      exact smul_ne_zero (inv_ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr hw))) hw
    rw [gramSchmidtOrthonormalBasis_apply _ hz]
    change |inner ℝ (‖w‖⁻¹ • w) (v i)| = ‖w‖
    rw [real_inner_smul_left,he,pow_two,← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw),one_mul,abs_of_nonneg (norm_nonneg w)]

theorem gram_volume_eq_residual_product (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  let b := gramSchmidtOrthonormalBasis
    (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v
  rw [gram_volume_eq_abs_basis_det b v]
  change |(gramSchmidtOrthonormalBasis _ v).toBasis.det v| = _
  rw [gramSchmidtOrthonormalBasis_det,Finset.abs_prod]
  exact Finset.prod_congr rfl (fun i _ => gramSchmidt_basis_diagonal_abs v i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original radial laws and source balls under positive affine rescaling -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_preimage_ball {a : ℝ} (ha : 0 < a) (c x : Space d) (r : ℝ) :
    radialZoom a ha.ne' c ⁻¹' Metric.ball x r = Metric.ball (c+a⁻¹ • x) (r/a) := by
  ext z
  have he : a • (z-c)-x = a • (z-(c+a⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    abel
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,radialZoom_apply]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha,lt_div_iff₀ ha]
  rw [mul_comm a]

theorem radialZoom_ball_apply (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c x : Space d) (r : ℝ) :
    Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) =
      μ (Metric.ball (c+a⁻¹ • x) (r/a)) := by
  rw [Measure.map_apply (radialZoom a ha.ne' c).measurable Metric.isOpen_ball.measurableSet,
    radialZoom_preimage_ball ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlateZoom
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact affine normalization of the heavy-plate inputs -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_full_frostman (μ : Measure (Space d))
    {a s C : ℝ} (ha : 0 < a) (c : Space d) (hfrost : FrostmanBallBound μ s C) :
    FrostmanBallBound (Measure.map (radialZoom a ha.ne' c) μ) s (C*a^(-s)) := by
  intro x r hr
  rw [radialZoom_ball_apply μ ha]
  have he : C*(r/a)^s = (C*a^(-s))*r^s := by
    rw [Real.div_rpow hr.le ha.le,Real.rpow_neg ha.le]
    ring
  rw [← he]
  exact hfrost _ _ (div_pos hr ha)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionDilation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive dilations of the chosen auxiliary projections -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem map_smul_linear (μ : Measure (Space d)) (P : Space d →L[ℝ] Space m)
    {a : ℝ} (ha : 0 < a) :
    μ.map (a • P) = (μ.map P).map (radialZoom a ha.ne' (0 : Space m)) := by
  rw [Measure.map_map (radialZoom a ha.ne' (0 : Space m)).measurable P.continuous.measurable]
  congr 1
  funext x
  simp only [Function.comp_apply,radialZoom_apply,sub_zero,smul_apply]

theorem dilated_projected_frostman (μ : Measure (Space d))
    (P : Space d →L[ℝ] Space m) {a s C : ℝ} (ha : 0 < a)
    (hfrost : FrostmanBallBound (μ.map P) s C) :
    FrostmanBallBound (μ.map (a • P)) s (C*a^(-s)) := by
  rw [map_smul_linear μ P ha]
  exact radialZoom_full_frostman (μ.map P) ha 0 hfrost

theorem exists_contractive_dilation (P : Space d →L[ℝ] Space m) :
    ∃ a : ℝ, 0 < a ∧ ‖a • P‖ ≤ 1 := by
  refine ⟨(‖P‖+1)⁻¹,by positivity,?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (‖P‖+1)⁻¹)]
  rw [inv_mul_le_iff₀ (by positivity : 0 < ‖P‖+1)]
  linarith only [norm_nonneg P]

theorem compact_projected_support (μ : Measure (Space d))
    (hK : IsCompact μ.support) (P : Space d →L[ℝ] Space m) :
    (μ.map P).support ⊆ P '' μ.support ∧ IsCompact (μ.map P).support := by
  have himage := hK.image P.continuous
  have hsub : (μ.map P).support ⊆ P '' μ.support := by
    apply Measure.support_subset_of_isClosed himage.isClosed
    change μ.map P (P '' μ.support)ᶜ = 0
    rw [Measure.map_apply P.continuous.measurable himage.isClosed.measurableSet.compl]
    apply measure_mono_null _ μ.measure_compl_support
    intro x hx hxS
    exact hx ⟨x,hxS,rfl⟩
  exact ⟨hsub,himage.of_isClosed_subset Measure.isClosed_support hsub⟩

theorem projected_supports_disjoint (μ ν : Measure (Space d))
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    (P : Space d →L[ℝ] Space m)
    (hneq : ∀ x ∈ μ.support, ∀ y ∈ ν.support, P x ≠ P y) :
    Disjoint (μ.map P).support (ν.map P).support := by
  apply Set.disjoint_left.mpr
  intro z hzμ hzν
  obtain ⟨x,hx,rfl⟩ := (compact_projected_support μ hμ P).1 hzμ
  obtain ⟨y,hy,hxy⟩ := (compact_projected_support ν hν P).1 hzν
  exact hneq x hx y hy hxy.symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ProjectedPair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original separated pairs with simultaneous projected Frostman bounds -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

variable {d m : ℕ}

private theorem frostman_enlarge {μ : Measure (Space d)} {s C D : ℝ}
    (h : FrostmanBallBound μ s C) (hCD : C ≤ D) : FrostmanBallBound μ s D := by
  intro x r hr
  exact (h x r hr).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hr.le _)))

theorem exists_projected_starting_pair (ζ : ProbabilityMeasure (Space d))
    {s C u ε : ℝ} (hu : 0 < u) (hus : u < s) (hum : u < (m:ℝ))
    (hfrost : FrostmanBallBound (ζ : Measure (Space d)) s C) (hε : 0 < ε) :
    Nonempty (ProjectedStartingPair ζ m u ε) := by
  obtain ⟨P,μ,hK,hdom,D,hD,hμ,hP⟩ := choose_projected_frostman ζ hu hus hum hfrost
  obtain ⟨a,ha,hcontract⟩ := exists_contractive_dilation P
  let Q := a • P
  have hQ : FrostmanBallBound ((μ : Measure (Space d)).map Q) u (D*a^(-u)) :=
    dilated_projected_frostman (μ : Measure (Space d)) P ha hP
  let := noAtoms_of_frostman ((μ : Measure (Space d)).map Q) hu hQ
  obtain ⟨A,B,hAc,hBc,_,_,hAm,hBm,r,c,hr,hc,w,hw,hgeom⟩ :=
    projected_compact_pieces μ hK Q hε
  let μ₁ := positiveRestriction μ A hAm
  let μ₂ := positiveRestriction μ B hBm
  have hleft : (μ₁ : Measure (Space d)).support ⊆ A :=
    positiveRestriction_support μ A hAm hAc.isClosed
  have hright : (μ₂ : Measure (Space d)).support ⊆ B :=
    positiveRestriction_support μ B hBm hBc.isClosed
  let C₁ := ((μ : Measure (Space d)) A).toReal⁻¹ * D
  let C₂ := ((μ : Measure (Space d)) B).toReal⁻¹ * D
  let C₃ := ((μ : Measure (Space d)) A).toReal⁻¹ * (D*a^(-u))
  let C₄ := ((μ : Measure (Space d)) B).toReal⁻¹ * (D*a^(-u))
  have hC₁ : 0 < C₁ := mul_pos (inv_pos.mpr
    (ENNReal.toReal_pos hAm.ne' (measure_ne_top _ _))) hD
  let C' := max (max C₁ C₂) (max C₃ C₄)
  have h1 : C₁ ≤ C' := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : C₂ ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : C₃ ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have h4 : C₄ ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  have hf1 : FrostmanBallBound (μ₁ : Measure (Space d)) u C₁ := by
    have hb := positiveRestriction_projected_frostman μ A hAm (ContinuousLinearMap.id ℝ (Space d))
      (by simpa using hμ)
    simpa [C₁] using hb
  have hf2 : FrostmanBallBound (μ₂ : Measure (Space d)) u C₂ := by
    have hb := positiveRestriction_projected_frostman μ B hBm (ContinuousLinearMap.id ℝ (Space d))
      (by simpa using hμ)
    simpa [C₂] using hb
  exact ⟨{
    projection := Q
    left := μ₁
    right := μ₂
    left_compact := hAc.of_isClosed_subset Measure.isClosed_support hleft
    right_compact := hBc.of_isClosed_subset Measure.isClosed_support hright
    left_ac := (positiveRestriction_absolutelyContinuous μ A hAm).trans hdom
    right_ac := (positiveRestriction_absolutelyContinuous μ B hBm).trans hdom
    constant := C'
    constant_pos := hC₁.trans_le h1
    left_frostman := frostman_enlarge hf1 h1
    right_frostman := frostman_enlarge hf2 h2
    projected_left_frostman := frostman_enlarge
      (positiveRestriction_projected_frostman μ A hAm Q hQ) h3
    projected_right_frostman := frostman_enlarge
      (positiveRestriction_projected_frostman μ B hBm Q hQ) h4
    contractive := hcontract
    radius := r
    radius_pos := hr
    lower := c
    lower_pos := hc
    direction := w
    direction_unit := hw
    geometry := fun x hx y hy => hgeom x (hleft hx) y (hright hy) }⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_EvenStartingCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original-pair starting cap estimate in even dimensions -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace ProjectedStartingPair
variable {d m : ℕ} {ζ : ProbabilityMeasure (Space d)} {s ε : ℝ}

theorem relation_measurable (p : ProjectedStartingPair ζ m s ε) :
    MeasurableSet p.relation :=
  Measure.isClosed_support.measurableSet.prod Measure.isClosed_support.measurableSet

theorem relation_mass (p : ProjectedStartingPair ζ m s ε) :
    ((p.left : Measure (Space d)).prod (p.right : Measure (Space d))) p.relation = 1 := by
  rw [relation,Measure.prod_prod]
  have hμ : (p.left : Measure (Space d)) (p.left : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  have hν : (p.right : Measure (Space d)) (p.right : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  rw [hμ,hν,mul_one]

theorem projected_disjoint (p : ProjectedStartingPair ζ m s ε) :
    Disjoint ((p.left : Measure (Space d)).map p.projection).support
      ((p.right : Measure (Space d)).map p.projection).support := by
  apply projected_supports_disjoint _ _ p.left_compact p.right_compact
  intro x hx y hy he
  have hlow := (p.geometry x hx y hy).2.2.1
  have hz : p.projection (radialDirection x y) = 0 := by
    simp only [radialDirection,map_smul,map_sub,he,sub_self,smul_zero]
  rw [hz,norm_zero] at hlow
  exact (not_le_of_gt p.lower_pos) hlow

theorem integer_available (hpublished : PublishedRadialMoment)
    {h : ℕ} (hh : 1 ≤ h) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (p : ProjectedStartingPair ζ (h+1) ((h:ℝ)+δ) ε) :
    CapAvailable p.left p.right (fun _ => p.relation) (h:ℝ) := by
  have hcap := integer_caps_of_published_radial hpublished h hh
    (p.left.map (p.projection.continuous.aemeasurable)) (p.right.map (p.projection.continuous.aemeasurable)) hδ hδ1
    (compact_projected_support _ p.left_compact p.projection).2
    (compact_projected_support _ p.right_compact p.projection).2
    p.projected_disjoint p.projected_left_frostman p.projected_right_frostman
    (fun _ => univ) (fun _ => MeasurableSet.univ)
  apply CapAvailable.pullback p.projection p.left p.right p.lower_pos p.contractive
    (Nat.cast_nonneg h) (fun _ => p.relation_measurable) (fun _ _ _ => mem_univ _) _ hcap
  intro N z hz
  exact ⟨(p.geometry z.1 hz.1 z.2 hz.2).2.2.1,
    (p.geometry z.1 hz.1 z.2 hz.2).2.2.2.1⟩

end ProjectedStartingPair

theorem exists_even_starting_caps (hpublished : PublishedRadialMoment)
    {d h : ℕ} (hh : 1 ≤ h) (ζ : ProbabilityMeasure (Space d))
    {s C ε : ℝ} (hs : (h:ℝ) < s)
    (hfrost : FrostmanBallBound (ζ : Measure (Space d)) s C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ p : ProjectedStartingPair ζ (h+1) ((h:ℝ)+δ) ε,
        CapAvailable p.left p.right (fun _ => p.relation) (h:ℝ) := by
  let δ := min (s-(h:ℝ)) 1 / 2
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hs) zero_lt_one) (by norm_num)
  have hδ1 : δ < 1 := by dsimp [δ]; have := min_le_right (s-(h:ℝ)) 1; linarith
  have hδs : (h:ℝ)+δ < s := by
    have hmin := min_le_left (s-(h:ℝ)) 1
    dsimp [δ]
    linarith
  have hu : 0 < (h:ℝ)+δ := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hδ
  have hum : (h:ℝ)+δ < (h+1:ℕ) := by push_cast; linarith
  obtain ⟨p⟩ := exists_projected_starting_pair ζ hu hδs hum hfrost hε
  exact ⟨δ,hδ,hδ1,p,p.integer_available hpublished hh hδ hδ1⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DilationNoncharging
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hyperplane noncharging survives positive projection normalization -/
namespace Falconer
open Set MeasureTheory
variable {d m : ℕ}

theorem dilated_hyperplane_null (μ : Measure (Space m)) {a : ℝ} (ha : 0 < a)
    (hnull : ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ, μ {x | inner ℝ w x = t} = 0) :
    ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
      μ.map (radialZoom a ha.ne' (0 : Space m)) {x | inner ℝ w x = t} = 0 := by
  intro w hw t
  rw [Measure.map_apply (radialZoom a ha.ne' (0 : Space m)).measurable
    (isClosed_eq (by fun_prop) continuous_const).measurableSet]
  have heq : radialZoom a ha.ne' (0 : Space m) ⁻¹' {x | inner ℝ w x = t} =
      {x | inner ℝ w x = t/a} := by
    ext x
    simp only [mem_preimage,mem_ofPred_eq,radialZoom_apply,sub_zero,inner_smul_right]
    rw [eq_div_iff ha.ne']
    constructor <;> intro h <;> nlinarith only [h]
  rw [heq]
  exact hnull w hw (t/a)

theorem dilated_projection_hyperplane_null (μ : Measure (Space d))
    (P : Space d →L[ℝ] Space m) {a : ℝ} (ha : 0 < a)
    (hnull : ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
      μ.map P {x | inner ℝ w x = t} = 0) :
    ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
      μ.map (a • P) {x | inner ℝ w x = t} = 0 := by
  rw [map_smul_linear μ P ha]
  exact dilated_hyperplane_null (μ.map P) ha hnull

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FrostmanDimension
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Hausdorff-dimension lower bound of the actual Frostman law -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem frostman_set_bound (μ : ProbabilityMeasure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (A : Set (Space d)) :
    (μ : Measure (Space d)) A ≤ ENNReal.ofReal (C*2^s) * (Metric.ediam A)^s := by
  let := noAtoms_of_frostman (μ : Measure (Space d)) hs hfrost
  have hK : 0 < C*2^s := mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)
  by_cases hA : A.Nonempty
  · obtain ⟨x,hx⟩ := hA
    by_cases hzero : Metric.ediam A = 0
    · rw [hzero,ENNReal.zero_rpow_of_pos hs,mul_zero]
      apply le_of_eq
      apply measure_mono_null _ (measure_singleton x)
      intro y hy
      exact Set.mem_singleton_iff.mpr ((Metric.ediam_eq_zero_iff.mp hzero) hy hx)
    by_cases htop : Metric.ediam A = ∞
    · rw [htop,ENNReal.top_rpow_of_pos hs,ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hK)]
      exact le_top
    let r := (Metric.ediam A).toReal
    have hr : 0 < r := ENNReal.toReal_pos hzero htop
    have hsub : A ⊆ ball x (2*r) := by
      intro y hy
      have hd : dist y x ≤ r := by
        have hd := ENNReal.toReal_mono htop (Metric.edist_le_ediam_of_mem hy hx)
        simpa only [edist_dist,ENNReal.toReal_ofReal dist_nonneg] using hd
      exact lt_of_le_of_lt hd (by linarith)
    calc
      (μ : Measure (Space d)) A ≤ ENNReal.ofReal (C*(2*r)^s) :=
        (measure_mono hsub).trans (hfrost x (2*r) (by positivity))
      _ = ENNReal.ofReal (C*2^s) * (Metric.ediam A)^s := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le,← mul_assoc,
          ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_rpow_of_pos hr]
        congr 1
        exact congrArg (fun z : ℝ≥0∞ => z^s) (ENNReal.ofReal_toReal htop)
  · rw [Set.not_nonempty_iff_eq_empty.mp hA,measure_empty]
    exact zero_le

theorem frostman_dimension_lower (μ : ProbabilityMeasure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ENNReal.ofReal s ≤ dimH (μ : Measure (Space d)).support := by
  let K := ENNReal.ofReal (C*2^s)
  have hK : K ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hKtop : K ≠ ∞ := ENNReal.ofReal_ne_top
  have hmeasure : K⁻¹ • (μ : Measure (Space d)) ≤ Measure.hausdorffMeasure s := by
    apply Measure.le_hausdorffMeasure s _ ∞ (by simp)
    intro A _
    rw [Measure.smul_apply,smul_eq_mul]
    calc
      K⁻¹ * (μ : Measure (Space d)) A ≤ K⁻¹ * (K*(Metric.ediam A)^s) :=
        mul_le_mul_right (frostman_set_bound μ hs hC hfrost A) _
      _ = (Metric.ediam A)^s := by rw [← mul_assoc,ENNReal.inv_mul_cancel hK hKtop,one_mul]
  have hsup : (μ : Measure (Space d)) (μ : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  have hpositive : 0 < (K⁻¹ • (μ : Measure (Space d))) (μ : Measure (Space d)).support := by
    rw [Measure.smul_apply,smul_eq_mul,hsup,mul_one]
    exact pos_iff_ne_zero.mpr (ENNReal.inv_ne_zero.mpr hKtop)
  have hnonzero : Measure.hausdorffMeasure s (μ : Measure (Space d)).support ≠ 0 :=
    (hpositive.trans_le (hmeasure _)).ne'
  rw [ENNReal.ofReal_eq_coe_nnreal hs.le]
  exact le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨s,hs.le⟩) hnonzero

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_AffineSliceCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric coordinates and ball bounds on an actual charged affine plane -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem affineSliceMap_continuous (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p : Space d) : Continuous (affineSliceMap V hn p) :=
  (slicePointCoordinates_continuous V hn).comp (continuous_id.sub continuous_const)

theorem affineSliceModel_isometry (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p : Space d) : Isometry (affineSliceModel V hn p) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (p + ((sliceCoordinates V hn).symm x : Space d))
    (p + ((sliceCoordinates V hn).symm y : Space d)) = dist x y
  rw [dist_add_left]
  exact (sliceCoordinates V hn).symm.isometry.dist_eq x y

theorem affineSliceModel_map (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p x : Space d) (hx : x-p ∈ V) :
    affineSliceModel V hn p (affineSliceMap V hn p x) = x := by
  have he : V.orthogonalProjectionOnto (x-p) = (⟨x-p,hx⟩ : V) :=
    V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x-p,hx⟩
  simp only [affineSliceModel,affineSliceMap,slicePointCoordinates,he,
    LinearIsometryEquiv.symm_apply_apply,Subtype.coe_mk]
  abel

theorem affineSliceMap_dist (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p x : Space d) (hx : x-p ∈ V) (y : Space n) :
    dist (affineSliceMap V hn p x) y = dist x (affineSliceModel V hn p y) := by
  have he := (affineSliceModel_isometry V hn p).dist_eq (affineSliceMap V hn p x) y
  rw [affineSliceModel_map V hn p x hx] at he
  exact he.symm

theorem affineSliceMap_frostman (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (hn : Module.finrank ℝ V = n) (p : Space d)
    (hplane : μ {x | x-p ∈ V}ᶜ = 0) {s C : ℝ} (hfrost : FrostmanBallBound μ s C) :
    FrostmanBallBound (μ.map (affineSliceMap V hn p)) s C := by
  intro y r hr
  rw [Measure.map_apply (affineSliceMap_continuous V hn p).measurable Metric.isOpen_ball.measurableSet]
  apply le_trans _ (hfrost (affineSliceModel V hn p y) r hr)
  apply measure_mono_ae
  have hplane' : ∀ᵐ x ∂μ, x-p ∈ V := hplane
  filter_upwards [hplane'] with x hx
  intro hxy
  show x ∈ Metric.ball (affineSliceModel V hn p y) r
  simpa only [mem_preimage,Metric.mem_ball,affineSliceMap_dist V hn p x hx y] using (show affineSliceMap V hn p x ∈ Metric.ball y r from hxy)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ClassicalAffineDistance
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The strict classical threshold on a charged affine plane

Coordinates are used isometrically inside the actual affine plane, so the
conclusion concerns original distances.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem frostman_exponent_le_dimension (μ : ProbabilityMeasure (Space n)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space n)) s C) :
    s ≤ (n:ℝ) := by
  have hu : dimH (univ : Set (Space n)) = (n:ℝ≥0∞) := by
    simp [Real.dimH_univ_eq_finrank,Space]
  have hd := (frostman_dimension_lower μ hs hC hfrost).trans
    ((dimH_mono (subset_univ _)).trans_eq hu)
  have hh := ENNReal.toReal_mono (by simp : (n:ℝ≥0∞) ≠ ∞) hd
  simpa [ENNReal.toReal_ofReal hs.le] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DimensionDescent
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The charged-plane alternative by induction on the ambient dimension

The affine plane has strictly smaller dimension than the original odd ambient
space. The lower-dimensional distance theorem therefore applies to the
charged-plane alternative in the dimension induction.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem distance_in_affine_plane_of_lower_dimensions
    (hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (μ : ProbabilityMeasure (Space d)) (hK : IsCompact (μ : Measure (Space d)).support)
    (V : Submodule ℝ (Space d)) (hn : Module.finrank ℝ V = n) (hnlt : n < d) (p : Space d)
    (hplane : (μ : Measure (Space d)) {x | x-p ∈ V}ᶜ = 0)
    {s C : ℝ} (hs : ((n:ℝ)+1)/2 < s) (hC : 0 < C)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    0 < volume (distanceSet (μ : Measure (Space d)).support) := by
  let P := affineSliceMap V hn p
  let ν := μ.map (f := P) (affineSliceMap_continuous V hn p).aemeasurable
  have hP : Continuous P := affineSliceMap_continuous V hn p
  have hfrostν : FrostmanBallBound (ν : Measure (Space n)) s C :=
    affineSliceMap_frostman (μ : Measure (Space d)) V hn p hplane hfrost
  have hs0 : 0 < s := (by positivity : (0:ℝ) ≤ ((n:ℝ)+1)/2).trans_lt hs
  have hsN := frostman_exponent_le_dimension ν hs0 hC hfrostν
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have hn1 : n ≤ 1 := by omega
    have hn1R : (n:ℝ) ≤ 1 := by exact_mod_cast hn1
    linarith
  have himage := hK.image hP
  have hsub : (ν : Measure (Space n)).support ⊆ P '' (μ : Measure (Space d)).support := by
    apply Measure.support_subset_of_isClosed himage.isClosed
    change (μ : Measure (Space d)).map P (P '' (μ : Measure (Space d)).support)ᶜ = 0
    rw [Measure.map_apply hP.measurable himage.isClosed.measurableSet.compl]
    apply measure_mono_null _ Measure.measure_compl_support
    intro x hx hxS
    exact hx ⟨x,hxS,rfl⟩
  have hKν : IsCompact (ν : Measure (Space n)).support :=
    himage.of_isClosed_subset Measure.isClosed_support hsub
  have hclosed : IsClosed {x : Space d | x-p ∈ V} :=
    V.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)
  have hsplane : (μ : Measure (Space d)).support ⊆ {x | x-p ∈ V} :=
    Measure.support_subset_of_isClosed hclosed hplane
  have hhalf : (n : ℝ≥0∞)/2 = ENNReal.ofReal ((n:ℝ)/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_natCast]
    norm_num
  have hdim : (n : ℝ≥0∞)/2 < dimH (ν : Measure (Space n)).support := by
    rw [hhalf]
    apply lt_of_lt_of_le _ (frostman_dimension_lower ν hs0 hC hfrostν)
    apply ENNReal.ofReal_lt_ofReal_iff hs0 |>.mpr
    linarith
  apply positive_distance_of_isometric_model (affineSliceModel_isometry V hn p) _
    (hmain n hnlt hn2 _ hKν hdim)
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨x,hx,rfl⟩ := hsub hy
  simpa only [P,affineSliceModel_map V hn p x (hsplane hx)] using hx


theorem charged_plane_distance_of_lower_dimensions
    (hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (μ : ProbabilityMeasure (Space d)) (hK : IsCompact (μ : Measure (Space d)).support)
    (V : Submodule ℝ (Space d)) (hVlt : Module.finrank ℝ V < d) (p : Space d)
    (hcharge : 0 < (μ : Measure (Space d)) {x | x-p ∈ V})
    {s C : ℝ} (hs : ((Module.finrank ℝ V : ℝ)+1)/2 < s) (hC : 0 < C)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    0 < volume (distanceSet (μ : Measure (Space d)).support) := by
  let A : Set (Space d) := {x | x-p ∈ V}
  have hA : IsClosed A :=
    V.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)
  let ν := positiveRestriction μ A hcharge
  have hdom : (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) :=
    positiveRestriction_absolutelyContinuous μ A hcharge
  have hsupp : (ν : Measure (Space d)).support ⊆ (μ : Measure (Space d)).support :=
    hdom.support_mono
  have hKν : IsCompact (ν : Measure (Space d)).support :=
    hK.of_isClosed_subset Measure.isClosed_support hsupp
  have hplane : (ν : Measure (Space d)) Aᶜ = 0 := by
    change (positiveRestriction μ A hcharge : Measure (Space d)) Aᶜ = 0
    rw [positiveRestriction_eq,Measure.smul_apply,Measure.restrict_apply hA.measurableSet.compl,
      compl_inter_self,measure_empty,smul_zero]
  have hCν : 0 < ((μ : Measure (Space d)) A).toReal⁻¹*C :=
    mul_pos (inv_pos.mpr (ENNReal.toReal_pos hcharge.ne' (measure_ne_top _ _))) hC
  have hfrostν : FrostmanBallBound (ν : Measure (Space d)) s
      (((μ : Measure (Space d)) A).toReal⁻¹*C) := by
    have hid := positiveRestriction_projected_frostman μ A hcharge
      (ContinuousLinearMap.id ℝ (Space d)) (by simpa using hfrost)
    simpa using hid
  have hdist := distance_in_affine_plane_of_lower_dimensions hmain ν hKν V rfl hVlt p
    hplane hs hCν hfrostν
  exact hdist.trans_le (measure_mono (distanceSet_mono hsupp))


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EvenPreparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Even-dimensional starting pairs in the original compact set

This is the even-dimensional branch of `prep:starting-pairs`, not the
all-dimensional distance theorem. The cap and exceptional-set conclusions
refer to the original marginal laws in `Space (2*h)`.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem even_starting_pairs_of_published
    (hF : PublishedFrostmanAboveHalf) (hR : PublishedRadialMoment)
    {h : ℕ} (hh : 1 ≤ h) (E : Set (Space (2*h))) (hE : IsCompact E)
    (hDim : ((2*h:ℕ) : ℝ≥0∞)/2 < dimH E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ζ : ProbabilityMeasure (Space (2*h))) (δ : ℝ), 0 < δ ∧ δ < 1 ∧
      ∃ p : ProjectedStartingPair ζ (h+1) ((h:ℝ)+δ) ε,
        (p.left : Measure (Space (2*h))).support ⊆ E ∧
        (p.right : Measure (Space (2*h))).support ⊆ E ∧
        CapAvailable p.left p.right (fun _ => p.relation) (h:ℝ) := by
  have hd : 2 ≤ 2*h := by omega
  obtain ⟨s,hs,_,ζ,hζ,C,_,hfrost⟩ := hF (2*h) hd E hE hDim
  have hhs : (h:ℝ) < s := by
    push_cast at hs
    linarith only [hs]
  obtain ⟨δ,hδ,hδ1,p,hcap⟩ := exists_even_starting_caps hR hh ζ hhs hfrost hε
  have hsupp : (ζ : Measure (Space (2*h))).support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed hζ
  exact ⟨ζ,δ,hδ,hδ1,p,p.left_ac.support_mono.trans hsupp,
    p.right_ac.support_mono.trans hsupp,hcap⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Put compact projected supports in a fixed unit cube -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem mem_centeredUnitCube_of_norm {x : Space d} (hx : ‖x‖ ≤ 1/4) :
    x ∈ (centeredUnitCube d).carrier := by
  intro i
  have hi : |x i| ≤ 1/4 := (PiLp.norm_apply_le x i).trans hx
  change -(1/2:ℝ) ≤ x i ∧ x i < -(1/2:ℝ)+1
  constructor <;> linarith [abs_le.mp hi]

theorem compact_projection_into_unitCube (E : Set (Space d)) (hE : IsCompact E)
    (P : Space d →L[ℝ] Space m) :
    ∃ a : ℝ, 0 < a ∧ ‖a • P‖ ≤ 1 ∧
      ∀ x ∈ E, (a • P) x ∈ (centeredUnitCube m).carrier := by
  obtain ⟨M,hM,hbound⟩ := (hE.image P.continuous).isBounded.exists_pos_norm_le
  let a := (4*(M+‖P‖+1))⁻¹
  have hden : 0 < 4*(M+‖P‖+1) := by positivity
  have ha : 0 < a := inv_pos.mpr hden
  refine ⟨a,ha,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    change (4*(M+‖P‖+1))⁻¹*‖P‖ ≤ 1
    rw [inv_mul_le_iff₀ hden]
    nlinarith only [hM,norm_nonneg P]
  · intro x hx
    apply mem_centeredUnitCube_of_norm
    rw [smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    calc
      a * ‖P x‖ ≤ a*M := mul_le_mul_of_nonneg_left (hbound _ ⟨x,hx,rfl⟩) ha.le
      _ ≤ 1/4 := by
        change (4*(M+‖P‖+1))⁻¹*M ≤ 1/4
        rw [inv_mul_le_iff₀ hden]
        nlinarith only [norm_nonneg P]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoProjectionCubes
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible unit-cube normalization of two successive projections -/
namespace Falconer
open Set MeasureTheory
variable {d m k : ℕ}

theorem two_projections_into_unitCubes (E : Set (Space d)) (hE : IsCompact E)
    (P : Space d →L[ℝ] Space m) (Q : Space m →L[ℝ] Space k) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ‖a • P‖ ≤ 1 ∧ ‖b • Q‖ ≤ 1 ∧
      (∀ x ∈ E, (a • P) x ∈ (centeredUnitCube m).carrier) ∧
      (∀ x ∈ E, ((b • Q).comp (a • P)) x ∈ (centeredUnitCube k).carrier) := by
  obtain ⟨a,ha,hP,hroot⟩ := compact_projection_into_unitCube E hE P
  obtain ⟨b,hb,hQ,hroot'⟩ := compact_projection_into_unitCube ((a • P) '' E)
    (hE.image (a • P).continuous) Q
  exact ⟨a,b,ha,hb,hP,hQ,hroot,fun x hx => hroot' _ ⟨x,hx,rfl⟩⟩

theorem scaled_composite {a b : ℝ} (P : Space d →L[ℝ] Space m)
    (Q : Space m →L[ℝ] Space k) :
    (b • Q).comp (a • P) = (a*b) • (Q.comp P) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,smul_apply,map_smul,smul_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoProjectionFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized auxiliary frame for the odd-dimensional preparation -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

variable {d m k : ℕ}

private theorem enlarge_frostman {μ : Measure (Space d)} {s C D : ℝ}
    (h : FrostmanBallBound μ s C) (hCD : C ≤ D) : FrostmanBallBound μ s D := by
  intro x r hr
  exact (h x r hr).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hr.le _)))

theorem normalize_two_projected_laws (μ : ProbabilityMeasure (Space d))
    (hK : IsCompact (μ : Measure (Space d)).support)
    (P : Space d →L[ℝ] Space m) (Q : Space m →L[ℝ] Space k)
    {s C : ℝ} (hC : 0 < C)
    (hμ : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hP : FrostmanBallBound ((μ : Measure (Space d)).map P) s C)
    (hQ : FrostmanBallBound ((μ : Measure (Space d)).map (Q.comp P)) s C)
    (hnull : ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
      ((μ : Measure (Space d)).map P) {y | inner ℝ w y = t} = 0) :
    Nonempty (TwoProjectionFrame μ m k s) := by
  obtain ⟨a,b,ha,hb,hPa,hQb,hroot,hroot'⟩ :=
    two_projections_into_unitCubes (μ : Measure (Space d)).support hK P Q
  let C' := max C (max (C*a^(-s)) (C*(a*b)^(-s)))
  have h0 : C ≤ C' := le_max_left _ _
  have h1 : C*a^(-s) ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : C*(a*b)^(-s) ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨{
    first := a • P
    second := b • Q
    first_contractive := hPa
    second_contractive := hQb
    first_root := hroot
    second_root := hroot'
    noncharging := dilated_projection_hyperplane_null (μ : Measure (Space d)) P ha hnull
    constant := C'
    constant_pos := hC.trans_le h0
    original_frostman := enlarge_frostman hμ h0
    first_frostman := enlarge_frostman (dilated_projected_frostman _ P ha hP) h1
    second_frostman := ?_ }⟩
  rw [scaled_composite]
  exact enlarge_frostman (dilated_projected_frostman _ (Q.comp P) (mul_pos ha hb) hQ) h2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoProjectionPieces
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive compact pieces in the normalized two-projection frame -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

variable {d m k : ℕ} {μ : ProbabilityMeasure (Space d)} {s ε : ℝ}

theorem exists_two_projection_pieces (hK : IsCompact (μ : Measure (Space d)).support)
    (f : TwoProjectionFrame μ m k s) (hs : 0 < s) (hε : 0 < ε) :
    Nonempty (TwoProjectionPieces f ε) := by
  let := noAtoms_of_frostman ((μ : Measure (Space d)).map (f.second.comp f.first)) hs f.second_frostman
  obtain ⟨A,B,hA,hB,hAs,hBs,hAp,hBp,r,c,hr,hc,w,hw,hgeom⟩ :=
    projected_compact_pieces μ hK (f.second.comp f.first) hε
  exact ⟨⟨A,B,hA,hB,hAs,hBs,hAp,hBp,r,hr,c,hc,w,hw,hgeom⟩⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMultiband
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian multi-vector bands with their exact coordinate determinant -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d j : ℕ}

theorem gaussian_projected_coordinates (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space j) :
    (stdGaussian (Space d)).map (fun x => b (V.orthogonalProjectionOnto x)) =
      stdGaussian (Space j) := by
  change (stdGaussian (Space d)).map (b ∘ V.orthogonalProjectionOnto) = _
  rw [← Measure.map_map b.continuous.measurable V.orthogonalProjectionOnto.continuous.measurable,
    gaussian_orthogonal_projection,stdGaussian_map]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_BorelProductPartition
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite disjoint Borel products in the original ambient space -/
namespace Falconer
open Set MeasureTheory

theorem HasBorelProductPartition.mono_bound {d : ℕ} {S : Set (Space d × Space d)}
    {K L : ℝ} (h : HasBorelProductPartition S K) (hKL : K ≤ L) :
    HasBorelProductPartition S L := by
  obtain ⟨n,hn,A,B,hAB,hdis,hS⟩ := h
  exact ⟨n,hn.trans hKL,A,B,hAB,hdis,hS⟩

theorem borel_product_partition_single {d : ℕ} {A B : Set (Space d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    HasBorelProductPartition (A ×ˢ B) 1 := by
  refine ⟨1,by norm_num,(fun _ => A),(fun _ => B),(fun _ => ⟨hA,hB⟩),?_,?_⟩
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · ext z
    simp only [mem_iUnion]
    exact ⟨fun hz => ⟨0,hz⟩,fun ⟨_,hz⟩ => hz⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_RectangularGramSchmidt
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable Gram--Schmidt residuals with exact prefix dependence -/

namespace Falconer
open Set Submodule InnerProductSpace
variable {d m : ℕ}

theorem rectangular_gramSchmidt_measurable (i : Fin m) :
    Measurable (fun v : Fin m → Space d => gramSchmidt ℝ v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have he : (fun v : Fin m → Space d => gramSchmidt ℝ v i) =
        fun v => v i - ∑ j ∈ Finset.Iio i, (ℝ ∙ gramSchmidt ℝ v j).starProjection (v i) :=
      funext (fun v => gramSchmidt_def ℝ v i)
    rw [he]
    simp_rw [starProjection_singleton]
    apply (measurable_pi_apply i).sub
    apply Finset.measurable_sum
    intro j hj
    have hg := ih j (Finset.mem_Iio.mp hj)
    change Measurable (fun v : Fin m → Space d =>
      (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖^2) • gramSchmidt ℝ v j)
    exact ((hg.inner (measurable_pi_apply i)).div (hg.norm.pow_const 2)).smul hg

theorem rectangular_independent_of_residuals (v : Fin m → Space d)
    (hv : ∀ i, gramSchmidt ℝ v i ≠ 0) : LinearIndependent ℝ v := by
  have hgs : LinearIndependent ℝ (gramSchmidt ℝ v) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hv (fun _ _ hij => gramSchmidt_orthogonal ℝ v hij)
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin m) = Module.finrank ℝ (span ℝ (range v))
  rw [← span_gramSchmidt ℝ v]
  exact (finrank_span_eq_card hgs).symm

theorem rectangular_zero_residual_mem_prefix (v : Fin m → Space d) (i : Fin m)
    (hz : gramSchmidt ℝ v i = 0) : v i ∈ span ℝ (v '' Iio i) := by
  rw [← span_gramSchmidt_Iio ℝ v i,gramSchmidt_def' ℝ v i,hz,zero_add]
  apply Submodule.sum_mem
  intro j hj
  simp only [starProjection_singleton]
  apply Submodule.smul_mem
  exact subset_span ⟨j,Finset.mem_Iio.mp hj,rfl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AffineNullTuples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine-null laws give independent sampled differences -/
namespace Falconer
open Set Submodule MeasureTheory InnerProductSpace
open scoped ENNReal
variable {d n : ℕ}

theorem prefix_span_finrank_le (v : Fin (n+1) → Space d) (i : Fin (n+1)) :
    Module.finrank ℝ (span ℝ (v '' Iio i)) ≤ n := by
  classical
  have he : v '' Iio i = ((Finset.Iio i).image v : Set (Space d)) := by
    ext x
    simp
  rw [he]
  apply (finrank_span_finset_le_card (R := ℝ) _).trans
  apply Finset.card_image_le.trans
  simpa using Nat.le_of_lt_succ i.isLt

theorem affine_null_residual_mass (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      μ {x | x-p ∈ V} = 0) (p : Space d) (i : Fin (n+1)) :
    (Measure.pi (fun _ : Fin (n+1) => μ))
      {w | gramSchmidt ℝ (fun j => w j-p) i = 0} = 0 := by
  have hm : Measurable (fun w : Fin (n+1) → Space d => fun j => w j-p) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply j).sub measurable_const
  have hE : MeasurableSet {w : Fin (n+1) → Space d |
      gramSchmidt ℝ (fun j => w j-p) i = 0} :=
    measurableSet_eq_fun ((rectangular_gramSchmidt_measurable i).comp hm) measurable_const
  have hbound := pi_measure_le_of_coordinate_sections μ i _ hE (0:ℝ≥0∞)
  have hsections : ∀ y : Fin n → Space d,
      μ {x | gramSchmidt ℝ (fun j => (i.insertNth x y : Fin (n+1) → Space d) j-p) i = 0} ≤ 0 := by
    intro y
    let v : Fin (n+1) → Space d := fun j => (i.insertNth 0 y : Fin (n+1) → Space d) j-p
    let V := span ℝ (v '' Iio i)
    have hz := hnull p V (prefix_span_finrank_le v i)
    apply (measure_mono (t := {x | x-p ∈ V}) ?_).trans hz.le
    intro x hx
    let w : Fin (n+1) → Space d := fun j => (i.insertNth x y : Fin (n+1) → Space d) j-p
    have hmem := rectangular_zero_residual_mem_prefix w i hx
    have hsub : w '' Iio i ⊆ v '' Iio i := by
      rintro _ ⟨j,hj,rfl⟩
      refine ⟨j,hj,?_⟩
      dsimp [v,w]
      rw [Fin.insertNth_apply_below hj,Fin.insertNth_apply_below hj]
    have hh := (span_mono hsub) hmem
    simpa only [mem_ofPred_eq,V,w,Fin.insertNth_apply_same] using hh
  have hle : (Measure.pi (fun _ : Fin (n+1) => μ))
      {w | gramSchmidt ℝ (fun j => w j-p) i = 0} ≤ 0 := by
    simpa only [zero_mul] using hbound hsections
  exact le_antisymm hle bot_le

theorem affine_null_differences_independent_ae (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      μ {x | x-p ∈ V} = 0) (p : Space d) :
    ∀ᵐ w : Fin (n+1) → Space d ∂Measure.pi (fun _ => μ),
      LinearIndependent ℝ (fun j => w j-p) := by
  have hzero : (Measure.pi (fun _ : Fin (n+1) => μ))
      (⋃ i : Fin (n+1), {w | gramSchmidt ℝ (fun j => w j-p) i = 0}) = 0 :=
    measure_iUnion_null (affine_null_residual_mass μ hnull p)
  have hgood : ∀ᵐ w : Fin (n+1) → Space d ∂Measure.pi (fun _ => μ),
      w ∉ ⋃ i : Fin (n+1), {w | gramSchmidt ℝ (fun j => w j-p) i = 0} := by
    rw [ae_iff]
    simpa only [not_not,ofPred_mem_eq] using hzero
  filter_upwards [hgood] with w hw
  apply rectangular_independent_of_residuals
  intro i hi
  exact hw (mem_iUnion.mpr ⟨i,hi⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianFullRank
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A square Gaussian matrix is nonsingular almost surely

Each zero Gram--Schmidt residual lies in a Gaussian-null fixed hyperplane
when the other rows are fixed. No polynomial zero-set theorem is assumed.
-/
namespace Falconer
open Set MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal BigOperators
variable {n : ℕ}

theorem gaussian_residual_zero_mass (i : Fin (n+1)) :
    gaussianRows (n+1) (n+1) {v | gramSchmidt ℝ v i = 0} = 0 := by
  have hh := pi_measure_le_of_coordinate_sections (stdGaussian (Space (n+1))) i
    {v | gramSchmidt ℝ v i = 0}
    (measurableSet_eq_fun (gramSchmidt_measurable i) measurable_const) (0:ℝ≥0∞)
  have hsections : ∀ y, stdGaussian (Space (n+1))
      {x | gramSchmidt ℝ (i.insertNth x y) i = 0} ≤ 0 := by
    intro y
    let v : Fin (n+1) → Space (n+1) := i.insertNth 0 y
    obtain ⟨w,hw,hinner⟩ := small_residual_fixed_slab v i
    have hsub : {x : Space (n+1) | gramSchmidt ℝ (i.insertNth x y) i = 0} ⊆
        {x | |inner ℝ w x| ≤ 0} := by
      intro x hx
      change gramSchmidt ℝ (i.insertNth x y) i = 0 at hx
      have hprefix : ∀ j : Fin (n+1), j < i →
          (i.insertNth x y : Fin (n+1) → Space (n+1)) j = v j := by
        intro j hj
        dsimp [v]
        rw [Fin.insertNth_apply_below hj,Fin.insertNth_apply_below hj]
      have hb := hinner (i.insertNth x y) hprefix
      simpa only [mem_ofPred_eq,Fin.insertNth_apply_same,hx,norm_zero] using hb
    exact (measure_mono hsub).trans (by simpa using gaussian_unit_inner_band hw (le_refl (0:ℝ)))
  have hle : gaussianRows (n+1) (n+1) {v | gramSchmidt ℝ v i = 0} ≤ 0 := by
    simpa only [gaussianRows,zero_mul] using hh hsections
  exact le_antisymm hle bot_le

theorem gaussian_square_det_ne_zero_ae :
    ∀ᵐ v : Fin (n+1) → Space (n+1) ∂gaussianRows (n+1) (n+1),
      (euclideanColumnMatrix v).det ≠ 0 := by
  have hzero : gaussianRows (n+1) (n+1)
      (⋃ i : Fin (n+1), {v | gramSchmidt ℝ v i = 0}) = 0 :=
    measure_iUnion_null gaussian_residual_zero_mass
  have hgood : ∀ᵐ v : Fin (n+1) → Space (n+1) ∂gaussianRows (n+1) (n+1),
      v ∉ ⋃ i : Fin (n+1), {v | gramSchmidt ℝ v i = 0} := by
    rw [ae_iff]
    simpa only [not_not,ofPred_mem_eq] using hzero
  filter_upwards [hgood] with v hv hdet
  have hp : (∏ i : Fin (n+1), ‖gramSchmidt ℝ v i‖) = 0 := by
    rw [← gram_volume_eq_residual_product,euclideanColumnMatrix_gram_sqrt,hdet,abs_zero]
  obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp hp
  exact hv (mem_iUnion.mpr ⟨i,norm_eq_zero.mp hi⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSpanRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian rows projected onto a fixed finite-dimensional span -/
namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d m : ℕ}

theorem projectedGaussianRows_measurable (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space m) : Measurable (projectedGaussianRows V b) := by
  apply measurable_pi_iff.mpr
  intro i
  exact b.continuous.measurable.comp
    (V.orthogonalProjectionOnto.continuous.measurable.comp (measurable_pi_apply i))

theorem projectedGaussianRows_law (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space m) :
    (gaussianRows d m).map (projectedGaussianRows V b) = gaussianRows m m := by
  let f : Space d → Space m := fun x => b (V.orthogonalProjectionOnto x)
  have hf : Measurable f := b.continuous.measurable.comp V.orthogonalProjectionOnto.continuous.measurable
  change (Measure.pi (fun _ : Fin m => stdGaussian (Space d))).map (fun A i => f (A i)) = _
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  exact congrArg Measure.pi (funext (fun _ => gaussian_projected_coordinates V b))

theorem inner_projectedGaussianRows (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space m) (A : Fin m → Space d) (z : V) (i : Fin m) :
    inner ℝ (b z) (projectedGaussianRows V b A i) = inner ℝ (z : Space d) (A i) := by
  rw [projectedGaussianRows,b.inner_map_map]
  exact V.inner_orthogonalProjectionOnto_eq_of_mem_left z (A i)

theorem eq_zero_of_orthogonal_columns (v : Fin m → Space m)
    (hv : (euclideanColumnMatrix v).det ≠ 0) (z : Space m)
    (hz : ∀ i, inner ℝ z (v i) = 0) : z = 0 := by
  obtain ⟨a,ha⟩ := (euclideanColumnEquiv v hv).surjective z
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ z z = inner ℝ z (∑ i, a i • v i) := by
      rw [← ha]
      rfl
    _ = 0 := by simp [inner_sum,inner_smul_right,hz]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPreservesIndependence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Gaussian map preserves each fixed independent family almost surely -/
namespace Falconer
open Set Submodule MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem gaussian_preserves_independent_family (v : Fin (n+1) → Space d)
    (hv : LinearIndependent ℝ v) :
    ∀ᵐ A : Fin (n+1) → Space d ∂gaussianRows d (n+1),
      LinearIndependent ℝ (fun i => gaussianRowMap A (v i)) := by
  let V := span ℝ (range v)
  have hdim : Module.finrank ℝ V = n+1 := by
    simpa [V] using finrank_span_eq_card hv
  let b := sliceCoordinates V hdim
  have ha : ∀ᵐ A : Fin (n+1) → Space d ∂gaussianRows d (n+1),
      (euclideanColumnMatrix (projectedGaussianRows V b A)).det ≠ 0 := by
    apply ae_of_ae_map (μ := gaussianRows d (n+1))
      (p := fun C => (euclideanColumnMatrix C).det ≠ 0)
      (projectedGaussianRows_measurable V b).aemeasurable
    rw [projectedGaussianRows_law]
    exact gaussian_square_det_ne_zero_ae
  filter_upwards [ha] with A hA
  have hker (z : Space d) (hz : z ∈ V) (hzero : gaussianRowMap A z = 0) : z = 0 := by
    have he := eq_zero_of_orthogonal_columns (projectedGaussianRows V b A) hA (b ⟨z,hz⟩) (by
      intro i
      rw [inner_projectedGaussianRows]
      have hi := congrArg (fun w : Space (n+1) => w i) hzero
      simpa only [gaussianRowMap_apply,PiLp.zero_apply] using hi)
    have hz' : (⟨z,hz⟩ : V) = 0 := b.injective (by simpa using he)
    exact congrArg Subtype.val hz'
  apply hv.map_injOn (gaussianRowMap A).toLinearMap
  intro x hx y hy hxy
  change gaussianRowMap A x = gaussianRowMap A y at hxy
  exact sub_eq_zero.mp (hker (x-y) (V.sub_mem hx hy) (by
    rw [map_sub,hxy,sub_self]))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ProjectedIndependentTuples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fubini transfers affine independence to almost every projected law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem independent_difference_tuple_measurable :
    MeasurableSet {z : Space d × (Fin (n+1) → Space d) |
      LinearIndependent ℝ (fun i => z.2 i-z.1)} := by
  apply isOpen_setOfPred_linearIndependent.measurableSet.preimage
  exact (continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).sub
    continuous_fst)).measurable

theorem projected_independent_tuple_measurable :
    MeasurableSet {q : (Space d × (Fin (n+1) → Space d)) × (Fin (n+1) → Space d) |
      LinearIndependent ℝ (fun i => gaussianRowMap q.2 (q.1.2 i-q.1.1))} := by
  apply isOpen_setOfPred_linearIndependent.measurableSet.preimage
  apply Continuous.measurable
  apply continuous_pi
  intro i
  change Continuous (fun q : (Space d × (Fin (n+1) → Space d)) × (Fin (n+1) → Space d) =>
    WithLp.toLp 2 (fun j => inner ℝ (q.2 j) (q.1.2 i-q.1.1)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact ((continuous_apply j).comp continuous_snd).inner
    (((continuous_apply i).comp (continuous_snd.comp continuous_fst)).sub
      (continuous_fst.comp continuous_fst))

theorem gaussian_projected_tuple_independent_ae (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      μ {x | x-p ∈ V} = 0) :
    ∀ᵐ A : Fin (n+1) → Space d ∂gaussianRows d (n+1),
      ∀ᵐ z : Space d × (Fin (n+1) → Space d) ∂μ.prod (Measure.pi (fun _ => μ)),
        LinearIndependent ℝ (fun i => gaussianRowMap A (z.2 i-z.1)) := by
  have ho : ∀ᵐ z : Space d × (Fin (n+1) → Space d) ∂μ.prod (Measure.pi (fun _ => μ)),
      LinearIndependent ℝ (fun i => z.2 i-z.1) := by
    apply (Measure.ae_prod_iff_ae_ae independent_difference_tuple_measurable).mpr
    exact Filter.Eventually.of_forall (affine_null_differences_independent_ae μ hnull)
  apply (Measure.ae_ae_comm projected_independent_tuple_measurable).mp
  filter_upwards [ho] with z hz
  exact gaussian_preserves_independent_family _ hz

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ProjectedHyperplaneNull
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent sampled tuples exclude mass on projected hyperplanes -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem orthogonal_independent_square_eq_zero (v : Fin (n+1) → Space (n+1))
    (hv : LinearIndependent ℝ v) (w : Space (n+1))
    (horth : ∀ i, inner ℝ w (v i) = 0) : w = 0 := by
  have hdet : (euclideanColumnMatrix v).det ≠ 0 := by
    intro hd
    have hg := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv
    apply hg
    rw [euclideanColumnMatrix_gram,Matrix.det_mul,Matrix.det_transpose,hd,mul_zero]
  exact eq_zero_of_orthogonal_columns v hdet w horth

theorem projected_hyperplane_null_of_tuples (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (P : Space d →L[ℝ] Space (n+1))
    (htuple : ∀ᵐ z : Space d × (Fin (n+1) → Space d) ∂μ.prod (Measure.pi (fun _ => μ)),
      LinearIndependent ℝ (fun i => P (z.2 i-z.1)))
    (w : Space (n+1)) (hw : ‖w‖ = 1) (t : ℝ) :
    (μ.map P) {y | inner ℝ w y = t} = 0 := by
  rw [Measure.map_apply P.continuous.measurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
  let K : Set (Space d) := {x | inner ℝ w (P x) = t}
  change μ K = 0
  by_contra hK
  have hpos : 0 < (μ.prod (Measure.pi (fun _ : Fin (n+1) => μ)))
      (K ×ˢ Set.pi univ (fun _ => K)) := by
    rw [Measure.prod_prod,Measure.pi_pi,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pos_iff_ne_zero.mpr (mul_ne_zero hK (pow_ne_zero _ hK))
  obtain ⟨z,hz,hind⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (ae_restrict_of_ae htuple)
  have horth (i : Fin (n+1)) : inner ℝ w (P (z.2 i-z.1)) = 0 := by
    rw [map_sub,inner_sub_right]
    exact sub_eq_zero.mpr ((hz.2 i (mem_univ i)).trans hz.1.symm)
  have hzero := orthogonal_independent_square_eq_zero _ hind w horth
  rw [hzero,norm_zero] at hw
  norm_num at hw

theorem gaussian_projected_hyperplanes_null_ae (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      μ {x | x-p ∈ V} = 0) :
    ∀ᵐ A : Fin (n+1) → Space d ∂gaussianRows d (n+1),
      ∀ w : Space (n+1), ‖w‖ = 1 → ∀ t : ℝ,
        (μ.map (gaussianRowMap A)) {y | inner ℝ w y = t} = 0 := by
  filter_upwards [gaussian_projected_tuple_independent_ae μ hnull] with A hA w hw t
  exact projected_hyperplane_null_of_tuples μ _ hA w hw t

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChooseNonchargingProjection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Select a noncharging projection and one common compact Frostman law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem choose_noncharging_projected_frostman (μ : ProbabilityMeasure (Space d))
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hum : u < (n+1:ℕ))
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      (μ : Measure (Space d)) {x | x-p ∈ V} = 0) :
    ∃ P : Space d →L[ℝ] Space (n+1), ∃ ν : ProbabilityMeasure (Space d),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ t : ℝ,
        ((ν : Measure (Space d)).map P) {y | inner ℝ w y = t} = 0) ∧
      ∃ D : ℝ, 0 < D ∧ FrostmanBallBound (ν : Measure (Space d)) u D ∧
        FrostmanBallBound ((ν : Measure (Space d)).map P) u D := by
  have hsource := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space d)) hu hus hfrost
  obtain ⟨A,hA,hn⟩ := ((gaussian_projected_energy_finite_ae (m := n+1)
    (μ : Measure (Space d)) hu hum hsource).and
      (gaussian_projected_hyperplanes_null_ae (μ : Measure (Space d)) hnull)).exists
  let P := gaussianRowMap A
  let dims : Bool → ℕ | false => d | true => n+1
  let maps : ∀ b, Space d →L[ℝ] Space (dims b)
    | false => ContinuousLinearMap.id ℝ (Space d)
    | true => P
  have henergy : ∀ b, PlanarFalconer.rieszEnergyOn
      ((μ : Measure (Space d)).map (maps b)) u < ∞ := by
    intro b
    cases b with
    | false => simpa [maps,dims] using hsource
    | true => exact hA
  obtain ⟨ν,hK,hdom,D,hD,hbounds⟩ := normalized_projected_frostman μ dims maps hu henergy
  refine ⟨P,ν,hK,hdom,?_,D,hD,?_,hbounds true⟩
  · intro w hw t
    exact (hdom.map P.continuous.measurable) (hn w hw t)
  · simpa [maps,dims] using hbounds false

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SecondProjectedFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous original, first-projection and second-projection ball bounds -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m k : ℕ}

theorem choose_second_projected_frostman (μ : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space m) {u : ℝ} (hu : 0 < u) (huk : u < (k:ℝ))
    (hsource : PlanarFalconer.rieszEnergyOn (μ : Measure (Space d)) u < ∞)
    (hfirst : PlanarFalconer.rieszEnergyOn ((μ : Measure (Space d)).map P) u < ∞) :
    ∃ Q : Space m →L[ℝ] Space k, ∃ ν : ProbabilityMeasure (Space d),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      ∃ C : ℝ, 0 < C ∧ FrostmanBallBound (ν : Measure (Space d)) u C ∧
        FrostmanBallBound ((ν : Measure (Space d)).map P) u C ∧
        FrostmanBallBound ((ν : Measure (Space d)).map (Q.comp P)) u C := by
  obtain ⟨A,hA⟩ := (gaussian_projected_energy_finite_ae (m := k)
    ((μ : Measure (Space d)).map P) hu huk hfirst).exists
  let Q := gaussianRowMap A
  let dims : Option Bool → ℕ | none => d | some false => m | some true => k
  let maps : ∀ i, Space d →L[ℝ] Space (dims i)
    | none => ContinuousLinearMap.id ℝ (Space d)
    | some false => P
    | some true => Q.comp P
  have henergy : ∀ i, PlanarFalconer.rieszEnergyOn
      ((μ : Measure (Space d)).map (maps i)) u < ∞ := by
    intro i
    cases i with
    | none => simpa [maps,dims] using hsource
    | some i =>
      cases i with
      | false => exact hfirst
      | true =>
        rw [Measure.map_map Q.continuous.measurable P.continuous.measurable] at hA
        exact hA
  obtain ⟨ν,hK,hdom,C,hC,hbounds⟩ := normalized_projected_frostman μ dims maps hu henergy
  refine ⟨Q,ν,hK,hdom,C,hC,?_,hbounds (some false),hbounds (some true)⟩
  simpa [maps,dims] using hbounds none

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TwoProjectedLaws
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two successive auxiliary laws with noncharging in the first target

The two exponent gaps are explicit: energy is taken below the first common
Frostman exponent before choosing the smaller auxiliary target.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem choose_two_projected_laws (μ : ProbabilityMeasure (Space d))
    {s C u v : ℝ} (hu : 0 < u) (huv : u < v) (hvs : v < s)
    (hv : v < (n+1:ℕ)) (hun : u < (n:ℝ))
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      (μ : Measure (Space d)) {x | x-p ∈ V} = 0) :
    ∃ (P : Space d →L[ℝ] Space (n+1)) (Q : Space (n+1) →L[ℝ] Space n)
      (ν : ProbabilityMeasure (Space d)),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ t : ℝ,
        ((ν : Measure (Space d)).map P) {y | inner ℝ w y = t} = 0) ∧
      ∃ D : ℝ, 0 < D ∧ FrostmanBallBound (ν : Measure (Space d)) u D ∧
        FrostmanBallBound ((ν : Measure (Space d)).map P) u D ∧
        FrostmanBallBound ((ν : Measure (Space d)).map (Q.comp P)) u D := by
  obtain ⟨P,η,_,hηdom,hηnull,D,_,hη,hηP⟩ :=
    choose_noncharging_projected_frostman μ (hu.trans huv) hvs hv hfrost hnull
  have hηenergy := rieszEnergyOn_lt_top_of_frostman (η : Measure (Space d)) hu huv hη
  have hηPenergy := rieszEnergyOn_lt_top_of_frostman ((η : Measure (Space d)).map P) hu huv hηP
  obtain ⟨Q,ν,hK,hdom,D',hD',hν,hνP,hνQ⟩ :=
    choose_second_projected_frostman η P hu hun hηenergy hηPenergy
  refine ⟨P,Q,ν,hK,hdom.trans hηdom,?_,D',hD',hν,hνP,hνQ⟩
  intro w hw t
  exact (hdom.map P.continuous.measurable) (hηnull w hw t)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OddProjectedPieces
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choose the normalized pair geometry in the noncharging odd-dimensional case -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem choose_odd_projected_pieces (hn : 2 ≤ n) (μ : ProbabilityMeasure (Space d))
    {s C ε : ℝ} (hs : (n:ℝ)-1/2 < s)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      (μ : Measure (Space d)) {x | x-p ∈ V} = 0) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      ∃ ν : ProbabilityMeasure (Space d), IsCompact (ν : Measure (Space d)).support ∧
        (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
        ∃ f : TwoProjectionFrame ν (n+1) n ((n:ℝ)-1/2+δ),
          Nonempty (TwoProjectionPieces f ε) := by
  let δ := min (s-((n:ℝ)-1/2)) (1/2) / 3
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hs) (by norm_num)) (by norm_num)
  have hδbound : δ ≤ (1/2:ℝ)/3 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hδs : 3*δ ≤ s-((n:ℝ)-1/2) := by
    dsimp [δ]
    linarith only [min_le_left (s-((n:ℝ)-1/2)) (1/2)]
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  let u := (n:ℝ)-1/2+δ
  let v := (n:ℝ)-1/2+2*δ
  have hu : 0 < u := by dsimp [u]; linarith
  have huv : u < v := by dsimp [u,v]; linarith
  have hvs : v < s := by dsimp [v]; linarith
  have hv : v < (n+1:ℕ) := by dsimp [v]; push_cast; linarith
  have hun : u < (n:ℝ) := by dsimp [u]; linarith
  obtain ⟨P,Q,ν,hK,hdom,hzero,D,hD,hν,hP,hQ⟩ :=
    choose_two_projected_laws μ hu huv hvs hv hun hfrost hnull
  obtain ⟨f⟩ := normalize_two_projected_laws ν hK P Q hD hν hP hQ hzero
  refine ⟨δ,hδ,by linarith,ν,hK,hdom,f,?_⟩
  exact exists_two_projection_pieces hK f hu hε

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PreparedPair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original starting pairs with the complete finite-filter interface

The pair and its Frostman gap are fixed before the coarse loss is chosen.
All cap bounds and partitions concern the original marginal laws.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem even_prepared_original_pair
    (hF : PublishedFrostmanAboveHalf) (hR : PublishedRadialMoment)
    {h : ℕ} (hh : 1 ≤ h) (E : Set (Space (2*h))) (hE : IsCompact E)
    (hDim : ((2*h:ℕ):ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (PreparedOriginalPair E ε) := by
  obtain ⟨ζ,δ,hδ,_,p,hleft,hright,hcap⟩ :=
    even_starting_pairs_of_published hF hR hh E hE hDim hε
  have hhalf : ((2*h:ℕ):ℝ)/2 = (h:ℝ) := by push_cast; ring
  refine ⟨{
    auxiliaryDimension := h+1
    exponent := (h:ℝ)+δ
    exponent_gt := by rw [hhalf]; linarith
    base := ζ
    pair := p
    left_subset := hleft
    right_subset := hright
    filters := ?_ }⟩
  intro ω hω _
  refine ⟨fun _ => p.relation,fun _ => p.relation_measurable,
    fun _ _ _ => subset_rfl,?_,fun _ => subset_rfl,?_,?_⟩
  · rw [iInter_const,p.relation_mass]
    norm_num
  · intro N
    have hbound : (1:ℝ) ≤ (2:ℝ)^(2*((2*h:ℕ):ℝ)*ω*(N:ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    exact (borel_product_partition_single Measure.isClosed_support.measurableSet
      Measure.isClosed_support.measurableSet).mono_bound hbound
  · simpa only [hhalf] using hcap

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OddPreparedPair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The odd-dimensional preparation and the genuine classical-plane alternative -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem odd_noncharging_prepared_original_pair
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} (E : Set (Space (2*h+3))) (hE : IsCompact E)
    (μ : ProbabilityMeasure (Space (2*h+3)))
    (hμE : (μ : Measure (Space (2*h+3))) Eᶜ = 0)
    {s C ε : ℝ} (hs : (h:ℝ)+3/2 < s)
    (hfrost : FrostmanBallBound (μ : Measure (Space (2*h+3))) s C)
    (hnull : ∀ x : Space (2*h+3), ∀ V : Submodule ℝ (Space (2*h+3)),
      Module.finrank ℝ V ≤ h+2 → (μ : Measure (Space (2*h+3))) {y | y-x ∈ V} = 0)
    (hε : 0 < ε) : Nonempty (PreparedOriginalPair E ε) := by
  have hs' : ((h+2:ℕ):ℝ)-1/2 < s := by push_cast; linarith
  obtain ⟨δ,hδ,hδ1,ζ,hK,hdom,f,⟨p⟩⟩ :=
    choose_odd_projected_pieces (by omega : 2 ≤ h+2) μ hs' hfrost hnull hε
  have hα : (h:ℝ)+3/2 < ((h+2:ℕ):ℝ)-1/2+δ := by push_cast; linarith
  have hα' : ((h+2:ℕ):ℝ)-1/2+δ < (h:ℝ)+2 := by push_cast; linarith
  have hhalf : ((2*h+3:ℕ):ℝ)/2 = (h:ℝ)+3/2 := by push_cast; ring
  have hsupp : (μ : Measure (Space (2*h+3))).support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed hμE
  refine ⟨{
    auxiliaryDimension := h+3
    exponent := ((h+2:ℕ):ℝ)-1/2+δ
    exponent_gt := by rw [hhalf]; exact hα
    base := ζ
    pair := p.firstPair
    left_subset := (p.left_ac.trans hdom).support_mono.trans hsupp
    right_subset := (p.right_ac.trans hdom).support_mono.trans hsupp
    filters := ?_ }⟩
  intro ω hω hω1
  obtain ⟨Γ,hΓ,hanti,hpos,hsub,hcap,hpartition⟩ :=
    p.odd_original_caps_partition hR hH hF hLW hα hα' hω hω1
  refine ⟨Γ,hΓ,hanti,hpos,hsub,?_,?_⟩
  · intro N
    apply (hpartition N).mono_bound
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hdim : ((h+3:ℕ):ℝ) ≤ ((2*h+3:ℕ):ℝ) := by exact_mod_cast (by omega : h+3 ≤ 2*h+3)
    nlinarith only [mul_le_mul_of_nonneg_right hdim (mul_nonneg hω.le (Nat.cast_nonneg N))]
  · simpa only [hhalf, TwoProjectionPieces.firstPair] using hcap

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OddDescent
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Odd-dimensional preparation using only lower-dimensional main statements -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem odd_prepared_pair_of_lower_dimensions
    (hFrostman : PublishedFrostmanAboveHalf)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ}
    (hmain : ∀ k : ℕ, k < 2*h+3 → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (E : Set (Space (2*h+3))) (hE : IsCompact E)
    (hDim : ((2*h+3:ℕ):ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
    0 < volume (distanceSet E) ∨ Nonempty (PreparedOriginalPair E ε) := by
  obtain ⟨s,hs,_,μ,hμE,C,hC,hfrost⟩ :=
    hFrostman (2*h+3) (by omega) E hE hDim
  have hs' : (h:ℝ)+3/2 < s := by push_cast at hs; linarith
  have hsupp : (μ : Measure (Space (2*h+3))).support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed hμE
  by_cases hnull : ∀ x : Space (2*h+3), ∀ V : Submodule ℝ (Space (2*h+3)),
      Module.finrank ℝ V ≤ h+2 → (μ : Measure (Space (2*h+3))) {y | y-x ∈ V} = 0
  · exact Or.inr (odd_noncharging_prepared_original_pair hR hH hF hLW
      E hE μ hμE hs' hfrost hnull hε)
  · push Not at hnull
    obtain ⟨x,V,hV,hcharge⟩ := hnull
    have hVr : (Module.finrank ℝ V:ℝ) ≤ (h:ℝ)+2 := by exact_mod_cast hV
    have hthreshold : ((Module.finrank ℝ V:ℝ)+1)/2 < s := by
      nlinarith [show (0:ℝ) ≤ (h:ℝ) by positivity]
    have hdist := charged_plane_distance_of_lower_dimensions hmain μ
      (hE.of_isClosed_subset Measure.isClosed_support hsupp) V (by omega) x
      (pos_iff_ne_zero.mpr hcharge) hthreshold hC hfrost
    exact Or.inl (hdist.trans_le (measure_mono (distanceSet_mono hsupp)))


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_StartingDescent
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient preparation by strict dimension descent in the charged case -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem prepared_pair_of_lower_dimensions_oai
    (hFrostman : PublishedFrostmanAboveHalf)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {d : ℕ}
    (hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (hd : 2 ≤ d) (E : Set (Space d)) (hE : IsCompact E)
    (hDim : (d:ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
    0 < volume (distanceSet E) ∨ Nonempty (PreparedOriginalPair E ε) := by
  by_cases heven : d % 2 = 0
  · obtain ⟨h,hh,rfl⟩ : ∃ h : ℕ, 1 ≤ h ∧ d = 2*h :=
      ⟨d/2,by omega,by omega⟩
    exact Or.inr (even_prepared_original_pair hFrostman hR hh E hE hDim hε)
  · obtain ⟨h,rfl⟩ : ∃ h : ℕ, d = 2*h+3 := ⟨(d-3)/2,by omega⟩
    exact odd_prepared_pair_of_lower_dimensions
      hFrostman hR hH hF hLW hmain E hE hDim hε


end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.prepared_pair_of_lower_dimensions_oai := @OAI.Falconer.prepared_pair_of_lower_dimensions_oai
