-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:25.544687+00:00
-- url     : https://prove2.me/submissions/eb8a7ebe-bab8-41d2-a67e-17846bc66982

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Definitions.Def_OAIQ231Rr001
import Theorems.Thm_OAI_RieszRectifiability_exists_dyadic_planar_measure_limit
import Theorems.Thm_OAI_RieszRectifiability_planar_full_support_of_reflectionless

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_MeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

theorem kernel_antisymm {d : ℕ} (n : ℕ) (x y : Ambient d) :
    kernel n y x = -kernel n x y := by
  rw [kernel, kernel, norm_sub_rev, ← neg_sub x y, smul_neg]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Elementary measurability and inverse-distance bounds for the Euclidean Riesz kernel.
Global upper growth records the ball-mass estimate used in kernel integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_measurable_right {d : ℕ} (n : ℕ) (x : Ambient d) :
    Measurable (kernel n x) := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  unfold kernel
  fun_prop

theorem kernel_norm_of_ne {d : ℕ} (n : ℕ) (x y : Ambient d) (hxy : x ≠ y) :
    ‖kernel n x y‖ = (dist x y ^ n)⁻¹ := by
  have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hnonneg : 0 ≤ (‖x - y‖ ^ (n + 1))⁻¹ := by positivity
  rw [kernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, dist_eq_norm, pow_succ]
  field_simp

theorem kernel_norm_le_truncation {d : ℕ} (n : ℕ) (x y : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (hy : ε ≤ dist x y) :
    ‖kernel n x y‖ ≤ (ε ^ n)⁻¹ := by
  have hd : 0 < dist x y := lt_of_lt_of_le hε hy
  rw [kernel_norm_of_ne n x y (dist_pos.mp hd)]
  simpa only [one_div] using!
    one_div_le_one_div_of_le (pow_pos hε n) (pow_le_pow_left₀ hε.le hy n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]
  [OpensMeasurableSpace X] [Nonempty X]

theorem finiteMeasure_cell_mass_tendsto (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (s : Set X) (hboundary : (ν : Measure X) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure X).real s) atTop (𝓝 ((ν : Measure X).real s)) := by
  have hn : Tendsto (fun j => (μ j).normalize) atTop (𝓝 ν.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hweak hν
  have hb : ν.normalize (frontier s) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν]
    rw [(ν.null_iff_toMeasure_null _).mpr hboundary, mul_zero]
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hb
  have hmass : Tendsto (fun j => (μ j) s) atTop (𝓝 (ν s)) := by
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using! hweak.mass.mul hp
  exact NNReal.continuous_coe.continuousAt.tendsto.comp hmass

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneBoxGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function
open scoped NNReal ENNReal

theorem GlobalUpperGrowth.mono_constant {d n : ℕ} {C D : ℝ}
    {μ : Measure (Ambient d)} (h : GlobalUpperGrowth n C μ) (hCD : C ≤ D) :
    GlobalUpperGrowth n D μ := by
  refine ⟨h.1.trans hCD, ?_⟩
  intro x r hr
  exact (h.2 x r hr).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (pow_nonneg hr.le n)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_OpenPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Open projection boxes and coordinate-plane measures

Pulling back open boxes along continuous coordinates gives open subsets of the
ambient space. Coordinate-plane measures satisfy upper growth bounds, which
in turn imply finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem GlobalUpperGrowth.finite_on_compacts {d n : ℕ} {C : ℝ}
    {μ : Measure (Ambient d)} (h : GlobalUpperGrowth n C μ) : IsFiniteMeasureOnCompacts μ := by
  let : IsLocallyFiniteMeasure μ := ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num),
    (h.2 x 1 (by norm_num)).trans_lt ENNReal.ofReal_lt_top⟩⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ClosedBallMeasureComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem measure_le_of_closedBall_le {d : ℕ} (ρ ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ρ] [IsFiniteMeasureOnCompacts ν]
    (hball : ∀ x : Ambient d, ∀ r : ℝ, 0 < r → ρ (closedBall x r) ≤ ν (closedBall x r)) :
    ρ ≤ ν := by
  apply Measure.le_iff'.mpr
  intro s
  let v := Besicovitch.vitaliFamily ρ
  apply v.measure_le_of_frequently_le ν Measure.AbsolutelyContinuous.rfl s
  intro x _hx
  apply Filter.Eventually.frequently
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with a ha
  obtain ⟨r, hr, rfl⟩ := ha
  exact hball x r hr

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PlanarPullbackMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pullback along the adjoint of an isometric embedding transports a measure supported on
its range to Euclidean coordinates, preserving ball masses and upper growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem planarPullbackMeasure_recover {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d))) :
    (planarPullbackMeasure L ν).map L = ν := by
  rw [planarPullbackMeasure, Measure.map_map L.continuous.measurable
    L.toContinuousLinearMap.adjoint.continuous.measurable]
  have heq : (fun x => L (L.toContinuousLinearMap.adjoint x)) =ᵐ[ν] id := by
    filter_upwards [ν.support_mem_ae] with x hx
    obtain ⟨y, hy⟩ := hs hx
    change L y = x at hy
    rw [← hy]
    have hleft : L.toContinuousLinearMap.adjoint (L y) = y := DFunLike.congr_fun L.adjoint_comp_self y
    simp only [id_eq, hleft]
  exact (Measure.map_congr heq).trans Measure.map_id

theorem planarPullbackMeasure_ball {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (x : Ambient n) (r : ℝ) : planarPullbackMeasure L ν (ball x r) = ν (ball (L x) r) := by
  rw [planarPullbackMeasure, Measure.map_apply L.toContinuousLinearMap.adjoint.continuous.measurable
    measurableSet_ball]
  apply measure_congr
  filter_upwards [ν.support_mem_ae] with y hy
  obtain ⟨z, hz⟩ := hs hy
  change L z = y at hz
  rw [← hz]
  have hleft : L.toContinuousLinearMap.adjoint (L z) = z := DFunLike.congr_fun L.adjoint_comp_self z
  apply propext
  change dist (L.toContinuousLinearMap.adjoint (L z)) x < r ↔ dist (L z) (L x) < r
  rw [hleft, L.dist_map]

theorem planarPullbackMeasure_growth {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C : ℝ) (hg : GlobalUpperGrowth n C ν) : GlobalUpperGrowth n C (planarPullbackMeasure L ν) := by
  refine ⟨hg.1, ?_⟩
  intro x r hr
  rw [planarPullbackMeasure_ball L ν hs]
  exact hg.2 (L x) r hr

theorem globalGrowth_finite_on_compacts {n d : ℕ} (C : ℝ)
    (ν : Measure (Ambient d)) (hg : GlobalUpperGrowth n C ν) : IsFiniteMeasureOnCompacts ν := by
  let : IsLocallyFiniteMeasure ν := ⟨fun x => ⟨ball x 1, ball_mem_nhds x zero_lt_one,
    (hg.2 x 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top⟩⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem planarPullbackMeasure_support_iff {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (x : Ambient n) : x ∈ (planarPullbackMeasure L ν).support ↔ L x ∈ ν.support := by
  rw [Metric.nhds_basis_ball.mem_measureSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [planarPullbackMeasure_ball L ν hs]

theorem planarPullbackMeasure_lower {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C : ℝ) (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r)) :
    ∀ x ∈ (planarPullbackMeasure L ν).support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ planarPullbackMeasure L ν (ball x r) := by
  intro x hx r hr
  rw [planarPullbackMeasure_ball L ν hs]
  exact hlower (L x) ((planarPullbackMeasure_support_iff L ν hs x).mp hx) r hr

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_GrowthVolumeDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Volume domination from intrinsic upper growth

An upper growth bound in the intrinsic Euclidean dimension implies domination
by Lebesgue measure. The density bound is normalized by the unit-ball volume
and includes the dimensional factor needed for closed-ball comparison.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem intrinsic_growth_le_volume (n : ℕ) (C : ℝ) (μ : Measure (Ambient n))
    (hg : GlobalUpperGrowth n C μ) :
    μ ≤ intrinsicGrowthDensityBound n C • (volume : Measure (Ambient n)) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts C μ hg
  let V : ℝ := (volume : Measure (Ambient n)).real (ball 0 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : Ambient n) zero_lt_one)) measure_ball_lt_top.ne
  have hD : (intrinsicGrowthDensityBound n C : ℝ) = C * 2 ^ n / V := by
    exact Real.coe_toNNReal _ (div_nonneg (mul_nonneg hg.1 (by positivity)) hV.le)
  have hDV : (intrinsicGrowthDensityBound n C : ℝ) * V = C * 2 ^ n := by
    rw [hD]
    exact div_mul_cancel₀ _ hV.ne'
  apply measure_le_of_closedBall_le
  intro x r hr
  have hvol : (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n * V := by
    simpa only [Ambient, finrank_euclideanSpace, Fintype.card_fin] using!
      (Measure.addHaar_real_closedBall (volume : Measure (Ambient n)) x hr.le)
  have hid : (intrinsicGrowthDensityBound n C : ℝ) *
      (volume : Measure (Ambient n)).real (closedBall x r) = C * (2 * r) ^ n := by
    rw [hvol]
    calc
      _ = ((intrinsicGrowthDensityBound n C : ℝ) * V) * r ^ n := by ring
      _ = _ := by rw [hDV, mul_pow, mul_assoc]
  calc
    μ (closedBall x r) ≤ μ (ball x (2 * r)) :=
      measure_mono (closedBall_subset_ball (by linarith))
    _ ≤ ENNReal.ofReal (C * (2 * r) ^ n) := hg.2 x (2 * r) (by positivity)
    _ = ENNReal.ofReal ((intrinsicGrowthDensityBound n C : ℝ) *
        (volume : Measure (Ambient n)).real (closedBall x r)) := congrArg ENNReal.ofReal hid.symm
    _ = (intrinsicGrowthDensityBound n C • (volume : Measure (Ambient n)))
        (closedBall x r) := by
      rw [ENNReal.ofReal_mul (intrinsicGrowthDensityBound n C).coe_nonneg,
        ENNReal.ofReal_coe_nnreal, Measure.real,
        ENNReal.ofReal_toReal (measure_closedBall_lt_top.ne), Measure.coe_nnreal_smul_apply]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BoundedPlanarDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded densities for measures supported on planes

Domination by a scalar multiple of a reference measure bounds the
Radon–Nikodym derivative and gives a measurable, everywhere bounded density.
Intrinsic upper growth applies this construction to Euclidean volume and to
measures supported on the range of a linear isometry.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem rnDeriv_le_of_nnreal_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite ν] (c : ℝ≥0) (hdom : μ ≤ c • ν) :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ (c : ℝ≥0∞) := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
  intro s _hs _hfin
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.coe_nnreal_smul_apply] using!
    (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ν) s).trans (hdom s)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_TwoSidedIntrinsicDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two-sided intrinsic densities

Lower ball-growth bounds give a positive multiple of Euclidean volume dominated
by the measure. Together with the upper-growth domination, this produces a
measurable density with pointwise lower and upper bounds by clipping its
Radon–Nikodym derivative without changing the represented measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem intrinsic_volume_le_of_lower_growth (n : ℕ) (C G : ℝ)
    (μ : Measure (Ambient n)) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x : Ambient n, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) :
    intrinsicLowerDensityBound n C • (volume : Measure (Ambient n)) ≤ μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  let V : ℝ := (volume : Measure (Ambient n)).real (ball 0 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : Ambient n) zero_lt_one)) measure_ball_lt_top.ne
  have hc : (intrinsicLowerDensityBound n C : ℝ) = (C * V)⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.mpr (mul_nonneg hC.le hV.le))
  apply measure_le_of_closedBall_le
  intro x r hr
  have hvol : (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n * V := by
    simpa only [Ambient, finrank_euclideanSpace, Fintype.card_fin] using!
      (Measure.addHaar_real_closedBall (volume : Measure (Ambient n)) x hr.le)
  have hid : (intrinsicLowerDensityBound n C : ℝ) *
      (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n / C := by
    rw [hc, hvol]
    field_simp [hV.ne', hC.ne']
  calc
    (intrinsicLowerDensityBound n C • (volume : Measure (Ambient n))) (closedBall x r) =
        ENNReal.ofReal ((intrinsicLowerDensityBound n C : ℝ) *
          (volume : Measure (Ambient n)).real (closedBall x r)) := by
      rw [ENNReal.ofReal_mul (intrinsicLowerDensityBound n C).coe_nonneg,
        ENNReal.ofReal_coe_nnreal, Measure.real,
        ENNReal.ofReal_toReal (measure_closedBall_lt_top.ne), Measure.coe_nnreal_smul_apply]
    _ = ENNReal.ofReal (r ^ n / C) := congrArg ENNReal.ofReal hid
    _ ≤ μ (ball x r) := hlower x r hr
    _ ≤ μ (closedBall x r) := measure_mono ball_subset_closedBall

theorem nnreal_le_rnDeriv_of_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (c : ℝ≥0) (hac : μ ≪ ν) (hdom : c • ν ≤ μ) :
    ∀ᵐ x ∂ν, (c : ℝ≥0∞) ≤ μ.rnDeriv ν x := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
  intro s hs _hfin
  rw [Measure.setLIntegral_rnDeriv' hac hs]
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.coe_nnreal_smul_apply] using! hdom s

theorem exists_two_sided_density_of_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hν : ν ≠ 0)
    (c D : ℝ≥0) (hlower : c • ν ≤ μ) (hupper : μ ≤ D • ν) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x, c ≤ f x ∧ f x ≤ D) ∧
      ν.withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
  have hac : μ ≪ ν := hupper.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have hlo := nnreal_le_rnDeriv_of_domination μ ν c hac hlower
  have hup := rnDeriv_le_of_nnreal_domination μ ν D hupper
  have : NeBot (ae ν) := ae_neBot.mpr hν
  have hcd : c ≤ D := by
    obtain ⟨x, hxlo, hxup⟩ := (hlo.and hup).exists
    exact ENNReal.coe_le_coe.mp (hxlo.trans hxup)
  let f : α → ℝ := fun x => min (D : ℝ) (max (c : ℝ) (μ.rnDeriv ν x).toReal)
  have hm : Measurable f := measurable_const.min
    (measurable_const.max (μ.measurable_rnDeriv ν).ennreal_toReal)
  have heq : (fun x => ENNReal.ofReal (f x)) =ᵐ[ν] μ.rnDeriv ν := by
    filter_upwards [hlo, hup] with x hxlo hxup
    have hne : μ.rnDeriv ν x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hxup
    have hreal_lo : (c : ℝ) ≤ (μ.rnDeriv ν x).toReal := by
      simpa only [ENNReal.coe_toReal] using!
        (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hne).mpr hxlo
    have hreal_up : (μ.rnDeriv ν x).toReal ≤ (D : ℝ) := by
      simpa only [ENNReal.coe_toReal] using!
        (ENNReal.toReal_le_toReal hne ENNReal.coe_ne_top).mpr hxup
    change ENNReal.ofReal (min (D : ℝ) (max (c : ℝ) (μ.rnDeriv ν x).toReal)) = _
    rw [max_eq_right hreal_lo, min_eq_right hreal_up, ENNReal.ofReal_toReal hne]
  refine ⟨f, hm, ?_, ?_⟩
  · intro x
    exact ⟨le_min (NNReal.coe_le_coe.mpr hcd) (le_max_left _ _), min_le_left _ _⟩
  · rw [withDensity_congr_ae heq]
    exact Measure.withDensity_rnDeriv_eq μ ν hac

theorem exists_two_sided_intrinsic_density (n : ℕ) (C G : ℝ)
    (μ : Measure (Ambient n)) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x : Ambient n, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) :
    ∃ f : Ambient n → ℝ, Measurable f ∧
      (∀ x, intrinsicLowerDensityBound n C ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound n G) ∧
      (volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact exists_two_sided_density_of_domination μ volume (by exact NeZero.ne volume)
    (intrinsicLowerDensityBound n C) (intrinsicGrowthDensityBound n G)
    (intrinsic_volume_le_of_lower_growth n C G μ hC hg hlower)
    (intrinsic_growth_le_volume n G μ hg)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EnergyIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem centered_coordinate_difference (u v c : ℝ) :
    (u - c) - (v - c) = u - v := by
  ring

theorem normal_coordinate_difference {d : ℕ} (e z x y : Ambient d) :
    inner ℝ e (x - z) - inner ℝ e (y - z) = inner ℝ e (x - y) := by
  simp only [inner_sub_right]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem meanCorrection_integrable (μ : Measure X) (φ η : X → ℝ)
    (hφ : Integrable φ μ) (hη : Integrable η μ) :
    Integrable (meanCorrection μ φ η) μ :=
  hφ.sub (hη.const_mul _)

theorem meanCorrection_integral_zero (μ : Measure X) (φ η : X → ℝ)
    (hφ : Integrable φ μ) (hη : Integrable η μ) (hne : (∫ x, η x ∂μ) ≠ 0) :
    (∫ x, meanCorrection μ φ η x ∂μ) = 0 := by
  change (∫ x, φ x - ((∫ y, φ y ∂μ) / (∫ y, η y ∂μ)) * η x ∂μ) = 0
  rw [integral_sub hφ (hη.const_mul _), integral_const_mul,
    div_mul_cancel₀ _ hne, sub_self]

theorem meanCorrection_coefficient_tendsto_zero
    (μ : ℕ → Measure X) (φ η : X → ℝ) (b : ℝ) (hb : b ≠ 0)
    (hφ : Tendsto (fun j => ∫ x, φ x ∂μ j) atTop (𝓝 0))
    (hη : Tendsto (fun j => ∫ x, η x ∂μ j) atTop (𝓝 b)) :
    Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0) := by
  simpa only [zero_div] using! hφ.div hη hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

variable [MetricSpace X]

omit [MeasurableSpace X] in
theorem fractionalPairEnergy_nonneg (m : ℕ) (w : X → ℝ) (x y : X) :
    0 ≤ fractionalPairEnergy m w x y := by
  unfold fractionalPairEnergy
  positivity

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BallLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localization to balls

Restricting a measure preserves its global upper growth bound and gives finite mass on
positive-radius balls. The diameter estimate controls pairs of points in a ball, while
the Lipschitz height estimate supplies the boundedness needed for local `MemLp` control.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem globalGrowth_restrict {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (s : Set (Ambient d)) :
    GlobalUpperGrowth m C (μ.restrict s) := by
  refine ⟨hg.1, fun a R hR => ?_⟩
  exact (Measure.restrict_le_self (s := s) (μ := μ) (ball a R)).trans (hg.2 a R hR)

theorem finiteMeasure_restrict_ball_of_globalGrowth {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) : IsFiniteMeasure (μ.restrict (ball a R)) := by
  constructor
  simpa only [Measure.restrict_apply_univ] using! (hg.2 a R hR).trans_lt ENNReal.ofReal_lt_top

theorem ball_restriction_mass_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    (μ.restrict (ball a R)).real univ ≤ C * R ^ m := by
  simpa only [Measure.real, Measure.restrict_apply_univ] using!
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity)) (hg.2 a R hR)

theorem ball_restriction_pair_diameter {d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d) (R : ℝ)
    [SFinite (μ.restrict (ball a R))] :
    ∀ᵐ q ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R)), dist q.1 q.2 ≤ 2 * R := by
  have hs : ∀ᵐ x ∂μ.restrict (ball a R), x ∈ ball a R := ae_restrict_mem measurableSet_ball
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
    Measure.quasiMeasurePreserving_snd.ae hs] with q hx hy
  change dist q.1 a < R at hx
  change dist q.2 a < R at hy
  have ht := dist_triangle q.1 a q.2
  rw [dist_comm a q.2] at ht
  linarith

theorem lipschitz_height_bound_on_ball {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a x : Ambient d) (R : ℝ) (hx : x ∈ ball a R) :
    |w x| ≤ |w a| + (K : ℝ) * R := by
  have hdiff : |w x - w a| ≤ (K : ℝ) * dist x a := by
    simpa only [Real.dist_eq] using! hw.dist_le_mul x a
  have habs : |w x| ≤ |w x - w a| + |w a| := by
    simpa only [sub_zero] using! abs_sub_le (w x) (w a) 0
  have hprod := mul_le_mul_of_nonneg_left hx.le K.coe_nonneg
  linarith

theorem lipschitz_height_memLp_on_ball {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    MemLp w 2 (μ.restrict (ball a R)) := by
  have := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  apply MemLp.of_bound hw.continuous.measurable.aestronglyMeasurable (|w a| + (K : ℝ) * R)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  simpa only [Real.norm_eq_abs] using! lipschitz_height_bound_on_ball w K hw a x R hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NearPairWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem nearPairSet_measurable {d : ℕ} (r : ℝ) :
    MeasurableSet (nearPairSet (d := d) r) :=
  measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const

theorem nearPairWeight_measurable {d : ℕ} (p : ℕ) (r : ℝ) :
    Measurable (nearPairWeight (d := d) p r) := by
  apply Measurable.indicator _ (nearPairSet_measurable r)
  unfold inverseDistancePow
  fun_prop

theorem nearPairWeight_nonneg {d : ℕ} (p : ℕ) (r : ℝ) (q : Ambient d × Ambient d) :
    0 ≤ nearPairWeight p r q :=
  indicator_nonneg (fun _ _ => inverseDistancePow_nonneg p _ _) q

theorem nearPairWeight_section {d : ℕ} (p : ℕ) (r : ℝ) (x : Ambient d) :
    (fun y => nearPairWeight p r (x, y)) =
      (closedBall x r).indicator (inverseDistancePow p x) := by
  funext y
  classical
  by_cases h : y ∈ closedBall x r
  · simp only [nearPairWeight, indicator_of_mem (show (x, y) ∈ nearPairSet r from h),
      indicator_of_mem h]
  · simp only [nearPairWeight, indicator_of_notMem (show (x, y) ∉ nearPairSet r from h),
      indicator_of_notMem h]

theorem nearPairWeight_section_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    Integrable (fun y => nearPairWeight p r (x, y)) μ := by
  rw [nearPairWeight_section]
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (inverseDistancePow_near_integrable_and_bound p C μ hg x r hr).1

theorem nearPairWeight_section_norm_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    (∫ y, ‖nearPairWeight p r (x, y)‖ ∂μ) ≤ 2 * (C * 2 ^ (p + 1) * 2 ^ p * r) := by
  simp_rw [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)]
  rw [nearPairWeight_section, integral_indicator measurableSet_closedBall]
  exact inverseDistancePow_near_integral_bound p C μ hg x r hr

theorem nearPairWeight_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) : Integrable (nearPairWeight p r) (μ.prod μ) := by
  have hmeas : AEStronglyMeasurable (nearPairWeight p r) (μ.prod μ) :=
    (nearPairWeight_measurable p r).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨Filter.Eventually.of_forall (nearPairWeight_section_integrable p C μ hg r hr), ?_⟩
  apply Integrable.of_bound hmeas.norm.integral_prod_right' (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact nearPairWeight_section_norm_bound p C μ hg r hr x

theorem nearPairWeight_integral_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) :
    (∫ q, nearPairWeight p r q ∂μ.prod μ) ≤
      μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) := by
  have hi := nearPairWeight_integrable p C μ hg r hr
  rw [integral_prod _ hi]
  have h := integral_mono hi.integral_prod_left
    (integrable_const (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))) (fun x => by
      simpa only [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)] using!
        nearPairWeight_section_norm_bound p C μ hg r hr x)
  simpa only [integral_const, smul_eq_mul] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function
open scoped NNReal

variable {d : ℕ}

theorem weightedDifference_measurable (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w) :
    Measurable (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) := by
  unfold weightedDifference
  fun_prop

theorem weightedDifference_sq (m : ℕ) (w : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y ^ 2 = fractionalPairEnergy m w x y := by
  rw [weightedDifference, div_pow, Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem weightedDifference_mul (m : ℕ) (w ψ : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y * weightedDifference m ψ x y = fractionalBilinear m w ψ x y := by
  rw [weightedDifference, weightedDifference, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem weightedDifference_memLp (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w)
    (ρ : Measure (Ambient d × Ambient d))
    (hE : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m w q.1 q.2) ρ) :
    MemLp (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) 2 ρ := by
  apply (memLp_two_iff_integrable_sq (weightedDifference_measurable m w hw).aestronglyMeasurable).mpr
  simpa only [weightedDifference_sq] using! hE

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarKernelDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem inverseDistancePow_far_difference {d : ℕ} (m : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a * inverseDistancePow (m + 2) a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  have h := inverse_pow_difference_le m (dist x y) (dist a y) (dist a y / 2)
    (by positivity) hhalf (by linarith)
  have hdist := abs_dist_sub_le x a y
  unfold inverseDistancePow
  calc
    _ ≤ (m + 1 : ℝ) * |dist x y - dist a y| * ((dist a y / 2) ^ (m + 2))⁻¹ := h
    _ ≤ (m + 1 : ℝ) * dist x a * ((dist a y / 2) ^ (m + 2))⁻¹ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (by positivity))
        (by positivity)
    _ = _ := by
      rw [div_pow, inv_div]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LipschitzTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

variable [MeasurableSpace X]

theorem meanCorrection_lipschitz (μ : Measure X) {φ η : X → ℝ}
    {Kφ Kη : ℝ≥0} (hφ : LipschitzWith Kφ φ) (hη : LipschitzWith Kη η) :
    LipschitzWith (Kφ + ‖(∫ y, φ y ∂μ) / (∫ y, η y ∂μ)‖₊ * Kη)
      (meanCorrection μ φ η) :=
  hφ.sub (lipschitz_const_mul_real hη _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedBilinearKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Function
open scoped NNReal

theorem cappedInverseDistancePow_eq {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) (h : ε ≤ dist q.1 q.2) :
    cappedInverseDistancePow m ε q = (dist q.1 q.2 ^ m)⁻¹ := by
  simp only [cappedInverseDistancePow, max_eq_right h]

theorem capped_bilinear_eq_outside {d : ℕ} (m : ℕ) (ε : ℝ) (w φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) (h : ε ≤ dist q.1 q.2) :
    (w q.1 - w q.2) * cappedTestKernel m ε φ q = fractionalBilinear m w φ q.1 q.2 := by
  unfold cappedTestKernel fractionalBilinear
  rw [cappedInverseDistancePow_eq _ _ _ h]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalLipschitzEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local Lipschitz control of fractional energy

Almost-everywhere Lipschitz difference bounds and bounded pair distances give
integrability of fractional pair energies under global upper growth. Their weighted
differences lie in L², yielding integrability of the associated bilinear pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem fractionalEnergy_bound_of_difference_bound {d : ℕ} (p : ℕ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (x y : Ambient d)
    (h : |w x - w y| ≤ (K : ℝ) * dist x y) :
    fractionalPairEnergy (p + 1) w x y ≤ (K : ℝ) ^ 2 * inverseDistancePow p x y := by
  by_cases hxy : x = y
  · subst y
    simp only [fractionalPairEnergy, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    exact mul_nonneg (sq_nonneg _) (inverseDistancePow_nonneg _ _ _)
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hsq : (w x - w y) ^ 2 ≤ (K : ℝ) ^ 2 * dist x y ^ 2 := by
      simpa only [sq_abs, mul_pow] using!
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg K.coe_nonneg dist_nonneg)).mpr h
    calc
      _ ≤ ((K : ℝ) ^ 2 * dist x y ^ 2) / dist x y ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hsq (pow_nonneg dist_nonneg _)
      _ = _ := by
        rw [show p + 1 + 1 = p + 2 by omega, pow_add]
        unfold inverseDistancePow
        field_simp

theorem fractionalEnergy_integrable_of_ae_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w : Ambient d → ℝ) (hw : Measurable w) (K : ℝ≥0)
    (hK : ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2)
      (μ.prod μ) := by
  have hm : Measurable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) w q.1 q.2) := by
    unfold fractionalPairEnergy
    fun_prop
  apply ((nearPairWeight_integrable p C μ hg r hr).const_mul ((K : ℝ) ^ 2)).mono'
    hm.aestronglyMeasurable
  filter_upwards [hK, hdiam] with q hq hd
  have hmem : q ∈ nearPairSet r := by
    simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm] using! hd
  rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _), nearPairWeight,
    indicator_of_mem hmem]
  exact fractionalEnergy_bound_of_difference_bound p w K q.1 q.2 hq

theorem fractionalBilinear_integrable_of_ae_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w ψ : Ambient d → ℝ) (hw : Measurable w) (hψ : Measurable ψ) (K L : ℝ≥0)
    (hK : ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2)
    (hL : ∀ᵐ q ∂μ.prod μ, |ψ q.1 - ψ q.2| ≤ (L : ℝ) * dist q.1 q.2)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w ψ q.1 q.2)
      (μ.prod μ) := by
  have hf := weightedDifference_memLp (p + 1) w hw (μ.prod μ)
    (fractionalEnergy_integrable_of_ae_lipschitz p C μ hg w hw K hK r hr hdiam)
  have hgtest := weightedDifference_memLp (p + 1) ψ hψ (μ.prod μ)
    (fractionalEnergy_integrable_of_ae_lipschitz p C μ hg ψ hψ L hL r hr hdiam)
  have hprod : MemLp (fun q : Ambient d × Ambient d =>
      weightedDifference (p + 1) w q.1 q.2 * weightedDifference (p + 1) ψ q.1 q.2)
      1 (μ.prod μ) := MemLp.mul' (hφ := hf) (hf := hgtest)
  simpa only [weightedDifference_mul] using! memLp_one_iff_integrable.mp hprod

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem lipschitz_height_radial_bound {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a y : Ambient d) (R : ℝ)
    (hR : 0 < R) (hy : R ≤ dist a y) :
    |w y| ≤ ((K : ℝ) + |w a| / R) * dist a y := by
  have hdiff : |w y - w a| ≤ (K : ℝ) * dist a y := by
    simpa only [Real.dist_eq, dist_comm y a] using! hw.dist_le_mul y a
  have hconstant : |w a| ≤ (|w a| / R) * dist a y := by
    have h := mul_le_mul_of_nonneg_left hy (div_nonneg (abs_nonneg (w a)) hR.le)
    simpa only [div_mul_cancel₀ _ hR.ne'] using! h
  calc
    _ ≤ |w y - w a| + |w a| := by
      simpa only [sub_add_cancel] using! abs_add_le (w y - w a) (w a)
    _ ≤ (K : ℝ) * dist a y + (|w a| / R) * dist a y := add_le_add hdiff hconstant
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ClosedTailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem closedExterior_measurable {d : ℕ} (a : Ambient d) (R : ℝ) :
    MeasurableSet (closedExterior a R) :=
  measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HeightTailSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Annular integrability for height-tail estimates

Lipschitz height functions are bounded on each dyadic annulus. The finite
annular mass supplied by upper growth then gives the square integrability
needed to apply shell estimates in the height-tail decomposition.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem weighted_height_closed_tail_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        ((K : ℝ) + |w a| / R) * (2 * (C * 2 ^ m / R)) := by
  obtain ⟨hweight, hbound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hm : Measurable (fun y => |w y| * inverseDistancePow (m + 2) a y) :=
    hw.continuous.measurable.abs.mul (inverseDistancePow_measurable _ _)
  have hpoint (y : Ambient d) (hy : y ∈ closedExterior a R) :
      |w y| * inverseDistancePow (m + 2) a y ≤
        ((K : ℝ) + |w a| / R) * inverseDistancePow (m + 1) a y := by
    have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
    calc
      _ ≤ (((K : ℝ) + |w a| / R) * dist a y) * inverseDistancePow (m + 2) a y :=
        mul_le_mul_of_nonneg_right (lipschitz_height_radial_bound w K hw a y R hR hy)
          (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        unfold inverseDistancePow
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        field_simp
  have hi : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ := by
    apply (hweight.const_mul ((K : ℝ) + |w a| / R)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _))]
    exact hpoint y hy
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in closedExterior a R,
        ((K : ℝ) + |w a| / R) * inverseDistancePow (m + 1) a y ∂μ := by
      apply integral_mono_ae hi (hweight.const_mul _)
      filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
      exact hpoint y hy
    _ = ((K : ℝ) + |w a| / R) * (∫ y in closedExterior a R, inverseDistancePow (m + 1) a y ∂μ) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RenormalizedFarPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem inverseDistancePow_far_le {d : ℕ} (p : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    inverseDistancePow p x y ≤ 2 ^ p * inverseDistancePow p a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  calc
    _ ≤ ((dist a y / 2) ^ p)⁻¹ := by
      simpa only [inverseDistancePow, one_div] using!
        one_div_le_one_div_of_le (pow_pos (by positivity : 0 < dist a y / 2) p)
          (pow_le_pow_left₀ (by positivity) hhalf p)
    _ = _ := by unfold inverseDistancePow; rw [div_pow, inv_div]; ring

theorem renormalizedNormalIntegrand_bound {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (a x y : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hx : dist x a ≤ H) (hy : R ≤ dist a y) :
    |renormalizedNormalIntegrand m w φ a (x, y)| ≤
      2 ^ (m + 1) * (|φ x * w x| * inverseDistancePow (m + 1) a y) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ x| * (|w y| * inverseDistancePow (m + 2) a y)) := by
  have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
  have hfar : 2 * dist x a ≤ dist a y := (by linarith : 2 * dist x a ≤ R).trans hy
  have hk := inverseDistancePow_far_le (m + 1) a x y hpos hfar
  have hdiff : |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * H * inverseDistancePow (m + 2) a y := by
    apply (inverseDistancePow_far_difference m a x y hpos hfar).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity))
      (inverseDistancePow_nonneg _ _ _)
  unfold renormalizedNormalIntegrand
  rw [abs_mul]
  calc
    _ ≤ |φ x| * (|w x| * inverseDistancePow (m + 1) x y +
        |w y| * |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y|) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (inverseDistancePow_nonneg _ _ _)] using!
        abs_sub_le (w x * inverseDistancePow (m + 1) x y) 0
          (w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))
    _ ≤ |φ x| * (|w x| * (2 ^ (m + 1) * inverseDistancePow (m + 1) a y) +
        |w y| * ((m + 1 : ℝ) * 2 ^ (m + 2) * H * inverseDistancePow (m + 2) a y)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))) (abs_nonneg _)
    _ = _ := by rw [abs_mul]; ring

theorem renormalizedNormalIntegrand_bound_of_support {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (a x y : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hx : φ x ≠ 0 → dist x a ≤ H) (hy : R ≤ dist a y) :
    |renormalizedNormalIntegrand m w φ a (x, y)| ≤
      2 ^ (m + 1) * (|φ x * w x| * inverseDistancePow (m + 1) a y) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ x| * (|w y| * inverseDistancePow (m + 2) a y)) := by
  by_cases hφ : φ x = 0
  · simp only [renormalizedNormalIntegrand, hφ, zero_mul, abs_zero, mul_zero, add_zero, le_refl]
  · exact renormalizedNormalIntegrand_bound m w φ a x y H R hR hHR (hx hφ) hy

theorem renormalized_far_pairing_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth m C μ) (w φ : Ambient d → ℝ)
    (hw : Measurable w) (hφm : Measurable φ) (hφ : Integrable φ ν)
    (hφw : Integrable (fun x => φ x * w x) ν)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ)
    (Z : ℝ) (hZ : (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤ Z) :
    Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod (μ.restrict (closedExterior a R))) ∧
      (∫ q, |renormalizedNormalIntegrand m w φ a q| ∂ν.prod (μ.restrict (closedExterior a R))) ≤
        2 ^ (m + 1) * ((∫ x, |φ x * w x| ∂ν) * (2 * (C * 2 ^ m / R))) +
          ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * ((∫ x, |φ x| ∂ν) * Z) := by
  let η := μ.restrict (closedExterior a R)
  obtain ⟨hkernel, hkernelBound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hdom₁ := (hφw.abs.mul_prod hkernel).const_mul ((2 : ℝ) ^ (m + 1))
  have hdom₂ := (hφ.abs.mul_prod hweighted).const_mul ((m + 1 : ℝ) * 2 ^ (m + 2) * H)
  have hm : Measurable (renormalizedNormalIntegrand m w φ a) := by
    unfold renormalizedNormalIntegrand inverseDistancePow
    fun_prop
  have hpoint : ∀ᵐ q ∂ν.prod η, |renormalizedNormalIntegrand m w φ a q| ≤
      2 ^ (m + 1) * (|φ q.1 * w q.1| * inverseDistancePow (m + 1) a q.2) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ q.1| * (|w q.2| * inverseDistancePow (m + 2) a q.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnear,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (closedExterior_measurable a R))] with q hx hy
    exact renormalizedNormalIntegrand_bound_of_support m w φ a q.1 q.2 H R hR hHR hx hy
  have hi : Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod η) := by
    apply (hdom₁.add hdom₂).mono' hm.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using! hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ q, 2 ^ (m + 1) * (|φ q.1 * w q.1| * inverseDistancePow (m + 1) a q.2) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ q.1| * (|w q.2| * inverseDistancePow (m + 2) a q.2)) ∂ν.prod η :=
      integral_mono_ae hi.abs (hdom₁.add hdom₂) hpoint
    _ = 2 ^ (m + 1) * ((∫ x, |φ x * w x| ∂ν) * (∫ y, inverseDistancePow (m + 1) a y ∂η)) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          ((∫ x, |φ x| ∂ν) * (∫ y, |w y| * inverseDistancePow (m + 2) a y ∂η)) := by
      rw [integral_add hdom₁ hdom₂]
      simp only [integral_const_mul]
      rw [integral_prod_mul (fun x => |φ x * w x|) (inverseDistancePow (m + 1) a),
        integral_prod_mul (fun x => |φ x|) (fun y => |w y| * inverseDistancePow (m + 2) a y)]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hkernelBound (integral_nonneg fun _ => abs_nonneg _)) (by positivity))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hZ (integral_nonneg fun _ => abs_nonneg _)) (by positivity))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszPairingIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar Riesz pairings and affine normal heights

Pairing the Riesz kernel with a fixed normal identifies its interior contribution
with the fractional bilinear form. For mean-zero tests, the exterior correction
integrates to zero, identifying the scalar Riesz pairing with the normal cutoff pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem affineNormalHeight_difference {d : ℕ} (e z : Ambient d) (b : ℝ) (x y : Ambient d) :
    affineNormalHeight e z b x - affineNormalHeight e z b y = inner ℝ e (x - y) := by
  rw [affineNormalHeight, affineNormalHeight, centered_coordinate_difference]
  exact normal_coordinate_difference e z x y

theorem affineNormalHeight_lipschitz {d : ℕ} (e z : Ambient d) (b : ℝ) :
    LipschitzWith ‖e‖₊ (affineNormalHeight e z b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, affineNormalHeight_difference]
  simpa only [Real.norm_eq_abs, coe_nnnorm, dist_eq_norm] using!
    norm_inner_le_norm (𝕜 := ℝ) e (x - y)

theorem kernel_inner_normal_difference {d : ℕ} (m : ℕ) (e : Ambient d)
    (w : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y)) (x y : Ambient d) :
    inner ℝ e (kernel m x y) = (w x - w y) * inverseDistancePow (m + 1) x y := by
  rw [kernel, real_inner_smul_right, ← hw x y, ← dist_eq_norm]
  unfold inverseDistancePow
  ring

theorem rieszInteriorIntegrand_eq_fractionalBilinear {d : ℕ} (m : ℕ) (e : Ambient d)
    (w φ : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e φ q = fractionalBilinear m w φ q.1 q.2 := by
  rw [rieszInteriorIntegrand, kernel_inner_normal_difference m e w hw]
  unfold inverseDistancePow fractionalBilinear
  ring

theorem rieszFarIntegrand_eq_normal_sub_correction {d : ℕ} (m : ℕ) (e : Ambient d)
    (w φ : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (q : Ambient d × Ambient d) :
    rieszFarIntegrand m e φ a q = renormalizedNormalIntegrand m w φ a q -
      (φ q.1 * w a) * inverseDistancePow (m + 1) a q.2 := by
  rw [rieszFarIntegrand, inner_sub_right, kernel_inner_normal_difference m e w hw,
    kernel_inner_normal_difference m e w hw]
  unfold renormalizedNormalIntegrand
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-measure truncated Riesz pairings

The scalar truncated kernel is measurable and bounded away from its singularity.
Symmetrization expresses finite-measure pairings as interior double integrals,
whose integrability yields convergence as the truncation scale tends to zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszInteriorIntegrand_integrable_of_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r) :
    Integrable (rieszInteriorIntegrand (p + 1) e φ) (ν.prod ν) := by
  let w := affineNormalHeight e 0 0
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e 0 0
  have hI := fractionalBilinear_integrable_of_ae_lipschitz p C ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable ‖e‖₊ L
    (Filter.Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hw.dist_le_mul q.1 q.2)
    (Filter.Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hφ.dist_le_mul q.1 q.2)
    r hr hdiam
  have heq : rieszInteriorIntegrand (p + 1) e φ =
      fun q => fractionalBilinear (p + 1) w φ q.1 q.2 := by
    funext q
    exact rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e w φ
      (affineNormalHeight_difference e 0 0) q
  rw [heq]
  exact hI

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedBilinearError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem capped_bilinear_error_pointwise {d : ℕ} (m : ℕ) (ε : ℝ)
    (w φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    |fractionalBilinear m w φ q.1 q.2 - (w q.1 - w q.2) * cappedTestKernel m ε φ q| ≤
      (nearPairSet ε).indicator (fun q => |fractionalBilinear m w φ q.1 q.2|) q := by
  classical
  by_cases hnear : q ∈ nearPairSet ε
  · rw [indicator_of_mem hnear]
    by_cases hdiag : q.1 = q.2
    · simp only [hdiag, fractionalBilinear, cappedTestKernel, sub_self, zero_mul, zero_div,
        abs_zero, le_refl]
    · have hd : 0 < dist q.1 q.2 := dist_pos.mpr hdiag
      have hcap : cappedInverseDistancePow (m + 1) ε q ≤ (dist q.1 q.2 ^ (m + 1))⁻¹ := by
        exact inv_anti₀ (pow_pos hd _) (pow_le_pow_left₀ hd.le (le_max_right _ _) _)
      have hdiff : 0 ≤ (dist q.1 q.2 ^ (m + 1))⁻¹ - cappedInverseDistancePow (m + 1) ε q :=
        sub_nonneg.mpr hcap
      have heq : fractionalBilinear m w φ q.1 q.2 - (w q.1 - w q.2) * cappedTestKernel m ε φ q =
          ((w q.1 - w q.2) * (φ q.1 - φ q.2)) *
            ((dist q.1 q.2 ^ (m + 1))⁻¹ - cappedInverseDistancePow (m + 1) ε q) := by
        unfold fractionalBilinear cappedTestKernel
        ring
      rw [heq, abs_mul, abs_of_nonneg hdiff]
      calc
        _ ≤ |(w q.1 - w q.2) * (φ q.1 - φ q.2)| * (dist q.1 q.2 ^ (m + 1))⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (sub_le_self _ (cappedInverseDistancePow_nonneg (m + 1) ε q)) (abs_nonneg _)
        _ = _ := by
          simp only [fractionalBilinear, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hd _))]
  · rw [indicator_of_notMem hnear]
    have hd : ε ≤ dist q.1 q.2 := by
      have hn : ¬dist q.2 q.1 ≤ ε := hnear
      simpa only [dist_comm q.2 q.1] using! (lt_of_not_ge hn).le
    rw [capped_bilinear_eq_outside m ε w φ q hd, sub_self, abs_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SymmetricPairingSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem integral_symmetric_pair_split {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (s : Set X) (hs : MeasurableSet s)
    (F : X × X → ℝ) (hF : Integrable F (ν.prod ν))
    (hsym : ∀ q, F q.swap = F q)
    (hzero : ∀ x ∉ s, ∀ y ∉ s, F (x, y) = 0) :
    (∫ q, F q ∂ν.prod ν) =
      (∫ q, F q ∂(ν.restrict s).prod (ν.restrict s)) +
        2 * (∫ q, F q ∂(ν.restrict s).prod (ν.restrict sᶜ)) := by
  have hss : Integrable F ((ν.restrict s).prod (ν.restrict s)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hsc : Integrable F ((ν.restrict s).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hcs : Integrable F ((ν.restrict sᶜ).prod (ν.restrict s)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hcc : Integrable F ((ν.restrict sᶜ).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hmeasure : ν.prod ν =
      ((ν.restrict s).prod (ν.restrict s) + (ν.restrict s).prod (ν.restrict sᶜ)) +
      ((ν.restrict sᶜ).prod (ν.restrict s) + (ν.restrict sᶜ).prod (ν.restrict sᶜ)) := by
    calc
      ν.prod ν = (ν.restrict s + ν.restrict sᶜ).prod (ν.restrict s + ν.restrict sᶜ) := by
        rw [Measure.restrict_add_restrict_compl hs]
      _ = _ := by rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  have hswap : (∫ q, F q ∂(ν.restrict sᶜ).prod (ν.restrict s)) =
      ∫ q, F q ∂(ν.restrict s).prod (ν.restrict sᶜ) := by
    simpa only [hsym] using! integral_prod_swap (μ := ν.restrict s) (ν := ν.restrict sᶜ) F
  have hcc0 : (∫ q, F q ∂(ν.restrict sᶜ).prod (ν.restrict sᶜ)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hs.compl),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs.compl)] with q hx hy
    exact hzero q.1 hx q.2 hy
  rw [hmeasure, integral_add_measure (hss.add_measure hsc) (hcs.add_measure hcc),
    integral_add_measure hss hsc, integral_add_measure hcs hcc, hswap, hcc0]
  ring

theorem rieszInteriorIntegrand_swap {d : ℕ} (m : ℕ) (e : Ambient d)
    (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e φ q.swap = rieszInteriorIntegrand m e φ q := by
  unfold rieszInteriorIntegrand
  dsimp only [Prod.swap]
  rw [kernel_antisymm, inner_neg_right]
  ring

theorem riesz_pairing_split {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [SFinite ν] (s : Set (Ambient d)) (hs : MeasurableSet s)
    (φ : Ambient d → ℝ) (hφzero : ∀ x ∉ s, φ x = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    Integrable (rieszRawCrossIntegrand m e φ) ((ν.restrict s).prod (ν.restrict sᶜ)) ∧
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
        (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂(ν.restrict s).prod (ν.restrict s)) +
          ∫ q, rieszRawCrossIntegrand m e φ q ∂(ν.restrict s).prod (ν.restrict sᶜ) := by
  have hcross : Integrable (rieszInteriorIntegrand m e φ) ((ν.restrict s).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have heq : rieszInteriorIntegrand m e φ =ᵐ[(ν.restrict s).prod (ν.restrict sᶜ)]
      rieszRawCrossIntegrand m e φ := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs.compl)] with q hy
    unfold rieszInteriorIntegrand rieszRawCrossIntegrand
    rw [hφzero q.2 hy, sub_zero, mul_comm]
  have hsplit := integral_symmetric_pair_split ν s hs (rieszInteriorIntegrand m e φ) hF
    (rieszInteriorIntegrand_swap m e φ) (by
      intro x hx y hy
      simp only [rieszInteriorIntegrand, hφzero x hx, hφzero y hy, sub_self, mul_zero])
  rw [integral_congr_ae heq] at hsplit
  refine ⟨(integrable_congr heq).mp hcross, ?_⟩
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FinitePairingCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem closedExterior_eq_compl_ball {d : ℕ} (a : Ambient d) (R : ℝ) :
    closedExterior a R = (ball a R)ᶜ := by
  ext y
  change (R ≤ dist a y) ↔ ¬ dist y a < R
  rw [dist_comm y a, not_lt]

theorem center_kernel_integrable_finite_exterior {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (kernel m a) (closedExterior a R) ν := by
  apply Integrable.of_bound (kernel_measurable_right m a).aestronglyMeasurable ((R ^ m)⁻¹)
  filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
  exact kernel_norm_le_truncation m a y R hR hy

theorem riesz_far_integral_eq_raw_of_mean_zero {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν) (hzero : (∫ x, φ x ∂ν) = 0)
    (a : Ambient d) (hk : Integrable (fun y => inner ℝ e (kernel m a y)) η)
    (hraw : Integrable (rieszRawCrossIntegrand m e φ) (ν.prod η)) :
    Integrable (rieszFarIntegrand m e φ a) (ν.prod η) ∧
      (∫ q, rieszFarIntegrand m e φ a q ∂ν.prod η) =
        ∫ q, rieszRawCrossIntegrand m e φ q ∂ν.prod η := by
  have hcorrection := hφ.mul_prod hk
  have heq : rieszFarIntegrand m e φ a = fun q => rieszRawCrossIntegrand m e φ q -
      φ q.1 * inner ℝ e (kernel m a q.2) := by
    funext q
    unfold rieszFarIntegrand rieszRawCrossIntegrand
    rw [inner_sub_right]
    ring
  rw [heq]
  refine ⟨hraw.sub hcorrection, ?_⟩
  rw [integral_sub hraw hcorrection, integral_prod_mul φ (fun y => inner ℝ e (kernel m a y)),
    hzero, zero_mul, sub_zero]

theorem finite_pairing_eq_renormalized {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν) (hφzero : ∀ x ∉ ball a R, φ x = 0)
    (hzero : (∫ x in ball a R, φ x ∂ν) = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    Integrable (rieszFarIntegrand m e φ a)
      ((ν.restrict (ball a R)).prod (ν.restrict (closedExterior a R))) ∧
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
        rieszScalarPairing m ν a R e φ := by
  obtain ⟨hraw, hsplit⟩ := riesz_pairing_split m e ν (ball a R) measurableSet_ball φ hφzero hF
  rw [← closedExterior_eq_compl_ball a R] at hraw hsplit
  have hk := Integrable.const_inner (𝕜 := ℝ) e (center_kernel_integrable_finite_exterior m ν a R hR)
  obtain ⟨hfar, heq⟩ := riesz_far_integral_eq_raw_of_mean_zero m e
    (ν.restrict (ball a R)) (ν.restrict (closedExterior a R)) φ hφ.restrict hzero a hk hraw
  refine ⟨hfar, hsplit.trans ?_⟩
  unfold rieszScalarPairing
  dsimp only
  rw [heq]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OuterPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem outerPairRadius_ge (R : ℝ) (k : ℕ) : R ≤ outerPairRadius R k := by
  unfold outerPairRadius
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem integral_outer_pair_exhaustion {d : ℕ} (ρ : Measure (Ambient d × Ambient d))
    (a : Ambient d) (R : ℝ) (F : Ambient d × Ambient d → ℝ) (hF : Integrable F ρ) :
    Tendsto (fun k : ℕ => ∫ q in univ ×ˢ ball a (outerPairRadius R k), F q ∂ρ)
      atTop (𝓝 (∫ q, F q ∂ρ)) := by
  let s := fun k : ℕ => (univ : Set (Ambient d)) ×ˢ ball a (outerPairRadius R k)
  have hs (k : ℕ) : MeasurableSet (s k) := MeasurableSet.univ.prod measurableSet_ball
  have hmono : Monotone s := by
    intro k l hkl q hq
    refine ⟨hq.1, ?_⟩
    apply (ball_subset_ball ?_) hq.2
    unfold outerPairRadius
    have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hcover : (⋃ k, s k) = univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨k, hk⟩ := exists_nat_gt (dist q.2 a - R)
    apply mem_iUnion.mpr
    refine ⟨k, mem_univ _, ?_⟩
    change dist q.2 a < R + (k : ℝ) + 1
    linarith
  have ht := tendsto_setIntegral_of_monotone hs hmono hF.restrict
  simpa only [hcover, Measure.restrict_univ] using! ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported Lipschitz Riesz pairings

Growth bounds control the exterior pairing of a compactly supported Lipschitz test.
Finite ball restrictions then connect truncated pairings to the renormalized
pairing through the outer-radius limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszFarIntegrand_integrable_of_compact_lipschitz {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) := by
  let ν := μ.restrict (ball a R)
  let w := affineNormalHeight e a 0
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w ‖e‖₊ hw a R hR
  have hφL2 := lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR
  have hφI := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν := memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hφL2) (hf := hwL2))
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w ‖e‖₊ hw a R hR
  have hN := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable hφI hφw a H R hH hR hHR
    (Filter.Eventually.of_forall hsupport) hweighted _ hZ).1
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have heq : rieszFarIntegrand m e φ a = renormalizedNormalIntegrand m w φ a := by
    funext q
    rw [rieszFarIntegrand_eq_normal_sub_correction m e w φ (affineNormalHeight_difference e a 0),
      hwa, mul_zero, zero_mul, sub_zero]
  rw [heq]
  exact hN

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalizedRieszPairingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized scalar Riesz pairing bounds

Lipschitz cancellation bounds the interior integrand by a weakly singular kernel.
The exterior estimate uses compact support and the normal height to control its
tail, giving quantitative bounds for the localized scalar pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszInteriorIntegrand_weak_kernel_bound {d : ℕ} (p : ℕ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (x y : Ambient d) :
    |rieszInteriorIntegrand (p + 1) e φ (x, y)| ≤
      (‖e‖ * (L : ℝ)) * inverseDistancePow p x y := by
  by_cases hxy : x = y
  · subst y
    simp only [rieszInteriorIntegrand, sub_self, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) L.coe_nonneg)
      (inverseDistancePow_nonneg _ _ _)
  have hd : dist x y ≠ 0 := (dist_pos.mpr hxy).ne'
  have he : |inner ℝ e (kernel (p + 1) x y)| ≤
      ‖e‖ * (dist x y ^ (p + 1))⁻¹ := by
    simpa only [Real.norm_eq_abs, kernel_norm_of_ne _ _ _ hxy] using!
      norm_inner_le_norm (𝕜 := ℝ) e (kernel (p + 1) x y)
  have hl : |φ x - φ y| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hφ.dist_le_mul x y
  calc
    _ = |inner ℝ e (kernel (p + 1) x y)| * |φ x - φ y| := by
      rw [rieszInteriorIntegrand, abs_mul]
    _ ≤ (‖e‖ * (dist x y ^ (p + 1))⁻¹) * ((L : ℝ) * dist x y) :=
      mul_le_mul he hl (abs_nonneg _) (by positivity)
    _ = _ := by
      unfold inverseDistancePow
      rw [pow_succ]
      field_simp

theorem rieszFarIntegrand_integral_abs_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    (∫ q, |rieszFarIntegrand m e φ a q|
      ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) ≤
      (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
        (‖e‖ * H * (∫ x in ball a R, |φ x| ∂μ)) * (2 * (C * 2 ^ m / R)) := by
  have hC : 0 ≤ C := hg.1
  let ν := μ.restrict (ball a R)
  let w := affineNormalHeight e a 0
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w ‖e‖₊ hw a R hR
  have hφL2 := lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR
  have hφI : Integrable φ ν := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν :=
    memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hφL2) (hf := hwL2))
  have hmoment : (∫ x, |φ x * w x| ∂ν) ≤
      (‖e‖ * H) * (∫ x, |φ x| ∂ν) := by
    calc
      _ ≤ ∫ x, (‖e‖ * H) * |φ x| ∂ν := by
        apply integral_mono hφw.abs (hφI.abs.const_mul _)
        intro x
        change |φ x * w x| ≤ (‖e‖ * H) * |φ x|
        by_cases hx : φ x = 0
        · simp only [hx, zero_mul, abs_zero, mul_zero, le_refl]
        have hwx : |w x| ≤ ‖e‖ * H := by
          have hb := hw.dist_le_mul x a
          simp only [Real.dist_eq, hwa, sub_zero, coe_nnnorm] at hb
          exact hb.trans (mul_le_mul_of_nonneg_left (hsupport x hx) (norm_nonneg _))
        rw [abs_mul, mul_comm (‖e‖ * H)]
        exact mul_le_mul_of_nonneg_left hwx (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w ‖e‖₊ hw a R hR
  simp only [hwa, abs_zero, zero_div, add_zero, coe_nnnorm] at hZ
  have hb := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable hφI hφw a H R hH hR hHR
    (Eventually.of_forall hsupport) hweighted _ hZ).2
  have heq : rieszFarIntegrand m e φ a = renormalizedNormalIntegrand m w φ a := by
    funext q
    rw [rieszFarIntegrand_eq_normal_sub_correction m e w φ
      (affineNormalHeight_difference e a 0), hwa, mul_zero, zero_mul, sub_zero]
  rw [heq]
  calc
    _ ≤ _ := hb
    _ ≤ 2 ^ (m + 1) * (((‖e‖ * H) * (∫ x, |φ x| ∂ν)) *
        (2 * (C * 2 ^ m / R))) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          ((∫ x, |φ x| ∂ν) * (‖e‖ * (2 * (C * 2 ^ m / R)))) := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmoment (by positivity)) (by positivity)
    _ = _ := by dsimp only [ν] <;> ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedRieszInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem cappedRieszInterior_continuous {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (e : Ambient d) (φ : Ambient d → ℝ) (hφ : Continuous φ) :
    Continuous (cappedRieszInterior m ε e φ) := by
  have hc := (cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε).continuous
  unfold cappedRieszInterior
  fun_prop

theorem distance_mul_cappedInverseDistancePow_bound {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (q : X × X) :
    dist q.1 q.2 * cappedInverseDistancePow (m + 1) ε q ≤ (ε ^ m)⁻¹ := by
  have hmax : 0 < max ε (dist q.1 q.2) := hε.trans_le (le_max_left _ _)
  calc
    _ ≤ max ε (dist q.1 q.2) * cappedInverseDistancePow (m + 1) ε q :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (cappedInverseDistancePow_nonneg _ _ _)
    _ = ((max ε (dist q.1 q.2)) ^ m)⁻¹ := by
      unfold cappedInverseDistancePow
      rw [pow_succ]
      field_simp
    _ ≤ _ := inv_anti₀ (pow_pos hε m) (pow_le_pow_left₀ hε.le (le_max_left _ _) m)

theorem cappedRieszInterior_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (e : Ambient d) (φ : Ambient d → ℝ) (B : ℝ≥0)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) (q : Ambient d × Ambient d) :
    |cappedRieszInterior m ε e φ q| ≤ (2 * (B : ℝ) * ‖e‖) * (ε ^ m)⁻¹ := by
  have hi : |inner ℝ e (q.1 - q.2)| ≤ ‖e‖ * dist q.1 q.2 := by
    simpa only [Real.norm_eq_abs, dist_eq_norm] using!
      norm_inner_le_norm (𝕜 := ℝ) e (q.1 - q.2)
  have hd : |φ q.1 - φ q.2| ≤ 2 * (B : ℝ) := by
    have ht := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith [hB q.1, hB q.2]
  calc
    _ = |inner ℝ e (q.1 - q.2)| * |φ q.1 - φ q.2| *
        cappedInverseDistancePow (m + 1) ε q := by
      rw [cappedRieszInterior, abs_mul, abs_mul,
        abs_of_nonneg (cappedInverseDistancePow_nonneg _ _ _)]
    _ ≤ (‖e‖ * dist q.1 q.2) * (2 * (B : ℝ)) *
        cappedInverseDistancePow (m + 1) ε q :=
      mul_le_mul_of_nonneg_right (mul_le_mul hi hd (abs_nonneg _) (by positivity))
        (cappedInverseDistancePow_nonneg _ _ _)
    _ = (2 * (B : ℝ) * ‖e‖) *
        (dist q.1 q.2 * cappedInverseDistancePow (m + 1) ε q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (distance_mul_cappedInverseDistancePow_bound m ε hε q) (by positivity)

theorem cappedRieszInterior_eq_affine_bilinear {d : ℕ} (m : ℕ) (ε : ℝ)
    (e : Ambient d) (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedRieszInterior m ε e φ q =
      (affineNormalHeight e 0 0 q.1 - affineNormalHeight e 0 0 q.2) *
        cappedTestKernel m ε φ q := by
  rw [affineNormalHeight_difference]
  unfold cappedRieszInterior cappedTestKernel
  ring

theorem rieszInterior_cap_error_pointwise {d : ℕ} (p : ℕ) (ε : ℝ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (q : Ambient d × Ambient d) :
    |rieszInteriorIntegrand (p + 1) e φ q - cappedRieszInterior (p + 1) ε e φ q| ≤
      (‖e‖ * (L : ℝ)) * nearPairWeight p ε q := by
  have hb := capped_bilinear_error_pointwise (p + 1) ε (affineNormalHeight e 0 0) φ q
  rw [← cappedRieszInterior_eq_affine_bilinear] at hb
  have heq := rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e
    (affineNormalHeight e 0 0) φ (affineNormalHeight_difference e 0 0)
  simp only [← heq] at hb
  apply hb.trans
  by_cases hq : q ∈ nearPairSet ε
  · rw [indicator_of_mem hq, nearPairWeight, indicator_of_mem hq]
    exact rieszInteriorIntegrand_weak_kernel_bound p e φ L hφ q.1 q.2
  · rw [indicator_of_notMem hq, nearPairWeight, indicator_of_notMem hq, mul_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CorrectedSingularTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem fractionalBilinear_test_sub {d : ℕ} (m : ℕ) (w φ η : Ambient d → ℝ)
    (c : ℝ) (x y : Ambient d) :
    fractionalBilinear m w (fun z => φ z - c * η z) x y =
      fractionalBilinear m w φ x y - c * fractionalBilinear m w η x y := by
  unfold fractionalBilinear
  ring

theorem fractionalBilinear_integral_test_sub {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (w φ η : Ambient d → ℝ) (c : ℝ)
    (hφ : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      (μ.prod μ))
    (hη : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w η q.1 q.2)
      (μ.prod μ)) :
    (∫ q : Ambient d × Ambient d, fractionalBilinear m w (fun z => φ z - c * η z) q.1 q.2
      ∂μ.prod μ) =
      (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2 ∂μ.prod μ) -
      c * (∫ q : Ambient d × Ambient d, fractionalBilinear m w η q.1 q.2 ∂μ.prod μ) := by
  simp only [fractionalBilinear_test_sub]
  rw [integral_sub hφ (hη.const_mul c), integral_const_mul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak convergence on continuity sets

Weak convergence of finite measures controls the masses of sets with null boundary.
Weighting by bounded continuous nonnegative functions transfers this control to restricted
integrals, providing continuity-set versions of the weak convergence estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem finiteMeasure_continuitySet_mass_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d))
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure (Ambient d)).real s) atTop
      (𝓝 ((ν : Measure (Ambient d)).real s)) := by
  by_cases hν : ν = 0
  · subst ν
    have ht : Tendsto (fun j => (μ j : Measure (Ambient d)).real univ) atTop (𝓝 0) := by
      simpa using! NNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
    simpa using! squeeze_zero (fun _ => measureReal_nonneg)
      (fun j => measureReal_mono (μ := (μ j : Measure (Ambient d))) (subset_univ s)) ht
  · exact finiteMeasure_cell_mass_tendsto μ ν hweak hν s hboundary

theorem weightedFiniteMeasure_integral {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(weightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂(μ : Measure (Ambient d)) := by
  exact integral_withDensity_eq_integral_smul (μ := (μ : Measure (Ambient d)))
    f.continuous.measurable g

theorem weightedFiniteMeasure_real_set {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) (s : Set (Ambient d)) (hs : MeasurableSet s) :
    (weightedFiniteMeasure μ f : Measure (Ambient d)).real s =
      ∫ x in s, (f x : ℝ) ∂(μ : Measure (Ambient d)) := by
  change ((μ : Measure (Ambient d)).withDensity (fun x => (f x : ℝ≥0∞))).real s = _
  rw [Measure.real, withDensity_apply _ hs]
  exact f.toReal_lintegral_coe_eq_integral ((μ : Measure (Ambient d)).restrict s)

theorem weightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (f : Ambient d →ᵇ ℝ≥0) :
    Tendsto (fun j => weightedFiniteMeasure (μ j) f) atTop (𝓝 (weightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  simp only [weightedFiniteMeasure_integral]
  let f₀ : Ambient d →ᵇ ℝ := BoundedContinuousFunction.comp ((↑) : ℝ≥0 → ℝ)
    NNReal.isometry_coe.lipschitz f
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (f₀ * g)

theorem weak_setIntegral_nnreal_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) (f : Ambient d →ᵇ ℝ≥0) :
    Tendsto (fun j => ∫ x in s, (f x : ℝ) ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x in s, (f x : ℝ) ∂(ν : Measure (Ambient d)))) := by
  have hb : (weightedFiniteMeasure ν f : Measure (Ambient d)) (frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ hboundary
  have h := finiteMeasure_continuitySet_mass_tendsto (fun j => weightedFiniteMeasure (μ j) f)
    (weightedFiniteMeasure ν f) (weightedFiniteMeasure_tendsto μ ν hweak f) s hb
  simpa only [weightedFiniteMeasure_real_set _ f s hs] using! h

theorem weak_setIntegral_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) (f : Ambient d →ᵇ ℝ) :
    Tendsto (fun j => ∫ x in s, f x ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x in s, f x ∂(ν : Measure (Ambient d)))) := by
  have hp := weak_setIntegral_nnreal_tendsto μ ν hweak s hs hboundary f.nnrealPart
  have hn := weak_setIntegral_nnreal_tendsto μ ν hweak s hs hboundary (-f).nnrealPart
  simpa only [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub] using! hp.sub hn

theorem restrictedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => restrictedFiniteMeasure (μ j) s) atTop (𝓝 (restrictedFiniteMeasure ν s)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact fun f => weak_setIntegral_tendsto μ ν hweak s hs hboundary f

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactWeakConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction CompactlySupported

theorem compactWeightedFiniteMeasure_integral {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0)) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(compactWeightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂μ := by
  exact integral_withDensity_eq_integral_smul f.continuous.measurable g

theorem compactWeightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (f : C_c(Ambient d, ℝ≥0)) :
    Tendsto (fun j => compactWeightedFiniteMeasure (μ j) f) atTop
      (𝓝 (compactWeightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let test : C_c(Ambient d, ℝ) :=
    ⟨⟨fun x => f.toReal x * g x, f.toReal.continuous.mul g.continuous⟩,
      f.toReal.hasCompactSupport.mul_right⟩
  have ht := hlocal test
  change Tendsto (fun j => ∫ x, f.toReal x * g x ∂μ j) atTop
    (𝓝 (∫ x, f.toReal x * g x ∂ν)) at ht
  simpa only [compactWeightedFiniteMeasure_integral,
    CompactlySupportedContinuousMap.toReal_apply] using! ht

theorem exists_compact_nonneg_cutoff {d : ℕ} (s : Set (Ambient d)) (hs : IsCompact s) :
    ∃ f : C_c(Ambient d, ℝ≥0), (∀ x ∈ s, f x = 1) ∧ ∀ x, f x ≤ 1 := by
  obtain ⟨g, hgs, _, hgc, hg⟩ :=
    exists_continuous_one_zero_of_isCompact hs isClosed_empty (disjoint_empty s)
  let g₀ : C_c(Ambient d, ℝ) := ⟨g, hgc⟩
  refine ⟨g₀.nnrealPart, ?_, ?_⟩
  · intro x hx
    change Real.toNNReal (g x) = 1
    rw [show g x = 1 from hgs hx]
    simp
  · intro x
    change Real.toNNReal (g x) ≤ 1
    simpa using! Real.toNNReal_le_toNNReal (hg x).2

theorem compactWeightedFiniteMeasure_restrict {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x = 1) :
    (compactWeightedFiniteMeasure μ f : Measure (Ambient d)).restrict s = μ.restrict s := by
  change (μ.withDensity (fun x => (f x : ℝ≥0∞))).restrict s = _
  rw [restrict_withDensity hs]
  calc
    _ = (μ.restrict s).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      simp only [hf x hx, ENNReal.coe_one, Pi.one_apply]
    _ = _ := withDensity_one

theorem compactTestConvergence_restrict_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (s : Set (Ambient d))
    (hs : MeasurableSet s) (hc : IsCompact (closure s))
    (hboundary : ν (frontier s) = 0) :
    Tendsto (fun j => relativelyCompactFiniteMeasure (μ j) s hc) atTop
      (𝓝 (relativelyCompactFiniteMeasure ν s hc)) := by
  obtain ⟨f, hf, _⟩ := exists_compact_nonneg_cutoff (closure s) hc
  have hf' : ∀ x ∈ s, f x = 1 := fun x hx => hf x (subset_closure hx)
  have hb : (compactWeightedFiniteMeasure ν f : Measure (Ambient d)) (frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ hboundary
  have h := restrictedFiniteMeasure_tendsto (fun j => compactWeightedFiniteMeasure (μ j) f)
    (compactWeightedFiniteMeasure ν f) (compactWeightedFiniteMeasure_tendsto μ ν hlocal f) s hs hb
  have heq : ∀ (ρ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ρ],
      restrictedFiniteMeasure (compactWeightedFiniteMeasure ρ f) s =
        relativelyCompactFiniteMeasure ρ s hc := by
    intro ρ _
    apply Subtype.ext
    exact compactWeightedFiniteMeasure_restrict ρ f s hs hf'
  simpa only [heq] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanCorrectionAdmissible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal CompactlySupported

theorem compact_meanCorrection_admissible {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ ν)
    (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0) :
    Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,
        (∫ x, η x ∂μ j) ≠ 0 ∧
        Integrable (meanCorrection (μ j) φ η) (μ j) ∧
        (∫ x, meanCorrection (μ j) φ η x ∂μ j) = 0 ∧
        LipschitzWith (Lφ + Lη) (meanCorrection (μ j) φ η) ∧
        (∀ x, |meanCorrection (μ j) φ η x| ≤ ((Bφ + Bη : ℝ≥0) : ℝ)) ∧
        HasCompactSupport (meanCorrection (μ j) φ η) := by
  have hφlim := hlocal (⟨⟨φ, hφ.continuous⟩, hcφ⟩ : C_c(Ambient d, ℝ))
  have hηlim := hlocal (⟨⟨η, hη.continuous⟩, hcη⟩ : C_c(Ambient d, ℝ))
  change Tendsto (fun j => ∫ x, φ x ∂μ j) atTop (𝓝 (∫ x, φ x ∂ν)) at hφlim
  change Tendsto (fun j => ∫ x, η x ∂μ j) atTop (𝓝 (∫ x, η x ∂ν)) at hηlim
  rw [hmean] at hφlim
  have hc := meanCorrection_coefficient_tendsto_zero μ φ η _ hbump hφlim hηlim
  refine ⟨hc, ?_⟩
  have hcabs : Tendsto (fun j => |(∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using! hc.norm
  filter_upwards [hηlim.eventually (eventually_ne_nhds hbump),
    hcabs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hηne hcoef
  have hiφ : Integrable φ (μ j) := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hiη : Integrable η (μ j) := hη.continuous.integrable_of_hasCompactSupport hcη
  refine ⟨hηne, meanCorrection_integrable (μ j) φ η hiφ hiη,
    meanCorrection_integral_zero (μ j) φ η hiφ hiη hηne, ?_, ?_, ?_⟩
  · apply (meanCorrection_lipschitz (μ j) hφ hη).weaken
    apply add_le_add le_rfl
    have hcNN : ‖(∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)‖₊ ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using! hcoef.le
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right hcNN (zero_le)
  · intro x
    unfold meanCorrection
    calc
      _ ≤ |φ x| + |(∫ y, φ y ∂μ j) / (∫ y, η y ∂μ j)| * |η x| := by
        simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using! abs_sub_le (φ x) 0
          (((∫ y, φ y ∂μ j) / (∫ y, η y ∂μ j)) * η x)
      _ ≤ (Bφ : ℝ) + 1 * (Bη : ℝ) :=
        add_le_add (hBφ x) (mul_le_mul hcoef.le (hBη x) (abs_nonneg _) (by norm_num))
      _ = _ := by rw [one_mul, NNReal.coe_add]
  · exact hcφ.sub hcη.mul_left

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PairingLocalizationIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independence of Riesz pairing localization

Exhaustion by outer balls recovers the scalar Riesz pairing from finite restrictions.
For compactly supported mean-zero Lipschitz tests, the resulting pairing is independent
of the localization center and radius satisfying the support separation bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem ball_subset_outer_of_radius_dist {d : ℕ} (a b : Ambient d) (R T : ℝ)
    (h : R + dist a b ≤ T) : ball a R ⊆ ball b T := by
  intro x hx
  change dist x b < T
  change dist x a < R at hx
  have ht := dist_triangle x a b
  linarith

theorem restrict_nested_balls_of_subset {d : ℕ} (μ : Measure (Ambient d))
    (a b : Ambient d) (R T : ℝ) (hsub : ball a R ⊆ ball b T) :
    (μ.restrict (ball b T)).restrict (ball a R) = μ.restrict (ball a R) := by
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hsub]

theorem rieszScalarPairing_restrict_outer_ball {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a b : Ambient d) (R T : ℝ)
    (hsub : ball a R ⊆ ball b T) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing m (μ.restrict (ball b T)) a R e φ =
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) +
      ∫ q in univ ×ˢ ball b T, rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)) := by
  have hcomm : (μ.restrict (ball b T)).restrict (closedExterior a R) =
      (μ.restrict (closedExterior a R)).restrict (ball b T) := by
    rw [Measure.restrict_restrict (closedExterior_measurable a R),
      Measure.restrict_restrict measurableSet_ball, inter_comm]
  have hprod : (μ.restrict (ball a R)).prod ((μ.restrict (closedExterior a R)).restrict (ball b T)) =
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))).restrict (univ ×ˢ ball b T) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  unfold rieszScalarPairing
  dsimp only
  rw [restrict_nested_balls_of_subset μ a b R T hsub, hcomm, hprod]

theorem rieszScalarPairing_outer_limit_at_center {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a b : Ambient d) (R T₀ : ℝ)
    (hcontain : R + dist a b ≤ T₀) (e : Ambient d) (φ : Ambient d → ℝ)
    (hfar : Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    Tendsto (fun k : ℕ => rieszScalarPairing m (μ.restrict (ball b (outerPairRadius T₀ k))) a R e φ)
      atTop (𝓝 (rieszScalarPairing m μ a R e φ)) := by
  have ht := integral_outer_pair_exhaustion
    ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) b T₀
    (rieszFarIntegrand m e φ a) hfar
  have heq : (fun k : ℕ => rieszScalarPairing m (μ.restrict (ball b (outerPairRadius T₀ k))) a R e φ) =
      fun k => (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) +
      ∫ q in univ ×ˢ ball b (outerPairRadius T₀ k), rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)) := by
    funext k
    exact rieszScalarPairing_restrict_outer_ball m μ a b R _
      (ball_subset_outer_of_radius_dist a b R _ (hcontain.trans (outerPairRadius_ge T₀ k))) e φ
  rw [heq]
  exact tendsto_const_nhds.add ht

theorem mean_zero_restrict_of_support {d : ℕ} (μ : Measure (Ambient d))
    (φ : Ambient d → ℝ) (a : Ambient d) (R : ℝ)
    (hsupport : ∀ x ∉ ball a R, φ x = 0) (hzero : (∫ x, φ x ∂μ) = 0) :
    (∫ x in ball a R, φ x ∂μ) = 0 :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).trans hzero

theorem rieszScalarPairing_localization_independent {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a b : Ambient d) (H J R S : ℝ) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hR : 0 < R) (hS : 0 < S) (hHR : 2 * H ≤ R) (hJS : 2 * J ≤ S)
    (hsupportA : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (hsupportB : ∀ x, φ x ≠ 0 → dist x b ≤ J)
    (hzero : (∫ x, φ x ∂μ) = 0) :
    rieszScalarPairing (p + 1) μ a R e φ = rieszScalarPairing (p + 1) μ b S e φ := by
  let T₀ := R + S + dist a b
  have hcontainA : R + dist a a ≤ T₀ := by dsimp [T₀]; rw [dist_self]; have := dist_nonneg (x := a) (y := b); linarith
  have hcontainB : S + dist b a ≤ T₀ := by dsimp [T₀]; rw [dist_comm b a]; linarith
  have hfarA := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ a H R hH hR hHR hsupportA
  have hfarB := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ b J S hJ hS hJS hsupportB
  have hlimA := rieszScalarPairing_outer_limit_at_center (p + 1) μ a a R T₀ hcontainA e φ hfarA
  have hlimB := rieszScalarPairing_outer_limit_at_center (p + 1) μ b a S T₀ hcontainB e φ hfarB
  have hφzeroA : ∀ x ∉ ball a R, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupportA x hn).trans_lt (by linarith : H < R))
  have hφzeroB : ∀ x ∉ ball b S, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupportB x hn).trans_lt (by linarith : J < S))
  have heq : (fun k : ℕ => rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius T₀ k))) a R e φ) =
      fun k => rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius T₀ k))) b S e φ := by
    funext k
    let T := outerPairRadius T₀ k
    let ν := μ.restrict (ball a T)
    have hRT₀ : R ≤ T₀ := by simpa only [dist_self, add_zero] using! hcontainA
    have hRT : R ≤ T := hRT₀.trans (outerPairRadius_ge T₀ k)
    have hT : 0 < T := hR.trans_le hRT
    have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a T hT
    have hφI : Integrable φ ν := (lipschitz_height_memLp_on_ball (p + 1) C μ hg φ L hφ a T hT).integrable (by norm_num)
    have hzeroν : (∫ x, φ x ∂ν) = 0 := mean_zero_restrict_of_support μ φ a T
      (fun x hx => hφzeroA x (fun hin => hx ((ball_subset_ball hRT) hin))) hzero
    have hF := rieszInteriorIntegrand_integrable_of_lipschitz p C ν
      (globalGrowth_restrict (p + 1) C μ hg (ball a T)) e φ L hφ (2 * T) (by positivity)
      (ball_restriction_pair_diameter μ a T)
    have hA := (finite_pairing_eq_renormalized (p + 1) e ν a R hR φ hφI hφzeroA
      (mean_zero_restrict_of_support ν φ a R hφzeroA hzeroν) hF).2
    have hB := (finite_pairing_eq_renormalized (p + 1) e ν b S hS φ hφI hφzeroB
      (mean_zero_restrict_of_support ν φ b S hφzeroB hzeroν) hF).2
    exact hA.symm.trans hB
  rw [← heq] at hlimB
  exact tendsto_nhds_unique hlimA hlimB

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OscillationTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem tsupport_subset_ball_of_support_bound {d : ℕ}
    (φ : Ambient d → ℝ) (a : Ambient d) (H A : ℝ) (hHA : H < A)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) : tsupport φ ⊆ ball a A := by
  have hclosed : tsupport φ ⊆ closedBall a H := by
    change closure (Function.support φ) ⊆ closedBall a H
    exact isClosed_closedBall.closure_subset_iff.mpr (fun x hx => hsupport x hx)
  intro x hx
  exact (hclosed hx).trans_lt hHA

theorem ScalarOscillationBound.lipschitz_test_bound {d : ℕ}
    (m : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (A v : ℝ)
    (hosc : ScalarOscillationBound m μ a A v) (e : Ambient d) (he : ‖e‖ ≤ 1)
    (φ : Ambient d → ℝ) (D : ℝ≥0) (hφ : LipschitzWith D φ)
    (hsupport : tsupport φ ⊆ ball a A) (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing m μ a (2 * A) e φ| ≤ ((D : ℝ) + 1) * v := by
  let c : ℝ := (D : ℝ) + 1
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hscaled := lipschitz_const_mul_real hφ c⁻¹
  have hcoef : ‖c⁻¹‖₊ * D ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    rw [abs_of_pos (inv_pos.mpr hc)]
    have hDc : (D : ℝ) ≤ c := by dsimp [c] <;> linarith
    calc
      c⁻¹ * (D : ℝ) = (D : ℝ) / c := by ring
      _ ≤ 1 := (div_le_one hc).mpr hDc
  have hzero' : (∫ x, c⁻¹ * φ x ∂μ) = 0 := by rw [integral_const_mul, hzero, mul_zero]
  have hb := hosc e he (fun x => c⁻¹ * φ x) (hscaled.weaken hcoef)
    (tsupport_mul_subset_right.trans hsupport) hzero'
  rw [rieszScalarPairing_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hc)] at hb
  calc
    |rieszScalarPairing m μ a (2 * A) e φ| = c * (c⁻¹ * |rieszScalarPairing m μ a (2 * A) e φ|) := by
      field_simp
    _ ≤ c * v := mul_le_mul_of_nonneg_left hb hc.le

theorem oscillation_bound_for_localized_test {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (a : Ambient d) (A v : ℝ) (hA : 0 < A) (hosc : ScalarOscillationBound (p + 1) μ a A v)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (φ : Ambient d → ℝ) (D : ℝ≥0) (hφ : LipschitzWith D φ)
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R) (hHA : H < A)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing (p + 1) μ a R e φ| ≤ ((D : ℝ) + 1) * v := by
  have hsupport' : ∀ x, φ x ≠ 0 → dist x a ≤ A := fun x hx => (hsupport x hx).trans hHA.le
  have heq := rieszScalarPairing_localization_independent p C μ hg e φ D hφ a a H A R (2 * A)
    hH hA.le hR (by positivity) hHR le_rfl hsupport hsupport' hzero
  rw [heq]
  exact hosc.lipschitz_test_bound (p + 1) μ a A v e he φ D hφ
    (tsupport_subset_ball_of_support_bound φ a H A hHA hsupport) hzero

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszInteriorCapError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrable errors for capped interior Riesz kernels

The capped interior integrand is integrable for finite measures and bounded
continuous tests. For Lipschitz tests, a near-diagonal weight dominates its
difference from the original integrand, giving integrability of the latter
and quantitative control of the capping error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem cappedRieszInterior_integrable {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (e : Ambient d) (φ : Ambient d → ℝ) (hφ : Continuous φ)
    (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Integrable (cappedRieszInterior m ε e φ) (μ.prod μ) := by
  apply Integrable.of_bound
    (cappedRieszInterior_continuous m ε hε e φ hφ).measurable.aestronglyMeasurable
    ((2 * (B : ℝ) * ‖e‖) * (ε ^ m)⁻¹)
  exact Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs] using! cappedRieszInterior_bound m ε hε e φ B hB q

theorem rieszInterior_integrable_and_cap_error {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    Integrable (rieszInteriorIntegrand (p + 1) e φ) (μ.prod μ) ∧
      |(∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂μ.prod μ) -
        ∫ q, cappedRieszInterior (p + 1) ε e φ q ∂μ.prod μ| ≤
          (‖e‖ * (L : ℝ)) * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε))) := by
  let F := rieszInteriorIntegrand (p + 1) e φ
  let G := cappedRieszInterior (p + 1) ε e φ
  have hG : Integrable G (μ.prod μ) :=
    cappedRieszInterior_integrable (p + 1) ε hε μ e φ hφ.continuous B hB
  have hFm : Measurable F := by
    have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
    have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
    have hφm := hφ.continuous.measurable
    dsimp only [F]
    unfold rieszInteriorIntegrand kernel
    fun_prop
  have hdom := (nearPairWeight_integrable p C μ hg ε hε).const_mul (‖e‖ * (L : ℝ))
  have herr : Integrable (fun q => F q - G q) (μ.prod μ) := by
    apply hdom.mono' (hFm.aestronglyMeasurable.sub hG.aestronglyMeasurable)
    exact Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using! rieszInterior_cap_error_pointwise p ε e φ L hφ q
  have hF : Integrable F (μ.prod μ) := by
    have heq : F = fun q => (F q - G q) + G q := by funext q; ring
    rw [heq]
    exact herr.add hG
  refine ⟨hF, ?_⟩
  change |(∫ q, F q ∂μ.prod μ) - ∫ q, G q ∂μ.prod μ| ≤ _
  rw [← integral_sub hF hG]
  calc
    _ ≤ ∫ q, |F q - G q| ∂μ.prod μ := abs_integral_le_integral_abs
    _ ≤ ∫ q, (‖e‖ * (L : ℝ)) * nearPairWeight p ε q ∂μ.prod μ :=
      integral_mono_ae herr.abs hdom
        (Eventually.of_forall fun q => rieszInterior_cap_error_pointwise p ε e φ L hφ q)
    _ = (‖e‖ * (L : ℝ)) * ∫ q, nearPairWeight p ε q ∂μ.prod μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (nearPairWeight_integral_bound p C μ hg ε hε)
      (mul_nonneg (norm_nonneg _) L.coe_nonneg)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CorrectedLocalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

theorem globally_corrected_local_singular_limit {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (s : Set (Ambient d))
    (w : ℕ → Ambient d → ℝ) (φ η : Ambient d → ℝ)
    (hc : Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0))
    (hφ : ∀ j, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m (w j) φ q.1 q.2)
      (((μ j).restrict s).prod ((μ j).restrict s)))
    (hη : ∀ j, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m (w j) η q.1 q.2)
      (((μ j).restrict s).prod ((μ j).restrict s)))
    (P Q : ℝ)
    (hP : Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) φ q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 P))
    (hQ : Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) η q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 Q)) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear m (w j) (meanCorrection (μ j) φ η) q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 P) := by
  have heq : ∀ j, (∫ q : Ambient d × Ambient d,
      fractionalBilinear m (w j) (meanCorrection (μ j) φ η) q.1 q.2
        ∂((μ j).restrict s).prod ((μ j).restrict s)) =
      (∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) φ q.1 q.2
        ∂((μ j).restrict s).prod ((μ j).restrict s)) -
        ((∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) *
          (∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) η q.1 q.2
            ∂((μ j).restrict s).prod ((μ j).restrict s)) := by
    intro j
    exact fractionalBilinear_integral_test_sub m ((μ j).restrict s) (w j) φ η _ (hφ j) (hη j)
  simp only [heq]
  simpa only [zero_mul, sub_zero] using! hP.sub (hc.mul hQ)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_FiniteWeakProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem finiteMeasure_smul_product {d k : ℕ}
    (μ : FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient k)) (c b : ℝ≥0) :
    (c • μ).prod (b • ν) = (c * b) • μ.prod ν := by
  apply Subtype.ext
  change (c • (μ : Measure (Ambient d))).prod (b • (ν : Measure (Ambient k))) =
    (c * b) • (μ : Measure (Ambient d)).prod (ν : Measure (Ambient k))
  simp only [← Measure.coe_nnreal_smul, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, ENNReal.coe_mul, mul_comm]

theorem finiteMeasure_product_normalization {d k : ℕ}
    (μ : FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient k)) :
    μ.prod ν = (μ.mass * ν.mass) • (μ.normalize.prod ν.normalize).toFiniteMeasure := by
  calc
    _ = (μ.mass • μ.normalize.toFiniteMeasure).prod
        (ν.mass • ν.normalize.toFiniteMeasure) :=
      congrArg₂ FiniteMeasure.prod μ.self_eq_mass_smul_normalize ν.self_eq_mass_smul_normalize
    _ = _ := finiteMeasure_smul_product μ.normalize.toFiniteMeasure ν.normalize.toFiniteMeasure
      μ.mass ν.mass

theorem finiteMeasure_product_tendsto_nonzero {d k : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : ℕ → FiniteMeasure (Ambient k))
    (μ₀ : FiniteMeasure (Ambient d)) (ν₀ : FiniteMeasure (Ambient k))
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hν : Tendsto ν atTop (𝓝 ν₀))
    (hμ₀ : μ₀ ≠ 0) (hν₀ : ν₀ ≠ 0) :
    Tendsto (fun j => (μ j).prod (ν j)) atTop (𝓝 (μ₀.prod ν₀)) := by
  have hP := FiniteMeasure.tendsto_normalize_of_tendsto hμ hμ₀
  have hQ := FiniteMeasure.tendsto_normalize_of_tendsto hν hν₀
  have hPQ : Tendsto (fun j => (μ j).normalize.prod (ν j).normalize) atTop
      (𝓝 (μ₀.normalize.prod ν₀.normalize)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (μ₀.normalize, ν₀.normalize)).comp (hP.prodMk_nhds hQ)
  have hF := (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto
    (μ₀.normalize.prod ν₀.normalize)).comp hPQ
  have hm := hμ.mass.mul hν.mass
  have ht := hm.smul hF
  simpa only [Function.comp_apply, ← finiteMeasure_product_normalization] using! ht

theorem finiteMeasure_bounded_product_integral_tendsto {d k : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : ℕ → FiniteMeasure (Ambient k))
    (μ₀ : FiniteMeasure (Ambient d)) (ν₀ : FiniteMeasure (Ambient k))
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hν : Tendsto ν atTop (𝓝 ν₀))
    (hμ₀ : μ₀ ≠ 0) (hν₀ : ν₀ ≠ 0) (F : Ambient d × Ambient k →ᵇ ℝ) :
    Tendsto (fun j => ∫ q, F q ∂(μ j : Measure (Ambient d)).prod (ν j : Measure (Ambient k)))
      atTop (𝓝 (∫ q, F q ∂(μ₀ : Measure (Ambient d)).prod (ν₀ : Measure (Ambient k)))) :=
  FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (finiteMeasure_product_tendsto_nonzero μ ν μ₀ ν₀ hμ hν hμ₀ hν₀) F

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakRieszInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal BoundedContinuousFunction

theorem cappedRieszInterior_integral_tendsto {d : ℕ} (m : ℕ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (e : Ambient d) (φ : Ambient d → ℝ) (hφ : Continuous φ)
    (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun j => ∫ q, cappedRieszInterior m ε e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q, cappedRieszInterior m ε e φ q
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  let Q := (2 * (B : ℝ) * ‖e‖) * (ε ^ m)⁻¹
  let F : Ambient d × Ambient d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨cappedRieszInterior m ε e φ, cappedRieszInterior_continuous m ε hε e φ hφ⟩
    (2 * Q) (by
      intro q z
      change dist (cappedRieszInterior m ε e φ q) (cappedRieszInterior m ε e φ z) ≤ 2 * Q
      rw [Real.dist_eq]
      have ht := abs_sub_le (cappedRieszInterior m ε e φ q) 0 (cappedRieszInterior m ε e φ z)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      have hq := cappedRieszInterior_bound m ε hε e φ B hB q
      have hz := cappedRieszInterior_bound m ε hε e φ B hB z
      dsimp only [Q]
      linarith)
  exact finiteMeasure_bounded_product_integral_tendsto μ μ ν ν hweak hweak hν hν F

theorem rieszInterior_integral_tendsto_of_weak {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j : Measure (Ambient d)))
    (hgν : GlobalUpperGrowth (p + 1) C (ν : Measure (Ambient d)))
    (M : ℝ) (hM : ∀ j, (μ j : Measure (Ambient d)).real univ ≤ M)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Tendsto (fun j => ∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q, rieszInteriorIntegrand (p + 1) e φ q
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  let N := max M ((ν : Measure (Ambient d)).real univ)
  have hN : 0 ≤ N := measureReal_nonneg.trans (le_max_right _ _)
  have hC : 0 ≤ C := hgν.1
  let A := (‖e‖ * (L : ℝ)) * (N * (2 * (C * 2 ^ (p + 1) * 2 ^ p)))
  have hA : 0 ≤ A := by dsimp only [A] <;> positivity
  have hsource (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
      |(∫ q, rieszInteriorIntegrand (p + 1) e φ q
          ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) -
        ∫ q, cappedRieszInterior (p + 1) ε e φ q
          ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))| ≤ A * ε := by
    have hb := (rieszInterior_integrable_and_cap_error p C (μ j : Measure (Ambient d))
      (hg j) e φ L B hφ hB ε hε).2
    apply hb.trans
    calc
      _ ≤ (‖e‖ * (L : ℝ)) * (N * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right ((hM j).trans (le_max_left _ _)) (by positivity))
          (by positivity)
      _ = _ := by dsimp only [A] <;> ring
  have htarget (ε : ℝ) (hε : 0 < ε) :
      |(∫ q, rieszInteriorIntegrand (p + 1) e φ q
          ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) -
        ∫ q, cappedRieszInterior (p + 1) ε e φ q
          ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))| ≤ A * ε := by
    have hb := (rieszInterior_integrable_and_cap_error p C (ν : Measure (Ambient d))
      hgν e φ L B hφ hB ε hε).2
    apply hb.trans
    calc
      _ ≤ (‖e‖ * (L : ℝ)) * (N * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)
      _ = _ := by dsimp only [A] <;> ring
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let ε := η / (3 * (A + 1))
  have hε : 0 < ε := by dsimp only [ε] <;> positivity
  have heq : (3 * (A + 1)) * ε = η := by
    dsimp only [ε]
    field_simp
  have hsmall : A * ε < η / 3 := by nlinarith
  have hthird : 0 < η / 3 := by positivity
  have hcap := cappedRieszInterior_integral_tendsto (p + 1) μ ν hweak hν e φ hφ.continuous B hB ε hε
  filter_upwards [Metric.tendsto_nhds.mp hcap (η / 3) hthird] with j hj
  have hjerr := (hsource j ε hε).trans_lt hsmall
  have hνerr := (htarget ε hε).trans_lt hsmall
  rw [← Real.dist_eq] at hjerr hνerr
  have ht := dist_triangle
    (∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d)))
    (∫ q, cappedRieszInterior (p + 1) ε e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d)))
    (∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))
  have ht' := dist_triangle
    (∫ q, cappedRieszInterior (p + 1) ε e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d)))
    (∫ q, cappedRieszInterior (p + 1) ε e φ q
      ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))
    (∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))
  rw [dist_comm] at hνerr
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactRieszInteriorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interior Riesz pairings under compact-test convergence

Restricting to a ball with zero boundary mass converts compact-test convergence into
weak convergence of finite measures. Common upper growth bounds then give convergence
of the interior Riesz pairing against bounded Lipschitz tests. For compactly supported
mean-zero limit tests, a bump with nonzero integral also controls the mean correction,
so the corrected pairings converge to the original limit pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_rieszInterior_ball {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν) (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Tendsto (fun j => ∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂((μ j).restrict (ball a R)).prod ((μ j).restrict (ball a R))) atTop
      (𝓝 (∫ q, rieszInteriorIntegrand (p + 1) e φ q
        ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R)))) := by
  let (j : ℕ) := (hg j).finite_on_compacts
  let := hgν.finite_on_compacts
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let μ' := fun j => relativelyCompactFiniteMeasure (μ j) (ball a R) hcompact
  let ν' := relativelyCompactFiniteMeasure ν (ball a R) hcompact
  have hweak' : Tendsto μ' atTop (𝓝 ν') :=
    compactTestConvergence_restrict_tendsto μ ν hweak (ball a R) measurableSet_ball hcompact hboundary
  have hν' : ν' ≠ 0 := by
    intro hz
    have heq := congrArg (fun ρ : FiniteMeasure (Ambient d) => (ρ : Measure (Ambient d)) univ) hz
    apply hmass
    change (ν.restrict (ball a R)) univ = (0 : Measure (Ambient d)) univ at heq
    simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using! heq
  apply rieszInterior_integral_tendsto_of_weak p (max C D) μ' ν' hweak' hν'
    (fun j => (globalGrowth_restrict (p + 1) C (μ j) (hg j) (ball a R)).mono_constant (le_max_left _ _))
    ((globalGrowth_restrict (p + 1) D ν hgν (ball a R)).mono_constant (le_max_right _ _))
    (C * R ^ (p + 1)) (fun j => ball_restriction_mass_bound (p + 1) C (μ j) (hg j) a R hR)
    e φ L B hφ hB

theorem compactTestConvergence_corrected_rieszInterior_ball {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν) (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (e : Ambient d) (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0) :
    Tendsto (fun j => ∫ q, rieszInteriorIntegrand (p + 1) e (meanCorrection (μ j) φ η) q
      ∂((μ j).restrict (ball a R)).prod ((μ j).restrict (ball a R))) atTop
      (𝓝 (∫ q, rieszInteriorIntegrand (p + 1) e φ q
        ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R)))) := by
  let (j : ℕ) := (hg j).finite_on_compacts
  let (j : ℕ) : IsFiniteMeasure ((μ j).restrict (ball a R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C (μ j) (hg j) a R hR
  have hcoef := (compact_meanCorrection_admissible μ ν hweak φ η Lφ Lη Bφ Bη
    hφ hη hcφ hcη hBφ hBη hmean hbump).1
  have hlimφ := compactTestConvergence_rieszInterior_ball p C D μ ν hg hgν hweak a R hR
    hboundary hmass e φ Lφ Bφ hφ hBφ
  have hlimη := compactTestConvergence_rieszInterior_ball p C D μ ν hg hgν hweak a R hR
    hboundary hmass e η Lη Bη hη hBη
  let w := affineNormalHeight e 0 0
  have heq (ψ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
      rieszInteriorIntegrand (p + 1) e ψ q = fractionalBilinear (p + 1) w ψ q.1 q.2 :=
    rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e w ψ
      (affineNormalHeight_difference e 0 0) q
  simp only [heq] at hlimφ hlimη ⊢
  apply globally_corrected_local_singular_limit (p + 1) μ (ball a R) (fun _ => w) φ η hcoef
    _ _ _ _ hlimφ hlimη
  · intro j
    have hi := (rieszInterior_integrable_and_cap_error p C ((μ j).restrict (ball a R))
      (globalGrowth_restrict (p + 1) C (μ j) (hg j) (ball a R)) e φ Lφ Bφ hφ hBφ 1 zero_lt_one).1
    change Integrable (fun q => rieszInteriorIntegrand (p + 1) e φ q) _ at hi
    simpa only [heq] using! hi
  · intro j
    have hi := (rieszInterior_integrable_and_cap_error p C ((μ j).restrict (ball a R))
      (globalGrowth_restrict (p + 1) C (μ j) (hg j) (ball a R)) e η Lη Bη hη hBη 1 zero_lt_one).1
    change Integrable (fun q => rieszInteriorIntegrand (p + 1) e η q) _ at hi
    simpa only [heq] using! hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactRieszPairingTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported pairing tails

Global upper growth bounds the integral of a bounded, compactly supported test
function. This gives an explicit constant for the inverse-radius error between
the scalar Riesz pairing and its interior product-measure integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compact_supported_abs_integral_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (H : ℝ) (hH : 0 ≤ H)
    (φ : Ambient d → ℝ) (hφ : Continuous φ) (B : ℝ≥0)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) (hs : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    Integrable φ μ ∧ (∫ x, |φ x| ∂μ) ≤ (B : ℝ) * (C * (H + 1) ^ m) := by
  let := hg.finite_on_compacts
  have hcomp : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall a H)
    intro x hx
    by_contra hn
    exact hx (hs x hn)
  have hi := hφ.integrable_of_hasCompactSupport (μ := μ) hcomp
  have hzero : ∀ x ∉ ball a (H + 1), |φ x| = 0 := by
    intro x hx
    have hz : φ x = 0 := by
      by_contra hn
      exact hx ((hs x hn).trans_lt (by linarith : H < H + 1))
    rw [hz, abs_zero]
  have hR : 0 < H + 1 := by positivity
  have hfinite : μ (ball a (H + 1)) < ∞ := (hg.2 a _ hR).trans_lt ENNReal.ofReal_lt_top
  have hmass : μ.real (ball a (H + 1)) ≤ C * (H + 1) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le _)) (hg.2 a _ hR)
  refine ⟨hi, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ = ‖∫ x in ball a (H + 1), |φ x| ∂μ‖ :=
      (Real.norm_of_nonneg (integral_nonneg fun x => abs_nonneg _)).symm
    _ ≤ (B : ℝ) * μ.real (ball a (H + 1)) :=
      norm_setIntegral_le_of_norm_le_const hfinite fun x _ => by
        simpa only [Real.norm_eq_abs, abs_abs] using! hB x
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass B.coe_nonneg

theorem compactRieszTailConstant_nonneg (m : ℕ) (C : ℝ) {d : ℕ} (e : Ambient d)
    (H : ℝ) (B : ℝ≥0) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    0 ≤ compactRieszTailConstant m C e H B := by
  unfold compactRieszTailConstant
  positivity

theorem rieszScalarPairing_interior_tail_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (hs : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    |rieszScalarPairing m μ a R e φ - (1 / 2 : ℝ) *
      (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R)))| ≤
      compactRieszTailConstant m C e H B / R := by
  have hC : 0 ≤ C := hg.1
  obtain ⟨hi, hmass⟩ := compact_supported_abs_integral_bound m C μ hg a H hH φ hφ.continuous B hB hs
  have hlocal : (∫ x in ball a R, |φ x| ∂μ) ≤ (B : ℝ) * (C * (H + 1) ^ m) :=
    (setIntegral_le_integral hi.abs (Eventually.of_forall fun x => abs_nonneg (φ x))).trans hmass
  have hb := rieszFarIntegrand_integral_abs_bound m C μ hg e φ L hφ a H R hH hR hHR hs
  have hf := abs_integral_le_integral_abs.trans hb
  unfold rieszScalarPairing
  dsimp only
  rw [add_sub_cancel_left]
  calc
    _ ≤ _ := hf
    _ ≤ (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
        (‖e‖ * H * ((B : ℝ) * (C * (H + 1) ^ m))) * (2 * (C * 2 ^ m / R)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by unfold compactRieszTailConstant; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LimitRieszInteriorOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interior bounds from vanishing Riesz oscillation

Mean-corrected compactly supported tests transfer scalar oscillation estimates along
a compact-test convergent sequence of measures. As the oscillation tends to zero on
expanding balls, convergence of the interior pairing leaves only the quantitative
tail bound for the limit measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem limit_rieszInterior_bound_of_oscillation {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, SFinite (μ j)]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν)
    (a : Ambient d) (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (v j))
    (e : Ambient d) (he : ‖e‖ ≤ 1)
    (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsφ : ∀ x, φ x ≠ 0 → dist x a ≤ H) (hsη : ∀ x, η x ≠ 0 → dist x a ≤ H)
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0) :
    |(1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R)))| ≤
      compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R := by
  let (j : ℕ) := (hg j).finite_on_compacts
  let ξ := fun j => meanCorrection (μ j) φ η
  have hadm := (compact_meanCorrection_admissible μ ν hweak φ η Lφ Lη Bφ Bη
    hφ hη hcφ hcη hBφ hBη hmean hbump).2
  have hsξ : ∀ j x, ξ j x ≠ 0 → dist x a ≤ H := by
    intro j x hx
    by_contra hn
    have hzφ : φ x = 0 := by by_contra hne; exact hn (hsφ x hne)
    have hzη : η x = 0 := by by_contra hne; exact hn (hsη x hne)
    exact hx (by simp only [ξ, meanCorrection, hzφ, hzη, mul_zero, sub_zero])
  have hIlim := (compactTestConvergence_corrected_rieszInterior_ball p C D μ ν hg hgν
    hweak a R hR hboundary hmass e φ η Lφ Lη Bφ Bη hφ hη hcφ hcη hBφ hBη hmean hbump).const_mul
      (1 / 2 : ℝ)
  let err := fun j => (((Lφ + Lη : ℝ≥0) : ℝ) + 1) * v j
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [mul_zero] using! hv.const_mul (((Lφ + Lη : ℝ≥0) : ℝ) + 1)
  have hbound : ∀ᶠ j in atTop,
      |(1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e (ξ j) q
        ∂((μ j).restrict (ball a R)).prod ((μ j).restrict (ball a R)))| ≤
        err j + compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R := by
    filter_upwards [hadm, hA.eventually (eventually_gt_atTop H)] with j hj hjA
    have hp := oscillation_bound_for_localized_test p C (μ j) (hg j) a (A j) (v j)
      (hH.trans_lt hjA) (hosc j) e he (ξ j) (Lφ + Lη) hj.2.2.2.1 H R hH hR hHR hjA
      (hsξ j) hj.2.2.1
    have ht := rieszScalarPairing_interior_tail_bound (p + 1) C (μ j) (hg j) a H R hH hR hHR
      e (ξ j) (Lφ + Lη) (Bφ + Bη) hj.2.2.2.1 hj.2.2.2.2.1 (hsξ j)
    let P := rieszScalarPairing (p + 1) (μ j) a R e (ξ j)
    let I := (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e (ξ j) q
      ∂((μ j).restrict (ball a R)).prod ((μ j).restrict (ball a R)))
    have htri : |I| ≤ |P| + |P - I| := by
      have h := abs_add_le P (-(P - I))
      rw [show P + -(P - I) = I by ring, abs_neg] at h
      exact h
    exact htri.trans (add_le_add hp ht)
  have hright : Tendsto
      (fun j => err j + compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R) atTop
      (𝓝 (compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R)) := by
    simpa only [zero_add] using! herr.add_const (compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R)
  exact le_of_tendsto_of_tendsto hIlim.abs hright hbound

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_LimitReflectionlessTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem limit_rieszScalarPairing_zero_of_oscillation {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, SFinite (μ j)] [SFinite ν]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν)
    (a : Ambient d) (ha : a ∈ ν.support) (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (v j))
    (e : Ambient d) (he : ‖e‖ ≤ 1)
    (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsφ : ∀ x, φ x ≠ 0 → dist x a ≤ H) (hsη : ∀ x, η x ≠ 0 → dist x a ≤ H)
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0) :
    rieszScalarPairing (p + 1) ν a R e φ = 0 := by
  let K₁ := compactRieszTailConstant (p + 1) C e H (Bφ + Bη)
  let K₂ := compactRieszTailConstant (p + 1) D e H Bφ
  let K := K₁ + K₂
  have hK₁ : 0 ≤ K₁ := compactRieszTailConstant_nonneg (p + 1) C e H (Bφ + Bη) (hg 0).1 hH
  have hK₂ : 0 ≤ K₂ := compactRieszTailConstant_nonneg (p + 1) D e H Bφ hgν.1 hH
  have hK : 0 ≤ K := add_nonneg hK₁ hK₂
  let P := rieszScalarPairing (p + 1) ν a R e φ
  by_contra hn
  have hP : 0 < |P| := abs_pos.mpr hn
  let T₀ := max (2 * H) ((K + 1) / |P|)
  obtain ⟨T, hTinterval, hboundary⟩ := exists_null_frontier_thickening ν {a}
    (show T₀ < T₀ + 1 by linarith)
  simp only [thickening_singleton] at hboundary
  have hHT : 2 * H ≤ T := (le_max_left _ _).trans hTinterval.1.le
  have hTlarge : (K + 1) / |P| < T := (le_max_right _ _).trans_lt hTinterval.1
  have hT : 0 < T := (div_pos (by positivity : 0 < K + 1) hP).trans hTlarge
  have hmass : ν (ball a T) ≠ 0 :=
    ((ν.mem_support_iff_forall a).mp ha (ball a T) (ball_mem_nhds a hT)).ne'
  have hinner := limit_rieszInterior_bound_of_oscillation p C D μ ν hg hgν hweak a A v hA hv hosc
    e he φ η Lφ Lη Bφ Bη hφ hη hcφ hcη hBφ hBη H T hH hT hHT hsφ hsη hmean hbump
    hboundary hmass
  have htail := rieszScalarPairing_interior_tail_bound (p + 1) D ν hgν a H T hH hT hHT
    e φ Lφ Bφ hφ hBφ hsφ
  have heq := rieszScalarPairing_localization_independent p D ν hgν e φ Lφ hφ
    a a H H R T hH hH hR hT hHR hHT hsφ hsφ hmean
  let I := (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q
    ∂(ν.restrict (ball a T)).prod (ν.restrict (ball a T)))
  have hb : |P| ≤ K / T := by
    change |rieszScalarPairing (p + 1) ν a R e φ| ≤ _
    rw [heq]
    calc
      _ ≤ |rieszScalarPairing (p + 1) ν a T e φ - I| + |I| := by
        simpa only [sub_add_cancel] using! abs_add_le
          (rieszScalarPairing (p + 1) ν a T e φ - I) I
      _ ≤ K₂ / T + K₁ / T := add_le_add htail hinner
      _ = _ := by dsimp only [K] <;> ring
  have hstrict : K / T < |P| := by
    apply (div_lt_iff₀ hT).mpr
    have h := (div_lt_iff₀ hP).mp hTlarge
    nlinarith
  exact (not_lt_of_ge hb) hstrict

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ScaledBallBumps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scaled ball bumps give compactly supported Lipschitz cutoffs. A lower ball-mass bound
allows normalization to integral one with an explicit scale-dependent Lipschitz bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem scaledBallBump_bounds {d : ℕ} (a : Ambient d) (r : ℝ) (x : Ambient d) :
    0 ≤ scaledBallBump a r x ∧ scaledBallBump a r x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem scaledBallBump_lipschitz {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    LipschitzWith (Real.toNNReal r⁻¹) (scaledBallBump a r) := by
  have h : LipschitzWith (Real.toNNReal r⁻¹)
      (fun x : Ambient d => r⁻¹ * dist x a) := by
    have heq : ‖r⁻¹‖₊ = Real.toNNReal r⁻¹ := by
      apply NNReal.coe_injective
      simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
        Real.coe_toNNReal r⁻¹ (inv_nonneg.mpr hr.le)]
    simpa only [mul_one, heq] using! lipschitz_const_mul_real (LipschitzWith.dist_left a) r⁻¹
  have hsub : LipschitzWith (Real.toNNReal r⁻¹)
      (fun x : Ambient d => 2 - r⁻¹ * dist x a) := by
    simpa only [zero_add] using! (LipschitzWith.const (2 : ℝ)).sub h
  exact (hsub.const_min 1).const_max 0

theorem scaledBallBump_eq_one {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : dist x a ≤ r) : scaledBallBump a r x = 1 := by
  have hb : r⁻¹ * dist x a ≤ 1 := by
    calc
      _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hr.le)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  simp only [scaledBallBump, min_eq_left (by linarith : (1 : ℝ) ≤ 2 - r⁻¹ * dist x a),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem scaledBallBump_support_bound {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : scaledBallBump a r x ≠ 0) : dist x a ≤ 2 * r := by
  by_contra hn
  have hdist : 2 * r < dist x a := lt_of_not_ge hn
  have hb : 2 < r⁻¹ * dist x a := by
    calc
      (2 : ℝ) = r⁻¹ * (2 * r) := by field_simp
      _ < _ := mul_lt_mul_of_pos_left hdist (inv_pos.mpr hr)
  exact hx (max_eq_left ((min_le_right _ _).trans (by linarith : 2 - r⁻¹ * dist x a ≤ 0)))

theorem scaledBallBump_hasCompactSupport {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (scaledBallBump a r) := by
  apply HasCompactSupport.intro (isCompact_closedBall a (2 * r))
  intro x hx
  by_contra hn
  exact hx (scaledBallBump_support_bound a r hr x hn)

theorem scaledBallBump_integral_lower {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    μ.real (ball a r) ≤ ∫ x, scaledBallBump a r x ∂μ := by
  have hi := (scaledBallBump_lipschitz a r hr).continuous.integrable_of_hasCompactSupport
    (μ := μ) (scaledBallBump_hasCompactSupport a r hr)
  have hs : (∫ x in ball a r, scaledBallBump a r x ∂μ) = μ.real (ball a r) := by
    calc
      _ = ∫ _x in ball a r, (1 : ℝ) ∂μ := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        exact scaledBallBump_eq_one a r hr x hx.le
      _ = _ := by simp only [setIntegral_const, smul_eq_mul, mul_one]
  rw [← hs]
  exact setIntegral_le_integral hi (Eventually.of_forall fun x => (scaledBallBump_bounds a r x).1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_LimitReflectionlessness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reflectionlessness of limits with vanishing oscillation

The scalar Riesz pairing scales linearly in its direction. This extends the
normalized-direction limit test to arbitrary directions and yields scalar
reflectionlessness when compact-test convergence and vanishing oscillation hold.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem rieszScalarPairing_smul_direction {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (R c : ℝ) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing m μ a R (c • e) φ = c * rieszScalarPairing m μ a R e φ := by
  have hi : rieszInteriorIntegrand m (c • e) φ = fun q => c * rieszInteriorIntegrand m e φ q := by
    funext q
    unfold rieszInteriorIntegrand
    rw [real_inner_smul_left]
    ring
  have hf : rieszFarIntegrand m (c • e) φ a = fun q => c * rieszFarIntegrand m e φ a q := by
    funext q
    unfold rieszFarIntegrand
    rw [real_inner_smul_left]
    ring
  unfold rieszScalarPairing
  dsimp only
  rw [hi, hf, integral_const_mul, integral_const_mul]
  ring

theorem limit_scalarReflectionlessAt_of_oscillation {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, SFinite (μ j)] [SFinite ν]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν)
    (a : Ambient d) (ha : a ∈ ν.support) (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (v j)) :
    ScalarReflectionlessAt (p + 1) ν a := by
  let := hgν.finite_on_compacts
  intro e φ L H R hφ hH hR hHR hs hmean
  have hcomp : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall a H)
    intro x hx
    by_contra hn
    exact hx (hs x hn)
  let B : ℝ≥0 := Real.toNNReal ((L : ℝ) * H + |φ a|)
  have hB : ∀ x, |φ x| ≤ (B : ℝ) := by
    intro x
    by_cases hx : φ x = 0
    · rw [hx, abs_zero]
      exact B.coe_nonneg
    have hd : |φ x - φ a| ≤ (L : ℝ) * H := by
      have h := hφ.dist_le_mul x a
      rw [Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hs x hx) L.coe_nonneg)
    have ht := abs_add_le (φ x - φ a) (φ a)
    rw [sub_add_cancel] at ht
    exact (ht.trans (add_le_add hd le_rfl)).trans (Real.le_coe_toNNReal _)
  let η := scaledBallBump a 1
  have hη : LipschitzWith 1 η := by
    simpa only [inv_one, Real.toNNReal_one] using! scaledBallBump_lipschitz a 1 zero_lt_one
  have hcη : HasCompactSupport η := scaledBallBump_hasCompactSupport a 1 zero_lt_one
  have hBη : ∀ x, |η x| ≤ (1 : ℝ≥0) := by
    intro x
    change |scaledBallBump a 1 x| ≤ 1
    rw [abs_of_nonneg (scaledBallBump_bounds a 1 x).1]
    exact (scaledBallBump_bounds a 1 x).2
  have hpos : 0 < ν.real (ball a 1) := by
    apply ENNReal.toReal_pos_iff.mpr
    exact ⟨(ν.mem_support_iff_forall a).mp ha (ball a 1) (ball_mem_nhds a zero_lt_one),
      (hgν.2 a 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top⟩
  have hbump : (∫ x, η x ∂ν) ≠ 0 :=
    (hpos.trans_le (scaledBallBump_integral_lower ν a 1 zero_lt_one)).ne'
  let J := max H 2
  have hJ : 0 ≤ J := hH.trans (le_max_left _ _)
  have hsφ : ∀ x, φ x ≠ 0 → dist x a ≤ J := fun x hx => (hs x hx).trans (le_max_left _ _)
  have hsη : ∀ x, η x ≠ 0 → dist x a ≤ J := by
    intro x hx
    have h := scaledBallBump_support_bound a 1 zero_lt_one x hx
    have hb : dist x a ≤ 2 := by simpa only [mul_one] using! h
    exact hb.trans (le_max_right _ _)
  have hunit : ∀ u : Ambient d, ‖u‖ ≤ 1 → rieszScalarPairing (p + 1) ν a R u φ = 0 := by
    intro u hu
    have hz := limit_rieszScalarPairing_zero_of_oscillation p C D μ ν hg hgν hweak a ha A v hA hv hosc
      u hu φ η L 1 B 1 hφ hη hcomp hcη hB hBη J (2 * J + 1) hJ (by positivity) (by linarith)
      hsφ hsη hmean hbump
    have heq := rieszScalarPairing_localization_independent p D ν hgν u φ L hφ
      a a H J R (2 * J + 1) hH hJ hR (by positivity) hHR (by linarith) hs hsφ hmean
    exact heq.trans hz
  let c := ‖e‖ + 1
  have hc : 0 < c := by dsimp only [c] <;> positivity
  have hnorm : ‖c⁻¹ • e‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      _ = ‖e‖ / c := by ring
      _ ≤ 1 := (div_le_one hc).mpr (by dsimp only [c] <;> linarith)
  have hz := hunit (c⁻¹ • e) hnorm
  have heq := rieszScalarPairing_smul_direction (p + 1) ν a R c (c⁻¹ • e) φ
  rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hz, mul_zero] at heq
  exact heq

theorem ScalarReflectionlessAt.change_center {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (a b : Ambient d) (h : ScalarReflectionlessAt (p + 1) μ a) :
    ScalarReflectionlessAt (p + 1) μ b := by
  intro e φ L H R hφ hH hR hHR hs hmean
  let J := H + dist b a
  have hJ : 0 ≤ J := add_nonneg hH dist_nonneg
  have hsA : ∀ x, φ x ≠ 0 → dist x a ≤ J := by
    intro x hx
    have ht := dist_triangle x b a
    have hb := hs x hx
    dsimp only [J]
    linarith
  have hz := h e φ L J (2 * J + 1) hφ hJ (by positivity) (by linarith) hsA hmean
  have heq := rieszScalarPairing_localization_independent p C μ hg e φ L hφ
    a b J H (2 * J + 1) R hJ hH (by positivity) hR (by linarith) hHR hsA hs hmean
  exact heq.symm.trans hz

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_DyadicReflectionlessMeasureLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reflectionless limits of dyadic planar approximations

The dyadic planar compactness construction supplies a limit measure and its
geometric data. Vanishing scalar oscillation makes this limit reflectionless at
the origin, and invariance under changing the center extends this to every center.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_reflectionless_measure_limit {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop) (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (v j)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧
        GlobalUpperGrowth (p + 1) (G * 2 ^ (p + 1)) ν ∧
        (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤ ν (ball x r)) ∧
        ν.support ⊆ (Llim.toLinearMap.range : Set (Ambient d)) ∧
        (0 : Ambient d) ∈ ν.support ∧
        (∃ f : Ambient (p + 1) → ℝ, Measurable f ∧
          (∀ x, 0 ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) ∧
          ((volume : Measure (Ambient (p + 1))).withDensity
            (fun x => ENNReal.ofReal (f x))).map Llim = ν) ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
            normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) ∧
        ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c := by
  obtain ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist, hmem, hsource⟩ :=
    exists_dyadic_planar_measure_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment
  let := hfinite
  have hreflect : ScalarReflectionlessAt (p + 1) ν 0 :=
    limit_scalarReflectionlessAt_of_oscillation p G (G * 2 ^ (p + 1))
      (fun j => μ (ρ j)) ν (fun j => hg (ρ j)) hgν hweak 0 horigin
      (fun j => A (ρ j)) (fun j => v (ρ j)) (hA.comp hρ.tendsto_atTop)
      (hv.comp hρ.tendsto_atTop) (fun j => hosc (ρ j))
  exact ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist, hmem, hsource,
    fun c => hreflect.change_center p (G * 2 ^ (p + 1)) ν hgν 0 c⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_DyadicFullPlanarMeasureLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_full_planar_measure_limit_oai {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop) (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (v j)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧
        GlobalUpperGrowth (p + 1) (G * 2 ^ (p + 1)) ν ∧
        (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤ ν (ball x r)) ∧
        ν.support = (Llim.toLinearMap.range : Set (Ambient d)) ∧
        (0 : Ambient d) ∈ ν.support ∧
        (∃ f : Ambient (p + 1) → ℝ, Measurable f ∧
          (∀ x, intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) ≤ f x ∧
            f x ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) ∧
          ((volume : Measure (Ambient (p + 1))).withDensity
            (fun x => ENNReal.ofReal (f x))).map Llim = ν) ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
            normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) ∧
        ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c := by
  obtain ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, _hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist, hmem, hsource, hreflect⟩ :=
    exists_dyadic_reflectionless_measure_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A v hA hv hosc
  have hC' : 0 < C * 4 ^ (p + 1) := mul_pos hC (pow_pos (by norm_num) _)
  have hfull := planar_full_support_of_reflectionless Llim ν hne hsupport
    (C * 4 ^ (p + 1)) (G * 2 ^ (p + 1)) hC' hgν hlowerν (fun c _ => hreflect c)
  have hlowerμ := planarPullbackMeasure_lower Llim ν hsupport (C * 4 ^ (p + 1)) hlowerν
  have hlowerAll : ∀ x : Ambient (p + 1), ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤
        planarPullbackMeasure Llim ν (ball x r) := by
    intro x r hr
    apply hlowerμ x _ r hr
    rw [hfull.1]
    exact mem_univ x
  obtain ⟨f, hm, hb, heq⟩ := exists_two_sided_intrinsic_density (p + 1)
    (C * 4 ^ (p + 1)) (G * 2 ^ (p + 1)) (planarPullbackMeasure Llim ν) hC'
    (planarPullbackMeasure_growth Llim ν hsupport (G * 2 ^ (p + 1)) hgν) hlowerAll
  have hpush : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map Llim = ν := by
    rw [heq]
    exact planarPullbackMeasure_recover Llim ν hsupport
  exact ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hfull.2,
    horigin, ⟨f, hm, hb, hpush⟩, ha, hLlim, hcenter, hL, horth, hsplit, hdist,
    hmem, hsource, hreflect⟩

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit_oai := @OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit_oai
