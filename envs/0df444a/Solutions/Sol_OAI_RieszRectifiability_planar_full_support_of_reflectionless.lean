-- Prove2me | solution 1 for OAI.RieszRectifiability.planar_full_support_of_reflectionless
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:30.866535+00:00
-- url     : https://prove2.me/submissions/81c85e40-0592-4d64-80cc-be8f4633d393

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

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

theorem planarPullbackMeasure_ne_zero {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (hne : ν ≠ 0) : planarPullbackMeasure L ν ≠ 0 := by
  intro hz
  apply hne
  rw [← planarPullbackMeasure_recover L ν hs, hz, Measure.map_zero]

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

theorem intrinsic_growth_absolutelyContinuous (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient n)) (hg : GlobalUpperGrowth n C μ) :
    μ ≪ (volume : Measure (Ambient n)) :=
  (intrinsic_growth_le_volume n C μ hg).absolutelyContinuous.trans
    Measure.smul_absolutelyContinuous

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_IntrinsicHyperplaneNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem intrinsic_growth_not_supported_in_hyperplane (n : ℕ)
    (μ : Measure (Ambient n)) (G : ℝ) (hg : GlobalUpperGrowth n G μ) (hμ : μ ≠ 0)
    (e : Ambient n) (he : e ≠ 0) :
    ¬ (∀ x ∈ μ.support, inner ℝ e x = 0) := by
  intro hside
  let S : Submodule ℝ (Ambient n) := (innerSL ℝ e).ker
  have hproper : S ≠ ⊤ := by
    intro htop
    have hemem : e ∈ S := by rw [htop]; trivial
    have hinner : inner ℝ e e = 0 := hemem
    exact he (inner_self_eq_zero.mp hinner)
  have hvol : (volume : Measure (Ambient n)) (S : Set (Ambient n)) = 0 :=
    Measure.addHaar_submodule volume S hproper
  have hnull : μ (S : Set (Ambient n)) = 0 :=
    intrinsic_growth_absolutelyContinuous n G μ hg hvol
  have hsnull : μ μ.support = 0 := measure_mono_null (fun x hx => hside x hx) hnull
  have huniv : μ univ = 0 := by
    apply le_antisymm _ bot_le
    calc
      μ univ = μ (μ.support ∪ μ.supportᶜ) := by rw [union_compl_self]
      _ ≤ μ μ.support + μ μ.supportᶜ := measure_union_le _ _
      _ = 0 := by rw [hsnull, μ.measure_compl_support, zero_add]
  exact hμ (Measure.measure_univ_eq_zero.mp huniv)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EnergyFromTruncations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

theorem nonnegative_integrable_of_exhaustion {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (s : ℕ → Set X) (hs : ∀ k, MeasurableSet (s k)) (hmono : Monotone s)
    (hcover : Function.support f ⊆ ⋃ k, s k)
    (hI : ∀ k, IntegrableOn f (s k) μ) (B : ℝ)
    (hB : ∀ k, (∫ x in s k, f x ∂μ) ≤ B) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hpos
  have hfull : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x in ⋃ k, s k, ENNReal.ofReal (f x) ∂μ := by
    rw [← lintegral_indicator (MeasurableSet.iUnion hs)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ⋃ k, s k
    · rw [indicator_of_mem hx]
    · have hfx : f x = 0 := by
        by_contra h
        exact hx (hcover h)
      rw [indicator_of_notMem hx, hfx, ENNReal.ofReal_zero]
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B := by
    rw [hfull, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    apply iSup_le
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hI k) (Filter.Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have hfin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ :=
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp hfin
  refine ⟨hint, ?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg hpos).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hbound

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

theorem lipschitz_bounded_product_real {f g : X → ℝ} {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  calc
    dist (f x * g x) (f y * g y) =
        |f x * (g x - g y) + (f x - f y) * g y| := by
      rw [Real.dist_eq]
      congr 1
      ring
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using! abs_add_le
        (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) +
        ((Kf : ℝ) * dist x y) * (Bg : ℝ) := by
      exact add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
        (mul_le_mul hf' (hBg y) (abs_nonneg _) (by positivity))
    _ = ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem inverseDistancePow_exterior_integral_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    (∫ y in {y | r < dist x y}, inverseDistancePow (m + 1) x y ∂μ) ≤ 2 * (C * 2 ^ m / r) := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ m / r) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in dyadicAnnulus x r k, ‖inverseDistancePow (m + 1) x y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => inverseDistancePow_annular_integral_bound m C μ hg x r hr k) hgeo
  have hiu : IntegrableOn (inverseDistancePow (m + 1) x) (⋃ k, dyadicAnnulus x r k) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun k => inverseDistancePow_integrableOn_annulus m (m + 1) C μ hg x r hr k) hs
  have hsub := exterior_subset_iUnion_dyadicAnnulus x r hr
  calc
    _ ≤ ∫ y in ⋃ k, dyadicAnnulus x r k, inverseDistancePow (m + 1) x y ∂μ :=
      setIntegral_mono_set hiu (Filter.Eventually.of_forall fun y => inverseDistancePow_nonneg _ _ _)
        (Filter.Eventually.of_forall fun y hy => hsub hy)
    _ = ∑' k, ∫ y in dyadicAnnulus x r k, ‖inverseDistancePow (m + 1) x y‖ ∂μ := by
      rw [integral_iUnion (dyadicAnnulus_measurable x r) (dyadicAnnulus_disjoint x r hr) hiu]
      simp only [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    _ ≤ ∑' k : ℕ, (C * 2 ^ m / r) * (1 / 2 : ℝ) ^ k :=
      Summable.tsum_le_tsum (fun k => inverseDistancePow_annular_integral_bound m C μ hg x r hr k)
        hs hgeo
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num
      ring

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedRegionTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem radialUnitCutoff_bounds {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d) :
    0 ≤ radialUnitCutoff a R x ∧ radialUnitCutoff a R x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem radialUnitCutoff_eq_one {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : dist x a ≤ R) : radialUnitCutoff a R x = 1 := by
  have h : (1 : ℝ) ≤ R + 1 - dist x a := by linarith
  simp only [radialUnitCutoff, min_eq_left h, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem radialUnitCutoff_support_bound {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : radialUnitCutoff a R x ≠ 0) : dist x a ≤ R + 1 := by
  by_contra h
  have hneg : R + 1 - dist x a < 0 := by linarith
  have hmin : min 1 (R + 1 - dist x a) ≤ 0 := (min_le_right _ _).trans hneg.le
  exact hx (max_eq_left hmin)

theorem radialUnitCutoff_lipschitz {d : ℕ} (a : Ambient d) (R : ℝ) :
    LipschitzWith 1 (radialUnitCutoff a R) := by
  have h : LipschitzWith 1 (fun x : Ambient d => R + 1 - dist x a) := by
    simpa using! (LipschitzWith.const (R + 1)).sub (LipschitzWith.dist_left a)
  exact (h.const_min 1).const_max 0

theorem radialUnitCutoff_hasCompactSupport {d : ℕ} (a : Ambient d) (R : ℝ) :
    HasCompactSupport (radialUnitCutoff a R) := by
  apply HasCompactSupport.intro (isCompact_closedBall a (R + 1))
  intro x hx
  by_contra h
  exact hx (radialUnitCutoff_support_bound a R x h)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_PlaneHeightDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Function SchwartzMap

theorem coordinatePlaneMeasure_affine_eq_map {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    coordinatePlaneMeasure (affinePlaneSection a L) =
      Measure.map (fun u : Ambient n => a + L u) volume := by
  change Measure.map ((fun u : Ambient n => a + L u) ∘ WithLp.toLp 2) volume = _
  rw [← (PiLp.volume_preserving_toLp (Fin n)).map_eq,
    Measure.map_map (by fun_prop) (PiLp.volume_preserving_toLp (Fin n)).measurable]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneTestExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact ambient extensions of plane tests

An adjoint coordinate projection extends a test function from an affine plane.
A radial cutoff makes the extension compactly supported while retaining its
values on the plane and explicit uniform and Lipschitz bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Function SchwartzMap
open scoped NNReal ContDiff

theorem exists_compact_ambient_plane_test {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (g : Ambient n → ℝ)
    (hc : HasCompactSupport g) (K B : ℝ≥0) (hg : LipschitzWith K g)
    (hB : ∀ u, |g u| ≤ (B : ℝ)) :
    ∃ (φ : Ambient d → ℝ) (J : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith J φ ∧ (∀ x, |φ x| ≤ (B : ℝ)) ∧
      (∀ u, φ (a + L u) = g u) ∧
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) ∧
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = ∫ u, g u := by
  obtain ⟨R, _, hR⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Ambient n)
  let π : Ambient d → Ambient n := fun x => L.toContinuousLinearMap.adjoint (x - a)
  have hπ : LipschitzWith ‖L.toContinuousLinearMap.adjoint‖₊ π := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using!
      L.toContinuousLinearMap.adjoint.lipschitz.dist_le_mul (x - a) (y - a)
  have hleft : ∀ u, π (a + L u) = u := by
    intro u
    change L.toContinuousLinearMap.adjoint ((a + L u) - a) = u
    rw [add_sub_cancel_left]
    exact DFunLike.congr_fun L.adjoint_comp_self u
  let χ := radialUnitCutoff a R
  let φ : Ambient d → ℝ := fun x => χ x * g (π x)
  have hχ : LipschitzWith 1 χ := radialUnitCutoff_lipschitz a R
  have hχB : ∀ x, |χ x| ≤ (1 : ℝ≥0) := by
    intro x
    rw [abs_of_nonneg (radialUnitCutoff_bounds a R x).1]
    exact (radialUnitCutoff_bounds a R x).2
  have hφ : LipschitzWith (1 * (K * ‖L.toContinuousLinearMap.adjoint‖₊) + 1 * B) φ :=
    lipschitz_bounded_product_real hχ (hg.comp hπ) hχB (fun x => hB (π x))
  have hext : ∀ u, φ (a + L u) = g u := by
    intro u
    change χ (a + L u) * g (π (a + L u)) = g u
    rw [hleft]
    by_cases hu : g u = 0
    · rw [hu, mul_zero]
    have hnorm : ‖u‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using! hR (subset_tsupport g hu)
    have hχone : χ (a + L u) = 1 := by
      apply radialUnitCutoff_eq_one
      simpa only [dist_eq_norm, add_sub_cancel_left, L.norm_map] using! hnorm
    rw [hχone, one_mul]
  refine ⟨φ, _, (radialUnitCutoff_hasCompactSupport a R).mul_right, hφ, ?_, hext, ?_, ?_⟩
  · intro x
    calc
      |φ x| = |χ x| * |g (π x)| := abs_mul _ _
      _ ≤ 1 * (B : ℝ) := mul_le_mul (hχB x) (hB (π x)) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · rw [coordinatePlaneMeasure_affine_eq_map]
    apply (integrable_map_measure (μ := (volume : Measure (Ambient n))) hφ.continuous.aestronglyMeasurable
      (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))).mpr
    have hIg : Integrable g (volume : Measure (Ambient n)) :=
      hg.continuous.integrable_of_hasCompactSupport hc
    simpa only [Function.comp_def, hext] using! hIg
  · rw [coordinatePlaneMeasure_affine_eq_map,
      integral_map (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))
        hφ.continuous.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall hext)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BlowupMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rescaled measures and their growth bounds

The blowup at a center and positive scale pushes a measure forward by translation
and dilation, then normalizes by the scale to the power `n`. Exact ball formulas
transport the support and preserve global upper and lower growth estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem blowup_preimage_ball {d : ℕ} (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' ball x R = ball (a + r • x) (r * R) := by
  ext y
  have hvec : y - (a + r • x) = r • (r⁻¹ • (y - a) - x) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hdist : dist y (a + r • x) = r * dist (r⁻¹ • (y - a)) x := by
    simp only [dist_eq_norm]
    rw [hvec, norm_smul, Real.norm_of_nonneg hr.le]
  simp only [mem_preimage, mem_ball, hdist]
  exact (mul_lt_mul_iff_right₀ hr).symm

theorem blowupMeasure_ball {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    blowupMeasure n μ a r (ball x R) =
      ENNReal.ofReal ((r ^ n)⁻¹) * μ (ball (a + r • x) (r * R)) := by
  have hblowup : Measurable (fun y : Ambient d => r⁻¹ • (y - a)) :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  rw [blowupMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hblowup measurableSet_ball, blowup_preimage_ball a x r R hr]

theorem blowupMeasure_growth {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r C : ℝ) (hr : 0 < r) (hg : GlobalUpperGrowth n C μ) :
    GlobalUpperGrowth n C (blowupMeasure n μ a r) := by
  refine ⟨hg.1, ?_⟩
  intro x R hR
  rw [blowupMeasure_ball n μ a x r R hr]
  calc
    _ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal (C * (r * R) ^ n) :=
      mul_le_mul_right (hg.2 (a + r • x) (r * R) (by positivity)) _
    _ = ENNReal.ofReal (C * R ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (r ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp

theorem blowupMeasure_support_iff {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r : ℝ) (hr : 0 < r) :
    x ∈ (blowupMeasure n μ a r).support ↔ a + r • x ∈ μ.support := by
  rw [Metric.nhds_basis_ball.mem_measureSupport, Metric.nhds_basis_ball.mem_measureSupport]
  have hcoef : 0 < ENNReal.ofReal ((r ^ n)⁻¹) := ENNReal.ofReal_pos.mpr (by positivity)
  constructor
  · intro hx R hR
    have h := hx (R / r) (by positivity)
    rw [blowupMeasure_ball n μ a x r (R / r) hr,
      mul_div_cancel₀ R hr.ne'] at h
    exact (ENNReal.mul_pos_iff.mp h).2
  · intro hx R hR
    rw [blowupMeasure_ball n μ a x r R hr]
    exact ENNReal.mul_pos_iff.mpr ⟨hcoef, hx (r * R) (by positivity)⟩

theorem blowupMeasure_origin_mem_support {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (ha : a ∈ μ.support) :
    (0 : Ambient d) ∈ (blowupMeasure n μ a r).support := by
  apply (blowupMeasure_support_iff n μ a 0 r hr).mpr
  simpa only [smul_zero, add_zero] using! ha

theorem blowupMeasure_lower_global {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r C : ℝ) (hr : 0 < r)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R)) :
    ∀ x ∈ (blowupMeasure n μ a r).support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ blowupMeasure n μ a r (ball x R) := by
  intro x hx R hR
  rw [blowupMeasure_ball n μ a x r R hr]
  have h := hlower (a + r • x) ((blowupMeasure_support_iff n μ a x r hr).mp hx)
    (r * R) (by positivity)
  calc
    _ = ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal ((r * R) ^ n / C) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (r ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp
    _ ≤ _ := mul_le_mul_right h _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ball-mass bounds through compact test functions

Compactly supported continuous cutoffs compare test integrals with ball masses from above
and below. These comparisons pass uniform growth bounds through convergence against
compact test functions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compact_test_integral_le_ball_mass {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ)) (a : Ambient d) (R : ℝ)
    (hf : ∀ x, f x ≤ 1) (hz : ∀ x, x ∉ ball a R → f x = 0) :
    (∫ x, f x ∂μ) ≤ μ.real (ball a R) := by
  have : IsFiniteMeasure (μ.restrict (ball a R)) := isFiniteMeasure_restrict.mpr
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a R).measure_lt_top).ne
  have hi : Integrable ((ball a R).indicator (fun _ : Ambient d => (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrable_const 1)
  have h := integral_mono (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) hi
    (fun x => by
      by_cases hx : x ∈ ball a R
      · simpa only [indicator_of_mem hx] using! hf x
      · simpa only [indicator_of_notMem hx] using! (hz x hx).le)
  simpa only [integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ, mul_one] using! h

theorem ball_mass_le_compact_test_integral {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ)) (a : Ambient d) (r : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hone : ∀ x ∈ ball a r, f x = 1) :
    μ.real (ball a r) ≤ ∫ x, f x ∂μ := by
  have : IsFiniteMeasure (μ.restrict (ball a r)) := isFiniteMeasure_restrict.mpr
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top).ne
  have hi : Integrable ((ball a r).indicator (fun _ : Ambient d => (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrable_const 1)
  have h := integral_mono hi (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    (fun x => by
      by_cases hx : x ∈ ball a r
      · simpa only [indicator_of_mem hx] using! (hone x hx).ge
      · simpa only [indicator_of_notMem hx] using! hf x)
  simpa only [integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ, mul_one] using! h

theorem compactTestConvergence_upper_growth {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hg : ∀ j, GlobalUpperGrowth n C (μ j)) :
    GlobalUpperGrowth n (C * 2 ^ n) ν := by
  have hC : 0 ≤ C := (hg 0).1
  refine ⟨mul_nonneg hC (by positivity), ?_⟩
  intro a r hr
  have hsub : closedBall a r ⊆ ball a (2 * r) := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall a r) isOpen_ball.isClosed_compl (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hfi : ∀ j, (∫ x, F x ∂μ j) ≤ C * (2 * r) ^ n := by
    intro j
    apply (compact_test_integral_le_ball_mass (μ j) F a (2 * r)
      (fun x => (hbounds x).2) (fun x hx => hzero hx)).trans
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (by positivity))
      ((hg j).2 a (2 * r) (by positivity))
  have hlim : (∫ x, F x ∂ν) ≤ C * (2 * r) ^ n :=
    le_of_tendsto (hlocal F) (Eventually.of_forall hfi)
  have hball : ν.real (ball a r) ≤ C * (2 * r) ^ n :=
    (ball_mass_le_compact_test_integral ν F a r (fun x => (hbounds x).1)
      (fun _ hx => hone (ball_subset_closedBall hx))).trans hlim
  have hfinite : ν (ball a r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top).ne
  apply (ENNReal.le_ofReal_iff_toReal_le hfinite (by positivity)).mpr
  simpa only [mul_pow, mul_assoc] using! hball

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_nearby_support {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d) (hx : x ∈ ν.support)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ j in atTop, ∃ y, y ∈ (μ j).support ∧ y ∈ ball x r := by
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hmass : 0 < ν.real (ball x (r / 2)) := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((ν.mem_support_iff_forall x).mp hx (ball x (r / 2))
        (ball_mem_nhds x (by positivity)))
    · exact ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall x (r / 2)).measure_lt_top).ne
  have hpos : 0 < ∫ y, F y ∂ν := hmass.trans_le
    (ball_mass_le_compact_test_integral ν F x (r / 2) (fun y => (hbounds y).1)
      (fun _ hy => hone (ball_subset_closedBall hy)))
  filter_upwards [(hlocal F).eventually (lt_mem_nhds hpos)] with j hj
  by_contra hnone
  have hzeroae : ∀ᵐ y ∂μ j, F y = 0 := by
    filter_upwards [(μ j).support_mem_ae] with y hy
    exact hzero (show y ∈ (ball x r)ᶜ from fun hball => hnone ⟨y, hy, hball⟩)
  have heq : (∫ y, F y ∂μ j) = 0 := integral_eq_zero_of_ae hzeroae
  rw [heq] at hj
  exact (lt_irrefl 0) hj

theorem compactTestConvergence_support_zero_of_tubes {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (q : Ambient d → ℝ) (hq : Continuous q)
    (hqnn : ∀ x, 0 ≤ q x)
    (htube : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ j in atTop, ∀ x ∈ ball (0 : Ambient d) R, x ∈ (μ j).support → q x < ε) :
    ∀ x ∈ ν.support, q x = 0 := by
  intro x hx
  by_contra hne
  have hpos : 0 < q x := lt_of_le_of_ne (hqnn x) (Ne.symm hne)
  let ε := q x / 2
  have hε : 0 < ε := by dsimp only [ε] <;> positivity
  have hnhds : {y | ε < q y} ∈ 𝓝 x :=
    (isOpen_lt continuous_const hq).mem_nhds (show ε < q x by dsimp only [ε] <;> linarith)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hR : 0 < ‖x‖ + r := by linarith [norm_nonneg x]
  obtain ⟨j, hjnear, hjtube⟩ := ((compactTestConvergence_nearby_support μ ν hlocal x hx r hr).and
    (htube (‖x‖ + r) ε hR hε)).exists
  obtain ⟨y, hysupport, hyball⟩ := hjnear
  have hy0 : y ∈ ball (0 : Ambient d) (‖x‖ + r) := by
    have htri := dist_triangle y x (0 : Ambient d)
    have hyr : dist y x < r := hyball
    simp only [mem_ball, dist_zero_right] at htri ⊢
    linarith
  exact (not_lt_of_ge (hball hyball).le) (hjtube y hy0 hysupport)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_EmptyBallHalfspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_nearest_point_to_hole {d : ℕ} (E : Set (Ambient d))
    (hclosed : IsClosed E) (hne : E.Nonempty) (c : Ambient d) (hc : c ∉ E) :
    ∃ a ∈ E, a ≠ c ∧ ∀ y ∈ E, dist a c ≤ dist y c := by
  obtain ⟨a, ha, heq⟩ := hclosed.exists_infDist_eq_dist hne c
  refine ⟨a, ha, (fun hac => hc (hac ▸ ha)), ?_⟩
  intro y hy
  rw [dist_comm a c, ← heq, dist_comm y c]
  exact infDist_le_dist_of_mem hy

theorem nearest_point_quadratic_constraint {d : ℕ} (a c y : Ambient d)
    (hmin : dist a c ≤ dist y c) :
    0 ≤ 2 * inner ℝ (a - c) (y - a) + ‖y - a‖ ^ 2 := by
  have hs := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist a c) hmin 2
  have heq : y - c = (a - c) + (y - a) := by abel
  simp only [dist_eq_norm] at hs
  rw [heq, norm_add_sq_real] at hs
  linarith

theorem nearest_point_rescaled_constraint {d : ℕ} (a c x : Ambient d)
    (r : ℝ) (hr : 0 < r) (hmin : dist a c ≤ dist (a + r • x) c) :
    0 ≤ 2 * inner ℝ (a - c) x + r * ‖x‖ ^ 2 := by
  have h := nearest_point_quadratic_constraint a c (a + r • x) hmin
  have heq : a + r • x - a = r • x := by abel
  rw [heq, inner_smul_right, norm_smul, Real.norm_of_nonneg hr.le] at h
  have hp : 0 ≤ r * (2 * inner ℝ (a - c) x + r * ‖x‖ ^ 2) := by nlinarith
  exact nonneg_of_mul_nonneg_right hp hr

theorem compactTestConvergence_halfspace_of_quadratic_constraint {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (e : Ambient d)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hr0 : Tendsto r atTop (𝓝 0))
    (hside : ∀ j x, x ∈ (μ j).support → 0 ≤ 2 * inner ℝ e x + r j * ‖x‖ ^ 2) :
    ∀ x ∈ ν.support, 0 ≤ inner ℝ e x := by
  have hzero : ∀ x ∈ ν.support, max 0 (-inner ℝ e x) = 0 := by
    apply compactTestConvergence_support_zero_of_tubes μ ν hlocal
      (fun x => max 0 (-inner ℝ e x)) (by fun_prop) (fun _ => le_max_left _ _)
    intro R ε hR hε
    have hconv : Tendsto (fun j => r j * R ^ 2) atTop (𝓝 0) := by
      simpa only [zero_mul] using! hr0.mul_const (R ^ 2)
    filter_upwards [hconv.eventually (gt_mem_nhds (by linarith : 0 < 2 * ε))] with j hj
    intro x hx hxsupport
    have hxR : ‖x‖ ≤ R := (mem_ball_zero_iff.mp hx).le
    have hs : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxR 2
    have hp := mul_le_mul_of_nonneg_left hs (hr j)
    have h := hside j x hxsupport
    apply max_lt_iff.mpr
    exact ⟨hε, by linarith⟩
  intro x hx
  have h := le_max_right (0 : ℝ) (-inner ℝ e x)
  rw [hzero x hx] at h
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitLowerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_lower_ball_mass {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d) (hx : x ∈ ν.support)
    (r b : ℝ) (hr : 0 < r)
    (hlower : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support, b ≤ (μ j).real (ball y (r / 4))) :
    b ≤ ν.real (ball x r) := by
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hbound : ∀ᶠ j in atTop, b ≤ ∫ z, F z ∂μ j := by
    filter_upwards [hlower, compactTestConvergence_nearby_support μ ν hlocal x hx
      (r / 4) (by positivity)] with j hj hnear
    obtain ⟨y, hysupp, hyball⟩ := hnear
    apply (hj y hysupp).trans
    apply ball_mass_le_compact_test_integral (μ j) F y (r / 4) (fun z => (hbounds z).1)
    intro z hz
    apply hone
    have htri := dist_triangle z y x
    have hzy : dist z y < r / 4 := hz
    have hyx : dist y x < r / 4 := hyball
    exact mem_closedBall.mpr (by linarith)
  have hlimit : b ≤ ∫ z, F z ∂ν := ge_of_tendsto (hlocal F) hbound
  exact hlimit.trans (compact_test_integral_le_ball_mass ν F x r
    (fun z => (hbounds z).2) (fun _ hz => hzero hz))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitOrigin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_mem_support_of_ball_masses {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d)
    (hmass : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, c ≤ (μ j).real (ball x r)) : x ∈ ν.support := by
  have hball : ∀ r : ℝ, 0 < r → 0 < ν (ball x r) := by
    intro r hr
    have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
    obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
        (disjoint_compl_right_iff_subset.mpr hsub)
    let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
    obtain ⟨c, hc, hmassc⟩ := hmass (r / 2) (by positivity)
    have hbound : ∀ᶠ j in atTop, c ≤ ∫ y, F y ∂μ j := by
      filter_upwards [hmassc] with j hj
      exact hj.trans (ball_mass_le_compact_test_integral (μ j) F x (r / 2)
        (fun y => (hbounds y).1) (fun _ hy => hone (ball_subset_closedBall hy)))
    have hlimit : c ≤ ∫ y, F y ∂ν := ge_of_tendsto (hlocal F) hbound
    have hpos : 0 < ν.real (ball x r) := hc.trans_le (hlimit.trans
      (compact_test_integral_le_ball_mass ν F x r (fun y => (hbounds y).2) (fun _ hy => hzero hy)))
    exact (ENNReal.toReal_pos_iff.mp hpos).1
  apply (ν.mem_support_iff_forall x).mpr
  intro U hU
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  exact (hball r hr).trans_le (measure_mono hsub)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessWeightIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability of the compactness weight

Local finiteness controls the weight on closed balls, while polynomial upper growth controls
its exterior integral. Together these give global integrability and a quantitative mass bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal

theorem compactnessWeight_exterior_integral_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (R : ℝ) (hR : 0 < R) :
    (∫ x in {x | R < dist (0 : Ambient d) x}, compactnessWeight n x ∂μ) ≤
      2 * (C * 2 ^ n / R) := by
  have hs : MeasurableSet {x | R < dist (0 : Ambient d) x} :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet
  apply le_trans _ (inverseDistancePow_exterior_integral_bound n C μ hg 0 R hR)
  apply integral_mono_ae (compactnessWeight_integrableOn_exterior n μ C hg R hR)
    (inverseDistancePow_integrableOn_exterior n C μ hg 0 R hR)
  filter_upwards [ae_restrict_mem (μ := μ) hs] with x hx
  exact compactnessWeight_le_inverseDistance n x (dist_pos.mp (hR.trans hx)).symm

theorem compactnessWeight_integral_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) :
    (∫ x, compactnessWeight n x ∂μ) ≤ 3 * C * 2 ^ n := by
  have hglobal := compactnessWeight_integrable n μ C hg
  have : IsFiniteMeasure (μ.restrict (closedBall (0 : Ambient d) 1)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top)
  have hm : μ.real (closedBall (0 : Ambient d) 1) ≤ C * 2 ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
      ((measure_mono (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))).trans
        (hg.2 0 2 (by norm_num)))
  have hi : (∫ x in closedBall (0 : Ambient d) 1, compactnessWeight n x ∂μ) ≤ C * 2 ^ n := by
    have h := integral_mono (μ := μ.restrict (closedBall (0 : Ambient d) 1))
      hglobal.integrableOn (integrable_const (1 : ℝ))
      (compactnessWeight_le_one n)
    have h' : (∫ x in closedBall (0 : Ambient d) 1, compactnessWeight n x ∂μ) ≤
        μ.real (closedBall (0 : Ambient d) 1) := by
      simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_one] using! h
    exact h'.trans hm
  have heq : (closedBall (0 : Ambient d) 1)ᶜ = {x | (1 : ℝ) < dist (0 : Ambient d) x} := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, not_le]
    rw [dist_comm]
  rw [← integral_add_compl (s := closedBall (0 : Ambient d) 1) measurableSet_closedBall hglobal, heq]
  calc
    _ ≤ C * 2 ^ n + 2 * (C * 2 ^ n / 1) :=
      add_le_add hi (compactnessWeight_exterior_integral_bound n μ C hg 1 zero_lt_one)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessWeightedMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite measures obtained from the compactness weight

The positive decaying compactness weight turns a globally growing measure into a finite
measure. Integral formulas give quantitative tail control and transfer a lower mass bound
on the unit ball to a lower bound for the weighted total mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal

theorem compactnessWeightedMeasure_real {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    {s : Set (Ambient d)} (hs : MeasurableSet s)
    (hi : IntegrableOn (compactnessWeight n) s μ) :
    (compactnessWeightedMeasure n μ).real s = ∫ x in s, compactnessWeight n x ∂μ := by
  rw [Measure.real, compactnessWeightedMeasure_apply n μ hs hi,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (compactnessWeight_pos n x).le))]

theorem compactnessFiniteMeasure_mass_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) :
    ((compactnessFiniteMeasure n μ C hg).mass : ℝ) ≤ 3 * C * 2 ^ n := by
  change (compactnessWeightedMeasure n μ).real univ ≤ _
  rw [compactnessWeightedMeasure_real n μ MeasurableSet.univ
    (compactnessWeight_integrable n μ C hg).integrableOn, Measure.restrict_univ]
  exact compactnessWeight_integral_bound n μ C hg

theorem compactnessFiniteMeasure_tail_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) (R : ℝ) (hR : 0 < R) :
    ((compactnessFiniteMeasure n μ C hg) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤
      2 * (C * 2 ^ n / R) := by
  have heq : (closedBall (0 : Ambient d) R)ᶜ = {x | R < dist (0 : Ambient d) x} := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, not_le]
    rw [dist_comm]
  change (compactnessWeightedMeasure n μ).real (closedBall (0 : Ambient d) R)ᶜ ≤ _
  have hs : MeasurableSet {x | R < dist (0 : Ambient d) x} :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet
  rw [heq, compactnessWeightedMeasure_real n μ hs
    (compactnessWeight_integrableOn_exterior n μ C hg R hR)]
  exact compactnessWeight_exterior_integral_bound n μ C hg R hR

theorem compactnessWeight_lower_on_unit_ball {d : ℕ} (n : ℕ) (x : Ambient d)
    (hx : x ∈ ball (0 : Ambient d) 1) : (2 : ℝ)⁻¹ ^ (n + 1) ≤ compactnessWeight n x := by
  have hn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using! hx
  have hpow : (1 + ‖x‖) ^ (n + 1) ≤ (2 : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (n + 1)
  simpa only [compactnessWeight, one_div, inv_pow] using!
    one_div_le_one_div_of_le (by positivity : 0 < (1 + ‖x‖) ^ (n + 1)) hpow

theorem compactnessWeight_integral_lower {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C c : ℝ) (hg : GlobalUpperGrowth n C μ)
    (hm : c ≤ μ.real (ball (0 : Ambient d) 1)) :
    c * (2 : ℝ)⁻¹ ^ (n + 1) ≤ ∫ x, compactnessWeight n x ∂μ := by
  have hi := compactnessWeight_integrable n μ C hg
  have : IsFiniteMeasure (μ.restrict (ball (0 : Ambient d) 1)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top).ne
  have hlocal : μ.real (ball (0 : Ambient d) 1) * (2 : ℝ)⁻¹ ^ (n + 1) ≤
      ∫ x in ball (0 : Ambient d) 1, compactnessWeight n x ∂μ := by
    have h := integral_mono_ae (μ := μ.restrict (ball (0 : Ambient d) 1))
      (integrable_const ((2 : ℝ)⁻¹ ^ (n + 1))) hi.integrableOn
      (by
        filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball] with x hx
        exact compactnessWeight_lower_on_unit_ball n x hx)
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] using! h
  exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans
    (hlocal.trans (setIntegral_le_integral hi (Eventually.of_forall
      (fun x => (compactnessWeight_pos n x).le))))

theorem compactnessFiniteMeasure_mass_lower {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C c : ℝ) (hg : GlobalUpperGrowth n C μ)
    (hm : c ≤ μ.real (ball (0 : Ambient d) 1)) :
    c * (2 : ℝ)⁻¹ ^ (n + 1) ≤ ((compactnessFiniteMeasure n μ C hg).mass : ℝ) := by
  change _ ≤ (compactnessWeightedMeasure n μ).real univ
  rw [compactnessWeightedMeasure_real n μ MeasurableSet.univ
    (compactnessWeight_integrable n μ C hg).integrableOn, Measure.restrict_univ]
  exact compactnessWeight_integral_lower n μ C c hg hm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessUnweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactnessWeight_inv_continuous {d : ℕ} (n : ℕ) :
    Continuous (fun x : Ambient d => (compactnessWeight n x)⁻¹) :=
  (compactnessWeight_continuous n).inv₀ (fun x => ne_of_gt (compactnessWeight_pos n x))

theorem compactnessUnweightedMeasure_locally_finite {d : ℕ} (n : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (compactnessUnweightedMeasure n ν) := by
  constructor
  intro K hK
  have hi : IntegrableOn (fun x => (compactnessWeight n x)⁻¹) K ν :=
    ContinuousOn.integrableOn_compact hK (compactnessWeight_inv_continuous n).continuousOn
  rw [compactnessUnweightedMeasure, withDensity_apply _ hK.measurableSet,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x =>
      inv_nonneg.mpr (compactnessWeight_pos n x).le))]
  exact ENNReal.ofReal_lt_top

theorem compactness_unweight_weight {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) :
    compactnessUnweightedMeasure n (compactnessWeightedMeasure n μ) = μ := by
  rw [compactnessUnweightedMeasure, compactnessWeightedMeasure,
    ← withDensity_mul μ (compactnessWeight_continuous n).measurable.ennreal_ofReal
      (compactnessWeight_inv_continuous n).measurable.ennreal_ofReal]
  have heq : (fun x : Ambient d => ENNReal.ofReal (compactnessWeight n x)) *
      (fun x => ENNReal.ofReal ((compactnessWeight n x)⁻¹)) = 1 := by
    funext x
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (compactnessWeight_pos n x).le,
      mul_inv_cancel₀ (ne_of_gt (compactnessWeight_pos n x)), ENNReal.ofReal_one, Pi.one_apply]
  rw [heq, withDensity_one]

theorem compactnessUnweightedMeasure_integral {d : ℕ} (n : ℕ)
    (ν : Measure (Ambient d)) (f : Ambient d → ℝ) :
    (∫ x, f x ∂compactnessUnweightedMeasure n ν) =
      ∫ x, (compactnessWeight n x)⁻¹ * f x ∂ν := by
  rw [compactnessUnweightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (compactnessWeight_inv_continuous n).measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (ENNReal.ofReal ((compactnessWeight n x)⁻¹)).toReal • f x =
      (compactnessWeight n x)⁻¹ * f x
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (compactnessWeight_pos n x).le), smul_eq_mul])

theorem compactness_unweight_weak_convergence {d : ℕ} (n : ℕ)
    (νj : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hν : Tendsto νj atTop (𝓝 ν)) :
    CompactTestConvergence (fun j => compactnessUnweightedMeasure n (νj j : Measure (Ambient d)))
      (compactnessUnweightedMeasure n (ν : Measure (Ambient d))) := by
  intro f
  let test : C_c(Ambient d, ℝ) :=
    ⟨⟨fun x => (compactnessWeight n x)⁻¹ * f x,
      (compactnessWeight_inv_continuous n).mul f.continuous⟩, f.hasCompactSupport.mul_left⟩
  have h := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν test.toBoundedContinuousFunction
  change Tendsto (fun j => ∫ x, (compactnessWeight n x)⁻¹ * f x ∂(νj j : Measure (Ambient d)))
    atTop (𝓝 (∫ x, (compactnessWeight n x)⁻¹ * f x ∂(ν : Measure (Ambient d)))) at h
  simpa only [compactnessUnweightedMeasure_integral] using! h

theorem compactness_weighted_limit_gives_original_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hg : ∀ j, GlobalUpperGrowth n C (μ j)) (ν : FiniteMeasure (Ambient d))
    (hν : Tendsto (fun j => compactnessFiniteMeasure n (μ j) C (hg j)) atTop (𝓝 ν)) :
    CompactTestConvergence μ (compactnessUnweightedMeasure n ν) := by
  have h := compactness_unweight_weak_convergence n _ ν hν
  simpa only [compactnessFiniteMeasure, FiniteMeasure.toMeasure_mk, compactness_unweight_weight] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_FiniteMeasureSequentialCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sequential compactness of finite measures

Normalization converts uniform tail estimates and a positive mass lower bound into
tightness of probability measures. A further subsequence of the masses recovers a
finite-measure limit while preserving the uniform mass bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal

theorem finiteMeasure_normalize_set_bound {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (a b : ℝ) (ha : 0 < a) (hm : a ≤ (μ.mass : ℝ))
    (s : Set (Ambient d)) (hs : (μ s : ℝ) ≤ b) : (μ.normalize s : ℝ) ≤ b / a := by
  have heq : (μ s : ℝ) = (μ.mass : ℝ) * (μ.normalize s : ℝ) := by
    exact_mod_cast μ.self_eq_mass_mul_normalize s
  apply (le_div_iff₀ ha).mpr
  calc
    (μ.normalize s : ℝ) * a ≤ (μ.normalize s : ℝ) * (μ.mass : ℝ) :=
      mul_le_mul_of_nonneg_left hm (μ.normalize s).coe_nonneg
    _ = (μ s : ℝ) := by linarith only [heq]
    _ ≤ b := hs

theorem exists_normalized_measure_subsequence {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hm : ∀ j, a ≤ ((μ j).mass : ℝ))
    (ht : ∀ j R, 0 < R → ((μ j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤ B / R) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ P : ProbabilityMeasure (Ambient d),
      Tendsto (fun j => (μ (ρ j)).normalize) atTop (𝓝 P) := by
  let u : ℕ → ℝ≥0 := fun k => Real.toNNReal (B / a) * (1 / 2) ^ k
  let K : ℕ → Set (Ambient d) := fun k => closedBall 0 ((2 : ℝ) ^ k)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u, mul_zero] using!
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0) < 1)).const_mul
        (Real.toNNReal (B / a))
  have hc : IsCompact {P : ProbabilityMeasure (Ambient d) | ∀ k, P (K k)ᶜ ≤ u k} :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le hu
      (fun k => isCompact_closedBall 0 _) (Or.inl inferInstance)
  have hin : ∀ j, (μ j).normalize ∈ {P : ProbabilityMeasure (Ambient d) | ∀ k, P (K k)ᶜ ≤ u k} := by
    intro j k
    have hreal : ((μ j).normalize (K k)ᶜ : ℝ) ≤ (u k : ℝ) := by
      calc
        _ ≤ (B / (2 : ℝ) ^ k) / a := finiteMeasure_normalize_set_bound
          (μ j) a _ ha (hm j) (K k)ᶜ (ht j _ (by positivity))
        _ = (u k : ℝ) := by
          simp only [u, NNReal.coe_mul, Real.coe_toNNReal _ (div_nonneg hB ha.le), NNReal.coe_pow, NNReal.coe_div,
            NNReal.coe_one, NNReal.coe_ofNat, div_pow, one_pow]
          ring
    exact_mod_cast hreal
  obtain ⟨P, _hP, ρ, hρ, hlim⟩ := hc.tendsto_subseq hin
  exact ⟨ρ, hρ, P, hlim⟩

theorem exists_finite_measure_subsequence {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (a A B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hm : ∀ j, a ≤ ((μ j).mass : ℝ) ∧ ((μ j).mass : ℝ) ≤ A)
    (ht : ∀ j R, 0 < R → ((μ j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤ B / R) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : FiniteMeasure (Ambient d),
      Tendsto (fun j => μ (ρ j)) atTop (𝓝 ν) ∧ a ≤ (ν.mass : ℝ) ∧ (ν.mass : ℝ) ≤ A := by
  obtain ⟨ρ, hρ, P, hP⟩ := exists_normalized_measure_subsequence μ a B ha hB
    (fun j => (hm j).1) ht
  have hbounded : ∀ j, ((μ (ρ j)).mass : ℝ) ∈ Icc a A := fun j => hm (ρ j)
  obtain ⟨m, hmI, σ, hσ, hmass⟩ := isCompact_Icc.tendsto_subseq hbounded
  let m' : ℝ≥0 := ⟨m, ha.le.trans hmI.1⟩
  have hmass' : Tendsto (fun j => (μ (ρ (σ j))).mass) atTop (𝓝 m') :=
    NNReal.tendsto_coe.mp hmass
  have hP' : Tendsto (fun j => (μ (ρ (σ j))).normalize.toFiniteMeasure) atTop
      (𝓝 P.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto P).comp
      (hP.comp hσ.tendsto_atTop)
  have hmasslim : (m' • P.toFiniteMeasure).mass = m' := by
    change (m' • P.toFiniteMeasure) univ = m'
    rw [FiniteMeasure.smul_apply]
    change m' * P.toFiniteMeasure.mass = m'
    rw [ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
  refine ⟨ρ ∘ σ, hρ.comp hσ, m' • P.toFiniteMeasure, ?_, ?_, ?_⟩
  · have h := hmass'.smul hP'
    simpa only [← FiniteMeasure.self_eq_mass_smul_normalize, comp_apply] using! h
  · rw [hmasslim]
    exact hmI.1
  · rw [hmasslim]
    exact hmI.2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OriginalMeasureCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem le_compactnessUnweightedMeasure {d : ℕ} (n : ℕ) (ν : Measure (Ambient d)) :
    ν ≤ compactnessUnweightedMeasure n ν := by
  have h : ν.withDensity 1 ≤ ν.withDensity (fun x => ENNReal.ofReal ((compactnessWeight n x)⁻¹)) := by
    apply withDensity_mono
    exact Eventually.of_forall (fun x => by
      change (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((compactnessWeight n x)⁻¹)
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [compactnessWeight, inv_inv]
      exact one_le_pow₀ (by linarith [norm_nonneg x]))
  simpa only [withDensity_one, compactnessUnweightedMeasure] using! h

theorem compactnessUnweightedMeasure_ne_zero {d : ℕ} (n : ℕ)
    (ν : FiniteMeasure (Ambient d)) (hν : ν ≠ 0) :
    compactnessUnweightedMeasure n (ν : Measure (Ambient d)) ≠ 0 := by
  intro hzero
  have h : (ν : Measure (Ambient d)) = 0 := by
    apply le_antisymm _ bot_le
    simpa only [hzero] using! le_compactnessUnweightedMeasure n (ν : Measure (Ambient d))
  apply hν
  apply FiniteMeasure.toMeasure_injective
  exact h

theorem exists_original_measure_compact_subsequence {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C c : ℝ) (hc : 0 < c) (hg : ∀ j, GlobalUpperGrowth n C (μ j))
    (hm : ∀ j, c ≤ (μ j).real (ball (0 : Ambient d) 1)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧ CompactTestConvergence (fun j => μ (ρ j)) ν := by
  let μw : ℕ → FiniteMeasure (Ambient d) := fun j => compactnessFiniteMeasure n (μ j) C (hg j)
  let a : ℝ := c * (2 : ℝ)⁻¹ ^ (n + 1)
  have ha : 0 < a := by dsimp only [a] <;> positivity
  have hC : 0 ≤ C := (hg 0).1
  have hmass : ∀ j, a ≤ ((μw j).mass : ℝ) ∧ ((μw j).mass : ℝ) ≤ 3 * C * 2 ^ n := by
    intro j
    exact ⟨compactnessFiniteMeasure_mass_lower n (μ j) C c (hg j) (hm j),
      compactnessFiniteMeasure_mass_bound n (μ j) C (hg j)⟩
  have htail : ∀ j R, 0 < R → ((μw j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤
      (2 * C * 2 ^ n) / R := by
    intro j R hR
    calc
      _ ≤ 2 * (C * 2 ^ n / R) := compactnessFiniteMeasure_tail_bound n (μ j) C (hg j) R hR
      _ = _ := by ring
  obtain ⟨ρ, hρ, νw, hweak, hlow, _hupp⟩ := exists_finite_measure_subsequence μw
    a (3 * C * 2 ^ n) (2 * C * 2 ^ n) ha (by positivity) hmass htail
  have hνw : νw ≠ 0 := by
    apply νw.mass_nonzero_iff.mp
    intro hz
    rw [hz, NNReal.coe_zero] at hlow
    exact (not_le_of_gt ha) hlow
  refine ⟨ρ, hρ, compactnessUnweightedMeasure n (νw : Measure (Ambient d)),
    compactnessUnweightedMeasure_locally_finite n _, compactnessUnweightedMeasure_ne_zero n νw hνw, ?_⟩
  exact compactness_weighted_limit_gives_original_limit n (fun j => μ (ρ j)) C
    (fun j => hg (ρ j)) νw hweak

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OriginalGrowthLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonzero compact-test limits with upper growth

A uniform lower bound on unit-ball mass prevents the compact-test subsequential
limit from vanishing. The upper growth estimate passes to this limit with the
explicit factor `2 ^ n` in its constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_original_growth_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C c : ℝ) (hc : 0 < c) (hg : ∀ j, GlobalUpperGrowth n C (μ j))
    (hm : ∀ j, c ≤ (μ j).real (ball (0 : Ambient d) 1)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (C * 2 ^ n) ν := by
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlimit⟩ :=
    exists_original_measure_compact_subsequence n μ C c hc hg hm
  let := hfinite
  exact ⟨ρ, hρ, ν, hfinite, hne, hlimit,
    compactTestConvergence_upper_growth n (fun j => μ (ρ j)) ν hlimit C (fun j => hg (ρ j))⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_GlobalLowerMeasureLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Global lower growth in measure limits

Compact-test convergence transfers lower ball-mass bounds to support points of the
limit, with the explicit factor `4 ^ n`. Combined with global upper growth and an origin
normalization, this produces a nonzero subsequential limit with both growth estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_global_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r)) :
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  intro x hx r hr
  have hquarter : 0 < r / 4 := by positivity
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by
    rw [div_pow]
    ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    apply Filter.Eventually.of_forall
    intro j y hy
    have hfinite : (μ j) (ball y (r / 4)) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall y (r / 4)).measure_lt_top).ne
    have h := ENNReal.toReal_mono hfinite (hlower j y hy (r / 4) hquarter)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C)] at h
    simpa only [heq, Measure.real] using! h
  have hreal := compactTestConvergence_lower_ball_mass μ ν hlocal x hx r _ hr hbound
  calc
    _ ≤ ENNReal.ofReal (ν.real (ball x r)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne

theorem exists_global_growth_measure_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
      (0 : Ambient d) ∈ ν.support ∧
      ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  have hmass : ∀ j, C⁻¹ ≤ (μ j).real (ball (0 : Ambient d) 1) := by
    intro j
    have h := ENNReal.toReal_mono
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top).ne
      (hlower j 0 (hzero j) 1 zero_lt_one)
    simpa only [one_pow, one_div, ENNReal.toReal_ofReal (inv_nonneg.mpr hC.le), Measure.real] using! h
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν⟩ :=
    exists_original_growth_limit n μ G C⁻¹ (inv_pos.mpr hC) hg hmass
  let := hfinite
  have horigin : (0 : Ambient d) ∈ ν.support := by
    apply compactTestConvergence_mem_support_of_ball_masses (fun j => μ (ρ j)) ν hlocal 0
    intro r hr
    refine ⟨r ^ n / C, by positivity, Filter.Eventually.of_forall fun j => ?_⟩
    have h := ENNReal.toReal_mono
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) r).measure_lt_top).ne
      (hlower (ρ j) 0 (hzero (ρ j)) r hr)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ n / C), Measure.real] using! h
  exact ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, horigin,
    compactTestConvergence_global_lower n (fun j => μ (ρ j)) ν hlocal C hC
      (fun j => hlower (ρ j))⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_HoleTangentMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tangent measures at a nearest point to a hole

Uniform growth bounds yield a nonzero subsequential blowup limit with inherited
two-sided growth. At a point nearest to a hole, the rescaled quadratic constraint
converges to a half-space constraint on the tangent measure's support.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_blowup_measure_limit {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (a : Ambient d) (ha : a ∈ μ.support) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ a (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      ∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R) := by
  have hg' : ∀ j, GlobalUpperGrowth n G (blowupMeasure n μ a (r j)) :=
    fun j => blowupMeasure_growth n μ a (r j) G (hr j) hg
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ a (r j)) :=
    fun j => globalGrowth_finite_on_compacts G _ (hg' j)
  exact exists_global_growth_measure_limit n (fun j => blowupMeasure n μ a (r j)) C G hC hg'
    (fun j => blowupMeasure_lower_global n μ a (r j) C (hr j) hlower)
    (fun j => blowupMeasure_origin_mem_support n μ a (r j) (hr j) ha)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ShrinkingBallIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem measure_ball_tendsto_zero_of_growth {d : ℕ} (n : ℕ) (hn : 0 < n)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j => μ (ball x (r j))) atTop (𝓝 0) := by
  have hbound : Tendsto (fun j => ENNReal.ofReal (C * r j ^ n)) atTop (𝓝 0) := by
    simpa only [zero_pow hn.ne', mul_zero, ENNReal.ofReal_zero] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hr0.pow n).const_mul C)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => bot_le) (fun j => hg.2 x (r j) (hr j))

theorem local_integral_tendsto_zero_on_shrinking_balls {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (x : Ambient d) (R : ℝ) (hR : 0 < R)
    (hi : IntegrableOn f (ball x R) μ) (r : ℕ → ℝ) (hr0 : Tendsto r atTop (𝓝 0))
    (hmass : Tendsto (fun j => μ (ball x (r j))) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y in ball x (r j), f y ∂μ) atTop (𝓝 0) := by
  have hrestrict : Tendsto (fun j => (μ.restrict (ball x R)) (ball x (r j))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass
      (fun _ => bot_le) (fun j => Measure.restrict_le_self (ball x (r j)))
  have hlim := hi.tendsto_setIntegral_nhds_zero hrestrict
  apply hlim.congr'
  filter_upwards [hr0.eventually (gt_mem_nhds hR)] with j hj
  rw [Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr (ball_subset_ball hj.le)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PositiveNormalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal

theorem positiveNormalHeight_nonneg {d : ℕ} (e x : Ambient d) :
    0 ≤ positiveNormalHeight e x := le_max_left _ _

theorem positiveNormalHeight_le_norm {d : ℕ} (e x : Ambient d) :
    positiveNormalHeight e x ≤ ‖e‖ * ‖x‖ := by
  exact max_le (by positivity) (real_inner_le_norm e x)

theorem positiveNormalPotential_nonneg {d : ℕ} (n : ℕ) (e x : Ambient d) :
    0 ≤ positiveNormalPotential n e x :=
  div_nonneg (positiveNormalHeight_nonneg e x) (by positivity)

theorem positiveNormalPotential_zero {d : ℕ} (n : ℕ) (e : Ambient d) :
    positiveNormalPotential n e 0 = 0 := by
  simp [positiveNormalPotential, positiveNormalHeight]

theorem positiveNormalPotential_measurable {d : ℕ} (n : ℕ) (e : Ambient d) :
    Measurable (positiveNormalPotential n e) := by
  unfold positiveNormalPotential positiveNormalHeight
  fun_prop

theorem positiveNormalPotential_truncated_bound {d : ℕ} (n : ℕ) (e x : Ambient d)
    (ε R : ℝ) (hε : 0 < ε) (hsmall : ε ≤ ‖x‖) (hlarge : ‖x‖ ≤ R) :
    positiveNormalPotential n e x ≤ (‖e‖ * R) * (ε ^ (n + 1))⁻¹ := by
  have hnum : positiveNormalHeight e x ≤ ‖e‖ * R :=
    (positiveNormalHeight_le_norm e x).trans (mul_le_mul_of_nonneg_left hlarge (norm_nonneg e))
  have hinv : (‖x‖ ^ (n + 1))⁻¹ ≤ (ε ^ (n + 1))⁻¹ := by
    simpa only [one_div] using! one_div_le_one_div_of_le (pow_pos hε (n + 1))
      (pow_le_pow_left₀ hε.le hsmall (n + 1))
  exact mul_le_mul hnum hinv (by positivity)
    (mul_nonneg (norm_nonneg e) ((norm_nonneg x).trans hlarge))

theorem positiveNormalPotential_integrableOn_truncated {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (e : Ambient d)
    (ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (positiveNormalPotential n e)
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) μ := by
  apply Measure.integrableOn_of_bounded
    ((measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top).ne
    (positiveNormalPotential_measurable n e).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))] with x hx
  rw [Real.norm_of_nonneg (positiveNormalPotential_nonneg n e x)]
  exact positiveNormalPotential_truncated_bound n e x ε R hε hx.2.le
    (mem_ball_zero_iff.mp hx.1).le

theorem positiveNormalPotential_integrable_of_truncated_bounds {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (e : Ambient d) (R B : ℝ)
    (hB : ∀ ε : ℝ, 0 < ε →
      (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) ≤ B) :
    IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R) μ ∧
      (∫ x in ball (0 : Ambient d) R, positiveNormalPotential n e x ∂μ) ≤ B := by
  apply nonnegative_integrable_of_exhaustion (μ.restrict (ball (0 : Ambient d) R))
    (positiveNormalPotential n e) (positiveNormalPotential_measurable n e)
    (positiveNormalPotential_nonneg n e)
    (fun k : ℕ => {x : Ambient d | (1 / 2 : ℝ) ^ k < ‖x‖})
    (fun _ => measurableSet_lt measurable_const continuous_norm.measurable)
  · intro k l hkl x hx
    have hp : (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl
    exact lt_of_le_of_lt hp hx
  · intro x hx
    have hne : x ≠ 0 := by
      intro h
      exact hx (h ▸ positiveNormalPotential_zero n e)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hne)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact mem_iUnion.mpr ⟨k, hk⟩
  · intro k
    simpa only [IntegrableOn, Measure.restrict_restrict
      (measurableSet_lt measurable_const continuous_norm.measurable), inter_comm] using!
      positiveNormalPotential_integrableOn_truncated n μ e ((1 / 2 : ℝ) ^ k) R (by positivity)
  · intro k
    simpa only [Measure.restrict_restrict
      (measurableSet_lt measurable_const continuous_norm.measurable), inter_comm] using!
      hB ((1 / 2 : ℝ) ^ k) (by positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BlowupNormalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal-height moments under blowup

Positive normal height is homogeneous of degree one. Combining this with the measure's
blowup normalization gives the moment scaling identity and bounds the rescaled height
integral by the positive normal potential on the original ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem positiveNormalHeight_continuous {d : ℕ} (e : Ambient d) :
    Continuous (positiveNormalHeight e) := by
  unfold positiveNormalHeight
  fun_prop

theorem positiveNormalHeight_smul {d : ℕ} (e x : Ambient d) (r : ℝ) (hr : 0 ≤ r) :
    positiveNormalHeight e (r • x) = r * positiveNormalHeight e x := by
  simp only [positiveNormalHeight, inner_smul_right, mul_max_of_nonneg _ _ hr, mul_zero]

theorem positiveNormalHeight_integrableOn_ball {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (e : Ambient d) (R : ℝ) :
    IntegrableOn (positiveNormalHeight e) (ball (0 : Ambient d) R) μ :=
  ((positiveNormalHeight_continuous e).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Ambient d) R)).mono_set ball_subset_closedBall

theorem blowup_positiveNormalHeight_integral {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (r R : ℝ) (hr : 0 < r) :
    (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 r) =
      (r ^ (n + 1))⁻¹ * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalHeight e y ∂μ := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  rw [blowupMeasure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹), smul_eq_mul,
    setIntegral_map measurableSet_ball (positiveNormalHeight_continuous e).aestronglyMeasurable
      (by fun_prop), blowup_preimage_ball 0 0 r R hr]
  simp only [smul_zero, add_zero, sub_zero]
  simp_rw [positiveNormalHeight_smul e _ r⁻¹ (inv_nonneg.mpr hr.le)]
  rw [integral_const_mul, pow_succ, mul_inv]
  ring

theorem positiveNormalHeight_eq_potential_weight {d : ℕ} (n : ℕ) (e x : Ambient d) :
    positiveNormalHeight e x = ‖x‖ ^ (n + 1) * positiveNormalPotential n e x := by
  by_cases hx : x = 0
  · subst x
    simp [positiveNormalHeight, positiveNormalPotential]
  · have hn : ‖x‖ ^ (n + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    unfold positiveNormalPotential
    field_simp

theorem blowup_positiveNormalHeight_le_potential_integral {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (e : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) (r * R)) μ) :
    (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 r) ≤
      R ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ := by
  have hbound : (∫ y in ball (0 : Ambient d) (r * R), positiveNormalHeight e y ∂μ) ≤
      (r * R) ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (positiveNormalHeight_integrableOn_ball μ e (r * R))
      (hi.const_mul ((r * R) ^ (n + 1)))
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [positiveNormalHeight_eq_potential_weight n e y]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg y) (mem_ball_zero_iff.mp hy).le (n + 1))
      (positiveNormalPotential_nonneg n e y)
  rw [blowup_positiveNormalHeight_integral n μ e r R hr]
  calc
    _ ≤ (r ^ (n + 1))⁻¹ * ((r * R) ^ (n + 1) *
        ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      rw [mul_pow]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BlowupNormalMomentDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem blowup_positiveNormalHeight_moments_tendsto_zero {d : ℕ}
    (n : ℕ) (hn : 0 < n) (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (e : Ambient d)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R₀) μ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0))
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
      positiveNormalHeight e x ∂blowupMeasure n μ 0 (r j)) atTop (𝓝 0) := by
  have hscale : Tendsto (fun j => r j * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hr0.mul_const R
  have hpot := local_integral_tendsto_zero_on_shrinking_balls μ (positiveNormalPotential n e)
    0 R₀ hR₀ hi (fun j => r j * R) hscale
      (measure_ball_tendsto_zero_of_growth n hn μ G hg 0 (fun j => r j * R)
        (fun j => mul_pos (hr j) hR) hscale)
  have hbound : ∀ᶠ j in atTop,
      (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 (r j)) ≤
        R ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r j * R), positiveNormalPotential n e y ∂μ := by
    filter_upwards [hscale.eventually (gt_mem_nhds hR₀)] with j hj
    exact blowup_positiveNormalHeight_le_potential_integral n μ e (r j) R (hr j) hR
      (hi.mono_set (ball_subset_ball hj.le))
  have hright : Tendsto (fun j => R ^ (n + 1) *
      ∫ y in ball (0 : Ambient d) (r j * R), positiveNormalPotential n e y ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using! hpot.const_mul (R ^ (n + 1))
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ =>
    integral_nonneg (positiveNormalHeight_nonneg e)) hbound hright

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitZeroMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported

theorem compactTestConvergence_support_zero_of_first_moments {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (q : Ambient d → ℝ) (hq : Continuous q)
    (hqnn : ∀ x, 0 ≤ q x)
    (hmoment : ∀ R : ℝ, 0 < R →
      Tendsto (fun j => ∫ x in ball (0 : Ambient d) R, q x ∂μ j) atTop (𝓝 0)) :
    ∀ x ∈ ν.support, q x = 0 := by
  intro x hx
  have hR : 0 < ‖x‖ + 2 := by positivity
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : Ambient d) (‖x‖ + 1)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (closedBall_subset_ball (by linarith : ‖x‖ + 1 < ‖x‖ + 2)))
  let F : C_c(Ambient d, ℝ) := ⟨⟨fun y => f y * q y, f.continuous.mul hq⟩, hcomp.mul_right⟩
  have hFnn : ∀ y, 0 ≤ F y := fun y => mul_nonneg (hbounds y).1 (hqnn y)
  have hbound : ∀ j, (∫ y, F y ∂μ j) ≤ ∫ y in ball (0 : Ambient d) (‖x‖ + 2), q y ∂μ j := by
    intro j
    have hi : IntegrableOn q (ball (0 : Ambient d) (‖x‖ + 2)) (μ j) :=
      (hq.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Ambient d) (‖x‖ + 2))).mono_set ball_subset_closedBall
    rw [← integral_indicator measurableSet_ball]
    apply integral_mono (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport)
      (hi.integrable_indicator measurableSet_ball)
    intro y
    by_cases hy : y ∈ ball (0 : Ambient d) (‖x‖ + 2)
    · simpa only [indicator_of_mem hy, one_mul] using!
        mul_le_mul_of_nonneg_right (hbounds y).2 (hqnn y)
    · change f y * q y ≤ _
      rw [hzero hy, Pi.zero_apply, zero_mul, indicator_of_notMem hy]
  have hle : (∫ y, F y ∂ν) ≤ 0 := le_of_tendsto_of_tendsto
    (hlocal F) (hmoment (‖x‖ + 2) hR) (Filter.Eventually.of_forall hbound)
  have heq : (∫ y, F y ∂ν) = 0 := le_antisymm hle (integral_nonneg hFnn)
  have hae : F =ᵐ[ν] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hFnn)
      (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport)).mp heq
  have hpoint := ν.support_subset_of_isClosed (isClosed_eq F.continuous continuous_const) hae hx
  change f x * q x = 0 at hpoint
  rw [hone (show x ∈ closedBall (0 : Ambient d) (‖x‖ + 1) by
    simp only [mem_closedBall, dist_zero_right] <;> linarith), Pi.one_apply, one_mul] at hpoint
  exact hpoint

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalAnnularKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal components of annular kernel integrals

Away from the origin the Riesz kernel is integrable on bounded annuli. For measures
supported in a nonnegative half-space, its normal component equals the positive
normal potential, so vector integral bounds control the scalar potential integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem rieszKernel_integrableOn_centered_annulus {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : Ambient d => kernel n x 0)
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) μ := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  apply Measure.integrableOn_of_bounded
    ((measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top).ne
    (show Measurable (fun x : Ambient d => kernel n x 0) by unfold kernel; fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))] with x hx
  exact kernel_norm_le_truncation n x 0 ε hε (by simpa only [dist_zero_right] using! hx.2.le)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_QuadraticNormalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem positiveNormalPotential_signed_decomposition {d : ℕ} (n : ℕ) (e x : Ambient d) :
    positiveNormalPotential n e x = inner ℝ e (kernel n x 0) + positiveNormalPotential n (-e) x := by
  simp only [positiveNormalPotential, positiveNormalHeight, inner_neg_left,
    kernel, sub_zero, inner_smul_right]
  by_cases h : 0 ≤ inner ℝ e x
  · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_left (le_of_not_ge h), max_eq_right (neg_nonneg.mpr (le_of_not_ge h))]
    ring

theorem negativeNormalPotential_quadratic_bound {d : ℕ} (p : ℕ) (e x : Ambient d)
    (hquad : 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2) :
    positiveNormalPotential (p + 1) (-e) x ≤ (1 / 2 : ℝ) * inverseDistancePow p 0 x := by
  by_cases hx : x = 0
  · subst x
    rw [positiveNormalPotential_zero]
    exact mul_nonneg (by norm_num) (inverseDistancePow_nonneg p 0 0)
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hnum : positiveNormalHeight (-e) x ≤ ‖x‖ ^ 2 / 2 := by
      apply max_le
      · positivity
      · rw [inner_neg_left]
        linarith
    calc
      positiveNormalPotential (p + 1) (-e) x ≤ (‖x‖ ^ 2 / 2) / ‖x‖ ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem negativeNormalPotential_integrable_of_quadratic_constraint {d : ℕ} (p : ℕ)
    (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G μ)
    (e : Ambient d) (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (positiveNormalPotential (p + 1) (-e)) (ball (0 : Ambient d) R) μ := by
  have hi := ((inverseDistancePow_near_integrable_and_bound p G μ hg 0 R hR).1.mono_set
    ball_subset_closedBall).const_mul (1 / 2 : ℝ)
  apply hi.mono' (positiveNormalPotential_measurable (p + 1) (-e)).aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (positiveNormalPotential_nonneg (p + 1) (-e) x)]
  exact negativeNormalPotential_quadratic_bound p e x (hquad x hx)

theorem positiveNormalPotential_integrable_of_quadratic_annuli {d : ℕ} (p : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G μ)
    (e : Ambient d) (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (R B : ℝ) (hR : 0 < R)
    (hB : ∀ ε : ℝ, 0 < ε →
      ‖∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, kernel (p + 1) x 0 ∂μ‖ ≤ B) :
    IntegrableOn (positiveNormalPotential (p + 1) e) (ball (0 : Ambient d) R) μ := by
  have hneg := negativeNormalPotential_integrable_of_quadratic_constraint p μ G hg e hquad R hR
  apply (positiveNormalPotential_integrable_of_truncated_bounds (p + 1) μ e R
    (‖e‖ * B + ∫ x in ball (0 : Ambient d) R, positiveNormalPotential (p + 1) (-e) x ∂μ) ?_).1
  intro ε hε
  have hk := rieszKernel_integrableOn_centered_annulus (p + 1) μ ε R hε
  have hlinear : IntegrableOn (fun x => inner ℝ e (kernel (p + 1) x 0))
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) μ := by
    simpa only [innerSL_apply_apply] using! (innerSL ℝ e).integrable_comp hk
  have hn := hneg.mono_set (inter_subset_left :
    ball (0 : Ambient d) R ∩ {x | ε < ‖x‖} ⊆ ball (0 : Ambient d) R)
  calc
    _ = inner ℝ e (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, kernel (p + 1) x 0 ∂μ) +
        ∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential (p + 1) (-e) x ∂μ := by
      simp_rw [positiveNormalPotential_signed_decomposition (p + 1) e]
      rw [integral_add hlinear hn]
      exact congrArg (fun z => z + ∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖},
        positiveNormalPotential (p + 1) (-e) x ∂μ) ((innerSL ℝ e).integral_comp_comm hk)
    _ ≤ _ := add_le_add
      ((real_inner_le_norm e _).trans (mul_le_mul_of_nonneg_left (hB ε hε) (norm_nonneg e)))
      (setIntegral_mono_set hneg (Filter.Eventually.of_forall (positiveNormalPotential_nonneg (p + 1) (-e)))
        (Filter.Eventually.of_forall fun _ hx => hx.1))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_QuadraticHyperplaneTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hyperplane tangents from a quadratic support constraint

Blowups turn the quadratic constraint into a halfspace condition, while vanishing
positive normal moments force the limiting support into its boundary hyperplane.
Intrinsic growth then rules out the resulting nonzero tangent measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem blowup_support_quadratic_constraint {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ (blowupMeasure n μ 0 r).support, 0 ≤ 2 * inner ℝ e x + r * ‖x‖ ^ 2 := by
  intro x hx
  have hsource : r • x ∈ μ.support := by
    simpa only [zero_add] using! (blowupMeasure_support_iff n μ 0 x r hr).mp hx
  have h := hquad (r • x) hsource
  rw [inner_smul_right, norm_smul, Real.norm_of_nonneg hr.le] at h
  have hp : 0 ≤ r * (2 * inner ℝ e x + r * ‖x‖ ^ 2) := by nlinarith
  exact nonneg_of_mul_nonneg_right hp hr

theorem quadratic_blowup_limit_support_in_normal_hyperplane {d : ℕ}
    (n : ℕ) (hn : 0 < n) (μ ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (e : Ambient d)
    (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R₀) μ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ 0 (r j)) ν) :
    ∀ x ∈ ν.support, inner ℝ e x = 0 := by
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ 0 (r j)) :=
    fun j => globalGrowth_finite_on_compacts G _ (blowupMeasure_growth n μ 0 (r j) G (hr j) hg)
  have hpositive := compactTestConvergence_support_zero_of_first_moments
    (fun j => blowupMeasure n μ 0 (r j)) ν hlocal (positiveNormalHeight e)
    (positiveNormalHeight_continuous e) (positiveNormalHeight_nonneg e)
    (blowup_positiveNormalHeight_moments_tendsto_zero n hn μ G hg e R₀ hR₀ hi r hr hr0)
  have hnonneg := compactTestConvergence_halfspace_of_quadratic_constraint
    (fun j => blowupMeasure n μ 0 (r j)) ν hlocal e r (fun j => (hr j).le) hr0
    (fun j => blowup_support_quadratic_constraint n μ e hquad (r j) (hr j))
  intro x hx
  have h := le_max_right (0 : ℝ) (inner ℝ e x)
  change inner ℝ e x ≤ positiveNormalHeight e x at h
  rw [hpositive x hx] at h
  exact le_antisymm h (hnonneg x hx)

theorem intrinsic_quadratic_annular_bound_impossible (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (C G : ℝ) (hC : 0 < C)
    (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ (p + 1) / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient (p + 1)) ∈ μ.support)
    (e : Ambient (p + 1)) (he : e ≠ 0)
    (hquad : ∀ x ∈ μ.support, 0 ≤ 2 * inner ℝ e x + ‖x‖ ^ 2)
    (R B : ℝ) (hR : 0 < R)
    (hB : ∀ ε : ℝ, 0 < ε →
      ‖∫ x in ball (0 : Ambient (p + 1)) R ∩ {x | ε < ‖x‖}, kernel (p + 1) x 0 ∂μ‖ ≤ B) : False := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hi := positiveNormalPotential_integrable_of_quadratic_annuli p μ G hg e hquad R B hR hB
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, _hzeroν, _hlowerν⟩ :=
    exists_blowup_measure_limit (p + 1) μ C G hC hg hlower 0 hzero
      (fun j : ℕ => (1 / 2 : ℝ) ^ j) (fun _ => by positivity)
  let := hfinite
  have hplane := quadratic_blowup_limit_support_in_normal_hyperplane (p + 1) (by omega)
    μ ν G hg e hquad R hR hi (fun j => (1 / 2 : ℝ) ^ ρ j) (fun _ => by positivity)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).comp hρ.tendsto_atTop) hlocal
  exact intrinsic_growth_not_supported_in_hyperplane (p + 1) ν (G * 2 ^ (p + 1)) hgν hne e he hplane

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TranslatedRieszAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Translation identifies centered annular Riesz integrals for the unit-scale blowup measure
with annular integrals around the original center, without changing the hard cutoff.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem translated_riesz_annulus_integral {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (ε R : ℝ) :
    (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, kernel n x 0 ∂blowupMeasure n μ a 1) =
      ∫ y in ball a R ∩ {y | ε < dist y a}, kernel n y a ∂μ := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  simp only [blowupMeasure, one_pow, inv_one, ENNReal.ofReal_one, one_smul]
  rw [setIntegral_map
    (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))
    (show AEStronglyMeasurable (fun x : Ambient d => kernel n x 0)
      (μ.map (fun y => y - a)) by unfold kernel; fun_prop) (by fun_prop)]
  have heq : (fun y : Ambient d => y - a) ⁻¹'
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) = ball a R ∩ {y | ε < dist y a} := by
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_ball, mem_ofPred_eq, dist_eq_norm, sub_zero]
  rw [heq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by simp only [kernel, sub_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FullSupportFromAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem intrinsic_full_support_of_local_annular_bounds (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (hμ : μ ≠ 0)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ (p + 1) / C) ≤ μ (ball x R))
    (hannuli : ∀ a ∈ μ.support, ∃ R : ℝ, 0 < R ∧ ∃ B : ℝ,
      ∀ ε : ℝ, 0 < ε →
        ‖∫ y in ball a R ∩ {y | ε < dist y a}, kernel (p + 1) y a ∂μ‖ ≤ B) :
    μ.support = univ := by
  apply eq_univ_of_forall
  intro c
  by_contra hc
  obtain ⟨a, ha, hac, hmin⟩ := exists_nearest_point_to_hole μ.support μ.isClosed_support
    (μ.nonempty_support hμ) c hc
  obtain ⟨R, hR, B, hB⟩ := hannuli a ha
  let σ := blowupMeasure (p + 1) μ a 1
  have hgσ : GlobalUpperGrowth (p + 1) G σ :=
    blowupMeasure_growth (p + 1) μ a 1 G zero_lt_one hg
  have hlowerσ : ∀ x ∈ σ.support, ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (p + 1) / C) ≤ σ (ball x t) :=
    blowupMeasure_lower_global (p + 1) μ a 1 C zero_lt_one hlower
  have hzeroσ : (0 : Ambient (p + 1)) ∈ σ.support :=
    blowupMeasure_origin_mem_support (p + 1) μ a 1 zero_lt_one ha
  have hquad : ∀ x ∈ σ.support, 0 ≤ 2 * inner ℝ (a - c) x + ‖x‖ ^ 2 := by
    intro x hx
    have hsource := (blowupMeasure_support_iff (p + 1) μ a x 1 zero_lt_one).mp hx
    simpa only [one_mul] using! nearest_point_rescaled_constraint a c x 1 zero_lt_one
      (hmin (a + (1 : ℝ) • x) hsource)
  have hBσ : ∀ ε : ℝ, 0 < ε →
      ‖∫ x in ball (0 : Ambient (p + 1)) R ∩ {x | ε < ‖x‖}, kernel (p + 1) x 0 ∂σ‖ ≤ B := by
    intro ε hε
    dsimp only [σ]
    rw [translated_riesz_annulus_integral]
    exact hB ε hε
  exact intrinsic_quadratic_annular_bound_impossible p σ C G hC hgσ hlowerσ hzeroσ
    (a - c) (sub_ne_zero.mpr hac) hquad R B hR hBσ

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_IsometricRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isometric transport of Riesz pairings

Linear isometries intertwine the Riesz kernel and preserve its scalar interior
and far-field integrands. Pulling back balls and closed exteriors then transports
the corresponding scalar pairing to the lower-dimensional ambient space.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem kernel_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (x y : Ambient n) :
    kernel m (L x) (L y) = L (kernel m x y) := by
  simp only [kernel, ← map_sub, L.norm_map, map_smul]

theorem rieszInteriorIntegrand_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (e : Ambient n) (φ : Ambient d → ℝ)
    (q : Ambient n × Ambient n) :
    rieszInteriorIntegrand m (L e) φ (L q.1, L q.2) =
      rieszInteriorIntegrand m e (fun x => φ (L x)) q := by
  simp only [rieszInteriorIntegrand, kernel_linearIsometry, L.inner_map_map]

theorem rieszFarIntegrand_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (e a : Ambient n) (φ : Ambient d → ℝ)
    (q : Ambient n × Ambient n) :
    rieszFarIntegrand m (L e) φ (L a) (L q.1, L q.2) =
      rieszFarIntegrand m e (fun x => φ (L x)) a q := by
  simp only [rieszFarIntegrand, kernel_linearIsometry, ← map_sub, L.inner_map_map]

theorem linearIsometry_pair_integral {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n)) [SFinite μ]
    (A B : Set (Ambient d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (F : Ambient d × Ambient d → ℝ) :
    (∫ q, F q ∂((μ.map L).restrict A).prod ((μ.map L).restrict B)) =
      ∫ q : Ambient n × Ambient n, F (L q.1, L q.2)
        ∂(μ.restrict (L ⁻¹' A)).prod (μ.restrict (L ⁻¹' B)) := by
  rw [Measure.restrict_map L.continuous.measurable hA,
    Measure.restrict_map L.continuous.measurable hB,
    Measure.map_prod_map _ _ L.continuous.measurable L.continuous.measurable]
  exact (L.isometry.isClosedEmbedding.measurableEmbedding.prodMap
    L.isometry.isClosedEmbedding.measurableEmbedding).integral_map F

theorem rieszScalarPairing_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n)) [SFinite μ]
    (a : Ambient n) (R : ℝ) (e : Ambient n) (φ : Ambient d → ℝ) :
    rieszScalarPairing m (μ.map L) (L a) R (L e) φ =
      rieszScalarPairing m μ a R e (fun x => φ (L x)) := by
  have hball : L ⁻¹' ball (L a) R = ball a R := by
    ext x
    simp only [mem_preimage, mem_ball, L.dist_map]
  have hext : L ⁻¹' closedExterior (L a) R = closedExterior a R := by
    ext x
    simp only [mem_preimage, closedExterior, mem_ofPred_eq, L.dist_map]
  unfold rieszScalarPairing
  dsimp only
  rw [linearIsometry_pair_integral L μ (ball (L a) R) (ball (L a) R)
      measurableSet_ball measurableSet_ball,
    linearIsometry_pair_integral L μ (ball (L a) R) (closedExterior (L a) R)
      measurableSet_ball (closedExterior_measurable (L a) R)]
  simp only [hball, hext, rieszInteriorIntegrand_linearIsometry,
    rieszFarIntegrand_linearIsometry]

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

theorem restrict_ball_nested {d : ℕ} (μ : Measure (Ambient d))
    (a : Ambient d) (R T : ℝ) (hRT : R ≤ T) :
    (μ.restrict (ball a T)).restrict (ball a R) = μ.restrict (ball a R) := by
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr (ball_subset_ball hRT)]

theorem rieszScalarPairing_restrict_ball {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    [SFinite μ]
    (a : Ambient d) (R T : ℝ) (hRT : R ≤ T) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing m (μ.restrict (ball a T)) a R e φ =
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) +
      ∫ q in univ ×ˢ ball a T, rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)) := by
  have hcomm : (μ.restrict (ball a T)).restrict (closedExterior a R) =
      (μ.restrict (closedExterior a R)).restrict (ball a T) := by
    rw [Measure.restrict_restrict (closedExterior_measurable a R),
      Measure.restrict_restrict measurableSet_ball, inter_comm]
  have hprod : (μ.restrict (ball a R)).prod ((μ.restrict (closedExterior a R)).restrict (ball a T)) =
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))).restrict (univ ×ˢ ball a T) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  unfold rieszScalarPairing
  dsimp only
  rw [restrict_ball_nested μ a R T hRT, hcomm, hprod]

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

theorem rieszScalarPairing_outer_limit {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    [SFinite μ]
    (a : Ambient d) (R : ℝ) (e : Ambient d) (φ : Ambient d → ℝ)
    (hfar : Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    Tendsto (fun k : ℕ => rieszScalarPairing m (μ.restrict (ball a (outerPairRadius R k))) a R e φ)
      atTop (𝓝 (rieszScalarPairing m μ a R e φ)) := by
  have ht := integral_outer_pair_exhaustion
    ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) a R
    (rieszFarIntegrand m e φ a) hfar
  have heq : (fun k : ℕ => rieszScalarPairing m (μ.restrict (ball a (outerPairRadius R k))) a R e φ) =
      fun k => (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) +
      ∫ q in univ ×ˢ ball a (outerPairRadius R k), rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)) := by
    funext k
    exact rieszScalarPairing_restrict_ball m μ a R _ (outerPairRadius_ge R k) e φ
  rw [heq]
  exact tendsto_const_nhds.add ht

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

theorem rieszInteriorIntegrand_integral_abs_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r) :
    (∫ q, |rieszInteriorIntegrand (p + 1) e φ q| ∂ν.prod ν) ≤
      (‖e‖ * (L : ℝ)) *
        (ν.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))) := by
  have hi := rieszInteriorIntegrand_integrable_of_lipschitz p C ν hg e φ L hφ r hr hdiam
  have hw := nearPairWeight_integrable p C ν hg r hr
  have hb : ∀ᵐ q ∂ν.prod ν, |rieszInteriorIntegrand (p + 1) e φ q| ≤
      (‖e‖ * (L : ℝ)) * nearPairWeight p r q := by
    filter_upwards [hdiam] with q hq
    have hmem : q ∈ nearPairSet r := by
      simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm] using! hq
    rw [nearPairWeight, indicator_of_mem hmem]
    exact rieszInteriorIntegrand_weak_kernel_bound p e φ L hφ q.1 q.2
  calc
    _ ≤ ∫ q, (‖e‖ * (L : ℝ)) * nearPairWeight p r q ∂ν.prod ν :=
      integral_mono_ae hi.abs (hw.const_mul _) hb
    _ = (‖e‖ * (L : ℝ)) * ∫ q, nearPairWeight p r q ∂ν.prod ν :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (nearPairWeight_integral_bound p C ν hg r hr)
      (mul_nonneg (norm_nonneg _) L.coe_nonneg)

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

theorem rieszScalarPairing_compact_lipschitz_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    |rieszScalarPairing (p + 1) μ a R e φ| ≤
      (1 / 2 : ℝ) * ((‖e‖ * (L : ℝ)) *
        (C * R ^ (p + 1) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * (2 * R))))) +
      (2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) *
        (‖e‖ * H * (∫ x in ball a R, |φ x| ∂μ)) *
          (2 * (C * 2 ^ (p + 1) / R)) := by
  have hC : 0 ≤ C := hg.1
  let ν := μ.restrict (ball a R)
  let : IsFiniteMeasure ν :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have hnear := rieszInteriorIntegrand_integral_abs_bound p C ν
    (globalGrowth_restrict (p + 1) C μ hg (ball a R)) e φ L hφ
    (2 * R) (by positivity) (ball_restriction_pair_diameter μ a R)
  have hmass := ball_restriction_mass_bound (p + 1) C μ hg a R hR
  have hfar := rieszFarIntegrand_integral_abs_bound (p + 1) C μ hg e φ L hφ
    a H R hH hR hHR hsupport
  simp only [Nat.cast_add, Nat.cast_one] at hfar
  have hn : |∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν| ≤
      (‖e‖ * (L : ℝ)) *
        (C * R ^ (p + 1) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * (2 * R)))) := by
    apply abs_integral_le_integral_abs.trans
    apply hnear.trans
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmass (by positivity)) (by positivity)
  have hf := abs_integral_le_integral_abs.trans hfar
  unfold rieszScalarPairing
  dsimp only
  apply (abs_add_le _ _).trans
  apply add_le_add _ hf
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left hn (by norm_num)

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

theorem exists_normalized_ball_bump {d : ℕ} (n : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ) (hc : 0 < c)
    (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (hmass : ENNReal.ofReal (c * r ^ n) ≤ μ (ball a r)) :
    ∃ (φ : Ambient d → ℝ) (L : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith L φ ∧
      (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≠ 0 → dist x a ≤ 2 * r) ∧
      (∫ x, φ x ∂μ) = 1 ∧ (L : ℝ) ≤ (c * r ^ (n + 1))⁻¹ := by
  let := hg.finite_on_compacts
  let b := scaledBallBump a r
  let M := ∫ x, b x ∂μ
  have hfinite : μ (ball a r) ≠ ∞ :=
    ((hg.2 a r hr).trans_lt ENNReal.ofReal_lt_top).ne
  have hl : c * r ^ n ≤ M := by
    have ht := ENNReal.toReal_mono hfinite hmass
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    exact ht.trans (scaledBallBump_integral_lower μ a r hr)
  have hM : 0 < M := (mul_pos hc (pow_pos hr n)).trans_le hl
  let φ := fun x => M⁻¹ * b x
  let L : ℝ≥0 := ‖M⁻¹‖₊ * Real.toNNReal r⁻¹
  refine ⟨φ, L, (scaledBallBump_hasCompactSupport a r hr).mul_left,
    lipschitz_const_mul_real (scaledBallBump_lipschitz a r hr) M⁻¹, ?_, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hM.le) (scaledBallBump_bounds a r x).1
  · intro x hx
    apply scaledBallBump_support_bound a r hr x
    intro hb
    exact hx (by simp only [φ, b, hb, mul_zero])
  · change (∫ x, M⁻¹ * b x ∂μ) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hM.ne'
  · change ((‖M⁻¹‖₊ : ℝ) * (Real.toNNReal r⁻¹ : ℝ)) ≤ _
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM),
      Real.coe_toNNReal r⁻¹ (inv_nonneg.mpr hr.le)]
    calc
      _ ≤ (c * r ^ n)⁻¹ * r⁻¹ := mul_le_mul_of_nonneg_right
        (by simpa only [one_div] using! one_div_le_one_div_of_le (by positivity : 0 < c * r ^ n) hl)
        (inv_nonneg.mpr hr.le)
      _ = _ := by rw [pow_succ, ← mul_assoc, mul_inv_rev]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedBumpPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem normalizedBumpPairingBound_nonneg (p : ℕ) (C c : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) : 0 ≤ normalizedBumpPairingBound p C c := by
  unfold normalizedBumpPairingBound
  positivity

theorem normalized_bump_pairing_uniform_bound {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (hnonneg : ∀ x, 0 ≤ φ x) (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ 2 * r)
    (hmean : (∫ x, φ x ∂μ) = 1)
    (hL : (L : ℝ) ≤ (c * r ^ (p + 1 + 1))⁻¹) (e : Ambient d) :
    |rieszScalarPairing (p + 1) μ a (4 * r) e φ| ≤
      ‖e‖ * normalizedBumpPairingBound p C c := by
  have hC : 0 ≤ C := hg.1
  have hφzero : ∀ x ∉ ball a (4 * r), φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : 2 * r < 4 * r))
  have hmass : (∫ x in ball a (4 * r), |φ x| ∂μ) = 1 := by
    simp only [abs_of_nonneg (hnonneg _)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hφzero, hmean]
  have hb := rieszScalarPairing_compact_lipschitz_bound p C μ hg e φ L hφ a
    (2 * r) (4 * r) (by positivity) (by positivity) (by linarith) hsupport
  rw [hmass] at hb
  calc
    _ ≤ _ := hb
    _ ≤ (1 / 2 : ℝ) * ((‖e‖ * (c * r ^ (p + 1 + 1))⁻¹) *
        (C * (4 * r) ^ (p + 1) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * (2 * (4 * r)))))) +
        (2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) *
          (‖e‖ * (2 * r) * 1) * (2 * (C * 2 ^ (p + 1) / (4 * r))) := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL (norm_nonneg _)) (by positivity)
    _ = _ := by
      unfold normalizedBumpPairingBound
      simp only [mul_pow, pow_succ]
      field_simp
      ring

theorem exists_uniformly_bounded_normalized_bump {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (hmass : ENNReal.ofReal (c * r ^ (p + 1)) ≤ μ (ball a r)) :
    ∃ (φ : Ambient d → ℝ) (L : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith L φ ∧ (∀ x, 0 ≤ φ x) ∧
      (∀ x, φ x ≠ 0 → dist x a ≤ 2 * r) ∧ (∫ x, φ x ∂μ) = 1 ∧
      ∀ e : Ambient d, |rieszScalarPairing (p + 1) μ a (4 * r) e φ| ≤
        ‖e‖ * normalizedBumpPairingBound p C c := by
  obtain ⟨φ, L, hcomp, hφ, hn, hs, hm, hL⟩ :=
    exists_normalized_ball_bump (p + 1) C c μ hg hc a r hr hmass
  exact ⟨φ, L, hcomp, hφ, hn, hs, hm,
    fun e => normalized_bump_pairing_uniform_bound p C c μ hg hc a r hr φ L hφ hn hs hm hL e⟩

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszPairingMeanCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean corrections for localized Riesz pairings

Subtracting the center kernel separates a far-field pairing into its renormalized
part and a correction proportional to the test function's integral. Comparing
localization radii expresses their difference through this mean and a shell integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem riesz_far_integral_with_mean_correction {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν)
    (a : Ambient d) (hk : Integrable (fun y => inner ℝ e (kernel m a y)) η)
    (hraw : Integrable (rieszRawCrossIntegrand m e φ) (ν.prod η)) :
    Integrable (rieszFarIntegrand m e φ a) (ν.prod η) ∧
      (∫ q, rieszRawCrossIntegrand m e φ q ∂ν.prod η) =
        (∫ q, rieszFarIntegrand m e φ a q ∂ν.prod η) +
          (∫ x, φ x ∂ν) * (∫ y, inner ℝ e (kernel m a y) ∂η) := by
  have hcorrection := hφ.mul_prod hk
  have heq : rieszFarIntegrand m e φ a = fun q =>
      rieszRawCrossIntegrand m e φ q - φ q.1 * inner ℝ e (kernel m a q.2) := by
    funext q
    unfold rieszFarIntegrand rieszRawCrossIntegrand
    rw [inner_sub_right]
    ring
  rw [heq]
  refine ⟨hraw.sub hcorrection, ?_⟩
  rw [integral_sub hraw hcorrection,
    integral_prod_mul φ (fun y => inner ℝ e (kernel m a y))]
  ring

theorem finite_pairing_eq_renormalized_with_mean {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν) (hφzero : ∀ x ∉ ball a R, φ x = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
      rieszScalarPairing m ν a R e φ +
        (∫ x, φ x ∂ν) * (∫ y in closedExterior a R, inner ℝ e (kernel m a y) ∂ν) := by
  obtain ⟨hraw, hsplit⟩ := riesz_pairing_split m e ν (ball a R) measurableSet_ball φ hφzero hF
  rw [← closedExterior_eq_compl_ball a R] at hraw hsplit
  have hk := Integrable.const_inner (𝕜 := ℝ) e
    (center_kernel_integrable_finite_exterior m ν a R hR)
  have heq := (riesz_far_integral_with_mean_correction m e
    (ν.restrict (ball a R)) (ν.restrict (closedExterior a R)) φ hφ.restrict a hk hraw).2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hφzero] at heq
  rw [hsplit, heq]
  unfold rieszScalarPairing
  dsimp only
  ring

theorem finite_rieszScalarPairing_radius_difference {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν)
    (hφzero : ∀ x ∉ ball a r, φ x = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    rieszScalarPairing m ν a R e φ - rieszScalarPairing m ν a r e φ =
      (∫ x, φ x ∂ν) * (∫ y in ball a R \ ball a r, inner ℝ e (kernel m a y) ∂ν) := by
  have hR : 0 < R := hr.trans_le hrR
  have hφzeroR : ∀ x ∉ ball a R, φ x = 0 :=
    fun x hx => hφzero x (fun hin => hx ((ball_subset_ball hrR) hin))
  have hs := finite_pairing_eq_renormalized_with_mean m e ν a r hr φ hφ hφzero hF
  have ht := finite_pairing_eq_renormalized_with_mean m e ν a R hR φ hφ hφzeroR hF
  have hk := Integrable.const_inner (𝕜 := ℝ) e
    (center_kernel_integrable_finite_exterior m ν a r hr)
  have hsub : closedExterior a R ⊆ closedExterior a r := fun _ hy => hrR.trans hy
  have hdiff := setIntegral_sdiff (closedExterior_measurable a R) hk hsub
  have hset : closedExterior a r \ closedExterior a R = ball a R \ ball a r := by
    ext y
    simp only [closedExterior_eq_compl_ball, Set.mem_sdiff, mem_compl_iff, not_not]
    tauto
  rw [hset] at hdiff
  rw [hdiff]
  nlinarith [hs, ht]

theorem rieszScalarPairing_radius_difference {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H r R : ℝ) (hH : 0 ≤ H) (hr : 0 < r)
    (hHr : 2 * H ≤ r) (hrR : r ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    rieszScalarPairing (p + 1) μ a R e φ - rieszScalarPairing (p + 1) μ a r e φ =
      (∫ x, φ x ∂μ) *
        (∫ y in ball a R \ ball a r, inner ℝ e (kernel (p + 1) a y) ∂μ) := by
  have hR : 0 < R := hr.trans_le hrR
  have hφzero : ∀ x ∉ ball a r, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : H < r))
  have hfarR := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg
    e φ L hφ a H R hH hR (hHr.trans hrR) hsupport
  have hfarr := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg
    e φ L hφ a H r hH hr hHr hsupport
  have hlimR := rieszScalarPairing_outer_limit (p + 1) μ a R e φ hfarR
  have hlimr := rieszScalarPairing_outer_limit_at_center (p + 1) μ a a r R
    (by simpa only [dist_self, add_zero] using! hrR) e φ hfarr
  have ht := hlimR.sub hlimr
  have heq : (fun k : ℕ =>
      rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius R k))) a R e φ -
        rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius R k))) a r e φ) =
      fun _ => (∫ x, φ x ∂μ) *
        (∫ y in ball a R \ ball a r, inner ℝ e (kernel (p + 1) a y) ∂μ) := by
    funext k
    let T := outerPairRadius R k
    let ν := μ.restrict (ball a T)
    have hRT : R ≤ T := outerPairRadius_ge R k
    have hT : 0 < T := hR.trans_le hRT
    let : IsFiniteMeasure ν :=
      finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a T hT
    have hφI : Integrable φ ν :=
      (lipschitz_height_memLp_on_ball (p + 1) C μ hg φ L hφ a T hT).integrable (by norm_num)
    have hF := rieszInteriorIntegrand_integrable_of_lipschitz p C ν
      (globalGrowth_restrict (p + 1) C μ hg (ball a T)) e φ L hφ (2 * T) (by positivity)
      (ball_restriction_pair_diameter μ a T)
    have hid := finite_rieszScalarPairing_radius_difference (p + 1) e ν a r R hr hrR
      φ hφI hφzero hF
    have hm : (∫ x, φ x ∂ν) = ∫ x, φ x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hφzero x (fun hin => hx ((ball_subset_ball (hrR.trans hRT)) hin)))
    have hμshell : ν.restrict (ball a R \ ball a r) = μ.restrict (ball a R \ ball a r) := by
      rw [show ν = μ.restrict (ball a T) from rfl,
        Measure.restrict_restrict (measurableSet_ball.diff measurableSet_ball),
        inter_eq_left.mpr (sdiff_subset.trans (ball_subset_ball hRT))]
    rw [hm, hμshell] at hid
    exact hid
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem rieszScalarPairing_sub_of_integrable {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (a : Ambient d) (R : ℝ) (e : Ambient d)
    (φ ψ : Ambient d → ℝ)
    (hIφ : Integrable (rieszInteriorIntegrand m e φ)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))))
    (hIψ : Integrable (rieszInteriorIntegrand m e ψ)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))))
    (hFφ : Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))))
    (hFψ : Integrable (rieszFarIntegrand m e ψ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    rieszScalarPairing m μ a R e (fun x => φ x - ψ x) =
      rieszScalarPairing m μ a R e φ - rieszScalarPairing m μ a R e ψ := by
  have hi : rieszInteriorIntegrand m e (fun x => φ x - ψ x) =
      fun q => rieszInteriorIntegrand m e φ q - rieszInteriorIntegrand m e ψ q := by
    funext q
    unfold rieszInteriorIntegrand
    ring
  have hf : rieszFarIntegrand m e (fun x => φ x - ψ x) a =
      fun q => rieszFarIntegrand m e φ a q - rieszFarIntegrand m e ψ a q := by
    funext q
    unfold rieszFarIntegrand
    ring
  unfold rieszScalarPairing
  dsimp only
  rw [hi, hf, integral_sub hIφ hIψ, integral_sub hFφ hFψ]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_ReflectionlessAnnularBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Annular bounds from scalar reflectionlessness

Scalar reflectionlessness annihilates localized pairings against mean-zero test
functions. Comparing normalized bumps at two radii bounds centered annular kernel
integrals, first in each scalar direction and then in the ambient Euclidean norm.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem reflectionless_centered_annular_scalar_bound {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d)
    (hlower : ∀ t : ℝ, 0 < t → ENNReal.ofReal (c * t ^ (p + 1)) ≤ μ (ball a t))
    (hreflect : ScalarReflectionlessAt (p + 1) μ a)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (e : Ambient d) :
    |∫ y in ball a R \ ball a r, inner ℝ e (kernel (p + 1) a y) ∂μ| ≤
      2 * ‖e‖ * normalizedBumpPairingBound p C c := by
  have hR : 0 < R := hr.trans_le hrR
  let := hg.finite_on_compacts
  let : IsFiniteMeasure (μ.restrict (ball a R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  obtain ⟨φ, L, hcφ, hφ, _hnφ, hsφ, hmφ, hbφ⟩ :=
    exists_uniformly_bounded_normalized_bump p C c μ hg hc a (r / 4) (by positivity)
      (hlower _ (by positivity))
  obtain ⟨ψ, K, hcψ, hψ, _hnψ, hsψ, hmψ, hbψ⟩ :=
    exists_uniformly_bounded_normalized_bump p C c μ hg hc a (R / 4) (by positivity)
      (hlower _ (by positivity))
  have hsmall : ∀ x, φ x ≠ 0 → dist x a ≤ R / 2 := by
    intro x hx
    have ht := hsφ x hx
    linarith
  have hlarge : ∀ x, ψ x ≠ 0 → dist x a ≤ R / 2 := by
    intro x hx
    have ht := hsψ x hx
    linarith
  have hdiffsupport : ∀ x, φ x - ψ x ≠ 0 → dist x a ≤ R / 2 := by
    intro x hx
    by_cases hφx : φ x = 0
    · apply hlarge x
      intro hψx
      exact hx (by rw [hφx, hψx, sub_self])
    · exact hsmall x hφx
  have hiφ : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hiψ : Integrable ψ μ := hψ.continuous.integrable_of_hasCompactSupport hcψ
  have hmean : (∫ x, φ x - ψ x ∂μ) = 0 := by
    rw [integral_sub hiφ hiψ, hmφ, hmψ, sub_self]
  have hz := hreflect e (fun x => φ x - ψ x) (L + K) (R / 2) R
    (hφ.sub hψ) (by positivity) hR (by linarith) hdiffsupport hmean
  have hIφ := rieszInteriorIntegrand_integrable_of_lipschitz p C (μ.restrict (ball a R))
    (globalGrowth_restrict (p + 1) C μ hg (ball a R)) e φ L hφ (2 * R) (by positivity)
    (ball_restriction_pair_diameter μ a R)
  have hIψ := rieszInteriorIntegrand_integrable_of_lipschitz p C (μ.restrict (ball a R))
    (globalGrowth_restrict (p + 1) C μ hg (ball a R)) e ψ K hψ (2 * R) (by positivity)
    (ball_restriction_pair_diameter μ a R)
  have hFφ := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ
    a (R / 2) R (by positivity) hR (by linarith) hsmall
  have hFψ := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e ψ K hψ
    a (R / 2) R (by positivity) hR (by linarith) hlarge
  rw [rieszScalarPairing_sub_of_integrable (p + 1) μ a R e φ ψ hIφ hIψ hFφ hFψ] at hz
  have hequal : rieszScalarPairing (p + 1) μ a R e φ =
      rieszScalarPairing (p + 1) μ a R e ψ := sub_eq_zero.mp hz
  have hid := rieszScalarPairing_radius_difference p C μ hg e φ L hφ a (2 * (r / 4))
    r R (by positivity) hr (by linarith) hrR hsφ
  rw [hmφ, one_mul, hequal] at hid
  have hbsmall := hbφ e
  have hbbig := hbψ e
  rw [show 4 * (r / 4) = r by ring] at hbsmall
  rw [show 4 * (R / 4) = R by ring] at hbbig
  rw [← hid]
  calc
    _ ≤ |rieszScalarPairing (p + 1) μ a R e ψ| +
        |rieszScalarPairing (p + 1) μ a r e φ| := by
      simpa only [sub_zero, zero_sub, abs_neg] using!
        abs_sub_le (rieszScalarPairing (p + 1) μ a R e ψ) 0
          (rieszScalarPairing (p + 1) μ a r e φ)
    _ ≤ ‖e‖ * normalizedBumpPairingBound p C c +
        ‖e‖ * normalizedBumpPairingBound p C c := add_le_add hbbig hbsmall
    _ = _ := by ring

theorem reflectionless_centered_annular_vector_bound {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d)
    (hlower : ∀ t : ℝ, 0 < t → ENNReal.ofReal (c * t ^ (p + 1)) ≤ μ (ball a t))
    (hreflect : ScalarReflectionlessAt (p + 1) μ a)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ‖∫ y in ball a R \ ball a r, kernel (p + 1) a y ∂μ‖ ≤
      2 * normalizedBumpPairingBound p C c := by
  have hR : 0 < R := hr.trans_le hrR
  let : IsFiniteMeasure (μ.restrict (ball a R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have hk : IntegrableOn (kernel (p + 1) a) (ball a R \ ball a r) μ := by
    have h := center_kernel_integrable_finite_exterior (p + 1) (μ.restrict (ball a R)) a r hr
    have hset : closedExterior a r ∩ ball a R = ball a R \ ball a r := by
      ext y
      simp only [closedExterior_eq_compl_ball, mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rwa [IntegrableOn, Measure.restrict_restrict (closedExterior_measurable a r), hset] at h
  let v := ∫ y in ball a R \ ball a r, kernel (p + 1) a y ∂μ
  have hb := reflectionless_centered_annular_scalar_bound p C c μ hg hc a hlower hreflect r R hr hrR v
  have heq : (∫ y in ball a R \ ball a r, inner ℝ v (kernel (p + 1) a y) ∂μ) =
      inner ℝ v v := integral_inner (𝕜 := ℝ) hk v
  rw [heq, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hb
  have hD := normalizedBumpPairingBound_nonneg p C c hg.1 hc
  by_cases hv : ‖v‖ = 0
  · change ‖v‖ ≤ _
    rw [hv]
    positivity
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    change ‖v‖ ≤ _
    nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_ReflectionlessFullSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Full intrinsic support of reflectionless measures

Monotone approximation of strict annuli extends the centered annular vector estimate
without a boundary-mass assumption. Kernel antisymmetry then puts these bounds in the
form needed by the intrinsic full-support criterion. Thus a nonzero reflectionless
measure with global upper growth and support-centered lower growth fills its ambient
space when the growth exponent equals the ambient dimension.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem reflectionless_strict_annular_vector_bound {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d)
    (hlower : ∀ t : ℝ, 0 < t → ENNReal.ofReal (c * t ^ (p + 1)) ≤ μ (ball a t))
    (hreflect : ScalarReflectionlessAt (p + 1) μ a)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) :
    ‖∫ y in ball a R ∩ {y | ε < dist y a}, kernel (p + 1) a y ∂μ‖ ≤
      2 * normalizedBumpPairingBound p C c := by
  have hD := normalizedBumpPairingBound_nonneg p C c hg.1 hc
  by_cases hεR : ε < R
  · let r := fun j : ℕ => ε + (R - ε) * (1 / 2 : ℝ) ^ j
    have hrε (j : ℕ) : ε < r j := by
      dsimp only [r]
      have hp : 0 < (R - ε) * (1 / 2 : ℝ) ^ j :=
        mul_pos (sub_pos.mpr hεR) (pow_pos (by norm_num) j)
      linarith
    have hrpos (j : ℕ) : 0 < r j := hε.trans (hrε j)
    have hrR (j : ℕ) : r j ≤ R := by
      have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hεR.le)
      dsimp only [r]
      linarith
    have hrmono : Antitone r := by
      intro i j hij
      have hp : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ i :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
      change ε + (R - ε) * (1 / 2 : ℝ) ^ j ≤ ε + (R - ε) * (1 / 2 : ℝ) ^ i
      linarith [mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hεR.le)]
    have hrlim : Tendsto r atTop (𝓝 ε) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      simpa only [mul_zero, add_zero] using!
        tendsto_const_nhds.add (hp.const_mul (R - ε))
    let s := fun j : ℕ => ball a R \ ball a (r j)
    have hsm (j : ℕ) : MeasurableSet (s j) := measurableSet_ball.diff measurableSet_ball
    have hsmono : Monotone s := by
      intro i j hij
      exact sdiff_subset_sdiff_right (ball_subset_ball (hrmono hij))
    have hcover : (⋃ j, s j) = ball a R ∩ {y | ε < dist y a} := by
      ext y
      constructor
      · intro hy
        obtain ⟨j, hj⟩ := mem_iUnion.mp hy
        have hd : r j ≤ dist y a := le_of_not_gt hj.2
        exact ⟨hj.1, (hrε j).trans_le hd⟩
      · intro hy
        obtain ⟨j, hj⟩ := (hrlim.eventually (gt_mem_nhds hy.2)).exists
        exact mem_iUnion.mpr ⟨j, hy.1, not_lt.mpr hj.le⟩
    let : IsFiniteMeasure (μ.restrict (ball a R)) :=
      finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
    have hk : IntegrableOn (kernel (p + 1) a)
        (ball a R ∩ {y | ε < dist y a}) μ := by
      have hbase := center_kernel_integrable_finite_exterior (p + 1)
        (μ.restrict (ball a R)) a ε hε
      have hsub : {y : Ambient d | ε < dist y a} ⊆ closedExterior a ε := by
        intro y hy
        simpa only [closedExterior, mem_ofPred_eq, dist_comm a y] using! hy.le
      have h := hbase.mono_set hsub
      have hmeas : MeasurableSet {y : Ambient d | ε < dist y a} :=
        measurableSet_lt measurable_const (continuous_id.dist continuous_const).measurable
      rw [IntegrableOn, Measure.restrict_restrict hmeas,
        inter_comm] at h
      exact h
    have ht := tendsto_setIntegral_of_monotone hsm hsmono
      (show IntegrableOn (kernel (p + 1) a) (⋃ j, s j) μ by rw [hcover]; exact hk)
    rw [hcover] at ht
    exact le_of_tendsto ht.norm (Eventually.of_forall fun j =>
      reflectionless_centered_annular_vector_bound p C c μ hg hc a hlower hreflect
        (r j) R (hrpos j) (hrR j))
  · have hs : ball a R ∩ {y : Ambient d | ε < dist y a} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hεR (hy.2.trans hy.1)
    rw [hs, Measure.restrict_empty, integral_zero_measure, norm_zero]
    positivity

theorem norm_integral_reverse_kernel {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) :
    ‖∫ y, kernel n y a ∂μ‖ = ‖∫ y, kernel n a y ∂μ‖ := by
  have heq : (fun y : Ambient d => kernel n y a) = fun y => -kernel n a y := by
    funext y
    exact kernel_antisymm (d := d) n a y
  rw [heq, integral_neg, norm_neg]

theorem intrinsic_full_support_of_reflectionless (p : ℕ)
    (μ : Measure (Ambient (p + 1))) [SFinite μ] (hμ : μ ≠ 0)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ (p + 1) / C) ≤ μ (ball x R))
    (hreflect : ∀ a ∈ μ.support, ScalarReflectionlessAt (p + 1) μ a) :
    μ.support = univ := by
  apply intrinsic_full_support_of_local_annular_bounds p μ hμ C G hC hg hlower
  intro a ha
  refine ⟨1, zero_lt_one, 2 * normalizedBumpPairingBound p G C⁻¹, ?_⟩
  intro ε hε
  have hl : ∀ t : ℝ, 0 < t → ENNReal.ofReal (C⁻¹ * t ^ (p + 1)) ≤ μ (ball a t) := by
    intro t ht
    convert! hlower a ha t ht using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hb := reflectionless_strict_annular_vector_bound (d := p + 1) p G C⁻¹ μ hg (inv_pos.mpr hC)
    a hl (hreflect a ha) ε 1 hε zero_lt_one
  rw [norm_integral_reverse_kernel]
  exact hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_PlanarReflectionlessSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reflectionless measures supported on a plane

Compactly supported plane tests extend to ambient tests, allowing the isometric
pullback of a plane-supported measure to inherit reflectionlessness. Upper and lower
growth bounds then give full support in the intrinsic coordinates. Recovering the
ambient measure identifies its support with the entire isometric plane.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem planarPullbackMeasure_reflectionless {p d : ℕ}
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (ν : Measure (Ambient d))
    (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G ν) (a : Ambient (p + 1))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a)) :
    ScalarReflectionlessAt (p + 1) (planarPullbackMeasure L ν) a := by
  let μ := planarPullbackMeasure L ν
  have hgμ : GlobalUpperGrowth (p + 1) G μ := planarPullbackMeasure_growth L ν hs G hg
  let := hgμ.finite_on_compacts
  have hrec : μ.map L = ν := planarPullbackMeasure_recover L ν hs
  intro e φ K H R hφ hH hR hHR hsφ hmean
  have hc : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall a H)
    intro x hx
    by_contra hn
    exact hx (hsφ x hn)
  let B : ℝ≥0 := Real.toNNReal ((K : ℝ) * H + |φ a|)
  have hB : ∀ x, |φ x| ≤ (B : ℝ) := by
    intro x
    by_cases hx : φ x = 0
    · rw [hx, abs_zero]
      exact B.coe_nonneg
    have hd : |φ x - φ a| ≤ (K : ℝ) * H := by
      have h := hφ.dist_le_mul x a
      rw [Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hsφ x hx) K.coe_nonneg)
    have ht := abs_add_le (φ x - φ a) (φ a)
    rw [sub_add_cancel] at ht
    exact (ht.trans (add_le_add hd le_rfl)).trans (Real.le_coe_toNNReal _)
  obtain ⟨ψ, Kψ, hcψ, hψ, _hBψ, hext, _hIvolume, _hmeanvolume⟩ :=
    exists_compact_ambient_plane_test (0 : Ambient d) L φ hc K B hφ hB
  simp only [zero_add] at hext
  have hmeanψ : (∫ x, ψ x ∂ν) = 0 := by
    rw [← hrec, L.isometry.isClosedEmbedding.measurableEmbedding.integral_map]
    exact (integral_congr_ae (Eventually.of_forall hext)).trans hmean
  obtain ⟨J, hJ, hJs⟩ := hcψ.isBounded.subset_closedBall_lt 0 (L a)
  have hsψ : ∀ x, ψ x ≠ 0 → dist x (L a) ≤ J := by
    intro x hx
    exact hJs (subset_tsupport ψ hx)
  let S := max (2 * J) (2 * H) + 1
  have hS : 0 < S := by
    have h := le_max_left (2 * J) (2 * H)
    dsimp only [S]
    linarith
  have hJS : 2 * J ≤ S := by dsimp only [S] <;> linarith [le_max_left (2 * J) (2 * H)]
  have hHS : 2 * H ≤ S := by dsimp only [S] <;> linarith [le_max_right (2 * J) (2 * H)]
  have hz := hreflect (L e) ψ Kψ J S hψ hJ.le hS hJS hsψ hmeanψ
  have hpair : rieszScalarPairing (p + 1) ν (L a) S (L e) ψ =
      rieszScalarPairing (p + 1) μ a S e φ := by
    rw [← hrec, rieszScalarPairing_linearIsometry]
    congr 1
    exact funext hext
  have hlocal := rieszScalarPairing_localization_independent p G μ hgμ e φ K hφ
    a a H H R S hH hH hR hS hHR hHS hsφ hsφ hmean
  exact hlocal.trans (hpair.symm.trans hz)

theorem planar_full_support_of_reflectionless_oai {p d : ℕ}
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (ν : Measure (Ambient d)) (hne : ν ≠ 0)
    (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ ν (ball x r))
    (hreflect : ∀ a ∈ ν.support, ScalarReflectionlessAt (p + 1) ν a) :
    (planarPullbackMeasure L ν).support = univ ∧
      ν.support = (L.toLinearMap.range : Set (Ambient d)) := by
  have hgμ := planarPullbackMeasure_growth L ν hs G hg
  let := hgμ.finite_on_compacts
  have hfull : (planarPullbackMeasure L ν).support = univ :=
    intrinsic_full_support_of_reflectionless p (planarPullbackMeasure L ν)
      (planarPullbackMeasure_ne_zero L ν hs hne) C G hC hgμ
      (planarPullbackMeasure_lower L ν hs C hlower)
      (fun a ha => planarPullbackMeasure_reflectionless L ν hs G hg a
        (hreflect (L a) ((planarPullbackMeasure_support_iff L ν hs a).mp ha)))
  refine ⟨hfull, Set.Subset.antisymm hs ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hx
  change L y = x at hy
  rw [← hy]
  apply (planarPullbackMeasure_support_iff L ν hs y).mp
  rw [hfull]
  exact mem_univ y

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.planar_full_support_of_reflectionless_oai := @OAI.RieszRectifiability.planar_full_support_of_reflectionless_oai
