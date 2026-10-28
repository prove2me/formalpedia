-- Prove2me | solution 1 for OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:25:31.103018+00:00
-- url     : https://prove2.me/submissions/87383a5a-8b90-46b1-a74a-bcb922ca6b26

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff Topology

theorem angularBinKernel_contDiff : ContDiff ℝ ∞ angularBinKernel :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem angularBinKernel_nonneg (t : ℝ) : 0 ≤ angularBinKernel t :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem angularBinKernel_two_terms {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    angularBinKernel t + angularBinKernel (t-1) = 1 := by
  unfold angularBinKernel
  rw [Real.smoothTransition.one_of_one_le (show 1 ≤ t+1 by linarith),
    Real.smoothTransition.zero_of_nonpos (show t-1 ≤ 0 by linarith),
    sub_add_cancel]
  ring

theorem angularBinKernel_translate_zero (t : ℝ) (k : ℤ)
    (hk : k ≠ ⌊t⌋ ∧ k ≠ ⌊t⌋+1) : angularBinKernel (t-k) = 0 := by
  have hlow := Int.floor_le t
  have hhigh := Int.lt_floor_add_one t
  by_cases h : k ≤ ⌊t⌋-1
  · apply angularBinKernel_zero_right
    have hh : (k : ℝ) ≤ (⌊t⌋ : ℝ)-1 := by exact_mod_cast h
    linarith
  · apply angularBinKernel_zero_left
    have hh : ⌊t⌋+2 ≤ k := by omega
    have hh : (⌊t⌋ : ℝ)+2 ≤ (k : ℝ) := by exact_mod_cast hh
    linarith

theorem angularBinKernel_floor_partition (t : ℝ) :
    angularBinKernel (t-(⌊t⌋ : ℤ)) + angularBinKernel (t-(⌊t⌋+1 : ℤ)) = 1 := by
  have h := angularBinKernel_two_terms (sub_nonneg.mpr (Int.floor_le t))
    (show t-(⌊t⌋ : ℤ) ≤ 1 by linarith [Int.lt_floor_add_one t])
  simpa only [Int.cast_add, Int.cast_one, sub_add_eq_sub_sub] using h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularBinSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ContDiff Topology

theorem angularBinSelection_two_terms (p : ℤ → Prop) (t : ℝ) :
    angularBinSelection p t =
      (if p ⌊t⌋ then angularBinKernel (t-(⌊t⌋ : ℤ)) else 0) +
      (if p (⌊t⌋+1) then angularBinKernel (t-(⌊t⌋+1 : ℤ)) else 0) := by
  classical
  unfold angularBinSelection
  rw [tsum_eq_sum (s := {⌊t⌋, ⌊t⌋+1})]
  · simp [show ⌊t⌋ ≠ ⌊t⌋+1 by omega]
  · intro k hk
    have hz := angularBinKernel_translate_zero t k (by simpa using hk)
    simp [hz]

theorem angularBinSelection_bounds (p : ℤ → Prop) (t : ℝ) :
    0 ≤ angularBinSelection p t ∧ angularBinSelection p t ≤ 1 := by
  classical
  rw [angularBinSelection_two_terms]
  have h0 := angularBinKernel_nonneg (t-(⌊t⌋ : ℤ))
  have h1 := angularBinKernel_nonneg (t-(⌊t⌋+1 : ℤ))
  have he := angularBinKernel_floor_partition t
  split_ifs <;> constructor <;> linarith

theorem angularBinSelection_local (p : ℤ → Prop) (t : ℝ) :
    angularBinSelection p =ᶠ[𝓝 t] (fun u =>
      ∑ k ∈ Finset.Icc (⌊t⌋-2) (⌊t⌋+3), if p k then angularBinKernel (u-k) else 0) := by
  classical
  filter_upwards [Ioo_mem_nhds (show t-1 < t by linarith) (show t < t+1 by linarith)] with u hu
  unfold angularBinSelection
  apply tsum_eq_sum
  intro k hk
  have hz : angularBinKernel (u-k) = 0 := by
    have hk : k < ⌊t⌋-2 ∨ ⌊t⌋+3 < k := by simpa only [Finset.mem_Icc, not_and_or, not_le] using hk
    rcases hk with hk | hk
    · apply angularBinKernel_zero_right
      have hc : (k : ℝ) < (⌊t⌋ : ℝ)-2 := by exact_mod_cast hk
      linarith [Int.floor_le t, hu.1]
    · apply angularBinKernel_zero_left
      have hc : (⌊t⌋ : ℝ)+3 < (k : ℝ) := by exact_mod_cast hk
      linarith [Int.lt_floor_add_one t, hu.2]
  simp [hz]

theorem angularBinSelection_contDiff (p : ℤ → Prop) : ContDiff ℝ ∞ (angularBinSelection p) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro t
  apply ContDiffAt.congr_of_eventuallyEq _ (angularBinSelection_local p t)
  apply ContDiff.contDiffAt
  apply ContDiff.sum
  intro k _
  by_cases hk : p k
  · simp only [hk, ↓reduceIte]
    exact angularBinKernel_contDiff.comp (contDiff_id.sub contDiff_const)
  · simp only [hk, ↓reduceIte]
    exact contDiff_const

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransformSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem angular_integrand_norm (r : ℝ) (ω : UnitCircle) (x : Plane)
    (b : Plane → UnitCircle → ℂ) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω‖ =
      ‖b x ω‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_PeriodicAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set
open scoped ContDiff Topology

theorem angularBinSelection_periodic (p : ℤ → Prop) (n : ℤ)
    (hp : ∀ k, p (k+n) ↔ p k) : Function.Periodic (angularBinSelection p) (n : ℝ) := by
  intro t
  unfold angularBinSelection
  rw [← (Equiv.addRight n).tsum_eq]
  apply tsum_congr
  intro k
  change (if p (k+n) then angularBinKernel (t+(n:ℝ)-(k+n : ℤ)) else 0) = _
  rw [show t+(n:ℝ)-(k+n : ℤ) = t-k by push_cast; ring]
  simp only [hp]

theorem periodicAngularBin_periodic (n j : ℕ) :
    Function.Periodic (periodicAngularBin n j) (2*Real.pi) := by
  have hp := angularBinSelection_periodic (fun k => (k % (n : ℤ)).toNat = j) (n : ℤ)
    (fun k => by simp)
  intro θ
  unfold periodicAngularBin
  convert hp ((n : ℝ)/(2*Real.pi)*θ) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  field_simp

theorem periodicAngularBin_contDiff (n j : ℕ) : ContDiff ℝ ∞ (periodicAngularBin n j) :=
  (angularBinSelection_contDiff _).comp (contDiff_const.mul contDiff_id)

theorem periodicAngularBin_bounds (n j : ℕ) (θ : ℝ) :
    0 ≤ periodicAngularBin n j θ ∧ periodicAngularBin n j θ ≤ 1 :=
  angularBinSelection_bounds _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedCircleRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem periodic_sourceAngle {f : ℝ → ℝ} (hf : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    f (sourceAngle (sourceUnitDirection θ)) = f θ := by
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := hf.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryArcLength
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

 theorem sourceArcLength_integral_period {F : UnitCircle → ℂ}
    (hF : AEStronglyMeasurable F sourceArcLength) :
    (∫ ω, F ω ∂sourceArcLength) = ∫ θ in (-Real.pi)..Real.pi, F (sourceUnitDirection θ) := by
  have he : (∫ ω, F ω ∂sourceArcLength) = ∫ θ in (0:ℝ)..2*Real.pi, F (sourceUnitDirection θ) := by
    rw [sourceArcLength,integral_map continuous_sourceUnitDirection.measurable.aemeasurable hF]
    exact (intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)).symm
  rw [he]
  have hp : Function.Periodic (fun θ => F (sourceUnitDirection θ)) (2*Real.pi) :=
    fun θ => congrArg F (sourceUnitDirection_periodic θ)
  have hh := hp.intervalIntegral_add_eq 0 (-Real.pi)
  have he' : -Real.pi+2*Real.pi = Real.pi := by ring
  simpa only [zero_add,he'] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleAngularBins
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem circleAngularBin_comp (n j : ℕ) (θ : ℝ) :
    circleAngularBin n j (sourceUnitDirection θ) = periodicAngularBin n j θ :=
  periodic_sourceAngle (periodicAngularBin_periodic n j) θ

 theorem circleAngularBin_continuous (n j : ℕ) : Continuous (circleAngularBin n j) := by
  let A := Icc (-Real.pi) Real.pi
  let : CompactSpace A := isCompact_iff_compactSpace.mp (show IsCompact A from isCompact_Icc)
  let f : A → UnitCircle := fun θ => sourceUnitDirection θ
  have hf : Continuous f := continuous_sourceUnitDirection.comp continuous_subtype_val
  have hs : Function.Surjective f := by
    intro dir
    refine ⟨⟨sourceAngle dir, (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩,
      sourceUnitDirection_sourceAngle dir⟩
  apply (hf.isClosedMap.isQuotientMap hf hs).continuous_iff.mpr
  have he : circleAngularBin n j ∘ f = fun θ : A => periodicAngularBin n j θ := by
    funext θ
    exact circleAngularBin_comp n j θ
  rw [he]
  exact (periodicAngularBin_contDiff n j).continuous.comp continuous_subtype_val

 theorem circleAngularBin_bounds (n j : ℕ) (dir : UnitCircle) :
    0 ≤ circleAngularBin n j dir ∧ circleAngularBin n j dir ≤ 1 :=
  periodicAngularBin_bounds n j (sourceAngle dir)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleRotation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem sourceCircleRotate_integral (axis : ℝ) {F : UnitCircle → ℂ} (hF : Measurable F) :
    (∫ dir, F (sourceCircleRotate axis dir) ∂sourceArcLength) = ∫ dir, F dir ∂sourceArcLength := by
  change (∫ dir, (F ∘ sourceCircleRotate axis) dir ∂sourceArcLength) = _
  rw [sourceArcLength_integral_period
    (hF.comp (sourceCircleRotate_isometry axis).continuous.measurable).aestronglyMeasurable,
    sourceArcLength_integral_period hF.aestronglyMeasurable]
  simp only [Function.comp_def, sourceCircleRotate_comp]
  rw [intervalIntegral.integral_comp_add_right (fun θ => F (sourceUnitDirection θ))]
  have hp : Function.Periodic (fun θ => F (sourceUnitDirection θ)) (2*Real.pi) :=
    fun θ => congrArg F (sourceUnitDirection_periodic θ)
  have hh := hp.intervalIntegral_add_eq (-Real.pi+axis) (-Real.pi)
  convert hh using 1 <;> congr 1 <;> ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCoordinateInverse
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem quarterTurn_smul (r : ℝ) (v : Plane) : quarterTurn (r • v) = r • quarterTurn v := by
  ext i
  fin_cases i <;> simp [quarterTurn]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSignPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem graphSignPlus_contDiff : ContDiff ℝ ∞ graphSignPlus := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_fst.add contDiff_snd).norm_sq ℝ).sub contDiff_const |>.div_const 2)

theorem graphSignMinus_contDiff : ContDiff ℝ ∞ graphSignMinus :=
  contDiff_const.sub graphSignPlus_contDiff

theorem graphSignPartition_bounds (p : Plane × Plane) :
    0 ≤ graphSignPlus p ∧ graphSignPlus p ≤ 1 ∧
    0 ≤ graphSignMinus p ∧ graphSignMinus p ≤ 1 ∧
    graphSignPlus p+graphSignMinus p = 1 := by
  have h₀ := Real.smoothTransition.nonneg ((‖p.1+p.2‖^2-1)/2)
  have h₁ := Real.smoothTransition.le_one ((‖p.1+p.2‖^2-1)/2)
  dsimp [graphSignPlus, graphSignMinus]
  exact ⟨h₀, h₁, sub_nonneg.mpr h₁, sub_le_self _ h₀, by ring⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphAngularCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem sourceDirection_add_arctan (φ z : ℝ) :
    sourceDirection (φ+Real.arctan z) =
      (Real.sqrt (1+z^2))⁻¹ • (sourceDirection φ+z • quarterTurn (sourceDirection φ)) := by
  ext i
  fin_cases i <;>
    simp [sourceDirection, quarterTurn, Complex.orthonormalBasisOneI_repr_apply,
      Real.cos_add, Real.sin_add, Real.cos_arctan, Real.sin_arctan,
      -Complex.ofReal_sin, -Complex.ofReal_cos] <;> ring

theorem sourceDirection_sub_arctan (φ z : ℝ) :
    sourceDirection (φ-Real.arctan z) =
      (Real.sqrt (1+z^2))⁻¹ • (sourceDirection φ-z • quarterTurn (sourceDirection φ)) := by
  simpa only [Real.arctan_neg, neg_sq, neg_smul, sub_eq_add_neg] using
    sourceDirection_add_arctan φ (-z)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ENNReal

theorem sourcePlaneWave_norm (r : ℝ) (ω : UnitCircle) (x : Plane) :
    ‖sourcePlaneWave r ω x‖ = 1 := by
  simpa only [sourcePlaneWave, mul_one, norm_one] using angular_integrand_norm r ω x (fun _ _ => 1)

theorem sourcePlaneWave_sub (r : ℝ) (ω : UnitCircle) (x y : Plane) :
    sourcePlaneWave r ω x * conj (sourcePlaneWave r ω y) =
      sourcePlaneWave r ω (x-y) := by
  simp only [sourcePlaneWave, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, ← Complex.exp_add, inner_sub_right, Complex.ofReal_sub]
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphConeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem graphConeCutoff_contDiff : ContDiff ℝ ∞ graphConeCutoff :=
  Complex.ofRealCLM.contDiff.comp graphConeBump.contDiff

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedConeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

theorem sourceConeCircle_norm_le (axis : ℝ) (dir : UnitCircle) :
    ‖sourceConeCircle axis dir‖ ≤ 1 := by
  simp only [sourceConeCircle, graphConeCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg graphConeBump.nonneg]
  exact graphConeBump.le_one

theorem sourceAngle_comp_on_period {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    sourceAngle (sourceUnitDirection θ) = θ := by
  rw [sourceAngle_sourceUnitDirection]
  exact_mod_cast Complex.arg_cos_add_sin_mul_I hθ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothRotatedCone
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology

theorem periodic_contDiff_of_principal {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi))
    (hf : ∀ θ ∈ Ioc (-Real.pi) Real.pi, ContDiffAt ℝ ∞ f θ) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hr : sourceAngle (sourceUnitDirection θ) ∈ Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hh := hf _ hr
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [sourceAngle_sourceUnitDirection, he] at hh
  let c : ℝ := 2*Real.pi*(⌊(Real.pi-θ)/(2*Real.pi)⌋ : ℤ)
  have ht : ContDiffAt ℝ ∞ (fun t : ℝ => t+c) θ := contDiffAt_id.add contDiffAt_const
  have hc : ContDiffAt ℝ ∞ f (θ+c) := by simpa only [c, add_comm] using hh
  have hcomp := hc.comp θ ht
  have heq : (fun t => f (t+c)) = f := by
    funext t
    simpa only [c, mul_comm] using hp.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋ t
  simpa only [Function.comp_def, heq] using hcomp

theorem sourceConeCircle_angular_contDiff :
    ContDiff ℝ ∞ (fun θ => sourceConeCircle 0 (sourceUnitDirection θ)) := by
  let f : ℝ → ℂ := fun θ => sourceConeCircle 0 (sourceUnitDirection θ)
  have hp : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg (sourceConeCircle 0) (sourceUnitDirection_periodic θ)
  have hlocal {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) : f θ = graphConeCutoff θ := by
    simp only [f, sourceConeCircle, neg_zero, sourceCircleRotate_zero, sourceAngle_comp_on_period hθ]
  have hzero (θ : ℝ) (hc : Real.cos θ < 0) : f θ = 0 := by
    by_contra hn
    have hs : sourceAngle (sourceUnitDirection θ) ∈ Icc (-1/5 : ℝ) (1/5) := by
      apply graphConeCutoff_support
      apply subset_closure
      simpa only [Function.mem_support, f, sourceConeCircle, neg_zero, sourceCircleRotate_zero] using hn
    have hcos : 0 ≤ Real.cos (sourceAngle (sourceUnitDirection θ)) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by have := Real.one_le_pi_div_two; linarith [hs.1])
        (by have := Real.one_le_pi_div_two; linarith [hs.2])
    have he := periodic_sourceAngle (show Function.Periodic Real.cos (2*Real.pi) from Real.cos_periodic) θ
    rw [he] at hcos
    linarith
  apply periodic_contDiff_of_principal hp
  intro θ hθ
  by_cases hlt : θ < Real.pi
  · apply graphConeCutoff_contDiff.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ.1, hlt⟩] with t ht
    exact hlocal ⟨ht.1, ht.2.le⟩
  · have hθπ : θ = Real.pi := le_antisymm hθ.2 (le_of_not_gt hlt)
    rw [hθπ]
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have hn : {t : ℝ | Real.cos t < 0} ∈ 𝓝 Real.pi :=
      (isOpen_lt Real.continuous_cos continuous_const).mem_nhds (by simp)
    filter_upwards [hn] with t ht
    exact hzero t ht

theorem sourceConeCircle_rotated_contDiff (axis : ℝ) :
    ContDiff ℝ ∞ (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) := by
  have he : (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) =
      fun θ => sourceConeCircle 0 (sourceUnitDirection (θ-axis)) := by
    funext θ
    simp only [sourceConeCircle, sourceCircleRotate_comp, neg_zero,
      sub_eq_add_neg, add_zero]
  rw [he]
  exact sourceConeCircle_angular_contDiff.comp (contDiff_id.sub contDiff_const)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphEndpointContinuity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem continuous_circle_of_direction {E : Type*} [TopologicalSpace E]
    (f : UnitCircle → E) (hf : Continuous (fun θ => f (sourceUnitDirection θ))) :
    Continuous f := by
  let A := Icc (-Real.pi) Real.pi
  let : CompactSpace A := isCompact_iff_compactSpace.mp (show IsCompact A from isCompact_Icc)
  let q : A → UnitCircle := fun θ => sourceUnitDirection θ
  have hq : Continuous q := continuous_sourceUnitDirection.comp continuous_subtype_val
  have hs : Function.Surjective q := by
    intro ω
    exact ⟨⟨sourceAngle ω, (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩,
      sourceUnitDirection_sourceAngle ω⟩
  exact (hq.isClosedMap.isQuotientMap hq hs).continuous_iff.mpr
    (hf.comp continuous_subtype_val)

theorem sourceConeCircle_continuous (axis : ℝ) : Continuous (sourceConeCircle axis) :=
  continuous_circle_of_direction _ (sourceConeCircle_rotated_contDiff axis).continuous

theorem circleGraphSignPlus_continuous : Continuous circleGraphSignPlus := by
  exact graphSignPlus_contDiff.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem circleGraphSignMinus_continuous : Continuous circleGraphSignMinus := by
  exact graphSignMinus_contDiff.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem sourcePlaneWave_continuous (x : Plane) :
    Continuous (fun p : ℝ × UnitCircle => sourcePlaneWave p.1 p.2 x) := by
  unfold sourcePlaneWave
  fun_prop

theorem graphBinWeight_continuous (n j k : ℕ) : Continuous (graphBinWeight n j k) :=
  ((circleAngularBin_continuous n j).comp continuous_fst).mul
    ((circleAngularBin_continuous n k).comp continuous_snd)

theorem graphDistanceWeight_continuous (axis : ℝ) (n j k : ℕ) :
    Continuous (graphDistanceWeight axis n j k) := by
  exact ((Complex.continuous_ofReal.comp (graphBinWeight_continuous n j k)).mul
    ((sourceConeCircle_continuous axis).comp continuous_fst)).mul
      (Complex.continuous_conj.comp ((sourceConeCircle_continuous axis).comp continuous_snd))

theorem graphProductWeight_continuous (plus : Bool) (n j k : ℕ) :
    Continuous (graphProductWeight plus n j k) := by
  cases plus <;> exact Complex.continuous_ofReal.comp
    ((graphBinWeight_continuous n j k).mul (by first
      | exact circleGraphSignMinus_continuous
      | exact circleGraphSignPlus_continuous))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphTorusAngles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem continuous_interval_integral_swap {f : ℝ → ℝ → ℂ}
    (hf : Continuous (Function.uncurry f)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, f x y) =
      ∫ y in c..d, ∫ x in a..b, f x y := by
  have hi : IntegrableOn (Function.uncurry f) ((Icc a b) ×ˢ (Icc c d)) volume :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi' : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
    using integral_integral_swap hi'

theorem periodic_half_difference_integral {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    (∫ u in (-Real.pi)..Real.pi, f u) =
      (2 : ℝ) • ∫ α in (-Real.pi/2)..(Real.pi/2), f (θ-2*α) := by
  rw [intervalIntegral.smul_integral_comp_sub_mul]
  have h := hp.intervalIntegral_add_eq (-Real.pi) (θ-Real.pi)
  convert h using 1 <;> congr 1 <;> ring

theorem periodic_mean_angle_integral {F : ℝ → ℝ → ℂ}
    (hp : ∀ u v, F (u+2*Real.pi) (v+2*Real.pi) = F u v) (α : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, F θ (θ-2*α)) =
      ∫ φ in (-Real.pi)..Real.pi, F (φ+α) (φ-α) := by
  let g : ℝ → ℂ := fun θ => F θ (θ-2*α)
  have hg : Function.Periodic g (2*Real.pi) := by
    intro θ
    dsimp [g]
    rw [show θ+2*Real.pi-2*α = (θ-2*α)+2*Real.pi by ring]
    exact hp θ (θ-2*α)
  have he : (fun φ => F (φ+α) (φ-α)) = fun φ => g (φ+α) := by
    funext φ
    dsimp [g]
    congr 1
    ring
  rw [he, intervalIntegral.integral_comp_add_right]
  have h := hg.intervalIntegral_add_eq (-Real.pi) (-Real.pi+α)
  convert h using 1 <;> congr 1 <;> ring

theorem graph_torus_mean_half_difference {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F))
    (h₁ : ∀ v, Function.Periodic (fun u => F u v) (2*Real.pi))
    (h₂ : ∀ u, Function.Periodic (F u) (2*Real.pi)) :
    (∫ θ₁ in (-Real.pi)..Real.pi, ∫ θ₂ in (-Real.pi)..Real.pi, F θ₁ θ₂) =
      (2 : ℝ) • ∫ α in (-Real.pi/2)..(Real.pi/2),
        ∫ φ in (-Real.pi)..Real.pi, F (φ+α) (φ-α) := by
  have he : (fun θ₁ => ∫ θ₂ in (-Real.pi)..Real.pi, F θ₁ θ₂) =
      fun θ₁ => (2 : ℝ) • ∫ α in (-Real.pi/2)..(Real.pi/2), F θ₁ (θ₁-2*α) := by
    funext θ₁
    exact periodic_half_difference_integral (h₂ θ₁) θ₁
  rw [he]
  rw [intervalIntegral.integral_smul]
  have hc : Continuous (fun p : ℝ × ℝ => F p.1 (p.1-2*p.2)) :=
    hF.comp (continuous_fst.prodMk (continuous_fst.sub (continuous_const.mul continuous_snd)))
  rw [continuous_interval_integral_swap (f := fun θ α => F θ (θ-2*α)) hc (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])]
  congr 1
  apply intervalIntegral.integral_congr
  intro α hα
  exact periodic_mean_angle_integral (fun u v => (h₁ (v+2*Real.pi) u).trans (h₂ u v)) α

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCartesianSubstitution
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem graphCartesianFrequency_polar (p : GraphLiftSpace) :
    graphCartesianFrequency (graphPolarMap p) = p 0 • sourceDirection (p 1) := by
  ext i
  fin_cases i <;> simp [graphCartesianFrequency, graphPolarMap, sourceDirection,
    Complex.orthonormalBasisOneI_repr_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem graphLiftMap_endpoint_frequencies (p : GraphLiftSpace) :
    (graphLiftMap p) 0 • sourceDirection ((graphLiftMap p) 1) =
      graphB (p 2) (graphCartesianFrequency (graphPolarMap p)) ∧
    (graphLiftMap p) 0 • sourceDirection ((graphLiftMap p) 2) =
      graphA (p 2) (graphCartesianFrequency (graphPolarMap p)) := by
  have hs : Real.sqrt (1+(p 2)^2) ≠ 0 := by positivity
  have hscale : p 0*Real.sqrt (1+(p 2)^2)/2*(Real.sqrt (1+(p 2)^2))⁻¹ = (1/2:ℝ)*p 0 := by
    field_simp
  rw [graphCartesianFrequency_polar]
  constructor
  · change (p 0*Real.sqrt (1+(p 2)^2)/2) • sourceDirection (p 1+Real.arctan (p 2)) = _
    rw [sourceDirection_add_arctan, smul_smul]
    rw [hscale,graphB,quarterTurn_smul,smul_comm (p 2),← smul_add,smul_smul]
  · change (p 0*Real.sqrt (1+(p 2)^2)/2) • sourceDirection (p 1-Real.arctan (p 2)) = _
    rw [sourceDirection_sub_arctan, smul_smul]
    rw [hscale,graphA,quarterTurn_smul,smul_comm (p 2),← smul_sub,smul_smul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphPolarAnnulus
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphPolarRectangle_subset {a b : ℝ} (ha : 0 < a) :
    graphPolarRectangle a b ⊆ polarCoord.target := by
  intro p hp
  exact ⟨ha.trans hp.1.1, hp.2⟩

theorem graph_polar_rectangle_integral (f : ℝ × ℝ → ℂ)
    (hf : Continuous f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in polarCoord.symm '' graphPolarRectangle a b,
      (polarCoord x).1⁻¹ • f (polarCoord x)) =
      ∫ φ in (-Real.pi)..Real.pi, ∫ ρ in a..b, f (ρ,φ) := by
  have hS : MeasurableSet (graphPolarRectangle a b) := measurableSet_Ioo.prod measurableSet_Ioo
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun p (_ : p ∈ graphPolarRectangle a b) => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    (polarCoord.symm.injOn.mono (graphPolarRectangle_subset ha))
    (fun x => (polarCoord x).1⁻¹ • f (polarCoord x))
  have hcancel : (∫ p in graphPolarRectangle a b,
      |(fderivPolarCoordSymm p).det| • ((polarCoord (polarCoord.symm p)).1⁻¹ •
        f (polarCoord (polarCoord.symm p)))) = ∫ p in graphPolarRectangle a b, f p := by
    apply setIntegral_congr_fun hS
    intro p hp
    have hr := (graphPolarRectangle_subset ha hp).1
    dsimp only
    rw [polarCoord.right_inv (graphPolarRectangle_subset ha hp), det_fderivPolarCoordSymm,
      abs_of_pos hr, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [he, hcancel]
  have hi : Integrable f ((volume.restrict (Ioo a b)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hi' := integral_prod_symm f hi
  rw [Measure.prod_restrict] at hi'
  simpa only [graphPolarRectangle, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo, ← Measure.volume_eq_prod] using hi'

theorem graphPlaneEquiv_volume_preserving : MeasurePreserving graphPlaneEquiv :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp
    ((volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow)

theorem graphPlaneEquiv_norm (x : ℝ × ℝ) :
    ‖graphPlaneEquiv x‖ = (polarCoord x).1 := by
  change ‖(WithLp.toLp 2 ![x.1,x.2] : Plane)‖ = Real.sqrt (x.1^2+x.2^2)
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem graph_plane_rectangle_integral (f : ℝ × ℝ → ℂ)
    (hf : Continuous f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ η in graphPlaneEquiv '' (polarCoord.symm '' graphPolarRectangle a b),
      ‖η‖⁻¹ • f (polarCoord (graphPlaneEquiv.symm η))) =
      ∫ φ in (-Real.pi)..Real.pi, ∫ ρ in a..b, f (ρ,φ) := by
  rw [graphPlaneEquiv_volume_preserving.setIntegral_image_emb graphPlaneEquiv.measurableEmbedding]
  simp only [MeasurableEquiv.symm_apply_apply, graphPlaneEquiv_norm]
  exact graph_polar_rectangle_integral f hf ha hab

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphTorusArcLength
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceArcLength_pair_integral_period {F : UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (Function.uncurry F)) :
    (∫ u, ∫ v, F u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ θ₁ in (-Real.pi)..Real.pi, ∫ θ₂ in (-Real.pi)..Real.pi,
        F (sourceUnitDirection θ₁) (sourceUnitDirection θ₂) := by
  rw [sourceArcLength_integral_period hF.stronglyMeasurable.integral_prod_right.aestronglyMeasurable]
  apply intervalIntegral.integral_congr
  intro θ _
  exact sourceArcLength_integral_period
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem arctan_interval_integral (g : ℝ → ℂ) :
    (∫ α in (-Real.pi/2)..(Real.pi/2), g α) =
      ∫ z : ℝ, (1+z^2)⁻¹ • g (Real.arctan z) := by
  have he := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun z (_ : z ∈ (univ : Set ℝ)) => (Real.hasDerivAt_arctan' z).hasDerivWithinAt)
    Real.arctan_injective.injOn g
  have habs (z : ℝ) : |(1+z^2)⁻¹| = (1+z^2)⁻¹ := abs_of_nonneg (by positivity)
  simp only [image_univ, Real.range_arctan, Measure.restrict_univ, habs] at he
  rw [intervalIntegral.integral_of_le
    (by simpa only [neg_div] using neg_le_self (half_pos Real.pi_pos).le),
    integral_Ioc_eq_integral_Ioo]
  simpa only [neg_div] using he

theorem sourceArcLength_pair_graph_angles {F : UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (Function.uncurry F))
    (hc : Continuous (fun p : ℝ × ℝ =>
      F (sourceUnitDirection p.1) (sourceUnitDirection p.2))) :
    (∫ u, ∫ v, F u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, (2/(1+z^2)) • ∫ φ in (-Real.pi)..Real.pi,
        F (sourceUnitDirection (φ+Real.arctan z))
          (sourceUnitDirection (φ-Real.arctan z)) := by
  rw [sourceArcLength_pair_integral_period hF,
    graph_torus_mean_half_difference (F := fun u v => F (sourceUnitDirection u)
      (sourceUnitDirection v)) hc
      (fun v u => congrArg (fun w => F w (sourceUnitDirection v)) (sourceUnitDirection_periodic u))
      (fun u v => congrArg (F (sourceUnitDirection u)) (sourceUnitDirection_periodic v)),
    arctan_interval_integral, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  rw [smul_smul, div_eq_mul_inv]

theorem sourceArcLength_pair_rotate_right (axis : ℝ)
    {F : UnitCircle → UnitCircle → ℂ} (hF : Measurable (Function.uncurry F)) :
    (∫ u, ∫ v, F u (sourceCircleRotate axis v) ∂sourceArcLength ∂sourceArcLength) =
      ∫ u, ∫ v, F u v ∂sourceArcLength ∂sourceArcLength := by
  apply integral_congr_ae
  filter_upwards with u
  exact sourceCircleRotate_integral axis (hF.comp (measurable_const.prodMk measurable_id))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_GraphRadialNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_radial_interval_normalization (f : ℝ → ℂ) {R : ℝ}
    (hR : 0 < R) (a b : ℝ) :
    R⁻¹ • (∫ r in (R*a)..(R*b), f r) = ∫ t in a..b, f (R*t) := by
  rw [intervalIntegral.integral_comp_mul_left f hR.ne']

theorem graph_radial_angular_density_interval (f : ℝ → ℂ) (z a b : ℝ) :
    (2/(1+z^2)) • (∫ t in a..b, f t) =
      (Real.sqrt (1+z^2))⁻¹ •
        ∫ ρ in (2*a/Real.sqrt (1+z^2))..(2*b/Real.sqrt (1+z^2)),
          f (ρ*Real.sqrt (1+z^2)/2) := by
  have hs : 0 < Real.sqrt (1+z^2) := Real.sqrt_pos.2 (by positivity)
  have he : (fun ρ => f (ρ*Real.sqrt (1+z^2)/2)) =
      fun ρ => f (ρ*(Real.sqrt (1+z^2)/2)) := by
    funext ρ
    congr 1
    ring
  have ha : (2*a/Real.sqrt (1+z^2))*(Real.sqrt (1+z^2)/2) = a := by field_simp
  have hb : (2*b/Real.sqrt (1+z^2))*(Real.sqrt (1+z^2)/2) = b := by field_simp
  rw [he, intervalIntegral.integral_comp_mul_right f (half_pos hs).ne', ha, hb, smul_smul]
  congr 1
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1+z^2)
  field_simp
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_GraphTorusRadial
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem continuous_radial_interval_integral
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {f : X → ℝ → ℂ} (hf : Continuous (Function.uncurry f)) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun x => ∫ t in a..b, f x t) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume) (s := Icc a b) hf isCompact_Icc
  simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using h

theorem circle_pair_radial_interval_swap {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ u, ∫ v, (∫ t in a..b, F t u v) ∂sourceArcLength ∂sourceArcLength := by
  let μ := sourceArcLength.prod sourceArcLength
  have hi : Integrable (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2)
      ((volume.restrict (Ioc a b)).prod μ) := by
    have hc : IntegrableOn (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2)
        ((Icc a b) ×ˢ univ) (volume.prod μ) :=
      hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_univ)
    rw [show (volume.restrict (Ioc a b)).prod μ =
      (volume.prod μ).restrict ((Ioc a b) ×ˢ univ) by
        simpa only [Measure.restrict_univ] using Measure.prod_restrict (μ := volume) (ν := μ) (Ioc a b) univ]
    exact hc.mono_set (Set.prod_mono Ioc_subset_Icc_self (Subset.refl _))
  have hs (t : ℝ) : Integrable (fun p : UnitCircle × UnitCircle => F t p.1 p.2) μ := by
    have hc : Continuous (fun p : UnitCircle × UnitCircle => F t p.1 p.2) :=
      hF.comp (continuous_const.prodMk continuous_id)
    simpa only [integrableOn_univ] using
      (hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ)
  simp only [intervalIntegral.integral_of_le hab]
  calc
    _ = ∫ t in Ioc a b, ∫ p, F t p.1 p.2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      exact (integral_prod _ (hs t)).symm
    _ = ∫ p, (∫ t in Ioc a b, F t p.1 p.2) ∂μ := integral_integral_swap hi
    _ = _ := integral_prod _ hi.integral_prod_right

theorem sourceArcLength_pair_graph_radial_interval
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, (Real.sqrt (1+z^2))⁻¹ • ∫ φ in (-Real.pi)..Real.pi,
        ∫ ρ in (2*a/Real.sqrt (1+z^2))..(2*b/Real.sqrt (1+z^2)),
          F (ρ*Real.sqrt (1+z^2)/2)
            (sourceUnitDirection (φ+Real.arctan z))
            (sourceUnitDirection (φ-Real.arctan z)) := by
  let G : UnitCircle → UnitCircle → ℂ := fun u v => ∫ t in a..b, F t u v
  have hc : Continuous (Function.uncurry G) :=
    continuous_radial_interval_integral (f := fun (p : UnitCircle × UnitCircle) t => F t p.1 p.2)
      (hF.comp continuous_swap) hab
  rw [circle_pair_radial_interval_swap hF hab]
  change (∫ u, ∫ v, G u v ∂sourceArcLength ∂sourceArcLength) = _
  rw [sourceArcLength_pair_graph_angles hc.measurable
    (hc.comp (continuous_sourceUnitDirection.prodMap continuous_sourceUnitDirection))]
  apply integral_congr_ae
  filter_upwards with z
  rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro φ hφ
  exact graph_radial_angular_density_interval
    (fun t => F t (sourceUnitDirection (φ+Real.arctan z))
      (sourceUnitDirection (φ-Real.arctan z))) z a b

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalChart
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphPlaneEquiv_symm_radius (η : Plane) :
    (polarCoord (graphPlaneEquiv.symm η)).1 = ‖η‖ := by
  rw [← graphPlaneEquiv_norm, MeasurableEquiv.apply_symm_apply]

theorem sourceArcLength_pair_graph_plane_interval
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice a b z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          F (‖η‖*Real.sqrt (1+z^2)/2)
            (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
            (sourceUnitDirection (graphPlaneAngle η-Real.arctan z)) := by
  rw [sourceArcLength_pair_graph_radial_interval hF hab]
  apply integral_congr_ae
  filter_upwards with z
  have hs : 0 < Real.sqrt (1+z^2) := by positivity
  let f : ℝ × ℝ → ℂ := fun p => F (p.1*Real.sqrt (1+z^2)/2)
    (sourceUnitDirection (p.2+Real.arctan z))
    (sourceUnitDirection (p.2-Real.arctan z))
  have hf : Continuous f := hF.comp
    (((continuous_fst.mul continuous_const).div_const 2).prodMk
      ((continuous_sourceUnitDirection.comp (continuous_snd.add continuous_const)).prodMk
        (continuous_sourceUnitDirection.comp (continuous_snd.sub continuous_const))))
  have he := graph_plane_rectangle_integral f hf
    (by positivity : 0 < 2*a/Real.sqrt (1+z^2))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab (by norm_num)) hs.le)
  rw [← he, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with η
  dsimp only [f, graphPlaneAngle]
  rw [graphPlaneEquiv_symm_radius, smul_smul, mul_inv_rev]

theorem sourceArcLength_pair_graph_plane_rotated
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (axis : ℝ) :
    (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice a b z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          F (‖η‖*Real.sqrt (1+z^2)/2)
            (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
            (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis)) := by
  let G : ℝ → UnitCircle → UnitCircle → ℂ := fun t u v => F t u (sourceCircleRotate axis v)
  have hg : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => G p.1 p.2.1 p.2.2) :=
    hF.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((sourceCircleRotate_isometry axis).continuous.comp (continuous_snd.comp continuous_snd))))
  have he : (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ t in a..b, ∫ u, ∫ v, G t u v ∂sourceArcLength ∂sourceArcLength := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact (sourceArcLength_pair_rotate_right (F := F t) axis
      (hF.comp (continuous_const.prodMk continuous_id)).measurable).symm
  rw [he, sourceArcLength_pair_graph_plane_interval hg ha hab]
  simp only [G, sourceCircleRotate_comp]

theorem sourceArcLength_pair_graph_plane_normalized
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hR : 0 < R) (axis : ℝ) :
    R⁻¹ • (∫ r in (R*a)..(R*b), ∫ u, ∫ v, F r u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice a b z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          F (R*(‖η‖*Real.sqrt (1+z^2)/2))
            (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
            (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis)) := by
  rw [graph_radial_interval_normalization _ hR]
  exact sourceArcLength_pair_graph_plane_rotated
    (F := fun t u v => F (R*t) u v)
    (hF.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)) ha hab axis

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalBump
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceArcLength_pair_graph_plane_supported
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hR : 0 < R)
    (hsupp : ∀ r u v, F r u v ≠ 0 → r/R ∈ Icc a b) (axis : ℝ) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, F r u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice a b z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          F (R*(‖η‖*Real.sqrt (1+z^2)/2))
            (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
            (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis)) := by
  have hz : ∀ r, r ∉ Icc (R*a) (R*b) →
      (∫ u, ∫ v, F r u v ∂sourceArcLength ∂sourceArcLength) = 0 := by
    intro r hr
    have he : ∀ u v, F r u v = 0 := by
      intro u v
      by_contra hn
      have hh := hsupp r u v hn
      apply hr
      exact ⟨by nlinarith [(le_div_iff₀ hR).mp hh.1],
        by nlinarith [(div_le_iff₀ hR).mp hh.2]⟩
    simp only [he, integral_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hR.le)]
  exact sourceArcLength_pair_graph_plane_normalized hF ha hab hR axis

theorem sourceArcLength_pair_graph_plane_bump
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {R : ℝ} (hR : 0 < R) (axis : ℝ) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • F r u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice (1/4) 4 z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          (Ψ (‖η‖*Real.sqrt (1+z^2)/2) •
            F (R*(‖η‖*Real.sqrt (1+z^2)/2))
              (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
              (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis))) := by
  have hc : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) =>
      Ψ (p.1/R) • F p.1 p.2.1 p.2.2) :=
    (hΨ.comp (continuous_fst.div_const R)).smul hF
  have hb : ∀ r u v, Ψ (r/R) • F r u v ≠ 0 → r/R ∈ Icc (1/4:ℝ) 4 := by
    intro r u v h
    have hn : Ψ (r/R) ≠ 0 := by intro he; exact h (by rw [he, zero_smul])
    exact Ioo_subset_Icc_self (hsupp (r/R) hn)
  have he := sourceArcLength_pair_graph_plane_supported hc
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) ≤ 4) hR hb axis
  simpa only [mul_div_cancel_left₀ _ hR.ne'] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalDomain
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphGlobalSlice_eq {a b : ℝ} (ha : 0 < a) (z : ℝ) :
    graphGlobalSlice a b z = graphPlaneSlit ∩ graphGlobalAnnulus a b z := by
  ext η
  have hs : 0 < Real.sqrt (1+z^2) := by positivity
  constructor
  · rintro ⟨x,⟨p,hp,rfl⟩,rfl⟩
    have hdom := graphPolarRectangle_subset
      (by positivity : 0 < 2*a/Real.sqrt (1+z^2)) hp
    constructor
    · change graphPlaneEquiv.symm (graphPlaneEquiv (polarCoord.symm p)) ∈ polarCoord.source
      rw [MeasurableEquiv.symm_apply_apply]
      exact polarCoord.map_target hdom
    · change ‖graphPlaneEquiv (polarCoord.symm p)‖*Real.sqrt (1+z^2)/2 ∈ Ioo a b
      rw [graphPlaneEquiv_norm, polarCoord.right_inv hdom]
      have hlo := (div_lt_iff₀ hs).mp hp.1.1
      have hhi := (lt_div_iff₀ hs).mp hp.1.2
      constructor <;> linarith
  · rintro ⟨hslit,hrad⟩
    change graphPlaneEquiv.symm η ∈ polarCoord.source at hslit
    change a < ‖η‖*Real.sqrt (1+z^2)/2 ∧ ‖η‖*Real.sqrt (1+z^2)/2 < b at hrad
    refine ⟨graphPlaneEquiv.symm η, ?_, MeasurableEquiv.apply_symm_apply _ _⟩
    refine ⟨polarCoord (graphPlaneEquiv.symm η), ?_, polarCoord.left_inv hslit⟩
    refine ⟨?_, (polarCoord.map_source hslit).2⟩
    rw [graphPlaneEquiv_symm_radius]
    exact ⟨(div_lt_iff₀ hs).mpr (by linarith [hrad.1]),
      (lt_div_iff₀ hs).mpr (by linarith [hrad.2])⟩

theorem graphPlaneSlit_ae_eq_univ : graphPlaneSlit =ᵐ[volume] univ := by
  have h := ((graphPlaneEquiv_volume_preserving.symm graphPlaneEquiv).quasiMeasurePreserving).preimage_ae_eq
    polarCoord_source_ae_eq_univ
  simpa only [graphPlaneSlit, preimage_univ] using h

theorem graphGlobalSlice_ae_eq_annulus {a b : ℝ} (ha : 0 < a) (z : ℝ) :
    graphGlobalSlice a b z =ᵐ[volume] graphGlobalAnnulus a b z := by
  rw [graphGlobalSlice_eq ha]
  filter_upwards [graphPlaneSlit_ae_eq_univ] with η hη
  change (η ∈ graphPlaneSlit) = True at hη
  have hm : η ∈ graphPlaneSlit := Eq.mp hη.symm trivial
  change (η ∈ graphPlaneSlit ∧ η ∈ graphGlobalAnnulus a b z) = (η ∈ graphGlobalAnnulus a b z)
  simp only [hm, true_and]

theorem sourceArcLength_pair_graph_annulus_bump
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {R : ℝ} (hR : 0 < R) (axis : ℝ) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • F r u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalAnnulus (1/4) 4 z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          (Ψ (‖η‖*Real.sqrt (1+z^2)/2) •
            F (R*(‖η‖*Real.sqrt (1+z^2)/2))
              (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
              (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis))) := by
  rw [sourceArcLength_pair_graph_plane_bump hF hΨ hsupp hR axis]
  apply integral_congr_ae
  filter_upwards with z
  exact setIntegral_congr_set (graphGlobalSlice_ae_eq_annulus (by norm_num) z)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalPhase
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphPlaneEquiv_polar (p : ℝ × ℝ) :
    graphPlaneEquiv (polarCoord.symm p) = p.1 • sourceDirection p.2 := by
  ext i
  fin_cases i <;> simp [graphPlaneEquiv, sourceDirection, Complex.orthonormalBasisOneI_repr_apply,
    polarCoord, MeasurableEquiv.finTwoArrow, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem graph_plane_axis {η : Plane} (hη : η ∈ graphPlaneSlit) :
    ‖η‖ • sourceDirection (graphPlaneAngle η) = η := by
  have he := graphPlaneEquiv_polar (polarCoord (graphPlaneEquiv.symm η))
  rw [polarCoord.left_inv hη, MeasurableEquiv.apply_symm_apply,
    graphPlaneEquiv_symm_radius] at he
  exact he.symm

theorem graph_global_endpoint_frequencies {η : Plane} (hη : η ∈ graphPlaneSlit) (z : ℝ) :
    (‖η‖*Real.sqrt (1+z^2)/2) • sourceDirection (graphPlaneAngle η+Real.arctan z) = graphB z η ∧
    (‖η‖*Real.sqrt (1+z^2)/2) • sourceDirection (graphPlaneAngle η-Real.arctan z) = graphA z η := by
  have he := graphLiftMap_endpoint_frequencies ![‖η‖,graphPlaneAngle η,z]
  simp only [graphCartesianFrequency_polar, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, graph_plane_axis hη] at he
  exact he

theorem graphB_inner (z : ℝ) (η x : Plane) :
    inner ℝ (graphB z η) x = inner ℝ η (graphA z x) := by
  have hq : inner ℝ (quarterTurn η) x = -inner ℝ η (quarterTurn x) := by
    simp [quarterTurn, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [graphA, graphB, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_sub_right, hq]
  ring

theorem graphA_inner (z : ℝ) (η x : Plane) :
    inner ℝ (graphA z η) x = inner ℝ η (graphB z x) := by
  simpa only [graphA, graphB, neg_smul, sub_neg_eq_add, ← sub_eq_add_neg] using graphB_inner (-z) η x

theorem graph_global_plane_wave_phase {η : Plane} (hη : η ∈ graphPlaneSlit)
    (z R : ℝ) (x y : Plane) :
    sourcePlaneWave (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η+Real.arctan z)) x *
      sourcePlaneWave (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η-Real.arctan z)) y =
      Complex.exp (Complex.I*(R:ℂ)*(inner ℝ η (graphA z x+graphB z y) : ℂ)) := by
  have he := graph_global_endpoint_frequencies hη z
  have hx := congrArg (fun w : Plane => inner ℝ w x) he.1
  have hy := congrArg (fun w : Plane => inner ℝ w y) he.2
  simp only [real_inner_smul_left, graphB_inner, graphA_inner] at hx hy
  simp only [sourcePlaneWave, ← Complex.exp_add, Complex.ofReal_mul]
  change Complex.exp (Complex.I*(↑R*↑(‖η‖*Real.sqrt (1+z^2)/2))*↑(inner ℝ
      (sourceDirection (graphPlaneAngle η+Real.arctan z)) x) +
    Complex.I*(↑R*↑(‖η‖*Real.sqrt (1+z^2)/2))*↑(inner ℝ
      (sourceDirection (graphPlaneAngle η-Real.arctan z)) y)) = _
  have hx' := congrArg (fun r : ℝ => (r:ℂ)) hx
  have hy' := congrArg (fun r : ℝ => (r:ℂ)) hy
  simp only [Complex.ofReal_mul] at hx' hy'
  rw [inner_add_right, Complex.ofReal_add]
  congr 1
  linear_combination Complex.I*(R:ℂ)*hx' + Complex.I*(R:ℂ)*hy'

theorem sourcePlaneWave_add_pi (r θ : ℝ) (x : Plane) :
    sourcePlaneWave r (sourceUnitDirection (θ+Real.pi)) x =
      sourcePlaneWave r (sourceUnitDirection θ) (-x) := by
  change Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (sourceDirection (θ+Real.pi)) x : ℂ)) =
    Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (sourceDirection θ) (-x) : ℂ))
  rw [sourceDirection_add_pi, inner_neg_left, inner_neg_right]

theorem graph_global_plane_wave_phase_minus {η : Plane} (hη : η ∈ graphPlaneSlit)
    (z R : ℝ) (x y : Plane) :
    sourcePlaneWave (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η+Real.arctan z)) x *
      sourcePlaneWave (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+Real.pi)) y =
      Complex.exp (Complex.I*(R:ℂ)*(inner ℝ η (graphA z x-graphB z y) : ℂ)) := by
  rw [sourcePlaneWave_add_pi, graph_global_plane_wave_phase hη]
  have hn : graphB z (-y) = -graphB z y := by
    ext i
    fin_cases i <;> simp [graphB, quarterTurn] <;> ring
  rw [hn, ← sub_eq_add_neg]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphFourPointKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphFourKernel_continuous (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    (hb : ∀ i, Continuous (b i (x i))) (hW : Continuous W) :
    Continuous (fun p : ℝ × (UnitCircle × UnitCircle) =>
      graphFourKernel b W x p.1 p.2.1 p.2.2) := by
  have hu : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hv : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => p.2.2) :=
    continuous_snd.comp continuous_snd
  exact (((sourcePlaneWave_continuous _).comp (continuous_fst.prodMk hu)).mul
    ((sourcePlaneWave_continuous _).comp (continuous_fst.prodMk hv))).mul
      (((hW.comp continuous_snd).mul
        ((hb 0 |>.comp hu).mul (Complex.continuous_conj.comp (hb 1 |>.comp hu)))).mul
        ((hb 2 |>.comp hv).mul (Complex.continuous_conj.comp (hb 3 |>.comp hv))))

theorem graphFourKernel_chart (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    (hb : ∀ i, Continuous (b i (x i))) (hW : Continuous W)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {R : ℝ} (hR : 0 < R) (axis : ℝ) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • graphFourKernel b W x r u v
      ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalAnnulus (1/4) 4 z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          (Ψ (‖η‖*Real.sqrt (1+z^2)/2) •
            graphFourKernel b W x (R*(‖η‖*Real.sqrt (1+z^2)/2))
              (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
              (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis))) :=
  sourceArcLength_pair_graph_annulus_bump (graphFourKernel_continuous b W x hb hW)
    hΨ hsupp hR axis

theorem graphFourKernel_phase_plus (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    {η : Plane} (hη : η ∈ graphPlaneSlit) (z R : ℝ) :
    graphFourKernel b W x (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
        (sourceUnitDirection (graphPlaneAngle η-Real.arctan z)) =
      Complex.exp (Complex.I*(R:ℂ)*
        (inner ℝ η (graphA z (x 0-x 1)+graphB z (x 2-x 3)) : ℂ)) *
        graphFourAmplitude b W x
          (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
          (sourceUnitDirection (graphPlaneAngle η-Real.arctan z)) := by
  rw [graphFourKernel, graph_global_plane_wave_phase hη]

theorem graphFourKernel_phase_minus (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    {η : Plane} (hη : η ∈ graphPlaneSlit) (z R : ℝ) :
    graphFourKernel b W x (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
        (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+Real.pi)) =
      Complex.exp (Complex.I*(R:ℂ)*
        (inner ℝ η (graphA z (x 0-x 1)-graphB z (x 2-x 3)) : ℂ)) *
        graphFourAmplitude b W x
          (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
          (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+Real.pi)) := by
  rw [graphFourKernel, graph_global_plane_wave_phase_minus hη]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphKernelBounds
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphBinWeight_bounds (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    0 ≤ graphBinWeight n j k p ∧ graphBinWeight n j k p ≤ 1 := by
  have hu := circleAngularBin_bounds n j p.1
  have hv := circleAngularBin_bounds n k p.2
  exact ⟨mul_nonneg hu.1 hv.1, by simpa [graphBinWeight] using mul_le_mul hu.2 hv.2 hv.1 zero_le_one⟩

theorem graphDistanceWeight_norm_le (axis : ℝ) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphDistanceWeight axis n j k p‖ ≤ 1 := by
  have hb := graphBinWeight_bounds n j k p
  simp only [graphDistanceWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb.1, Complex.norm_conj]
  exact (mul_le_mul (mul_le_mul hb.2 (sourceConeCircle_norm_le axis p.1)
    (norm_nonneg _) zero_le_one) (sourceConeCircle_norm_le axis p.2)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem graphProductWeight_norm_le (plus : Bool) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphProductWeight plus n j k p‖ ≤ 1 := by
  have hb := graphBinWeight_bounds n j k p
  have hs := graphSignPartition_bounds (p.1,p.2)
  cases plus <;> simp only [graphProductWeight, Bool.false_eq_true, ↓reduceIte,
    Complex.norm_real, Real.norm_eq_abs, circleGraphSignPlus, circleGraphSignMinus]
  · rw [abs_of_nonneg (mul_nonneg hb.1 hs.2.2.1)]
    exact (mul_le_mul hb.2 hs.2.2.2.1 hs.2.2.1 zero_le_one).trans_eq (by ring)
  · rw [abs_of_nonneg (mul_nonneg hb.1 hs.1)]
    exact (mul_le_mul hb.2 hs.2.1 hs.1 zero_le_one).trans_eq (by ring)

theorem graphFourKernel_norm_le (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (B : Fin 4 → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hb : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hW : ∀ p, ‖W p‖ ≤ 1) (x : Fin 4 → Plane) (r : ℝ) (u v : UnitCircle) :
    ‖graphFourKernel b W x r u v‖ ≤ (B 0*B 1)*(B 2*B 3) := by
  simp only [graphFourKernel, graphFourAmplitude, norm_mul, sourcePlaneWave_norm,
    one_mul, Complex.norm_conj]
  exact (mul_le_mul
    (mul_le_mul (hW (u,v))
      (mul_le_mul (hb 0 _ _) (hb 1 _ _) (norm_nonneg _) (hB 0))
      (by positivity) zero_le_one)
    (mul_le_mul (hb 2 _ _) (hb 3 _ _) (norm_nonneg _) (hB 2))
    (by positivity) (mul_nonneg zero_le_one (mul_nonneg (hB 0) (hB 1)))).trans_eq (by ring)

theorem graphFourKernel_measurable (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hW : Measurable W) :
    Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphFourKernel b W p.2 p.1.1 p.1.2.1 p.1.2.2) := by
  unfold graphFourKernel graphFourAmplitude sourcePlaneWave
  have h0 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 0 (p.2 0) p.1.2.1) := (hb 0).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 0, p.1.2.1)) from by fun_prop)
  have h1 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 1 (p.2 1) p.1.2.1) := (hb 1).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 1, p.1.2.1)) from by fun_prop)
  have h2 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 2 (p.2 2) p.1.2.2) := (hb 2).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 2, p.1.2.2)) from by fun_prop)
  have h3 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 3 (p.2 3) p.1.2.2) := (hb 3).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 3, p.1.2.2)) from by fun_prop)
  apply Measurable.mul
  · fun_prop
  · exact (((hW.comp (measurable_snd.comp measurable_fst)).mul
      (h0.mul (Complex.continuous_conj.measurable.comp h1))).mul
      (h2.mul (Complex.continuous_conj.measurable.comp h3)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalSupports
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_directions_sum (φ z : ℝ) :
    sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z) =
      (2/Real.sqrt (1+z^2)) • sourceDirection φ := by
  rw [sourceDirection_add_arctan, sourceDirection_sub_arctan, ← smul_add]
  have he (u v : Plane) : (u+v)+(u-v) = (2:ℝ) • u := by
    simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm]
  rw [he, smul_smul]
  congr 1
  ring

theorem graph_directions_sum_norm (φ z : ℝ) :
    ‖sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z)‖ =
      2/Real.sqrt (1+z^2) := by
  rw [graph_directions_sum, norm_smul, Real.norm_eq_abs, norm_sourceDirection,
    mul_one, abs_of_nonneg (by positivity)]

theorem graph_parameter_bound (φ z : ℝ)
    (hc : 1/2 ≤ ‖sourceDirection (φ+Real.arctan z) + sourceDirection (φ-Real.arctan z)‖) :
    Real.sqrt (1+z^2) ≤ 4 ∧ |z| ≤ 4 := by
  rw [graph_directions_sum_norm] at hc
  have hs : 0 < Real.sqrt (1+z^2) := by positivity
  have hh := (le_div_iff₀ hs).mp hc
  have hb : Real.sqrt (1+z^2) ≤ 4 := by linarith
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1+z^2)
  exact ⟨hb, by nlinarith [sq_abs z, abs_nonneg z]⟩

theorem graph_plus_support_parameter (φ z : ℝ)
    (hc : (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ∈
      tsupport circleGraphSignPlus) :
    |z| ≤ 4 := by
  have hh := circleGraphSignPlus_tsupport hc
  change 1 ≤ ‖(sourceUnitDirection (φ+Real.arctan z) : Plane) +
    (sourceUnitDirection (φ-Real.arctan z) : Plane)‖ at hh
  apply (graph_parameter_bound φ z _).2
  change 1/2 ≤ ‖(sourceUnitDirection (φ+Real.arctan z) : Plane) +
    (sourceUnitDirection (φ-Real.arctan z) : Plane)‖
  linarith

theorem graph_minus_support_parameter (φ z : ℝ)
    (hc : (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z+Real.pi)) ∈
      tsupport circleGraphSignMinus) : |z| ≤ 4 := by
  have hh := circleGraphSignMinus_tsupport hc
  change 1 ≤ ‖sourceDirection (φ+Real.arctan z) -
    sourceDirection (φ-Real.arctan z+Real.pi)‖ at hh
  rw [sourceDirection_add_pi, sub_neg_eq_add] at hh
  exact (graph_parameter_bound φ z (by linarith)).2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphTransportIntegrability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphTransportBox_compact : IsCompact graphTransportBox :=
  isCompact_Icc.prod (isCompact_closedBall 0 8)

theorem graphPlaneAngle_measurable : Measurable graphPlaneAngle := by
  change Measurable (fun η => Complex.arg (Complex.equivRealProd.symm (graphPlaneEquiv.symm η)))
  exact Complex.measurable_arg.comp
    (Complex.measurableEquivRealProd.symm.measurable.comp graphPlaneEquiv.symm.measurable)

theorem graphTransport_measurable {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (R axis : ℝ) :
    Measurable (graphTransport F Ψ R axis) := by
  have ha : Measurable (fun p : ℝ × Plane => graphPlaneAngle p.2) :=
    graphPlaneAngle_measurable.comp measurable_snd
  have hu : Measurable (fun p : ℝ × Plane =>
      sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1)) := by fun_prop
  have hv : Measurable (fun p : ℝ × Plane =>
      sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+axis)) := by fun_prop
  unfold graphTransport
  simp only [Complex.real_smul]
  apply Measurable.mul
  · fun_prop
  · apply Measurable.mul
    · apply Complex.measurable_ofReal.comp
      exact hΨ.comp (show Measurable (fun p : ℝ × Plane =>
        ‖p.2‖*Real.sqrt (1+p.1^2)/2) from by fun_prop)
    · exact hF.comp (show Measurable (fun p : ℝ × Plane =>
        (R*(‖p.2‖*Real.sqrt (1+p.1^2)/2),
          (sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1),
           sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+axis)))) from
        (by fun_prop))

theorem graphTransport_support {F : ℝ → UnitCircle → UnitCircle → ℂ}
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (R axis : ℝ)
    (hchart : ∀ r φ z, F r (sourceUnitDirection (φ+Real.arctan z))
      (sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    Function.support (graphTransport F Ψ R axis) ⊆ graphTransportBox := by
  intro p hp
  have hb : Ψ (‖p.2‖*Real.sqrt (1+p.1^2)/2) ≠ 0 := by
    intro hz; exact hp (by simp [graphTransport, hz])
  have hf : F (R*(‖p.2‖*Real.sqrt (1+p.1^2)/2))
      (sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1))
      (sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+axis)) ≠ 0 := by
    intro hz; exact hp (by simp [graphTransport, hz])
  have hr := hsupp _ hb
  have hz := hchart _ _ _ hf
  have hs : 1 ≤ Real.sqrt (1+p.1^2) :=
    Real.one_le_sqrt.mpr (le_add_of_nonneg_right (sq_nonneg p.1))
  refine ⟨abs_le.mp hz, ?_⟩
  change dist p.2 0 ≤ 8
  rw [dist_zero_right]
  nlinarith [hr.2, mul_le_mul_of_nonneg_left hs (norm_nonneg p.2)]

theorem graphTransport_norm_le {F : ℝ → UnitCircle → UnitCircle → ℂ}
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hF : ∀ r u v, ‖F r u v‖ ≤ C) (hΨ : ∀ t, |Ψ t| ≤ B)
    (R axis : ℝ) (p : ℝ × Plane) : ‖graphTransport F Ψ R axis p‖ ≤ 2*(B*C) := by
  by_cases hz : Ψ (‖p.2‖*Real.sqrt (1+p.1^2)/2) = 0
  · simp [graphTransport, hz, mul_nonneg hB hC]
  have hr := (hsupp _ hz).1
  have hd : (0:ℝ) < ‖p.2‖*Real.sqrt (1+p.1^2) := by linarith
  have hi : (‖p.2‖*Real.sqrt (1+p.1^2))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    linarith
  simp only [graphTransport, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hd]
  exact mul_le_mul hi (mul_le_mul (hΨ _) (hF _ _ _) (norm_nonneg _) hB)
    (by positivity) (by norm_num)

theorem graphTransport_integrable {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hbound : ∀ r u v, ‖F r u v‖ ≤ C) (hbump : ∀ t, |Ψ t| ≤ B)
    (R axis : ℝ)
    (hchart : ∀ r φ z, F r (sourceUnitDirection (φ+Real.arctan z))
      (sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    Integrable (graphTransport F Ψ R axis) := by
  apply (integrableOn_iff_integrable_of_support_subset
    (graphTransport_support hsupp R axis hchart)).mp
  exact IntegrableOn.of_bound graphTransportBox_compact.measure_lt_top
    (graphTransport_measurable hF hΨ R axis).aestronglyMeasurable
    (2*(B*C)) (Filter.Eventually.of_forall (graphTransport_norm_le hsupp hC hB hbound hbump R axis))

theorem graphTransport_annulus_integral (F : ℝ → UnitCircle → UnitCircle → ℂ)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (R axis z : ℝ) :
    (∫ η in graphGlobalAnnulus (1/4) 4 z, graphTransport F Ψ R axis (z,η)) =
      ∫ η, graphTransport F Ψ R axis (z,η) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro η hη
  have hz : Ψ (‖η‖*Real.sqrt (1+z^2)/2) = 0 := by
    by_contra hn
    exact hη (hsupp _ hn)
  simp [graphTransport, hz]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualTransport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphFourKernel_weight_ne_zero (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane) (r : ℝ) (u v : UnitCircle)
    (h : graphFourKernel b W x r u v ≠ 0) : W (u,v) ≠ 0 := by
  intro hz
  exact h (by simp [graphFourKernel, graphFourAmplitude, hz])

theorem graphProductWeight_parameter (plus : Bool) (n j k : ℕ) (φ z : ℝ)
    (h : graphProductWeight plus n j k
      (sourceUnitDirection (φ+Real.arctan z),
        sourceUnitDirection (φ-Real.arctan z+(if plus then 0 else Real.pi))) ≠ 0) :
    |z| ≤ 4 := by
  cases plus
  · apply graph_minus_support_parameter φ z
    apply subset_closure
    intro hz
    exact h (by simp [graphProductWeight, hz])
  · apply graph_plus_support_parameter φ z
    apply subset_closure
    intro hz
    exact h (by simp [graphProductWeight, hz])

theorem graphFourKernel_transport_integrable
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i x, Continuous (b i x)) (hW : Continuous W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (R axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4)
    (x : Fin 4 → Plane) :
    Integrable (graphTransport (graphFourKernel b W x) Ψ R axis) := by
  apply graphTransport_integrable (graphFourKernel_continuous b W x
    (fun i => hb i (x i)) hW).measurable hΨ.measurable hsupp
    (mul_nonneg (mul_nonneg (hB 0) (hB 1)) (mul_nonneg (hB 2) (hB 3))) hC
    (graphFourKernel_norm_le b W B hB hbound hw x) hc R axis
  intro r φ z hn
  exact hchart φ z (graphFourKernel_weight_ne_zero b W x r _ _ hn)

theorem graphFourKernel_chart_product
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i x, Continuous (b i x)) (hW : Continuous W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) (axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4)
    (x : Fin 4 → Plane) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • graphFourKernel b W x r u v
      ∂sourceArcLength ∂sourceArcLength) =
      ∫ p : ℝ × Plane, graphTransport (graphFourKernel b W x) Ψ R axis p := by
  have hi := graphFourKernel_transport_integrable b W hb hW B hB hbound hw hΨ
    hsupp hC hc R axis hchart x
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  calc
    _ = ∫ z : ℝ, ∫ η in graphGlobalAnnulus (1/4) 4 z,
        graphTransport (graphFourKernel b W x) Ψ R axis (z,η) :=
      graphFourKernel_chart b W x (fun i => hb i (x i)) hW hΨ hsupp hR axis
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun parameter =>
      graphTransport_annulus_integral _ hsupp R axis parameter)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphRotatedWeights
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphRotatedDistanceWeight_continuous (axis : ℝ) (n j k : ℕ) :
    Continuous (graphRotatedDistanceWeight axis n j k) :=
  (graphDistanceWeight_continuous 0 n j k).comp
    (((sourceCircleRotate_isometry (-axis)).continuous.comp continuous_fst).prodMk
      ((sourceCircleRotate_isometry (-axis)).continuous.comp continuous_snd))

theorem graphRotatedDistanceWeight_norm_le (axis : ℝ) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphRotatedDistanceWeight axis n j k p‖ ≤ 1 := graphDistanceWeight_norm_le 0 n j k _

theorem graphRotatedDistanceWeight_parameter (axis : ℝ) (n j k : ℕ) (φ z : ℝ)
    (h : graphRotatedDistanceWeight axis n j k
      (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ≠ 0) :
    |z| ≤ 4 := by
  rw [graphRotatedDistanceWeight_eq] at h
  have hu : sourceConeCircle axis (sourceUnitDirection (φ+Real.arctan z)) ≠ 0 := by
    intro hz; exact h (by simp [hz])
  have hv : sourceConeCircle axis (sourceUnitDirection (φ-Real.arctan z)) ≠ 0 := by
    intro hz; exact h (by simp [hz])
  have hb := sourceConeCircle_plus_nondegenerate axis _ _ (subset_closure hu) (subset_closure hv)
  exact (graph_parameter_bound φ z ((by norm_num : (1/2:ℝ) ≤ 6/5).trans hb)).2

theorem graphSourceWeight_continuous (distance plus : Bool) (axis : ℝ) (n j k : ℕ) :
    Continuous (graphSourceWeight distance plus axis n j k) := by
  cases distance
  · exact graphProductWeight_continuous plus n j k
  · exact graphRotatedDistanceWeight_continuous axis n j k

theorem graphSourceWeight_norm_le (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    (p : UnitCircle × UnitCircle) : ‖graphSourceWeight distance plus axis n j k p‖ ≤ 1 := by
  cases distance
  · exact graphProductWeight_norm_le plus n j k p
  · exact graphRotatedDistanceWeight_norm_le axis n j k p

theorem graphSourceWeight_parameter (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    (φ z : ℝ)
    (h : graphSourceWeight distance plus axis n j k
      (sourceUnitDirection (φ+Real.arctan z),
        sourceUnitDirection (φ-Real.arctan z+graphSourceChartAxis distance plus)) ≠ 0) :
    |z| ≤ 4 := by
  cases distance
  · exact graphProductWeight_parameter plus n j k φ z h
  · apply graphRotatedDistanceWeight_parameter axis n j k φ z
    simpa only [graphSourceWeight, graphSourceChartAxis, ↓reduceIte, add_zero] using h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFourTransformExpansion
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphFourKernel_endpoint_product
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) (x : Fin 4 → Plane) :
    graphFourKernel b W x r u v = W (u,v) *
      ∏ i : Fin 4, (![fun y => sourcePlaneWave r u y * b 0 y u,
        fun y => conj (sourcePlaneWave r u y * b 1 y u),
        fun y => sourcePlaneWave r v y * b 2 y v,
        fun y => conj (sourcePlaneWave r v y * b 3 y v)] i) (x i) := by
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, graphFourKernel, graphFourAmplitude,
    ← sourcePlaneWave_sub, map_mul]
  ring

theorem sourceGraphFourTransform_endpoint_integral
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) :
    sourceGraphFourTransform ρ X M b W r u v =
      ((M 0*M 1)*(M 2*M 3))⁻¹ •
        (∫ x, graphFourKernel b W x r u v ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  simp_rw [graphFourKernel_endpoint_product, integral_const_mul]
  rw [integral_fintype_prod_eq_prod]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [integral_conj]
  simp only [sourceGraphFourTransform, sourceAngularTransform, sourcePlaneWave,
    Complex.real_smul, map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv,
    Complex.ofReal_mul, mul_inv_rev]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSpatialFubini
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem compact_finite_spatial_integrable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α) (μ : Measure β)
    [IsFiniteMeasure μ] {K : Set α} (hK : MeasurableSet K) (hfinite : ν K < ∞)
    {f : α × β → ℂ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ p, ‖f p‖ ≤ C) (hsupp : ∀ p, f p ≠ 0 → p.1 ∈ K) :
    Integrable f (ν.prod μ) := by
  have hi : Integrable (K.indicator (fun _ : α => C)) ν :=
    (integrableOn_const hfinite.ne).integrable_indicator hK
  apply (hi.comp_fst μ).mono hf.aestronglyMeasurable
  filter_upwards with p
  by_cases hp : p.1 ∈ K
  · simpa only [indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg hC] using hbound p
  · have hz : f p = 0 := by by_contra hn; exact hp (hsupp p hn)
    simp [indicator_of_notMem hp, hz]

theorem graphTransport_family_measurable {α : Type*} [MeasurableSpace α]
    (F : α → ℝ → UnitCircle → UnitCircle → ℂ)
    (hF : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × α =>
      F p.2 p.1.1 p.1.2.1 p.1.2.2)) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (R axis : ℝ) :
    Measurable (fun p : (ℝ × Plane) × α => graphTransport (F p.2) Ψ R axis p.1) := by
  have ha : Measurable (fun p : (ℝ × Plane) × α => graphPlaneAngle p.1.2) :=
    graphPlaneAngle_measurable.comp (measurable_snd.comp measurable_fst)
  have hg : Measurable (fun p : (ℝ × Plane) × α =>
      F p.2 (R*(‖p.1.2‖*Real.sqrt (1+p.1.1^2)/2))
        (sourceUnitDirection (graphPlaneAngle p.1.2+Real.arctan p.1.1))
        (sourceUnitDirection (graphPlaneAngle p.1.2-Real.arctan p.1.1+axis))) :=
    hF.comp (show Measurable (fun p : (ℝ × Plane) × α =>
      ((R*(‖p.1.2‖*Real.sqrt (1+p.1.1^2)/2),
        (sourceUnitDirection (graphPlaneAngle p.1.2+Real.arctan p.1.1),
         sourceUnitDirection (graphPlaneAngle p.1.2-Real.arctan p.1.1+axis))), p.2)) from by fun_prop)
  unfold graphTransport
  simp only [Complex.real_smul]
  apply Measurable.mul
  · fun_prop
  · apply Measurable.mul
    · apply Complex.measurable_ofReal.comp
      exact hΨ.comp (show Measurable (fun p : (ℝ × Plane) × α =>
        ‖p.1.2‖*Real.sqrt (1+p.1.1^2)/2) from by fun_prop)
    · exact hg

theorem graphFourKernel_spatial_integrable
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (R axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    Integrable (fun p : (ℝ × Plane) × (Fin 4 → Plane) =>
      graphTransport (graphFourKernel b W p.2) Ψ R axis p.1) (volume.prod μ) := by
  have hB' := mul_nonneg (mul_nonneg (hB 0) (hB 1)) (mul_nonneg (hB 2) (hB 3))
  apply compact_finite_spatial_integrable volume μ graphTransportBox_compact.measurableSet
    graphTransportBox_compact.measure_lt_top
    (graphTransport_family_measurable _ (graphFourKernel_measurable b W hb hW) hΨ R axis)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hC hB'))
  · intro p
    exact graphTransport_norm_le hsupp hB' hC
      (graphFourKernel_norm_le b W B hB hbound hw p.2) hc R axis p.1
  · intro p hp
    exact graphTransport_support hsupp R axis
      (fun r φ z hn => hchart φ z (graphFourKernel_weight_ne_zero b W p.2 r _ _ hn)) hp

theorem graphFourKernel_spatial_chart
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hbcont : ∀ i x, Continuous (b i x)) (hW : Continuous W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) (axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    R⁻¹ • (∫ x, ∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • graphFourKernel b W x r u v
      ∂sourceArcLength ∂sourceArcLength ∂volume ∂μ) =
      ∫ p : ℝ × Plane, ∫ x, graphTransport (graphFourKernel b W x) Ψ R axis p ∂μ := by
  rw [← integral_smul]
  simp_rw [graphFourKernel_chart_product b W hbcont hW B hB hbound hw hΨ hsupp hC hc hR axis hchart]
  exact integral_integral_swap
    (graphFourKernel_spatial_integrable μ b W hb hW.measurable B hB hbound hw hΨ.measurable
      hsupp hC hc R axis hchart).swap

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphOriginalFubini
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem graphOriginalKernel_measurable
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (R : ℝ) :
    Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphOriginalKernel b W Ψ R p.1 p.2) := by
  unfold graphOriginalKernel
  simp only [Complex.real_smul]
  apply Measurable.mul
  · fun_prop
  · exact graphFourKernel_measurable b W hb hW

theorem graphOriginalKernel_norm_le
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (R : ℝ)
    (p : ℝ × (UnitCircle × UnitCircle)) (x : Fin 4 → Plane) :
    ‖graphOriginalKernel b W Ψ R p x‖ ≤ C*((B 0*B 1)*(B 2*B 3)) := by
  simp only [graphOriginalKernel, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hc _) (graphFourKernel_norm_le b W B hB hbound hw x _ _ _)
    (norm_nonneg _) hC

theorem graphOriginalKernel_integrable
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) :
    Integrable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphOriginalKernel b W Ψ R p.1 p.2)
      ((volume.prod (sourceArcLength.prod sourceArcLength)).prod μ) := by
  have hK : IsCompact (Icc (R/4) (4*R) ×ˢ (univ : Set (UnitCircle × UnitCircle))) :=
    isCompact_Icc.prod isCompact_univ
  apply compact_finite_spatial_integrable _ μ hK.measurableSet hK.measure_lt_top
    (graphOriginalKernel_measurable b W hb hW hΨ R)
    (mul_nonneg hC (mul_nonneg (mul_nonneg (hB 0) (hB 1)) (mul_nonneg (hB 2) (hB 3))))
  · intro p
    exact graphOriginalKernel_norm_le b W B hB hbound hw hC hc R p.1 p.2
  · intro p hp
    have hn : Ψ (p.1.1/R) ≠ 0 := by
      intro hz; exact hp (by simp [graphOriginalKernel, hz])
    have hh := hsupp _ hn
    refine ⟨⟨?_,?_⟩,mem_univ _⟩
    · have := (lt_div_iff₀ hR).mp hh.1; linarith
    · have := (div_lt_iff₀ hR).mp hh.2; linarith

theorem circle_pair_integral (F : UnitCircle × UnitCircle → ℂ)
    (hF : Measurable F) {C : ℝ} (hb : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, F p ∂sourceArcLength.prod sourceArcLength) =
      ∫ u, ∫ v, F (u,v) ∂sourceArcLength ∂sourceArcLength :=
  integral_prod _ (Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hb))

theorem graphOriginalKernel_spatial_swap
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ r : ℝ, ∫ u, ∫ v, ∫ x, graphOriginalKernel b W Ψ R (r,(u,v)) x ∂μ
      ∂sourceArcLength ∂sourceArcLength) =
      ∫ x, ∫ r : ℝ, ∫ u, ∫ v, graphOriginalKernel b W Ψ R (r,(u,v)) x
        ∂sourceArcLength ∂sourceArcLength ∂volume ∂μ := by
  let G := graphOriginalKernel b W Ψ R
  have hg := graphOriginalKernel_measurable b W hb hW hΨ R
  have hd := graphOriginalKernel_norm_le b W B hB hbound hw hC hc R
  have hi := graphOriginalKernel_integrable μ b W hb hW B hB hbound hw hΨ hsupp hC hc hR
  have hslice (x : Fin 4 → Plane) : Integrable (fun p => G p x)
      (volume.prod (sourceArcLength.prod sourceArcLength)) := by
    have hh := graphOriginalKernel_integrable (Measure.dirac x) b W hb hW B hB hbound hw
      hΨ hsupp hC hc hR
    have he := hh.integral_prod_left
    simpa only [integral_dirac] using he
  have hcircle (r : ℝ) :
      (∫ p, ∫ x, G (r,p) x ∂μ ∂sourceArcLength.prod sourceArcLength) =
        ∫ u, ∫ v, ∫ x, G (r,(u,v)) x ∂μ ∂sourceArcLength ∂sourceArcLength := by
    have hm : Measurable (fun p : (UnitCircle × UnitCircle) × (Fin 4 → Plane) => G (r,p.1) p.2) :=
      hg.comp (show Measurable (fun p : (UnitCircle × UnitCircle) × (Fin 4 → Plane) =>
        ((r,p.1),p.2)) from by fun_prop)
    exact circle_pair_integral _ hm.stronglyMeasurable.integral_prod_right'.measurable
      (fun p => norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (hd (r,p))))
  calc
    _ = ∫ r : ℝ, ∫ p, ∫ x, G (r,p) x ∂μ ∂sourceArcLength.prod sourceArcLength := by
      simp_rw [hcircle]
      rfl
    _ = ∫ p, ∫ x, G p x ∂μ ∂volume.prod (sourceArcLength.prod sourceArcLength) :=
      (integral_prod _ hi.integral_prod_left).symm
    _ = ∫ x, ∫ p, G p x ∂volume.prod (sourceArcLength.prod sourceArcLength) ∂μ :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_prod _ (hslice x)]
      apply integral_congr_ae
      filter_upwards with r
      exact circle_pair_integral _
        (hg.comp (show Measurable (fun p : UnitCircle × UnitCircle => ((r,p),x)) from by fun_prop))
        (fun p => hd (r,p) x)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphTransformChart
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceGraphFourTransform_chart
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hbcont : ∀ i x, Continuous (b i x)) (hW : Continuous W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) (axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • sourceGraphFourTransform ρ X M b W r u v
      ∂sourceArcLength ∂sourceArcLength) =
      ((M 0*M 1)*(M 2*M 3))⁻¹ •
        (∫ p : ℝ × Plane, ∫ x, graphTransport (graphFourKernel b W x) Ψ R axis p
          ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  let μ := Measure.pi (fun i => (ρ i).restrict (X i))
  let c := ((M 0*M 1)*(M 2*M 3))⁻¹
  have he (r : ℝ) (u v : UnitCircle) :
      Ψ (r/R) • sourceGraphFourTransform ρ X M b W r u v =
        c • (∫ x, graphOriginalKernel b W Ψ R (r,(u,v)) x ∂μ) := by
    rw [sourceGraphFourTransform_endpoint_integral]
    change Ψ (r/R) • (c • (∫ x, graphFourKernel b W x r u v ∂μ)) = _
    rw [smul_comm]
    apply congrArg (fun value : ℂ => c • value)
    exact (integral_smul _ _).symm
  simp_rw [he, integral_smul]
  rw [smul_comm (R⁻¹) c]
  apply congrArg (fun value : ℂ => c • value)
  rw [graphOriginalKernel_spatial_swap μ b W hb hW.measurable B hB hbound hw
    hΨ.measurable hsupp hC hc hR]
  exact graphFourKernel_spatial_chart μ b W hb hbcont hW B hB hbound hw hΨ hsupp hC hc hR axis hchart

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphInheritedTransformChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem continuous_supported_bump_bound {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |Ψ t| ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (1/4:ℝ) 4)).exists_bound_of_continuousOn
    hΨ.continuousOn
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t
  by_cases hz : Ψ t = 0
  · simp only [hz, abs_zero]; exact le_max_left _ _
  · exact (hC t (Ioo_subset_Icc_self (hsupp t hz))).trans (le_max_right _ _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphPointIntegralChart
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphTransport_eq_point_phase (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ)
    {η : Plane} (hη : η ∈ graphPlaneSlit) (z : ℝ) :
    graphTransport (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
      Ψ ((2:ℝ)^v) (graphSourceChartAxis distance plus) (z,η) =
      Complex.exp (Complex.I*Complex.ofReal ((2:ℝ)^v*inner ℝ η
        (graphA z (x 0-x 1)+graphSourceSign distance plus • graphB z (x 2-x 3)))) *
        graphAmplitudePullback b x distance plus axis δ j k Ψ (η,z) := by
  cases distance <;> cases plus <;>
    simp only [graphTransport,graphAmplitudePullback,graphShellJacobian,
      graphSourceChartAxis,graphSourceSign,Bool.false_eq_true,↓reduceIte,add_zero,one_smul,
      neg_one_smul,← sub_eq_add_neg] <;>
    first | rw [graphFourKernel_phase_plus b _ x hη] | rw [graphFourKernel_phase_minus b _ x hη]
  all_goals simp only [Complex.real_smul,Complex.ofReal_mul]; ring_nf

theorem graphTransport_integral_eq_pointIntegral (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ)
    (hi : Integrable (graphTransport
      (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
      Ψ ((2:ℝ)^v) (graphSourceChartAxis distance plus))) :
    (∫ p : ℝ × Plane, graphTransport
      (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
      Ψ ((2:ℝ)^v) (graphSourceChartAxis distance plus) p) =
    graphPointIntegral (graphAmplitudePullback b x distance plus axis δ j k Ψ)
      v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards [graphPlaneSlit_ae_eq_univ] with η hη
  exact graphTransport_eq_point_phase b x distance plus axis δ v j k Ψ (hη.mpr (mem_univ η)) z

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFourTransformPointIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceGraphFourTransform_pointIntegral_oai
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hbcont : ∀ i x, Continuous (b i x))
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      sourceGraphFourTransform ρ X M b (graphSourceWeight distance plus axis (angularBinCount δ) j k) r u w
        ∂sourceArcLength ∂sourceArcLength) =
    ((M 0*M 1)*(M 2*M 3))⁻¹ •
      (∫ x, graphPointIntegral (graphAmplitudePullback b x distance plus axis δ j k Ψ)
        v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)
        ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  let W := graphSourceWeight distance plus axis (angularBinCount δ) j k
  let μ := Measure.pi (fun i => (ρ i).restrict (X i))
  have hW := graphSourceWeight_continuous distance plus axis (angularBinCount δ) j k
  have hw := graphSourceWeight_norm_le distance plus axis (angularBinCount δ) j k
  have hchart := graphSourceWeight_parameter distance plus axis (angularBinCount δ) j k
  obtain ⟨C,hC,hc⟩ := continuous_supported_bump_bound hΨ hsupp
  rw [sourceGraphFourTransform_chart ρ X M b W hb hbcont hW B hB hbound hw hΨ hsupp hC hc
    (by positivity : (0:ℝ) < (2:ℝ)^v) (graphSourceChartAxis distance plus) hchart]
  congr 1
  have hi := graphFourKernel_spatial_integrable μ b W hb hW.measurable B hB hbound hw
    hΨ.measurable hsupp hC hc ((2:ℝ)^v) (graphSourceChartAxis distance plus) hchart
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with x
  exact graphTransport_integral_eq_pointIntegral b x distance plus axis δ v j k Ψ
    (graphFourKernel_transport_integrable b W hbcont hW B hB hbound hw hΨ hsupp hC hc
      ((2:ℝ)^v) (graphSourceChartAxis distance plus) hchart x)

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral_oai := @OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral_oai
