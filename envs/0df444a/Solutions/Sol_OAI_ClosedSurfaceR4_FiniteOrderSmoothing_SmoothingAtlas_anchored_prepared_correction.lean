-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_prepared_correction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:41:14.462798+00:00
-- url     : https://prove2.me/submissions/c389bd88-141d-4bb0-b24a-17a5fcb74c4d

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_anchored_fixed_order_step

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_add (p : M) (ψ : M → ℝ) (f g : M → V) :
    localize p ψ (f + g) = localize p ψ f + localize p ψ g := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_add]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and elementary norm operations for actual global metric tensors. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualSmul
variable (A : SmoothingAtlas M)
include A

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberSpace
local instance metricBoundSectionNormed_r37ce0b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_r37ce0b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_add {T S : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hS : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (S p)))
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbT : A.TensorWeightedBound s m C T) (hbS : A.TensorWeightedBound s m D S) :
    A.TensorWeightedBound s m (C+D) (T+S) := by
  intro i
  change WeightedEstimates.WeightedBound univ s m (C+D) (A.bundleLocalize A.tensorTriv i (T+S))
  rw [A.bundleLocalize_add]
  exact (hbT i).add uniqueDiffOn_univ hs
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT).contDiffOn
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hS).contDiffOn (hbS i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition and inverse-scale evaluation of the polynomial
budgets in the correction construction. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.of_le {f g : ℝ → ℝ} (hg : HasPolynomialBound g)
    (h0 : ∀ x, 1 ≤ x → 0 ≤ f x) (hle : ∀ x, 1 ≤ x → f x ≤ g x) :
    HasPolynomialBound f := by
  obtain ⟨d,C,hC,hg⟩ := hg
  exact ⟨d,C,hC,fun x hx => ⟨h0 x hx,(hle x hx).trans (hg x hx).2⟩⟩

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionScaleAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale arithmetic in the normalized metric-error estimate. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

lemma scale_quotient_product {t : ℝ} (ht : 0 < t) (a b c : ℝ) :
    (t ^ a * t ^ b) / t ^ c = t ^ (a + b - c) := by
  rw [← Real.rpow_add ht, Real.rpow_sub ht]

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExplicitPowerThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit integer-power thresholds for the finitely many real powers
used by the first correction block. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

theorem powerThreshold_spec {n : ℕ} (hn : 0 < n) {c b p : ℝ}
    (hc : 0 ≤ c) (hb : 0 < b) (hp : (n : ℝ)⁻¹ ≤ p) :
    0 < powerThreshold n c b ∧ powerThreshold n c b ≤ 1 ∧
    ∀ t : ℝ, 0 < t → t < powerThreshold n c b → c*t^p < b := by
  let q := min 1 (b/(c+1))
  have hq : 0 < q := lt_min zero_lt_one (div_pos hb (by linarith))
  have hq1 : q ≤ 1 := min_le_left _ _
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨pow_pos hq n, pow_le_one₀ hq.le hq1,?_⟩
  intro t ht hsmall
  have ht1 : t ≤ 1 := hsmall.le.trans (pow_le_one₀ hq.le hq1)
  have hroot : t^((n : ℝ)⁻¹) < q := by
    have h := Real.rpow_lt_rpow ht.le hsmall (inv_pos.mpr hn')
    change t^((n : ℝ)⁻¹) < (q^n)^((n : ℝ)⁻¹) at h
    rwa [← Real.rpow_natCast, Real.rpow_rpow_inv hq.le hn'.ne'] at h
  have htp : t^p < q :=
    (Real.rpow_le_rpow_of_exponent_ge ht ht1 hp).trans_lt hroot
  have hqb : (c+1)*q ≤ b := by
    have h := (le_div_iff₀ (show 0 < c+1 by linarith)).mp
      (show q ≤ b/(c+1) from min_le_right _ _)
    nlinarith
  calc
    c*t^p ≤ (c+1)*t^p := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ht.le _)
    _ < (c+1)*q := mul_lt_mul_of_pos_left htp (by linarith)
    _ ≤ b := hqb

/-- An upper bound on the reciprocal threshold follows from upper bounds
on the coefficient and reciprocal margin. -/
lemma powerThreshold_inverse_le {n : ℕ} {c b C B : ℝ}
    (hc : 0 ≤ c) (hb : 0 < b) (hC : c ≤ C) (hB : b⁻¹ ≤ B) :
    (powerThreshold n c b)⁻¹ ≤ (1+(C+1)*B)^n := by
  have hC0 : 0 ≤ C := hc.trans hC
  have hB0 : 0 ≤ B := (inv_pos.mpr hb).le.trans hB
  have hq : 0 < min 1 (b/(c+1)) := lt_min zero_lt_one (div_pos hb (by linarith))
  have hi : (min 1 (b/(c+1)))⁻¹ ≤ 1+(C+1)*B := by
    have hh : (c+1)/b ≤ (C+1)*B := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (by linarith) hB (inv_nonneg.mpr hb.le) (by linarith)
    by_cases hle : b/(c+1) ≤ 1
    · rw [min_eq_right hle, inv_div]
      linarith
    · rw [min_eq_left (le_of_not_ge hle), inv_one]
      nlinarith
  rw [powerThreshold, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hi n

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ExplicitCorrectionBudgetThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit scale preserving the input and metric correction budgets. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

theorem correctionBudgetThreshold_spec {A B a N L : ℝ} (hAB : A < B) (ha : 0 < a) :
    0 < correctionBudgetThreshold A B a N L ∧
    correctionBudgetThreshold A B a N L ≤ 1 ∧
    ∀ t : ℝ, 0 < t → t < correctionBudgetThreshold A B a N L →
      A+N*t^(1/5 : ℝ)*(1+B) ≤ B ∧ L*(1+2*B)*t^(1/5 : ℝ) ≤ a/8 := by
  have h₁ := powerThreshold_spec (n := 5) (by decide) (abs_nonneg (N*(1+B)))
    (sub_pos.mpr hAB) (show ((5 : ℕ) : ℝ)⁻¹ ≤ (1/5 : ℝ) by norm_num)
  have h₂ := powerThreshold_spec (n := 5) (by decide) (abs_nonneg (L*(1+2*B)))
    (show 0 < a/8 by positivity) (show ((5 : ℕ) : ℝ)⁻¹ ≤ (1/5 : ℝ) by norm_num)
  refine ⟨lt_min h₁.1 h₂.1, (min_le_left _ _).trans h₁.2.1,?_⟩
  intro t ht hsmall
  have h₁t := (h₁.2.2 t ht (hsmall.trans_le (min_le_left _ _))).le
  have h₂t := (h₂.2.2 t ht (hsmall.trans_le (min_le_right _ _))).le
  have hpow : 0 ≤ t^(1/5 : ℝ) := Real.rpow_nonneg ht.le _
  have hn := mul_le_mul_of_nonneg_right (le_abs_self (N*(1+B))) hpow
  have hl := mul_le_mul_of_nonneg_right (le_abs_self (L*(1+2*B))) hpow
  constructor
  · nlinarith
  · exact hl.trans h₂t

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanIteration
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth of the actual finite mean iteration and of the
finite value budget appearing in its explicit smallness threshold. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.nonneg {f : ℝ → ℝ} (hf : HasPolynomialBound f)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ f x := by
  obtain ⟨_,_,_,h⟩ := hf
  exact (h x hx).1

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPowerThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial reciprocal control for explicit positive-power thresholds.
No compactness choice enters the numerical threshold. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

theorem powerThreshold_inverse_polynomial (n : ℕ) (c b C B : ℝ → ℝ)
    (hC : HasPolynomialBound C) (hB : HasPolynomialBound B)
    (hc : ∀ x, 1 ≤ x → 0 ≤ c x) (hb : ∀ x, 1 ≤ x → 0 < b x)
    (hcC : ∀ x, 1 ≤ x → c x ≤ C x)
    (hbB : ∀ x, 1 ≤ x → (b x)⁻¹ ≤ B x) :
    HasPolynomialBound (fun x => (powerThreshold n (c x) (b x))⁻¹) := by
  apply HasPolynomialBound.of_le
    (((polynomialBound_const zero_le_one).add
      ((hC.add (polynomialBound_const zero_le_one)).mul hB)).pow n)
  · intro x hx
    apply inv_nonneg.mpr
    unfold powerThreshold
    exact pow_nonneg (le_min zero_le_one (div_nonneg (hb x hx).le (by linarith [hc x hx]))) _
  · intro x hx
    exact powerThreshold_inverse_le (hc x hx) (hb x hx) (hcC x hx) (hbB x hx)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFixedOrderThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At each fixed order, the reciprocal of the scale threshold is
polynomial in the numerical data and reciprocal geometric margins. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

lemma min_inverse_le_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (min x y)⁻¹ ≤ x⁻¹+y⁻¹ := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    linarith [inv_nonneg.mpr hy.le]
  · rw [min_eq_right h]
    linarith [inv_nonneg.mpr hx.le]

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialCorrectionBudget
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial reciprocal control for preservation of the iteration budgets. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

lemma polynomial_inverse_min {f g : ℝ → ℝ}
    (hf : HasPolynomialBound (fun x => (f x)⁻¹))
    (hg : HasPolynomialBound (fun x => (g x)⁻¹))
    (hfp : ∀ x, 1 ≤ x → 0 < f x) (hgp : ∀ x, 1 ≤ x → 0 < g x) :
    HasPolynomialBound (fun x => (min (f x) (g x))⁻¹) := by
  apply HasPolynomialBound.of_le (hf.add hg)
  · intro x hx
    exact inv_nonneg.mpr (lt_min (hfp x hx) (hgp x hx)).le
  · intro x hx
    exact min_inverse_le_add (hfp x hx) (hgp x hx)

theorem correctionBudgetThreshold_inverse_polynomial
    (A B N L : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hB : HasPolynomialBound B) (hN : HasPolynomialBound N) (hL : HasPolynomialBound L)
    (hgap : ∀ x, 1 ≤ x → 1 ≤ B x-A x) :
    HasPolynomialBound (fun x => (correctionBudgetThreshold (A x) (B x) a (N x) (L x))⁻¹) := by
  let C₁ := fun x => N x*(1+B x)
  let C₂ := fun x => L x*(1+2*B x)
  have hC₁ : HasPolynomialBound C₁ := hN.mul ((polynomialBound_const zero_le_one).add hB)
  have hC₂ : HasPolynomialBound C₂ := hL.mul ((polynomialBound_const zero_le_one).add
    ((polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul hB))
  have h₁ : HasPolynomialBound (fun x => (powerThreshold 5 |N x*(1+B x)| (B x-A x))⁻¹) := by
    apply powerThreshold_inverse_polynomial 5 _ _ C₁ (fun _ => 1) hC₁
      (polynomialBound_const zero_le_one) (fun _ _ => abs_nonneg _) (fun x hx => zero_lt_one.trans_le (hgap x hx))
    · intro x hx
      exact le_of_eq (abs_of_nonneg (hC₁.nonneg hx))
    · intro x hx
      simpa only [one_div,inv_one] using one_div_le_one_div_of_le zero_lt_one (hgap x hx)
  have h₂ : HasPolynomialBound (fun x => (powerThreshold 5 |L x*(1+2*B x)| (a/8))⁻¹) := by
    apply powerThreshold_inverse_polynomial 5 _ _ C₂ (fun _ => (a/8)⁻¹) hC₂
      (polynomialBound_const (by positivity)) (fun _ _ => abs_nonneg _)
      (fun _ _ => by positivity)
    · intro x hx
      exact le_of_eq (abs_of_nonneg (hC₂.nonneg hx))
    · intro _ _
      exact le_rfl
  apply polynomial_inverse_min h₁ h₂
  · intro x hx
    unfold powerThreshold
    exact pow_pos (lt_min zero_lt_one (div_pos (zero_lt_one.trans_le (hgap x hx)) (by positivity))) _
  · intro x _
    unfold powerThreshold
    exact pow_pos (lt_min zero_lt_one (div_pos (by positivity) (by positivity))) _

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InputSize
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joint input norms for the adaptive correction iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeFiberSpace
local instance inputSizeSectionNormed_r37ce0b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputSizeSectionSpace_r37ce0b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma inputBound_mono_order {t C : ℝ} {m r : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p} (hb : A.InputBound t m C G H)
    (hr : r ≤ m) : A.InputBound t r C G H := by
  constructor
  · intro i j hj x
    exact hb.1 i j (hj.trans (Nat.add_le_add_left hr 2)) x
  · intro i
    exact (hb.2 i).mono_order hr

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExactInputRecurrenceBound
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two components of the actual input share a contracting affine bound. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

theorem exact_input_recurrence_bound {t P P₀ Pm B C L B₀ : ℝ} {k : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hPm : 0 ≤ Pm) (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) (hB₀ : 0 ≤ B₀) :
    P+P₀+t^(6/5 : ℝ)*Pm+(t^(6/5 : ℝ)/t)*C+
      (B*(t^(k : ℝ)*t^(6/5 : ℝ)))/(t^(6/5 : ℝ))^2+
      L*(1+B₀+C)*t^(1/5 : ℝ) ≤
    P+P₀+(Pm+B+L*(1+B₀)+1+L)*t^(1/5 : ℝ)*(1+C) := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hτ : t^(6/5 : ℝ) ≤ t^(1/5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have hratio : t^(6/5 : ℝ)/t = t^(1/5 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_sub ht]
    norm_num
  have hquotient : (t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^2 =
      t^((k : ℝ)-(6/5 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ht.le,scale_quotient_product ht]
    congr 1
    ring
  have hquotient_le : (t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^2 ≤ t^(1/5 : ℝ) := by
    rw [hquotient]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hterm : (B*(t^(k : ℝ)*t^(6/5 : ℝ)))/(t^(6/5 : ℝ))^2 ≤ B*t^(1/5 : ℝ) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hquotient_le hB
  calc
    _ ≤ P+P₀+t^(1/5 : ℝ)*Pm+t^(1/5 : ℝ)*C+B*t^(1/5 : ℝ)+
        L*(1+B₀+C)*t^(1/5 : ℝ) := by
      rw [hratio]
      gcongr
    _ = P+P₀+(Pm+C+B+L*(1+B₀+C))*t^(1/5 : ℝ) := by ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      rw [mul_assoc _ _ (1+C),mul_comm (t^(1/5 : ℝ)) (1+C),← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
      nlinarith [mul_nonneg hPm hC,mul_nonneg hB hC,
        mul_nonneg (mul_nonneg hL hB₀) hC]

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExactScaleOrdering
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and ordering of the actual scales in each correction step. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

theorem exact_scale_order {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {k : ℕ} (hk : 10 ≤ k) :
    t^((6/5 : ℝ)*((k : ℝ)+1)) ≤ t^(k : ℝ) ∧
      t^(k : ℝ) ≤ t^(6/5 : ℝ) ∧ t^(6/5 : ℝ) ≤ t^(11/10 : ℝ) ∧
      t^(11/10 : ℝ) ≤ t := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith),
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith),
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num),?_⟩
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (show (1 : ℝ) ≤ 11/10 by norm_num)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShiftedScaleGain
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inherited derivatives gain a scale ratio above the fixed prefix. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reducing the scale preserves the unweighted prefix and contracts all
higher weighted derivatives by at least `τ/t`. -/
theorem ShiftedBound.shrink_with_prefix {q m : ℕ} {t τ A C : ℝ} {f : Base → V}
    (hb : ShiftedBound q 0 t A f) (hc : ShiftedBound q m t C f)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ShiftedBound q m τ (A + (τ / t) * C) f := by
  intro j hj x
  by_cases hjq : j ≤ q
  · have h := hb j (by omega) x
    simp only [Nat.sub_eq_zero_of_le hjq, pow_zero, one_mul] at h ⊢
    exact h.trans (le_add_of_nonneg_right (mul_nonneg (div_nonneg hτ ht.le) hC))
  · have hp : (τ / t) ^ (j - q) ≤ τ / t := by
      simpa only [pow_one] using pow_le_pow_of_le_one (div_nonneg hτ ht.le)
        ((div_le_one ht).mpr hτt) (show 1 ≤ j - q by omega)
    calc
      _ ≤ τ ^ (j - q) * (C / t ^ (j - q)) :=
        mul_le_mul_of_nonneg_left (hc.deriv_le ht hj x) (pow_nonneg hτ _)
      _ = (τ / t) ^ (j - q) * C := by rw [div_pow]; ring
      _ ≤ (τ / t) * C := mul_le_mul_of_nonneg_right hp hC
      _ ≤ _ := le_add_of_nonneg_left hA

/-- Adding the actual increment adds its shifted derivative budget. -/
theorem ShiftedBound.add {q m : ℕ} {s A B : ℝ} {f g : Base → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hs : 0 ≤ s)
    (hb : ShiftedBound q m s A f) (hc : ShiftedBound q m s B g) :
    ShiftedBound q m s (A + B) (f + g) := by
  intro j hj x
  rw [iteratedFDeriv_add_apply (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt]
  calc
    _ ≤ s ^ (j - q) * (‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hs _)
    _ = s ^ (j - q) * ‖iteratedFDeriv ℝ j f x‖ +
        s ^ (j - q) * ‖iteratedFDeriv ℝ j g x‖ := by ring
    _ ≤ _ := add_le_add (hb j hj x) (hc j hj x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalScaleGain
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inherited-map part of the all-order correction recurrence. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- Shrinking the scale gains one ratio in every positive weighted order. -/
theorem shifted_shrink_with_prefix {q m : ℕ} {t τ P C : ℝ} {f : M → V}
    (hb : A.ShiftedBound q 0 t P f) (hc : A.ShiftedBound q m t C f)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    A.ShiftedBound q m τ (P + (τ / t) * C) f :=
  fun i => (hb i).shrink_with_prefix (hc i) ht hτ hτt hP hC

/-- The new map keeps the old low-derivative baseline; its inherited high
orders contract, and the actual increment contributes its own budget. -/
theorem shifted_map_recurrence {q m : ℕ} {t τ P C D : ℝ} {f u : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f)
    (hu : ContMDiff planeModel 𝓘(ℝ, V) ∞ u)
    (hb : A.ShiftedBound q 0 t P f) (hc : A.ShiftedBound q m t C f)
    (hd : A.ShiftedBound q m τ D u)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    A.ShiftedBound q m τ (P + (τ / t) * C + D) (f + u) := by
  have hsh := A.shifted_shrink_with_prefix hb hc ht hτ hτt hP hC
  intro i
  rw [localize_add]
  exact (hsh i).add
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hu) hτ (hd i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalInputRecurrence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both components of the actual next input admit a common recurrence bound. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates JetPolynomial
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma shiftedBound_of_weighted {f : Base → V} {s C : ℝ} {q m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : WeightedEstimates.WeightedBound univ s (q+m) C f) :
    ShiftedBound q m s (C/s^q) f := by
  intro j hj x
  have hh := hb.deriv_le hs hj (mem_univ x)
  rw [iteratedFDerivWithin_univ] at hh
  by_cases hq : q ≤ j
  · have he : s^j = s^(j-q)*s^q := by rw [← pow_add,Nat.sub_add_cancel hq]
    calc
      _ ≤ s^(j-q)*(C/s^j) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ = _ := by rw [he]; field_simp
  · have hjq : j ≤ q := by omega
    simp only [Nat.sub_eq_zero_of_le hjq,pow_zero,one_mul]
    exact hh.trans (div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 hjq))

lemma weighted_shrink_with_norm {E W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E → W} {s P C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hp : WeightedEstimates.WeightedBound univ 1 0 P f)
    (hc : WeightedEstimates.WeightedBound univ 1 m C f) :
    WeightedEstimates.WeightedBound univ s m (P+s*C) f := by
  intro j hj x hx
  by_cases hz : j = 0
  · subst j
    have h := hp 0 le_rfl x hx
    simp only [pow_zero,one_mul] at h ⊢
    exact h.trans (le_add_of_nonneg_right (mul_nonneg hs hC))
  · have h := hc j hj x hx
    simp only [one_pow,one_mul] at h
    calc
      _ ≤ s^j*C := mul_le_mul_of_nonneg_left h (pow_nonneg hs _)
      _ ≤ s*C := mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using pow_le_pow_of_le_one hs hs1 (show 1 ≤ j by omega)) hC
      _ ≤ P+s*C := le_add_of_nonneg_left (by
        exact le_trans (norm_nonneg (f x)) (hp.norm_le (mem_univ x)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputRecurrenceFiberSpace
omit [CompactSpace M] in
lemma weighted_to_shifted {F : M → V} {s C : ℝ} {q m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : A.WeightedBound s (q+m) C F) : A.ShiftedBound q m s (C/s^q) F :=
  fun i => shiftedBound_of_weighted hs hs1 hC (hb i)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputRecurrenceFiberNormed
omit [CompactSpace M] in
lemma tensor_shrink_with_norm {T : ∀ p : M, CovariantTwoTensor p} {s P C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hp : A.TensorWeightedBound 1 0 P T) (hc : A.TensorWeightedBound 1 m C T) :
    A.TensorWeightedBound s m (P+s*C) T :=
  fun i => weighted_shrink_with_norm hs hs1 hC (hp i) (hc i)

theorem next_input_bound {target : ∀ p : M, CovariantTwoTensor p}
    (htarget : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    {F U : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hU : ContMDiff planeModel spaceModel ∞ U)
    {t τ P P₀ Pm C K B δ' : ℝ} {m : ℕ}
    (ht : 0 < t) (hτ : 0 < τ) (hτt : τ ≤ t) (hτ1 : τ ≤ 1)
    (hP : 0 ≤ P) (hP₀ : 0 ≤ P₀) (hPm : 0 ≤ Pm)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hp : A.ShiftedBound 2 0 t P F) (hc : A.ShiftedBound 2 m t C F)
    (hu : A.WeightedBound τ (2+m) K U)
    (ht₀ : A.TensorWeightedBound 1 0 P₀ target)
    (htm : A.TensorWeightedBound 1 m Pm target)
    (hb : A.TensorWeightedBound τ m B (normalizedTensorDefect target δ' (F+U)-target)) :
    A.InputBound τ m (P+P₀+τ*Pm+(τ/t)*C+K/τ^2+B)
      (F+U) (normalizedTensorDefect target δ' (F+U)) := by
  have hmap := A.shifted_map_recurrence hF hU hp hc
    (A.weighted_to_shifted hτ hτ1 hK hu) ht hτ.le hτt hP hC
  have htargetBound := A.tensor_shrink_with_norm hτ.le hτ1 hPm ht₀ htm
  have hdiff := (A.normalizedTensorDefect_smooth htarget δ' (hF.add hU)).sub_section htarget
  have htensor := A.tensorWeightedBound_add htarget hdiff hτ.le htargetBound hb
  have he : target+(normalizedTensorDefect target δ' (F+U)-target) =
      normalizedTensorDefect target δ' (F+U) := by abel
  rw [he] at htensor
  constructor
  · intro i j hj x
    exact (hmap i j hj x).trans (by
      have hq : 0 ≤ τ*Pm := mul_nonneg hτ.le hPm
      linarith)
  · intro i
    exact (htensor i).mono_const (by
      have hq : 0 ≤ (τ/t)*C := mul_nonneg (div_nonneg hτ.le ht.le) hC
      have hk : 0 ≤ K/τ^2 := div_nonneg hK (sq_nonneg τ)
      linarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExactInputRecurrence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual next map and normalized defect satisfy the waiting recurrence. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

local instance exactInputFiberNormed_r37ce0b_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance exactInputFiberSpace_r37ce0b_1 : NormedSpace ℝ TensorFiber := inferInstance
theorem exact_scale_input_recurrence {g : SmoothMetric M} {G U : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U)
    {t P P₀ Pm B C L B₀ δ' : ℝ} {k m : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hP : 0 ≤ P) (hP₀ : 0 ≤ P₀) (hPm : 0 ≤ Pm)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) (hB₀ : 0 ≤ B₀)
    (hp : A.ShiftedBound 2 0 t P G)
    (hc : A.ShiftedBound 2 m t C G)
    (hu : A.WeightedBound (t^(6/5 : ℝ)) (2+m) (B*(t^(k : ℝ)*t^(6/5 : ℝ))) U)
    (ht₀ : A.TensorWeightedBound 1 0 P₀ g.inner)
    (htm : A.TensorWeightedBound 1 m Pm g.inner)
    (he : A.TensorWeightedBound (t^(6/5 : ℝ)) m (L*(1+B₀+C)*t^(1/5 : ℝ))
      (normalizedTensorDefect g.inner δ' (G+U)-g.inner)) :
    A.InputBound (t^(6/5 : ℝ)) m
      (P+P₀+(Pm+B+L*(1+B₀)+1+L)*t^(1/5 : ℝ)*(1+C))
      (G+U) (normalizedTensorDefect g.inner δ' (G+U)) := by
  have hτ : 0 < t^(6/5 : ℝ) := Real.rpow_pos_of_pos ht _
  obtain ⟨_,_,hτs,hst⟩ := ExactCorrection.exact_scale_order ht ht1 hk
  have hτt := hτs.trans hst
  have hh := A.next_input_bound g.contMDiff hG hU ht hτ hτt (hτt.trans ht1)
    hP hP₀ hPm hC (mul_nonneg hB (mul_nonneg (Real.rpow_nonneg ht.le _) hτ.le))
    (mul_nonneg (mul_nonneg hL (by linarith)) (Real.rpow_nonneg ht.le _))
    hp hc hu ht₀ htm he
  have hsize := ExactCorrection.exact_input_recurrence_bound ht ht1 hk hPm hB hC hL hB₀
    (P := P) (P₀ := P₀)
  constructor
  · intro i j hj x
    exact (hh.1 i j hj x).trans hsize
  · intro i
    exact (hh.2 i).mono_const hsize

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AnchoredInputStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full next-input recurrence with polynomial fast-family constants. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredInputFiberNormed
local instance anchoredInputFiberSpace_r37ce0b_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance anchoredInputDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredInputFiberNormed
local instance anchoredInputFiberSpace_r37ce0b_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance anchoredInputDualSmul_r37ce0b_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance anchoredInputSectionNormed_r37ce0b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredInputSectionSpace_r37ce0b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem anchored_input_step (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ Base : ℝ → ℝ, HasPolynomialBound Base →
    ∃ A₀ : ℝ → ℝ, HasPolynomialBound A₀ ∧
    ∀ Budget : ℝ → ℝ, HasPolynomialBound Budget → ∀ k : ℕ, 10 ≤ k →
    ∃ ε L : ℝ → ℝ, ∃ N : ℕ → ℝ → ℝ,
      HasPolynomialBound (fun x => (ε x)⁻¹) ∧ HasPolynomialBound L ∧
      (∀ m, HasPolynomialBound (N m)) ∧
      (∀ x, 1 ≤ x → 0 < ε x ∧ ε x ≤ 1) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
      A.ShiftedBound 2 0 1 (Base z⁻¹) F →
    ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε z⁻¹ → ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      A.InputBound t (40*(k+1)) (Budget z⁻¹) G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
      A.WeightedBound 1 2 ((z^4/D)/4) (G-F) →
      (∀ x, ‖A.tensorEncode (normalizedTensorDefect g.inner (t^(k : ℝ)) G) x-A.tensorEncode g.inner x‖ ≤ a/8) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m ≤ k/2, A.WeightedBound 1 m ((z^4/D)*t) U) ∧
        A.TensorWeightedBound (t^(6/5 : ℝ)) 0 (L z⁻¹*(1+2*Budget z⁻¹)*t^(1/5 : ℝ))
          (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner) ∧
        ∀ m C, 0 ≤ C → A.InputBound t m C G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
          A.InputBound (t^(6/5 : ℝ)) m (A₀ z⁻¹+N m z⁻¹*t^(1/5 : ℝ)*(1+C))
            (G+U) (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)) := by
  classical
  obtain ⟨z₀,a,D,hz₀,hz₀1,ha,hD,hall⟩ := A.anchored_fixed_order_step g houter R c B b hc hB hb
  choose Pg hPg hgb using fun m => A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain m g.contMDiff
  refine ⟨z₀,a,D,hz₀,hz₀1,ha,hD,?_⟩
  intro Base hBase
  let A₀ := fun x => Base x+1+Pg 0
  have hA₀ : HasPolynomialBound A₀ := ((hBase.add (polynomialBound_const zero_le_one)).add
    (polynomialBound_const (hPg 0)))
  refine ⟨A₀,hA₀,?_⟩
  intro Budget hBudget k hk
  obtain ⟨ε,P,L,hε,hP,hL,hεp,hstep⟩ := hall k hk Budget hBudget
  let N := fun m x => Pg m+P (m+2) x+L m x*(1+Budget x)+1+L m x
  have hN (m : ℕ) : HasPolynomialBound (N m) :=
    ((((polynomialBound_const (hPg m)).add (hP (m+2))).add
      ((hL m).mul ((polynomialBound_const zero_le_one).add hBudget))).add
      (polynomialBound_const zero_le_one)).add (hL m)
  refine ⟨ε,L 0,N,hε,hL 0,hN,hεp,?_⟩
  intro z hz hzsmall F hF hFb hFm hbase G hG t ht htε j hkj hjk hinput hnear hmetric
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  have hBaseN := hBase.nonneg hx
  have ht1 : t ≤ 1 := htε.le.trans (hεp z⁻¹ hx).2
  obtain ⟨U,hU,hUB,hsmall,herror⟩ := hstep z hz hzsmall F hF hFb hFm G hG t ht htε j hkj hjk hinput hnear hmetric
  have hbase' : A.WeightedBound 1 2 (Base z⁻¹) F := by
    intro i l hl x _
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hbase i l (by omega) x
  have hsum := A.weightedBound_add hF (hG.sub hF) zero_le_one hbase' hnear
  change A.WeightedBound 1 2 (Base z⁻¹+(z^4/D)/4) (F+(G-F)) at hsum
  have heG : F+(G-F) = G := by abel
  rw [heG] at hsum
  have hρ1 : (z^4/D)/4 ≤ 1 := by
    have hz1 := hzsmall.trans hz₀1
    have hz4 : z^4 ≤ 1 := pow_le_one₀ hz.le hz1
    have hd0 : 0 < D := zero_lt_one.trans_le hD
    have hh : z^4/D ≤ 1 := (div_le_one hd0).mpr (hz4.trans hD)
    linarith
  have hGbase : A.WeightedBound 1 2 (Base z⁻¹+1) G :=
    fun i => (hsum i).mono_const (by linarith)
  have hbaseline : A.ShiftedBound 2 0 t (Base z⁻¹+1) G := by
    intro i l hl x
    have hl2 : l ≤ 2 := by omega
    have hh := hGbase i l hl2 x (mem_univ x)
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,Nat.sub_eq_zero_of_le hl2,pow_zero] using hh
  refine ⟨U,hU,hsmall,?_,?_⟩
  · have hi0 := A.inputBound_mono_order hinput (show 0 ≤ 40*(k+1) from Nat.zero_le _)
    simpa only [show 1+Budget z⁻¹+Budget z⁻¹ = 1+2*Budget z⁻¹ by ring] using
      herror 0 (Budget z⁻¹) (hBudget.nonneg hx) hi0
  · intro m C hC hCm
    have hUB' : A.WeightedBound (t^(6/5 : ℝ)) (2+m)
        (P (m+2) z⁻¹*(t^(k : ℝ)*t^(6/5 : ℝ))) U := by
      simpa only [Nat.add_comm] using hUB (m+2)
    exact A.exact_scale_input_recurrence hG hU ht ht1 hk
      (by positivity) (hPg 0) (hPg m) ((hP (m+2)).nonneg hx) hC ((hL m).nonneg hx)
      (hBudget.nonneg hx) hbaseline hCm.1 hUB' (hgb 0) (hgb m) (herror m C hC hCm)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AnchoredPreparedCorrection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual adaptive data with a polynomially controlled initial threshold. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance anchoredPreparedFiberNormed_r37ce0b_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredPreparedFiberSpace_r37ce0b_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance anchoredPreparedDualAdd_r37ce0b_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredPreparedDualSmul_r37ce0b_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance anchoredPreparedSectionNormed_r37ce0b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredPreparedSectionSpace_r37ce0b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem anchored_prepared_correction_oai (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ Base Wish : ℝ → ℝ, HasPolynomialBound Base → HasPolynomialBound Wish →
    ∃ Budget EpsInv : ℝ → ℝ, HasPolynomialBound Budget ∧ HasPolynomialBound EpsInv ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
      A.ShiftedBound 2 0 1 (Base z⁻¹) F →
      ∃ p : PreparedCorrection (⟨A,houter⟩ : CorrectionGeometry g F),
        p.a = a ∧ p.ρ = z^4/D ∧ p.budget = Budget z⁻¹ ∧
        Wish z⁻¹ < p.budget/4 ∧ (p.ε 0)⁻¹ ≤ EpsInv z⁻¹ := by
  classical
  obtain ⟨z₀,a,D,hz₀,hz₀1,ha,hD,hall⟩ := A.anchored_input_step g houter R c B b hc hB hb
  refine ⟨z₀,a,D,hz₀,hz₀1,ha,hD,?_⟩
  intro Base Wish hBase hWish
  obtain ⟨A₀,hA₀,hsteps⟩ := hall Base hBase
  let Budget := fun x => 4*(A₀ x+Wish x+1)
  have hBudget : HasPolynomialBound Budget := (polynomialBound_const (by norm_num : (0:ℝ) ≤ 4)).mul
    ((hA₀.add hWish).add (polynomialBound_const zero_le_one))
  have hgap (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Budget x-A₀ x := by
    have hA := hA₀.nonneg hx
    have hW := hWish.nonneg hx
    dsimp [Budget] <;> linarith
  have hBp (x : ℝ) (hx : 1 ≤ x) : 0 < Budget x := by
    have hA := hA₀.nonneg hx
    have hW := hWish.nonneg hx
    dsimp [Budget] <;> linarith
  have horders (k : ℕ) := hsteps Budget hBudget (correctionOrder k) (by unfold correctionOrder; omega)
  choose ε L N hε hL hN hεp hstep using horders
  let η := fun k x => ExactCorrection.correctionBudgetThreshold (A₀ x) (Budget x) a
    (N k (correctionInputOrder k) x) (L k x)
  have hpres (k : ℕ) (x : ℝ) (hx : 1 ≤ x) :=
    ExactCorrection.correctionBudgetThreshold_spec (A := A₀ x) (B := Budget x)
      (N := N k (correctionInputOrder k) x) (L := L k x) (by linarith [hgap x hx]) ha
  have hη (k : ℕ) : HasPolynomialBound (fun x => (η k x)⁻¹) :=
    ExactCorrection.correctionBudgetThreshold_inverse_polynomial A₀ Budget
      (N k (correctionInputOrder k)) (L k) a ha hBudget (hN k _) (hL k) hgap
  let EpsInv := fun x => (min (ε 0 x) (η 0 x))⁻¹
  have hEpsInv : HasPolynomialBound EpsInv := ExactCorrection.polynomial_inverse_min
    (hε 0) (hη 0) (fun x hx => (hεp 0 x hx).1) (fun x hx => (hpres 0 x hx).1)
  refine ⟨Budget,EpsInv,hBudget,hEpsInv,?_⟩
  intro z hz hzsmall F hF hFb hFm hbase
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  let p : PreparedCorrection (⟨A,houter⟩ : CorrectionGeometry g F) := {
    a := a
    ρ := z^4/D
    baseline := A₀ z⁻¹
    budget := Budget z⁻¹
    a_pos := ha
    ρ_pos := div_pos (pow_pos hz 4) (zero_lt_one.trans_le hD)
    baseline_nonneg := hA₀.nonneg hx
    budget_pos := hBp z⁻¹ hx
    baseline_lt := by
      have hw := hWish.nonneg hx
      dsimp [Budget]; linarith
    ε := fun k => min (ε k z⁻¹) (η k z⁻¹)
    L := fun k => L k z⁻¹
    N := fun k m => N k m z⁻¹
    ε_pos := fun k => lt_min (hεp k z⁻¹ hx).1 (hpres k z⁻¹ hx).1
    ε_le_one := fun k => (min_le_left _ _).trans (hεp k z⁻¹ hx).2
    L_nonneg := fun k => (hL k).nonneg hx
    N_nonneg := fun k m => (hN k m).nonneg hx
    preserve := by
      intro k t ht htε
      exact (hpres k z⁻¹ hx).2.2 t ht (htε.trans_le (min_le_right _ _))
    step := by
      intro k G hG t ht htε j hj hj' hin hnear hmetric
      exact hstep k z hz hzsmall F hF hFb hFm hbase G hG t ht
        (htε.trans_le (min_le_left _ _)) j hj hj' hin hnear hmetric
  }
  refine ⟨p,rfl,rfl,rfl,?_,le_rfl⟩
  change Wish z⁻¹ < Budget z⁻¹/4
  have hA := hA₀.nonneg hx
  dsimp [Budget] <;> linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_prepared_correction_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_prepared_correction_oai.{u_1}
