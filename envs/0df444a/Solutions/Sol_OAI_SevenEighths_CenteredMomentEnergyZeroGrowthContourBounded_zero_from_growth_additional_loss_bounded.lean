-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:16:25.795323+00:00
-- url     : https://prove2.me/submissions/fe6fd47c-3cfa-412f-bab9-172d223ec364

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyReferenceDeletionEnergy_original_energy_weighted_deletion
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroGrowthReflection_live_deleted_reflection
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroRetainedError_natural_original_error_mass

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

end EisensteinSchwartzPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert (preTransparency := .instances) hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

theorem radial_weight_lattice_bound (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  let t := M⁻¹
  have ht : 0 < t := inv_pos.mpr hMp
  have ht1 : t ≤ 1 := (inv_le_one₀ hMp).mpr hM
  let B := 4 * (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (z : O) : ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      B * ((1 + t * ‖eisEmbedding z‖ ^ 2) ^ 2)⁻¹ := by
    have hq : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2, 0)) (k := 2) (n := 0) le_rfl le_rfl W (‖eisEmbedding z‖ ^ 2 / M)
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    change (1 + ‖eisEmbedding z‖ ^ 2 / M) ^ 2 * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ B at hh
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  have hb := hs.tsum_le_tsum hp ((scaled_eisenstein_cauchy_summable t ht).mul_left B)
  rw [tsum_mul_left] at hb
  have hsmall := scaled_eisenstein_cauchy_small t ht ht1
  have hmul := mul_le_mul_of_nonneg_left hb ht.le
  have hcontrol := mul_le_mul_of_nonneg_left hsmall hB
  have hfinal : t * (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W := by
    unfold diagonalControl
    dsimp [B] at hcontrol hmul
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hfinal hMp.le
  simpa only [t, ← mul_assoc, mul_inv_cancel₀ hMp.ne', one_mul, mul_comm] using hh

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.InverseContour
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem logPullbackCLM_apply (a b : ℝ) (W : SchwartzMap ℝ ℂ) (u : ℝ) :
    logPullbackCLM a b W u = logCutoff a b u • W (patchedExp a b u) := by
  rw [logPullbackCLM, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply
    ((logCutoff a b).hasCompactSupport.hasTemperateGrowth (logCutoff a b).contDiff)]
  rfl

theorem logCutoff_eq_one_of_source (a b : ℝ) (ha : 0 < a) (u : ℝ)
    (hu : Real.exp u ∈ Set.Icc a b) : logCutoff a b u = 1 := by
  apply (logCutoff a b).one_of_mem_closedBall
  have hl := Real.log_le_log ha hu.1
  have hr := Real.log_le_log (Real.exp_pos u) hu.2
  simp only [Real.log_exp] at hl hr
  change dist u 0 ≤ logRadius a b
  rw [Real.dist_eq, sub_zero]
  apply abs_le.mpr
  constructor <;> dsimp [logRadius] <;>
    linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem patchedExp_eq_exp_of_cutoff_ne_zero (a b u : ℝ) (hu : logCutoff a b u ≠ 0) :
    patchedExp a b u = Real.exp u := by
  have hmem : u ∈ Function.support (logCutoff a b) := hu
  rw [(logCutoff a b).support_eq] at hmem
  have heta : logOuterCutoff a b u = 1 := by
    apply (logOuterCutoff a b).one_of_mem_closedBall
    change dist u 0 ≤ logRadius a b + 1
    change dist u 0 < logRadius a b + 1 at hmem
    exact le_of_lt hmem
  simp [patchedExp, expCorrection, heta]

theorem logPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    logPullbackCLM a b W u = W (Real.exp u) := by
  rw [logPullbackCLM_apply]
  by_cases hW : W (Real.exp u) = 0
  · by_cases hcut : logCutoff a b u = 0
    · simp [hcut, hW]
    · rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u hcut, hW, smul_zero]
  · have hcut := logCutoff_eq_one_of_source a b ha u (hsupp hW)
    rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u (by rw [hcut]; norm_num), hcut, one_smul]

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

lemma derivativeSeminormSum_nonneg (g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [logPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end JointLogSeparation

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Counting
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCounting
open CenteredMomentPrimary
open QuadraticInitialBound

theorem norm_tsum_ideal_ball (f : Ideal O → ℂ) (H M : ℝ)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hzero : f ⊥ = 0)
    (hbound : ∀ I, ‖f I‖ ≤ M)
    (hsupport : ∀ I, f I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ H) :
    ‖∑' I : Ideal O, f I‖ ≤ 128 * M * H := by
  classical
  have hfinite : (Function.support f).Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).subset
    intro I hI
    exact_mod_cast (hsupport I hI).trans (Nat.le_ceil H)
  let S := hfinite.toFinset
  have hmem (I : Ideal O) : I ∈ S ↔ f I ≠ 0 := hfinite.mem_toFinset
  have htsum : (∑' I : Ideal O, f I) = ∑ I ∈ S, f I := by
    exact tsum_eq_sum (fun I hI => not_ne_iff.mp (mt (hmem I).mpr hI))
  rw [htsum]
  by_cases hS : S.Nonempty
  · obtain ⟨I, hI⟩ := hS
    have hI0 : I ≠ ⊥ := by intro h; exact (hmem I).mp hI (h ▸ hzero)
    have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hI0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH1 : 1 ≤ H := hn.trans (hsupport I ((hmem I).mp hI))
    have hcount := DescentFiberCost.finite_ideal_count_real S H hH1
      (fun J hJ hz => (hmem J).mp hJ (hz ▸ hzero))
      (fun J hJ => hsupport J ((hmem J).mp hJ))
    calc
      _ ≤ ∑ I ∈ S, ‖f I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ S, M := Finset.sum_le_sum (fun I _ => hbound I)
      _ = (S.card : ℝ) * M := by simp
      _ ≤ (128 * H) * M := mul_le_mul_of_nonneg_right hcount hM
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty, norm_zero]
    positivity

end SevenEighths.CenteredMomentCounting
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Height
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentHeight
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open QuadraticInitialBound CenteredMomentLattice
open CenteredMomentPrimary CenteredMomentTwist

lemma normalized_height_le (t : ℝ) : ‖t / (2 * Real.pi)‖ ≤ ‖t‖ := by
  rw [norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])

end SevenEighths.CenteredMomentHeight
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAbsoluteEnergy
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem radial_norm_summable (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖Φ (‖eisEmbedding z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

theorem radial_weight_lattice_bound_all (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O, ‖Φ (‖eisEmbedding z‖^2/K)‖) ≤ diagonalControl Φ*max 1 K := by
  by_cases hlarge : 1≤K
  · simpa only [max_eq_right hlarge] using radial_weight_lattice_bound Φ K hlarge
  have hsmall : K≤1 := (not_le.mp hlarge).le
  let B := 4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hB : 0≤B := by dsimp [B]; positivity
  have hp (z : O) : ‖Φ (‖eisEmbedding z‖^2/K)‖ ≤
      B*((1+1*‖eisEmbedding z‖^2)^2)⁻¹ := by
    have hq : 0≤‖eisEmbedding z‖^2/K := div_nonneg (sq_nonneg _) hK.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl Φ (‖eisEmbedding z‖^2/K)
    simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hq] at hh
    norm_num only [show (2:ℝ)^2=4 by norm_num] at hh
    change (1+‖eisEmbedding z‖^2/K)^2*‖Φ (‖eisEmbedding z‖^2/K)‖≤B at hh
    have hq' : ‖eisEmbedding z‖^2≤‖eisEmbedding z‖^2/K := by
      apply (le_div_iff₀ hK).mpr
      exact mul_le_of_le_one_right (sq_nonneg _) hsmall
    have hden : (1+1*‖eisEmbedding z‖^2)^2≤(1+‖eisEmbedding z‖^2/K)^2 := by
      simp only [one_mul]
      gcongr
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hh
  have hb := (radial_norm_summable Φ K hK).tsum_le_tsum hp
    ((scaled_eisenstein_cauchy_summable 1 (by norm_num)).mul_left B)
  rw [tsum_mul_left] at hb
  have hc := scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
  simp only [one_mul] at hc hb
  have ht := hb.trans (mul_le_mul_of_nonneg_left hc hB)
  rw [max_eq_left hsmall,mul_one]
  dsimp only [B] at ht
  unfold diagonalControl
  nlinarith

end SevenEighths.CenteredMomentAbsoluteEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Sobolev
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace trunc

theorem nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

end trunc
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open FourierBridge JointLogSeparation CompletedHeight CenteredMomentLattice
open EisensteinSchwartzPoisson

theorem frequencyTwist_source_control (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (g : 𝓢(ℝ, ℂ)) (t : ℝ),
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤
          C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g * (1 + ‖t‖)^n := by
  let T := S.biUnion fun z => (Finset.range (z.2+1)).image fun i => (z.1,i)
  let c : ℕ × ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*(z.2+1)
  let C := 1 + ∑ z ∈ S, c z
  have hc (z) : 0 ≤ c z := by dsimp [c]; positivity
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z)
    dsimp [C]; linarith
  refine ⟨S.sup Prod.snd,T,C,hC,?_⟩
  intro g t
  have hder (z) (hz : z ∈ S) : derivativeSeminormSum g z.1 z.2 ≤
      (z.2+1:ℝ) * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := by
    calc
      _ ≤ ∑ i ∈ Finset.range (z.2+1), T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := by
        apply Finset.sum_le_sum
        intro i hi
        apply Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) (i := (z.1,i))
        exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
      _ = _ := by simp
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z ≤ C := by
    have := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]; linarith
  calc
    _ ≤ ((2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2) *
        (1+‖t‖)^z.2 := frequencyTwist_seminorm_polynomial g t z.1 z.2
    _ ≤ (c z * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g) *
        (1+‖t‖)^z.2 := by
      dsimp only [c]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hder z hz)
          (show 0 ≤ (2:ℝ)^z.2*(1+2*Real.pi)^z.2 by positivity))
        (show 0 ≤ (1+‖t‖)^z.2 by positivity)).trans_eq (by ring)
    _ ≤ (C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g) *
        (1+‖t‖)^(S.sup Prod.snd) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hzC (apply_nonneg _ _)
      · exact pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)
      · positivity
      · positivity

theorem normPowerProfile_source_control (a b : ℝ) (ha : 0 < a)
    (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ, ℂ), ∀ hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b,
      ∀ t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩ := schwartzCLM_finite_seminorm_control (fixedLogReturnCLM a b ha) S
  obtain ⟨n,S₂,C₂,hC₂,h₂⟩ := frequencyTwist_source_control S₁
  obtain ⟨T,C₃,hC₃,h₃⟩ := schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM a b) S₂
  refine ⟨n,T,C₁*C₂*C₃,by positivity,?_⟩
  intro W hs t
  have heq : CubicReflectionKernel.logSchwartz W a b ha hs (W.smooth ⊤) =
      CubicReflectionKernel.logPullbackCLM a b W := by
    ext u
    rw [CubicReflectionKernel.logSchwartz_apply,
      CubicReflectionKernel.logPullbackCLM_eq_actual a b ha W hs]
  have ht : (1+‖t/(2*Real.pi)‖)^n ≤ (1+‖t‖)^n := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  unfold normPowerProfile uniformTwistedSchwartz
  rw [heq]
  calc
    _ ≤ C₁ * S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (CubicReflectionKernel.logPullbackCLM a b W) (t/(2*Real.pi))) := h₁ _
    _ ≤ C₁ * (C₂ * (C₃ * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (1+‖t‖)^n) := by
      apply mul_le_mul_of_nonneg_left _ hC₁.le
      exact (h₂ _ _).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (h₃ W) hC₂.le) ht (by positivity) (by positivity))
    _ = _ := by ring
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentCommonMaskEnergy
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentLattice
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

lemma heightCoefficient_norm (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoefficient β t I‖=‖β I‖ := by
  have hn : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [heightCoefficient,norm_mul]
  have hp : ‖(I.absNorm:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hn (Complex.I*t)
  rw [hp,mul_one]

end SevenEighths.CenteredMomentCommonMaskEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.State
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

namespace NaturalState
variable {Z Bmask bΦ:ℝ}
lemma width_nonneg (s:NaturalState Z Bmask bΦ):0≤ s.width :=
  add_nonneg s.row_nonneg s.character_nonneg

lemma radical_bound (s:NaturalState Z Bmask bΦ):
    (s.puncture.radical.absNorm:ℝ)≤Z^Bmask :=by
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=s.puncture))))
end NaturalState

end SevenEighths.CenteredMomentEnergyState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.Bands
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentEnergyBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O"=>HeckeFamily.O

lemma length_nonneg (Z X:ℝ)(hZ:1<Z):0≤length Z X:=
  Real.logb_nonneg hZ (le_max_left _ _)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyBands

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

lemma radialEnergy_effective (r:Radial)(f:O→ℂ):
    radialEnergy f (effectiveRadial r).keep r.profile r.scale=
      radialEnergy f r.keep r.profile r.scale:=by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hz:r.profile (‖eisEmbedding z‖^2/r.scale)=0 <;>
    simp [effectiveRadial,hk,hz]

end SevenEighths.CenteredMomentEnergyReferenceState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalReflectionErrorMass
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentOriginalReflectionErrorMass
open HeckeFamily HeckeDyadic HeckePrimeAnnular HeckePrimeRay
open CenteredMomentCounting CenteredMomentAbsoluteEnergy CenteredMomentComparisonReflection
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma annularWeight_zero_norm (W : ℝ→ℂ) (D freq : ℝ) (hD : 0<D)
    (I : Ideal O) (hI : I≠0) :
    ‖annularWeight W D 0 freq I‖=‖W ((I.absNorm:ℝ)/D)‖ := by
  have hn : 0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hn hD)]
  simp only [Complex.neg_re,shift_re,neg_zero,Real.rpow_zero,mul_one]

lemma actual_coefficient_norm (χ : Character) (W : ℝ→ℂ) (D freq B : ℝ)
    (hD : 0<D) (hB : 0≤B) (hW : ∀x,‖W x‖≤B) (I : Ideal O) :
    ‖idealCoeff χ I*annularWeight W D 0 freq I‖≤B := by
  by_cases hI:I=0
  · subst I
    simpa only [idealCoeff_zero,zero_mul,norm_zero] using hB
  rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
  exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

lemma actual_coefficient_support (χ : Character) (W : ℝ→ℂ) (b D freq : ℝ)
    (hD : 0<D) (hs : Function.support W⊆Set.Iic b) (I : Ideal O)
    (hne : idealCoeff χ I*annularWeight W D 0 freq I≠0) :
    (I.absNorm:ℝ)≤ max 1 b*D := by
  have hw : W ((I.absNorm:ℝ)/D)≠0:=by
    intro hz
    exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
  exact ((div_le_iff₀ hD).mp (hs hw)).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le)

lemma polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ false W D 0 freq=
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,idealCoeff χ I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he:(∑'I:NonzeroIdeal,idealCoeff χ I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,idealCoeff χ I*annularWeight W D 0 freq I:=by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>idealCoeff χ I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [idealCoeff_zero,zero_mul])
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,
    annularWeight,mul_assoc] using he

lemma normalized_linear_bound (D c : ℝ) (hD : 0<D) (v : ℂ)
    (hv : ‖v‖≤ c*D) : ‖(D:ℂ)^(-(1/2:ℂ))*v‖≤ c*Real.sqrt D := by
  rw [inverse_half_power D hD.le,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg D)]
  have hs:Real.sqrt D≠0:=(Real.sqrt_pos.mpr hD).ne'
  have hd:D/Real.sqrt D=Real.sqrt D:=by
    apply (div_eq_iff hs).mpr
    simpa only [pow_two] using (Real.sq_sqrt hD.le).symm
  calc
    _ ≤ (Real.sqrt D)⁻¹*(c*D):=mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Real.sqrt_nonneg D))
    _ = c*(D/Real.sqrt D):=by ring
    _ = _:=by rw [hd]

theorem plain_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ false W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>idealCoeff χ I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change idealCoeff χ (0:Ideal O)*_ = 0
      rw [idealCoeff_zero,zero_mul])
    (actual_coefficient_norm χ W D freq B hD hB hW)
    (actual_coefficient_support χ W b D freq hD hs)
  convert (preTransparency := .instances) hh using 1; ring

lemma errorConstant_pos {α : Type*} (F : Finset α) (bshort Bshort : ℝ) (b B : α→ℝ) :
    0<errorConstant F bshort Bshort b B := by
  apply mul_pos
  · positivity
  · exact Finset.prod_pos (fun j _=>zero_lt_one.trans_le (le_max_left _ _))

end SevenEighths.CenteredMomentOriginalReflectionErrorMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceAllocatedErrorMass
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentCounting CenteredMomentAbsoluteEnergy CenteredMomentComparisonReflection
open CenteredMomentOriginalReflectionErrorMass
local notation "O" => HeckeFamily.O

theorem naturalSlot_ideal_bound (χ : Character) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (b M P : ℝ) (hM : 0≤M) (hP : 0<P)
    (hβ : ∀I∈pool,‖β I‖≤M)
    (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    ‖naturalSlot χ pool β P‖≤(128*max 1 b*M)*Real.sqrt P := by
  let f : Ideal O→ℂ:=fun I=>if I∈pool then idealCoeff χ I*β I else 0
  have hf0 : f 0=0:=by simp only [f,idealCoeff_zero,zero_mul,ite_self]
  have hf : ∀I,‖f I‖≤M := by
    intro I
    by_cases hi : I∈pool
    · simp only [f,if_pos hi,norm_mul]
      exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hβ I hi) (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    · simpa only [f,if_neg hi,norm_zero] using hM
  have hsup : ∀I,f I≠0 → (I.absNorm:ℝ)≤ max 1 b*P := by
    intro I hi
    have hm : I∈pool:=by by_contra hn;exact hi (by simp only [f,if_neg hn])
    have hb : β I≠0:=by intro hz;exact hi (by simp only [f,if_pos hm,hz,mul_zero])
    exact (hs I hm hb).trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hP.le)
  have he : (∑'I:Ideal O,f I)=∑I∈pool,idealCoeff χ I*β I := by
    rw [tsum_eq_sum (s:=pool) (fun I hi=>by simp only [f,if_neg hi])]
    exact Finset.sum_congr rfl (fun I hi=>by simp only [f,if_pos hi])
  have hh:=norm_tsum_ideal_ball f (max 1 b*P) M (by positivity) hM hf0 hf hsup
  rw [he] at hh
  unfold naturalSlot
  rw [←inverse_half_power P hP.le]
  apply normalized_linear_bound P _ hP
  convert (preTransparency := .instances) hh using 1 ; ring

theorem radialEnergy_le_absolute_mass (R : O→ℂ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hPhi : ∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hs : Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)) :
    CenteredMomentOriginalRadialComparison.radialEnergy R keep Φ K≤
      ∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2 := by
  let f:=fun z:O=>if keep z then ‖R z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hn (z:O):0≤f z:=by dsimp only [f];split_ifs;exact mul_nonneg (sq_nonneg _) (hPhi z);exact le_rfl
  have hb (z:O):f z≤‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2 := by
    dsimp only [f]
    split_ifs
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Complex.re_le_norm (Φ (‖eisEmbedding z‖^2/K))) (sq_nonneg ‖R z‖)
    · positivity
  exact (Summable.of_nonneg_of_le hn hb hs).tsum_le_tsum hb hs

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneousError
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceHomogeneousError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalReflectionErrorMass CenteredMomentNaturalFixedRaySource
open CenteredMomentOriginalRadialComparison
open CenteredMomentCounting CenteredMomentAbsoluteEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

theorem natural_remaining_homogeneous_bound {α : Type*} (F T : Finset α) (hT : T⊆F)
    (W : ℝ→ℂ) (bshort Bshort : ℝ) (b M : α→ℝ)
    (hBshort : 0≤Bshort) (hM : ∀j∈F,0≤M j)
    (hW : ∀x,‖W x‖≤Bshort) (hsW : Function.support W⊆Set.Iic bshort)
    (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ)
    (P : α→ℝ) (X omega : ℝ) (hX : 0<X) (hP : ∀j∈T,0<P j)
    (hβ : ∀j∈T,∀I∈pool j,‖β j I‖≤M j)
    (hs : ∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) :
    ‖polynomial χ false W X 0 omega*∏j∈T,naturalSlot χ (pool j) (β j) (P j)‖^2≤
      errorConstant F bshort 1 b M*Bshort^2*X*∏j∈T,P j := by
  have hshort:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ W bshort Bshort X omega hBshort hX hW hsW) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hshort
  have hj (j:α) (hj:j∈T):
      ‖naturalSlot χ (pool j) (β j) (P j)‖^2≤(128*max 1 (b j)*M j)^2*P j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (naturalSlot_ideal_bound χ (pool j) (β j) (b j) (M j) (P j)
        (hM j (hT hj)) (hP j hj) (hβ j hj) (hs j hj)) 2
    simpa only [mul_pow,Real.sq_sqrt (hP j hj).le] using hh
  have hc₀ : (128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M := by
    have hp : (∏j∈T,(128*max 1 (b j)*M j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      (Finset.prod_le_prod (fun j _=>sq_nonneg _) (fun j _=>le_max_right 1 _)).trans
        (Finset.prod_le_prod_of_subset_of_one_le hT (fun j _=>by positivity)
          (fun j _ _=>le_max_left 1 _))
    unfold errorConstant
    simp only [mul_one]
    exact mul_le_mul (by linarith [sq_nonneg (128*max 1 bshort)]) hp
      (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M*Bshort^2 := by
    calc
      _=((128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*Bshort^2:=by ring
      _≤_:=mul_le_mul_of_nonneg_right hc₀ (sq_nonneg Bshort)
  calc
    _ = ‖polynomial χ false W X 0 omega‖^2*∏j∈T,‖naturalSlot χ (pool j) (β j) (P j)‖^2 := by
      simp only [norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*X)*∏j∈T,(128*max 1 (b j)*M j)^2*P j :=
      mul_le_mul hshort (Finset.prod_le_prod (fun j _=>sq_nonneg _) hj)
        (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*(X*∏j∈T,P j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ (errorConstant F bshort 1 b M*Bshort^2)*(X*∏j∈T,P j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hP j hj).le)))
    _ = _ := by ring

theorem natural_reference_error_homogeneous {α:Type*}(F:Finset α)(bshort:ℝ)(b M:α→ℝ)
    (hM:∀i∈F,0≤M i):
    ∃C:ℝ,0<C ∧ ∀(T:Finset α),T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:O→Character)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) →
      (∀i∈T,∀I∈pool i,Prime I) →
      (∀i∈T,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈T,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  refine ⟨errorConstant F bshort 1 b M,errorConstant_pos _ _ _ _ _,?_⟩
  intro T hT W hsW χ pool β P t X K Φ keep hX hK hP hp hβ hs hΦ
  let A:=(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W
  have hA:0≤A:=apply_nonneg _ _
  have hWA:∀x,‖W x‖≤A:=SchwartzMap.norm_le_seminorm ℝ W
  let R:=fun z:O=>polynomial (χ z) false W X 0 t *
    ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)
  let V:=errorConstant F bshort 1 b M*A^2*X*∏i∈T,P i
  have hV:0≤V:=by
    dsimp only [V]
    exact mul_nonneg (mul_nonneg (mul_nonneg (errorConstant_pos F bshort 1 b M).le
      (sq_nonneg A)) hX.le) (Finset.prod_nonneg (fun i hi=>(hP i hi).le))
  have hr(z:O):‖R z‖^2≤V:=by
    have hh:=natural_remaining_homogeneous_bound F T hT W bshort A b M hA hM hWA hsW
      (χ z) pool (fun i=>heightCoefficient (β i) t) P X t hX hP
      (fun i hi I hI=>by rw [heightCoefficient_norm _ _ _ (hp i hi I hI).ne_zero];exact hβ i hi I hI)
      (fun i hi I hI hn=>hs i hi I hI (left_ne_zero_of_mul hn))
    exact hh
  have hsum:Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2):=
    Summable.of_nonneg_of_le (fun z=>mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
  apply (radialEnergy_le_absolute_mass R keep Φ K hΦ hsum).trans
  calc
    _≤∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*V:=hsum.tsum_le_tsum
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
    _=(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*V:=tsum_mul_right
    _≤(diagonalControl Φ*max 1 K)*V:=mul_le_mul_of_nonneg_right
      (radial_weight_lattice_bound_all Φ K hK) hV
    _=_:=by dsimp [V,A];ring

end SevenEighths.CenteredMomentEnergyReferenceHomogeneousError

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChildProfiles
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyProfiles
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

theorem independent_profile_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t₁ t₂:ℝ,
      (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S≤
        C*(sourceControl T W₁*sourceControl T W₂)*(1+‖t₁‖+‖t₂‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hc⟩:=normPowerProfile_source_control a b ha S
  refine ⟨n,T,C ^2,sq_pos_of_pos hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t₁ t₂
  have h₁:=hc W₁ hs₁ t₁
  have h₂:=hc W₂ hs₂ t₂
  have hp₁:(1+‖t₁‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₂]) n
  have hp₂:(1+‖t₂‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₁]) n
  have h₁':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)≤C*sourceControl T W₁*(1+‖t₁‖+‖t₂‖)^n:=
    h₁.trans (mul_le_mul_of_nonneg_left hp₁ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  have h₂':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)≤C*sourceControl T W₂*(1+‖t₁‖+‖t₂‖)^n:=
    h₂.trans (mul_le_mul_of_nonneg_left hp₂ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  simp only [Profiles.control,independentProfiles,show (1:Fin 2)≠0 by decide,ite_true,ite_false]
  apply (mul_le_mul h₁' h₂' (apply_nonneg _ _)
    (mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg _ _)) (by positivity))).trans_eq
  rw [show (1+‖t₁‖+‖t₂‖)^(2*n)=((1+‖t₁‖+‖t₂‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.CenteredMomentEnergyReferenceChildProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
local notation "O"=>HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

end SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLiveClippingDefect
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentRetainedEnergy
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_support_witness (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X : ℝ) (h : rowTwistedSum η m A z W t X ≠ 0) :
    ∃ I : Ideal O, I ≠ 0 ∧ W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold rowTwistedSum
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · subst I
        rw [idealCoeff_zero, zero_mul, zero_mul, zero_mul]
      · rw [hn I hI, mul_zero]
    _ = 0 := tsum_zero

theorem rowTwistedSum_support_scale (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X b : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b)
    (h : rowTwistedSum η m A z W t X ≠ 0) : 1 ≤ b * X := by
  obtain ⟨I, hI, hW⟩ := rowTwistedSum_support_witness η m A z W t X h
  have hn : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hn.trans ((div_le_iff₀ hX).mp (hs hW))

variable {ι : Type*} [Fintype ι]

theorem positiveSlotRow_support_scales (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (h : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  have hp := left_ne_zero_of_mul (right_ne_zero_of_mul h)
  exact ⟨rowTwistedSum_support_scale η m A z W₁ t X₁ b hX₁ hs₁
      (left_ne_zero_of_mul hp),
    rowTwistedSum_support_scale η m A z W₂ t X₂ b hX₂ hs₂
      (right_ne_zero_of_mul hp)⟩

theorem positiveSlotRow_profiles_scales (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (h : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  exact positiveSlotRow_support_scales η m A z _ _ S β P t X₁ X₂ b hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) h

theorem energy_support_witness (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : CenteredMomentInductionEnergy.energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≠ 0) :
    ∃ z : O, keep z ∧ positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold CenteredMomentInductionEnergy.energy
  calc
    _ = ∑' _z : O, (0 : ℝ) := by
      apply tsum_congr
      intro z
      by_cases hk : keep z
      · simp only [if_pos hk, hn z hk, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      · simp only [if_neg hk]
    _ = 0 := tsum_zero

open CenteredMomentEnergyReferenceState

end SevenEighths.CenteredMomentEnergyLiveClippingDefect

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceDivisors
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyReferenceState
local notation "O"=>HeckeFamily.O

lemma divisor_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    1≤((∏P∈D,P).absNorm:ℝ) ∧ ((∏P∈D,P).absNorm:ℝ)≤Z^Bmask:=by
  have hs:D⊆IdealMobiusDivisorSum.primeSupport s.puncture:=Finset.mem_powerset.mp hD
  have hn:=IdealMobiusDivisorSum.support_product_ne_zero hs
  have hp:0<(∏P∈D,P).absNorm:=Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  refine ⟨by exact_mod_cast hp,?_⟩
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (IdealMobiusDivisorSum.support_product_dvd s.puncture_ne_zero hs))

end SevenEighths.CenteredMomentEnergyReferenceDivisors

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma control_mono {S T:Finset (ℕ×ℕ)}(h:S⊆T)(W:𝓢(ℝ,ℂ)):
    sourceControl S W≤ sourceControl T W:=Seminorm.le_def.mp (Finset.sup_mono h) W

theorem reference_envelopes (a b:ℝ)(ha:0<a)
    (S T Slong:Finset (ℕ×ℕ))(degree n nlong:ℕ)(Cref Dchild Dref:ℝ)
    (hCr:0<Cref)(hDc:0<Dchild)(hDr:0<Dref):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t height:ℝ,0≤height →
      let E:=C*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J;
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*(1+|t|+height)^degree≤E ∧
      Cref*Dchild*(sourceControl Slong W₂)^2*(sourceControl T W₁)^2*
        (1+‖t‖)^(2*nlong)*(1+|t|+height)^(degree+2*n)≤E ∧
      Dref*(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
        (1+‖t‖)^(2*nlong)≤E:=by
  obtain ⟨na,Ta,Ca,hCa,hprof⟩:=independent_profile_control a b ha S
  let U:=((Ta∪T)∪Slong)∪{(0,0)}
  let J:=degree+4*na+2*n+2*nlong
  let C:=1+Ca^2*2^(4*na)+Cref*Dchild+Dref
  have hC:0<C:=by dsimp only [C];positivity
  refine ⟨J,U,C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only
  let H:=1+|t|+height
  let A:=sourceControl U W₁*sourceControl U W₂
  have hH:1≤H:=by dsimp only [H];linarith [abs_nonneg t]
  have hH0:0≤H:=zero_le_one.trans hH
  have hA:0≤A:=mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have haU:Ta⊆U:=by intro x hx;simp [U,hx]
  have hTU:T⊆U:=by intro x hx;simp [U,hx]
  have hlU:Slong⊆U:=by intro x hx;simp [U,hx]
  have hzU:(0,0)∈U:=by simp [U]
  have hz:(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁≤ sourceControl U W₁:=
    Seminorm.le_def.mp (Finset.le_sup hzU) W₁
  have hp:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S≤Ca*A*(2*H)^(2*na):=by
    apply (hprof W₁ W₂ hs₁ hs₂ t t).trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ hCa.le
      exact mul_le_mul (control_mono haU W₁) (control_mono haU W₂)
        (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    · apply pow_le_pow_left₀ (by positivity)
      dsimp only [H]
      simp only [Real.norm_eq_abs]
      linarith [abs_nonneg t]
    · positivity
    · positivity
  have hd:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S^2*H^degree≤
      (Ca^2*2^(4*na))*A^2*H^J:=by
    have hsq:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
    have hmul:=mul_le_mul_of_nonneg_right hsq (pow_nonneg hH0 degree)
    have hid:(Ca*A*(2*H)^(2*na))^2*H^degree=
        (Ca^2*2^(4*na))*A^2*H^(degree+4*na):=by
      rw [mul_pow,mul_pow,←pow_mul,show (2*na)*2=4*na by omega,mul_pow,pow_add]
      ring_nf
    rw [hid] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (by positivity))
  have hm:(sourceControl Slong W₂)^2*(sourceControl T W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul (control_mono hTU W₁) (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have he:(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (apply_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul hz (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hheightpow:(1+‖t‖)^(2*nlong)≤H^(2*nlong):=by
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [H]
    simp only [Real.norm_eq_abs]
    linarith
  have hcm: Cref*Dchild≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hce:Dref≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hcd:Ca^2*2^(4*na)≤C:=by dsimp only [C];nlinarith
  refine ⟨hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (sq_nonneg A)) (pow_nonneg hH0 J)),?_,?_⟩
  · calc
      _=(Cref*Dchild)*((sourceControl Slong W₂)^2*(sourceControl T W₁)^2)*
          ((1+‖t‖)^(2*nlong)*H^(degree+2*n)):=by ring
      _≤C*A^2*(H^(2*nlong)*H^(degree+2*n)):=by gcongr
      _≤C*A^2*H^J:=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (sq_nonneg A))
        rw [←pow_add]
        exact pow_le_pow_right₀ hH (by dsimp only [J];omega)
  · calc
      _=Dref*((sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2)*(1+‖t‖)^(2*nlong):=by ring
      _≤C*A^2*H^(2*nlong):=by gcongr
      _≤C*A^2*H^J:=mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (mul_nonneg hC.le (sq_nonneg A))

end SevenEighths.CenteredMomentEnergyReferenceProfileBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceScalarBounds
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceScalarBounds
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource

lemma radical_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(d:ℝ)(hd:0≤d):
    (s.puncture.radical.absNorm:ℝ)^d≤Z^(Bmask*d):=by
  have hh:=Real.rpow_le_rpow (Nat.cast_nonneg _) s.radical_bound hd
  simpa only [←Real.rpow_mul (zero_lt_one.trans_le s.base_ge_one).le] using hh

lemma conductor_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap d:ℝ)(hs:s.width≤Mcap)(hd:0≤d):
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))^d*Z^(Mcap*d):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hM:0≤Mcap:=s.width_nonneg.trans hs
  have hz:1≤Z^Mcap:=Real.one_le_rpow s.base_ge_one hM
  have hc:1≤ max 1 ((fixedConductorFactor:ℝ)*bΦ):=le_max_left _ _
  have hbase:max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))*Z^Mcap:=by
    apply max_le
    · nlinarith
    · apply le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZ.le _))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hs)
        (zero_le_one.trans hc)
  have hh:=Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase hd
  rw [Real.mul_rpow (zero_le_one.trans hc) (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le] at hh
  exact hh

lemma log_interval (Z L d:ℝ)(hZ:1≤Z)(hL:0≤L)(hd:0<d):
    1+2*(L*Real.log Z)≤(1+2*L/d)*Z^d:=by
  have hlog:=Real.log_le_rpow_div (zero_le_one.trans hZ) hd
  have hone:=Real.one_le_rpow hZ hd.le
  have hh:=mul_le_mul_of_nonneg_left hlog (show 0≤2*L by positivity)
  calc
    _≤Z^d+2*L*(Z^d/d):=by nlinarith
    _=(1+2*L/d)*Z^d:=by ring

end SevenEighths.CenteredMomentEnergyReferenceScalarBounds

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroReflectionSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReflectionSupport
open HeckeFamily Filter CenteredMomentNaturalPrimitive EisensteinSchwartzPoisson
open CenteredMomentReflectionMass CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentReflectionDeletion CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O" => HeckeFamily.O

lemma deleted_short_length (Z b Xshort Xlong Nshort : ℝ)
    (hZ : 1<Z)(_hb : 0<b)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hN : 1≤Nshort)(hsupport : 1≤b*Xlong) :
    length Z (Xshort/Nshort)≤Real.logb Z Xlong+Real.logb Z (max 1 b) := by
  have hx : 0<Xlong := hshort.trans_le hlong
  have hn : 0<Nshort := zero_lt_one.trans_le hN
  have hd : Xshort/Nshort≤Xlong := (div_le_self hshort.le hN).trans hlong
  have hlog := Real.logb_le_logb_of_le hZ (div_pos hshort hn) hd
  have hprod : 1≤ max 1 b*Xlong := hsupport.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.le)
  have hzero := Real.logb_nonneg hZ hprod
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left 1 b))) hx.ne'] at hzero
  rw [length_eq_max_log Z _ hZ (div_pos hshort hn)]
  apply max_le
  · linarith
  · exact hlog.trans (le_add_of_nonneg_right (Real.logb_nonneg hZ (le_max_left _ _)))

theorem eventually_endpoint_defect (b epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b)≤epsilon := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (max 1 b)/epsilon))] with Z hZ hz
  refine ⟨hZ,?_⟩
  rw [Real.logb]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have hh := (div_le_iff₀ hepsilon).mp hz
  nlinarith

end SevenEighths.CenteredMomentEnergyZeroReflectionSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroReferenceError
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceError
open HeckeFamily ConcreteTraceCRT HeckeDyadic QuadraticInitialBound
open CenteredMomentCommonMaskEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyReferenceHomogeneousError
local notation "O"=>HeckeFamily.O

theorem short_energy_bound (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),Function.support (W:ℝ→ℂ)⊆Set.Iic b →
      ∀(χ:O→Character)(t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),0<X →0<K →
      (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*diagonalControl Φ*max 1 K*X:=by
  obtain ⟨C,hC,h⟩:=natural_reference_error_homogeneous (∅:Finset (Fin 0)) b
    (fun _=>0) (fun _=>0) (by simp)
  refine ⟨C,hC,?_⟩
  intro W hs χ t X K Φ keep hX hK hΦ
  have hh:=h ∅ (Finset.Subset.refl _) W hs χ (fun _=>∅) (fun _ _=>0)
    (fun _=>1) t X K Φ keep hX hK (by simp) (by simp) (by simp) (by simp) hΦ
  simpa only [Finset.prod_empty,mul_one] using hh

end SevenEighths.CenteredMomentEnergyZeroReferenceError

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthBounds
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounds
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyZeroReferenceError CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

lemma actual_window_cap (Z b Bmask bΦ Mcap defect xi L Xlong:ℝ)
    (hZ:1<Z)(hb:0<b)(hx:0<Xlong)(hsupport:1≤b*Xlong)
    (hdefect:Real.logb Z (max 1 b)≤defect)
    (hL:Mcap+Bmask+defect+xi≤L)(hL0:0≤L)
    (s:NaturalState Z Bmask bΦ)(hs:s.width≤Mcap)
    (Dlong:Finset (Ideal O))(hDl:Dlong∈(CompletedGauss.primeSupport s.puncture).powerset):
    max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)≤L:=by
  obtain ⟨hn,hncap⟩:=divisor_norm s Dlong hDl
  have hnp:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hnp).mpr hncap
  have hlow:=deleted_short_length Z b Xlong Xlong 1 hZ hb hx le_rfl le_rfl hsupport
  simp only [div_one] at hlow
  have hnon:=CenteredMomentEnergyBands.length_nonneg Z Xlong hZ
  apply max_le hL0
  rw [Real.logb_div hx.ne' hnp.ne']
  linarith

theorem actual_deleted_short_mass (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ L:ℝ)(s:NaturalState Z Bmask bΦ)
      (W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Iic b→
      ∀t X:ℝ,0<X→X≤Z^L→
      ∀D:Finset (Ideal O),D∈(CompletedGauss.primeSupport s.puncture).powerset→
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W
        (X/((∏P∈D,P).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L:=by
  obtain ⟨C,hC,hbound⟩:=short_energy_bound b
  refine ⟨C,hC,?_⟩
  intro Z Bmask bΦ L s W hW t X hX hcap D hD
  obtain ⟨hn,_⟩:=divisor_norm s D hD
  have hnp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hh:=hbound W hW (naturalCharacter s.character) t
    (X/((∏P∈D,P).absNorm:ℝ)) s.radial.scale s.radial.profile
    (effectiveState s).radial.keep (div_pos hX hnp) s.radial.scale_pos s.radial.nonneg
  apply hh.trans
  apply mul_le_mul_of_nonneg_left ((div_le_self hX.le hn).trans hcap)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
    (diagonalControl_nonneg _)) (le_max_of_le_left zero_le_one)

end SevenEighths.CenteredMomentEnergyZeroGrowthBounds

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthBounded
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounded
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyZeroGrowthReflection CenteredMomentEnergyZeroGrowthBounds

theorem live_deleted_bounded (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
    Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤ s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(L*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L :=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=live_deleted_reflection
    a b bΦ epsilon xi defect saving Lreflect ha hlo hhi hbΦ hepsilon hxi hdefect B hB S
  obtain ⟨Cshort,hCs,hshortmass⟩:=actual_deleted_short_mass b
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cshort,hC,mul_pos hD hCs,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive
  have hL0:0≤L:=by linarith [s.width_nonneg]
  have hw:=actual_window_cap Z b Bmask bΦ Mcap defect xi L Xlong hZ.1 (by linarith)
    (hshort.trans_le hlong) hsupport hendpoint.2 hL hL0 s hs Dlong hDl
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hwindow:1+2*(max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)
      ≤1+2*(L*Real.log Z):=by nlinarith
  have hmass:=hshortmass Z Bmask bΦ L s Wshort (fun x hx=>(hsShort hx).2)
    t Xshort hshort hshortcap Dshort hDs
  have hd:=diagonalControl_nonneg s.radial.profile
  have hN:0≤((∏P∈Dlong,P).absNorm:ℝ):=Nat.cast_nonneg _
  have hZ0:0<Z:=zero_lt_one.trans hZ.1
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hwindow (by positivity)
    · positivity
  · have he:=mul_le_mul_of_nonneg_left hmass
      (show 0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving) by positivity)
    convert (preTransparency := .instances) he using 1 ; ring

end SevenEighths.CenteredMomentEnergyZeroGrowthBounded

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthOriginal
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthOriginal
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthBounded CenteredMomentEnergyZeroRetainedError
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentInductionEnergy CenteredMomentEnergyLiveClippingDefect CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

lemma swapProfiles_control {a b:ℝ}(p:Profiles a b)(U:Finset (ℕ×ℕ)):
    (swapProfiles p).control U=p.control U:=by
  simp [swapProfiles,Profiles.control,mul_comm]

lemma plainEnergy_swap {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (p:Profiles a b)(t X₁ X₂:ℝ):
    s.plainEnergy (swapProfiles p) t X₂ X₁=s.plainEnergy p t X₁ X₂:=by
  unfold NaturalState.plainEnergy energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow s.character s.mask 1 z ((swapProfiles p).profile 0)
      ((swapProfiles p).profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      t X₂ X₁=positiveSlotRow s.character s.mask 1 z (p.profile 0) (p.profile 1)
      (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) t X₁ X₂:=by
    simp only [swapProfiles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    unfold positiveSlotRow
    rw [mul_comm X₂ X₁]
    ring
  rw [hh]

theorem original_from_growth (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
      Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
      s.plainEnergy p t X₁ X₂≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
          (s.puncture.radical.absNorm:ℝ)^epsilon*
          ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
            (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
           (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
            Z^(-2*saving)*max 1 s.radial.scale*Z^L):=by
  obtain ⟨n,T,Dchild,hDc,nlive,Slive,Clive,Dlive,hCl,hDl,hlive⟩:=
    live_deleted_bounded a b bΦ epsilon xi defect saving Lreflect
      ha hlo hhi hbΦ hepsilon hxi hdefect 2 (by norm_num) S
  obtain ⟨ndead,Sdead,Cdead,hCd,hdead⟩:=natural_original_error_mass
    a b bΦ epsilon xi saving ha (by linarith only [hlo, hhi]) hbΦ hepsilon hxi
  obtain ⟨Cweight,hCw,hweight⟩:=original_energy_weighted_deletion (α:=Fin 0)
    (fun _=>0) (fun _=>0) (fun _=>le_refl 0) epsilon hepsilon
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T (Slive∪Sdead)
    0 n (nlive+ndead) Clive Dchild (Dlive+Cdead) hCl hDc (by positivity)
  refine ⟨J,U,Cweight*Cprofile,by positivity,?_⟩
  filter_upwards [hlive,hdead] with Z hZ hZd
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect s hQ hs
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hL0:0≤L:=by linarith only [s.width_nonneg, hs, hBmask, hdefect, hxi, hL]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hd:=diagonalControl_nonneg s.radial.profile
  let Rcap:=max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)
  let Pmain:=Rcap^epsilon*(1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)
  let Perror:=Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*Z^L
  have hPm:0≤Pmain:=by dsimp only [Pmain,Rcap];positivity
  have hPe:0≤Perror:=by dsimp only [Perror,Rcap];positivity
  have hordered (p:Profiles a b)(t Xshort Xlong:ℝ)(hXs:0<Xshort)(horder:Xshort≤Xlong)
      (hcap:Xshort≤Z^L)(hsupport:1≤b*Xlong):
      s.plainEnergy p t Xshort Xlong≤
        Cweight*Cprofile*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
          (s.puncture.radical.absNorm:ℝ)^epsilon*(Pmain+Perror):=by
    have hXl:0<Xlong:=hXs.trans_le horder
    have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
    simp only [add_zero,zero_add,pow_zero,mul_one] at hp
    let A:=Cprofile*(p.control U)^2*(1+|t|)^J
    let E:=(K+1)*diagonalControl s.radial.profile*A
    have hA:0≤A:=by dsimp only [A];positivity
    have hE:0≤E:=by dsimp only [E];positivity
    have hSl:sourceControl Slive (p.profile 1)≤ sourceControl (Slive∪Sdead) (p.profile 1):=
      control_mono Finset.subset_union_left _
    have hSd:sourceControl Sdead (p.profile 1)≤ sourceControl (Slive∪Sdead) (p.profile 1):=
      control_mono Finset.subset_union_right _
    have hSl0:=sourceControl_nonneg Slive (p.profile 1)
    have hSd0:=sourceControl_nonneg Sdead (p.profile 1)
    have hheight:1≤1+‖t‖:=le_add_of_nonneg_right (norm_nonneg _)
    have hnL:(1+‖t‖)^(2*nlive)≤(1+‖t‖)^(2*(nlive+ndead)):=
      pow_le_pow_right₀ hheight (by omega)
    have hnD:(1+‖t‖)^(2*ndead)≤(1+‖t‖)^(2*(nlive+ndead)):=
      pow_le_pow_right₀ hheight (by omega)
    have hmain:Clive*(sourceControl Slive (p.profile 1))^2*(1+‖t‖)^(2*nlive)*
        (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*(1+|t|)^(2*n))≤E:=by
      have hh:Clive*Dchild*(sourceControl Slive (p.profile 1))^2*(sourceControl T (p.profile 0))^2*
          (1+‖t‖)^(2*nlive)*(1+|t|)^(2*n)≤A:=by
        apply le_trans _ hp.2.1
        gcongr
      have hh':=mul_le_mul_of_nonneg_left hh (mul_nonneg hK hd)
      have he:K*diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hd hA]
      apply le_trans _ he
      convert (preTransparency := .instances) hh' using 1; ring
    have herrLive:Dlive*(sourceControl Slive (p.profile 1))^2*(1+‖t‖)^(2*nlive)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
      have hh:Dlive*(sourceControl Slive (p.profile 1))^2*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*nlive)≤A:=by
        apply le_trans _ hp.2.2
        gcongr
        exact le_add_of_nonneg_right hCd.le
      have hh':=mul_le_mul_of_nonneg_left hh hd
      have he:diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hK (mul_nonneg hd hA)]
      apply le_trans _ he
      convert (preTransparency := .instances) hh' using 1; ring
    have herrDead:Cdead*(sourceControl Sdead (p.profile 1))^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*ndead)*
        diagonalControl s.radial.profile≤E:=by
      have hh:Cdead*(sourceControl Sdead (p.profile 1))^2*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*ndead)≤A:=by
        apply le_trans _ hp.2.2
        gcongr
        exact le_add_of_nonneg_left hDl.le
      have hh':=mul_le_mul_of_nonneg_left hh hd
      have he:diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hK (mul_nonneg hd hA)]
      apply le_trans _ he
      convert (preTransparency := .instances) hh' using 1; ring
    have hw:=hweight Z Bmask bΦ a b s (p.profile 0) (p.profile 1) ha (by linarith only [hlo, hhi])
      (p.support 0) (p.support 1) (fun _=>∅) (fun _ _=>0) (fun _=>1)
      t Xshort Xlong (E*(Pmain+Perror)) 1
    have hresult:s.plainEnergy p t Xshort Xlong≤
        Cweight*(s.puncture.radical.absNorm:ℝ)^epsilon*(E*(Pmain+Perror)):=by
      apply hw
      · simp
      · simp
      · simp
      · simp
      · exact hXs
      · exact hXl
      · exact mul_nonneg hE (add_nonneg hPm hPe)
      · norm_num
      · intro Ds hDs Dl hDl' I hI
        obtain ⟨hNs,_⟩:=divisor_norm s Ds hDs
        obtain ⟨hNl,_⟩:=divisor_norm s Dl hDl'
        have hpS:0<((∏P∈Ds,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
        have hpL:0<((∏P∈Dl,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
        have heffective (f:O→ℂ):radialEnergy f (effectiveState s).radial.keep
            s.radial.profile s.radial.scale=radialEnergy f s.radial.keep s.radial.profile s.radial.scale:=
          radialEnergy_effective s.radial f
        simp only [Finset.univ_eq_empty,Finset.empty_sdiff,Finset.prod_empty,mul_one,Real.rpow_one]
        rw [show (fun z:O=>polynomial (naturalCharacter s.character z) false (p.profile 0)
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) 0 t*
            polynomial (naturalCharacter s.character z) false (p.profile 1)
              (Xlong/((∏P∈Dl,P).absNorm:ℝ)) 0 t)=
            (fun z:O=>polynomial (naturalCharacter s.character z) false (p.profile 1)
              (Xlong/((∏P∈Dl,P).absNorm:ℝ)) 0 t*
            polynomial (naturalCharacter s.character z) false (p.profile 0)
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) 0 t) by funext z;exact mul_comm _ _]
        by_cases hl:0≤ s.width-Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ))+xi
        · have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
            s hQ hs (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
            t Xshort Xlong hXs horder hcap hsupport Ds Dl hDs hDl' hl
          have hb:=add_le_add
            (mul_le_mul_of_nonneg_right hmain (mul_nonneg hPm hpL.le))
            (mul_le_mul_of_nonneg_right herrLive hPe)
          have hc:E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+E*Perror≤
              E*(Pmain+Perror)*((∏P∈Dl,P).absNorm:ℝ):=by
            calc
              _ ≤ E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+(E*Perror)*((∏P∈Dl,P).absNorm:ℝ) :=
                add_le_add le_rfl (le_mul_of_one_le_right (mul_nonneg hE hPe) hNl)
              _ = _ := by ring
          apply hh.trans
          calc
            _ ≤ E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+E*Perror := by
              convert (preTransparency := .instances) hb using 1 <;> dsimp only [Pmain,Perror,Rcap] <;> ring
            _ ≤ _ := hc
        · have hfar:s.width+xi<Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ)):=by linarith only [hl]
          have hh:=hZd.2 Bmask s (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
            t t (Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ)))
            (Xshort/((∏P∈Ds,P).absNorm:ℝ)) (div_pos hXs hpS) hfar
          rw [Real.rpow_logb hz hZ.1.ne' (div_pos hXl hpL)] at hh
          rw [heffective]
          have hshortcap:Xshort/((∏P∈Ds,P).absNorm:ℝ)≤Z^L:=
            (div_le_self hXs.le hNs).trans hcap
          have hb:=mul_le_mul_of_nonneg_right herrDead
            (show 0≤Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) by positivity)
          have hc:E*(Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)))≤E*Perror:=by
            dsimp only [Perror]
            gcongr
          have hf:E*Perror≤E*(Pmain+Perror)*((∏P∈Dl,P).absNorm:ℝ):=by
            exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hPm) hE).trans
              (le_mul_of_one_le_right (mul_nonneg hE (add_nonneg hPm hPe)) hNl)
          apply hh.trans
          calc
            _ ≤ E*(Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
                (Xshort/((∏P∈Ds,P).absNorm:ℝ))) := by
              convert (preTransparency := .instances) hb using 1; dsimp only [Rcap,sourceControl]; ring
            _ ≤ E*Perror := hc
            _ ≤ _ := hf
    apply hresult.trans_eq
    dsimp only [E,A]
    ring
  intro p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  by_cases hzero:s.plainEnergy p t X₁ X₂=0
  · rw [hzero]
    positivity
  · obtain ⟨z,hz,hrow⟩:=energy_support_witness s.character s.mask 1 t
      (p.profile 0) (p.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ s.radial.keep s.radial.profile s.radial.scale hzero
    obtain ⟨hs₁,hs₂⟩:=positiveSlotRow_profiles_scales s.character s.mask 1 z p
      (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) t X₁ X₂ hX₁ hX₂ hrow
    by_cases horder:X₁≤X₂
    · exact hordered p t X₁ X₂ hX₁ horder hc₁ hs₂
    · have hh:=hordered (swapProfiles p) t X₂ X₁ hX₂ (le_of_not_ge horder) hc₂ hs₁
      simpa only [plainEnergy_swap,swapProfiles_control] using hh

end SevenEighths.CenteredMomentEnergyZeroGrowthOriginal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthReserve
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroGrowthReserve
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarBounds

theorem ledger_bound (Mcap Bmask bΦ L d loss defect xi saving ε:ℝ)
    (_hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+1)+loss+defect+xi≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+L≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBp:0<B:=by dsimp [B];positivity
  refine ⟨A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:max 1 s.radial.scale≤Z^s.width:=by
    apply max_le (Real.one_le_rpow hZ s.width_nonneg)
    rw [s.scale_eq]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    exact le_add_of_nonneg_right s.character_nonneg
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+loss+defect+xi)):=by gcongr
      _=A^d*B*Z^(s.width+(d*(Bmask+Mcap+1)+loss+defect+xi)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+loss+defect+xi)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herr:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
        Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+L)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add hreflect herr
    _=_:=by ring

end SevenEighths.CenteredMomentEnergyZeroGrowthReserve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthContourBounded
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalRowSource QuadraticInitialBound
local notation "O"=>HeckeFamily.O

private lemma ledger_loss_mono (Z d ell A B P w:ℝ)(hZ:1≤Z)(hd:0≤d)(hell:0≤ell)
    (hA:0≤A)(hB:0≤B)(hP:0≤P):
    P*(A*Z^(w+ell+d+d)+B)≤Z^ell*(P*(A*Z^(w+d+d+d)+B)):=by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hp:1≤Z^ell:=Real.one_le_rpow hZ hell
  have hm:Z^(w+ell+d+d)≤Z^ell*Z^(w+d+d+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _≤P*(A*(Z^ell*Z^(w+d+d+d))+Z^ell*B):=by
      apply mul_le_mul_of_nonneg_left _ hP
      exact add_le_add (mul_le_mul_of_nonneg_left hm hA)
        (le_mul_of_one_le_left hB hp)
    _=_:=by ring

theorem bounded_growth_reserve (ε Mcap Bmask bΦ Loriginal:ℝ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L saving C:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ 0<saving ∧ 0<C ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧ Loriginal≤L ∧
      Mcap+Bmask+d+d≤L ∧
      ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+d+d+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let d:=min 1 (ε/(8*(Bmask+Mcap+4)))
  let L:=max Loriginal (Mcap+Bmask+2*d)+1
  let saving:=L+Bmask*d+2*Mcap*d+1
  have hd:0<d:=lt_min (by norm_num) (by positivity)
  have hd1:d≤1:=min_le_left _ _
  have hdε:d*(Bmask+Mcap+4)≤ε/8:=by
    have hh: d≤ε/(8*(Bmask+Mcap+4)):=min_le_right _ _
    have he: d*(8*(Bmask+Mcap+4))≤ε:=
      (le_div_iff₀ (by positivity)).mp hh
    linarith
  have hL:0<L:=by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+2*d)]
  have hs:0<saving:=by dsimp [saving];positivity
  have hmain:d*(Bmask+Mcap+1)+d+d+d≤ε:=by linarith
  have herr:Bmask*d+Mcap*(2*d)-2*saving+L≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hbound⟩:=CenteredMomentEnergyZeroGrowthReserve.ledger_bound
    Mcap Bmask bΦ L d d d d saving ε hM hB hL.le hd hmain herr
  refine ⟨d,L,saving,C,hd,hd1,hL,hs,hC,rfl,?_,?_,hbound⟩
  · dsimp only [L];linarith [le_max_left Loriginal (Mcap+Bmask+2*d)]
  · dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+2*d)]

theorem zero_from_growth_additional_loss_bounded_oai (a b bΦ ε Mcap Bmask Loriginal:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ Loriginal≤L ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧
      L≤ max Loriginal (Mcap+Bmask+2)+1 ∧
      ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(ell:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ell→0≤K→
        ZeroGrowthAt Q a b bΦ Bmask L Mcap ell Z degree S K→
        ZeroAt Q a b bΦ Bmask Loriginal Mcap (ell+ε) Z J U (C*(K+1)):=by
  obtain ⟨d,L,saving,Cledger,hd,hd1,hL,hsaving,hCledger,hLexact,hLoriginal,hroom,hledger⟩:=
    bounded_growth_reserve
      ε Mcap Bmask bΦ Loriginal hε hM hB
  refine ⟨d,L,hd,hd1,hL,hLoriginal,hLexact,?_,?_⟩
  · rw [hLexact]
    gcongr
    linarith only [hd1]
  intro S
  obtain ⟨J,U,Csource,hCsource,hsource⟩:=
    CenteredMomentEnergyZeroGrowthOriginal.original_from_growth
      a b bΦ d d d saving L ha hlo hhi hbΦ hd hd hd S
  refine ⟨J,U,Csource*Cledger,mul_pos hCsource hCledger,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ell Q degree K hell hK hgrowth s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:Z^Loriginal≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLoriginal
  have hh:=hZ.2 Bmask L Mcap ell Q degree K hK hgrowth hB hroom
    (by linarith) s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale)
  let Rcap:=max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)
  let A:=Rcap^d*(1+2*(L*Real.log Z))
  let B:=Rcap^(2*d)*Z^(-2*saving)*max 1 s.radial.scale*Z^L
  let P:=(s.puncture.radical.absNorm:ℝ)^d
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hA:0≤A:=by dsimp [A,Rcap];positivity
  have hBb:0≤B:=by dsimp [B,Rcap];positivity
  have hP:0≤P:=by dsimp [P];positivity
  have hb:=ledger_loss_mono Z d ell A B P s.width hZ.1.le hd.le hell hA hBb hP
  have hl:=mul_le_mul_of_nonneg_left (hledger Z hZ.1.le s hs) (Real.rpow_nonneg hz.le ell)
  have htotal:P*(A*Z^(s.width+ell+d+d)+B)≤Cledger*Z^(s.width+(ell+ε)):=by
    apply hb.trans
    calc
      _≤Z^ell*(Cledger*Z^(s.width+ε)):=hl
      _=Cledger*(Z^ell*Z^(s.width+ε)):=by ring
      _=Cledger*Z^(s.width+(ell+ε)):=by rw [←Real.rpow_add hz];congr 2;ring
  have hfront:0≤Csource*(K+1)*diagonalControl s.radial.profile*
      (p.control U)^2*(1+|t|)^J:=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  calc
    _≤Csource*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
        (Cledger*Z^(s.width+(ell+ε))):=by
      apply hh.trans
      convert (preTransparency := .instances) mul_le_mul_of_nonneg_left htotal hfront using 1 ; dsimp only [P,A,B,Rcap] ; ring
    _=_:=by rw [Real.norm_eq_abs];ring

end SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded_oai := @OAI.SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded_oai
