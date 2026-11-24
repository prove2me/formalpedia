-- Prove2me | solution 1 for GlobalTheory.integral_intervalIntegral_mul_right_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:20.932529+00:00
-- url     : https://prove2.me/submissions/b976dbbd-6069-4fdb-9e03-e12c0000b401

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RightTranslationCurveSqLeAndIntegralDerivEqZeroA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsMulRightInvariant] [IsProbabilityMeasure μ]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    (c : ℝ → K) (hc : Continuous c) (g : K → E) (hg : Continuous g) :
    ∫ x, (∫ t in (0:ℝ)..1, g (x * c t)) ∂μ = ∫ x, g x ∂μ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hg).isBounded.exists_norm_le
  have hcont : Continuous (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t)) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Eventually.of_forall fun p => ?_)
    exact hC _ ⟨_, Set.mem_univ _, rfl⟩
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [integral_integral_swap hint]
  simp_rw [integral_mul_right_eq_self g]
  simp
end GlobalTheory
