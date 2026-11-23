-- Prove2me | solution 1 for GlobalTheory.SW.NearPrim.exists_reduce
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:22.115692+00:00
-- url     : https://prove2.me/submissions/6ed5472c-bc04-468d-ba72-4f2aed0b9cae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.NearPrim
namespace GlobalTheory.SW.NearPrim
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, ∀ x : E, ∃ y : E, IsIntegral ℤ y ∧ ‖canonicalEmbedding E (x - y)‖ ≤ C := by
  classical
  let b := integralBasis E
  refine ⟨∑ i, ‖canonicalEmbedding E (b i)‖, fun x => ⟨∑ i, ⌊b.repr x i⌋ • b i, ?_, ?_⟩⟩
  · refine IsIntegral.sum _ fun i _ => IsIntegral.zsmul ?_ _
    simp only [b, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  · have h : x - ∑ i, ⌊b.repr x i⌋ • b i = ∑ i, (Int.fract (b.repr x i) : ℚ) • b i := by
      conv_lhs => rw [← b.sum_repr x]
      rw [b.sum_repr x]
      nth_rewrite 1 [← b.sum_repr x]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
    rw [h, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_rat_smul, norm_smul]
    have h0 := Int.fract_nonneg (b.repr x i)
    have h1 := (Int.fract_lt_one (b.repr x i)).le
    have : ‖(Int.fract (b.repr x i) : ℚ)‖ ≤ 1 := by
      rw [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast h0)]
      exact_mod_cast h1
    exact mul_le_of_le_one_left (norm_nonneg _) this
end GlobalTheory.SW.NearPrim
