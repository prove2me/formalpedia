-- Prove2me | solution 1 for GlobalTheory.FiniteCovolume.inv_keeps_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:12.788118+00:00
-- url     : https://prove2.me/submissions/9a8c933b-f075-49e0-8458-c7f8401e87be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOrthUpdateMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FiniteCovolume
theorem _root_.solution {r : ℕ} {J a : Matrix (Fin r) (Fin r) ℂ} (hJ : J.det ≠ 0)
    (ha : aᵀ * J * a.map (starRingEnd ℂ) = J) :
    (a⁻¹)ᵀ * J * (a⁻¹).map (starRingEnd ℂ) = J := by
  have hdet : IsUnit a.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
    rw [← ha, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
  have h2 : (a⁻¹)ᵀ * aᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have h3 : a.map (starRingEnd ℂ) * (a⁻¹).map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  calc (a⁻¹)ᵀ * J * (a⁻¹).map (starRingEnd ℂ)
      = (a⁻¹)ᵀ * (aᵀ * J * a.map (starRingEnd ℂ)) * (a⁻¹).map (starRingEnd ℂ) := by rw [ha]
    _ = ((a⁻¹)ᵀ * aᵀ) * J * (a.map (starRingEnd ℂ) * (a⁻¹).map (starRingEnd ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]
end GlobalTheory.FiniteCovolume
