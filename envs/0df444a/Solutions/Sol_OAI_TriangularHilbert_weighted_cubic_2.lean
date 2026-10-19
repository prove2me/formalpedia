-- Prove2me | solution 2 for OAI.TriangularHilbert.weighted_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:22:08.799048+00:00
-- url     : https://prove2.me/submissions/13170c98-d4b5-485b-b676-b9a95fd2152b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/WeightedCubic.lean:L61-L92
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.weighted_cubic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump

-- ---- from OAI.Analysis.TriangularHilbert.WeightedCubic ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert
open scoped BigOperators

lemma sum_sq_le_sum_mul_of_nonneg {ι : Type uι} (s : Finset ι) (x y z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) (hz : ∀ i ∈ s, 0 ≤ z i)
    (he : ∀ i ∈ s, x i ^ 2 = y i * z i) :
    (∑ i ∈ s, x i)^2 ≤ (∑ i ∈ s, y i)*(∑ i ∈ s, z i) := by
  have hp i (hi : i ∈ s) : Real.sqrt (y i) * Real.sqrt (z i) = x i := by
    rw [← Real.sqrt_mul (hy i hi),← he i hi,Real.sqrt_sq (hx i hi)]
  have hh := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => Real.sqrt (y i)) (fun i => Real.sqrt (z i))
  have hys : (∑ i ∈ s, (Real.sqrt (y i))^2) = ∑ i ∈ s, y i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hy i hi))
  have hzs : (∑ i ∈ s, (Real.sqrt (z i))^2) = ∑ i ∈ s, z i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hz i hi))
  rw [hys,hzs] at hh
  have he' : (∑ i ∈ s, Real.sqrt (y i) * Real.sqrt (z i)) = ∑ i ∈ s, x i :=
    Finset.sum_congr rfl hp
  rw [he'] at hh
  have hq := sq_le_sq₀ (Finset.sum_nonneg hx) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr hh
  simpa only [mul_pow,Real.sq_sqrt (Finset.sum_nonneg hy),Real.sq_sqrt (Finset.sum_nonneg hz)] using hq

lemma weighted_cubic {ι : Type uι} (s : Finset ι) (a w : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, a i^2*w i) * Real.sqrt (∑ i ∈ s, a i^2*w i) ≤
      (∑ i ∈ s, a i^3*w i) * Real.sqrt (∑ i ∈ s, w i) := by
  let T := ∑ i ∈ s, a i^2*w i
  let B := ∑ i ∈ s, a i^3*w i
  let L := ∑ i ∈ s, a i*w i
  let W := ∑ i ∈ s, w i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i hi => mul_nonneg (sq_nonneg _) (hw i hi))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (pow_nonneg (ha i hi) _) (hw i hi))
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (hw i hi))
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hTL : T^2 ≤ B*L := sum_sq_le_sum_mul_of_nonneg s _ _ _
    (fun i hi => mul_nonneg (sq_nonneg _) (hw i hi))
    (fun i hi => mul_nonneg (pow_nonneg (ha i hi) _) (hw i hi))
    (fun i hi => mul_nonneg (ha i hi) (hw i hi)) (fun i _ => by ring)
  have hLW : L^2 ≤ T*W := sum_sq_le_sum_mul_of_nonneg s _ _ _
    (fun i hi => mul_nonneg (ha i hi) (hw i hi))
    (fun i hi => mul_nonneg (sq_nonneg _) (hw i hi)) hw (fun i _ => by ring)
  change T * Real.sqrt T ≤ B * Real.sqrt W
  by_cases ht : T = 0
  · simpa only [ht,zero_mul] using mul_nonneg hB (Real.sqrt_nonneg W)
  have htpos : 0 < T := hT.lt_of_ne' ht
  have hq := mul_le_mul hTL hTL (sq_nonneg T) (mul_nonneg hB hL)
  have hh := mul_le_mul_of_nonneg_left hLW (sq_nonneg B)
  have hc : T^3 ≤ B^2 * W := by
    by_contra! hc
    have hp := mul_pos htpos (sub_pos.mpr hc)
    nlinarith
  apply (sq_le_sq₀ (mul_nonneg hT (Real.sqrt_nonneg T)) (mul_nonneg hB (Real.sqrt_nonneg W))).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt hT,Real.sq_sqrt hW]
  nlinarith [hc]
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open scoped BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.weighted_cubic.{uι} := @_root_.OAI.TriangularHilbert.weighted_cubic.{uι}
