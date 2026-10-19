-- Prove2me | solution 1 for OAI.Problem313.weighted_holder_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:19:37.284338+00:00
-- url     : https://prove2.me/submissions/add31323-04e0-49e2-99dd-c10d8ee16814

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/ProjectionNorm.lean:L11-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.weighted_holder_four_thirds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities

-- ---- from OAI.Combinatorics.SharpThreshold.ProjectionNorm ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313

/-- Weighted finite Hölder inequality with conjugate exponents `4/3` and `4`.
Weights need not be normalized. -/
theorem weighted_holder_four_thirds {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * v i * u i| ≤
      (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        (∑ i, w i * u i ^ 4) ^ (1 / 4 : ℝ) := by
  classical
  have hpq : Real.HolderConjugate (4 / 3 : ℝ) 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (f := fun i => w i ^ (3 / 4 : ℝ) * |v i|)
    (g := fun i => w i ^ (1 / 4 : ℝ) * |u i|) hpq
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
  have hleft : (∑ i, (w i ^ (3 / 4 : ℝ) * |v i|) *
      (w i ^ (1 / 4 : ℝ) * |u i|)) = ∑ i, w i * |v i| * |u i| := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (w i ^ (3 / 4 : ℝ) * w i ^ (1 / 4 : ℝ)) * |v i| * |u i| := by ring
      _ = w i * |v i| * |u i| := by
        rw [← Real.rpow_add' (hw i) (by norm_num : (3 / 4 : ℝ) + 1 / 4 ≠ 0)]
        norm_num
  have hfirst : (∑ i, (w i ^ (3 / 4 : ℝ) * |v i|) ^ (4 / 3 : ℝ)) =
      ∑ i, w i * |v i| ^ (4 / 3 : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg _),
      ← Real.rpow_mul (hw i)]
    norm_num
  have hsecond : (∑ i, (w i ^ (1 / 4 : ℝ) * |u i|) ^ (4 : ℝ)) =
      ∑ i, w i * u i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg _),
      ← Real.rpow_mul (hw i)]
    have habs : |u i| ^ (4 : ℕ) = u i ^ 4 := by
      rcases le_total 0 (u i) with hi | hi
      · rw [abs_of_nonneg hi]
      · rw [abs_of_nonpos hi]
        ring
    norm_num [Real.rpow_natCast, habs]
  rw [hleft, hfirst, hsecond] at h
  norm_num at h
  refine (Finset.abs_sum_le_sum_abs (fun i => w i * v i * u i) Finset.univ).trans ?_
  simpa only [abs_mul, abs_of_nonneg (hw _)] using h

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.weighted_holder_four_thirds.{u} := @_root_.OAI.Problem313.weighted_holder_four_thirds.{u}
