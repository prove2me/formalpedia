-- Prove2me | solution 1 for OAI.Problem313.weighted_projection_noise_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:22:45.81616+00:00
-- url     : https://prove2.me/submissions/c5758bab-372d-46ca-8749-6ca1a5806518

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/ProjectionNorm.lean:L129-L149
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.weighted_projection_noise_bound. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_projection_moment_bound
import Theorems.Thm_OAI_Problem313_weighted_holder_four_thirds

-- ---- from OAI.Combinatorics.SharpThreshold.ProjectionNorm ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313

/-- A low-degree fourth-moment bound implies the dual projection estimate.
The hypothesis `hproj` is the usual orthogonal-projection identity
`⟨v,u⟩ = ⟨u,u⟩`; this formulation avoids choosing a normalized dual vector. -/
theorem weighted_projection_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (A : ℝ) (hA : 0 ≤ A)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤ A ^ 4 * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      A ^ 2 * (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
  have hM : 0 ≤ ∑ i, w i * u i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hV : 0 ≤ ∑ i, w i * |v i| ^ (4 / 3 : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  have hH : 0 ≤ ∑ i, w i * u i ^ 4 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (by positivity)
  apply projection_moment_bound hM hV hH hA _ hfour
  have h := weighted_holder_four_thirds w v u hw
  simpa only [hproj, abs_of_nonneg hM] using h

/-- Dual projection estimate for functions taking their values in `{-1,0,1}`,
as Boolean coordinate differences do. -/
theorem weighted_projection_pivotal_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤ A ^ 4 * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      A ^ 2 * (∑ i, if v i ≠ 0 then w i else 0) ^ (3 / 2 : ℝ) := by
  classical
  have hnorm : (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) =
      ∑ i, if v i ≠ 0 then w i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rcases hv i with hi | hi | hi <;> simp [hi]
  simpa only [hnorm] using weighted_projection_bound w v u hw A hA hproj hfour

/-- The exponent form used for low-degree projections of Boolean derivatives. -/
theorem weighted_projection_noise_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (ρ d : ℝ) (hρ : 0 ≤ ρ)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤
      ρ ^ (-4 * d) * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      ρ ^ (-2 * d) * (∑ i, if v i ≠ 0 then w i else 0) ^ (3 / 2 : ℝ) := by
  have hfourpow : (ρ ^ (-d)) ^ (4 : ℕ) = ρ ^ (-4 * d) := by
    rw [← Real.rpow_mul_natCast hρ]
    congr 1
    ring
  have htwopow : (ρ ^ (-d)) ^ (2 : ℕ) = ρ ^ (-2 * d) := by
    rw [← Real.rpow_mul_natCast hρ]
    congr 1
    ring
  have h := weighted_projection_pivotal_bound w v u hw hv (ρ ^ (-d))
    (Real.rpow_nonneg hρ _) hproj (by simpa only [hfourpow] using hfour)
  simpa only [htwopow] using h

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.weighted_projection_noise_bound.{u} := @_root_.OAI.Problem313.weighted_projection_noise_bound.{u}
