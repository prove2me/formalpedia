-- Prove2me | solution 1 for OAI.Problem313.lowDegree_fourth_of_noise
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:17:48.11793+00:00
-- url     : https://prove2.me/submissions/107dad66-d9bf-47b9-b8b6-1745bbc65879

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegreeL4.lean:L35-L71
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.lowDegree_fourth_of_noise. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_inverse_noise_energy_le

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegreeL4 ----
namespace OAI

universe u v

noncomputable section

namespace Problem313

open scoped BigOperators

/-- Spectral inversion turns a diagonal-noise `L² → L⁴` estimate into an
`L⁴` estimate for a low-degree expansion.  This version is independent of
any particular construction of the orthonormal basis. -/
theorem lowDegree_fourth_of_noise
    {ι : Type u} {X : Type v} [Fintype ι] [Fintype X]
    (degree : ι → ℕ) (basis : ι → X → ℝ) (weight : X → ℝ)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : ι → ℝ,
      (∑ x, weight x * (∑ i, rho ^ (degree i : ℝ) * a i * basis i x) ^ 4) ≤
        (∑ i, (a i) ^ 2) ^ 2)
    (c : ι → ℝ) (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ x, weight x * (∑ i, c i * basis i x) ^ 4) ≤
      rho ^ (-4 * k) * (∑ i, (c i) ^ 2) ^ 2 := by
  let a : ι → ℝ := fun i => rho ^ (-(degree i : ℝ)) * c i
  have hinv (i : ι) : rho ^ (degree i : ℝ) * a i = c i := by
    dsimp [a]
    rw [← mul_assoc, ← Real.rpow_add hrho]
    simp
  have hnoise' :
      (∑ x, weight x * (∑ i, c i * basis i x) ^ 4) ≤
        (∑ i, (a i) ^ 2) ^ 2 := by
    simpa only [hinv] using hnoise a
  have henergy : (∑ i, (a i) ^ 2) ≤
      rho ^ (-2 * k) * ∑ i, (c i) ^ 2 :=
    inverse_noise_energy_le degree c rho k hrho hrho1 hdegree
  have hnonneg : 0 ≤ ∑ i, (a i) ^ 2 := by positivity
  have hsq : (∑ i, (a i) ^ 2) ^ 2 ≤
      (rho ^ (-2 * k) * ∑ i, (c i) ^ 2) ^ 2 := by
    exact pow_le_pow_left₀ hnonneg henergy 2
  have hscale : (rho ^ (-2 * k) * ∑ i, (c i) ^ 2) ^ 2 =
      rho ^ (-4 * k) * (∑ i, (c i) ^ 2) ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_mul hrho.le]
    congr 1
    ring
  exact hnoise'.trans (hsq.trans_eq hscale)

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem313.lowDegree_fourth_of_noise.{u,v} := @_root_.OAI.Problem313.lowDegree_fourth_of_noise.{u,v}
