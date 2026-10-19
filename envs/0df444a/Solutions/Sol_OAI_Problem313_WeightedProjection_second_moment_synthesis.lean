-- Prove2me | solution 1 for OAI.Problem313.WeightedProjection.second_moment_synthesis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:14:00.937433+00:00
-- url     : https://prove2.me/submissions/2712b698-4a5d-4cdf-ace3-034edae23955

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/ProjectionIdentities.lean:L53-L71
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.WeightedProjection.second_moment_synthesis. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_WeightedProjection_coefficient_synthesis

-- ---- from OAI.Combinatorics.SharpThreshold.ProjectionIdentities ----
namespace OAI

universe u v

noncomputable section

namespace Problem313.WeightedProjection

open scoped BigOperators

variable {ι : Type u} {X : Type v} [Fintype X]

/-- Pairing a function with a finite spectral expansion pairs its coefficients. -/
theorem inner_synthesis (w : X → ℝ) (basis : ι → X → ℝ)
    (f : X → ℝ) (L : Finset ι) (c : ι → ℝ) :
    (∑ x, w x * f x * synthesis basis L c x) =
      ∑ i ∈ L, c i * coefficient w basis f i := by
  simp only [synthesis, coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- The squared norm of a finite orthonormal expansion is its coefficient energy. -/
theorem second_moment_synthesis [DecidableEq ι]
    (w : X → ℝ) (basis : ι → X → ℝ)
    (horth : ∀ i j, (∑ x, w x * basis i x * basis j x) = if i = j then 1 else 0)
    (L : Finset ι) (c : ι → ℝ) :
    (∑ x, w x * (synthesis basis L c x) ^ 2) = ∑ i ∈ L, (c i) ^ 2 := by
  have hid := inner_synthesis w basis (synthesis basis L c) L c
  simp only [coefficient_synthesis w basis horth] at hid
  calc
    (∑ x, w x * (synthesis basis L c x) ^ 2) =
        ∑ x, w x * synthesis basis L c x * synthesis basis L c x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ i ∈ L, c i * (if i ∈ L then c i else 0) := hid
    _ = ∑ i ∈ L, (c i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi, pow_two]

end Problem313.WeightedProjection

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.WeightedProjection
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem313.WeightedProjection.second_moment_synthesis.{u,v} := @_root_.OAI.Problem313.WeightedProjection.second_moment_synthesis.{u,v}
