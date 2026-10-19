-- Prove2me | solution 1 for OAI.Problem313.WeightedProjection.coefficient_synthesis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:12:18.163984+00:00
-- url     : https://prove2.me/submissions/31d46df6-c30b-4e3c-82dc-59d9695bddfe

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/ProjectionIdentities.lean:L34-L51
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.WeightedProjection.coefficient_synthesis. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.ProjectionIdentities ----
namespace OAI

universe u v

noncomputable section

namespace Problem313.WeightedProjection

open scoped BigOperators

variable {ι : Type u} {X : Type v} [Fintype X]

/-- Orthonormality computes the coefficient of a finite spectral expansion. -/
theorem coefficient_synthesis [DecidableEq ι]
    (w : X → ℝ) (basis : ι → X → ℝ)
    (horth : ∀ i j, (∑ x, w x * basis i x * basis j x) = if i = j then 1 else 0)
    (L : Finset ι) (c : ι → ℝ) (i : ι) :
    coefficient w basis (synthesis basis L c) i = if i ∈ L then c i else 0 := by
  unfold coefficient synthesis
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (j : ι) :
      (∑ x, w x * (c j * basis j x) * basis i x) =
        c j * (if j = i then 1 else 0) := by
    rw [← horth j i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  simp only [hterm]
  simp

end Problem313.WeightedProjection

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.WeightedProjection
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem313.WeightedProjection.coefficient_synthesis.{u,v} := @_root_.OAI.Problem313.WeightedProjection.coefficient_synthesis.{u,v}
