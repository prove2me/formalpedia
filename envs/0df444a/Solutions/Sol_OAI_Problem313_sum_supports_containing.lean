-- Prove2me | solution 1 for OAI.Problem313.sum_supports_containing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:30:25.554872+00:00
-- url     : https://prove2.me/submissions/dfd760de-812b-447e-8748-9901078c87b0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/DirichletEnergy.lean:L12-L28
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.sum_supports_containing. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.DirichletEnergy ----
namespace OAI

universe u

noncomputable section
namespace Problem313
open Finset
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Delete a distinguished coordinate to reindex all supports containing it. -/
theorem sum_supports_containing (i : ι) (a : Finset ι → ℝ) :
    (∑ S : Finset ι, if i ∈ S then a S else 0) =
      ∑ S : Finset ι, if i ∉ S then a (insert i S) else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun S _ => S.erase i) (fun S _ => insert i S) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp
  · intro S hS
    simp
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2
  · intro S hS
    exact Finset.erase_insert (Finset.mem_filter.mp hS).2
  · intro S hS
    rw [Finset.insert_erase (Finset.mem_filter.mp hS).2]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open Finset


theorem solution.{u} : type_of% @_root_.OAI.Problem313.sum_supports_containing.{u} := @_root_.OAI.Problem313.sum_supports_containing.{u}
