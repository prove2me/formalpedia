-- Prove2me | solution 1 for OAI.Problem313.block_boundary_mem_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:22:10.754252+00:00
-- url     : https://prove2.me/submissions/a7a050f5-ecf7-44f0-a39e-c517703a8ee5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockOrbits.lean:L112-L128
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.block_boundary_mem_orbit. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.BlockOrbits ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Boundary edges with the same exterior endpoint are in one block orbit. -/
theorem block_boundary_mem_orbit {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} {u w : Fin n} (hu : u ∈ B) (hw : w ∉ B)
    (he : e.val = {u, w}) (v : B) :
    blockBoundaryEdge w hw v ∈ blockEdgeOrbit B e := by
  classical
  refine mem_blockEdgeOrbit.mpr ⟨Equiv.swap u v.val, ?_, ?_⟩
  · intro z hz
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hzu
      exact hz (hzu ▸ hu)
    · intro hzv
      exact hz (hzv ▸ v.property)
  · apply Subtype.ext
    have hwu : w ≠ u := by intro h; exact hw (h ▸ hu)
    have hwv : w ≠ v.val := by intro h; exact hw (h ▸ v.property)
    simp [permEdge, blockBoundaryEdge, he, Equiv.swap_apply_of_ne_of_ne hwu hwv]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.block_boundary_mem_orbit := @_root_.OAI.Problem313.block_boundary_mem_orbit
