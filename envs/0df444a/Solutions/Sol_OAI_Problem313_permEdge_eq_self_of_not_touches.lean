-- Prove2me | solution 1 for OAI.Problem313.permEdge_eq_self_of_not_touches
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:19:09.299902+00:00
-- url     : https://prove2.me/submissions/19bd3690-8ce4-4e37-9b29-d67ecc0893d8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockRestrictionSymmetry.lean:L53-L68
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.permEdge_eq_self_of_not_touches. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.BlockRestrictionSymmetry ----
namespace OAI

noncomputable section
namespace Problem313

lemma permEdge_eq_self_of_not_touches {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π)
    (e : GraphEdge n) (he : ¬ EdgeTouches B e) : permEdge π e = e := by
  apply Subtype.ext
  ext v
  rw [block_mem_permEdge_iff]
  constructor
  · intro hv
    have hn : π.symm v ∉ B := fun h => he ⟨π.symm v, hv, h⟩
    have hf := hπ (π.symm v) hn
    have hf' : v = π.symm v := by simpa using hf
    exact hf'.symm ▸ hv
  · intro hv
    have hn : v ∉ B := fun h => he ⟨v, hv, h⟩
    have hf := supportedOnBlock_symm hπ v hn
    simpa [hf] using hv

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.permEdge_eq_self_of_not_touches := @_root_.OAI.Problem313.permEdge_eq_self_of_not_touches
