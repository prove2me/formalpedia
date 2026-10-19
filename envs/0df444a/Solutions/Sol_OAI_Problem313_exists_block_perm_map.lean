-- Prove2me | solution 1 for OAI.Problem313.exists_block_perm_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:20:36.895475+00:00
-- url     : https://prove2.me/submissions/d5f47d89-8e06-4568-bccc-6547fc791b62

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockOrbits.lean:L11-L42
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.exists_block_perm_map. The node keeps its source
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

/-- A permutation supported on a finite block can map any two equally sized
subsets of the block to one another. -/
theorem exists_block_perm_map {α : Type u} [Fintype α] [DecidableEq α]
    (B s t : Finset α) (hs : s ⊆ B) (ht : t ⊆ B)
    (hc : s.card = t.card) :
    ∃ π : Equiv.Perm α, (∀ u, u ∉ B → π u = u) ∧
      s.map π.toEmbedding = t := by
  classical
  let sB := s.subtype (· ∈ B)
  let tB := t.subtype (· ∈ B)
  have hsmap : sB.map (Function.Embedding.subtype _) = s :=
    Finset.subtype_map_of_mem hs
  have htmap : tB.map (Function.Embedding.subtype _) = t :=
    Finset.subtype_map_of_mem ht
  have hcB : sB.card = tB.card := by
    have hsc := congrArg Finset.card hsmap
    have htc := congrArg Finset.card htmap
    simpa using hsc.trans (hc.trans htc.symm)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq sB tB hcB
  let π : Equiv.Perm α := σ.extendDomain (Equiv.refl {u // u ∈ B})
  refine ⟨π, ?_, ?_⟩
  · intro u hu
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hu
  · calc
      s.map π.toEmbedding = (sB.map (Function.Embedding.subtype _)).map π.toEmbedding := by
        rw [hsmap]
      _ = (sB.map σ.toEmbedding).map (Function.Embedding.subtype _) := by
        rw [Finset.map_map, Finset.map_map]
        congr 1
        ext u
        exact Equiv.Perm.extendDomain_apply_image σ (Equiv.refl _) u
      _ = t := by rw [hσ, htmap]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution.{u} : type_of% @_root_.OAI.Problem313.exists_block_perm_map.{u} := @_root_.OAI.Problem313.exists_block_perm_map.{u}
