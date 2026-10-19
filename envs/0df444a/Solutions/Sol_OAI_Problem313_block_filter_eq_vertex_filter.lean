-- Prove2me | solution 1 for OAI.Problem313.block_filter_eq_vertex_filter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:06:16.388747+00:00
-- url     : https://prove2.me/submissions/84c9b978-a5d7-48cd-b826-711979506536

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockIncidence.lean:L9-L31
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.block_filter_eq_vertex_filter. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.BlockIncidence ----
namespace OAI

noncomputable section

namespace Problem313

/-- If a block meets the vertex support in one vertex, precisely that vertex's
incident support edges survive restriction to the block. -/
theorem block_filter_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S.filter (fun e => (e.val ∩ B).Nonempty) =
      S.filter (fun e => u ∈ e.val) := by
  classical
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, v, hv⟩
    have hvB : v ∈ B := (Finset.mem_inter.mp hv).2
    have hvE : v ∈ e.val := (Finset.mem_inter.mp hv).1
    have hvS : v ∈ S.biUnion (fun e => e.val) :=
      Finset.mem_biUnion.mpr ⟨e, he, hvE⟩
    have hvu : v = u := by
      have : v ∈ ({u} : Finset (Fin n)) := h ▸ Finset.mem_inter.mpr ⟨hvB, hvS⟩
      exact Finset.mem_singleton.mp this
    exact ⟨he, hvu ▸ hvE⟩
  · rintro ⟨he, huE⟩
    have hu : u ∈ B ∩ S.biUnion (fun e => e.val) := by rw [h]; simp
    exact ⟨he, u, Finset.mem_inter.mpr ⟨huE, (Finset.mem_inter.mp hu).1⟩⟩

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.block_filter_eq_vertex_filter := @_root_.OAI.Problem313.block_filter_eq_vertex_filter
