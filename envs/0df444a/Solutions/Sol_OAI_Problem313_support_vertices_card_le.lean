-- Prove2me | solution 1 for OAI.Problem313.support_vertices_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:12:28.602133+00:00
-- url     : https://prove2.me/submissions/0b1348d9-c2eb-4a92-91bd-9ece9d4d8db4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/SupportDegreeGraph.lean:L10-L22
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.support_vertices_card_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.SupportDegree ----
namespace OAI

universe u

/-! Elementary support-graph combinatorics, independent of probability. -/

namespace Problem313.SupportCombinatorics

open Finset

variable {α : Type u} [DecidableEq α]

lemma card_vertices_le {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) : (vertices S).card ≤ 2 * S.card := by
  calc
    (vertices S).card ≤ ∑ e ∈ S, e.card := card_biUnion_le
    _ = 2 * S.card := by
      rw [sum_congr rfl hS]
      simp [Nat.mul_comm]

end Problem313.SupportCombinatorics

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.SupportDegreeGraph ----
namespace OAI

namespace Problem313

open Finset

lemma support_vertices_card_le {n : ℕ} (S : Finset (GraphEdge n)) :
    (S.biUnion (fun e => e.val)).card ≤ 2 * S.card := by
  classical
  have h := SupportCombinatorics.card_vertices_le
    (S := S.image Subtype.val) (by
      intro e he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact f.property)
  have hv : SupportCombinatorics.vertices (S.image Subtype.val) =
      S.biUnion (fun e => e.val) := by
    ext u
    simp [SupportCombinatorics.vertices]
  simpa [hv, card_image_of_injective S Subtype.val_injective] using h

end Problem313

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open Finset


theorem solution : type_of% @_root_.OAI.Problem313.support_vertices_card_le := @_root_.OAI.Problem313.support_vertices_card_le
