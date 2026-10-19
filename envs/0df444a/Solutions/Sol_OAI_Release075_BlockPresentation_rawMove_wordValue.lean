-- Prove2me | solution 1 for OAI.Release075.BlockPresentation.rawMove_wordValue
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:21:52.812989+00:00
-- url     : https://prove2.me/submissions/6dbac210-1e36-4531-9946-4e6a316b2737

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/LiftedFilling.lean:L139-L151
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.BlockPresentation.rawMove_wordValue. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling

-- ---- from OAI.GroupTheory.Hyperbolic.LiftedFilling ----
namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem rawMove_wordValue {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    d.wordValue (d.rawWord p) = d.wordValue (d.rawWord q) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change d.wordValue [] = d.wordValue [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)]
      simp only [wordValue_nil,wordValue_cons,orientedLabel_reverse,edgeValue_flip,mul_one,mul_inv_cancel]
  | triangle b i u v =>
    change d.edgeValue (d.orientedL b i u v) * d.edgeValue (d.orientedX i u v) * 1 =
      d.edgeValue (d.orientedR b i u v) * 1
    simp only [edgeValue,orientedL,orientedX,orientedR,↓reduceIte,mul_one]
    exact (eq_inv_mul_iff_mul_eq).mp (d.triangle_relation b i u v)

end Release075.BlockPresentation

namespace Release075.TriangleFilling
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge}

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).LiftedEdge}

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.BlockPresentation
open CategoryTheory


theorem solution : type_of% @_root_.OAI.Release075.BlockPresentation.rawMove_wordValue := @_root_.OAI.Release075.BlockPresentation.rawMove_wordValue
