-- Prove2me | solution 1 for OAI.ForestSpace.main_lens
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:05:30.236445+00:00
-- url     : https://prove2.me/submissions/abb9e803-e9e6-415b-a35c-48d11fd45b9e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Lens.lean:L135-L152
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.main_lens. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
import Definitions.Def_OAI_Analysis_ForestSpace_Components
import Definitions.Def_OAI_Analysis_ForestSpace_FullDual
import Theorems.Thm_OAI_ForestSpace_main_lens_aprox

-- ---- from OAI.Analysis.ForestSpace.Lens ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Lens
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The squared separated-midpoint deficit. -/
 theorem main_lens (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (x : FullDual Vertex) (y : ℕ → FullDual Vertex)
    (hp : ∀ j, ‖x+y j‖ ≤ R) (hm : ∀ j, ‖x-y j‖ ≤ R)
    (hs : ∀ i j, i ≠ j → ε ≤ ‖y i-y j‖) :
    ε^2/48 ≤ R^2-‖x‖^2 := by
  have hh : ‖x‖^2+ε^2/48 ≤ R^2 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let η := min 1 (δ/(8*(R+1)))
    have hc : 0 < 8*(R+1) := by positivity
    have hη : 0 < η := lt_min (by norm_num) (div_pos hδ hc)
    have hb := main_lens_aprox R ε hR hε x y hp hm hs η hη (min_le_left _ _)
    have he : 8*(R+1)*η ≤ δ := by
      rw [mul_comm]
      exact (le_div_iff₀ hc).mp (min_le_right _ _)
    linarith
  linarith

end Lens

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.main_lens := @_root_.OAI.ForestSpace.main_lens
