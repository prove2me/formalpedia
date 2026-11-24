-- Prove2me | solution 1 for GlobalTheory.CubeFace.prod_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:20:51.296809+00:00
-- url     : https://prove2.me/submissions/eab72066-13cf-4c25-8b24-0f45c67a6290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
import Theorems.Thm_GlobalTheory_CubeFace_prod_subsets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
namespace GlobalTheory.CubeFace
theorem _root_.solution (f : Finset (Fin 3) → ℂ) :
    ∏ I : Finset (Fin 3), f I ^ ((-1 : ℤ) ^ (3 - I.card)) =
      (f ∅)⁻¹ * f {0} * f {1} * f {2} * (f {0, 1})⁻¹ * (f {0, 2})⁻¹ * (f {1, 2})⁻¹ *
        f {0, 1, 2} := by
  rw [prod_subsets]
  have h01 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have h02 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have h12 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have h012 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  rw [h01, h02, h12, h012]
  norm_num
end GlobalTheory.CubeFace
