-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.prod_erase_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:23:48.310843+00:00
-- url     : https://prove2.me/submissions/5389efe5-5448-436e-819b-e69dc15f4b0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.Model
namespace GlobalTheory.WigSh.Model
theorem _root_.solution {n : ℕ} (f : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∏ j ∈ univ.erase l, f j = ∏ j : Fin n, f (l.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
    Finset.prod_image (fun a _ b _ hab => Fin.succAbove_right_injective hab)]
end GlobalTheory.WigSh.Model
