-- Prove2me | solution 1 for GlobalTheory.Cyc.padic_norm_sub_le_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:52.642626+00:00
-- url     : https://prove2.me/submissions/ba82f3cd-9e10-436e-b4bb-fe82eb9b9651

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution {x y z : ℚ_[l]} {r : ℝ} (h1 : ‖x - y‖ ≤ r) (h2 : ‖y - z‖ ≤ r) :
    ‖x - z‖ ≤ r := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
end GlobalTheory.Cyc
