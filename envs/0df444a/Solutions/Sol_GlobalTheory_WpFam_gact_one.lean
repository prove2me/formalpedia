-- Prove2me | solution 1 for GlobalTheory.WpFam.gact_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:22.287005+00:00
-- url     : https://prove2.me/submissions/3e4c6c59-9fcb-4e15-80d3-e464106dc1fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups Matrix
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution (N : ℕ) (α : GL (Fin 2) (ZMod N)) (γ : SL(2, ℤ)) : gact N 1 α γ = α * redGL N γ := by
  simp [gact]
end GlobalTheory.WpFam
