-- Prove2me | solution 1 for GlobalTheory.UnitValueExistence.norm_one_add_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:18.667951+00:00
-- url     : https://prove2.me/submissions/99e4e4a5-9f8b-485d-b8bf-70e62c4b3dd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitValueExistence
open Matrix
namespace GlobalTheory.UnitValueExistence
theorem _root_.solution {E : Type} [NormedField E] [IsUltrametricDist E] {a : E}
    (ha : ‖a‖ < 1) : ‖1 + a‖ = 1 := by
  have h : ‖(1 : E)‖ ≠ ‖a‖ := by rw [norm_one]; exact ha.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, norm_one, max_eq_left ha.le]
end GlobalTheory.UnitValueExistence
