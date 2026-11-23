-- Prove2me | solution 1 for GlobalTheory.UnitValueExistence.norm_add_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:44.062247+00:00
-- url     : https://prove2.me/submissions/28fc8725-614b-47ba-9c90-2517449a555b

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
theorem _root_.solution {E : Type} [NormedField E] [IsUltrametricDist E] {a b : E}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)
end GlobalTheory.UnitValueExistence
