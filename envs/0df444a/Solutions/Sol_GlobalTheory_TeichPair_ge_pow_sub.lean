-- Prove2me | solution 1 for GlobalTheory.TeichPair.ge_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:16:21.778971+00:00
-- url     : https://prove2.me/submissions/78631c05-476f-400e-ac72-4fc0df58d017

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.TeichPair
variable {C : Type} [Field C]
namespace GlobalTheory.TeichPair
theorem _root_.solution {V : VF C} {w : ℝ} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.Ge w (a - b)) (m : ℕ) :
    V.Ge w (a ^ m - b ^ m) := by
  induction m with
  | zero => simpa using VF.Ge.zero (V := V) w
  | succ m ih =>
    have : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + b ^ m * (a - b) := by ring
    rw [this]
    exact (ha.mul_int ih).add ((hb.pow m).mul_int h)
end GlobalTheory.TeichPair
