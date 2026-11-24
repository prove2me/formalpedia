-- Prove2me | solution 1 for GlobalTheory.IntegralFrameCheck.vV_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:50.74691+00:00
-- url     : https://prove2.me/submissions/03d3a7e6-c099-41a8-82dc-f413db9141a7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_Formalism_L2_Pj_vV_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']
namespace GlobalTheory.IntegralFrameCheck
theorem _root_.solution {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV]
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero n hx) hx, ih]; push_cast; ring
end GlobalTheory.IntegralFrameCheck
