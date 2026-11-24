-- Prove2me | solution 1 for GlobalTheory.WeilM.eq_one_of_forall_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:58:59.395873+00:00
-- url     : https://prove2.me/submissions/1dc8c444-793d-4e3d-9991-415fd2bedc2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise
open GlobalTheory GlobalTheory.WeilM
namespace GlobalTheory.WeilM
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerTwoNormLowerBound.main
  | exact _root_.GlobalTheory.PowerTwoNormLowerBound.main
  | (apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerTwoNormLowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerTwoNormLowerBound.main ..)
end GlobalTheory.WeilM
