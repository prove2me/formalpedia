-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.shiftS_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:42.465749+00:00
-- url     : https://prove2.me/submissions/262e0a3e-922d-4faa-843f-5b2b05ef7f38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
namespace GlobalTheory.MomOne.Basic
theorem _root_.solution (ζ : ℂ_[q]) : shiftS ζ X = C ζ * (1 + X) - 1 := by
  ext n
  rw [shiftS, coeff_mk, tsum_eq_single 1 (fun m hm => by simp [coeff_X, hm])]
  rcases n with _ | _ | n <;> simp [coeff_X, coeff_one, mul_add, Nat.choose_eq_zero_of_lt]
end GlobalTheory.MomOne.Basic
