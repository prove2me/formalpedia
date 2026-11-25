-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.shiftS_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:46.082639+00:00
-- url     : https://prove2.me/submissions/a182366a-1451-4cfe-ab62-111cb6621376

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
open PowerSeries
open scoped ComplexConjugate
variable {q : ℕ} [Fact q.Prime]
open Filter Topology
namespace GlobalTheory.MomOne.Basic
namespace _root_.GlobalTheory.MomOne.Basic
theorem _root_.solution (f : ℂ_[q]⟦X⟧) :
    _root_.GlobalTheory.MomOne.shiftS 1 f = f := by
  ext n
  rw [_root_.GlobalTheory.MomOne.shiftS, coeff_mk, tsum_eq_single n]
  · simp
  · intro m hm
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · have : m - n ≠ 0 := by omega
      simp [zero_pow this]
end _root_.GlobalTheory.MomOne.Basic
end GlobalTheory.MomOne.Basic
