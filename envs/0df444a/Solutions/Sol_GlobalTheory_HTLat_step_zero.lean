-- Prove2me | solution 1 for GlobalTheory.HTLat.step_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:45.505188+00:00
-- url     : https://prove2.me/submissions/f53a898c-2d90-41f5-86cd-ba8826c95105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
namespace GlobalTheory.HTLat
namespace _root_.GlobalTheory.HTLat
theorem _root_.solution (f : Fin N → U) :
    _root_.GlobalTheory.HTLat.step C f 0 = ⊥ := by
  simp [_root_.GlobalTheory.HTLat.step]
end _root_.GlobalTheory.HTLat
end GlobalTheory.HTLat
