-- Prove2me | solution 1 for GlobalTheory.HTLat.isSplitting_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:48:23.980975+00:00
-- url     : https://prove2.me/submissions/23174ca0-c631-4583-acfd-46b594f5ff19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_iff_isUnit_det
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
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.HTLat
theorem _root_.solution (R : Type) [CommRing R] :
    IsSplitting (fun _ : Unit => Int.castRingHom R) := by
  rw [isSplitting_iff_isUnit_det _ (Module.Basis.singleton Unit ℤ)]
  simp
end GlobalTheory.HTLat
