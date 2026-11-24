-- Prove2me | solution 1 for GlobalTheory.modPPairing_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:42.336906+00:00
-- url     : https://prove2.me/submissions/923b55bc-c3f8-495b-baaf-e745566533bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] (m : M) :
    modPPairing p M 1 m = Submodule.Quotient.mk m := by
  have h := ZMod.lift_coe p (A := M →+ (M ⧸ pMultiples p M))
    ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩ 1
  simp only [Int.cast_one] at h
  unfold modPPairing
  rw [h]
  simp
end GlobalTheory
