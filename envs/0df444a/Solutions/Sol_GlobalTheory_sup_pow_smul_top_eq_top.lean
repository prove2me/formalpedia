-- Prove2me | solution 1 for GlobalTheory.sup_pow_smul_top_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:26.238727+00:00
-- url     : https://prove2.me/submissions/304e9835-95c7-4668-9b58-b9da7fa11d0a

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution {I : Ideal A} {N : Submodule A M} (h : N ⊔ I • ⊤ = ⊤) (n : ℕ) :
    N ⊔ I ^ n • ⊤ = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine eq_top_iff.mpr (ih.ge.trans (sup_le le_sup_left ?_))
    refine (Submodule.smul_mono le_rfl h.ge).trans ?_
    rw [Submodule.smul_sup, ← mul_smul, ← pow_succ]
    exact sup_le_sup_right Submodule.smul_le_right _
end GlobalTheory
