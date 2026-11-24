-- Prove2me | solution 1 for GlobalTheory.DualFibreRank.cmp_bijective_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:54.346069+00:00
-- url     : https://prove2.me/submissions/7698ac0b-1e44-431c-945e-c19d0aa5b773

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.DualFibreRank
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]
variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
namespace GlobalTheory.DualFibreRank
theorem _root_.solution [Module.Free O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  have h := (TensorProduct.isBaseChange O M A)
  have : cmp A M (O := O) = h.toDualBaseChange.toLinearMap := by
    ext g x
    have := h.toDualBaseChange_tmul 1 g x
    simp only [TensorProduct.mk_apply] at this
    simp [cmp, this, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact h.toDualBaseChange.bijective
end GlobalTheory.DualFibreRank
