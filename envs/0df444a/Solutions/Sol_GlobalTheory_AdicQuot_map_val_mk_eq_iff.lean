-- Prove2me | solution 1 for GlobalTheory.AdicQuot.map_val_mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:34.757862+00:00
-- url     : https://prove2.me/submissions/4bfcc7a1-1326-45a8-919f-b031d96e8b55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
import Theorems.Thm_GlobalTheory_AdicQuot_mem_smul_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)
namespace GlobalTheory.AdicQuot
theorem _root_.solution (s : AdicCauchySequence J A) (n : ℕ) (c : A ⧸ q) :
    (map J (Submodule.mkQ q) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl
end GlobalTheory.AdicQuot
