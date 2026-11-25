-- Prove2me | solution 1 for GlobalTheory.eval_detProdPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:44:04.376612+00:00
-- url     : https://prove2.me/submissions/89eb81bf-5a3b-4caa-a6d5-8381b92bc183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Theorems.Thm_P2M_GlobalTheory_eval_Hom_detProdPoly_9518250e38f2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] {n : ι → Type*}
    [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)] (ξ : EntryIndex n n → R) :
    MvPolynomial.eval ξ (detProdPoly R n) = ∏ s, (ofEntries ξ s).det :=
  eval₂Hom_detProdPoly (RingHom.id R) ξ
end GlobalTheory
