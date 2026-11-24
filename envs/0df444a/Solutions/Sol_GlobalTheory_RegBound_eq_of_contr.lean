-- Prove2me | solution 1 for GlobalTheory.RegBound.eq_of_contr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:12.795916+00:00
-- url     : https://prove2.me/submissions/3b739195-052d-4209-82a2-6aff6311af73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.RegBound
theorem _root_.solution {F G : MvPolynomial σ L} (h : ∀ φ : L →ₗ[K] K, contr φ F = contr φ G) :
    F = G := by
  ext m
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  rw [map_sub, sub_eq_zero, ← coeff_contr, ← coeff_contr, h]
end GlobalTheory.RegBound
