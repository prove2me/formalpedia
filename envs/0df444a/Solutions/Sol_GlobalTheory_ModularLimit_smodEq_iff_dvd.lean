-- Prove2me | solution 1 for GlobalTheory.ModularLimit.smodEq_iff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:21.640794+00:00
-- url     : https://prove2.me/submissions/9f208b29-285c-4517-af8f-5bf8bdf9cef6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SmodEqIffDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ModularLimit
namespace GlobalTheory.ModularLimit
theorem _root_.solution {W : Type} [CommRing W] (x a b : W) (k : ℕ) :
    a ≡ b [SMOD ((Ideal.span {x}) ^ k • ⊤ : Submodule W W)] ↔ x ^ k ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
end GlobalTheory.ModularLimit
