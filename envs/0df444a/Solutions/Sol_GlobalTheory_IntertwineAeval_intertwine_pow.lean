-- Prove2me | solution 1 for GlobalTheory.IntertwineAeval.intertwine_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:52:06.572216+00:00
-- url     : https://prove2.me/submissions/14717496-dbd1-40d2-b471-ba8eea1db3f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntertwineAeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwineAeval
namespace GlobalTheory.IntertwineAeval
theorem _root_.solution {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (r : M →ₗ[ℂ] N) {T : Module.End ℂ M} {T' : Module.End ℂ N}
    (h : ∀ v : M, r (T v) = T' (r v)) (n : ℕ) (v : M) : r ((T ^ n) v) = (T' ^ n) (r v) := by
  induction n generalizing v with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
end GlobalTheory.IntertwineAeval
