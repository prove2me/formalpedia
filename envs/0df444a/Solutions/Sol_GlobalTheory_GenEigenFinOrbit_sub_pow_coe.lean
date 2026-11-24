-- Prove2me | solution 1 for GlobalTheory.GenEigenFinOrbit.sub_pow_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:21.662192+00:00
-- url     : https://prove2.me/submissions/9a0b6945-4f84-40c6-90db-fa73b125fc78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.GenEigenFinOrbit
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.GenEigenFinOrbit
theorem _root_.solution {U : Submodule ℂ V} (z : End ℂ V) (F : End ℂ U)
    (hF : ∀ u : U, (F u : V) = z u) (c : ℂ) (k : ℕ) (u : U) :
    (((F - c • 1) ^ k) u : V) = ((z - algebraMap ℂ (End ℂ V) c) ^ k) (u : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    simp [hF]
end GlobalTheory.GenEigenFinOrbit
