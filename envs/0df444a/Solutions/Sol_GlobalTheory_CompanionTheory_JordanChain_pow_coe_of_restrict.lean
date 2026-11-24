-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JordanChain.pow_coe_of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:01.516127+00:00
-- url     : https://prove2.me/submissions/20415da6-4994-41bd-8cd3-52e51a791e9f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JordanChain
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.CompanionTheory.JordanChain
theorem _root_.solution {W : Submodule K V} (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hg : ∀ x, (g x : V) = f x) (k : ℕ) (x : W) : (((g ^ k) x : W) : V) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hg]
end GlobalTheory.CompanionTheory.JordanChain
