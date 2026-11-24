-- Prove2me | solution 1 for GlobalTheory.oneZ_tmul_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:23.390922+00:00
-- url     : https://prove2.me/submissions/f311d4ae-27bf-4660-854d-00a854877747

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
theorem _root_.solution (p : ℕ) (M : ModuleCat.{0} ℤ) :
    ∀ t : TensorProduct ℤ (zmodOverInt p) M, ∃ m : M, oneZ p ⊗ₜ[ℤ] m = t := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul a m =>
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := p) a
    have h1 := map_zsmul (AddMonoidHom.mk' (fun x : M => oneZ p ⊗ₜ[ℤ] x) (TensorProduct.tmul_add _)) k m
    have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] m)
      (fun b c => TensorProduct.add_tmul b c m)) k (oneZ p)
    refine ⟨_, (h1.trans h2.symm).trans (congrArg (fun x => x ⊗ₜ[ℤ] m) ?_)⟩
    show (k • (1 : ZMod p) : ZMod p) = a
    rw [zsmul_one]
    exact hk
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, (TensorProduct.tmul_add _ u v).trans (by rw [hu, hv])⟩
end GlobalTheory
