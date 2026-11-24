-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.gauss_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:15.912831+00:00
-- url     : https://prove2.me/submissions/8175ca02-d52e-4ecf-84f3-adf900d5fd76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
import Theorems.Thm_GlobalTheory_TripleIntertwiner_gauss_pow_four_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution {M : Type*} [AddCommGroup M] [Fintype M] (β : M → M → ℂ)
    (hl : ∀ x x' y, β (x + x') y = β x y * β x' y) (hr : ∀ x y y', β x (y + y') = β x y * β x y')
    (hne : ∀ x y, β x y ≠ 0) :
    (∑ m, β m m) ^ 4 = (∑ m, (β m m)⁻¹) ^ 4 := by
  let γ : M →+ M →+ Additive ℂˣ := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (Units.mk0 (β x y) (hne x y))) (by
      intro y y'
      rw [← ofMul_mul]; congr 1; ext; simp [hr]))
    (by
      intro x x'
      ext y
      simp [hl])
  simpa [γ] using gauss_pow_four_hom γ
end GlobalTheory.TripleIntertwiner
