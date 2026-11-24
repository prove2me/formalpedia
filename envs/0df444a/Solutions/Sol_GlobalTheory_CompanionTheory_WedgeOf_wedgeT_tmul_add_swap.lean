-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul_add_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:47.143418+00:00
-- url     : https://prove2.me/submissions/c9ac02eb-c7f1-4c19-b2d7-633ed4794bab

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (a b : V) :
    wedgeT (R := R) V (a ⊗ₜ[R] b) + wedgeT (R := R) V (b ⊗ₜ[R] a) = 0 := by
  have h := wedgeT_tmul_self (R := R) (a + b)
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add,
    map_add, wedgeT_tmul_self, wedgeT_tmul_self, zero_add, add_zero] at h
  exact h
end GlobalTheory.CompanionTheory.WedgeOf
