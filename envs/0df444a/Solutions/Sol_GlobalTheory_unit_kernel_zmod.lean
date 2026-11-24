-- Prove2me | solution 1 for GlobalTheory.unit_kernel_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:34.98415+00:00
-- url     : https://prove2.me/submissions/002ced77-4d09-4924-a173-c48d429156bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
import Theorems.Thm_GlobalTheory_tensorToModP_unit

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
theorem _root_.solution (p : ℕ) (M : ModuleCat.{0} ℤ) (y : M)
    (hy : ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom y = 0) :
    ∃ x : M, ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x = y := by
  have h := tensorToModP_unit p M y
  rw [hy] at h
  exact (Submodule.Quotient.mk_eq_zero _).mp (h.symm.trans (map_zero (tensorToModP p M)))
end GlobalTheory
