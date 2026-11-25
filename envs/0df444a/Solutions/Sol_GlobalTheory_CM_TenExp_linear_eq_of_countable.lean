-- Prove2me | solution 1 for GlobalTheory.CM.TenExp.linear_eq_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:00.198592+00:00
-- url     : https://prove2.me/submissions/cc90a4db-10f8-4bad-bf75-9feec30efe24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsDiagonalCoordinates
import Theorems.Thm_GlobalTheory_CM_TenExp_mem_of_countable
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.TenExp
namespace GlobalTheory.CM.TenExp
theorem _root_.solution {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    {Λ : Set V} (hΛ : Λ.Countable) {F F' : U →ₗ[ℂ] V} (h : ∀ u, F u - F' u ∈ Λ) : F = F' := by
  ext u
  rw [← sub_eq_zero, ← Submodule.mem_bot ℂ]
  refine mem_of_countable hΛ ⊥ fun z => ⟨_, h (z • u), ?_⟩
  simp [smul_sub]
end GlobalTheory.CM.TenExp
