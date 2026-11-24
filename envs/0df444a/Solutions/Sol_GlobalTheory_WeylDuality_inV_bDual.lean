-- Prove2me | solution 1 for GlobalTheory.WeylDuality.inV_bDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:51.026266+00:00
-- url     : https://prove2.me/submissions/c99b179d-33c4-4334-9240-1bcbe4d8a7f7

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_fockQ_hw_pos
import Theorems.Thm_GlobalTheory_WeylDuality_mem_bDual
import Theorems.Thm_GlobalTheory_WeylDuality_normB_apply
import Theorems.Thm_GlobalTheory_WeylDuality_mem_inV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (hM : ∀ Q ∈ M, Q ∈ dualWeyl ℚ r n ν) :
    inV ν (bDual r n hn ν M) = (normB hn ν).dualSubmodule (inV ν M) := by
  have hc := fockQ_hw_pos hn ν
  ext x
  rw [mem_inV, mem_bDual, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · rintro ⟨-, h⟩ y hy
    rw [mem_inV] at hy
    obtain ⟨z, hz⟩ := h y.1 hy
    rw [Submodule.mem_one]
    refine ⟨z, ?_⟩
    rw [normB_apply, hz, algebraMap_int_eq, eq_intCast]
    field_simp
  · intro h
    refine ⟨x.2, fun Q hQ => ?_⟩
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (h ⟨Q, hM Q hQ⟩ ((mem_inV _ _ _).mpr hQ))
    refine ⟨z, ?_⟩
    rw [normB_apply, algebraMap_int_eq, eq_intCast, eq_inv_mul_iff_mul_eq₀ hc.ne'] at hz
    rw [← hz, mul_comm]
end GlobalTheory.WeylDuality
