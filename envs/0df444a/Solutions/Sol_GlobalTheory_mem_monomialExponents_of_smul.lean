-- Prove2me | solution 1 for GlobalTheory.mem_monomialExponents_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:06.841398+00:00
-- url     : https://prove2.me/submissions/2fb0f3c4-3c1a-4b5c-bcd0-cc9e0f29cb8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials
import Theorems.Thm_GlobalTheory_mem_subfield_of_zpow_mem
import Theorems.Thm_GlobalTheory_mem_monomialExponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {I : Type} [Fintype I] {K : Type} [Field K]
    (k₀ : Subfield K) [IsAlgClosed k₀] (t : I → Kˣ) (v : I → ℤ) (m : ℤ) (hm : m ≠ 0)
    (h : m • v ∈ monomialExponents k₀ t) : v ∈ monomialExponents k₀ t := by
  rw [mem_monomialExponents] at h ⊢
  apply mem_subfield_of_zpow_mem k₀ _ m hm
  convert h using 2
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, mul_comm]
end GlobalTheory
