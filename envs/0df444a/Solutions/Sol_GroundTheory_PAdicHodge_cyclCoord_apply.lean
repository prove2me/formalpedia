-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclCoord_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:05.858795+00:00
-- url     : https://prove2.me/submissions/a53c67bc-1edc-4c1a-a0e7-e49a8f012445

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_mem_cycl_of_pow_prime_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_map
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_map_of_map_eq
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mul_of_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η ε : PadicAlgCl p} (hεp : ε ^ p = 1) (hτη : τ η = ε * η)
    (y : PadicAlgCl p) {i : ℕ} (hi : i ≤ p ^ (k + 1)) :
    cyclCoord k η (τ y) i = ε ^ i * cyclCoord k η y i := by
  have hεk : ε ∈ cycl p k := mem_cycl_of_pow_prime_eq_one hk hεp
  have hε1 : ε ^ (p ^ (k + 1)) = 1 := by rw [pow_succ', pow_mul, hεp, one_pow]
  have e : τ y * η ^ (p ^ (k + 1) - i) = ε ^ i * τ (y * η ^ (p ^ (k + 1) - i)) := by
    rw [map_mul, map_pow, hτη, mul_pow]
    calc τ y * η ^ (p ^ (k + 1) - i)
        = τ y * (ε ^ (i + (p ^ (k + 1) - i)) * η ^ (p ^ (k + 1) - i)) := by
          rw [Nat.add_sub_cancel' hi, hε1, one_mul]
      _ = _ := by rw [pow_add]; ring
  rw [cyclCoord, e, normTrace_mul_of_mem _ (pow_mem hεk i),
    normTrace_map_of_map_eq (cycl p k) τ (cycl_map τ k), hτ _ (normTrace_mem _ _), cyclCoord]
end GroundTheory.PAdicHodge
