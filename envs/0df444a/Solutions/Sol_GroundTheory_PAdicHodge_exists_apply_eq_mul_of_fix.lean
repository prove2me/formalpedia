-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_apply_eq_mul_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:30.082124+00:00
-- url     : https://prove2.me/submissions/33b27fb2-af76-46a5-a455-69accd33fc9c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl


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
theorem _root_.solution {k : ℕ} (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1))) :
    ∃ ε : PadicAlgCl p, ε ^ p = 1 ∧ τ η = ε * η := by
  have hη0 : η ≠ 0 := hη.ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hc : η ^ p ∈ cycl p k :=
    pow_eq_one_mem_cycl (by rw [← pow_mul, ← pow_succ']; exact hη.pow_eq_one)
  refine ⟨τ η * η⁻¹, ?_, by field_simp⟩
  rw [mul_pow, inv_pow, ← map_pow, hτ _ hc, mul_inv_cancel₀ (pow_ne_zero _ hη0)]
end GroundTheory.PAdicHodge
