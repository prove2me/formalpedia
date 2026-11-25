-- Prove2me | solution 1 for GroundTheory.PAdicHodge.pow_prime_fix_cycl_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:46.324644+00:00
-- url     : https://prove2.me/submissions/7561c824-a55f-45b9-86ee-a8884ab35530

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_exists_apply_eq_mul_of_fix
import Theorems.Thm_GroundTheory_PAdicHodge_mem_cycl_of_pow_prime_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_eq_adjoin
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) : ∀ x ∈ cycl p (k + 1), (τ ^ p) x = x := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
  obtain ⟨ε, hεp, hτζ⟩ := exists_apply_eq_mul_of_fix τ hτ hζ
  have hεk : ε ∈ cycl p k := mem_cycl_of_pow_prime_eq_one hk hεp
  have hpow : ∀ j : ℕ, (τ ^ j) ζ = ε ^ j * ζ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτζ, map_mul, ih]
      have : (τ ^ j) ε = ε := by
        clear ih
        induction j with
        | zero => simp
        | succ j ih2 => rw [pow_succ, AlgEquiv.mul_apply, hτ ε hεk, ih2]
      rw [this]; ring
  have hfix : (τ ^ p) ζ = ζ := by rw [hpow, hεp, one_mul]
  intro x hx
  rw [cycl_eq_adjoin hζ, mem_adjoin_simple_iff] at hx
  obtain ⟨r, s, rfl⟩ := hx
  rw [map_div₀, ← AlgEquiv.coe_toAlgHom, ← aeval_algHom_apply, ← aeval_algHom_apply,
    AlgEquiv.coe_toAlgHom, hfix]
end GroundTheory.PAdicHodge
