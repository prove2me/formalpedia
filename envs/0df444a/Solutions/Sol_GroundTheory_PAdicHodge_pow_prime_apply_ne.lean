-- Prove2me | solution 1 for GroundTheory.PAdicHodge.pow_prime_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:45.668069+00:00
-- url     : https://prove2.me/submissions/3064e691-efb7-42e8-ba8a-d2fbfbd7ac16

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_exists_apply_eq_mul_of_fix
import Theorems.Thm_GroundTheory_PAdicHodge_apply_ne_of_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl
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
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (hτη : τ η ≠ η) {η' : PadicAlgCl p} (hη' : IsPrimitiveRoot η' (p ^ (k + 1 + 1))) :
    (τ ^ p) η' ≠ η' := by
  have hpr := (Fact.out : p.Prime)
  have hη'0 : η' ≠ 0 := hη'.ne_zero (pow_ne_zero _ hpr.ne_zero)
  have hη'p : IsPrimitiveRoot (η' ^ p) (p ^ (k + 1)) :=
    hη'.pow (pow_pos hpr.pos _) (by ring)
  obtain ⟨ε, hεp, hτε⟩ := exists_apply_eq_mul_of_fix τ hτ hη'p
  have hε1 : ε ≠ 1 := by
    rintro rfl; rw [one_mul] at hτε
    exact apply_ne_of_isPrimitiveRoot τ hτ hη hτη hη'p hτε
  set δ := τ η' * η'⁻¹ with hδ
  have hτη' : τ η' = δ * η' := by rw [hδ]; field_simp
  have hδp : δ ^ p = ε := by
    rw [hδ, mul_pow, inv_pow, ← map_pow, hτε, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hη'0),
      mul_one]
  have hδk : δ ∈ cycl p k := by
    apply pow_eq_one_mem_cycl
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show p ^ (j + 2) = p * (p * p ^ j) by ring, pow_mul, hδp, pow_mul, hεp, one_pow]
  have hpow : ∀ j : ℕ, (τ ^ j) η' = δ ^ j * η' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτη', map_mul, ih]
      have : (τ ^ j) δ = δ := by
        clear ih
        induction j with
        | zero => simp
        | succ j ih2 => rw [pow_succ, AlgEquiv.mul_apply, hτ δ hδk, ih2]
      rw [this]; ring
  rw [hpow, hδp]
  intro h
  have : ε = 1 := by
    have := congrArg (· * η'⁻¹) h
    simpa [mul_assoc, mul_inv_cancel₀ hη'0] using this
  exact hε1 this
end GroundTheory.PAdicHodge
