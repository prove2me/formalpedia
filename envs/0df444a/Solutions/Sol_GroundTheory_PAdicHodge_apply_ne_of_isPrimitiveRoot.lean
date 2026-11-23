-- Prove2me | solution 1 for GroundTheory.PAdicHodge.apply_ne_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:50.321592+00:00
-- url     : https://prove2.me/submissions/95e1467f-df38-4499-a157-5c5db05cfcbd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_exists_apply_eq_mul_of_fix
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
theorem _root_.solution {k : ℕ} (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (hτη : τ η ≠ η) {η' : PadicAlgCl p} (hη' : IsPrimitiveRoot η' (p ^ (k + 1))) : τ η' ≠ η' := by
  have hpr := (Fact.out : p.Prime)
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hpr.ne_zero⟩
  obtain ⟨ε, hεp, hτη'⟩ := exists_apply_eq_mul_of_fix τ hτ hη
  have hε1 : ε ≠ 1 := by rintro rfl; rw [one_mul] at hτη'; exact hτη hτη'
  have hprim : IsPrimitiveRoot ε p := by
    have := IsPrimitiveRoot.orderOf ε
    rwa [orderOf_eq_prime hεp hε1] at this
  obtain ⟨j, -, rfl⟩ := hη.eq_pow_of_pow_eq_one hη'.pow_eq_one
  have hj : ¬ p ∣ j := by
    intro h
    obtain ⟨c, rfl⟩ := h
    have := hη'.pow_eq_one_iff_dvd (p ^ k)
    have h2 : (η ^ (p * c)) ^ (p ^ k) = 1 := by
      rw [← pow_mul, show p * c * p ^ k = p ^ (k + 1) * c by ring, pow_mul, hη.pow_eq_one, one_pow]
    have h3 := this.1 h2
    have h4 := Nat.le_of_dvd (pow_pos hpr.pos _) h3
    have h5 : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hpr.one_lt (by omega)
    omega
  rw [map_pow, hτη', mul_pow]
  intro h
  have hη0 : η ^ j ≠ 0 := pow_ne_zero _ (hη.ne_zero (pow_ne_zero _ hpr.ne_zero))
  have : ε ^ j = 1 := by
    have := congrArg (· * (η ^ j)⁻¹) h
    simpa [mul_assoc, mul_inv_cancel₀ hη0] using this
  exact hj ((hprim.pow_eq_one_iff_dvd j).1 this)
end GroundTheory.PAdicHodge
