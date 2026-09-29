-- Prove2me | solution 1 for IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/62c8e7a0-9e64-5b09-a2bf-3b46e23fa670

import Mathlib
import Theorems.Thm_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
import Theorems.Thm_IsRegularLocalRing_exists_isUnit_pow_eq_mul_of_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open IsLocalRing Polynomial

open scoped TensorProduct

theorem solution
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (hdim : ringKrullDim R ≤ 2)
    (s : R) (hs : s ∈ maximalIdeal R) (hs2 : s ∉ maximalIdeal R ^ 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R))
    (R' : Type*) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R'] [Algebra.Etale R R']
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    (hdeg : Module.finrank K₀ F = e)
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (u' : R'ˣ)
    (e' : R' ⊗[R] B ≃ₐ[R'] AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) :
    ∃ u : Rˣ, Nonempty (B ≃ₐ[R] AdjoinRoot (X ^ e - C ((u : R) * s) : R[X])) := by
  obtain ⟨u, θ, hθ⟩ := IsRegularLocalRing.exists_isUnit_pow_eq_mul_of_baseChange hdim s hs hs2 e he heR R' B hres u' e'
  have ht : (u : R) * s ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hs
  have ht2 : (u : R) * s ∉ maximalIdeal R ^ 2 := fun h => hs2 (by
    have := Ideal.mul_mem_left (maximalIdeal R ^ 2) ((u⁻¹ : Rˣ) : R) h
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
  obtain ⟨φ, -⟩ := IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
    hdim ht ht2 he B K₀ F hdeg θ hθ
  exact ⟨u, ⟨φ.symm⟩⟩

end S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed
end P2MW
export P2MW.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed (solution)
