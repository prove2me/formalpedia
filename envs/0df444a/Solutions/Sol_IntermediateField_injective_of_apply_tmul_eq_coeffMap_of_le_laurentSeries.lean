-- Prove2me | solution 1 for IntermediateField.injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/33d38f25-d2c9-5412-8a74-bc554f2174b1

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

universe u v

theorem solution
    (κ : Type u) [Field κ] (k : Type v) [Field k] [Algebra κ k]
    (R : IntermediateField κ (LaurentSeries κ))
    (φ : k ⊗[κ] ↥R →ₐ[k] LaurentSeries k)
    (hφ : ∀ r : ↥R, φ (1 ⊗ₜ[κ] r) = ModularCurve.coeffMap (algebraMap κ k) ((r : ↥R) : LaurentSeries κ)) :
    Function.Injective φ := by
  classical
  let b₀ := Module.Free.chooseBasis κ k
  let bT := Algebra.TensorProduct.basis (↥R) b₀

  have hφ' : ∀ (c : k) (r : ↥R),
      φ (c ⊗ₜ[κ] r) = algebraMap k (LaurentSeries k) c *
        ModularCurve.coeffMap (algebraMap κ k) ((r : ↥R) : LaurentSeries κ) := by
    intro c r
    have : c ⊗ₜ[κ] r = algebraMap k (k ⊗[κ] ↥R) c * ((1 : k) ⊗ₜ[κ] r) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, map_mul, AlgHom.commutes, hφ]
  rw [injective_iff_map_eq_zero]
  intro z hz
  set z' : ↥R ⊗[κ] k := TensorProduct.comm κ k ↥R z with hz'
  have hzz : z = (TensorProduct.comm κ k ↥R).symm z' := by
    simp [hz']
  set s := (bT.repr z').support with hs
  set c : Module.Free.ChooseBasisIndex κ k → ↥R := fun i => bT.repr z' i with hc

  have hexp : z' = ∑ i ∈ s, (c i) ⊗ₜ[κ] (b₀ i) := by
    conv_lhs => rw [← bT.linearCombination_repr z']
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

  have hsum : φ z = ∑ i ∈ s, algebraMap k (LaurentSeries k) (b₀ i) *
      ModularCurve.coeffMap (algebraMap κ k) ((c i : ↥R) : LaurentSeries κ) := by
    rw [hzz, hexp, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [TensorProduct.comm_symm_tmul, hφ']

  have hcoeff : ∀ i ∈ s, ∀ n : ℤ, ((c i : ↥R) : LaurentSeries κ).coeff n = 0 := by
    intro i hi n
    have h0 : (φ z).coeff n = 0 := by rw [hz]; rfl
    rw [hsum, HahnSeries.coeff_sum] at h0
    have h1 : ∑ j ∈ s, (((c j : ↥R) : LaurentSeries κ).coeff n) • b₀ j = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        ModularCurve.coeffMap_coeff, Algebra.smul_def, mul_comm]
    exact linearIndependent_iff'.mp b₀.linearIndependent s _ h1 i hi
  have hc0 : ∀ i ∈ s, c i = 0 := by
    intro i hi
    have : ((c i : ↥R) : LaurentSeries κ) = 0 := by
      ext n
      simpa using hcoeff i hi n
    exact_mod_cast this
  have hrepr : bT.repr z' = 0 := by
    refine Finsupp.ext fun i => ?_
    by_cases hi : i ∈ s
    · exact hc0 i hi
    · rw [Finsupp.zero_apply]
      exact Finsupp.notMem_support_iff.mp hi
  have hz'0 : z' = 0 := by
    simpa using hrepr
  rw [hzz, hz'0, map_zero]

end S_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries
end P2MW
export P2MW.S_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries (solution)
