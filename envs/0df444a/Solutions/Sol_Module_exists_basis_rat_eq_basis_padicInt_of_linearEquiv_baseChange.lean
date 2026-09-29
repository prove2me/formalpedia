-- Prove2me | solution 1 for Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4486b0f4-c029-597c-b31b-4615114b5fbf

import Mathlib
import Theorems.Thm_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange

open scoped TensorProduct
set_option maxHeartbeats 6400000

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module ℚ A] [Module.Finite ℚ A]
    (Hp : Type*) [AddCommGroup Hp] [Module ℤ_[p] Hp]
    [Module.Finite ℤ_[p] Hp] [Module.Flat ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ A) (bHp : Module.Basis (Fin n) ℤ_[p] Hp),
      ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i) := by
  classical
  haveI : Module.Free ℤ_[p] Hp := Module.free_of_finite_type_torsion_free'
  set n := Module.finrank ℚ A with hn
  have hnHp : Module.finrank ℤ_[p] Hp = n := by
    have h1 : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] A) = Module.finrank ℚ A := by
      rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
    have h2 : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Hp) = Module.finrank ℤ_[p] Hp := by
      rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
    have h3 := LinearEquiv.finrank_eq φ
    omega
  let a₀ : Module.Basis (Fin n) ℚ A := Module.finBasis ℚ A
  let c₀ : Module.Basis (Fin n) ℤ_[p] Hp := Module.finBasisOfFinrankEq ℤ_[p] Hp hnHp
  let aQp : Module.Basis (Fin n) ℚ_[p] (ℚ_[p] ⊗[ℚ] A) := Algebra.TensorProduct.basis ℚ_[p] a₀
  let cQp : Module.Basis (Fin n) ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Hp) := Algebra.TensorProduct.basis ℚ_[p] c₀
  let M : Matrix (Fin n) (Fin n) ℚ_[p] := LinearMap.toMatrix aQp cQp φ.toLinearMap
  have hMdet : IsUnit M.det := LinearEquiv.isUnit_det φ aQp cQp
  obtain ⟨Q, P, hQdet, hPdet, hMQ⟩ :=
    Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det p n M hMdet
  let b : Module.Basis (Fin n) ℚ A := Module.Basis.map a₀ (Matrix.toLinearEquiv a₀ Q hQdet)
  let bHp : Module.Basis (Fin n) ℤ_[p] Hp := Module.Basis.map c₀ (Matrix.toLinearEquiv c₀ P hPdet)
  refine ⟨n, b, bHp, fun j => ?_⟩

  have hb : b j = ∑ i, Q i j • a₀ i := by
    simp only [b, Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hbHp : bHp j = ∑ i, P i j • c₀ i := by
    simp only [bHp, Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]

  have tmul_scalar_A : ∀ (r : ℚ) (x : A),
      (1:ℚ_[p]) ⊗ₜ[ℚ] (r • x) = (algebraMap ℚ ℚ_[p] r) • ((1:ℚ_[p]) ⊗ₜ[ℚ] x) := fun r x => by
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  have tmul_scalar_Hp : ∀ (r : ℤ_[p]) (x : Hp),
      (1:ℚ_[p]) ⊗ₜ[ℤ_[p]] (r • x) = (algebraMap ℤ_[p] ℚ_[p] r) • ((1:ℚ_[p]) ⊗ₜ[ℤ_[p]] x) := fun r x => by
    rw [TensorProduct.tmul_smul, algebraMap_smul]

  have haQp : ∀ i, aQp i = 1 ⊗ₜ[ℚ] (a₀ i) := fun i => Algebra.TensorProduct.basis_apply a₀ i
  have hcQp : ∀ i, cQp i = 1 ⊗ₜ[ℤ_[p]] (c₀ i) := fun i => Algebra.TensorProduct.basis_apply c₀ i

  have hLHS : φ (1 ⊗ₜ[ℚ] (b j)) = ∑ i, (algebraMap ℚ ℚ_[p] (Q i j)) • φ (aQp i) := by
    rw [hb, TensorProduct.tmul_sum]
    simp only [tmul_scalar_A, map_sum, map_smul, haQp]

  have hRHS : (1:ℚ_[p]) ⊗ₜ[ℤ_[p]] (bHp j) = ∑ i, (algebraMap ℤ_[p] ℚ_[p] (P i j)) • cQp i := by
    rw [hbHp, TensorProduct.tmul_sum]
    simp only [tmul_scalar_Hp, hcQp]
  rw [hLHS, hRHS]

  have hφaQp : ∀ i, φ (aQp i) = ∑ k, M k i • cQp k := fun i => by
    have h := Matrix.toLin_self aQp cQp M i
    rw [show Matrix.toLin aQp cQp M = φ.toLinearMap from by
      simp only [M, Matrix.toLin_toMatrix]] at h
    exact h
  simp only [hφaQp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have := congrFun (congrFun hMQ k) j
  simp only [Matrix.mul_apply, Matrix.map_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end S_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
end P2MW
export P2MW.S_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange (solution)
