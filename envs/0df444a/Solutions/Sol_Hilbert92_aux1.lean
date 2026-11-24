-- Prove2me | solution 1 for Hilbert92_aux1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:22.401935+00:00
-- url     : https://prove2.me/submissions/096f1488-c785-4799-b647-55397c030c86

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92

set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
variable [NumberField K]
include hKL
theorem _root_.solution (n : ℕ) (H : Fin n → Additive (𝓞 K)ˣ) (ν : (𝓞 k)ˣ)
    (a : ℤ) (ι : Fin n → ℤ) (η : Fin n → Additive (𝓞 k)ˣ)
    (ha : ∑ i : Fin n, ι i • η i = (a * ↑↑p) • Additive.ofMul ν)
    (hη :
      ∀ i, Additive.toMul (η i) = Algebra.norm k (S := K) ((Additive.toMul (H i) : _) : K)) :
    letI J : (𝓞 K)ˣ := (Additive.toMul (∑ i : Fin n, ι i • H i)) *
      (Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ν) ^ (-a)
    Algebra.norm k (S := K) ((J : (𝓞 K)ˣ) : K) = 1 := by
  have h := congrArg (fun x : Additive (𝓞 k)ˣ ↦ ((↑(Additive.toMul x) : 𝓞 k) : k)) ha
  simp only [toMul_sum, toMul_zsmul, Units.coe_prod, map_prod, Units.coe_zpow,
    toMul_ofMul, hη] at h
  simp only [toMul_sum, toMul_zsmul, Units.val_mul, Units.coe_prod, map_prod,
    Units.coe_zpow, map_mul, Algebra.norm_zpow]
  rw [h]
  change (ν : k) ^ (a * (p : ℤ)) * (Algebra.norm k) (algebraMap k K ν) ^ (-a) = 1
  rw [Algebra.norm_algebraMap, hKL, ← zpow_natCast, ← zpow_mul, mul_comm (p : ℤ),
    neg_mul, zpow_neg, mul_inv_cancel₀]
  exact zpow_ne_zero _ (by simp)
