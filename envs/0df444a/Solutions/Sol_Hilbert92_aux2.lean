-- Prove2me | solution 1 for Hilbert92_aux2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:14.729349+00:00
-- url     : https://prove2.me/submissions/47653f2b-a7cc-4d96-86c6-c0494160a13a

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_norm_eq_prod_pow_gen

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
variable [IsGalois k K]
attribute [local instance] _p2m_local_instance_fee6646a52_507
attribute [local instance] _p2m_local_instance_fee6646a52_512
attribute [local instance] _p2m_local_instance_fee6646a52_515
include hKL hσ hp
theorem _root_.solution (E : (𝓞 K)ˣ) (ν : k) (hE : algebraMap k K ν = E / σ E)
  (hν : (ν : k) ^ p = 1) (hpodd : p ≠ 2) :
    algebraMap k K (Algebra.norm k (S := K) E) = E ^ p := by
  have h1 : ∀ (i : ℕ), (σ ^ i) E = ((algebraMap k K ν)⁻¹)^i * E := by
    intro i
    induction i with
    | zero =>
      simp only [pow_zero, AlgEquiv.one_apply, one_mul]
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ']
      simp only [inv_pow, map_mul, map_inv₀, map_pow, AlgEquiv.commutes]
      have h0 : algebraMap k K ν ≠ 0 := fun h ↦ by
        simp [(map_eq_zero _).1 h, hp.ne_zero] at hν
      rw [hE]
      field_simp
  rw [norm_eq_prod_pow_gen σ hσ, orderOf_eq_card_of_forall_mem_zpowers hσ,
    IsGalois.card_aut_eq_finrank, hKL]
  conv =>
    enter [1, 2, i]
    rw [h1 i, mul_comm]
  rw [prod_mul_distrib, prod_const, card_range, prod_pow_eq_pow_sum, inv_pow, mul_eq_left₀,
    inv_eq_one, sum_range_id, Nat.mul_div_assoc, pow_mul, ← map_pow, hν, map_one, one_pow]
  · exact even_iff_two_dvd.1 (hp.even_sub_one hpodd)
  · simp
