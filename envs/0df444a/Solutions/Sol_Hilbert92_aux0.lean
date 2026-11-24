-- Prove2me | solution 1 for Hilbert92_aux0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:19.927996+00:00
-- url     : https://prove2.me/submissions/238309d2-c5b8-4cb6-9962-1c13eefdb5d6

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
include hKL
theorem _root_.solution (h : ℕ) (ν : (𝓞 k)ˣ) (hν : IsPrimitiveRoot (ν : k) (p ^ h))
    (H : ∀ ε : (𝓞 K)ˣ, algebraMap k K ν ^ (p ^ (h - 1)) ≠ ε / (σ ε : K)) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by
  let η := (Units.map (algebraMap (𝓞 k) (𝓞 K)) ν : (𝓞 K)ˣ)
  use η ^ (p ^ (h - 1))
  refine ⟨?_, H⟩
  simp only [Units.val_pow_eq_pow_val, map_pow]
  change (Algebra.norm k) ((algebraMap k K) _) ^ _ = 1
  rw [Algebra.norm_algebraMap, hKL, ← pow_mul]
  nth_rewrite 1 [← pow_one p]
  rw [← pow_add]
  apply (hν.pow_eq_one_iff_dvd _).2
  cases h <;> simp [add_comm]
