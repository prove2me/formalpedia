-- Prove2me | solution 1 for Hilbert92
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:57.914719+00:00
-- url     : https://prove2.me/submissions/3d24af59-24ea-4b4b-a1af-dbfc4e7802f5

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_almostHilbert92

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
theorem _root_.solution [Algebra k K] [IsGalois k K] [NumberField k] [NumberField K]
    (hKL : Nat.Prime (finrank k K)) (hpodd : finrank k K ≠ 2)
    (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) :=
  have := IsUnramifiedAtInfinitePlaces_of_odd_finrank (hKL.odd_of_ne_two hpodd)
  have : IsCyclic (K ≃ₐ[k] K) := ⟨σ, hσ⟩
  almostHilbert92 (finrank k K) hKL rfl σ hσ hpodd
