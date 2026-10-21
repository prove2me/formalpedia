-- Prove2me | solution 1 for HScattered.Hyperplanes.hCount_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:13:28.076623+00:00
-- url     : https://prove2.me/submissions/71ee1253-70e8-4ecd-bc06-0eb5f49ef47d

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

set_option autoImplicit false

open HScattered.Hyperplanes

lemma hyp_inter_lb {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (U : Submodule F V) (W : Submodule K V)
    (hW : Module.finrank K W = Module.finrank K V - 1) (hr : 0 < Module.finrank K V) :
    Module.finrank F U ≤ Module.finrank F ↥(W.restrictScalars F ⊓ U) + Module.finrank F K := by
  have : Module.Finite F K := Module.Finite.of_finite
  have : Module.Finite F V := Module.Finite.trans K V
  have h1 : Module.finrank F V = Module.finrank K V * Module.finrank F K :=
    by rw [← Module.finrank_mul_finrank F K V, mul_comm]
  have h2 : Module.finrank F ↥(W.restrictScalars F) = Module.finrank K W * Module.finrank F K := by
    have h2' : Module.finrank F ↥(W.restrictScalars F) = Module.finrank F ↥W := rfl
    rw [h2', ← Module.finrank_mul_finrank F K W, mul_comm]
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (W.restrictScalars F) U
  have h4 : Module.finrank F ↥(W.restrictScalars F ⊔ U) ≤ Module.finrank F V :=
    Submodule.finrank_le _
  have h5 : Module.finrank K V * Module.finrank F K =
      Module.finrank K W * Module.finrank F K + Module.finrank F K := by
    rw [hW]
    obtain ⟨r, hr'⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    rw [hr']; simp [Nat.succ_mul]
  omega

theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (i : ℕ) (hi : i + Module.finrank F K < Module.finrank F U) :
    hCount F K U i = 0 := by
  unfold hCount
  have : IsEmpty {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1 ∧
      Module.finrank F ↥(W.restrictScalars F ⊓ U) = i} := by
    constructor
    rintro ⟨W, hW, hWi⟩
    have := hyp_inter_lb U W hW (by have := hU.2.1; omega)
    omega
  exact Nat.card_of_isEmpty
