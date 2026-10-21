-- Prove2me | solution 1 for HScattered.Hyperplanes.eq_23
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:08:39.836979+00:00
-- url     : https://prove2.me/submissions/e44d09d0-43bd-44fa-993e-e22a31e2df06

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

set_option autoImplicit false

open HScattered.Hyperplanes

lemma hyp_count (K V : Type*) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hr : 0 < Module.finrank K V) :
    Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} *
        (Nat.card K - 1) = Nat.card K ^ Module.finrank K V - 1 := by
  have e : {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} ≃
      Projectivization K (Module.Dual K V) :=
    (Equiv.subtypeEquiv ((Subspace.orderIsoFiniteDimensional (K := K) (V := V)).toEquiv.trans
        OrderDual.ofDual) (p := fun W : Submodule K V => Module.finrank K W = Module.finrank K V - 1)
      (q := fun Φ : Submodule K (Module.Dual K V) => Module.finrank K Φ = 1) (by
        intro W
        have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
        show _ ↔ Module.finrank K W.dualAnnihilator = 1
        omega)).trans (Projectivization.equivSubmodule K (Module.Dual K V)).symm
  rw [Nat.card_congr e]
  have h1 := Projectivization.card K (Module.Dual K V)
  have h2 : Nat.card (Module.Dual K V) = Nat.card K ^ Module.finrank K V := by
    rw [Module.natCard_eq_pow_finrank (K := K), Subspace.dual_finrank_eq]
  rw [h2] at h1
  exact h1.symm

lemma sum_hCount {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V] (U : Submodule F V) :
    ∑ i ∈ Finset.range (Module.finrank F U + 1), HScattered.Hyperplanes.hCount F K U i =
      Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} := by
  classical
  haveI : Module.Finite F K := Module.Finite.of_finite
  haveI : Module.Finite F V := Module.Finite.trans K V
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (Submodule K V) :=
    Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype (Submodule K V) := Fintype.ofFinite _
  set g : Submodule K V → ℕ := fun W => Module.finrank F ↥(W.restrictScalars F ⊓ U) with hg
  set Hs : Finset (Submodule K V) :=
    Finset.univ.filter (fun W => Module.finrank K W = Module.finrank K V - 1) with hHs
  have hcard : Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} =
      Hs.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfib : ∀ i, HScattered.Hyperplanes.hCount F K U i = (Hs.filter (fun W => g W = i)).card := by
    intro i
    unfold HScattered.Hyperplanes.hCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext W
    simp [hHs, hg]
  rw [hcard, Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.range (Module.finrank F U + 1))]
  · exact Finset.sum_congr rfl (fun i _ => hfib i)
  · intro W _
    simp only [Finset.coe_range, Set.mem_Iio, hg]
    have : Module.finrank F ↥(W.restrictScalars F ⊓ U) ≤ Module.finrank F U :=
      Submodule.finrank_mono inf_le_right
    omega

theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K) :
    ∑ i ∈ Finset.range (Module.finrank F U + 1),
        (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) =
      (Fintype.card F : ℤ) ^ (Module.finrank K V * Module.finrank F K) - 1 := by
  have hr : 0 < Module.finrank K V := by have := hU.2.1; omega
  have h1 := hyp_count K V hr
  have h2 := sum_hCount (F := F) (K := K) U
  have hK : Nat.card K = Fintype.card F ^ Module.finrank F K := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := K)]
  rw [← Finset.sum_mul, ← Nat.cast_sum, h2]
  have h3 : (Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} : ℤ) *
      ((Nat.card K : ℤ) - 1) = (Nat.card K : ℤ) ^ Module.finrank K V - 1 := by
    have h4 : 1 ≤ Nat.card K := Nat.card_pos
    have h5 : 1 ≤ Nat.card K ^ Module.finrank K V := Nat.one_le_pow _ _ h4
    have := congrArg (fun n : ℕ => (n : ℤ)) h1
    simp only [Nat.cast_mul, Nat.cast_sub h4, Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at this
    exact this
  rw [hK] at h3
  push_cast at h3
  rw [h3, ← pow_mul, mul_comm (Module.finrank F K)]
