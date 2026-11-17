-- Prove2me | solution 1 for HScattered.Bound.result_4_6
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T14:55:43.853253+00:00
-- url     : https://prove2.me/submissions/7b1b5ec8-e578-4232-a629-d484f73b5f23

import Mathlib

theorem solution {F X Y : Type*} [Field F] [Fintype F]
    [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
    (m n d : ℕ) (hm : Module.finrank F X = m) (hn : Module.finrank F Y = n) (hnm : n ≤ m)
    (C : Finset (X →ₗ[F] Y)) (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (hC : ∀ f ∈ C, ∀ g ∈ C, f ≠ g → d ≤ Module.finrank F (LinearMap.range (f - g))) :
    C.card ≤ Fintype.card F ^ (m * (n - d + 1)) := by
  classical
  subst hm
  subst hn
  have hdY : d - 1 ≤ Module.finrank F Y := by omega
  let b := Module.finBasis F Y
  let s : Set (Fin (Module.finrank F Y)) := {i | (i : ℕ) < d - 1}
  let U : Submodule F Y :=
    Submodule.span F (Set.range (fun i : s => b (i : Fin (Module.finrank F Y))))
  have hlin : LinearIndependent F (fun i : s => b (i : Fin (Module.finrank F Y))) :=
    b.linearIndependent.comp (fun i : s => (i : Fin (Module.finrank F Y))) Subtype.val_injective
  have hcard_s : Fintype.card s = d - 1 := by
    have hc : Fintype.card s = Fintype.card (Fin (d - 1)) := by
      apply Fintype.card_congr
      exact
        { toFun := fun i => ⟨(i.1 : ℕ), i.2⟩
          invFun := fun j => ⟨⟨(j : ℕ), lt_of_lt_of_le j.2 hdY⟩, j.2⟩
          left_inv := by intro i; rfl
          right_inv := by intro j; rfl }
    simpa using hc
  have hU : Module.finrank F U = d - 1 := by
    have h1 : Module.finrank F U = Fintype.card s :=
      finrank_span_eq_card hlin
    rw [h1, hcard_s]
  have hq : Module.finrank F (Y ⧸ U) = Module.finrank F Y - d + 1 := by
    have h := Submodule.finrank_quotient_add_finrank U
    rw [hU] at h
    omega
  have hinj : ∀ f ∈ C, ∀ g ∈ C,
      (Submodule.mkQ U).comp f = (Submodule.mkQ U).comp g → f = g := by
    intro f hf g hg heq
    by_contra hne
    have hle : LinearMap.range (f - g) ≤ U := by
      rintro y ⟨x, rfl⟩
      have h1 : (Submodule.mkQ U) (f x) = (Submodule.mkQ U) (g x) := by
        have h2 := (LinearMap.ext_iff.mp heq) x
        simpa [LinearMap.comp_apply] using h2
      have h0 : (Submodule.mkQ U) ((f - g) x) = 0 := by
        rw [LinearMap.sub_apply, map_sub, h1, sub_self]
      have hmem : (f - g) x ∈ LinearMap.ker (Submodule.mkQ U) := by
        rw [LinearMap.mem_ker]
        exact h0
      rwa [Submodule.ker_mkQ] at hmem
    have hd : d ≤ Module.finrank F (LinearMap.range (f - g)) := hC f hf g hg hne
    have hmono : Module.finrank F (LinearMap.range (f - g)) ≤ Module.finrank F U :=
      Submodule.finrank_mono hle
    omega
  have hcard : C.card ≤ Nat.card (X →ₗ[F] (Y ⧸ U)) := by
    haveI hFinF : Finite F := Finite.of_fintype F
    haveI hFinHom : Finite (X →ₗ[F] (Y ⧸ U)) := Module.finite_of_finite F
    have hinj' : Function.Injective
        (fun f : ↥C => (Submodule.mkQ U).comp (f : X →ₗ[F] Y)) := by
      intro f g hfg
      exact Subtype.ext (hinj f.1 f.2 g.1 g.2 hfg)
    have h1 : Nat.card ↥C ≤ Nat.card (X →ₗ[F] (Y ⧸ U)) :=
      Nat.card_le_card_of_injective _ hinj'
    have h2 : Nat.card ↥C = C.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    omega
  have hnat : Nat.card (X →ₗ[F] (Y ⧸ U)) =
      Fintype.card F ^ (Module.finrank F X * (Module.finrank F Y - d + 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := F),
      Module.finrank_linearMap F F X (Y ⧸ U), hq, Nat.card_eq_fintype_card]
  rw [← hnat]
  exact hcard
