-- Prove2me | solution 2 for OAI.SevenEighths.FiniteConductor.quotient_inf_card_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:54.128561+00:00
-- url     : https://prove2.me/submissions/c77db9c6-782e-41e7-a199-a43a418f0a91

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R]

theorem solution (I J : Ideal R) [Finite (R ⧸ I)] [Finite (R ⧸ J)] :
    Nat.card (R ⧸ I ⊓ J) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  rw [← Nat.card_prod]
  let f : R ⧸ I ⊓ J →+* (R ⧸ I) × (R ⧸ J) :=
    Ideal.Quotient.lift (I ⊓ J) ((Ideal.Quotient.mk I).prod (Ideal.Quotient.mk J)) (by
      intro a ha
      exact Prod.ext (Ideal.Quotient.eq_zero_iff_mem.mpr ha.1)
        (Ideal.Quotient.eq_zero_iff_mem.mpr ha.2))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 := congrArg Prod.fst hx
    have h2 := congrArg Prod.snd hx
    simp only [f, Ideal.Quotient.lift_mk, RingHom.prod_apply] at h1 h2
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ⟨Ideal.Quotient.eq_zero_iff_mem.mp h1, Ideal.Quotient.eq_zero_iff_mem.mp h2⟩
  haveI : Finite ((R ⧸ I) × (R ⧸ J)) := inferInstance
  exact Nat.card_le_card_of_injective _ hf
