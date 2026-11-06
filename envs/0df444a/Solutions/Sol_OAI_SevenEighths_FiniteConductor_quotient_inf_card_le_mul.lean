-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.quotient_inf_card_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:13:25.634818+00:00
-- url     : https://prove2.me/submissions/0c240d8a-7a79-4573-a70d-937c384be760

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
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (I J : Ideal R) [Finite (R ⧸ I)] [Finite (R ⧸ J)] :
    Nat.card (R ⧸ I ⊓ J) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  let f : R ⧸ I ⊓ J →+* (R ⧸ I) × (R ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf
end OAI.SevenEighths.FiniteConductor
