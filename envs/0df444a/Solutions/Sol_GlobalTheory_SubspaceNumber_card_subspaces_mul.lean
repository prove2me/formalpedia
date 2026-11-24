-- Prove2me | solution 1 for GlobalTheory.SubspaceNumber.card_subspaces_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:11:55.054379+00:00
-- url     : https://prove2.me/submissions/eba858f6-3bf3-4bbe-8c99-7f42af5896d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBases
import Theorems.Thm_GlobalTheory_SubspaceNumber_card_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.SubspaceNumber
namespace GlobalTheory.SubspaceNumber
theorem _root_.solution :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V →
      Nat.card {W : Submodule F V // Module.finrank F W = a} *
        ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) =
      ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by
  intro F _ _ V _ _ _ a ha
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // Module.finrank F W = a} := Fintype.ofFinite _
  let f : {s : Fin a → V // LinearIndependent F s} →
      {W : Submodule F V // Module.finrank F W = a} := fun s =>
    ⟨Submodule.span F (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩
  have hfib : ∀ W, Nat.card {s // f s = W} =
      ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) := by
    rintro ⟨W, hW⟩
    have e : {s // f s = ⟨W, hW⟩} ≃ {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} :=
      Equiv.subtypeEquivRight (fun s => Subtype.ext_iff)
    rw [Nat.card_congr e, card_fibre a W hW, card_linearIndependent hW.ge, hW,
      Finset.prod_range, Nat.card_eq_fintype_card]
  have h := card_linearIndependent (K := F) (V := V) ha
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma] at h
  simp_rw [hfib] at h
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  rw [h, Finset.prod_range]
end GlobalTheory.SubspaceNumber
