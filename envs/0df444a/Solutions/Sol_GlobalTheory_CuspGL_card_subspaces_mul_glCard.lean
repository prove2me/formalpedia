-- Prove2me | solution 1 for GlobalTheory.CuspGL.card_subspaces_mul_glCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:37:23.839045+00:00
-- url     : https://prove2.me/submissions/85d35201-75ba-42d9-ba11-a9302c30f0ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCard
import Theorems.Thm_GlobalTheory_CuspGL_card_GL_eq_prod_range
import Theorems.Thm_GlobalTheory_T_card_subspaces_of_finrank_mul_card_bases


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * (Nat.card F : ℂ) ^ (a * (Module.finrank F V - a)) * glCard F a * glCard F (Module.finrank F V - a) = glCard F (Module.finrank F V) := by
  intro F _ _ V _ _ _ a ha
  have h := GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases F V a ha
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le ha
  have hb' : Module.finrank F V - a = b := by omega
  rw [hb']
  rw [hb] at h ⊢
  unfold glCard
  rw [card_GL_eq_prod_range, card_GL_eq_prod_range, card_GL_eq_prod_range]
  have key : Nat.card {W : Submodule F V // Module.finrank F W = a} * Nat.card F ^ (a * b) *
      (∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i)) *
      (∏ i ∈ Finset.range b, (Nat.card F ^ b - Nat.card F ^ i)) =
      ∏ i ∈ Finset.range (a + b), (Nat.card F ^ (a + b) - Nat.card F ^ i) := by
    rw [Finset.prod_range_add, ← h]
    have h2 : ∏ i ∈ Finset.range b, (Nat.card F ^ (a + b) - Nat.card F ^ (a + i)) =
        Nat.card F ^ (a * b) * ∏ i ∈ Finset.range b, (Nat.card F ^ b - Nat.card F ^ i) := by
      simp only [pow_add, ← Nat.mul_sub, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_range, pow_mul]
    rw [h2]
    ring
  exact_mod_cast key
end GlobalTheory.CuspGL
