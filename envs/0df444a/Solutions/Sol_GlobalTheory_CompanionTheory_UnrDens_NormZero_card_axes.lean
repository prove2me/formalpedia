-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormZero.card_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:04.28161+00:00
-- url     : https://prove2.me/submissions/7e26cad4-d148-4071-bfc3-d8d4eca467b3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormZero
theorem _root_.solution {F : Type} [Finite F] (z : F) :
    Nat.card {p : F × F // p.1 = z ∨ p.2 = z} + 1 = 2 * Nat.card F := by
  classical
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (Finset.univ.filter fun p : F × F => p.1 = z ∨ p.2 = z)
      = (({z} : Finset F) ×ˢ (Finset.univ : Finset F)) ∪ ((Finset.univ : Finset F) ×ˢ ({z} : Finset F)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true, true_and]
  have h2 : (({z} : Finset F) ×ˢ (Finset.univ : Finset F)) ∩ ((Finset.univ : Finset F) ×ˢ ({z} : Finset F))
      = {(z, z)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true,
      true_and, Prod.mk.injEq]
  have h3 := Finset.card_union_add_card_inter (({z} : Finset F) ×ˢ (Finset.univ : Finset F))
    ((Finset.univ : Finset F) ×ˢ ({z} : Finset F))
  rw [h2] at h3
  rw [h1]
  simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ, one_mul, mul_one] at h3
  omega
end GlobalTheory.CompanionTheory.UnrDens.NormZero
