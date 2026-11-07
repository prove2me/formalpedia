-- Prove2me | solution 1 for NaturalProofs.expand_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:54.424958+00:00
-- url     : https://prove2.me/submissions/bc890d0d-cec7-4edd-aed6-3191db635c2a

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_expand_injective

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
namespace NaturalProofs
theorem _root_.solution (k i : ℕ) :
    Function.Bijective (expand : ((Fin i → Bool) → Fin (2 * k) → Bool) → _ → Bits k) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨expand_injective k i, ?_⟩
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul, ← pow_mul, pow_succ]
  ring_nf
end NaturalProofs
