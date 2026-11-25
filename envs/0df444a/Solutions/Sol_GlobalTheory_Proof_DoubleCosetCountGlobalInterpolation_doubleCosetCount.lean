-- Prove2me | solution 1 for GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation.doubleCosetCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:05:34.767119+00:00
-- url     : https://prove2.me/submissions/60895b23-5c4a-4d25-9ca7-2503a4da4b18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_StabiliserCardinality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DoubleCosetCount
import Theorems.Thm_GlobalTheory_Proof_DoubleCosetCountGlobalInterpolation_card_fiber_mul_card_stab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
open GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality
namespace GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
theorem _root_.solution : DoubleCosetCount := by
  intro G _ Γ U K hUK hfi _ hfin hfree rep hrep
  have hne : U.relIndex K ≠ 0 := hfi.index_ne_zero
  let π : DoubleCoset.Quotient (Γ : Set G) (U : Set G) →
      DoubleCoset.Quotient (Γ : Set G) (K : Set G) := fun d => DoubleCoset.mk Γ K d.out
  have key : ∀ c, Nat.card {d // π d = c} * Nat.card (stab Γ K (rep c)) = U.relIndex K := by
    intro c
    have := card_fiber_mul_card_stab Γ U K hUK hfree (rep c)
    rw [hrep c] at this
    exact this
  have : ∀ c, Finite {d // π d = c} := fun c =>
    Nat.finite_of_card_ne_zero fun h => hne (by rw [← key c, h, zero_mul])
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv π), ?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs : (Nat.card (stab Γ K (rep c)) : ℚ) ≠ 0 := by
    have := hfin (rep c)
    exact_mod_cast Nat.card_pos.ne'
  rw [← key c]
  push_cast
  field_simp
end GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
