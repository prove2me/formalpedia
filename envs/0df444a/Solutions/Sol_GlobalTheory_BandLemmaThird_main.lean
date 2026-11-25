-- Prove2me | solution 1 for GlobalTheory.BandLemmaThird.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:26:32.840962+00:00
-- url     : https://prove2.me/submissions/d23972a9-16df-4b1a-8eec-dfd0ebea7423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.BandLemmaThird
namespace GlobalTheory.BandLemmaThird
theorem _root_.solution : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [inst_1 : Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {i j : ℕ} {X Y : Matrix ι ι k}, d1 ℓ i X → d1 ℓ j Y → d1 ℓ (i + j) (X * Y)) := by
  intro d1 k _ ι _ _ ℓ i j X Y hX hY r s hrs
  show (X * Y) r s = 0
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases h : ℓ t < ℓ r + i
  · rw [hX r t h, zero_mul]
  · rw [hY t s (by omega), mul_zero]
end GlobalTheory.BandLemmaThird
