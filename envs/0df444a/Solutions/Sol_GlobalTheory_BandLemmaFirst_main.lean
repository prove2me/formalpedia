-- Prove2me | solution 1 for GlobalTheory.BandLemmaFirst.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:35:53.551088+00:00
-- url     : https://prove2.me/submissions/587187d7-c00d-42a4-aa1f-5a7cb14a9645

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.BandLemmaFirst
namespace GlobalTheory.BandLemmaFirst
theorem _root_.solution :
    (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop :=
      @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦
        ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k));
    ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {j : ℕ}
      {X Y : Matrix ι ι k}, d1 ℓ j X → d1 ℓ j Y → d1 ℓ j (X + Y)) := by
  intro d1 k _ ι _ _ ℓ j X Y hX hY r s h
  show (X + Y) r s = 0
  rw [Matrix.add_apply, hX r s h, hY r s h, add_zero]
end GlobalTheory.BandLemmaFirst
