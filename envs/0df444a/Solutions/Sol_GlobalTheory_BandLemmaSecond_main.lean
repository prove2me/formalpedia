-- Prove2me | solution 1 for GlobalTheory.BandLemmaSecond.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:31:47.716261+00:00
-- url     : https://prove2.me/submissions/4f22de92-3eac-4942-b80e-41b3230e8139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.BandLemmaSecond
namespace GlobalTheory.BandLemmaSecond
theorem _root_.solution : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {j : ℕ} {X : Matrix ι ι k}, d1 ℓ j X → d1 ℓ j (-X)) := by
  intro d1 k _ ι _ _ ℓ j X h r s hrs
  simp only [Matrix.neg_apply, h r s hrs, neg_zero]
end GlobalTheory.BandLemmaSecond
