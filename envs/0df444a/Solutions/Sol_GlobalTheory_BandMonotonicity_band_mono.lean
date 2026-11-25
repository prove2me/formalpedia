-- Prove2me | solution 1 for GlobalTheory.BandMonotonicity.band_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:26:40.415872+00:00
-- url     : https://prove2.me/submissions/f07893e4-a62e-4d2d-8473-a00f931ceca0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BandMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.BandMonotonicity
namespace GlobalTheory.BandMonotonicity
theorem _root_.solution :
    (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop :=
      @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦
        ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k));
    ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ}
      {i j : ℕ} {X : Matrix ι ι k}, d1 ℓ j X → i ≤ j → d1 ℓ i X) := by
  intro d1 k _ ι _ _ ℓ i j X h hij r s hrs
  exact h r s (by omega)
end GlobalTheory.BandMonotonicity
