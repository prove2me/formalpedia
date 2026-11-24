-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.corner_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:50.763869+00:00
-- url     : https://prove2.me/submissions/accf2da5-0820-4555-a2a0-7b5c47aa2562

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_mul_row_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution (hH : Heis) (hU : IsUnramInv ϖ σ q) {e f : ℕ} {C D : Matrix (Fin N) (Fin N) L}
    {u w : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hw : w ∈ radQ σ N) (h0 : rowOf w = 0)
    (hs : Small ϖ e f C D u) (hs' : Small ϖ e f C D (u * w)) : ϖ ^ f * cornerOf w ∈ intL L := by
  obtain ⟨hr, hc, hk⟩ := mul_row_zero hH hU hu hw h0
  unfold GlobalTheory.InertZeta.Small at hs hs'
  have h2 := hs'.2
  rw [hr, hc, hk] at h2
  have e : ϖ ^ f * cornerOf w = ϖ ^ f * (cornerOf u + cornerOf w - rowOf u ⬝ᵥ D *ᵥ colOf u)
      - ϖ ^ f * (cornerOf u - rowOf u ⬝ᵥ D *ᵥ colOf u) := by ring
  rw [e]
  exact sub_mem h2 hs.2
end GlobalTheory.CompanionTheory.InertCount
