-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.small_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:51.982888+00:00
-- url     : https://prove2.me/submissions/7385b435-ef48-4edb-827f-ef9ee50863f5

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
    (hs : Small ϖ e f C D u) (hx : ϖ ^ f * cornerOf w ∈ intL L) : Small ϖ e f C D (u * w) := by
  obtain ⟨hr, hc, hk⟩ := mul_row_zero hH hU hu hw h0
  unfold GlobalTheory.InertZeta.Small at hs ⊢
  obtain ⟨hs1, hs2⟩ := hs
  refine ⟨fun j => by rw [hr]; exact hs1 j, ?_⟩
  rw [hr, hc, hk]
  have e : ϖ ^ f * (cornerOf u + cornerOf w - rowOf u ⬝ᵥ D *ᵥ colOf u)
      = ϖ ^ f * (cornerOf u - rowOf u ⬝ᵥ D *ᵥ colOf u) + ϖ ^ f * cornerOf w := by ring
  rw [e]
  exact add_mem hs2 hx
end GlobalTheory.CompanionTheory.InertCount
