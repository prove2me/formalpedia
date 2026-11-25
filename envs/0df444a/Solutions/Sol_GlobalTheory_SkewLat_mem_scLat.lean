-- Prove2me | solution 1 for GlobalTheory.SkewLat.mem_scLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:55.112805+00:00
-- url     : https://prove2.me/submissions/257291c9-d560-4c89-bd20-7d31fecf53f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPairLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SkewLat
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SkewLat
theorem _root_.solution {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} :
    y ∈ scLat 𝔞 Λ ↔ ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ := Iff.rfl
end GlobalTheory.SkewLat
