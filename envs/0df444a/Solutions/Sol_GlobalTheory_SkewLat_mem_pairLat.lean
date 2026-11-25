-- Prove2me | solution 1 for GlobalTheory.SkewLat.mem_pairLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:51.915953+00:00
-- url     : https://prove2.me/submissions/df5236ee-57f1-4d5e-b6e6-cf8f5c8bc67f

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
theorem _root_.solution {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}
    {e : Fin a ⊕ Fin b ≃ Fin d} {x : Fin d → E} :
    x ∈ pairLat ΛA ΛB e ↔ (fun k => x (e (.inl k))) ∈ ΛA ∧ (fun k => x (e (.inr k))) ∈ ΛB := Iff.rfl
end GlobalTheory.SkewLat
