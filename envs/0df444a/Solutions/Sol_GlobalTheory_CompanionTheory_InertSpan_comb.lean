-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:00:44.779804+00:00
-- url     : https://prove2.me/submissions/82a4bb5e-6799-4cf3-985a-3388730af50e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_sum_smul_blockVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertSpan
theorem _root_.solution (R : Submodule (intL L) (Fin (N + 2) → L)) {X : Matrix (Fin N) (Fin N) L} (hX : IsInt X)
    (M : Matrix (Fin N) (Fin N) L) (s : Fin N → L) (h : ∀ k, vec3 (0 : L) (M k) (s k) ∈ R) (i : Fin N) :
    vec3 (0 : L) ((X * M) i) ((X *ᵥ s) i) ∈ R := by
  have e : vec3 (0 : L) ((X * M) i) ((X *ᵥ s) i) = ∑ k, X i k • vec3 (0 : L) (M k) (s k) := by
    rw [sum_smul_blockVector]
    rfl
  rw [e]
  exact R.sum_mem fun k _ => R.smul_mem ⟨X i k, hX i k⟩ (h k)
end GlobalTheory.CompanionTheory.InertSpan
