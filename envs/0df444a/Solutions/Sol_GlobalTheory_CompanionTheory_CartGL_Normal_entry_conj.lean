-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.Normal.entry_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:43.319799+00:00
-- url     : https://prove2.me/submissions/54350884-019b-4834-b11d-a26fcfb93427

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompact
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.Normal
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartGL.Normal
theorem _root_.solution {C D X : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hC : ∀ i j, ‖C i j‖ ≤ 1) (hD : ∀ i j, ‖D i j‖ ≤ 1) (hCD : C * D = 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ r) (i j : Fin n) : ‖(C * X * D - 1) i j‖ ≤ r := by
  have e : C * X * D - 1 = C * (X - 1) * D := by
    rw [mul_sub, sub_mul, mul_one, hCD]
  rw [e]
  have h := entry_mul (mul_nonneg zero_le_one h0) zero_le_one
    (entry_mul zero_le_one h0 hC hX) hD i j
  simpa using h
end GlobalTheory.CompanionTheory.CartGL.Normal
