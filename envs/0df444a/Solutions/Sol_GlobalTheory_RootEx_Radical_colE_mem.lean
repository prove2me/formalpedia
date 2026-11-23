-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.colE_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:06.394077+00:00
-- url     : https://prove2.me/submissions/edd1afab-f0a2-4791-9d7d-067e5008c611

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.Radical
theorem _root_.solution {i : ℕ} (β : n → k) (hi : p < i) : colE c i β ∈ N k n c p := by
  rw [mem_N_iff]
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [colE, upU, Matrix.one_apply]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : ¬ (s.val + 1 = i) := by omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]
end GlobalTheory.RootEx.Radical
