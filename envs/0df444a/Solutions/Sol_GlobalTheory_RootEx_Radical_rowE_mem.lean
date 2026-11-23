-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.rowE_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:08.697519+00:00
-- url     : https://prove2.me/submissions/5068b765-4988-4cf8-97a1-698b6feda181

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
theorem _root_.solution {l : ℕ} (u : n → k) (hl : l < p) : rowE c l u ∈ N k n c p := by
  rw [mem_N_iff]
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [rowE, lowU, Matrix.one_apply]
  · simp [rowE, lowU]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : ¬ (r.val + 1 = l) := by omega
    simp [rowE, lowU, this]
  · simp [rowE, lowU, Matrix.one_apply]
end GlobalTheory.RootEx.Radical
