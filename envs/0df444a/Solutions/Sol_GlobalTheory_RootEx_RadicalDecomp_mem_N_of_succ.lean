-- Prove2me | solution 1 for GlobalTheory.RootEx.RadicalDecomp.mem_N_of_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:15.753303+00:00
-- url     : https://prove2.me/submissions/5f49341e-568c-4f90-9084-d10b26493a6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecomposition
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RadicalDecomp
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.RadicalDecomp
theorem _root_.solution {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (p + 1))
    (h0 : ∀ (l : Fin c) (s : n), l.val + 1 = p → g.val (Sum.inr l) (Sum.inl s) = 0) :
    g ∈ N k n c p := by
  rw [mem_N_iff] at hg ⊢
  intro r s hrs
  rcases r with a | l <;> rcases s with b | j
  · exact hg _ _ (by simp [lev])
  · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢; omega)
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    by_cases hp : l.val + 1 = p
    · rw [h0 l b hp]
      simp
    · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega)
  · exact hg _ _ (by simpa [lev] using hrs)
end GlobalTheory.RootEx.RadicalDecomp
