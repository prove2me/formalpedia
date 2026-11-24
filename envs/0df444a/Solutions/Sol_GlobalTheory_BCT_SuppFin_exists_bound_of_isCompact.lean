-- Prove2me | solution 1 for GlobalTheory.BCT.SuppFin.exists_bound_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:28.424152+00:00
-- url     : https://prove2.me/submissions/b3bee644-ee67-414e-a061-3e2f12044ae2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompact
import Theorems.Thm_GlobalTheory_BCT_SuppFin_isOpen_vle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
noncomputable section
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.SuppFin
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.BCT.SuppFin
theorem _root_.solution (w : HeightOneSpectrum (𝓞 E)) {K : Set (w.adicCompletion E)}
    (hK : IsCompact K) : ∃ N : ℤ, ∀ z ∈ K, Valued.v z ≤ WithZero.exp N := by
  have hcov : K ⊆ ⋃ N : ℤ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp N} := by
    intro z _
    rw [Set.mem_iUnion]
    by_cases hz : Valued.v z = 0
    · exact ⟨0, by simp [hz]⟩
    · exact ⟨WithZero.log (Valued.v z), by simp [WithZero.exp_log hz]⟩
  obtain ⟨N, hN⟩ := hK.elim_directed_cover _ (fun N => isOpen_vle w N) hcov
    (Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 hab))
  exact ⟨N, fun z hz => hN hz⟩
end GlobalTheory.BCT.SuppFin
