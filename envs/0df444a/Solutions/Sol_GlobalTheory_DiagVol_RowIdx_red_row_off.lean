-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.red_row_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:04:35.80982+00:00
-- url     : https://prove2.me/submissions/a6231650-5cb6-4d8f-9619-50a2aca37915

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_red_incl_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.DiagVol GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.DiagVol.RowIdx
theorem _root_.solution {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) {t : ι} {S : Finset ι}
    (hrow : ∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) (z : H) (s : ι) (hs : s ∉ S) :
    (red (Subgroup.inclusion hHK z)).val t s = (1 : Matrix ι ι 𝓀[k]) t s := by
  have hint := ((mem_KO_iff _).1 (hHK z.2)).1 t s
  rw [red_incl_val hHK z t s hint]
  have e : (⟨z.1.val t s, hint⟩ : 𝒪[k]) = (1 : Matrix ι ι 𝒪[k]) t s := by
    apply Subtype.ext
    show z.1.val t s = _
    rw [hrow z.1 z.2 s hs]
    by_cases h : t = s <;> simp [Matrix.one_apply, h]
  rw [e]
  by_cases h : t = s <;> simp [Matrix.one_apply, h]
end GlobalTheory.DiagVol.RowIdx
