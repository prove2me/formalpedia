-- Prove2me | solution 1 for GlobalTheory.MinorGerm.dg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:31.729567+00:00
-- url     : https://prove2.me/submissions/dddb6a08-07f5-4ba6-bf5d-3254d190d9c3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
theorem _root_.solution (j : Fin N × Fin N' → σ) (hj : Function.Injective j) (f : ℕ → ℕ)
    (b : Fin N) (c : Fin N') : dg j f (j (b, c)) = if b.val = c.val then f b.val else 0 := by
  classical
  unfold dg
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b.val]
  · unfold dgOne
    by_cases hbc : b.val = c.val
    · rw [if_pos hbc, dif_pos ⟨b.isLt, by rw [hbc]; exact c.isLt⟩, Finsupp.single_apply,
        if_pos (by congr 1; exact Prod.ext (Fin.ext rfl) (Fin.ext hbc))]
    · rw [if_neg hbc]
      split_ifs with h
      · rw [Finsupp.single_apply, if_neg]
        intro he
        have h' := congrArg (fun x => x.2.val) (hj he)
        exact hbc (by simpa using h')
      · rfl
  · intro ρ _ hρ
    unfold dgOne
    split_ifs with h
    · rw [Finsupp.single_apply, if_neg]
      intro he
      have h' := congrArg (fun x => x.1.val) (hj he)
      exact hρ (by simpa using h')
    · rfl
  · intro hb
    exact absurd (Finset.mem_range.2 b.isLt) hb
end GlobalTheory.MinorGerm
