-- Prove2me | solution 1 for GlobalTheory.MinorGerm.dg_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:26.004437+00:00
-- url     : https://prove2.me/submissions/6429436a-21b8-4020-aafa-9cf62b186102

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
theorem _root_.solution (j : Fin N × Fin N' → σ) (f : ℕ → ℕ) (x : σ) (hx : ∀ y, x ≠ j y) :
    dg j f x = 0 := by
  classical
  unfold dg
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro ρ _
  unfold dgOne
  split_ifs
  · rw [Finsupp.single_apply, if_neg (fun h => hx _ h.symm)]
  · rfl
end GlobalTheory.MinorGerm
