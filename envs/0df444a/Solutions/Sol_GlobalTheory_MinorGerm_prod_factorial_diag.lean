-- Prove2me | solution 1 for GlobalTheory.MinorGerm.prod_factorial_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:08.616099+00:00
-- url     : https://prove2.me/submissions/773a6f51-2277-40f7-b12f-d70a6f61f248

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_monAl_eq_zero

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
theorem _root_.solution (e : ℕ → ℕ) :
    ∏ x : Fin N × Fin N', (if x.1.val = x.2.val then monAl N N' e x.1.val else 0).factorial =
      ∏ ρ : Fin N, (monAl N N' e ρ.val).factorial := by
  classical
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro b _
  by_cases hb : b.val < N'
  · rw [Finset.prod_eq_single ⟨b.val, hb⟩]
    · simp
    · intro c _ hc
      rw [if_neg, Nat.factorial_zero]
      intro h
      exact hc (Fin.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [monAl_eq_zero e hb, Nat.factorial_zero]
    apply Finset.prod_eq_one
    intro c _
    rw [if_neg, Nat.factorial_zero]
    intro h
    have h' : b.val = c.val := h
    exact hb (by rw [h']; exact c.isLt)
end GlobalTheory.MinorGerm
