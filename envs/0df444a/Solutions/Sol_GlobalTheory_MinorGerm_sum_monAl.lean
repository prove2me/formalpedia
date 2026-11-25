-- Prove2me | solution 1 for GlobalTheory.MinorGerm.sum_monAl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:02:50.683285+00:00
-- url     : https://prove2.me/submissions/534f7e3c-edff-47df-8bfc-7e62141bfd63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_monAl_eq
import Theorems.Thm_GlobalTheory_MinorGerm_sum_range_ite

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
namespace GlobalTheory.MinorGerm
theorem _root_.solution (e : ℕ → ℕ) : ∑ ρ : Fin N, monAl N N' e ρ.val = monDeg N N' e := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun ρ => monAl N N' e ρ) N]
  simp only [monAl_eq]
  rw [Finset.sum_comm]
  unfold monDeg
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [sum_range_ite (by omega : k ≤ N) (fun _ => e k), Finset.sum_const, Finset.card_range, smul_eq_mul]
end GlobalTheory.MinorGerm
