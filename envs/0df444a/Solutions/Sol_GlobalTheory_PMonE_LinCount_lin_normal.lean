-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.lin_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:17:25.847718+00:00
-- url     : https://prove2.me/submissions/ef5b6ef4-9978-4cfe-acd1-efb8093eb354

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
namespace GlobalTheory.PMonE.LinCount
theorem _root_.solution (K : ℕ) (M : ℕ → Matrix m m F) (h : Normal (K + 1) M) : Normal 1 (lin K M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n r c
    unfold lin
    split_ifs <;> first | exact h.int _ _ _ | simp
  · ext ⟨i, a⟩ ⟨j, b⟩
    have h1 : M (1 + K) = 1 := by rw [add_comm]; exact h.top
    by_cases hi : i = Fin.last K
    · subst hi
      by_cases hj : j = Fin.last K
      · subst hj
        simp [lin, h1, Matrix.one_apply]
      · simp [lin, hj, Matrix.one_apply, Ne.symm hj]
    · simp [lin, hi, Matrix.one_apply]
  · intro n hn r c
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp only [lin, h0, h1, if_false]
    split_ifs
    · exact h.small _ (by omega) _ _
    · simp
    · simp
end GlobalTheory.PMonE.LinCount
