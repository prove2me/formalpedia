-- Prove2me | solution 1 for GlobalTheory.FlagHook.Degree.sum_permExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:28:28.355964+00:00
-- url     : https://prove2.me/submissions/02e53906-b7d6-4281-9ebd-a6193710502c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde
import Theorems.Thm_GlobalTheory_FlagHook_Degree_sum_rho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
noncomputable section
open GlobalTheory GlobalTheory.FlagHook GlobalTheory.FlagHook.Degree
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
omit [DecidableEq ι]
namespace GlobalTheory.FlagHook.Degree
theorem _root_.solution (σ : ι → Equiv.Perm (Fin N)) : ∑ x, permExp σ x = dimFl ι N := by
  rw [Fintype.sum_prod_type]
  have h : ∀ τ, ∑ i : Fin N, permExp σ (τ, i) = N * (N - 1) / 2 := by
    intro τ
    rw [← sum_rho N]
    exact Fintype.sum_equiv (σ τ) _ _ (fun i => by simp [permExp])
  simp [h, dimFl]
end GlobalTheory.FlagHook.Degree
