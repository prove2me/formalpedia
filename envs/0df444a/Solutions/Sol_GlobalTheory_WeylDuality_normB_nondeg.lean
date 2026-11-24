-- Prove2me | solution 1 for GlobalTheory.WeylDuality.normB_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:51.75233+00:00
-- url     : https://prove2.me/submissions/fdf56bbf-9308-45cd-9d03-e3bce4df0d32

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_fockQ_hw_pos
import Theorems.Thm_GlobalTheory_WeylDuality_normB_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : (normB hn ν).Nondegenerate := by
  have hc := fockQ_hw_pos hn ν
  have key : ∀ x : dualWeyl ℚ r n ν, normB hn ν x x = 0 → x = 0 := by
    intro x hx
    rw [normB_apply, mul_eq_zero, inv_eq_zero] at hx
    rcases hx with h | h
    · exact absurd h hc.ne'
    · by_contra hne
      have hx0 : (x : MvPolynomial (Fin r × Fin n) ℚ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      exact ((fockQPos _ x.1 x.1).2 hx0).ne' h
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩
end GlobalTheory.WeylDuality
