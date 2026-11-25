-- Prove2me | solution 1 for GlobalTheory.DiagBlock.mfact_diagMon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:58:29.232616+00:00
-- url     : https://prove2.me/submissions/46b6203c-5655-405b-b806-06e100bc3129

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_diagMon_inl
import Theorems.Thm_GlobalTheory_DiagBlock_diagMon_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution {n0 n : ℕ} (L y : ℕ) :
    mfact (diagMon n0 n L y) = ((L * y).factorial * y.factorial) ^ (n - n0) := by
  classical
  have hcard : ((Finset.univ : Finset (Fin n)).filter fun ρ => n0 ≤ ρ.val).card = n - n0 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun ρ : Fin n => ρ.val < n0)
    rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h1
    simp only [not_lt] at h1
    omega
  have key : ∀ t : ℕ, ∏ ρ : Fin n, ∏ c : Fin n, (if n0 ≤ ρ.val ∧ c = ρ then t else 0).factorial =
      t.factorial ^ (n - n0) := by
    intro t
    have hrow : ∀ ρ : Fin n, ∏ c : Fin n, (if n0 ≤ ρ.val ∧ c = ρ then t else 0).factorial =
        if n0 ≤ ρ.val then t.factorial else 1 := by
      intro ρ
      by_cases hρ : n0 ≤ ρ.val
      · rw [if_pos hρ, Finset.prod_eq_single ρ]
        · simp [hρ]
        · intro c _ hc
          simp [hc]
        · intro h
          exact absurd (Finset.mem_univ ρ) h
      · simp [hρ]
    rw [Finset.prod_congr rfl (fun ρ _ => hrow ρ), ← Finset.prod_filter, Finset.prod_const, hcard]
  rw [mfact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_sum_type,
    Fintype.prod_prod_type, Fintype.prod_prod_type]
  simp only [diagMon_inl, diagMon_inr]
  rw [key, key, mul_pow]
end GlobalTheory.DiagBlock
