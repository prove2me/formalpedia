-- Prove2me | solution 1 for GlobalTheory.offDiagPart_sq_le_of_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:31.177282+00:00
-- url     : https://prove2.me/submissions/f7c7d625-6332-41e8-91b1-6fcf5e3718e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleLevelOffDiagNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirOffDiagonalNormSqLeOfLevel
import Theorems.Thm_GlobalTheory_norm_sum_sq_le_fin_mul
import Theorems.Thm_GlobalTheory_lev_offDiag_normSq_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M),
    IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) →
      ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hsh hj hlev

  have step1 : ∀ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤
      (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 :=
    fun b => norm_sum_sq_le_fin_mul _ _
  have swap : ∑ b, ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 =
      ∑ c, ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 :=
    Finset.sum_comm' (fun b c => by
      simp only [mem_univ, mem_erase, true_and, and_true]
      exact ne_comm)
  have step2 : ∀ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 ≤
      (bv / 16) ^ 2 * ‖x c‖ ^ 2 := by
    intro c
    refine le_trans ?_ (lev_offDiag_normSq_le M n ε E μ kk j bv (x c) hmod hsh hj (hlev c))
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    calc ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2
        ≤ ∑ b ∈ univ.erase c, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 := by
          refine sum_le_sum fun b hb => ?_
          have hcb : c ∈ univ.erase b :=
            mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 h.symm, mem_univ _⟩
          exact single_le_sum (f := fun b' => ‖E b b' (x c)‖ ^ 2) (fun _ _ => sq_nonneg _) hcb
      _ ≤ ∑ b, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2
      ≤ ∑ b, (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 := sum_le_sum fun b _ => step1 b
    _ = ∑ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 := by
      rw [← mul_sum, swap, mul_sum]
    _ ≤ ∑ c, (bv / 16) ^ 2 * ‖x c‖ ^ 2 := sum_le_sum fun c _ => step2 c
    _ = (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by rw [mul_sum]
end GlobalTheory
