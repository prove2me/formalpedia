-- Prove2me | solution 1 for GlobalTheory.PMonE.lowerOrder_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:06.671807+00:00
-- url     : https://prove2.me/submissions/1b614dba-c29b-44f7-9768-cd1a334882c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
import Theorems.Thm_GlobalTheory_PMonE_norm_one_apply_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
omit [Fintype m]
namespace GlobalTheory.PMonE
theorem _root_.solution {N : ℕ} (hN : 1 ≤ N) {M : ℕ → Matrix m m F} (hM : Normal (N + 1) M) :
    Normal N (lowerOrder N M) where
  int n i j := by
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · split_ifs
      · exact norm_one_apply_le i j
      · simp
    · split_ifs
      · rw [Matrix.neg_apply, norm_neg]
        exact norm_one_apply_le i j
      · simp
    · split_ifs
      · exact hM.int 0 i j
      · simp
    · exact hM.int (n + 1) i j
  top := by
    have h1 : N + 1 ≠ N := by omega
    have h2 : N ≠ 0 := by omega
    simp [lowerOrder, h1, h2, hM.top]
  small n hn i j := by
    have h1 : n ≠ N := by omega
    have h2 : n + 1 ≠ N := by omega
    have h3 : n ≠ 0 := by omega
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, if_neg h1, if_neg h2, if_neg h3,
        Matrix.zero_apply, norm_zero, zero_lt_one]
    exact hM.small (n + 1) (by omega) i j
end GlobalTheory.PMonE
