-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.choose_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:37.481167+00:00
-- url     : https://prove2.me/submissions/038cd909-cf65-4a20-864b-d3a29bd01b96

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_two_choose_add
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_eq_sum_blocks
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_same_block
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_swap_block
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
namespace GlobalTheory.CompanionTheory.FinGL
theorem _root_.solution :
    (Fintype.card ι).choose 2 = Fintype.card {p : ι × ι // b p.1 < b p.2} +
      ∑ c, (Fintype.card {i // b i = c}).choose 2 := by
  have h1 := card_pairs b
  rw [card_swap_block, card_same_block] at h1
  have h2 := two_choose_add (Fintype.card ι)
  have h3 : ∑ c, Fintype.card {i // b i = c} * Fintype.card {i // b i = c} =
      2 * ∑ c, (Fintype.card {i // b i = c}).choose 2 + Fintype.card ι := by
    rw [card_eq_sum_blocks b, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => (two_choose_add _).symm
  omega
end GlobalTheory.CompanionTheory.FinGL
