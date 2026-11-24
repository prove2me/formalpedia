-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:40.150681+00:00
-- url     : https://prove2.me/submissions/c068f2ac-6ae0-4308-b92f-abf21d04c73c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup

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
    Fintype.card ι * Fintype.card ι = Fintype.card {p : ι × ι // b p.1 < b p.2} +
      Fintype.card {p : ι × ι // b p.2 < b p.1} + Fintype.card {p : ι × ι // b p.1 = b p.2} := by
  rw [← Fintype.card_prod]
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases lt_trichotomy (b p.1) (b p.2) with h | h | h
  · simp [h, h.ne, not_lt_of_gt h]
  · simp [h]
  · simp [h, h.ne', not_lt_of_gt h]
end GlobalTheory.CompanionTheory.FinGL
