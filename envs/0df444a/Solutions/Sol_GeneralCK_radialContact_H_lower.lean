-- Prove2me | solution 1 for GeneralCK.radialContact_H_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T20:57:06.743883+00:00
-- url     : https://prove2.me/submissions/afb5c751-38ba-4113-ab2c-500c1275475d

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_bellman
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_H_strictMonoOn

/-! Precise target, not a proof of the Courtade--Kumar conjecture. -/
namespace GeneralCK
open scoped BigOperators





























end GeneralCK

open GeneralCK
theorem solution {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    radialContact (1 - 2 * v) (H v) = v := by
  have hHv : 0 < H v := H_pos hv (by linarith)
  have hset : {u : ℝ | 0 < u ∧ u < 1 / 2 ∧
      (1 - 2 * v) * H u = H v * (1 - 2 * u)} = {v} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, hu', heq⟩
      rcases lt_trichotomy u v with h | h | h
      · have hH := H_strictMonoOn ⟨hu.le, hu'.le⟩ ⟨hv.le, hv'.le⟩ h
        have hmul : (1 - 2 * v) * H u < (1 - 2 * v) * H v :=
          mul_lt_mul_of_pos_left hH (by linarith)
        have hmul' : H v * (1 - 2 * v) < H v * (1 - 2 * u) :=
          mul_lt_mul_of_pos_left (by linarith) hHv
        nlinarith
      · exact h
      · have hH := H_strictMonoOn ⟨hv.le, hv'.le⟩ ⟨hu.le, hu'.le⟩ h
        have hmul : (1 - 2 * v) * H v < (1 - 2 * v) * H u :=
          mul_lt_mul_of_pos_left hH (by linarith)
        have hmul' : H v * (1 - 2 * u) < H v * (1 - 2 * v) :=
          mul_lt_mul_of_pos_left (by linarith) hHv
        nlinarith
    · rintro rfl
      exact ⟨hv, hv', mul_comm _ _⟩
  unfold radialContact
  rw [hset, csInf_singleton]
