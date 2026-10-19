-- Prove2me | solution 1 for OAI.C0Absorption.tailFactor_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:24:10.850533+00:00
-- url     : https://prove2.me/submissions/d7b8411f-1cf5-4a51-88ca-0feb50bfa5e8

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution {c : ℝ} (hc : 0 < c) (N : ℕ) :
    LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ (tailFactor c N) := by
  have h1 : LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ (fun s : C0 => 2 - tau N s / c) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have := (tau_lipschitz N).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, NNReal.coe_mk] at this ⊢
    rw [Real.dist_eq] at this ⊢
    rw [show 2 - tau N x / c - (2 - tau N y / c) = -(tau N x - tau N y) * c⁻¹ by field_simp; ring,
      abs_mul, abs_neg, abs_of_pos (inv_pos.2 hc), mul_comm]
    exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 hc.le)
  have h2 := (h1.max_const 0).const_min 1
  exact h2

