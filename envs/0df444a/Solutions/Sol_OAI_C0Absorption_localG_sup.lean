-- Prove2me | solution 1 for OAI.C0Absorption.localG_sup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:21:58.10143+00:00
-- url     : https://prove2.me/submissions/491b9878-e35b-427a-887c-779baef567d4

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology


theorem solution {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localG q ε u x| ≤ A := by
  have h0 : 0 ≤ chi (dist x q / ε) := by unfold chi; exact le_min zero_le_one (le_max_left _ _)
  have h1 : chi (dist x q / ε) ≤ 1 := by unfold chi; exact min_le_left _ _
  have e : localG q ε u x = (1 - chi (dist x q / ε)) * u q + chi (dist x q / ε) * u x := by
    unfold localG; ring
  rw [e]
  have hq := abs_le.1 (hu q)
  have hx := abs_le.1 (hu x)
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hq.1 (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hq.2 (sub_nonneg.2 h1),
    mul_le_mul_of_nonneg_left hx.1 h0, mul_le_mul_of_nonneg_left hx.2 h0]

