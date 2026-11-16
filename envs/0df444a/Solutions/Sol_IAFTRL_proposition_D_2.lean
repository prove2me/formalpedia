-- Prove2me | solution 1 for IAFTRL.proposition_D_2
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:26:39.010512+00:00
-- url     : https://prove2.me/submissions/ae3eaa8b-e29f-4bcc-bd0d-8919f4afb309

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_regretVs

import Theorems.Thm_IAFTRL_proposition_D_2_trivial
import Theorems.Thm_IAFTRL_proposition_D_2_ftrl

open Matrix MeasureTheory IAFTRL

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (hT : 1 ≤ T) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R)
    (u : Fin K) :
    regretVs P arms T R u ≤
      min (2 * (T : ℝ)) (16 * (d : ℝ) * Real.log (Real.exp 1 * K) +
        21 * Real.sqrt ((d : ℝ) * T * Real.log (Real.exp 1 * K))) :=
  le_min (proposition_D_2_trivial hd arms hA P T hT R hR u)
    (proposition_D_2_ftrl hd arms hA P T hT R hR u)
