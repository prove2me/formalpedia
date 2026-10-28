-- Prove2me | solution 1 for LevyStochCalc.Probability.exists_lt_exitTime_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:06:22.526299+00:00
-- url     : https://prove2.me/submissions/d6cb26f5-28a9-43aa-83da-04e3833afe83

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime
import Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]
/-- **Localisation.** For a continuous path, every time lies strictly below the exit time at
level `k` for all large `k`. -/
theorem solution {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (t : WithTop ℝ) < LevyStochCalc.Probability.exitTime X (k : ℝ) ω := by
  obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_isMaxOn
    (Set.nonempty_Icc.2 ht) hX.norm.continuousOn
  obtain ⟨K, hK⟩ := exists_nat_gt ‖X ω s₀‖
  refine ⟨K, fun k hk => ?_⟩
  rcases lt_or_ge (t : WithTop ℝ) (LevyStochCalc.Probability.exitTime X (k : ℝ) ω) with hlt | hle
  · exact hlt
  · exfalso
    obtain ⟨s, hs, hks⟩ := (LevyStochCalc.Probability.exitTime_le_iff_readable hX (k : ℝ) t).1 hle
    have h1 : ‖X ω s‖ ≤ ‖X ω s₀‖ := hmax hs
    have h2 : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
