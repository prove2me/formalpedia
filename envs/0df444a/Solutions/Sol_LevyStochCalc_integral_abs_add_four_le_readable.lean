-- Prove2me | solution 1 for LevyStochCalc.integral_abs_add_four_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:13.532415+00:00
-- url     : https://prove2.me/submissions/13636262-096f-4a89-93f5-eb679e628838

import Definitions.Def_KLSModular_LevyStochCalc_Probability_AbsMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/AbsMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]
/-- A four-term triangle inequality under the integral. -/
theorem solution {P : Measure Ω} [IsProbabilityMeasure P]
    {a b c d : Ω → ℝ} (ha : Integrable a P) (hb : Integrable b P) (hc : Integrable c P)
    (hd : Integrable d P) {A B C D : ℝ} (hA : ∫ ω, |a ω| ∂P ≤ A)
    (hB : ∫ ω, |b ω| ∂P ≤ B) (hC : ∫ ω, |c ω| ∂P ≤ C) (hD : ∫ ω, |d ω| ∂P ≤ D) :
    ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ A + B + C + D := by
  have hab : Integrable (fun ω => |a ω| + |b ω|) P := ha.abs.add hb.abs
  have habc : Integrable (fun ω => |a ω| + |b ω| + |c ω|) P := hab.add hc.abs
  have habcd : Integrable (fun ω => |a ω| + |b ω| + |c ω| + |d ω|) P := habc.add hd.abs
  have htri : ∀ ω, |a ω + b ω + c ω + d ω| ≤ |a ω| + |b ω| + |c ω| + |d ω| := by
    intro ω
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  calc ∫ ω, |a ω + b ω + c ω + d ω| ∂P
      ≤ ∫ ω, (|a ω| + |b ω| + |c ω| + |d ω|) ∂P :=
        integral_mono (((ha.add hb).add hc).add hd).abs habcd htri
    _ = ∫ ω, (|a ω| + |b ω| + |c ω|) ∂P + ∫ ω, |d ω| ∂P := integral_add habc hd.abs
    _ = ∫ ω, (|a ω| + |b ω|) ∂P + ∫ ω, |c ω| ∂P + ∫ ω, |d ω| ∂P := by
        rw [integral_add hab hc.abs]
    _ = ∫ ω, |a ω| ∂P + ∫ ω, |b ω| ∂P + ∫ ω, |c ω| ∂P + ∫ ω, |d ω| ∂P := by
        rw [integral_add ha.abs hb.abs]
    _ ≤ A + B + C + D := add_le_add (add_le_add (add_le_add hA hB) hC) hD
