-- Prove2me | solution 1 for LearnNoConc.ERM.shift_starShaped
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:33:15.039727+00:00
-- url     : https://prove2.me/submissions/cadb868a-20a4-4a40-b903-608da6c53536

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

open MeasureTheory
open scoped ENNReal

open LearnNoConc.ERM in
theorem solution {Ω : Type*} (F : Set (Ω → ℝ)) (hFconv : Convex ℝ F)
    (fstar : Ω → ℝ) (hfstar : fstar ∈ F) :
    StarShaped (shift F fstar) := by
  rintro h ⟨f, hf, rfl⟩ c hc0 hc1
  refine ⟨c • f + (1 - c) • fstar, hFconv hf hfstar hc0.le (by linarith) (by ring), ?_⟩
  funext x
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring
