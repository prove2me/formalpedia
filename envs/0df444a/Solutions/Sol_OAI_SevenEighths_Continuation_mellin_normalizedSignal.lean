-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.mellin_normalizedSignal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:51:54.541504+00:00
-- url     : https://prove2.me/submissions/babaca24-2b4e-44ab-bcbd-3020703a2b63

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Mathlib.Analysis.MellinInversion
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationInversion

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution (f : ℝ → ℂ) (c : ℝ) (s : ℂ) :
    mellin (normalizedSignal f c) (-s) = signalMellin f c s := by
  unfold normalizedSignal signalMellin
  rw [mellin_cpow_smul]
  congr 1
  ring
end OAI.SevenEighths.Continuation
