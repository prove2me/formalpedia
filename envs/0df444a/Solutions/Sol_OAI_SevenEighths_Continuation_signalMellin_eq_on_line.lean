-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.signalMellin_eq_on_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:13:54.762505+00:00
-- url     : https://prove2.me/submissions/8a57d6e5-b935-4556-911f-93426cae0776

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Mathlib.Analysis.MellinInversion
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationInversion
import Theorems.Thm_OAI_SevenEighths_Continuation_mellin_mellinInv_eq
import Theorems.Thm_OAI_SevenEighths_Continuation_mellin_normalizedSignal

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution (f : ℝ → ℂ) (A : ℂ → ℂ) (c d : ℝ)
    (hf : MellinConvergent f (-((d : ℂ) + (c : ℂ))))
    (hA : Integrable (fun y : ℝ => A ((d : ℂ) - 2 * Real.pi * y * Complex.I)))
    (hcont : Continuous (fun y : ℝ => A ((d : ℂ) - 2 * Real.pi * y * Complex.I)))
    (hrep : ∀ x : ℝ, 0 < x → normalizedSignal f c x =
      mellinInv (-d) (fun s => A (-s)) x) (y : ℝ) :
    signalMellin f c ((d : ℂ) - 2 * Real.pi * y * Complex.I) =
      A ((d : ℂ) - 2 * Real.pi * y * Complex.I) := by
  have hf' : MellinConvergent (normalizedSignal f c) ((-d : ℝ) : ℂ) := by
    unfold normalizedSignal
    apply MellinConvergent.cpow_smul.mpr
    convert hf using 1; push_cast; ring
  have harg (y : ℝ) : -(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I) =
      (d : ℂ) - 2 * Real.pi * y * Complex.I := by push_cast; ring
  have hA' : Integrable
      (fun y : ℝ => A (-(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I))) := by
    simpa only [harg] using hA
  have hcont' : Continuous
      (fun y : ℝ => A (-(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I))) := by
    simpa only [harg] using hcont
  have hid := mellin_mellinInv_eq (-d) (fun s => A (-s))
    (normalizedSignal f c) hf' hA' hcont' hrep y
  rw [harg] at hid
  rw [← mellin_normalizedSignal]
  convert hid using 1; congr 1; push_cast; ring
end OAI.SevenEighths.Continuation
