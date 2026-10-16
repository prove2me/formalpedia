-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.scaled_centers_ne_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:13:06.008848+00:00
-- url     : https://prove2.me/submissions/ebfa29a4-5af1-41b6-815b-df122c7d11fa

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    {j k : Fin K} (hjk : j ≠ k) :
    ∃ i : Fin m, (j.val : ℂ) * r i ≠ (k.val : ℂ) * r i := by
  by_contra h
  push_neg at h
  apply hjk
  apply hc
  funext i
  exact h i