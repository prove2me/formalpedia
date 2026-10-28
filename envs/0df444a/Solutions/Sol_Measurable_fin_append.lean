-- Prove2me | solution 1 for Measurable.fin_append
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:25.670415+00:00
-- url     : https://prove2.me/submissions/b3d991fc-b07b-4a19-ad5d-929d0d7f8bab

import Mathlib

set_option autoImplicit false

-- carved verbatim out of submission 0f39c22d-cf6c-4cef-9f8e-35718ff87eba, lines 229-239


theorem solution {X : Type*} [MeasurableSpace X] (l : ℕ) :
    Measurable (fun p : (Fin l → X) × (Fin l → X) => (Fin.append p.1 p.2 : Fin (l + l) → X)) := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact (measurable_pi_apply i).comp measurable_fst
  | right i =>
    simp only [Fin.append_right]
    exact (measurable_pi_apply i).comp measurable_snd
