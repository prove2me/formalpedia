-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scale_causal_integrand_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:47:59.358178+00:00
-- url     : https://prove2.me/submissions/76c8440f-42f5-4e9c-86f7-9167ec39d38d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Mathlib.Tactic.Linarith
set_option autoImplicit false

open Kyprianou.Ch08.StageB Set

theorem solution (W : ℝ → ℝ)
    (hmono : MonotoneOn W (Set.Ici (0 : ℝ)))
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ W t)
    (x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) (hsx : s ≤ x) :
    W s * W (x - s) ≤ (W x) ^ 2 := by
  have hsIn : s ∈ Set.Ici (0 : ℝ) := hs
  have hxIn : x ∈ Set.Ici (0 : ℝ) := hx
  have hdiff : 0 ≤ x - s := sub_nonneg.mpr hsx
  have hdiffIn : x - s ∈ Set.Ici (0 : ℝ) := hdiff
  have hsW : W s ≤ W x := hmono hsIn hxIn hsx
  have hdiffW : W (x - s) ≤ W x :=
    hmono hdiffIn hxIn (sub_le_self x hs)
  have hbound := mul_le_mul hsW hdiffW (hpos (x - s) hdiff) (hpos x hx)
  nlinarith [hbound]
