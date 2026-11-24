-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_shifted_overshoot_payoff_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:45:54.358783+00:00
-- url     : https://prove2.me/submissions/10454097-fdb8-4936-9293-1f80b1c45cc3

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution
    {Ω : Type} (X : ℝ≥0 → Ω → ℝ) (q c y : ℝ) :
    downOvershootTilt X q c y = downEsscherPayoff X q c y := by
  funext ω
  have ht : tauMinus (shifted X y) 0 ω = tauMinus X (-y) ω := by
    unfold tauMinus
    congr 1
    ext t
    simp only [mem_setOf_eq, shifted]
    constructor <;> rintro ⟨u,hu,he,hv⟩ <;> exact ⟨u,hu,he,by linarith⟩
  unfold downOvershootTilt downEsscherPayoff
  rw [ht]
  cases tauMinus X (-y) ω <;> simp [add_comm]
