-- Prove2me | solution 1 for MixFlex.Reliable.lossAverse_eq_expectedUtility
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:20:53.524412+00:00
-- url     : https://prove2.me/submissions/01fe7e16-d4f9-4af8-b943-fdaa1beabae9

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model
set_option autoImplicit false
open MeasureTheory MixFlex.Reliable
private theorem la_mono (P : Params) (hP : P.Standing) :
    Monotone (fun w : ℝ => max (w - P.w0) 0 - P.beta * max (-(w - P.w0)) 0) := by
  intro a b hab
  have h1 : max (a-P.w0) 0 ≤ max (b-P.w0) 0 := max_le_max (by linarith) le_rfl
  have h2 : max (-(b-P.w0)) 0 ≤ max (-(a-P.w0)) 0 := max_le_max (by linarith) le_rfl
  have h3 := mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one hP.one_le_beta)
  linarith

theorem solution (P : Params) (hP : P.Standing) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Monotone (uLA P) ∧
      ∀ W : Ω → ℝ, Integrable W μ → lossAverseValue P μ W = expectedUtility μ (uLA P) W := by
  constructor
  · intro a b hab
    have hh := la_mono P hP hab
    dsimp [uLA]
    linarith
  · intro W hW
    have hp : Integrable (fun ω => max (W ω - P.w0) 0) μ :=
      (hW.sub (integrable_const _)).sup (integrable_const _)
    have hn : Integrable (fun ω => max (-(W ω - P.w0)) 0) μ :=
      (hW.sub (integrable_const _)).neg.sup (integrable_const _)
    have ha : Integrable (fun ω => P.w0 + max (W ω - P.w0) 0) μ :=
      (integrable_const P.w0).add hp
    unfold lossAverseValue expectedUtility uLA
    rw [integral_sub hp (hn.const_mul P.beta), integral_sub ha (hn.const_mul P.beta)]
    rw [integral_add (integrable_const P.w0) hp]
    simp
    ring
