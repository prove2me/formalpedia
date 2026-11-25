-- Prove2me | solution 1 for Kyprianou.Ch04.boundedVariationIntegerDivergenceExtends
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:50:49.972084+00:00
-- url     : https://prove2.me/submissions/394812f2-c989-4494-898d-b335785f1ca0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (x : NNReal → Real) (d : Real) (hd : 0 < d)
    (hm : Monotone (fun t : NNReal => d * (t : Real) - x t))
    (hx : Tendsto (fun n : Nat => x (n : NNReal)) atTop atBot) :
    Tendsto x atTop atBot := by
  apply tendsto_atBot.2
  intro b
  obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atBot.1 hx (b - d))
  filter_upwards [eventually_ge_atTop (N : NNReal)] with t ht
  let n := ⌊(t : Real)⌋₊
  have hn : (n : Real) ≤ (t : Real) := Nat.floor_le t.coe_nonneg
  have hnN : N ≤ n := Nat.le_floor (by exact_mod_cast ht)
  have hdiff : (t : Real) < (n : Real) + 1 := Nat.lt_floor_add_one _
  have hmono := hm (show (n : NNReal) ≤ t by exact_mod_cast hn)
  have hstep := mul_lt_mul_of_pos_left hdiff hd
  have hbound := hN n hnN
  push_cast at hmono
  linarith
