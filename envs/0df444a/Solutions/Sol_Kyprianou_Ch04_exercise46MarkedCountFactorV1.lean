-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MarkedCountFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:49.284575+00:00
-- url     : https://prove2.me/submissions/1414b7aa-d61f-4075-a04b-fee8b7ad13b3

import Mathlib.Data.ENNReal.Basic
open scoped ENNReal
set_option autoImplicit false
theorem solution
    (a b clock rate mark : ENNReal)
    (ha : a = clock * rate)
    (hb : b = clock * (rate * mark)) :
    b = a * mark := by
  rw [ha, hb, mul_assoc]
