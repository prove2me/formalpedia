-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1DrawdownRationalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:49.375803+00:00
-- url     : https://prove2.me/submissions/84ae5d52-203a-4f7e-8bf5-6fff7b559595

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
theorem solution
    (lambda mu beta : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hbeta : 0 < beta) :
    (1-lambda/mu)*beta / (beta-lambda*beta/(mu+beta)) =
      (1-lambda/mu)*(1+lambda/(mu-lambda+beta)) := by
  have hm : 0 < mu := hlambda.trans hmu
  have hmb : 0 < mu+beta := add_pos hm hbeta
  have hd : 0 < mu-lambda+beta := by linarith
  have hpsi : beta-lambda*beta/(mu+beta) =
      beta*(mu-lambda+beta)/(mu+beta) := by
    field_simp [hmb.ne']
    <;> ring
  rw [hpsi]
  field_simp [hm.ne', hmb.ne', hd.ne', hbeta.ne']
  <;> ring
