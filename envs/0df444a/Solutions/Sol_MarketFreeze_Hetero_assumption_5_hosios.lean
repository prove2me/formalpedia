-- Prove2me | solution 1 for MarketFreeze.Hetero.assumption_5_hosios
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:52:31.098673+00:00
-- url     : https://prove2.me/submissions/762234d4-9a13-4617-9941-ee8e9f12e580

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

open MarketFreeze.Hetero in
theorem solution (P : Params) (hlam : 0 < P.lam) (n : ℝ) (hn : 0 < n) :
    alpha P n / n = P.lam / (1 + n) ∧
    n * deriv (alpha P) n / alpha P n = beta n ∧
    1 - beta n = n / (1 + n) := by
  have hn0 : n ≠ 0 := hn.ne'
  have hn1 : 1 + n ≠ 0 := by positivity
  have hfun : alpha P = fun y => (P.lam * y) / (1 + y) := by
    funext y; rfl
  have hd : HasDerivAt (alpha P)
      ((P.lam * 1 * (1 + n) - P.lam * n * 1) / (1 + n) ^ 2) n := by
    rw [hfun]
    apply HasDerivAt.div
    · exact (hasDerivAt_id n).const_mul P.lam
    · exact (hasDerivAt_id n).const_add 1
    · exact hn1
  refine ⟨?_, ?_, ?_⟩
  · unfold alpha; field_simp
  · rw [hd.deriv]
    unfold alpha beta
    have : P.lam ≠ 0 := hlam.ne'
    field_simp
    ring
  · unfold beta; field_simp; ring
