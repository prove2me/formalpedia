-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1RationalAtZeroV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:25:22.803287+00:00
-- url     : https://prove2.me/submissions/271aa62f-fa08-47aa-af03-876aa9bae3ef

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

theorem _root_.solution
    (lambda mu beta : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hbeta : 0 < beta) :
    Tendsto (fun phi : Real =>
      (phi+mu-lambda)*(mu+beta) /
        ((mu+beta)*(mu+phi)-lambda*mu))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1-lambda/mu)*(1+lambda/(mu-lambda+beta)))) := by
  have hmu0 : 0 < mu := lt_trans hlambda hmu
  have hd : (mu+beta)*(mu+0)-lambda*mu ≠ 0 := by
    have : (mu+beta)*(mu+0)-lambda*mu = mu * (mu - lambda + beta) := by ring
    rw [this]; exact (mul_pos hmu0 (by linarith)).ne'
  have hc : ContinuousAt (fun phi : ℝ => (phi+mu-lambda)*(mu+beta) / ((mu+beta)*(mu+phi)-lambda*mu)) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hd
  have e : (0+mu-lambda)*(mu+beta) / ((mu+beta)*(mu+0)-lambda*mu) = (1-lambda/mu)*(1+lambda/(mu-lambda+beta)) := by
    have h1 : mu - lambda + beta ≠ 0 := by linarith
    have h2 := hmu0.ne'
    rw [div_eq_iff hd]; field_simp; ring
  have := hc.tendsto
  rw [e] at this
  exact this.mono_left nhdsWithin_le_nhds

