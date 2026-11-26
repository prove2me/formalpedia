-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1SmallRootTransformV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:29:52.19765+00:00
-- url     : https://prove2.me/submissions/f37bddbc-c88e-496b-abc6-1d9920e9419d

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

theorem _root_.solution
    (lambda mu beta : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hbeta : 0 < beta) :
    let psi : Real → Real := fun x => x - lambda*x/(mu+x)
    Tendsto (fun phi : Real =>
      (psi phi / phi) * ((beta-phi)/(psi beta-psi phi)))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1-lambda/mu)*(1+lambda/(mu-lambda+beta)))) := by
  intro psi
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
  have ht := hc.tendsto
  rw [e] at ht
  refine (ht.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hbeta] with phi hp
  obtain ⟨hphi, hpb⟩ := hp
  have h1 : mu + phi ≠ 0 := by positivity
  have h2 : mu + beta ≠ 0 := by positivity
  have hD : (mu+beta)*(mu+phi)-lambda*mu ≠ 0 := by
    have : 0 < (mu+beta)*(mu+phi)-lambda*mu := by nlinarith [mul_pos hbeta hphi, mul_pos hmu0 (sub_pos.2 hmu), mul_pos hmu0 hbeta, mul_pos hmu0 hphi]
    exact this.ne'
  have e1 : psi phi / phi = (phi+mu-lambda)/(mu+phi) := by
    show (phi - lambda*phi/(mu+phi)) / phi = _
    have := hphi.ne'
    field_simp
    ring
  have e2 : psi beta - psi phi = (beta - phi) * ((mu+beta)*(mu+phi)-lambda*mu) / ((mu+beta)*(mu+phi)) := by
    show (beta - lambda*beta/(mu+beta)) - (phi - lambda*phi/(mu+phi)) = _
    field_simp
    ring
  have hb : beta - phi ≠ 0 := (sub_pos.2 hpb).ne'
  rw [e1, e2]
  generalize hE : (mu+beta)*(mu+phi)-lambda*mu = E at hD ⊢
  field_simp

