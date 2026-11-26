-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1RootRationalAgreementV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:25:24.806873+00:00
-- url     : https://prove2.me/submissions/57700942-d687-44ef-a9e5-4020d342a539

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

theorem _root_.solution
    (lambda mu beta phi : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hbeta : 0 < beta)
    (hphi : 0 < phi) (hpb : phi < beta) :
    let psi : Real → Real := fun x => x - lambda*x/(mu+x)
    (psi phi / phi) * ((beta-phi)/(psi beta-psi phi)) =
      (phi+mu-lambda)*(mu+beta) /
        ((mu+beta)*(mu+phi)-lambda*mu) := by
  intro psi
  have hmu0 : 0 < mu := lt_trans hlambda hmu
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

