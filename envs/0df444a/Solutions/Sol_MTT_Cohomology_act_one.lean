-- Prove2me | solution 1 for MTT.Cohomology.act_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:49:41.643615+00:00
-- url     : https://prove2.me/submissions/0cafe076-aa8d-4f25-8440-98be41a2471e

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem solution {R : Type*} [CommRing R] (P : Binary R) :
    act (1 : Matrix (Fin 2) (Fin 2) ℤ) P = P := by
  simp only [act, AlgHom.toLinearMap_apply]
  convert MvPolynomial.aeval_X_left_apply P using 3
  funext i
  fin_cases i <;> simp [Matrix.one_apply]
