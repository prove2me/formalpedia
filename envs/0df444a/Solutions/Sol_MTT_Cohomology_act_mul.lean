-- Prove2me | solution 1 for MTT.Cohomology.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:48:50.132732+00:00
-- url     : https://prove2.me/submissions/d421bf36-a07e-4698-8061-275bb9c2edf3

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem solution {R : Type*} [CommRing R]
    (γ δ : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act γ (act δ P) = act (γ * δ) P := by
  simp only [act, AlgHom.toLinearMap_apply]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext i
  simp only [Fin.sum_univ_two, map_add, map_smul, MvPolynomial.aeval_X, smul_add, smul_smul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, MvPolynomial.smul_eq_C_mul, Int.cast_add,
    Int.cast_mul, map_add, map_mul]
  ring
