-- Prove2me | solution 1 for InverseGalois.mvPolynomial_faithfulSMul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T01:35:36.327524+00:00
-- url     : https://prove2.me/submissions/a0f013c3-d9a9-4771-a27e-fe8b7e0e5bb2

import Definitions.Def_InverseGalois_regular_action

open InverseGalois

theorem solution (G I R : Type*) [Group G] [CommRing R]
    [Nontrivial R] [MulAction G I] [FaithfulSMul G I] :
    letI := mvPolynomialMulSemiringAction G I R
    FaithfulSMul G (MvPolynomial I R) := by
  letI := mvPolynomialMulSemiringAction G I R
  constructor
  intro g h heq
  apply eq_of_smul_eq_smul (α := I)
  intro i
  apply MvPolynomial.X_injective (R := R)
  have hx := heq (MvPolynomial.X i)
  change MvPolynomial.rename (g • ·) (MvPolynomial.X i) =
    MvPolynomial.rename (h • ·) (MvPolynomial.X i) at hx
  simpa only [MvPolynomial.rename_X] using hx
