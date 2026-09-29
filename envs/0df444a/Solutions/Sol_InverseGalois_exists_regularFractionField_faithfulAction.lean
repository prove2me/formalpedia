-- Prove2me | solution 1 for InverseGalois.exists_regularFractionField_faithfulAction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T01:51:14.04753+00:00
-- url     : https://prove2.me/submissions/333d0eaf-272c-49d1-806b-131c3ea661f8

import Definitions.Def_InverseGalois_regular_action
import Theorems.Thm_InverseGalois_shrink_faithfulSMul
import Theorems.Thm_InverseGalois_mvPolynomial_faithfulSMul

open InverseGalois

universe u

theorem solution (G : Type u) [Fintype G] [Group G] :
    ∃ action : MulSemiringAction G (RegularFractionField G),
      @FaithfulSMul G (RegularFractionField G) action.toSMul := by
  letI : FaithfulSMul G (Shrink.{0} G) := shrink_faithfulSMul
  letI : MulSemiringAction G (RegularPolynomialRing G) :=
    mvPolynomialMulSemiringAction G (Shrink.{0} G) ℚ
  letI : FaithfulSMul G (RegularPolynomialRing G) :=
    mvPolynomial_faithfulSMul G (Shrink.{0} G) ℚ
  let action : MulSemiringAction G (RegularFractionField G) :=
    IsFractionRing.mulSemiringAction G (RegularPolynomialRing G)
      (RegularFractionField G)
  letI : MulSemiringAction G (RegularFractionField G) := action
  letI : SMulDistribClass G (RegularPolynomialRing G) (RegularFractionField G) :=
    IsFractionRing.smulDistribClass G (RegularPolynomialRing G)
      (RegularFractionField G)
  exact ⟨action,
    IsFractionRing.faithfulSMul G (RegularPolynomialRing G)
      (RegularFractionField G)⟩
