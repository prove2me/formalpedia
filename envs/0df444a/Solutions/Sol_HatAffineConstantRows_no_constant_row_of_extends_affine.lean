-- Prove2me | solution 1 for HatAffineConstantRows.no_constant_row_of_extends_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:24:19.212555+00:00
-- url     : https://prove2.me/submissions/0a6b2811-1aac-4c9a-a2c5-85b6a103b92f

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_eval_affineObstruction
import Theorems.Thm_HatAffineConstantRows_rowSeparating_obstruction_ne_zero
import Theorems.Thm_HatAffineConstantRows_rowSeparating_obstruction_totalDegree_lt
import Theorems.Thm_HatAffineConstantRows_puncturedBox_vanishing_of_totalDegree_lt
import Theorems.Thm_HatAffineGeneral_extends_iff_coverable
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (b : Fin (Fintype.card K - 1) → K)
    (F :
      (Fin m → K) →
      Fin (Fintype.card K - 1) → K)
    (hrealize : AffineRealizes A b F)
    (hext : HatAffineGeneral.Extends F) :
    ∀ i, A i ≠ 0 := by
  classical
  intro i0 hi0
  let x : Fin (Fintype.card K - 1) → K := rowSeparatingOffset A b
  let P : MvPolynomial (Fin m) K := affineObstruction A b x
  have hPne : P ≠ 0 := by
    simpa only [P, x] using rowSeparating_obstruction_ne_zero A b
  have hPdeg : P.totalDegree < Fintype.card K - 1 := by
    have hdeg := rowSeparating_obstruction_totalDegree_lt A b i0 hi0
    simpa only [P, x, Fintype.card_fin] using hdeg
  have hcovers := (HatAffineGeneral.extends_iff_coverable F).mp hext
  obtain ⟨g, hg⟩ := hcovers x
  have hvanish :
      ∀ y : Fin m → K,
        (∀ j, y j ≠ g j) →
        MvPolynomial.eval y P = 0 := by
    intro y hy
    have hleft : ∃ i, F y i = x i := by
      by_contra hnone
      have hybad : y ∈ HatAffineGeneral.BadSet F x := by
        change ∀ i, F y i ≠ x i
        intro i hi
        exact hnone ⟨i, hi⟩
      obtain ⟨j, hj⟩ := hg y hybad
      exact hy j hj
    obtain ⟨i, hi⟩ := hleft
    change MvPolynomial.eval y (affineObstruction A b x) = 0
    rw [eval_affineObstruction A b x F hrealize y]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_eq_zero.mpr hi)
  have hPzero :=
    puncturedBox_vanishing_of_totalDegree_lt hm hq g P hPdeg hvanish
  exact hPne hPzero
end HatAffineConstantRows
