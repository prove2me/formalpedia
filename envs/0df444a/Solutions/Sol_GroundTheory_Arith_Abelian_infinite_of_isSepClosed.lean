-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.infinite_of_isSepClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:06.517934+00:00
-- url     : https://prove2.me/submissions/ccc536c0-afd6-4170-ae08-dbef09b84de6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (k : Type*) [Field k] [IsSepClosed k] : Infinite k := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite k
  set q := Fintype.card k
  have hq : (q : k) = 0 := FiniteField.cast_card_eq_zero k
  have hq1 : 1 < q := Fintype.one_lt_card
  set p : k[X] := X ^ q - (X + 1)
  have hp' : derivative p = -1 := by
    simp only [p, derivative_sub, derivative_X_pow, derivative_add, derivative_X, derivative_one,
      hq, map_zero, zero_mul, add_zero, zero_sub]
  have hsep : p.Separable := by
    rw [Polynomial.separable_def, hp']
    exact ⟨0, -1, by ring⟩
  have hdeg : p.natDegree = q := by
    simp only [p]
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp only [natDegree_X_pow]
    calc (X + 1 : k[X]).natDegree ≤ 1 := by compute_degree
      _ < q := hq1
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root p
    (by rw [degree_eq_natDegree (fun h => by rw [h] at hdeg; simp at hdeg; omega), hdeg]; simp; omega)
    hsep
  simp only [IsRoot, p, eval_sub, eval_pow, eval_X, eval_add, eval_one] at hx
  rw [show x ^ q = x from FiniteField.pow_card x] at hx
  exact one_ne_zero (by linear_combination -hx : (1 : k) = 0)
end GroundTheory.Arith.Abelian
