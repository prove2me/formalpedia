-- Prove2me | solution 1 for GlobalTheory.Nef.homogenize_multiset_prod_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:06:11.750006+00:00
-- url     : https://prove2.me/submissions/d4a4c34c-779d-49e0-9e07-419721b4957b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BinaryFormSplits
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution {E : Type} [Field E] (R : Multiset E) :
    Polynomial.homogenize (R.map fun a => Polynomial.X - Polynomial.C a).prod (Multiset.card R)
      = (R.map fun a => MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a R ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      Polynomial.homogenize_mul _ _ (m := 1) (n := Multiset.card R) ?_ ?_, ih]
    · simp [Multiset.map_cons]
    · exact Polynomial.natDegree_X_sub_C_le a
    · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
end GlobalTheory.Nef
