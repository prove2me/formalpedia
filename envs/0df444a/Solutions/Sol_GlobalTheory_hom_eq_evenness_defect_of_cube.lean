-- Prove2me | solution 1 for GlobalTheory.hom_eq_evenness_defect_of_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:00:09.023668+00:00
-- url     : https://prove2.me/submissions/e9cc4573-bad6-498d-8e95-256a7939abfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CubicalFunctionOfHomomorphism
import Theorems.Thm_GlobalTheory_evenDefectTriangle_neg
import Theorems.Thm_GlobalTheory_evenDefectTriangle_cube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (A : Type) [CommGroup A] (h : X → A)
    (hh : ∀ a b, h (a + b) = h a * h b) :
    ∃ k : X → A, (∀ a a' b : X, k (a + a' + b) * k a * k a' * k b
        = k (a + a') * k (a + b) * k (a' + b)) ∧ ∀ a, k (-a) = h a * k a := by
  classical
  let e := Module.Free.chooseBasis ℤ X
  let ψ : Multiplicative X →* A := MonoidHom.mk' (fun x => h x.toAdd) (fun x y => hh _ _)
  have hrep : ∀ x, h x = ∏ i, h (e i) ^ (e.repr x i) := by
    intro x
    conv_lhs => rw [← e.sum_repr x]
    change ψ (Multiplicative.ofAdd (∑ i, e.repr x i • e i)) = _
    rw [ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ofAdd_zsmul, map_zpow]
    rfl
  refine ⟨fun x => ∏ i, h (e i) ^ evenDefectTriangle (e.repr x i), ?_, ?_⟩
  · intro a a' c
    simp only [map_add, Finsupp.add_apply, ← Finset.prod_mul_distrib, ← zpow_add]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [evenDefectTriangle_cube]
  · intro a
    simp only [map_neg, Finsupp.neg_apply, evenDefectTriangle_neg]
    rw [hrep a, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_add, add_comm]
end GlobalTheory
