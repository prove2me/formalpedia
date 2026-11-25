-- Prove2me | solution 1 for GlobalTheory.Capelli.casimir_mixedOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:31:13.440302+00:00
-- url     : https://prove2.me/submissions/e2d7686b-ab9f-4adb-aae3-d8602c5fb40b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
import Theorems.Thm_GlobalTheory_Capelli_colOp_apply
import Theorems.Thm_GlobalTheory_Capelli_cross_term
import Theorems.Thm_P2M_GlobalTheory_Capelli_cross_term__f82fd11a3764
import Theorems.Thm_GlobalTheory_Capelli_casimir_colOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Capelli.polar_apply

set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open Capelli
open GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K] {p q n : ℕ}
namespace GlobalTheory.Capelli
theorem _root_.solution (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (y : Fin q × Fin n → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w)
    (P : MvPolynomial σ K) :
    ∑ k, ∑ l, mixedOp K z y k l (mixedOp K z y l k P) =
      (∑ a, ∑ b, rowOp K z a b (rowOp K z b a P) +
        ((n : K) - (p : K)) • ∑ a, rowOp K z a a P) +
      (∑ a, ∑ b, rowOp K y a b (rowOp K y b a P) +
        ((n : K) - (q : K)) • ∑ a, rowOp K y a a P) -
      (2 : K) • ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by
  have c₁ := cross_term z y hzy P
  have c₂ := cross_term' z y hzy P
  simp only [← colOp_apply] at c₁ c₂
  rw [Finset.sum_comm] at c₂
  rw [← casimir_colOp z hz, ← casimir_colOp y hy, two_smul,
    Finset.sum_comm (f := fun k l => colOp K y k l (colOp K y l k P))]
  simp only [mixedOp, LinearMap.sub_apply, map_sub, Finset.sum_sub_distrib]
  rw [c₁, c₂]
  abel
end GlobalTheory.Capelli
