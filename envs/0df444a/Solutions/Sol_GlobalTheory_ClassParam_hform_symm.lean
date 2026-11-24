-- Prove2me | solution 1 for GlobalTheory.ClassParam.hform_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:30.367811+00:00
-- url     : https://prove2.me/submissions/e4a04284-25b4-4af0-8fc3-0941be6863cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)
namespace GlobalTheory.ClassParam
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) {J : Matrix (Fin r) (Fin r) A} (hJ : IsHerm σ J)
    (x y : Fin r → A) : hform σ J y x = σ (hform σ J x y) := by
  have h : ∀ i j, σ (J i j) = J j i := fun i j => congrFun (congrFun hJ j) i
  simp only [hform, map_sum, map_mul, hσ, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.ClassParam
