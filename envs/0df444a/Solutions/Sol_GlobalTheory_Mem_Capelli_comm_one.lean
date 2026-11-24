-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.comm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:00.969912+00:00
-- url     : https://prove2.me/submissions/6b156525-3d5d-4dbb-8d46-d89f94f7a8ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)
omit [Algebra ℂ A]
include hdd hdx
namespace GlobalTheory.Mem.Capelli
theorem _root_.solution (a : Fin m) (l i j : Fin n) :
    D a l * (X * D) i j = (X * D) i j * D a l + if i = l then D a j else 0 := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, hdx, add_mul, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => by rw [mul_assoc, mul_assoc, hdd]
  · by_cases h : i = l <;> simp [h]
end GlobalTheory.Mem.Capelli
