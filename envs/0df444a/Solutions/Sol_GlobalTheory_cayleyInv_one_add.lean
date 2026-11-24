-- Prove2me | solution 1 for GlobalTheory.cayleyInv_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:03.658337+00:00
-- url     : https://prove2.me/submissions/0edcb540-fbeb-46b8-9890-19f09b5dc17c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory
variable {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    1 + (X - 1) * (X + 1)⁻¹ = X * ((2:ℂ) • (X + 1)⁻¹) := by
  have h1 : (X + 1) * (X + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (X + 1) + (X - 1) = X + X := by abel
  calc 1 + (X - 1) * (X + 1)⁻¹ = (X + 1) * (X + 1)⁻¹ + (X - 1) * (X + 1)⁻¹ := by rw [h1]
    _ = (X + X) * (X + 1)⁻¹ := by rw [← add_mul, e]
    _ = X * ((2:ℂ) • (X + 1)⁻¹) := by rw [mul_smul_comm, two_smul, add_mul]
end GlobalTheory
