-- Prove2me | solution 1 for GlobalTheory.cayleyInv_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:25.106861+00:00
-- url     : https://prove2.me/submissions/0c644c1f-4713-4b77-b920-ff0d2a2b2e09

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
    1 - (X - 1) * (X + 1)⁻¹ = (2:ℂ) • (X + 1)⁻¹ := by
  have h1 : (X + 1) * (X + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (X + 1) - (X - 1) = (1 : Matrix (Fin n) (Fin n) ℂ) + 1 := by abel
  calc 1 - (X - 1) * (X + 1)⁻¹ = (X + 1) * (X + 1)⁻¹ - (X - 1) * (X + 1)⁻¹ := by rw [h1]
    _ = ((X + 1) - (X - 1)) * (X + 1)⁻¹ := by rw [← Matrix.sub_mul]
    _ = (2:ℂ) • (X + 1)⁻¹ := by rw [e, add_mul, one_mul, two_smul]
end GlobalTheory
