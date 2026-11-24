-- Prove2me | solution 1 for GlobalTheory.TorsExists.exists_isUnit_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:26.104325+00:00
-- url     : https://prove2.me/submissions/4832c798-1c93-4f36-84c2-1cfabdb23acb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
import Theorems.Thm_GlobalTheory_TorsExists_exists_mul_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsExists
theorem _root_.solution {K : Type} [Field K] (D : Matrix Ix Ix K) (hD : D * D = 0)
    (hex : ∀ v : Ix → K, D.mulVec v = 0 → ∃ w, D.mulVec w = v) :
    ∃ G : Matrix Ix Ix K, IsUnit (D * G + G * D).det := by
  obtain ⟨G, hG⟩ := exists_mul_mul_eq D
  refine ⟨G, ?_⟩
  set N := 1 - (D * G + G * D) with hN
  have h1 : D * N = 0 := by
    rw [hN, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, hD, hG]; simp
  have h2 : N * D = 0 := by
    rw [hN, sub_mul, add_mul, mul_assoc G, hD, hG]; simp
  have h3 : N * N = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, hw⟩ := hex (N.mulVec v) (by rw [Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec])
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec, h2,
      Matrix.zero_mulVec, Matrix.zero_mulVec]
  have h4 : (D * G + G * D) * (1 + N) = 1 := by
    have : D * G + G * D = 1 - N := by rw [hN]; abel
    rw [this, sub_mul, mul_add, mul_add, h3]; simp
  exact Matrix.isUnit_det_of_right_inverse h4
end GlobalTheory.TorsExists
