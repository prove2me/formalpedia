-- Prove2me | solution 1 for GlobalTheory.natAbs_det_of_transpose_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:57.070859+00:00
-- url     : https://prove2.me/submissions/fc554b65-d517-45f0-bf5d-d62bf463b2f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRepresentativesModSimilitudeTranspose

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
theorem _root_.solution (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    al.det.natAbs = m ^ 2 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one] at h1
  have h2 := congrArg Int.natAbs h1
  simp only [Int.natAbs_mul, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast] at h2
  have h3 : al.det.natAbs ^ 2 = (m ^ 2) ^ 2 := by rw [sq, h2]; ring
  exact Nat.pow_left_injective (by norm_num) h3
end GlobalTheory
