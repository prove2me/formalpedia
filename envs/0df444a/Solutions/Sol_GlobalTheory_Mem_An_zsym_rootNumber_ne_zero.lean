-- Prove2me | solution 1 for GlobalTheory.Mem.An.zsym_rootNumber_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:38.194137+00:00
-- url     : https://prove2.me/submissions/10ef5d38-b94c-4c62-bb83-aa25028bc2b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
variable {q : ℕ}
variable [NeZero q]
namespace GlobalTheory.Mem.An
theorem _root_.solution {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 := by
  intro h
  have h1 := hχ.completedLFunction_one_sub (-1)
  rw [h, mul_zero, zero_mul] at h1
  have h2 := χ.LFunction_eq_completed_div_gammaFactor (1 - -1) (Or.inl (by norm_num))
  rw [h1, zero_div] at h2
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by norm_num)) (by norm_num) h2
end GlobalTheory.Mem.An
