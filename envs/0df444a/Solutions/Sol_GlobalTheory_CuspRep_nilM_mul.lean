-- Prove2me | solution 1 for GlobalTheory.CuspRep.nilM_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:05:36.437236+00:00
-- url     : https://prove2.me/submissions/2377f59a-4264-4347-bdc9-c1c8c1c2da27

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsOpenStabilizer
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_IsOpenStabOfMemNhds
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CuspRep
variable {a : ℕ} {R : Type} [CommRing R]
namespace GlobalTheory.CuspRep
theorem _root_.solution {r : ℕ} (x y : BlockIx a r → R) : nilM x * nilM y = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : l.val < r
  · simp [nilM, not_le.2 h]
  · simp [nilM, h]
end GlobalTheory.CuspRep
