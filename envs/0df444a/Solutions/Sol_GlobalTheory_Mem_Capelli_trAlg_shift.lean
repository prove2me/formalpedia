-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.trAlg_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:19.737052+00:00
-- url     : https://prove2.me/submissions/d8c87231-7562-42e7-89e0-1f32ca044178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
import Theorems.Thm_GlobalTheory_Mem_Capelli_trAlg_shift_le

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
namespace GlobalTheory.Mem.Capelli
theorem _root_.solution (M : Matrix (Fin n) (Fin n) A) {s : ℂ} (hs : s ≠ 0) (c : ℂ) :
    trAlg (s • M + c • 1) = trAlg M := by
  refine le_antisymm (trAlg_shift_le M s c) ?_
  have h := trAlg_shift_le (s • M + c • (1 : Matrix (Fin n) (Fin n) A)) s⁻¹ (-(s⁻¹ * c))
  rwa [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, neg_smul, add_neg_cancel_right] at h
end GlobalTheory.Mem.Capelli
