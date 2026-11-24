-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.trace_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:50.548902+00:00
-- url     : https://prove2.me/submissions/063e18ba-c365-4a0e-b886-93c92cadbf20

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
namespace GlobalTheory.Mem.Capelli
theorem _root_.solution (M : Matrix (Fin n) (Fin n) A) (k : ℕ) : (M ^ k).trace ∈ trAlg M := by
  cases k with
  | zero => simpa using natCast_mem (trAlg M) n
  | succ k => exact Algebra.subset_adjoin ⟨k, rfl⟩
end GlobalTheory.Mem.Capelli
