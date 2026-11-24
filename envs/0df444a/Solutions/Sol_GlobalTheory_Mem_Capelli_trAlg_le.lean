-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.trAlg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:26:02.449335+00:00
-- url     : https://prove2.me/submissions/f16e7720-9eb6-484f-9d28-6164297c3063

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
theorem _root_.solution {M : Matrix (Fin n) (Fin n) A} {S : Subalgebra ℂ A} (h : ∀ k, (M ^ (k + 1)).trace ∈ S) :
    trAlg M ≤ S := Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact h k)
end GlobalTheory.Mem.Capelli
