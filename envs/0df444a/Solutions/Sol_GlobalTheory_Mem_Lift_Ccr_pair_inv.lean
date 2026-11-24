-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.Ccr.pair_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:36:08.980186+00:00
-- url     : https://prove2.me/submissions/ee3073a2-358b-4f15-9535-7af5daea177f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsCCRXOpDOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.Ccr
namespace GlobalTheory.Mem.Lift.Ccr
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (k l : ι) :
    star (H⁻¹ *ᵥ Pi.single l 1) ⬝ᵥ H *ᵥ Pi.single k 1 = if k = l then (1 : ℂ) else 0 := by
  rw [star_mulVec, conjTranspose_nonsing_inv, hH, ← dotProduct_mulVec, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), one_mulVec, dotProduct_single]
  by_cases h : k = l <;> simp [h]
end GlobalTheory.Mem.Lift.Ccr
