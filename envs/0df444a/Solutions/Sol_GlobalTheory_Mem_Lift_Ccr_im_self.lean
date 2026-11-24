-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.Ccr.im_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:36:01.095181+00:00
-- url     : https://prove2.me/submissions/71f8d722-33f8-46c1-b6bd-fee574e7bc3b

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
theorem _root_.solution {ι : Type} [Fintype ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (x : ι → ℂ) :
    (star x ⬝ᵥ H *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ H *ᵥ x) = star x ⬝ᵥ H *ᵥ x := by
    rw [← star_dotProduct_star, star_star, star_mulVec, hH, dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h
end GlobalTheory.Mem.Lift.Ccr
