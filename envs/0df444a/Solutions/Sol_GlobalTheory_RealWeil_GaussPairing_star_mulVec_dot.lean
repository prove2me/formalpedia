-- Prove2me | solution 1 for GlobalTheory.RealWeil.GaussPairing.star_mulVec_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:52:57.671551+00:00
-- url     : https://prove2.me/submissions/8e92e1bc-6b7a-4588-9819-9123a9acfb8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingOfNormSqEqSumComplexCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.GaussPairing
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type} [Fintype ι]
namespace GlobalTheory.RealWeil.GaussPairing
theorem _root_.solution (g : Matrix ι ι ℂ) (z w : ι → ℂ) :
    star (g *ᵥ z) ⬝ᵥ w = star z ⬝ᵥ gᴴ *ᵥ w := by
  rw [star_mulVec, dotProduct_mulVec]
end GlobalTheory.RealWeil.GaussPairing
