-- Prove2me | solution 1 for GlobalTheory.RealWeil.GaussPairing.posDef_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:52:56.914931+00:00
-- url     : https://prove2.me/submissions/ee0f2221-88e2-4bdd-851e-8afa8260fc3a

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
namespace GlobalTheory.RealWeil.GaussPairing
theorem _root_.solution {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (g : Matrix κ ι ℂ) :
    (1 + gᴴ * g).PosDef :=
  PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self g)
end GlobalTheory.RealWeil.GaussPairing
