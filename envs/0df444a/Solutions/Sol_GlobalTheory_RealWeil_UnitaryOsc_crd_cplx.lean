-- Prove2me | solution 1 for GlobalTheory.RealWeil.UnitaryOsc.crd_cplx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:44.260928+00:00
-- url     : https://prove2.me/submissions/99a0cb5c-87b1-4185-8356-d533192916af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RealWeil.UnitaryOsc
theorem _root_.solution (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (v : EuclideanSpace ℂ ι) :
    crd ι (cplx s h1 h2 v) = I • s *ᵥ crd ι v := by
  rw [← smul_mulVec]
  exact crd_kL (I • s) v
end GlobalTheory.RealWeil.UnitaryOsc
