-- Prove2me | solution 1 for GlobalTheory.RealWeil.UnitaryOsc.omJ_cplx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:17.275572+00:00
-- url     : https://prove2.me/submissions/b325b2b0-0b24-465e-8651-107ae6455512

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_crd_cplx
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_cplx_cplx
import Theorems.Thm_GlobalTheory_RealWeil_omJ_skew


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
theorem _root_.solution (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (x y : EuclideanSpace ℂ ι) :
    omJ (cplx s h1 h2) x y = (star (crd ι y) ⬝ᵥ s *ᵥ crd ι x).im := by
  rw [omJ_skew (cplx_cplx s h1 h2), omJ, inner_crd, crd_cplx, dotProduct_smul]
  simp
end GlobalTheory.RealWeil.UnitaryOsc
