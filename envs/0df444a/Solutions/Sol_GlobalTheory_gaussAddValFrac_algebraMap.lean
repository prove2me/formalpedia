-- Prove2me | solution 1 for GlobalTheory.gaussAddValFrac_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:46.372847+00:00
-- url     : https://prove2.me/submissions/e0a69dcf-b546-47f7-942d-43e5cf10baf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module IsDedekindDomain
namespace GlobalTheory
theorem _root_.solution {K Γ σ F : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial σ K) : gaussAddValFrac v σ F (algebraMap _ F f) = gaussAddVal v f :=
  gaussValFrac_algebraMap (AddValuation.toValuation v) f
end GlobalTheory
