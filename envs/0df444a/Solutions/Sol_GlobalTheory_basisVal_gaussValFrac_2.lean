-- Prove2me | solution 2 for GlobalTheory.basisVal_gaussValFrac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:27.643123+00:00
-- url     : https://prove2.me/submissions/d6aceb60-4b96-44db-bdd6-929ace0e706e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_baseChange_rTensor

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
theorem _root_.solution {O K Γ₀ ι σ F M : Type*} [CommRing O] [Field K] [Algebra O K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F] [Algebra O F]
    [IsScalarTower O (MvPolynomial σ K) F] [AddCommGroup M] [Module O M] (b : Basis ι O M)
    (x : MvPolynomial σ K ⊗[O] M) :
    basisVal (gaussValFrac v σ F) (b.baseChange F)
      ((IsScalarTower.toAlgHom O (MvPolynomial σ K) F).toLinearMap.rTensor M x) =
      tensorContent v b x :=
  basisVal_baseChange_rTensor _ b _ _ (fun a => gaussValFrac_algebraMap v a) x
end GlobalTheory
