-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.isWeightedHomogeneous_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:38.097334+00:00
-- url     : https://prove2.me/submissions/9448ea0a-5488-4118-8586-7eefea800c99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial
variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {M : Type*} [AddCommMonoid M] (w : σ → M) (m : M)
    (f : K →+* L) {p : MvPolynomial σ K} (hp : p.IsWeightedHomogeneous w m) :
    (map f p).IsWeightedHomogeneous w m := fun d hd =>
  hp fun h => hd (by rw [coeff_map, h, map_zero])
end GlobalTheory.GaloisDescent
