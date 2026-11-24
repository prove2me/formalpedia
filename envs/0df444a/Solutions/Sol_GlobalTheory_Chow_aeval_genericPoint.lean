-- Prove2me | solution 1 for GlobalTheory.Chow.aeval_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:57.354101+00:00
-- url     : https://prove2.me/submissions/5df363df-12ee-4040-8f38-3415f4a1e58b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {σ β : Type*} [Fintype σ]
variable {K : Type*} [CommRing K]
omit [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution (p : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) :
    aeval (genericPoint p) g = algebraMap (MvPolynomial σ K ⧸ p) _ (Ideal.Quotient.mk p g) := by
  have : (aeval (genericPoint p) : _ →ₐ[K] _) =
      (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p) _).comp (Ideal.Quotient.mkₐ K p) := by
    ext j; simp [genericPoint]
  exact DFunLike.congr_fun this g
end GlobalTheory.Chow
