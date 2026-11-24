-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.LSeries_coef_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:17.226172+00:00
-- url     : https://prove2.me/submissions/466076a9-e284-45db-a357-5b7c5368a139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
namespace GlobalTheory.Mem
namespace RayData
theorem _root_.solution {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
    (χ : D.G →* ℂˣ) (s : ℂ) (h : ∀ c, LSeriesSummable (D.cnt c) s) :
    LSeries (D.coef χ) s = ∑ c, (χ c : ℂ) * LSeries (D.cnt c) s := by
  have e : D.coef χ = ∑ c, (χ c : ℂ) • D.cnt c := by
    funext n
    simp [RayData.coef, Finset.sum_apply]
  rw [e, LSeries_sum (fun c _ => (h c).smul _)]
  simp [LSeries_smul]
end RayData
end GlobalTheory.Mem
