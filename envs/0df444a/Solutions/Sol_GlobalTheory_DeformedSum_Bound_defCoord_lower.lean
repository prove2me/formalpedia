-- Prove2me | solution 1 for GlobalTheory.DeformedSum.Bound.defCoord_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:03.830155+00:00
-- url     : https://prove2.me/submissions/f78b7a71-45e9-43fe-9086-6e16e964e975

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DeformedSum GlobalTheory.DeformedSum.Bound
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.DeformedSum.Bound
theorem _root_.solution (φ : I → E →+* ℂ) (z : I → ℂ) (x : E) (i : I) {r : ℝ} (hz : ‖z i‖ ≤ r) :
    (1 - r) * ‖φ i x‖ ≤ ‖defCoord φ z x i‖ := by
  have h1 : ‖z i * starRingEnd ℂ (φ i x)‖ = ‖z i‖ * ‖φ i x‖ := by rw [norm_mul, Complex.norm_conj]
  have h2 := norm_sub_norm_le (φ i x) (-(z i * starRingEnd ℂ (φ i x)))
  rw [norm_neg, h1, sub_neg_eq_add] at h2
  unfold defCoord
  nlinarith [norm_nonneg (φ i x)]
end GlobalTheory.DeformedSum.Bound
