-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.proper_flat_geometricallyIntegral_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:48.54236+00:00
-- url     : https://prove2.me/submissions/ae787197-6b66-4309-83d7-1a4f84a10d95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution :
    IsProper (toSpec W) ∧ Flat (toSpec W) ∧
      (LocallyOfFinitePresentation (toSpec W) ∧ QuasiCompact (toSpec W) ∧
        QuasiSeparated (toSpec W)) ∧
      GeometricallyIntegral (toSpec W) ∧
      (IsUnit W.Δ → SmoothOfRelativeDimension 1 (toSpec W)) :=
  ⟨inferInstance, inferInstance, ⟨inferInstance, inferInstance, inferInstance⟩, inferInstance,
    smoothOfRelativeDimension_toSpec_of_isUnit W⟩
end GlobalTheory.WeierstrassCurve
