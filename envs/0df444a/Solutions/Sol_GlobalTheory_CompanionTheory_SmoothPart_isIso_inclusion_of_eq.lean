-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothPart.isIso_inclusion_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:27.041472+00:00
-- url     : https://prove2.me/submissions/d58371e1-4535-4ada-a760-366bcd25d080

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothPart
namespace GlobalTheory.CompanionTheory.SmoothPart
theorem _root_.solution {X : Scheme.{0}} {I J : X.IdealSheafData} (h : I ≤ J) (e : I = J) :
    IsIso (Scheme.IdealSheafData.inclusion h) := by
  subst e
  rw [Scheme.IdealSheafData.inclusion_id]
  infer_instance
end GlobalTheory.CompanionTheory.SmoothPart
