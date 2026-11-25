-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothPart.ideal_vanishingIdeal_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:07:07.613016+00:00
-- url     : https://prove2.me/submissions/fc6ff73d-72ce-4929-acf8-2a4afb7703f1

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOff
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothPart
namespace GlobalTheory.CompanionTheory.SmoothPart
theorem _root_.solution {X : Scheme.{0}} (A B : Closeds X) (W : X.affineOpens)
    (h : ∀ x ∈ W.1, x ∈ A ↔ x ∈ B) :
    (Scheme.IdealSheafData.vanishingIdeal A).ideal W =
      (Scheme.IdealSheafData.vanishingIdeal B).ideal W := by
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal]
  congr 1
  ext p
  have hp : W.2.fromSpec p ∈ W.1 := by
    exact (IsAffineOpen.range_fromSpec (U := W.1) W.2).le (Set.mem_range_self p)
  exact h _ hp
end GlobalTheory.CompanionTheory.SmoothPart
