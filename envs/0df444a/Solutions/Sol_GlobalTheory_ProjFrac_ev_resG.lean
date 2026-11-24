-- Prove2me | solution 1 for GlobalTheory.ProjFrac.ev_resG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:30.942855+00:00
-- url     : https://prove2.me/submissions/e010d541-d4f2-40d1-ac3e-42c4910075c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
open GlobalTheory GlobalTheory.ProjFrac
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {𝒜}
namespace GlobalTheory.ProjFrac
theorem _root_.solution {U V : (Proj 𝒜).Opens} (h : V ≤ U) (x : Proj 𝒜) (hx : x ∈ V) (s : Γ(Proj 𝒜, U)) :
    ev 𝒜 V x hx (resG (Proj 𝒜) h s) = ev 𝒜 U x (h hx) s := rfl
end GlobalTheory.ProjFrac
