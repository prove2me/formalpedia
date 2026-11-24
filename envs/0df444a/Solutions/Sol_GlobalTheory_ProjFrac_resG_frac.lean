-- Prove2me | solution 1 for GlobalTheory.ProjFrac.resG_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:46.845576+00:00
-- url     : https://prove2.me/submissions/e62f58bb-add1-44ec-a0d7-2c4f43f1c282

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
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b} {hU' : U ≤ Proj.basicOpen 𝒜 b'}
namespace GlobalTheory.ProjFrac
theorem _root_.solution (h : V ≤ U) :
    resG (Proj 𝒜) h (frac 𝒜 U a b ha hb hU) = frac 𝒜 V a b ha hb (h.trans hU) := rfl
end GlobalTheory.ProjFrac
