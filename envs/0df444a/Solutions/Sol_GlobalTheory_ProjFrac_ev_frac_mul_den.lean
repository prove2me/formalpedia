-- Prove2me | solution 1 for GlobalTheory.ProjFrac.ev_frac_mul_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:30.319801+00:00
-- url     : https://prove2.me/submissions/888d7aa5-4c8d-46b8-ac2f-d2fc3173a89f

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
theorem _root_.solution (x : Proj 𝒜) (hx : x ∈ U) :
    ev 𝒜 U x hx (frac 𝒜 U a b ha hb hU) * algebraMap A _ b = algebraMap A _ a := by
  rw [ev_frac, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ a (⟨b, hU hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)
end GlobalTheory.ProjFrac
