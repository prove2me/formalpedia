-- Prove2me | solution 1 for GlobalTheory.ProjFrac.frac_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:40:56.771595+00:00
-- url     : https://prove2.me/submissions/4331a380-24ee-484a-9a9e-96e780c4721d

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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {𝒜}
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'}
namespace GlobalTheory.ProjFrac
namespace _root_.GlobalTheory.ProjFrac
theorem _root_.solution {a₂ : A} {ha₂ : a₂ ∈ 𝒜 d} :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U (a + a₂) b (add_mem ha ha₂) hb hU =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU +
        _root_.GlobalTheory.ProjFrac.frac 𝒜 U a₂ b ha₂ hb hU := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_add, _root_.GlobalTheory.ProjFrac.ev_frac, _root_.GlobalTheory.ProjFrac.ev_frac,
    _root_.GlobalTheory.ProjFrac.ev_frac, Localization.add_mk_self]
end _root_.GlobalTheory.ProjFrac
end GlobalTheory.ProjFrac
