-- Prove2me | solution 1 for GlobalTheory.ProjFrac.frac_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:27.813632+00:00
-- url     : https://prove2.me/submissions/95f8224c-47be-4021-bb1e-200c95ed3d90

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
theorem _root_.solution (n : ℕ) :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU ^ n =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U (a ^ n) (b ^ n) (SetLike.pow_mem_graded n ha)
        (SetLike.pow_mem_graded n hb) (fun x hx h => hU hx (x.isPrime.mem_of_pow_mem n h)) := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_pow, _root_.GlobalTheory.ProjFrac.ev_frac, Localization.mk_pow]
  exact (_root_.GlobalTheory.ProjFrac.ev_frac (a := a ^ n) (b := b ^ n)
    (ha := SetLike.pow_mem_graded n ha) (hb := SetLike.pow_mem_graded n hb)
    (hU := fun x hx h => hU hx (x.isPrime.mem_of_pow_mem n h)) x hx).symm
end _root_.GlobalTheory.ProjFrac
end GlobalTheory.ProjFrac
