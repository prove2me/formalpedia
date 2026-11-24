-- Prove2me | solution 1 for GlobalTheory.ProjFrac.basicOpen_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:49.450575+00:00
-- url     : https://prove2.me/submissions/0ec427d6-224e-4813-a908-709c8eb726da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Theorems.Thm_GlobalTheory_ProjFrac_ev_resG
import Theorems.Thm_GlobalTheory_ProjFrac_resG_frac

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
theorem _root_.solution :
    (Proj 𝒜).basicOpen (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU) =
      U ⊓ Proj.basicOpen 𝒜 a := by
  ext x
  constructor
  · intro hx
    have hVU : (Proj 𝒜).basicOpen (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU) ≤ U :=
      (Proj 𝒜).basicOpen_le _
    have hxU : x ∈ U := hVU hx
    have hres : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG (Proj 𝒜) hVU (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) :=
      (Proj 𝒜).toRingedSpace.isUnit_res_basicOpen _
    have hunit := hres.map (_root_.GlobalTheory.ProjFrac.ev 𝒜 _ x hx)
    have heq : _root_.GlobalTheory.ProjFrac.ev 𝒜 _ x hx
        (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG (Proj 𝒜) hVU (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) =
        Localization.mk a ⟨b, hU hxU⟩ :=
      (_root_.GlobalTheory.ProjFrac.ev_resG hVU x hx _).trans
        (_root_.GlobalTheory.ProjFrac.ev_frac x hxU)
    rw [heq] at hunit
    have hnum : IsUnit (algebraMap A (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) a) := by
      rw [← IsLocalization.mk'_spec (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) a
        (⟨b, hU hxU⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl), ← Localization.mk_eq_mk']
      exact hunit.mul (IsLocalization.map_units _ _)
    exact ⟨hxU, (IsLocalization.AtPrime.isUnit_to_map_iff _ _ a).1 hnum⟩
  · rintro ⟨hxU, hxa⟩
    have hWU : U ⊓ Proj.basicOpen 𝒜 a ≤ U := inf_le_left
    have hunit : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG (Proj 𝒜) hWU
        (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) := by
      rw [_root_.GlobalTheory.ProjFrac.resG_frac]
      exact IsUnit.of_mul_eq_one (_root_.GlobalTheory.ProjFrac.frac 𝒜 _ b a hb ha inf_le_right)
        ((_root_.GlobalTheory.ProjFrac.frac_mul_eq (a'' := a) (b'' := a) (ha'' := ha) (hb'' := ha)
          (hU'' := inf_le_right) (by ring)).trans _root_.GlobalTheory.ProjFrac.frac_self)
    have hb := (Proj 𝒜).basicOpen_of_isUnit hunit
    have hx : x ∈ U ⊓ Proj.basicOpen 𝒜 a := ⟨hxU, hxa⟩
    rw [← hb] at hx
    exact ((Proj 𝒜).basicOpen_res _ (homOfLE hWU).op ▸ hx).2
end _root_.GlobalTheory.ProjFrac
end GlobalTheory.ProjFrac
