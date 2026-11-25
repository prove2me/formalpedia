-- Prove2me | solution 1 for GlobalTheory.HolHomOnto.exists_isDerivAt_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:05.999674+00:00
-- url     : https://prove2.me/submissions/cbd22810-44af-4251-bd04-3bd4f1d35de1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsDerivAtOfSurjective
import Theorems.Thm_GlobalTheory_HolHomOnto_exists_coords
import Theorems.Thm_GlobalTheory_AffinePoints_volume_image_eq_zero_of_finrank_lt
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_HolAt_exists_isDerivAt
import Theorems.Thm_GlobalTheory_HolHom_HolAt_precomp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_over
import Theorems.Thm_GlobalTheory_HolHom_eq_of_fderiv_eq
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_of_holAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HolHomOnto
open GlobalTheory.TangentOrigin GlobalTheory.HolHom
namespace GlobalTheory.HolHomOnto
theorem _root_.solution : ∀ (G : Over (Sp ℂ)) [GrpObj G] (y : Sp ℂ ⟶ Sp ℂ), y = 𝟙 _ → Smooth G.hom → ∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) → ∀ v : Sp (DualNumber ℂ) ⟶ G.left, v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (e 0).left → ∃ w, GlobalTheory.HolHom.IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w v := by
  intro G _ y hy hs g e he hsurj hol v hv hv0
  subst hy
  obtain ⟨n, U, t, W, h0, hW, hW0, hp, hext⟩ := exists_coords G.hom (e 0).left (Over.w (e 0))
  have hA := holAt_of_isHolTo hol (Set.mem_univ 0)
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (fun z => valAt' (e z).left U (t i)) 0).toLinearMap
  have hover : ∀ {w u}, IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w u →
      u ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := fun hu =>
    (IsDerivAt.over (a := e) hu).trans (Category.comp_id _)
  have key : ∀ (w : Fin g → ℂ) (u : Sp (DualNumber ℂ) ⟶ G.left), u ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) →
      spMap fstC ≫ u = (e 0).left → (L w = fun i => (valR u U (t i)).snd) →
      IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w u := by
    intro w u hu hu0 hL
    obtain ⟨u', hu'⟩ := hA.exists_isDerivAt w
    have : u = u' := hext u u' hu (hover hu') hu0 hu'.1 fun i =>
      (congrFun hL i).symm.trans (hu'.2 U h0 (t i)).symm
    exact this ▸ hu'
  suffices hL : Function.Surjective L by
    obtain ⟨w, hw⟩ := hL fun i => (valR v U (t i)).snd
    exact ⟨w, key w v hv hv0 hw⟩
  obtain ⟨ρ, hρ⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let P : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (ρ ∘ₗ L.rangeRestrict)
  have hLP : ∀ z, L (P z) = L z := fun z =>
    congrArg Subtype.val (DFunLike.congr_fun hρ (L.rangeRestrict z))
  have hfac : e = fun z => e (P z) := by
    refine eq_of_fderiv_eq he (fun z w => by rw [map_add, he]) hol
      (isHolTo_of_holAt isOpen_univ fun z _ =>
        (holAt_of_isHolTo hol (Set.mem_univ (P z))).precomp P.differentiableAt) fun V hV f => ?_
    ext1 z
    have h1 : HasFDerivAt (fun z => valAt' (e z).left V f) (fderiv ℂ (fun z => valAt' (e z).left V f) 0) (P 0) := by
      rw [map_zero]; exact ((hA V hV).2 f).hasFDerivAt
    refine Eq.trans ?_ (congrArg (· z) (h1.comp 0 P.hasFDerivAt).fderiv).symm
    obtain ⟨u, hu⟩ := hA.exists_isDerivAt z
    have hu' := key (P z) u (hover hu) hu.1 ((hLP z).trans (funext fun i => (hu.2 U h0 (t i)).symm))
    exact (hu.2 V hV f).symm.trans (hu'.2 V hV f)
  have hol' : IsHolTo Set.univ (fun r : LinearMap.range L => (show Sp ℂ ⟶ G.left from (e (ρ r)).left)) :=
    isHolTo_of_holAt isOpen_univ fun r _ =>
      (holAt_of_isHolTo hol (Set.mem_univ (ρ r))).precomp (LinearMap.toContinuousLinearMap ρ).differentiableAt
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have hlt : Module.finrank ℂ (LinearMap.range L) < n := by
    simpa using Submodule.finrank_lt hne
  have hnull := AffinePoints.volume_image_eq_zero_of_finrank_lt hlt
    (f := fun r i => valAt' (e (ρ r)).left U (t i)) (differentiableOn_pi.2 fun i => (hol' U (t i)).2)
  refine (hW.measure_pos MeasureTheory.volume ⟨0, hW0⟩).ne' (MeasureTheory.measure_mono_null (fun w hw => ?_) hnull)
  obtain ⟨p, hps, hpU, hpt⟩ := hp w hw
  obtain ⟨z, hz⟩ := hsurj (Over.homMk p hps)
  have hz' : (e (ρ (L.rangeRestrict z))).left = p :=
    congrArg (·.left) ((congrFun hfac z).symm.trans hz)
  refine ⟨L.rangeRestrict z, ⟨trivial, ?_⟩, funext fun i => ?_⟩
  · subst hz'
    exact hpU
  · subst hz'
    exact hpt i
end GlobalTheory.HolHomOnto
