-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:48.72827+00:00
-- url     : https://prove2.me/submissions/d9b51f3d-7f8d-45a2-b6ca-44e5dc438e39

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOff
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_radical_eq_of_isReduced
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_ideal_vanishingIdeal_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_exists_isOpenImmersion_of_comap_eq
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced


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
theorem _root_.solution : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData)
    (A : Closeds X) (O : X.Opens), Smooth (Z.subschemeι ≫ g) → (A : Set X) ⊆ Z.support →
    (O : Set X) = ((Z.support : Set X) \ A)ᶜ →
    Smooth ((Scheme.IdealSheafData.vanishingIdeal A).subschemeι ≫ g) ∧
      (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by
  intro k _ X g Z A O hs hA hO
  have hred : IsReduced Z.subscheme := GlobalTheory.isReduced_of_smooth_of_isReduced (Z.subschemeι ≫ g)
  have hZ : Scheme.IdealSheafData.vanishingIdeal Z.support = Z := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support, radical_eq_of_isReduced]
  have hAO : ∀ x, x ∈ O → (x ∈ A ↔ x ∈ Z.support) := by
    intro x hx
    have hx' : x ∈ (O : Set X) := hx
    rw [hO] at hx'
    refine ⟨fun h => hA h, fun h => ?_⟩
    by_contra hn
    exact hx' ⟨h, hn⟩
  have key : ∀ W : X.affineOpens, W.1 ≤ O →
      (Scheme.IdealSheafData.vanishingIdeal A).ideal W = Z.ideal W := by
    intro W hW
    rw [ideal_vanishingIdeal_congr A Z.support W (fun x hx => hAO x (hW hx)), hZ]
  have hcomap : (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by
    ext U : 2
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      key _ (Scheme.Opens.ι_image_le O U.1)]
  refine ⟨?_, hcomap⟩
  have hsub : (((Scheme.IdealSheafData.vanishingIdeal A).support : Closeds X) : Set X) ⊆ O := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hO]
    exact fun x hx hx' => hx'.2 hx
  obtain ⟨h, hh, hc⟩ := exists_isOpenImmersion_of_comap_eq _ Z O hsub hcomap
  rw [← hc, Category.assoc]
  infer_instance
end GlobalTheory.CompanionTheory.SmoothPart
