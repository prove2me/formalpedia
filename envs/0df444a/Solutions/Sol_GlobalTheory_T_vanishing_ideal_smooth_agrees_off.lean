-- Prove2me | solution 1 for GlobalTheory.T.vanishing_ideal_smooth_agrees_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:09.822667+00:00
-- url     : https://prove2.me/submissions/db185d5c-381a-4d17-999f-0c3aa6e8cef7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOff
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOffStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_smooth_and_comap_eq


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (A : Closeds X) (O : X.Opens), Smooth (Z.subschemeι ≫ g) → (A : Set X) ⊆ Z.support → (O : Set X) = ((Z.support : Set X) \ A)ᶜ → Smooth ((Scheme.IdealSheafData.vanishingIdeal A).subschemeι ≫ g) ∧ (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by
  first | exact @GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq | exact GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq | (intros; apply GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq <;> assumption)
end _root_.GlobalTheory.T
