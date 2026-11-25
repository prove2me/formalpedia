-- Prove2me | solution 1 for GlobalTheory.T.kernelPolarisation_trivial_of_sections_vanish_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:53:20.949442+00:00
-- url     : https://prove2.me/submissions/1f8a7573-1201-4f91-bbe6-ea1477a6aec2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_KernelPolarisationTrivialOfSectionsVanishZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_KernelPolarisationTrivialOfSectionsVanishZeroStatement
import Theorems.Thm_GlobalTheory_kTriv_of_sections_vanish_on_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → (∀ (R' : Type) [CommRing R'] (f : Sp R' ⟶ S) (Y : Scheme.{0}) (φ : Y ⟶ A.left) (q : Y ⟶ Sp R'), IsPullback φ q A.hom f → ∀ (s : (L.pull φ).Sec) (T : Scheme.{0}) (t : T ⟶ Y) (j : (L.pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ (L.pull φ).U j), t ≫ φ = t ≫ φ ≫ A.hom ≫ eSec A → (t.appLE ((L.pull φ).U j) ⊤ h).hom (s.f j) = 0) → Out.KTriv A L := by
  first | exact @GlobalTheory.kTriv_of_sections_vanish_on_zero | exact GlobalTheory.kTriv_of_sections_vanish_on_zero | (intros; apply GlobalTheory.kTriv_of_sections_vanish_on_zero <;> assumption)
end _root_.GlobalTheory.T
