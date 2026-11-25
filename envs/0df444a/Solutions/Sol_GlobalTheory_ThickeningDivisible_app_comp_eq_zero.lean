-- Prove2me | solution 1 for GlobalTheory.ThickeningDivisible.app_comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:32:58.946358+00:00
-- url     : https://prove2.me/submissions/ea06b6b4-be07-450a-8456-dcd5102bd13e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecDivOfThickenings
import Theorems.Thm_GlobalTheory_ThickeningDivisible_gs_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_constFn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
open ThickeningDetermines ThickeningClosed
namespace GlobalTheory.ThickeningDivisible
theorem _root_.solution {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (a : Y ⟶ X) (b : Z ⟶ Y) (r : R)
    (hr : ∀ z, cst (b ≫ a ≫ p) z r = 0) (U : X.Opens) (f : Γ(X, U)) (t : Γ(Y, a ⁻¹ᵁ U))
    (h : (a.app U).hom f = resTop _ (scal (a ≫ p) r) * t) : ((b ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz ↦ ?_
  have hz' : b z ∈ a ⁻¹ᵁ U := hz
  have h' : (a.app U).hom f = constFn (a ≫ p) _ r * t := h
  rw [gs_pull (𝟙 Z) (b ≫ a) z U hz, Category.id_comp, ← gs_pull b a z U hz, h', gs_mul _ _ _ hz',
    gs_constFn _ _ _ _ hz', hr, zero_mul, gs_zero]
end GlobalTheory.ThickeningDivisible
