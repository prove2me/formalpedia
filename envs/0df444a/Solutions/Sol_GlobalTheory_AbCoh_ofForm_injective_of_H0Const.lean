-- Prove2me | solution 1 for GlobalTheory.AbCoh.ofForm_injective_of_H0Const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:11.941485+00:00
-- url     : https://prove2.me/submissions/0903dab0-3296-4cd5-8e8b-dd4a7bb79127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OfFormInjectiveOfH0Const
import Theorems.Thm_GlobalTheory_CechDR_ofForm_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hF : CohomZeroIsConstants F) : Function.Injective (ofForm F) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  obtain ⟨g, hg, hD⟩ := ofForm_eq_zero.1 hω
  have h0 : d0 F g = 0 := by
    funext T T' φ
    have e : d0 F g T T' φ = g T' - mp F φ (g T) := rfl
    rw [e, ← hg φ, sub_self]; rfl
  obtain ⟨r, hr, -⟩ := hF g h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  rw [← hD T, hr T]
  exact (D R (F.obj T)).map_algebraMap r
end GlobalTheory.AbCoh
