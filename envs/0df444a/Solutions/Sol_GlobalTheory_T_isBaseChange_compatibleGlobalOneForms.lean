-- Prove2me | solution 1 for GlobalTheory.T.isBaseChange_compatibleGlobalOneForms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:22:39.170984+00:00
-- url     : https://prove2.me/submissions/dedec56d-a51e-46d5-ab67-7e29aa7e674c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsBaseChangeCompatibleGlobalOneForms
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsBaseChangeCompatibleGlobalOneFormsStatement
import Theorems.Thm_GlobalTheory_AbCoh_isBaseChange_glob1


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]), (∀ w, e w = w.1 T) → IsBaseChange (F.obj T) e := by
  first | exact @GlobalTheory.AbCoh.isBaseChange_glob1 | exact GlobalTheory.AbCoh.isBaseChange_glob1 | (intros; apply GlobalTheory.AbCoh.isBaseChange_glob1 <;> assumption)
end _root_.GlobalTheory.T
