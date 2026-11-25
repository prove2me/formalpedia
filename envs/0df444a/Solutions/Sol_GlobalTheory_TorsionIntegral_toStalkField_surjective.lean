-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.toStalkField_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:27:21.528053+00:00
-- url     : https://prove2.me/submissions/047a8f86-92f6-4f34-a7b2-946a8f9b5ead

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_GlobalTheory_UU_IsWt_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
namespace GlobalTheory.TorsionIntegral
theorem _root_.solution (F : Type) [Field F] (z : Spec (CommRingCat.of F)) :
    Function.Surjective (toStalkField F z) := by
  intro v
  obtain ⟨U, hU, a, rfl⟩ := (Spec (CommRingCat.of F)).presheaf.germ_exist v
  obtain rfl : U = ⊤ := top_unique fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  exact ⟨x, rfl⟩
end GlobalTheory.TorsionIntegral
