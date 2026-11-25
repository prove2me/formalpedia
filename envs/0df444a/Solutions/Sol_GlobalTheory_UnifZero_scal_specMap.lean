-- Prove2me | solution 1 for GlobalTheory.UnifZero.scal_specMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:35:22.151801+00:00
-- url     : https://prove2.me/submissions/fd3ea4de-9c6d-4035-bcd3-0ad2bb6c29b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Theorems.Thm_GlobalTheory_UnifZero_appTop_scal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable {X Y Y' : Scheme.{0}} {J J' J'' : Type} [Fintype J] [Fintype J'] [Fintype J'']
variable {A B : Type} [CommRing A] [CommRing B]
namespace GlobalTheory.UnifZero
theorem _root_.solution (p : Y ⟶ Spec (CommRingCat.of B)) (φ : A →+* B) (r : A) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
  have nat := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [← appTop_scal, scal, scal, nat]
end GlobalTheory.UnifZero
