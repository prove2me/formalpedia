-- Prove2me | solution 1 for GlobalTheory.TorusDefect.charVal_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:00.6888+00:00
-- url     : https://prove2.me/submissions/659f29f5-19c8-4aa4-b426-eb723d7644db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)
open GlobalTheory GlobalTheory.TorusDefect
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SqZero GlobalTheory.Diag
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
  {C C' : Type} [CommRing C] [Algebra A C] [CommRing C'] [Algebra A C']
namespace GlobalTheory.TorusDefect
theorem _root_.solution (φ : C →ₐ[A] C') (w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) (x : X) :
    charVal (spMap φ ≫ w) x = φ (charVal w x) := by
  refine (GlobalTheory.Diag.left_eq_iff (g := Spec.map (CommRingCat.ofHom (algebraMap A C))) φ.toRingHom ?_
    (spMap φ ≫ w) w).1 ?_ x
  · have h := Over.w (spMap φ)
    rw [spMap_left] at h
    exact h.symm
  · rw [Over.comp_left, spMap_left]
end GlobalTheory.TorusDefect
