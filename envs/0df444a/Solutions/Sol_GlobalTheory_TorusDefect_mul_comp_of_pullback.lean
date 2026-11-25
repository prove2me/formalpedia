-- Prove2me | solution 1 for GlobalTheory.TorusDefect.mul_comp_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:52:21.58045+00:00
-- url     : https://prove2.me/submissions/3db36836-044f-4007-9ed8-c8b935ab5574

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
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
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
theorem _root_.solution {S S' : Scheme.{0}} (i : S' ⟶ S) {G H : Over S} [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom ((Over.pullback i).map f)] {W : Scheme.{0}} (s : W ⟶ S') (z : W ⟶ S)
    (hz : z = s ≫ i) (a b : Over.mk z ⟶ G) : (a * b) ≫ f = a ≫ f * b ≫ f := by
  subst hz
  obtain ⟨a', ha'⟩ : ∃ a' : Over.mk s ⟶ (Over.pullback i).obj G,
      a'.left ≫ pullback.fst G.hom i = a.left :=
    ⟨Over.homMk (pullback.lift a.left s (Over.w a)) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Over.mk s ⟶ (Over.pullback i).obj G,
      b'.left ≫ pullback.fst G.hom i = b.left :=
    ⟨Over.homMk (pullback.lift b.left s (Over.w b)) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  have hpf : ((Over.pullback i).map f).left ≫ pullback.fst H.hom i = pullback.fst G.hom i ≫ f.left :=
    pullback.lift_fst _ _ _
  have h1 := SplitTorus.mul_left_comp_fst G i a' b' a b ha'.symm hb'.symm
  have h2 := SplitTorus.mul_left_comp_fst H i (a' ≫ (Over.pullback i).map f)
    (b' ≫ (Over.pullback i).map f) (a ≫ f) (b ≫ f)
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc, ha'])
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc, hb'])
  apply Over.OverMorphism.ext
  rw [h2, ← MonObj.mul_comp, Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc,
    ← h1]
end GlobalTheory.TorusDefect
