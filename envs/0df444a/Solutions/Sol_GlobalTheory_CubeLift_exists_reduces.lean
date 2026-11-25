-- Prove2me | solution 1 for GlobalTheory.CubeLift.exists_reduces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:23.941606+00:00
-- url     : https://prove2.me/submissions/a97ddcd8-b8a7-4642-82c4-440708f25b24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
import Theorems.Thm_GlobalTheory_CubeLift_exists_pmaps_lift
import Theorems.Thm_GlobalTheory_CubeLift_prod_triv
import Theorems.Thm_GlobalTheory_CubTransport_val_pmaps
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_one_left_comp
import Theorems.Thm_GlobalTheory_UU_surjective_red
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X]
  {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G]
  {G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G₀] [IsCommMonObj G₀]
  {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ red J} {P : CP G} {P₀ : CP G₀}
  {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i₀ : splitTorus _ X ⟶ G₀}
namespace GlobalTheory.CubeLift
theorem _root_.solution (hJ : IsNilpotent J) (h : IsCPMap P₀ P (red J) F hw w)
    (hi : bcMap (red J) X ≫ i.left = i₀.left ≫ F) (σ₀ : CubTriv P₀.c i₀) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : splitTorus _ X ⟶ G).left] ![1, -1]),
      t.IsGen ∧ Reduces w t σ₀ := by
  have := surjective_red hJ
  have hp := (SplitTorus.isPullback_bcMap (red J) X).flip
  have : IsClosedImmersion (bcMap (red J) X) := MorphismProperty.of_isPullback hp inferInstance
  have : Surjective (bcMap (red J) X) := MorphismProperty.of_isPullback hp inferInstance
  have : IsAffine (splitTorus (Spec (CommRingCat.of A)) X).left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of A)) X).hom
  have hc : ∀ k : Fin 2, ![i₀.left, (1 : splitTorus _ X ⟶ G₀).left] k ≫ F =
      bcMap (red J) X ≫ ![i.left, (1 : splitTorus _ X ⟶ G).left] k := fun k => by
    fin_cases k
    · exact hi.symm
    · refine (one_left_comp h.mul _).trans (Eq.trans ?_ (congrArg (bcMap (red J) X ≫ ·) (one_left G _)).symm)
      rw [← SplitTorus.bcMap_hom, Category.assoc]
  obtain ⟨t, ht, H⟩ := exists_pmaps_lift ((isGen_iff w).1 h.gen) P.L.isLB P₀.L.isLB (bcMap (red J) X) hc σ₀.s σ₀.gen
  refine ⟨t, ht, fun T z C₀ C hC₀ hC W hW x => ?_⟩
  simp only [hW]
  exact (CubTransport.val_pmaps hc H x.left hC hC₀).trans
    (congrArg₂ (· * ·) (prod_triv x (fun q => gw w q z (C (q ≫ F)) (C₀ q))) rfl)
end GlobalTheory.CubeLift
