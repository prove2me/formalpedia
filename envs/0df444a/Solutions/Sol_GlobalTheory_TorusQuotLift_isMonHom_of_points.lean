-- Prove2me | solution 1 for GlobalTheory.TorusQuotLift.isMonHom_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:16:25.489923+00:00
-- url     : https://prove2.me/submissions/bef8ef70-a8cd-44ba-b93e-979d27b6eb08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PreimageEqTopOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsProperAndGeometricallyConnectedOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsAffineOpen
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.TorusQuotLift
namespace GlobalTheory.TorusQuotLift
theorem _root_.solution {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H)
    (key : ∀ {T : Over S} (x y : T ⟶ G), (x * y) ≫ φ = (x ≫ φ) * (y ≫ φ)) : IsMonHom φ := by
  refine ⟨?_, ?_⟩
  ·
    have hsq := key (T := 𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at hsq
    have hid : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) = 1 := by
      have h2 : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) =
          ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * 1 := by rw [← hsq, _root_.mul_one]
      exact mul_left_cancel h2
    have eG : (1 : 𝟙_ (Over S) ⟶ G) = η := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have eH : (1 : 𝟙_ (Over S) ⟶ H) = η := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [eG, eH] at hid
    exact hid
  ·
    have hm := key (T := G ⊗ G) (fst G G) (snd G G)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
    have ht : (φ ⊗ₘ φ) = lift (fst G G ≫ φ) (snd G G ≫ φ) := by
      ext <;> simp
    rw [ht]
    exact hm
end GlobalTheory.TorusQuotLift
