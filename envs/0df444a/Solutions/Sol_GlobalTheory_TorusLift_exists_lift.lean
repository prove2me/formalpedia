-- Prove2me | solution 1 for GlobalTheory.TorusLift.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:43.080519+00:00
-- url     : https://prove2.me/submissions/5ee9b6fe-fb37-48b9-b314-c577814457c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PreimageEqTopOfSurjective
import Theorems.Thm_GlobalTheory_TorusLift_map_left_fst
import Theorems.Thm_GlobalTheory_TorusLift_hom_ext_fst
import Theorems.Thm_GlobalTheory_TorusLift_preimage_eq_top_of_surjective
import Theorems.Thm_GlobalTheory_TorusLift_surjective_specMap
import Theorems.Thm_GlobalTheory_TorusLift_isAffine_splitTorus
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main
import Theorems.Thm_GlobalTheory_NilpotentLift_main
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
open GlobalTheory GlobalTheory.TorusLift
namespace GlobalTheory.TorusLift
theorem _root_.solution {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [Smooth G.hom]
    (g : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G)
    {W : G.left.Opens} (hW : IsAffineOpen W) (hg : (g.left ≫ pullback.fst _ _) ⁻¹ᵁ W = ⊤) :
    ∃ f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, f.left ⁻¹ᵁ W = ⊤ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f = g := by
  have := isAffine_splitTorus A X
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)
  obtain ⟨f, hf⟩ := GlobalTheory.NilpotentLift.main A J hJ G (splitTorus (Spec (CommRingCat.of A)) X)
    (g.left ≫ pullback.fst _ _) (by
      have hw := Over.w g
      simp only [Over.pullback_obj_hom] at hw
      rw [Category.assoc, pullback.condition (f := G.hom), reassoc_of% hw]
      exact pullback.condition.symm) ⟨W, hW, hg⟩
  refine ⟨f, ?_, ?_⟩
  · apply preimage_eq_top_of_surjective
      (pullback.fst (splitTorus (Spec (CommRingCat.of A)) X).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    rw [hf]
    exact hg
  · apply hom_ext_fst
    rw [map_left_fst, hf]
end GlobalTheory.TorusLift
