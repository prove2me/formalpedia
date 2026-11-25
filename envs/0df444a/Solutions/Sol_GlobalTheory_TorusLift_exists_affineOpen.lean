-- Prove2me | solution 1 for GlobalTheory.TorusLift.exists_affineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:45.206467+00:00
-- url     : https://prove2.me/submissions/c23a70d4-b14d-43aa-9d5f-f7c17914426a

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
import Theorems.Thm_GlobalTheory_TorusLift_surjective_specMap
import Theorems.Thm_GlobalTheory_IsCoaction_injective
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_isAffine_of_isAffine_pullback_quotient_of_isNilpotent
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
open GlobalTheory GlobalTheory.TorusLift
namespace GlobalTheory.TorusLift
theorem _root_.solution {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (G : Over (Spec (CommRingCat.of A)))
    (W : (pullback G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).Opens)
    (hW : IsAffineOpen W) : ∃ U : G.left.Opens, IsAffineOpen U ∧
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ U = W := by
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)
  let i := pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have hemb : Topology.IsClosedEmbedding i.base := i.isClosedEmbedding
  have hbij : Function.Bijective i.base := ⟨hemb.injective, i.surjective⟩
  have hopen : IsOpen (i.base '' (W : Set _)) := by
    rw [← compl_compl (i.base '' (W : Set _)), ← Set.image_compl_eq hbij]
    exact (hemb.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl
  let U : G.left.Opens := ⟨_, hopen⟩
  have hU : i ⁻¹ᵁ U = W := by
    ext x
    change i.base x ∈ i.base '' (W : Set _) ↔ x ∈ W
    exact hemb.injective.mem_set_image
  refine ⟨U, ?_, hU⟩
  have hW' : IsAffineOpen (i ⁻¹ᵁ U) := hU ▸ hW
  have : IsAffine (pullback (U.ι ≫ G.hom) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    have : IsAffine (i ⁻¹ᵁ U) := hW'
    exact IsAffine.of_isIso ((pullbackRightPullbackFstIso G.hom _ U.ι).inv ≫
      (pullbackSymmetry _ _).hom ≫ (pullbackRestrictIsoRestrict i U).hom)
  exact GlobalTheory.isAffine_of_isAffine_pullback_quotient_of_isNilpotent A J hJ (Over.mk (U.ι ≫ G.hom)) this
end GlobalTheory.TorusLift
