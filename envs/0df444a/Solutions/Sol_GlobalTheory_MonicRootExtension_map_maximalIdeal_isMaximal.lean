-- Prove2me | solution 1 for GlobalTheory.MonicRootExtension.map_maximalIdeal_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:33.030805+00:00
-- url     : https://prove2.me/submissions/29914f20-05ee-465b-b314-107eb73ece49

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.MonicRootExtension
variable {A : Type} [CommRing A] [IsLocalRing A] (M : A[X]) (hM : M.Monic)
  (hirr : Irreducible (M.map (residue A)))
include hM hirr
namespace GlobalTheory.MonicRootExtension
theorem _root_.solution :
    ((maximalIdeal A).map (algebraMap A (AdjoinRoot M))).IsMaximal := by
  haveI : Fact (Irreducible (M.map (residue A))) := ⟨hirr⟩
  have hR : IsField (AdjoinRoot (M.map (residue A))) := Field.toIsField _
  rw [AdjoinRoot.algebraMap_eq]
  exact Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap M (maximalIdeal A)).toRingEquiv.toMulEquiv)
end GlobalTheory.MonicRootExtension
