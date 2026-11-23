-- Prove2me | solution 1 for GlobalTheory.MonicRootExtension.maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:47.738292+00:00
-- url     : https://prove2.me/submissions/d6a2701f-1e6e-4a52-8d58-62f7191a34e0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
import Theorems.Thm_GlobalTheory_MonicRootExtension_map_maximalIdeal_isMaximal

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
theorem _root_.solution [IsLocalRing (AdjoinRoot M)] :
    (maximalIdeal A).map (algebraMap A (AdjoinRoot M)) = maximalIdeal (AdjoinRoot M) :=
  IsLocalRing.eq_maximalIdeal (map_maximalIdeal_isMaximal M hM hirr)
end GlobalTheory.MonicRootExtension
