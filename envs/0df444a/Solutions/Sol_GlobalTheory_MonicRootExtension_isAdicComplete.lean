-- Prove2me | solution 1 for GlobalTheory.MonicRootExtension.isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:54.625702+00:00
-- url     : https://prove2.me/submissions/8db901b9-2628-4593-9675-f0839d42d2d1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
import Theorems.Thm_GlobalTheory_MonicRootExtension_maximalIdeal_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_isPrecomplete_of_basis


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
variable {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (M : A[X]) (hM : M.Monic) (hirr : Irreducible (M.map (residue A)))
include hM hirr
namespace GlobalTheory.MonicRootExtension
theorem _root_.solution [IsLocalRing (AdjoinRoot M)] [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal (AdjoinRoot M)) (AdjoinRoot M) := by
  have : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  rw [← maximalIdeal_eq M hM hirr, IsAdicComplete.map_algebraMap_iff]
  haveI : IsPrecomplete (maximalIdeal A) (AdjoinRoot M) :=
    ReciprocityTheory.ChartRestriction.G.Semi.Nb.isPrecomplete_of_basis _ (AdjoinRoot.powerBasis' hM).basis
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := inferInstance }
end GlobalTheory.MonicRootExtension
