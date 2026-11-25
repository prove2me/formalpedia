-- Prove2me | solution 1 for GlobalTheory.T.preimage_generic_fiber_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:23:24.864537+00:00
-- url     : https://prove2.me/submissions/335ccdc6-fb6e-476b-bd29-eda0d5471842

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PreimageGenericFiberIsOpen
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PreimageGenericFiberIsOpenStatement
import Theorems.Thm_GlobalTheory_GenericFibreOpen_isOpen_preimage_range_spMap_fraction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R] [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by
  first | exact @GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction | exact GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction | (intros; apply GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction <;> assumption)
end _root_.GlobalTheory.T
