-- Prove2me | solution 1 for GlobalTheory.isRegularRing_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:17:38.816699+00:00
-- url     : https://prove2.me/submissions/4b5617c7-36f5-486b-b952-b3ceef18d685

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_isRegularLocalRing_of_flat_of_map_eq_maximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] [IsRegularLocalRing R] :
    IsRegularRing R := by
  rw [isRegularRing_iff]
  intro p _
  exact isRegularLocalRing_of_flat_of_map_eq_maximalIdeal R _ p
    Localization.AtPrime.map_eq_maximalIdeal.symm
end GlobalTheory
