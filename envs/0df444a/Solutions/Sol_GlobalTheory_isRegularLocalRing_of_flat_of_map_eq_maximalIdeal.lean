-- Prove2me | solution 1 for GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:22.113246+00:00
-- url     : https://prove2.me/submissions/eb7e67f7-e8d9-48a9-9f1c-f8949b327e94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SerreRegular_pd_flat
import Theorems.Thm_GlobalTheory_isRegularLocalRing_of_hasProjectiveDimensionLE_residueField
import Theorems.Thm_GlobalTheory_exists_hasProjectiveDimensionLE_of_isRegularLocalRing


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
theorem _root_.solution (R S : Type) [CommRing R]
    [IsRegularLocalRing R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [Module.Flat R S] (q : Ideal R) (hq : maximalIdeal S = q.map (algebraMap R S)) :
    IsRegularLocalRing S := by
  obtain ⟨n, hn⟩ := exists_hasProjectiveDimensionLE_of_isRegularLocalRing R (R ⧸ q)
  have h := SerreRegular.pd_flat (B := S) n (ModuleCat.of R (R ⧸ q)) hn
  refine isRegularLocalRing_of_hasProjectiveDimensionLE_residueField S n ?_
  rw [hq]
  exact hasProjectiveDimensionLT_of_iso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S q).toLinearEquiv.toModuleIso.symm _
end GlobalTheory
