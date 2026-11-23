-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.coe_idealUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:01.630478+00:00
-- url     : https://prove2.me/submissions/c9657194-8599-4264-9880-231d110bd35e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIntegralOfMemRayI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.RayData
theorem _root_.solution (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (idealUnit I hI : FractionalIdeal (𝓞 K)⁰ K) = (I : FractionalIdeal (𝓞 K)⁰ K) := rfl
end GlobalTheory.Mem.RayData
