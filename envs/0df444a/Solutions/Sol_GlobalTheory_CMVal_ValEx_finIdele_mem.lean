-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.finIdele_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:30.663039+00:00
-- url     : https://prove2.me/submissions/0abaac4d-c731-4d83-a8d5-12a5e3bc644e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_mem_unitI

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
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {P : HeightOneSpectrum (𝓞 E)} {y : (Af E)ˣ} (h : SuppAt P y) (h1 : Valued.v ((y : Af E) P) = 1) :
    finIdele E y ∈ unitI := mem_unitI.2 fun w => by
  change Valued.v ((y : Af E) w) = 1
  by_cases hw : w = P
  · rw [hw, h1]
  · rw [h w hw, map_one]
end GlobalTheory.CMVal.ValEx
