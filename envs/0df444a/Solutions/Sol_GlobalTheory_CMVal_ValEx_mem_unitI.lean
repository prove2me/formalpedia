-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.mem_unitI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:22.897343+00:00
-- url     : https://prove2.me/submissions/e3ca1ef7-f46b-49cf-aa50-b51b054365db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {x : Ideles E} : x ∈ unitI ↔ ∀ P, Valued.v ((finOf x : Af E) P) = 1 := by
  simp only [unitI, Subgroup.mem_iInf, Subgroup.mem_comap]
  refine forall_congr' fun P => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact Valuation.map_sub_le _ h.le (by simp)
end GlobalTheory.CMVal.ValEx
