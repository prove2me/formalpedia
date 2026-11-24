-- Prove2me | solution 1 for GlobalTheory.CMVal.LatBij.diag_unit_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:31.068699+00:00
-- url     : https://prove2.me/submissions/9918da51-a67e-4696-b998-baf20de42de9

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticePointsIntegralIdelesEquiv
import Theorems.Thm_GlobalTheory_CMVal_algebraMap_mem_hatO
import Theorems.Thm_GlobalTheory_CMVal_algebraMap_mem_orderC
import Theorems.Thm_GlobalTheory_CMVal_mem_hatOUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.LatBij
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.LatBij
theorem _root_.solution (c : Ideal (OF E)) (u : (OF E)ˣ) :
    diag (Units.map (algebraMap (OF E) E).toMonoidHom u) ∈ hatOUnits c := by
  rw [mem_hatOUnits, ← map_inv, ← map_inv]
  exact ⟨algebraMap_mem_hatO (algebraMap_mem_orderC c _), algebraMap_mem_hatO (algebraMap_mem_orderC c _)⟩
end GlobalTheory.CMVal.LatBij
