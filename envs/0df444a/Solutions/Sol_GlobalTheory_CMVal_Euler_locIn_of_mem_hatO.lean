-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.locIn_of_mem_hatO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:56.705341+00:00
-- url     : https://prove2.me/submissions/f1e4627c-ce1c-41e5-ae21-06ae1ba1814a

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_mem_aboveF
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_exists_cong


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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {c : Ideal (OF E)} {z : Af E} (hz : z ∈ hatO c) (v : HeightOneSpectrum (OF E)) :
    LocIn (expIn c v) v z := by
  obtain ⟨a, ha⟩ := OrderUnits.exists_cong v (expIn c v) (pow_multiplicity_dvd _ _) _
    (fun P hP => (mem_aboveF P v).1 hP) hz
  exact ⟨a, fun P hP => by rw [Valuation.map_sub_swap]; exact ha P ((mem_aboveF P v).2 hP)⟩
end GlobalTheory.CMVal.Euler
