-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.val_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:22:58.55013+00:00
-- url     : https://prove2.me/submissions/ed3a7d5f-5c63-4285-8102-d2f5c910245b

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_val_le_one
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
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution {c : Ideal (OF E)} {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) P) = 1 := by
  have h1 := val_le_one (mem_hatOUnits.1 hy).1 P
  have h2 := val_le_one (mem_hatOUnits.1 hy).2 P
  have h3 : Valued.v ((y : Af E) P) * Valued.v ((↑y⁻¹ : Af E) P) = 1 := by
    rw [← map_mul]
    exact (congrArg Valued.v (coord P y).val_inv).trans (map_one _)
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((y : Af E) P) * 1 := by gcongr
      _ = _ := mul_one _)
end GlobalTheory.CMVal.OrderUnits
