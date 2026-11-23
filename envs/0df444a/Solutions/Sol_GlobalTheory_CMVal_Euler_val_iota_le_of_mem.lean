-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.val_iota_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:19.663335+00:00
-- url     : https://prove2.me/submissions/3addc750-8c29-4dfa-b5a8-1cf6b4714c4a

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_iff

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
theorem _root_.solution {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over P v) (n : ℕ) {a : OF E}
    (ha : a ∈ v.asIdeal ^ n) : Valued.v (iota a P) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [val_iota_le_iff]
  have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) (v.asIdeal ^ n) ≤ P.asIdeal ^ n := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ n
    rw [Ideal.map_le_iff_le_comap]
    exact h.ge
  exact h1 (Ideal.mem_map_of_mem _ ha)
end GlobalTheory.CMVal.Euler
