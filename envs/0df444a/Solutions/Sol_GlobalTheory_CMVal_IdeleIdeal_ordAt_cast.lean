-- Prove2me | solution 1 for GlobalTheory.CMVal.IdeleIdeal.ordAt_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:44.256799+00:00
-- url     : https://prove2.me/submissions/e92f419a-7587-4ee3-8f92-f2245364937b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_coord_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleIdeal
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.IdeleIdeal
theorem _root_.solution {y : (Af E)ˣ} {w : HeightOneSpectrum (𝓞 E)} (h : Valued.v ((y : Af E) w) ≤ 1) :
    (ordAt y w : ℤ) = -WithZero.log (Valued.v ((y : Af E) w)) := by
  have h0 := IdeleModule.coord_ne y w
  have : WithZero.log (Valued.v ((y : Af E) w)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log h0, WithZero.exp_zero]; exact h
  unfold ordAt
  omega
end GlobalTheory.CMVal.IdeleIdeal
