-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.exp_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:54.805207+00:00
-- url     : https://prove2.me/submissions/90403067-4074-4bc3-8cee-6bda2f401052

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal

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
variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution : WithZero.exp (-1 : ℤ) ≤ (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
end GlobalTheory.CMVal.ValEx
