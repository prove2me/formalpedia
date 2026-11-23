-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.exp_one_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:13.627216+00:00
-- url     : https://prove2.me/submissions/7be290d7-e471-4176-9673-0406f03d553c

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
theorem _root_.solution : WithZero.exp (-1 : ℤ) * WithZero.exp (-1 : ℤ) = WithZero.exp (-2 : ℤ) := by
  rw [← WithZero.exp_add]; norm_num
end GlobalTheory.CMVal.ValEx
