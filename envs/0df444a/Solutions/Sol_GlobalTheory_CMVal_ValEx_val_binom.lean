-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.val_binom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:01.861707+00:00
-- url     : https://prove2.me/submissions/435d42d1-d3fd-42e5-98e8-6ab73ff0be6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_nat_le
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
variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {t : K} (ht : v t ≤ 1) (n : ℕ) : v ((1 + t) ^ n - 1 - n * t) ≤ v t * v t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (1 + t) ^ (n + 1) - 1 - ((n + 1 : ℕ) : K) * t = (1 + t) * ((1 + t) ^ n - 1 - n * t) + n * (t * t) := by
      push_cast; ring
    rw [this]
    refine v.map_add_le ?_ ?_
    · rw [map_mul]
      exact (mul_le_mul' (v.map_add_le (by simp) ht) ih).trans (by rw [one_mul])
    · rw [map_mul, map_mul]
      exact (mul_le_mul' (val_nat_le v n) le_rfl).trans (by rw [one_mul])
end GlobalTheory.CMVal.ValEx
