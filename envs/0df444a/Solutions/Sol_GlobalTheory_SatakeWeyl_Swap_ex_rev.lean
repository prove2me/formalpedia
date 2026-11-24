-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Swap.ex_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:49:16.354802+00:00
-- url     : https://prove2.me/submissions/552de6d4-7712-425b-b2fc-52e628b747cc

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReduction
import Theorems.Thm_GlobalTheory_SatakeWeyl_Swap_ex_low
import Theorems.Thm_GlobalTheory_SatakeWeyl_Swap_ex_high
import Theorems.Thm_GlobalTheory_SatakeWeyl_Swap_ex_mid
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Swap
namespace GlobalTheory.SatakeWeyl.Swap
theorem _root_.solution {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (c : Fin n) : ex n m a c.rev = -ex n m a c := by
  have h1 := c.2
  have h2 := Fin.val_rev c
  by_cases h : c.val < m
  · rw [ex_low a c ⟨c.val, h⟩ rfl, ex_high hm a c.rev ⟨c.val, h⟩ (by simp only; omega)]
  · by_cases h' : c.val + m < n
    · rw [ex_mid a c (by omega) h', ex_mid a c.rev (by omega) (by omega), neg_zero]
    · rw [ex_high hm a c ⟨c.rev.val, by omega⟩ (by simp only; omega), ex_low a c.rev ⟨c.rev.val, by omega⟩ rfl,
        neg_neg]
end GlobalTheory.SatakeWeyl.Swap
