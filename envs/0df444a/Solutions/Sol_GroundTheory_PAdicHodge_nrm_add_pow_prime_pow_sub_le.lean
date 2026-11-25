-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_add_pow_prime_pow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:59.974487+00:00
-- url     : https://prove2.me/submissions/ff290a6b-5585-4338-9892-770dd5b6d620

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pow_sub_pow_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_le_one_of_pow
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_pow_prime_sub_le
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue


attribute [local simp] GroundTheory.PAdicHodge.nrm_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
variable {p : ℕ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (hp : p.Prime) {a b : Ω} (ha : nrm K a ≤ 1)
    (hb : nrm K b ≤ 1) (k : ℕ) :
    nrm K ((a + b) ^ (p ^ k) - a ^ (p ^ k) - b ^ (p ^ k)) ≤ nrm K (p : Ω) := by
  induction k with
  | zero => simp [nrm_nonneg]
  | succ k ih =>
    set A := a ^ (p ^ k)
    set B := b ^ (p ^ k)
    set X := (a + b) ^ (p ^ k)
    have hA : nrm K A ≤ 1 := nrm_le_one_of_pow ha _
    have hB : nrm K B ≤ 1 := nrm_le_one_of_pow hb _
    have hX : nrm K X ≤ 1 := nrm_le_one_of_pow (nrm_add_le_one ha hb) _
    have e : (a + b) ^ (p ^ (k + 1)) - a ^ (p ^ (k + 1)) - b ^ (p ^ (k + 1)) =
        (X ^ p - (A + B) ^ p) + ((A + B) ^ p - A ^ p - B ^ p) := by
      simp only [X, A, B, pow_succ, pow_mul]; ring
    rw [e]
    refine nrm_add_le_of_le ?_ (nrm_add_pow_prime_sub_le hp hA hB)
    refine (nrm_pow_sub_pow_le hX (nrm_add_le_one hA hB) p).trans ?_
    have : X - (A + B) = X - A - B := by ring
    rw [this]; exact ih
end GroundTheory.PAdicHodge
