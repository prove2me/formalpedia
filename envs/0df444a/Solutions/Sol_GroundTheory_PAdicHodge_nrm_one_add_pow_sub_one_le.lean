-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_one_add_pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:43.557402+00:00
-- url     : https://prove2.me/submissions/80f8bc74-87d7-4546-82e4-f3a8c47d01c0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pow
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_max
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_natCast_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_binomialSum_le
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
theorem _root_.solution (hp : p.Prime) {w : Ω} (hw : nrm K w ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    nrm K ((1 + w) ^ (p ^ k) - 1) ≤ nrm K w * max (nrm K (p : Ω)) (nrm K w ^ (p - 1)) := by
  have hM : max (nrm K (p : Ω)) (nrm K w ^ (p - 1)) ≤ 1 :=
    max_le (nrm_natCast_le_one p) (pow_le_one₀ (nrm_nonneg _) hw)

  have one : ∀ {v : Ω}, nrm K v ≤ 1 →
      nrm K ((1 + v) ^ p - 1) ≤ nrm K v * max (nrm K (p : Ω)) (nrm K v ^ (p - 1)) := by
    intro v hv
    rw [add_pow_prime_eq hp 1 v]
    have e : 1 ^ p + v ^ p + (p : Ω) * 1 * v * ∑ k ∈ Finset.Ioo 0 p, 1 ^ (k - 1) * v ^ (p - k - 1) *
        ((p.choose k / p : ℕ) : Ω) - 1 = v * v ^ (p - 1) + v * ((p : Ω) * ∑ k ∈ Finset.Ioo 0 p,
          1 ^ (k - 1) * v ^ (p - k - 1) * ((p.choose k / p : ℕ) : Ω)) := by
      rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]; ring
    rw [e]
    have hS := nrm_binomialSum_le (p := p) (1 : Ω) v (by simp) hv
    refine (nrm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [nrm_mul, nrm_pow]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (nrm_nonneg _)
    · rw [nrm_mul, nrm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (nrm_nonneg _)
      calc nrm K (p : Ω) * _ ≤ nrm K (p : Ω) * 1 := mul_le_mul_of_nonneg_left hS (nrm_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact le_max_left _ _
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  induction k with
  | zero => simpa using one hw
  | succ k ih =>
    have hw' := ih (Nat.succ_ne_zero _)
    set w' := (1 + w) ^ (p ^ (k + 1)) - 1
    have hw'1 : nrm K w' ≤ nrm K w := hw'.trans (by
      calc _ ≤ nrm K w * 1 := mul_le_mul_of_nonneg_left hM (nrm_nonneg _)
        _ = _ := mul_one _)
    have e : (1 + w) ^ (p ^ (k + 1 + 1)) = (1 + w') ^ p := by
      simp only [w', pow_succ _ (k + 1), pow_mul]; ring
    rw [e]
    refine (one (hw'1.trans hw)).trans ?_
    have hM' : max (nrm K (p : Ω)) (nrm K w' ^ (p - 1)) ≤ 1 :=
      max_le (nrm_natCast_le_one p) (pow_le_one₀ (nrm_nonneg _) (hw'1.trans hw))
    calc nrm K w' * _ ≤ nrm K w' * 1 := mul_le_mul_of_nonneg_left hM' (nrm_nonneg _)
      _ = nrm K w' := mul_one _
      _ ≤ _ := hw'
end GroundTheory.PAdicHodge
