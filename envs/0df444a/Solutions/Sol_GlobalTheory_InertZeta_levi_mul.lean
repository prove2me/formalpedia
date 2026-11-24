-- Prove2me | solution 1 for GlobalTheory.InertZeta.levi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:07:09.52253+00:00
-- url     : https://prove2.me/submissions/1eaff7bc-4ee1-4f0d-8072-26128cc1e4b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SphericalInductionTransitivityOfLeviExists
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {ϖ : L} (hϖ : ϖ ≠ 0) {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g m)
    (h' : IsLeviElt ϖ a' g' m') : IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  have e : ∀ i j, mat (m * m') i j = mat m i 0 * mat m' 0 j + ∑ l, mat m i (mid l) * mat m' (mid l) j +
      mat m i (Fin.last (N + 1)) * mat m' (Fin.last (N + 1)) j := fun i j => by
    rw [mat_mul, Matrix.mul_apply, sum_idx (fun l => mat m i l * mat m' l j)]
  have z : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  have z' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := h'.1
  refine ⟨mul_mem h.1 h'.1, ?_, ?_, fun i j => ?_⟩
  · rw [e, h.2.1, h'.2.1, z 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
      Finset.sum_eq_zero (fun l _ => by rw [z 0 (mid l) (by simp), zero_mul]), add_zero, zpow_add₀ hϖ]
  · rw [e, h.2.2.1, h'.2.2.1, z (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
      Finset.sum_eq_zero (fun l _ => by rw [z (Fin.last (N + 1)) (mid l) (by simp), zero_mul]), zero_add,
      neg_add, zpow_add₀ hϖ]
  · rw [e, z (mid i) 0 (by simp), z (mid i) (Fin.last (N + 1)) (by simp), zero_mul, zero_mul, zero_add, add_zero,
      mat_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.2.2.2, h'.2.2.2]
end GlobalTheory.InertZeta
