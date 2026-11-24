-- Prove2me | solution 1 for GlobalTheory.PhaseLipschitz.norm_iteratedFDeriv_psi_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:18.320801+00:00
-- url     : https://prove2.me/submissions/c4e112ac-b639-4a8f-b9e0-55416376b76b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Theorems.Thm_GlobalTheory_PhaseLipschitz_contDiff_psi
import Theorems.Thm_GlobalTheory_PhaseLipschitz_norm_psi_le
import Theorems.Thm_GlobalTheory_PhaseLipschitz_norm_iteratedDeriv_psi_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.PhaseLipschitz
namespace GlobalTheory.PhaseLipschitz
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) {N i : ℕ} (hi : i ≤ N) (x : V) :
    ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ ≤
      (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * (1 + ‖x‖) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hL := norm_nonneg L
  have hx := norm_nonneg x
  have hk := abs_nonneg k
  have h1N : (1 : ℝ) ≤ (1 + ‖L‖) ^ N := one_le_pow₀ (by linarith)
  rcases i with _ | j
  · rw [norm_iteratedFDeriv_zero, Function.comp_apply]
    refine (norm_psi_le k (L x)).trans ?_
    have h2 : |L x + k| ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by
      have h3 : |L x| ≤ ‖L‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using L.le_opNorm x
      calc |L x + k| ≤ |L x| + |k| := abs_add_le _ _
        _ ≤ ‖L‖ * ‖x‖ + |k| := by linarith
        _ ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by nlinarith
    have h4 : 2 * Real.pi ≤ (2 * Real.pi) ^ (N + 1) := le_self_pow₀ hpi (by omega)
    calc 2 * Real.pi * |L x + k| ≤ 2 * Real.pi * ((‖L‖ + |k|) * (1 + ‖x‖)) := by gcongr
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * 1) * (1 + ‖x‖) := by
          rw [mul_one]; rw [← mul_assoc]; gcongr
      _ ≤ _ := by gcongr
  · rw [L.iteratedFDeriv_comp_right (contDiff_psi k) x (i := j + 1) (by exact_mod_cast le_top)]
    have h5 : (2 * Real.pi) ^ (j + 1) ≤ (2 * Real.pi) ^ (N + 1) := pow_le_pow_right₀ hpi (by omega)
    have h6 : ‖L‖ ^ (j + 1) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by
      rw [pow_succ']
      gcongr
      · linarith
      · calc ‖L‖ ^ j ≤ (1 + ‖L‖) ^ j := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ N := pow_le_pow_right₀ (by linarith) (by omega)
    calc _ ≤ ‖iteratedFDeriv ℝ (j + 1) (psi k) (L x)‖ * ∏ _j : Fin (j + 1), ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = (2 * Real.pi) ^ (j + 1) * ‖L‖ ^ (j + 1) := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_psi_succ]; simp
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * 1 := by
          rw [mul_one]; gcongr
      _ ≤ _ := by gcongr; linarith
end GlobalTheory.PhaseLipschitz
