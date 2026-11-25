-- Prove2me | solution 1 for GlobalTheory.HCXi.LineStabiliser.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:32:30.501484+00:00
-- url     : https://prove2.me/submissions/5b0621f7-0c47-4861-89f3-8eeb4d41cf99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_e0_eq
import Theorems.Thm_GlobalTheory_LevelUnitary_inclH_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.LineStabiliser
open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser
variable (k r' : ℕ)
namespace GlobalTheory.HCXi.LineStabiliser
theorem _root_.solution (u : Fin (2 * (1 + r') + k + 1) → ℂ) (hu : u (lst k r') = 0) :
    u = liftVec k 1 r' ((incl k 1 r')ᴴ *ᵥ u) + u (fst k r') • e0 k r' := by
  have hc : ∀ j, ((incl k 1 r')ᴴ *ᵥ u) j = u (levPos k 1 r' j) := fun j =>
    inclH_mul k 1 r' (Matrix.of fun a _ => u a) j j
  ext i
  have hi := i.isLt
  rw [Pi.add_apply, Pi.smul_apply, e0_eq, Pi.single_apply, smul_eq_mul]
  unfold liftVec
  by_cases h : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos h, hc, if_neg (by simp only [fst, Fin.ext_iff]; omega), mul_zero, add_zero]
    congr 1
    simp only [levPos, Fin.ext_iff]
    omega
  · rw [dif_neg h, zero_add]
    by_cases h0 : i = fst k r'
    · rw [if_pos h0, mul_one, h0]
    · rw [if_neg h0, mul_zero, ← hu]
      congr 1
      simp only [fst, lst, Fin.ext_iff] at h0 ⊢
      omega
end GlobalTheory.HCXi.LineStabiliser
