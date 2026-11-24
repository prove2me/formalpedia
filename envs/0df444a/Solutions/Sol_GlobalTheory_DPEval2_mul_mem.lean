-- Prove2me | solution 1 for GlobalTheory.DPEval2.mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:55:45.447743+00:00
-- url     : https://prove2.me/submissions/8f9f930d-b795-4f82-a2c0-a2e674b39e4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
import Theorems.Thm_GlobalTheory_DPEval2_bv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DPEval2
namespace GlobalTheory.DPEval2
theorem _root_.solution {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) : x * y ∈ D := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [bv_mul]
    exact Submodule.smul_of_tower_mem _ _ (bv_mem _)
  · intro y _; simp
  · intro y _; simp
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
end GlobalTheory.DPEval2
