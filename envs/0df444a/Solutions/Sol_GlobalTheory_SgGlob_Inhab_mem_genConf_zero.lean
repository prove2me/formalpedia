-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_genConf_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:38.680861+00:00
-- url     : https://prove2.me/submissions/1f5d0def-5314-4511-9804-c9e8a5d47400

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_selfDual_std
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_pairLat_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    ((std E, !![0; 1], !![(g : E); 1 + g]) : Tri E 2 0) ∈
      GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] := by
  refine ⟨selfDual_std σ, ⟨⟨⟨!![0, 1], ?_⟩, ?_⟩, ⟨⟨!![-1, 1], ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, TF, Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, TF, Matrix.mul_apply]; ring
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, Matrix.mul_apply]; ring
  · dsimp only
    rw [pairLat_std hg]
    exact ⟨le_rfl, fun v hv _ => hv⟩
end GlobalTheory.SgGlob.Inhab
