-- Prove2me | solution 1 for GlobalTheory.PMonE.norm_mul_apply_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:46.32807+00:00
-- url     : https://prove2.me/submissions/7b34c4ff-1117-48c9-a9f8-40f31e499d8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A B : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ < 1) (i j : m) :
    ‖(A * B) i j‖ < 1 := by
  rw [Matrix.mul_apply]
  rcases isEmpty_or_nonempty m with hm | hm
  · simp
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image (univ : Finset m) (fun k => ‖A i k * B k j‖) univ_nonempty
  have hlt : ‖A i k₀ * B k₀ j‖ < 1 := by
    rw [norm_mul]
    calc ‖A i k₀‖ * ‖B k₀ j‖ ≤ 1 * ‖B k₀ j‖ := mul_le_mul_of_nonneg_right (hA i k₀) (norm_nonneg _)
      _ = ‖B k₀ j‖ := one_mul _
      _ < 1 := hB k₀ j
  exact lt_of_le_of_lt
    (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => hk₀ k hk) hlt
end GlobalTheory.PMonE
