-- Prove2me | solution 1 for GlobalTheory.CommTriang.exists_common_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:18.269466+00:00
-- url     : https://prove2.me/submissions/9bd8a7d8-b0cd-4bb8-a9ed-84aa2781cab8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonEigenvectorCommuting
import Theorems.Thm_GlobalTheory_CommTriang_exists_common_eigenvector_commuting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CommTriang
namespace GlobalTheory.CommTriang
theorem _root_.solution : ∀ (k ι : Type) [Field k] [IsAlgClosed k] (n : ℕ)
    (T : ι → Matrix (Fin (n+1)) (Fin (n+1)) k), (∀ i j, T i * T j = T j * T i) →
    ∃ v : Fin (n+1) → k, v ≠ 0 ∧ ∃ χ : ι → k, ∀ i, (T i).mulVec v = χ i • v := by
  intro k ι _ _ n T hT
  have hc : ∀ i j, Matrix.toLin' (T i) * Matrix.toLin' (T j) = Matrix.toLin' (T j) * Matrix.toLin' (T i) := by
    intro i j
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hT]
  obtain ⟨x, -, hx0, hx⟩ := exists_common_eigenvector_commuting (fun i => Matrix.toLin' (T i)) hc _ ⊤ rfl
    (by simp) (fun _ _ _ => Submodule.mem_top)
  choose χ hχ using hx
  exact ⟨x, hx0, χ, fun i => by simpa using hχ i⟩
end GlobalTheory.CommTriang
