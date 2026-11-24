-- Prove2me | solution 1 for GlobalTheory.HasTriangularWeight.norm_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:14.092739+00:00
-- url     : https://prove2.me/submissions/f45d4cb7-0917-4ead-a61a-a75a2cedcd47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
import Theorems.Thm_GlobalTheory_HasTriangularWeight_of_continuous
import Theorems.Thm_GlobalTheory_exists_orthonormal_frameMul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace 𝕜 (V s)]
  [∀ s, FiniteDimensional 𝕜 (V s)]
namespace GlobalTheory
namespace HasTriangularWeight
theorem _root_.solution (hV : ∀ s, finrank 𝕜 (V s) = r s)
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W} (hP : HasTriangularWeight 𝕜 a P)
    (hc : Continuous P) {C : ℝ} (hC : ∀ y, (∀ s, Orthonormal 𝕜 (y s)) → ‖P y‖ ≤ C)
    (x : ∀ s, Fin (r s) → V s) : ‖P x‖ ≤ C * ∏ s, ∏ i, ‖x s i‖ ^ a s i := by
  obtain ⟨y, b, hy, hb, hbx, rfl⟩ := exists_orthonormal_frameMul_eq hV x
  rw [hP.of_continuous y (hc.comp (by unfold frameMul; fun_prop)) b hb, norm_smul, mul_comm]
  refine mul_le_mul (hC y hy) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC y hy))
  simp only [norm_prod, norm_pow]
  gcongr with s _ i _
  exact hbx s i
end HasTriangularWeight
end GlobalTheory
