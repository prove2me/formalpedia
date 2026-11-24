-- Prove2me | solution 1 for GlobalTheory.HasTriangularWeight.norm_le_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:46.294178+00:00
-- url     : https://prove2.me/submissions/f96b5a2c-1598-43d6-b9f2-d6250e645eba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Theorems.Thm_GlobalTheory_exists_orthonormal_frameMul_eq
import Theorems.Thm_GlobalTheory_HasTriangularWeight_norm_le_prod

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
    {R : ι → ℝ} {x : ∀ s, Fin (r s) → V s} (hx : ∀ s i, ‖x s i‖ ≤ R s) :
    ‖P x‖ ≤ C * ∏ s, R s ^ ∑ i, a s i := by
  have hC0 : 0 ≤ C := by
    obtain ⟨y, -, hy, -⟩ := exists_orthonormal_frameMul_eq hV x
    exact (norm_nonneg _).trans (hC y hy)
  refine (hP.norm_le_prod hV hc hC x).trans ?_
  simp only [← Finset.prod_pow_eq_pow_sum]
  gcongr with s _ i _
  exact hx s i
end HasTriangularWeight
end GlobalTheory
