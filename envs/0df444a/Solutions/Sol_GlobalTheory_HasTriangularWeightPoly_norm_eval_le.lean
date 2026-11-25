-- Prove2me | solution 1 for GlobalTheory.HasTriangularWeightPoly.norm_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:40.403853+00:00
-- url     : https://prove2.me/submissions/d21a6f49-9c4f-4836-8ca2-c5168f900b25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
import Theorems.Thm_GlobalTheory_HasTriangularWeight_norm_le_prod_pow
import Theorems.Thm_GlobalTheory_HasTriangularWeightPoly_hasTriangularWeight

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
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜]
namespace GlobalTheory
namespace HasTriangularWeightPoly
theorem _root_.solution {a : ∀ s, Fin (r s) → ℕ}
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) 𝕜}
    (hp : HasTriangularWeightPoly a p) {C : ℝ}
    (hC : ∀ u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜,
      (∀ s, u s ∈ Matrix.unitaryGroup (Fin (r s)) 𝕜) → ‖MvPolynomial.eval (entries u) p‖ ≤ C)
    {R : ι → ℝ} (hR : ∀ s, 0 ≤ R s) {x : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜}
    (hx : ∀ s j, ∑ i, ‖x s i j‖ ^ 2 ≤ R s ^ 2) :
    ‖MvPolynomial.eval (entries x) p‖ ≤ C * ∏ s, R s ^ ∑ i, a s i := by
  let L : ∀ s, Fin (r s) → Module.Dual 𝕜 (EuclideanSpace 𝕜 (Fin (r s))) := fun s i =>
    EuclideanSpace.projₗ i
  have hw := hp.hasTriangularWeight L
  have hc : Continuous fun y : ∀ s, Fin (r s) → EuclideanSpace 𝕜 (Fin (r s)) =>
      MvPolynomial.eval (entries fun s => Matrix.of fun i j => L s i (y s j)) p := by
    refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun k => ?_)
    change Continuous fun y : ∀ s, Fin (r s) → EuclideanSpace 𝕜 (Fin (r s)) => y k.1 k.2.2 k.2.1
    fun_prop
  refine hw.norm_le_prod_pow (fun s => by simp) hc (fun y hy => hC _ fun s => ?_)
    (x := fun s j => WithLp.toLp 2 fun i => x s i j) fun s j => ?_
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := orthonormal_iff_ite.1 (hy s) i j
    rw [PiLp.inner_apply] at this
    simpa [L, Matrix.mul_apply, Matrix.one_apply, mul_comm] using this
  · refine (sq_le_sq₀ (norm_nonneg _) (hR s)).1 ?_
    rw [EuclideanSpace.norm_sq_eq]
    exact hx s j
end HasTriangularWeightPoly
end GlobalTheory
