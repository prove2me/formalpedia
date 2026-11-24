-- Prove2me | solution 1 for GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:21.073786+00:00
-- url     : https://prove2.me/submissions/9e554802-6989-422b-a499-efb6be1e18df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open GlobalTheory GlobalTheory.OneLeDetOneAdd
namespace GlobalTheory.OneLeDetOneAdd
theorem _root_.solution {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {D : Matrix n n 𝕜} (hD : D.PosSemidef) : (1 : 𝕜) ≤ (1 + D).det := by
  have hA : (1 + D).IsHermitian := Matrix.isHermitian_one.add hD.1
  have hμ : ∀ i, 1 ≤ hA.eigenvalues i := by
    intro i
    have hv1 : RCLike.re (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis i)) = 1 := by
      rw [dotProduct_comm]
      simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hA.eigenvectorBasis.orthonormal.1 i, algebraMap.coe_one, one_pow, RCLike.one_re]
    have h := hA.eigenvalues_eq i
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, map_add, hv1] at h
    have h0 := hD.re_dotProduct_nonneg ⇑(hA.eigenvectorBasis i)
    linarith
  have hprod : (1 : ℝ) ≤ ∏ i, hA.eigenvalues i := by
    calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ ∏ i, hA.eigenvalues i := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hμ i)
  rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  calc (1 : 𝕜) = ((1 : ℝ) : 𝕜) := by simp
    _ ≤ _ := RCLike.ofReal_le_ofReal.mpr hprod
end GlobalTheory.OneLeDetOneAdd
