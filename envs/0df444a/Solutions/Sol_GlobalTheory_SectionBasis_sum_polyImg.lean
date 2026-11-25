-- Prove2me | solution 1 for GlobalTheory.SectionBasis.sum_polyImg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:32:35.229438+00:00
-- url     : https://prove2.me/submissions/27da4f27-f467-41cd-b42a-5cf4c55b9879

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_GenericSection_polyImg_succAbove


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}
namespace GlobalTheory.SectionBasis
theorem _root_.solution (j0 : Fin (N + 1)) (v : Fin (N + 1) → Ω) (x : Fin N → Ω) (hv : v j0 ≠ 0)
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) (i : Fin (D + 1)) :
    ∑ j, polyImg j0 x (i, j) * C (v j) =
      C (v j0) * (polyImg j0 x (i, j0) + ∑ k, X (Sum.inr (i, k)) * C (x k)) := by
  rw [Fin.sum_univ_succAbove _ j0, mul_add, Finset.mul_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [polyImg_succAbove, mul_left_comm, ← C_mul, hx, mul_div_cancel₀ _ hv]
end GlobalTheory.SectionBasis
