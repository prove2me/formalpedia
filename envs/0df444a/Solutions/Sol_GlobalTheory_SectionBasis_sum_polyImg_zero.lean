-- Prove2me | solution 1 for GlobalTheory.SectionBasis.sum_polyImg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:43.311415+00:00
-- url     : https://prove2.me/submissions/4cd9bf51-494b-413e-aefa-80a272597579

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_SectionBasis_sum_polyImg
import Theorems.Thm_GlobalTheory_GenericSection_polyImg_same


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
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) :
    ∑ j, polyImg (D := D) j0 x (0, j) * C (v j) ≠ 0 := by
  rw [sum_polyImg j0 v x hv hx, polyImg_same, if_pos rfl]
  intro h
  have := congrArg (eval (Sum.elim (fun _ => (1 : Ω)) (fun _ => 0))) h
  simp [hv] at this
end GlobalTheory.SectionBasis
