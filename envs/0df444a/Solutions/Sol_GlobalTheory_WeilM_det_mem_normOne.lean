-- Prove2me | solution 1 for GlobalTheory.WeilM.det_mem_normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:22.349547+00:00
-- url     : https://prove2.me/submissions/3ad5fda6-5b6f-46af-b6b1-a1c9222889fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_mem_normOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
namespace GlobalTheory.WeilM
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι E} (hJ : IsHerm c J) (g : UG c J) :
    Matrix.GeneralLinearGroup.det (g : GL ι E) ∈ normOne c := by
  have h := congrArg Matrix.det (show ((g : GL ι E) : Matrix ι ι E)ᵀ * J * ((g : GL ι E) : Matrix ι ι E).map c = J from g.2)
  rw [det_mul, det_mul, det_transpose,
    show (((g : GL ι E) : Matrix ι ι E).map c).det = c ((g : GL ι E) : Matrix ι ι E).det from
      (c.toRingHom.map_det _).symm] at h
  refine mem_normOne.mpr (hJ.2.mul_left_cancel ?_)
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  linear_combination h
end GlobalTheory.WeilM
