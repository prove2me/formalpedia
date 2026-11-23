-- Prove2me | solution 1 for GlobalTheory.MinorInt.form_diff_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:12.318252+00:00
-- url     : https://prove2.me/submissions/72ad70f2-0c51-401a-b9ce-2e1f6e5d5a50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_form_gram_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ)
    (t : ι → ℂ) : (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re =
      ∑ k, ‖(A *ᵥ t) k‖ ^ 2 - ∑ k, ‖(C *ᵥ t) k‖ ^ 2 := by
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, form_gram_re, form_gram_re]
end GlobalTheory.MinorInt
