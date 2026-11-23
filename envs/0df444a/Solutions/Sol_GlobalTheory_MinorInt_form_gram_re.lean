-- Prove2me | solution 1 for GlobalTheory.MinorInt.form_gram_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:51.161659+00:00
-- url     : https://prove2.me/submissions/a17656f0-c6a0-4880-83fb-801464316898

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_star_dot_self_re

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Matrix κ ι ℂ) (x : ι → ℂ) :
    (star x ⬝ᵥ (Bᴴ * B) *ᵥ x).re = ∑ k, ‖(B *ᵥ x) k‖ ^ 2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dot_self_re]
end GlobalTheory.MinorInt
