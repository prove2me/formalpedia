-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.norm_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:42.751816+00:00
-- url     : https://prove2.me/submissions/5abac269-8f82-44c2-98b0-2150a98f14d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckeStrip
theorem _root_.solution (φ : I → K →+* ℂ) (n : I → ℤ) {a : K} (ha : a ≠ 0) : ‖wt φ n a‖ = 1 := by
  unfold wt
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  have h : φ i a ≠ 0 := (map_ne_zero _).2 ha
  rw [norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h), one_zpow]
end GlobalTheory.HeckeStrip
