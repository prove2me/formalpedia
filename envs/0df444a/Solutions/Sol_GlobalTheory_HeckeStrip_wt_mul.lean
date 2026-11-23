-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.wt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:24.690671+00:00
-- url     : https://prove2.me/submissions/004fa452-f3e0-4a56-98a4-610faa013def

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
theorem _root_.solution (φ : I → K →+* ℂ) (n : I → ℤ) (a b : K) : wt φ n (a * b) = wt φ n a * wt φ n b := by
  unfold wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_zpow]
end GlobalTheory.HeckeStrip
