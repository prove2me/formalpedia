-- Prove2me | solution 1 for GlobalTheory.GramSubmodular.gram_det_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:40.809807+00:00
-- url     : https://prove2.me/submissions/ad1ca6f1-c2ce-43e2-9c64-6cab6f83b11a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetFromColsEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open GlobalTheory.GramSubmodular
variable {m α β γ : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace GlobalTheory.GramSubmodular
theorem _root_.solution (U : Matrix m α ℂ) : 0 ≤ (Uᴴ * U).det.re :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self U).det_nonneg).1
end GlobalTheory.GramSubmodular
