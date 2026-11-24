-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.sesq_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:21.470289+00:00
-- url     : https://prove2.me/submissions/b03ef9ce-fb37-4b5b-ae1a-b03f53dcc0da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.WrongSignGauss
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.WrongSignGauss
theorem _root_.solution (u w : ℂ) : sesq u w = u * conj w := by
  simp [sesq]; ring
end GlobalTheory.WrongSignGauss
