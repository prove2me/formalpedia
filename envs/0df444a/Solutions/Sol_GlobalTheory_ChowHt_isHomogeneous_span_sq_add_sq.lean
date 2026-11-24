-- Prove2me | solution 1 for GlobalTheory.ChowHt.isHomogeneous_span_sq_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:17:31.829476+00:00
-- url     : https://prove2.me/submissions/6903ee98-24b5-4c85-b045-99c7cb52e58a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
namespace GlobalTheory.ChowHt
theorem _root_.solution :
    (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}).IsHomogeneous
      (homogeneousSubmodule (Fin 2) ℚ) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ rfl
  exact ⟨2, (isHomogeneous_X_pow _ _).add (isHomogeneous_X_pow _ _)⟩
end GlobalTheory.ChowHt
