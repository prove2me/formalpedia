-- Prove2me | solution 1 for GlobalTheory.HCA.SolFunc.continuousOn_extendByZeroOffSubset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:02.677395+00:00
-- url     : https://prove2.me/submissions/41f38acd-d976-49c2-8272-0fa243faeee0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SolFunc
variable {d : ℕ}
namespace GlobalTheory.HCA.SolFunc
theorem _root_.solution {U : Set (E d)} (u : U →ᵇ ℂ) : ContinuousOn (ext0 U u) U := by
  rw [continuousOn_iff_continuous_restrict]
  have : U.domRestrict (ext0 U u) = u := by funext x; exact dif_pos x.2
  rw [this]; exact u.continuous
end GlobalTheory.HCA.SolFunc
