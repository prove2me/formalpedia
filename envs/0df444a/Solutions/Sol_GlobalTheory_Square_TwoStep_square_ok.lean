-- Prove2me | solution 1 for GlobalTheory.Square.TwoStep.square_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:57:16.366858+00:00
-- url     : https://prove2.me/submissions/ab185faa-cee2-4460-946e-5398751dfe34

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
open GlobalTheory.Square.TwoStep
omit [NumberField K] [StarRing K]
namespace GlobalTheory.Square.TwoStep
theorem _root_.solution : (square K).OK 3 2 :=
  ⟨rfl, le_rfl, rfl, rfl, Complex.I_ne_zero, one_ne_zero, one_ne_zero, Complex.I_ne_zero⟩
end GlobalTheory.Square.TwoStep
