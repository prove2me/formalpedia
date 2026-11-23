-- Prove2me | solution 1 for GlobalTheory.Square.TwoStep.vw_natCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:04.922837+00:00
-- url     : https://prove2.me/submissions/4b0f024d-5f92-4171-a275-13758e1f2d0b

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int_nonneg


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
namespace GlobalTheory.Square.TwoStep
theorem _root_.solution (w : Pl K) (n : ℕ) : (0 : ℝ) ≤ (vw w (n : K) : ℝ) := by
  have : 0 ≤ vw w (n : K) := by simpa using Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (n : 𝓞 K)
  exact_mod_cast this
end GlobalTheory.Square.TwoStep
