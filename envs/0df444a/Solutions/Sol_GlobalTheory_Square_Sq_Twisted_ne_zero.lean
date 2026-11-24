-- Prove2me | solution 1 for GlobalTheory.Square.Sq.Twisted.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:42.635586+00:00
-- url     : https://prove2.me/submissions/628c4439-adc5-4ecc-8e21-e9f287354224

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Theorems.Thm_GlobalTheory_Square_Sq_Tuple_tuple_constants_ne_zero

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
namespace GlobalTheory.Square
namespace Sq.Twisted
theorem _root_.solution {S : Sq K} {hd y : ℕ} {σ₀ : K →+* ℂ} {w : Pl K} {cw : ℂ} {zA zA' : K}
    {zT zTd : ℤ → K} {gT : ℤ → ℤ} {n0 : ℤ → ℝ} {er dl : ℝ} {T : Type} {S0 : Finset T} {cc qq : T → ℕ}
    (h : S.Twisted σ₀ w cw zA zA' zT zTd gT n0 er dl S0 cc qq) (hS : S.OK hd y) : cw ≠ 0 := by
  obtain ⟨a, _, _, _, _, _, rfl, _, h1, _⟩ := h
  exact (h1.tuple_constants_ne_zero hS).2
end Sq.Twisted
end GlobalTheory.Square
