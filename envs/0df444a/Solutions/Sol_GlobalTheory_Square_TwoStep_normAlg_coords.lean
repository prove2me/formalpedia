-- Prove2me | solution 1 for GlobalTheory.Square.TwoStep.normAlg_coords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:49.637546+00:00
-- url     : https://prove2.me/submissions/09fa3c3e-530e-45e8-83f3-b959797a83ef

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
namespace GlobalTheory.Square.TwoStep
theorem _root_.solution (t : ℕ) : normAlg (square K).G (coords K t).gam (coords K t).z = (t : K) ^ 2 := by
  show (∑ _x : Fin 2, ((2 : ℕ) : K)⁻¹ * ∑ _k : Unit, ∑ _l : Unit, (t : K) * star (t : K) * 1) = _
  simp; ring
end GlobalTheory.Square.TwoStep
