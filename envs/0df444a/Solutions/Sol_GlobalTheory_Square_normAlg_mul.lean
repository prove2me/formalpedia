-- Prove2me | solution 1 for GlobalTheory.Square.normAlg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:17:52.194696+00:00
-- url     : https://prove2.me/submissions/0db6bcbb-29ab-44bc-b502-bf931b1ec173

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
omit [NumberField K]
namespace GlobalTheory.Square
theorem _root_.solution {κ X : Type} [Fintype κ] [Fintype X] (G : κ → κ → K) (gam : X → ℕ) (z : X → κ → K) (t : K) :
    normAlg G gam (fun x k => t * z x k) = t * star t * normAlg G gam z := by
  simp only [normAlg, Finset.mul_sum, star_mul']
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring
end GlobalTheory.Square
