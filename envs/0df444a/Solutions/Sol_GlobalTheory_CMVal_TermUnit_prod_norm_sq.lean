-- Prove2me | solution 1 for GlobalTheory.CMVal.TermUnit.prod_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:22:52.945819+00:00
-- url     : https://prove2.me/submissions/3cdc054c-244d-48d0-bc72-a378817e0ac5

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_bijective_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.CMVal.TermUnit
theorem _root_.solution [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |(Algebra.norm ℚ x : ℝ)| := by
  calc ∏ i, ‖φ i x‖ ^ 2 = ∏ w : InfinitePlace E, w x ^ InfinitePlace.mult w :=
        Fintype.prod_bijective _ (bijective_mk h) _ _ fun i => by
          rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]
    _ = _ := by rw [InfinitePlace.prod_eq_abs_norm]; push_cast; rfl
end GlobalTheory.CMVal.TermUnit
