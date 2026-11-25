-- Prove2me | solution 1 for GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:25:01.795947+00:00
-- url     : https://prove2.me/submissions/7f5f16af-7e9a-4473-a8ac-e2dc86f27503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealPowNatCastDvdFiniteIntegersAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealPowNatCastDvdFiniteIntegersAlgebraStatement
import Theorems.Thm_GlobalTheory_maxIdeal_pow_dvd_natCast_of_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A → ∃ N : ℕ, (p : A) ∣ a ^ N := by
  first | exact @GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers | exact GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers | (intros; apply GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers <;> assumption)
end _root_.GlobalTheory.T
