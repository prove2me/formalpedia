-- Prove2me | solution 1 for GlobalTheory.AdLat.exists_nat_valued_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:23.482716+00:00
-- url     : https://prove2.me/submissions/d95d6a93-5915-48b7-bf65-0412e3a50d5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Theorems.Thm_GlobalTheory_AdLat_valued_natCast_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.AdLat
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.AdLat
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, Valued.v ((p ^ n : ℕ) : v.adicCompletion F) ≤ exp (-(n : ℤ)) := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, fun n => ?_⟩
  · exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · rw [valued_natCast_eq, HeightOneSpectrum.intValuation_le_pow_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) n
end GlobalTheory.AdLat
