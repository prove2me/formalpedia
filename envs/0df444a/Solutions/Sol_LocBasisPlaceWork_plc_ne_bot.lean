-- Prove2me | solution 1 for LocBasisPlaceWork.plc_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:14.316322+00:00
-- url     : https://prove2.me/submissions/1660a6e8-25c5-4d26-8718-0d4fa715ea41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_SpanClear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_MemPrimeComplIff
import Theorems.Thm_LocBasisPlaceWork_norm_p_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open LocBasisPlaceWork
variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p])
namespace LocBasisPlaceWork
theorem _root_.solution : plc ρ ≠ ⊥ := by
  intro h
  have hp : (p : 𝓞 E) ∈ plc ρ := by
    rw [mem_plc]
    simpa [map_natCast] using norm_p_lt_one (p := p)
  rw [h, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
end LocBasisPlaceWork
