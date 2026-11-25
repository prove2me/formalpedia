-- Prove2me | solution 1 for LocBasisPlaceWork.mem_primeCompl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:48.675715+00:00
-- url     : https://prove2.me/submissions/d6ba7c60-11bb-426d-9dd2-9be704707bd3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_SpanClear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_MemPrimeComplIff

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
theorem _root_.solution (s : 𝓞 E) : s ∈ (plc ρ).primeCompl ↔ ‖ρ (s : E)‖ = 1 := by
  rw [Ideal.mem_primeCompl_iff, mem_plc, not_lt]
  exact ⟨fun h => le_antisymm (norm_le_one ρ s) h, fun h => h.ge⟩
end LocBasisPlaceWork
