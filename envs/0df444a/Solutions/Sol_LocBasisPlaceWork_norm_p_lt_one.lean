-- Prove2me | solution 1 for LocBasisPlaceWork.norm_p_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:41.15213+00:00
-- url     : https://prove2.me/submissions/c3d8d603-656b-4bba-ad3a-63c221cf42bb

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
theorem _root_.solution : ‖(p : ℂ_[p])‖ < 1 := by
  have h1 := PadicComplex.norm_extends' p (p : ℚ_[p])
  simp only [map_natCast, Padic.norm_p] at h1
  have h2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    convert h1 using 2
    first
    | rfl
    | exact (map_natCast _ p).symm
    | norm_cast
  rw [h2]
  exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
end LocBasisPlaceWork
