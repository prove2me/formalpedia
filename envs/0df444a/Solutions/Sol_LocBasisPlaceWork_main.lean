-- Prove2me | solution 1 for LocBasisPlaceWork.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:42.421697+00:00
-- url     : https://prove2.me/submissions/3607aea3-d24a-4d48-b226-4159fa687ca1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_SpanClear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_MemPrimeComplIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_Imports
import Theorems.Thm_LocBasisPlaceWork_core
import Theorems.Thm_LocBasisPlaceWork_mem_primeCompl_iff
import Theorems.Thm_LocBasisPlaceWork_plc_ne_bot


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
namespace LocBasisPlaceWork
theorem _root_.solution : PI.LocBasisPlace := by
  intro E _ _ p _ ρ N L hL hsp
  let A := Localization.AtPrime (plc ρ)
  have hle : (plc ρ).primeCompl ≤ nonZeroDivisors (𝓞 E) :=
    Ideal.primeCompl_le_nonZeroDivisors (plc ρ)
  letI : Algebra A E :=
    IsLocalization.localizationAlgebraOfSubmonoidLe A E (plc ρ).primeCompl
      (nonZeroDivisors (𝓞 E)) hle
  have : IsScalarTower (𝓞 E) A E :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A E (plc ρ).primeCompl
      (nonZeroDivisors (𝓞 E)) hle
  have : IsDomain A := IsLocalization.isDomain_localization hle
  have : IsFractionRing A E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (plc ρ).primeCompl A E
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) (plc_ne_bot ρ) A
  obtain ⟨P, hdet, hcol, hx⟩ := core (A := A) (plc ρ).primeCompl N L hL hsp
  refine ⟨P, hdet, fun a => ?_, fun x hxL => ?_⟩
  · obtain ⟨s, hs, h⟩ := hcol a
    exact ⟨s, (mem_primeCompl_iff ρ s).mp hs, h⟩
  · obtain ⟨s, hs, c, h⟩ := hx x hxL
    exact ⟨s, (mem_primeCompl_iff ρ s).mp hs, c, h⟩
end LocBasisPlaceWork
