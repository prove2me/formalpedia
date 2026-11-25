-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.isEquiv_comap_laurentHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:53.518803+00:00
-- url     : https://prove2.me/submissions/84f7b3c2-554a-4119-9124-5fdc3c196fd6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent
import Theorems.Thm_GroundTheory_LocalField_EqualChar_valuation_uniformizer_pos
import Theorems.Thm_GroundTheory_LocalField_EqualChar_valuation_laurentHom
import Theorems.Thm_GroundTheory_LocalField_EqualChar_valued_le_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries
open GroundTheory.LocalField.EqualChar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
namespace GroundTheory.LocalField.EqualChar
theorem _root_.solution :
    ((valuation K).comap (laurentHom K p)).IsEquiv (Valued.v : Valuation 𝓀[K]⸨X⸩ ℤᵐ⁰) :=
  Valuation.isEquiv_of_val_le_one fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rw [Valuation.comap_apply, valuation_laurentHom K p hx,
      zpow_le_one_iff_right_of_lt_one₀ (valuation_uniformizer_pos K)
        (valuation_uniformizer_lt_one K), valued_le_one_iff K hx]
end GroundTheory.LocalField.EqualChar
