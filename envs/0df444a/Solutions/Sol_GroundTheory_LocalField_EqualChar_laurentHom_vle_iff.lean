-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.laurentHom_vle_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:38:04.209889+00:00
-- url     : https://prove2.me/submissions/40a28fe8-3f76-4003-bc23-0739e19964f4

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent
import Theorems.Thm_GroundTheory_LocalField_EqualChar_isEquiv_comap_laurentHom

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
theorem _root_.solution (x y : 𝓀[K]⸨X⸩) :
    laurentHom K p x ≤ᵥ laurentHom K p y ↔ x ≤ᵥ y := by
  rw [Valuation.Compatible.vle_iff_le (v := valuation K),
    Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation 𝓀[K]⸨X⸩ ℤᵐ⁰))]
  simpa using (isEquiv_comap_laurentHom K p).le_iff_le (x := x) (y := y)
end GroundTheory.LocalField.EqualChar
