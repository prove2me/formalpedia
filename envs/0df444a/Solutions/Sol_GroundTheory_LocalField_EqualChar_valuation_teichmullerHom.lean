-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.valuation_teichmullerHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:54.603796+00:00
-- url     : https://prove2.me/submissions/2c872021-64b6-498f-a6b7-329ff1e2e92f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent

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
theorem _root_.solution {a : 𝓀[K]} (ha : a ≠ 0) :
    valuation K (teichmullerHom K p a : K) = 1 :=
  (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp
    ((teichmullerHom K p).isUnit_map ha.isUnit)
end GroundTheory.LocalField.EqualChar
