-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.valued_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:38:50.075668+00:00
-- url     : https://prove2.me/submissions/d98879fa-ef41-4709-ae9e-2e3534859276

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
omit [Fact p.Prime] [CharP K p]
namespace GroundTheory.LocalField.EqualChar
theorem _root_.solution {x : 𝓀[K]⸨X⸩} (hx : x ≠ 0) : Valued.v x ≤ 1 ↔ 0 ≤ x.order := by
  have h := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := 𝓀[K]) (D := 0) (f := x)
  simp only [neg_zero, exp_zero] at h
  rw [h]
  constructor
  · intro H
    by_contra hneg
    exact hx (HahnSeries.coeff_order_eq_zero.mp (H _ (not_le.mp hneg)))
  · intro H n hn
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hn H)
end GroundTheory.LocalField.EqualChar
