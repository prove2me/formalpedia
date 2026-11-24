-- Prove2me | solution 1 for GlobalTheory.T.principal_series_coordinate_near_infinity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:14.569708+00:00
-- url     : https://prove2.me/submissions/ef36e439-2a1b-401d-b236-7dd71937a94d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinity
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinityStatement
import Theorems.Thm_GlobalTheory_PrinTwo_coord_eq_of_far


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by
  first | exact @GlobalTheory.PrinTwo.coord_eq_of_far | exact GlobalTheory.PrinTwo.coord_eq_of_far | (intros; apply GlobalTheory.PrinTwo.coord_eq_of_far <;> assumption)
end _root_.GlobalTheory.T
