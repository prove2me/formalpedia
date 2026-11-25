-- Prove2me | solution 1 for GlobalTheory.T.exists_weak_approx_unit_finite_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:32.984668+00:00
-- url     : https://prove2.me/submissions/92837b80-4152-48a4-8df3-ee3504ce56e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsWeakApproxUnitFinitePlace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsWeakApproxUnitFinitePlaceStatement
import Theorems.Thm_GlobalTheory_HkFin_exists_weak_approx_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ), ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.HkFin.exists_weak_approx_unit | exact GlobalTheory.HkFin.exists_weak_approx_unit | (intros; apply GlobalTheory.HkFin.exists_weak_approx_unit <;> assumption)
end _root_.GlobalTheory.T
