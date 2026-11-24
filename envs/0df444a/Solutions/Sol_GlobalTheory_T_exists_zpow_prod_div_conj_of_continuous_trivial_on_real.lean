-- Prove2me | solution 1 for GlobalTheory.T.exists_zpow_prod_div_conj_of_continuous_trivial_on_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:07.484609+00:00
-- url     : https://prove2.me/submissions/71edb761-e529-46a3-891a-f8bec2f32357

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryCharPiComplexUnitsEqProdZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryCharPiComplexUnitsEqProdZpowStatement
import Theorems.Thm_GlobalTheory_unitaryChar_pi_complexUnits_eq_prod_zpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (f : (ι → ℂˣ) →* Circle), Continuous f → (∀ z : ι → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → f z = 1) → ∃ k : ι → ℤ, ∀ z, ((f z : Circle) : ℂ) = ∏ i, ((z i : ℂ) / starRingEnd ℂ (z i : ℂ)) ^ k i := by
  first | exact @GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow | exact GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow | (intros; apply GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow <;> assumption)
end _root_.GlobalTheory.T
