-- Prove2me | solution 1 for GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:40.626549+00:00
-- url     : https://prove2.me/submissions/20ea86aa-a604-415c-9d4d-c094126ed42e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPowerStatement
import Theorems.Thm_GlobalTheory_PMonE_existsUnique_integral_gsum_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → ∀ U : ℕ → Matrix m m F, (∀ i j, ‖(U 0 - 1) i j‖ < 1) → (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) → ∀ b : m → F, Integral b → ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  first | exact @GlobalTheory.PMonE.existsUnique_integral_gsum_eq | exact GlobalTheory.PMonE.existsUnique_integral_gsum_eq | (intros; apply GlobalTheory.PMonE.existsUnique_integral_gsum_eq <;> assumption)
end _root_.GlobalTheory.T
