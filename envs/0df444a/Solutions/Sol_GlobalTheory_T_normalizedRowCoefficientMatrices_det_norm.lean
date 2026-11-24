-- Prove2me | solution 1 for GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:40.335801+00:00
-- url     : https://prove2.me/submissions/08e3a1b1-148e-470a-af6c-72ddd9a3458c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNormStatement
import Theorems.Thm_GlobalTheory_PMonE_coefB_det


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
theorem _root_.solution : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F), ϖ ≠ 0 → ∀ lam π : Fin h → F, (∀ j, lam j ≠ 0) → (∀ j, π j ≠ 0) → Antitone (fun j => ‖lam j‖) → Orth p lam → ∀ L U : ℕ, ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  first | exact @GlobalTheory.PMonE.coefB_det | exact GlobalTheory.PMonE.coefB_det | (intros; apply GlobalTheory.PMonE.coefB_det <;> assumption)
end _root_.GlobalTheory.T
