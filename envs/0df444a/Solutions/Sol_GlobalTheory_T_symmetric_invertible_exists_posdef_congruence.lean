-- Prove2me | solution 1 for GlobalTheory.T.symmetric_invertible_exists_posdef_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:53.489201+00:00
-- url     : https://prove2.me/submissions/3daa0967-855a-484f-b94a-df0cd7f28d15

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SymmetricInvertibleExistsPosdefCongruence
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SymmetricInvertibleExistsPosdefCongruenceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_exists_posDef_majorant_of_isSymm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 → ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | exact GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | (intros; apply GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm <;> assumption)
end _root_.GlobalTheory.T
