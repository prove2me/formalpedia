-- Prove2me | solution 1 for GlobalTheory.T.fibre_cosine_explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:07.47354+00:00
-- url     : https://prove2.me/submissions/32562a9d-5b4c-4ce5-8627-24bb300b0405

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreCosineExplicitFormula
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreCosineExplicitFormulaStatement
import Theorems.Thm_GlobalTheory_FibCos_cos_fs_moebius


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → ∀ x : ℂ, 1 + G 1 0 / G 0 0 * x ≠ 0 →
    GlobalTheory.FibCos.cos G x = 1 / (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ∧
    GlobalTheory.FibCos.fs G x = ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 *
      (1 / (Real.pi * (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ^ 2)) := by
  first | exact @GlobalTheory.FibCos.cos_fs_moebius | exact GlobalTheory.FibCos.cos_fs_moebius | (intros; apply GlobalTheory.FibCos.cos_fs_moebius <;> assumption)
end _root_.GlobalTheory.T
