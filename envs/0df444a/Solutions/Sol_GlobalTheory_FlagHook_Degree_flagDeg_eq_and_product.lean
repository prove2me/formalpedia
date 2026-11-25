-- Prove2me | solution 1 for GlobalTheory.FlagHook.Degree.flagDeg_eq_and_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:41:27.997423+00:00
-- url     : https://prove2.me/submissions/10017621-7c37-40e7-b11e-584b5e2d5a92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde
import Theorems.Thm_GlobalTheory_FlagHook_Degree_eval_detE_rho
import Theorems.Thm_GlobalTheory_FlagHook_Degree_flagDeg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
noncomputable section
open GlobalTheory GlobalTheory.FlagHook GlobalTheory.FlagHook.Degree
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
namespace GlobalTheory.FlagHook.Degree
theorem _root_.solution :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (u : ι → Fin N → ℝ),
      flagDeg ι N u = ((dimFl ι N).factorial : ℝ) * ∏ τ, eval (u τ) (detE (rho N))) ∧
    ∀ (N : ℕ) (v : Fin N → ℝ), eval v (detE (rho N)) =
      (∏ a : Fin N, ∏ b ∈ Ioi a, (v a - v b)) / ∏ m ∈ range N, (m.factorial : ℝ) :=
  ⟨fun _ _ _ _ u => flagDeg_eq u, eval_detE_rho⟩
end GlobalTheory.FlagHook.Degree
