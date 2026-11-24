-- Prove2me | solution 1 for GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:16.207963+00:00
-- url     : https://prove2.me/submissions/567d9662-b4b8-410a-b61c-34025abaaf57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivIteratedFDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by
  induction n generalizing j with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.zero_add]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      norm_iteratedFDeriv_fderiv, ih (j + 1)]
    rw [show n + (j + 1) = n + 1 + j by omega]
end GlobalTheory
