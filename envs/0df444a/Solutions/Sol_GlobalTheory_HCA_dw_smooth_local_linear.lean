-- Prove2me | solution 1 for GlobalTheory.HCA.dw_smooth_local_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:51.077544+00:00
-- url     : https://prove2.me/submissions/7538338e-74bf-4e34-b604-220b370eadd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Theorems.Thm_GlobalTheory_HCA_contDiffOn_dw_of_isOpen
import Theorems.Thm_GlobalTheory_HCA_eqOn_dw_of_isOpen
import Theorems.Thm_GlobalTheory_HCA_eqOn_dw_lincomb_of_isOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)),
    (∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ (dw w u) U) ∧
    (∀ u v : E d → ℂ, Set.EqOn u v U → Set.EqOn (dw w u) (dw w v) U) ∧
    (∀ u v : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U → ∀ s t : ℂ,
      Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U) :=
  fun _ _ hU w => ⟨contDiffOn_dw_of_isOpen hU w, eqOn_dw_of_isOpen hU w,
    eqOn_dw_lincomb_of_isOpen hU w⟩
end GlobalTheory.HCA
