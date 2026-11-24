-- Prove2me | solution 1 for GlobalTheory.mem_span_of_norm_lt_succMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:33.2618+00:00
-- url     : https://prove2.me/submissions/3fa356ec-a669-4953-ae93-221e746f88da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Theorems.Thm_GlobalTheory_mem_span_of_lt_succMinOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}
namespace GlobalTheory
theorem _root_.solution {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : ‖x‖ < succMin L (i + 1)) : x ∈ span ℝ (v '' {j | (j : ℕ) < i}) :=
  mem_span_of_lt_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E)) hv hL hN hi hx
    (norm_nonneg x) h
end GlobalTheory
