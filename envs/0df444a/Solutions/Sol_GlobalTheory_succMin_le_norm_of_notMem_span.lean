-- Prove2me | solution 1 for GlobalTheory.succMin_le_norm_of_notMem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:11.229589+00:00
-- url     : https://prove2.me/submissions/7b00e96b-dce5-4054-b5cd-6ad3acdbc971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Theorems.Thm_GlobalTheory_mem_span_of_norm_lt_succMin

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
    (hx : x ∈ L) (h : x ∉ span ℝ (v '' {j | (j : ℕ) < i})) : succMin L (i + 1) ≤ ‖x‖ :=
  not_lt.1 fun h' => h (mem_span_of_norm_lt_succMin hv hL hN hi hx h')
end GlobalTheory
