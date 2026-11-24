-- Prove2me | solution 1 for GlobalTheory.InertZeta.exists_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:31:14.359841+00:00
-- url     : https://prove2.me/submissions/07dd4e71-452f-450e-88c8-7a9e8fd552ae

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) : ∃ τ ∈ intL L, τ + σ τ = 1 := by
  obtain ⟨hσσ, hσ, -, -, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hx0 : σ x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  refine ⟨σ x * (σ x - x)⁻¹, mul_mem (by rw [GlobalTheory.UnitarySwap.mem_int, hσ]; exact hx)
    (by rw [GlobalTheory.UnitarySwap.mem_int, map_inv₀, hx1, inv_one]), ?_⟩
  rw [map_mul, map_inv₀, map_sub, hσσ, ← neg_sub (σ x) x, inv_neg]
  linear_combination mul_inv_cancel₀ hx0
end GlobalTheory.InertZeta
