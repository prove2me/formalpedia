-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.smodEq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:24:18.4887+00:00
-- url     : https://prove2.me/submissions/c679a2b0-9e07-48c6-9545-1b62b30aa6a1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Theorems.Thm_GlobalTheory_PadicComplexHost_valuation_coe_eq_norm
import Theorems.Thm_GlobalTheory_PadicComplexHost_norm_p

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
open GlobalTheory GlobalTheory.PadicComplexHost
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.PadicComplexHost
theorem _root_.solution (n : ℕ) (x y : 𝓞_ℂ_[p]) :
    x ≡ y [SMOD ((span {((p : ℕ) : 𝓞_ℂ_[p])}) ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton, (PadicComplexInt.integers p).dvd_iff_le, map_pow, map_natCast,
    ← norm_p, ← norm_pow, ← valuation_coe_eq_norm, ← valuation_coe_eq_norm, NNReal.coe_le_coe]
  rfl
end GlobalTheory.PadicComplexHost
