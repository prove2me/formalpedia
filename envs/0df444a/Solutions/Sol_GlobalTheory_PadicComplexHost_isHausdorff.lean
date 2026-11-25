-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.isHausdorff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:33:18.165417+00:00
-- url     : https://prove2.me/submissions/e9b41b8a-7b8d-4eae-a1ea-db855a29f527

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Theorems.Thm_GlobalTheory_PadicComplexHost_smodEq_iff
import Theorems.Thm_GlobalTheory_PadicComplexHost_tendsto_inv_p_pow

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
theorem _root_.solution : IsHausdorff (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun x hx => ?_⟩
  have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := fun n => by
    simpa using (smodEq_iff p n x 0).1 (hx n)
  have h0 : ‖(x : ℂ_[p])‖ ≤ 0 :=
    ge_of_tendsto (tendsto_inv_p_pow p) (Filter.Eventually.of_forall h)
  exact Subtype.ext (norm_le_zero_iff.1 h0)
end GlobalTheory.PadicComplexHost
