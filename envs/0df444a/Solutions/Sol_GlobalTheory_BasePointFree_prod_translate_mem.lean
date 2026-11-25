-- Prove2me | solution 1 for GlobalTheory.BasePointFree.prod_translate_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:53.251591+00:00
-- url     : https://prove2.me/submissions/f667ec77-dd6b-4c77-acdb-890feeae3eb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
import Theorems.Thm_GlobalTheory_BasePointFree_HC_add_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.BasePointFree
namespace GlobalTheory.BasePointFree
theorem _root_.solution {E : Type} [Field E] [NumberField E] (X : PT E) {n : ℕ}
    (s : (Fin n → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 n) (m : ℕ) (c : Fin n → Vsp X.dim) :
    (fun w => s (w + (1 : ℂ) • c) ^ m * s (w + (-(m : ℂ)) • c)) ∈ X.Sec (m + 1) n := by
  obtain ⟨hd, hs⟩ := hs
  refine ⟨?_, fun γ hγ v => ?_⟩
  · exact ((hd.comp (by fun_prop)).pow m).mul (hd.comp (by fun_prop))
  · simp only
    rw [add_right_comm v γ, add_right_comm v γ, hs γ hγ, hs γ hγ, HC_add_smul_left,
      HC_add_smul_left, mul_pow, mul_pow, ← Complex.exp_nat_mul]
    have : ((m + 1 : ℕ) : ℂ) * Real.pi * HC v γ + ((m + 1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2 =
        (m : ℂ) * (((1 : ℕ) : ℂ) * Real.pi * (HC v γ + 1 * HC c γ) +
          ((1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2) +
        (((1 : ℕ) : ℂ) * Real.pi * (HC v γ + -(m : ℂ) * HC c γ) +
          ((1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2) := by
      push_cast; ring
    rw [this, Complex.exp_add ((m : ℂ) * _)]
    ring
end GlobalTheory.BasePointFree
