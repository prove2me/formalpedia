-- Prove2me | solution 1 for GlobalTheory.TorsionCoset.isPi_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:38:34.527328+00:00
-- url     : https://prove2.me/submissions/b485ba52-0d20-43ca-b139-63b83014643e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Theorems.Thm_GlobalTheory_TorsionCoset_natCast_smul_mem
import Theorems.Thm_GlobalTheory_TorsionCoset_eps_natCast_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.TorsionCoset
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TorsionCoset
theorem _root_.solution (X : PT E) (n : ℕ) : IsPi X (n ^ 2) ((n : ℂ) • LinearMap.id) := by
  refine ⟨fun α v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    simp [act]
    ring
  · exact natCast_smul_mem X hx n
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    unfold Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
    ring
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    have h := eps_natCast_smul X hx n
    have h2 : (X.eps x : ℝ) ^ n = (X.eps x : ℝ) ^ (n ^ 2) := by
      rcases X.eps_pm x hx with h1 | h1
      · simp [h1]
      · rw [h1]
        push_cast
        rw [sq, pow_mul]
        rcases neg_one_pow_eq_or ℝ n with h3 | h3 <;> simp [h3]
    exact_mod_cast h.trans h2
end GlobalTheory.TorsionCoset
