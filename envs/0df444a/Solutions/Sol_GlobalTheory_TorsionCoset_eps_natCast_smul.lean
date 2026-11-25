-- Prove2me | solution 1 for GlobalTheory.TorsionCoset.eps_natCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:14:49.600497+00:00
-- url     : https://prove2.me/submissions/d23a95fa-8dff-4772-a7d1-77b4061bc311

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Theorems.Thm_GlobalTheory_TorsionCoset_eps_zero
import Theorems.Thm_GlobalTheory_TorsionCoset_natCast_smul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


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
theorem _root_.solution (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (X.eps ((k : ℂ) • x) : ℝ) = (X.eps x : ℝ) ^ k := by
  induction k with
  | zero => simp [eps_zero]
  | succ k ih =>
    have h := X.eps_add _ (natCast_smul_mem X hx k) x hx
    have him : (Hf ((k : ℂ) • x) x).im = 0 := by
      unfold Hf
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [PiLp.smul_apply, mul_assoc, Complex.mul_conj]
    rw [show ((k + 1 : ℕ) : ℂ) • x = (k : ℂ) • x + x by push_cast; rw [add_smul, one_smul],
      h, ih, him]
    simp [pow_succ]
end GlobalTheory.TorsionCoset
