-- Prove2me | solution 1 for GlobalTheory.bijective_fin_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:02:58.8427+00:00
-- url     : https://prove2.me/submissions/c5277b7d-508f-44e1-a23b-452067670d50

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply
attribute [local simp] GlobalTheory.thetaLevelBasis_apply

set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
omit [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (hN : 0 < N) :
    Function.Bijective fun (c : ι → Fin N) i => ((((c i : ℕ) : ℤ)) : ZMod N) := by
  have : NeZero N := ⟨hN.ne'⟩
  refine ⟨fun c c' h => funext fun i => Fin.ext ?_, fun c => ⟨fun i => ⟨(c i).val, ZMod.val_lt _⟩, ?_⟩⟩
  · have := congrArg ZMod.val (congrFun h i)
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Fin.is_lt _)] using this
  · funext i; simp
end GlobalTheory
