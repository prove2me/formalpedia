-- Prove2me | solution 1 for GlobalTheory.differentiable_rmul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:35:59.003439+00:00
-- url     : https://prove2.me/submissions/feebf5a8-bd87-4734-aa18-b333ac611df9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x I : Frame Ψ r) :
    Differentiable ℂ fun z : Frame Ψ r => rmul x (I + z) := by
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  have : (fun z : Frame Ψ r => rmul x (I + z) τ a b) =
      fun z => ∑ k, x τ a k * (I τ k b + z τ k b) := by
    funext z
    simp [rmul, mat, mul_apply]
  rw [this]
  fun_prop
end GlobalTheory
