-- Prove2me | solution 1 for GlobalTheory.JetConj.wr_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:25.082681+00:00
-- url     : https://prove2.me/submissions/1c34bc59-687a-4034-af14-b4b4c8b3202d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
namespace GlobalTheory.JetConj
theorem _root_.solution {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c d z : ℂ) :
    wr (fun w => f (c * w + d)) z = c ^ 2 * wr f (c * z + d) := by
  have key : ∀ {g : ℂ → ℂ}, Differentiable ℂ g →
      deriv (fun w => g (c * w + d)) = fun w => c * deriv g (c * w + d) := by
    intro g hg
    funext w
    have := (hg (c * w + d)).hasDerivAt.comp w (((hasDerivAt_id w).const_mul c).add_const d)
    rw [show (fun w => g (c * w + d)) = g ∘ fun w => c * id w + d from rfl, this.deriv]
    ring
  unfold wr
  rw [key hf, deriv_const_mul_field', key hf.deriv]
  ring
end GlobalTheory.JetConj
