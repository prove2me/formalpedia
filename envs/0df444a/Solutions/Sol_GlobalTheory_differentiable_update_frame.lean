-- Prove2me | solution 1 for GlobalTheory.differentiable_update_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:13.023902+00:00
-- url     : https://prove2.me/submissions/95b2b65c-8faa-47f0-bb1b-a4008580ed16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrameSectionSliceEqPolyDivDetPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {r : ℕ}
    (x : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => Function.update x τ y) := by
  intro y
  exact (hasFDerivAt_update x y).differentiableAt
end GlobalTheory
