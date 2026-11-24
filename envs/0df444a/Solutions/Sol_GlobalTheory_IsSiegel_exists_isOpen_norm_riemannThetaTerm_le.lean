-- Prove2me | solution 1 for GlobalTheory.IsSiegel.exists_isOpen_norm_riemannThetaTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:17.468944+00:00
-- url     : https://prove2.me/submissions/8d10121d-e35b-4c9f-a9a6-4bc42f7b6556

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Theorems.Thm_GlobalTheory_IsSiegel_exists_eventually_norm_riemannThetaTerm_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : ∃ U : Set ((ι → ℂ) × (ι → ι → ℂ)), IsOpen U ∧ (v, of.symm Ω) ∈ U ∧
      ∃ u : (ι → ℤ) → ℝ, Summable u ∧
        ∀ n, ∀ p ∈ U, ‖riemannThetaTerm a b (of p.2) p.1 n‖ ≤ u n := by
  obtain ⟨c, hc, S, hS⟩ := h.exists_eventually_norm_riemannThetaTerm_le a b v
  obtain ⟨U, hU, hUo, hp⟩ := _root_.eventually_nhds_iff.mp hS
  exact ⟨U, hUo, hp, _, summable_riemannThetaBound a hc S, fun n p hp => hU p hp n⟩
end IsSiegel
end GlobalTheory
