-- Prove2me | solution 1 for GlobalTheory.IsSiegel.analyticAt_riemannTheta_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:12.134871+00:00
-- url     : https://prove2.me/submissions/02cec73f-66ef-4bb8-8e28-f67a25a45aed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Theorems.Thm_GlobalTheory_differentiable_riemannThetaTerm
import Theorems.Thm_GlobalTheory_IsSiegel_exists_isOpen_norm_riemannThetaTerm_le
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_locally_normal


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
    (a b : ι → ℝ) (v : ι → ℂ) :
    AnalyticAt ℂ (fun p : (ι → ℂ) × (ι → ι → ℂ) => riemannTheta a b (of p.2) p.1)
      (v, of.symm Ω) := by
  obtain ⟨U, hU, hp, u, hu, hle⟩ := h.exists_isOpen_norm_riemannThetaTerm_le a b v
  exact SCV.analyticAt_of_differentiableOn (SCV.differentiableOn_tsum_of_locally_normal hU
    (fun n => (differentiable_riemannThetaTerm a b n).differentiableOn)
    fun x hx => ⟨U, hU.mem_nhds hx, u, hu, hle⟩) (hU.mem_nhds hp)
end IsSiegel
end GlobalTheory
