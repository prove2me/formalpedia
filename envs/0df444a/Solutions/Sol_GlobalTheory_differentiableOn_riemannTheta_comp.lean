-- Prove2me | solution 1 for GlobalTheory.differentiableOn_riemannTheta_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:28.373921+00:00
-- url     : https://prove2.me/submissions/35f4ec0b-76bd-4d42-b171-6ba69b6b6c8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Theorems.Thm_GlobalTheory_IsSiegel_analyticAt_riemannTheta_entries

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory
theorem _root_.solution (a b : ι → ℝ) {Ω : E → Matrix ι ι ℂ} {v : E → ι → ℂ}
    {U : Set E} (h : ∀ x ∈ U, IsSiegel (Ω x)) (hΩ : ∀ i j, DifferentiableOn ℂ (fun y => Ω y i j) U)
    (hv : DifferentiableOn ℂ v U) :
    DifferentiableOn ℂ (fun y => riemannTheta a b (Ω y) (v y)) U := fun x hx =>
  ((h x hx).analyticAt_riemannTheta_entries a b (v x)).differentiableAt.comp_differentiableWithinAt
    (f := fun y => (v y, of.symm (Ω y))) x
    ((hv x hx).prodMk
      (differentiableWithinAt_pi.mpr fun i => differentiableWithinAt_pi.mpr fun j => hΩ i j x hx))
end GlobalTheory
