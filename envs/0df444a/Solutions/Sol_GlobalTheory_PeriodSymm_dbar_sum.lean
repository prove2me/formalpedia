-- Prove2me | solution 1 for GlobalTheory.PeriodSymm.dbar_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:29.624462+00:00
-- url     : https://prove2.me/submissions/3a5d02bd-aa5d-4475-ab8f-8a6117c7316f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
namespace GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma hasFDerivAt_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ}
    {A' : ι → E →L[ℝ] ℂ} {x : E} (h : ∀ i ∈ s, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i ∈ s, A i y) (∑ i ∈ s, A' i) x := by
  exact HasFDerivAt.fun_sum h
end GlobalTheory.PeriodSymm
end

set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
open GlobalTheory GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PeriodSymm
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} {z : E}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (u : E) :
    dbar (fun x => ∑ i ∈ s, f i x) u z = ∑ i ∈ s, dbar (f i) u z := by
  have H := hasFDerivAt_finset_sum s (fun i hi => (h i hi).hasFDerivAt)
  rw [dbar, H.fderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rfl
end GlobalTheory.PeriodSymm
