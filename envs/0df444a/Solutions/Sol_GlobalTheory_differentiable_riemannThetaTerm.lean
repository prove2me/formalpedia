-- Prove2me | solution 1 for GlobalTheory.differentiable_riemannThetaTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:45.440196+00:00
-- url     : https://prove2.me/submissions/e95e483a-d907-4a7d-8673-807a33de5707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
import Theorems.Thm_GlobalTheory_riemannThetaTerm_eq_cexp_jointForm
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero


attribute [local simp] GlobalTheory.riemannThetaJointForm_apply

set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (a b : ι → ℝ) (n : ι → ℤ) :
    Differentiable ℂ fun p : (ι → ℂ) × (ι → ι → ℂ) => riemannThetaTerm a b (of p.2) p.1 n := by
  simp only [riemannThetaTerm_eq_cexp_jointForm]
  fun_prop
end GlobalTheory
