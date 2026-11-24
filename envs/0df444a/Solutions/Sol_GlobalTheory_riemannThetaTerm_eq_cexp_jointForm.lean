-- Prove2me | solution 1 for GlobalTheory.riemannThetaTerm_eq_cexp_jointForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:32:43.899631+00:00
-- url     : https://prove2.me/submissions/698ad045-d7ac-4a1a-a4ff-dc78eadd0f6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
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
theorem _root_.solution (a b : ι → ℝ) (n : ι → ℤ)
    (p : (ι → ℂ) × (ι → ι → ℂ)) :
    riemannThetaTerm a b (of p.2) p.1 n =
      cexp (riemannThetaJointForm a n p + riemannThetaForm a n fun i => (b i : ℂ)) := by
  have : (fun i => p.1 i + (b i : ℂ)) = p.1 + fun i => (b i : ℂ) := rfl
  rw [riemannThetaTerm, riemannThetaJointForm_apply, riemannThetaForm_apply, this, dotProduct_add]
  congr 1
  ring
end GlobalTheory
