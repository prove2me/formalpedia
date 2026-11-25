-- Prove2me | solution 1 for GlobalTheory.KernelTri.kernel_trilinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:49.343139+00:00
-- url     : https://prove2.me/submissions/5bac0a77-0aea-4011-b4c5-c4d38390ed84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwistedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocalTrilinearFormUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity ValuativeRel IsLocalRing
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.KernelTri
namespace GlobalTheory.KernelTri
theorem _root_.solution {V' A B V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup V] [Module ℂ V] (θ : V' →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] V)
    (p : Submodule ℂ (B →ₗ[ℂ] V)) (hmem : ∀ v a, θ v a ∈ p) (v : V') (a : A) :
    (th1 θ p hmem v a).1 = θ v a := rfl
end GlobalTheory.KernelTri
