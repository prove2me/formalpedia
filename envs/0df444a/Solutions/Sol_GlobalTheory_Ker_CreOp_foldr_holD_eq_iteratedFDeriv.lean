-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.foldr_holD_eq_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:41:21.818159+00:00
-- url     : https://prove2.me/submissions/fe6eda2c-c213-4a90-9b8e-acd47547413a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_Ker_CreOp_holD_of_differentiableAt
import Theorems.Thm_GlobalTheory_SCV_contDiff_of_differentiable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.Ker GlobalTheory.Ker.CreOp
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable {σ : Type} (u : σ → W)
namespace GlobalTheory.Ker.CreOp
theorem _root_.solution [FiniteDimensional ℂ W] {θ : W → ℂ}
    (hθ : Differentiable ℂ θ) (M : List σ) :
    M.foldr (fun l => holD (u l)) θ =
      fun z => iteratedFDeriv ℂ M.length θ z fun k => u (M.get k) := by
  have hθ' : ContDiff ℂ ⊤ θ := GlobalTheory.SCV.contDiff_of_differentiable hθ ⊤
  induction M with
  | nil => funext z; simp
  | cons l M ih =>
    have hA : Differentiable ℂ (iteratedFDeriv ℂ M.length θ) :=
      hθ'.differentiable_iteratedFDeriv (WithTop.coe_lt_top _)
    funext z
    simp only [List.foldr_cons]
    rw [ih, holD_of_differentiableAt ((hA z).continuousMultilinear_apply_const _),
      fderiv_continuousMultilinear_apply_const_apply (hA z)]
    rfl
end GlobalTheory.Ker.CreOp
