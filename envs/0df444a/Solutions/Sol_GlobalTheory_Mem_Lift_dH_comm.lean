-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.dH_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:49.054848+00:00
-- url     : https://prove2.me/submissions/9ec37270-22fd-4390-bad2-63da6cee89b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped ContDiff Real
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
open MeasureTheory Complex Matrix
open scoped ContDiff Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B]
namespace GlobalTheory.Mem.Lift
namespace _root_.GlobalTheory.Mem.Lift
theorem _root_.solution {ρ : V → B →L[ℂ] B} (A : B →L[ℂ] B)
    (hA : ∀ v f, A (ρ v f) = ρ v (A f)) {f : B} (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    _root_.GlobalTheory.RealWeil.Sm ρ (A f) ∧
      ∀ v, _root_.GlobalTheory.Mem.Lift.dH ρ v (A f) = A (_root_.GlobalTheory.Mem.Lift.dH ρ v f) := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hfun : (fun u => ρ u (A f)) = fun u => (A.restrictScalars ℝ) (ρ u f) := by
    funext u
    simp [hA]
  refine ⟨?_, fun v => ?_⟩
  · unfold _root_.GlobalTheory.RealWeil.Sm
    rw [hfun]
    exact (A.restrictScalars ℝ).contDiff.comp hf
  · unfold _root_.GlobalTheory.Mem.Lift.dH
    have h : HasFDerivAt (fun u => (A.restrictScalars ℝ) (ρ u f))
        ((A.restrictScalars ℝ).comp (fderiv ℝ (fun u => ρ u f) 0)) 0 :=
      (A.restrictScalars ℝ).hasFDerivAt.comp (0 : V) hf'.hasFDerivAt
    rw [hfun, h.fderiv]
    rfl
end _root_.GlobalTheory.Mem.Lift
end GlobalTheory.Mem.Lift
