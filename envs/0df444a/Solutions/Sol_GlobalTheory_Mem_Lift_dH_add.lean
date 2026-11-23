-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.dH_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:51.546792+00:00
-- url     : https://prove2.me/submissions/b3588f96-eef0-4a9f-9a30-3cba0f7fca5f

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
theorem _root_.solution {ρ : V → B →L[ℂ] B} (v : V) {f g : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) (hg : _root_.GlobalTheory.RealWeil.Sm ρ g) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (f + g) =
      _root_.GlobalTheory.Mem.Lift.dH ρ v f + _root_.GlobalTheory.Mem.Lift.dH ρ v g := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hg' : DifferentiableAt ℝ (fun u => ρ u g) 0 :=
    (ContDiff.differentiable hg (by simp)).differentiableAt
  unfold _root_.GlobalTheory.Mem.Lift.dH
  simp only [map_add]
  rw [(hf'.hasFDerivAt.fun_add hg'.hasFDerivAt).fderiv]
  rfl
end _root_.GlobalTheory.Mem.Lift
end GlobalTheory.Mem.Lift
