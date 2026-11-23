-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.dH_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:34.958172+00:00
-- url     : https://prove2.me/submissions/dc199dfa-022c-4242-9fab-c3b3655921f0

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
theorem _root_.solution {ρ : V → B →L[ℂ] B} (v : V) (a : ℂ) {f : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (a • f) = a • _root_.GlobalTheory.Mem.Lift.dH ρ v f := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  unfold _root_.GlobalTheory.Mem.Lift.dH
  simp only [map_smul]
  rw [(hf'.hasFDerivAt.fun_const_smul a).fderiv]
  rfl
end _root_.GlobalTheory.Mem.Lift
end GlobalTheory.Mem.Lift
