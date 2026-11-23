-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.sm_heis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:30.2698+00:00
-- url     : https://prove2.me/submissions/eeb800cc-a6c1-4e54-ae72-84ffd27d490c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.DCalc
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B}
namespace GlobalTheory.Mem.Lift.DCalc
theorem _root_.solution (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w : V) : Sm ρ (ρ w f) := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have e : (fun u => ρ u (ρ w f)) = fun u => cexp (π * I * (om u w : ℂ)) • ρ (u + w) f := by
    funext u
    exact h.2.1 u w f
  show ContDiff ℝ ∞ (fun u => ρ u (ρ w f))
  rw [e]
  apply ContDiff.smul
  · apply ContDiff.cexp
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (om.contDiff.clm_apply contDiff_const))
  · exact hf'.comp (contDiff_id.add contDiff_const)
end GlobalTheory.Mem.Lift.DCalc
