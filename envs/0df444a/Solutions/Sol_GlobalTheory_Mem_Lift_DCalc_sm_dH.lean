-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.sm_dH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:12.425223+00:00
-- url     : https://prove2.me/submissions/c796ccac-61c0-427f-b268-db91fd6b37fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_heis_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_contDiff_fderiv

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
theorem _root_.solution (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have e : (fun u => ρ u (dH ρ v f)) =
      fun u => fderiv ℝ (fun u => ρ u f) u v + (π * I * (om u v : ℂ)) • ρ u f := by
    funext u
    exact heis_dH h hf u v
  show ContDiff ℝ ∞ (fun u => ρ u (dH ρ v f))
  rw [e]
  refine ((contDiff_fderiv hf).clm_apply contDiff_const).add ?_
  exact (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (om.contDiff.clm_apply contDiff_const))).smul hf'
end GlobalTheory.Mem.Lift.DCalc
