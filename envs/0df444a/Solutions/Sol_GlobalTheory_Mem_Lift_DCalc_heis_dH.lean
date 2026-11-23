-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.heis_dH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:27.003869+00:00
-- url     : https://prove2.me/submissions/70442211-ef80-40b9-909d-287b4615eb70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_line
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_phase
import Theorems.Thm_GlobalTheory_Mem_Lift_hasDerivAt_dH


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
theorem _root_.solution (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w y : V) :
    ρ w (dH ρ y f) = fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f := by
  have hd : Differentiable ℝ (fun u => ρ u f) :=
    (show ContDiff ℝ ∞ (fun u => ρ u f) from hf).differentiable (by simp)
  have h1 : HasDerivAt (fun t : ℝ => ρ w (ρ (t • y) f)) (ρ w (dH ρ y f)) 0 := by
    have hl := hasDerivAt_dH y hf
    exact ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => ρ w (ρ (t • y) f))
      (fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f) 0 := by
    have hp := hasDerivAt_phase (om w y) (hasDerivAt_line hd w y)
    convert hp using 1
    · funext t
      rw [h.2.1]
      simp
    · simp
  exact h1.unique h2
end GlobalTheory.Mem.Lift.DCalc
