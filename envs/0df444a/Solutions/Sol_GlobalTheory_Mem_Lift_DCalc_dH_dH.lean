-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.dH_dH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:47.359435+00:00
-- url     : https://prove2.me/submissions/440574a2-b01e-430d-b284-c072bac7bc97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_line
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_lin
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_heis_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_contDiff_fderiv
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_sm_dH
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
theorem _root_.solution (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (u v : V) :
    dH ρ u (dH ρ v f) = fderiv ℝ (fderiv ℝ fun u => ρ u f) 0 u v + (π * I * (om u v : ℂ)) • f := by
  have hd2 : Differentiable ℝ (fderiv ℝ fun u => ρ u f) :=
    (contDiff_fderiv hf).differentiable (by simp)
  have h1 := hasDerivAt_dH u (sm_dH h hf v)
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (fun u => ρ u f) (0 + t • u) v)
      (fderiv ℝ (fderiv ℝ fun u => ρ u f) 0 u v) 0 := by
    have hl := (hasDerivAt_line hd2 0 u).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using hl
  have hB := (hasDerivAt_lin (om u v)).smul (hasDerivAt_dH u hf)
  have h2 := hA.add hB
  have e : (fun t : ℝ => ρ (t • u) (dH ρ v f)) = fun t : ℝ =>
      fderiv ℝ (fun u => ρ u f) (0 + t • u) v + (π * I * ((t * om u v : ℝ) : ℂ)) • ρ (t • u) f := by
    funext t
    rw [heis_dH h hf]
    simp
  rw [e] at h1
  rw [h1.unique h2]
  simp [h.1]
end GlobalTheory.Mem.Lift.DCalc
