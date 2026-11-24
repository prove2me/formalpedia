-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.dH_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:48.395778+00:00
-- url     : https://prove2.me/submissions/01a7854a-8872-4b70-8a4a-6dc0a77f7265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_line
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_phase
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_skew
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_heis_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_sm_heis
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
theorem _root_.solution (h0 : ∀ x, om x x = 0) (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f := by
  have hd : Differentiable ℝ (fun u => ρ u f) :=
    (show ContDiff ℝ ∞ (fun u => ρ u f) from hf).differentiable (by simp)
  have h1 := hasDerivAt_dH v (sm_heis h hf w)
  have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) (ρ w f))
      (fderiv ℝ (fun u => ρ u f) w v + (π * I * (om v w : ℂ)) • ρ w f) 0 := by
    have hp := hasDerivAt_phase (om v w) (hasDerivAt_line hd w v)
    convert hp using 1
    · funext t
      rw [h.2.1, add_comm (t • v) w]
      simp
    · simp
  rw [h1.unique h2, heis_dH h hf w v, skew h0 w v, add_assoc, ← add_smul]
  congr 2
  push_cast
  ring
end GlobalTheory.Mem.Lift.DCalc
