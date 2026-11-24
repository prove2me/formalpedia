-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.dH_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:31:03.726674+00:00
-- url     : https://prove2.me/submissions/9655a53e-b783-46b1-b6a1-c7e579a97ebc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_heis_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_sm_heis
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_sm_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_dH_heis
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_dH_commutator

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
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  intro V _ _ B _ _ om ρ h0 h f hf
  exact ⟨fun v => sm_dH h hf v, fun w => sm_heis h hf w,
    fun w y => eq_sub_of_add_eq (heis_dH h hf w y).symm, fun v w => dH_heis h0 h hf v w,
    fun u v => dH_commutator h0 h hf u v⟩
end GlobalTheory.Mem.Lift.DCalc
