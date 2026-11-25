-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.fderiv_eq_quad_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:25.454465+00:00
-- url     : https://prove2.me/submissions/222b318f-3aa8-49c1-a221-cfff31790434

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivEqQuadComm
import Theorems.Thm_GlobalTheory_Mem_Lift_IsQuadOf_apply_vec
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_dH_calculus
import Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_skew
import Theorems.Thm_GlobalTheory_Mem_Lift_dH_add
import Theorems.Thm_GlobalTheory_Mem_Lift_dH_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift
namespace GlobalTheory.Mem.Lift
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (X : V → V) (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (fun x y => om x y) X c p q → ∀ f, Sm ρ f → ∀ w, fderiv ℝ (fun u => ρ u f) w (X w) = quad ρ c p q (ρ w f) - ρ w (quad ρ c p q f) := by
  intro V _ _ B _ _ om ρ h0 hH X κ _ c p q hQ f hf w
  have C := GlobalTheory.Mem.Lift.DCalc.dH_calculus V B om ρ h0 hH
  obtain ⟨h1, h2, h3, h4, -⟩ := C f hf
  have skew : om w (X w) = - om (X w) w := by
    have := h0 (w + X w)
    simp only [map_add, _root_.add_apply, h0] at this
    linarith
  have key : ∀ u v, dH ρ u (dH ρ v (ρ w f)) = ρ w (dH ρ u (dH ρ v f))
      + (2 * π * I : ℂ) • ρ w ((om v w : ℂ) • dH ρ u f + (om u w : ℂ) • dH ρ v f)
      + ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om v w : ℂ) * (om u w : ℂ)))) • ρ w f := by
    intro u v
    obtain ⟨-, g2, -, g4, -⟩ := C _ (h1 v)
    have hs : Sm ρ ((2 * π * I * (om v w : ℂ)) • ρ w f) := (smS ρ).smul_mem _ (h2 w)
    rw [h4 v w, dH_add u (g2 w) hs, dH_smul u _ (h2 w), g4 u w, h4 u w]
    simp only [map_add, map_smul]
    module
  have e1 := hQ.apply_vec (fderiv ℝ (fun u => ρ u f) 0).toLinearMap w
  have e1' : (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = dH ρ (X w) f := e1
  have e2 := hQ (Complex.ofRealCLM.toLinearMap ∘ₗ (om.flip w).toLinearMap) w
  have e2' : 2 * π * I * ∑ i, c i * ((om (q i) w : ℂ) * (om (p i) w : ℂ) + (om (p i) w : ℂ) * (om (q i) w : ℂ))
      = (om (X w) w : ℂ) := e2
  have e3 : ∑ i, c i * ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om (q i) w : ℂ) * (om (p i) w : ℂ))))
      = π * I * (om (X w) w : ℂ) := by
    rw [← e2', Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i, c i • (2 * π * I : ℂ) • ρ w ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = ρ w (dH ρ (X w) f) := by
    rw [← e1', map_smul, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_comm]
  have e5 : quad ρ c p q (ρ w f) = ρ w (quad ρ c p q f) + ρ w (dH ρ (X w) f)
      + (π * I * (om (X w) w : ℂ)) • ρ w f := by
    rw [← e3, ← e4, Finset.sum_smul]
    unfold quad
    rw [map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key, smul_add, smul_add, map_smul, smul_smul (c i) _ (ρ w f)]
  rw [h3, e5, skew]
  push_cast
  module
end GlobalTheory.Mem.Lift
