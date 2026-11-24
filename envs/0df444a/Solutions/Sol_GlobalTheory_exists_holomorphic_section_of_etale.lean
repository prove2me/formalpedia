-- Prove2me | solution 1 for GlobalTheory.exists_holomorphic_section_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:45.033639+00:00
-- url     : https://prove2.me/submissions/3fb9ff52-e9ad-4b74-9a40-060b0dce5832

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Theorems.Thm_GlobalTheory_exists_testFunctions_subset_of_mem_nhds
import Theorems.Thm_GlobalTheory_AffinePoints_exists_chart_of_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open AffinePoints
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) := by
  intro g A _ _ _ _ _ e he
  let φ : MvPolynomial (Fin g) ℂ →ₐ[ℂ] A := IsScalarTower.toAlgHom ℂ _ A
  have hφ : φ.Etale := RingHom.etale_algebraMap.2 inferInstance
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin g) ℂ) inferInstance inferInstance
  obtain ⟨c, hc, hcφ, han⟩ := exists_chart_of_etale φ hφ e
  have h0 : c e = 0 := by rw [hcφ]; ext i; exact he i
  obtain ⟨n, f, ε, hε, hf⟩ := exists_testFunctions_subset_of_mem_nhds (c.open_source.mem_nhds hc)
  refine ⟨c.target, c.symm, n, f, ε, c.open_target, h0 ▸ c.map_source hc, ?_, hε,
    fun a => (han a).differentiableOn, fun w hw i => ?_, fun x hx => ?_⟩
  · rw [← h0, c.left_inv hc]
  · have := c.right_inv hw
    rw [hcφ] at this
    exact congrFun this i
  · exact ⟨c x, c.map_source (hf x hx), (c.left_inv (hf x hx)).symm⟩
end GlobalTheory
