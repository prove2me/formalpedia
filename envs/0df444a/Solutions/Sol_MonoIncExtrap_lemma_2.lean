-- Prove2me | solution 1 for MonoIncExtrap.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:41:53.227681+00:00
-- url     : https://prove2.me/submissions/65f8be30-2282-47d5-b99f-18a53c339807

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1
import Definitions.Def_MonoIncExtrap_Algorithm2

open InnerProductSpace ThreeOpSplitting.Convergence

namespace Aux_MIEb

open MonoIncExtrap

theorem lip_ball {n : ℕ} (B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hloc : IsLocallyLipschitzOn F (closure (dom B))) (c : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    ∃ L : ℝ, 0 < L ∧ IsLipschitzOn F (ballIn B c R) L := by
  obtain ⟨L, hL, hLip⟩ := hloc (closure (dom B) ∩ Metric.closedBall c R) Set.inter_subset_left
    ((isCompact_closedBall c R).inter_left isClosed_closure)
  have sub : ∀ x, x ∈ ballIn B c R → x ∈ closure (dom B) ∩ Metric.closedBall c R := by
    intro x hx
    exact ⟨subset_closure hx.1, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.2⟩
  exact ⟨L, hL, fun x hx y hy => hLip x (sub x hx) y (sub y hy)⟩

end Aux_MIEb

namespace Aux_MIE2

open MonoIncExtrap

theorem perturb_lip {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (L ρ : ℝ) (hρ : 1 ≤ ρ)
    (z : EuclideanSpace ℝ (Fin n)) (h : IsLipschitzOn F S L) :
    IsLipschitzOn (perturb F ρ z) S (L + 1) := by
  intro x hx y hy
  have hc0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr (by linarith)
  have hc1 : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
  have e : perturb F ρ z x - perturb F ρ z y = (F x - F y) + ρ⁻¹ • (x - y) := by
    simp only [perturb, smul_sub]; abel
  rw [e]
  calc ‖(F x - F y) + ρ⁻¹ • (x - y)‖ ≤ ‖F x - F y‖ + ‖ρ⁻¹ • (x - y)‖ := norm_add_le _ _
    _ = ‖F x - F y‖ + ρ⁻¹ * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    _ ≤ L * ‖x - y‖ + 1 * ‖x - y‖ := by
        gcongr
        exact h x hx y hy
    _ = (L + 1) * ‖x - y‖ := by ring

end Aux_MIE2

open MonoIncExtrap Aux_MIEb Aux_MIE2 in
theorem solution {n : ℕ}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))}
    {I : Alg2.Input (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hI : Alg2.Standing B I xstar) :
    ∃ LQ LQhat : ℝ, Alg2.ValidQ B I xstar LQ LQhat := by
  have hloc := hI.assumption.locally_lipschitz
  have hrho : ∀ k, 1 ≤ I.rho k := by
    intro k
    unfold Alg2.Input.rho
    exact one_le_mul_of_one_le_of_one_le hI.ρ0_ge (one_le_pow₀ hI.ζ_gt.le)
  obtain ⟨L1, hL1, h1⟩ := lip_ball B I.F hloc xstar
    ((1 / Real.sqrt (1 - 2 * I.ν ^ 2) + 1) *
      (I.rbar xstar + I.ρ0 * I.τ0 / (1 - I.σ * I.ζ)))
  obtain ⟨L2, hL2, h2⟩ := lip_ball B I.F hloc xstar
    (((5 + 9 * I.γ0 * (L1 + 1)) / (3 * Real.sqrt (1 - 2 * I.ν ^ 2)) + 1) *
      (I.rbar xstar + I.ρ0 * I.τ0 / (1 - I.σ * I.ζ)))
  refine ⟨L1 + 1, L2 + 1, by linarith, by linarith, fun k z => ⟨?_, ?_⟩⟩
  · exact perturb_lip _ _ _ _ (hrho k) z h1
  · exact perturb_lip _ _ _ _ (hrho k) z h2
