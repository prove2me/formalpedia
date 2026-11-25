-- Prove2me | solution 1 for GlobalTheory.mem_periodLattice_of_theta_translate_eq_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:59.748386+00:00
-- url     : https://prove2.me/submissions/02ec8683-00f9-4cfb-b1d5-8e7e5fc4cf88

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
import Theorems.Thm_GlobalTheory_entire_eq_of_mul_eq_mul_right
import Theorems.Thm_GlobalTheory_entire_eq_exp_linear_of_multiplier
import Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (w : Fin g → ℂ) (h : (Fin g → ℂ) → ℂ), Differentiable ℂ h → (∀ z, h z ≠ 0) → (∀ z, theta 0 0 (z + w) τ = h z * theta 0 0 z τ) → w ∈ periodLattice τ) := by
  intro H1 H2 g τ hτ w h hd h0 hrel
  obtain ⟨⟨hθd, hqp⟩, hθ0⟩ := H1 g τ hτ
  obtain ⟨-, hspan, -⟩ := H2 g τ hτ
  have hmult : ∀ n n' : Fin g → ℤ, ∀ z, h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) =
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z := by
    intro n n'
    set A : (Fin g → ℂ) → ℂ := fun z =>
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) with hA
    have hAne : ∀ z, A z ≠ 0 := fun z => by
      simp only [hA, eC]
      exact Complex.exp_ne_zero _
    have hAw : ∀ z, A (z + w) = A z * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
      intro z
      simp only [hA]
      rw [← eC_add, dotProduct_add]
      congr 1
      ring
    have hAc : Continuous A := by
      simp only [hA, eC]
      exact Complex.continuous_exp.comp (continuous_const.mul (continuous_const.mul
        (continuous_const.add (continuous_const.dotProduct continuous_id))))
    have hne : (fun z => A z * theta 0 0 z τ) ≠ 0 := by
      intro hz
      apply hθ0
      funext z
      have := congrFun hz z
      simp only [Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left (hAne z)
    have hEq : ∀ z, h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) * (A z * theta 0 0 z τ) =
        eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z * (A z * theta 0 0 z τ) := by
      intro z
      have e2 : theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n')) τ = A z * theta 0 0 z τ := by
        rw [← add_assoc]
        exact hqp n n' z
      have e3 : theta 0 0 (z + w + (τ *ᵥ ofIntVec n + ofIntVec n')) τ =
          A (z + w) * theta 0 0 (z + w) τ := by
        rw [← add_assoc]
        exact hqp n n' (z + w)
      calc h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) * (A z * theta 0 0 z τ)
          = h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) *
              theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n')) τ := by rw [e2]
        _ = theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n') + w) τ := (hrel _).symm
        _ = theta 0 0 (z + w + (τ *ᵥ ofIntVec n + ofIntVec n')) τ := by rw [add_right_comm]
        _ = A (z + w) * theta 0 0 (z + w) τ := e3
        _ = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z * (A z * theta 0 0 z τ) := by
          rw [hAw, hrel]
          ring
    intro z
    exact congrFun (entire_eq_of_mul_eq_mul_right
      (f₁ := fun z => h (z + (τ *ᵥ ofIntVec n + ofIntVec n')))
      (f₂ := fun z => eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z)
      (hd.comp (differentiable_id.add_const _)) ((differentiable_const _).mul hd)
      (hAc.mul hθd.continuous) hne hEq) z
  have hS : ∀ s ∈ (periodLattice τ : Set (Fin g → ℂ)), ∃ c : ℂ, ∀ z, h (z + s) = c * h z := by
    rintro s ⟨n, n', rfl⟩
    exact ⟨_, hmult n n'⟩
  obtain ⟨L, hL⟩ := entire_eq_exp_linear_of_multiplier hd h0 hspan hS
  have hexp : ∀ n n' : Fin g → ℤ, Complex.exp (L (τ *ᵥ ofIntVec n + ofIntVec n')) =
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
    intro n n'
    have e := hmult n n' 0
    rw [zero_add] at e
    have e' : h 0 * Complex.exp (L (τ *ᵥ ofIntVec n + ofIntVec n')) =
        h 0 * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
      rw [← hL, e, mul_comm]
    exact mul_left_cancel₀ (h0 0) e'
  have hk : ∀ j : Fin g, ∃ m : ℤ, L (Pi.single j 1) = m * (2 * Real.pi * Complex.I) := by
    intro j
    have e := hexp 0 (Pi.single j 1)
    have hv : τ *ᵥ ofIntVec (0 : Fin g → ℤ) + ofIntVec (Pi.single j 1) = Pi.single j 1 := by
      rw [ofIntVec_zero, mulVec_zero, zero_add]
      ext i
      by_cases hij : i = j
      · subst hij
        simp [ofIntVec]
      · simp [ofIntVec, hij]
    rw [hv, ofIntVec_zero, zero_dotProduct, mul_zero, eC_zero] at e
    exact Complex.exp_eq_one_iff.mp e
  choose k hk using hk
  have hLz : ∀ z, L z = 2 * Real.pi * Complex.I * (ofIntVec k ⬝ᵥ z) := by
    intro z
    calc L z = L (∑ i, Pi.single i (z i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i, z i * L (Pi.single i 1) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hsi : (Pi.single i (z i) : Fin g → ℂ) = z i • (Pi.single i 1 : Fin g → ℂ) := by
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [hj]
        rw [hsi, map_smul, smul_eq_mul]
      _ = 2 * Real.pi * Complex.I * (ofIntVec k ⬝ᵥ z) := by
        simp only [hk, dotProduct, ofIntVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
  have hm : ∀ j : Fin g, ∃ m : ℤ, w j + (τ *ᵥ ofIntVec k) j = m := by
    intro j
    have e := hexp (Pi.single j 1) 0
    rw [ofIntVec_zero, add_zero, hLz] at e
    have hdot1 : ofIntVec (Pi.single j 1) ⬝ᵥ w = w j := by
      simp [ofIntVec, dotProduct, Pi.single_apply]
    have hdot2 : ofIntVec k ⬝ᵥ (τ *ᵥ ofIntVec (Pi.single j 1)) = (τ *ᵥ ofIntVec k) j := by
      rw [dot_mulVec_symm hτ.1]
      simp [ofIntVec, dotProduct, Pi.single_apply]
    rw [hdot1, hdot2] at e
    unfold eC at e
    have e2 : Complex.exp (2 * Real.pi * Complex.I * (w j + (τ *ᵥ ofIntVec k) j)) = 1 := by
      rw [mul_add, Complex.exp_add, e, ← Complex.exp_add,
        show 2 * (Real.pi : ℂ) * Complex.I * w j + 2 * Real.pi * Complex.I * (-(1 : ℂ) * w j) = 0 by
          ring, Complex.exp_zero]
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp e2
    exact ⟨m, mul_left_cancel₀ Complex.two_pi_I_ne_zero (by rw [hm]; ring)⟩
  choose m hm using hm
  show ∃ n n' : Fin g → ℤ, w = τ *ᵥ ofIntVec n + ofIntVec n'
  refine ⟨-k, m, ?_⟩
  ext j
  have hj := hm j
  rw [ofIntVec_neg, mulVec_neg, Pi.add_apply, Pi.neg_apply]
  simp only [ofIntVec] at hj ⊢
  linear_combination hj
end GlobalTheory
