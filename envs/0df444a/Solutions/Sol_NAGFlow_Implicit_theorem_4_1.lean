-- Prove2me | solution 1 for NAGFlow.Implicit.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:32:55.401675+00:00
-- url     : https://prove2.me/submissions/ed4af410-8079-4223-accb-662b0296e984

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

namespace RRAux_NAGFlow_Implicit_theorem_4_1

-- scalar core of the Lyapunov step
lemma key (a g g' μ F F' fs ip iq pq nq np nd qd : ℝ)
    (hg : 0 < g) (ha : 0 < a) (hμ : 0 ≤ μ) (hg' : (1 + a) * g' = g + a * μ)
    (C1 : F - F' - a * ip ≥ 0)
    (C2 : fs - F' + (ip + iq) ≥ μ / 2 * (np + 2 * pq + nq))
    (hd : g * qd = a * μ * pq - a * iq)
    (hnp : 0 ≤ np) (hnd : 0 ≤ nd) :
    F' - fs + g' / 2 * nq ≤ (F - fs + g / 2 * (nq - 2 * qd + nd)) / (1 + a) := by
  rw [le_div_iff₀ (by linarith)]
  have h1 := mul_le_mul_of_nonneg_left C2 ha.le
  have h2 := mul_nonneg (mul_nonneg ha.le hμ) hnp
  have h3 := mul_nonneg hg.le hnd
  have h4 : (1 + a) * g' * nq = (g + a * μ) * nq := by rw [hg']
  nlinarith

lemma gamma_pos {α γ : ℕ → ℝ} {μ : ℝ} (hμ : 0 ≤ μ) (h0 : 0 < γ 0) (ha : ∀ k, 0 < α k)
    (heq : ∀ k, (γ (k + 1) - γ k) / α k = μ - γ (k + 1)) : ∀ k, 0 < γ k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hak := ha k
    have h := heq k
    rw [div_eq_iff hak.ne'] at h
    nlinarith

end RRAux_NAGFlow_Implicit_theorem_4_1

open NAGFlow.Implicit in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V → ℝ) (gradf : V → V) (μ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (x v : ℕ → V) (hrun : IsImplicitRun gradf μ α γ x v) :
    ∀ k : ℕ, lyap f xstar x v γ (k + 1) ≤ lyap f xstar x v γ k / (1 + α k) := by
  have hγ : ∀ k, 0 < γ k := RRAux_NAGFlow_Implicit_theorem_4_1.gamma_pos hf.mu_nonneg
    hrun.gamma0_pos (fun k => (hrun.step k).alpha_pos) (fun k => (hrun.step k).gamma_eq)
  intro k
  obtain ⟨ha, hxe, hve, hge⟩ := hrun.step k
  have hg := hγ k
  set a := α k
  set g := γ k
  set g' := γ (k + 1)
  set x' := x (k + 1)
  set v' := v (k + 1)
  set x0 := x k
  set v0 := v k
  set G := gradf x'
  have hg' : (1 + a) * g' = g + a * μ := by
    rw [div_eq_iff ha.ne'] at hge; linarith
  -- vector forms
  have hx : x0 - x' = a • (x' - v') := by
    have := congrArg (fun w => a • w) hxe
    simp only [smul_smul, mul_one_div_cancel ha.ne', one_smul] at this
    rw [← neg_sub x' x0, this, ← smul_neg, neg_sub]
  have hv : g • (v' - v0) = (a * μ) • (x' - v') - a • G := by
    have := congrArg (fun w => (a * g) • w) hve
    simp only [smul_sub, smul_smul] at this
    have e1 : a * g * (1 / a) = g := by field_simp
    have e2 : a * g * (μ / g) = a * μ := by field_simp
    have e3 : a * g * (1 / g) = a := by field_simp
    rw [e1, e2, e3] at this
    simp only [smul_sub]; exact this
  set p := x' - v'
  set q := v' - xstar
  set d := v' - v0
  have hvq : v0 - xstar = q - d := by simp only [q, d]; abel
  have hxq : xstar - x' = -(p + q) := by simp only [p, q]; abel
  have C1 := hf.mu_convex x0 x'
  have C2 := hf.mu_convex xstar x'
  rw [hx, real_inner_smul_right] at C1
  rw [hxq, inner_neg_right, inner_add_right, norm_neg, norm_add_sq_real] at C2
  have hd : g * inner ℝ q d = a * μ * inner ℝ p q - a * inner ℝ G q := by
    have := congrArg (fun w => inner ℝ w q) hv
    simp only [inner_sub_left, real_inner_smul_left] at this
    rw [← real_inner_comm q d]; exact this
  have C1' : f x0 - f x' - a * inner ℝ G p ≥ 0 := by
    have := mul_nonneg (div_nonneg hf.mu_nonneg (by norm_num : (0:ℝ) ≤ 2))
      (sq_nonneg ‖a • p‖)
    linarith
  show f x' - f xstar + g' / 2 * ‖q‖ ^ 2 ≤ (f x0 - f xstar + g / 2 * ‖v0 - xstar‖ ^ 2) / (1 + a)
  rw [hvq, norm_sub_sq_real q d]
  exact RRAux_NAGFlow_Implicit_theorem_4_1.key a g g' μ (f x0) (f x') (f xstar)
    (inner ℝ G p) (inner ℝ G q) (inner ℝ p q) (‖q‖ ^ 2) (‖p‖ ^ 2) (‖d‖ ^ 2) (inner ℝ q d)
    hg ha hf.mu_nonneg hg' C1' (by linarith) hd (sq_nonneg _) (sq_nonneg _)

#print axioms solution
