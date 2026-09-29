-- Prove2me | solution 1 for ModularForm.continuous_logEta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/57f75580-4096-5738-a511-77685a660435

import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_continuous_logEta

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

lemma norm_eta_q (n : ℕ) (z : ℂ) : ‖ModularForm.eta_q n z‖ = Real.exp (-(2 * π * (n + 1) * z.im)) := by
  rw [ModularForm.eta_q_eq_cexp, norm_exp]
  congr 1
  simp [mul_re, mul_im]

lemma norm_eta_q_lt_one (n : ℕ) {z : ℂ} (hz : 0 < z.im) : ‖ModularForm.eta_q n z‖ < 1 := by
  rw [norm_eta_q, Real.exp_lt_one_iff]
  have : 0 < 2 * π * (n + 1) * z.im := by positivity
  linarith

lemma one_sub_eta_q_mem_slitPlane (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    1 - ModularForm.eta_q n z ∈ slitPlane := by
  rw [sub_eq_add_neg]
  exact mem_slitPlane_of_norm_lt_one (by rw [norm_neg]; exact norm_eta_q_lt_one n hz)

lemma summable_log (z : ℍ) : Summable fun n : ℕ => log (1 - ModularForm.eta_q n z) := by
  have h := Complex.summable_log_one_add_of_summable (Summable.of_norm (ModularForm.summable_eta_q z))
  simpa [sub_eq_add_neg] using h

lemma continuousOn_logEta {δ : ℝ} (hδ : 0 < δ) : ContinuousOn logEta {z : ℂ | δ < z.im} := by
  have hlin : Continuous fun z : ℂ => π * I * z / 12 := by fun_prop
  refine hlin.continuousOn.add ?_
  set r : ℝ := Real.exp (-(2 * π * δ)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith

  have hq : ∀ (n : ℕ) (z : ℂ), δ < z.im → ‖ModularForm.eta_q n z‖ ≤ r ^ (n + 1) := by
    intro n z hz
    rw [norm_eta_q, hr, ← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    have : 0 < 2 * π * (n + 1) := by positivity
    nlinarith
  set C : ℝ := r * (1 - r)⁻¹ / 2 + 1 with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ (1 - r)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  refine continuousOn_tsum (u := fun n : ℕ => C * r ^ (n + 1)) (fun n => ?_) ?_ ?_
  ·
    have h1 : ContinuousOn (fun z : ℂ => 1 - ModularForm.eta_q n z) {z : ℂ | δ < z.im} := by
      apply Continuous.continuousOn
      simp only [ModularForm.eta_q_eq_cexp]
      fun_prop
    exact h1.clog fun z hz => one_sub_eta_q_mem_slitPlane n (hδ.trans hz)
  · exact (summable_geometric_of_lt_one hr0.le hr1).mul_left C |>.comp_injective (add_left_injective 1)
      |>.congr fun n => by simp [Function.comp, pow_succ]
  · intro n z hz
    have hx1 : ‖ModularForm.eta_q n z‖ < 1 := norm_eta_q_lt_one n (hδ.trans hz)
    have hxr : ‖ModularForm.eta_q n z‖ ≤ r := by
      refine (hq n z hz).trans ?_
      calc r ^ (n + 1) ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_add_left 1 n)
        _ = r := pow_one r
    have h := Complex.norm_log_one_add_le (z := -ModularForm.eta_q n z) (by rwa [norm_neg])
    rw [norm_neg, ← sub_eq_add_neg] at h
    refine h.trans ?_
    set x := ‖ModularForm.eta_q n z‖ with hx
    have hx0 : 0 ≤ x := norm_nonneg _
    have h1r : 0 < 1 - r := by linarith
    have hinv : (1 - x)⁻¹ ≤ (1 - r)⁻¹ := inv_anti₀ h1r (by linarith)
    calc x ^ 2 * (1 - x)⁻¹ / 2 + x ≤ x * r * (1 - r)⁻¹ / 2 + x := by
          have : x ^ 2 * (1 - x)⁻¹ ≤ x * r * (1 - r)⁻¹ := by
            rw [sq]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hxr hx0) hinv (inv_nonneg.2 (by linarith))
              (by positivity)
          linarith
      _ = C * x := by rw [hC]; ring
      _ ≤ C * r ^ (n + 1) := mul_le_mul_of_nonneg_left (hq n z hz) hC0

theorem continuous_logEta : Continuous fun τ : ℍ => logEta τ := by
  refine continuous_iff_continuousAt.2 fun τ => ?_
  have hδ : 0 < τ.im / 2 := half_pos τ.im_pos
  have hopen : IsOpen {z : ℂ | τ.im / 2 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hmem : (τ : ℂ) ∈ {z : ℂ | τ.im / 2 < z.im} := by
    show τ.im / 2 < (τ : ℂ).im
    rw [UpperHalfPlane.coe_im]; linarith [τ.im_pos]
  exact ((continuousOn_logEta hδ).continuousAt (hopen.mem_nhds hmem)).comp
    UpperHalfPlane.continuous_coe.continuousAt

end DedekindEtaLog

end

theorem solution : Continuous fun τ : UpperHalfPlane => (Real.pi * Complex.I * (τ : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (τ : ℂ))) :=
  DedekindEtaLog.continuous_logEta

end S_ModularForm_continuous_logEta
end P2MW
export P2MW.S_ModularForm_continuous_logEta (solution)
