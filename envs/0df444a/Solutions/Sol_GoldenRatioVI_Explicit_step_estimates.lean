-- Prove2me | solution 1 for GoldenRatioVI.Explicit.step_estimates
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:15:45.070196+00:00
-- url     : https://prove2.me/submissions/e3937668-b17b-4b1f-b18f-1d5722cb24ec

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Definitions.Def_GoldenRatioVI_Explicit_viProblem
import Definitions.Def_GoldenRatioVI_Explicit_egraalRun

open scoped RealInnerProductSpace
namespace GoldenRatioVI.Explicit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem run_pos (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta) :
    ∀ k, 0 < lam k ∧ 0 < theta k := by
  have hp : 0 < ϕ := by linarith [h.one_lt_phi]
  have hr : 0 < rho ϕ := by dsimp [rho]; positivity
  intro k
  induction k with
  | zero => exact ⟨h.lam_zero_pos, by rw [h.theta_zero]; norm_num⟩
  | succ k ih =>
    have hlk : 0 < lam k := ih.1
    have htk : 0 < theta k := ih.2
    have hl : 0 < lam (k+1) := by
      by_cases hf : F (z (k+1)) = F (z k)
      · rw [h.step_of_eq k hf]; exact lt_min (mul_pos hr ih.1) h.lamBar_pos
      · have hz : z (k+1)-z k ≠ 0 := by intro he; exact hf (congrArg F (sub_eq_zero.mp he))
        have hFn : F (z (k+1))-F (z k) ≠ 0 := sub_ne_zero.mpr hf
        rw [h.step_of_ne k hf]
        exact lt_min (lt_min (mul_pos hr ih.1)
          (mul_pos (div_pos (mul_pos hp ih.2) (by positivity))
            (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hz))
              (sq_pos_of_pos (norm_pos_iff.mpr hFn))))) h.lamBar_pos
    exact ⟨hl, by rw [h.theta_succ]; exact mul_pos (div_pos hl ih.1) hp⟩

private theorem run_estimates (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (h : IsEGRAALRun g F ϕ lamBar z zbar lam theta) (k : ℕ) :
    theta (k+1) ≤ 1+1/ϕ ∧
      4*(lam (k+1))^2*‖F (z (k+1))-F (z k)‖^2 ≤
        theta (k+1)*theta k*‖z (k+1)-z k‖^2 := by
  have hp : 0 < ϕ := by linarith [h.one_lt_phi]
  have hpos := run_pos g F ϕ lamBar z zbar lam theta h
  have hlk : 0 < lam k := (hpos k).1
  have hln : 0 < lam (k+1) := (hpos (k+1)).1
  have htk : 0 < theta k := (hpos k).2
  have htn : 0 < theta (k+1) := (hpos (k+1)).2
  have hl : lam (k+1) ≤ rho ϕ*lam k := by
    by_cases hf : F (z (k+1)) = F (z k)
    · rw [h.step_of_eq k hf]; exact min_le_left _ _
    · rw [h.step_of_ne k hf]; exact (min_le_left _ _).trans (min_le_left _ _)
  constructor
  · rw [h.theta_succ]
    have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ (hpos k).1).mpr hl) hp.le
    convert! hh using 1 <;> try dsimp [rho]
    all_goals try field_simp
    all_goals first | rfl | ring
  · by_cases hf : F (z (k+1)) = F (z k)
    · simp only [hf, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero]
      positivity
    · have hFn : 0 < ‖F (z (k+1))-F (z k)‖^2 :=
        sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hf))
      have hmid : lam (k+1) ≤ ϕ*theta k/(4*lam k) *
          (‖z (k+1)-z k‖^2/‖F (z (k+1))-F (z k)‖^2) := by
        rw [h.step_of_ne k hf]; exact (min_le_left _ _).trans (min_le_right _ _)
      have hh := mul_le_mul_of_nonneg_right hmid (show 0 ≤ 4*lam (k+1)*‖F (z (k+1))-F (z k)‖^2 by positivity)
      rw [h.theta_succ]
      convert! hh using 1 <;>
        try field_simp [hlk.ne', norm_ne_zero_iff.mpr (sub_ne_zero.mpr hf)]
      all_goals first | rfl | ring

end GoldenRatioVI.Explicit
open GoldenRatioVI.Explicit

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hrun : IsEGRAALRun g F ϕ lamBar z zbar lam theta) (k : ℕ) (hk : 1 ≤ k) :
    lam k ≤ lam (k-1)*(1/ϕ+1/ϕ^2) ∧ theta k ≤ 1+1/ϕ ∧
    lam k^2*‖F (z k)-F (z (k-1))‖^2 ≤ theta k*theta (k-1)/4*‖z k-z (k-1)‖^2 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]
  have hh := run_estimates g F ϕ lamBar z zbar lam theta hrun t
  refine ⟨?_,hh.1,?_⟩
  · have hl : lam (t+1) ≤ rho ϕ*lam t := by
      by_cases hf : F (z (t+1))=F (z t)
      · rw [hrun.step_of_eq t hf];exact min_le_left _ _
      · rw [hrun.step_of_ne t hf];exact (min_le_left _ _).trans (min_le_left _ _)
    simpa only [rho,mul_comm] using hl
  · nlinarith [hh.2]
