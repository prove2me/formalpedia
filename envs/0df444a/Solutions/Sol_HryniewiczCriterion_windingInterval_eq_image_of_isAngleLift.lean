-- Prove2me | solution 1 for HryniewiczCriterion.windingInterval_eq_image_of_isAngleLift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:47:05.207195+00:00
-- url     : https://prove2.me/submissions/357acb82-7611-495b-864a-05fb8b0405e5

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Theorems.Thm_FiniteEnergyPlane_exists_int_forall_mem_Ioo_of_forall_ne
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.UnitInterval

open HryniewiczCriterion

namespace HryniewiczCriterion

theorem lw_cos_sub_eq_one {r r' x y : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (h : r' • rotationVector x = r • rotationVector y) : Real.cos (x - y) = 1 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hsq : r' ^ 2 = r ^ 2 := by
    have : (r' * Real.sin x) ^ 2 + (r' * Real.cos x) ^ 2 =
        (r * Real.sin y) ^ 2 + (r * Real.cos y) ^ 2 := by
      rw [h0, h1]
    nlinarith
  have hrr : r' = r := by nlinarith
  subst hrr
  have hc : Real.cos x = Real.cos y := mul_left_cancel₀ hr.ne' h0
  have hs : Real.sin x = Real.sin y := mul_left_cancel₀ hr.ne' h1
  rw [Real.cos_sub, hc, hs]; linarith

theorem lw_int_eq_of_lt {z a : ℤ} (h1 : (a : ℝ) - 1 < z) (h2 : (z : ℝ) < a + 1) : z = a := by
  have h1' : a - 1 < z := by exact_mod_cast h1
  have h2' : z < a + 1 := by exact_mod_cast h2
  omega

/-- Two angle lifts with the same starting angle agree at `t = 1`. -/
theorem lw_isAngleLift_eq_one {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ} {θ θ' : ℝ → ℝ}
    (hθ : IsAngleLift φ s θ) (hθ' : IsAngleLift φ s θ') : θ' 1 = θ 1 := by
  have hpi := Real.pi_pos
  let f : unitInterval → ℝ := fun t => θ' t - θ t
  have hfc : Continuous f :=
    (hθ'.1.comp_continuous continuous_subtype_val (fun t => t.2)).sub
      (hθ.1.comp_continuous continuous_subtype_val (fun t => t.2))
  have hcos : ∀ t : unitInterval, Real.cos (f t) = 1 := by
    intro t
    obtain ⟨r', hr', e'⟩ := hθ'.2.2 t t.2
    obtain ⟨r, hr, e⟩ := hθ.2.2 t t.2
    exact lw_cos_sub_eq_one hr hr' (e'.symm.trans e)
  obtain ⟨m, hm⟩ := FiniteEnergyPlane.exists_int_forall_mem_Ioo_of_forall_ne f hfc Real.pi
    (2 * Real.pi) (by linarith) (by
      intro t m e
      have := hcos t
      rw [e, Real.cos_add_int_mul_two_pi, Real.cos_pi] at this
      norm_num at this)
  have hf0 : f 0 = 0 := by
    simp only [f, Set.Icc.coe_zero, hθ.2.1, hθ'.2.1, sub_self]
  have hm1 : m = -1 := by
    obtain ⟨a1, a2⟩ := hm 0
    rw [hf0] at a1 a2
    apply lw_int_eq_of_lt <;> push_cast <;> nlinarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (f 1)).1 (hcos 1)
  have hn0 : n = 0 := by
    obtain ⟨a1, a2⟩ := hm 1
    rw [← hn, hm1] at a1 a2
    push_cast at a1 a2
    apply lw_int_eq_of_lt <;> push_cast <;> nlinarith
  have : f 1 = 0 := by rw [← hn, hn0]; simp
  simpa [f, sub_eq_zero] using this

/-- If `θ s` is an angle lift of `φ` starting at `s` for every `s`, then the winding interval of
`φ` is the image of `s ↦ (θ s 1 - s) / 2π` on `[0, 2π]`. -/
theorem windingInterval_eq_image_of_isAngleLift_aux (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (θ : ℝ → ℝ → ℝ) (hθ : ∀ s, IsAngleLift φ s (θ s)) :
    windingInterval φ =
      (fun s => (θ s 1 - s) / (2 * Real.pi)) '' Set.Icc 0 (2 * Real.pi) := by
  ext d
  constructor
  · rintro ⟨s, hs, θ', hθ', rfl⟩
    exact ⟨s, hs, by simp only [lw_isAngleLift_eq_one (hθ s) hθ']⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, θ s, hθ s, rfl⟩

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution
    (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ → ℝ → ℝ) (hθ : ∀ s, IsAngleLift φ s (θ s)) :
    windingInterval φ =
      (fun s => (θ s 1 - s) / (2 * Real.pi)) '' Set.Icc 0 (2 * Real.pi) :=
  HryniewiczCriterion.windingInterval_eq_image_of_isAngleLift_aux φ θ hθ
