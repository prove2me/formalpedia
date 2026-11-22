-- Prove2me | solution 1 for KarimiPL.GD.quadUpper_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-10T21:37:45.245982+00:00
-- url     : https://prove2.me/submissions/56e796e9-6f0c-4e00-84d9-9730d0984968

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass

open scoped InnerProductSpace

set_option autoImplicit false

theorem solution {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f)
    (L : ℝ) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    ShiOptRates.QuadUpper f (gradient f) L := by
  by_cases hnt : Nontrivial (EuclideanSpace ℝ (Fin d))
  · -- Main case: the space is nontrivial, so hLip forces 0 ≤ L.
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    have hpos : 0 < ‖a - b‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hab
    have hL : 0 ≤ L := by
      rcases lt_or_ge L 0 with hneg | hge
      · exfalso
        have h1 := hLip a b
        have h2 : L * ‖a - b‖ < 0 := mul_neg_of_neg_of_pos hneg hpos
        have h3 : 0 ≤ ‖gradient f a - gradient f b‖ := norm_nonneg _
        linarith
      · exact hge
    unfold ShiOptRates.QuadUpper
    intro x y
    -- The segment curve c t = x + t • (y - x), with derivative y - x.
    have hcdiff : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      intro t
      have h2 : HasDerivAt (fun t : ℝ => t • (y - x)) (y - x) t := by
        simpa using (hasDerivAt_id' t).smul_const (y - x)
      have h3 := (hasDerivAt_const t x).add h2
      rw [show ((fun _ : ℝ => x) + (fun t : ℝ => t • (y - x))) = (fun t : ℝ => x + t • (y - x))
        from funext fun t => rfl, zero_add] at h3
      exact h3
    -- Chain rule: derivative of t ↦ f (c t) is the directional derivative.
    have hcomp : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • (y - x)))
        (fderiv ℝ f (x + t • (y - x)) (y - x)) t := by
      intro t
      have h := (hdiff (x + t • (y - x))).hasFDerivAt.comp_hasDerivAt t (hcdiff t)
      simpa [Function.comp_def] using h
    have hderiv : deriv (fun t : ℝ => f (x + t • (y - x)))
        = fun t => fderiv ℝ f (x + t • (y - x)) (y - x) := by
      funext t
      exact (hcomp t).deriv
    -- A Lipschitz gradient is continuous (ε-δ, avoiding LipschitzWith instance matching).
    have hgc : Continuous (gradient f) := by
      rw [Metric.continuous_iff]
      intro x ε hε
      refine ⟨ε / (L + 1), div_pos hε (by linarith), fun y hy => ?_⟩
      have h1 := hLip y x
      rw [dist_eq_norm] at hy ⊢
      rcases hL.eq_or_lt with rfl | hLpos
      · rw [zero_mul] at h1
        have h00 : ‖gradient f y - gradient f x‖ = 0 :=
          le_antisymm h1 (norm_nonneg _)
        rw [h00]
        exact hε
      · have hLe : L * (ε / (L + 1)) ≤ ε := by
          have h1' : (0:ℝ) < L + 1 := by linarith
          have hle : L / (L + 1) ≤ 1 := (div_le_one h1').mpr (by linarith)
          calc L * (ε / (L + 1)) = (L / (L + 1)) * ε := by ring
            _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hle (le_of_lt hε)
            _ = ε := one_mul ε
        calc ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖ := h1
          _ < L * (ε / (L + 1)) := mul_lt_mul_of_pos_left hy hLpos
          _ ≤ ε := hLe
    have hcc : Continuous fun t : ℝ => x + t • (y - x) :=
      continuous_const.add (continuous_id'.smul continuous_const)
    have hgi : Continuous fun t : ℝ => ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ :=
      (hgc.comp hcc).inner continuous_const
    have hcont : Continuous fun t : ℝ => fderiv ℝ f (x + t • (y - x)) (y - x) := by
      have e : (fun t : ℝ => fderiv ℝ f (x + t • (y - x)) (y - x))
          = fun t : ℝ => ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ := by
        funext t
        rw [← inner_gradient_left]
      rw [e]
      exact hgi
    -- FTC along the segment: f y - f x = ∫₀¹ ⟪∇f(c t), y - x⟫ dt.
    have hftc : ∫ t in (0:ℝ)..1, fderiv ℝ f (x + t • (y - x)) (y - x) = f y - f x := by
      have h := intervalIntegral.integral_deriv_eq_sub' (a := (0:ℝ)) (b := (1:ℝ)) _ hderiv
        (fun t _ => (hcomp t).differentiableAt) hcont.continuousOn
      simpa using h
    have hftc' : ∫ t in (0:ℝ)..1, ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ
        = f y - f x := by
      have e : (fun t : ℝ => ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ)
          = fun t => fderiv ℝ f (x + t • (y - x)) (y - x) := by
        funext t
        rw [inner_gradient_left]
      rw [e]
      exact hftc
    -- Pointwise bound on [0,1] via Cauchy–Schwarz and Lipschitz.
    have hbound : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ - ⟪gradient f x, y - x⟫_ℝ
          ≤ L * t * ‖y - x‖ ^ 2 := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have hnorm : ‖(x + t • (y - x)) - x‖ = t * ‖y - x‖ := by
        have e2 : (x + t • (y - x)) - x = t • (y - x) :=
          add_sub_cancel_left x (t • (y - x))
        rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have h2 : ‖gradient f (x + t • (y - x)) - gradient f x‖ ≤ L * (t * ‖y - x‖) := by
        have h1 := hLip (x + t • (y - x)) x
        rw [hnorm] at h1
        exact h1
      have hcs : ⟪gradient f (x + t • (y - x)) - gradient f x, y - x⟫_ℝ
          = ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ - ⟪gradient f x, y - x⟫_ℝ :=
        inner_sub_left _ _ _
      rw [← hcs]
      calc ⟪gradient f (x + t • (y - x)) - gradient f x, y - x⟫_ℝ
            ≤ ‖gradient f (x + t • (y - x)) - gradient f x‖ * ‖y - x‖ :=
            real_inner_le_norm _ _
        _ ≤ (L * (t * ‖y - x‖)) * ‖y - x‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = L * t * ‖y - x‖ ^ 2 := by ring
    -- Integrability of everything in sight.
    have hint0 : IntervalIntegrable (fun t : ℝ => ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ)
        MeasureTheory.volume 0 1 :=
      hgi.continuousOn.intervalIntegrable
    have hint1 : IntervalIntegrable
        (fun t : ℝ => ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ - ⟪gradient f x, y - x⟫_ℝ)
        MeasureTheory.volume 0 1 :=
      (hgi.sub continuous_const).continuousOn.intervalIntegrable
    have hint2 : IntervalIntegrable (fun _ : ℝ => ⟪gradient f x, y - x⟫_ℝ)
        MeasureTheory.volume 0 1 :=
      continuous_const.continuousOn.intervalIntegrable
    have hint3 : IntervalIntegrable (fun t : ℝ => L * t * ‖y - x‖ ^ 2)
        MeasureTheory.volume 0 1 :=
      ((continuous_const.mul continuous_id').mul continuous_const).continuousOn.intervalIntegrable
    -- f y - f x - ⟪∇f x, y - x⟫ is the integral of the difference.
    have hdiff_eq : f y - f x - ⟪gradient f x, y - x⟫_ℝ
        = ∫ t in (0:ℝ)..1,
            (⟪gradient f (x + t • (y - x)), y - x⟫_ℝ - ⟪gradient f x, y - x⟫_ℝ) := by
      have hsub := intervalIntegral.integral_sub hint0 hint2
      have hc : ∫ _t in (0:ℝ)..1, ⟪gradient f x, y - x⟫_ℝ = ⟪gradient f x, y - x⟫_ℝ := by
        rw [intervalIntegral.integral_const]
        simp
      rw [hsub, hftc', hc]
    -- Monotonicity of the integral + closed form ∫₀¹ L t ‖y-x‖² dt = L/2 ‖y-x‖².
    have hle : ∫ t in (0:ℝ)..1,
          (⟪gradient f (x + t • (y - x)), y - x⟫_ℝ - ⟪gradient f x, y - x⟫_ℝ)
        ≤ ∫ t in (0:ℝ)..1, L * t * ‖y - x‖ ^ 2 :=
      intervalIntegral.integral_mono_on zero_le_one hint1 hint3 hbound
    have hrhs : ∫ t in (0:ℝ)..1, L * t * ‖y - x‖ ^ 2 = L / 2 * ‖y - x‖ ^ 2 := by
      have e : (fun t : ℝ => L * t * ‖y - x‖ ^ 2) = fun t => (L * ‖y - x‖ ^ 2) * t := by
        funext t
        ring
      rw [e, intervalIntegral.integral_const_mul, integral_id]
      ring
    have hstep := hle.trans hrhs.le
    rw [← hdiff_eq] at hstep
    linarith
  · -- Degenerate case d = 0: the space is a subsingleton, so x = y and both sides agree.
    rw [not_nontrivial_iff_subsingleton] at hnt
    unfold ShiOptRates.QuadUpper
    intro x y
    have hxy : x = y := hnt.elim x y
    subst hxy
    simp
