-- Prove2me | solution 1 for InertialAVD.StrongCvx.thm_3_4_first_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:21:07.403196+00:00
-- url     : https://prove2.me/submissions/038e8d1f-09ce-4d0b-b912-2594ad4ef853

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting

set_option autoImplicit false
open InnerProductSpace Filter Topology Asymptotics
open InertialAVD.StrongCvx

theorem avd_deriv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (α t₀ : ℝ) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (lam p : ℝ) (t : ℝ) (ht : t ∈ Set.Ici t₀) :
    HasDerivWithinAt (energyP Φ x v xstar lam p)
      ((p + 2) * t ^ (p + 1) * (Φ (x t) - Φ xstar)
        - lam * t ^ (p + 1) * ⟪x t - xstar, gradient Φ (x t)⟫_ℝ
        - lam * (α - lam - 1 - p) * t ^ p * ⟪x t - xstar, v t⟫_ℝ
        + lam ^ 2 * p / 2 * t ^ (p - 1) * ‖x t - xstar‖ ^ 2
        - (α - lam - 1 - p / 2) * t ^ (p + 1) * ‖v t‖ ^ 2) (Set.Ici t₀) t := by
  obtain ⟨ht0, hs⟩ := hsol
  have htp : 0 < t := lt_of_lt_of_le ht0 ht
  obtain ⟨hx, hv⟩ := hs t ht
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (x t)) (x t) :=
    ((hΦ.differentiable one_ne_zero) (x t)).hasFDerivAt
  have hgrad : ∀ h : H, ⟪gradient Φ (x t), h⟫_ℝ = fderiv ℝ Φ (x t) h := by
    intro h
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hΦx : HasDerivWithinAt (fun s => Φ (x s)) (⟪gradient Φ (x t), v t⟫_ℝ) (Set.Ici t₀) t := by
    rw [hgrad]
    exact hΦd.comp_hasDerivWithinAt t hx
  have hid : HasDerivWithinAt (fun s : ℝ => s) 1 (Set.Ici t₀) t := hasDerivWithinAt_id t _
  have hlx : HasDerivWithinAt (fun s => lam • (x s - xstar)) (lam • v t) (Set.Ici t₀) t := by
    have := (hx.sub_const xstar).const_smul lam
    exact this
  have htv : HasDerivWithinAt (fun s => s • v s)
      (t • (-(α / t) • v t - gradient Φ (x t)) + (1 : ℝ) • v t) (Set.Ici t₀) t :=
    hid.smul hv
  have hw : HasDerivWithinAt (fun s => lam • (x s - xstar) + s • v s)
      (lam • v t + (t • (-(α / t) • v t - gradient Φ (x t)) + (1 : ℝ) • v t)) (Set.Ici t₀) t :=
    hlx.add htv
  have hn := hw.norm_sq
  have hsq : HasDerivWithinAt (fun s : ℝ => s ^ 2) (2 * t) (Set.Ici t₀) t := by
    have := (hasDerivAt_pow 2 t).hasDerivWithinAt (s := Set.Ici t₀)
    simpa using this
  have hΦm : HasDerivWithinAt (fun s => Φ (x s) - Φ xstar) (⟪gradient Φ (x t), v t⟫_ℝ) (Set.Ici t₀) t :=
    hΦx.sub_const _
  have hE0 := (hsq.mul hΦm).add (hn.const_mul (1 / 2))
  have hpow : HasDerivWithinAt (fun s : ℝ => s ^ p) (p * t ^ (p - 1)) (Set.Ici t₀) t :=
    (Real.hasDerivAt_rpow_const (Or.inl htp.ne')).hasDerivWithinAt
  have hE := hpow.mul hE0
  have hfun : energyP Φ x v xstar lam p = fun s => s ^ p * (s ^ 2 * (Φ (x s) - Φ xstar)
      + 1 / 2 * ‖lam • (x s - xstar) + s • v s‖ ^ 2) := by
    funext s
    simp [energyP, energy]
  rw [hfun]
  refine hE.congr_deriv ?_
  set a := x t - xstar with ha
  set g := gradient Φ (x t) with hg
  have hvv : ⟪v t, v t⟫_ℝ = ‖v t‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hn1 : ‖lam • a + t • v t‖ ^ 2 = lam ^ 2 * ‖a‖ ^ 2 + 2 * lam * t * ⟪a, v t⟫_ℝ + t ^ 2 * ‖v t‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, mul_pow, mul_pow,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    simp
    ring
  have hn2 : ⟪lam • a + t • v t, lam • v t + (t • (-(α / t) • v t - g) + (1 : ℝ) • v t)⟫_ℝ
      = lam * (lam + 1 - α) * ⟪a, v t⟫_ℝ - lam * t * ⟪a, g⟫_ℝ + t * (lam + 1 - α) * ‖v t‖ ^ 2
        - t ^ 2 * ⟪v t, g⟫_ℝ := by
    have htne : t ≠ 0 := htp.ne'
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_sub_right,
      inner_neg_right, hvv, one_smul, smul_sub, smul_smul, RCLike.conj_to_real]
    rw [real_inner_comm (v t) a]
    field_simp
    ring
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [hn1, hn2]
  have hp1 : t ^ (p + 1) = t ^ p * t := Real.rpow_add_one htp.ne' p
  have hp2 : t ^ (p - 1) = t ^ p / t := Real.rpow_sub_one htp.ne' p
  rw [hp1, hp2, real_inner_comm g (v t)]
  field_simp
  ring

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 0 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) (lam p : ℝ) (hlam : 0 ≤ lam) (hp : 0 ≤ p) :
    ∀ t ∈ Set.Ici t₀, ∀ D : ℝ,
      HasDerivWithinAt (energyP Φ x v xstar lam p) D (Set.Ici t₀) t →
      D ≤ (p + 2 - lam) * t ^ (p + 1) * (Φ (x t) - Φ xstar)
          - lam * (α - lam - 1 - p) * t ^ p * ⟪x t - xstar, v t⟫_ℝ
          - lam / 2 * (μ * t ^ 2 - p * lam) * t ^ (p - 1) * ‖x t - xstar‖ ^ 2
          - (α - lam - 1 - p / 2) * t ^ (p + 1) * ‖v t‖ ^ 2 := by
  intro t ht D hD
  have h := avd_deriv Φ hΦ α t₀ x v hsol xstar lam p t ht
  have hDe := UniqueDiffWithinAt.eq_deriv (Set.Ici t₀) (uniqueDiffOn_Ici t₀ t ht) hD h
  rw [hDe]
  have htp : 0 < t := lt_of_lt_of_le hsol.1 ht
  have hsc' := hsc.2 (x t) xstar
  have hB : Φ (x t) - Φ xstar + μ / 2 * ‖x t - xstar‖ ^ 2 ≤ ⟪x t - xstar, gradient Φ (x t)⟫_ℝ := by
    have e : ⟪gradient Φ (x t), xstar - x t⟫_ℝ = - ⟪x t - xstar, gradient Φ (x t)⟫_ℝ := by
      rw [← inner_neg_left, neg_sub, real_inner_comm]
    rw [e] at hsc'
    linarith
  have key : t ^ (p + 1) = t ^ 2 * t ^ (p - 1) := by
    rw [Real.rpow_add_one htp.ne' p, Real.rpow_sub_one htp.ne' p]
    field_simp
  have hT : 0 < t ^ (p + 1) := Real.rpow_pos_of_pos htp _
  have hprod : 0 ≤ lam * t ^ (p + 1) * (⟪x t - xstar, gradient Φ (x t)⟫_ℝ - (Φ (x t) - Φ xstar)
      - μ / 2 * ‖x t - xstar‖ ^ 2) :=
    mul_nonneg (mul_nonneg hlam hT.le) (by linarith)
  rw [key] at hprod ⊢
  linarith [hprod]
