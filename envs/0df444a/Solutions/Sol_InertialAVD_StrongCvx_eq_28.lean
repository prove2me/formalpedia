-- Prove2me | solution 1 for InertialAVD.StrongCvx.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:33:52.151289+00:00
-- url     : https://prove2.me/submissions/d8982b35-1a3e-41ad-a7c5-45e2327722e8

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

theorem avd_first {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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

theorem avd_params (α : ℝ) (hα : 3 < α) :
    0 < pExp α ∧ 0 < lam α ∧ pExp α + 2 - lam α = 0 ∧ α - lam α - 1 - pExp α / 2 = 0 ∧
      α - lam α - 1 - pExp α = - pExp α / 2 := by
  unfold pExp lam
  refine ⟨by linarith, by linarith, by ring, by ring, by ring⟩

theorem avd_t1 (t₀ α μ : ℝ) (hα : 3 < α) (hμ : 0 < μ) (ht0 : 0 < t₀) (t : ℝ) (ht : t1 t₀ α μ ≤ t) :
    t₀ ≤ t ∧ 0 < t ∧ pExp α * lam α ≤ μ * t ^ 2 := by
  obtain ⟨hp, hl, -, -, -⟩ := avd_params α hα
  have h1 : t₀ ≤ t := le_trans (le_max_left _ _) ht
  have h2 : 0 < t := lt_of_lt_of_le ht0 h1
  have h3 : Real.sqrt (pExp α * lam α / μ) ≤ t := le_trans (le_max_right _ _) ht
  have h4 : pExp α * lam α / μ ≤ t ^ 2 := by
    have := Real.sq_sqrt (show 0 ≤ pExp α * lam α / μ from by positivity)
    rw [← this]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
  refine ⟨h1, h2, ?_⟩
  rw [div_le_iff₀ hμ] at h4
  linarith

theorem avd_gradzero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) : gradient Φ xstar = 0 := by
  have h0 : fderiv ℝ Φ xstar = 0 :=
    ((isMinOn_univ_iff.mpr hmin).isLocalMin Filter.univ_mem).fderiv_eq_zero
  simp [gradient, h0]

theorem avd_dist {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ) (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y)
    (y : H) : ‖y - xstar‖ ^ 2 ≤ 2 / μ * (Φ y - Φ xstar) := by
  have h := hsc.2 xstar y
  rw [avd_gradzero Φ xstar hmin] at h
  simp only [inner_zero_left, add_zero] at h
  have hμ := hsc.1
  have : ‖xstar - y‖ = ‖y - xstar‖ := norm_sub_rev _ _
  rw [this] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  nlinarith

theorem avd_E_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) (t : ℝ) (ht : t1 t₀ α μ ≤ t) :
    energyP Φ x v xstar (lam α) (pExp α) t
      ≤ energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ)
        + lam α * pExp α / 4 * t ^ pExp α * ‖x t - xstar‖ ^ 2 := by
  obtain ⟨hp, hl, e1, e2, e3⟩ := avd_params α hα
  have hμ := hsc.1
  have ht0 := hsol.1
  set c : ℝ := lam α * pExp α / 4 with hc
  have hc0 : 0 ≤ c := by positivity
  -- Ψ
  set Ψ : ℝ → ℝ := fun s => energyP Φ x v xstar (lam α) (pExp α) s
      - c * (s ^ pExp α * ‖x s - xstar‖ ^ 2) with hΨ
  have hderiv : ∀ s ∈ Set.Ici t₀, HasDerivWithinAt Ψ
      (((pExp α + 2) * s ^ (pExp α + 1) * (Φ (x s) - Φ xstar)
        - lam α * s ^ (pExp α + 1) * ⟪x s - xstar, gradient Φ (x s)⟫_ℝ
        - lam α * (α - lam α - 1 - pExp α) * s ^ pExp α * ⟪x s - xstar, v s⟫_ℝ
        + lam α ^ 2 * pExp α / 2 * s ^ (pExp α - 1) * ‖x s - xstar‖ ^ 2
        - (α - lam α - 1 - pExp α / 2) * s ^ (pExp α + 1) * ‖v s‖ ^ 2)
       - c * (pExp α * s ^ (pExp α - 1) * ‖x s - xstar‖ ^ 2
          + s ^ pExp α * (2 * ⟪x s - xstar, v s⟫_ℝ))) (Set.Ici t₀) s := by
    intro s hs
    have hsp : 0 < s := lt_of_lt_of_le ht0 hs
    obtain ⟨hx, -⟩ := hsol.2 s hs
    have hpow : HasDerivWithinAt (fun r : ℝ => r ^ pExp α) (pExp α * s ^ (pExp α - 1)) (Set.Ici t₀) s :=
      (Real.hasDerivAt_rpow_const (Or.inl hsp.ne')).hasDerivWithinAt
    have hn := (hx.sub_const xstar).norm_sq
    have hM := hpow.mul hn
    exact (avd_deriv Φ hΦ α t₀ x v hsol xstar (lam α) (pExp α) s hs).sub (hM.const_mul c)
  have hanti : AntitoneOn Ψ (Set.Ici (t1 t₀ α μ)) := by
    have ht1 : t₀ ≤ t1 t₀ α μ := le_max_left _ _
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _) (f' := fun s =>
      ((pExp α + 2) * s ^ (pExp α + 1) * (Φ (x s) - Φ xstar)
        - lam α * s ^ (pExp α + 1) * ⟪x s - xstar, gradient Φ (x s)⟫_ℝ
        - lam α * (α - lam α - 1 - pExp α) * s ^ pExp α * ⟪x s - xstar, v s⟫_ℝ
        + lam α ^ 2 * pExp α / 2 * s ^ (pExp α - 1) * ‖x s - xstar‖ ^ 2
        - (α - lam α - 1 - pExp α / 2) * s ^ (pExp α + 1) * ‖v s‖ ^ 2)
       - c * (pExp α * s ^ (pExp α - 1) * ‖x s - xstar‖ ^ 2
          + s ^ pExp α * (2 * ⟪x s - xstar, v s⟫_ℝ)))
    · intro s hs
      exact ((hderiv s (le_trans ht1 hs)).continuousWithinAt).mono
        (fun r hr => le_trans ht1 hr)
    · intro s hs
      rw [interior_Ici] at hs
      exact (hderiv s (le_trans ht1 (le_of_lt hs))).mono
        (fun r hr => by rw [interior_Ici] at hr; exact le_trans ht1 (le_of_lt hr))
    · intro s hs
      rw [interior_Ici] at hs
      have hs' : t1 t₀ α μ ≤ s := le_of_lt hs
      obtain ⟨hs1, hs2, hs3⟩ := avd_t1 t₀ α μ hα hμ ht0 s hs'
      have hD := avd_first Φ hΦ μ hsc α t₀ (by linarith) x v hsol xstar hmin (lam α) (pExp α)
        hl.le hp.le s hs1 _ (avd_deriv Φ hΦ α t₀ x v hsol xstar (lam α) (pExp α) s hs1)
      rw [e1, e2, e3] at hD
      have key : s ^ (pExp α + 1) = s ^ 2 * s ^ (pExp α - 1) := by
        rw [Real.rpow_add_one hs2.ne' (pExp α), Real.rpow_sub_one hs2.ne' (pExp α)]
        field_simp
      have hT0 : 0 ≤ s ^ (pExp α - 1) := (Real.rpow_pos_of_pos hs2 _).le
      have hprod : 0 ≤ (lam α / 2 * (μ * s ^ 2 - pExp α * lam α) + lam α * pExp α ^ 2 / 4)
          * s ^ (pExp α - 1) * ‖x s - xstar‖ ^ 2 := by
        apply mul_nonneg (mul_nonneg _ hT0) (sq_nonneg _)
        have : 0 ≤ μ * s ^ 2 - pExp α * lam α := by linarith
        positivity
      show _ ≤ (0 : ℝ)
      rw [hc]
      rw [key] at hD ⊢
      rw [e2, e3]
      nlinarith [hD, hprod]
  have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [hΨ] at this
  have hpos : 0 ≤ c * (t1 t₀ α μ ^ pExp α * ‖x (t1 t₀ α μ) - xstar‖ ^ 2) := by
    have : 0 < t1 t₀ α μ := lt_of_lt_of_le ht0 (le_max_left _ _)
    positivity
  linarith

theorem avd_26 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) :
    ∀ t, t1 t₀ α μ ≤ t →
      energyP Φ x v xstar (lam α) (pExp α) t
          ≤ energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ)
            + lam α * pExp α / 4 * t ^ pExp α * ‖x t - xstar‖ ^ 2 ∧
      energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ)
            + lam α * pExp α / 4 * t ^ pExp α * ‖x t - xstar‖ ^ 2
          ≤ energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ)
            + lam α * pExp α / (2 * μ) * t ^ pExp α * (Φ (x t) - Φ xstar) := by
  intro t ht
  refine ⟨avd_E_le Φ hΦ μ hsc α t₀ hα x v hsol xstar hmin t ht, ?_⟩
  obtain ⟨hp, hl, -, -, -⟩ := avd_params α hα
  have hμ := hsc.1
  obtain ⟨-, htp, -⟩ := avd_t1 t₀ α μ hα hμ hsol.1 t ht
  have hd := avd_dist Φ μ hsc xstar hmin (x t)
  have hT : 0 ≤ t ^ pExp α := (Real.rpow_pos_of_pos htp _).le
  have hc : 0 ≤ lam α * pExp α / 4 * t ^ pExp α := by positivity
  have := mul_le_mul_of_nonneg_left hd hc
  have e : lam α * pExp α / 4 * t ^ pExp α * (2 / μ * (Φ (x t) - Φ xstar))
      = lam α * pExp α / (2 * μ) * t ^ pExp α * (Φ (x t) - Φ xstar) := by
    field_simp
    ring
  linarith [this, e]

theorem avd_basic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) (t : ℝ) (ht : t1 t₀ α μ ≤ t) :
    0 < t ∧ 0 ≤ Φ (x t) - Φ xstar ∧
    t ^ pExp α * t ^ 2 * (Φ (x t) - Φ xstar) ≤ 2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) ∧
    energyP Φ x v xstar (lam α) (pExp α) t ≤ 2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) := by
  obtain ⟨hp, hl, -, -, -⟩ := avd_params α hα
  have hμ := hsc.1
  obtain ⟨-, htp, hmu⟩ := avd_t1 t₀ α μ hα hμ hsol.1 t ht
  have h26 := (avd_26 Φ hΦ μ hsc α t₀ hα x v hsol xstar hmin t ht)
  have hN : 0 ≤ Φ (x t) - Φ xstar := by linarith [hmin (x t)]
  have hT : 0 ≤ t ^ pExp α := (Real.rpow_pos_of_pos htp _).le
  have hEge : t ^ pExp α * t ^ 2 * (Φ (x t) - Φ xstar) ≤ energyP Φ x v xstar (lam α) (pExp α) t := by
    unfold energyP energy
    have h0 : 0 ≤ 1 / 2 * ‖lam α • (x t - xstar) + t • v t‖ ^ 2 + 0 / 2 * ‖x t - xstar‖ ^ 2 := by positivity
    nlinarith [mul_nonneg hT h0]
  have hcoef : lam α * pExp α / (2 * μ) ≤ t ^ 2 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hTN : 0 ≤ t ^ pExp α * (Φ (x t) - Φ xstar) := mul_nonneg hT hN
  have h1 : lam α * pExp α / (2 * μ) * t ^ pExp α * (Φ (x t) - Φ xstar) ≤
      t ^ 2 / 2 * (t ^ pExp α * (Φ (x t) - Φ xstar)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hcoef hTN
  have h2 := h26.1.trans h26.2
  refine ⟨htp, hN, ?_, ?_⟩ <;> nlinarith [h1, h2, hEge]

theorem avd_27 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) :
    ∀ t, t1 t₀ α μ ≤ t →
      Φ (x t) - Φ xstar
          ≤ 2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2) ∧
      2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2)
          = 2 * energyP Φ x v xstar (2 / 3 * α) (2 / 3 * (α - 3)) (t1 t₀ α μ)
              * t ^ (-(2 / 3) * α) := by
  intro t ht
  obtain ⟨htp, hN, h3, -⟩ := avd_basic Φ hΦ μ hsc α t₀ hα x v hsol xstar hmin t ht
  have hex : t ^ (-pExp α - 2) = (t ^ pExp α * t ^ 2)⁻¹ := by
    have : -pExp α - 2 = -(pExp α + 2) := by ring
    rw [this, Real.rpow_neg htp.le, Real.rpow_add htp]
    norm_cast
  refine ⟨?_, ?_⟩
  · rw [hex, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  · have : -pExp α - 2 = -(2 / 3) * α := by unfold pExp; ring
    rw [this]
    rfl

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) :
    ∀ t, t1 t₀ α μ ≤ t →
      ‖x t - xstar‖ ^ 2 ≤ 2 / μ * (Φ (x t) - Φ xstar) ∧
      2 / μ * (Φ (x t) - Φ xstar)
          ≤ 4 / μ * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2) ∧
      4 / μ * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2)
          = 4 / μ * energyP Φ x v xstar (2 / 3 * α) (2 / 3 * (α - 3)) (t1 t₀ α μ)
              * t ^ (-(2 / 3) * α) := by
  intro t ht
  have hμ := hsc.1
  obtain ⟨h27, h27'⟩ := avd_27 Φ hΦ μ hsc α t₀ hα x v hsol xstar hmin t ht
  refine ⟨avd_dist Φ μ hsc xstar hmin (x t), ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left h27 (show (0:ℝ) ≤ 2 / μ by positivity)
    have e : 2 / μ * (2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2))
        = 4 / μ * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2) := by
      field_simp; ring
    linarith
  · have e : 4 / μ * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2)
        = 2 / μ * (2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2)) := by
      field_simp; ring
    rw [e, h27']
    ring
