-- Prove2me | solution 1 for MasulloAudit.periodization_kernel_support_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:16:10.348648+00:00
-- url     : https://prove2.me/submissions/f053dabb-abe4-4a11-a9aa-24257597fb54

import Mathlib

set_option autoImplicit false

open scoped ContDiff

theorem solution (γ a A₀ : ℝ) (hγ : 1 < γ) (ha : 1 < a) (haγ : γ < a ^ 2)
    (hA₀ : a ≤ A₀) (hA₀' : A₀ < a * γ) :
    ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ Function.support φ ⊆ Set.Icc a⁻¹ a ∧
      (∀ x : ℝ, 0 < x → HasSum (fun k : ℤ => φ (γ ^ k * x)) 0) ∧
      ¬ ∃ ψ : ℝ → ℂ,
        Function.support ψ ⊆ Set.Icc (Real.exp (-|Real.log A₀ - Real.log γ|))
          (Real.exp |Real.log A₀ - Real.log γ|) ∧
        ∀ x : ℝ, 0 < x → ψ x - ψ (γ * x) = φ x := by
  have hγ0 : 0 < γ := by linarith
  have ha0 : 0 < a := by linarith
  have hA0pos : 0 < A₀ := by linarith
  -- `exp A < a` for `A = |log A₀ - log γ|`
  have hexpA : Real.exp |Real.log A₀ - Real.log γ| < a := by
    have h1 : Real.log A₀ - Real.log γ < Real.log a := by
      have h := Real.log_lt_log hA0pos hA₀'
      rw [Real.log_mul ha0.ne' hγ0.ne'] at h
      linarith
    have h2 : -Real.log a < Real.log A₀ - Real.log γ := by
      have h3 : Real.log γ < Real.log (a ^ 2) := Real.log_lt_log hγ0 haγ
      have h4 : Real.log a ≤ Real.log A₀ := Real.log_le_log ha0 hA₀
      rw [Real.log_pow] at h3
      push_cast at h3
      linarith
    have h5 : |Real.log A₀ - Real.log γ| < Real.log a := abs_lt.mpr ⟨h2, h1⟩
    calc Real.exp |Real.log A₀ - Real.log γ| < Real.exp (Real.log a) := Real.exp_lt_exp.mpr h5
      _ = a := Real.exp_log ha0
  have hga : γ / a < a := by
    rw [div_lt_iff₀ ha0]; nlinarith
  obtain ⟨c, hcA, hcg, hca⟩ : ∃ c : ℝ, Real.exp |Real.log A₀ - Real.log γ| ≤ c ∧ γ / a ≤ c ∧ c < a :=
    ⟨max (Real.exp |Real.log A₀ - Real.log γ|) (γ / a), le_max_left _ _, le_max_right _ _,
      max_lt hexpA hga⟩
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos _) hcA
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ = (c + a) / 2 := ⟨_, rfl⟩
  have hx0pos : 0 < x₀ := by rw [hx₀]; linarith
  let b : ContDiffBump x₀ := ⟨(a - c) / 4, (a - c) / 2, by linarith, by linarith⟩
  have hb_supp : ∀ x : ℝ, b x ≠ 0 → c < x ∧ x < a := by
    intro x hx
    have h : x ∈ Function.support b := hx
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at h
    have h' : -((a - c) / 2) < x - x₀ ∧ x - x₀ < (a - c) / 2 := h
    constructor <;> linarith [h'.1, h'.2]
  have hbx0 : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  refine ⟨fun x => ((b x - b (γ * x) : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · -- smoothness
    have h1 : ContDiff ℝ ∞ (fun x : ℝ => b x) := b.contDiff
    have h2 : ContDiff ℝ ∞ (fun x : ℝ => b (γ * x)) :=
      b.contDiff.comp (contDiff_const.mul contDiff_id)
    exact Complex.ofRealCLM.contDiff.comp (h1.sub h2)
  · -- support
    intro x hx
    rw [Function.mem_support] at hx
    have hor : b x ≠ 0 ∨ b (γ * x) ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      simp [h.1, h.2]
    have hinv : a⁻¹ < γ / a := by
      rw [inv_eq_one_div]
      exact div_lt_div_of_pos_right hγ ha0
    rcases hor with h | h
    · obtain ⟨h1, h2⟩ := hb_supp x h
      exact ⟨by linarith, h2.le⟩
    · obtain ⟨h1, h2⟩ := hb_supp _ h
      have h3 : γ * a⁻¹ < γ * x := by
        rw [← div_eq_mul_inv]; linarith
      have h4 : a⁻¹ < x := lt_of_mul_lt_mul_left h3 hγ0.le
      have h5 : 0 < x := lt_trans (inv_pos.mpr ha0) h4
      exact ⟨h4.le, by nlinarith⟩
  · -- the periodization vanishes
    intro x hx
    obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (a / x) hγ
    obtain ⟨n2, hn2⟩ := pow_unbounded_of_one_lt (x / c) hγ
    have hax : a < γ ^ n1 * x := (div_lt_iff₀ hx).mp hn1
    have hxc : x < γ ^ n2 * c := (div_lt_iff₀ hc0).mp hn2
    have hf0 : ∀ k : ℤ, k ∉ Finset.Icc (-(n2 : ℤ)) (n1 : ℤ) → b (γ ^ k * x) = 0 := by
      intro k hk
      by_contra hne
      obtain ⟨h1, h2⟩ := hb_supp _ hne
      apply hk
      rw [Finset.mem_Icc]
      constructor
      · by_contra hlt
        push Not at hlt
        have h3 : γ ^ k ≤ γ ^ (-(n2 : ℤ)) := zpow_le_zpow_right₀ hγ.le hlt.le
        rw [zpow_neg, zpow_natCast] at h3
        have hk1 : γ ^ k * γ ^ n2 ≤ 1 := by
          calc γ ^ k * γ ^ n2 ≤ (γ ^ n2)⁻¹ * γ ^ n2 :=
                mul_le_mul_of_nonneg_right h3 (pow_pos hγ0 _).le
            _ = 1 := inv_mul_cancel₀ (pow_pos hγ0 _).ne'
        have h4 : γ ^ k * x < γ ^ k * (γ ^ n2 * c) :=
          mul_lt_mul_of_pos_left hxc (zpow_pos hγ0 k)
        have h5 : γ ^ k * (γ ^ n2 * c) = (γ ^ k * γ ^ n2) * c := by ring
        have h6 : (γ ^ k * γ ^ n2) * c ≤ 1 * c := mul_le_mul_of_nonneg_right hk1 hc0.le
        linarith
      · by_contra hgt
        push Not at hgt
        have h3 : γ ^ (n1 : ℤ) ≤ γ ^ k := zpow_le_zpow_right₀ hγ.le hgt.le
        rw [zpow_natCast] at h3
        have h4 : γ ^ n1 * x ≤ γ ^ k * x := mul_le_mul_of_nonneg_right h3 hx.le
        linarith
    have hS : HasSum (fun k : ℤ => b (γ ^ k * x))
        (∑ k ∈ Finset.Icc (-(n2 : ℤ)) (n1 : ℤ), b (γ ^ k * x)) :=
      hasSum_sum_of_ne_finset_zero hf0
    have hS' : HasSum (fun k : ℤ => b (γ ^ (k + 1) * x))
        (∑ k ∈ Finset.Icc (-(n2 : ℤ)) (n1 : ℤ), b (γ ^ k * x)) :=
      ((Equiv.addRight (1 : ℤ)).hasSum_iff (f := fun k : ℤ => b (γ ^ k * x))).mpr hS
    have hd := hS.sub hS'
    rw [sub_self] at hd
    have hd' := Complex.hasSum_ofReal.mpr hd
    have hfun : (fun k : ℤ => ((b (γ ^ k * x) - b (γ * (γ ^ k * x)) : ℝ) : ℂ)) =
        fun k : ℤ => ((b (γ ^ k * x) - b (γ ^ (k + 1) * x) : ℝ) : ℂ) := by
      funext k
      have e : γ * (γ ^ k * x) = γ ^ (k + 1) * x := by
        rw [zpow_add_one₀ hγ0.ne']; ring
      rw [e]
    show HasSum (fun k : ℤ => ((b (γ ^ k * x) - b (γ * (γ ^ k * x)) : ℝ) : ℂ)) 0
    rw [hfun]
    simpa using hd'
  · -- no solution of the difference equation is supported in `K_A`
    rintro ⟨ψ, hψs, hψ⟩
    have key : ∀ n : ℕ, ψ (γ ^ n * x₀) - (b (γ ^ n * x₀) : ℂ) = ψ x₀ - (b x₀ : ℂ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hpos : 0 < γ ^ n * x₀ := by positivity
        have h := hψ (γ ^ n * x₀) hpos
        have e : γ ^ (n + 1) * x₀ = γ * (γ ^ n * x₀) := by ring
        rw [e, ← ih]
        simp only [Complex.ofReal_sub] at h
        linear_combination (-1 : ℂ) * h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (a / x₀) hγ
    have hax : a < γ ^ n * x₀ := (div_lt_iff₀ hx0pos).mp hn
    have hψ0 : ψ (γ ^ n * x₀) = 0 := by
      by_contra h
      have h' := (hψs h).2
      linarith
    have hb0 : b (γ ^ n * x₀) = 0 := by
      by_contra h
      have h' := (hb_supp _ h).2
      linarith
    have hψx0 : ψ x₀ = 0 := by
      by_contra h
      have h' := (hψs h).2
      rw [hx₀] at h'
      linarith
    have hk := key n
    rw [hψ0, hb0, hψx0, hbx0] at hk
    simp at hk
