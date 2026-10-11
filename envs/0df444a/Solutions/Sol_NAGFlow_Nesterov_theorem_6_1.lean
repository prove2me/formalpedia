-- Prove2me | solution 1 for NAGFlow.Nesterov.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:49:22.074026+00:00
-- url     : https://prove2.me/submissions/8def9510-0f3e-4129-8a1e-b6dc9230f5d9

import Mathlib
import Definitions.Def_NAGFlow_Nesterov_Setting

namespace RRAux_NAGFlow_Nesterov_theorem_6_1

lemma u_step (u u' a sL sg k : ℝ) (hu : 0 ≤ u) (hu' : 0 ≤ u') (huu : u' ≤ u)
    (hsq : u' ^ 2 = (1 - a) * u ^ 2) (hsL : 0 < sL) (hsg : 0 ≤ sg)
    (hk : sL * a ≥ sg * u') (ih : u * (2 * sL + k * sg) ≤ 2 * sL) :
    u' * (2 * sL + (k + 1) * sg) ≤ 2 * sL := by
  rcases hu.lt_or_eq with hpos | hzero
  · have h1 : a * u / 2 ≤ u - u' := by
      have e : (u - u') * (u + u') = a * u ^ 2 := by linear_combination -hsq
      have e2 : (u - u') * (u + u') ≤ (u - u') * (2 * u) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have h2 : u * (u' * sg) ≤ u * (sL * a) := mul_le_mul_of_nonneg_left (by linarith) hu
    have h3 : u' * (u * (2 * sL + k * sg)) ≤ u' * (2 * sL) := mul_le_mul_of_nonneg_left ih hu'
    have h4 : sL * (a * u) ≤ sL * (2 * (u - u')) := mul_le_mul_of_nonneg_left (by linarith) hsL.le
    have : u * (u' * (2 * sL + (k + 1) * sg)) ≤ u * (2 * sL) := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  · subst hzero
    have : u' ^ 2 = 0 := by rw [hsq]; ring
    have : u' = 0 := by simpa using this
    subst this; simp; positivity

lemma ratesN (μ L : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (α γ : ℕ → ℝ) (hγ0 : 0 < γ 0)
    (hα : ∀ k, 0 < α k ∧ α k ≤ 1) (hγs : ∀ k, γ (k + 1) = (1 - α k) * γ k + μ * α k)
    (hLa : ∀ k, L * α k ^ 2 = γ (k + 1)) (Λ : ℕ → ℝ)
    (h98 : ∀ k, Λ (k + 1) ≤ (1 - α k) * Λ k) (h0 : 0 ≤ Λ 0) :
    (∀ k : ℕ, Λ k ≤ Λ 0 * min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
        ((1 - Real.sqrt (min (γ 1) μ / L)) ^ k)) ∧
    (∀ k : ℕ, 1 ≤ k → Λ k ≤ (L / γ 0 * Λ 0) *
        min (4 / (k : ℝ) ^ 2) ((1 - Real.sqrt (min (γ 1) μ / L)) ^ (k - 1))) := by
  set lam : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, (1 - α i) with hlam
  have hl0 : lam 0 = 1 := by simp [lam]
  have hls : ∀ k, lam (k + 1) = lam k * (1 - α k) := fun k => Finset.prod_range_succ _ k
  have hlnn : ∀ k, 0 ≤ lam k := fun k =>
    Finset.prod_nonneg (fun i _ => by linarith [(hα i).2])
  have hΛ : ∀ k, Λ k ≤ lam k * Λ 0 := by
    intro k
    induction k with
    | zero => simp [hl0]
    | succ k ih =>
      calc Λ (k + 1) ≤ (1 - α k) * Λ k := h98 k
        _ ≤ (1 - α k) * (lam k * Λ 0) :=
            mul_le_mul_of_nonneg_left ih (by linarith [(hα k).2])
        _ = lam (k + 1) * Λ 0 := by rw [hls]; ring
  -- γ k ≥ γ0 lam k
  have hγl : ∀ k, γ 0 * lam k ≤ γ k := by
    intro k
    induction k with
    | zero => simp [hl0]
    | succ k ih =>
      rw [hγs, hls]
      have := (hα k).1; have := (hα k).2
      nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ 1 - α k)]
  -- α k ≥ ŝ
  set m := min (γ 1) μ
  have hγm : ∀ k, m ≤ γ (k + 1) := by
    intro k
    induction k with
    | zero => exact min_le_left _ _
    | succ k ih =>
      rw [hγs (k + 1)]
      have hmμ : m ≤ μ := min_le_right _ _
      have := (hα (k + 1)).1; have := (hα (k + 1)).2
      nlinarith
  set sh := Real.sqrt (m / L)
  have hαs : ∀ k, sh ≤ α k := by
    intro k
    have h1 := hLa k
    have h2 := hγm k
    have : m / L ≤ α k ^ 2 := by rw [div_le_iff₀ hL]; linarith
    calc sh ≤ Real.sqrt (α k ^ 2) := Real.sqrt_le_sqrt this
      _ = α k := Real.sqrt_sq (hα k).1.le
  have hsh1 : 0 ≤ 1 - sh := by linarith [hαs 0, (hα 0).2]
  have hgeo : ∀ k, lam k ≤ (1 - sh) ^ k := by
    intro k
    induction k with
    | zero => simp [hl0]
    | succ k ih =>
      rw [hls, pow_succ]
      exact mul_le_mul ih (by linarith [hαs k]) (by linarith [(hα k).2]) (pow_nonneg hsh1 _)
  have hgeo1 : ∀ k, lam (k + 1) ≤ (1 - α 0) * (1 - sh) ^ k := by
    intro k
    induction k with
    | zero => simp [hls, hl0]
    | succ k ih =>
      rw [hls (k + 1), pow_succ, ← mul_assoc]
      exact mul_le_mul ih (by linarith [hαs (k + 1)]) (by linarith [(hα (k + 1)).2])
        (mul_nonneg (by linarith [(hα 0).2]) (pow_nonneg hsh1 _))
  -- sublinear rate
  set sL := Real.sqrt L
  set sg := Real.sqrt (γ 0)
  have hsL : 0 < sL := Real.sqrt_pos.mpr hL
  have hsg : 0 < sg := Real.sqrt_pos.mpr hγ0
  have hsLsq : sL ^ 2 = L := Real.sq_sqrt hL.le
  have hsgsq : sg ^ 2 = γ 0 := Real.sq_sqrt hγ0.le
  have hu : ∀ k : ℕ, Real.sqrt (lam k) * (2 * sL + k * sg) ≤ 2 * sL := by
    intro k
    induction k with
    | zero => simp [hl0]
    | succ k ih =>
      have hsq : Real.sqrt (lam (k + 1)) ^ 2 = (1 - α k) * Real.sqrt (lam k) ^ 2 := by
        rw [Real.sq_sqrt (hlnn _), Real.sq_sqrt (hlnn _), hls]; ring
      have huu : Real.sqrt (lam (k + 1)) ≤ Real.sqrt (lam k) := by
        apply Real.sqrt_le_sqrt; rw [hls]
        have := hlnn k; have := (hα k).1
        nlinarith
      have hk : sL * α k ≥ sg * Real.sqrt (lam (k + 1)) := by
        apply le_of_pow_le_pow_left₀ two_ne_zero (by have := (hα k).1; positivity)
        rw [mul_pow, mul_pow, hsLsq, hsgsq, Real.sq_sqrt (hlnn _), hLa k]
        exact hγl (k + 1)
      have := u_step _ _ (α k) sL sg k (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) huu hsq hsL
        hsg.le hk ih
      push_cast
      linarith
  have hlam1 : ∀ k : ℕ, lam k ≤ 4 * L / (sg * k + 2 * sL) ^ 2 := by
    intro k
    have hpos : 0 < sg * k + 2 * sL := by positivity
    rw [le_div_iff₀ (by positivity)]
    have h1 := hu k
    have h2 : (Real.sqrt (lam k) * (2 * sL + k * sg)) ^ 2 ≤ (2 * sL) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, Real.sq_sqrt (hlnn k), mul_pow, hsLsq] at h2
    nlinarith
  constructor
  · intro k
    calc Λ k ≤ lam k * Λ 0 := hΛ k
      _ = Λ 0 * lam k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_min (hlam1 k) (hgeo k)) h0
  · intro k hk
    have hC : 0 ≤ L / γ 0 * Λ 0 := by positivity
    rw [mul_min_of_nonneg _ _ hC]
    apply le_min
    · calc Λ k ≤ Λ 0 * lam k := by linarith [hΛ k]
        _ ≤ Λ 0 * (4 * L / (sg * k + 2 * sL) ^ 2) := mul_le_mul_of_nonneg_left (hlam1 k) h0
        _ ≤ L / γ 0 * Λ 0 * (4 / (k : ℝ) ^ 2) := by
          have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
          have : 4 * L / (sg * k + 2 * sL) ^ 2 ≤ L / γ 0 * (4 / (k : ℝ) ^ 2) := by
            rw [div_le_iff₀ (by positivity)]
            have : L / γ 0 * (4 / (k : ℝ) ^ 2) * (sg * k + 2 * sL) ^ 2
                = 4 * L * ((sg * k + 2 * sL) ^ 2 / (sg ^ 2 * k ^ 2)) := by
              rw [hsgsq]; field_simp
            rw [this]
            have : 1 ≤ (sg * k + 2 * sL) ^ 2 / (sg ^ 2 * k ^ 2) := by
              rw [one_le_div (by positivity)]
              nlinarith [mul_nonneg (mul_nonneg hsg.le hkpos.le) hsL.le]
            nlinarith
          nlinarith
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [show j + 1 - 1 = j by omega]
      have hγL : (1 - α 0) * γ 0 ≤ L := by
        have h1 := hLa 0
        have h2 := hγs 0
        have ha0 := (hα 0).1; have ha1 := (hα 0).2
        have e1 : α 0 ^ 2 ≤ 1 := by nlinarith
        have e2 : L * α 0 ^ 2 ≤ L := mul_le_of_le_one_right hL.le e1
        have e3 : 0 ≤ μ * α 0 := mul_nonneg hμ ha0.le
        linarith
      calc Λ (j + 1) ≤ lam (j + 1) * Λ 0 := hΛ _
        _ ≤ (1 - α 0) * (1 - sh) ^ j * Λ 0 := mul_le_mul_of_nonneg_right (hgeo1 j) h0
        _ ≤ L / γ 0 * Λ 0 * (1 - sh) ^ j := by
            have hp : 0 ≤ (1 - sh) ^ j := pow_nonneg hsh1 _
            have : 1 - α 0 ≤ L / γ 0 := by rw [le_div_iff₀ hγ0]; exact hγL
            have := mul_le_mul_of_nonneg_right this (mul_nonneg hp h0)
            nlinarith


-- scalar core of the estimate-sequence step (98)
lemma key (a g g' μ Fx Fx' Fy fs AA BB AB GA GB GG GX NV : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hg : 0 < g) (hg'pos : 0 < g') (hμ : 0 ≤ μ)
    (hg' : g' = (1 - a) * g + μ * a)
    (hy : (g + μ * a) * GB = a * g * GA + g' * GX)
    (hv : g' ^ 2 * NV = (1 - a) ^ 2 * g ^ 2 * AA + a ^ 2 * μ ^ 2 * BB + a ^ 2 * GG
      + 2 * ((1 - a) * g * (a * μ)) * AB - 2 * ((1 - a) * g * a) * GA - 2 * (a * μ * a) * GB)
    (Desc : g' * Fx' ≤ g' * Fy - a ^ 2 / 2 * GG)
    (C1 : Fx ≥ Fy + (GX - GB))
    (C2 : fs ≥ Fy - GB + μ / 2 * BB)
    (hAB : 0 ≤ AA - 2 * AB + BB) :
    Fx' - fs + g' / 2 * NV ≤ (1 - a) * (Fx - fs + g / 2 * AA) := by
  have h1a : 0 ≤ 1 - a := by linarith
  have e1 := mul_le_mul_of_nonneg_left C1 (mul_nonneg h1a hg'pos.le)
  have e2 := mul_le_mul_of_nonneg_left C2 (mul_nonneg ha.le hg'pos.le)
  have e3 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1a hg.le) ha.le) hμ) hAB
  have e4 : (1 - a) * ((g + μ * a) * GB) = (1 - a) * (a * g * GA + g' * GX) := by rw [hy]
  suffices h : g' * (Fx' - fs + g' / 2 * NV) ≤ g' * ((1 - a) * (Fx - fs + g / 2 * AA)) from
    le_of_mul_le_mul_left h hg'pos
  subst hg'
  nlinarith

end RRAux_NAGFlow_Nesterov_theorem_6_1

open NAGFlow.Nesterov in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ z, f xstar ≤ f z)
    (α γ : ℕ → ℝ) (x y v : ℕ → V) (hrun : IsNAGRun f gradf μ L α γ x y v) :
    (∀ k : ℕ, 0 < α k ∧ α k ≤ 1) ∧
      (∀ k : ℕ, lyap f xstar x v γ (k + 1) ≤ (1 - α k) * lyap f xstar x v γ k) ∧
      (∀ k : ℕ, lyap f xstar x v γ k ≤
        lyap f xstar x v γ 0 *
          min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
            ((1 - Real.sqrt (min (γ 1) μ / L)) ^ k)) ∧
      (∀ k : ℕ, 1 ≤ k → lyap f xstar x v γ k ≤
        (L / γ 0 * (f (x 0) - f xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2) *
          min (4 / (k : ℝ) ^ 2) ((1 - Real.sqrt (min (γ 1) μ / L)) ^ (k - 1))) := by
  have hμ := hf.mu_nonneg
  have hL := hf.L_pos
  have hμL := hf.mu_le_L
  have hLa : ∀ k, L * α k ^ 2 = γ (k + 1) := fun k => by
    rw [hrun.alpha_eq k, hrun.gamma_eq k]
  have hγp : ∀ k, 0 < γ k := by
    intro k
    cases k with
    | zero => exact hrun.gamma0_pos
    | succ k => rw [← hLa k]; have := hrun.alpha_pos k; positivity
  have hα : ∀ k, 0 < α k ∧ α k ≤ 1 := by
    intro k
    refine ⟨hrun.alpha_pos k, ?_⟩
    by_contra hc
    push Not at hc
    have h1 := hrun.alpha_eq k
    have h2 := hγp k
    have h3 : 0 < (α k - 1) * (L * (α k + 1) + γ k - μ) := by
      apply mul_pos (by linarith)
      nlinarith
    nlinarith
  have h98 : ∀ k : ℕ, lyap f xstar x v γ (k + 1) ≤ (1 - α k) * lyap f xstar x v γ k := by
    intro k
    obtain ⟨ha, ha1⟩ := hα k
    have hg := hγp k
    have hg'p := hγp (k + 1)
    have hge := hrun.gamma_eq k
    have hye := hrun.y_eq k
    have hve := hrun.v_eq k
    have hD := hrun.x_desc k
    have hLak := hLa k
    set a := α k
    set g := γ k
    set g' := γ (k + 1)
    set x' := x (k + 1)
    set v' := v (k + 1)
    set x0 := x k
    set v0 := v k
    set y0 := y k
    set G := gradf y0
    have hgμ : 0 < g + μ * a := by have := mul_nonneg hμ ha.le; linarith
    have hy1 : (g + μ * a) • y0 = (a * g) • v0 + g' • x0 := by
      rw [hye, smul_smul, mul_one_div_cancel hgμ.ne', one_smul]
    have hv1 : g' • v' = ((1 - a) * g) • v0 + a • (μ • y0 - G) := by
      rw [hve, smul_smul, mul_one_div_cancel hg'p.ne', one_smul]
    set A := v0 - xstar
    set B := y0 - xstar
    set X := x0 - xstar
    set W := v' - xstar
    have hyB : (g + μ * a) • B = (a * g) • A + g' • X := by
      simp only [A, B, X]
      linear_combination (norm := module) hy1 + (hge • xstar)
    have hvW : g' • W = ((1 - a) * g) • A + (a * μ) • B - a • G := by
      simp only [A, B, W]
      linear_combination (norm := module) hv1 - (hge • xstar)
    -- scalar facts
    have hy : (g + μ * a) * inner ℝ G B = a * g * inner ℝ G A + g' * inner ℝ G X := by
      have := congrArg (fun w => inner ℝ G w) hyB
      simp only [inner_add_right, real_inner_smul_right] at this
      exact this
    have hv : g' ^ 2 * inner ℝ W W = (1 - a) ^ 2 * g ^ 2 * inner ℝ A A
        + a ^ 2 * μ ^ 2 * inner ℝ B B + a ^ 2 * inner ℝ G G
        + 2 * ((1 - a) * g * (a * μ)) * inner ℝ A B - 2 * ((1 - a) * g * a) * inner ℝ G A
        - 2 * (a * μ * a) * inner ℝ G B := by
      have := congrArg (fun w => inner ℝ w w) hvW
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right] at this
      simp only [real_inner_comm A B, real_inner_comm G A, real_inner_comm G B] at this
      linear_combination this
    have Desc : g' * f x' ≤ g' * f y0 - a ^ 2 / 2 * inner ℝ G G := by
      have := mul_le_mul_of_nonneg_left hD hg'p.le
      rw [real_inner_self_eq_norm_sq]
      have e : g' * (1 / (2 * L) * ‖G‖ ^ 2) = a ^ 2 / 2 * ‖G‖ ^ 2 := by
        rw [← hLak]; field_simp
      nlinarith
    have C1 : f x0 ≥ f y0 + (inner ℝ G X - inner ℝ G B) := by
      have h := hf.mu_convex x0 y0
      have e : x0 - y0 = X - B := by simp only [X, B]; abel
      rw [e, inner_sub_right] at h
      have := mul_nonneg (div_nonneg hμ (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg ‖X - B‖)
      linarith
    have C2 : f xstar ≥ f y0 - inner ℝ G B + μ / 2 * inner ℝ B B := by
      have h := hf.mu_convex xstar y0
      have e : xstar - y0 = -B := by simp only [B]; abel
      rw [e, inner_neg_right, norm_neg, ← real_inner_self_eq_norm_sq] at h
      linarith
    have hAB : 0 ≤ inner ℝ A A - 2 * inner ℝ A B + inner ℝ B B := by
      have := real_inner_self_nonneg (x := A - B)
      simp only [inner_sub_left, inner_sub_right, real_inner_comm A B] at this
      linarith
    show f x' - f xstar + g' / 2 * ‖W‖ ^ 2 ≤ (1 - a) * (f x0 - f xstar + g / 2 * ‖A‖ ^ 2)
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact RRAux_NAGFlow_Nesterov_theorem_6_1.key a g g' μ (f x0) (f x') (f y0) (f xstar)
      (inner ℝ A A) (inner ℝ B B) (inner ℝ A B) (inner ℝ G A) (inner ℝ G B) (inner ℝ G G)
      (inner ℝ G X) (inner ℝ W W) ha ha1 hg hg'p hμ hge hy hv Desc C1 C2 hAB
  have h0 : 0 ≤ lyap f xstar x v γ 0 := by
    show 0 ≤ f (x 0) - f xstar + γ 0 / 2 * ‖v 0 - xstar‖ ^ 2
    have := hxstar (x 0)
    have := hrun.gamma0_pos
    positivity
  obtain ⟨r99, r100⟩ := RRAux_NAGFlow_Nesterov_theorem_6_1.ratesN μ L hL hμ α γ hrun.gamma0_pos
    hα hrun.gamma_eq hLa (lyap f xstar x v γ) h98 h0
  refine ⟨hα, h98, r99, fun k hk => ?_⟩
  have hC : L / γ 0 * (f (x 0) - f xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2
      = L / γ 0 * lyap f xstar x v γ 0 := by
    show _ = L / γ 0 * (f (x 0) - f xstar + γ 0 / 2 * ‖v 0 - xstar‖ ^ 2)
    have := hrun.gamma0_pos.ne'
    field_simp
  rw [hC]
  exact r100 k hk

#print axioms solution
