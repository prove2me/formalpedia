-- Prove2me | solution 1 for MomentSearch.rakhmanov_equilibrium_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:37:39.964034+00:00
-- url     : https://prove2.me/submissions/8ebc1a71-0f7f-4a2f-9cea-8b7b77403039

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_quantile_phase_bounds
import Theorems.Thm_MomentSearch_rakhmanov_equilibrium_product_envelope

theorem solution :
    ∃ B : ℝ, 0 < B ∧
      ∀ N k : ℕ, 1 ≤ k → k < N →
      let ζ : ℕ → ℝ := fun j => -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
      let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
        ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
      ∀ r : ℝ, r = Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2) →
      ∀ x : ℝ, -r < x → x < r →
      ∃ M y : ℝ, ∃ H : Polynomial ℝ,
        0 < M ∧ M ≤ (N : ℝ) / 2 ∧ |x - y| ≤ 2 / M ∧
        (N : ℝ) / Real.pi * Real.arctan ((N : ℝ) / (k : ℝ) *
          Real.sqrt (r ^ 2 - x ^ 2)) ≤ M ∧
        H.natDegree ≤ N - k - 1 ∧ H.eval x ≠ 0 ∧
        (∀ j ∈ Finset.Icc 1 N,
          |H.eval (ζ j)| ≤ B * |H.eval x| * (w x / w (ζ j)) /
            max 1 (M * |ζ j - y|)) := by 
  refine ⟨192, by norm_num, ?_⟩
  intro N k hk hkN ζ w r hr x hx₁ hx₂
  subst r
  let r := Real.sqrt (1 - (k : ℝ)^2 / (N : ℝ)^2)
  have hr : r = Real.sqrt (1 - (k : ℝ)^2 / (N : ℝ)^2) := rfl
  let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
    ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
  let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
  have hx : x ∈ Set.Ioo (-r) r := ⟨hx₁,hx₂⟩
  obtain ⟨M,y,hy,hy0,hM,hMN,hxy,hρ,hphase⟩ :=
    MomentSearch.rakhmanov_quantile_phase_bounds N k hk hkN x hx
  change f y = 0 at hy0
  let q : ℝ → ℝ := fun z => if z = y then Real.pi * ρ y else |f z| / |z-y|
  change M/4 ≤ q x ∧ ∀ z ∈ Set.Icc (-1 : ℝ) 1, q z * max 1 (M * |z-y|) ≤ 4*M at hphase
  obtain ⟨S,a,hdeg,henv,hcomp,hslope⟩ :=
    MomentSearch.rakhmanov_equilibrium_product_envelope N k hk hkN
  have hr1 : r ≤ 1 := by
    rw [hr, Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [div_nonneg (sq_nonneg (k : ℝ)) (sq_nonneg (N : ℝ))]
  have inside (z : ℝ) (hz : z ∈ Set.Ioo (-r) r) : z ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hw (z : ℝ) : 0 < w z := Real.exp_pos _
  have env (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
      0 < a z ∧ |S.eval z| * w z = a z * |f z| := by
    simpa only [f, ρ, hr] using henv z hz
  have hy' : y ∈ Set.Ioo (-r) r := hy
  have hyS : S.IsRoot y := by
    have he := (env y (inside _ hy')).2
    rw [hy0, abs_zero, mul_zero] at he
    exact abs_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (hw y).ne')
  obtain ⟨H,hH⟩ := Polynomial.dvd_iff_isRoot.mpr hyS
  have repr (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
      |H.eval z| * w z = a z * q z := by
    by_cases h : z = y
    · subst z
      have he := hslope y hy (by simpa only [f, ρ, hr] using hy0)
      rw [hH] at he
      simpa [q, Polynomial.derivative_mul, ρ, hr] using he
    · have he := (env z hz).2
      rw [hH, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        abs_mul] at he
      simp only [q, if_neg h]
      rw [← mul_div_assoc, eq_div_iff (abs_ne_zero.mpr (sub_ne_zero.mpr h))]
      linarith only [show |H.eval z| * w z * |z-y| = a z * |f z| by linarith only [he]]
  have ax := (env x (inside _ hx)).1
  have hl : a x * (M/4) ≤ |H.eval x| * w x := by
    rw [repr _ (inside _ hx)]
    exact mul_le_mul_of_nonneg_left hphase.1 ax.le
  have hHx : H.eval x ≠ 0 := by
    intro he
    rw [he, abs_zero, zero_mul] at hl
    exact (not_lt_of_ge hl) (by positivity)
  have deg : H.natDegree ≤ N-k-1 := by
    have hHne : H ≠ 0 := by intro h; simp [h] at hHx
    rw [hH, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hHne,
      Polynomial.natDegree_X_sub_C] at hdeg
    omega
  refine ⟨M,y,H,hM,hMN,hxy,?_,deg,hHx,?_⟩
  · simpa only [hr] using hρ
  · intro j hj
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    obtain ⟨hj₁,hj₂⟩ := Finset.mem_Icc.mp hj
    have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
    have h2 : (j : ℝ) ≤ N := by exact_mod_cast hj₂
    have hz : ζ j ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp [ζ]
      constructor
      · linarith [div_nonneg (show 0 ≤ 2*(j : ℝ)-1 by linarith) hNr.le]
      · linarith [(div_le_iff₀ hNr).2 (show 2*(j : ℝ)-1 ≤ 2*N by linarith)]
    let D := max 1 (M * |ζ j-y|)
    have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left ..)
    have hc := hcomp x hx (ζ j) hz
    have hb : |H.eval (ζ j)| * w (ζ j) * D ≤ 192 * (|H.eval x| * w x) := calc
      _ = a (ζ j) * (q (ζ j) * D) := by rw [repr _ hz, mul_assoc]
      _ ≤ a (ζ j) * (4*M) := mul_le_mul_of_nonneg_left (hphase.2 _ hz) (env _ hz).1.le
      _ ≤ (12*a x) * (4*M) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ _ := by linarith only [hl]
    change _ ≤ _ / D
    apply (le_div_iff₀ hD).2
    rw [← mul_div_assoc, le_div_iff₀ (hw _)]
    linarith only [hb]
