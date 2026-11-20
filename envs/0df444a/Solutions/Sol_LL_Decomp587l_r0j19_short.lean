-- Prove2me | solution 1 for LL_Decomp587l.r0j19_short
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T11:00:02.417185+00:00
-- url     : https://prove2.me/submissions/211127a6-7294-4e97-921a-2a951acfa11c

import Mathlib
import Definitions.Def_LL_Decomp587l_IsBuchstab
import Definitions.Def_LL_Decomp587l_ZeroBelowOne
import Definitions.Def_LL_Decomp587l_domain
import Definitions.Def_LL_Decomp587l_buchstabIntegral
import Definitions.Def_LL_Decomp587l_r0j19_lo
import Definitions.Def_LL_Decomp587l_r0j19_hi
import Definitions.Def_r0j19_cert_core
import Theorems.Thm_R0J19Cert_b3_certs_lo
import Theorems.Thm_R0J19Cert_b3_certs_hi
import Theorems.Thm_R0J19Cert_outer_certs

open Real Set Finset MeasureTheory LL_Decomp587l R0J19Cert
open scoped Classical

namespace SolBuchstab4D_r0j19

/-! ### Constants as Reals -/

private noncomputable def a0R : ℝ := 100 / 353
private noncomputable def a1R : ℝ := 10 / 29
private noncomputable def bR : ℝ := 25 / 61
private noncomputable def cR : ℝ := 5 / 11

private lemma a0R_eq : a0R = (A0_num : ℝ) / D_den := by
  unfold a0R A0_num D_den; norm_num

private lemma a1R_eq : a1R = (A1_num : ℝ) / D_den := by
  unfold a1R A1_num D_den; norm_num

private lemma bR_eq : bR = (B_num : ℝ) / D_den := by
  unfold bR B_num D_den; norm_num

private lemma cR_eq : cR = (C_num : ℝ) / D_den := by
  unfold cR C_num D_den; norm_num

private lemma eqDeriv {f : ℝ → ℝ} {d1 d2 x : ℝ}
    (h : HasDerivAt f d1 x) (heq : d1 = d2) : HasDerivAt f d2 x := heq ▸ h

local infixl:45 " ▸d " => eqDeriv

/-! ### Part 2: Buchstab Function Bounds -/

private lemma buchstab_mul_mono_on {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hnn : ∀ u ∈ Ioo a b, 0 ≤ ω (u - 1)) :
    a * ω a ≤ b * ω b := by
  have hcont : ContinuousOn (fun v => v * ω v) (Icc a b) :=
    continuousOn_id.mul (hω.1.mono (fun x hx => Set.mem_Ici.mpr (by linarith [hx.1])))
  have hmono : MonotoneOn (fun v => v * ω v) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (hω.2.2 x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hω.2.2 x (by linarith [hx.1])).deriv]
      exact hnn x hx
  exact hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

private lemma buchstab_nonneg {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∀ u : ℝ, 0 ≤ ω u := by
  suffices h : ∀ n : ℕ, ∀ u : ℝ, u ≤ (n : ℝ) + 1 → 0 ≤ ω u by
    intro u
    exact h (Nat.ceil (max u 0)) u (by
      have h1 := Nat.le_ceil (max u 0)
      have h2 := le_max_left u 0
      linarith)
  intro n
  induction n with
  | zero =>
    intro u hu
    push_cast at hu
    by_cases h1 : u < 1
    · rw [hz u h1]
    · push Not at h1
      have h2 : u = 1 := by linarith
      rw [h2, hω.2.1 1 le_rfl (by norm_num)]
      norm_num
  | succ n ih =>
    intro u hu
    by_cases h1 : u ≤ (n : ℝ) + 1
    · exact ih u h1
    · push Not at h1
      by_cases hn0 : n = 0
      · subst hn0
        rw [hω.2.1 u (by linarith) (by push_cast at hu; linarith)]
        positivity
      · have ha : (2 : ℝ) ≤ (n : ℝ) + 1 := by
          have : (1 : ℕ) ≤ n := by omega
          have : (1 : ℝ) ≤ n := by exact_mod_cast this
          linarith
        have hmul := buchstab_mul_mono_on hω ha (le_of_lt h1) (fun v hv =>
          ih (v - 1) (by push_cast at hu; linarith [hv.2]))
        have ha_nn : 0 ≤ ((n : ℝ) + 1) * ω ((n : ℝ) + 1) :=
          mul_nonneg (by linarith) (ih ((n : ℝ) + 1) le_rfl)
        have hu_pos : 0 < u := by linarith
        nlinarith

private lemma buchstab_le_two_thirds_on_two_three {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (h2 : 2 ≤ u) (h3 : u ≤ 3) : ω u ≤ 2 / 3 := by
  have hcont : ContinuousOn (fun v => v * ω v - (v - 1)) (Icc 2 u) :=
    (continuousOn_id.mul (hω.1.mono (fun x hx => Set.mem_Ici.mpr (by linarith [hx.1])))).sub
      (continuousOn_id.sub continuousOn_const)
  have hanti : AntitoneOn (fun v => v * ω v - (v - 1)) (Icc 2 u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 2 u) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hω.2.2 x hx.1).fun_sub ((hasDerivAt_id' x).fun_sub (hasDerivAt_const x 1))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hd : HasDerivAt (fun v => v * ω v - (v - 1)) (ω (x - 1) - 1) x :=
        ((hω.2.2 x hx.1).fun_sub ((hasDerivAt_id' x).fun_sub (hasDerivAt_const x 1))) ▸d (by ring)
      rw [hd.deriv]
      rw [hω.2.1 (x - 1) (by linarith [hx.1]) (by linarith [hx.2])]
      have hx1 : 1 ≤ x - 1 := by linarith [hx.1]
      have : 1 / (x - 1) ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hx1
      linarith
  have hle := hanti (left_mem_Icc.mpr h2) (right_mem_Icc.mpr h2) h2
  dsimp only at hle
  have h2val : (2 : ℝ) * ω 2 - (2 - 1) = 0 := by
    rw [hω.2.1 2 (by norm_num) (by norm_num)]; norm_num
  rw [h2val] at hle
  have : u * ω u ≤ (2 / 3 : ℝ) * u := by linarith
  have hu_pos : 0 < u := by linarith
  nlinarith

private lemma buchstab_le_two_thirds_ge_two {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ∀ n : ℕ, ∀ u : ℝ, 2 ≤ u → u ≤ (n : ℝ) + 3 → ω u ≤ 2 / 3 := by
  intro n
  induction n with
  | zero =>
    intro u h2 h3
    exact buchstab_le_two_thirds_on_two_three hω h2 (by simpa using h3)
  | succ n ih =>
    intro u h2 hu
    by_cases hle : u ≤ (n : ℝ) + 3
    · exact ih u h2 hle
    · push Not at hle
      let a : ℝ := (n : ℝ) + 3
      have ha3 : 3 ≤ a := by simp only [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hcont : ContinuousOn (fun v => v * ω v - (2 / 3 : ℝ) * v) (Icc a u) :=
        (continuousOn_id.mul (hω.1.mono (fun x hx => Set.mem_Ici.mpr (by linarith [hx.1])))).sub
          (continuousOn_const.mul continuousOn_id)
      have hanti : AntitoneOn (fun v => v * ω v - (2 / 3 : ℝ) * v) (Icc a u) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc a u) hcont
        · intro x hx
          rw [interior_Icc] at hx
          exact ((hω.2.2 x (by linarith [hx.1])).fun_sub
            ((hasDerivAt_id' x).const_mul (2 / 3 : ℝ))).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hd : HasDerivAt (fun v => v * ω v - (2 / 3 : ℝ) * v) (ω (x - 1) - 2 / 3) x :=
            ((hω.2.2 x (by linarith [hx.1])).fun_sub ((hasDerivAt_id' x).const_mul (2 / 3 : ℝ))) ▸d (by ring)
          rw [hd.deriv]
          have hih := ih (x - 1) (by linarith [hx.1]) (by push_cast at hu; linarith [hx.2])
          linarith
      have hstep := hanti (left_mem_Icc.mpr (le_of_lt hle)) (right_mem_Icc.mpr (le_of_lt hle)) (le_of_lt hle)
      dsimp only at hstep
      have ha_le : ω a ≤ 2 / 3 := ih a (by linarith) le_rfl
      have ha_pos : 0 < a := by linarith
      have hu_pos : 0 < u := by linarith
      nlinarith


private lemma buchstab_le_four_fifths {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : (5 / 4 : ℝ) ≤ u) : ω u ≤ 4 / 5 := by
  by_cases h2 : u ≤ 2
  · rw [hω.2.1 u (by linarith) h2]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  · push Not at h2
    have hle := buchstab_le_two_thirds_ge_two hω (Nat.ceil u) u (le_of_lt h2)
      (by have := Nat.le_ceil u; linarith)
    linarith

/-! ### Part 3: Elementary Calculus Bounds -/

private lemma log_one_add_le_rat {y : ℝ} (hy : 0 ≤ y) :
    Real.log (1 + y) ≤ y * (6 + y) / (6 + 4 * y) := by
  let F : ℝ → ℝ := fun t => t * (6 + t) / (6 + 4 * t) - Real.log (1 + t)
  have hF0 : F 0 = 0 := by simp [F]
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt F (4 * t ^ 3 / ((6 + 4 * t) ^ 2 * (1 + t))) t := by
    intro t ht
    have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
    have hden1 : 6 + 4 * t ≠ 0 := by linarith
    have hden2 : 1 + t ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun s => s * (6 + s)) (6 + 2 * t) t :=
      ((hasDerivAt_id' t).fun_mul ((hasDerivAt_const t (6 : ℝ)).fun_add (hasDerivAt_id' t))) ▸d (by ring)
    have hd2 : HasDerivAt (fun s => 6 + 4 * s) 4 t :=
      ((hasDerivAt_const t (6 : ℝ)).fun_add ((hasDerivAt_id' t).const_mul 4)) ▸d (by ring)
    have hdq := hd1.fun_div hd2 hden1
    have hdl : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + t)) t :=
      (((hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id' t)).log hden2) ▸d (by ring)
    exact (hdq.fun_sub hdl) ▸d (by field_simp; ring)
  have hcont : ContinuousOn F (Icc 0 y) := fun t ht =>
    (hderiv t ht.1).continuousAt.continuousWithinAt
  have hmono : MonotoneOn F (Icc 0 y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 y) hcont
    · intro t ht; rw [interior_Icc] at ht
      exact (hderiv t (le_of_lt ht.1)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      rw [(hderiv t (le_of_lt ht.1)).deriv]
      have ht0 : 0 ≤ t := le_of_lt ht.1
      positivity
  have hle := hmono (left_mem_Icc.mpr hy) (right_mem_Icc.mpr hy) hy
  rw [hF0] at hle
  simp only [F] at hle
  linarith

private lemma secant_bound_of_deriv_mono {g g' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hmono : MonotoneOn g' (Ioo a b)) :
    ∀ x ∈ Icc a b, g x * (b - a) ≤ g a * (b - x) + g b * (x - a) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · linarith
  rcases eq_or_lt_of_le hx.2 with rfl | hxb
  · linarith
  have h1 : ∃ c₁ ∈ Ioo a x, g' c₁ = (g x - g a) / (x - a) :=
    exists_hasDerivAt_eq_slope g g' hax
      (hcont.mono (Icc_subset_Icc_right (le_of_lt hxb)))
      (fun t ht => hderiv t ⟨ht.1, lt_trans ht.2 hxb⟩)
  have h2 : ∃ c₂ ∈ Ioo x b, g' c₂ = (g b - g x) / (b - x) :=
    exists_hasDerivAt_eq_slope g g' hxb
      (hcont.mono (Icc_subset_Icc_left (le_of_lt hax)))
      (fun t ht => hderiv t ⟨lt_trans hax ht.1, ht.2⟩)
  rcases h1 with ⟨c₁, hc₁, heq₁⟩
  rcases h2 with ⟨c₂, hc₂, heq₂⟩
  have hle : g' c₁ ≤ g' c₂ :=
    hmono ⟨hc₁.1, lt_trans hc₁.2 hxb⟩ ⟨lt_trans hax hc₂.1, hc₂.2⟩ (le_of_lt (lt_trans hc₁.2 hc₂.1))
  rw [heq₁, heq₂, div_le_div_iff₀ (sub_pos.mpr hax) (sub_pos.mpr hxb)] at hle
  nlinarith

private lemma integral_le_trapezoid_add_K {f f' f'' : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hd1 : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hK : ∀ x ∈ Ioo a b, -K ≤ f'' x) :
    ∫ x in a..b, f x ≤ ((f a + f b) / 2) * (b - a) + (K / 12) * (b - a) ^ 3 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  let g : ℝ → ℝ := fun x => f x + (K / 2) * x ^ 2
  let g' : ℝ → ℝ := fun x => f' x + K * x
  have hg_cont : ContinuousOn g (Icc a b) :=
    hcont.add (continuousOn_const.mul (continuousOn_id.pow 2))
  have hg_d1 : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x := by
    intro x hx
    have hq : HasDerivAt (fun t => (K / 2) * t ^ 2) (K * x) x :=
      ((hasDerivAt_pow 2 x).const_mul (K / 2)) ▸d (by ring)
    exact (hd1 x hx).fun_add hq
  have hg'_mono : MonotoneOn g' (Ioo a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo a b)
    · intro x hx
      exact ((hd2 x hx).fun_add ((hasDerivAt_id' x).const_mul K)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact ((hd2 x hx).fun_add ((hasDerivAt_id' x).const_mul K)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      have hd : HasDerivAt g' (f'' x + K) x :=
        ((hd2 x hx).fun_add ((hasDerivAt_id' x).const_mul K)) ▸d (by ring)
      rw [hd.deriv]
      linarith [hK x hx]
  have hsec := secant_bound_of_deriv_mono hlt hg_cont hg_d1 hg'_mono
  have hba_pos : 0 < b - a := sub_pos.mpr hlt
  have hpt : ∀ x ∈ Icc a b, g x ≤ (g a * (b - x) + g b * (x - a)) / (b - a) := by
    intro x hx
    rw [le_div_iff₀ hba_pos]
    exact hsec x hx
  have hint_g : IntervalIntegrable g volume a b := hg_cont.intervalIntegrable_of_Icc hab
  have hint_lin : IntervalIntegrable (fun x => (g a * (b - x) + g b * (x - a)) / (b - a)) volume a b :=
    (show Continuous (fun x => (g a * (b - x) + g b * (x - a)) / (b - a)) by fun_prop).intervalIntegrable _ _
  have hint_quad : IntervalIntegrable (fun x => (K / 2) * x ^ 2) volume a b :=
    (show Continuous (fun x => (K / 2) * x ^ 2) by fun_prop).intervalIntegrable _ _
  have hmono_int := intervalIntegral.integral_mono_on hab hint_g hint_lin hpt
  have hlin_eval : ∫ x in a..b, (g a * (b - x) + g b * (x - a)) / (b - a) =
      ((g a + g b) / 2) * (b - a) := by
    have hF : ∀ x ∈ uIcc a b, HasDerivAt
        (fun t => (g a * (b * t - t ^ 2 / 2) + g b * (t ^ 2 / 2 - a * t)) / (b - a))
        ((g a * (b - x) + g b * (x - a)) / (b - a)) x := by
      intro x _
      have h1 : HasDerivAt (fun t => b * t - t ^ 2 / 2) (b - x) x :=
        (((hasDerivAt_id' x).const_mul b).fun_sub ((hasDerivAt_pow 2 x).div_const 2)) ▸d (by ring)
      have h2 : HasDerivAt (fun t => t ^ 2 / 2 - a * t) (x - a) x :=
        (((hasDerivAt_pow 2 x).div_const 2).fun_sub ((hasDerivAt_id' x).const_mul a)) ▸d (by ring)
      exact ((h1.const_mul (g a)).fun_add (h2.const_mul (g b))).div_const (b - a)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint_lin]
    field_simp [ne_of_gt hba_pos]
    ring
  have hquad_eval : ∫ x in a..b, (K / 2) * x ^ 2 = (K / 6) * (b ^ 3 - a ^ 3) := by
    have hF : ∀ x ∈ uIcc a b, HasDerivAt (fun t => (K / 6) * t ^ 3) ((K / 2) * x ^ 2) x := by
      intro x _
      exact ((hasDerivAt_pow 3 x).const_mul (K / 6)) ▸d (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint_quad]
    ring
  have hsplit : ∫ x in a..b, g x = (∫ x in a..b, f x) + ∫ x in a..b, (K / 2) * x ^ 2 :=
    intervalIntegral.integral_add (hcont.intervalIntegrable_of_Icc hab) hint_quad
  rw [hsplit, hquad_eval, hlin_eval] at hmono_int
  have halg : ((g a + g b) / 2) * (b - a) - (K / 6) * (b ^ 3 - a ^ 3) =
      ((f a + f b) / 2) * (b - a) + (K / 12) * (b - a) ^ 3 := by
    simp only [g]; ring
  linarith


/-! ### Part 3b: g_real, gm_real, Unimodality, Second Derivatives, Antitonicity, and Hm Convexity -/

noncomputable def g_real (t x : ℝ) : ℝ :=
  if t ≤ 3 * x then 0
  else
    let U := min cR (t - 2 * x)
    (Real.log (U / x) + Real.log ((t - 2 * x) / (t - x - U))) / (x * (t - x))

noncomputable def gm_real (t_lo t_hi x : ℝ) : ℝ :=
  let tp := 2 * x + cR
  if t_hi ≤ tp then g_real t_hi x
  else if tp ≤ t_lo then g_real t_lo x
  else g_real tp x

private lemma g_real_nonneg {t x : ℝ} (hx : bR ≤ x) (hxc : x ≤ cR) : 0 ≤ g_real t x := by
  unfold g_real
  split_ifs with h1
  · exact le_rfl
  · push Not at h1
    have hxp : 0 < x := by unfold bR at hx; linarith
    have hU_ge : x ≤ min cR (t - 2 * x) := le_min hxc (by linarith)
    have hU_le : min cR (t - 2 * x) ≤ t - 2 * x := min_le_right _ _
    have hden_pos : 0 < t - x - min cR (t - 2 * x) := by linarith
    have hl1 : 0 ≤ Real.log (min cR (t - 2 * x) / x) :=
      Real.log_nonneg (by rw [one_le_div hxp]; exact hU_ge)
    have hl2 : 0 ≤ Real.log ((t - 2 * x) / (t - x - min cR (t - 2 * x))) :=
      Real.log_nonneg (by rw [one_le_div hden_pos]; linarith)
    exact div_nonneg (add_nonneg hl1 hl2) (mul_nonneg (le_of_lt hxp) (by linarith))

private lemma g_real_eq_g1 {t x : ℝ} (hxc : x ≤ cR) (ht : 2 * x + cR ≤ t) :
    g_real t x = (Real.log (cR / x) + Real.log ((t - 2 * x) / (t - x - cR))) / (x * (t - x)) := by
  unfold g_real
  dsimp only
  by_cases h3 : t ≤ 3 * x
  · have hxeq : x = cR := by linarith
    have hteq : t = 3 * cR := by linarith
    rw [if_pos h3, hxeq, hteq]
    have hc : cR ≠ 0 := by unfold cR; norm_num
    have h1 : cR / cR = 1 := div_self hc
    have h2 : (3 * cR - 2 * cR) / (3 * cR - cR - cR) = 1 := by field_simp; ring
    rw [h1, h2, Real.log_one, add_zero, zero_div]
  · rw [if_neg h3]
    have hmin : min cR (t - 2 * x) = cR := min_eq_left (by linarith)
    rw [hmin]

private lemma g_real_eq_g2 {t x : ℝ} (ht1 : 3 * x ≤ t) (ht2 : t ≤ 2 * x + cR) :
    g_real t x = 2 * Real.log ((t - 2 * x) / x) / (x * (t - x)) := by
  unfold g_real
  dsimp only
  by_cases h3 : t ≤ 3 * x
  · have hteq : t = 3 * x := le_antisymm h3 ht1
    rw [if_pos h3, hteq]
    by_cases hx0 : x = 0
    · simp [hx0]
    · have : (3 * x - 2 * x) / x = 1 := by field_simp; ring
      rw [this, Real.log_one, mul_zero, zero_div]
  · rw [if_neg h3]
    have hmin : min cR (t - 2 * x) = t - 2 * x := min_eq_right (by linarith)
    rw [hmin]
    have hsub : t - x - (t - 2 * x) = x := by ring
    rw [hsub]; ring

private lemma g_real_eq_peak {x : ℝ} (hxc : x ≤ cR) :
    g_real (2 * x + cR) x = 2 * Real.log (cR / x) / (x * (cR + x)) := by
  rw [g_real_eq_g2 (by linarith) le_rfl]
  have h1 : 2 * x + cR - 2 * x = cR := by ring
  have h2 : 2 * x + cR - x = cR + x := by ring
  rw [h1, h2]

private lemma g_real_mono_left {x t1 t2 : ℝ} (hxb : bR ≤ x) (hxc : x ≤ cR)
    (ht12 : t1 ≤ t2) (ht2 : t2 ≤ 2 * x + cR) :
    g_real t1 x ≤ g_real t2 x := by
  by_cases h3 : t1 ≤ 3 * x
  · have hg1 : g_real t1 x = 0 := by unfold g_real; rw [if_pos h3]
    rw [hg1]; exact g_real_nonneg hxb hxc
  · push Not at h3
    have hxp : 0 < x := by unfold bR at hxb; linarith
    have hcb : cR / bR < 2 := by unfold bR cR; norm_num
    let F : ℝ → ℝ := fun t => 2 * Real.log ((t - 2 * x) / x) / (x * (t - x))
    have hF_eq : ∀ t ∈ Icc t1 t2, g_real t x = F t := fun t ht =>
      g_real_eq_g2 (by linarith [ht.1]) (le_trans ht.2 ht2)
    rw [hF_eq t1 (left_mem_Icc.mpr ht12), hF_eq t2 (right_mem_Icc.mpr ht12)]
    have hderiv : ∀ t ∈ Icc t1 t2, HasDerivAt F
        (2 * ((t - x) / (t - 2 * x) - Real.log ((t - 2 * x) / x)) / (x * (t - x) ^ 2)) t := by
      intro t ht
      have ht2x : 0 < t - 2 * x := by linarith [ht.1]
      have htx : 0 < t - x := by linarith [ht.1]
      have hlog : HasDerivAt (fun s => Real.log ((s - 2 * x) / x)) (1 / (t - 2 * x)) t := by
        have hlin : HasDerivAt (fun s => (s - 2 * x) / x) (1 / x) t :=
          (((hasDerivAt_id' t).fun_sub (hasDerivAt_const t (2 * x))).div_const x) ▸d (by ring)
        exact (hlin.log (ne_of_gt (div_pos ht2x hxp))) ▸d (by field_simp)
      have hnum := hlog.const_mul 2
      have hden : HasDerivAt (fun s => x * (s - x)) x t :=
        (((hasDerivAt_id' t).fun_sub (hasDerivAt_const t x)).const_mul x) ▸d (by ring)
      exact (hnum.fun_div hden (ne_of_gt (mul_pos hxp htx))) ▸d (by field_simp)
    have hmono : MonotoneOn F (Icc t1 t2) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc t1 t2)
      · intro t ht; exact (hderiv t ht).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Icc] at ht
        exact (hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Icc] at ht
        rw [(hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).deriv]
        have ht2x : 0 < t - 2 * x := by linarith [ht.1]
        have htx : 0 < t - x := by linarith [ht.1]
        have hlog_le : Real.log ((t - 2 * x) / x) ≤ (t - 2 * x) / x - 1 :=
          Real.log_le_sub_one_of_pos (div_pos ht2x hxp)
        have hlt2 : (t - 2 * x) / x ≤ cR / bR := by
          have h1 : (t - 2 * x) / x ≤ cR / x := div_le_div_of_nonneg_right (by linarith [ht.2]) (le_of_lt hxp)
          have h2 : cR / x ≤ cR / bR := div_le_div_of_nonneg_left (by unfold cR; norm_num) (by unfold bR; norm_num) hxb
          linarith
        have hgt1 : 1 ≤ (t - x) / (t - 2 * x) := by rw [one_le_div ht2x]; linarith
        exact div_nonneg (by linarith) (by positivity)
    exact hmono (left_mem_Icc.mpr ht12) (right_mem_Icc.mpr ht12) ht12

private lemma g_real_anti_right {x t1 t2 : ℝ} (hxb : bR ≤ x) (hxc : x ≤ cR)
    (ht1 : 2 * x + cR ≤ t1) (ht12 : t1 ≤ t2) :
    g_real t2 x ≤ g_real t1 x := by
  rw [g_real_eq_g1 hxc (le_trans ht1 ht12), g_real_eq_g1 hxc ht1]
  have hxp : 0 < x := by unfold bR at hxb; linarith
  have h1p : 0 < t1 - x := by linarith
  have h2p : 0 < t2 - x := by linarith
  have hd1 : 0 < t1 - x - cR := by linarith
  have hd2 : 0 < t2 - x - cR := by linarith
  have hnum_le : Real.log (cR / x) + Real.log ((t2 - 2 * x) / (t2 - x - cR)) ≤
      Real.log (cR / x) + Real.log ((t1 - 2 * x) / (t1 - x - cR)) := by
    apply add_le_add le_rfl
    apply Real.log_le_log (div_pos (by linarith) hd2)
    rw [div_le_div_iff₀ hd2 hd1]
    nlinarith
  have hnum_nn : 0 ≤ Real.log (cR / x) + Real.log ((t2 - 2 * x) / (t2 - x - cR)) := by
    apply add_nonneg
    · exact Real.log_nonneg (by rw [one_le_div hxp]; exact hxc)
    · exact Real.log_nonneg (by rw [one_le_div hd2]; linarith)
  have hden_le : x * (t1 - x) ≤ x * (t2 - x) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hxp)
  exact le_trans (div_le_div_of_nonneg_right hnum_le (mul_nonneg (le_of_lt hxp) (le_of_lt h2p)))
    (div_le_div_of_nonneg_left (le_trans hnum_nn hnum_le) (mul_pos hxp h1p) hden_le)

private lemma g_real_le_gm_real {t_lo t_hi t x : ℝ} (hxb : bR ≤ x) (hxc : x ≤ cR)
    (ht_lo : t_lo ≤ t) (ht_hi : t ≤ t_hi) :
    g_real t x ≤ gm_real t_lo t_hi x := by
  unfold gm_real
  dsimp only
  split_ifs with h1 h2
  · exact g_real_mono_left hxb hxc ht_hi h1
  · exact g_real_anti_right hxb hxc h2 ht_lo
  · push Not at h1 h2
    by_cases ht : t ≤ 2 * x + cR
    · exact g_real_mono_left hxb hxc ht le_rfl
    · exact g_real_anti_right hxb hxc le_rfl (le_of_not_ge ht)

/-! Second-derivative bounds on the three regimes of gm_real -/

private lemma g1_integral_le_trap {t xl xr : ℝ}
    (hbl : bR ≤ xl) (hlr : xl ≤ xr) (hrc : xr ≤ cR) (ht : 2 * xr + cR ≤ t) :
    ∫ x in xl..xr, g_real t x ≤ ((g_real t xl + g_real t xr) / 2) * (xr - xl) + (55 / 12 : ℝ) * (xr - xl) ^ 3 := by
  let u : ℝ → ℝ := fun x => 1 / (x * (t - x))
  let u' : ℝ → ℝ := fun x => -(t - 2 * x) / (x * (t - x)) ^ 2
  let u'' : ℝ → ℝ := fun x => 2 * (3 * x ^ 2 - 3 * t * x + t ^ 2) / (x * (t - x)) ^ 3
  let v : ℝ → ℝ := fun x => Real.log (cR / x) + Real.log ((t - 2 * x) / (t - x - cR))
  let v' : ℝ → ℝ := fun x => -1 / x - 2 / (t - 2 * x) + 1 / (t - x - cR)
  let v'' : ℝ → ℝ := fun x => 1 / x ^ 2 - 4 / (t - 2 * x) ^ 2 + 1 / (t - x - cR) ^ 2
  have heq : ∀ x ∈ Icc xl xr, g_real t x = u x * v x := fun x hx => by
    rw [g_real_eq_g1 (le_trans hx.2 hrc) (by linarith [hx.2])]
    simp only [u, v]; ring
  have hint_eq : ∫ x in xl..xr, g_real t x = ∫ x in xl..xr, u x * v x :=
    intervalIntegral.integral_congr (fun x hx => by rw [uIcc_of_le hlr] at hx; exact heq x hx)
  rw [hint_eq, heq xl (left_mem_Icc.mpr hlr), heq xr (right_mem_Icc.mpr hlr)]
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have hc_pos : (0 : ℝ) < cR := by unfold cR; norm_num
  have hcont : ContinuousOn (fun x => u x * v x) (Icc xl xr) := by
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_
      intro x hx
      have hxp : 0 < x := by linarith [hx.1]
      have htx : 0 < t - x := by linarith [hx.2]
      exact ne_of_gt (mul_pos hxp htx)
    · refine ContinuousOn.add ?_ ?_
      · refine ContinuousOn.log (continuousOn_const.div continuousOn_id (fun x hx => by linarith [hx.1])) ?_
        intro x hx; exact ne_of_gt (div_pos hc_pos (by linarith [hx.1]))
      · refine ContinuousOn.log ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).div
          ((continuousOn_const.sub continuousOn_id).sub continuousOn_const) (fun x hx => by linarith [hx.1, hx.2])) ?_
        intro x hx; exact ne_of_gt (div_pos (by linarith [hx.2]) (by linarith [hx.1, hx.2]))
  have hu_d1 : ∀ x ∈ Ioo xl xr, HasDerivAt u (u' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have htx : 0 < t - x := by linarith [hx.2]
    have hd : HasDerivAt (fun s => s * (t - s)) (t - 2 * x) x :=
      ((hasDerivAt_id' x).fun_mul ((hasDerivAt_const x t).fun_sub (hasDerivAt_id' x))) ▸d (by ring)
    exact ((hasDerivAt_const x (1 : ℝ)).fun_div hd (ne_of_gt (mul_pos hxp htx))) ▸d
      (by simp only [u']; field_simp; ring)
  have hu_d2 : ∀ x ∈ Ioo xl xr, HasDerivAt u' (u'' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have htx : 0 < t - x := by linarith [hx.2]
    have hnum : HasDerivAt (fun s => -(t - 2 * s)) 2 x :=
      (((hasDerivAt_const x t).fun_sub ((hasDerivAt_id' x).const_mul 2)).fun_neg) ▸d (by ring)
    have hden : HasDerivAt (fun s => (s * (t - s)) ^ 2) (2 * (x * (t - x)) * (t - 2 * x)) x := by
      have hd : HasDerivAt (fun s => s * (t - s)) (t - 2 * x) x :=
        ((hasDerivAt_id' x).fun_mul ((hasDerivAt_const x t).fun_sub (hasDerivAt_id' x))) ▸d (by ring)
      exact (hd.fun_pow 2) ▸d (by ring)
    exact (hnum.fun_div hden (ne_of_gt (pow_pos (mul_pos hxp htx) 2))) ▸d
      (by simp only [u'']; field_simp; ring)
  have hv_d1 : ∀ x ∈ Ioo xl xr, HasDerivAt v (v' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have ht2x : 0 < t - 2 * x := by linarith [hx.2]
    have htxc : 0 < t - x - cR := by linarith [hx.1, hx.2]
    have hl1 : HasDerivAt (fun s => Real.log (cR / s)) (-1 / x) x := by
      have hq : HasDerivAt (fun s => cR / s) (-cR / x ^ 2) x :=
        ((hasDerivAt_const x cR).fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by field_simp; ring)
      exact (hq.log (ne_of_gt (div_pos hc_pos hxp))) ▸d (by field_simp)
    have hl2 : HasDerivAt (fun s => Real.log ((t - 2 * s) / (t - s - cR)))
        (-2 / (t - 2 * x) + 1 / (t - x - cR)) x := by
      have h1 : HasDerivAt (fun s => t - 2 * s) (-2) x :=
        ((hasDerivAt_const x t).fun_sub ((hasDerivAt_id' x).const_mul 2)) ▸d (by ring)
      have h2 : HasDerivAt (fun s => t - s - cR) (-1) x :=
        (((hasDerivAt_const x t).fun_sub (hasDerivAt_id' x)).fun_sub (hasDerivAt_const x cR)) ▸d (by ring)
      have hq := h1.fun_div h2 (ne_of_gt htxc)
      exact (hq.log (ne_of_gt (div_pos ht2x htxc))) ▸d (by field_simp; ring)
    exact (hl1.fun_add hl2) ▸d (by simp only [v']; ring)
  have hv_d2 : ∀ x ∈ Ioo xl xr, HasDerivAt v' (v'' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have ht2x : 0 < t - 2 * x := by linarith [hx.2]
    have htxc : 0 < t - x - cR := by linarith [hx.1, hx.2]
    have h1 : HasDerivAt (fun s => -1 / s) (1 / x ^ 2) x :=
      ((hasDerivAt_const x (-1 : ℝ)).fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by field_simp; ring)
    have h2 : HasDerivAt (fun s => 2 / (t - 2 * s)) (4 / (t - 2 * x) ^ 2) x := by
      have hd : HasDerivAt (fun s => t - 2 * s) (-2) x :=
        ((hasDerivAt_const x t).fun_sub ((hasDerivAt_id' x).const_mul 2)) ▸d (by ring)
      exact ((hasDerivAt_const x (2 : ℝ)).fun_div hd (ne_of_gt ht2x)) ▸d (by field_simp; ring)
    have h3 : HasDerivAt (fun s => 1 / (t - s - cR)) (1 / (t - x - cR) ^ 2) x := by
      have hd : HasDerivAt (fun s => t - s - cR) (-1) x :=
        (((hasDerivAt_const x t).fun_sub (hasDerivAt_id' x)).fun_sub (hasDerivAt_const x cR)) ▸d (by ring)
      exact ((hasDerivAt_const x (1 : ℝ)).fun_div hd (ne_of_gt htxc)) ▸d (by field_simp; ring)
    exact (h1.fun_sub h2).fun_add h3
  apply integral_le_trapezoid_add_K (f' := fun x => u' x * v x + u x * v' x)
    (f'' := fun x => u'' x * v x + 2 * u' x * v' x + u x * v'' x) hlr hcont
  · intro x hx
    exact (hu_d1 x hx).fun_mul (hv_d1 x hx)
  · intro x hx
    have h1 := (hu_d2 x hx).fun_mul (hv_d1 x hx)
    have h2 := (hu_d1 x hx).fun_mul (hv_d2 x hx)
    exact (h1.fun_add h2) ▸d (by ring)
  · intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have htx : 0 < t - x := by linarith [hx.2]
    have ht2x : cR ≤ t - 2 * x := by linarith [hx.2]
    have htxc : x ≤ t - x - cR := by linarith [hx.2]
    have hu_nn : 0 ≤ u x := by simp only [u]; positivity
    have hu_le : u x ≤ 1 / (bR * (bR + cR)) := by
      simp only [u]
      exact div_le_div_of_nonneg_left zero_le_one (mul_pos hb_pos (by linarith))
        (mul_le_mul (by linarith [hx.1]) (by linarith [hx.1, hx.2]) (by linarith) (le_of_lt hxp))
    have hu'_np : u' x ≤ 0 := by
      simp only [u']; exact div_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (by positivity)
    have hu''_nn : 0 ≤ u'' x := by
      simp only [u'']
      have hquad : 0 ≤ 3 * x ^ 2 - 3 * t * x + t ^ 2 := by nlinarith
      exact div_nonneg (by linarith) (pow_nonneg (mul_nonneg (le_of_lt hxp) (le_of_lt htx)) 3)
    have hv_nn : 0 ≤ v x := by
      simp only [v]
      apply add_nonneg
      · exact Real.log_nonneg (by rw [one_le_div hxp]; linarith [hx.2])
      · exact Real.log_nonneg (by rw [one_le_div (by linarith)]; linarith [hx.2])
    have hv'_np : v' x ≤ 0 := by
      simp only [v', neg_div]
      have h1 : 1 / (t - x - cR) ≤ 1 / x := div_le_div_of_nonneg_left zero_le_one hxp htxc
      have h2 : 0 ≤ 2 / (t - 2 * x) := div_nonneg (by norm_num) (by linarith)
      linarith
    have hv''_ge : -(4 / cR ^ 2) ≤ v'' x := by
      simp only [v'']
      have h1 : 0 ≤ 1 / x ^ 2 := by positivity
      have h2 : 0 ≤ 1 / (t - x - cR) ^ 2 := by positivity
      have h3 : 4 / (t - 2 * x) ^ 2 ≤ 4 / cR ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (pow_pos hc_pos 2) (by nlinarith)
      linarith
    have hprod1 : 0 ≤ u'' x * v x := mul_nonneg hu''_nn hv_nn
    have hprod2 : 0 ≤ 2 * u' x * v' x := by nlinarith
    have hprod3 : -(4 / (bR * (bR + cR) * cR ^ 2)) ≤ u x * v'' x := by
      have h1 : u x * -(4 / cR ^ 2) ≤ u x * v'' x := mul_le_mul_of_nonneg_left hv''_ge hu_nn
      have h2 : (1 / (bR * (bR + cR))) * -(4 / cR ^ 2) ≤ u x * -(4 / cR ^ 2) := by
        have : u x * (4 / cR ^ 2) ≤ (1 / (bR * (bR + cR))) * (4 / cR ^ 2) :=
          mul_le_mul_of_nonneg_right hu_le (by positivity)
        linarith
      have h3 : (1 / (bR * (bR + cR))) * -(4 / cR ^ 2) = -(4 / (bR * (bR + cR) * cR ^ 2)) := by field_simp
      linarith
    have hnum55 : 4 / (bR * (bR + cR) * cR ^ 2) ≤ 55 := by unfold bR cR; norm_num
    linarith

private lemma gpeak_integral_le_trap {xl xr : ℝ}
    (hbl : bR ≤ xl) (hlr : xl ≤ xr) (hrc : xr ≤ cR) :
    ∫ x in xl..xr, g_real (2 * x + cR) x ≤
      ((g_real (2 * xl + cR) xl + g_real (2 * xr + cR) xr) / 2) * (xr - xl) := by
  let u : ℝ → ℝ := fun x => 2 / (x * (cR + x))
  let u' : ℝ → ℝ := fun x => -2 * (cR + 2 * x) / (x * (cR + x)) ^ 2
  let u'' : ℝ → ℝ := fun x => 4 * (cR ^ 2 + 3 * cR * x + 3 * x ^ 2) / (x * (cR + x)) ^ 3
  let v : ℝ → ℝ := fun x => Real.log (cR / x)
  let v' : ℝ → ℝ := fun x => -1 / x
  let v'' : ℝ → ℝ := fun x => 1 / x ^ 2
  have heq : ∀ x ∈ Icc xl xr, g_real (2 * x + cR) x = u x * v x := fun x hx => by
    rw [g_real_eq_peak (le_trans hx.2 hrc)]; simp only [u, v]; ring
  have hint_eq : ∫ x in xl..xr, g_real (2 * x + cR) x = ∫ x in xl..xr, u x * v x :=
    intervalIntegral.integral_congr (fun x hx => by rw [uIcc_of_le hlr] at hx; exact heq x hx)
  rw [hint_eq, heq xl (left_mem_Icc.mpr hlr), heq xr (right_mem_Icc.mpr hlr)]
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have hc_pos : (0 : ℝ) < cR := by unfold cR; norm_num
  have hcont : ContinuousOn (fun x => u x * v x) (Icc xl xr) := by
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_const.div (continuousOn_id.mul (continuousOn_const.add continuousOn_id)) ?_
      intro x hx; exact ne_of_gt (mul_pos (by linarith [hx.1]) (by linarith [hx.1]))
    · refine ContinuousOn.log (continuousOn_const.div continuousOn_id (fun x hx => by linarith [hx.1])) ?_
      intro x hx; exact ne_of_gt (div_pos hc_pos (by linarith [hx.1]))
  have hu_d1 : ∀ x ∈ Ioo xl xr, HasDerivAt u (u' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have hd : HasDerivAt (fun s => s * (cR + s)) (cR + 2 * x) x :=
      ((hasDerivAt_id' x).fun_mul ((hasDerivAt_const x cR).fun_add (hasDerivAt_id' x))) ▸d (by ring)
    exact ((hasDerivAt_const x (2 : ℝ)).fun_div hd (ne_of_gt (mul_pos hxp (by linarith)))) ▸d
      (by simp only [u']; field_simp; ring)
  have hu_d2 : ∀ x ∈ Ioo xl xr, HasDerivAt u' (u'' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have hnum : HasDerivAt (fun s => -2 * (cR + 2 * s)) (-4) x :=
      (((hasDerivAt_const x cR).fun_add ((hasDerivAt_id' x).const_mul 2)).const_mul (-2)) ▸d (by ring)
    have hden : HasDerivAt (fun s => (s * (cR + s)) ^ 2) (2 * (x * (cR + x)) * (cR + 2 * x)) x := by
      have hd : HasDerivAt (fun s => s * (cR + s)) (cR + 2 * x) x :=
        ((hasDerivAt_id' x).fun_mul ((hasDerivAt_const x cR).fun_add (hasDerivAt_id' x))) ▸d (by ring)
      exact (hd.fun_pow 2) ▸d (by ring)
    exact (hnum.fun_div hden (ne_of_gt (pow_pos (mul_pos hxp (by linarith)) 2))) ▸d
      (by simp only [u'']; field_simp; ring)
  have hv_d1 : ∀ x ∈ Ioo xl xr, HasDerivAt v (v' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have hq : HasDerivAt (fun s => cR / s) (-cR / x ^ 2) x :=
      ((hasDerivAt_const x cR).fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by field_simp; ring)
    exact (hq.log (ne_of_gt (div_pos hc_pos hxp))) ▸d (by simp only [v']; field_simp)
  have hv_d2 : ∀ x ∈ Ioo xl xr, HasDerivAt v' (v'' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    exact ((hasDerivAt_const x (-1 : ℝ)).fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d
      (by simp only [v'']; field_simp; ring)
  have htr := integral_le_trapezoid_add_K (f' := fun x => u' x * v x + u x * v' x)
    (f'' := fun x => u'' x * v x + 2 * u' x * v' x + u x * v'' x) (K := 0) hlr hcont
    (fun x hx => (hu_d1 x hx).fun_mul (hv_d1 x hx))
    (fun x hx => by
      have h1 := (hu_d2 x hx).fun_mul (hv_d1 x hx)
      have h2 := (hu_d1 x hx).fun_mul (hv_d2 x hx)
      exact (h1.fun_add h2) ▸d (by ring))
    (fun x hx => by
      have hxp : 0 < x := by linarith [hx.1]
      have hv_nn : 0 ≤ v x := Real.log_nonneg (by rw [one_le_div hxp]; linarith [hx.2])
      have hu_nn : 0 ≤ u x := by simp only [u]; positivity
      have hu'_np : u' x ≤ 0 := by
        simp only [u']; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      have hu''_nn : 0 ≤ u'' x := by simp only [u'']; positivity
      have hv'_np : v' x ≤ 0 := by simp only [v']; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (le_of_lt hxp)
      have hv''_nn : 0 ≤ v'' x := by simp only [v'']; positivity
      have h1 : 0 ≤ u'' x * v x := mul_nonneg hu''_nn hv_nn
      have h2 : 0 ≤ 2 * u' x * v' x := by nlinarith
      have h3 : 0 ≤ u x * v'' x := mul_nonneg hu_nn hv''_nn
      linarith)
  simpa using htr

private lemma g2_integral_le_trap {t xl xr : ℝ}
    (hbl : bR ≤ xl) (hlr : xl ≤ xr) (_hrc : xr ≤ cR)
    (ht1 : 3 * xr ≤ t) (ht2 : t ≤ 2 * xl + cR) :
    ∫ x in xl..xr, g_real t x ≤ ((g_real t xl + g_real t xr) / 2) * (xr - xl) + (110 / 12 : ℝ) * (xr - xl) ^ 3 := by
  let u : ℝ → ℝ := fun x => 2 / (x * (t - x))
  let u' : ℝ → ℝ := fun x => -2 * (t - 2 * x) / (x * (t - x)) ^ 2
  let u'' : ℝ → ℝ := fun x => 4 * (3 * x ^ 2 - 3 * t * x + t ^ 2) / (x * (t - x)) ^ 3
  let v : ℝ → ℝ := fun x => Real.log ((t - 2 * x) / x)
  let v' : ℝ → ℝ := fun x => -2 / (t - 2 * x) - 1 / x
  let v'' : ℝ → ℝ := fun x => -4 / (t - 2 * x) ^ 2 + 1 / x ^ 2
  have heq : ∀ x ∈ Icc xl xr, g_real t x = u x * v x := fun x hx => by
    rw [g_real_eq_g2 (by linarith [hx.2]) (by linarith [hx.1])]
    simp only [u, v]; ring
  have hint_eq : ∫ x in xl..xr, g_real t x = ∫ x in xl..xr, u x * v x :=
    intervalIntegral.integral_congr (fun x hx => by rw [uIcc_of_le hlr] at hx; exact heq x hx)
  rw [hint_eq, heq xl (left_mem_Icc.mpr hlr), heq xr (right_mem_Icc.mpr hlr)]
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have hcont : ContinuousOn (fun x => u x * v x) (Icc xl xr) := by
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_
      intro x hx; exact ne_of_gt (mul_pos (by linarith [hx.1]) (by linarith [hx.1, hx.2]))
    · refine ContinuousOn.log ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).div
        continuousOn_id (fun x hx => by linarith [hx.1])) ?_
      intro x hx; exact ne_of_gt (div_pos (by linarith [hx.1, hx.2]) (by linarith [hx.1]))
  have hu_d1 : ∀ x ∈ Ioo xl xr, HasDerivAt u (u' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have htx : 0 < t - x := by linarith [hx.1, hx.2]
    have hd : HasDerivAt (fun s => s * (t - s)) (t - 2 * x) x :=
      ((hasDerivAt_id' x).fun_mul ((hasDerivAt_const x t).fun_sub (hasDerivAt_id' x))) ▸d (by ring)
    exact ((hasDerivAt_const x (2 : ℝ)).fun_div hd (ne_of_gt (mul_pos hxp htx))) ▸d
      (by simp only [u']; field_simp; ring)
  have hu_d2 : ∀ x ∈ Ioo xl xr, HasDerivAt u' (u'' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have htx : 0 < t - x := by linarith [hx.1, hx.2]
    have hnum : HasDerivAt (fun s => -2 * (t - 2 * s)) 4 x :=
      (((hasDerivAt_const x t).fun_sub ((hasDerivAt_id' x).const_mul 2)).const_mul (-2)) ▸d (by ring)
    have hden : HasDerivAt (fun s => (s * (t - s)) ^ 2) (2 * (x * (t - x)) * (t - 2 * x)) x := by
      have hd : HasDerivAt (fun s => s * (t - s)) (t - 2 * x) x :=
        ((hasDerivAt_id' x).fun_mul ((hasDerivAt_const x t).fun_sub (hasDerivAt_id' x))) ▸d (by ring)
      exact (hd.fun_pow 2) ▸d (by ring)
    exact (hnum.fun_div hden (ne_of_gt (pow_pos (mul_pos hxp htx) 2))) ▸d
      (by simp only [u'']; field_simp; ring)
  have hv_d1 : ∀ x ∈ Ioo xl xr, HasDerivAt v (v' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have ht2x : 0 < t - 2 * x := by linarith [hx.1, hx.2]
    have hq : HasDerivAt (fun s => (t - 2 * s) / s) (-t / x ^ 2) x := by
      have h1 : HasDerivAt (fun s => t - 2 * s) (-2) x :=
        ((hasDerivAt_const x t).fun_sub ((hasDerivAt_id' x).const_mul 2)) ▸d (by ring)
      exact (h1.fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by field_simp; ring)
    have ht2x' : t - x * 2 ≠ 0 := by linarith
    exact (hq.log (ne_of_gt (div_pos ht2x hxp))) ▸d (by simp only [v']; field_simp [ne_of_gt ht2x, ht2x', ne_of_gt hxp]; ring)
  have hv_d2 : ∀ x ∈ Ioo xl xr, HasDerivAt v' (v'' x) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have ht2x : 0 < t - 2 * x := by linarith [hx.1, hx.2]
    have h1 : HasDerivAt (fun s => -2 / (t - 2 * s)) (-4 / (t - 2 * x) ^ 2) x := by
      have hd : HasDerivAt (fun s => t - 2 * s) (-2) x :=
        ((hasDerivAt_const x t).fun_sub ((hasDerivAt_id' x).const_mul 2)) ▸d (by ring)
      exact ((hasDerivAt_const x (-2 : ℝ)).fun_div hd (ne_of_gt ht2x)) ▸d (by field_simp; ring)
    have h2 : HasDerivAt (fun s => 1 / s) (-1 / x ^ 2) x :=
      ((hasDerivAt_const x (1 : ℝ)).fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by field_simp; ring)
    exact (h1.fun_sub h2) ▸d (by simp only [v'']; ring)
  apply integral_le_trapezoid_add_K (f' := fun x => u' x * v x + u x * v' x)
    (f'' := fun x => u'' x * v x + 2 * u' x * v' x + u x * v'' x) hlr hcont
  · intro x hx; exact (hu_d1 x hx).fun_mul (hv_d1 x hx)
  · intro x hx
    have h1 := (hu_d2 x hx).fun_mul (hv_d1 x hx)
    have h2 := (hu_d1 x hx).fun_mul (hv_d2 x hx)
    exact (h1.fun_add h2) ▸d (by ring)
  · intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have htx : 2 * x < t - x := by linarith [hx.2]
    have ht2x : x < t - 2 * x := by linarith [hx.2]
    have hu_nn : 0 ≤ u x := by simp only [u]; exact div_nonneg (by norm_num) (mul_nonneg (le_of_lt hxp) (by linarith))
    have hu_le : u x ≤ 1 / x ^ 2 := by
      simp only [u]
      rw [div_le_div_iff₀ (mul_pos hxp (by linarith)) (pow_pos hxp 2)]
      nlinarith
    have hu'_np : u' x ≤ 0 := by
      simp only [u']; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have hu''_nn : 0 ≤ u'' x := by
      simp only [u'']
      have hquad : 0 ≤ 3 * x ^ 2 - 3 * t * x + t ^ 2 := by nlinarith
      exact div_nonneg (by linarith) (pow_nonneg (mul_nonneg (le_of_lt hxp) (by linarith)) 3)
    have hv_nn : 0 ≤ v x := Real.log_nonneg (by rw [one_le_div hxp]; linarith)
    have hv'_np : v' x ≤ 0 := by
      simp only [v', neg_div]
      have h1 : 0 ≤ 2 / (t - 2 * x) := div_nonneg (by norm_num) (by linarith)
      have h2 : 0 ≤ 1 / x := div_nonneg zero_le_one (le_of_lt hxp)
      linarith
    have hv''_ge : -(3 / x ^ 2) ≤ v'' x := by
      simp only [v'', neg_div]
      have h4 : 4 / (t - 2 * x) ^ 2 ≤ 4 / x ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (pow_pos hxp 2) (by nlinarith)
      have hsub : -(4 / x ^ 2) + 1 / x ^ 2 = -(3 / x ^ 2) := by ring
      linarith
    have hprod1 : 0 ≤ u'' x * v x := mul_nonneg hu''_nn hv_nn
    have hprod2 : 0 ≤ 2 * u' x * v' x := by nlinarith
    have hprod3 : -(3 / bR ^ 4) ≤ u x * v'' x := by
      have h1 : u x * -(3 / x ^ 2) ≤ u x * v'' x := mul_le_mul_of_nonneg_left hv''_ge hu_nn
      have h2 : (1 / x ^ 2) * -(3 / x ^ 2) ≤ u x * -(3 / x ^ 2) := by
        have : u x * (3 / x ^ 2) ≤ (1 / x ^ 2) * (3 / x ^ 2) :=
          mul_le_mul_of_nonneg_right hu_le (by positivity)
        linarith
      have h3 : (1 / x ^ 2) * -(3 / x ^ 2) = -(3 / x ^ 4) := by field_simp
      have h4 : 3 / x ^ 4 ≤ 3 / bR ^ 4 :=
        div_le_div_of_nonneg_left (by norm_num) (pow_pos hb_pos 4)
          (pow_le_pow_left₀ (le_of_lt hb_pos) (by linarith [hx.1]) 4)
      linarith
    have hnum110 : 3 / bR ^ 4 ≤ 110 := by unfold bR; norm_num
    linarith

private lemma ae_ne_const (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  simp [ae_iff, measure_singleton]

private lemma g_real_continuousOn : ContinuousOn (fun p : ℝ × ℝ => g_real p.1 p.2) (Set.univ ×ˢ Icc bR cR) := by
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have hS1_cl : IsClosed {p : ℝ × ℝ | p.1 ≤ 3 * p.2} :=
    isClosed_le continuous_fst (continuous_const.mul continuous_snd)
  have hS2_cl : IsClosed {p : ℝ × ℝ | 3 * p.2 ≤ p.1} :=
    isClosed_le (continuous_const.mul continuous_snd) continuous_fst
  let g2f : ℝ × ℝ → ℝ := fun p =>
    let U := min cR (p.1 - 2 * p.2)
    (Real.log (U / p.2) + Real.log ((p.1 - 2 * p.2) / (p.1 - p.2 - U))) / (p.2 * (p.1 - p.2))
  have hcont2 : ContinuousOn g2f ((Set.univ ×ˢ Icc bR cR) ∩ {p : ℝ × ℝ | 3 * p.2 ≤ p.1}) := by
    rintro ⟨t, x⟩ ⟨⟨_, hxb, hxc⟩, h3⟩
    simp only [mem_ofPred_eq] at h3
    dsimp only at hxb hxc h3
    have hxp : 0 < x := lt_of_lt_of_le hb_pos hxb
    have ht2x : x ≤ t - 2 * x := by linarith
    have htx : 2 * x ≤ t - x := by linarith
    have hU_ge : x ≤ min cR (t - 2 * x) := le_min hxc ht2x
    have hU_le : min cR (t - 2 * x) ≤ t - 2 * x := min_le_right _ _
    have hden_pos : 0 < t - x - min cR (t - 2 * x) := by linarith
    have hU_cont : ContinuousAt (fun p : ℝ × ℝ => min cR (p.1 - 2 * p.2)) (t, x) :=
      continuousAt_const.min (continuousAt_fst.sub (continuousAt_const.mul continuousAt_snd))
    have hl1 : ContinuousAt (fun p : ℝ × ℝ => Real.log (min cR (p.1 - 2 * p.2) / p.2)) (t, x) :=
      (hU_cont.div continuousAt_snd (ne_of_gt hxp)).log (ne_of_gt (div_pos (lt_of_lt_of_le hxp hU_ge) hxp))
    have hl2 : ContinuousAt (fun p : ℝ × ℝ => Real.log ((p.1 - 2 * p.2) / (p.1 - p.2 - min cR (p.1 - 2 * p.2)))) (t, x) :=
      ((continuousAt_fst.sub (continuousAt_const.mul continuousAt_snd)).div
        ((continuousAt_fst.sub continuousAt_snd).sub hU_cont) (ne_of_gt hden_pos)).log
        (ne_of_gt (div_pos (lt_of_lt_of_le hxp ht2x) hden_pos))
    have hden : ContinuousAt (fun p : ℝ × ℝ => p.2 * (p.1 - p.2)) (t, x) :=
      continuousAt_snd.mul (continuousAt_fst.sub continuousAt_snd)
    exact ((hl1.add hl2).div hden (ne_of_gt (mul_pos hxp (by linarith)))).continuousWithinAt
  have h1 : ContinuousOn (fun p : ℝ × ℝ => g_real p.1 p.2) ((Set.univ ×ˢ Icc bR cR) ∩ {p : ℝ × ℝ | p.1 ≤ 3 * p.2}) := by
    refine (continuousOn_const (c := (0 : ℝ))).congr (fun p hp => ?_)
    unfold g_real; rw [if_pos (Set.mem_ofPred_eq.mp hp.2)]
  have h2 : ContinuousOn (fun p : ℝ × ℝ => g_real p.1 p.2) ((Set.univ ×ˢ Icc bR cR) ∩ {p : ℝ × ℝ | 3 * p.2 ≤ p.1}) := by
    refine hcont2.congr (fun p hp => ?_)
    unfold g_real
    dsimp only [g2f]
    split_ifs with hle
    · have heq : p.1 = 3 * p.2 := le_antisymm hle hp.2
      have hxp : 0 < p.2 := lt_of_lt_of_le hb_pos hp.1.2.1
      have hmin : min cR (p.1 - 2 * p.2) = p.2 := by
        rw [heq]; have : 3 * p.2 - 2 * p.2 = p.2 := by ring
        rw [this]; exact min_eq_right hp.1.2.2
      rw [hmin, heq]
      have hsub1 : (3 * p.2 - 2 * p.2) = p.2 := by ring
      have hsub2 : 3 * p.2 - p.2 - p.2 = p.2 := by ring
      rw [hsub1, hsub2, div_self (ne_of_gt hxp), Real.log_one, add_zero, zero_div]
    · rfl
  have hun : (Set.univ ×ˢ Icc bR cR : Set (ℝ × ℝ)) =
      ((Set.univ ×ˢ Icc bR cR) ∩ {p | p.1 ≤ 3 * p.2}) ∪ ((Set.univ ×ˢ Icc bR cR) ∩ {p | 3 * p.2 ≤ p.1}) := by
    ext p; simp only [Set.mem_union, Set.mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hp; rcases le_total p.1 (3 * p.2) with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  rw [hun]
  have hS_cl : IsClosed (Set.univ ×ˢ Icc bR cR : Set (ℝ × ℝ)) := isClosed_univ.prod isClosed_Icc
  exact h1.union_of_isClosed h2 (hS_cl.inter hS1_cl) (hS_cl.inter hS2_cl)


private lemma gm_real_nonneg {t_lo t_hi x : ℝ} (hxb : bR ≤ x) (hxc : x ≤ cR) :
    0 ≤ gm_real t_lo t_hi x := by
  unfold gm_real; dsimp only; split_ifs <;> exact g_real_nonneg hxb hxc

private lemma g_real_anti_x_g1 {t x y : ℝ} (hxb : bR ≤ x) (hxy : x ≤ y) (hyc : y ≤ cR)
    (ht : 2 * y + cR ≤ t) : g_real t y ≤ g_real t x := by
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  have h2bc : 2 * cR < 2 * bR + cR := by unfold bR cR; norm_num
  have hxp : 0 < x := lt_of_lt_of_le hb_pos hxb
  have hyp : 0 < y := lt_of_lt_of_le hxp hxy
  rw [g_real_eq_g1 hyc ht, g_real_eq_g1 (le_trans hxy hyc) (by linarith)]
  have htx : 0 < t - x := by linarith
  have hty : 0 < t - y := by linarith
  have hdx : 0 < t - x - cR := by linarith
  have hdy : 0 < t - y - cR := by linarith
  have hl1 : Real.log (cR / y) ≤ Real.log (cR / x) :=
    Real.log_le_log (div_pos (lt_of_lt_of_le hyp hyc) hyp)
      (div_le_div_of_nonneg_left (le_of_lt (lt_of_lt_of_le hyp hyc)) hxp hxy)
  have hl2 : Real.log ((t - 2 * y) / (t - y - cR)) ≤ Real.log ((t - 2 * x) / (t - x - cR)) := by
    apply Real.log_le_log (div_pos (by linarith) hdy)
    rw [div_le_div_iff₀ hdy hdx]
    have ht2c : 0 ≤ t - 2 * cR := by linarith
    nlinarith
  have hnum_nonneg : 0 ≤ Real.log (cR / y) + Real.log ((t - 2 * y) / (t - y - cR)) := by
    have h1 : 0 ≤ Real.log (cR / y) := Real.log_nonneg (by rw [one_le_div hyp]; exact hyc)
    have h2 : 0 ≤ Real.log ((t - 2 * y) / (t - y - cR)) :=
      Real.log_nonneg (by rw [one_le_div hdy]; linarith)
    linarith
  have hden_le : x * (t - x) ≤ y * (t - y) := by nlinarith
  exact le_trans (div_le_div_of_nonneg_right (add_le_add hl1 hl2) (le_of_lt (mul_pos hyp hty)))
    (div_le_div_of_nonneg_left (by linarith) (mul_pos hxp htx) hden_le)

private lemma g_real_anti_x_peak {x y : ℝ} (hxb : bR ≤ x) (hxy : x ≤ y) (hyc : y ≤ cR) :
    g_real (2 * y + cR) y ≤ g_real (2 * x + cR) x := by
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have hxp : 0 < x := lt_of_lt_of_le hb_pos hxb
  have hyp : 0 < y := lt_of_lt_of_le hxp hxy
  have hcp : 0 < cR := lt_of_lt_of_le hyp hyc
  rw [g_real_eq_peak hyc, g_real_eq_peak (le_trans hxy hyc)]
  have hl : Real.log (cR / y) ≤ Real.log (cR / x) :=
    Real.log_le_log (div_pos hcp hyp) (div_le_div_of_nonneg_left (le_of_lt hcp) hxp hxy)
  have hl0 : 0 ≤ Real.log (cR / y) := Real.log_nonneg (by rw [one_le_div hyp]; exact hyc)
  have hden_le : x * (cR + x) ≤ y * (cR + y) := by nlinarith
  exact le_trans (div_le_div_of_nonneg_right (by linarith) (le_of_lt (mul_pos hyp (by linarith))))
    (div_le_div_of_nonneg_left (by linarith) (mul_pos hxp (by linarith)) hden_le)

private lemma g_real_anti_x_g2 {t x y : ℝ} (hxb : bR ≤ x) (hxy : x ≤ y) (hyc : y ≤ cR)
    (ht : t ≤ 2 * x + cR) : g_real t y ≤ g_real t x := by
  by_cases h3y : t ≤ 3 * y
  · have : g_real t y = 0 := by unfold g_real; rw [if_pos h3y]
    rw [this]; exact g_real_nonneg hxb (le_trans hxy hyc)
  · push Not at h3y
    have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
    have hxp : 0 < x := lt_of_lt_of_le hb_pos hxb
    have hyp : 0 < y := lt_of_lt_of_le hxp hxy
    rw [g_real_eq_g2 (le_of_lt h3y) (by linarith), g_real_eq_g2 (by linarith) ht]
    have htx : 0 < t - x := by linarith
    have hty : 0 < t - y := by linarith
    have hl : Real.log ((t - 2 * y) / y) ≤ Real.log ((t - 2 * x) / x) := by
      apply Real.log_le_log (div_pos (by linarith) hyp)
      rw [div_le_div_iff₀ hyp hxp]; nlinarith
    have hl0 : 0 ≤ Real.log ((t - 2 * y) / y) :=
      Real.log_nonneg (by rw [one_le_div hyp]; linarith)
    have hden_le : x * (t - x) ≤ y * (t - y) := by nlinarith
    exact le_trans (div_le_div_of_nonneg_right (by linarith) (le_of_lt (mul_pos hyp hty)))
      (div_le_div_of_nonneg_left (by linarith) (mul_pos hxp htx) hden_le)

private lemma gm_real_antitone {t_lo t_hi x y : ℝ} (hlo : t_lo ≤ t_hi)
    (hxb : bR ≤ x) (hxy : x ≤ y) (hyc : y ≤ cR) :
    gm_real t_lo t_hi y ≤ gm_real t_lo t_hi x := by
  unfold gm_real; dsimp only
  split_ifs with hy1 hx1 hx2 hy2 hx1' hx2' hy2' hx1''
  · exact g_real_anti_x_g2 hxb hxy hyc hx1
  · -- 2*x + cR ≤ t_lo ≤ t_hi ≤ 2*y + cR
    set m1 := (t_lo - cR) / 2
    set m2 := (t_hi - cR) / 2
    have hxm1 : x ≤ m1 := by simp only [m1]; linarith
    have hm12 : m1 ≤ m2 := by simp only [m1, m2]; linarith
    have hm2y : m2 ≤ y := by simp only [m2]; linarith
    have h1 := g_real_anti_x_g2 (t := t_hi) (le_trans hxb (le_trans hxm1 hm12)) hm2y hyc (by simp only [m2]; linarith)
    have h2 := g_real_anti_x_peak (le_trans hxb hxm1) hm12 (le_trans hm2y hyc)
    have h3 := g_real_anti_x_g1 (t := t_lo) hxb hxm1 (le_trans hm12 (le_trans hm2y hyc)) (by simp only [m1]; linarith)
    have heq1 : 2 * m1 + cR = t_lo := by simp only [m1]; ring
    have heq2 : 2 * m2 + cR = t_hi := by simp only [m2]; ring
    rw [heq1, heq2] at h2; exact le_trans h1 (le_trans h2 h3)
  · set m2 := (t_hi - cR) / 2
    have hxm2 : x ≤ m2 := by simp only [m2]; linarith
    have hm2y : m2 ≤ y := by simp only [m2]; linarith
    have h1 := g_real_anti_x_g2 (t := t_hi) (le_trans hxb hxm2) hm2y hyc (by simp only [m2]; linarith)
    have h2 := g_real_anti_x_peak hxb hxm2 (le_trans hm2y hyc)
    have heq2 : 2 * m2 + cR = t_hi := by simp only [m2]; ring
    rw [heq2] at h2; exact le_trans h1 h2
  · linarith
  · exact g_real_anti_x_g1 hxb hxy hyc hy2
  · linarith
  · linarith
  · set m1 := (t_lo - cR) / 2
    have hxm1 : x ≤ m1 := by simp only [m1]; linarith
    have hm1y : m1 ≤ y := by simp only [m1]; linarith
    have h1 := g_real_anti_x_peak (le_trans hxb hxm1) hm1y hyc
    have h2 := g_real_anti_x_g1 (t := t_lo) hxb hxm1 (le_trans hm1y hyc) (by simp only [m1]; linarith)
    have heq1 : 2 * m1 + cR = t_lo := by simp only [m1]; ring
    rw [heq1] at h1; exact le_trans h1 h2
  · exact g_real_anti_x_peak hxb hxy hyc

private lemma Hm_convex_linear_le {t_lo t_hi yr yr1 x1 : ℝ}
    (hlo : t_lo ≤ t_hi) (hbr : bR ≤ yr) (h1 : yr ≤ x1) (h2 : x1 ≤ yr1) (hrc : yr1 ≤ cR)
    (hpos : 0 < yr1 - yr) :
    ∫ x2 in x1..cR, gm_real t_lo t_hi x2 ≤
      ((yr1 - x1) / (yr1 - yr)) * (∫ x2 in yr..cR, gm_real t_lo t_hi x2) +
      ((x1 - yr) / (yr1 - yr)) * (∫ x2 in yr1..cR, gm_real t_lo t_hi x2) := by
  have hcont : ContinuousOn (fun x => gm_real t_lo t_hi x) (Icc bR cR) := by
    have heq : ∀ x ∈ Icc bR cR, gm_real t_lo t_hi x = g_real (max t_lo (min t_hi (2 * x + cR))) x := by
      intro x _; unfold gm_real; dsimp only
      split_ifs with ha hb
      · rw [min_eq_left ha, max_eq_right hlo]
      · push Not at ha; rw [min_eq_right (le_of_lt ha), max_eq_left hb]
      · push Not at ha hb; rw [min_eq_right (le_of_lt ha), max_eq_right (le_of_lt hb)]
    refine ContinuousOn.congr ?_ heq
    have hclamp : Continuous (fun x : ℝ => max t_lo (min t_hi (2 * x + cR))) :=
      continuous_const.max (continuous_const.min ((continuous_const.mul continuous_id).add continuous_const))
    exact g_real_continuousOn.comp (hclamp.continuousOn.prodMk continuousOn_id) (fun x hx => ⟨trivial, hx⟩)
  have hint : ∀ u v : ℝ, bR ≤ u → u ≤ v → v ≤ cR →
      IntervalIntegrable (fun x => gm_real t_lo t_hi x) volume u v := fun u v hu huv hv =>
    (hcont.mono (Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc huv
  have hI_yr : ∫ x2 in yr..cR, gm_real t_lo t_hi x2 =
      (∫ x2 in yr..x1, gm_real t_lo t_hi x2) + ∫ x2 in x1..cR, gm_real t_lo t_hi x2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint yr x1 hbr h1 (le_trans h2 hrc)) (hint x1 cR (le_trans hbr h1) (le_trans h2 hrc) le_rfl)).symm
  have hI_x1 : ∫ x2 in x1..cR, gm_real t_lo t_hi x2 =
      (∫ x2 in x1..yr1, gm_real t_lo t_hi x2) + ∫ x2 in yr1..cR, gm_real t_lo t_hi x2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint x1 yr1 (le_trans hbr h1) h2 hrc) (hint yr1 cR (le_trans hbr (le_trans h1 h2)) hrc le_rfl)).symm
  have hlow : (x1 - yr) * gm_real t_lo t_hi x1 ≤ ∫ x2 in yr..x1, gm_real t_lo t_hi x2 := by
    have hconst : ∫ _ in yr..x1, gm_real t_lo t_hi x1 = (x1 - yr) * gm_real t_lo t_hi x1 := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    exact intervalIntegral.integral_mono_on h1 intervalIntegrable_const
      (hint yr x1 hbr h1 (le_trans h2 hrc))
      (fun x hx => gm_real_antitone hlo (le_trans hbr hx.1) hx.2 (le_trans h2 hrc))
  have hhigh : ∫ x2 in x1..yr1, gm_real t_lo t_hi x2 ≤ (yr1 - x1) * gm_real t_lo t_hi x1 := by
    have hconst : ∫ _ in x1..yr1, gm_real t_lo t_hi x1 = (yr1 - x1) * gm_real t_lo t_hi x1 := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    exact intervalIntegral.integral_mono_on h2 (hint x1 yr1 (le_trans hbr h1) h2 hrc)
      intervalIntegrable_const
      (fun x hx => gm_real_antitone hlo (le_trans hbr h1) hx.1 (le_trans hx.2 hrc))
  have hcross : (x1 - yr) * (∫ x2 in x1..yr1, gm_real t_lo t_hi x2) ≤
      (yr1 - x1) * (∫ x2 in yr..x1, gm_real t_lo t_hi x2) := by
    have hA := mul_le_mul_of_nonneg_left hhigh (sub_nonneg.mpr h1)
    have hB := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr h2)
    linarith
  rw [hI_yr, hI_x1]
  have hne : yr1 - yr ≠ 0 := ne_of_gt hpos
  rw [← sub_nonneg]
  have halg : ((yr1 - x1) / (yr1 - yr)) * ((∫ x2 in yr..x1, gm_real t_lo t_hi x2) +
        ((∫ x2 in x1..yr1, gm_real t_lo t_hi x2) + ∫ x2 in yr1..cR, gm_real t_lo t_hi x2)) +
      ((x1 - yr) / (yr1 - yr)) * (∫ x2 in yr1..cR, gm_real t_lo t_hi x2) -
      ((∫ x2 in x1..yr1, gm_real t_lo t_hi x2) + ∫ x2 in yr1..cR, gm_real t_lo t_hi x2) =
      ((yr1 - x1) * (∫ x2 in yr..x1, gm_real t_lo t_hi x2) -
        (x1 - yr) * (∫ x2 in x1..yr1, gm_real t_lo t_hi x2)) / (yr1 - yr) := by
    field_simp [hne]; ring
  rw [halg]
  exact div_nonneg (by linarith) (le_of_lt hpos)

private lemma wL_integral_le {xi xi1 yr1 hy : ℝ}
    (hxi_pos : 0 < xi) (hle : xi ≤ xi1) (hyr1 : xi1 ≤ yr1) (hhy : 0 < hy) :
    ∫ x in xi..xi1, (yr1 - x) / (hy * x) ≤
      ((xi1 - xi) / (2 * hy)) * ((yr1 - xi) / xi + (yr1 - xi1) / xi1) := by
  have hcont : ContinuousOn (fun x => (yr1 - x) / (hy * x)) (Icc xi xi1) :=
    (continuousOn_const.sub continuousOn_id).div (continuousOn_const.mul continuousOn_id)
      (fun x hx => ne_of_gt (mul_pos hhy (lt_of_lt_of_le hxi_pos hx.1)))
  have hd1 : ∀ x ∈ Ioo xi xi1, HasDerivAt (fun x => (yr1 - x) / (hy * x)) (-yr1 / (hy * x ^ 2)) x := by
    intro x hx
    have hxp : 0 < x := lt_of_lt_of_le hxi_pos (le_of_lt hx.1)
    have h1 : HasDerivAt (fun x => yr1 - x) (-1) x :=
      ((hasDerivAt_const x yr1).fun_sub (hasDerivAt_id' x)) ▸d (by ring)
    have h2 : HasDerivAt (fun x => hy * x) hy x :=
      ((hasDerivAt_id' x).const_mul hy) ▸d (by ring)
    exact (h1.fun_div h2 (ne_of_gt (mul_pos hhy hxp))) ▸d (by
      field_simp [ne_of_gt hhy, ne_of_gt hxp]; ring)
  have hd2 : ∀ x ∈ Ioo xi xi1, HasDerivAt (fun x => -yr1 / (hy * x ^ 2)) (2 * yr1 / (hy * x ^ 3)) x := by
    intro x hx
    have hxp : 0 < x := lt_of_lt_of_le hxi_pos (le_of_lt hx.1)
    have h2 : HasDerivAt (fun x => hy * x ^ 2) (2 * hy * x) x :=
      (((hasDerivAt_pow 2 x).const_mul hy)) ▸d (by ring)
    exact ((hasDerivAt_const x (-yr1)).fun_div h2 (ne_of_gt (mul_pos hhy (pow_pos hxp 2)))) ▸d (by
      field_simp [ne_of_gt hhy, ne_of_gt hxp]; ring)
  have htr := integral_le_trapezoid_add_K hle hcont hd1 hd2 (K := 0) (fun x hx => by
    have hxp : 0 < x := lt_of_lt_of_le hxi_pos (le_of_lt hx.1)
    have hyr1p : 0 ≤ yr1 := le_trans (le_of_lt hxi_pos) (le_trans hle hyr1)
    have : 0 ≤ 2 * yr1 / (hy * x ^ 3) := div_nonneg (by linarith) (le_of_lt (mul_pos hhy (pow_pos hxp 3)))
    linarith)
  have hxi1_pos : 0 < xi1 := lt_of_lt_of_le hxi_pos hle
  have halg : (((yr1 - xi) / (hy * xi) + (yr1 - xi1) / (hy * xi1)) / 2) * (xi1 - xi) +
      (0 / 12) * (xi1 - xi) ^ 3 =
      ((xi1 - xi) / (2 * hy)) * ((yr1 - xi) / xi + (yr1 - xi1) / xi1) := by
    field_simp [ne_of_gt hhy, ne_of_gt hxi_pos, ne_of_gt hxi1_pos]; ring
  linarith

private lemma wR_integral_le {xi xi1 yr hy : ℝ}
    (hyr_nonneg : 0 ≤ yr) (_hyr_le : yr ≤ xi) (hxi_pos : 0 < xi) (hle : xi ≤ xi1) (hhy : 0 < hy) :
    ∫ x in xi..xi1, (x - yr) / (hy * x) ≤
      ((xi1 - xi) / hy) * (((xi + xi1) / 2 - yr) / ((xi + xi1) / 2)) := by
  set xm := (xi + xi1) / 2
  have hxm_pos : 0 < xm := by simp only [xm]; linarith
  have hcont : ContinuousOn (fun x => (x - yr) / (hy * x)) (Icc xi xi1) :=
    (continuousOn_id.sub continuousOn_const).div (continuousOn_const.mul continuousOn_id)
      (fun x hx => ne_of_gt (mul_pos hhy (lt_of_lt_of_le hxi_pos hx.1)))
  have hlin_int : IntervalIntegrable (fun x => ((xm - yr) / (hy * xm)) + (yr / (hy * xm ^ 2)) * (x - xm)) volume xi xi1 :=
    intervalIntegrable_const.add (((continuousOn_id.sub continuousOn_const).intervalIntegrable_of_Icc hle).const_mul _)
  have hpt : ∀ x ∈ Icc xi xi1,
      (x - yr) / (hy * x) ≤ ((xm - yr) / (hy * xm)) + (yr / (hy * xm ^ 2)) * (x - xm) := by
    intro x hx
    have hxp : 0 < x := lt_of_lt_of_le hxi_pos hx.1
    rw [← sub_nonneg]
    have halg : ((xm - yr) / (hy * xm)) + (yr / (hy * xm ^ 2)) * (x - xm) - (x - yr) / (hy * x) =
        yr * (x - xm) ^ 2 / (hy * x * xm ^ 2) := by
      field_simp [ne_of_gt hhy, ne_of_gt hxp, ne_of_gt hxm_pos]; ring
    rw [halg]
    exact div_nonneg (mul_nonneg hyr_nonneg (sq_nonneg _))
      (le_of_lt (mul_pos (mul_pos hhy hxp) (pow_pos hxm_pos 2)))
  have hmono := intervalIntegral.integral_mono_on hle (hcont.intervalIntegrable_of_Icc hle) hlin_int hpt
  have hlin_eval : ∫ x in xi..xi1, (((xm - yr) / (hy * xm)) + (yr / (hy * xm ^ 2)) * (x - xm)) =
      ((xi1 - xi) / hy) * ((xm - yr) / xm) := by
    have hF : ∀ x ∈ uIcc xi xi1,
        HasDerivAt (fun t => ((xm - yr) / (hy * xm)) * t + (yr / (hy * xm ^ 2)) * ((t - xm) ^ 2 / 2))
          (((xm - yr) / (hy * xm)) + (yr / (hy * xm ^ 2)) * (x - xm)) x := by
      intro x _
      have h1 : HasDerivAt (fun t => ((xm - yr) / (hy * xm)) * t) ((xm - yr) / (hy * xm)) x :=
        ((hasDerivAt_id' x).const_mul ((xm - yr) / (hy * xm))) ▸d (by ring)
      have h2 : HasDerivAt (fun t => (t - xm) ^ 2 / 2) (x - xm) x := by
        have hs : HasDerivAt (fun t => t - xm) 1 x :=
          ((hasDerivAt_id' x).sub_const xm) ▸d (by ring)
        exact ((hs.pow 2).div_const 2) ▸d (by ring)
      exact (h1.add (h2.const_mul (yr / (hy * xm ^ 2)))) ▸d (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hlin_int]
    have hsq : (xi1 - xm) ^ 2 = (xi - xm) ^ 2 := by simp only [xm]; ring
    rw [hsq]; field_simp [ne_of_gt hhy, ne_of_gt hxm_pos]; ring
  linarith

private lemma intervalIntegral_ite_ge {f : ℝ → ℝ} {a b x0 : ℝ}
    (hax : a ≤ x0) (hxb : x0 ≤ b) (hf : IntervalIntegrable f volume a b) :
    ∫ x in a..b, (if x0 ≤ x then f x else 0) = ∫ x in x0..b, f x := by
  have h1 : IntervalIntegrable (fun x => if x0 ≤ x then f x else 0) volume a x0 := by
    have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a x0 := intervalIntegrable_const
    refine hzero.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le hax]
    filter_upwards [ae_ne_const x0] with x hne hx
    rw [if_neg (not_le.mpr (lt_of_le_of_ne hx.2 hne))]
  have h2 : IntervalIntegrable (fun x => if x0 ≤ x then f x else 0) volume x0 b := by
    have hsub : uIcc x0 b ⊆ uIcc a b :=
      uIcc_subset_uIcc (by rw [uIcc_of_le (le_trans hax hxb)]; exact ⟨hax, hxb⟩) right_mem_uIcc
    refine (hf.mono_set hsub).congr ?_
    intro x hx
    rw [uIoc_of_le hxb] at hx
    exact (if_pos (le_of_lt hx.1)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hleft : ∫ x in a..x0, (if x0 ≤ x then f x else 0) = 0 := by
    rw [intervalIntegral.integral_of_le hax]
    refine (setIntegral_congr_ae measurableSet_Ioc ?_).trans (by simp : ∫ _ in Ioc a x0, (0 : ℝ) = 0)
    filter_upwards [ae_ne_const x0] with x hne hx
    exact if_neg (not_le.mpr (lt_of_le_of_ne hx.2 hne))
  have hright : ∫ x in x0..b, (if x0 ≤ x then f x else 0) = ∫ x in x0..b, f x :=
    intervalIntegral.integral_congr (fun x hx => by rw [uIcc_of_le hxb] at hx; exact if_pos hx.1)
  rw [hleft, zero_add, hright]

private lemma intervalIntegral_ite_Icc {f : ℝ → ℝ} {A B u v : ℝ}
    (hAu : A ≤ u) (huv : u ≤ v) (hvB : v ≤ B) (hf : IntervalIntegrable f volume u v) :
    ∫ x in A..B, (if u ≤ x ∧ x ≤ v then f x else 0) = ∫ x in u..v, f x := by
  have h1 : IntervalIntegrable (fun x => if u ≤ x ∧ x ≤ v then f x else 0) volume A u := by
    refine (intervalIntegrable_const (c := (0 : ℝ))).congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le hAu]
    filter_upwards [ae_ne_const u] with x hne hx
    have : ¬ (u ≤ x ∧ x ≤ v) := fun h => hne (le_antisymm hx.2 h.1)
    rw [if_neg this]
  have h2 : IntervalIntegrable (fun x => if u ≤ x ∧ x ≤ v then f x else 0) volume u v :=
    hf.congr (fun x hx => by rw [uIoc_of_le huv] at hx; exact (if_pos ⟨le_of_lt hx.1, hx.2⟩).symm)
  have h3 : IntervalIntegrable (fun x => if u ≤ x ∧ x ≤ v then f x else 0) volume v B := by
    refine (intervalIntegrable_const (c := (0 : ℝ))).congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le hvB]
    filter_upwards with x hx
    have : ¬ (u ≤ x ∧ x ≤ v) := fun h => not_lt_of_ge h.2 hx.1
    rw [if_neg this]
  have h12 : IntervalIntegrable (fun x => if u ≤ x ∧ x ≤ v then f x else 0) volume A v :=
    h1.trans h2
  rw [← intervalIntegral.integral_add_adjacent_intervals h12 h3,
      ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hz1 : ∫ x in A..u, (if u ≤ x ∧ x ≤ v then f x else 0) = 0 := by
    rw [intervalIntegral.integral_of_le hAu]
    refine (setIntegral_congr_ae measurableSet_Ioc ?_).trans (by simp : ∫ _ in Ioc A u, (0 : ℝ) = 0)
    filter_upwards [ae_ne_const u] with x hne hx
    exact if_neg (fun h => hne (le_antisymm hx.2 h.1))
  have hz3 : ∫ x in v..B, (if u ≤ x ∧ x ≤ v then f x else 0) = 0 := by
    rw [intervalIntegral.integral_of_le hvB]
    refine (setIntegral_congr_ae measurableSet_Ioc ?_).trans (by simp : ∫ _ in Ioc v B, (0 : ℝ) = 0)
    filter_upwards with x hx
    exact if_neg (fun h => not_lt_of_ge h.2 hx.1)
  have hmid : ∫ x in u..v, (if u ≤ x ∧ x ≤ v then f x else 0) = ∫ x in u..v, f x :=
    intervalIntegral.integral_congr (fun x hx => by rw [uIcc_of_le huv] at hx; exact if_pos hx)
  rw [hz1, zero_add, hmid, hz3, add_zero]

private def e4 : (Fin 4 → ℝ) ≃ᵐ ℝ × (ℝ × (ℝ × ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
        ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)))

private lemma e4_measurePreserving : MeasurePreserving e4 volume volume := by
  unfold e4
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 := volume_preserving_finTwoArrow ℝ
  exact (((MeasurePreserving.id volume).prod (((MeasurePreserving.id volume).prod h3).comp h2)).comp h1)

private lemma e4_apply (x : Fin 4 → ℝ) : e4 x = (x 0, (x 1, (x 2, x 3))) := by
  simp [e4, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.finTwoArrow]
  rfl


private lemma r0j19_domain_preimage :
    domain (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) =
      e4 ⁻¹' {z : ℝ × (ℝ × (ℝ × ℝ)) |
        z ∈ (Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR))) ∧
        z.2.1 ≤ z.2.2.1 ∧ z.2.2.1 ≤ z.2.2.2} := by
  have hlo0 : (r0j19_lo 0 : ℝ) = a0R := by simp [r0j19_lo, a0R]
  have hlo1 : (r0j19_lo 1 : ℝ) = bR := by simp [r0j19_lo, bR]
  have hlo2 : (r0j19_lo 2 : ℝ) = bR := by simp [r0j19_lo, bR]
  have hlo3 : (r0j19_lo 3 : ℝ) = bR := by simp [r0j19_lo, bR]
  have hhi0 : (r0j19_hi 0 : ℝ) = a1R := by simp [r0j19_hi, a1R]
  have hhi1 : (r0j19_hi 1 : ℝ) = cR := by simp [r0j19_hi, cR]
  have hhi2 : (r0j19_hi 2 : ℝ) = cR := by simp [r0j19_hi, cR]
  have hhi3 : (r0j19_hi 3 : ℝ) = cR := by simp [r0j19_hi, cR]
  have ha1b : a1R ≤ bR := by unfold a1R bR; norm_num
  ext x
  simp only [domain, Set.mem_preimage, mem_ofPred_eq, e4_apply, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨hmono, hbox⟩
    have h0 := hbox 0; rw [hlo0, hhi0] at h0
    have h1 := hbox 1; rw [hlo1, hhi1] at h1
    have h2 := hbox 2; rw [hlo2, hhi2] at h2
    have h3 := hbox 3; rw [hlo3, hhi3] at h3
    exact ⟨⟨h0, h1, h2, h3⟩, hmono (by decide : (1 : Fin 4) ≤ 2), hmono (by decide : (2 : Fin 4) ≤ 3)⟩
  · rintro ⟨⟨h0, h1, h2, h3⟩, h12, h23⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, ha1b]
    · intro j
      fin_cases j
      · exact ⟨by simpa [hlo0] using h0.1, by simpa [hhi0] using h0.2⟩
      · exact ⟨by simpa [hlo1] using h1.1, by simpa [hhi1] using h1.2⟩
      · exact ⟨by simpa [hlo2] using h2.1, by simpa [hhi2] using h2.2⟩
      · exact ⟨by simpa [hlo3] using h3.1, by simpa [hhi3] using h3.2⟩

private lemma setIntegral_B4_eq_iterated {G : ℝ × (ℝ × (ℝ × ℝ)) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hG_meas : Measurable G)
    (hG_bound : ∀ z ∈ Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR)), ‖G z‖ ≤ M) :
    ∫ z in {z : ℝ × (ℝ × (ℝ × ℝ)) |
        z ∈ (Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR))) ∧
        z.2.1 ≤ z.2.2.1 ∧ z.2.2.1 ≤ z.2.2.2}, G z =
      ∫ x0 in a0R..a1R, ∫ x1 in bR..cR, ∫ x2 in x1..cR, ∫ x3 in x2..cR, G (x0, x1, x2, x3) := by
  have ha01 : a0R ≤ a1R := by unfold a0R a1R; norm_num
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  let B4 : Set (ℝ × (ℝ × (ℝ × ℝ))) := Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR))
  let S4 : Set (ℝ × (ℝ × (ℝ × ℝ))) := {z | z.2.1 ≤ z.2.2.1 ∧ z.2.2.1 ≤ z.2.2.2}
  let F : ℝ × (ℝ × (ℝ × ℝ)) → ℝ := fun z => if z ∈ S4 then G z else 0
  have hS4_meas : MeasurableSet S4 :=
    (isClosed_le (continuous_fst.comp continuous_snd)
      (continuous_fst.comp (continuous_snd.comp continuous_snd))).measurableSet.inter
      (isClosed_le (continuous_fst.comp (continuous_snd.comp continuous_snd))
        (continuous_snd.comp (continuous_snd.comp continuous_snd))).measurableSet
  have hset_eq : {z | z ∈ B4 ∧ z.2.1 ≤ z.2.2.1 ∧ z.2.2.1 ≤ z.2.2.2} = B4 ∩ S4 := rfl
  rw [hset_eq, ← setIntegral_indicator hS4_meas]
  have hind_eq : S4.indicator G = F := by ext z; simp only [F, Set.indicator]; split_ifs <;> rfl
  rw [hind_eq]
  have hG_int : IntegrableOn G B4 volume := by
    have hfin : volume B4 ≠ ⊤ :=
      (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).measure_lt_top.ne
    refine Integrable.mono' (integrableOn_const (C := M) (hs := hfin)) hG_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)))] with z hz
    exact hG_bound z hz
  have hF_int : IntegrableOn F B4 volume := by rw [← hind_eq]; exact hG_int.indicator hS4_meas
  have hF_meas : Measurable F := by rw [← hind_eq]; exact hG_meas.indicator hS4_meas
  change ∫ z in Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR)), F z = _
  rw [Measure.volume_eq_prod, MeasureTheory.setIntegral_prod F (by rwa [← Measure.volume_eq_prod])]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha01]
  apply intervalIntegral.integral_congr
  intro x0 hx0
  rw [uIcc_of_le ha01] at hx0
  dsimp only
  have hinner_int : IntegrableOn (fun y : ℝ × (ℝ × ℝ) => F (x0, y))
      (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR)) volume := by
    have hfin : volume (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR)) ≠ ⊤ :=
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top.ne
    refine Integrable.mono' (integrableOn_const (C := M) (hs := hfin))
      (hF_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc))] with y hy
    simp only [F]; split_ifs
    · exact hG_bound (x0, y) ⟨hx0, hy⟩
    · rw [norm_zero]; exact hM
  rw [Measure.volume_eq_prod, MeasureTheory.setIntegral_prod (fun y => F (x0, y)) (by rwa [← Measure.volume_eq_prod])]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc]
  apply intervalIntegral.integral_congr
  intro x1 hx1
  rw [uIcc_of_le hbc] at hx1
  dsimp only
  have hinner2 : IntegrableOn (fun q : ℝ × ℝ => F (x0, x1, q)) (Icc bR cR ×ˢ Icc bR cR) volume := by
    have hfin : volume (Icc bR cR ×ˢ Icc bR cR) ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    refine Integrable.mono' (integrableOn_const (C := M) (hs := hfin))
      (hF_meas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
    simp only [F]; split_ifs
    · exact hG_bound (x0, x1, q) ⟨hx0, hx1, hq⟩
    · rw [norm_zero]; exact hM
  rw [Measure.volume_eq_prod, MeasureTheory.setIntegral_prod (fun q => F (x0, x1, q)) (by rwa [← Measure.volume_eq_prod])]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc]
  have hx2_rew : ∀ x2 ∈ uIcc bR cR,
      (∫ x3 in Icc bR cR, F (x0, x1, x2, x3)) =
        if x1 ≤ x2 then ∫ x3 in x2..cR, G (x0, x1, x2, x3) else 0 := by
    intro x2 hx2
    rw [uIcc_of_le hbc] at hx2
    by_cases h12 : x1 ≤ x2
    · rw [if_pos h12, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc]
      have hcongr : ∀ x3 ∈ uIcc bR cR, F (x0, x1, x2, x3) = if x2 ≤ x3 then G (x0, x1, x2, x3) else 0 := by
        intro x3 _; simp only [F, S4, mem_ofPred_eq, h12, true_and]
      rw [intervalIntegral.integral_congr hcongr]
      apply intervalIntegral_ite_ge hx2.1 hx2.2
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbc]
      have hm3 : Measurable (fun x3 : ℝ => G (x0, x1, x2, x3)) :=
        hG_meas.comp (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      refine Integrable.mono' (integrableOn_const (C := M) (hs := isCompact_Icc.measure_lt_top.ne))
        hm3.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x3 hx3
      exact hG_bound (x0, x1, x2, x3) ⟨hx0, hx1, hx2, hx3⟩
    · rw [if_neg h12]
      have hz : ∀ x3, F (x0, x1, x2, x3) = 0 := fun x3 => by
        simp only [F, S4, mem_ofPred_eq, h12, false_and, ↓reduceIte]
      simp [hz]
  rw [intervalIntegral.integral_congr hx2_rew]
  have hint_x2 : IntervalIntegrable (fun x2 => ∫ x3 in x2..cR, G (x0, x1, x2, x3)) volume bR cR := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbc]
    have hprod_int : IntegrableOn (fun q : ℝ × ℝ => if q.1 ≤ q.2 then G (x0, x1, q.1, q.2) else 0)
        (Icc bR cR ×ˢ Icc bR cR) volume := by
      have hfin : volume (Icc bR cR ×ˢ Icc bR cR) ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
      have hm : Measurable (fun q : ℝ × ℝ => if q.1 ≤ q.2 then G (x0, x1, q.1, q.2) else 0) :=
        Measurable.ite (isClosed_le continuous_fst continuous_snd).measurableSet
          (hG_meas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))) measurable_const
      refine Integrable.mono' (integrableOn_const (C := M) (hs := hfin)) hm.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
      split_ifs
      · exact hG_bound (x0, x1, q) ⟨hx0, hx1, hq⟩
      · rw [norm_zero]; exact hM
    have hint_outer : IntegrableOn (fun x2 => ∫ x3 in Icc bR cR,
        (if x2 ≤ x3 then G (x0, x1, x2, x3) else 0)) (Icc bR cR) volume := by
      rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod_int
      exact hprod_int.integral_prod_left
    refine hint_outer.congr_fun (fun x2 hx2 => ?_) measurableSet_Icc
    dsimp only
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc]
    apply intervalIntegral_ite_ge hx2.1 hx2.2
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbc]
    have hm3 : Measurable (fun x3 : ℝ => G (x0, x1, x2, x3)) :=
      hG_meas.comp (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    refine Integrable.mono' (integrableOn_const (C := M) (hs := isCompact_Icc.measure_lt_top.ne))
      hm3.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x3 hx3
    exact hG_bound (x0, x1, x2, x3) ⟨hx0, hx1, hx2, hx3⟩
  exact intervalIntegral_ite_ge hx1.1 hx1.2 hint_x2

private lemma buchstab_measurable_le_one {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    Measurable ω ∧ ∀ u : ℝ, ω u ≤ 1 := by
  refine ⟨?_, ?_⟩
  · have h_eq : ω = Set.piecewise (Ici 1) (fun u => ω (max u 1)) (fun _ => 0) := by
      ext u; simp only [Set.piecewise]; split_ifs with hu
      · rw [max_eq_left (Set.mem_Ici.mp hu)]
      · exact hz u (not_le.mp hu)
    rw [h_eq]
    have hcomp : Continuous (fun u : ℝ => ω (max u 1)) :=
      hω.1.comp_continuous (continuous_id.max continuous_const) (fun u => le_max_right u 1)
    exact Measurable.piecewise measurableSet_Ici hcomp.measurable measurable_const
  · intro u
    by_cases h1 : u < 1
    · rw [hz u h1]; norm_num
    · push Not at h1
      by_cases h2 : u ≤ 2
      · rw [hω.2.1 u h1 h2, div_le_one (by linarith)]; exact h1
      · push Not at h2
        have := buchstab_le_two_thirds_ge_two hω (Nat.ceil u) u (le_of_lt h2)
          (by have := Nat.le_ceil u; linarith)
        linarith


private lemma buchstabIntegral_eq_setIntegral_B4 {ω : ℝ → ℝ} (φ : ℝ) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ =
      ∫ z in {z : ℝ × (ℝ × (ℝ × ℝ)) |
          z ∈ (Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR))) ∧
          z.2.1 ≤ z.2.2.1 ∧ z.2.2.1 ≤ z.2.2.2},
        ω ((φ - z.1 - z.2.1 - z.2.2.1 - z.2.2.2) / z.2.2.1) /
          (z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2) := by
  let G : ℝ × (ℝ × (ℝ × ℝ)) → ℝ := fun z =>
    ω ((φ - z.1 - z.2.1 - z.2.2.1 - z.2.2.2) / z.2.2.1) /
      (z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2)
  have hfun_eq : (fun x : Fin 4 → ℝ =>
      ω ((φ - ∑ j : Fin 4, x j) / x ⟨2, by omega⟩) / ((∏ j : Fin 4, x j) * x ⟨2, by omega⟩)) =
      G ∘ e4 := by
    ext x
    have h2 : (⟨2, by omega⟩ : Fin 4) = 2 := rfl
    simp only [Function.comp_apply, G, e4_apply, Fin.sum_univ_four, Fin.prod_univ_four, h2]
    congr 1
    · congr 1; ring
    · ring
  unfold buchstabIntegral
  rw [r0j19_domain_preimage, hfun_eq]
  exact e4_measurePreserving.setIntegral_preimage_emb e4.measurableEmbedding G _

private lemma buchstabIntegral_eq_iterated {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    (φ : ℝ) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ =
      ∫ x0 in a0R..a1R, ∫ x1 in bR..cR, ∫ x2 in x1..cR, ∫ x3 in x2..cR,
        ω ((φ - x0 - x1 - x2 - x3) / x2) / (x0 * x1 * x2 * x2 * x3) := by
  have ha0_pos : (0 : ℝ) < a0R := by unfold a0R; norm_num
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  rcases buchstab_measurable_le_one hω hz with ⟨hω_meas, hω_le_one⟩
  rw [buchstabIntegral_eq_setIntegral_B4]
  apply setIntegral_B4_eq_iterated (M := 1 / (a0R * bR * bR * bR * bR)) (by positivity)
  · exact (hω_meas.comp (by fun_prop)).div (by fun_prop)
  · rintro z ⟨hz0, hz1, hz2, hz3⟩
    have h0p : 0 < z.1 := lt_of_lt_of_le ha0_pos hz0.1
    have h1p : 0 < z.2.1 := lt_of_lt_of_le hb_pos hz1.1
    have h2p : 0 < z.2.2.1 := lt_of_lt_of_le hb_pos hz2.1
    have h3p : 0 < z.2.2.2 := lt_of_lt_of_le hb_pos hz3.1
    have hden_ge : a0R * bR * bR * bR * bR ≤ z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2 := by
      have h1 := mul_le_mul hz0.1 hz1.1 (le_of_lt hb_pos) (le_of_lt h0p)
      have h2 := mul_le_mul h1 hz2.1 (le_of_lt hb_pos) (mul_nonneg (le_of_lt h0p) (le_of_lt h1p))
      have h3 := mul_le_mul h2 hz2.1 (le_of_lt hb_pos) (mul_nonneg (mul_nonneg (le_of_lt h0p) (le_of_lt h1p)) (le_of_lt h2p))
      exact mul_le_mul h3 hz3.1 (le_of_lt hb_pos)
        (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt h0p) (le_of_lt h1p)) (le_of_lt h2p)) (le_of_lt h2p))
    rw [Real.norm_of_nonneg (div_nonneg (buchstab_nonneg hω hz _) (by positivity))]
    exact le_trans (div_le_div_of_nonneg_right (hω_le_one _) (by positivity))
      (div_le_div_of_nonneg_left zero_le_one (by positivity) hden_ge)

/-! ### Part 4b: Tail Bound (2.28 ≤ φ ≤ 7/2) -/

private lemma r0j19_tail_bound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (228 / 100 : ℝ) ≤ φ) (_hφtop : φ ≤ 7 / 2) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
      ((70737 / 1000000000) : ℝ) := by
  have ha0_pos : (0 : ℝ) < a0R := by unfold a0R; norm_num
  have ha01 : a0R ≤ a1R := by unfold a0R a1R; norm_num
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  have hc_pos : (0 : ℝ) < cR := lt_of_lt_of_le hb_pos hbc
  rcases buchstab_measurable_le_one hω hz with ⟨hω_meas, hω_le_one⟩
  rw [buchstabIntegral_eq_setIntegral_B4]
  let S_dom : Set (ℝ × (ℝ × (ℝ × ℝ))) :=
    {z | z ∈ (Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR))) ∧
         z.2.1 ≤ z.2.2.1 ∧ z.2.2.1 ≤ z.2.2.2}
  let G_lhs : ℝ × (ℝ × (ℝ × ℝ)) → ℝ := fun z =>
    ω ((φ - z.1 - z.2.1 - z.2.2.1 - z.2.2.2) / z.2.2.1) /
      (z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2)
  let G_rhs : ℝ × (ℝ × (ℝ × ℝ)) → ℝ := fun z =>
    (4 / 5 : ℝ) / (z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2)
  have hS_meas : MeasurableSet S_dom :=
    (measurableSet_Icc.prod (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc))).inter
      ((isClosed_le (continuous_fst.comp continuous_snd)
        (continuous_fst.comp (continuous_snd.comp continuous_snd))).measurableSet.inter
        (isClosed_le (continuous_fst.comp (continuous_snd.comp continuous_snd))
          (continuous_snd.comp (continuous_snd.comp continuous_snd))).measurableSet)
  have hfin : volume S_dom ≠ ⊤ := by
    have hsub : S_dom ⊆ Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR)) := fun z hz => hz.1
    exact (measure_mono hsub).trans_lt
      (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).measure_lt_top |>.ne
  have hden_ge : ∀ z ∈ Icc a0R a1R ×ˢ (Icc bR cR ×ˢ (Icc bR cR ×ˢ Icc bR cR)),
      a0R * bR * bR * bR * bR ≤ z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2 := by
    rintro z ⟨hz0, hz1, hz2, hz3⟩
    have h0p : 0 < z.1 := lt_of_lt_of_le ha0_pos hz0.1
    have h1p : 0 < z.2.1 := lt_of_lt_of_le hb_pos hz1.1
    have h2p : 0 < z.2.2.1 := lt_of_lt_of_le hb_pos hz2.1
    have h1 := mul_le_mul hz0.1 hz1.1 (le_of_lt hb_pos) (le_of_lt h0p)
    have h2 := mul_le_mul h1 hz2.1 (le_of_lt hb_pos) (mul_nonneg (le_of_lt h0p) (le_of_lt h1p))
    have h3 := mul_le_mul h2 hz2.1 (le_of_lt hb_pos) (mul_nonneg (mul_nonneg (le_of_lt h0p) (le_of_lt h1p)) (le_of_lt h2p))
    exact mul_le_mul h3 hz3.1 (le_of_lt hb_pos)
      (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt h0p) (le_of_lt h1p)) (le_of_lt h2p)) (le_of_lt h2p))
  have hG_lhs_int : IntegrableOn G_lhs S_dom volume := by
    have hm : Measurable G_lhs := (hω_meas.comp (by fun_prop)).div (by fun_prop)
    refine Integrable.mono' (integrableOn_const (C := 1 / (a0R * bR * bR * bR * bR)) (hs := hfin))
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS_meas] with z hzS
    have hd := hden_ge z hzS.1
    have hdp : 0 < z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2 := lt_of_lt_of_le (by positivity) hd
    rw [Real.norm_of_nonneg (div_nonneg (buchstab_nonneg hω hz _) (le_of_lt hdp))]
    exact le_trans (div_le_div_of_nonneg_right (hω_le_one _) (le_of_lt hdp))
      (div_le_div_of_nonneg_left zero_le_one (by positivity) hd)
  have hG_rhs_int : IntegrableOn G_rhs S_dom volume := by
    have hm : Measurable G_rhs := measurable_const.div (by fun_prop)
    refine Integrable.mono' (integrableOn_const (C := (4 / 5) / (a0R * bR * bR * bR * bR)) (hs := hfin))
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS_meas] with z hzS
    have hd := hden_ge z hzS.1
    have hdp : 0 < z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2 := lt_of_lt_of_le (by positivity) hd
    rw [Real.norm_of_nonneg (div_nonneg (by norm_num) (le_of_lt hdp))]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
  have hpt : ∀ z ∈ S_dom, G_lhs z ≤ G_rhs z := by
    rintro z ⟨⟨hz0, hz1, hz2, hz3⟩, _, _⟩
    have h2p : 0 < z.2.2.1 := lt_of_lt_of_le hb_pos hz2.1
    have hdp : 0 < z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2 :=
      lt_of_lt_of_le (by positivity) (hden_ge z ⟨hz0, hz1, hz2, hz3⟩)
    have hnum_ge : (5 / 4 : ℝ) * cR ≤ φ - z.1 - z.2.1 - z.2.2.1 - z.2.2.2 := by
      have hc_bound : (5 / 4 : ℝ) * cR + a1R + 3 * cR ≤ 228 / 100 := by
        unfold a1R cR; norm_num
      linarith [hz0.2, hz1.2, hz2.2, hz3.2]
    have hu_ge : (5 / 4 : ℝ) ≤ (φ - z.1 - z.2.1 - z.2.2.1 - z.2.2.2) / z.2.2.1 := by
      rw [le_div_iff₀ h2p]; nlinarith [hz2.2]
    exact div_le_div_of_nonneg_right (buchstab_le_four_fifths hω hu_ge) (le_of_lt hdp)
  have hle_set : ∫ z in S_dom, G_lhs z ≤ ∫ z in S_dom, G_rhs z :=
    setIntegral_mono_on hG_lhs_int hG_rhs_int hS_meas hpt
  have hrhs_eval : ∫ z in S_dom, G_rhs z =
      (4 / 5 : ℝ) * Real.log (a1R / a0R) *
        ((1 / bR + 1 / cR) * Real.log (cR / bR) - 2 * (1 / bR - 1 / cR)) := by
    have hiter : ∫ z in S_dom, G_rhs z =
        ∫ x0 in a0R..a1R, ∫ x1 in bR..cR, ∫ x2 in x1..cR, ∫ x3 in x2..cR, G_rhs (x0, x1, x2, x3) :=
      setIntegral_B4_eq_iterated (G := G_rhs) (M := (4 / 5) / (a0R * bR * bR * bR * bR)) (by positivity)
        (measurable_const.div (by fun_prop)) (fun z hzB => by
          have hd := hden_ge z hzB
          have hdp : 0 < z.1 * z.2.1 * z.2.2.1 * z.2.2.1 * z.2.2.2 := lt_of_lt_of_le (by positivity) hd
          rw [Real.norm_of_nonneg (div_nonneg (by norm_num) (le_of_lt hdp))]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hd)
    rw [hiter]
    -- Inner x3 integral: ∫_{x2}^{cR} (4/5)/(x0*x1*x2*x2*x3) dx3 = (4/5)*log(cR/x2)/(x0*x1*x2^2)
    have h_inv_int : ∀ u v : ℝ, 0 < u → u ≤ v → ∫ t in u..v, (1 / t : ℝ) = Real.log (v / u) := by
      intro u v hu huv
      have hvp : 0 < v := lt_of_lt_of_le hu huv
      have hF : ∀ t ∈ uIcc u v, HasDerivAt Real.log (1 / t) t := fun t ht => by
        rw [uIcc_of_le huv] at ht
        exact (Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hu ht.1))) ▸d (by ring)
      have hcont : ContinuousOn (fun t : ℝ => 1 / t) (Icc u v) :=
        continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (lt_of_lt_of_le hu ht.1))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable_of_Icc huv),
          Real.log_div (ne_of_gt hvp) (ne_of_gt hu)]
    -- Evaluate inner triple integral over (x1, x2, x3) independently of x0!
    -- First: ∫_{x1}^{cR} log(cR/x2)/x2^2 dx2 = (log(cR/x1) - 1)/x1 + 1/cR via F(t) = (-log(cR/t) + 1)/t
    have h_x2_eval : ∀ x1 ∈ Icc bR cR,
        ∫ x2 in x1..cR, Real.log (cR / x2) / x2 ^ 2 = (Real.log (cR / x1) - 1) / x1 + 1 / cR := by
      intro x1 hx1
      have h1p : 0 < x1 := lt_of_lt_of_le hb_pos hx1.1
      have hF : ∀ x ∈ uIcc x1 cR,
          HasDerivAt (fun t => (-Real.log (cR / t) + 1) / t) (Real.log (cR / x) / x ^ 2) x := by
        intro x hx
        rw [uIcc_of_le hx1.2] at hx
        have hxp : 0 < x := lt_of_lt_of_le h1p hx.1
        have hdiv : HasDerivAt (fun t => cR / t) (-cR / x ^ 2) x :=
          ((hasDerivAt_const x cR).fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by
            field_simp [ne_of_gt hxp]; ring)
        have hlog : HasDerivAt (fun t => Real.log (cR / t)) (-1 / x) x :=
          (hdiv.log (ne_of_gt (div_pos hc_pos hxp))) ▸d (by
            field_simp [ne_of_gt hc_pos, ne_of_gt hxp])
        have hnum : HasDerivAt (fun t => -Real.log (cR / t) + 1) (1 / x) x :=
          ((hlog.neg).add_const 1) ▸d (by ring)
        exact (hnum.fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by
          field_simp [ne_of_gt hxp]; ring)
      have hcont : ContinuousOn (fun x => Real.log (cR / x) / x ^ 2) (Icc x1 cR) :=
        ((continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (lt_of_lt_of_le h1p hx.1))).log
          (fun x hx => ne_of_gt (div_pos hc_pos (lt_of_lt_of_le h1p hx.1)))).div
          (continuousOn_id.pow 2) (fun x hx => ne_of_gt (pow_pos (lt_of_lt_of_le h1p hx.1) 2))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable_of_Icc hx1.2)]
      rw [div_self (ne_of_gt hc_pos), Real.log_one]; ring
    -- Outer x1 integral: ∫_{bR}^{cR} (1/x1) * ((log(cR/x1) - 1)/x1 + 1/cR) dx1
    -- Antiderivative: G(t) = (-log(cR/t) + 2)/t + log(t)/cR!
    have h_x1_eval :
        ∫ x1 in bR..cR, (1 / x1) * ((Real.log (cR / x1) - 1) / x1 + 1 / cR) =
          (1 / bR + 1 / cR) * Real.log (cR / bR) - 2 * (1 / bR - 1 / cR) := by
      have hF : ∀ x ∈ uIcc bR cR,
          HasDerivAt (fun t => (-Real.log (cR / t) + 2) / t + Real.log t / cR)
            ((1 / x) * ((Real.log (cR / x) - 1) / x + 1 / cR)) x := by
        intro x hx
        rw [uIcc_of_le hbc] at hx
        have hxp : 0 < x := lt_of_lt_of_le hb_pos hx.1
        have hdiv : HasDerivAt (fun t => cR / t) (-cR / x ^ 2) x :=
          ((hasDerivAt_const x cR).fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by
            field_simp [ne_of_gt hxp]; ring)
        have hlog : HasDerivAt (fun t => Real.log (cR / t)) (-1 / x) x :=
          (hdiv.log (ne_of_gt (div_pos hc_pos hxp))) ▸d (by
            field_simp [ne_of_gt hc_pos, ne_of_gt hxp])
        have h1 : HasDerivAt (fun t => (-Real.log (cR / t) + 2) / t) ((Real.log (cR / x) - 1) / x ^ 2) x :=
          (((hlog.fun_neg).add_const 2).fun_div (hasDerivAt_id' x) (ne_of_gt hxp)) ▸d (by
            field_simp [ne_of_gt hxp]; ring)
        have h2 : HasDerivAt (fun t => Real.log t / cR) (1 / (cR * x)) x :=
          ((Real.hasDerivAt_log (ne_of_gt hxp)).div_const cR) ▸d (by
            field_simp [ne_of_gt hc_pos, ne_of_gt hxp])
        exact (h1.add h2) ▸d (by field_simp [ne_of_gt hc_pos, ne_of_gt hxp])
      have hcont : ContinuousOn (fun x => (1 / x) * ((Real.log (cR / x) - 1) / x + 1 / cR)) (Icc bR cR) :=
        (continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (lt_of_lt_of_le hb_pos hx.1))).mul
          ((((continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (lt_of_lt_of_le hb_pos hx.1))).log
            (fun x hx => ne_of_gt (div_pos hc_pos (lt_of_lt_of_le hb_pos hx.1)))).sub continuousOn_const).div
            continuousOn_id (fun x hx => ne_of_gt (lt_of_lt_of_le hb_pos hx.1)) |>.add continuousOn_const)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable_of_Icc hbc)]
      rw [div_self (ne_of_gt hc_pos), Real.log_one, Real.log_div (ne_of_gt hc_pos) (ne_of_gt hb_pos)]
      ring
    -- Put all 4 iterated integrals together!
    have hstep : ∀ x0 ∈ uIcc a0R a1R,
        (∫ x1 in bR..cR, ∫ x2 in x1..cR, ∫ x3 in x2..cR, G_rhs (x0, x1, x2, x3)) =
        ((4 / 5 : ℝ) * ((1 / bR + 1 / cR) * Real.log (cR / bR) - 2 * (1 / bR - 1 / cR))) * (1 / x0) := by
      intro x0 hx0
      rw [uIcc_of_le ha01] at hx0
      have hstep1 : ∀ x1 ∈ uIcc bR cR,
          (∫ x2 in x1..cR, ∫ x3 in x2..cR, G_rhs (x0, x1, x2, x3)) =
          ((4 / 5 : ℝ) / x0) * ((1 / x1) * ((Real.log (cR / x1) - 1) / x1 + 1 / cR)) := by
        intro x1 hx1
        rw [uIcc_of_le hbc] at hx1
        have hstep2 : ∀ x2 ∈ uIcc x1 cR,
            (∫ x3 in x2..cR, G_rhs (x0, x1, x2, x3)) =
            ((4 / 5 : ℝ) / x0 * (1 / x1)) * (Real.log (cR / x2) / x2 ^ 2) := by
          intro x2 hx2
          rw [uIcc_of_le hx1.2] at hx2
          have h2p : 0 < x2 := lt_of_lt_of_le (lt_of_lt_of_le hb_pos hx1.1) hx2.1
          have hrew : (fun x3 => G_rhs (x0, x1, x2, x3)) =
              fun x3 => ((4 / 5 : ℝ) / (x0 * x1 * x2 ^ 2)) * (1 / x3) := by
            ext x3; simp only [G_rhs]; ring
          rw [hrew, intervalIntegral.integral_const_mul, h_inv_int x2 cR h2p hx2.2]; ring
        rw [intervalIntegral.integral_congr hstep2, intervalIntegral.integral_const_mul, h_x2_eval x1 hx1]
        ring
      rw [intervalIntegral.integral_congr hstep1, intervalIntegral.integral_const_mul, h_x1_eval]
      ring
    rw [intervalIntegral.integral_congr hstep, intervalIntegral.integral_const_mul, h_inv_int a0R a1R ha0_pos ha01]
    ring
  rw [hrhs_eval] at hle_set
  -- Bound log(a1R/a0R) = log(1 + 63/290) and log(cR/bR) = log(1 + 6/55) via log_one_add_le_rat
  have hl0_arg : a1R / a0R = 1 + (63 / 290 : ℝ) := by unfold a0R a1R; norm_num
  have hl0 : Real.log (a1R / a0R) ≤ (63 / 290 : ℝ) * (6 + 63 / 290) / (6 + 4 * (63 / 290)) := by
    rw [hl0_arg]; exact log_one_add_le_rat (by norm_num)
  have hl0_nn : 0 ≤ Real.log (a1R / a0R) := Real.log_nonneg (by rw [hl0_arg]; norm_num)
  have hlc_arg : cR / bR = 1 + (6 / 55 : ℝ) := by unfold bR cR; norm_num
  have hlc : Real.log (cR / bR) ≤ (6 / 55 : ℝ) * (6 + 6 / 55) / (6 + 4 * (6 / 55)) := by
    rw [hlc_arg]; exact log_one_add_le_rat (by norm_num)
  have hm3_le : (1 / bR + 1 / cR) * Real.log (cR / bR) - 2 * (1 / bR - 1 / cR) ≤
      (1 / bR + 1 / cR) * ((6 / 55 : ℝ) * (6 + 6 / 55) / (6 + 4 * (6 / 55))) - 2 * (1 / bR - 1 / cR) := by
    have hpos_coef : 0 ≤ 1 / bR + 1 / cR := by unfold bR cR; norm_num
    nlinarith
  have hm3_nn : 0 ≤ (1 / bR + 1 / cR) * ((6 / 55 : ℝ) * (6 + 6 / 55) / (6 + 4 * (6 / 55))) - 2 * (1 / bR - 1 / cR) := by
    unfold bR cR; norm_num
  have hprod : (4 / 5 : ℝ) * Real.log (a1R / a0R) *
      ((1 / bR + 1 / cR) * Real.log (cR / bR) - 2 * (1 / bR - 1 / cR)) ≤
      (4 / 5 : ℝ) * ((63 / 290 : ℝ) * (6 + 63 / 290) / (6 + 4 * (63 / 290))) *
      ((1 / bR + 1 / cR) * ((6 / 55 : ℝ) * (6 + 6 / 55) / (6 + 4 * (6 / 55))) - 2 * (1 / bR - 1 / cR)) := by
    have h1 := mul_le_mul_of_nonneg_left hm3_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5) hl0_nn)
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl0 (by norm_num : (0 : ℝ) ≤ 4 / 5)) hm3_nn
    linarith
  have hnum : (4 / 5 : ℝ) * ((63 / 290 : ℝ) * (6 + 63 / 290) / (6 + 4 * (63 / 290))) *
      ((1 / bR + 1 / cR) * ((6 / 55 : ℝ) * (6 + 6 / 55) / (6 + 4 * (6 / 55))) - 2 * (1 / bR - 1 / cR)) ≤
      ((70737 / 1000000000) : ℝ) := by
    unfold bR cR; norm_num
  linarith

/-! ### Part 4c: Exact Reduction to 1D Convolution I(φ) = ∫_{a0}^{a1} (1/x0) J(φ - x0) dx0 -/

private lemma inner_x3_eq_g_real {t x2 : ℝ} (hxb : bR ≤ x2) (hxc : x2 ≤ cR) :
    ∫ x3 in x2..cR, (if x3 ≤ t - 2 * x2 then 1 / (x2 * x3 * (t - x2 - x3)) else 0) = g_real t x2 := by
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have h2p : 0 < x2 := lt_of_lt_of_le hb_pos hxb
  by_cases h3 : t ≤ 3 * x2
  · have hg0 : g_real t x2 = 0 := by unfold g_real; rw [if_pos h3]
    rw [hg0, intervalIntegral.integral_of_le hxc]
    refine (setIntegral_congr_ae measurableSet_Ioc ?_).trans (by simp : ∫ _ in Ioc x2 cR, (0 : ℝ) = 0)
    filter_upwards with x3 hx3
    have hnot : ¬ (x3 ≤ t - 2 * x2) := by linarith [hx3.1]
    exact if_neg hnot
  · push Not at h3
    let U : ℝ := min cR (t - 2 * x2)
    have hx2U : x2 ≤ U := le_min hxc (by linarith)
    have hUc : U ≤ cR := min_le_left _ _
    have hUt : U ≤ t - 2 * x2 := min_le_right _ _
    have htx2 : 0 < t - x2 := by linarith
    have hcont : ContinuousOn (fun x3 : ℝ => 1 / (x2 * x3 * (t - x2 - x3))) (Icc x2 U) := by
      refine continuousOn_const.div ((continuousOn_const.mul continuousOn_id).mul
        (continuousOn_const.sub continuousOn_id)) ?_
      intro x3 hx3
      have h3p : 0 < x3 := lt_of_lt_of_le h2p hx3.1
      have hdiff : 0 < t - x2 - x3 := by linarith [hx3.2]
      exact ne_of_gt (mul_pos (mul_pos h2p h3p) hdiff)
    have hsplit : ∫ x3 in x2..cR, (if x3 ≤ t - 2 * x2 then 1 / (x2 * x3 * (t - x2 - x3)) else 0) =
        ∫ x3 in x2..U, 1 / (x2 * x3 * (t - x2 - x3)) := by
      have h1 : IntervalIntegrable (fun x3 => if x3 ≤ t - 2 * x2 then 1 / (x2 * x3 * (t - x2 - x3)) else 0) volume x2 U :=
        (hcont.intervalIntegrable_of_Icc hx2U).congr (fun x3 hx3 => by
          rw [uIoc_of_le hx2U] at hx3; exact (if_pos (le_trans hx3.2 hUt)).symm)
      have h2 : IntervalIntegrable (fun x3 => if x3 ≤ t - 2 * x2 then 1 / (x2 * x3 * (t - x2 - x3)) else 0) volume U cR := by
        refine (intervalIntegrable_const (c := (0 : ℝ))).congr_ae ?_
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le hUc]
        filter_upwards with x3 hx3
        have : ¬ (x3 ≤ t - 2 * x2) := by
          have : U = t - 2 * x2 := by
            rcases eq_or_lt_of_le hUc with heq | hlt
            · exfalso; linarith [hx3.1, hx3.2]
            · exact min_eq_right (by
                by_contra hcon; push Not at hcon
                have : U = cR := min_eq_left (le_of_lt hcon)
                linarith)
          linarith [hx3.1]
        exact (if_neg this).symm
      rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
      have hz2 : ∫ x3 in U..cR, (if x3 ≤ t - 2 * x2 then 1 / (x2 * x3 * (t - x2 - x3)) else 0) = 0 := by
        rw [intervalIntegral.integral_of_le hUc]
        refine (setIntegral_congr_ae measurableSet_Ioc ?_).trans (by simp : ∫ _ in Ioc U cR, (0 : ℝ) = 0)
        filter_upwards with x3 hx3
        have : ¬ (x3 ≤ t - 2 * x2) := by
          have hlt : U < cR := lt_of_lt_of_le hx3.1 hx3.2
          have : U = t - 2 * x2 := min_eq_right (by
            by_contra hcon; push Not at hcon
            have : U = cR := min_eq_left (le_of_lt hcon); linarith)
          linarith [hx3.1]
        exact if_neg this
      have hl : ∫ x3 in x2..U, (if x3 ≤ t - 2 * x2 then 1 / (x2 * x3 * (t - x2 - x3)) else 0) =
          ∫ x3 in x2..U, 1 / (x2 * x3 * (t - x2 - x3)) :=
        intervalIntegral.integral_congr (fun x3 hx3 => by
          rw [uIcc_of_le hx2U] at hx3; exact if_pos (le_trans hx3.2 hUt))
      rw [hl, hz2, add_zero]
    rw [hsplit]
    have hF : ∀ y ∈ uIcc x2 U, HasDerivAt
        (fun x3 => (Real.log x3 - Real.log (t - x2 - x3)) / (x2 * (t - x2)))
        (1 / (x2 * y * (t - x2 - y))) y := by
      intro y hy
      rw [uIcc_of_le hx2U] at hy
      have hyp : 0 < y := lt_of_lt_of_le h2p hy.1
      have hdiff : 0 < t - x2 - y := by linarith [hy.2]
      have hd1 : HasDerivAt Real.log (1 / y) y :=
        (Real.hasDerivAt_log (ne_of_gt hyp)) ▸d (by ring)
      have hd2 : HasDerivAt (fun x3 => Real.log (t - x2 - x3)) (-1 / (t - x2 - y)) y := by
        have hlin : HasDerivAt (fun x3 => t - x2 - x3) (-1) y :=
          ((hasDerivAt_const y (t - x2)).fun_sub (hasDerivAt_id' y)) ▸d (by ring)
        exact (hlin.log (ne_of_gt hdiff)) ▸d (by ring)
      exact ((hd1.fun_sub hd2).div_const (x2 * (t - x2))) ▸d (by
        field_simp [ne_of_gt h2p, ne_of_gt hyp, ne_of_gt htx2, ne_of_gt hdiff]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable_of_Icc hx2U)]
    unfold g_real
    rw [if_neg (not_le.mpr h3)]
    dsimp only
    have hUp : 0 < U := lt_of_lt_of_le h2p hx2U
    have hdU : 0 < t - x2 - U := by linarith
    have hdx2 : 0 < t - x2 - x2 := by linarith
    have h1 : Real.log (U / x2) = Real.log U - Real.log x2 := Real.log_div (ne_of_gt hUp) (ne_of_gt h2p)
    have h2 : Real.log ((t - 2 * x2) / (t - x2 - U)) = Real.log (t - 2 * x2) - Real.log (t - x2 - U) :=
      Real.log_div (by linarith) (ne_of_gt hdU)
    have hsub : t - x2 - x2 = t - 2 * x2 := by ring
    rw [h1, h2, hsub]
    ring


noncomputable def J_real (u : ℝ) : ℝ :=
  ∫ x1 in bR..cR, (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2)

private lemma J_real_nonneg (u : ℝ) : 0 ≤ J_real u := by
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  unfold J_real
  refine intervalIntegral.integral_nonneg hbc (fun x1 hx1 => mul_nonneg
    (div_nonneg zero_le_one (le_of_lt (lt_of_lt_of_le hb_pos hx1.1))) ?_)
  exact intervalIntegral.integral_nonneg hx1.2 (fun x2 hx2 => g_real_nonneg (le_trans hx1.1 hx2.1) hx2.2)

private lemma g_real_norm_le_M :
    ∀ t : ℝ, ∀ x2 ∈ Icc bR cR, ‖g_real t x2‖ ≤ 2 * Real.log (cR / bR) / (bR * (cR + bR)) := by
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  have hc_pos : (0 : ℝ) < cR := lt_of_lt_of_le hb_pos hbc
  intro t x2 hx2
  rw [Real.norm_of_nonneg (g_real_nonneg hx2.1 hx2.2)]
  have hpeak : g_real t x2 ≤ g_real (2 * x2 + cR) x2 := by
    by_cases h1 : t ≤ 2 * x2 + cR
    · exact g_real_mono_left hx2.1 hx2.2 h1 le_rfl
    · exact g_real_anti_right hx2.1 hx2.2 le_rfl (le_of_lt (not_le.mp h1))
  rw [g_real_eq_peak hx2.2] at hpeak
  refine le_trans hpeak ?_
  have hxp : 0 < x2 := lt_of_lt_of_le hb_pos hx2.1
  have hlog_le : Real.log (cR / x2) ≤ Real.log (cR / bR) :=
    Real.log_le_log (div_pos hc_pos hxp) (div_le_div_of_nonneg_left (le_of_lt hc_pos) hb_pos hx2.1)
  have hlog_nn : 0 ≤ Real.log (cR / bR) := Real.log_nonneg (by rw [one_le_div hb_pos]; exact hbc)
  have hden_ge : bR * (cR + bR) ≤ x2 * (cR + x2) := by nlinarith [hx2.1]
  exact le_trans (div_le_div_of_nonneg_right (by linarith) (le_of_lt (mul_pos hxp (by linarith))))
    (div_le_div_of_nonneg_left (by linarith) (mul_pos hb_pos (by linarith)) hden_ge)

private lemma J_integrand_continuousOn (u : ℝ) :
    ContinuousOn (fun x1 : ℝ => (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2)) (Icc bR cR) := by
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  let M : ℝ := 2 * Real.log (cR / bR) / (bR * (cR + bR))
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (g_real_norm_le_M 0 bR ⟨le_rfl, hbc⟩)
  intro x1 hx1
  have h1p : 0 < x1 := lt_of_lt_of_le hb_pos hx1.1
  have hinv : ContinuousWithinAt (fun x : ℝ => 1 / x) (Icc bR cR) x1 :=
    continuousWithinAt_const.div continuousWithinAt_id (ne_of_gt h1p)
  have hint_cont : ContinuousWithinAt (fun x : ℝ => ∫ x2 in x..cR, g_real (u - x) x2) (Icc bR cR) x1 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have huc : UniformContinuousOn (fun p : ℝ × ℝ => g_real p.1 p.2)
        (Icc (u - cR) (u - bR) ×ˢ Icc bR cR) :=
      (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
        (g_real_continuousOn.mono (Set.prod_mono (Set.subset_univ _) subset_rfl))
    rw [Metric.uniformContinuousOn_iff] at huc
    have hlen_pos : 0 < cR - bR := by unfold bR cR; norm_num
    obtain ⟨δ1, hδ1_pos, hδ1⟩ := huc (ε / (2 * (cR - bR))) (by positivity)
    let δ := min δ1 (ε / (2 * (M + 1)))
    refine ⟨δ, lt_min hδ1_pos (by positivity), fun x hx hdist => ?_⟩
    have hdist1 : dist x x1 < δ1 := lt_of_lt_of_le hdist (min_le_left _ _)
    have hdist2 : dist x x1 < ε / (2 * (M + 1)) := lt_of_lt_of_le hdist (min_le_right _ _)
    have hg_int : ∀ a d : ℝ, ∀ t : ℝ, bR ≤ a → a ≤ cR → bR ≤ d → d ≤ cR →
        IntervalIntegrable (fun x2 => g_real t x2) volume a d := fun a d t ha1 ha2 hd1 hd2 => by
      have hc_t : ContinuousOn (fun x2 => g_real t x2) (Icc bR cR) :=
        g_real_continuousOn.comp (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨trivial, hz⟩)
      exact (hc_t.mono (uIcc_subset_Icc ⟨ha1, ha2⟩ ⟨hd1, hd2⟩)).intervalIntegrable
    have hsplit : (∫ x2 in x..cR, g_real (u - x) x2) - (∫ x2 in x1..cR, g_real (u - x1) x2) =
        (∫ x2 in x..x1, g_real (u - x) x2) +
        (∫ x2 in x1..cR, (g_real (u - x) x2 - g_real (u - x1) x2)) := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hg_int x x1 (u - x) hx.1 hx.2 hx1.1 hx1.2)
        (hg_int x1 cR (u - x) hx1.1 hx1.2 hbc le_rfl)
      have h2 := intervalIntegral.integral_sub
        (hg_int x1 cR (u - x) hx1.1 hx1.2 hbc le_rfl)
        (hg_int x1 cR (u - x1) hx1.1 hx1.2 hbc le_rfl)
      linarith
    rw [Real.dist_eq, hsplit]
    have hpart1 : |∫ x2 in x..x1, g_real (u - x) x2| ≤ M * |x1 - x| := by
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := M)
        (f := fun x2 => g_real (u - x) x2) (a := x) (b := x1)
        (fun x2 hx2 => g_real_norm_le_M (u - x) x2 (uIoc_subset_uIcc.trans (uIcc_subset_Icc hx hx1) hx2))
      rwa [Real.norm_eq_abs] at hle
    have hpart2 : |∫ x2 in x1..cR, (g_real (u - x) x2 - g_real (u - x1) x2)| ≤
        (ε / (2 * (cR - bR))) * (cR - x1) := by
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / (2 * (cR - bR)))
        (f := fun x2 => g_real (u - x) x2 - g_real (u - x1) x2) (a := x1) (b := cR)
        (fun x2 hx2 => by
          rw [uIoc_of_le hx1.2] at hx2
          have hx2_mem : x2 ∈ Icc bR cR := ⟨le_trans hx1.1 (le_of_lt hx2.1), hx2.2⟩
          have hd_pair : dist ((u - x, x2) : ℝ × ℝ) (u - x1, x2) < δ1 := by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
            have hsub : (u - x) - (u - x1) = x1 - x := by ring
            rw [hsub, abs_sub_comm]; exact hdist1
          have hval := hδ1 (u - x, x2) ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, hx2_mem⟩
            (u - x1, x2) ⟨⟨by linarith [hx1.2], by linarith [hx1.1]⟩, hx2_mem⟩ hd_pair
          rw [Real.norm_eq_abs]; exact le_of_lt hval)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx1.2)] at hle
      exact hle
    have h1_lt : M * |x1 - x| < ε / 2 := by
      have habs : |x1 - x| < ε / (2 * (M + 1)) := by simpa [Real.dist_eq, abs_sub_comm] using hdist2
      have hMp : 0 < M + 1 := by linarith
      calc M * |x1 - x| ≤ (M + 1) * |x1 - x| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (M + 1) * (ε / (2 * (M + 1))) := mul_lt_mul_of_pos_left habs hMp
        _ = ε / 2 := by field_simp [ne_of_gt hMp]
    have h2_le : (ε / (2 * (cR - bR))) * (cR - x1) ≤ ε / 2 := by
      calc (ε / (2 * (cR - bR))) * (cR - x1) ≤ (ε / (2 * (cR - bR))) * (cR - bR) :=
            mul_le_mul_of_nonneg_left (by linarith [hx1.1]) (by positivity)
        _ = ε / 2 := by field_simp [ne_of_gt hlen_pos]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
  exact hinv.mul hint_cont

private lemma J_real_continuous : Continuous J_real := by
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  let M : ℝ := 2 * Real.log (cR / bR) / (bR * (cR + bR))
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (g_real_norm_le_M 0 bR ⟨le_rfl, hbc⟩)
  unfold J_real
  rw [continuous_iff_continuousAt]
  intro u0
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => (1 / bR) * (M * (cR - bR))) ?_ ?_ intervalIntegrable_const ?_
  · refine Filter.Eventually.of_forall (fun u => ?_)
    exact ((J_integrand_continuousOn u).aestronglyMeasurable measurableSet_Icc).mono_set
      (by rw [uIoc_of_le hbc]; exact Ioc_subset_Icc_self)
  · refine Filter.Eventually.of_forall (fun u => ?_)
    filter_upwards with x1 hx1
    rw [uIoc_of_le hbc] at hx1
    have h1p : 0 < x1 := lt_of_lt_of_le hb_pos (le_of_lt hx1.1)
    rw [norm_mul, Real.norm_of_nonneg (div_nonneg zero_le_one (le_of_lt h1p))]
    have hinv_le : 1 / x1 ≤ 1 / bR := div_le_div_of_nonneg_left zero_le_one hb_pos (le_of_lt hx1.1)
    have hinner_le : ‖∫ x2 in x1..cR, g_real (u - x1) x2‖ ≤ M * (cR - bR) := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (C := M)
        (f := fun x2 => g_real (u - x1) x2) (a := x1) (b := cR) (fun x2 hx2 => by
          rw [uIoc_of_le hx1.2] at hx2
          exact g_real_norm_le_M (u - x1) x2 ⟨le_trans (le_of_lt hx1.1) (le_of_lt hx2.1), hx2.2⟩)
      rw [abs_of_nonneg (sub_nonneg.mpr hx1.2)] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_left (by linarith [hx1.1]) hM_nn)
    exact mul_le_mul hinv_le hinner_le (norm_nonneg _) (by positivity)
  · filter_upwards with x1 hx1
    rw [uIoc_of_le hbc] at hx1
    refine continuousAt_const.mul ?_
    refine intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ => M) ?_ ?_ intervalIntegrable_const ?_
    · refine Filter.Eventually.of_forall (fun u => ?_)
      have hc : ContinuousOn (fun x2 => g_real (u - x1) x2) (Icc x1 cR) :=
        g_real_continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
          (fun x2 hx2 => ⟨trivial, le_trans (le_of_lt hx1.1) hx2.1, hx2.2⟩)
      exact (hc.aestronglyMeasurable measurableSet_Icc).mono_set
        (by rw [uIoc_of_le hx1.2]; exact Ioc_subset_Icc_self)
    · refine Filter.Eventually.of_forall (fun u => Filter.Eventually.of_forall (fun x2 hx2 => ?_))
      rw [uIoc_of_le hx1.2] at hx2
      exact g_real_norm_le_M (u - x1) x2 ⟨le_trans (le_of_lt hx1.1) (le_of_lt hx2.1), hx2.2⟩
    · filter_upwards with x2 hx2
      rw [uIoc_of_le hx1.2] at hx2
      have hmem : (u0 - x1, x2) ∈ (Set.univ : Set ℝ) ×ˢ Icc bR cR :=
        ⟨trivial, le_trans (le_of_lt hx1.1) (le_of_lt hx2.1), hx2.2⟩
      have hcomp : ContinuousOn (fun u : ℝ => g_real (u - x1) x2) Set.univ :=
        g_real_continuousOn.comp ((continuous_id.sub continuous_const).prodMk continuous_const).continuousOn
          (fun u _ => ⟨trivial, hmem.2⟩)
      exact hcomp.continuousAt Filter.univ_mem

private lemma r0j19_buchstabIntegral_eq_conv {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (_hφ2 : 2 ≤ φ) (hφhi : φ ≤ (229 / 100 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ =
      ∫ x0 in a0R..a1R, (1 / x0) * J_real (φ - x0) := by
  have ha01 : a0R ≤ a1R := by unfold a0R a1R; norm_num
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  have ha0_pos : (0 : ℝ) < a0R := by unfold a0R; norm_num
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  rw [buchstabIntegral_eq_iterated hω hz φ]
  apply intervalIntegral.integral_congr
  intro x0 hx0
  rw [uIcc_of_le ha01] at hx0
  have h0p : 0 < x0 := lt_of_lt_of_le ha0_pos hx0.1
  dsimp only
  unfold J_real
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x1 hx1
  rw [uIcc_of_le hbc] at hx1
  have h1p : 0 < x1 := lt_of_lt_of_le hb_pos hx1.1
  dsimp only
  rw [← mul_assoc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x2 hx2
  rw [uIcc_of_le hx1.2] at hx2
  have h2b : bR ≤ x2 := le_trans hx1.1 hx2.1
  have h2p : 0 < x2 := lt_of_lt_of_le hb_pos h2b
  dsimp only
  rw [← inner_x3_eq_g_real (t := φ - x0 - x1) h2b hx2.2, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x3 hx3
  rw [uIcc_of_le hx2.2] at hx3
  have h3p : 0 < x3 := lt_of_lt_of_le h2p hx3.1
  dsimp only
  set u := (φ - x0 - x1 - x2 - x3) / x2
  have hu_le2 : u ≤ 2 := by
    rw [div_le_iff₀ h2p]
    have hnum : (229 / 100 : ℝ) - a0R - 3 * bR ≤ 2 * bR := by unfold a0R bR; norm_num
    linarith [hx0.1, hx1.1, hx2.1, hx3.1, h2b]
  by_cases hcond : x3 ≤ φ - x0 - x1 - 2 * x2
  · rw [if_pos hcond]
    have hu_ge1 : 1 ≤ u := by rw [le_div_iff₀ h2p]; linarith
    rw [hω.2.1 u hu_ge1 hu_le2]
    have hden_pos : 0 < φ - x0 - x1 - x2 - x3 := by linarith
    simp only [u]
    field_simp [ne_of_gt h0p, ne_of_gt h1p, ne_of_gt h2p, ne_of_gt h3p, ne_of_gt hden_pos]
  · rw [if_neg hcond, mul_zero]
    have hu_lt1 : u < 1 := by rw [div_lt_iff₀ h2p]; linarith
    rw [hz u hu_lt1, zero_div]


/-! ### Part 5: Soundness of the Integer Certificate Checker -/

private lemma ceilDiv_sound {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (ceilDiv a b : ℝ) := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbr]
  have h1 : b * ((a + b - 1) / b) + (a + b - 1) % b = a + b - 1 := Nat.div_add_mod (a + b - 1) b
  have h2 : (a + b - 1) % b < b := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ ((a + b - 1) / b) * b := by
    have : b * ((a + b - 1) / b) = ((a + b - 1) / b) * b := Nat.mul_comm _ _
    omega
  unfold ceilDiv
  exact_mod_cast h3

private lemma log1pNat_sound {p q : ℕ} (hq : 0 < q) :
    Real.log (1 + (p : ℝ) / (q : ℝ)) ≤ (log1pNat p q : ℝ) / S_sc := by
  unfold log1pNat
  by_cases hp : p = 0
  · subst hp; simp
  · have hbeq : (p == 0) = false := beq_false_of_ne hp
    rw [hbeq]
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
    have hy : 0 ≤ (p : ℝ) / q := div_nonneg (Nat.cast_nonneg _) (le_of_lt hqr)
    have hlog := log_one_add_le_rat hy
    have hrat : (p : ℝ) / q * (6 + (p : ℝ) / q) / (6 + 4 * ((p : ℝ) / q)) =
        ((S_sc * p * (6 * q + p) : ℕ) : ℝ) / ((q * (6 * q + 4 * p) : ℕ) : ℝ) / S_sc := by
      push_cast
      have hden : (6 * (q : ℝ) + 4 * p) ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) p]
      have hden2 : 6 + 4 * ((p : ℝ) / q) ≠ 0 := by linarith
      field_simp [ne_of_gt hqr, ne_of_gt hS, hden, hden2]
    rw [hrat] at hlog
    have hq_pos : 0 < q * (6 * q + 4 * p) := Nat.mul_pos hq (by omega)
    exact le_trans hlog (div_le_div_of_nonneg_right (ceilDiv_sound hq_pos) (le_of_lt hS))

private lemma gNat_sound {t_n x_n : ℕ} (hx1 : B_num ≤ x_n) (hx2 : x_n ≤ C_num) :
    g_real ((t_n : ℝ) / D_den) ((x_n : ℝ) / D_den) ≤ (gNat t_n x_n : ℝ) / S_sc := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  have hx_pos : 0 < x_n := by unfold B_num at hx1; omega
  have hxr : (0 : ℝ) < x_n := by exact_mod_cast hx_pos
  unfold g_real gNat
  rw [cR_eq]
  by_cases h3 : t_n ≤ 3 * x_n
  · have h3r : (t_n : ℝ) / D_den ≤ 3 * ((x_n : ℝ) / D_den) := by
      have : 3 * ((x_n : ℝ) / D_den) = ((3 * x_n : ℕ) : ℝ) / D_den := by push_cast; ring
      rw [this]; exact div_le_div_of_nonneg_right (by exact_mod_cast h3) (le_of_lt hD)
    rw [if_pos h3, if_pos h3r]; simp
  · push Not at h3
    have h3r : ¬ ((t_n : ℝ) / D_den ≤ 3 * ((x_n : ℝ) / D_den)) := by
      push Not
      have : 3 * ((x_n : ℝ) / D_den) = ((3 * x_n : ℕ) : ℝ) / D_den := by push_cast; ring
      rw [this]; exact div_lt_div_of_pos_right (by exact_mod_cast h3) hD
    rw [if_neg (not_le.mpr h3), if_neg h3r]
    dsimp only
    set R_n := t_n - x_n
    set U_n := min C_num (R_n - x_n)
    have hR_eq : (R_n : ℝ) = (t_n : ℝ) - x_n := Nat.cast_sub (by omega)
    have hU_eq : min ((C_num : ℝ) / D_den) ((t_n : ℝ) / D_den - 2 * ((x_n : ℝ) / D_den)) = (U_n : ℝ) / D_den := by
      have hRx : (t_n : ℝ) / D_den - 2 * ((x_n : ℝ) / D_den) = ((R_n - x_n : ℕ) : ℝ) / D_den := by
        rw [Nat.cast_sub (by omega), hR_eq]; ring
      rw [hRx]
      have hmin_r : (U_n : ℝ) / D_den = min ((C_num : ℝ) / D_den) (((R_n - x_n : ℕ) : ℝ) / D_den) := by
        simp only [U_n, Nat.cast_min, min_div_div_right (le_of_lt hD)]
      exact hmin_r.symm
    rw [hU_eq]
    by_cases hUx : U_n ≤ x_n
    · rw [if_pos hUx]
      have hU_ge : x_n ≤ U_n := le_min hx2 (by omega)
      have hU_eq_x : U_n = x_n := le_antisymm hUx hU_ge
      rw [hU_eq_x, div_self (ne_of_gt (div_pos hxr hD)), Real.log_one, zero_add]
      have hsub : (t_n : ℝ) / D_den - (x_n : ℝ) / D_den - (x_n : ℝ) / D_den =
          (t_n : ℝ) / D_den - 2 * ((x_n : ℝ) / D_den) := by ring
      rw [hsub]
      have ht2x_pos : 0 < (t_n : ℝ) / D_den - 2 * ((x_n : ℝ) / D_den) := by
        have : (3 * x_n : ℝ) < t_n := by exact_mod_cast h3
        have hrew : 2 * ((x_n : ℝ) / D_den) = (2 * x_n : ℝ) / D_den := by ring
        rw [sub_pos, hrew, div_lt_div_iff_of_pos_right hD]; linarith
      rw [div_self (ne_of_gt ht2x_pos), Real.log_one, zero_div]; simp
    · push Not at hUx
      rw [if_neg (not_le.mpr hUx)]
      set p := U_n - x_n
      have hRU_pos : 0 < R_n - U_n := by
        have : U_n ≤ R_n - x_n := min_le_right _ _
        omega
      have hR_pos : 0 < R_n := by omega
      have hp_eq : (p : ℝ) = (U_n : ℝ) - x_n := Nat.cast_sub (le_of_lt hUx)
      have hRU_eq : ((R_n - U_n : ℕ) : ℝ) = (R_n : ℝ) - U_n := Nat.cast_sub (by omega)
      have hl1_arg : (U_n : ℝ) / D_den / ((x_n : ℝ) / D_den) = 1 + (p : ℝ) / x_n := by
        rw [hp_eq]; field_simp [ne_of_gt hD, ne_of_gt hxr]; ring
      have hl2_arg : ((t_n : ℝ) / D_den - 2 * ((x_n : ℝ) / D_den)) /
          ((t_n : ℝ) / D_den - (x_n : ℝ) / D_den - (U_n : ℝ) / D_den) = 1 + (p : ℝ) / ((R_n - U_n : ℕ) : ℝ) := by
        have hRU_r : (0 : ℝ) < (R_n - U_n : ℕ) := by exact_mod_cast hRU_pos
        rw [hRU_eq] at hRU_r ⊢
        rw [hR_eq] at hRU_r ⊢
        rw [hp_eq]
        have hden : (t_n : ℝ) / D_den - (x_n : ℝ) / D_den - (U_n : ℝ) / D_den = ((t_n : ℝ) - x_n - U_n) / D_den := by ring
        rw [hden]
        have hne : (t_n : ℝ) - x_n - U_n ≠ 0 := ne_of_gt hRU_r
        field_simp [ne_of_gt hD, hne]; ring
      rw [hl1_arg, hl2_arg]
      have hl1 := log1pNat_sound (p := p) hx_pos
      have hl2 := log1pNat_sound (p := p) hRU_pos
      have hRr : (0 : ℝ) < R_n := by exact_mod_cast hR_pos
      have hden_eq : (x_n : ℝ) / D_den * ((t_n : ℝ) / D_den - (x_n : ℝ) / D_den) =
          ((x_n * R_n : ℕ) : ℝ) / (D2 : ℝ) := by
        unfold D2; push_cast; rw [hR_eq]; ring
      rw [hden_eq]
      have hD2 : (0 : ℝ) < D2 := by unfold D2 D_den; norm_num
      have hsum_le : Real.log (1 + (p : ℝ) / x_n) + Real.log (1 + (p : ℝ) / ((R_n - U_n : ℕ) : ℝ)) ≤
          ((log1pNat p x_n + log1pNat p (R_n - U_n) : ℕ) : ℝ) / S_sc := by
        push_cast; rw [add_div]; linarith
      have hstep := div_le_div_of_nonneg_right hsum_le (div_nonneg (Nat.cast_nonneg (x_n * R_n)) (le_of_lt hD2))
      have hrew : ((log1pNat p x_n + log1pNat p (R_n - U_n) : ℕ) : ℝ) / S_sc /
          (((x_n * R_n : ℕ) : ℝ) / (D2 : ℝ)) =
          ((D2 * (log1pNat p x_n + log1pNat p (R_n - U_n)) : ℕ) : ℝ) / ((x_n * R_n : ℕ) : ℝ) / S_sc := by
        push_cast; field_simp [ne_of_gt hS, ne_of_gt hD2, ne_of_gt hxr, ne_of_gt hRr]
      rw [hrew] at hstep
      exact le_trans hstep (div_le_div_of_nonneg_right (ceilDiv_sound (Nat.mul_pos hx_pos hR_pos)) (le_of_lt hS))

private lemma gmNat_sound {t_lo t_hi x_n : ℕ} (hx1 : B_num ≤ x_n) (hx2 : x_n ≤ C_num) :
    gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) ((x_n : ℝ) / D_den) ≤ (gmNat t_lo t_hi x_n : ℝ) / S_sc := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  unfold gm_real gmNat
  rw [cR_eq]
  dsimp only
  have htp : 2 * ((x_n : ℝ) / D_den) + (C_num : ℝ) / D_den = ((2 * x_n + C_num : ℕ) : ℝ) / D_den := by
    push_cast; ring
  rw [htp]
  by_cases h1 : t_hi ≤ 2 * x_n + C_num
  · have h1r : (t_hi : ℝ) / D_den ≤ ((2 * x_n + C_num : ℕ) : ℝ) / D_den :=
      div_le_div_of_nonneg_right (by exact_mod_cast h1) (le_of_lt hD)
    rw [if_pos h1, if_pos h1r]; exact gNat_sound hx1 hx2
  · have h1r : ¬ ((t_hi : ℝ) / D_den ≤ ((2 * x_n + C_num : ℕ) : ℝ) / D_den) := by
      push Not; exact div_lt_div_of_pos_right (by exact_mod_cast (not_le.mp h1)) hD
    rw [if_neg h1, if_neg h1r]
    by_cases h2 : 2 * x_n + C_num ≤ t_lo
    · have h2r : ((2 * x_n + C_num : ℕ) : ℝ) / D_den ≤ (t_lo : ℝ) / D_den :=
        div_le_div_of_nonneg_right (by exact_mod_cast h2) (le_of_lt hD)
      rw [if_pos h2, if_pos h2r]; exact gNat_sound hx1 hx2
    · have h2r : ¬ (((2 * x_n + C_num : ℕ) : ℝ) / D_den ≤ (t_lo : ℝ) / D_den) := by
        push Not; exact div_lt_div_of_pos_right (by exact_mod_cast (not_le.mp h2)) hD
      rw [if_neg h2, if_neg h2r]; exact gNat_sound hx1 hx2

private lemma gm_real_continuousOn {t_lo t_hi : ℝ} (hlo : t_lo ≤ t_hi) :
    ContinuousOn (fun x => gm_real t_lo t_hi x) (Icc bR cR) := by
  have heq : ∀ x ∈ Icc bR cR, gm_real t_lo t_hi x = g_real (max t_lo (min t_hi (2 * x + cR))) x := by
    intro x _
    unfold gm_real; dsimp only
    split_ifs with h1 h2
    · rw [min_eq_left h1, max_eq_right hlo]
    · push Not at h1
      rw [min_eq_right (le_of_lt h1), max_eq_left h2]
    · push Not at h1 h2
      rw [min_eq_right (le_of_lt h1), max_eq_right (le_of_lt h2)]
  refine ContinuousOn.congr ?_ heq
  have hclamp : Continuous (fun x : ℝ => max t_lo (min t_hi (2 * x + cR))) :=
    continuous_const.max (continuous_const.min ((continuous_const.mul continuous_id).add continuous_const))
  exact g_real_continuousOn.comp (hclamp.continuousOn.prodMk continuousOn_id) (fun x hx => ⟨trivial, hx⟩)

private lemma trapK_le_real {t_lo t_hi K xl xr : ℕ}
    (hbl : B_num ≤ xl) (hlr : xl ≤ xr) (hrc : xr ≤ C_num)
    (hint : ∫ x in ((xl : ℝ) / D_den)..((xr : ℝ) / D_den),
        gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤
      ((gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) ((xl : ℝ) / D_den) +
        gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) ((xr : ℝ) / D_den)) / 2) *
        ((xr : ℝ) / D_den - (xl : ℝ) / D_den) +
      ((K : ℝ) / 12) * ((xr : ℝ) / D_den - (xl : ℝ) / D_den) ^ 3) :
    ∫ x in ((xl : ℝ) / D_den)..((xr : ℝ) / D_den),
      gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤ (trapK t_lo t_hi K xl xr : ℝ) / S_sc := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  unfold trapK
  by_cases hle : xr ≤ xl
  · have heq : xl = xr := le_antisymm hlr hle
    subst heq; simp
  · push Not at hle
    rw [if_neg (not_le.mpr hle)]
    dsimp only
    set dx := xr - xl
    have hdx_eq : (dx : ℝ) = (xr : ℝ) - xl := Nat.cast_sub hlr
    have hdiff : (xr : ℝ) / D_den - (xl : ℝ) / D_den = (dx : ℝ) / D_den := by rw [hdx_eq]; ring
    have hgl := gmNat_sound (t_lo := t_lo) (t_hi := t_hi) hbl (le_trans hlr hrc)
    have hgr := gmNat_sound (t_lo := t_lo) (t_hi := t_hi) (le_trans hbl hlr) hrc
    have htrap_step :
        ((gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) ((xl : ℝ) / D_den) +
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) ((xr : ℝ) / D_den)) / 2) *
          ((xr : ℝ) / D_den - (xl : ℝ) / D_den) ≤
        (ceilDiv ((gmNat t_lo t_hi xl + gmNat t_lo t_hi xr) * dx) TwoD : ℝ) / S_sc := by
      rw [hdiff]
      have h1 : ((gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) ((xl : ℝ) / D_den) +
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) ((xr : ℝ) / D_den)) / 2) * ((dx : ℝ) / D_den) ≤
          (((gmNat t_lo t_hi xl : ℝ) / S_sc + (gmNat t_lo t_hi xr : ℝ) / S_sc) / 2) * ((dx : ℝ) / D_den) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (add_le_add hgl hgr) (by norm_num))
          (div_nonneg (Nat.cast_nonneg _) (le_of_lt hD))
      have h2 : (((gmNat t_lo t_hi xl : ℝ) / S_sc + (gmNat t_lo t_hi xr : ℝ) / S_sc) / 2) * ((dx : ℝ) / D_den) =
          (((gmNat t_lo t_hi xl + gmNat t_lo t_hi xr) * dx : ℕ) : ℝ) / (TwoD : ℝ) / S_sc := by
        unfold TwoD; push_cast; field_simp [ne_of_gt hD, ne_of_gt hS]
      rw [h2] at h1
      have h2D_pos : 0 < TwoD := by unfold TwoD D_den; omega
      exact le_trans h1 (div_le_div_of_nonneg_right (ceilDiv_sound h2D_pos) (le_of_lt hS))
    have herr_step :
        ((K : ℝ) / 12) * ((xr : ℝ) / D_den - (xl : ℝ) / D_den) ^ 3 ≤
        ((if K == 0 then 0 else ceilDiv (S_sc * K * dx * dx * dx) TwelveD3 : ℕ) : ℝ) / S_sc := by
      by_cases hK0 : K = 0
      · subst hK0; simp
      · have hbeq : (K == 0) = false := beq_false_of_ne hK0
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        rw [hdiff]
        have hTwelve_eq : (TwelveD3 : ℝ) = 12 * (D_den : ℝ) * D_den * D_den := by
          simp only [TwelveD3, Nat.cast_mul, Nat.cast_ofNat]
        have hrew : ((K : ℝ) / 12) * ((dx : ℝ) / D_den) ^ 3 =
            ((S_sc * K * dx * dx * dx : ℕ) : ℝ) / (TwelveD3 : ℝ) / S_sc := by
          rw [hTwelve_eq]; push_cast; field_simp [ne_of_gt hD, ne_of_gt hS]
        rw [hrew]
        have hD_pos_n : 0 < D_den := by unfold D_den; omega
        have h12_pos : 0 < TwelveD3 := by
          rw [show TwelveD3 = 12 * D_den * D_den * D_den from rfl]
          exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hD_pos_n) hD_pos_n) hD_pos_n
        exact div_le_div_of_nonneg_right (ceilDiv_sound h12_pos) (le_of_lt hS)
    rw [Nat.cast_add, add_div]
    linarith

private lemma evalInterval_sound {t_lo t_hi xa xb xc xl xr : ℕ}
    (hbl : B_num ≤ xl) (hlr : xl ≤ xr) (hrc : xr ≤ C_num)
    (htlo : C_num < t_lo) (htlh : t_lo ≤ t_hi)
    (hxa : 2 * xa = t_lo - C_num) (hxb : 2 * xb = t_hi - C_num) (hxc : 3 * xc = t_hi) :
    ∫ x in ((xl : ℝ) / D_den)..((xr : ℝ) / D_den),
      gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤
      (evalInterval t_lo t_hi xa xb xc xl xr : ℝ) / S_sc := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  have htlh_r : (t_lo : ℝ) / D_den ≤ (t_hi : ℝ) / D_den :=
    div_le_div_of_nonneg_right (by exact_mod_cast htlh) (le_of_lt hD)
  have hgm_cont : ContinuousOn (fun x => gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) (Icc bR cR) :=
    gm_real_continuousOn htlh_r
  have hgm_int : ∀ u v : ℕ, B_num ≤ u → u ≤ v → v ≤ C_num →
      IntervalIntegrable (fun x => gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) volume
        ((u : ℝ) / D_den) ((v : ℝ) / D_den) := by
    intro u v hu huv hv
    have hu_r : bR ≤ (u : ℝ) / D_den := by rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hu) (le_of_lt hD)
    have hv_r : (v : ℝ) / D_den ≤ cR := by rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hv) (le_of_lt hD)
    have huv_r : (u : ℝ) / D_den ≤ (v : ℝ) / D_den := div_le_div_of_nonneg_right (by exact_mod_cast huv) (le_of_lt hD)
    exact (hgm_cont.mono (Icc_subset_Icc hu_r hv_r)).intervalIntegrable_of_Icc huv_r
  let p1 := min xr (max xl xa)
  let p2 := min xr (max xl xb)
  let p3 := min xr (max xl xc)
  have hxab : xa ≤ xb := by omega
  have hp1_ge : xl ≤ p1 := le_min hlr (le_max_left _ _)
  have hp12 : p1 ≤ p2 := min_le_min_left xr (max_le_max_left xl hxab)
  have hp23 : p2 ≤ p3 := by
    by_cases h3c : t_hi ≤ 3 * C_num
    · have hxbc : xb ≤ xc := by omega
      exact min_le_min_left xr (max_le_max_left xl hxbc)
    · have hxc_gt : C_num < xc := by omega
      have hxb_gt : C_num < xb := by omega
      have hp2_eq : p2 = xr := min_eq_left (le_trans hrc (le_trans (le_of_lt hxb_gt) (le_max_right _ _)))
      have hp3_eq : p3 = xr := min_eq_left (le_trans hrc (le_trans (le_of_lt hxc_gt) (le_max_right _ _)))
      omega
  have hp3_le : p3 ≤ xr := min_le_left _ _
  have hsplit1 :
      ∫ x in ((xl : ℝ) / D_den)..((xr : ℝ) / D_den), gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x =
      (∫ x in ((xl : ℝ) / D_den)..((p1 : ℝ) / D_den), gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) +
      (∫ x in ((p1 : ℝ) / D_den)..((p2 : ℝ) / D_den), gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) +
      (∫ x in ((p2 : ℝ) / D_den)..((p3 : ℝ) / D_den), gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) +
      (∫ x in ((p3 : ℝ) / D_den)..((xr : ℝ) / D_den), gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) := by
    have i1 := hgm_int xl p1 hbl hp1_ge (by omega)
    have i2 := hgm_int p1 p2 (by omega) hp12 (by omega)
    have i3 := hgm_int p2 p3 (by omega) hp23 (by omega)
    have i4 := hgm_int p3 xr (by omega) hp3_le hrc
    have i12 := i1.trans i2
    have i123 := i12.trans i3
    rw [← intervalIntegral.integral_add_adjacent_intervals i123 i4,
        ← intervalIntegral.integral_add_adjacent_intervals i12 i3,
        ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have hR1 : ∫ x in ((xl : ℝ) / D_den)..((p1 : ℝ) / D_den),
      gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤
      (trapK t_lo t_hi 55 xl (min xr xa) : ℝ) / S_sc := by
    by_cases hlt : xl < p1
    · set xr1 := min xr xa
      have hp1_eq : p1 = xr1 := by omega
      rw [hp1_eq]
      have hlr1 : xl ≤ xr1 := by omega
      have hrc1 : xr1 ≤ C_num := le_trans (min_le_left _ _) hrc
      have hxa1 : xr1 ≤ xa := min_le_right _ _
      have h2x_le : 2 * ((xr1 : ℝ) / D_den) + cR ≤ (t_lo : ℝ) / D_den := by
        rw [cR_eq]
        have : 2 * xr1 + C_num ≤ t_lo := by omega
        have hcast : 2 * ((xr1 : ℝ) / D_den) + (C_num : ℝ) / D_den =
            ((2 * xr1 + C_num : ℕ) : ℝ) / D_den := by push_cast; ring
        rw [hcast]; exact div_le_div_of_nonneg_right (by exact_mod_cast this) (le_of_lt hD)
      have heq_gm : ∀ x ∈ Icc ((xl : ℝ) / D_den) ((xr1 : ℝ) / D_den),
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x = g_real ((t_lo : ℝ) / D_den) x := by
        intro x hx
        unfold gm_real; dsimp only
        have h2x : 2 * x + cR ≤ (t_lo : ℝ) / D_den := by linarith [hx.2]
        by_cases hhi : (t_hi : ℝ) / D_den ≤ 2 * x + cR
        · rw [if_pos hhi]; have : (t_hi : ℝ) / D_den = (t_lo : ℝ) / D_den := by linarith
          rw [this]
        · rw [if_neg hhi, if_pos h2x]
      apply trapK_le_real hbl hlr1 hrc1
      have hlr1_r : (xl : ℝ) / D_den ≤ (xr1 : ℝ) / D_den :=
        div_le_div_of_nonneg_right (by exact_mod_cast hlr1) (le_of_lt hD)
      have hint1 : ∫ x in ((xl : ℝ) / D_den)..((xr1 : ℝ) / D_den), gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x =
          ∫ x in ((xl : ℝ) / D_den)..((xr1 : ℝ) / D_den), g_real ((t_lo : ℝ) / D_den) x :=
        intervalIntegral.integral_congr (fun x hx => by rw [uIcc_of_le hlr1_r] at hx; exact heq_gm x hx)
      rw [hint1, heq_gm _ (left_mem_Icc.mpr hlr1_r), heq_gm _ (right_mem_Icc.mpr hlr1_r)]
      simpa using g1_integral_le_trap
        (by rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hbl) (le_of_lt hD))
        hlr1_r
        (by rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hrc1) (le_of_lt hD))
        h2x_le
    · have heq : p1 = xl := by omega
      rw [heq, intervalIntegral.integral_same]
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hS)
  have hR2 : ∫ x in ((p1 : ℝ) / D_den)..((p2 : ℝ) / D_den),
      gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤
      (trapK t_lo t_hi 0 (max xl xa) (min xr xb) : ℝ) / S_sc := by
    by_cases hlt : p1 < p2
    · set xl2 := max xl xa
      set xr2 := min xr xb
      have hp1_eq : p1 = xl2 := by omega
      have hp2_eq : p2 = xr2 := by omega
      rw [hp1_eq, hp2_eq]
      have hbl2 : B_num ≤ xl2 := le_trans hbl (le_max_left _ _)
      have hlr2 : xl2 ≤ xr2 := by omega
      have hrc2 : xr2 ≤ C_num := le_trans (min_le_left _ _) hrc
      have heq_gm : ∀ x ∈ Icc ((xl2 : ℝ) / D_den) ((xr2 : ℝ) / D_den),
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x = g_real (2 * x + cR) x := by
        intro x hx
        unfold gm_real; dsimp only
        have hlo_le : (t_lo : ℝ) / D_den ≤ 2 * x + cR := by
          rw [cR_eq]
          have h1 : xa ≤ xl2 := le_max_right _ _
          have h2 : t_lo ≤ 2 * xl2 + C_num := by omega
          have h3 : (t_lo : ℝ) / D_den ≤ 2 * ((xl2 : ℝ) / D_den) + (C_num : ℝ) / D_den := by
            have hc : 2 * ((xl2 : ℝ) / D_den) + (C_num : ℝ) / D_den =
                ((2 * xl2 + C_num : ℕ) : ℝ) / D_den := by push_cast; ring
            rw [hc]; exact div_le_div_of_nonneg_right (by exact_mod_cast h2) (le_of_lt hD)
          linarith [hx.1]
        have hhi_ge : 2 * x + cR ≤ (t_hi : ℝ) / D_den := by
          rw [cR_eq]
          have h1 : xr2 ≤ xb := min_le_right _ _
          have h2 : 2 * xr2 + C_num ≤ t_hi := by omega
          have h3 : 2 * ((xr2 : ℝ) / D_den) + (C_num : ℝ) / D_den ≤ (t_hi : ℝ) / D_den := by
            have hc : 2 * ((xr2 : ℝ) / D_den) + (C_num : ℝ) / D_den =
                ((2 * xr2 + C_num : ℕ) : ℝ) / D_den := by push_cast; ring
            rw [hc]; exact div_le_div_of_nonneg_right (by exact_mod_cast h2) (le_of_lt hD)
          linarith [hx.2]
        split_ifs with h1 h2
        · have : (t_hi : ℝ) / D_den = 2 * x + cR := by linarith
          rw [this]
        · have : (t_lo : ℝ) / D_den = 2 * x + cR := by linarith
          rw [this]
        · rfl
      apply trapK_le_real hbl2 hlr2 hrc2
      have hlr2_r : (xl2 : ℝ) / D_den ≤ (xr2 : ℝ) / D_den :=
        div_le_div_of_nonneg_right (by exact_mod_cast hlr2) (le_of_lt hD)
      have hint2 : ∫ x in ((xl2 : ℝ) / D_den)..((xr2 : ℝ) / D_den), gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x =
          ∫ x in ((xl2 : ℝ) / D_den)..((xr2 : ℝ) / D_den), g_real (2 * x + cR) x :=
        intervalIntegral.integral_congr (fun x hx => by rw [uIcc_of_le hlr2_r] at hx; exact heq_gm x hx)
      rw [hint2, heq_gm _ (left_mem_Icc.mpr hlr2_r), heq_gm _ (right_mem_Icc.mpr hlr2_r)]
      have hg := gpeak_integral_le_trap
        (by rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hbl2) (le_of_lt hD))
        hlr2_r
        (by rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hrc2) (le_of_lt hD))
      simpa using hg
    · have heq : p2 = p1 := by omega
      rw [heq, intervalIntegral.integral_same]
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hS)
  have hR3 : ∫ x in ((p2 : ℝ) / D_den)..((p3 : ℝ) / D_den),
      gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤
      (trapK t_lo t_hi 110 (max xl xb) (min xr xc) : ℝ) / S_sc := by
    by_cases hlt : p2 < p3
    · set xl3 := max xl xb
      set xr3 := min xr xc
      have hp2_eq : p2 = xl3 := by omega
      have hp3_eq : p3 = xr3 := by omega
      rw [hp2_eq, hp3_eq]
      have hbl3 : B_num ≤ xl3 := le_trans hbl (le_max_left _ _)
      have hlr3 : xl3 ≤ xr3 := by omega
      have hrc3 : xr3 ≤ C_num := le_trans (min_le_left _ _) hrc
      have ht1 : 3 * ((xr3 : ℝ) / D_den) ≤ (t_hi : ℝ) / D_den := by
        have h1 : 3 * xr3 ≤ t_hi := by
          have : xr3 ≤ xc := min_le_right _ _
          omega
        have hc : 3 * ((xr3 : ℝ) / D_den) = ((3 * xr3 : ℕ) : ℝ) / D_den := by push_cast; ring
        rw [hc]; exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (le_of_lt hD)
      have ht2 : (t_hi : ℝ) / D_den ≤ 2 * ((xl3 : ℝ) / D_den) + cR := by
        rw [cR_eq]
        have h1 : t_hi ≤ 2 * xl3 + C_num := by
          have : xb ≤ xl3 := le_max_right _ _
          omega
        have hc : 2 * ((xl3 : ℝ) / D_den) + (C_num : ℝ) / D_den =
            ((2 * xl3 + C_num : ℕ) : ℝ) / D_den := by push_cast; ring
        rw [hc]; exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (le_of_lt hD)
      have heq_gm : ∀ x ∈ Icc ((xl3 : ℝ) / D_den) ((xr3 : ℝ) / D_den),
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x = g_real ((t_hi : ℝ) / D_den) x := by
        intro x hx
        unfold gm_real; dsimp only
        rw [if_pos (by linarith [hx.1])]
      apply trapK_le_real hbl3 hlr3 hrc3
      have hlr3_r : (xl3 : ℝ) / D_den ≤ (xr3 : ℝ) / D_den :=
        div_le_div_of_nonneg_right (by exact_mod_cast hlr3) (le_of_lt hD)
      have hint3 : ∫ x in ((xl3 : ℝ) / D_den)..((xr3 : ℝ) / D_den), gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x =
          ∫ x in ((xl3 : ℝ) / D_den)..((xr3 : ℝ) / D_den), g_real ((t_hi : ℝ) / D_den) x :=
        intervalIntegral.integral_congr (fun x hx => by rw [uIcc_of_le hlr3_r] at hx; exact heq_gm x hx)
      rw [hint3, heq_gm _ (left_mem_Icc.mpr hlr3_r), heq_gm _ (right_mem_Icc.mpr hlr3_r)]
      simpa using g2_integral_le_trap
        (by rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hbl3) (le_of_lt hD))
        hlr3_r
        (by rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hrc3) (le_of_lt hD))
        ht1 ht2
    · have heq : p3 = p2 := by omega
      rw [heq, intervalIntegral.integral_same]
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hS)
  have hR4 : ∫ x in ((p3 : ℝ) / D_den)..((xr : ℝ) / D_den),
      gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x = 0 := by
    by_cases hlt : p3 < xr
    · have hp3_ge : xc ≤ p3 := by omega
      have hp3_le_r : (p3 : ℝ) / D_den ≤ (xr : ℝ) / D_den :=
        div_le_div_of_nonneg_right (by exact_mod_cast hp3_le) (le_of_lt hD)
      have hz : ∀ x ∈ uIcc ((p3 : ℝ) / D_den) ((xr : ℝ) / D_den),
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x = 0 := by
        intro x hx
        rw [uIcc_of_le hp3_le_r] at hx
        have h3x : (t_hi : ℝ) / D_den ≤ 3 * x := by
          have h1 : t_hi ≤ 3 * p3 := by omega
          have h2 : (t_hi : ℝ) / D_den ≤ 3 * ((p3 : ℝ) / D_den) := by
            have hc : 3 * ((p3 : ℝ) / D_den) = ((3 * p3 : ℕ) : ℝ) / D_den := by push_cast; ring
            rw [hc]; exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (le_of_lt hD)
          linarith [hx.1]
        have hxc_r : x ≤ cR := by
          rw [cR_eq]
          exact le_trans hx.2 (div_le_div_of_nonneg_right (by exact_mod_cast hrc) (le_of_lt hD))
        unfold gm_real; dsimp only
        rw [if_pos (by linarith)]
        unfold g_real; rw [if_pos h3x]
      rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
    · have heq : p3 = xr := by omega
      rw [heq, intervalIntegral.integral_same]
  unfold evalInterval
  rw [hsplit1, hR4, add_zero, Nat.cast_add, Nat.cast_add, add_div, add_div]
  linarith


/-! ### Soundness of evalBinFast, checkS8, checkKer, checkJ8, checkJWin, checkW0Go, checkSlices -/

private lemma evalBinFast_eq_evalInterval {t_lo t_hi xa xb xc hy err55 err110 xl : ℕ}
    (_hbl : B_num ≤ xl) (hlrc : xl + hy ≤ C_num) (hhy_pos : 0 < hy)
    (htlo : C_num < t_lo) (htlh : t_lo ≤ t_hi)
    (hxa : 2 * xa = t_lo - C_num) (hxb : 2 * xb = t_hi - C_num) (hxc : 3 * xc = t_hi)
    (herr55 : err55 = ceilDiv (S_sc * 55 * hy * hy * hy) TwelveD3)
    (herr110 : err110 = ceilDiv (S_sc * 110 * hy * hy * hy) TwelveD3)
    (hgl : ∀ _h : xl < xc, True) :
    evalInterval t_lo t_hi xa xb xc xl (xl + hy) ≤
      evalBinFast t_lo t_hi xa xb xc hy err55 err110 xl
        (if xc ≤ xl then 0 else gmNat t_lo t_hi xl)
        (if xc ≤ xl then 0 else gmNat t_lo t_hi (xl + hy)) := by
  have hxab : xa ≤ xb := by omega
  unfold evalBinFast evalInterval
  dsimp only
  split_ifs with h1 h2 h3 h4
  · -- xc <= xl
    have hxb_le : xb ≤ xl := by omega
    have hxa_le : xa ≤ xl := le_trans hxab hxb_le
    have hmin1 : min (xl + hy) xa ≤ xl := le_trans (min_le_right _ _) hxa_le
    have hmin2 : min (xl + hy) xb ≤ max xl xa := le_trans (min_le_right _ _) (le_trans hxb_le (le_max_left _ _))
    have hmin3 : min (xl + hy) xc ≤ max xl xb := le_trans (min_le_right _ _) (le_trans h1 (le_max_left _ _))
    simp only [trapK, hmin1, hmin2, hmin3, ↓reduceIte, add_zero, le_refl]
  · -- ¬(xc ≤ xl), xl + hy ≤ xa
    have hmin1 : min (xl + hy) xa = xl + hy := min_eq_left h2
    have hmax1 : max xl xa = xa := max_eq_right (by omega)
    have hmin2 : min (xl + hy) xb ≤ xa := le_trans (min_le_left _ _) h2
    have hmin3 : min (xl + hy) xc ≤ max xl xb := le_trans (min_le_left _ _) (le_trans h2 (le_trans hxab (le_max_right _ _)))
    rw [hmin1, hmax1]
    simp only [trapK, hmin2, hmin3, ↓reduceIte, add_zero]
    have hnot : ¬ (xl + hy ≤ xl) := by omega
    rw [if_neg hnot]
    have hsub : xl + hy - xl = hy := by omega
    rw [hsub, herr55]; simp
  · -- ¬(xc ≤ xl), ¬(xl + hy ≤ xa), xa ≤ xl && xl + hy ≤ xb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    have hmin1 : min (xl + hy) xa ≤ xl := le_trans (min_le_right _ _) h3.1
    have hmax1 : max xl xa = xl := max_eq_left h3.1
    have hmin2 : min (xl + hy) xb = xl + hy := min_eq_left h3.2
    have hmax2 : max xl xb = xb := max_eq_right (by omega)
    have hmin3 : min (xl + hy) xc ≤ xb := le_trans (min_le_left _ _) h3.2
    rw [hmax1, hmin2, hmax2]
    simp only [trapK, hmin1, hmin3, ↓reduceIte, zero_add, add_zero]
    have hnot : ¬ (xl + hy ≤ xl) := by omega
    rw [if_neg hnot]
    have hsub : xl + hy - xl = hy := by omega
    rw [hsub]; simp
  · -- ¬(xc ≤ xl), ¬(xl + hy ≤ xa), ¬(...), xb ≤ xl && xl + hy ≤ xc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
    have hmin1 : min (xl + hy) xa ≤ xl := le_trans (min_le_right _ _) (le_trans hxab h4.1)
    have hmin2 : min (xl + hy) xb ≤ max xl xa := le_trans (min_le_right _ _) (le_trans h4.1 (le_max_left _ _))
    have hmax2 : max xl xb = xl := max_eq_left h4.1
    have hmin3 : min (xl + hy) xc = xl + hy := min_eq_left h4.2
    rw [hmax2, hmin3]
    simp only [trapK, hmin1, hmin2, ↓reduceIte, zero_add]
    have hnot : ¬ (xl + hy ≤ xl) := by omega
    rw [if_neg hnot]
    have hsub : xl + hy - xl = hy := by omega
    rw [hsub, herr110]; simp
  · exact le_rfl

private lemma evalBinFast_sound {t_lo t_hi xa xb xc hy err55 err110 xl gl gr : ℕ}
    (hbl : B_num ≤ xl) (hlrc : xl + hy ≤ C_num) (hhy_pos : 0 < hy)
    (htlo : C_num < t_lo) (htlh : t_lo ≤ t_hi)
    (hxa : 2 * xa = t_lo - C_num) (hxb : 2 * xb = t_hi - C_num) (hxc : 3 * xc = t_hi)
    (herr55 : err55 = ceilDiv (S_sc * 55 * hy * hy * hy) TwelveD3)
    (herr110 : err110 = ceilDiv (S_sc * 110 * hy * hy * hy) TwelveD3)
    (hgl : xl < xc → gl = gmNat t_lo t_hi xl)
    (hgr : xl < xc → gr = gmNat t_lo t_hi (xl + hy)) :
    ∫ x in ((xl : ℝ) / D_den)..(((xl + hy : ℕ) : ℝ) / D_den),
      gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤
      (evalBinFast t_lo t_hi xa xb xc hy err55 err110 xl gl gr : ℝ) / S_sc := by
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  have h1 := evalInterval_sound hbl (by omega) hlrc htlo htlh hxa hxb hxc
  have h2 := evalBinFast_eq_evalInterval hbl hlrc hhy_pos htlo htlh hxa hxb hxc herr55 herr110 (fun _ => trivial)
  have h3 : evalBinFast t_lo t_hi xa xb xc hy err55 err110 xl
      (if xc ≤ xl then 0 else gmNat t_lo t_hi xl)
      (if xc ≤ xl then 0 else gmNat t_lo t_hi (xl + hy)) =
      evalBinFast t_lo t_hi xa xb xc hy err55 err110 xl gl gr := by
    by_cases hle : xc ≤ xl
    · unfold evalBinFast; simp [hle]
    · push Not at hle
      simp only [if_neg (not_le.mpr hle), hgl hle, hgr hle]
  rw [h3] at h2
  exact le_trans h1 (div_le_div_of_nonneg_right (by exact_mod_cast h2) (le_of_lt hS))

private lemma evalRow8_sound {t_lo x0 h hy err55 err110 v8 : ℕ}
    (hx0b : B_num ≤ x0) (hx8c : x0 + 8 * hy ≤ C_num) (hhy_pos : 0 < hy)
    (hh_le : 2 * h ≤ X_span_num) (hh6 : h % 6 = 0) (ht6 : t_lo % 6 = 0)
    (herr55 : err55 = ceilDiv (S_sc * 55 * hy * hy * hy) TwelveD3)
    (herr110 : err110 = ceilDiv (S_sc * 110 * hy * hy * hy) TwelveD3)
    (hnext : ∫ x in (((x0 + 8 * hy : ℕ) : ℝ) / D_den)..cR,
      gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (v8 : ℝ) / S_sc) :
    let r := evalRow8 t_lo x0 h hy err55 err110 v8
    (∫ x in (((x0 + 0 * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (r.1 : ℝ) / S_sc) ∧
    (∫ x in (((x0 + 1 * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (r.2.1 : ℝ) / S_sc) ∧
    (∫ x in (((x0 + 2 * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (r.2.2.1 : ℝ) / S_sc) ∧
    (∫ x in (((x0 + 3 * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (r.2.2.2.1 : ℝ) / S_sc) ∧
    (∫ x in (((x0 + 4 * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (r.2.2.2.2.1 : ℝ) / S_sc) ∧
    (∫ x in (((x0 + 5 * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (r.2.2.2.2.2.1 : ℝ) / S_sc) ∧
    (∫ x in (((x0 + 6 * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (r.2.2.2.2.2.2.1 : ℝ) / S_sc) ∧
    (∫ x in (((x0 + 7 * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) (((t_lo + 2 * h : ℕ) : ℝ) / D_den) x ≤ (r.2.2.2.2.2.2.2 : ℝ) / S_sc) := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  dsimp only
  unfold evalRow8
  set t_hi := t_lo + 2 * h
  have htlh : t_lo ≤ t_hi := by omega
  have htlh_r : (t_lo : ℝ) / D_den ≤ (t_hi : ℝ) / D_den :=
    div_le_div_of_nonneg_right (by exact_mod_cast htlh) (le_of_lt hD)
  have hgm_int : ∀ u v : ℕ, B_num ≤ u → u ≤ v → v ≤ C_num →
      IntervalIntegrable (fun x => gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) volume
        ((u : ℝ) / D_den) ((v : ℝ) / D_den) := fun u v hu huv hv => by
    have hcont := gm_real_continuousOn htlh_r
    have hu_r : bR ≤ (u : ℝ) / D_den := by rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hu) (le_of_lt hD)
    have hv_r : (v : ℝ) / D_den ≤ cR := by rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hv) (le_of_lt hD)
    have huv_r : (u : ℝ) / D_den ≤ (v : ℝ) / D_den := div_le_div_of_nonneg_right (by exact_mod_cast huv) (le_of_lt hD)
    exact (hcont.mono (Icc_subset_Icc hu_r hv_r)).intervalIntegrable_of_Icc huv_r
  by_cases hzero : t_hi ≤ 3 * x0
  · simp only [if_pos hzero]
    have hzero_int : ∀ k ≤ 7, ∫ x in (((x0 + k * hy : ℕ) : ℝ) / D_den)..cR,
        gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x = 0 := by
      intro k hk
      have hk8 : k * hy ≤ 8 * hy := Nat.mul_le_mul_right hy (by omega)
      have hle_c : (((x0 + k * hy : ℕ) : ℝ) / D_den) ≤ cR := by
        rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : x0 + k * hy ≤ C_num)) (le_of_lt hD)
      have hcongr : ∀ x ∈ uIcc (((x0 + k * hy : ℕ) : ℝ) / D_den) cR,
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x = 0 := by
        intro x hx
        rw [uIcc_of_le hle_c] at hx
        have h3x : (t_hi : ℝ) / D_den ≤ 3 * x := by
          have h1 : (t_hi : ℝ) / D_den ≤ 3 * ((x0 : ℝ) / D_den) := by
            have hc : 3 * ((x0 : ℝ) / D_den) = ((3 * x0 : ℕ) : ℝ) / D_den := by push_cast; ring
            rw [hc]; exact div_le_div_of_nonneg_right (by exact_mod_cast hzero) (le_of_lt hD)
          have h2 : (x0 : ℝ) / D_den ≤ ((x0 + k * hy : ℕ) : ℝ) / D_den :=
            div_le_div_of_nonneg_right (by exact_mod_cast (by omega : x0 ≤ x0 + k * hy)) (le_of_lt hD)
          linarith [hx.1]
        unfold gm_real; dsimp only
        have htp : (t_hi : ℝ) / D_den ≤ 2 * x + cR := by linarith [hx.2]
        rw [if_pos htp]; unfold g_real; rw [if_pos h3x]
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hzero_int 0 (by omega)]; simp
    · rw [hzero_int 1 (by omega)]; simp
    · rw [hzero_int 2 (by omega)]; simp
    · rw [hzero_int 3 (by omega)]; simp
    · rw [hzero_int 4 (by omega)]; simp
    · rw [hzero_int 5 (by omega)]; simp
    · rw [hzero_int 6 (by omega)]; simp
    · rw [hzero_int 7 (by omega)]; simp
  · push Not at hzero
    simp only [if_neg (not_le.mpr hzero)]
    have hC_lt_tlo : C_num < t_lo := by
      have hB_eq : B_num = 810770400 := rfl
      have hC_eq : C_num = 899218080 := rfl
      have hX_eq : X_span_num = 88447680 := rfl
      omega
    have hC6 : C_num % 6 = 0 := by unfold C_num; omega
    have hxa : 2 * ((t_lo - C_num) / 2) = t_lo - C_num := by omega
    have hxb : 2 * ((t_hi - C_num) / 2) = t_hi - C_num := by omega
    have hxc : 3 * (t_hi / 3) = t_hi := by omega
    have hstep_bin : ∀ (k : ℕ) (hk : k ≤ 7) (gl gr : ℕ),
        (x0 + k * hy < t_hi / 3 → gl = gmNat t_lo t_hi (x0 + k * hy)) →
        (x0 + k * hy < t_hi / 3 → gr = gmNat t_lo t_hi (x0 + k * hy + hy)) →
        ∫ x in (((x0 + k * hy : ℕ) : ℝ) / D_den)..(((x0 + (k + 1) * hy : ℕ) : ℝ) / D_den),
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤
        (evalBinFast t_lo t_hi ((t_lo - C_num) / 2) ((t_hi - C_num) / 2) (t_hi / 3)
          hy err55 err110 (x0 + k * hy) gl gr : ℝ) / S_sc := by
      intro k hk gl gr hgl hgr
      have hadd : x0 + (k + 1) * hy = x0 + k * hy + hy := by ring
      have hk8 : (k + 1) * hy ≤ 8 * hy := Nat.mul_le_mul_right hy (by omega)
      rw [hadd]
      exact evalBinFast_sound (by omega) (by omega) hhy_pos hC_lt_tlo htlh hxa hxb hxc herr55 herr110 hgl hgr
    have hsplit : ∀ k ≤ 7,
        ∫ x in (((x0 + k * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x =
        (∫ x in (((x0 + k * hy : ℕ) : ℝ) / D_den)..(((x0 + (k + 1) * hy : ℕ) : ℝ) / D_den),
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) +
        (∫ x in (((x0 + (k + 1) * hy : ℕ) : ℝ) / D_den)..cR, gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x) := by
      intro k hk
      have hk_le : k * hy ≤ (k + 1) * hy := Nat.mul_le_mul_right hy (by omega)
      have hk8 : (k + 1) * hy ≤ 8 * hy := Nat.mul_le_mul_right hy (by omega)
      rw [cR_eq]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hgm_int (x0 + k * hy) (x0 + (k + 1) * hy) (by omega) (by omega) (by omega))
        (hgm_int (x0 + (k + 1) * hy) C_num (by omega) (by omega) le_rfl)).symm
    have hstep_back : ∀ (k : ℕ) (hk : k ≤ 7) (s_next b_k : ℕ),
        (∫ x in (((x0 + k * hy : ℕ) : ℝ) / D_den)..(((x0 + (k + 1) * hy : ℕ) : ℝ) / D_den),
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤ (b_k : ℝ) / S_sc) →
        (∫ x in (((x0 + (k + 1) * hy : ℕ) : ℝ) / D_den)..cR,
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤ (s_next : ℝ) / S_sc) →
        ∫ x in (((x0 + k * hy : ℕ) : ℝ) / D_den)..cR,
          gm_real ((t_lo : ℝ) / D_den) ((t_hi : ℝ) / D_den) x ≤ ((b_k + s_next : ℕ) : ℝ) / S_sc := by
      intro k hk s_next b_k hbk hsn
      rw [hsplit k hk, Nat.cast_add b_k s_next, add_div]; linarith
    have hb7 := hstep_bin 7 (by omega)
      (if t_hi / 3 ≤ x0 + 6 * hy then 0 else gmNat t_lo t_hi (x0 + 7 * hy))
      (if t_hi / 3 ≤ x0 + 7 * hy then 0 else gmNat t_lo t_hi (x0 + 8 * hy))
      (fun hlt => by rw [if_neg (by omega)])
      (fun hlt => by rw [if_neg (by omega)]; congr 1; ring)
    have hb6 := hstep_bin 6 (by omega)
      (if t_hi / 3 ≤ x0 + 5 * hy then 0 else gmNat t_lo t_hi (x0 + 6 * hy))
      (if t_hi / 3 ≤ x0 + 6 * hy then 0 else gmNat t_lo t_hi (x0 + 7 * hy))
      (fun hlt => by rw [if_neg (by omega)])
      (fun hlt => by rw [if_neg (by omega)]; congr 1; ring)
    have hb5 := hstep_bin 5 (by omega)
      (if t_hi / 3 ≤ x0 + 4 * hy then 0 else gmNat t_lo t_hi (x0 + 5 * hy))
      (if t_hi / 3 ≤ x0 + 5 * hy then 0 else gmNat t_lo t_hi (x0 + 6 * hy))
      (fun hlt => by rw [if_neg (by omega)])
      (fun hlt => by rw [if_neg (by omega)]; congr 1; ring)
    have hb4 := hstep_bin 4 (by omega)
      (if t_hi / 3 ≤ x0 + 3 * hy then 0 else gmNat t_lo t_hi (x0 + 4 * hy))
      (if t_hi / 3 ≤ x0 + 4 * hy then 0 else gmNat t_lo t_hi (x0 + 5 * hy))
      (fun hlt => by rw [if_neg (by omega)])
      (fun hlt => by rw [if_neg (by omega)]; congr 1; ring)
    have hb3 := hstep_bin 3 (by omega)
      (if t_hi / 3 ≤ x0 + 2 * hy then 0 else gmNat t_lo t_hi (x0 + 3 * hy))
      (if t_hi / 3 ≤ x0 + 3 * hy then 0 else gmNat t_lo t_hi (x0 + 4 * hy))
      (fun hlt => by rw [if_neg (by omega)])
      (fun hlt => by rw [if_neg (by omega)]; congr 1; ring)
    have hb2 := hstep_bin 2 (by omega)
      (if t_hi / 3 ≤ x0 + 1 * hy then 0 else gmNat t_lo t_hi (x0 + 2 * hy))
      (if t_hi / 3 ≤ x0 + 2 * hy then 0 else gmNat t_lo t_hi (x0 + 3 * hy))
      (fun hlt => by rw [if_neg (by omega)])
      (fun hlt => by rw [if_neg (by omega)]; congr 1; ring)
    have hb1 := hstep_bin 1 (by omega)
      (if t_hi / 3 ≤ x0 + 0 * hy then 0 else gmNat t_lo t_hi (x0 + 1 * hy))
      (if t_hi / 3 ≤ x0 + 1 * hy then 0 else gmNat t_lo t_hi (x0 + 2 * hy))
      (fun hlt => by rw [if_neg (by omega)])
      (fun hlt => by rw [if_neg (by omega)]; congr 1; ring)
    have hb0 := hstep_bin 0 (by omega)
      (gmNat t_lo t_hi (x0 + 0 * hy))
      (if t_hi / 3 ≤ x0 + 0 * hy then 0 else gmNat t_lo t_hi (x0 + 1 * hy))
      (fun _ => rfl)
      (fun hlt => by rw [if_neg (by omega)]; congr 1; ring)
    have hs7 := hstep_back 7 (by omega) _ _ hb7 hnext
    have hs6 := hstep_back 6 (by omega) _ _ hb6 hs7
    have hs5 := hstep_back 5 (by omega) _ _ hb5 hs6
    have hs4 := hstep_back 4 (by omega) _ _ hb4 hs5
    have hs3 := hstep_back 3 (by omega) _ _ hb3 hs4
    have hs2 := hstep_back 2 (by omega) _ _ hb2 hs3
    have hs1 := hstep_back 1 (by omega) _ _ hb1 hs2
    have hs0 := hstep_back 0 (by omega) _ _ hb0 hs1
    exact ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩

private lemma wLNat_sound {s_sub hy h r d : ℕ}
    (hs_pos : 0 < s_sub) (hh_pos : 0 < h) (hhy_eq : hy = s_sub * h) (hd : d < s_sub) :
    ∫ x in (((B_num + r * hy + d * h : ℕ) : ℝ) / D_den)..(((B_num + r * hy + (d + 1) * h : ℕ) : ℝ) / D_den),
      (((B_num + (r + 1) * hy : ℕ) : ℝ) / D_den - x) / (((hy : ℝ) / D_den) * x) ≤
      (wLNat s_sub hy h r d : ℝ) / S_sc := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  have hB_pos : 0 < B_num := by unfold B_num; omega
  set yr := B_num + r * hy
  set yr1 := yr + hy
  set xi := yr + d * h
  set xi1 := xi + h
  have hxi_pos_n : 0 < xi := by omega
  have hxi1_pos_n : 0 < xi1 := by omega
  have hhy_pos_n : 0 < hy := by rw [hhy_eq]; exact Nat.mul_pos hs_pos hh_pos
  have hxi_pos : (0 : ℝ) < (xi : ℝ) / D_den := div_pos (by exact_mod_cast hxi_pos_n) hD
  have hhy_pos : (0 : ℝ) < (hy : ℝ) / D_den := div_pos (by exact_mod_cast hhy_pos_n) hD
  have hxi_le_xi1 : (xi : ℝ) / D_den ≤ (xi1 : ℝ) / D_den :=
    div_le_div_of_nonneg_right (by exact_mod_cast (by omega : xi ≤ xi1)) (le_of_lt hD)
  have hxi1_le_yr1_n : xi1 ≤ yr1 := by
    have h1 : (d + 1) * h ≤ s_sub * h := Nat.mul_le_mul_right h (by omega)
    have h2 : d * h + h = (d + 1) * h := by ring
    omega
  have hxi1_le_yr1 : (xi1 : ℝ) / D_den ≤ (yr1 : ℝ) / D_den :=
    div_le_div_of_nonneg_right (by exact_mod_cast hxi1_le_yr1_n) (le_of_lt hD)
  have hrew1 : B_num + r * hy + (d + 1) * h = xi1 := by simp only [xi1, xi, yr]; ring
  have hrew2 : B_num + (r + 1) * hy = yr1 := by simp only [yr1, yr]; ring
  rw [hrew1, hrew2]
  have htr := wL_integral_le hxi_pos hxi_le_xi1 hxi1_le_yr1 hhy_pos
  have hnum_eq : (((xi1 : ℝ) / D_den - (xi : ℝ) / D_den) / (2 * ((hy : ℝ) / D_den))) *
      (((yr1 : ℝ) / D_den - (xi : ℝ) / D_den) / ((xi : ℝ) / D_den) +
       ((yr1 : ℝ) / D_den - (xi1 : ℝ) / D_den) / ((xi1 : ℝ) / D_den)) =
      ((S_sc * ((yr1 - xi) * xi1 + (yr1 - xi1) * xi) : ℕ) : ℝ) / ((2 * s_sub * xi * xi1 : ℕ) : ℝ) / S_sc := by
    have hsub1 : ((yr1 - xi : ℕ) : ℝ) = (yr1 : ℝ) - xi := Nat.cast_sub (by omega)
    have hsub2 : ((yr1 - xi1 : ℕ) : ℝ) = (yr1 : ℝ) - xi1 := Nat.cast_sub hxi1_le_yr1_n
    have hxi1_r : (xi1 : ℝ) = (xi : ℝ) + h := by simp only [xi1]; push_cast; ring
    have hhy_r : (hy : ℝ) = (s_sub : ℝ) * h := by rw [hhy_eq]; push_cast; ring
    have hh_r : (0 : ℝ) < h := by exact_mod_cast hh_pos
    have hs_r : (0 : ℝ) < s_sub := by exact_mod_cast hs_pos
    have hxi_r : (0 : ℝ) < xi := by exact_mod_cast hxi_pos_n
    have hxi1_p : (0 : ℝ) < xi1 := by exact_mod_cast hxi1_pos_n
    push_cast
    rw [hsub1, hsub2, hhy_r, hxi1_r]
    have hxi1_p' : (xi : ℝ) + h ≠ 0 := by linarith
    field_simp [ne_of_gt hD, ne_of_gt hS, ne_of_gt hh_r, ne_of_gt hs_r, ne_of_gt hxi_r, hxi1_p']
    ring
  rw [hnum_eq] at htr
  unfold wLNat
  have hden_pos : 0 < 2 * s_sub * xi * xi1 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hs_pos) hxi_pos_n) hxi1_pos_n
  exact le_trans htr (div_le_div_of_nonneg_right (ceilDiv_sound hden_pos) (le_of_lt hS))

private lemma wRNat_sound {s_sub hy h r d : ℕ}
    (hs_pos : 0 < s_sub) (hh_pos : 0 < h) (hh_even : h % 2 = 0) (hhy_eq : hy = s_sub * h) (_hd : d < s_sub) :
    ∫ x in (((B_num + r * hy + d * h : ℕ) : ℝ) / D_den)..(((B_num + r * hy + (d + 1) * h : ℕ) : ℝ) / D_den),
      (x - ((B_num + r * hy : ℕ) : ℝ) / D_den) / (((hy : ℝ) / D_den) * x) ≤
      (wRNat s_sub hy h r d : ℝ) / S_sc := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  have hB_pos : 0 < B_num := by unfold B_num; omega
  set yr := B_num + r * hy
  set xi := yr + d * h
  set xi1 := xi + h
  set xmid := xi + h / 2
  have hxi_pos_n : 0 < xi := by omega
  have hxm_pos_n : 0 < xmid := by omega
  have hhy_pos_n : 0 < hy := by rw [hhy_eq]; exact Nat.mul_pos hs_pos hh_pos
  have hxi_pos : (0 : ℝ) < (xi : ℝ) / D_den := div_pos (by exact_mod_cast hxi_pos_n) hD
  have hhy_pos : (0 : ℝ) < (hy : ℝ) / D_den := div_pos (by exact_mod_cast hhy_pos_n) hD
  have hyr_le : (yr : ℝ) / D_den ≤ (xi : ℝ) / D_den :=
    div_le_div_of_nonneg_right (by exact_mod_cast (by omega : yr ≤ xi)) (le_of_lt hD)
  have hxi_le_xi1 : (xi : ℝ) / D_den ≤ (xi1 : ℝ) / D_den :=
    div_le_div_of_nonneg_right (by exact_mod_cast (by omega : xi ≤ xi1)) (le_of_lt hD)
  have hrew1 : B_num + r * hy + (d + 1) * h = xi1 := by simp only [xi1, xi, yr]; ring
  rw [hrew1]
  have htr := wR_integral_le (div_nonneg (Nat.cast_nonneg yr) (le_of_lt hD)) hyr_le hxi_pos hxi_le_xi1 hhy_pos
  have hnum_eq : (((xi1 : ℝ) / D_den - (xi : ℝ) / D_den) / ((hy : ℝ) / D_den)) *
      ((((xi : ℝ) / D_den + (xi1 : ℝ) / D_den) / 2 - (yr : ℝ) / D_den) /
       (((xi : ℝ) / D_den + (xi1 : ℝ) / D_den) / 2)) =
      ((S_sc * (xmid - yr) : ℕ) : ℝ) / ((s_sub * xmid : ℕ) : ℝ) / S_sc := by
    have hxm_r : (xmid : ℝ) = ((xi : ℝ) + xi1) / 2 := by
      have h2 : 2 * (h / 2) = h := by omega
      have h2r : (2 : ℝ) * (h / 2 : ℕ) = h := by exact_mod_cast h2
      simp only [xmid, xi1]; push_cast; linarith
    have hsub : ((xmid - yr : ℕ) : ℝ) = (xmid : ℝ) - yr := Nat.cast_sub (by omega)
    have hxi1_r : (xi1 : ℝ) = (xi : ℝ) + h := by simp only [xi1]; push_cast; ring
    have hhy_r : (hy : ℝ) = (s_sub : ℝ) * h := by rw [hhy_eq]; push_cast; ring
    have hh_r : (0 : ℝ) < h := by exact_mod_cast hh_pos
    have hs_r : (0 : ℝ) < s_sub := by exact_mod_cast hs_pos
    have hxm_r_pos : (0 : ℝ) < xmid := by exact_mod_cast hxm_pos_n
    push_cast
    rw [hsub, hhy_r]
    have havg : ((xi : ℝ) / D_den + (xi1 : ℝ) / D_den) / 2 = (xmid : ℝ) / D_den := by rw [hxm_r]; ring
    rw [havg, hxi1_r]
    field_simp [ne_of_gt hD, ne_of_gt hS, ne_of_gt hh_r, ne_of_gt hs_r, ne_of_gt hxm_r_pos]
    ring
  rw [hnum_eq] at htr
  unfold wRNat
  have hden_pos : 0 < s_sub * xmid := Nat.mul_pos hs_pos hxm_pos_n
  exact le_trans htr (div_le_div_of_nonneg_right (ceilDiv_sound hden_pos) (le_of_lt hS))

private lemma checkListLe_spec : ∀ {xs ys : List ℕ}, checkListLe xs ys = true →
    xs.length = ys.length ∧ ∀ i < xs.length, xs.getD i 0 ≤ ys.getD i 0
  | [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | _ :: _, [], h => by simp [checkListLe] at h
  | [], _ :: _, h => by simp [checkListLe] at h
  | a :: as, b :: bs, h => by
    simp only [checkListLe, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlen, hget⟩ := checkListLe_spec h.2
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero => exact h.1
    | succ i' => exact hget i' (by simpa using hi)

private lemma mkKerL_len (s_sub hy h r : ℕ) : ∀ n, (mkKerL s_sub hy h r n).length = n
  | 0 => rfl
  | n + 1 => by simp [mkKerL, mkKerL_len s_sub hy h r n]

private lemma mkKerR_len (s_sub hy h r : ℕ) : ∀ n, (mkKerR s_sub hy h r n).length = n
  | 0 => rfl
  | n + 1 => by simp [mkKerR, mkKerR_len s_sub hy h r n]

private lemma mkKerL_getD (s_sub hy h r : ℕ) : ∀ n t, t < n →
    (mkKerL s_sub hy h r n).getD t 0 = wLNat s_sub hy h r (n - 1 - t)
  | 0, _, ht => absurd ht (Nat.not_lt_zero _)
  | n + 1, 0, _ => by simp [mkKerL]
  | n + 1, t + 1, ht => by
    simp only [mkKerL, List.getD_cons_succ]
    rw [mkKerL_getD s_sub hy h r n t (by omega)]
    congr 1; omega

private lemma mkKerR_getD (s_sub hy h r : ℕ) : ∀ n t, t < n →
    (mkKerR s_sub hy h r n).getD t 0 = wRNat s_sub hy h r (n - 1 - t)
  | 0, _, ht => absurd ht (Nat.not_lt_zero _)
  | n + 1, 0, _ => by simp [mkKerR]
  | n + 1, t + 1, ht => by
    simp only [mkKerR, List.getD_cons_succ]
    rw [mkKerR_getD s_sub hy h r n t (by omega)]
    congr 1; omega

private lemma dotSmall_acc : ∀ (ws cs : List ℕ) (acc : ℕ),
    dotSmall ws cs acc = acc + dotSmall ws cs 0
  | [], _, acc => by simp [dotSmall]
  | _ :: _, [], acc => by simp [dotSmall]
  | w :: ws, c :: cs, acc => by
    simp only [dotSmall, zero_add]
    rw [dotSmall_acc ws cs (acc + w * c), dotSmall_acc ws cs (w * c)]
    omega

private lemma dotSmall_eq_sum_getD : ∀ (ws cs : List ℕ), ws.length ≤ cs.length →
    dotSmall ws cs 0 = ∑ t ∈ Finset.range ws.length, ws.getD t 0 * cs.getD t 0
  | [], _, _ => by simp [dotSmall]
  | _ :: _, [], h => by simp at h
  | w :: ws, c :: cs, h => by
    simp only [dotSmall, zero_add, List.length_cons, Finset.sum_range_succ']
    rw [dotSmall_acc ws cs (w * c), dotSmall_eq_sum_getD ws cs (by simpa using h)]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    omega

private lemma list_getD_drop (l : List ℕ) (n i : ℕ) : (l.drop n).getD i 0 = l.getD (n + i) 0 := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons a t =>
      simp only [List.drop_succ_cons]
      rw [ih t, show n + 1 + i = (n + i) + 1 by omega, List.getD_cons_succ]

private lemma dropN_eq_drop : ∀ (n : ℕ) (l : List ℕ), dropN n l = l.drop n
  | 0, l => by simp [dropN]
  | n + 1, [] => by simp [dropN]
  | n + 1, _ :: t => by simp [dropN, dropN_eq_drop n t]

private lemma list_getD_append {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) :
    (l1 ++ l2).getD i d = if i < l1.length then l1.getD i d else l2.getD (i - l1.length) d := by
  induction l1 generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.cons_append, List.getD_cons_succ, List.length_cons]
      rw [ih]
      by_cases h : i' < t.length
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]; congr 1; omega

private lemma list_getD_reverse (l : List ℕ) :
    ∀ k < l.length, l.reverse.getD (l.length - 1 - k) 0 = l.getD k 0 := by
  induction l with
  | nil => intro _ h; simp at h
  | cons a t ih =>
    intro k hk
    simp only [List.reverse_cons, List.length_cons]
    rw [list_getD_append]
    cases k with
    | zero =>
      simp only [Nat.sub_zero, Nat.add_sub_cancel, List.length_reverse, lt_self_iff_false,
        ↓reduceIte, Nat.sub_self, List.getD_cons_zero]
    | succ k' =>
      have hk' : k' < t.length := by simp at hk; omega
      have hlt : t.length + 1 - 1 - (k' + 1) < t.reverse.length := by simp; omega
      rw [if_pos hlt]
      have heq : t.length + 1 - 1 - (k' + 1) = t.length - 1 - k' := by omega
      rw [heq, ih k' hk', List.getD_cons_succ]

private def concatLists {α : Type*} : List (List α) → List α
  | [] => []
  | g :: gs => g ++ concatLists gs

private lemma concatLists_getD_len8 {α : Type*} (d : α) :
    ∀ (Gs : List (List α)), (∀ g < Gs.length, (Gs.getD g []).length = 8) →
      ∀ r < 8 * Gs.length, (concatLists Gs).getD r d = (Gs.getD (r / 8) []).getD (r % 8) d
  | [], _, r, hr => by simp at hr
  | G :: Gs, hlen, r, hr => by
    simp only [concatLists]
    rw [list_getD_append]
    have hG8 : G.length = 8 := by simpa using hlen 0 (by simp)
    by_cases hlt : r < 8
    · rw [if_pos (by omega), Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]; simp
    · rw [if_neg (by omega), hG8]
      have ih := concatLists_getD_len8 d Gs (fun g hg => by simpa using hlen (g + 1) (by simp; omega)) (r - 8) (by simp at hr; omega)
      rw [ih]
      have hdiv : r / 8 = (r - 8) / 8 + 1 := by omega
      have hmod : r % 8 = (r - 8) % 8 := by omega
      rw [hdiv, hmod, List.getD_cons_succ]

private lemma sum_range_mul_eight (f : ℕ → ℕ) :
    ∀ n, ∑ r ∈ Finset.range (8 * n), f r = ∑ g ∈ Finset.range n, ∑ j ∈ Finset.range 8, f (g * 8 + j)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, ← sum_range_mul_eight f n, show 8 * (n + 1) = 8 * n + 8 by ring]
    rw [Finset.sum_range_add]
    congr 1; apply Finset.sum_congr rfl; intro j _; congr 1; ring

private lemma checkKersAll_spec {s_sub hy h : ℕ} :
    ∀ {r0 : ℕ} {Kers : List (List ℕ)},
      checkKersAll s_sub hy h r0 Kers = true →
      ∀ r < Kers.length, checkKer s_sub hy h (r0 + r) (Kers.getD r []) = true
  | _, [], _, _, hr => absurd hr (Nat.not_lt_zero _)
  | r0, k :: ks, hchk, r, hr => by
    simp only [checkKersAll, Bool.and_eq_true] at hchk
    cases r with
    | zero => simpa using hchk.1
    | succ r' =>
      have ih := checkKersAll_spec hchk.2 r' (by simpa using hr)
      simpa only [show r0 + (r' + 1) = (r0 + 1) + r' by omega, List.getD_cons_succ] using ih

private lemma checkSJ8Go_aux {t0 x0 h hy err55 err110 s_sub off7 Nu : ℕ} {useOut : Bool}
    {k0 k1 k2 k3 k4 k5 k6 k7 : List ℕ}
    (hx0b : B_num ≤ x0) (hx8c : x0 + 8 * hy ≤ C_num) (hhy_pos : 0 < hy)
    (hh_le : 2 * h ≤ X_span_num) (hh6 : h % 6 = 0) (ht06 : t0 % 6 = 0)
    (herr55 : err55 = ceilDiv (S_sc * 55 * hy * hy * hy) TwelveD3)
    (herr110 : err110 = ceilDiv (S_sc * 110 * hy * hy * hy) TwelveD3)
    {rem : ℕ} {nextRev outRev jgRev q0 q1 q2 q3 q4 q5 q6 q7 : List ℕ}
    (hnext : ∀ idx < rem,
      ∫ x in (((x0 + 8 * hy : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤
        (nextRev.getD (rem - 1 - idx) 0 : ℝ) / S_sc)
    (hchk : checkSJ8Go t0 x0 h hy err55 err110 s_sub off7 Nu useOut k0 k1 k2 k3 k4 k5 k6 k7
              rem nextRev outRev jgRev q0 q1 q2 q3 q4 q5 q6 q7 = true) :
    ∃ c0 c1 c2 c3 c4 c5 c6 c7 : List ℕ,
      c0.length = rem + q0.length ∧ c1.length = rem + q1.length ∧
      c2.length = rem + q2.length ∧ c3.length = rem + q3.length ∧
      c4.length = rem + q4.length ∧ c5.length = rem + q5.length ∧
      c6.length = rem + q6.length ∧ c7.length = rem + q7.length ∧
      c0.drop rem = q0 ∧ c1.drop rem = q1 ∧ c2.drop rem = q2 ∧ c3.drop rem = q3 ∧
      c4.drop rem = q4 ∧ c5.drop rem = q5 ∧ c6.drop rem = q6 ∧ c7.drop rem = q7 ∧
      (∀ idx < rem,
        (∫ x in (((x0 + 0 * hy : ℕ) : ℝ) / D_den)..cR, gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤ (c0.getD idx 0 : ℝ) / S_sc) ∧
        (∫ x in (((x0 + 1 * hy : ℕ) : ℝ) / D_den)..cR, gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤ (c1.getD idx 0 : ℝ) / S_sc) ∧
        (∫ x in (((x0 + 2 * hy : ℕ) : ℝ) / D_den)..cR, gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤ (c2.getD idx 0 : ℝ) / S_sc) ∧
        (∫ x in (((x0 + 3 * hy : ℕ) : ℝ) / D_den)..cR, gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤ (c3.getD idx 0 : ℝ) / S_sc) ∧
        (∫ x in (((x0 + 4 * hy : ℕ) : ℝ) / D_den)..cR, gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤ (c4.getD idx 0 : ℝ) / S_sc) ∧
        (∫ x in (((x0 + 5 * hy : ℕ) : ℝ) / D_den)..cR, gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤ (c5.getD idx 0 : ℝ) / S_sc) ∧
        (∫ x in (((x0 + 6 * hy : ℕ) : ℝ) / D_den)..cR, gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤ (c6.getD idx 0 : ℝ) / S_sc) ∧
        (∫ x in (((x0 + 7 * hy : ℕ) : ℝ) / D_den)..cR, gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤ (c7.getD idx 0 : ℝ) / S_sc)) ∧
      (useOut = true → outRev.length = rem ∧ ∀ idx < rem, c0.getD idx 0 ≤ outRev.getD (rem - 1 - idx) 0) ∧
      (jgRev.length = min rem (off7 + Nu) - off7 ∧
       ∀ k < min rem (off7 + Nu) - off7,
         dotSmall k0 (c0.drop (off7 + 7 * s_sub + k)) 0 +
         dotSmall k1 (c1.drop (off7 + 6 * s_sub + k)) 0 +
         dotSmall k2 (c2.drop (off7 + 5 * s_sub + k)) 0 +
         dotSmall k3 (c3.drop (off7 + 4 * s_sub + k)) 0 +
         dotSmall k4 (c4.drop (off7 + 3 * s_sub + k)) 0 +
         dotSmall k5 (c5.drop (off7 + 2 * s_sub + k)) 0 +
         dotSmall k6 (c6.drop (off7 + 1 * s_sub + k)) 0 +
         dotSmall k7 (c7.drop (off7 + 0 * s_sub + k)) 0 ≤
         jgRev.getD (min rem (off7 + Nu) - off7 - 1 - k) 0 * JG_DIV) := by
  induction rem generalizing nextRev outRev jgRev q0 q1 q2 q3 q4 q5 q6 q7 with
  | zero =>
    simp only [checkSJ8Go, Bool.and_eq_true, List.isEmpty_iff] at hchk
    refine ⟨q0, q1, q2, q3, q4, q5, q6, q7, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
            by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
            fun _ h => absurd h (Nat.not_lt_zero _),
            fun _ => ⟨by simp [hchk.1], fun _ h => absurd h (Nat.not_lt_zero _)⟩,
            by simp [hchk.2], fun _ h => by simp at h⟩
  | succ rem ih =>
    unfold checkSJ8Go at hchk
    dsimp only at hchk
    rw [Bool.and_eq_true, Bool.and_eq_true] at hchk
    rcases hchk with ⟨⟨hok_out, hok_j⟩, hrec_chk⟩
    have hv8_eq : (match nextRev with | a :: b => (a, b) | [] => (0, [])).1 = nextRev.getD 0 0 := by
      cases nextRev <;> rfl
    have hnext'_getD : ∀ i, (match nextRev with | a :: b => (a, b) | [] => (0, [])).2.getD i 0 = nextRev.getD (i + 1) 0 := by
      intro i; cases nextRev <;> rfl
    have hnext' : ∀ idx < rem,
        ∫ x in (((x0 + 8 * hy : ℕ) : ℝ) / D_den)..cR,
          gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤
          ((match nextRev with | a :: b => (a, b) | [] => (0, [])).2.getD (rem - 1 - idx) 0 : ℝ) / S_sc := by
      intro idx hidx
      rw [hnext'_getD, show (rem - 1 - idx) + 1 = (rem + 1) - 1 - idx by omega]
      exact hnext idx (by omega)
    have hnext_cur : ∫ x in (((x0 + 8 * hy : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0 + rem * h : ℕ) : ℝ) / D_den) (((t0 + rem * h + 2 * h : ℕ) : ℝ) / D_den) x ≤
        ((match nextRev with | a :: b => (a, b) | [] => (0, [])).1 : ℝ) / S_sc := by
      rw [hv8_eq]
      have := hnext rem (by omega)
      simpa only [show (rem + 1) - 1 - rem = 0 by omega] using this
    have ht_mod : (t0 + rem * h) % 6 = 0 := by rw [Nat.add_mod, Nat.mul_mod, ht06, hh6]; norm_num
    have hr8 := evalRow8_sound hx0b hx8c hhy_pos hh_le hh6 ht_mod herr55 herr110 hnext_cur
    set r := evalRow8 (t0 + rem * h) x0 h hy err55 err110 (match nextRev with | a :: b => (a, b) | [] => (0, [])).1
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7,
            hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7,
            hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
            hHrec, hout_rec, hjg_len, hjg_rec⟩ := ih hnext' hrec_chk
    have hdrop_help : ∀ (c q : List ℕ) (s : ℕ), c.drop rem = s :: q →
        c.drop (rem + 1) = q ∧ c.getD rem 0 = s ∧ ∀ d, c.drop (rem + d) = (s :: q).drop d := by
      intro c q s hcd
      have hdd : ∀ d, c.drop (rem + d) = (s :: q).drop d := fun d => by
        rw [← hcd, List.drop_drop]
      refine ⟨by simpa using hdd 1, ?_, hdd⟩
      have := list_getD_drop c rem 0
      rw [hcd, Nat.add_zero] at this
      exact this.symm
    obtain ⟨hd0', hg0', hdd0⟩ := hdrop_help c0 q0 r.1 hd0
    obtain ⟨hd1', hg1', hdd1⟩ := hdrop_help c1 q1 r.2.1 hd1
    obtain ⟨hd2', hg2', hdd2⟩ := hdrop_help c2 q2 r.2.2.1 hd2
    obtain ⟨hd3', hg3', hdd3⟩ := hdrop_help c3 q3 r.2.2.2.1 hd3
    obtain ⟨hd4', hg4', hdd4⟩ := hdrop_help c4 q4 r.2.2.2.2.1 hd4
    obtain ⟨hd5', hg5', hdd5⟩ := hdrop_help c5 q5 r.2.2.2.2.2.1 hd5
    obtain ⟨hd6', hg6', hdd6⟩ := hdrop_help c6 q6 r.2.2.2.2.2.2.1 hd6
    obtain ⟨hd7', hg7', hdd7⟩ := hdrop_help c7 q7 r.2.2.2.2.2.2.2 hd7
    refine ⟨c0, c1, c2, c3, c4, c5, c6, c7,
            by simp at hl0; omega, by simp at hl1; omega, by simp at hl2; omega, by simp at hl3; omega,
            by simp at hl4; omega, by simp at hl5; omega, by simp at hl6; omega, by simp at hl7; omega,
            hd0', hd1', hd2', hd3', hd4', hd5', hd6', hd7', ?_, ?_, ?_⟩
    · intro idx hidx
      by_cases hlt : idx < rem
      · exact hHrec idx hlt
      · have heq : idx = rem := by omega
        rw [heq, hg0', hg1', hg2', hg3', hg4', hg5', hg6', hg7']
        exact hr8
    · intro huse
      rw [if_pos huse] at hok_out hout_rec
      cases outRev with
      | nil => simp at hok_out
      | cons v0 os =>
        simp only [decide_eq_true_eq] at hok_out
        obtain ⟨hos_len, hos_bd⟩ := hout_rec huse
        refine ⟨by simp [hos_len], fun idx hidx => ?_⟩
        by_cases hlt : idx < rem
        · rw [show (rem + 1) - 1 - idx = (rem - 1 - idx) + 1 by omega, List.getD_cons_succ]
          exact hos_bd idx hlt
        · have heq : idx = rem := by omega
          rw [heq, show (rem + 1) - 1 - rem = 0 by omega, List.getD_cons_zero, hg0']
          exact hok_out
    · clear ih hr8 hHrec hout_rec hok_out hnext hnext' hnext_cur hrec_chk hnext'_getD hv8_eq ht_mod
        herr55 herr110 hx0b hx8c hhy_pos hh_le hh6 ht06
      by_cases hin : off7 ≤ rem ∧ rem < off7 + Nu
      · have hcond : (decide (off7 ≤ rem) && decide (rem < off7 + Nu)) = true := by
          simp [hin.1, hin.2]
        rw [if_pos hcond] at hok_j hjg_len hjg_rec
        cases jgRev with
        | nil => simp at hok_j
        | cons j js =>
          dsimp only at hok_j hjg_len hjg_rec
          simp only [decide_eq_true_eq, dropN_eq_drop] at hok_j
          rw [dotSmall_acc k0, dotSmall_acc k1, dotSmall_acc k2, dotSmall_acc k3,
              dotSmall_acc k4, dotSmall_acc k5, dotSmall_acc k6] at hok_j
          have hmin1 : min (rem + 1) (off7 + Nu) - off7 = (rem - off7) + 1 := by
            rw [Nat.min_eq_left (Nat.succ_le_of_lt hin.2), Nat.succ_sub hin.1]
          have hmin0 : min rem (off7 + Nu) - off7 = rem - off7 := by
            rw [Nat.min_eq_left (le_of_lt hin.2)]
          rw [hmin0] at hjg_len hjg_rec
          rw [hmin1]
          refine ⟨by simp [hjg_len], fun k hk => ?_⟩
          by_cases hklt : k < rem - off7
          · rw [show (rem - off7) + 1 - 1 - k = (rem - off7 - 1 - k) + 1 by omega, List.getD_cons_succ]
            exact hjg_rec k hklt
          · have hkeq : k = rem - off7 := by omega
            rw [hkeq, show (rem - off7) + 1 - 1 - (rem - off7) = 0 by omega, List.getD_cons_zero]
            have he : ∀ m, off7 + m + (rem - off7) = rem + m := fun m => by
              rw [Nat.add_right_comm, Nat.add_sub_of_le hin.1]
            rw [he, he, he, he, he, he, he, he, Nat.zero_mul,
                hdd0, hdd1, hdd2, hdd3, hdd4, hdd5, hdd6, hdd7, List.drop_zero]
            have hok_j' :
                dotSmall k7 (r.2.2.2.2.2.2.2 :: q7) 0 +
                dotSmall k6 (List.drop (1 * s_sub) (r.2.2.2.2.2.2.1 :: q6)) 0 +
                dotSmall k5 (List.drop (2 * s_sub) (r.2.2.2.2.2.1 :: q5)) 0 +
                dotSmall k4 (List.drop (3 * s_sub) (r.2.2.2.2.1 :: q4)) 0 +
                dotSmall k3 (List.drop (4 * s_sub) (r.2.2.2.1 :: q3)) 0 +
                dotSmall k2 (List.drop (5 * s_sub) (r.2.2.1 :: q2)) 0 +
                dotSmall k1 (List.drop (6 * s_sub) (r.2.1 :: q1)) 0 +
                dotSmall k0 (List.drop (7 * s_sub) (r.1 :: q0)) 0 ≤ j * JG_DIV := by
              cases nextRev <;> exact hok_j
            linarith
      · have hcond : ¬((decide (off7 ≤ rem) && decide (rem < off7 + Nu)) = true) := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hin
        rw [if_neg hcond] at hjg_len hjg_rec
        have hmin_eq : min (rem + 1) (off7 + Nu) - off7 = min rem (off7 + Nu) - off7 := by
          by_cases h1 : rem < off7
          · rw [Nat.sub_eq_zero_of_le (le_trans (Nat.min_le_left _ _) (Nat.succ_le_of_lt h1)),
                Nat.sub_eq_zero_of_le (le_trans (Nat.min_le_left _ _) (le_of_lt h1))]
          · have h2 : off7 + Nu ≤ rem := Nat.le_of_not_lt (fun hlt => hin ⟨Nat.le_of_not_lt h1, hlt⟩)
            rw [Nat.min_eq_right (Nat.le_succ_of_le h2), Nat.min_eq_right h2]
        rw [hmin_eq]
        exact ⟨hjg_len, hjg_rec⟩

private def Group8Ok (t0 x0 h hy s_sub off7 Nu rem : ℕ)
    (k0 k1 k2 k3 k4 k5 k6 k7 jgRev : List ℕ) (G : List (List ℕ)) : Prop :=
  G.length = 8 ∧
  (∀ j < 8, (G.getD j []).length = rem) ∧
  (∀ j < 8, ∀ idx < rem,
    ∫ x in (((x0 + j * hy : ℕ) : ℝ) / D_den)..cR,
      gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤
      ((G.getD j []).getD idx 0 : ℝ) / S_sc) ∧
  (∀ k < Nu,
    dotSmall k0 ((G.getD 0 []).drop (off7 + 7 * s_sub + k)) 0 +
    dotSmall k1 ((G.getD 1 []).drop (off7 + 6 * s_sub + k)) 0 +
    dotSmall k2 ((G.getD 2 []).drop (off7 + 5 * s_sub + k)) 0 +
    dotSmall k3 ((G.getD 3 []).drop (off7 + 4 * s_sub + k)) 0 +
    dotSmall k4 ((G.getD 4 []).drop (off7 + 3 * s_sub + k)) 0 +
    dotSmall k5 ((G.getD 5 []).drop (off7 + 2 * s_sub + k)) 0 +
    dotSmall k6 ((G.getD 6 []).drop (off7 + 1 * s_sub + k)) 0 +
    dotSmall k7 ((G.getD 7 []).drop (off7 + 0 * s_sub + k)) 0 ≤
    jgRev.getD (Nu - 1 - k) 0 * JG_DIV)

private lemma checkSJ8Go_sound {t0 x0 h hy err55 err110 s_sub off7 Nu rem : ℕ} {useOut : Bool}
    {k0 k1 k2 k3 k4 k5 k6 k7 nextRev outRev jgRev : List ℕ}
    (hx0b : B_num ≤ x0) (hx8c : x0 + 8 * hy ≤ C_num) (hhy_pos : 0 < hy)
    (hh_le : 2 * h ≤ X_span_num) (hh6 : h % 6 = 0) (ht06 : t0 % 6 = 0)
    (hoff_le : off7 + Nu ≤ rem)
    (herr55 : err55 = ceilDiv (S_sc * 55 * hy * hy * hy) TwelveD3)
    (herr110 : err110 = ceilDiv (S_sc * 110 * hy * hy * hy) TwelveD3)
    (hnext : ∀ idx < rem,
      ∫ x in (((x0 + 8 * hy : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤
        (nextRev.getD (rem - 1 - idx) 0 : ℝ) / S_sc)
    (hchk : checkSJ8Go t0 x0 h hy err55 err110 s_sub off7 Nu useOut k0 k1 k2 k3 k4 k5 k6 k7
              rem nextRev outRev jgRev [] [] [] [] [] [] [] [] = true) :
    ∃ G : List (List ℕ),
      Group8Ok t0 x0 h hy s_sub off7 Nu rem k0 k1 k2 k3 k4 k5 k6 k7 jgRev G ∧
      (useOut = true → ∀ idx < rem,
        ∫ x in (((x0 : ℕ) : ℝ) / D_den)..cR,
          gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤
          (outRev.getD (rem - 1 - idx) 0 : ℝ) / S_sc) := by
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7,
          hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7,
          _, _, _, _, _, _, _, _,
          hH, hout, _, hjg⟩ :=
    checkSJ8Go_aux hx0b hx8c hhy_pos hh_le hh6 ht06 herr55 herr110 hnext hchk
  have hmin : min rem (off7 + Nu) - off7 = Nu := by omega
  rw [hmin] at hjg
  refine ⟨[c0, c1, c2, c3, c4, c5, c6, c7], ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj; interval_cases j <;> simpa using ‹_›
  · intro j hj idx hidx
    have hHi := hH idx hidx
    interval_cases j
    · exact hHi.1
    · exact hHi.2.1
    · exact hHi.2.2.1
    · exact hHi.2.2.2.1
    · exact hHi.2.2.2.2.1
    · exact hHi.2.2.2.2.2.1
    · exact hHi.2.2.2.2.2.2.1
    · exact hHi.2.2.2.2.2.2.2
  · intro k hk; simpa using hjg k hk
  · intro huse idx hidx
    have h0 := (hH idx hidx).1
    have hle := (hout huse).2 idx hidx
    have h0' : ∫ x in (((x0 : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0 + idx * h : ℕ) : ℝ) / D_den) (((t0 + idx * h + 2 * h : ℕ) : ℝ) / D_den) x ≤
        (c0.getD idx 0 : ℝ) / S_sc := by simpa only [Nat.zero_mul, add_zero] using h0
    exact le_trans h0' (div_le_div_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hS))

private lemma checkJ1Sum_spec : ∀ {a J : List ℕ}, checkJ1Sum a J = true →
    a.length = J.length ∧ ∀ k < J.length, a.getD k 0 ≤ J.getD k 0 * JG_MUL
  | [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | _ :: _, [], h => by simp [checkJ1Sum] at h
  | [], _ :: _, h => by simp [checkJ1Sum] at h
  | a :: as, j :: js, h => by
    simp only [checkJ1Sum, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hl, hr⟩ := checkJ1Sum_spec h.2
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => exact h.1
    | succ k' => exact hr k' (by simpa using hk)

private lemma checkJ2Sum_spec : ∀ {a b J : List ℕ}, checkJ2Sum a b J = true →
    a.length = J.length ∧ b.length = J.length ∧ ∀ k < J.length, a.getD k 0 + b.getD k 0 ≤ J.getD k 0 * JG_MUL
  | [], [], [], _ => ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | a :: as, b :: bs, j :: js, h => by
    simp only [checkJ2Sum, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hla, hlb, hr⟩ := checkJ2Sum_spec h.2
    refine ⟨by simp [hla], by simp [hlb], fun k hk => ?_⟩
    cases k with
    | zero => exact h.1
    | succ k' => exact hr k' (by simpa using hk)
  | [], _ :: _, _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h | [], [], _ :: _, h => by simp [checkJ2Sum] at h

private lemma checkJ6Sum_spec : ∀ {a b c d e f J : List ℕ}, checkJ6Sum a b c d e f J = true →
    a.length = J.length ∧ b.length = J.length ∧ c.length = J.length ∧
    d.length = J.length ∧ e.length = J.length ∧ f.length = J.length ∧
    ∀ k < J.length,
      a.getD k 0 + b.getD k 0 + c.getD k 0 + d.getD k 0 + e.getD k 0 + f.getD k 0 ≤ J.getD k 0 * JG_MUL
  | [], [], [], [], [], [], [], _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | a :: as, b :: bs, c :: cs, d :: ds, e :: es, f :: fs, j :: js, h => by
    simp only [checkJ6Sum, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨la, lb, lc, ld, le, lf, hr⟩ := checkJ6Sum_spec h.2
    refine ⟨by simp [la], by simp [lb], by simp [lc], by simp [ld], by simp [le], by simp [lf], fun k hk => ?_⟩
    cases k with
    | zero => exact h.1
    | succ k' => exact hr k' (by simpa using hk)
  | [], _, _, _, _, _, _ :: _, h | _, [], _, _, _, _, _ :: _, h | _, _, [], _, _, _, _ :: _, h
  | _, _, _, [], _, _, _ :: _, h | _, _, _, _, [], _, _ :: _, h | _, _, _, _, _, [], _ :: _, h
  | _ :: _, _, _, _, _, _, [], h | _, _ :: _, _, _, _, _, [], h | _, _, _ :: _, _, _, _, [], h
  | _, _, _, _ :: _, _, _, [], h | _, _, _, _, _ :: _, _, [], h | _, _, _, _, _, _ :: _, [], h => by
    simp [checkJ6Sum] at h

private lemma checkJWin1_spec : ∀ {J Jw : List ℕ}, checkJWin1 J Jw = true →
    J.length = Jw.length + 1 ∧ ∀ k < Jw.length, ∀ q ≤ 1, J.getD (k + q) 0 ≤ Jw.getD k 0
  | [_], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | a :: b :: rest, w :: ws, h => by
    simp only [checkJWin1, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hl, hr⟩ := checkJWin1_spec h.2
    refine ⟨by simp at hl ⊢; omega, fun k hk q hq => ?_⟩
    cases k with
    | zero =>
      interval_cases q
      · exact h.1.1
      · exact h.1.2
    | succ k' =>
      simpa only [show k' + 1 + q = (k' + q) + 1 by omega, List.getD_cons_succ] using hr k' (by simpa using hk) q hq
  | [], _, h | [_], _ :: _, h | _ :: _ :: _, [], h => by simp [checkJWin1] at h

private lemma checkJWin4_spec : ∀ {J Jw : List ℕ}, checkJWin4 J Jw = true →
    J.length = Jw.length + 4 ∧ ∀ k < Jw.length, ∀ q ≤ 4, J.getD (k + q) 0 ≤ Jw.getD k 0
  | [_, _, _, _], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | a :: b :: c :: d :: e :: rest, w :: ws, h => by
    simp only [checkJWin4, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hl, hr⟩ := checkJWin4_spec h.2
    refine ⟨by simp at hl ⊢; omega, fun k hk q hq => ?_⟩
    cases k with
    | zero =>
      interval_cases q
      · exact h.1.1.1.1.1
      · exact h.1.1.1.1.2
      · exact h.1.1.1.2
      · exact h.1.1.2
      · exact h.1.2
    | succ k' =>
      simpa only [show k' + 1 + q = (k' + q) + 1 by omega, List.getD_cons_succ] using hr k' (by simpa using hk) q hq
  | [], _, h | [_], _, h | [_, _], _, h | [_, _, _], _, h
  | [_, _, _, _], _ :: _, h | _ :: _ :: _ :: _ :: _ :: _, [], h => by simp [checkJWin4] at h

private lemma checkW0Go_spec {h N0 xhi : ℕ} {W0 : List ℕ}
    (hchk : checkW0Go h N0 xhi W0 = true) :
    W0.length = N0 ∧ ∀ d < N0,
      log1pNat ((xhi - d * h) - max A0_num (xhi - d * h - h)) (max A0_num (xhi - d * h - h)) ≤ W0.getD d 0 := by
  induction N0 generalizing xhi W0 with
  | zero =>
    cases W0 with
    | nil => exact ⟨rfl, fun _ hd => absurd hd (Nat.not_lt_zero _)⟩
    | cons _ _ => simp [checkW0Go] at hchk
  | succ N0 ih =>
    cases W0 with
    | nil => simp [checkW0Go] at hchk
    | cons w ws =>
      simp only [checkW0Go, Bool.and_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨hlen, hrec⟩ := ih hchk.2
      refine ⟨by simp [hlen], fun d hd => ?_⟩
      cases d with
      | zero => simpa using hchk.1
      | succ d' =>
        have hsub : xhi - (d' + 1) * h = (xhi - h) - d' * h := by
          rw [Nat.sub_sub]; congr 1; ring
        simpa only [hsub, List.getD_cons_succ] using hrec d' (by omega)

private lemma dotNat_acc : ∀ (xs ys : List ℕ) (acc : ℕ), dotNat xs ys acc = acc + dotNat xs ys 0
  | [], _, acc => by simp [dotNat]
  | _ :: _, [], acc => by simp [dotNat]
  | a :: as, b :: bs, acc => by
    simp only [dotNat, zero_add]
    rw [dotNat_acc as bs (acc + a * b), dotNat_acc as bs (a * b)]
    omega

private lemma dotNat_eq_sum_getD : ∀ (xs ys : List ℕ), xs.length ≤ ys.length →
    dotNat xs ys 0 = ∑ d ∈ Finset.range xs.length, xs.getD d 0 * ys.getD d 0
  | [], _, _ => by simp [dotNat]
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [dotNat, zero_add, List.length_cons, Finset.sum_range_succ']
    rw [dotNat_acc as bs (a * b), dotNat_eq_sum_getD as bs (by simpa using h)]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    omega

private lemma checkSlices_spec {k mult : ℕ} {w0 jw : List ℕ}
    (hchk : checkSlices k mult w0 jw = true) :
    ∀ p < k, dotNat w0 (jw.drop (p * mult)) 0 ≤ TARGET_S2 := by
  induction k generalizing jw with
  | zero => intro _ hp; exact absurd hp (Nat.not_lt_zero _)
  | succ k ih =>
    simp only [checkSlices, Bool.and_eq_true, decide_eq_true_eq, dropN_eq_drop] at hchk
    intro p hp
    cases p with
    | zero => simpa using hchk.1
    | succ p' =>
      have hrec := ih hchk.2 p' (by omega)
      rw [List.drop_drop, show mult + p' * mult = (p' + 1) * mult by ring] at hrec
      exact hrec

/-! ### Core Band Soundness Theorem (Unified Across All 5 Bands!) -/

-- First: given column bounds S_cols[r] (for r < M2) and J_cert bounds via per-column dotSmall sums,
-- prove J_real u ≤ (J_cert.getD k 0 : ℝ) / S_sc for every u ∈ [u0 + k*h, u0 + (k+1)*h] / D_den!
private lemma J_cert_sound {u0 M2 s_sub h hy Nu : ℕ}
    {S_cols Kers : List (List ℕ)} {J_cert : List ℕ}
    (hM2_pos : 0 < M2) (hs_pos : 0 < s_sub)
    (hh_pos : 0 < h) (hh_even : h % 2 = 0)
    (hhy_eq : hy = s_sub * h) (hspan : M2 * hy = X_span_num)
    (hC_le_u0 : C_num ≤ u0)
    (hJlen : J_cert.length = Nu)
    (hS_bound : ∀ r < M2, ∀ idx < Nu + M2 * s_sub - 1,
      ∫ x2 in (((B_num + r * hy : ℕ) : ℝ) / D_den)..cR,
        gm_real ((((u0 - C_num) + idx * h : ℕ) : ℝ) / D_den)
          ((((u0 - C_num) + idx * h + 2 * h : ℕ) : ℝ) / D_den) x2 ≤
        ((S_cols.getD r []).getD idx 0 : ℝ) / S_sc)
    (hS_len : ∀ r < M2, (S_cols.getD r []).length = Nu + M2 * s_sub - 1)
    (hKer_ok : ∀ r < M2, checkKer s_sub hy h r (Kers.getD r []) = true)
    (hJ_sum : ∀ k < Nu,
      ∑ r ∈ Finset.range M2,
        dotSmall (Kers.getD r []) ((S_cols.getD r []).drop ((M2 - 1 - r) * s_sub + k)) 0 ≤
        J_cert.getD k 0 * S_sc) :
    ∀ k < Nu, ∀ u : ℝ, ((u0 + k * h : ℕ) : ℝ) / D_den ≤ u → u ≤ ((u0 + (k + 1) * h : ℕ) : ℝ) / D_den →
      J_real u ≤ (J_cert.getD k 0 : ℝ) / S_sc := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  have hbc : bR ≤ cR := by unfold bR cR; norm_num
  have hb_pos : (0 : ℝ) < bR := by unfold bR; norm_num
  set M1 := M2 * s_sub
  have hM1_pos : 0 < M1 := Nat.mul_pos hM2_pos hs_pos
  have hM1h : M1 * h = X_span_num := by
    rw [show M1 * h = M2 * (s_sub * h) by ring, ← hhy_eq, hspan]
  have hBM1 : B_num + M1 * h = C_num := by
    rw [hM1h]; unfold X_span_num B_num C_num; omega
  have hhy_pos_n : 0 < hy := by rw [hhy_eq]; exact Nat.mul_pos hs_pos hh_pos
  have hhy_pos : (0 : ℝ) < (hy : ℝ) / D_den := div_pos (by exact_mod_cast hhy_pos_n) hD
  intro k hk u hu1 hu2
  -- Split J_real u = ∑ r < M2, ∑ d < s_sub, ∫_{x_{r,d}}^{x_{r,d+1}} (1/x1) (∫_{x1}^{cR} g_real (u - x1) x2 dx2) dx1
  have hJ_int : ContinuousOn (fun x1 : ℝ => (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2)) (Icc bR cR) :=
    J_integrand_continuousOn u
  have hM2_hy : M2 * hy = C_num - B_num := by rw [hspan]; rfl
  have hB_le_C : B_num ≤ C_num := by unfold B_num C_num; omega
  have hB_pos : 0 < B_num := by unfold B_num; omega
  have hsum_split : J_real u =
      ∑ r ∈ Finset.range M2, ∑ d ∈ Finset.range s_sub,
        ∫ x1 in (((B_num + r * hy + d * h : ℕ) : ℝ) / D_den)..(((B_num + r * hy + (d + 1) * h : ℕ) : ℝ) / D_den),
          (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2) := by
    unfold J_real
    have houter : ∀ n ≤ M2,
        ∫ x1 in bR..(((B_num + n * hy : ℕ) : ℝ) / D_den), (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2) =
        ∑ r ∈ Finset.range n,
          ∫ x1 in (((B_num + r * hy : ℕ) : ℝ) / D_den)..(((B_num + (r + 1) * hy : ℕ) : ℝ) / D_den),
            (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2) := by
      intro n hn
      induction n with
      | zero => simp [bR_eq]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← ih (by omega)]
        have h1 : bR ≤ ((B_num + n * hy : ℕ) : ℝ) / D_den := by
          rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num ≤ B_num + n * hy)) (le_of_lt hD)
        have hnhy : n * hy ≤ (n + 1) * hy := Nat.mul_le_mul_right hy (by omega)
        have h2 : ((B_num + n * hy : ℕ) : ℝ) / D_den ≤ ((B_num + (n + 1) * hy : ℕ) : ℝ) / D_den :=
          div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num + n * hy ≤ B_num + (n + 1) * hy)) (le_of_lt hD)
        have h3 : ((B_num + (n + 1) * hy : ℕ) : ℝ) / D_den ≤ cR := by
          rw [cR_eq]
          have hle_n : B_num + (n + 1) * hy ≤ C_num := by
            have : (n + 1) * hy ≤ M2 * hy := Nat.mul_le_mul_right hy hn
            omega
          exact div_le_div_of_nonneg_right (by exact_mod_cast hle_n) (le_of_lt hD)
        exact (intervalIntegral.integral_add_adjacent_intervals
          ((hJ_int.mono (Icc_subset_Icc le_rfl (le_trans h2 h3))).intervalIntegrable_of_Icc h1)
          ((hJ_int.mono (Icc_subset_Icc h1 h3)).intervalIntegrable_of_Icc h2)).symm
    have htop := houter M2 le_rfl
    have hBM2 : B_num + M2 * hy = C_num := by omega
    rw [hBM2, ← cR_eq] at htop
    rw [htop]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < M2 := Finset.mem_range.mp hr
    have hinner : ∀ m ≤ s_sub,
        ∫ x1 in (((B_num + r * hy : ℕ) : ℝ) / D_den)..(((B_num + r * hy + m * h : ℕ) : ℝ) / D_den),
          (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2) =
        ∑ d ∈ Finset.range m,
          ∫ x1 in (((B_num + r * hy + d * h : ℕ) : ℝ) / D_den)..(((B_num + r * hy + (d + 1) * h : ℕ) : ℝ) / D_den),
            (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2) := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih (by omega)]
        have h0 : bR ≤ ((B_num + r * hy : ℕ) : ℝ) / D_den := by
          rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num ≤ B_num + r * hy)) (le_of_lt hD)
        have h1 : ((B_num + r * hy : ℕ) : ℝ) / D_den ≤ ((B_num + r * hy + m * h : ℕ) : ℝ) / D_den :=
          div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num + r * hy ≤ B_num + r * hy + m * h)) (le_of_lt hD)
        have hmh : m * h ≤ (m + 1) * h := Nat.mul_le_mul_right h (by omega)
        have h2 : ((B_num + r * hy + m * h : ℕ) : ℝ) / D_den ≤ ((B_num + r * hy + (m + 1) * h : ℕ) : ℝ) / D_den :=
          div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num + r * hy + m * h ≤ B_num + r * hy + (m + 1) * h)) (le_of_lt hD)
        have h3 : ((B_num + r * hy + (m + 1) * h : ℕ) : ℝ) / D_den ≤ cR := by
          rw [cR_eq]
          have hle_n : B_num + r * hy + (m + 1) * h ≤ C_num := by
            have hm_le : (m + 1) * h ≤ hy := by rw [hhy_eq]; exact Nat.mul_le_mul_right h hm
            have hr_le : (r + 1) * hy ≤ M2 * hy := Nat.mul_le_mul_right hy (by omega)
            have : B_num + r * hy + hy = B_num + (r + 1) * hy := by ring
            omega
          exact div_le_div_of_nonneg_right (by exact_mod_cast hle_n) (le_of_lt hD)
        exact (intervalIntegral.integral_add_adjacent_intervals
          ((hJ_int.mono (Icc_subset_Icc h0 (le_trans h2 h3))).intervalIntegrable_of_Icc h1)
          ((hJ_int.mono (Icc_subset_Icc (le_trans h0 h1) h3)).intervalIntegrable_of_Icc h2)).symm
    have hbot := hinner s_sub le_rfl
    have heq_r : B_num + r * hy + s_sub * h = B_num + (r + 1) * hy := by rw [← hhy_eq]; ring
    rwa [heq_r] at hbot
  -- Bound each cell (r, d)!
  have hcell : ∀ r < M2, ∀ d < s_sub,
      ∫ x1 in (((B_num + r * hy + d * h : ℕ) : ℝ) / D_den)..(((B_num + r * hy + (d + 1) * h : ℕ) : ℝ) / D_den),
        (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2) ≤
      ((wLNat s_sub hy h r d : ℝ) / S_sc) *
        (((S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)) 0 : ℝ) / S_sc) +
      if r + 1 < M2 then
        ((wRNat s_sub hy h r d : ℝ) / S_sc) *
          (((S_cols.getD (r + 1) []).getD ((M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)) 0 : ℝ) / S_sc)
      else 0 := by
    intro r hr d hd
    set idx := (M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)
    have hidx_lt : idx < Nu + M1 - 1 := by
      have : (M2 - 1 - r) * s_sub + (s_sub - 1 - d) ≤ M2 * s_sub - 1 := by
        have h1 : (M2 - 1 - r + 1) * s_sub ≤ M2 * s_sub := Nat.mul_le_mul_right s_sub (by omega)
        have h2 : (M2 - 1 - r) * s_sub + s_sub = (M2 - 1 - r + 1) * s_sub := by ring
        omega
      omega
    set t_lo_n := (u0 - C_num) + idx * h
    set t_hi_n := t_lo_n + 2 * h
    set xi_n := B_num + r * hy + d * h
    set xi1_n := B_num + r * hy + (d + 1) * h
    set yr_n := B_num + r * hy
    set yr1_n := B_num + (r + 1) * hy
    have hxi_le_xi1_n : xi_n ≤ xi1_n := by
      simp only [xi_n, xi1_n]; have : d * h ≤ (d + 1) * h := Nat.mul_le_mul_right h (by omega); omega
    have hxi1_le_yr1_n : xi1_n ≤ yr1_n := by
      have h1 : (d + 1) * h ≤ hy := by rw [hhy_eq]; exact Nat.mul_le_mul_right h (by omega)
      have h2 : B_num + (r + 1) * hy = B_num + r * hy + hy := by ring
      omega
    have hyr1_le_C_n : yr1_n ≤ C_num := by
      have h1 : (r + 1) * hy ≤ M2 * hy := Nat.mul_le_mul_right hy (by omega)
      omega
    have hxi_le_xi1 : (xi_n : ℝ) / D_den ≤ (xi1_n : ℝ) / D_den :=
      div_le_div_of_nonneg_right (by exact_mod_cast hxi_le_xi1_n) (le_of_lt hD)
    have htlh_r : (t_lo_n : ℝ) / D_den ≤ (t_hi_n : ℝ) / D_den :=
      div_le_div_of_nonneg_right (by exact_mod_cast (by omega : t_lo_n ≤ t_hi_n)) (le_of_lt hD)
    -- Verify exact t_lo_n + xi1_n = u0 + k * h and t_hi_n + xi_n = u0 + (k + 1) * h!
    have ht_lo_id : t_lo_n + xi1_n = u0 + k * h := by
      have h1 : idx * h + r * hy + (d + 1) * h = k * h + M1 * h := by
        have hM2_r : (M2 - 1 - r) * s_sub + (s_sub - 1 - d) + r * s_sub + (d + 1) = M2 * s_sub := by
          have hA : (M2 - 1 - r + r) * s_sub = (M2 - 1) * s_sub := by congr 1; omega
          have hB : (M2 - 1) * s_sub + s_sub = M2 * s_sub := by
            have : M2 - 1 + 1 = M2 := by omega
            calc (M2 - 1) * s_sub + s_sub = (M2 - 1 + 1) * s_sub := by ring
              _ = M2 * s_sub := by rw [this]
          have hC : (M2 - 1 - r) * s_sub + r * s_sub = (M2 - 1 - r + r) * s_sub := by ring
          omega
        calc idx * h + r * hy + (d + 1) * h
            = ((M2 - 1 - r) * s_sub + (s_sub - 1 - d) + r * s_sub + (d + 1)) * h + k * h := by
              rw [hhy_eq]; simp only [idx]; ring
          _ = M1 * h + k * h := by rw [hM2_r]
          _ = k * h + M1 * h := by ring
      have h2 : (u0 - C_num) + B_num + M1 * h = u0 := by omega
      simp only [t_lo_n, xi1_n]; omega
    have ht_hi_id : t_hi_n + xi_n = u0 + (k + 1) * h := by
      have h1 : xi1_n = xi_n + h := by simp only [xi1_n, xi_n]; ring
      have h2 : (k + 1) * h = k * h + h := by ring
      simp only [t_hi_n]; omega
    set Sr : ℝ := ∫ x2 in ((yr_n : ℝ) / D_den)..cR, gm_real ((t_lo_n : ℝ) / D_den) ((t_hi_n : ℝ) / D_den) x2
    set Sr1 : ℝ := ∫ x2 in ((yr1_n : ℝ) / D_den)..cR, gm_real ((t_lo_n : ℝ) / D_den) ((t_hi_n : ℝ) / D_den) x2
    have hSr_nn : 0 ≤ Sr := intervalIntegral.integral_nonneg
      (by rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : yr_n ≤ C_num)) (le_of_lt hD))
      (fun x2 hx2 => gm_real_nonneg
        (by rw [bR_eq]; exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num ≤ yr_n)) (le_of_lt hD)) hx2.1)
        hx2.2)
    have hSr1_nn : 0 ≤ Sr1 := intervalIntegral.integral_nonneg
      (by rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hyr1_le_C_n) (le_of_lt hD))
      (fun x2 hx2 => gm_real_nonneg
        (by rw [bR_eq]; exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num ≤ yr1_n)) (le_of_lt hD)) hx2.1)
        hx2.2)
    have hpt_x1 : ∀ x1 ∈ Icc ((xi_n : ℝ) / D_den) ((xi1_n : ℝ) / D_den),
        (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2) ≤
        (((yr1_n : ℝ) / D_den - x1) / (((hy : ℝ) / D_den) * x1)) * Sr +
        ((x1 - (yr_n : ℝ) / D_den) / (((hy : ℝ) / D_den) * x1)) * Sr1 := by
      intro x1 hx1
      have h1_ge_b : bR ≤ x1 := by
        rw [bR_eq]; exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num ≤ xi_n)) (le_of_lt hD)) hx1.1
      have h1_le_c : x1 ≤ cR := by
        rw [cR_eq]; exact le_trans hx1.2 (div_le_div_of_nonneg_right (by exact_mod_cast (by omega : xi1_n ≤ C_num)) (le_of_lt hD))
      have h1p : 0 < x1 := lt_of_lt_of_le hb_pos h1_ge_b
      have hux1_lo : (t_lo_n : ℝ) / D_den ≤ u - x1 := by
        have h1 : (t_lo_n : ℝ) / D_den + (xi1_n : ℝ) / D_den = ((u0 + k * h : ℕ) : ℝ) / D_den := by
          rw [← add_div]; norm_cast; rw [ht_lo_id]
        linarith [hu1, hx1.2]
      have hux1_hi : u - x1 ≤ (t_hi_n : ℝ) / D_den := by
        have h1 : (t_hi_n : ℝ) / D_den + (xi_n : ℝ) / D_den = ((u0 + (k + 1) * h : ℕ) : ℝ) / D_den := by
          rw [← add_div]; norm_cast; rw [ht_hi_id]
        linarith [hu2, hx1.1]
      have hg_le_gm : ∫ x2 in x1..cR, g_real (u - x1) x2 ≤
          ∫ x2 in x1..cR, gm_real ((t_lo_n : ℝ) / D_den) ((t_hi_n : ℝ) / D_den) x2 := by
        have hc1 : ContinuousOn (fun x2 => g_real (u - x1) x2) (Icc x1 cR) :=
          g_real_continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
            (fun x2 hx2 => ⟨trivial, le_trans h1_ge_b hx2.1, hx2.2⟩)
        have hc2 : ContinuousOn (fun x2 => gm_real ((t_lo_n : ℝ) / D_den) ((t_hi_n : ℝ) / D_den) x2) (Icc x1 cR) :=
          (gm_real_continuousOn htlh_r).mono (Icc_subset_Icc h1_ge_b le_rfl)
        exact intervalIntegral.integral_mono_on h1_le_c (hc1.intervalIntegrable_of_Icc h1_le_c)
          (hc2.intervalIntegrable_of_Icc h1_le_c)
          (fun x2 hx2 => g_real_le_gm_real (le_trans h1_ge_b hx2.1) hx2.2 hux1_lo hux1_hi)
      have hbr_r : bR ≤ (yr_n : ℝ) / D_den := by
        rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num ≤ yr_n)) (le_of_lt hD)
      have hyr_x1 : (yr_n : ℝ) / D_den ≤ x1 :=
        le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (by omega : yr_n ≤ xi_n)) (le_of_lt hD)) hx1.1
      have hx1_yr1 : x1 ≤ (yr1_n : ℝ) / D_den :=
        le_trans hx1.2 (div_le_div_of_nonneg_right (by exact_mod_cast hxi1_le_yr1_n) (le_of_lt hD))
      have hyr1_c : (yr1_n : ℝ) / D_den ≤ cR := by
        rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hyr1_le_C_n) (le_of_lt hD)
      have hdiff_hy : (yr1_n : ℝ) / D_den - (yr_n : ℝ) / D_den = (hy : ℝ) / D_den := by
        have : (yr1_n : ℝ) = (yr_n : ℝ) + hy := by
          have : yr1_n = yr_n + hy := by simp only [yr1_n, yr_n]; ring
          exact_mod_cast this
        rw [this]; ring
      have hconv := Hm_convex_linear_le htlh_r hbr_r hyr_x1 hx1_yr1 hyr1_c (by rw [hdiff_hy]; exact hhy_pos)
      rw [hdiff_hy] at hconv
      have hcomb := le_trans hg_le_gm hconv
      have hmul := mul_le_mul_of_nonneg_left hcomb (div_nonneg zero_le_one (le_of_lt h1p))
      have halg : (1 / x1) * ((((yr1_n : ℝ) / D_den - x1) / ((hy : ℝ) / D_den)) * Sr +
          ((x1 - (yr_n : ℝ) / D_den) / ((hy : ℝ) / D_den)) * Sr1) =
          (((yr1_n : ℝ) / D_den - x1) / (((hy : ℝ) / D_den) * x1)) * Sr +
          ((x1 - (yr_n : ℝ) / D_den) / (((hy : ℝ) / D_den) * x1)) * Sr1 := by
        field_simp [ne_of_gt h1p, ne_of_gt hhy_pos]
      linarith
    have hint_lhs : IntervalIntegrable (fun x1 => (1 / x1) * (∫ x2 in x1..cR, g_real (u - x1) x2))
        volume ((xi_n : ℝ) / D_den) ((xi1_n : ℝ) / D_den) := by
      have h1 : bR ≤ (xi_n : ℝ) / D_den := by
        rw [bR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : B_num ≤ xi_n)) (le_of_lt hD)
      have h2 : (xi1_n : ℝ) / D_den ≤ cR := by
        rw [cR_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : xi1_n ≤ C_num)) (le_of_lt hD)
      exact (hJ_int.mono (Icc_subset_Icc h1 h2)).intervalIntegrable_of_Icc hxi_le_xi1
    have hxi_pos_r : (0 : ℝ) < (xi_n : ℝ) / D_den :=
      div_pos (by exact_mod_cast (by omega : 0 < xi_n)) hD
    have hint_wL : IntervalIntegrable (fun x1 => ((yr1_n : ℝ) / D_den - x1) / (((hy : ℝ) / D_den) * x1))
        volume ((xi_n : ℝ) / D_den) ((xi1_n : ℝ) / D_den) :=
      ((continuousOn_const.sub continuousOn_id).div (continuousOn_const.mul continuousOn_id)
        (fun x hx => ne_of_gt (mul_pos hhy_pos (lt_of_lt_of_le hxi_pos_r hx.1)))).intervalIntegrable_of_Icc hxi_le_xi1
    have hint_wR : IntervalIntegrable (fun x1 => (x1 - (yr_n : ℝ) / D_den) / (((hy : ℝ) / D_den) * x1))
        volume ((xi_n : ℝ) / D_den) ((xi1_n : ℝ) / D_den) :=
      ((continuousOn_id.sub continuousOn_const).div (continuousOn_const.mul continuousOn_id)
        (fun x hx => ne_of_gt (mul_pos hhy_pos (lt_of_lt_of_le hxi_pos_r hx.1)))).intervalIntegrable_of_Icc hxi_le_xi1
    have hmono := intervalIntegral.integral_mono_on hxi_le_xi1 hint_lhs
      ((hint_wL.mul_const Sr).add (hint_wR.mul_const Sr1)) hpt_x1
    rw [intervalIntegral.integral_add (hint_wL.mul_const Sr) (hint_wR.mul_const Sr1),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const] at hmono
    have hwL_le := wLNat_sound (r := r) (d := d) hs_pos hh_pos hhy_eq hd
    have hwR_le := wRNat_sound (r := r) (d := d) hs_pos hh_pos hh_even hhy_eq hd
    have hSr_le : Sr ≤ ((S_cols.getD r []).getD idx 0 : ℝ) / S_sc := hS_bound r hr idx hidx_lt
    have htermL : (∫ x in ((xi_n : ℝ) / D_den)..((xi1_n : ℝ) / D_den),
          ((yr1_n : ℝ) / D_den - x) / (((hy : ℝ) / D_den) * x)) * Sr ≤
        ((wLNat s_sub hy h r d : ℝ) / S_sc) * (((S_cols.getD r []).getD idx 0 : ℝ) / S_sc) :=
      mul_le_mul hwL_le hSr_le hSr_nn (div_nonneg (Nat.cast_nonneg _) (le_of_lt hS))
    have htermR : (∫ x in ((xi_n : ℝ) / D_den)..((xi1_n : ℝ) / D_den),
          (x - (yr_n : ℝ) / D_den) / (((hy : ℝ) / D_den) * x)) * Sr1 ≤
        if r + 1 < M2 then
          ((wRNat s_sub hy h r d : ℝ) / S_sc) * (((S_cols.getD (r + 1) []).getD idx 0 : ℝ) / S_sc)
        else 0 := by
      split_ifs with hr1
      · exact mul_le_mul hwR_le (hS_bound (r + 1) hr1 idx hidx_lt) hSr1_nn
          (div_nonneg (Nat.cast_nonneg _) (le_of_lt hS))
      · have hr_eq : r + 1 = M2 := by omega
        have hyr1_eq_c : (yr1_n : ℝ) / D_den = cR := by
          rw [cR_eq]; congr 1
          have : yr1_n = C_num := by
            simp only [yr1_n, hr_eq, hspan]; unfold X_span_num B_num C_num; omega
          exact_mod_cast this
        have hSr1_zero : Sr1 = 0 := by simp only [Sr1, hyr1_eq_c, intervalIntegral.integral_same]
        rw [hSr1_zero, mul_zero]
    linarith
  -- Sum hcell over r < M2 and d < s_sub, and regroup by column r!
  have hsum_cells : J_real u ≤
      ∑ r ∈ Finset.range M2, ∑ d ∈ Finset.range s_sub,
        (((wLNat s_sub hy h r d : ℝ) / S_sc) *
          (((S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)) 0 : ℝ) / S_sc) +
        if r + 1 < M2 then
          ((wRNat s_sub hy h r d : ℝ) / S_sc) *
            (((S_cols.getD (r + 1) []).getD ((M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)) 0 : ℝ) / S_sc)
        else 0) := by
    rw [hsum_split]
    exact Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun d hd =>
      hcell r (Finset.mem_range.mp hr) d (Finset.mem_range.mp hd)))
  -- Split L-sum and R-sum, reindex R-sum from r to r+1!
  have hregroup :
      (∑ r ∈ Finset.range M2, ∑ d ∈ Finset.range s_sub,
        (((wLNat s_sub hy h r d : ℝ) / S_sc) *
          (((S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)) 0 : ℝ) / S_sc) +
        if r + 1 < M2 then
          ((wRNat s_sub hy h r d : ℝ) / S_sc) *
            (((S_cols.getD (r + 1) []).getD ((M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)) 0 : ℝ) / S_sc)
        else 0)) =
      (∑ r ∈ Finset.range M2,
        ((∑ t ∈ Finset.range s_sub,
            wLNat s_sub hy h r (s_sub - 1 - t) *
              (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + t) 0 +
          if r = 0 then 0 else
          ∑ t ∈ Finset.range s_sub,
            wRNat s_sub hy h (r - 1) (s_sub - 1 - t) *
              (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub + t)) 0 : ℕ) : ℝ)) / (S_sc * S_sc) := by
    -- Helper: reversing index d ↦ s_sub - 1 - d
    have hrev : ∀ f : ℕ → ℝ, ∑ d ∈ Finset.range s_sub, f d = ∑ t ∈ Finset.range s_sub, f (s_sub - 1 - t) := fun f =>
      Finset.sum_nbij' (fun d => s_sub - 1 - d) (fun t => s_sub - 1 - t)
        (fun d hd => Finset.mem_range.mpr (by have := Finset.mem_range.mp hd; omega))
        (fun t ht => Finset.mem_range.mpr (by have := Finset.mem_range.mp ht; omega))
        (fun d hd => by have := Finset.mem_range.mp hd; omega)
        (fun t ht => by have := Finset.mem_range.mp ht; omega)
        (fun d hd => by congr 1; have := Finset.mem_range.mp hd; omega)
    have hsplit_sum : ∀ r ∈ Finset.range M2,
        ∑ d ∈ Finset.range s_sub,
          (((wLNat s_sub hy h r d : ℝ) / S_sc) *
            (((S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)) 0 : ℝ) / S_sc) +
          if r + 1 < M2 then
            ((wRNat s_sub hy h r d : ℝ) / S_sc) *
              (((S_cols.getD (r + 1) []).getD ((M2 - 1 - r) * s_sub + k + (s_sub - 1 - d)) 0 : ℝ) / S_sc)
          else 0) =
        (∑ t ∈ Finset.range s_sub,
          ((wLNat s_sub hy h r (s_sub - 1 - t) *
            (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + t) 0 : ℕ) : ℝ)) / (S_sc * S_sc) +
        (if r + 1 < M2 then
          (∑ t ∈ Finset.range s_sub,
            ((wRNat s_sub hy h r (s_sub - 1 - t) *
              (S_cols.getD (r + 1) []).getD ((M2 - 1 - r) * s_sub + k + t) 0 : ℕ) : ℝ)) / (S_sc * S_sc)
         else 0) := by
      intro r _
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [hrev, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro t ht
        have ht' := Finset.mem_range.mp ht
        have hdd : s_sub - 1 - (s_sub - 1 - t) = t := by omega
        rw [hdd]; push_cast; ring
      · split_ifs
        · rw [hrev, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro t ht
          have ht' := Finset.mem_range.mp ht
          have hdd : s_sub - 1 - (s_sub - 1 - t) = t := by omega
          rw [hdd]; push_cast; ring
        · simp
    rw [Finset.sum_congr rfl hsplit_sum, Finset.sum_add_distrib]
    -- Reindex the second sum: ∑_{r < M2} (if r + 1 < M2 then F(r) else 0) = ∑_{r < M2} (if r = 0 then 0 else F(r - 1))
    have hR_shift :
        (∑ r ∈ Finset.range M2,
          if r + 1 < M2 then
            (∑ t ∈ Finset.range s_sub,
              ((wRNat s_sub hy h r (s_sub - 1 - t) *
                (S_cols.getD (r + 1) []).getD ((M2 - 1 - r) * s_sub + k + t) 0 : ℕ) : ℝ)) / (S_sc * S_sc)
          else 0) =
        ∑ r ∈ Finset.range M2,
          if r = 0 then 0 else
            (∑ t ∈ Finset.range s_sub,
              ((wRNat s_sub hy h (r - 1) (s_sub - 1 - t) *
                (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub + t)) 0 : ℕ) : ℝ)) / (S_sc * S_sc) := by
      have hM2_eq : M2 = (M2 - 1) + 1 := by omega
      conv_lhs => rw [hM2_eq, Finset.sum_range_succ]
      conv_rhs => rw [hM2_eq, Finset.sum_range_succ']
      simp only [lt_self_iff_false, ↓reduceIte, add_zero]
      apply Finset.sum_congr rfl
      intro r hr
      have hr' := Finset.mem_range.mp hr
      rw [if_pos (by omega), if_neg (by omega)]
      simp only [Nat.add_sub_cancel]
      congr 1; apply Finset.sum_congr rfl; intro t _
      congr 1; congr 1; congr 1
      have h1 : M2 - 1 - r = (M2 - 1 - (r + 1)) + 1 := by omega
      rw [h1]; ring
    rw [hR_shift, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> (push_cast; simp [add_div])
  -- Now compare each column r's exact Nat sum against dotSmall (Kers.getD r []) ...!
  have hcol_le : ∀ r < M2,
      (∑ t ∈ Finset.range s_sub,
          wLNat s_sub hy h r (s_sub - 1 - t) *
            (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + t) 0 +
        if r = 0 then 0 else
        ∑ t ∈ Finset.range s_sub,
          wRNat s_sub hy h (r - 1) (s_sub - 1 - t) *
            (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub + t)) 0) ≤
      dotSmall (Kers.getD r []) ((S_cols.getD r []).drop ((M2 - 1 - r) * s_sub + k)) 0 := by
    intro r hr
    have hck := hKer_ok r hr
    unfold checkKer at hck
    obtain ⟨hklen, hkget⟩ := checkListLe_spec hck
    have hclen := hS_len r hr
    by_cases hr0 : r = 0
    · subst hr0
      simp only [beq_self_eq_true, ↓reduceIte, add_zero] at hklen hkget ⊢
      rw [mkKerL_len] at hklen
      have hdrop_len : (Kers.getD 0 []).length ≤ ((S_cols.getD 0 []).drop ((M2 - 1 - 0) * s_sub + k)).length := by
        rw [List.length_drop, hclen, ← hklen]
        have hsub0 : M2 - 1 - 0 = M2 - 1 := by omega
        have hmul0 : (M2 - 1) * s_sub + s_sub = M2 * s_sub := by
          calc (M2 - 1) * s_sub + s_sub = (M2 - 1 + 1) * s_sub := by ring
            _ = M2 * s_sub := by rw [show M2 - 1 + 1 = M2 by omega]
        rw [hsub0]; omega
      rw [dotSmall_eq_sum_getD _ _ hdrop_len, ← hklen]
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [list_getD_drop]
      have h1 := hkget t (by rw [mkKerL_len]; exact ht')
      rw [mkKerL_getD s_sub hy h 0 s_sub t ht'] at h1
      exact Nat.mul_le_mul_right _ h1
    · have hbeq : (r == 0) = false := beq_false_of_ne hr0
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, if_neg hr0] at hklen hkget ⊢
      rw [List.length_append, mkKerL_len, mkKerR_len] at hklen
      have hdrop_len : (Kers.getD r []).length ≤ ((S_cols.getD r []).drop ((M2 - 1 - r) * s_sub + k)).length := by
        rw [List.length_drop, hclen, ← hklen]
        have h1 : (M2 - 1 - r + 2) * s_sub ≤ M2 * s_sub := Nat.mul_le_mul_right s_sub (by omega)
        have h2 : (M2 - 1 - r) * s_sub + (s_sub + s_sub) = (M2 - 1 - r + 2) * s_sub := by ring
        omega
      rw [dotSmall_eq_sum_getD _ _ hdrop_len, ← hklen, Finset.sum_range_add]
      apply Nat.add_le_add
      · apply Finset.sum_le_sum
        intro t ht
        have ht' := Finset.mem_range.mp ht
        rw [list_getD_drop]
        have h1 := hkget t (by rw [List.length_append, mkKerL_len s_sub hy h r, mkKerR_len s_sub hy h (r - 1)]; omega)
        have happ : (mkKerL s_sub hy h r s_sub ++ mkKerR s_sub hy h (r - 1) s_sub).getD t 0 =
            (mkKerL s_sub hy h r s_sub).getD t 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [mkKerL_len s_sub hy h r]; exact ht')]
        rw [happ, mkKerL_getD s_sub hy h r s_sub t ht'] at h1
        exact Nat.mul_le_mul_right _ h1
      · apply Finset.sum_le_sum
        intro t ht
        have ht' := Finset.mem_range.mp ht
        rw [list_getD_drop]
        have h1 := hkget (s_sub + t) (by rw [List.length_append, mkKerL_len s_sub hy h r, mkKerR_len s_sub hy h (r - 1)]; omega)
        have happ : (mkKerL s_sub hy h r s_sub ++ mkKerR s_sub hy h (r - 1) s_sub).getD (s_sub + t) 0 =
            (mkKerR s_sub hy h (r - 1) s_sub).getD t 0 := by
          have hge : (mkKerL s_sub hy h r s_sub).length ≤ s_sub + t := by rw [mkKerL_len s_sub hy h r]; omega
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, mkKerL_len s_sub hy h r,
            Nat.add_sub_cancel_left]
        rw [happ, mkKerR_getD s_sub hy h (r - 1) s_sub t ht'] at h1
        exact Nat.mul_le_mul_right _ h1
  have hnat_total :
      ∑ r ∈ Finset.range M2,
        (∑ t ∈ Finset.range s_sub,
            wLNat s_sub hy h r (s_sub - 1 - t) *
              (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + t) 0 +
          if r = 0 then 0 else
          ∑ t ∈ Finset.range s_sub,
            wRNat s_sub hy h (r - 1) (s_sub - 1 - t) *
              (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub + t)) 0) ≤
      J_cert.getD k 0 * S_sc :=
    le_trans (Finset.sum_le_sum (fun r hr => hcol_le r (Finset.mem_range.mp hr))) (hJ_sum k hk)
  have hreal_total :
      (∑ r ∈ Finset.range M2,
        ((∑ t ∈ Finset.range s_sub,
            wLNat s_sub hy h r (s_sub - 1 - t) *
              (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + t) 0 +
          if r = 0 then 0 else
          ∑ t ∈ Finset.range s_sub,
            wRNat s_sub hy h (r - 1) (s_sub - 1 - t) *
              (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub + t)) 0 : ℕ) : ℝ)) / (S_sc * S_sc) ≤
      (J_cert.getD k 0 : ℝ) / S_sc := by
    have hcast : (∑ r ∈ Finset.range M2,
        ((∑ t ∈ Finset.range s_sub,
            wLNat s_sub hy h r (s_sub - 1 - t) *
              (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + t) 0 +
          if r = 0 then 0 else
          ∑ t ∈ Finset.range s_sub,
            wRNat s_sub hy h (r - 1) (s_sub - 1 - t) *
              (S_cols.getD r []).getD ((M2 - 1 - r) * s_sub + k + (s_sub + t)) 0 : ℕ) : ℝ)) ≤
        ((J_cert.getD k 0 * S_sc : ℕ) : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hnat_total
    have hdiv := div_le_div_of_nonneg_right hcast (mul_nonneg (le_of_lt hS) (le_of_lt hS))
    have hrew : ((J_cert.getD k 0 * S_sc : ℕ) : ℝ) / ((S_sc : ℝ) * S_sc) = (J_cert.getD k 0 : ℝ) / S_sc := by
      push_cast; field_simp [ne_of_gt hS]
    rwa [hrew] at hdiv
  linarith

private lemma J_cert_sound_groups {u0 ngrp s_sub h hy Nu : ℕ}
    {Gs : List (List (List ℕ))} {Jgs Kers : List (List ℕ)} {J_cert : List ℕ}
    (hngrp_pos : 0 < ngrp) (hs_pos : 0 < s_sub)
    (hh_pos : 0 < h) (hh_even : h % 2 = 0)
    (hhy_eq : hy = s_sub * h) (hspan : (8 * ngrp) * hy = X_span_num)
    (hC_le_u0 : C_num ≤ u0)
    (hJlen : J_cert.length = Nu)
    (hGs_len : Gs.length = ngrp)
    (hKers_len : Kers.length = 8 * ngrp)
    (hKers_ok : checkKersAll s_sub hy h 0 Kers = true)
    (hG_ok : ∀ g < ngrp,
      Group8Ok (u0 - C_num) (B_num + (g * 8) * hy) h hy s_sub
        ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub) Nu (Nu + (8 * ngrp) * s_sub - 1)
        (Kers.getD (g * 8 + 0) []) (Kers.getD (g * 8 + 1) [])
        (Kers.getD (g * 8 + 2) []) (Kers.getD (g * 8 + 3) [])
        (Kers.getD (g * 8 + 4) []) (Kers.getD (g * 8 + 5) [])
        (Kers.getD (g * 8 + 6) []) (Kers.getD (g * 8 + 7) [])
        (Jgs.getD g []) (Gs.getD g []))
    (hJsum : ∀ k < Nu,
      ∑ g ∈ Finset.range ngrp, (Jgs.getD g []).getD (Nu - 1 - k) 0 ≤ J_cert.getD k 0 * JG_MUL) :
    ∀ k < Nu, ∀ u : ℝ, ((u0 + k * h : ℕ) : ℝ) / D_den ≤ u → u ≤ ((u0 + (k + 1) * h : ℕ) : ℝ) / D_den →
      J_real u ≤ (J_cert.getD k 0 : ℝ) / S_sc := by
  have hlen8 : ∀ g < Gs.length, (Gs.getD g []).length = 8 := fun g hg => (hG_ok g (by omega)).1
  apply J_cert_sound (u0 := u0) (M2 := 8 * ngrp) (s_sub := s_sub) (h := h) (hy := hy) (Nu := Nu)
    (S_cols := concatLists Gs) (Kers := Kers) (J_cert := J_cert)
    (by omega) hs_pos hh_pos hh_even hhy_eq hspan hC_le_u0 hJlen
  · intro r hr idx hidx
    rw [concatLists_getD_len8 [] Gs hlen8 r (by omega)]
    have hg : r / 8 < ngrp := by omega
    have hj : r % 8 < 8 := Nat.mod_lt r (by omega)
    have hr_eq : B_num + r * hy = B_num + (r / 8 * 8) * hy + (r % 8) * hy := by
      have : r = r / 8 * 8 + r % 8 := by omega
      conv_lhs => rw [this]
      ring
    rw [hr_eq]
    exact (hG_ok (r / 8) hg).2.2.1 (r % 8) hj idx hidx
  · intro r hr
    rw [concatLists_getD_len8 [] Gs hlen8 r (by omega)]
    exact (hG_ok (r / 8) (by omega)).2.1 (r % 8) (Nat.mod_lt r (by omega))
  · intro r hr
    simpa using checkKersAll_spec hKers_ok r (by omega)
  · intro k hk
    rw [sum_range_mul_eight]
    have hstep : ∀ g ∈ Finset.range ngrp,
        ∑ j ∈ Finset.range 8,
          dotSmall (Kers.getD (g * 8 + j) [])
            (((concatLists Gs).getD (g * 8 + j) []).drop ((8 * ngrp - 1 - (g * 8 + j)) * s_sub + k)) 0 ≤
        (Jgs.getD g []).getD (Nu - 1 - k) 0 * JG_DIV := by
      intro g hg
      have hg' : g < ngrp := Finset.mem_range.mp hg
      have hG := (hG_ok g hg').2.2.2 k hk
      have hterm : ∀ j < 8,
          dotSmall (Kers.getD (g * 8 + j) [])
            (((concatLists Gs).getD (g * 8 + j) []).drop ((8 * ngrp - 1 - (g * 8 + j)) * s_sub + k)) 0 =
          dotSmall (Kers.getD (g * 8 + j) [])
            (((Gs.getD g []).getD j []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + (7 - j) * s_sub + k)) 0 := by
        intro j hj
        rw [concatLists_getD_len8 [] Gs hlen8 (g * 8 + j) (by omega)]
        have hdiv : (g * 8 + j) / 8 = g := by omega
        have hmod : (g * 8 + j) % 8 = j := by omega
        rw [hdiv, hmod]
        congr 2
        have hsub : 8 * ngrp - 1 - (g * 8 + j) = (8 * ngrp - 1 - (g * 8 + 7)) + (7 - j) := by omega
        rw [hsub, Nat.add_mul]
      have hsum8 : ∑ j ∈ Finset.range 8,
          dotSmall (Kers.getD (g * 8 + j) [])
            (((concatLists Gs).getD (g * 8 + j) []).drop ((8 * ngrp - 1 - (g * 8 + j)) * s_sub + k)) 0 =
          dotSmall (Kers.getD (g * 8 + 0) []) (((Gs.getD g []).getD 0 []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + 7 * s_sub + k)) 0 +
          dotSmall (Kers.getD (g * 8 + 1) []) (((Gs.getD g []).getD 1 []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + 6 * s_sub + k)) 0 +
          dotSmall (Kers.getD (g * 8 + 2) []) (((Gs.getD g []).getD 2 []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + 5 * s_sub + k)) 0 +
          dotSmall (Kers.getD (g * 8 + 3) []) (((Gs.getD g []).getD 3 []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + 4 * s_sub + k)) 0 +
          dotSmall (Kers.getD (g * 8 + 4) []) (((Gs.getD g []).getD 4 []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + 3 * s_sub + k)) 0 +
          dotSmall (Kers.getD (g * 8 + 5) []) (((Gs.getD g []).getD 5 []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + 2 * s_sub + k)) 0 +
          dotSmall (Kers.getD (g * 8 + 6) []) (((Gs.getD g []).getD 6 []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + 1 * s_sub + k)) 0 +
          dotSmall (Kers.getD (g * 8 + 7) []) (((Gs.getD g []).getD 7 []).drop ((8 * ngrp - 1 - (g * 8 + 7)) * s_sub + 0 * s_sub + k)) 0 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        rw [hterm 0 (by omega), hterm 1 (by omega), hterm 2 (by omega), hterm 3 (by omega),
            hterm 4 (by omega), hterm 5 (by omega), hterm 6 (by omega), hterm 7 (by omega)]
      rw [hsum8]
      exact hG
    calc ∑ g ∈ Finset.range ngrp, ∑ j ∈ Finset.range 8,
            dotSmall (Kers.getD (g * 8 + j) [])
              (((concatLists Gs).getD (g * 8 + j) []).drop ((8 * ngrp - 1 - (g * 8 + j)) * s_sub + k)) 0
        ≤ ∑ g ∈ Finset.range ngrp, (Jgs.getD g []).getD (Nu - 1 - k) 0 * JG_DIV := Finset.sum_le_sum hstep
      _ = (∑ g ∈ Finset.range ngrp, (Jgs.getD g []).getD (Nu - 1 - k) 0) * JG_DIV := (Finset.sum_mul ..).symm
      _ ≤ (J_cert.getD k 0 * JG_MUL) * JG_DIV := Nat.mul_le_mul_right JG_DIV (hJsum k hk)
      _ = J_cert.getD k 0 * S_sc := by rw [Nat.mul_assoc]; rfl

-- Second: given J_cert_sound on [u0, u0 + Nu*h] / D_den, checkW0Go, checkJWin, checkSlices,
-- prove buchstabIntegral ≤ 70737 / 10^9 on [phi0, phi0 + Nphi * mult * h] / D_den!
private lemma conv_band_sound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {phi0 h mult Nphi N0 Nu : ℕ} {W0 J_cert J_win : List ℕ}
    (hh_pos : 0 < h) (hmult_pos : 0 < mult) (hNphi_pos : 0 < Nphi)
    (hphi0_ge : 2 * D_den ≤ phi0)
    (hphi1_le : 100 * (phi0 + Nphi * mult * h) ≤ 229 * D_den)
    (hN0_cov : A1_num - A0_num ≤ N0 * h) (hN0_lt : (N0 - 1) * h < A1_num - A0_num)
    (hNu_eq : Nu = (Nphi - 1) * mult + N0 + mult)
    (hW0 : checkW0Go h N0 A1_num W0 = true)
    (hJlen : J_cert.length = Nu)
    (hJ_bound : ∀ k < Nu, ∀ u : ℝ,
      ((phi0 - A1_num + k * h : ℕ) : ℝ) / D_den ≤ u →
      u ≤ ((phi0 - A1_num + (k + 1) * h : ℕ) : ℝ) / D_den →
      J_real u ≤ (J_cert.getD k 0 : ℝ) / S_sc)
    (hJW_len : J_win.length + mult = Nu)
    (hJW_spec : ∀ k < J_win.length, ∀ q ≤ mult, J_cert.getD (k + q) 0 ≤ J_win.getD k 0)
    (hSl : checkSlices Nphi mult W0 J_win = true) :
    ∀ φ : ℝ, (phi0 : ℝ) / D_den ≤ φ → φ ≤ ((phi0 + Nphi * mult * h : ℕ) : ℝ) / D_den →
      buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
        ((70737 / 1000000000) : ℝ) := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have hS : (0 : ℝ) < S_sc := by unfold S_sc; norm_num
  have ha01 : a0R ≤ a1R := by unfold a0R a1R; norm_num
  have ha0_pos : (0 : ℝ) < a0R := by unfold a0R; norm_num
  have hA0_pos : 0 < A0_num := by unfold A0_num; omega
  have hA01 : A0_num < A1_num := by unfold A0_num A1_num; omega
  have hA1_le_phi0 : A1_num ≤ phi0 := by unfold A1_num D_den at *; omega
  obtain ⟨hW0_len, hW0_spec⟩ := checkW0Go_spec hW0
  have hSl_spec := checkSlices_spec hSl
  intro φ hφ_lo hφ_hi
  have hφ2 : 2 ≤ φ := by
    have : (2 : ℝ) ≤ (phi0 : ℝ) / D_den := by
      rw [le_div_iff₀ hD]; exact_mod_cast hphi0_ge
    linarith
  have hφhi229 : φ ≤ (229 / 100 : ℝ) := by
    have : ((phi0 + Nphi * mult * h : ℕ) : ℝ) / D_den ≤ 229 / 100 := by
      rw [div_le_div_iff₀ hD (by norm_num)]
      have hmul_comm : (phi0 + Nphi * mult * h) * 100 ≤ 229 * D_den := by omega
      exact_mod_cast hmul_comm
    linarith
  rw [r0j19_buchstabIntegral_eq_conv hω hz hφ2 hφhi229]
  -- Pick slice index p < Nphi such that phi0 + p*mult*h ≤ φ * D_den ≤ phi0 + (p+1)*mult*h
  set step := mult * h
  have hstep_pos : 0 < step := Nat.mul_pos hmult_pos hh_pos
  have hstep_r : (0 : ℝ) < step := by exact_mod_cast hstep_pos
  have hex_p : ∃ p < Nphi,
      ((phi0 + p * step : ℕ) : ℝ) / D_den ≤ φ ∧ φ ≤ ((phi0 + (p + 1) * step : ℕ) : ℝ) / D_den := by
    let idx := Nat.floor ((φ * D_den - phi0) / step)
    have hdiff_nn : 0 ≤ φ * D_den - phi0 := by
      have := (div_le_iff₀ hD).mp hφ_lo; linarith
    have hdiff_le : φ * D_den - phi0 ≤ (Nphi : ℝ) * step := by
      have := (le_div_iff₀ hD).mp hφ_hi
      have hcast : ((phi0 + Nphi * mult * h : ℕ) : ℝ) = (phi0 : ℝ) + (Nphi : ℝ) * step := by
        simp only [step]; push_cast; ring
      linarith
    by_cases hlt : idx < Nphi
    · refine ⟨idx, hlt, ?_, ?_⟩
      · have hfl := Nat.floor_le (div_nonneg hdiff_nn (le_of_lt hstep_r))
        have hmul := (le_div_iff₀ hstep_r).mp hfl
        rw [div_le_iff₀ hD]; push_cast; linarith
      · have hfl := Nat.lt_floor_add_one ((φ * D_den - phi0) / step)
        have hmul := (div_lt_iff₀ hstep_r).mp hfl
        rw [le_div_iff₀ hD]; push_cast; linarith
    · push Not at hlt
      refine ⟨Nphi - 1, by omega, ?_, ?_⟩
      · have hfl : (Nphi : ℝ) ≤ (φ * D_den - phi0) / step :=
          le_trans (by exact_mod_cast hlt) (Nat.floor_le (div_nonneg hdiff_nn (le_of_lt hstep_r)))
        have hmul := (le_div_iff₀ hstep_r).mp hfl
        have hsub : (Nphi - 1 : ℕ) * step ≤ Nphi * step := Nat.mul_le_mul_right step (by omega)
        rw [div_le_iff₀ hD]
        have hle2 : ((phi0 + (Nphi - 1) * step : ℕ) : ℝ) ≤ (phi0 : ℝ) + (Nphi : ℝ) * step := by
          have : phi0 + (Nphi - 1) * step ≤ phi0 + Nphi * step := by omega
          exact_mod_cast this
        linarith
      · have hrew : Nphi - 1 + 1 = Nphi := by omega
        rw [hrew]; simpa only [step, mul_assoc] using hφ_hi
  obtain ⟨p, hp, hφp_lo, hφp_hi⟩ := hex_p
  -- Split ∫_{a0R}^{a1R} (1/x0) J_real (φ - x0) dx0 into N0 subintervals [xlo_d, xhi_d] / D_den!
  have hcont_x0 : ContinuousOn (fun x0 : ℝ => (1 / x0) * J_real (φ - x0)) (Icc a0R a1R) :=
    (continuousOn_const.div continuousOn_id (fun x0 hx0 => ne_of_gt (lt_of_lt_of_le ha0_pos hx0.1))).mul
      (J_real_continuous.comp (continuous_const.sub continuous_id)).continuousOn
  let xpt : ℕ → ℕ := fun d => max A0_num (A1_num - d * h)
  have hxpt_anti : ∀ d, xpt (d + 1) ≤ xpt d := fun d => by
    simp only [xpt]; apply max_le_max_left; exact Nat.sub_le_sub_left (Nat.mul_le_mul_right h (by omega)) A1_num
  have hxpt_ge : ∀ d, A0_num ≤ xpt d := fun d => le_max_left _ _
  have hxpt_le : ∀ d, xpt d ≤ A1_num := fun d => max_le (le_of_lt hA01) (Nat.sub_le _ _)
  have hxpt_0 : xpt 0 = A1_num := by simp [xpt, le_of_lt hA01]
  have hxpt_N0 : xpt N0 = A0_num := by
    simp only [xpt]; exact max_eq_left (by omega)
  have hsplit_x0 : ∫ x0 in a0R..a1R, (1 / x0) * J_real (φ - x0) =
      ∑ d ∈ Finset.range N0,
        ∫ x0 in ((xpt (d + 1) : ℝ) / D_den)..((xpt d : ℝ) / D_den), (1 / x0) * J_real (φ - x0) := by
    have haux : ∀ m ≤ N0,
        ∫ x0 in ((xpt m : ℝ) / D_den)..a1R, (1 / x0) * J_real (φ - x0) =
        ∑ d ∈ Finset.range m,
          ∫ x0 in ((xpt (d + 1) : ℝ) / D_den)..((xpt d : ℝ) / D_den), (1 / x0) * J_real (φ - x0) := by
      intro m hm
      induction m with
      | zero => rw [hxpt_0, ← a1R_eq]; simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih (by omega)]
        have h1 : a0R ≤ (xpt (m + 1) : ℝ) / D_den := by
          rw [a0R_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hxpt_ge (m + 1)) (le_of_lt hD)
        have h2 : (xpt (m + 1) : ℝ) / D_den ≤ (xpt m : ℝ) / D_den :=
          div_le_div_of_nonneg_right (by exact_mod_cast hxpt_anti m) (le_of_lt hD)
        have h3 : (xpt m : ℝ) / D_den ≤ a1R := by
          rw [a1R_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hxpt_le m) (le_of_lt hD)
        have hadd_adj := (intervalIntegral.integral_add_adjacent_intervals
          ((hcont_x0.mono (Icc_subset_Icc h1 h3)).intervalIntegrable_of_Icc (μ := volume) h2)
          ((hcont_x0.mono (Icc_subset_Icc (le_trans h1 h2) le_rfl)).intervalIntegrable_of_Icc (μ := volume) h3)).symm
        linarith
    have htop := haux N0 le_rfl
    rwa [hxpt_N0, ← a0R_eq] at htop
  -- Bound each d-bin [xpt(d+1), xpt(d)] / D_den by (W0[d]/S_sc) * (J_win[p*mult + d]/S_sc)!
  have hbin : ∀ d < N0,
      ∫ x0 in ((xpt (d + 1) : ℝ) / D_den)..((xpt d : ℝ) / D_den), (1 / x0) * J_real (φ - x0) ≤
      ((W0.getD d 0 : ℝ) / S_sc) * ((J_win.getD (p * mult + d) 0 : ℝ) / S_sc) := by
    intro d hd
    have hxd_eq : xpt d = A1_num - d * h := by
      simp only [xpt]
      have h1 : d * h ≤ (N0 - 1) * h := Nat.mul_le_mul_right h (by omega)
      exact max_eq_right (by omega)
    have hxlo_eq : xpt (d + 1) = max A0_num (A1_num - d * h - h) := by
      simp only [xpt]; congr 1; rw [Nat.sub_sub]; congr 1; ring
    have hle_n : xpt (d + 1) ≤ xpt d := hxpt_anti d
    have hle_r : (xpt (d + 1) : ℝ) / D_den ≤ (xpt d : ℝ) / D_den :=
      div_le_div_of_nonneg_right (by exact_mod_cast hle_n) (le_of_lt hD)
    have hlo_pos_n : 0 < xpt (d + 1) := lt_of_lt_of_le hA0_pos (hxpt_ge (d + 1))
    have hlo_pos : (0 : ℝ) < (xpt (d + 1) : ℝ) / D_den := div_pos (by exact_mod_cast hlo_pos_n) hD
    have hJW_idx_lt : p * mult + d < J_win.length := by
      have : p * mult ≤ (Nphi - 1) * mult := Nat.mul_le_mul_right mult (by omega)
      omega
    -- On x0 ∈ [xpt(d+1)/D, xpt(d)/D], J_real(φ - x0) ≤ J_win[p*mult + d] / S_sc!
    have hJ_pt : ∀ x0 ∈ Icc ((xpt (d + 1) : ℝ) / D_den) ((xpt d : ℝ) / D_den),
        J_real (φ - x0) ≤ (J_win.getD (p * mult + d) 0 : ℝ) / S_sc := by
      intro x0 hx0
      set u0 := phi0 - A1_num
      set k0 := p * mult + d
      have hu_lo : ((u0 + k0 * h : ℕ) : ℝ) / D_den ≤ φ - x0 := by
        have h1 : (phi0 : ℝ) - (A1_num : ℝ) + (p * mult + d : ℕ) * h =
            (phi0 + p * step : ℕ) - (A1_num - d * h : ℕ) := by
          have hd_le : d * h ≤ A1_num := by
            have : d * h ≤ (N0 - 1) * h := Nat.mul_le_mul_right h (by omega); omega
          rw [Nat.cast_sub hd_le]; simp only [step]; push_cast; ring
        have h2 : ((u0 + k0 * h : ℕ) : ℝ) = (phi0 : ℝ) - A1_num + (p * mult + d : ℕ) * h := by
          simp only [u0, k0]; rw [Nat.cast_add, Nat.cast_sub hA1_le_phi0]; push_cast; ring
        rw [h2, h1, sub_div]
        have hx0_le : x0 ≤ ((A1_num - d * h : ℕ) : ℝ) / D_den := by rw [← hxd_eq]; exact hx0.2
        linarith [hφp_lo]
      have hu_hi : φ - x0 ≤ ((u0 + (k0 + 1 + mult) * h : ℕ) : ℝ) / D_den := by
        have hx0_ge : ((A1_num - (d + 1) * h : ℕ) : ℝ) / D_den ≤ x0 := by
          have : A1_num - (d + 1) * h ≤ xpt (d + 1) := le_max_right _ _
          exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast this) (le_of_lt hD)) hx0.1
        have h1 : ((phi0 + (p + 1) * step : ℕ) : ℝ) - ((A1_num - (d + 1) * h : ℕ) : ℝ) ≤
            ((u0 + (k0 + 1 + mult) * h : ℕ) : ℝ) := by
          have hsub_le : (A1_num : ℝ) - ((d + 1) * h : ℕ) ≤ ((A1_num - (d + 1) * h : ℕ) : ℝ) := by
            by_cases hle' : (d + 1) * h ≤ A1_num
            · rw [Nat.cast_sub hle']
            · have : A1_num - (d + 1) * h = 0 := Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hle'))
              rw [this]; push_cast; have : (A1_num : ℝ) < ((d + 1) * h : ℕ) := by exact_mod_cast not_le.mp hle'
              push_cast at this; linarith
          have hcast_rhs : ((u0 + (k0 + 1 + mult) * h : ℕ) : ℝ) = (phi0 : ℝ) - A1_num + ((k0 + 1 + mult) * h : ℕ) := by
            simp only [u0]; rw [Nat.cast_add, Nat.cast_sub hA1_le_phi0]
          rw [hcast_rhs]
          simp only [k0, step] at hsub_le ⊢
          push_cast at hsub_le ⊢; linarith
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt hD)
        rw [sub_div] at h2
        linarith [hφp_hi]
      -- Find q ≤ mult with φ - x0 ∈ [u0 + (k0+q)*h, u0 + (k0+q+1)*h] / D_den
      have hh_r : (0 : ℝ) < h := by exact_mod_cast hh_pos
      let q := min mult (Nat.floor (((φ - x0) * D_den - (u0 + k0 * h : ℕ)) / h))
      have hq_le : q ≤ mult := min_le_left _ _
      have hdiff_nn : 0 ≤ (φ - x0) * D_den - (u0 + k0 * h : ℕ) := by
        have := (div_le_iff₀ hD).mp hu_lo; linarith
      have hdiff_le : (φ - x0) * D_den - (u0 + k0 * h : ℕ) ≤ ((mult + 1 : ℕ) : ℝ) * h := by
        have := (le_div_iff₀ hD).mp hu_hi
        have hcast : ((u0 + (k0 + 1 + mult) * h : ℕ) : ℝ) = ((u0 + k0 * h : ℕ) : ℝ) + ((mult + 1 : ℕ) : ℝ) * h := by
          push_cast; ring
        linarith
      have hq_lo : ((u0 + (k0 + q) * h : ℕ) : ℝ) / D_den ≤ φ - x0 := by
        have hfl : (q : ℝ) ≤ ((φ - x0) * D_den - (u0 + k0 * h : ℕ)) / h :=
          le_trans (by exact_mod_cast min_le_right _ _) (Nat.floor_le (div_nonneg hdiff_nn (le_of_lt hh_r)))
        have hmul := (le_div_iff₀ hh_r).mp hfl
        rw [div_le_iff₀ hD]; push_cast at hmul ⊢; linarith
      have hq_hi : φ - x0 ≤ ((u0 + (k0 + q + 1) * h : ℕ) : ℝ) / D_den := by
        by_cases hmin : Nat.floor (((φ - x0) * D_den - (u0 + k0 * h : ℕ)) / h) ≤ mult
        · have hq_eq : q = Nat.floor (((φ - x0) * D_den - (u0 + k0 * h : ℕ)) / h) := min_eq_right hmin
          have hfl := Nat.lt_floor_add_one (((φ - x0) * D_den - (u0 + k0 * h : ℕ)) / h)
          rw [← hq_eq] at hfl
          have hmul := (div_lt_iff₀ hh_r).mp hfl
          rw [le_div_iff₀ hD]; push_cast at hmul ⊢; linarith
        · have hq_eq : q = mult := min_eq_left (le_of_lt (not_le.mp hmin))
          rw [hq_eq, show k0 + mult + 1 = k0 + 1 + mult by omega]; exact hu_hi
      have hJ_le := hJ_bound (k0 + q) (by omega) (φ - x0) hq_lo hq_hi
      have hJW_le : (J_cert.getD (k0 + q) 0 : ℝ) / S_sc ≤ (J_win.getD k0 0 : ℝ) / S_sc :=
        div_le_div_of_nonneg_right (by exact_mod_cast hJW_spec k0 hJW_idx_lt q hq_le) (le_of_lt hS)
      exact le_trans hJ_le hJW_le
    -- Integrate (1/x0) * J_real(φ - x0) ≤ (1/x0) * (J_win[k0] / S_sc) over [xpt(d+1)/D, xpt(d)/D]!
    have hinv_cont : ContinuousOn (fun x0 : ℝ => 1 / x0) (Icc ((xpt (d + 1) : ℝ) / D_den) ((xpt d : ℝ) / D_den)) :=
      continuousOn_const.div continuousOn_id (fun x0 hx0 => ne_of_gt (lt_of_lt_of_le hlo_pos hx0.1))
    have h1 : a0R ≤ (xpt (d + 1) : ℝ) / D_den := by
      rw [a0R_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hxpt_ge (d + 1)) (le_of_lt hD)
    have h2 : (xpt d : ℝ) / D_den ≤ a1R := by
      rw [a1R_eq]; exact div_le_div_of_nonneg_right (by exact_mod_cast hxpt_le d) (le_of_lt hD)
    have hmono := intervalIntegral.integral_mono_on hle_r
      ((hcont_x0.mono (Icc_subset_Icc h1 h2)).intervalIntegrable_of_Icc (μ := volume) hle_r)
      ((hinv_cont.intervalIntegrable_of_Icc (μ := volume) hle_r).mul_const ((J_win.getD (p * mult + d) 0 : ℝ) / S_sc))
      (fun x0 hx0 => mul_le_mul_of_nonneg_left (hJ_pt x0 hx0)
        (div_nonneg zero_le_one (le_of_lt (lt_of_lt_of_le hlo_pos hx0.1))))
    rw [intervalIntegral.integral_mul_const] at hmono
    -- Evaluate ∫_{xlo/D}^{xhi/D} (1/x0) dx0 = log(xhi/xlo) ≤ W0[d] / S_sc!
    have hlog_eval : ∫ x0 in ((xpt (d + 1) : ℝ) / D_den)..((xpt d : ℝ) / D_den), (1 / x0 : ℝ) =
        Real.log (1 + ((xpt d - xpt (d + 1) : ℕ) : ℝ) / (xpt (d + 1) : ℝ)) := by
      have hF : ∀ x ∈ uIcc ((xpt (d + 1) : ℝ) / D_den) ((xpt d : ℝ) / D_den), HasDerivAt Real.log (1 / x) x := by
        intro x hx; rw [uIcc_of_le hle_r] at hx
        exact (Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hlo_pos hx.1))) ▸d (by ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hinv_cont.intervalIntegrable_of_Icc hle_r),
          ← Real.log_div (ne_of_gt (lt_of_lt_of_le hlo_pos hle_r)) (ne_of_gt hlo_pos)]
      congr 1
      have hsub : ((xpt d - xpt (d + 1) : ℕ) : ℝ) = (xpt d : ℝ) - xpt (d + 1) := Nat.cast_sub hle_n
      have hlo_r : (0 : ℝ) < xpt (d + 1) := by exact_mod_cast hlo_pos_n
      rw [hsub]; field_simp [ne_of_gt hD, ne_of_gt hlo_r]; ring
    have hw0_le : ∫ x0 in ((xpt (d + 1) : ℝ) / D_den)..((xpt d : ℝ) / D_den), (1 / x0 : ℝ) ≤
        (W0.getD d 0 : ℝ) / S_sc := by
      rw [hlog_eval]
      have h1 := log1pNat_sound (p := xpt d - xpt (d + 1)) hlo_pos_n
      have h2 := hW0_spec d hd
      rw [← hxlo_eq, ← hxd_eq] at h2
      exact le_trans h1 (div_le_div_of_nonneg_right (by exact_mod_cast h2) (le_of_lt hS))
    exact le_trans hmono (mul_le_mul_of_nonneg_right hw0_le (div_nonneg (Nat.cast_nonneg _) (le_of_lt hS)))
  -- Sum over d < N0 and connect to dotNat W0 (J_win.drop (p * mult)) 0 ≤ TARGET_S2!
  rw [hsplit_x0]
  have hsum_le : ∑ d ∈ Finset.range N0,
      ∫ x0 in ((xpt (d + 1) : ℝ) / D_den)..((xpt d : ℝ) / D_den), (1 / x0) * J_real (φ - x0) ≤
      (∑ d ∈ Finset.range N0, ((W0.getD d 0 * J_win.getD (p * mult + d) 0 : ℕ) : ℝ)) / (S_sc * S_sc) := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum (fun d hd => ?_)
    have h1 := hbin d (Finset.mem_range.mp hd)
    have hrew : ((W0.getD d 0 : ℝ) / S_sc) * ((J_win.getD (p * mult + d) 0 : ℝ) / S_sc) =
        ((W0.getD d 0 * J_win.getD (p * mult + d) 0 : ℕ) : ℝ) / (S_sc * S_sc) := by
      push_cast; ring
    linarith
  have hdrop_len : W0.length ≤ (J_win.drop (p * mult)).length := by
    rw [List.length_drop, hW0_len]
    have : p * mult ≤ (Nphi - 1) * mult := Nat.mul_le_mul_right mult (by omega)
    omega
  have hdot_eq : ∑ d ∈ Finset.range N0, W0.getD d 0 * J_win.getD (p * mult + d) 0 =
      dotNat W0 (J_win.drop (p * mult)) 0 := by
    rw [dotNat_eq_sum_getD _ _ hdrop_len, hW0_len]
    apply Finset.sum_congr rfl
    intro d _; rw [list_getD_drop]
  have hdot_le : dotNat W0 (J_win.drop (p * mult)) 0 ≤ TARGET_S2 := hSl_spec p hp
  have hcast_le : (∑ d ∈ Finset.range N0, ((W0.getD d 0 * J_win.getD (p * mult + d) 0 : ℕ) : ℝ)) ≤ (TARGET_S2 : ℝ) := by
    rw [← Nat.cast_sum, hdot_eq]; exact_mod_cast hdot_le
  have hfinal := div_le_div_of_nonneg_right hcast_le (mul_nonneg (le_of_lt hS) (le_of_lt hS))
  have htarg_eq : (TARGET_S2 : ℝ) / (S_sc * S_sc) = (70737 / 1000000000 : ℝ) := by
    unfold TARGET_S2 S_sc; norm_num
  linarith


/-! ### Part 6: Imported Verified Certificate Theorems -/

private theorem SJ_b3_g0_ok : checkSJ8Go t0_b3 810770400 h_288 hy_48 err55_48 err110_48 6 240 525 false Ker_288_0 Ker_288_1 Ker_288_2 Ker_288_3 Ker_288_4 Ker_288_5 Ker_288_6 Ker_288_7 812 Bdry_b3_8 [] Jg_b3_0 [] [] [] [] [] [] [] [] = true := R0J19Cert.b3_certs_lo.1
private theorem SJ_b3_g1_ok : checkSJ8Go t0_b3 825511680 h_288 hy_48 err55_48 err110_48 6 192 525 true Ker_288_8 Ker_288_9 Ker_288_10 Ker_288_11 Ker_288_12 Ker_288_13 Ker_288_14 Ker_288_15 812 Bdry_b3_16 Bdry_b3_8 Jg_b3_1 [] [] [] [] [] [] [] [] = true := R0J19Cert.b3_certs_lo.2.1
private theorem SJ_b3_g2_ok : checkSJ8Go t0_b3 840252960 h_288 hy_48 err55_48 err110_48 6 144 525 true Ker_288_16 Ker_288_17 Ker_288_18 Ker_288_19 Ker_288_20 Ker_288_21 Ker_288_22 Ker_288_23 812 Bdry_b3_24 Bdry_b3_16 Jg_b3_2 [] [] [] [] [] [] [] [] = true := R0J19Cert.b3_certs_lo.2.2
private theorem SJ_b3_g3_ok : checkSJ8Go t0_b3 854994240 h_288 hy_48 err55_48 err110_48 6 96 525 true Ker_288_24 Ker_288_25 Ker_288_26 Ker_288_27 Ker_288_28 Ker_288_29 Ker_288_30 Ker_288_31 812 Bdry_b3_32 Bdry_b3_24 Jg_b3_3 [] [] [] [] [] [] [] [] = true := R0J19Cert.b3_certs_hi.1
private theorem SJ_b3_g4_ok : checkSJ8Go t0_b3 869735520 h_288 hy_48 err55_48 err110_48 6 48 525 true Ker_288_32 Ker_288_33 Ker_288_34 Ker_288_35 Ker_288_36 Ker_288_37 Ker_288_38 Ker_288_39 812 Bdry_b3_40 Bdry_b3_32 Jg_b3_4 [] [] [] [] [] [] [] [] = true := R0J19Cert.b3_certs_hi.2.1
private theorem SJ_b3_g5_ok : checkSJ8Go t0_b3 884476800 h_288 hy_48 err55_48 err110_48 6 0 525 true Ker_288_40 Ker_288_41 Ker_288_42 Ker_288_43 Ker_288_44 Ker_288_45 Ker_288_46 Ker_288_47 812 [] Bdry_b3_40 Jg_b3_5 [] [] [] [] [] [] [] [] = true := R0J19Cert.b3_certs_hi.2.2.1
private theorem Jsum_b3_ok : checkJ6Sum Jg_b3_0 Jg_b3_1 Jg_b3_2 Jg_b3_3 Jg_b3_4 Jg_b3_5 Jc_b3.reverse = true := R0J19Cert.b3_certs_hi.2.2.2.1
private theorem JW_b3_ok : checkJWin1 Jc_b3 Jw_b3 = true := R0J19Cert.b3_certs_hi.2.2.2.2.1
private theorem Sl_b3_ok : checkSlices 128 1 W0_cert_288 Jw_b3 = true := R0J19Cert.b3_certs_hi.2.2.2.2.2.1
private theorem W0_cert_288_ok : checkW0Go h_288 397 A1_num W0_cert_288 = true := R0J19Cert.b3_certs_hi.2.2.2.2.2.2.1
private theorem Kers_288_ok : checkKersAll 6 hy_48 h_288 0 Kers_288 = true := R0J19Cert.b3_certs_hi.2.2.2.2.2.2.2
private theorem W0_cert_16_ok : checkW0Go h_16 23 A1_num W0_cert_16 = true := R0J19Cert.outer_certs.1
private theorem Kers_16_ok : checkKersAll 2 hy_8 h_16 0 Kers_16 = true := R0J19Cert.outer_certs.2.1
private theorem W0_cert_48_ok : checkW0Go h_48 67 A1_num W0_cert_48 = true := R0J19Cert.outer_certs.2.2.1
private theorem Kers_48_ok : checkKersAll 3 hy_16 h_48 0 Kers_48 = true := R0J19Cert.outer_certs.2.2.2.1
private theorem SJ_b1_g0_ok : checkSJ8Go t0_b1 810770400 h_16 hy_8 err55_8 err110_8 2 0 55 false Ker_16_0 Ker_16_1 Ker_16_2 Ker_16_3 Ker_16_4 Ker_16_5 Ker_16_6 Ker_16_7 70 [] [] Jg_b1_0 [] [] [] [] [] [] [] [] = true := R0J19Cert.outer_certs.2.2.2.2.1
private theorem Jsum_b1_ok : checkJ1Sum Jg_b1_0 Jc_b1.reverse = true := R0J19Cert.outer_certs.2.2.2.2.2.1
private theorem JW_b1_ok : checkJWin4 Jc_b1 Jw_b1 = true := R0J19Cert.outer_certs.2.2.2.2.2.2.1
private theorem Sl_b1_ok : checkSlices 8 4 W0_cert_16 Jw_b1 = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.1
private theorem SJ_b2_g0_ok : checkSJ8Go t0_b2 810770400 h_48 hy_16 err55_16 err110_16 3 24 80 false Ker_48_0 Ker_48_1 Ker_48_2 Ker_48_3 Ker_48_4 Ker_48_5 Ker_48_6 Ker_48_7 127 Bdry_b2_8 [] Jg_b2_0 [] [] [] [] [] [] [] [] = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.1
private theorem SJ_b2_g1_ok : checkSJ8Go t0_b2 854994240 h_48 hy_16 err55_16 err110_16 3 0 80 true Ker_48_8 Ker_48_9 Ker_48_10 Ker_48_11 Ker_48_12 Ker_48_13 Ker_48_14 Ker_48_15 127 [] Bdry_b2_8 Jg_b2_1 [] [] [] [] [] [] [] [] = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.1
private theorem Jsum_b2_ok : checkJ2Sum Jg_b2_0 Jg_b2_1 Jc_b2.reverse = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.1
private theorem JW_b2_ok : checkJWin1 Jc_b2 Jw_b2 = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.1
private theorem Sl_b2_ok : checkSlices 13 1 W0_cert_48 Jw_b2 = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem SJ_b4_g0_ok : checkSJ8Go t0_b4 810770400 h_48 hy_16 err55_16 err110_16 3 24 90 false Ker_48_0 Ker_48_1 Ker_48_2 Ker_48_3 Ker_48_4 Ker_48_5 Ker_48_6 Ker_48_7 137 Bdry_b4_8 [] Jg_b4_0 [] [] [] [] [] [] [] [] = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem SJ_b4_g1_ok : checkSJ8Go t0_b4 854994240 h_48 hy_16 err55_16 err110_16 3 0 90 true Ker_48_8 Ker_48_9 Ker_48_10 Ker_48_11 Ker_48_12 Ker_48_13 Ker_48_14 Ker_48_15 137 [] Bdry_b4_8 Jg_b4_1 [] [] [] [] [] [] [] [] = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem Jsum_b4_ok : checkJ2Sum Jg_b4_0 Jg_b4_1 Jc_b4.reverse = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem JW_b4_ok : checkJWin1 Jc_b4 Jw_b4 = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem Sl_b4_ok : checkSlices 23 1 W0_cert_48 Jw_b4 = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem SJ_b5_g0_ok : checkSJ8Go t0_b5 810770400 h_16 hy_8 err55_8 err110_8 2 0 75 false Ker_16_0 Ker_16_1 Ker_16_2 Ker_16_3 Ker_16_4 Ker_16_5 Ker_16_6 Ker_16_7 90 [] [] Jg_b5_0 [] [] [] [] [] [] [] [] = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem Jsum_b5_ok : checkJ1Sum Jg_b5_0 Jc_b5.reverse = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem JW_b5_ok : checkJWin4 Jc_b5 Jw_b5 = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem Sl_b5_ok : checkSlices 13 4 W0_cert_16 Jw_b5 = true := R0J19Cert.outer_certs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private lemma band_b1_sound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∀ φ : ℝ, (phi0_b1 : ℝ) / D_den ≤ φ → φ ≤ ((4133454912 : ℕ) : ℝ) / D_den →
      buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
        ((70737 / 1000000000) : ℝ) := by
  have hphi1_eq : phi0_b1 + 8 * 4 * h_16 = 4133454912 := by unfold phi0_b1 h_16; omega
  rw [← hphi1_eq]
  have ht0_eq : t0_b1 = phi0_b1 - A1_num - C_num := by unfold t0_b1 phi0_b1 A1_num C_num; omega
  have hnm_eq : 70 = 55 + (8 * 1) * 2 - 1 := by omega
  have hS_end : ∀ idx < 70,
      ∫ x in (((810770400 + 8 * hy_8 : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0_b1 + idx * h_16 : ℕ) : ℝ) / D_den)
          (((t0_b1 + idx * h_16 + 2 * h_16 : ℕ) : ℝ) / D_den) x ≤
        (([] : List ℕ).getD (70 - 1 - idx) 0 : ℝ) / S_sc := by
    intro idx _
    have hc_eq : ((810770400 + 8 * hy_8 : ℕ) : ℝ) / D_den = cR := by
      rw [cR_eq]; unfold hy_8 C_num; norm_num
    rw [hc_eq, intervalIntegral.integral_same]; simp
  obtain ⟨G0, hG0_ok, hBdry_0⟩ :=
    checkSJ8Go_sound (t0 := t0_b1) (x0 := 810770400) (h := h_16) (hy := hy_8)
      (err55 := err55_8) (err110 := err110_8) (s_sub := 2) (off7 := 0) (Nu := 55) (rem := 70)
      (by unfold B_num; omega) (by unfold C_num hy_8; omega) (by unfold hy_8; omega)
      (by unfold h_16 X_span_num C_num B_num; omega) (by unfold h_16; omega) (by unfold t0_b1; omega)
      (by omega) rfl rfl hS_end SJ_b1_g0_ok
  obtain ⟨_, hJsum_bd⟩ := checkJ1Sum_spec Jsum_b1_ok
  obtain ⟨hJW_len, hJW_bd⟩ := checkJWin4_spec JW_b1_ok
  have hJc_len : Jc_b1.length = 55 := by decide +kernel
  have hJ_bound : ∀ k < 55, ∀ u : ℝ,
      ((phi0_b1 - A1_num + k * h_16 : ℕ) : ℝ) / D_den ≤ u →
      u ≤ ((phi0_b1 - A1_num + (k + 1) * h_16 : ℕ) : ℝ) / D_den →
      J_real u ≤ (Jc_b1.getD k 0 : ℝ) / S_sc := by
    apply J_cert_sound_groups (u0 := phi0_b1 - A1_num) (ngrp := 1) (s_sub := 2)
      (h := h_16) (hy := hy_8) (Nu := 55)
      (Gs := [G0]) (Jgs := [Jg_b1_0]) (Kers := Kers_16) (J_cert := Jc_b1)
      (by omega) (by omega) (by unfold h_16; omega) (by unfold h_16; omega)
      (by unfold hy_8 h_16; omega) (by unfold hy_8 X_span_num C_num B_num; omega)
      (by unfold phi0_b1 A1_num C_num; omega) hJc_len rfl (by decide +kernel) Kers_16_ok
    · intro g hg
      rw [← ht0_eq, ← hnm_eq]
      interval_cases g
      · norm_num only; simpa only [Kers_16, List.getD_cons_zero, List.getD_cons_succ, show B_num + 0 * hy_8 = 810770400 by unfold B_num hy_8; omega] using hG0_ok
    · intro k hk
      have hrev := list_getD_reverse Jc_b1 k (by omega)
      rw [hJc_len] at hrev
      have hjs := hJsum_bd (55 - 1 - k) (by simp [hJc_len]; omega)
      rw [hrev] at hjs
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, List.getD_cons_zero, List.getD_cons_succ] using hjs
  exact conv_band_sound hω hz (phi0 := phi0_b1) (h := h_16) (mult := 4) (Nphi := 8)
    (N0 := 23) (Nu := 55) (W0 := W0_cert_16) (J_cert := Jc_b1) (J_win := Jw_b1)
    (by unfold h_16; omega) (by omega) (by omega)
    (by unfold phi0_b1 D_den; omega) (by unfold phi0_b1 h_16 D_den; omega)
    (by unfold A1_num A0_num h_16; omega) (by unfold A1_num A0_num h_16; omega)
    (by omega) W0_cert_16_ok hJc_len hJ_bound (by omega) hJW_bd Sl_b1_ok

private lemma band_b2_sound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∀ φ : ℝ, (phi0_b2 : ℝ) / D_den ≤ φ → φ ≤ ((4157409492 : ℕ) : ℝ) / D_den →
      buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
        ((70737 / 1000000000) : ℝ) := by
  have hphi1_eq : phi0_b2 + 13 * 1 * h_48 = 4157409492 := by unfold phi0_b2 h_48; omega
  rw [← hphi1_eq]
  have ht0_eq : t0_b2 = phi0_b2 - A1_num - C_num := by unfold t0_b2 phi0_b2 A1_num C_num; omega
  have hnm_eq : 127 = 80 + (8 * 2) * 3 - 1 := by omega
  have hS_end : ∀ idx < 127,
      ∫ x in (((854994240 + 8 * hy_16 : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0_b2 + idx * h_48 : ℕ) : ℝ) / D_den)
          (((t0_b2 + idx * h_48 + 2 * h_48 : ℕ) : ℝ) / D_den) x ≤
        (([] : List ℕ).getD (127 - 1 - idx) 0 : ℝ) / S_sc := by
    intro idx _
    have hc_eq : ((854994240 + 8 * hy_16 : ℕ) : ℝ) / D_den = cR := by
      rw [cR_eq]; unfold hy_16 C_num; norm_num
    rw [hc_eq, intervalIntegral.integral_same]; simp
  obtain ⟨G1, hG1_ok, hBdry_1⟩ :=
    checkSJ8Go_sound (t0 := t0_b2) (x0 := 854994240) (h := h_48) (hy := hy_16)
      (err55 := err55_16) (err110 := err110_16) (s_sub := 3) (off7 := 0) (Nu := 80) (rem := 127)
      (by unfold B_num; omega) (by unfold C_num hy_16; omega) (by unfold hy_16; omega)
      (by unfold h_48 X_span_num C_num B_num; omega) (by unfold h_48; omega) (by unfold t0_b2; omega)
      (by omega) rfl rfl hS_end SJ_b2_g1_ok
  obtain ⟨G0, hG0_ok, hBdry_0⟩ :=
    checkSJ8Go_sound (t0 := t0_b2) (x0 := 810770400) (h := h_48) (hy := hy_16)
      (err55 := err55_16) (err110 := err110_16) (s_sub := 3) (off7 := 24) (Nu := 80) (rem := 127)
      (by unfold B_num; omega) (by unfold C_num hy_16; omega) (by unfold hy_16; omega)
      (by unfold h_48 X_span_num C_num B_num; omega) (by unfold h_48; omega) (by unfold t0_b2; omega)
      (by omega) rfl rfl (fun idx hidx => by simpa only [show 810770400 + 8 * hy_16 = 854994240 by unfold hy_16; omega] using hBdry_1 rfl idx hidx) SJ_b2_g0_ok
  obtain ⟨_, _, hJsum_bd⟩ := checkJ2Sum_spec Jsum_b2_ok
  obtain ⟨hJW_len, hJW_bd⟩ := checkJWin1_spec JW_b2_ok
  have hJc_len : Jc_b2.length = 80 := by decide +kernel
  have hJ_bound : ∀ k < 80, ∀ u : ℝ,
      ((phi0_b2 - A1_num + k * h_48 : ℕ) : ℝ) / D_den ≤ u →
      u ≤ ((phi0_b2 - A1_num + (k + 1) * h_48 : ℕ) : ℝ) / D_den →
      J_real u ≤ (Jc_b2.getD k 0 : ℝ) / S_sc := by
    apply J_cert_sound_groups (u0 := phi0_b2 - A1_num) (ngrp := 2) (s_sub := 3)
      (h := h_48) (hy := hy_16) (Nu := 80)
      (Gs := [G0, G1]) (Jgs := [Jg_b2_0, Jg_b2_1]) (Kers := Kers_48) (J_cert := Jc_b2)
      (by omega) (by omega) (by unfold h_48; omega) (by unfold h_48; omega)
      (by unfold hy_16 h_48; omega) (by unfold hy_16 X_span_num C_num B_num; omega)
      (by unfold phi0_b2 A1_num C_num; omega) hJc_len rfl (by decide +kernel) Kers_48_ok
    · intro g hg
      rw [← ht0_eq, ← hnm_eq]
      interval_cases g
      · norm_num only; simpa only [Kers_48, List.getD_cons_zero, List.getD_cons_succ, show B_num + 0 * hy_16 = 810770400 by unfold B_num hy_16; omega] using hG0_ok
      · norm_num only; simpa only [Kers_48, List.getD_cons_zero, List.getD_cons_succ, show B_num + 8 * hy_16 = 854994240 by unfold B_num hy_16; omega] using hG1_ok
    · intro k hk
      have hrev := list_getD_reverse Jc_b2 k (by omega)
      rw [hJc_len] at hrev
      have hjs := hJsum_bd (80 - 1 - k) (by simp [hJc_len]; omega)
      rw [hrev] at hjs
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, List.getD_cons_zero, List.getD_cons_succ] using hjs
  exact conv_band_sound hω hz (phi0 := phi0_b2) (h := h_48) (mult := 1) (Nphi := 13)
    (N0 := 67) (Nu := 80) (W0 := W0_cert_48) (J_cert := Jc_b2) (J_win := Jw_b2)
    (by unfold h_48; omega) (by omega) (by omega)
    (by unfold phi0_b2 D_den; omega) (by unfold phi0_b2 h_48 D_den; omega)
    (by unfold A1_num A0_num h_48; omega) (by unfold A1_num A0_num h_48; omega)
    (by omega) W0_cert_48_ok hJc_len hJ_bound (by omega) hJW_bd Sl_b2_ok

private lemma band_b3_sound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∀ φ : ℝ, (phi0_b3 : ℝ) / D_den ≤ φ → φ ≤ ((4196719572 : ℕ) : ℝ) / D_den →
      buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
        ((70737 / 1000000000) : ℝ) := by
  have hphi1_eq : phi0_b3 + 128 * 1 * h_288 = 4196719572 := by unfold phi0_b3 h_288; omega
  rw [← hphi1_eq]
  have ht0_eq : t0_b3 = phi0_b3 - A1_num - C_num := by unfold t0_b3 phi0_b3 A1_num C_num; omega
  have hnm_eq : 812 = 525 + (8 * 6) * 6 - 1 := by omega
  have hS_end : ∀ idx < 812,
      ∫ x in (((884476800 + 8 * hy_48 : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0_b3 + idx * h_288 : ℕ) : ℝ) / D_den)
          (((t0_b3 + idx * h_288 + 2 * h_288 : ℕ) : ℝ) / D_den) x ≤
        (([] : List ℕ).getD (812 - 1 - idx) 0 : ℝ) / S_sc := by
    intro idx _
    have hc_eq : ((884476800 + 8 * hy_48 : ℕ) : ℝ) / D_den = cR := by
      rw [cR_eq]; unfold hy_48 C_num; norm_num
    rw [hc_eq, intervalIntegral.integral_same]; simp
  obtain ⟨G5, hG5_ok, hBdry_5⟩ :=
    checkSJ8Go_sound (t0 := t0_b3) (x0 := 884476800) (h := h_288) (hy := hy_48)
      (err55 := err55_48) (err110 := err110_48) (s_sub := 6) (off7 := 0) (Nu := 525) (rem := 812)
      (by unfold B_num; omega) (by unfold C_num hy_48; omega) (by unfold hy_48; omega)
      (by unfold h_288 X_span_num C_num B_num; omega) (by unfold h_288; omega) (by unfold t0_b3; omega)
      (by omega) rfl rfl hS_end SJ_b3_g5_ok
  obtain ⟨G4, hG4_ok, hBdry_4⟩ :=
    checkSJ8Go_sound (t0 := t0_b3) (x0 := 869735520) (h := h_288) (hy := hy_48)
      (err55 := err55_48) (err110 := err110_48) (s_sub := 6) (off7 := 48) (Nu := 525) (rem := 812)
      (by unfold B_num; omega) (by unfold C_num hy_48; omega) (by unfold hy_48; omega)
      (by unfold h_288 X_span_num C_num B_num; omega) (by unfold h_288; omega) (by unfold t0_b3; omega)
      (by omega) rfl rfl (fun idx hidx => by simpa only [show 869735520 + 8 * hy_48 = 884476800 by unfold hy_48; omega] using hBdry_5 rfl idx hidx) SJ_b3_g4_ok
  obtain ⟨G3, hG3_ok, hBdry_3⟩ :=
    checkSJ8Go_sound (t0 := t0_b3) (x0 := 854994240) (h := h_288) (hy := hy_48)
      (err55 := err55_48) (err110 := err110_48) (s_sub := 6) (off7 := 96) (Nu := 525) (rem := 812)
      (by unfold B_num; omega) (by unfold C_num hy_48; omega) (by unfold hy_48; omega)
      (by unfold h_288 X_span_num C_num B_num; omega) (by unfold h_288; omega) (by unfold t0_b3; omega)
      (by omega) rfl rfl (fun idx hidx => by simpa only [show 854994240 + 8 * hy_48 = 869735520 by unfold hy_48; omega] using hBdry_4 rfl idx hidx) SJ_b3_g3_ok
  obtain ⟨G2, hG2_ok, hBdry_2⟩ :=
    checkSJ8Go_sound (t0 := t0_b3) (x0 := 840252960) (h := h_288) (hy := hy_48)
      (err55 := err55_48) (err110 := err110_48) (s_sub := 6) (off7 := 144) (Nu := 525) (rem := 812)
      (by unfold B_num; omega) (by unfold C_num hy_48; omega) (by unfold hy_48; omega)
      (by unfold h_288 X_span_num C_num B_num; omega) (by unfold h_288; omega) (by unfold t0_b3; omega)
      (by omega) rfl rfl (fun idx hidx => by simpa only [show 840252960 + 8 * hy_48 = 854994240 by unfold hy_48; omega] using hBdry_3 rfl idx hidx) SJ_b3_g2_ok
  obtain ⟨G1, hG1_ok, hBdry_1⟩ :=
    checkSJ8Go_sound (t0 := t0_b3) (x0 := 825511680) (h := h_288) (hy := hy_48)
      (err55 := err55_48) (err110 := err110_48) (s_sub := 6) (off7 := 192) (Nu := 525) (rem := 812)
      (by unfold B_num; omega) (by unfold C_num hy_48; omega) (by unfold hy_48; omega)
      (by unfold h_288 X_span_num C_num B_num; omega) (by unfold h_288; omega) (by unfold t0_b3; omega)
      (by omega) rfl rfl (fun idx hidx => by simpa only [show 825511680 + 8 * hy_48 = 840252960 by unfold hy_48; omega] using hBdry_2 rfl idx hidx) SJ_b3_g1_ok
  obtain ⟨G0, hG0_ok, hBdry_0⟩ :=
    checkSJ8Go_sound (t0 := t0_b3) (x0 := 810770400) (h := h_288) (hy := hy_48)
      (err55 := err55_48) (err110 := err110_48) (s_sub := 6) (off7 := 240) (Nu := 525) (rem := 812)
      (by unfold B_num; omega) (by unfold C_num hy_48; omega) (by unfold hy_48; omega)
      (by unfold h_288 X_span_num C_num B_num; omega) (by unfold h_288; omega) (by unfold t0_b3; omega)
      (by omega) rfl rfl (fun idx hidx => by simpa only [show 810770400 + 8 * hy_48 = 825511680 by unfold hy_48; omega] using hBdry_1 rfl idx hidx) SJ_b3_g0_ok
  obtain ⟨_, _, _, _, _, _, hJsum_bd⟩ := checkJ6Sum_spec Jsum_b3_ok
  obtain ⟨hJW_len, hJW_bd⟩ := checkJWin1_spec JW_b3_ok
  have hJc_len : Jc_b3.length = 525 := by decide +kernel
  have hJ_bound : ∀ k < 525, ∀ u : ℝ,
      ((phi0_b3 - A1_num + k * h_288 : ℕ) : ℝ) / D_den ≤ u →
      u ≤ ((phi0_b3 - A1_num + (k + 1) * h_288 : ℕ) : ℝ) / D_den →
      J_real u ≤ (Jc_b3.getD k 0 : ℝ) / S_sc := by
    apply J_cert_sound_groups (u0 := phi0_b3 - A1_num) (ngrp := 6) (s_sub := 6)
      (h := h_288) (hy := hy_48) (Nu := 525)
      (Gs := [G0, G1, G2, G3, G4, G5]) (Jgs := [Jg_b3_0, Jg_b3_1, Jg_b3_2, Jg_b3_3, Jg_b3_4, Jg_b3_5]) (Kers := Kers_288) (J_cert := Jc_b3)
      (by omega) (by omega) (by unfold h_288; omega) (by unfold h_288; omega)
      (by unfold hy_48 h_288; omega) (by unfold hy_48 X_span_num C_num B_num; omega)
      (by unfold phi0_b3 A1_num C_num; omega) hJc_len rfl (by decide +kernel) Kers_288_ok
    · intro g hg
      rw [← ht0_eq, ← hnm_eq]
      interval_cases g
      · norm_num only; simpa only [Kers_288, List.getD_cons_zero, List.getD_cons_succ, show B_num + 0 * hy_48 = 810770400 by unfold B_num hy_48; omega] using hG0_ok
      · norm_num only; simpa only [Kers_288, List.getD_cons_zero, List.getD_cons_succ, show B_num + 8 * hy_48 = 825511680 by unfold B_num hy_48; omega] using hG1_ok
      · norm_num only; simpa only [Kers_288, List.getD_cons_zero, List.getD_cons_succ, show B_num + 16 * hy_48 = 840252960 by unfold B_num hy_48; omega] using hG2_ok
      · norm_num only; simpa only [Kers_288, List.getD_cons_zero, List.getD_cons_succ, show B_num + 24 * hy_48 = 854994240 by unfold B_num hy_48; omega] using hG3_ok
      · norm_num only; simpa only [Kers_288, List.getD_cons_zero, List.getD_cons_succ, show B_num + 32 * hy_48 = 869735520 by unfold B_num hy_48; omega] using hG4_ok
      · norm_num only; simpa only [Kers_288, List.getD_cons_zero, List.getD_cons_succ, show B_num + 40 * hy_48 = 884476800 by unfold B_num hy_48; omega] using hG5_ok
    · intro k hk
      have hrev := list_getD_reverse Jc_b3 k (by omega)
      rw [hJc_len] at hrev
      have hjs := hJsum_bd (525 - 1 - k) (by simp [hJc_len]; omega)
      rw [hrev] at hjs
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, List.getD_cons_zero, List.getD_cons_succ] using hjs
  exact conv_band_sound hω hz (phi0 := phi0_b3) (h := h_288) (mult := 1) (Nphi := 128)
    (N0 := 397) (Nu := 525) (W0 := W0_cert_288) (J_cert := Jc_b3) (J_win := Jw_b3)
    (by unfold h_288; omega) (by omega) (by omega)
    (by unfold phi0_b3 D_den; omega) (by unfold phi0_b3 h_288 D_den; omega)
    (by unfold A1_num A0_num h_288; omega) (by unfold A1_num A0_num h_288; omega)
    (by omega) W0_cert_288_ok hJc_len hJ_bound (by omega) hJW_bd Sl_b3_ok

private lemma band_b4_sound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∀ φ : ℝ, (phi0_b4 : ℝ) / D_den ≤ φ → φ ≤ ((4239100752 : ℕ) : ℝ) / D_den →
      buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
        ((70737 / 1000000000) : ℝ) := by
  have hphi1_eq : phi0_b4 + 23 * 1 * h_48 = 4239100752 := by unfold phi0_b4 h_48; omega
  rw [← hphi1_eq]
  have ht0_eq : t0_b4 = phi0_b4 - A1_num - C_num := by unfold t0_b4 phi0_b4 A1_num C_num; omega
  have hnm_eq : 137 = 90 + (8 * 2) * 3 - 1 := by omega
  have hS_end : ∀ idx < 137,
      ∫ x in (((854994240 + 8 * hy_16 : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0_b4 + idx * h_48 : ℕ) : ℝ) / D_den)
          (((t0_b4 + idx * h_48 + 2 * h_48 : ℕ) : ℝ) / D_den) x ≤
        (([] : List ℕ).getD (137 - 1 - idx) 0 : ℝ) / S_sc := by
    intro idx _
    have hc_eq : ((854994240 + 8 * hy_16 : ℕ) : ℝ) / D_den = cR := by
      rw [cR_eq]; unfold hy_16 C_num; norm_num
    rw [hc_eq, intervalIntegral.integral_same]; simp
  obtain ⟨G1, hG1_ok, hBdry_1⟩ :=
    checkSJ8Go_sound (t0 := t0_b4) (x0 := 854994240) (h := h_48) (hy := hy_16)
      (err55 := err55_16) (err110 := err110_16) (s_sub := 3) (off7 := 0) (Nu := 90) (rem := 137)
      (by unfold B_num; omega) (by unfold C_num hy_16; omega) (by unfold hy_16; omega)
      (by unfold h_48 X_span_num C_num B_num; omega) (by unfold h_48; omega) (by unfold t0_b4; omega)
      (by omega) rfl rfl hS_end SJ_b4_g1_ok
  obtain ⟨G0, hG0_ok, hBdry_0⟩ :=
    checkSJ8Go_sound (t0 := t0_b4) (x0 := 810770400) (h := h_48) (hy := hy_16)
      (err55 := err55_16) (err110 := err110_16) (s_sub := 3) (off7 := 24) (Nu := 90) (rem := 137)
      (by unfold B_num; omega) (by unfold C_num hy_16; omega) (by unfold hy_16; omega)
      (by unfold h_48 X_span_num C_num B_num; omega) (by unfold h_48; omega) (by unfold t0_b4; omega)
      (by omega) rfl rfl (fun idx hidx => by simpa only [show 810770400 + 8 * hy_16 = 854994240 by unfold hy_16; omega] using hBdry_1 rfl idx hidx) SJ_b4_g0_ok
  obtain ⟨_, _, hJsum_bd⟩ := checkJ2Sum_spec Jsum_b4_ok
  obtain ⟨hJW_len, hJW_bd⟩ := checkJWin1_spec JW_b4_ok
  have hJc_len : Jc_b4.length = 90 := by decide +kernel
  have hJ_bound : ∀ k < 90, ∀ u : ℝ,
      ((phi0_b4 - A1_num + k * h_48 : ℕ) : ℝ) / D_den ≤ u →
      u ≤ ((phi0_b4 - A1_num + (k + 1) * h_48 : ℕ) : ℝ) / D_den →
      J_real u ≤ (Jc_b4.getD k 0 : ℝ) / S_sc := by
    apply J_cert_sound_groups (u0 := phi0_b4 - A1_num) (ngrp := 2) (s_sub := 3)
      (h := h_48) (hy := hy_16) (Nu := 90)
      (Gs := [G0, G1]) (Jgs := [Jg_b4_0, Jg_b4_1]) (Kers := Kers_48) (J_cert := Jc_b4)
      (by omega) (by omega) (by unfold h_48; omega) (by unfold h_48; omega)
      (by unfold hy_16 h_48; omega) (by unfold hy_16 X_span_num C_num B_num; omega)
      (by unfold phi0_b4 A1_num C_num; omega) hJc_len rfl (by decide +kernel) Kers_48_ok
    · intro g hg
      rw [← ht0_eq, ← hnm_eq]
      interval_cases g
      · norm_num only; simpa only [Kers_48, List.getD_cons_zero, List.getD_cons_succ, show B_num + 0 * hy_16 = 810770400 by unfold B_num hy_16; omega] using hG0_ok
      · norm_num only; simpa only [Kers_48, List.getD_cons_zero, List.getD_cons_succ, show B_num + 8 * hy_16 = 854994240 by unfold B_num hy_16; omega] using hG1_ok
    · intro k hk
      have hrev := list_getD_reverse Jc_b4 k (by omega)
      rw [hJc_len] at hrev
      have hjs := hJsum_bd (90 - 1 - k) (by simp [hJc_len]; omega)
      rw [hrev] at hjs
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, List.getD_cons_zero, List.getD_cons_succ] using hjs
  exact conv_band_sound hω hz (phi0 := phi0_b4) (h := h_48) (mult := 1) (Nphi := 23)
    (N0 := 67) (Nu := 90) (W0 := W0_cert_48) (J_cert := Jc_b4) (J_win := Jw_b4)
    (by unfold h_48; omega) (by omega) (by omega)
    (by unfold phi0_b4 D_den; omega) (by unfold phi0_b4 h_48 D_den; omega)
    (by unfold A1_num A0_num h_48; omega) (by unfold A1_num A0_num h_48; omega)
    (by omega) W0_cert_48_ok hJc_len hJ_bound (by omega) hJW_bd Sl_b4_ok

private lemma band_b5_sound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∀ φ : ℝ, (phi0_b5 : ℝ) / D_den ≤ φ → φ ≤ ((4526555712 : ℕ) : ℝ) / D_den →
      buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
        ((70737 / 1000000000) : ℝ) := by
  have hphi1_eq : phi0_b5 + 13 * 4 * h_16 = 4526555712 := by unfold phi0_b5 h_16; omega
  rw [← hphi1_eq]
  have ht0_eq : t0_b5 = phi0_b5 - A1_num - C_num := by unfold t0_b5 phi0_b5 A1_num C_num; omega
  have hnm_eq : 90 = 75 + (8 * 1) * 2 - 1 := by omega
  have hS_end : ∀ idx < 90,
      ∫ x in (((810770400 + 8 * hy_8 : ℕ) : ℝ) / D_den)..cR,
        gm_real (((t0_b5 + idx * h_16 : ℕ) : ℝ) / D_den)
          (((t0_b5 + idx * h_16 + 2 * h_16 : ℕ) : ℝ) / D_den) x ≤
        (([] : List ℕ).getD (90 - 1 - idx) 0 : ℝ) / S_sc := by
    intro idx _
    have hc_eq : ((810770400 + 8 * hy_8 : ℕ) : ℝ) / D_den = cR := by
      rw [cR_eq]; unfold hy_8 C_num; norm_num
    rw [hc_eq, intervalIntegral.integral_same]; simp
  obtain ⟨G0, hG0_ok, hBdry_0⟩ :=
    checkSJ8Go_sound (t0 := t0_b5) (x0 := 810770400) (h := h_16) (hy := hy_8)
      (err55 := err55_8) (err110 := err110_8) (s_sub := 2) (off7 := 0) (Nu := 75) (rem := 90)
      (by unfold B_num; omega) (by unfold C_num hy_8; omega) (by unfold hy_8; omega)
      (by unfold h_16 X_span_num C_num B_num; omega) (by unfold h_16; omega) (by unfold t0_b5; omega)
      (by omega) rfl rfl hS_end SJ_b5_g0_ok
  obtain ⟨_, hJsum_bd⟩ := checkJ1Sum_spec Jsum_b5_ok
  obtain ⟨hJW_len, hJW_bd⟩ := checkJWin4_spec JW_b5_ok
  have hJc_len : Jc_b5.length = 75 := by decide +kernel
  have hJ_bound : ∀ k < 75, ∀ u : ℝ,
      ((phi0_b5 - A1_num + k * h_16 : ℕ) : ℝ) / D_den ≤ u →
      u ≤ ((phi0_b5 - A1_num + (k + 1) * h_16 : ℕ) : ℝ) / D_den →
      J_real u ≤ (Jc_b5.getD k 0 : ℝ) / S_sc := by
    apply J_cert_sound_groups (u0 := phi0_b5 - A1_num) (ngrp := 1) (s_sub := 2)
      (h := h_16) (hy := hy_8) (Nu := 75)
      (Gs := [G0]) (Jgs := [Jg_b5_0]) (Kers := Kers_16) (J_cert := Jc_b5)
      (by omega) (by omega) (by unfold h_16; omega) (by unfold h_16; omega)
      (by unfold hy_8 h_16; omega) (by unfold hy_8 X_span_num C_num B_num; omega)
      (by unfold phi0_b5 A1_num C_num; omega) hJc_len rfl (by decide +kernel) Kers_16_ok
    · intro g hg
      rw [← ht0_eq, ← hnm_eq]
      interval_cases g
      · norm_num only; simpa only [Kers_16, List.getD_cons_zero, List.getD_cons_succ, show B_num + 0 * hy_8 = 810770400 by unfold B_num hy_8; omega] using hG0_ok
    · intro k hk
      have hrev := list_getD_reverse Jc_b5 k (by omega)
      rw [hJc_len] at hrev
      have hjs := hJsum_bd (75 - 1 - k) (by simp [hJc_len]; omega)
      rw [hrev] at hjs
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, List.getD_cons_zero, List.getD_cons_succ] using hjs
  exact conv_band_sound hω hz (phi0 := phi0_b5) (h := h_16) (mult := 4) (Nphi := 13)
    (N0 := 23) (Nu := 75) (W0 := W0_cert_16) (J_cert := Jc_b5) (J_win := Jw_b5)
    (by unfold h_16; omega) (by omega) (by omega)
    (by unfold phi0_b5 D_den; omega) (by unfold phi0_b5 h_16 D_den; omega)
    (by unfold A1_num A0_num h_16; omega) (by unfold A1_num A0_num h_16; omega)
    (by omega) W0_cert_16_ok hJc_len hJ_bound (by omega) hJW_bd Sl_b5_ok


private lemma r0j19_main_bound {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ2 : 2 ≤ φ) (hφhi : φ ≤ (228 / 100 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
      ((70737 / 1000000000) : ℝ) := by
  have hD : (0 : ℝ) < D_den := by unfold D_den; norm_num
  have h_start : (phi0_b1 : ℝ) / D_den = 2 := by unfold phi0_b1 D_den; norm_num
  have h_end : (228 / 100 : ℝ) ≤ ((4526555712 : ℕ) : ℝ) / D_den := by unfold D_den; norm_num
  by_cases h1 : φ ≤ ((4133454912 : ℕ) : ℝ) / D_den
  · exact band_b1_sound hω hz φ (by linarith) h1
  · by_cases h2 : φ ≤ ((4157409492 : ℕ) : ℝ) / D_den
    · exact band_b2_sound hω hz φ (by unfold phi0_b2; linarith) h2
    · by_cases h3 : φ ≤ ((4196719572 : ℕ) : ℝ) / D_den
      · exact band_b3_sound hω hz φ (by unfold phi0_b3; linarith) h3
      · by_cases h4 : φ ≤ ((4239100752 : ℕ) : ℝ) / D_den
        · exact band_b4_sound hω hz φ (by unfold phi0_b4; linarith) h4
        · exact band_b5_sound hω hz φ (by unfold phi0_b5; linarith) (le_trans hφhi h_end)

lemma r0j19_short_proved {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
      ((70737 / 1000000000) : ℝ) := by
  by_cases hmid : φ ≤ (228 / 100 : ℝ)
  · exact r0j19_main_bound hω hz hφ hmid
  · exact r0j19_tail_bound hω hz (le_of_lt (not_le.mp hmid)) hφtop

end SolBuchstab4D_r0j19

theorem solution {ω : ℝ → ℝ} (hω : LL_Decomp587l.IsBuchstab ω) (hz : LL_Decomp587l.ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    LL_Decomp587l.buchstabIntegral ω 2 (fun j => (LL_Decomp587l.r0j19_lo j : ℝ))
      (fun j => (LL_Decomp587l.r0j19_hi j : ℝ)) φ ≤ ((70737 / 1000000000) : ℝ) :=
  SolBuchstab4D_r0j19.r0j19_short_proved hω hz hφ hφtop
