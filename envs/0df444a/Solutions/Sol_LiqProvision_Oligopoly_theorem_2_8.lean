-- Prove2me | solution 1 for LiqProvision.Oligopoly.theorem_2_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:53:14.36023+00:00
-- url     : https://prove2.me/submissions/a07a4e10-8843-4f03-b682-4ecbbc912f8f

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model
import Theorems.Thm_LiqProvision_Oligopoly_lemma_2_5_a

open Set Filter Topology
open LiqProvision.Oligopoly

namespace LiqT28Aux

theorem diffAt {P : ℝ → ℝ} (hP : IsPriceSchedule P) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ P x :=
  (hP.2.2.differentiableOn (by norm_num) x hx).differentiableAt
    (isOpen_compl_singleton.mem_nhds hx)

theorem deriv_lt {P : ℝ → ℝ} (hP : IsPriceSchedule P) (hsc : StrictConvexOn ℝ univ P)
    {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x < y) : deriv P x < deriv P y :=
  (hsc.deriv_lt_slope (mem_univ _) (mem_univ _) hxy (diffAt hP hx)).trans
    (hsc.slope_lt_deriv (mem_univ _) (mem_univ _) hxy (diffAt hP hy))

/-- chord slope is below the derivative at any nonzero point further right -/
theorem chord_lt_deriv {P : ℝ → ℝ} (hP : IsPriceSchedule P) (hsc : StrictConvexOn ℝ univ P)
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (hc : c ≠ 0) :
    P b - P a < (b - a) * deriv P c := by
  have h1 := hsc.slope_strict_mono_adjacent (mem_univ a) (mem_univ c) hab hbc
  have h2 := hsc.slope_lt_deriv (mem_univ b) (mem_univ c) hbc (diffAt hP hc)
  rw [slope_def_field] at h2
  have h3 : (P b - P a) / (b - a) < deriv P c := h1.trans h2
  rwa [div_lt_iff₀ (by linarith), mul_comm] at h3

theorem deriv_lt_chord {P : ℝ → ℝ} (hP : IsPriceSchedule P) (hsc : StrictConvexOn ℝ univ P)
    {a b c : ℝ} (hca : c < a) (hab : a < b) (hc : c ≠ 0) :
    (b - a) * deriv P c < P b - P a := by
  have h1 := hsc.slope_strict_mono_adjacent (mem_univ c) (mem_univ b) hca hab
  have h2 := hsc.deriv_lt_slope (mem_univ c) (mem_univ a) hca (diffAt hP hc)
  rw [slope_def_field] at h2
  have h3 : deriv P c < (P b - P a) / (b - a) := h2.trans h1
  rwa [lt_div_iff₀ (by linarith), mul_comm] at h3

theorem lim_le {P : ℝ → ℝ} (hP : IsPriceSchedule P) (hsc : StrictConvexOn ℝ univ P)
    {ℓ : EReal} (hℓ : Tendsto (fun n => ((deriv P n : ℝ) : EReal)) atBot (𝓝 ℓ))
    {x : ℝ} (hx : x ≠ 0) : ℓ ≤ ((deriv P x : ℝ) : EReal) := by
  apply le_of_tendsto hℓ
  filter_upwards [eventually_lt_atBot (min x 0)] with z hz
  have hz0 : z ≠ 0 := by intro h; subst h; exact absurd hz (by simp)
  exact_mod_cast (deriv_lt hP hsc hz0 hx (lt_of_lt_of_le hz (min_le_left _ _))).le

theorem le_lim {P : ℝ → ℝ} (hP : IsPriceSchedule P) (hsc : StrictConvexOn ℝ univ P)
    {r : EReal} (hr : Tendsto (fun n => ((deriv P n : ℝ) : EReal)) atTop (𝓝 r))
    {x : ℝ} (hx : x ≠ 0) : ((deriv P x : ℝ) : EReal) ≤ r := by
  apply ge_of_tendsto hr
  filter_upwards [eventually_gt_atTop (max x 0)] with z hz
  have hz0 : z ≠ 0 := by intro h; subst h; exact absurd hz (by simp)
  exact_mod_cast (deriv_lt hP hsc hx hz0 (lt_of_le_of_lt (le_max_left _ _) hz)).le

/-- linear growth with slopes separated from `s` -/
theorem growth {P : ℝ → ℝ} (hP : IsPriceSchedule P) {ℓ r : EReal}
    (hℓ : Tendsto (fun n => ((deriv P n : ℝ) : EReal)) atBot (𝓝 ℓ))
    (hr : Tendsto (fun n => ((deriv P n : ℝ) : EReal)) atTop (𝓝 r))
    {s₂ s s₁ : ℝ} (h2 : ℓ < s₂) (h1 : (s₁ : EReal) < r) (hs2 : s₂ < s) (hs1 : s < s₁) :
    ∃ C, ∀ x, s * x + min (s₁ - s) (s - s₂) * |x| - C ≤ P x := by
  set δ := min (s₁ - s) (s - s₂) with hδ
  have hδ1 : δ ≤ s₁ - s := min_le_left _ _
  have hδ2 : δ ≤ s - s₂ := min_le_right _ _
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  obtain ⟨A₁', hA₁'⟩ := eventually_atTop.1 (hr.eventually (lt_mem_nhds h1))
  obtain ⟨A₂', hA₂'⟩ := eventually_atBot.1 (hℓ.eventually (gt_mem_nhds h2))
  set A₁ := max A₁' 1
  set A₂ := min A₂' (-1)
  have hA₁ : ∀ x, A₁ ≤ x → s₁ < deriv P x := fun x hx =>
    by exact_mod_cast hA₁' x ((le_max_left _ _).trans hx)
  have hA₂ : ∀ x, x ≤ A₂ → deriv P x < s₂ := fun x hx =>
    by exact_mod_cast hA₂' x (hx.trans (min_le_left _ _))
  have hA₁pos : 1 ≤ A₁ := le_max_right _ _
  have hA₂neg : A₂ ≤ -1 := min_le_right _ _
  have hPc := hP.1
  have hup : ∀ x, A₁ ≤ x → P A₁ + s₁ * (x - A₁) ≤ P x := by
    intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope P hx hPc.continuousOn
        (fun z hz => (diffAt hP (by linarith [hz.1] : z ≠ 0)).differentiableWithinAt)
      have := hA₁ c hc.1.le
      rw [hcd, lt_div_iff₀ (by linarith)] at this
      linarith
    · simp
  have hlow : ∀ x, x ≤ A₂ → P A₂ - s₂ * (A₂ - x) ≤ P x := by
    intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope P hx hPc.continuousOn
        (fun z hz => (diffAt hP (by linarith [hz.2] : z ≠ 0)).differentiableWithinAt)
      have := hA₂ c hc.2.le
      rw [hcd, div_lt_iff₀ (by linarith)] at this
      linarith
    · simp
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := A₂) (b := A₁)).exists_bound_of_continuousOn
    hPc.continuousOn
  refine ⟨|P A₁| + |s₁ * A₁| + |P A₂| + |s₂ * A₂| + |B| + (|s| + δ) * (|A₁| + |A₂|),
    fun x => ?_⟩
  have hpos : 0 ≤ (|s| + δ) * (|A₁| + |A₂|) := by positivity
  have e1 := le_abs_self (P A₁); have e1' := neg_abs_le (P A₁)
  have e2 := le_abs_self (s₁ * A₁); have e2' := neg_abs_le (s₁ * A₁)
  have e3 := le_abs_self (P A₂); have e3' := neg_abs_le (P A₂)
  have e4 := le_abs_self (s₂ * A₂); have e4' := neg_abs_le (s₂ * A₂)
  have e5 := le_abs_self B
  have e6 := abs_nonneg (P A₁); have e7 := abs_nonneg (s₁ * A₁)
  have e8 := abs_nonneg (P A₂); have e9 := abs_nonneg (s₂ * A₂)
  have e10 := abs_nonneg B
  by_cases hx1 : A₁ ≤ x
  · have hx0 : 0 ≤ x := by linarith
    rw [abs_of_nonneg hx0]
    have := hup x hx1
    have : (s + δ) * x ≤ s₁ * x := mul_le_mul_of_nonneg_right (by linarith) hx0
    nlinarith
  by_cases hx2 : x ≤ A₂
  · have hx0 : x ≤ 0 := by linarith
    rw [abs_of_nonpos hx0]
    have := hlow x hx2
    have : (s - δ) * x ≤ s₂ * x := mul_le_mul_of_nonpos_right (by linarith) hx0
    nlinarith
  push Not at hx1 hx2
  have hbx := hB x ⟨hx2.le, hx1.le⟩
  rw [Real.norm_eq_abs] at hbx
  have hPx : -|B| ≤ P x := by linarith [neg_abs_le (P x), le_abs_self B]
  have habs : |x| ≤ |A₁| + |A₂| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self A₁, abs_nonneg A₂]
    · rw [abs_of_nonpos h]; linarith [neg_abs_le A₂, abs_nonneg A₁]
  have hsx : s * x ≤ |s| * |x| := by rw [← abs_mul]; exact le_abs_self _
  have : (|s| + δ) * |x| ≤ (|s| + δ) * (|A₁| + |A₂|) :=
    mul_le_mul_of_nonneg_left habs (by positivity)
  nlinarith

theorem obj_diff (M : Params) (Q : Fin M.K → ℝ → ℝ) (y : ℝ) (n n' : Fin M.K → ℝ) :
    clientObj M Q y n' - clientObj M Q y n =
      y * (∑ k, n' k - ∑ k, n k) - (∑ k, (Q k (n' k) - Q k (n k))) -
        M.γc / 2 * ((∑ k, n' k) ^ 2 - (∑ k, n k) ^ 2) := by
  simp only [clientObj, Finset.sum_sub_distrib]; ring

/-- necessity of `ℓ_j < r_i` -/
theorem nec (M : Params) (Q : Fin M.K → ℝ → ℝ)
    (hQ : ∀ k, IsPriceSchedule (Q k) ∧ StrictConvexOn ℝ univ (Q k)) (ℓ r : Fin M.K → EReal)
    (hℓ : ∀ k, Tendsto (fun n => ((deriv (Q k) n : ℝ) : EReal)) atBot (𝓝 (ℓ k)))
    (hr : ∀ k, Tendsto (fun n => ((deriv (Q k) n : ℝ) : EReal)) atTop (𝓝 (r k)))
    (y : ℝ) (n : Fin M.K → ℝ) (hn : IsClientMax M Q y n) : ∀ i j, ℓ j < r i := by
  intro i j
  by_contra hcon
  push Not at hcon
  by_cases hij : i = j
  · subst hij
    have h1 := lim_le (hQ i).1 (hQ i).2 (hℓ i) (by norm_num : (-1:ℝ) ≠ 0)
    have h2 := le_lim (hQ i).1 (hQ i).2 (hr i) (by norm_num : (1:ℝ) ≠ 0)
    have h3 : ((deriv (Q i) (-1) : ℝ) : EReal) < ((deriv (Q i) 1 : ℝ) : EReal) := by
      exact_mod_cast deriv_lt (hQ i).1 (hQ i).2 (by norm_num) (by norm_num) (by norm_num)
    exact absurd (h1.trans_lt (h3.trans_le h2)) (not_lt.2 hcon)
  · set a := n i
    set b := n j
    set c₁ : ℝ := max (a + 1) 0 + 1
    set c₂ : ℝ := min (b - 1) 0 - 1
    have hc₁ : a + 1 < c₁ := by have := le_max_left (a + 1) 0; linarith
    have hc₁0 : c₁ ≠ 0 := by have := le_max_right (a + 1) 0; intro h; linarith
    have hc₂ : c₂ < b - 1 := by have := min_le_left (b - 1) 0; linarith
    have hc₂0 : c₂ ≠ 0 := by have := min_le_right (b - 1) 0; intro h; linarith
    have hA := chord_lt_deriv (hQ i).1 (hQ i).2 (by linarith : a < a + 1) hc₁ hc₁0
    have hB := deriv_lt_chord (hQ j).1 (hQ j).2 hc₂ (by linarith : b - 1 < b) hc₂0
    have hle : deriv (Q i) c₁ ≤ deriv (Q j) c₂ := by
      have := ((le_lim (hQ i).1 (hQ i).2 (hr i) hc₁0).trans hcon).trans
        (lim_le (hQ j).1 (hQ j).2 (hℓ j) hc₂0)
      exact_mod_cast this
    set n' : Fin M.K → ℝ := fun k => if k = i then a + 1 else if k = j then b - 1 else n k
      with hn'
    have hd : ∑ k, (n' k - n k) = 0 := by
      rw [Fintype.sum_eq_add i j hij]
      · simp [hn', Ne.symm hij, a, b]
      · rintro k ⟨hk0, hk1⟩; simp [hn', hk0, hk1]
    have hdP : ∑ k, (Q k (n' k) - Q k (n k)) =
        (Q i (a + 1) - Q i a) + (Q j (b - 1) - Q j b) := by
      rw [Fintype.sum_eq_add i j hij]
      · simp [hn', Ne.symm hij, a, b]
      · rintro k ⟨hk0, hk1⟩; simp [hn', hk0, hk1]
    rw [Finset.sum_sub_distrib] at hd
    have hdiff := obj_diff M Q y n n'
    rw [hdP] at hdiff
    have e : ∑ k, n' k = ∑ k, n k := by linarith
    rw [e] at hdiff
    have := hn n'
    simp only [sub_self, mul_zero, sub_zero] at hdiff
    norm_num at hA hB
    nlinarith

/-- coercivity gives existence of a maximizer -/
theorem exist (M : Params) (hγc : 0 < M.γc) (Q : Fin M.K → ℝ → ℝ)
    (hQ : ∀ k, IsPriceSchedule (Q k)) (s δ : ℝ) (hδ : 0 < δ) (C : Fin M.K → ℝ)
    (hC : ∀ k x, s * x + δ * |x| - C k ≤ Q k x) (y : ℝ) : ∃ n, IsClientMax M Q y n := by
  set Φ := clientObj M Q y with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ]; unfold clientObj
    have : ∀ k, Continuous (Q k) := fun k => (hQ k).1
    fun_prop
  set C₀ : ℝ := (y - s) ^ 2 / (2 * M.γc) + ∑ k, C k with hC₀
  have hbound : ∀ n : Fin M.K → ℝ, Φ n ≤ C₀ - δ * ∑ k, |n k| := by
    intro n
    have hsumP : s * ∑ k, n k + δ * ∑ k, |n k| - ∑ k, C k ≤ ∑ k, Q k (n k) := by
      have := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hC k (n k))
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at this
      linarith
    have hq : (y - s) * ∑ k, n k - M.γc / 2 * (∑ k, n k) ^ 2 ≤ (y - s) ^ 2 / (2 * M.γc) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (M.γc * ∑ k, n k - (y - s))]
    simp only [hΦ, clientObj, hC₀]
    nlinarith
  set T := {n : Fin M.K → ℝ | Φ 0 ≤ Φ n} with hT
  have hTc : IsCompact T := by
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_const hΦc)
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨(C₀ - Φ 0) / δ, fun n hn => ?_⟩
    have hb := hbound n
    have hn' : Φ 0 ≤ Φ n := hn
    have hs : ∑ k, |n k| ≤ (C₀ - Φ 0) / δ := by
      rw [le_div_iff₀ hδ]; linarith
    have hs0 : 0 ≤ ∑ k, |n k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (hs0.trans hs)]
    intro k
    rw [Real.norm_eq_abs]
    exact (Finset.single_le_sum (f := fun k => |n k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ k)).trans hs
  obtain ⟨n0, hn0T, hn0⟩ := hTc.exists_isMaxOn ⟨0, show Φ 0 ≤ Φ 0 from le_refl _⟩
    hΦc.continuousOn
  refine ⟨n0, fun n' => ?_⟩
  by_cases h : n' ∈ T
  · exact hn0 h
  · have h' : Φ n' < Φ 0 := lt_of_not_ge h
    have : Φ 0 ≤ Φ n0 := hn0T
    show Φ n' ≤ Φ n0
    linarith

theorem uniq (M : Params) (Q : Fin M.K → ℝ → ℝ)
    (hsc : ∀ k, StrictConvexOn ℝ univ (Q k)) (y : ℝ) (n₁ n₂ : Fin M.K → ℝ)
    (h₁ : IsClientMax M Q y n₁) (h₂ : IsClientMax M Q y n₂) (hγc : 0 < M.γc) : n₁ = n₂ := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, n₁ k ≠ n₂ k := by
    by_contra h; push Not at h; exact hne (funext h)
  set mid : Fin M.K → ℝ := fun j => (n₁ j + n₂ j) / 2 with hmid
  have hmidP : ∀ j, Q j (mid j) ≤ (Q j (n₁ j) + Q j (n₂ j)) / 2 := by
    intro j
    have := (hsc j).convexOn.2 (mem_univ (n₁ j)) (mem_univ (n₂ j)) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e : (n₁ j + n₂ j) / 2 = 1 / 2 * n₁ j + 1 / 2 * n₂ j := by ring
    simp only [hmid, e]; linarith
  have hmidPk : Q k (mid k) < (Q k (n₁ k) + Q k (n₂ k)) / 2 := by
    have := (hsc k).2 (mem_univ (n₁ k)) (mem_univ (n₂ k)) hk (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e : (n₁ k + n₂ k) / 2 = 1 / 2 * n₁ k + 1 / 2 * n₂ k := by ring
    simp only [hmid, e]; linarith
  have hsumlt : ∑ j, Q j (mid j) < ∑ j, (Q j (n₁ j) + Q j (n₂ j)) / 2 :=
    Finset.sum_lt_sum (fun j _ => hmidP j) ⟨k, Finset.mem_univ _, hmidPk⟩
  have hsplit : ∑ j, (Q j (n₁ j) + Q j (n₂ j)) / 2 =
      (∑ j, Q j (n₁ j) + ∑ j, Q j (n₂ j)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hsm : ∑ j, mid j = (∑ j, n₁ j + ∑ j, n₂ j) / 2 := by
    simp only [hmid]; rw [← Finset.sum_div, Finset.sum_add_distrib]
  have e1 := h₁ mid
  have e3 := h₁ n₂
  have e4 := h₂ n₁
  simp only [clientObj] at e1 e3 e4
  rw [hsm] at e1
  nlinarith [sq_nonneg (∑ j, n₁ j - ∑ j, n₂ j)]

/-- coordinatewise optimality: `n k` minimizes `Q k m - λ m` with `λ = y - γc S`. -/
theorem coord_opt (M : Params) (Q : Fin M.K → ℝ → ℝ)
    (hsc : ∀ k, StrictConvexOn ℝ univ (Q k)) (hγc : 0 < M.γc) (y : ℝ) (n : Fin M.K → ℝ)
    (hn : IsClientMax M Q y n) (k : Fin M.K) (m : ℝ) :
    Q k (n k) - (y - M.γc * ∑ j, n j) * n k ≤ Q k m - (y - M.γc * ∑ j, n j) * m := by
  set lam := y - M.γc * ∑ j, n j with hlam
  by_contra hcon
  push Not at hcon
  set D := (Q k (n k) - lam * n k) - (Q k m - lam * m) with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  set Δ := m - n k with hΔ
  set t : ℝ := min 1 (D / (M.γc * Δ ^ 2 + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ D / (M.γc * Δ ^ 2 + 1) := min_le_right _ _
  have hconv := (hsc k).convexOn.2 (mem_univ (n k)) (mem_univ m) (by linarith : 0 ≤ 1 - t)
    ht0.le (by ring)
  simp only [smul_eq_mul] at hconv
  have e : (1 - t) * n k + t * m = n k + t * Δ := by rw [hΔ]; ring
  rw [e] at hconv
  set n' : Fin M.K → ℝ := Function.update n k (n k + t * Δ) with hn'
  have hd : ∑ j, (n' j - n j) = t * Δ := by
    rw [Fintype.sum_eq_single k]
    · simp [hn']
    · intro j hj; simp [hn', hj]
  have hdP : ∑ j, (Q j (n' j) - Q j (n j)) = Q k (n k + t * Δ) - Q k (n k) := by
    rw [Fintype.sum_eq_single k]
    · simp [hn']
    · intro j hj; simp [hn', hj]
  rw [Finset.sum_sub_distrib] at hd
  have hdiff := obj_diff M Q y n n'
  rw [hdP] at hdiff
  have e2 : ∑ j, n' j = ∑ j, n j + t * Δ := by linarith
  rw [e2] at hdiff
  have := hn n'
  -- t * (γc Δ²) < D
  have htD : t * (M.γc * Δ ^ 2) < D := by
    have h1 : t * (M.γc * Δ ^ 2 + 1) ≤ D := by
      rw [le_div_iff₀ (by positivity)] at ht2; exact ht2
    nlinarith
  have hkey : clientObj M Q y n' - clientObj M Q y n ≥ t * D - M.γc / 2 * t ^ 2 * Δ ^ 2 := by
    rw [hdiff]
    have : Q k (n k + t * Δ) - lam * (n k + t * Δ) ≤ (Q k (n k) - lam * n k) - t * D := by
      rw [hD]; nlinarith
    rw [hlam] at this
    nlinarith
  have : t * D - M.γc / 2 * t ^ 2 * Δ ^ 2 > 0 := by
    have : M.γc / 2 * t ^ 2 * Δ ^ 2 = t * (t * (M.γc * Δ ^ 2)) / 2 := by ring
    rw [this]
    have h3 : t * (M.γc * Δ ^ 2) < D := htD
    nlinarith [mul_lt_mul_of_pos_left h3 ht0]
  linarith

/-- minimizers of `Q m - λ m` are monotone in `λ`. -/
theorem argmin_mono {P : ℝ → ℝ} (hsc : StrictConvexOn ℝ univ P) {l₁ l₂ n₁ n₂ : ℝ}
    (h₁ : ∀ m, P n₁ - l₁ * n₁ ≤ P m - l₁ * m) (h₂ : ∀ m, P n₂ - l₂ * n₂ ≤ P m - l₂ * m)
    (hl : l₁ ≤ l₂) : n₁ ≤ n₂ := by
  rcases hl.lt_or_eq with hlt | heq
  · have a := h₁ n₂
    have b := h₂ n₁
    by_contra hc
    push Not at hc
    nlinarith
  · subst heq
    by_contra hc
    push Not at hc
    have := hsc.2 (mem_univ n₁) (mem_univ n₂) hc.ne' (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have a := h₁ (1/2 * n₁ + 1/2 * n₂)
    have b := h₂ n₁
    nlinarith

theorem argmin_strict {P : ℝ → ℝ} (hP : IsPriceSchedule P) {l₁ l₂ n : ℝ}
    (h₁ : ∀ m, P n - l₁ * n ≤ P m - l₁ * m) (h₂ : ∀ m, P n - l₂ * n ≤ P m - l₂ * m)
    (hn : n ≠ 0) : l₁ = l₂ := by
  have hd := diffAt hP hn
  have key : ∀ lam : ℝ, (∀ m, P n - lam * n ≤ P m - lam * m) → deriv P n = lam := by
    intro lam h
    have hmin : IsLocalMin (fun m => P m - lam * m) n :=
      Filter.Eventually.of_forall (fun m => h m)
    have := hmin.deriv_eq_zero
    have hd2 : HasDerivAt (fun m => P m - lam * m) (deriv P n - lam * 1) n :=
      hd.hasDerivAt.sub ((hasDerivAt_id n).const_mul lam)
    rw [hd2.deriv] at this
    linarith
  rw [← key l₁ h₁, key l₂ h₂]

end LiqT28Aux

open LiqT28Aux in
open Filter Topology in
theorem solution (M : Params) (hK : 2 ≤ M.K) (hγc : 0 < M.γc)
    (Q : Fin M.K → ℝ → ℝ) (hQ : ∀ k, Admissible M (Q k)) (ℓ r : Fin M.K → EReal)
    (hℓ : ∀ k, Tendsto (fun n => ((deriv (Q k) n : ℝ) : EReal)) atBot (𝓝 (ℓ k)))
    (hr : ∀ k, Tendsto (fun n => ((deriv (Q k) n : ℝ) : EReal)) atTop (𝓝 (r k))) :
    (Compatible M Q ↔ Finset.univ.sup ℓ < Finset.univ.inf r) ∧
    (Compatible M Q →
      (∀ y, ∃! n, IsClientMax M Q y n) ∧
      ∀ resp : ℝ → Fin M.K → ℝ, IsResponse M Q resp → ∀ k : Fin M.K,
        Continuous (fun y => resp y k) ∧ Monotone (fun y => resp y k) ∧
          StrictMonoOn (fun y => resp y k) {y | resp y k ≠ 0}) := by
  have hQ' : ∀ k, IsPriceSchedule (Q k) ∧ StrictConvexOn ℝ univ (Q k) :=
    fun k => (LiqProvision.Oligopoly.lemma_2_5_a M hK hγc (Q k)).1 (hQ k)
  have hne : (Finset.univ : Finset (Fin M.K)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  -- the separation condition gives unique maximizers
  have hsep_exists : Finset.univ.sup ℓ < Finset.univ.inf r → ∀ y, ∃! n, IsClientMax M Q y n := by
    intro hsep y
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.1 hsep
    obtain ⟨s₂, hs₂1, hs₂2⟩ := EReal.lt_iff_exists_real_btwn.1 hs1
    obtain ⟨s₁, hs₁1, hs₁2⟩ := EReal.lt_iff_exists_real_btwn.1 hs2
    have hs₂s : s₂ < s := by exact_mod_cast hs₂2
    have hss₁ : s < s₁ := by exact_mod_cast hs₁1
    have hg : ∀ k, ∃ C, ∀ x, s * x + min (s₁ - s) (s - s₂) * |x| - C ≤ Q k x := by
      intro k
      exact growth (hQ' k).1 (hℓ k) (hr k)
        ((Finset.le_sup (Finset.mem_univ k)).trans_lt hs₂1)
        (hs₁2.trans_le (Finset.inf_le (Finset.mem_univ k))) hs₂s hss₁
    choose C hC using hg
    obtain ⟨n, hn⟩ := exist M hγc Q (fun k => (hQ' k).1) s _ (lt_min (by linarith) (by linarith))
      C hC y
    exact ⟨n, hn, fun n' hn' => uniq M Q (fun k => (hQ' k).2) y n' n hn' hn hγc⟩
  have part1 : Compatible M Q ↔ Finset.univ.sup ℓ < Finset.univ.inf r := by
    constructor
    · rintro ⟨-, y, n, hn⟩
      have h := nec M Q hQ' ℓ r hℓ hr y n hn
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup _ hne ℓ
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf _ hne r
      rw [hj, hi]; exact h i j
    · intro hsep
      obtain ⟨n, hn, -⟩ := hsep_exists hsep 0
      exact ⟨hQ, 0, n, hn⟩
  refine ⟨part1, fun hcomp => ⟨hsep_exists (part1.1 hcomp), ?_⟩⟩
  intro resp hresp k
  -- λ(y) and coordinate optimality
  set S : ℝ → ℝ := fun y => ∑ j, resp y j with hS
  set L : ℝ → ℝ := fun y => y - M.γc * S y with hL
  have hopt : ∀ y j m, Q j (resp y j) - L y * resp y j ≤ Q j m - L y * m :=
    fun y j m => coord_opt M Q (fun k => (hQ' k).2) hγc y (resp y) (hresp y) j m
  have hmonoL : ∀ y y', L y ≤ L y' → ∀ j, resp y j ≤ resp y' j :=
    fun y y' h j => argmin_mono (hQ' j).2 (hopt y j) (hopt y' j) h
  have hLstrict : StrictMono L := by
    intro y y' hyy'
    by_contra hc
    push Not at hc
    have h1 : S y' ≤ S y := Finset.sum_le_sum (fun j _ => hmonoL y' y hc j)
    simp only [hL] at hc
    nlinarith
  have hmono : ∀ j, Monotone (fun y => resp y j) :=
    fun j y y' h => hmonoL y y' (hLstrict.monotone h) j
  have hlip : ∀ y y', y ≤ y' → resp y' k - resp y k ≤ (y' - y) / M.γc := by
    intro y y' h
    have h1 : L y ≤ L y' := hLstrict.monotone h
    simp only [hL] at h1
    have h2 : resp y' k - resp y k ≤ ∑ j, (resp y' j - resp y j) :=
      Finset.single_le_sum (f := fun j => resp y' j - resp y j)
        (fun j _ => sub_nonneg.2 (hmono j h)) (Finset.mem_univ k)
    rw [Finset.sum_sub_distrib] at h2
    rw [le_div_iff₀ hγc]
    simp only [hS] at h1
    nlinarith
  refine ⟨?_, hmono k, ?_⟩
  · rw [Metric.continuous_iff]
    intro b ε hε
    refine ⟨M.γc * ε, by positivity, fun a hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    rcases le_total a b with h | h
    · have h1 := hlip a b h
      have h2 := hmono k h
      rw [abs_sub_comm, abs_of_nonneg (by simpa using h2)]
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hab
      calc resp b k - resp a k ≤ (b - a) / M.γc := h1
        _ < ε := by rw [div_lt_iff₀ hγc]; linarith
    · have h1 := hlip b a h
      have h2 := hmono k h
      rw [abs_of_nonneg (by simpa using h2)]
      rw [abs_of_nonneg (by linarith)] at hab
      calc resp a k - resp b k ≤ (a - b) / M.γc := h1
        _ < ε := by rw [div_lt_iff₀ hγc]; linarith
  · intro y hy y' hy' hyy'
    rcases (hmono k hyy'.le).lt_or_eq with h | h
    · exact h
    · exfalso
      have heq : L y = L y' := by
        apply argmin_strict (hQ' k).1 (hopt y k) _ hy
        intro m
        have := hopt y' k m
        simp only at h
        rw [h]; exact this
      exact (hLstrict hyy').ne heq
