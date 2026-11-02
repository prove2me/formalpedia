-- Prove2me | solution 1 for LiqProvision.Oligopoly.lemma_2_5_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:39:12.121093+00:00
-- url     : https://prove2.me/submissions/7da79d57-1f29-4752-a22d-8880d86fe780

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

open Set Filter Topology
open LiqProvision.Oligopoly

namespace LiqL25Aux

theorem strictConvex_aux (P : ℝ → ℝ) (hc : Continuous P)
    (h : ∀ x t, t ≠ 0 → 2 * P x < P (x + t) + P (x - t)) (u v : ℝ) (huv : u < v) :
    ∀ z ∈ Ioo u v, P z < P u + (P v - P u) / (v - u) * (z - u) := by
  set s := (P v - P u) / (v - u) with hs
  set D : ℝ → ℝ := fun z => P z - (P u + s * (z - u)) with hD
  have hDc : Continuous D := by simp only [hD]; fun_prop
  have hDu : D u = 0 := by simp [hD]
  have hDv : D v = 0 := by
    have hne : v - u ≠ 0 := by linarith
    simp only [hD, hs, div_mul_cancel₀ _ hne]; ring
  have hmid : ∀ x t, t ≠ 0 → 2 * D x < D (x + t) + D (x - t) := by
    intro x t ht; have := h x t ht; simp only [hD]; linarith
  intro z hz
  by_contra hcon
  push Not at hcon
  have hz0 : 0 ≤ D z := by simp only [hD]; linarith
  obtain ⟨c, hcI, hcmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 huv.le) hDc.continuousOn
  rw [isMaxOn_iff] at hcmax
  obtain ⟨c', hc'I, hc'max⟩ : ∃ c' ∈ Ioo u v, ∀ w ∈ Icc u v, D w ≤ D c' := by
    by_cases hci : c ∈ Ioo u v
    · exact ⟨c, hci, hcmax⟩
    · refine ⟨z, hz, fun w hw => ?_⟩
      have hce : c = u ∨ c = v := by
        rcases hcI with ⟨h1, h2⟩
        rcases h1.lt_or_eq with h1 | h1
        · rcases h2.lt_or_eq with h2 | h2
          · exact absurd ⟨h1, h2⟩ hci
          · exact Or.inr h2
        · exact Or.inl h1.symm
      have hDc0 : D c = 0 := by rcases hce with rfl | rfl <;> assumption
      linarith [hcmax w hw]
  have ht : 0 < min (c' - u) (v - c') := lt_min (by linarith [hc'I.1]) (by linarith [hc'I.2])
  have h1 : c' + min (c' - u) (v - c') ∈ Icc u v :=
    ⟨by linarith [hc'I.1], by linarith [min_le_right (c' - u) (v - c')]⟩
  have h2 : c' - min (c' - u) (v - c') ∈ Icc u v :=
    ⟨by linarith [min_le_left (c' - u) (v - c')], by linarith [hc'I.2]⟩
  have := hmid c' _ ht.ne'
  linarith [hc'max _ h1, hc'max _ h2]

theorem strictConvex_of_mid (P : ℝ → ℝ) (hc : Continuous P)
    (h : ∀ x t, t ≠ 0 → 2 * P x < P (x + t) + P (x - t)) : StrictConvexOn ℝ univ P := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  simp only [smul_eq_mul]
  obtain rfl : a = 1 - b := by linarith
  rcases hxy.lt_or_gt with hlt | hlt
  · have hmem : (1 - b) * x + b * y ∈ Ioo x y := ⟨by nlinarith, by nlinarith⟩
    have := strictConvex_aux P hc h x y hlt _ hmem
    have e : (P y - P x) / (y - x) * ((1 - b) * x + b * y - x) = b * (P y - P x) := by
      field_simp; ring
    linarith
  · have hmem : (1 - b) * x + b * y ∈ Ioo y x := ⟨by nlinarith, by nlinarith⟩
    have := strictConvex_aux P hc h y x hlt _ hmem
    have e : (P x - P y) / (x - y) * ((1 - b) * x + b * y - y) = (1 - b) * (P x - P y) := by
      field_simp; ring
    linarith

theorem obj_const (M : Params) (P : ℝ → ℝ) (y x : ℝ) :
    clientObj M (fun _ => P) y (fun _ => x) =
      y * ((M.K : ℝ) * x) - (M.K : ℝ) * P x - M.γc / 2 * ((M.K : ℝ) * x) ^ 2 := by
  simp [clientObj, Finset.sum_const, Finset.card_univ]

theorem forward (M : Params) (hK : 2 ≤ M.K) (hγc : 0 < M.γc) (P : ℝ → ℝ)
    (hA : Admissible M P) : StrictConvexOn ℝ univ P := by
  obtain ⟨hPS, huniq⟩ := hA
  have hPc : Continuous P := hPS.1
  obtain ⟨i0, i1, hi01⟩ : ∃ i0 i1 : Fin M.K, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have hKpos : (0 : ℝ) < M.K := by exact_mod_cast (show 0 < M.K by omega)
  choose nf hnf using fun y => (huniq y).exists
  have hun : ∀ y n, IsClientMax M (fun _ => P) y n → n = nf y :=
    fun y n hn => (huniq y).unique hn (hnf y)
  -- the unique maximizer is symmetric
  have hsym : ∀ y k, nf y k = nf y i0 := by
    intro y k
    have hmax : IsClientMax M (fun _ => P) y (nf y ∘ Equiv.swap i0 k) := by
      intro n'
      have e : clientObj M (fun _ => P) y (nf y ∘ Equiv.swap i0 k) =
          clientObj M (fun _ => P) y (nf y) := by
        simp only [clientObj, Function.comp]
        rw [Equiv.sum_comp (Equiv.swap i0 k) (fun j => nf y j),
          Equiv.sum_comp (Equiv.swap i0 k) (fun j => P (nf y j))]
      rw [e]; exact hnf y n'
    have := congrFun (hun y _ hmax) i0
    simpa [Equiv.swap_apply_left] using this
  set m : ℝ → ℝ := fun y => nf y i0 with hm
  have hnf_eq : ∀ y, nf y = fun _ => m y := fun y => funext (hsym y)
  set K : ℝ := (M.K : ℝ) with hKdef
  set ψ : ℝ → ℝ → ℝ := fun y x => y * (K * x) - K * P x - M.γc / 2 * (K * x) ^ 2 with hψ
  have hψmax : ∀ y x, ψ y x ≤ ψ y (m y) := by
    intro y x
    have := hnf y (fun _ => x)
    rw [hnf_eq y, obj_const, obj_const] at this
    exact this
  -- monotonicity of m
  have hmono : Monotone m := by
    intro y y' hyy'
    rcases hyy'.eq_or_lt with rfl | hlt
    · exact le_rfl
    by_contra hcon
    push Not at hcon
    have h1 := hψmax y (m y')
    have h2 := hψmax y' (m y)
    simp only [hψ] at h1 h2
    have : 0 < (y' - y) * (m y - m y') * K := by
      apply mul_pos (mul_pos (by linarith) (by linarith)) hKpos
    nlinarith
  -- limits of m are maximizers
  have hlim : ∀ y₀ (F : Filter ℝ) [F.NeBot], F ≤ 𝓝 y₀ → ∀ L, Tendsto m F (𝓝 L) → m y₀ = L := by
    intro y₀ F _ hF L hmL
    have hmaxL : IsClientMax M (fun _ => P) y₀ (fun _ => L) := by
      intro n'
      rw [obj_const]
      have hy : Tendsto (fun y : ℝ => y) F (𝓝 y₀) := hF
      have hPm : Tendsto (fun y => P (m y)) F (𝓝 (P L)) := (hPc.tendsto L).comp hmL
      have ht : Tendsto (fun y => (y * (K * m y) - K * P (m y) - M.γc / 2 * (K * m y) ^ 2) -
          clientObj M (fun _ => P) y n') F
          (𝓝 ((y₀ * (K * L) - K * P L - M.γc / 2 * (K * L) ^ 2) -
            clientObj M (fun _ => P) y₀ n')) := by
        simp only [clientObj]
        refine Tendsto.sub (Tendsto.sub (Tendsto.sub (hy.mul (tendsto_const_nhds.mul hmL))
          (tendsto_const_nhds.mul hPm))
          (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hmL).pow 2))) ?_
        exact ((hy.mul tendsto_const_nhds).sub tendsto_const_nhds).sub tendsto_const_nhds
      have hge : (0:ℝ) ≤ (y₀ * (K * L) - K * P L - M.γc / 2 * (K * L) ^ 2) -
            clientObj M (fun _ => P) y₀ n' := ge_of_tendsto' ht (fun y => by
        have := hnf y n'
        rw [hnf_eq y, obj_const] at this
        linarith)
      linarith
    have := congrFun (hun y₀ _ hmaxL) i0
    rw [hm]; exact this.symm
  have hcont : Continuous m := by
    rw [continuous_iff_continuousAt]
    intro y₀
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · have h := hmono.tendsto_nhdsLT y₀
      have := hlim y₀ _ nhdsWithin_le_nhds _ h
      rw [ContinuousWithinAt, this]; exact h
    · have h := hmono.tendsto_nhdsGT y₀
      have := hlim y₀ _ nhdsWithin_le_nhds _ h
      rw [ContinuousWithinAt, this]; exact h
  -- unboundedness
  set R : ℝ → ℝ := fun x => K * P x + M.γc / 2 * (K * x) ^ 2 with hR
  have hRc : Continuous R := by simp only [hR]; fun_prop
  have hψR : ∀ y x, ψ y x = y * K * x - R x := by intro y x; simp only [hψ, hR]; ring
  have htop : Tendsto m atTop atTop := by
    apply hmono.tendsto_atTop_atTop
    intro B
    by_contra hcon
    push Not at hcon
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := m 0) (b := B)).exists_bound_of_continuousOn
      hRc.continuousOn
    set y : ℝ := (|R (B + 1)| + |C| + 1) / K with hy
    have hy0 : 0 ≤ y := by positivity
    have hmy : m y ∈ Icc (m 0) B := ⟨hmono hy0, (hcon y).le⟩
    have hb := hC _ hmy
    rw [Real.norm_eq_abs] at hb
    have h1 := hψmax y (B + 1)
    rw [hψR, hψR] at h1
    have hyK : y * K = |R (B + 1)| + |C| + 1 := by rw [hy]; field_simp
    have : y * K ≤ y * K * (B + 1 - m y) := by
      have h1' : 1 ≤ B + 1 - m y := by linarith [hcon y]
      have := mul_le_mul_of_nonneg_left h1' (mul_nonneg hy0 hKpos.le)
      linarith
    have := le_abs_self (R (B + 1))
    have := neg_abs_le (R (m y))
    have := le_abs_self C
    nlinarith
  have hbot : Tendsto m atBot atBot := by
    apply hmono.tendsto_atBot_atBot
    intro B
    by_contra hcon
    push Not at hcon
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := B) (b := m 0)).exists_bound_of_continuousOn
      hRc.continuousOn
    set y : ℝ := -((|R (B - 1)| + |C| + 1) / K) with hy
    have hy0 : y ≤ 0 := by rw [hy]; have : 0 ≤ (|R (B - 1)| + |C| + 1) / K := by positivity
                           linarith
    have hmy : m y ∈ Icc B (m 0) := ⟨(hcon y).le, hmono hy0⟩
    have hb := hC _ hmy
    rw [Real.norm_eq_abs] at hb
    have h1 := hψmax y (B - 1)
    rw [hψR, hψR] at h1
    have hyK : -(y * K) = |R (B - 1)| + |C| + 1 := by rw [hy]; field_simp
    have : -(y * K) ≤ y * K * (B - 1 - m y) := by
      have h1' : B - 1 - m y ≤ -1 := by linarith [hcon y]
      have := mul_le_mul_of_nonpos_left h1' (mul_nonpos_of_nonpos_of_nonneg hy0 hKpos.le)
      linarith
    have := le_abs_self (R (B - 1))
    have := neg_abs_le (R (m y))
    have := le_abs_self C
    nlinarith
  have hsurj := hcont.surjective htop hbot
  apply strictConvex_of_mid P hPc
  intro x t ht
  obtain ⟨y, rfl⟩ := hsurj x
  by_contra hle
  push Not at hle
  set n' : Fin M.K → ℝ := fun k => if k = i0 then m y + t else if k = i1 then m y - t else m y
    with hn'
  have hd : ∑ k, (n' k - nf y k) = 0 := by
    rw [Fintype.sum_eq_add i0 i1 hi01]
    · simp [hn', hi01.symm, hsym y, hm]
    · rintro k ⟨hk0, hk1⟩; simp [hn', hk0, hk1, hsym y k, hm]
  have hdP : ∑ k, (P (n' k) - P (nf y k)) = P (m y + t) + P (m y - t) - 2 * P (m y) := by
    rw [Fintype.sum_eq_add i0 i1 hi01]
    · simp [hn', hi01.symm, hsym y, hm]; ring
    · rintro k ⟨hk0, hk1⟩; simp [hn', hk0, hk1, hsym y k, hm]
  rw [Finset.sum_sub_distrib] at hd hdP
  have hmax' : IsClientMax M (fun _ => P) y n' := by
    intro n''
    have := hnf y n''
    simp only [clientObj] at this ⊢
    have e : ∑ k, n' k = ∑ k, nf y k := by linarith
    rw [e]; linarith
  have := congrFun (hun y n' hmax') i0
  simp [hn', hm] at this
  exact ht this

theorem lower_bound (P : ℝ → ℝ) (hP0 : P 0 = 0) (hsc : StrictConvexOn ℝ univ P) :
    ∃ c d : ℝ, 0 < d ∧ ∀ t, c * t + d * |t| - 2 * d ≤ P t := by
  have hcv := hsc.convexOn
  have hab : -P (-1) < P 1 := by
    have := hsc.slope_strict_mono_adjacent (x := -1) (y := 0) (z := 1) (mem_univ _) (mem_univ _)
      (by norm_num) (by norm_num)
    simp [hP0] at this; linarith
  refine ⟨(P 1 - P (-1)) / 2, (P 1 + P (-1)) / 2, by linarith, fun t => ?_⟩
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [abs_of_neg ht]
    rcases lt_or_ge t (-1) with ht1 | ht1
    · have := hcv.slope_mono_adjacent (x := t) (y := -1) (z := 0) (mem_univ _) (mem_univ _)
        ht1 (by norm_num)
      rw [div_le_div_iff₀ (by linarith) (by norm_num)] at this
      simp [hP0] at this
      nlinarith
    · have := hcv.slope_mono_adjacent (x := t) (y := 0) (z := 1) (mem_univ _) (mem_univ _)
        ht (by norm_num)
      rw [div_le_div_iff₀ (by linarith) (by norm_num)] at this
      simp [hP0] at this
      nlinarith
  · subst ht; simp [hP0]; linarith
  · rw [abs_of_pos ht]
    rcases lt_or_ge 1 t with ht1 | ht1
    · have := hcv.slope_mono_adjacent (x := 0) (y := 1) (z := t) (mem_univ _) (mem_univ _)
        (by norm_num) ht1
      rw [div_le_div_iff₀ (by norm_num) (by linarith)] at this
      simp [hP0] at this
      nlinarith
    · have := hcv.slope_mono_adjacent (x := -1) (y := 0) (z := t) (mem_univ _) (mem_univ _)
        (by norm_num) ht
      rw [div_le_div_iff₀ (by norm_num) (by linarith)] at this
      simp [hP0] at this
      nlinarith

theorem backward (M : Params) (hγc : 0 < M.γc) (P : ℝ → ℝ)
    (hPS : IsPriceSchedule P) (hsc : StrictConvexOn ℝ univ P) : Admissible M P := by
  have hPc : Continuous P := hPS.1
  refine ⟨hPS, fun y => ?_⟩
  apply existsUnique_of_exists_of_unique
  · obtain ⟨c, d, hd, hcd⟩ := lower_bound P hPS.2.1 hsc
    set Φ := clientObj M (fun _ => P) y with hΦ
    have hΦc : Continuous Φ := by rw [hΦ]; unfold clientObj; fun_prop
    set C₀ : ℝ := (y - c) ^ 2 / (2 * M.γc) + 2 * d * M.K with hC₀
    have hbound : ∀ n : Fin M.K → ℝ, Φ n ≤ C₀ - d * ∑ k, |n k| := by
      intro n
      have hsumP : c * ∑ k, n k + d * ∑ k, |n k| - 2 * d * M.K ≤ ∑ k, P (n k) := by
        have := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hcd (n k))
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
        linarith
      have hq : (y - c) * ∑ k, n k - M.γc / 2 * (∑ k, n k) ^ 2 ≤ (y - c) ^ 2 / (2 * M.γc) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (M.γc * ∑ k, n k - (y - c))]
      simp only [hΦ, clientObj, hC₀]
      nlinarith
    set T := {n : Fin M.K → ℝ | Φ 0 ≤ Φ n} with hT
    have hTc : IsCompact T := by
      apply Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_const hΦc)
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨(C₀ - Φ 0) / d, fun n hn => ?_⟩
      have hb := hbound n
      have hn' : Φ 0 ≤ Φ n := hn
      have hs : ∑ k, |n k| ≤ (C₀ - Φ 0) / d := by
        rw [le_div_iff₀ hd]; linarith
      have hs0 : 0 ≤ ∑ k, |n k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (hs0.trans hs)]
      intro k
      rw [Real.norm_eq_abs]
      exact (Finset.single_le_sum (f := fun k => |n k|) (fun k _ => abs_nonneg _)
        (Finset.mem_univ k)).trans hs
    obtain ⟨n0, hn0T, hn0⟩ := hTc.exists_isMaxOn ⟨0, show Φ 0 ≤ Φ 0 from le_refl _⟩ hΦc.continuousOn
    refine ⟨n0, fun n' => ?_⟩
    by_cases h : n' ∈ T
    · exact hn0 h
    · have h' : Φ n' < Φ 0 := lt_of_not_ge h
      have : Φ 0 ≤ Φ n0 := hn0T
      show Φ n' ≤ Φ n0
      linarith
  · intro n₁ n₂ h₁ h₂
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, n₁ k ≠ n₂ k := by
      by_contra h; push Not at h; exact hne (funext h)
    set mid : Fin M.K → ℝ := fun j => (n₁ j + n₂ j) / 2 with hmid
    have hmidP : ∀ j, P (mid j) ≤ (P (n₁ j) + P (n₂ j)) / 2 := by
      intro j
      have := hsc.convexOn.2 (mem_univ (n₁ j)) (mem_univ (n₂ j)) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      simp only [smul_eq_mul] at this
      have e : (n₁ j + n₂ j) / 2 = 1 / 2 * n₁ j + 1 / 2 * n₂ j := by ring
      simp only [hmid, e]; linarith
    have hmidPk : P (mid k) < (P (n₁ k) + P (n₂ k)) / 2 := by
      have := hsc.2 (mem_univ (n₁ k)) (mem_univ (n₂ k)) hk (by norm_num : (0:ℝ) < 1/2)
        (by norm_num : (0:ℝ) < 1/2) (by norm_num)
      simp only [smul_eq_mul] at this
      have e : (n₁ k + n₂ k) / 2 = 1 / 2 * n₁ k + 1 / 2 * n₂ k := by ring
      simp only [hmid, e]; linarith
    have hsumlt : ∑ j, P (mid j) < ∑ j, (P (n₁ j) + P (n₂ j)) / 2 :=
      Finset.sum_lt_sum (fun j _ => hmidP j) ⟨k, Finset.mem_univ _, hmidPk⟩
    have hsplit : ∑ j, (P (n₁ j) + P (n₂ j)) / 2 = (∑ j, P (n₁ j) + ∑ j, P (n₂ j)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    have hsm : ∑ j, mid j = (∑ j, n₁ j + ∑ j, n₂ j) / 2 := by
      simp only [hmid]; rw [← Finset.sum_div, Finset.sum_add_distrib]
    have e1 := h₁ mid
    have e2 := h₂ mid
    have e3 := h₁ n₂
    have e4 := h₂ n₁
    simp only [clientObj] at e1 e2 e3 e4
    rw [hsm] at e1 e2
    nlinarith [sq_nonneg (∑ j, n₁ j - ∑ j, n₂ j), M.γc]

end LiqL25Aux

open LiqL25Aux in
theorem solution (M : Params) (hK : 2 ≤ M.K) (hγc : 0 < M.γc) (P : ℝ → ℝ) :
    Admissible M P ↔ IsPriceSchedule P ∧ StrictConvexOn ℝ Set.univ P :=
  ⟨fun h => ⟨h.1, forward M hK hγc P h⟩, fun h => backward M hγc P h.1 h.2⟩
