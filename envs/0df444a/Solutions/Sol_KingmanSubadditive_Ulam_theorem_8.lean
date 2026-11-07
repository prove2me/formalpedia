-- Prove2me | solution 1 for KingmanSubadditive.Ulam.theorem_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:37:44.966997+00:00
-- url     : https://prove2.me/submissions/95b6813b-1d2c-42c1-9605-954e7eff20d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations
import Theorems.Thm_KingmanSubadditive_Ulam_eq_2_4_8
import Theorems.Thm_KingmanSubadditive_Ulam_beta_infimum
import Theorems.Thm_KingmanSubadditive_Ulam_theorem_8_lower_bound

open Filter Topology
open KingmanSubadditive.Ulam

theorem solution (c : ℝ) (hc : KingmanSubadditive.Ulam.ConvergesInProbUniform c) :
    (∃! δ : ℝ, 0 < δ ∧ Real.log (1 + δ) = 2 * δ / (1 + δ)) ∧
    (∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) →
      Real.sqrt (8 / Real.pi) ≤ c ∧ c ≤ Real.sqrt δ + 1 / Real.sqrt δ) ∧
    (1.59 : ℝ) < c ∧ c < 2.49 := by
  obtain ⟨hex, hinf⟩ := beta_infimum
  have hlow := theorem_8_lower_bound c hc
  -- upper bound: c ≤ every admissible b
  have hS : ∀ b : ℝ, b ∈ {b : ℝ | 0 < b ∧ ∃ α : ℝ, 0 < α ∧ α < b ∧ stirlingExponent α b < 0} →
      c ≤ b := by
    rintro b ⟨hb, α, hα, hαb, hst⟩
    by_contra hlt
    push Not at hlt
    set ε := (c - b) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have h1 := eq_2_4_8 α b hα hαb hst
    have h2 := hc ε hεpos
    have hsum := h1.add h2
    rw [add_zero] at hsum
    have hge : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) ≤ unifProb n (fun σ => b * Real.sqrt n ≤ (lis σ : ℝ)) +
          unifProb n (fun σ => ε < |(lis σ : ℝ) / Real.sqrt n - c|) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      classical
      unfold unifProb
      have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
      rw [← add_div, le_div_iff₀ hfac, one_mul]
      have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => b * Real.sqrt n ≤ (lis σ : ℝ))) ∪
          (Finset.univ.filter
            (fun σ : Equiv.Perm (Fin n) => ε < |(lis σ : ℝ) / Real.sqrt n - c|)) := by
        intro σ _
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        by_cases hσ : b * Real.sqrt n ≤ (lis σ : ℝ)
        · exact Or.inl ⟨Finset.mem_univ _, hσ⟩
        · right
          refine ⟨Finset.mem_univ _, ?_⟩
          push Not at hσ
          have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
          have : (lis σ : ℝ) / Real.sqrt n < b := by rwa [div_lt_iff₀ hsq]
          rw [abs_sub_comm, abs_of_pos (by linarith)]
          linarith
      have hc1 := Finset.card_le_card hsub
      have hc2 := Finset.card_union_le
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => b * Real.sqrt n ≤ (lis σ : ℝ)))
        (Finset.univ.filter
            (fun σ : Equiv.Perm (Fin n) => ε < |(lis σ : ℝ) / Real.sqrt n - c|))
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hc1
      have h3 := hc1.trans hc2
      have h4 : ((Nat.factorial n : ℕ) : ℝ) ≤ ((_ + _ : ℕ) : ℝ) := Nat.cast_le.mpr h3
      push_cast at h4
      convert h4 using 3
    have := ge_of_tendsto hsum hge
    norm_num at this
  -- the root δ: bounds 1 ≤ δ ≤ 3.94
  have hroot_ge : ∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) → 1 ≤ δ := by
    intro δ hδ heq
    by_contra hlt
    push Not at hlt
    have h1 : Real.log (1 + δ) ≤ δ := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + δ by linarith)
      linarith
    have h2 : δ < 2 * δ / (1 + δ) := by
      rw [lt_div_iff₀ (by linarith)]; nlinarith
    linarith
  have hexp : Real.exp (1.5952 : ℝ) < 4.94 := by
    have he : Real.exp (1.5952 : ℝ) = Real.exp 1 * Real.exp 0.5952 := by
      rw [← Real.exp_add]; norm_num
    have hb := Real.exp_bound (x := (0.5952 : ℝ)) (by norm_num [abs_of_pos]) (n := 6) (by norm_num)
    rw [abs_le] at hb
    have hb2 : Real.exp 0.5952 ≤ ∑ i ∈ Finset.range 6, (0.5952 : ℝ) ^ i / (Nat.factorial i) +
        |(0.5952 : ℝ)| ^ 6 * ((Nat.succ 6 : ℕ) / ((Nat.factorial 6 : ℕ) * (6 : ℕ))) := by
      linarith [hb.2]
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at hb2
    have h1 := Real.exp_one_lt_d9
    rw [he]
    have hpos : 0 < Real.exp 0.5952 := Real.exp_pos _
    nlinarith
  have hf394 : 0 < Real.log (1 + 3.94) - 2 * 3.94 / (1 + 3.94) := by
    have : (1.5952 : ℝ) < Real.log (1 + 3.94) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; norm_num at hexp ⊢; exact hexp
    norm_num at this ⊢
    linarith
  have hf1 : Real.log (1 + 1) - 2 * 1 / (1 + 1) < 0 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢; linarith
  obtain ⟨δ₀, hδ₀mem, hδ₀eq⟩ : ∃ x ∈ Set.Icc (1 : ℝ) 3.94,
      Real.log (1 + x) - 2 * x / (1 + x) = 0 := by
    have hcont : ContinuousOn (fun x : ℝ => Real.log (1 + x) - 2 * x / (1 + x))
        (Set.Icc (1 : ℝ) 3.94) := by
      apply ContinuousOn.sub
      · apply ContinuousOn.log (by fun_prop)
        intro x hx; have := hx.1; linarith
      · apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx; have := hx.1; linarith
    have := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 3.94) hcont
    exact this ⟨hf1.le, hf394.le⟩
  have hroot_le : ∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) → δ ≤ 3.94 := by
    intro δ hδ heq
    obtain ⟨d, _, huniq⟩ := hex
    have e1 := huniq δ ⟨hδ, heq⟩
    have e2 := huniq δ₀ ⟨by linarith [hδ₀mem.1], by linarith⟩
    rw [e1, ← e2]; exact hδ₀mem.2
  have hupper : ∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) →
      c ≤ Real.sqrt δ + 1 / Real.sqrt δ := by
    intro δ hδ heq
    rw [← hinf δ hδ heq]
    have hβpos : 0 < Real.sqrt δ + 1 / Real.sqrt δ := by
      have := Real.sqrt_pos.mpr hδ; positivity
    apply le_csInf _ hS
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have := hinf δ hδ heq
    rw [hne, Real.sInf_empty] at this
    linarith
  have hsqrt8 : (1.59 : ℝ) < Real.sqrt (8 / Real.pi) := by
    rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  refine ⟨hex, fun δ hδ heq => ⟨hlow, hupper δ hδ heq⟩, by linarith, ?_⟩
  obtain ⟨δ, ⟨hδ, heq⟩, _⟩ := hex
  have hc := hupper δ hδ heq
  have hd1 := hroot_ge δ hδ heq
  have hd2 := hroot_le δ hδ heq
  set s := Real.sqrt δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hδ
  have hss : s ^ 2 = δ := Real.sq_sqrt hδ.le
  have hs1 : 1 ≤ s := by nlinarith
  have hs2 : s ≤ 1.985 := by nlinarith
  have key : s + 1 / s < 2.49 := by
    have : s + 1 / s = (s ^ 2 + 1) / s := by field_simp
    rw [this, div_lt_iff₀ hs0]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ s - 0.5034)
      (by linarith : s - 1.985 ≤ 0)]
  linarith
