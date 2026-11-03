-- Prove2me | solution 1 for GreedWorks.OnlineTime.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:25:03.881336+00:00
-- url     : https://prove2.me/submissions/30951f26-de16-4d1d-9d6d-5b86370d17b7

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP
import Definitions.Def_GreedWorks_OnlineTime_Greedy

open GreedWorks.OnlineTime Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Lemma7Helper

variable {M : Type*} [Fintype M] {n : ℕ}

private lemma disjoint_Ico_sum_le_aux (m : ℕ) :
    ∀ (S : Finset (Fin n)) (_hcard : S.card = m) (s len : Fin n → ℝ) (a b : ℝ)
      (_hab : a ≤ b) (_hlen_pos : ∀ k ∈ S, 0 < len k)
      (_hsub : ∀ k ∈ S, a ≤ s k ∧ s k + len k ≤ b)
      (_hdisj : ∀ k₁ ∈ S, ∀ k₂ ∈ S, k₁ ≠ k₂ →
        Disjoint (Set.Ico (s k₁) (s k₁ + len k₁)) (Set.Ico (s k₂) (s k₂ + len k₂))),
      ∑ k ∈ S, len k ≤ b - a := by
  induction m with
  | zero =>
    intro S hcard _ len a b hab _ _ _
    rw [Finset.card_eq_zero.mp hcard, Finset.sum_empty]
    linarith
  | succ m ih =>
    intro S hcard s len a b _ hlen_pos hsub hdisj
    have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨k₀, hk₀S, hk₀_max⟩ := S.exists_max_image s hS_ne
    let S' := S.erase k₀
    have hcard' : S'.card = m := by
      rw [Finset.card_erase_of_mem hk₀S, hcard]
      omega
    have hab' : a ≤ s k₀ := (hsub k₀ hk₀S).1
    have hlen_pos' : ∀ k ∈ S', 0 < len k :=
      fun k hk => hlen_pos k (Finset.mem_of_mem_erase hk)
    have hsub' : ∀ k ∈ S', a ≤ s k ∧ s k + len k ≤ s k₀ := by
      intro k hk
      have hne : k ≠ k₀ := (Finset.mem_erase.mp hk).1
      have hkS : k ∈ S := (Finset.mem_erase.mp hk).2
      refine ⟨(hsub k hkS).1, ?_⟩
      by_contra! hgt
      have hsk_le : s k ≤ s k₀ := hk₀_max k hkS
      have hmem1 : s k₀ ∈ Set.Ico (s k) (s k + len k) := ⟨hsk_le, hgt⟩
      have hmem2 : s k₀ ∈ Set.Ico (s k₀) (s k₀ + len k₀) :=
        ⟨le_refl _, by linarith [hlen_pos k₀ hk₀S]⟩
      exact Set.disjoint_left.mp (hdisj k hkS k₀ hk₀S hne) hmem1 hmem2
    have hdisj' : ∀ k₁ ∈ S', ∀ k₂ ∈ S', k₁ ≠ k₂ →
        Disjoint (Set.Ico (s k₁) (s k₁ + len k₁)) (Set.Ico (s k₂) (s k₂ + len k₂)) :=
      fun k₁ hk₁ k₂ hk₂ hne =>
        hdisj k₁ (Finset.mem_of_mem_erase hk₁) k₂ (Finset.mem_of_mem_erase hk₂) hne
    have hstep := ih S' hcard' s len a (s k₀) hab' hlen_pos' hsub' hdisj'
    have hsum : ∑ k ∈ S', len k + len k₀ = ∑ k ∈ S, len k :=
      Finset.sum_erase_add S len hk₀S
    have hk₀_hi : s k₀ + len k₀ ≤ b := (hsub k₀ hk₀S).2
    linarith

private lemma disjoint_Ico_sum_le (S : Finset (Fin n)) (s len : Fin n → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hlen_pos : ∀ k ∈ S, 0 < len k)
    (hsub : ∀ k ∈ S, a ≤ s k ∧ s k + len k ≤ b)
    (hdisj : ∀ k₁ ∈ S, ∀ k₂ ∈ S, k₁ ≠ k₂ →
      Disjoint (Set.Ico (s k₁) (s k₁ + len k₁)) (Set.Ico (s k₂) (s k₂ + len k₂))) :
    ∑ k ∈ S, len k ≤ b - a :=
  disjoint_Ico_sum_le_aux S.card S rfl s len a b hab hlen_pos hsub hdisj

private def costTerm (p : M → Fin n → ℝ) (w : Fin n → ℝ) (i : M) (j k : Fin n) : ℝ :=
  if w j / p i j ≤ w k / p i k then w j * p i k else w k * p i j

private lemma cost_eq_base_add_sum (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (m : Fin n → M) (s : Fin n → ℝ) (j : Fin n) (i : M) :
    cost c r p w m s j i =
      w j * ((1 + 1 / c) * modRelease c r p i j + p i j) +
        ∑ k ∈ waiting r m s i j, costTerm p w i j k := by
  unfold cost
  have hsplit := (Finset.sum_filter_add_sum_filter_not (waiting r m s i j)
    (fun k => w j / p i j ≤ w k / p i k) (costTerm p w i j)).symm
  have h1 : ∑ k ∈ (waiting r m s i j).filter (fun k => w j / p i j ≤ w k / p i k),
        costTerm p w i j k =
      w j * ∑ k ∈ (waiting r m s i j).filter (fun k => w j / p i j ≤ w k / p i k),
        p i k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hle : w j / p i j ≤ w k / p i k := (Finset.mem_filter.mp hk).2
    simp [costTerm, hle]
  have h2 : (waiting r m s i j).filter (fun k => ¬ w j / p i j ≤ w k / p i k) =
      (waiting r m s i j).filter (fun k => w k / p i k < w j / p i j) := by
    ext k; simp [not_le]
  have h3 : ∑ k ∈ (waiting r m s i j).filter (fun k => ¬ w j / p i j ≤ w k / p i k),
        costTerm p w i j k =
      ∑ k ∈ (waiting r m s i j).filter (fun k => w k / p i k < w j / p i j),
        w k * p i j := by
    rw [h2]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hlt : w k / p i k < w j / p i j := (Finset.mem_filter.mp hk).2
    have hnle : ¬ w j / p i j ≤ w k / p i k := not_le.mpr hlt
    simp [costTerm, hnle]
  rw [hsplit, h1, h3]
  ring

private lemma costTerm_le_left (p : M → Fin n → ℝ) (w : Fin n → ℝ) (i : M) (j k : Fin n)
    (hpij : 0 < p i j) (hpik : 0 < p i k) :
    costTerm p w i j k ≤ w j * p i k := by
  unfold costTerm
  split_ifs with hle
  · exact le_refl _
  · have hlt : w k / p i k < w j / p i j := not_le.mp hle
    exact le_of_lt ((div_lt_div_iff₀ hpik hpij).mp hlt)

private lemma costTerm_le_right (p : M → Fin n → ℝ) (w : Fin n → ℝ) (i : M) (j k : Fin n)
    (hpij : 0 < p i j) (hpik : 0 < p i k) :
    costTerm p w i j k ≤ w k * p i j := by
  unfold costTerm
  split_ifs with hle
  · exact (div_le_div_iff₀ hpij hpik).mp hle
  · exact le_refl _

private lemma betaF_nonneg (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (m : Fin n → M) (s : Fin n → ℝ) (f : ℝ) (i : M) (t : ℕ) :
    0 ≤ betaF r p w m s f i t := by
  unfold betaF dualBeta
  exact Finset.sum_nonneg (fun k _ => hw k)

private lemma summable_betaF_div (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (m : Fin n → M) (s : Fin n → ℝ) (f b : ℝ) (hf : 1 ≤ f) (i : M) :
    Summable (fun t : ℕ => betaF r p w m s f i t / b) := by
  let N : ℕ := ∑ k : Fin n, (Nat.ceil (nominalCompletion p m s k) + 1)
  refine summable_of_ne_finset_zero (s := Finset.range N) (fun t ht => ?_)
  have hNt : N ≤ t := Nat.le_of_not_lt (Finset.mem_range.not.mp ht)
  have hempty : Finset.univ.filter
      (fun k => m k = i ∧ (r k : ℝ) ≤ f * (t : ℝ) ∧ f * (t : ℝ) ≤ nominalCompletion p m s k) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k _
    rintro ⟨_, _, hle⟩
    have hk_le : Nat.ceil (nominalCompletion p m s k) + 1 ≤ N :=
      Finset.single_le_sum (f := fun l : Fin n => Nat.ceil (nominalCompletion p m s l) + 1)
        (fun l _ => Nat.zero_le _) (Finset.mem_univ k)
    have hkt : Nat.ceil (nominalCompletion p m s k) + 1 ≤ t := le_trans hk_le hNt
    have hceil : nominalCompletion p m s k ≤ (Nat.ceil (nominalCompletion p m s k) : ℝ) :=
      Nat.le_ceil _
    have hkt_real : (Nat.ceil (nominalCompletion p m s k) : ℝ) + 1 ≤ (t : ℝ) := by
      exact_mod_cast hkt
    have hft : (t : ℝ) ≤ f * (t : ℝ) := by
      have := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg t)
      linarith
    linarith
  unfold betaF dualBeta
  rw [hempty, Finset.sum_empty, zero_div]

private lemma cost_le_bound (elig : M → Fin n → Prop)
    (r : Fin n → ℕ) (hr : Monotone r)
    (p : M → Fin n → ℝ) (hp : ∀ i j, elig i j → 1 ≤ p i j)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (c f : ℝ) (hf : 1 ≤ f)
    (m : Fin n → M) (s : Fin n → ℝ) (hG : IsGreedy c r p w elig m s)
    (i : M) (j : Fin n) (t : ℕ) (helig : elig i j) (hrjt : r j ≤ t) :
    cost c r p w m s j i ≤
      w j * ((1 + 1 / c) * modRelease c r p i j + p i j + (f * (t : ℝ) - (r j : ℝ))) +
        betaF r p w m s f i t * p i j := by
  have hpij_pos : 0 < p i j := by have := hp i j helig; linarith
  have hpik_pos : ∀ k ∈ waiting r m s i j, 0 < p i k := by
    intro k hk
    have hmk : m k = i := (Finset.mem_filter.mp hk).2.2.1
    have helig_k : elig i k := hmk ▸ (hG.1 k).1
    have := hp i k helig_k
    linarith
  let W := waiting r m s i j
  let W_early := W.filter (fun k => s k + p i k ≤ f * (t : ℝ))
  let W_late := W.filter (fun k => ¬ (s k + p i k ≤ f * (t : ℝ)))
  have hsplit : ∑ k ∈ W, costTerm p w i j k =
      ∑ k ∈ W_early, costTerm p w i j k + ∑ k ∈ W_late, costTerm p w i j k :=
    (Finset.sum_filter_add_sum_filter_not W (fun k => s k + p i k ≤ f * (t : ℝ))
      (costTerm p w i j)).symm
  have hearly_bound : ∑ k ∈ W_early, costTerm p w i j k ≤ w j * (f * (t : ℝ) - (r j : ℝ)) := by
    have h1 : ∑ k ∈ W_early, costTerm p w i j k ≤ w j * ∑ k ∈ W_early, p i k := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k hk => ?_)
      exact costTerm_le_left p w i j k hpij_pos (hpik_pos k (Finset.mem_of_mem_filter k hk))
    have hab : (r j : ℝ) ≤ f * (t : ℝ) := by
      have hrt : (r j : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr hrjt
      have htf : (t : ℝ) ≤ f * (t : ℝ) := by
        have := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg t)
        linarith
      linarith
    have h2 : ∑ k ∈ W_early, p i k ≤ f * (t : ℝ) - (r j : ℝ) := by
      refine disjoint_Ico_sum_le W_early s (p i) (r j : ℝ) (f * (t : ℝ)) hab
        (fun k hk => hpik_pos k (Finset.mem_of_mem_filter k hk))
        (fun k hk => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2.2.2,
          (Finset.mem_filter.mp hk).2⟩) ?_
      intro k₁ hk₁ k₂ hk₂ hne
      have hm1 : m k₁ = i := (Finset.mem_filter.mp (Finset.mem_filter.mp hk₁).1).2.2.1
      have hm2 : m k₂ = i := (Finset.mem_filter.mp (Finset.mem_filter.mp hk₂).1).2.2.1
      have hd := hG.2.2.1 k₁ k₂ hne (hm1.trans hm2.symm)
      rwa [hm1, hm2] at hd
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (hw j))
  have hlate_bound : ∑ k ∈ W_late, costTerm p w i j k ≤ betaF r p w m s f i t * p i j := by
    have h1 : ∑ k ∈ W_late, costTerm p w i j k ≤ ∑ k ∈ W_late, w k * p i j := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      exact costTerm_le_right p w i j k hpij_pos (hpik_pos k (Finset.mem_of_mem_filter k hk))
    let B := Finset.univ.filter
      (fun k => m k = i ∧ (r k : ℝ) ≤ f * (t : ℝ) ∧ f * (t : ℝ) ≤ nominalCompletion p m s k)
    have hsub : W_late ⊆ B := by
      intro k hk
      have hkW : k ∈ W := (Finset.mem_filter.mp hk).1
      have hnot : ¬ (s k + p i k ≤ f * (t : ℝ)) := (Finset.mem_filter.mp hk).2
      have hkj : k < j := (Finset.mem_filter.mp hkW).2.1
      have hmk : m k = i := (Finset.mem_filter.mp hkW).2.2.1
      have hrk_le_t : r k ≤ t := le_trans (hr (le_of_lt hkj)) hrjt
      have hrk_real : (r k : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr hrk_le_t
      have htf : (t : ℝ) ≤ f * (t : ℝ) := by
        have := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg t)
        linarith
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ k, hmk, le_trans hrk_real htf, ?_⟩
      unfold nominalCompletion
      rw [hmk]
      linarith
    have h2 : ∑ k ∈ W_late, w k * p i j ≤ ∑ k ∈ B, w k * p i j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => mul_nonneg (hw k) (le_of_lt hpij_pos))
    have h3 : ∑ k ∈ B, w k * p i j = betaF r p w m s f i t * p i j := by
      unfold betaF dualBeta
      rw [Finset.sum_mul]
    linarith
  rw [cost_eq_base_add_sum, hsplit]
  linarith

private lemma coeff_bound (c a f rj t pij : ℝ)
    (hc : 0 < c) (hf : 1 ≤ f) (hrj : 0 ≤ rj) (hrjt : rj ≤ t) (_ht : 0 ≤ t) (hpij : 0 ≤ pij)
    (h₁ : 2 * (2 + c) ≤ a * f) (h₂ : 1 / c ≤ f * (a - 1)) :
    (1 + 1 / c) * max rj (c * pij) + pij + (f * t - rj) ≤
      a * f * ((t + 1 / 2) + pij / 2) := by
  have hmax : max rj (c * pij) ≤ rj + c * pij :=
    max_le (le_add_of_nonneg_right (mul_nonneg (le_of_lt hc) hpij))
      (le_add_of_nonneg_left hrj)
  have h1c_pos : 0 ≤ 1 + 1 / c := by positivity
  have hmul_max : (1 + 1 / c) * max rj (c * pij) ≤ (1 + 1 / c) * (rj + c * pij) :=
    mul_le_mul_of_nonneg_left hmax h1c_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have h_expand : (1 + 1 / c) * (rj + c * pij) = rj + (1 / c) * rj + (1 + c) * pij := by
    calc (1 + 1 / c) * (rj + c * pij)
        = rj + (1 / c) * rj + (c + (1 / c) * c) * pij := by ring
      _ = rj + (1 / c) * rj + (c + 1) * pij := by
        rw [one_div_mul_cancel hc_ne]
      _ = rj + (1 / c) * rj + (1 + c) * pij := by ring
  have h_step1 : (1 + 1 / c) * max rj (c * pij) + pij + (f * t - rj) ≤
      (1 / c) * rj + f * t + (2 + c) * pij := by
    linarith
  have hrj_t : (1 / c) * rj ≤ (1 / c) * (t + 1 / 2) := by
    refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h1c_le : (1 / c) * (t + 1 / 2) ≤ (f * (a - 1)) * (t + 1 / 2) :=
    mul_le_mul_of_nonneg_right h₂ (by linarith)
  have hft_le : f * t ≤ f * (t + 1 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpij_le : (2 + c) * pij ≤ (a * f / 2) * pij := by
    refine mul_le_mul_of_nonneg_right (by linarith) hpij
  linarith

end Lemma7Helper

open Lemma7Helper

theorem solution {M : Type*} [Fintype M] [Nonempty M] {n : ℕ}
    (elig : M → Fin n → Prop) (_hElig : ∀ j, ∃ i, elig i j)
    (r : Fin n → ℕ) (hr : Monotone r)
    (p : M → Fin n → ℝ) (hp : ∀ i j, elig i j → 1 ≤ p i j)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (c a b f : ℝ) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hf : 1 ≤ f)
    (h₁ : 2 * (2 + c) ≤ a * f) (h₂ : 1 / c ≤ f * (a - 1)) (h₃ : b ≤ a * f)
    (m : Fin n → M) (s : Fin n → ℝ) (hG : IsGreedy c r p w elig m s) :
    IsFeasibleD elig r p w (fun j => alphaF c r p w m s f j / a)
      (fun i t => betaF r p w m s f i t / b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i t
    exact div_nonneg (betaF_nonneg r p w hw m s f i t) (le_of_lt hb)
  · intro i
    exact summable_betaF_div r p w m s f b hf i
  · intro i j t helig hrjt
    have hpij_one : 1 ≤ p i j := hp i j helig
    have hpij_pos : 0 < p i j := by linarith
    have haf_pos : 0 < a * f := mul_pos ha (by linarith)
    have h_assign : dualAlpha c r p w m s j ≤ cost c r p w m s j i :=
      (hG.1 j).2 i helig
    have h_cost := cost_le_bound elig r hr p hp w hw c f hf m s hG i j t helig hrjt
    have h_coeff := coeff_bound c a f (r j : ℝ) (t : ℝ) (p i j) hc hf
      (Nat.cast_nonneg (r j)) (Nat.cast_le.mpr hrjt) (Nat.cast_nonneg t)
      (le_of_lt hpij_pos) h₁ h₂
    have h_w_coeff : w j * ((1 + 1 / c) * modRelease c r p i j + p i j + (f * (t : ℝ) - (r j : ℝ))) ≤
        w j * (a * f * (((t : ℝ) + 1 / 2) + p i j / 2)) :=
      mul_le_mul_of_nonneg_left h_coeff (hw j)
    have h_alpha_le : dualAlpha c r p w m s j ≤
        a * f * w j * (((t : ℝ) + 1 / 2) + p i j / 2) + betaF r p w m s f i t * p i j := by
      linarith
    have h_div : dualAlpha c r p w m s j / (a * f * p i j) ≤
        (a * f * w j * (((t : ℝ) + 1 / 2) + p i j / 2) + betaF r p w m s f i t * p i j) /
          (a * f * p i j) :=
      div_le_div_of_nonneg_right h_alpha_le (le_of_lt (mul_pos haf_pos hpij_pos))
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hf_ne : f ≠ 0 := by linarith
    have hpij_ne : p i j ≠ 0 := ne_of_gt hpij_pos
    have h_lhs : (alphaF c r p w m s f j / a) / p i j =
        dualAlpha c r p w m s j / (a * f * p i j) := by
      unfold alphaF
      field_simp
    have h_rhs : (a * f * w j * (((t : ℝ) + 1 / 2) + p i j / 2) + betaF r p w m s f i t * p i j) /
          (a * f * p i j) =
        betaF r p w m s f i t / (a * f) + w j * (((t : ℝ) + 1 / 2) / p i j + 1 / 2) := by
      field_simp
      ring
    have h_beta_div : betaF r p w m s f i t / (a * f) ≤ betaF r p w m s f i t / b :=
      div_le_div_of_nonneg_left (betaF_nonneg r p w hw m s f i t) hb h₃
    linarith
