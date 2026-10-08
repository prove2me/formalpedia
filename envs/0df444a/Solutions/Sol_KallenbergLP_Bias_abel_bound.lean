-- Prove2me | solution 1 for KallenbergLP.Bias.abel_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:12:42.797012+00:00
-- url     : https://prove2.me/submissions/450669c5-2038-4c53-9b41-1c0552d209ee

import Definitions.Def_KallenbergLP_Bias_Criteria

open Filter


namespace KallenbergLP.Bias

set_option linter.unusedSectionVars false

lemma kb_partial_identity (d : ℕ → ℝ) (β : ℝ) (T : ℕ) :
    ∑ n ∈ Finset.range T, β ^ n * d n =
      (1 - β) * ∑ n ∈ Finset.range T, β ^ n * (∑ k ∈ Finset.range (n + 1), d k)
        + β ^ T * ∑ k ∈ Finset.range T, d k := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ (fun k => d k) T]
    ring

lemma kb_partial_bound (d : ℕ → ℝ) (β K : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hD : ∀ T, ∑ k ∈ Finset.range T, d k ≤ K) (T : ℕ) :
    ∑ n ∈ Finset.range T, β ^ n * d n ≤ K := by
  rw [kb_partial_identity]
  have h1 : (1 - β) * ∑ n ∈ Finset.range T, β ^ n * (∑ k ∈ Finset.range (n + 1), d k)
      ≤ (1 - β) * ∑ n ∈ Finset.range T, β ^ n * K := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Finset.sum_le_sum
    intro n _
    exact mul_le_mul_of_nonneg_left (hD _) (pow_nonneg hβ0 _)
  have h2 : β ^ T * ∑ k ∈ Finset.range T, d k ≤ β ^ T * K :=
    mul_le_mul_of_nonneg_left (hD _) (pow_nonneg hβ0 _)
  have h3 : (1 - β) * ∑ n ∈ Finset.range T, β ^ n * K + β ^ T * K = K := by
    rw [← Finset.sum_mul]
    have := geom_sum_mul β T
    linear_combination (-K) * this
  linarith

lemma kb_abel_core (r : ℕ → ℝ) (C : ℝ) (hC : ∀ n, |r n| ≤ C) :
    limsup (fun β : ℝ => (1 - β) * ∑' n : ℕ, β ^ n * r n) (nhdsWithin 1 (Set.Iio 1)) ≤
      limsup (fun T : ℕ => (T : ℝ)⁻¹ * ∑ n ∈ Finset.range T, r n) atTop := by
  set a : ℕ → ℝ := fun T => (T : ℝ)⁻¹ * ∑ n ∈ Finset.range T, r n with ha
  set L := limsup a atTop
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hsum_abs : ∀ T : ℕ, |∑ n ∈ Finset.range T, r n| ≤ T * C := by
    intro T
    calc |∑ n ∈ Finset.range T, r n| ≤ ∑ n ∈ Finset.range T, |r n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range T, C := Finset.sum_le_sum (fun n _ => hC n)
      _ = T * C := by simp
  have hab : ∀ T, |a T| ≤ C := by
    intro T
    rcases Nat.eq_zero_or_pos T with h | h
    · subst h; simp [ha, hC0]
    · have hT : (0:ℝ) < T := by exact_mod_cast h
      simp only [ha, abs_mul, abs_inv, Nat.abs_cast]
      rw [inv_mul_le_iff₀ hT]
      exact hsum_abs T
  have hbddA : IsBoundedUnder (· ≤ ·) atTop a :=
    ⟨C, Filter.eventually_map.2 (Filter.Eventually.of_forall (fun (T : ℕ) => (abs_le.1 (hab T)).2))⟩
  -- summability
  have hsumm : ∀ β : ℝ, 0 ≤ β → β < 1 → ∀ c : ℝ, ∀ g : ℕ → ℝ, (∀ n, |g n| ≤ c) →
      Summable (fun n => β ^ n * g n) := by
    intro β h0 h1 c g hg
    apply Summable.of_norm_bounded (g := fun n => c * β ^ n)
    · exact (summable_geometric_of_lt_one h0 h1).mul_left c
    · intro n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 n), mul_comm]
      exact mul_le_mul_of_nonneg_right (hg n) (pow_nonneg h0 n)
  -- lower bound for coboundedness
  have hlow : ∀ β : ℝ, 0 ≤ β → β < 1 → -C ≤ (1 - β) * ∑' n : ℕ, β ^ n * r n := by
    intro β h0 h1
    have hs1 := hsumm β h0 h1 C r hC
    have hs2 : Summable (fun n : ℕ => β ^ n * (-C)) :=
      (summable_geometric_of_lt_one h0 h1).mul_right _
    have : ∑' n : ℕ, β ^ n * (-C) ≤ ∑' n : ℕ, β ^ n * r n := by
      apply hs2.tsum_le_tsum _ hs1
      intro n
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hC n)).1]) (pow_nonneg h0 n)
    rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1] at this
    have hpos : 0 < 1 - β := by linarith
    have := mul_le_mul_of_nonneg_left this hpos.le
    rw [show (1 - β) * ((1 - β)⁻¹ * -C) = -C by field_simp] at this
    exact this
  have hev01 : ∀ᶠ β in nhdsWithin (1:ℝ) (Set.Iio 1), β ∈ Set.Ioo (0:ℝ) 1 :=
    Ioo_mem_nhdsLT (by norm_num)
  have hcob : IsCoboundedUnder (· ≤ ·) (nhdsWithin (1:ℝ) (Set.Iio 1))
      (fun β : ℝ => (1 - β) * ∑' n : ℕ, β ^ n * r n) := by
    exact isCoboundedUnder_le_of_eventually_le (nhdsWithin (1:ℝ) (Set.Iio 1)) (x := -C)
      (by filter_upwards [hev01] with β hβ; exact hlow β hβ.1.le hβ.2)
  have key : ∀ ε > 0, limsup (fun β : ℝ => (1 - β) * ∑' n : ℕ, β ^ n * r n)
      (nhdsWithin 1 (Set.Iio 1)) ≤ L + 2 * ε := by
    intro ε hε
    have hev : ∀ᶠ T in atTop, a T < L + ε :=
      eventually_lt_of_limsup_lt (by linarith) hbddA
    obtain ⟨T0, hT0⟩ := eventually_atTop.1 hev
    set L' := L + ε
    set d : ℕ → ℝ := fun n => r n - L' with hd
    set K : ℝ := T0 * (C + |L'|)
    have hK0 : 0 ≤ K := by positivity
    have hD : ∀ T, ∑ k ∈ Finset.range T, d k ≤ K := by
      intro T
      have hsplit : ∑ k ∈ Finset.range T, d k = ∑ k ∈ Finset.range T, r k - T * L' := by
        simp [hd, Finset.sum_sub_distrib]
      rcases lt_or_ge T T0 with hT | hT
      · calc ∑ k ∈ Finset.range T, d k ≤ ∑ k ∈ Finset.range T, |d k| := by
              exact le_trans (le_abs_self _) (Finset.abs_sum_le_sum_abs _ _)
          _ ≤ ∑ k ∈ Finset.range T, (C + |L'|) := by
              apply Finset.sum_le_sum; intro k _
              simp only [hd]
              exact le_trans (abs_sub _ _) (add_le_add (hC k) le_rfl)
          _ = T * (C + |L'|) := by simp; ring
          _ ≤ K := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast hT.le
      · rcases Nat.eq_zero_or_pos T with h0 | h0
        · subst h0; simp [hK0]
        · have hTpos : (0:ℝ) < T := by exact_mod_cast h0
          have := hT0 T hT
          simp only [ha] at this
          rw [inv_mul_lt_iff₀ hTpos] at this
          rw [hsplit]; nlinarith
    have hbound : ∀ β : ℝ, 0 < β → β < 1 →
        (1 - β) * ∑' n : ℕ, β ^ n * r n ≤ (1 - β) * K + L' := by
      intro β h0 h1
      have hdb : ∀ n, |d n| ≤ C + |L'| := fun n => le_trans (abs_sub _ _) (add_le_add (hC n) le_rfl)
      have hs := hsumm β h0.le h1 _ d hdb
      have hS : ∑' n : ℕ, β ^ n * d n ≤ K :=
        le_of_tendsto' hs.hasSum.tendsto_sum_nat
          (fun T => kb_partial_bound d β K h0.le h1.le hD T)
      have hg : Summable (fun n : ℕ => β ^ n * L') :=
        (summable_geometric_of_lt_one h0.le h1).mul_right _
      have heq : ∑' n : ℕ, β ^ n * r n = ∑' n : ℕ, β ^ n * d n + L' * (1 - β)⁻¹ := by
        rw [← tsum_geometric_of_lt_one h0.le h1, ← tsum_mul_left, ← hs.tsum_add (by
          simpa [mul_comm] using hg)]
        congr 1; ext n; simp only [hd]; ring
      rw [heq]
      have hpos : 0 < 1 - β := by linarith
      rw [mul_add, show (1 - β) * (L' * (1 - β)⁻¹) = L' by field_simp]
      have := mul_le_mul_of_nonneg_left hS hpos.le
      linarith
    apply limsup_le_of_le hcob
    have hδ : (0:ℝ) < ε / (K + 1) := by positivity
    have hmem : Set.Ioo (max 0 (1 - ε / (K + 1))) 1 ∈ nhdsWithin (1:ℝ) (Set.Iio 1) :=
      Ioo_mem_nhdsLT (by
        rw [max_lt_iff]; constructor <;> linarith)
    filter_upwards [hmem] with β hβ
    have h0 : 0 < β := lt_of_le_of_lt (le_max_left _ _) hβ.1
    have h1 : 1 - ε / (K + 1) < β := lt_of_le_of_lt (le_max_right _ _) hβ.1
    have := hbound β h0 hβ.2
    have hk : (1 - β) * K ≤ ε := by
      have : 1 - β < ε / (K + 1) := by linarith
      have h2 : (1 - β) * (K + 1) ≤ ε := by
        rw [lt_div_iff₀ (by linarith)] at this; linarith
      nlinarith [hβ.2]
    simp only [L'] at this
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have := key (ε / 2) (by positivity)
  linarith


variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

def kbExt {n : ℕ} (h : History N α n) (a : α) (j : Fin N) : History N α (n + 1) where
  states := Fin.snoc h.states j
  chosen := Fin.snoc h.chosen a

def kbEquiv (n : ℕ) : History N α (n + 1) ≃ History N α n × α × Fin N where
  toFun h' := (⟨fun i => h'.states i.castSucc, fun i => h'.chosen i.castSucc⟩,
    h'.chosen (Fin.last n), h'.states (Fin.last (n + 1)))
  invFun p := kbExt p.1 p.2.1 p.2.2
  left_inv := by
    intro h'
    cases h' with
    | mk s c =>
      simp only [kbExt]
      congr 1
      · exact Fin.snoc_init_self s
      · exact Fin.snoc_init_self c
  right_inv := by
    rintro ⟨⟨s, c⟩, a, j⟩
    simp [kbExt]

lemma kb_prefix_cs {n : ℕ} (h : History N α n) (a : α) (j : Fin N) (k : Fin n) :
    (kbExt h a j).prefix k.castSucc = h.prefix k := by
  cases h with
  | mk s c =>
    simp only [History.prefix, kbExt]
    congr 1
    · funext x
      have : (⟨x.val, by omega⟩ : Fin (n + 1 + 1)) = Fin.castSucc ⟨x.val, by omega⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    · funext x
      have : (⟨x.val, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨x.val, by omega⟩ := rfl
      rw [this, Fin.snoc_castSucc]

lemma kb_prefix_last {n : ℕ} (h : History N α n) (a : α) (j : Fin N) :
    (kbExt h a j).prefix (Fin.last n) = h := by
  cases h with
  | mk s c =>
    simp only [History.prefix, kbExt]
    congr 1
    · funext x
      have : (⟨x.val, by omega⟩ : Fin (n + 1 + 1)) = Fin.castSucc x := rfl
      rw [this, Fin.snoc_castSucc]
    · funext x
      have : (⟨x.val, by omega⟩ : Fin (n + 1)) = Fin.castSucc x := rfl
      rw [this, Fin.snoc_castSucc]

lemma kb_hp_ext (M : MDP N α) (R : Policy M) (i : Fin N) {n : ℕ}
    (h : History N α n) (a : α) (j : Fin N) :
    historyProb M R i (n + 1) (kbExt h a j) =
      historyProb M R i n h * (R.choose n h a * M.transition h.last a j) := by
  unfold historyProb
  rw [Fin.prod_univ_castSucc, ← mul_assoc]
  congr 1
  · congr 1
    · apply Finset.prod_congr rfl
      intro k _
      rw [kb_prefix_cs]
      have e1 : (kbExt h a j).chosen k.castSucc = h.chosen k := by
        simp [kbExt]
      have e2 : (kbExt h a j).states ⟨k.val, by omega⟩ = h.states ⟨k.val, by omega⟩ := by
        have : (⟨k.val, by omega⟩ : Fin (n + 1 + 1)) = Fin.castSucc ⟨k.val, by omega⟩ := rfl
        simp only [kbExt]; rw [this, Fin.snoc_castSucc]
      have e3 : (kbExt h a j).states ⟨k.val + 1, by omega⟩ = h.states ⟨k.val + 1, by omega⟩ := by
        have : (⟨k.val + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.castSucc ⟨k.val + 1, by omega⟩ := rfl
        simp only [kbExt]; rw [this, Fin.snoc_castSucc]
      simp only [Fin.coe_castSucc] at e2 e3 ⊢
      rw [e1, e2, e3]
  · rw [kb_prefix_last]
    have e1 : (kbExt h a j).chosen (Fin.last n) = a := by simp [kbExt]
    have e2 : (kbExt h a j).states ⟨(Fin.last n).val, by simp⟩ = h.last := by
      have : (⟨(Fin.last n).val, by simp⟩ : Fin (n + 1 + 1)) = Fin.castSucc (Fin.last n) := rfl
      simp only [kbExt]; rw [this, Fin.snoc_castSucc]; rfl
    have e3 : (kbExt h a j).states ⟨(Fin.last n).val + 1, by simp⟩ = j := by
      have : (⟨(Fin.last n).val + 1, by simp⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) := rfl
      simp only [kbExt]; rw [this, Fin.snoc_last]
    rw [e1, e2, e3]
    rfl

lemma kb_hp_nonneg (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) (h : History N α n) :
    0 ≤ historyProb M R i n h := by
  unfold historyProb
  apply mul_nonneg
  · split_ifs <;> norm_num
  · apply Finset.prod_nonneg
    intro k _
    by_cases ha : h.chosen k ∈ M.actions (h.prefix k).last
    · exact mul_nonneg (R.choose_nonneg _ _ _) (M.transition_nonneg _ _ _ ha)
    · rw [R.choose_outside _ _ _ ha]; simp

def kbEquiv0 : History N α 0 ≃ Fin N where
  toFun h := h.states 0
  invFun j := ⟨fun _ => j, Fin.elim0⟩
  left_inv := by
    intro h
    cases h with
    | mk s c =>
      simp only
      congr 1
      · funext x; exact congrArg s (Fin.ext (by have := x.isLt; simp))
      · funext x; exact Fin.elim0 x
  right_inv := by intro j; rfl

lemma kb_hp_sum (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) :
    ∑ h : History N α n, historyProb M R i n h = 1 := by
  induction n with
  | zero =>
    rw [← (kbEquiv0 (N := N) (α := α)).symm.sum_comp]
    have hx : ∀ x : Fin N, historyProb M R i 0 ((kbEquiv0 (N := N) (α := α)).symm x)
        = if x = i then 1 else 0 := by
      intro x
      unfold historyProb
      rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      rfl
    simp only [hx]
    rw [Fintype.sum_eq_single i (fun x hx => if_neg hx)]; exact if_pos rfl
  | succ n ih =>
    rw [← (kbEquiv n).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    have hk : ∀ (h : History N α n) (a : α) (j : Fin N),
        historyProb M R i (n + 1) ((kbEquiv n).symm (h, a, j)) =
          historyProb M R i n h * (R.choose n h a * M.transition h.last a j) := by
      intro h a j
      exact kb_hp_ext M R i h a j
    simp only [hk]
    rw [← ih]
    apply Finset.sum_congr rfl
    intro h _
    have : ∀ a : α, ∑ j : Fin N, historyProb M R i n h * (R.choose n h a * M.transition h.last a j)
        = historyProb M R i n h * R.choose n h a := by
      intro a
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      by_cases ha : a ∈ M.actions h.last
      · rw [M.transition_sum_one _ _ ha, mul_one]
      · rw [R.choose_outside _ _ _ ha]; simp
    simp only [this]
    rw [← Finset.mul_sum, R.choose_sum_one, mul_one]

lemma kb_occ_nonneg (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α) (n : ℕ) :
    0 ≤ occupancy M R i j a n := by
  unfold occupancy
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact mul_nonneg (kb_hp_nonneg M R i n h) (R.choose_nonneg _ _ _)
  · exact le_rfl

lemma kb_occ_sum (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) :
    ∑ j : Fin N, ∑ a : α, occupancy M R i j a n = 1 := by
  unfold occupancy
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (γ := Fin N) (f := fun j h => _)]
  rw [Finset.sum_comm]
  have : ∀ h : History N α n, ∀ a : α,
      ∑ j : Fin N, (if h.last = j then historyProb M R i n h * R.choose n h a else 0)
        = historyProb M R i n h * R.choose n h a := by
    intro h a
    rw [Finset.sum_ite_eq]; simp
  simp only [this]
  rw [← kb_hp_sum M R i n]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_sum, R.choose_sum_one, mul_one]

lemma kb_period_bound (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) :
    |periodReward M R i n| ≤ ∑ j : Fin N, ∑ a : α, |M.reward j a| := by
  set B := ∑ j : Fin N, ∑ a : α, |M.reward j a|
  have hB : ∀ j a, |M.reward j a| ≤ B := by
    intro j a
    calc |M.reward j a| ≤ ∑ a' : α, |M.reward j a'| :=
          Finset.single_le_sum (f := fun a' => |M.reward j a'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
      _ ≤ B := Finset.single_le_sum (f := fun j' => ∑ a' : α, |M.reward j' a'|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ j)
  unfold periodReward
  calc |∑ j : Fin N, ∑ a : α, occupancy M R i j a n * M.reward j a|
      ≤ ∑ j : Fin N, |∑ a : α, occupancy M R i j a n * M.reward j a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, ∑ a : α, |occupancy M R i j a n * M.reward j a| :=
        Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j : Fin N, ∑ a : α, occupancy M R i j a n * B := by
        apply Finset.sum_le_sum; intro j _; apply Finset.sum_le_sum; intro a _
        rw [abs_mul, abs_of_nonneg (kb_occ_nonneg M R i j a n)]
        exact mul_le_mul_of_nonneg_left (hB j a) (kb_occ_nonneg M R i j a n)
    _ = B := by
        simp only [← Finset.sum_mul]
        rw [kb_occ_sum, one_mul]


theorem abel_bound_core {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (R : Policy M) (i : Fin N) :
    limsup (fun β : ℝ => (1 - β) * discountedReward M R i β)
      (nhdsWithin 1 (Set.Iio 1)) ≤ upperAverageReward M R i :=
  kb_abel_core (periodReward M R i) _ (kb_period_bound M R i)

end KallenbergLP.Bias

open KallenbergLP.Bias
open Filter

theorem solution {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (R : Policy M) (i : Fin N) :
    limsup (fun β : ℝ => (1 - β) * discountedReward M R i β)
      (nhdsWithin 1 (Set.Iio 1)) ≤ upperAverageReward M R i := by
  exact abel_bound_core M R i
