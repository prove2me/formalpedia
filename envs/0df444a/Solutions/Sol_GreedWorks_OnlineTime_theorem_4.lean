-- Prove2me | solution 1 for GreedWorks.OnlineTime.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:20:01.461345+00:00
-- url     : https://prove2.me/submissions/65257b92-3a46-4c5b-a9e4-20a65cd21e87

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_Greedy
import Definitions.Def_GreedWorks_OnlineTime_StochasticGreedy
import Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP
import Theorems.Thm_GreedWorks_OnlineTime_lemma_6
import Theorems.Thm_GreedWorks_OnlineTime_lemma_7
import Theorems.Thm_GreedWorks_OnlineTime_lemma_8
import Theorems.Thm_GreedWorks_OnlineTime_eq_13

open MeasureTheory GreedWorks.OnlineTime

set_option linter.unusedSectionVars false

namespace GW4Sol

open Classical

variable {M : Type*} [Fintype M] {n : ℕ}

/-! ## Time scaling of the deterministic greedy schedule -/

lemma ratio_scale {K : ℝ} (hK : 0 < K) (a b x y : ℝ) :
    a / (K * x) ≤ b / (K * y) ↔ a / x ≤ b / y := by
  rw [mul_comm K x, mul_comm K y, ← div_div, ← div_div, div_le_div_iff_of_pos_right hK]

lemma ratio_scale_lt {K : ℝ} (hK : 0 < K) (a b x y : ℝ) :
    a / (K * x) < b / (K * y) ↔ a / x < b / y := by
  rw [mul_comm K x, mul_comm K y, ← div_div, ← div_div, div_lt_div_iff_of_pos_right hK]

lemma modRelease_scale (K : ℕ) (hK : 0 < (K : ℝ)) (c : ℝ) (r : Fin n → ℕ)
    (p : M → Fin n → ℝ) (i : M) (j : Fin n) :
    modRelease c (fun j => K * r j) (fun i j => (K : ℝ) * p i j) i j =
      K * modRelease c r p i j := by
  unfold modRelease
  push_cast
  rw [mul_max_of_nonneg _ _ hK.le]
  congr 1; ring

lemma waiting_scale (K : ℕ) (hK : 0 < (K : ℝ)) (r : Fin n → ℕ) (m : Fin n → M)
    (s : Fin n → ℝ) (i : M) (j : Fin n) :
    waiting (fun j => K * r j) m (fun j => (K : ℝ) * s j) i j = waiting r m s i j := by
  unfold waiting
  apply Finset.filter_congr
  intro k _
  push_cast
  rw [mul_le_mul_iff_of_pos_left hK]

lemma cost_scale (K : ℕ) (hK : 0 < (K : ℝ)) (c : ℝ) (r : Fin n → ℕ)
    (p : M → Fin n → ℝ) (w : Fin n → ℝ) (m : Fin n → M) (s : Fin n → ℝ) (j : Fin n) (i : M) :
    cost c (fun j => K * r j) (fun i j => (K : ℝ) * p i j) w m (fun j => (K : ℝ) * s j) j i =
      K * cost c r p w m s j i := by
  unfold cost
  rw [waiting_scale K hK, modRelease_scale K hK]
  have h1 : (waiting r m s i j).filter (fun k => w j / ((K : ℝ) * p i j) ≤ w k / ((K : ℝ) * p i k))
      = (waiting r m s i j).filter (fun k => w j / p i j ≤ w k / p i k) :=
    Finset.filter_congr (fun k _ => ratio_scale hK _ _ _ _)
  have h2 : (waiting r m s i j).filter (fun k => w k / ((K : ℝ) * p i k) < w j / ((K : ℝ) * p i j))
      = (waiting r m s i j).filter (fun k => w k / p i k < w j / p i j) :=
    Finset.filter_congr (fun k _ => ratio_scale_lt hK _ _ _ _)
  rw [h1, h2, ← Finset.mul_sum]
  have h3 : ∑ k ∈ (waiting r m s i j).filter (fun k => w k / p i k < w j / p i j),
      w k * ((K : ℝ) * p i j) =
      K * ∑ k ∈ (waiting r m s i j).filter (fun k => w k / p i k < w j / p i j),
        w k * p i j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [h3]; ring

lemma isGreedy_scale (K : ℕ) (hK : 0 < (K : ℝ)) {c : ℝ} {r : Fin n → ℕ}
    {p : M → Fin n → ℝ} {w : Fin n → ℝ} {elig : M → Fin n → Prop} {m : Fin n → M}
    {s : Fin n → ℝ} (hG : IsGreedy c r p w elig m s) :
    IsGreedy c (fun j => K * r j) (fun i j => (K : ℝ) * p i j) w elig m
      (fun j => (K : ℝ) * s j) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨(h1 j).1, fun i hi => ?_⟩
    rw [cost_scale K hK, cost_scale K hK]
    exact mul_le_mul_of_nonneg_left ((h1 j).2 i hi) hK.le
  · intro k
    rw [modRelease_scale K hK]
    exact mul_le_mul_of_nonneg_left (h2 k) hK.le
  · intro j k hjk hm
    have := h3 j k hjk hm
    rw [Set.Ico_disjoint_Ico] at this ⊢
    rw [← mul_add, ← mul_add, ← mul_min_of_nonneg _ _ hK.le, ← mul_max_of_nonneg _ _ hK.le]
    exact mul_le_mul_of_nonneg_left this hK.le
  · intro k t ht1 ht2
    rw [modRelease_scale K hK] at ht1
    obtain ⟨l, hl1, hl2, hl3⟩ := h4 k (t / K)
      (by rw [le_div_iff₀ hK, mul_comm]; exact ht1)
      (by rw [div_lt_iff₀ hK, mul_comm]; exact ht2)
    refine ⟨l, hl1, ?_, ?_⟩
    · have := (le_div_iff₀ hK).mp hl2; linarith
    · have := (div_lt_iff₀ hK).mp hl3; linarith
  · intro j k hm ha hb
    rw [modRelease_scale K hK] at ha
    have := h5 j k hm (le_of_mul_le_mul_left ha hK) (lt_of_mul_lt_mul_left hb hK.le)
    exact (ratio_scale hK _ _ _ _).mpr this

lemma nominalCompletion_scale (K : ℕ) (p : M → Fin n → ℝ) (m : Fin n → M) (s : Fin n → ℝ)
    (j : Fin n) :
    nominalCompletion (fun i j => (K : ℝ) * p i j) m (fun j => (K : ℝ) * s j) j =
      K * nominalCompletion p m s j := by
  unfold nominalCompletion; ring

lemma nominalValue_scale (K : ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ) (m : Fin n → M)
    (s : Fin n → ℝ) :
    nominalValue (fun i j => (K : ℝ) * p i j) w m (fun j => (K : ℝ) * s j) =
      K * nominalValue p w m s := by
  unfold nominalValue
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [nominalCompletion_scale]; ring

/-! ## Weak duality for (P_r) / (D_r) -/

lemma weak_duality (elig : M → Fin n → Prop) (r : Fin n → ℕ) (μ : M → Fin n → ℝ)
    (w : Fin n → ℝ) (α : Fin n → ℝ) (β : M → ℕ → ℝ) (y : M → Fin n → ℕ → ℝ)
    (hD : IsFeasibleD elig r μ w α β) (hP : IsFeasibleP elig r μ y) :
    ∑ j, α j - ∑ i, ∑' s, β i s ≤ valueP elig μ w y := by
  classical
  obtain ⟨hβ0, hβs, hc⟩ := hD
  obtain ⟨hy0, hyE, hyR, hyS, hyS2, hy1, hy3⟩ := hP
  have hyle : ∀ i j s, y i j s ≤ 1 := fun i j s =>
    le_trans (Finset.single_le_sum (fun k _ => hy0 i k s) (Finset.mem_univ j)) (hy1 i s)
  have hyβS : ∀ i j, Summable (fun s => y i j s * β i s) := fun i j =>
    Summable.of_nonneg_of_le (fun s => mul_nonneg (hy0 i j s) (hβ0 i s))
      (fun s => by
        have := mul_le_mul_of_nonneg_right (hyle i j s) (hβ0 i s)
        linarith) (hβs i)
  have hCS : ∀ i j, Summable (fun s : ℕ => y i j s / μ i j * ((s : ℝ) + 1 / 2) + y i j s / 2) :=
    fun i j => by
      have h1 : Summable (fun s : ℕ => (1 / μ i j) * (((s : ℝ) + 1 / 2) * y i j s)) :=
        (hyS2 i j).mul_left _
      have h2 : Summable (fun s : ℕ => (1 / 2 : ℝ) * y i j s) := (hyS i j).mul_left _
      refine (h1.add h2).congr (fun s => ?_)
      ring
  -- per job bound
  have hjob : ∀ j, α j ≤ ∑ i ∈ Finset.univ.filter (fun i => elig i j),
      ∑' s, y i j s * β i s + w j * completionP elig μ y j := by
    intro j
    have hα : α j = ∑ i ∈ Finset.univ.filter (fun i => elig i j),
        ∑' s, y i j s * (α j / μ i j) := by
      have := hy3 j
      calc α j = (∑ i ∈ Finset.univ.filter (fun i => elig i j), (∑' s, y i j s) / μ i j) * α j :=
            by rw [this, one_mul]
        _ = _ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [tsum_mul_right]; ring
    rw [hα, completionP, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : elig i j := (Finset.mem_filter.mp hi).2
    rw [← tsum_mul_left, ← (hyβS i j).tsum_add ((hCS i j).mul_left _)]
    refine (hyS i j).mul_right _ |>.tsum_le_tsum (fun s => ?_) ((hyβS i j).add ((hCS i j).mul_left _))
    by_cases hs : r j ≤ s
    · have := mul_le_mul_of_nonneg_left (hc i j s hi' hs) (hy0 i j s)
      have e : y i j s * (β i s + w j * (((s : ℝ) + 1 / 2) / μ i j + 1 / 2)) =
          y i j s * β i s + w j * (y i j s / μ i j * ((s : ℝ) + 1 / 2) + y i j s / 2) := by ring
      linarith
    · rw [hyR i j s (Nat.lt_of_not_le hs)]; simp
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hjob j)
  rw [Finset.sum_add_distrib] at hsum
  -- the β part
  have hB : ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => elig i j), ∑' s, y i j s * β i s ≤
      ∑ i, ∑' s, β i s := by
    calc _ ≤ ∑ j : Fin n, ∑ i : M, ∑' s, y i j s * β i s := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => tsum_nonneg (fun s => mul_nonneg (hy0 i j s) (hβ0 i s)))
      _ = ∑ i : M, ∑' s, ∑ j : Fin n, y i j s * β i s := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Summable.tsum_finsetSum (fun j _ => hyβS i j)]
      _ ≤ ∑ i, ∑' s, β i s := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          refine (summable_sum (fun j _ => hyβS i j)).tsum_le_tsum (fun s => ?_) (hβs i)
          rw [← Finset.sum_mul]
          have := mul_le_mul_of_nonneg_right (hy1 i s) (hβ0 i s)
          linarith
  unfold valueP
  linarith


/-! ## Scaling a dual solution of the time-scaled instance back to unit slots -/

lemma sum_range_affine (c : ℝ) (N : ℕ) :
    ∑ u ∈ Finset.range N, ((c + u) + 1 / 2 : ℝ) = N * c + (N : ℝ) ^ 2 / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma downscale_feasible (elig : M → Fin n → Prop) (r : Fin n → ℕ) (μ : M → Fin n → ℝ)
    (w : Fin n → ℝ) (A : Fin n → ℝ) (B : M → ℕ → ℝ) (K : ℕ) (hK : 0 < K)
    (hμ : ∀ i j, elig i j → 0 < μ i j)
    (hD : IsFeasibleD elig (fun j => K * r j) (fun i j => (K : ℝ) * μ i j) w A B) :
    IsFeasibleD elig r μ w (fun j => A j / K)
      (fun i s => (∑ u ∈ Finset.range K, B i (K * s + u)) / K) := by
  obtain ⟨hβ0, hβs, hc⟩ := hD
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨fun i s => div_nonneg (Finset.sum_nonneg fun u _ => hβ0 _ _) hK'.le, fun i => ?_, ?_⟩
  · refine (summable_sum (fun u _ => (hβs i).comp_injective ?_)).div_const _
    intro a b h
    have h' : K * a + u = K * b + u := h
    exact Nat.eq_of_mul_eq_mul_left hK (by omega)
  · intro i j s hij hs
    have hμ' := hμ i j hij
    have key := Finset.sum_le_sum (fun u (_ : u ∈ Finset.range K) =>
      hc i j (K * s + u) hij (le_trans (Nat.mul_le_mul_left K hs) (Nat.le_add_right _ _)))
    simp only at key
    have e1 : ∑ u ∈ Finset.range K, A j / ((K : ℝ) * μ i j) = K * (A j / ((K : ℝ) * μ i j)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e2 : ∑ u ∈ Finset.range K, (B i (K * s + u) + w j * ((((K * s + u : ℕ) : ℝ) + 1 / 2) /
        ((K : ℝ) * μ i j) + 1 / 2)) = ∑ u ∈ Finset.range K, B i (K * s + u) +
        K * (w j * (((s : ℝ) + 1 / 2) / μ i j + 1 / 2)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
      have := sum_range_affine ((K : ℝ) * s) K
      push_cast
      rw [this]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [e1, e2] at key
    rw [div_div]
    have := div_le_div_of_nonneg_right key hK'.le
    calc A j / ((K : ℝ) * μ i j) = K * (A j / ((K : ℝ) * μ i j)) / K := by field_simp
      _ ≤ _ := this
      _ = _ := by field_simp

/-! ## The β-sum: counting slots -/

lemma count_le (f X : ℝ) (hf : 0 < f) (hX : 0 ≤ X) (T : ℕ) :
    ∑ t ∈ Finset.range T, (if f * t ≤ X then (1 : ℝ) else 0) ≤ X / f + 1 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_one]
  have hsub : (Finset.range T).filter (fun t : ℕ => f * t ≤ X) ⊆
      Finset.range (⌊X / f⌋₊ + 1) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    rw [le_div_iff₀ hf]; linarith [ht.2]
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  calc (((Finset.range T).filter (fun t : ℕ => f * t ≤ X)).card : ℝ)
      ≤ ((⌊X / f⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
    _ ≤ X / f + 1 := by push_cast; linarith [Nat.floor_le (div_nonneg hX hf.le)]

lemma betaF_sum_le (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (m : Fin n → M) (s : Fin n → ℝ) (f : ℝ) (hf : 0 < f)
    (hC : ∀ k, 0 ≤ nominalCompletion p m s k) (i : M) (T : ℕ) :
    ∑ t ∈ Finset.range T, betaF r p w m s f i t ≤
      ∑ k, (if m k = i then w k else 0) * (nominalCompletion p m s k / f + 1) := by
  have h1 : ∀ t : ℕ, betaF r p w m s f i t ≤ ∑ k, (if m k = i then w k else 0) *
      (if f * t ≤ nominalCompletion p m s k then 1 else 0) := by
    intro t
    unfold betaF dualBeta
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have := hw k
    split_ifs <;> simp_all
  calc _ ≤ ∑ t ∈ Finset.range T, ∑ k, (if m k = i then w k else 0) *
        (if f * t ≤ nominalCompletion p m s k then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun t _ => h1 t)
    _ = ∑ k, (if m k = i then w k else 0) * ∑ t ∈ Finset.range T,
        (if f * t ≤ nominalCompletion p m s k then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ _ := by
        refine Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
          (count_le f _ hf (hC k) T) ?_)
        split_ifs
        · exact hw k
        · exact le_rfl

lemma sum_range_reindex (g : ℕ → ℝ) (K N : ℕ) :
    ∑ s ∈ Finset.range N, ∑ u ∈ Finset.range K, g (K * s + u) =
      ∑ t ∈ Finset.range (K * N), g t := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]

/-! ## Deterministic bound: `ALG_P ≤ (7 + 11/51) z^{P_r}(y)` for every feasible `y` -/

lemma alg_le_LP (elig : M → Fin n → Prop) (hElig : ∀ j, ∃ i, elig i j) [Nonempty M]
    (r : Fin n → ℕ) (hr : Monotone r) (μ : M → Fin n → ℝ) (hμ : ∀ i j, elig i j → 1 ≤ μ i j)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) r μ w elig m s) (y : M → Fin n → ℕ → ℝ)
    (hP : IsFeasibleP elig r μ y) :
    nominalValue μ w m s ≤ 368 / 51 * valueP elig μ w y := by
  set V := nominalValue μ w m s with hV
  set W := ∑ k, w k with hW
  have hm : ∀ j, elig (m j) j := fun j => (hG.1 j).1
  have hs0 : ∀ j, 0 ≤ s j := fun j => le_trans (le_trans (Nat.cast_nonneg _) (le_max_left _ _))
    (hG.2.1 j)
  have hC0 : ∀ k, 0 ≤ nominalCompletion μ m s k := fun k => by
    unfold nominalCompletion; linarith [hs0 k, hμ _ _ (hm k)]
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun k _ => hw k)
  have hKbound : ∀ K : ℕ, 0 < K → V * (51 / 368) - 3 / 16 * W / K ≤ valueP elig μ w y := by
    intro K hK
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hG' := isGreedy_scale K hK' hG
    have hp' : ∀ i j, elig i j → 1 ≤ (K : ℝ) * μ i j := fun i j h =>
      one_le_mul_of_one_le_of_one_le hK1 (hμ i j h)
    have hr' : Monotone (fun j => K * r j) := fun a b h => Nat.mul_le_mul_left K (hr h)
    have h6 := lemma_6 elig hElig (fun j => K * r j) hr' (fun i j => (K : ℝ) * μ i j) hp' w hw
      (2 / 3) (by norm_num) m (fun j => (K : ℝ) * s j) hG'
    have h7 := lemma_7 elig hElig (fun j => K * r j) hr' (fun i j => (K : ℝ) * μ i j) hp' w hw
      (2 / 3) (32 / 23) (16 / 3) (23 / 6) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) m (fun j => (K : ℝ) * s j) hG'
    have hD := downscale_feasible elig r μ w _ _ K hK (fun i j h => by linarith [hμ i j h]) h7
    have hwd := weak_duality elig r μ w _ _ y hD hP
    rw [nominalValue_scale] at h6
    -- the α part
    have hα : V * (3 / 16) ≤ ∑ j, alphaF (2 / 3) (fun j => K * r j) (fun i j => (K : ℝ) * μ i j)
        w m (fun j => (K : ℝ) * s j) (23 / 6) j / (32 / 23) / K := by
      simp only [alphaF, dualAlpha]
      rw [← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div]
      rw [le_div_iff₀ hK']
      linarith
    -- the β part
    have hβi : ∀ i, ∑' t, (∑ u ∈ Finset.range K, betaF (fun j => K * r j)
        (fun i j => (K : ℝ) * μ i j) w m (fun j => (K : ℝ) * s j) (23 / 6) i (K * t + u) /
          (16 / 3)) / K ≤
        (∑ k, (if m k = i then w k else 0) * (K * nominalCompletion μ m s k / (23 / 6) + 1)) /
          (16 / 3) / K := by
      intro i
      refine Real.tsum_le_of_sum_range_le (fun t => div_nonneg (Finset.sum_nonneg
        (fun u _ => h7.1 i (K * t + u))) hK'.le) (fun N => ?_)
      rw [← Finset.sum_div, sum_range_reindex (fun t => betaF (fun j => K * r j)
        (fun i j => (K : ℝ) * μ i j) w m (fun j => (K : ℝ) * s j) (23 / 6) i t / (16 / 3)) K N]
      refine div_le_div_of_nonneg_right ?_ hK'.le
      rw [← Finset.sum_div]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      have := betaF_sum_le (fun j => K * r j) (fun i j => (K : ℝ) * μ i j) w hw m
        (fun j => (K : ℝ) * s j) (23 / 6) (by norm_num)
        (fun k => by rw [nominalCompletion_scale]; exact mul_nonneg hK'.le (hC0 k)) i (K * N)
      simp only [nominalCompletion_scale] at this
      exact this
    have hβ : ∑ i, ∑' t, (∑ u ∈ Finset.range K, betaF (fun j => K * r j)
        (fun i j => (K : ℝ) * μ i j) w m (fun j => (K : ℝ) * s j) (23 / 6) i (K * t + u) /
          (16 / 3)) / K ≤ (K * V / (23 / 6) + W) / (16 / 3) / K := by
      refine le_trans (Finset.sum_le_sum (fun i _ => hβi i)) (le_of_eq ?_)
      rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]
      congr 2
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_congr rfl (fun k _ => Finset.sum_ite_eq (Finset.univ) (m k) _)]
      simp only [Finset.mem_univ, if_true]
      rw [hV, hW]
      unfold nominalValue
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    have e : (K * V / (23 / 6) + W) / (16 / 3) / K = V * (18 / 368) + 3 / 16 * W / K := by
      field_simp; ring
    rw [e] at hβ
    linarith
  by_contra hcon
  push Not at hcon
  set δ := V * (51 / 368) - valueP elig μ w y with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (3 / 16 * W / δ)
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := lt_of_le_of_lt (div_nonneg (by positivity) hδ0.le) hK
    exact_mod_cast this
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have h1 := hKbound K hKpos
  have h2 : 3 / 16 * W < δ * K := by have := (div_lt_iff₀ hδ0).mp hK; linarith
  have h3 : 3 / 16 * W / K < δ := by rw [div_lt_iff₀ hK']; linarith
  linarith

/-! ## The stochastic policy versus the nominal schedule -/

lemma stochStartAux_integrable {Ω : Type*} [MeasurableSpace Ω] (I : StochasticInstance M n Ω)
    (m : Fin n → M) (s : Fin n → ℝ) (hm : ∀ j, I.eligible (m j) j) :
    ∀ fuel j, Integrable (fun ω => stochStartAux m s (realize I ω) fuel j) I.Pr := by
  haveI := I.probability
  have hP : ∀ l, Integrable (fun ω => ((realize I ω) (m l) l : ℝ)) I.Pr := fun l =>
    (I.memLp (m l) l (hm l)).integrable (by norm_num)
  intro fuel
  induction fuel with
  | zero => intro j; simp only [stochStartAux]; exact integrable_const _
  | succ k ih =>
    intro j
    rcases h : nominalPred m s j with _ | l
    · simp only [stochStartAux, h]; exact integrable_const _
    · simp only [stochStartAux, h]
      exact (integrable_const (s j)).sup ((ih l).add (hP l))

lemma hFactor_ge_one {Δ : ℝ} (hΔ : 0 ≤ Δ) : 1 ≤ hFactor Δ := by
  unfold hFactor
  split_ifs
  · linarith [Real.sqrt_nonneg Δ]
  · have : 0 ≤ Δ / (Δ + 1) := div_nonneg hΔ (by linarith)
    linarith

lemma stoch_le {Ω : Type*} [MeasurableSpace Ω] [Nonempty M] (I : StochasticInstance M n Ω)
    (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s) :
    stochValue I m s ≤ hFactor I.Delta * nominalValue (mean I) I.weight m s := by
  haveI := I.probability
  have hm : ∀ j, I.eligible (m j) j := fun j => (hG.1 j).1
  have hP : ∀ l, Integrable (fun ω => ((realize I ω) (m l) l : ℝ)) I.Pr := fun l =>
    (I.memLp (m l) l (hm l)).integrable (by norm_num)
  have hS : ∀ j, Integrable (fun ω => stochStart m s (realize I ω) j) I.Pr := fun j =>
    stochStartAux_integrable I m s hm n j
  have hh := hFactor_ge_one I.Delta_nonneg
  have hint : ∀ j, Integrable (fun ω => I.weight j * stochCompletion m s (realize I ω) j) I.Pr :=
    fun j => ((hS j).add (hP j)).const_mul _
  unfold stochValue nominalValue
  rw [integral_finset_sum _ (fun j _ => hint j), Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  unfold stochCompletion nominalCompletion
  rw [integral_const_mul, integral_add (hS j) (hP j)]
  have h8 := lemma_8 I m s hG j
  have hmean : ∫ ω, ((realize I ω) (m j) j : ℝ) ∂I.Pr = mean I (m j) j := rfl
  rw [hmean]
  have hs : 0 ≤ s j := le_trans (le_trans (Nat.cast_nonneg _) (le_max_left _ _)) (hG.2.1 j)
  have hμ1 : 1 ≤ mean I (m j) j := I.meanAtLeastOne _ _ (hm j)
  have hμ : 0 ≤ mean I (m j) j := by linarith
  have hw := I.weight_nonneg j
  calc I.weight j * (∫ ω, stochStart m s (realize I ω) j ∂I.Pr + mean I (m j) j)
      ≤ I.weight j * (hFactor I.Delta * s j + mean I (m j) j) :=
        mul_le_mul_of_nonneg_left (by linarith) hw
    _ ≤ I.weight j * (hFactor I.Delta * (s j + mean I (m j) j)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hw
    _ = _ := by ring

end GW4Sol

open GW4Sol in
theorem solution {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (I : StochasticInstance M n Ω) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s)
    (pol : GreedWorks.OnlineList.Policy M n) (hpol : IsAdmissible I pol) :
    stochValue I m s ≤ (7.216 + 3.608 * I.Delta) * hFactor I.Delta * policyCost I pol := by
  obtain ⟨hA, hB⟩ := eq_13 I
  obtain ⟨y, hyS, hyv⟩ := hB pol hpol
  obtain ⟨y', hy'P, hy'v⟩ := hA y hyS
  have hdet := alg_le_LP I.eligible I.hasMachine I.release I.release_monotone (mean I)
    (fun i j h => I.meanAtLeastOne i j h) I.weight I.weight_nonneg m s hG y' hy'P
  have hst := stoch_le I m s hG
  have hm : ∀ j, I.eligible (m j) j := fun j => (hG.1 j).1
  have hΔ := I.Delta_nonneg
  have hh := hFactor_ge_one hΔ
  have hV0 : 0 ≤ nominalValue (mean I) I.weight m s := by
    unfold nominalValue nominalCompletion
    refine Finset.sum_nonneg (fun j _ => mul_nonneg (I.weight_nonneg j) ?_)
    have hs : 0 ≤ s j := le_trans (le_trans (Nat.cast_nonneg _) (le_max_left _ _)) (hG.2.1 j)
    have hμ1 : 1 ≤ mean I (m j) j := I.meanAtLeastOne _ _ (hm j)
    linarith
  have h1 : nominalValue (mean I) I.weight m s ≤
      368 / 51 * ((1 + I.Delta / 2) * policyCost I pol) :=
    le_trans hdet (mul_le_mul_of_nonneg_left (le_trans hy'v
      (mul_le_mul_of_nonneg_left hyv (by positivity))) (by norm_num))
  have hPi : 0 ≤ policyCost I pol := by
    have : 0 ≤ (1 + I.Delta / 2) * policyCost I pol := by linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp this
  have hp : 0 ≤ hFactor I.Delta * policyCost I pol * (1 + I.Delta / 2) := by
    have : 0 ≤ hFactor I.Delta := by linarith
    positivity
  calc stochValue I m s ≤ hFactor I.Delta * nominalValue (mean I) I.weight m s := hst
    _ ≤ hFactor I.Delta * (368 / 51 * ((1 + I.Delta / 2) * policyCost I pol)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ _ := by nlinarith [mul_nonneg hp (show (0 : ℝ) ≤ 7.216 - 368 / 51 by norm_num)]
