-- Prove2me | solution 1 for KellyStochasticNetworks.MaxWeight.foster_lyapunov
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:46:09.890086+00:00
-- url     : https://prove2.me/submissions/6a8b82cb-6c22-401d-ad1a-bf8f8a753c0a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain

open scoped ENNReal
open Classical

namespace X5FL
open KellyStochasticNetworks.MaxWeight

variable {S : Type*} (P : Chain S)

/-- `∑ P(i,k) L(k) = L(i) + drift(i)`. -/
lemma drift_real (L : S → ℝ) (i : S) (hint : DriftIntegrable P L i) :
    Summable (fun k => (P i k).toReal * L k) ∧
      ∑' k, (P i k).toReal * L k = L i + drift P L i := by
  have hne : ∀ k, P i k ≠ ⊤ := PMF.apply_ne_top (P i)
  have hsum1 : ∑' k, (P i k).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hne, PMF.tsum_coe, ENNReal.toReal_one]
  have hs1 : Summable (fun k => (P i k).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have hf : Summable (fun k => (P i k).toReal * (L k - L i)) := by
    apply Summable.of_norm
    refine (hint).congr (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have hg : Summable (fun k => (P i k).toReal * L k) :=
    (hf.add (hs1.mul_right (L i))).congr (fun k => by ring)
  have htsum : ∑' k, (P i k).toReal * L k = L i + drift P L i := by
    have : ∑' k, (P i k).toReal * L k =
        ∑' k, ((P i k).toReal * (L k - L i) + (P i k).toReal * L i) :=
      tsum_congr (fun k => by ring)
    rw [this, hf.tsum_add (hs1.mul_right (L i)), tsum_mul_right, hsum1]
    unfold drift; ring
  exact ⟨hg, htsum⟩

lemma drift_nonneg (L : S → ℝ) (hL : ∀ i, 0 ≤ L i) (i : S) (hint : DriftIntegrable P L i) :
    0 ≤ L i + drift P L i := by
  rw [← (drift_real P L i hint).2]
  exact tsum_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (hL k))

lemma drift_sum (L : S → ℝ) (hL : ∀ i, 0 ≤ L i) (i : S) (hint : DriftIntegrable P L i) :
    ∑' k, P i k * ENNReal.ofReal (L k) = ENNReal.ofReal (L i + drift P L i) := by
  have hne : ∀ k, P i k ≠ ⊤ := PMF.apply_ne_top (P i)
  obtain ⟨hg, htsum⟩ := drift_real P L i hint
  rw [← htsum, ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg ENNReal.toReal_nonneg (hL k)) hg]
  refine tsum_congr (fun k => ?_)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hne k)]

/-- Truncated expected return time to `K`, counted from states outside `K`. -/
noncomputable def Gs (K : Set S) (n : ℕ) (j : S) : ℝ≥0∞ :=
  if j ∈ K then 0 else ∑ m ∈ Finset.range n, avoidProbability P K m j

lemma Gs_succ (K : Set S) (n : ℕ) (j : S) :
    Gs P K (n + 1) j = if j ∈ K then 0 else 1 + ∑' k, P j k * Gs P K n k := by
  unfold Gs
  split_ifs with hj
  · rfl
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  simp only [avoidProbability]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr (fun k => ?_)
  split_ifs with hk
  · simp
  · rw [Finset.mul_sum]

lemma Gs_zero (K : Set S) (j : S) : Gs P K 0 j = 0 := by
  unfold Gs; split_ifs <;> simp

lemma Gs_mem (K : Set S) (n : ℕ) {j : S} (hj : j ∈ K) : Gs P K n j = 0 := by
  unfold Gs; rw [if_pos hj]

lemma meanReturn_eq (K : Set S) (i : S) :
    meanReturn P K i = 1 + ∑' k, P i k * ⨆ n, Gs P K n k := by
  unfold meanReturn
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [avoidProbability]
  congr 1
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun k => ?_)
  by_cases hk : k ∈ K
  · simp [hk, Gs]
  · simp only [hk, if_false, Gs, ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_eq_iSup_nat]

lemma Gs_mono (K : Set S) : ∀ n j, Gs P K n j ≤ Gs P K (n + 1) j := by
  intro n
  induction n with
  | zero => intro j; rw [Gs_zero]; exact zero_le'
  | succ n ih =>
    intro j
    rw [Gs_succ P K n j, Gs_succ P K (n + 1) j]
    split_ifs
    · exact le_rfl
    · gcongr with k
      exact ih k

lemma Gs_mono' (K : Set S) {m n : ℕ} (h : m ≤ n) (j : S) : Gs P K m j ≤ Gs P K n j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Gs_mono P K _ j)

lemma Gs_le (K : Set S) : ∀ n j, Gs P K n j ≤ n := by
  intro n
  induction n with
  | zero => intro j; rw [Gs_zero]; simp
  | succ n ih =>
    intro j
    rw [Gs_succ]
    split_ifs
    · exact zero_le'
    · calc 1 + ∑' k, P j k * Gs P K n k ≤ 1 + ∑' k, P j k * (n : ℝ≥0∞) := by
            gcongr with k; exact ih k
        _ = 1 + n := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        _ = ((n + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- Part 1: finite mean return time to the finite set `K`. -/
theorem part1 (L : S → ℝ) (hL : ∀ i, 0 ≤ L i) (ε b : ℝ) (hε : 0 < ε) (K : Finset S)
    (hint : ∀ i, DriftIntegrable P L i)
    (hbound : ∀ i, drift P L i ≤ if i ∈ K then b - ε else -ε) :
    ∀ i, meanReturn P (K : Set S) i < ∞ := by
  have key : ∀ n j, ENNReal.ofReal ε * Gs P K n j ≤ ENNReal.ofReal (L j) := by
    intro n
    induction n with
    | zero => intro j; rw [Gs_zero]; simp
    | succ n ih =>
      intro j
      rw [Gs_succ]
      split_ifs with hj
      · simp
      · have hd := hbound j
        rw [if_neg (by simpa using hj)] at hd
        rw [mul_add, mul_one, ← ENNReal.tsum_mul_left]
        calc ENNReal.ofReal ε + ∑' k, ENNReal.ofReal ε * (P j k * Gs P K n k)
            ≤ ENNReal.ofReal ε + ∑' k, P j k * ENNReal.ofReal (L k) := by
              refine add_le_add_right (ENNReal.tsum_le_tsum (fun k => ?_)) _
              calc ENNReal.ofReal ε * (P j k * Gs P K n k) =
                  P j k * (ENNReal.ofReal ε * Gs P K n k) := by ring
                _ ≤ _ := mul_le_mul_right (ih k) _
          _ = ENNReal.ofReal ε + ENNReal.ofReal (L j + drift P L j) := by
              rw [drift_sum P L hL j (hint j)]
          _ = ENNReal.ofReal (ε + (L j + drift P L j)) := by
              rw [ENNReal.ofReal_add hε.le]
              exact drift_nonneg P L hL j (hint j)
          _ ≤ ENNReal.ofReal (L j) := ENNReal.ofReal_le_ofReal (by linarith)
  intro i
  have hε' : ENNReal.ofReal ε ≠ 0 := by simpa using hε
  have h1 : ENNReal.ofReal ε * meanReturn P (K : Set S) i ≤
      ENNReal.ofReal ε + ENNReal.ofReal (L i + drift P L i) := by
    rw [meanReturn_eq, mul_add, mul_one, ← ENNReal.tsum_mul_left]
    gcongr
    rw [← drift_sum P L hL i (hint i)]
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    rw [mul_left_comm, ENNReal.mul_iSup]
    exact mul_le_mul_right (iSup_le (fun n => key n k)) _
  have h2 : ENNReal.ofReal ε * meanReturn P (K : Set S) i < ∞ :=
    lt_of_le_of_lt h1 (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  rcases ENNReal.mul_lt_top_iff.1 h2 with h | h | h
  · exact h.2
  · exact absurd h hε'
  · rw [h]; exact ENNReal.zero_lt_top

end X5FL


open scoped ENNReal
open Classical

namespace X5FL
open KellyStochasticNetworks.MaxWeight

variable {S : Type*} (P : Chain S) (i₀ : S)

/-- The chain killed at `i₀`. -/
noncomputable def T (j l : S) : ℝ≥0∞ := if j = i₀ then 0 else P j l

noncomputable def Tp : ℕ → S → S → ℝ≥0∞
  | 0, j, k => if j = k then 1 else 0
  | N + 1, j, k => ∑' l, T P i₀ j l * Tp N l k

lemma T_le (j l : S) : T P i₀ j l ≤ P j l := by
  unfold T; split_ifs <;> simp

lemma tsum_delta (j : S) (f : S → ℝ≥0∞) : ∑' k, (if j = k then (1:ℝ≥0∞) else 0) * f k = f j := by
  have : ∀ k, (if j = k then (1:ℝ≥0∞) else 0) * f k = if k = j then f k else 0 := by
    intro k; by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h]
  simp only [this]; exact tsum_ite_eq j f

lemma Tp_succ_mul (N : ℕ) (j : S) (f : S → ℝ≥0∞) :
    ∑' k, Tp P i₀ (N + 1) j k * f k = ∑' l, T P i₀ j l * ∑' k, Tp P i₀ N l k * f k := by
  simp only [Tp, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

lemma g_succ (n : ℕ) (j : S) :
    Gs P {i₀} (n + 1) j = if j = i₀ then 0 else 1 + ∑' k, P j k * Gs P {i₀} n k := by
  rw [Gs_succ]; simp only [Set.mem_singleton_iff]

lemma g_self (n : ℕ) : Gs P {i₀} n i₀ = 0 := Gs_mem P _ n rfl

lemma tp_le_one : ∀ N j k, transitionPower P N j k ≤ 1 := by
  intro N
  induction N with
  | zero => intro j k; simp only [transitionPower]; split_ifs <;> simp
  | succ N ih =>
    intro j k
    simp only [transitionPower]
    calc ∑' l, P j l * transitionPower P N l k ≤ ∑' l, P j l * 1 := by
          gcongr with l; exact ih l k
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma S_le : ∀ N j, ∑' k, Tp P i₀ N j k * (if k = i₀ then 0 else 1) +
    transitionPower P N j i₀ ≤ 1 := by
  intro N
  induction N with
  | zero =>
    intro j
    simp only [Tp, transitionPower]
    rw [tsum_delta]
    by_cases h : j = i₀ <;> simp [h]
  | succ N ih =>
    intro j
    rw [Tp_succ_mul]
    simp only [transitionPower]
    by_cases hj : j = i₀
    · simp only [T, hj, if_true, zero_mul, tsum_zero, zero_add]
      calc ∑' l, P i₀ l * transitionPower P N l i₀ ≤ ∑' l, P i₀ l * 1 := by
            gcongr with l; exact tp_le_one P N l i₀
        _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    · simp only [T, hj, if_false]
      rw [← ENNReal.tsum_add]
      calc ∑' l, (P j l * ∑' k, Tp P i₀ N l k * (if k = i₀ then 0 else 1) +
            P j l * transitionPower P N l i₀) ≤ ∑' l, P j l * 1 := by
            refine ENNReal.tsum_le_tsum (fun l => ?_)
            rw [← mul_add]; exact mul_le_mul_right (ih l) _
        _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- `N`-step expansion of the truncated hitting times of `i₀`. -/
lemma expand : ∀ N m j, Gs P {i₀} (m + N) j ≤ N + ∑' k, Tp P i₀ N j k * Gs P {i₀} m k := by
  intro N
  induction N with
  | zero => intro m j; simp only [Tp, add_zero, Nat.cast_zero, zero_add]; rw [tsum_delta]
  | succ N ih =>
    intro m j
    rw [← add_assoc, g_succ, Tp_succ_mul]
    split_ifs with hj
    · exact zero_le'
    · simp only [T, hj, if_false]
      calc 1 + ∑' k, P j k * Gs P {i₀} (m + N) k
          ≤ 1 + ∑' k, P j k * (N + ∑' l, Tp P i₀ N k l * Gs P {i₀} m l) := by
            gcongr with k; exact ih m k
        _ = 1 + N + ∑' k, P j k * ∑' l, Tp P i₀ N k l * Gs P {i₀} m l := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            ring
        _ = ((N + 1 : ℕ) : ℝ≥0∞) + ∑' k, P j k * ∑' l, Tp P i₀ N k l * Gs P {i₀} m l := by
            push_cast; ring

end X5FL


open scoped ENNReal
open Classical

namespace X5FL
open KellyStochasticNetworks.MaxWeight

variable {S : Type*} (P : Chain S) (i₀ : S)

noncomputable def Mx (K : Finset S) (m : ℕ) : ℝ≥0∞ := (insert i₀ K).sup (Gs P {i₀} m)

lemma Mx_mono (K : Finset S) (m : ℕ) : Mx P i₀ K m ≤ Mx P i₀ K (m + 1) :=
  Finset.sup_mono_fun (fun k _ => Gs_mono P _ m k)

section
variable (L : S → ℝ) (hL : ∀ i, 0 ≤ L i) (ε b : ℝ) (hε : 0 < ε) (K : Finset S)
    (hint : ∀ i, DriftIntegrable P L i)
    (hbound : ∀ i, drift P L i ≤ if i ∈ K then b - ε else -ε)
include hL hε hint hbound

lemma drift_le_bp (j : S) : drift P L j ≤ max b 0 := by
  have := hbound j
  split_ifs at this
  · linarith [le_max_left b 0]
  · linarith [le_max_right b 0]

lemma Tp_L : ∀ N j, ∑' k, Tp P i₀ N j k * ENNReal.ofReal (L k) ≤
    ENNReal.ofReal (L j + N * max b 0) := by
  have hbp : 0 ≤ max b 0 := le_max_right _ _
  intro N
  induction N with
  | zero => intro j; simp only [Tp, Nat.cast_zero, zero_mul, add_zero]; rw [tsum_delta]
  | succ N ih =>
    intro j
    rw [Tp_succ_mul]
    calc ∑' l, T P i₀ j l * ∑' k, Tp P i₀ N l k * ENNReal.ofReal (L k)
        ≤ ∑' l, P j l * (ENNReal.ofReal (L l) + ENNReal.ofReal (N * max b 0)) := by
          refine ENNReal.tsum_le_tsum (fun l => ?_)
          rw [← ENNReal.ofReal_add (hL l) (by positivity)]
          exact mul_le_mul' (T_le P i₀ j l) (ih l)
      _ = ENNReal.ofReal (L j + drift P L j) + ENNReal.ofReal (N * max b 0) := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          rw [drift_sum P L hL j (hint j)]
      _ = ENNReal.ofReal (L j + drift P L j + N * max b 0) := by
          rw [ENNReal.ofReal_add (drift_nonneg P L hL j (hint j)) (by positivity)]
      _ ≤ ENNReal.ofReal (L j + ((N + 1 : ℕ) : ℝ) * max b 0) := by
          apply ENNReal.ofReal_le_ofReal
          have := drift_le_bp P L hL ε b hε K hint hbound j
          push_cast; nlinarith

lemma claim1 : ∀ m j, ENNReal.ofReal ε * Gs P {i₀} m j ≤
    ENNReal.ofReal (L j) + ENNReal.ofReal ε * Mx P i₀ K m := by
  intro m
  induction m with
  | zero => intro j; rw [Gs_zero]; simp
  | succ m ih =>
    intro j
    by_cases hjK : j ∈ insert i₀ K
    · have : Gs P {i₀} (m + 1) j ≤ Mx P i₀ K (m + 1) := Finset.le_sup (f := Gs P {i₀} (m + 1)) hjK
      calc ENNReal.ofReal ε * Gs P {i₀} (m + 1) j ≤ ENNReal.ofReal ε * Mx P i₀ K (m + 1) :=
            mul_le_mul_right this _
        _ ≤ _ := le_add_self
    · have hj0 : j ≠ i₀ := fun h => hjK (by simp [h])
      have hjK' : j ∉ K := fun h => hjK (Finset.mem_insert_of_mem h)
      have hd := hbound j
      rw [if_neg hjK'] at hd
      rw [g_succ, if_neg hj0, mul_add, mul_one, ← ENNReal.tsum_mul_left]
      calc ENNReal.ofReal ε + ∑' k, ENNReal.ofReal ε * (P j k * Gs P {i₀} m k)
          ≤ ENNReal.ofReal ε + ∑' k, P j k * (ENNReal.ofReal (L k) +
              ENNReal.ofReal ε * Mx P i₀ K m) := by
            refine add_le_add_right (ENNReal.tsum_le_tsum (fun k => ?_)) _
            calc ENNReal.ofReal ε * (P j k * Gs P {i₀} m k) =
                P j k * (ENNReal.ofReal ε * Gs P {i₀} m k) := by ring
              _ ≤ _ := mul_le_mul_right (ih k) _
        _ = ENNReal.ofReal ε + ENNReal.ofReal (L j + drift P L j) +
              ENNReal.ofReal ε * Mx P i₀ K m := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            rw [drift_sum P L hL j (hint j)]; ring
        _ ≤ ENNReal.ofReal (L j) + ENNReal.ofReal ε * Mx P i₀ K (m + 1) := by
            gcongr
            · rw [← ENNReal.ofReal_add hε.le (drift_nonneg P L hL j (hint j))]
              exact ENNReal.ofReal_le_ofReal (by linarith)
            · exact Mx_mono P i₀ K m

/-- One-state contraction: from `k ≠ i₀`, `i₀` is reached in `N` steps with probability `p`. -/
lemma contract (k : S) (hk : k ≠ i₀) (N : ℕ) (m : ℕ) :
    ENNReal.ofReal ε * Gs P {i₀} m k ≤
      (ENNReal.ofReal ε * N + ENNReal.ofReal (L k + N * max b 0)) +
        ENNReal.ofReal ε * Mx P i₀ K m * (1 - transitionPower P N k i₀) := by
  have h1 : Gs P {i₀} m k ≤ Gs P {i₀} (m + N) k := Gs_mono' P _ (by omega) k
  have h2 := expand P i₀ N m k
  have hsum : ∑' l, Tp P i₀ N k l * (ENNReal.ofReal ε * Gs P {i₀} m l) ≤
      ENNReal.ofReal (L k + N * max b 0) +
        ENNReal.ofReal ε * Mx P i₀ K m * (1 - transitionPower P N k i₀) := by
    have hS := S_le P i₀ N k
    have hS' : ∑' l, Tp P i₀ N k l * (if l = i₀ then 0 else 1) ≤ 1 - transitionPower P N k i₀ :=
      ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top ENNReal.one_ne_top
        (tp_le_one P N k i₀)) hS
    calc ∑' l, Tp P i₀ N k l * (ENNReal.ofReal ε * Gs P {i₀} m l)
        ≤ ∑' l, (Tp P i₀ N k l * ENNReal.ofReal (L l) +
            Tp P i₀ N k l * (if l = i₀ then 0 else 1) * (ENNReal.ofReal ε * Mx P i₀ K m)) := by
          refine ENNReal.tsum_le_tsum (fun l => ?_)
          by_cases hl : l = i₀
          · subst hl; rw [g_self]; simp
          · simp only [hl, if_false, mul_one, ← mul_add]
            exact mul_le_mul_right (claim1 P i₀ L hL ε b hε K hint hbound m l) _
      _ = ∑' l, Tp P i₀ N k l * ENNReal.ofReal (L l) +
            (∑' l, Tp P i₀ N k l * (if l = i₀ then 0 else 1)) * (ENNReal.ofReal ε * Mx P i₀ K m) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ ≤ ENNReal.ofReal (L k + N * max b 0) +
            (1 - transitionPower P N k i₀) * (ENNReal.ofReal ε * Mx P i₀ K m) :=
          add_le_add (Tp_L P i₀ L hL ε b hε K hint hbound N k) (by gcongr)
      _ = _ := by ring
  calc ENNReal.ofReal ε * Gs P {i₀} m k ≤ ENNReal.ofReal ε * Gs P {i₀} (m + N) k :=
        mul_le_mul_right h1 _
    _ ≤ ENNReal.ofReal ε * (N + ∑' l, Tp P i₀ N k l * Gs P {i₀} m l) := mul_le_mul_right h2 _
    _ = ENNReal.ofReal ε * N + ∑' l, Tp P i₀ N k l * (ENNReal.ofReal ε * Gs P {i₀} m l) := by
        rw [mul_add, ← ENNReal.tsum_mul_left]
        congr 1; exact tsum_congr (fun l => by ring)
    _ ≤ _ := by rw [add_assoc]; exact add_le_add_right hsum _

lemma uniform (hirr : Irreducible P) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ m, ENNReal.ofReal ε * Mx P i₀ K m ≤ C := by
  set K' := (insert i₀ K).erase i₀
  have hN : ∀ k, ∃ N, 0 < transitionPower P N k i₀ := fun k => hirr k i₀
  choose Nf hNf using hN
  set c : ℝ≥0∞ := ∑ k ∈ K', (ENNReal.ofReal ε * Nf k + ENNReal.ofReal (L k + Nf k * max b 0))
  set p : ℝ≥0∞ := min 1 (K'.inf (fun k => transitionPower P (Nf k) k i₀))
  have hc : c < ∞ := by
    apply ENNReal.sum_lt_top.2
    intro k _
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.natCast_lt_top _),
      ENNReal.ofReal_lt_top⟩
  have hp0 : 0 < p := by
    apply lt_min one_pos
    rw [Finset.lt_inf_iff ENNReal.zero_lt_top]
    intro k _; exact hNf k
  have hp1 : p ≤ 1 := min_le_left _ _
  have hstep : ∀ m, ENNReal.ofReal ε * Mx P i₀ K m ≤ c + ENNReal.ofReal ε * Mx P i₀ K m * (1 - p) := by
    intro m
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup (insert i₀ K) (Finset.insert_nonempty _ _)
      (Gs P {i₀} m)
    unfold Mx; rw [hkeq]
    by_cases hk0 : k = i₀
    · subst hk0; rw [g_self]; simp
    · have hkK' : k ∈ K' := Finset.mem_erase.2 ⟨hk0, hk⟩
      have h := contract P i₀ L hL ε b hε K hint hbound k hk0 (Nf k) m
      unfold Mx at h; rw [hkeq] at h
      refine h.trans (add_le_add ?_ ?_)
      · exact Finset.single_le_sum (f := fun k => ENNReal.ofReal ε * Nf k +
          ENNReal.ofReal (L k + Nf k * max b 0)) (fun _ _ => zero_le) hkK'
      · apply mul_le_mul_right
        apply tsub_le_tsub_left
        exact (min_le_right _ _).trans (Finset.inf_le hkK')
  refine ⟨ENNReal.ofReal (c.toReal / p.toReal), ENNReal.ofReal_lt_top, fun m => ?_⟩
  set x := ENNReal.ofReal ε * Mx P i₀ K m
  have hx : x < ∞ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    unfold Mx
    refine lt_of_le_of_lt (Finset.sup_le (fun k _ => Gs_le P _ m k)) (ENNReal.natCast_lt_top m)
  have h : x ≤ c + x * (1 - p) := hstep m
  clear_value x
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hr := (ENNReal.toReal_le_toReal (b := c + x * (1 - p)) hx.ne (by
    exact ENNReal.add_ne_top.2 ⟨hc.ne, ENNReal.mul_ne_top hx.ne
      (ENNReal.sub_ne_top ENNReal.one_ne_top)⟩)).2 h
  rw [ENNReal.toReal_add hc.ne (ENNReal.mul_ne_top hx.ne (ENNReal.sub_ne_top ENNReal.one_ne_top)),
    ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hp1 ENNReal.one_ne_top, ENNReal.toReal_one] at hr
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hpt
  calc x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx.ne).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hpr]
      nlinarith

end

end X5FL


open scoped ENNReal
open Classical

namespace X5FL
open KellyStochasticNetworks.MaxWeight

theorem main {S : Type*} [Countable S] [Nonempty S]
    (P : Chain S) (hirr : Irreducible P) (L : S → ℝ) (hL : ∀ i, 0 ≤ L i)
    (ε b : ℝ) (hε : 0 < ε) (K : Finset S)
    (hint : ∀ i, DriftIntegrable P L i)
    (hbound : ∀ i, drift P L i ≤ if i ∈ K then b - ε else -ε) :
    (∀ i, meanReturn P (K : Set S) i < ∞) ∧ PositiveRecurrent P := by
  refine ⟨part1 P L hL ε b hε K hint hbound, fun i₀ => ?_⟩
  obtain ⟨C, hC, hCb⟩ := uniform P i₀ L hL ε b hε K hint hbound hirr
  have hε' : ENNReal.ofReal ε ≠ 0 := by simpa using hε
  have h1 : ENNReal.ofReal ε * meanReturn P {i₀} i₀ ≤
      ENNReal.ofReal ε + (ENNReal.ofReal (L i₀ + drift P L i₀) + C) := by
    rw [meanReturn_eq, mul_add, mul_one, ← ENNReal.tsum_mul_left]
    gcongr
    calc ∑' k, ENNReal.ofReal ε * (P i₀ k * ⨆ n, Gs P {i₀} n k)
        ≤ ∑' k, P i₀ k * (ENNReal.ofReal (L k) + C) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          rw [mul_left_comm, ENNReal.mul_iSup]
          refine mul_le_mul_right (iSup_le (fun n => ?_)) _
          exact (claim1 P i₀ L hL ε b hε K hint hbound n k).trans (add_le_add_right (hCb n) _)
      _ = _ := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          rw [drift_sum P L hL i₀ (hint i₀)]
  have h2 : ENNReal.ofReal ε * meanReturn P {i₀} i₀ < ∞ :=
    lt_of_le_of_lt h1 (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
      ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hC⟩⟩)
  rcases ENNReal.mul_lt_top_iff.1 h2 with h | h | h
  · exact h.2
  · exact absurd h hε'
  · rw [h]; exact ENNReal.zero_lt_top

end X5FL


open scoped NNReal
open KellyStochasticNetworks.MaxWeight in
theorem solution {S : Type*} [Countable S] [Nonempty S]
    (P : Chain S) (hirr : Irreducible P) (L : S → ℝ) (hL : ∀ i, 0 ≤ L i)
    (ε b : ℝ) (hε : 0 < ε) (K : Finset S)
    (hint : ∀ i, DriftIntegrable P L i)
    (hbound : ∀ i, drift P L i ≤ if i ∈ K then b - ε else -ε) :
    (∀ i, meanReturn P (K : Set S) i < ∞) ∧ PositiveRecurrent P :=
  X5FL.main P hirr L hL ε b hε K hint hbound
