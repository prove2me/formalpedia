-- Prove2me | solution 1 for KellyStochasticNetworks.MaxWeight.positive_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:34:04.87831+00:00
-- url     : https://prove2.me/submissions/ba4e2b5b-65a3-47d2-866d-8881bd557710

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Network
import Theorems.Thm_KellyStochasticNetworks_MaxWeight_poisson_envelope_moments

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


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5WD
open KellyStochasticNetworks.MaxWeight

/-- Expectations under a pushed-forward PMF. -/
lemma tsum_map_mul {α β : Type*} (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑' j, (p.map g) j * f j = ∑' a, p a * f (g a) := by
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun a => ?_)
  have : ∀ j, (if j = g a then p a else 0) * f j = if j = g a then p a * f (g a) else 0 := by
    intro j; split_ifs with h
    · rw [h]
    · simp
  simp only [this]
  exact tsum_ite_eq (g a) _

lemma tsum_bind_mul {α β : Type*} (p : PMF α) (h : α → PMF β) (f : β → ℝ≥0∞) :
    ∑' j, (p.bind h) j * f j = ∑' a, p a * ∑' j, h a j * f j := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

variable {R : Type*} [Fintype R]

lemma chain_exp (lam : R → ℝ≥0) (tie : (R → ℕ) → PMF (R → ℕ)) (q : R → ℕ)
    (f : (R → ℕ) → ℝ≥0∞) :
    ∑' j, queueChain lam tie q j * f j =
      ∑' σ, tie q σ * ∑' a, arrivalLaw lam a * f (nextQueue q σ a) := by
  unfold queueChain
  rw [tsum_bind_mul]
  refine tsum_congr (fun σ => ?_)
  rw [tsum_map_mul]

/-- Poisson mean. -/
lemma poisson_mean (l : ℝ≥0) :
    ∫⁻ x : ℕ, ENNReal.ofReal (x : ℝ) ∂(poissonMeasure l) = (l : ℝ≥0∞) := by
  rw [lintegral_countable']
  simp only [poissonMeasure_singleton]
  have hs : HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-(l : ℝ)) * (l : ℝ) ^ n / n.factorial))
      (l : ℝ) := by
    have he := NormedSpace.expSeries_div_hasSum_exp (l : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at he
    have h1 : HasSum (fun n : ℕ => Real.exp (-(l : ℝ)) * (l : ℝ) * ((l : ℝ) ^ n / n.factorial))
        (Real.exp (-(l : ℝ)) * (l : ℝ) * Real.exp (l : ℝ)) := he.mul_left _
    have h2 : Real.exp (-(l : ℝ)) * (l : ℝ) * Real.exp (l : ℝ) = (l : ℝ) := by
      rw [mul_comm (Real.exp _) (l : ℝ), mul_assoc, ← Real.exp_add]; simp
    rw [h2] at h1
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
    refine h1.congr_fun (fun n => ?_)
    rw [Nat.factorial_succ]; push_cast
    field_simp
    ring
  calc ∑' n : ℕ, ENNReal.ofReal (n : ℝ) *
        ENNReal.ofReal (Real.exp (-(l : ℝ)) * (l : ℝ) ^ n / n.factorial)
      = ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * (Real.exp (-(l : ℝ)) * (l : ℝ) ^ n / n.factorial)) :=
        tsum_congr (fun n => (ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm)
    _ = ENNReal.ofReal (l : ℝ) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]
    _ = (l : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

lemma arrival_mean (lam : R → ℝ≥0) (r : R) :
    ∑' a, arrivalLaw lam a * ENNReal.ofReal (a r : ℝ) = (lam r : ℝ≥0∞) := by
  unfold arrivalLaw
  simp only [Measure.toPMF_apply]
  have : ∑' a : R → ℕ, (Measure.pi fun r => poissonMeasure (lam r)) {a} * ENNReal.ofReal (a r : ℝ) =
      ∫⁻ a : R → ℕ, ENNReal.ofReal (a r : ℝ) ∂(Measure.pi fun r => poissonMeasure (lam r)) := by
    rw [lintegral_countable']; exact tsum_congr (fun a => mul_comm _ _)
  rw [this]
  have hmp := measurePreserving_eval (fun r => poissonMeasure (lam r)) r
  rw [← poisson_mean (lam r)]
  exact hmp.lintegral_comp (f := fun x : ℕ => ENNReal.ofReal (x : ℝ)) (measurable_of_countable _)

lemma arrival_total (lam : R → ℝ≥0) : ∑' a, arrivalLaw lam a = 1 := PMF.tsum_coe _

end X5WD


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5WD
open KellyStochasticNetworks.MaxWeight

variable {R : Type*} [Fintype R] (lam : R → ℝ≥0) (tie : (R → ℕ) → PMF (R → ℕ))

lemma next_cast (q σ a : R → ℕ) (r : R) :
    ((nextQueue q σ a r : ℕ) : ℝ) = ((q r - σ r : ℕ) : ℝ) + (a r : ℝ) := by
  unfold nextQueue; push_cast; ring

lemma exp_abs (q : R → ℕ) (r : R) :
    ∑' j, queueChain lam tie q j * ENNReal.ofReal |(j r : ℝ) - q r| ≤ (lam r : ℝ≥0∞) + q r := by
  rw [chain_exp]
  calc ∑' σ, tie q σ * ∑' a, arrivalLaw lam a *
        ENNReal.ofReal |((nextQueue q σ a r : ℕ) : ℝ) - q r|
      ≤ ∑' σ, tie q σ * ∑' a, arrivalLaw lam a * (ENNReal.ofReal (a r : ℝ) + q r) := by
        refine ENNReal.tsum_le_tsum (fun σ => mul_le_mul_right
          (ENNReal.tsum_le_tsum (fun a => mul_le_mul_right ?_ _)) _)
        rw [next_cast]
        have h1 : ((q r - σ r : ℕ) : ℝ) ≤ q r := by exact_mod_cast Nat.sub_le _ _
        have h2 : (0:ℝ) ≤ ((q r - σ r : ℕ) : ℝ) := Nat.cast_nonneg _
        have h3 : (0:ℝ) ≤ (a r : ℝ) := Nat.cast_nonneg _
        have : |((q r - σ r : ℕ) : ℝ) + (a r : ℝ) - q r| ≤ (a r : ℝ) + q r := by
          rw [abs_le]; constructor <;> linarith
        calc ENNReal.ofReal |((q r - σ r : ℕ) : ℝ) + (a r : ℝ) - q r|
            ≤ ENNReal.ofReal ((a r : ℝ) + q r) := ENNReal.ofReal_le_ofReal this
          _ = ENNReal.ofReal (a r : ℝ) + q r := by
            rw [ENNReal.ofReal_add h3 (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
              ENNReal.ofReal_natCast]
    _ = (lam r : ℝ≥0∞) + q r := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, arrival_mean, arrival_total,
          one_mul, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

lemma integrable (q : R → ℕ) (r : R) :
    DriftIntegrable (queueChain lam tie) (fun x => (x r : ℝ)) q := by
  unfold DriftIntegrable
  have hfin : ∑' j, queueChain lam tie q j * ENNReal.ofReal |(j r : ℝ) - q r| ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.natCast_ne_top _⟩)
      (exp_abs lam tie q r)
  refine (ENNReal.summable_toReal hfin).congr (fun j => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Expected number of unused-service-free departures complement. -/
noncomputable def Ex (q : R → ℕ) (r : R) : ℝ≥0∞ := ∑' σ, tie q σ * ((q r - σ r : ℕ) : ℝ≥0∞)

lemma Ex_le (q : R → ℕ) (r : R) : Ex tie q r ≤ q r := by
  unfold Ex
  calc ∑' σ, tie q σ * ((q r - σ r : ℕ) : ℝ≥0∞) ≤ ∑' σ, tie q σ * (q r : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum (fun σ => mul_le_mul_right (by exact_mod_cast Nat.sub_le _ _) _)
    _ = q r := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma Ex_ne_top (q : R → ℕ) (r : R) : Ex tie q r ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (Ex_le tie q r)

lemma exp_coord (q : R → ℕ) (r : R) :
    ∑' j, queueChain lam tie q j * ENNReal.ofReal (j r : ℝ) = Ex tie q r + lam r := by
  rw [chain_exp]
  have h : ∀ σ, ∑' a, arrivalLaw lam a * ENNReal.ofReal ((nextQueue q σ a r : ℕ) : ℝ) =
      ((q r - σ r : ℕ) : ℝ≥0∞) + lam r := by
    intro σ
    have : ∀ a, arrivalLaw lam a * ENNReal.ofReal ((nextQueue q σ a r : ℕ) : ℝ) =
        arrivalLaw lam a * ((q r - σ r : ℕ) : ℝ≥0∞) + arrivalLaw lam a * ENNReal.ofReal (a r : ℝ) := by
      intro a
      rw [next_cast, ENNReal.ofReal_add (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, mul_add]
    simp only [this]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, arrival_total, one_mul, arrival_mean]
  simp only [h, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rfl

lemma drift_formula (q : R → ℕ) (r : R) :
    drift (queueChain lam tie) (fun x => (x r : ℝ)) q = (Ex tie q r).toReal + lam r - q r := by
  set P := queueChain lam tie
  have hne : ∀ j, P q j ≠ ⊤ := PMF.apply_ne_top (P q)
  have hfin : ∑' j, P q j * ENNReal.ofReal (j r : ℝ) ≠ ⊤ := by
    rw [exp_coord]; exact ENNReal.add_ne_top.2 ⟨Ex_ne_top tie q r, ENNReal.coe_ne_top⟩
  have hs1 : Summable (fun j => (P q j).toReal * (j r : ℝ)) :=
    (ENNReal.summable_toReal hfin).congr (fun j => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg _)])
  have hs2 : Summable (fun j => (P q j).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have htot : ∑' j, (P q j).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hne, PMF.tsum_coe, ENNReal.toReal_one]
  have hmean : ∑' j, (P q j).toReal * (j r : ℝ) = (Ex tie q r).toReal + lam r := by
    rw [← ENNReal.toReal_ofReal_eq_iff.2 (show (0:ℝ) ≤ ∑' j, (P q j).toReal * (j r : ℝ) from
      tsum_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)))]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) hs1]
    have : ∀ j, ENNReal.ofReal ((P q j).toReal * (j r : ℝ)) = P q j * ENNReal.ofReal (j r : ℝ) := by
      intro j; rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hne j)]
    simp only [this]
    rw [exp_coord, ENNReal.toReal_add (Ex_ne_top tie q r) ENNReal.coe_ne_top]
    rfl
  unfold drift
  have : ∀ j, (P q j).toReal * ((j r : ℝ) - q r) = (P q j).toReal * (j r : ℝ) - (P q j).toReal * q r :=
    fun j => by ring
  simp only [this]
  rw [hs1.tsum_sub (hs2.mul_right _), tsum_mul_right, htot, hmean]
  ring

end X5WD


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5WD
open KellyStochasticNetworks.MaxWeight

variable {R : Type*} [Fintype R]

/-- Strictly inside the capacity region: a uniform slack `δ`. -/
lemma interior_slack (N : Network R) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ c : (R → ℕ) → ℝ, (∀ σ ∈ N.schedules, 0 ≤ c σ) ∧
      (∑ σ ∈ N.schedules, c σ) = 1 ∧
      ∀ r, (lam r : ℝ) + δ ≤ ∑ σ ∈ N.schedules, c σ * (σ r : ℝ) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hlam
  obtain ⟨ε, hε, hball⟩ := hlam
  refine ⟨ε / 2, by linarith, ?_⟩
  have hv : (fun r => (lam r : ℝ) + ε / 2) ∈ capacityRegion N := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro r
    rw [Real.dist_eq]
    simp only [add_sub_cancel_left]
    rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨-, c, hc0, hc1, hcle⟩ := hv
  exact ⟨c, hc0, hc1, hcle⟩

noncomputable def Bm (N : Network R) : ℝ := ∑ r, (serviceBound N r : ℝ)

lemma sched_le (N : Network R) {σ : R → ℕ} (hσ : σ ∈ N.schedules) (r : R) :
    (σ r : ℝ) ≤ Bm N := by
  have h1 : σ r ≤ serviceBound N r := Finset.le_sup (f := fun σ => σ r) hσ
  have h2 : (serviceBound N r : ℝ) ≤ Bm N :=
    Finset.single_le_sum (f := fun r => (serviceBound N r : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_univ r)
  exact le_trans (by exact_mod_cast h1) h2

/-- Per-schedule bound for a maximizing schedule. -/
lemma per_sched (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0) (δ : ℝ)
    (c : (R → ℕ) → ℝ) (hc0 : ∀ σ ∈ N.schedules, 0 ≤ c σ) (hc1 : (∑ σ ∈ N.schedules, c σ) = 1)
    (hcle : ∀ r, (lam r : ℝ) + δ ≤ ∑ σ ∈ N.schedules, c σ * (σ r : ℝ))
    (q σ : R → ℕ) (hσ : σ ∈ N.schedules)
    (hmax : ∀ π ∈ N.schedules, scheduleWeight α q π ≤ scheduleWeight α q σ) :
    ∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ) ≤
      ∑ r, (q r : ℝ) ^ α * (q r : ℝ) - ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ) +
        Fintype.card R * (Bm N * Bm N ^ α) := by
  have hqa : ∀ r, 0 ≤ (q r : ℝ) ^ α := fun r => Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- convex combination is dominated by the max weight
  have h1 : ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ) ≤ scheduleWeight α q σ := by
    calc ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ)
        ≤ ∑ r, (q r : ℝ) ^ α * ∑ π ∈ N.schedules, c π * (π r : ℝ) :=
          Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hcle r) (hqa r))
      _ = ∑ π ∈ N.schedules, c π * scheduleWeight α q π := by
          unfold scheduleWeight
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun r _ => by ring))
      _ ≤ ∑ π ∈ N.schedules, c π * scheduleWeight α q σ :=
          Finset.sum_le_sum (fun π hπ => mul_le_mul_of_nonneg_left (hmax π hπ) (hc0 π hπ))
      _ = scheduleWeight α q σ := by rw [← Finset.sum_mul, hc1, one_mul]
  -- unused service is bounded
  have hB0 : 0 ≤ Bm N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have h2 : ∀ r, (σ r : ℝ) * (q r : ℝ) ^ α ≤
      ((q r : ℝ) - ((q r - σ r : ℕ) : ℝ)) * (q r : ℝ) ^ α + Bm N * Bm N ^ α := by
    intro r
    have hBa : 0 ≤ Bm N * Bm N ^ α := mul_nonneg hB0 (Real.rpow_nonneg hB0 _)
    rcases le_or_gt (σ r) (q r) with h | h
    · rw [Nat.cast_sub h]; nlinarith [hqa r]
    · have hz : q r - σ r = 0 := by omega
      rw [hz, Nat.cast_zero, sub_zero]
      have hs := sched_le N hσ r
      have hq : (q r : ℝ) ≤ Bm N := le_trans (by exact_mod_cast h.le) hs
      have := Real.rpow_le_rpow (Nat.cast_nonneg (q r)) hq hα.le
      have : (σ r : ℝ) * (q r : ℝ) ^ α ≤ Bm N * Bm N ^ α :=
        mul_le_mul hs this (hqa r) hB0
      nlinarith [hqa r, (Nat.cast_nonneg (q r) : (0:ℝ) ≤ q r)]
  have h3 : scheduleWeight α q σ ≤ ∑ r, (((q r : ℝ) - ((q r - σ r : ℕ) : ℝ)) * (q r : ℝ) ^ α +
      Bm N * Bm N ^ α) := Finset.sum_le_sum (fun r _ => h2 r)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
  have e : ∑ r, ((q r : ℝ) - ((q r - σ r : ℕ) : ℝ)) * (q r : ℝ) ^ α =
      ∑ r, (q r : ℝ) ^ α * (q r : ℝ) - ∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun r _ => by ring)
  linarith

/-- Main drift estimate. -/
lemma drift_main (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0) (δ : ℝ)
    (c : (R → ℕ) → ℝ) (hc0 : ∀ σ ∈ N.schedules, 0 ≤ c σ) (hc1 : (∑ σ ∈ N.schedules, c σ) = 1)
    (hcle : ∀ r, (lam r : ℝ) + δ ≤ ∑ σ ∈ N.schedules, c σ * (σ r : ℝ))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) (q : R → ℕ) :
    weightedDrift α (queueChain lam tie) q ≤
      -(δ * ∑ r, (q r : ℝ) ^ α) + Fintype.card R * (Bm N * Bm N ^ α) := by
  set U := ∑ r, (q r : ℝ) ^ α * (q r : ℝ) - ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ) +
        Fintype.card R * (Bm N * Bm N ^ α)
  have hqa : ∀ r, 0 ≤ (q r : ℝ) ^ α := fun r => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsupp : ∀ σ, tie q σ ≠ 0 → ∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ) ≤ U := by
    intro σ hσ
    obtain ⟨hσs, hmax⟩ := htie q σ hσ
    exact per_sched N α hα lam δ c hc0 hc1 hcle q σ hσs hmax
  have hU : 0 ≤ U := by
    obtain ⟨σ, hσ⟩ := (tie q).support_nonempty
    refine le_trans (Finset.sum_nonneg (fun r _ => mul_nonneg (hqa r) (Nat.cast_nonneg _)))
      (hsupp σ ((PMF.mem_support_iff _ _).1 hσ))
  -- average over the tie rule
  have hE : ∑ r, (q r : ℝ) ^ α * (Ex tie q r).toReal ≤ U := by
    have hen : ∑ r, ENNReal.ofReal ((q r : ℝ) ^ α) * Ex tie q r =
        ∑' σ, tie q σ * ENNReal.ofReal (∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ)) := by
      unfold Ex
      simp only [← ENNReal.tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr (fun σ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg (hqa r) (Nat.cast_nonneg _)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [ENNReal.ofReal_mul (hqa r), ENNReal.ofReal_natCast]; ring
    have hle : ∑ r, ENNReal.ofReal ((q r : ℝ) ^ α) * Ex tie q r ≤ ENNReal.ofReal U := by
      rw [hen]
      calc ∑' σ, tie q σ * ENNReal.ofReal (∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ))
          ≤ ∑' σ, tie q σ * ENNReal.ofReal U := by
            refine ENNReal.tsum_le_tsum (fun σ => ?_)
            by_cases h : tie q σ = 0
            · rw [h]; simp
            · exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hsupp σ h)) _
        _ = ENNReal.ofReal U := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    have hfin : ∀ r, ENNReal.ofReal ((q r : ℝ) ^ α) * Ex tie q r ≠ ⊤ :=
      fun r => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Ex_ne_top tie q r)
    have := ENNReal.toReal_le_of_le_ofReal hU hle
    rw [ENNReal.toReal_sum (fun r _ => hfin r)] at this
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hqa _)] using this
  unfold weightedDrift
  simp only [drift_formula]
  have e : ∑ r, (q r : ℝ) ^ α * ((Ex tie q r).toReal + lam r - q r) =
      ∑ r, (q r : ℝ) ^ α * (Ex tie q r).toReal + ∑ r, (q r : ℝ) ^ α * (lam r : ℝ) -
        ∑ r, (q r : ℝ) ^ α * (q r : ℝ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  have e2 : ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ) =
      ∑ r, (q r : ℝ) ^ α * (lam r : ℝ) + δ * ∑ r, (q r : ℝ) ^ α := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [e]
  simp only [U] at hE
  linarith

end X5WD


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5WD
open KellyStochasticNetworks.MaxWeight

variable {R : Type*} [Fintype R] [Nonempty R]

lemma norm_bound (α : ℝ) (hα : 0 < α) (q : R → ℕ) :
    queueNorm q ^ α ≤ Real.sqrt (Fintype.card R) ^ α * ∑ r, (q r : ℝ) ^ α := by
  obtain ⟨r0, -, hr0⟩ := Finset.exists_max_image Finset.univ (fun r => q r) Finset.univ_nonempty
  set m : ℝ := (q r0 : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have h1 : ∑ r, (q r : ℝ) ^ (2 : ℕ) ≤ Fintype.card R * m ^ 2 := by
    calc ∑ r, (q r : ℝ) ^ (2 : ℕ) ≤ ∑ _r : R, m ^ 2 := Finset.sum_le_sum (fun r _ => by
          have : (q r : ℝ) ≤ m := by simp only [m]; exact_mod_cast hr0 r (Finset.mem_univ r)
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2)
      _ = Fintype.card R * m ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : queueNorm q ≤ Real.sqrt (Fintype.card R) * m := by
    unfold queueNorm
    calc Real.sqrt (∑ r, (q r : ℝ) ^ (2 : ℕ)) ≤ Real.sqrt (Fintype.card R * m ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (Fintype.card R) * m := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hm]
  have hn0 : 0 ≤ queueNorm q := Real.sqrt_nonneg _
  calc queueNorm q ^ α ≤ (Real.sqrt (Fintype.card R) * m) ^ α :=
        Real.rpow_le_rpow hn0 h2 hα.le
    _ = Real.sqrt (Fintype.card R) ^ α * m ^ α := Real.mul_rpow (Real.sqrt_nonneg _) hm
    _ ≤ Real.sqrt (Fintype.card R) ^ α * ∑ r, (q r : ℝ) ^ α := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        exact Finset.single_le_sum (f := fun r => (q r : ℝ) ^ α)
          (fun r _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.mem_univ r0)

theorem main (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) :
    (∀ q r, DriftIntegrable (queueChain lam tie) (fun x => (x r : ℝ)) q) ∧
    ∃ ε K b : ℝ, 0 < ε ∧ 0 < K ∧
      (∀ q, K < queueNorm q →
        weightedDrift α (queueChain lam tie) q < -ε * queueNorm q ^ α) ∧
      (∀ q, queueNorm q ≤ K → weightedDrift α (queueChain lam tie) q < b) := by
  refine ⟨fun q r => integrable lam tie q r, ?_⟩
  obtain ⟨δ, hδ, c, hc0, hc1, hcle⟩ := interior_slack N lam hlam
  set C0 : ℝ := Fintype.card R * (Bm N * Bm N ^ α)
  have hB0 : 0 ≤ Bm N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hC0 : 0 ≤ C0 := by positivity
  set s : ℝ := Real.sqrt (Fintype.card R) ^ α
  have hs : 0 < s := Real.rpow_pos_of_pos (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)) _
  have hD := fun q => drift_main N α hα lam δ c hc0 hc1 hcle tie htie q
  set x : ℝ := 2 * C0 * s / δ + 1
  have hx : 0 < x := by positivity
  refine ⟨δ / (2 * s), x ^ α⁻¹, C0 + 1, by positivity, Real.rpow_pos_of_pos hx _, ?_, ?_⟩
  · intro q hq
    have hK : (x ^ α⁻¹) ^ α < queueNorm q ^ α :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hx.le _) hq hα
    rw [Real.rpow_inv_rpow hx.le hα.ne'] at hK
    have hnb := norm_bound α hα q
    have hsum : queueNorm q ^ α / s ≤ ∑ r, (q r : ℝ) ^ α := by
      rw [div_le_iff₀ hs]; linarith
    have h1 := hD q
    have h2 : 2 * C0 * s / δ < queueNorm q ^ α := by linarith
    rw [div_lt_iff₀ hδ] at h2
    have h3 : δ * (queueNorm q ^ α / s) ≤ δ * ∑ r, (q r : ℝ) ^ α :=
      mul_le_mul_of_nonneg_left hsum hδ.le
    have e1 : δ * (queueNorm q ^ α / s) = δ / s * queueNorm q ^ α := by ring
    have e2 : δ / (2 * s) * queueNorm q ^ α = δ / s * queueNorm q ^ α / 2 := by ring
    have h4 : C0 < δ / s * queueNorm q ^ α / 2 := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0:ℝ) < 2), div_mul_eq_mul_div,
        lt_div_iff₀ hs] at *
      nlinarith
    linarith
  · intro q _
    have h1 := hD q
    have : 0 ≤ δ * ∑ r, (q r : ℝ) ^ α :=
      mul_nonneg hδ.le (Finset.sum_nonneg (fun r _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    linarith

end X5WD


namespace X5PR

/-- Tangent line below `t ↦ t^p`, `p ≥ 1`. -/
lemma tangent_le {p x y : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ p + p * x ^ (p - 1) * (y - x) ≤ y ^ p := by
  rcases hx.lt_or_eq with hx | hx
  · have hs : (-1:ℝ) ≤ y / x - 1 := by have : 0 ≤ y / x := by positivity
                                       linarith
    have hb := one_add_mul_self_le_rpow_one_add hs hp
    rw [add_sub_cancel, Real.div_rpow hy hx.le] at hb
    have hpos : 0 < x ^ p := Real.rpow_pos_of_pos hx p
    rw [le_div_iff₀ hpos] at hb
    have hsub : x ^ (p - 1) = x ^ p / x := Real.rpow_sub_one hx.ne' p
    rw [hsub]
    have : (1 + p * (y / x - 1)) * x ^ p = x ^ p + p * (x ^ p / x) * (y - x) := by
      field_simp
    linarith
  · subst hx
    rcases (show (0:ℝ) ≤ p - 1 by linarith).lt_or_eq with h | h
    · rw [Real.zero_rpow h.ne', Real.zero_rpow (by linarith)]; simp
      exact Real.rpow_nonneg hy _
    · have hp1 : p = 1 := by linarith
      subst hp1; simp

/-- The second-order remainder of `t^(α+1)/(α+1)` at `x`. -/
noncomputable def err (α x y : ℝ) : ℝ := (y ^ (α + 1) - x ^ (α + 1)) / (α + 1) - x ^ α * (y - x)

lemma err_nonneg {α x y : ℝ} (hα : 0 < α) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ err α x y := by
  have h := tangent_le (p := α + 1) (by linarith) hx hy
  rw [add_sub_cancel_right] at h
  unfold err
  rw [sub_nonneg, le_div_iff₀ (by linarith)]
  nlinarith

lemma err_le {α x y : ℝ} (hα : 0 < α) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    err α x y ≤ (y ^ α - x ^ α) * (y - x) := by
  have h := tangent_le (p := α + 1) (by linarith) hy hx
  rw [add_sub_cancel_right] at h
  unfold err
  rw [sub_le_iff_le_add, div_le_iff₀ (by linarith)]
  nlinarith

/-- Bound of the remainder by a moment of the jump size `Z ≥ |y - x|`. -/
noncomputable def cfac (α x : ℝ) : ℝ := if α ≤ 1 then 1 else α * (x + 1) ^ (α - 1)

lemma err_le_Z {α x y Z : ℝ} (hα : 0 < α) (hx : 0 ≤ x) (hy : 0 ≤ y) (hZ : |y - x| ≤ Z) :
    err α x y ≤ cfac α x * (1 + Z) ^ (α + 1) := by
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) hZ
  have h1 := err_le hα hx hy
  have hprod : (y ^ α - x ^ α) * (y - x) ≤ |y ^ α - x ^ α| * |y - x| := by
    rw [← abs_mul]; exact le_abs_self _
  have hZ1 : 0 < 1 + Z := by linarith
  unfold cfac
  split_ifs with ha
  · -- α ≤ 1: subadditivity
    have hsub : |y ^ α - x ^ α| ≤ |y - x| ^ α := by
      rcases le_total x y with hxy | hxy
      · have := Real.rpow_add_le_add_rpow hx (sub_nonneg.2 hxy) hα.le ha
        rw [add_sub_cancel] at this
        rw [abs_of_nonneg (by linarith [Real.rpow_le_rpow hx hxy hα.le]),
          abs_of_nonneg (sub_nonneg.2 hxy)]
        linarith
      · have := Real.rpow_add_le_add_rpow hy (sub_nonneg.2 hxy) hα.le ha
        rw [add_sub_cancel] at this
        rw [abs_of_nonpos (by linarith [Real.rpow_le_rpow hy hxy hα.le]),
          abs_of_nonpos (by linarith), neg_sub, neg_sub]
        linarith
    have h2 : |y - x| ^ α ≤ (1 + Z) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith) hα.le
    have h3 : |y ^ α - x ^ α| * |y - x| ≤ (1 + Z) ^ α * (1 + Z) :=
      mul_le_mul (hsub.trans h2) (by linarith) (abs_nonneg _) (Real.rpow_nonneg hZ1.le _)
    rw [Real.rpow_add_one hZ1.ne', one_mul]
    linarith
  · push_neg at ha
    -- α > 1: mean value via tangent lines
    have hm : |y ^ α - x ^ α| ≤ α * (x + Z) ^ (α - 1) * |y - x| := by
      rcases le_total x y with hxy | hxy
      · have t := tangent_le (p := α) ha.le hy hx
        have hyZ : y ≤ x + Z := by have := le_abs_self (y - x); linarith
        have hmono : y ^ (α - 1) ≤ (x + Z) ^ (α - 1) :=
          Real.rpow_le_rpow hy hyZ (by linarith)
        rw [abs_of_nonneg (by linarith [Real.rpow_le_rpow hx hxy hα.le]),
          abs_of_nonneg (sub_nonneg.2 hxy)]
        have : α * y ^ (α - 1) * (y - x) ≤ α * (x + Z) ^ (α - 1) * (y - x) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hmono hα.le
        nlinarith
      · have t := tangent_le (p := α) ha.le hx hy
        have hmono : x ^ (α - 1) ≤ (x + Z) ^ (α - 1) :=
          Real.rpow_le_rpow hx (by linarith) (by linarith)
        rw [abs_of_nonpos (by linarith [Real.rpow_le_rpow hy hxy hα.le]),
          abs_of_nonpos (by linarith)]
        have : α * x ^ (α - 1) * (x - y) ≤ α * (x + Z) ^ (α - 1) * (x - y) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hmono hα.le
        nlinarith
    have hxz : x + Z ≤ (x + 1) * (1 + Z) := by nlinarith
    have h4 : (x + Z) ^ (α - 1) ≤ (x + 1) ^ (α - 1) * (1 + Z) ^ (α - 1) := by
      rw [← Real.mul_rpow (by linarith) hZ1.le]
      exact Real.rpow_le_rpow (by linarith) hxz (by linarith)
    have h5 : |y ^ α - x ^ α| * |y - x| ≤ α * ((x + 1) ^ (α - 1) * (1 + Z) ^ (α - 1)) * (Z * Z) := by
      calc |y ^ α - x ^ α| * |y - x| ≤ α * (x + Z) ^ (α - 1) * |y - x| * |y - x| :=
            mul_le_mul_of_nonneg_right hm (abs_nonneg _)
        _ ≤ α * ((x + 1) ^ (α - 1) * (1 + Z) ^ (α - 1)) * (Z * Z) := by
            rw [mul_assoc]
            apply mul_le_mul (mul_le_mul_of_nonneg_left h4 hα.le)
              (mul_le_mul hZ hZ (abs_nonneg _) hZ0) (by positivity) (by positivity)
    have e : (1 + Z) ^ (α + 1) = (1 + Z) ^ (α - 1) * ((1 + Z) * (1 + Z)) := by
      rw [show α + 1 = (α - 1) + 1 + 1 by ring, Real.rpow_add_one hZ1.ne',
        Real.rpow_add_one hZ1.ne']; ring
    have h6 : α * ((x + 1) ^ (α - 1) * (1 + Z) ^ (α - 1)) * (Z * Z) ≤
        α * (x + 1) ^ (α - 1) * (1 + Z) ^ (α + 1) := by
      rw [e]
      have : Z * Z ≤ (1 + Z) * (1 + Z) := by nlinarith
      have hp : 0 ≤ α * (x + 1) ^ (α - 1) * (1 + Z) ^ (α - 1) := by positivity
      nlinarith
    linarith

lemma cfac_nonneg {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) : 0 ≤ cfac α x := by
  unfold cfac; split_ifs
  · norm_num
  · have : 0 ≤ x + 1 := by linarith
    positivity

/-- `cfac α x = o(x^α)`. -/
lemma cfac_le {α : ℝ} (hα : 0 < α) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → cfac α x ≤ η * x ^ α + C := by
  unfold cfac
  rcases le_or_gt α 1 with h1 | h1
  · refine ⟨1, zero_le_one, fun x hx => ?_⟩
    rw [if_pos h1]; have := Real.rpow_nonneg hx α; nlinarith
  · set T : ℝ := max 1 (α * 2 ^ (α - 1) / η)
    have hT1 : 1 ≤ T := le_max_left _ _
    refine ⟨α * (T + 1) ^ (α - 1), by positivity, fun x hx => ?_⟩
    rw [if_neg (not_le.2 h1)]
    have hα1 : 0 ≤ α - 1 := by linarith
    have hxa : 0 ≤ η * x ^ α := mul_nonneg hη.le (Real.rpow_nonneg hx _)
    rcases le_or_gt x T with hxT | hxT
    · have : (x + 1) ^ (α - 1) ≤ (T + 1) ^ (α - 1) :=
        Real.rpow_le_rpow (by linarith) (by linarith) hα1
      nlinarith
    · have hx1 : 1 ≤ x := le_trans hT1 hxT.le
      have hxpos : 0 < x := by linarith
      have h2 : (x + 1) ^ (α - 1) ≤ (2 * x) ^ (α - 1) :=
        Real.rpow_le_rpow (by linarith) (by linarith) hα1
      rw [Real.mul_rpow (by norm_num) hxpos.le, Real.rpow_sub_one hxpos.ne'] at h2
      have hKx : α * 2 ^ (α - 1) / η ≤ x := le_trans (le_max_right _ _) hxT.le
      have hKx' : α * 2 ^ (α - 1) ≤ η * x := by rw [div_le_iff₀ hη] at hKx; linarith
      have hxa' : 0 ≤ x ^ α := Real.rpow_nonneg hx _
      have h3 : α * (x + 1) ^ (α - 1) ≤ α * 2 ^ (α - 1) * (x ^ α / x) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hα.le
      have h4 : α * 2 ^ (α - 1) * (x ^ α / x) ≤ η * x ^ α := by
        rw [mul_div_assoc', div_le_iff₀ hxpos]; nlinarith
      have : 0 ≤ α * (T + 1) ^ (α - 1) := by positivity
      linarith

end X5PR


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5PR
open KellyStochasticNetworks.MaxWeight X5WD

variable {R : Type*} [Fintype R]

noncomputable def Lq (α : ℝ) (q : R → ℕ) : ℝ := ∑ r, (q r : ℝ) ^ (α + 1) / (α + 1)

lemma Lq_nonneg (α : ℝ) (hα : 0 < α) (q : R → ℕ) : 0 ≤ Lq α q :=
  Finset.sum_nonneg (fun r _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith))

lemma L_diff (α : ℝ) (q j : R → ℕ) :
    Lq α j - Lq α q = ∑ r, ((q r : ℝ) ^ α * ((j r : ℝ) - q r) + err α (q r) (j r)) := by
  unfold Lq err
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun r _ => by ring)

lemma arr_marg (lam : R → ℝ≥0) (r : R) (f : ℕ → ℝ≥0∞) :
    ∑' a, arrivalLaw lam a * f (a r) = ∫⁻ x, f x ∂(poissonMeasure (lam r)) := by
  unfold arrivalLaw
  simp only [Measure.toPMF_apply]
  have : ∑' a : R → ℕ, (Measure.pi fun r => poissonMeasure (lam r)) {a} * f (a r) =
      ∫⁻ a : R → ℕ, f (a r) ∂(Measure.pi fun r => poissonMeasure (lam r)) := by
    rw [lintegral_countable']; exact tsum_congr (fun a => mul_comm _ _)
  rw [this]
  exact (measurePreserving_eval (fun r => poissonMeasure (lam r)) r).lintegral_comp
    (f := f) (measurable_of_countable _)

/-- The moment `E (1 + a_r + B)^(α+1)`. -/
noncomputable def Mr (N : Network R) (α : ℝ) (lam : R → ℝ≥0) (r : R) : ℝ≥0∞ :=
  ∫⁻ x : ℕ, ENNReal.ofReal ((1 + (x : ℝ) + Bm N) ^ (α + 1)) ∂(poissonMeasure (lam r))

lemma Mr_lt_top (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0) (r : R) :
    Mr N α lam r < ⊤ := by
  set Bn : ℕ := ∑ r, serviceBound N r + 1
  have hBn : (1 : ℝ) + Bm N = Bn := by unfold Bm; simp only [Bn]; push_cast; ring
  have hint := ((poisson_envelope_moments (lam r) Bn α 1 hα one_pos).1 (α + 1) (by linarith))
  have h2 := (hint.const_mul ((2:ℝ) ^ (α + 1))).lintegral_lt_top
  refine lt_of_le_of_lt (lintegral_mono (fun x => ?_)) h2
  apply ENNReal.ofReal_le_ofReal
  unfold incrementEnvelope
  rw [← Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
  apply Real.rpow_le_rpow (by unfold Bm; positivity) _ (by linarith)
  have : (1 : ℝ) + x + Bm N = x + Bn := by rw [← hBn]; ring
  rw [this]
  have h1 : (x : ℝ) ≤ ((max x Bn : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
  have h2 : (Bn : ℝ) ≤ ((max x Bn : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  linarith

variable (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie)
include hα htie

lemma exp_err (q : R → ℕ) (r : R) :
    ∑' j, queueChain lam tie q j * ENNReal.ofReal (err α (q r) (j r)) ≤
      ENNReal.ofReal (cfac α (q r)) * Mr N α lam r := by
  rw [chain_exp]
  calc ∑' σ, tie q σ * ∑' a, arrivalLaw lam a * ENNReal.ofReal (err α (q r) (nextQueue q σ a r))
      ≤ ∑' σ, tie q σ * (ENNReal.ofReal (cfac α (q r)) * Mr N α lam r) := by
        refine ENNReal.tsum_le_tsum (fun σ => ?_)
        by_cases h0 : tie q σ = 0
        · rw [h0]; simp
        · refine mul_le_mul_right ?_ _
          have hσ := (htie q σ h0).1
          have hs := sched_le N hσ r
          unfold Mr
          rw [← arr_marg lam r, ← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum (fun a => ?_)
          rw [mul_left_comm]
          refine mul_le_mul_right ?_ _
          rw [← ENNReal.ofReal_mul (cfac_nonneg hα (Nat.cast_nonneg _))]
          apply ENNReal.ofReal_le_ofReal
          have hZ : |((nextQueue q σ a r : ℕ) : ℝ) - q r| ≤ (a r : ℝ) + Bm N := by
            rw [next_cast]
            have h1 : (q r : ℝ) - σ r ≤ ((q r - σ r : ℕ) : ℝ) := by
              rcases le_total (σ r) (q r) with h | h
              · rw [Nat.cast_sub h]
              · rw [Nat.sub_eq_zero_of_le h]; push_cast; linarith [(by exact_mod_cast h : (q r : ℝ) ≤ σ r)]
            have h2 : ((q r - σ r : ℕ) : ℝ) ≤ q r := by exact_mod_cast Nat.sub_le _ _
            have h3 : (0:ℝ) ≤ a r := Nat.cast_nonneg _
            rw [abs_le]; constructor <;> linarith
          have := err_le_Z hα (Nat.cast_nonneg (q r)) (Nat.cast_nonneg (nextQueue q σ a r)) hZ
          calc err α (q r) (nextQueue q σ a r) ≤ cfac α (q r) * (1 + ((a r : ℝ) + Bm N)) ^ (α + 1) := this
            _ = cfac α (q r) * (1 + (a r : ℝ) + Bm N) ^ (α + 1) := by ring_nf
    _ = ENNReal.ofReal (cfac α (q r)) * Mr N α lam r := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma err_summable (q : R → ℕ) (r : R) :
    Summable (fun j => (queueChain lam tie q j).toReal * err α (q r) (j r)) := by
  have hfin : ∑' j, queueChain lam tie q j * ENNReal.ofReal (err α (q r) (j r)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Mr_lt_top N α hα lam r).ne)
      (exp_err N α hα lam tie htie q r)
  refine (ENNReal.summable_toReal hfin).congr (fun j => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (err_nonneg hα (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

lemma err_exp_real (q : R → ℕ) (r : R) :
    ∑' j, (queueChain lam tie q j).toReal * err α (q r) (j r) ≤
      cfac α (q r) * (Mr N α lam r).toReal := by
  have hne : ∀ j, queueChain lam tie q j ≠ ⊤ := PMF.apply_ne_top _
  have h := exp_err N α hα lam tie htie q r
  have hfin : ENNReal.ofReal (cfac α (q r)) * Mr N α lam r ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Mr_lt_top N α hα lam r).ne
  have := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (cfac_nonneg hα (Nat.cast_nonneg _))] at this
  rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.mul_ne_top (hne j) ENNReal.ofReal_ne_top)] at this
  refine le_trans (le_of_eq (tsum_congr (fun j => ?_))) this
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (err_nonneg hα (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

lemma L_integrable (q : R → ℕ) : DriftIntegrable (queueChain lam tie) (Lq α) q := by
  unfold DriftIntegrable
  have hs : Summable (fun j => ∑ r, ((q r : ℝ) ^ α *
      ((queueChain lam tie q j).toReal * |(j r : ℝ) - q r|) +
      (queueChain lam tie q j).toReal * err α (q r) (j r))) :=
    summable_sum (fun r _ => ((integrable lam tie q r).mul_left _).add
      (err_summable N α hα lam tie htie q r))
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
    (fun j => ?_) hs
  rw [L_diff]
  have hP := (ENNReal.toReal_nonneg : 0 ≤ (queueChain lam tie q j).toReal)
  calc (queueChain lam tie q j).toReal *
        |∑ r, ((q r : ℝ) ^ α * ((j r : ℝ) - q r) + err α (q r) (j r))|
      ≤ (queueChain lam tie q j).toReal *
          ∑ r, ((q r : ℝ) ^ α * |(j r : ℝ) - q r| + err α (q r) (j r)) := by
        apply mul_le_mul_of_nonneg_left _ hP
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
        have he := err_nonneg hα (Nat.cast_nonneg (q r)) (Nat.cast_nonneg (j r))
        have hq := Real.rpow_nonneg (Nat.cast_nonneg (q r)) α
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hq, abs_of_nonneg he]
    _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun r _ => by ring)

lemma L_drift (q : R → ℕ) :
    drift (queueChain lam tie) (Lq α) q = weightedDrift α (queueChain lam tie) q +
      ∑ r, ∑' j, (queueChain lam tie q j).toReal * err α (q r) (j r) := by
  set P := queueChain lam tie
  have h1 : ∀ r, Summable (fun j => (P q j).toReal * ((j r : ℝ) - q r)) := fun r =>
    Summable.of_norm ((integrable lam tie q r).congr (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]))
  have hsplit : ∀ j, (P q j).toReal * (Lq α j - Lq α q) =
      ∑ r, ((q r : ℝ) ^ α * ((P q j).toReal * ((j r : ℝ) - q r)) +
        (P q j).toReal * err α (q r) (j r)) := by
    intro j; rw [L_diff, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  unfold drift weightedDrift
  simp only [hsplit]
  rw [Summable.tsum_finsetSum (fun r _ => ((h1 r).mul_left _).add
    (err_summable N α hα lam tie htie q r)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [((h1 r).mul_left _).tsum_add (err_summable N α hα lam tie htie q r), tsum_mul_left]
  rfl

end X5PR


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5PR
open KellyStochasticNetworks.MaxWeight X5WD

variable {R : Type*} [Fintype R]

lemma lam_pos (N : Network R) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N)) (r : R) : 0 < lam r := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hlam
  obtain ⟨ε, hε, hball⟩ := hlam
  set v : R → ℝ := fun r' => (lam r' : ℝ) - (if r' = r then ε / 2 else 0)
  have hv : v ∈ capacityRegion N := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro r'
    rw [Real.dist_eq]
    simp only [v]
    split_ifs
    · rw [show (lam r' : ℝ) - ε / 2 - lam r' = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith
    · simp [hε]
  have := hv.1 r
  change 0 ≤ (lam r : ℝ) - (if r = r then ε / 2 else 0) at this
  rw [if_pos rfl] at this
  have : (0:ℝ) < lam r := by linarith
  exact_mod_cast this

lemma unit_sched (N : Network R) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N)) (r : R) :
    Pi.single r 1 ∈ N.schedules := by
  obtain ⟨δ, hδ, c, hc0, hc1, hcle⟩ := interior_slack N lam hlam
  by_contra hno
  have hall : ∀ σ ∈ N.schedules, σ r = 0 := by
    intro σ hσ
    by_contra h
    apply hno
    apply N.downward σ hσ
    intro r'
    by_cases h' : r' = r
    · subst h'; simp; omega
    · simp [Pi.single_apply, h']
  have := hcle r
  rw [Finset.sum_eq_zero (fun σ hσ => by rw [hall σ hσ]; simp)] at this
  have : (0:ℝ) ≤ lam r := NNReal.coe_nonneg _
  linarith

lemma arr_pos (lam : R → ℝ≥0) (hpos : ∀ r, 0 < lam r) (a : R → ℕ) : 0 < arrivalLaw lam a := by
  unfold arrivalLaw
  rw [Measure.toPMF_apply, ← Set.univ_pi_singleton, Measure.pi_pi]
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro r _
  rw [poissonMeasure_singleton]
  apply ne_of_gt
  rw [ENNReal.ofReal_pos]
  have := hpos r
  have : (0:ℝ) < lam r := by exact_mod_cast this
  positivity

lemma P_ge (lam : R → ℝ≥0) (tie : (R → ℕ) → PMF (R → ℕ)) (q σ a : R → ℕ) :
    tie q σ * arrivalLaw lam a ≤ queueChain lam tie q (nextQueue q σ a) := by
  unfold queueChain
  rw [PMF.bind_apply]
  refine le_trans ?_ (ENNReal.le_tsum σ)
  refine mul_le_mul_right ?_ _
  rw [PMF.map_apply]
  refine le_trans ?_ (ENNReal.le_tsum a)
  simp

lemma step_down (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie)
    (q : R → ℕ) (hq : q ≠ 0) :
    ∃ σ, tie q σ ≠ 0 ∧ ∑ r, nextQueue q σ 0 r < ∑ r, q r := by
  obtain ⟨σ, hσ⟩ := (tie q).support_nonempty
  have hσ' : tie q σ ≠ 0 := (PMF.mem_support_iff _ _).1 hσ
  refine ⟨σ, hσ', ?_⟩
  obtain ⟨hσs, hmax⟩ := htie q σ hσ'
  obtain ⟨r0, hr0⟩ : ∃ r0, q r0 ≠ 0 := by
    by_contra h; push_neg at h; exact hq (funext h)
  have hpos0 : 0 < scheduleWeight α q (Pi.single r0 1) := by
    unfold scheduleWeight
    rw [Finset.sum_eq_single r0]
    · simp only [Pi.single_eq_same, Nat.cast_one, one_mul]
      exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hr0) _
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hWσ := lt_of_lt_of_le hpos0 (hmax _ (unit_sched N lam hlam r0))
  obtain ⟨r, hr⟩ : ∃ r, σ r ≠ 0 ∧ q r ≠ 0 := by
    by_contra h
    push_neg at h
    have : scheduleWeight α q σ = 0 := by
      unfold scheduleWeight
      refine Finset.sum_eq_zero (fun r _ => ?_)
      by_cases hs : σ r = 0
      · simp [hs]
      · rw [h r hs]; simp [Real.zero_rpow hα.ne']
    linarith
  apply Finset.sum_lt_sum
  · intro i _; unfold nextQueue; simp only [Pi.zero_apply]; omega
  · exact ⟨r, Finset.mem_univ r, by unfold nextQueue; simp only [Pi.zero_apply]; omega⟩

theorem irreducible (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) :
    Irreducible (queueChain lam tie) := by
  have hpos := lam_pos N lam hlam
  intro q q'
  induction hs : ∑ r, q r using Nat.strong_induction_on generalizing q with
  | _ s ih =>
    by_cases hq : q = 0
    · subst hq
      obtain ⟨σ, hσ⟩ := (tie 0).support_nonempty
      have hσ' : tie 0 σ ≠ 0 := (PMF.mem_support_iff _ _).1 hσ
      refine ⟨1, ?_⟩
      simp only [transitionPower]
      refine lt_of_lt_of_le ?_ (ENNReal.le_tsum q')
      rw [if_pos rfl, mul_one]
      have hn : nextQueue 0 σ q' = q' := by funext r; simp [nextQueue]
      have := P_ge lam tie 0 σ q'
      rw [hn] at this
      exact lt_of_lt_of_le (ENNReal.mul_pos hσ' (arr_pos lam hpos q').ne') this
    · obtain ⟨σ, hσ, hlt⟩ := step_down N α hα lam hlam tie htie q hq
      obtain ⟨n, hn⟩ := ih _ (hs ▸ hlt) (nextQueue q σ 0) rfl
      refine ⟨n + 1, ?_⟩
      simp only [transitionPower]
      refine lt_of_lt_of_le ?_ (ENNReal.le_tsum (nextQueue q σ 0))
      have hP := lt_of_lt_of_le (ENNReal.mul_pos hσ (arr_pos lam hpos 0).ne') (P_ge lam tie q σ 0)
      exact ENNReal.mul_pos hP.ne' hn.ne'

end X5PR


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5PR
open KellyStochasticNetworks.MaxWeight X5WD

variable {R : Type*} [Fintype R] [Nonempty R]

theorem main (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) :
    PositiveRecurrent (queueChain lam tie) := by
  obtain ⟨δ, hδ, c, hc0, hc1, hcle⟩ := interior_slack N lam hlam
  set C0 : ℝ := Fintype.card R * (Bm N * Bm N ^ α)
  have hB0 : 0 ≤ Bm N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hC0 : 0 ≤ C0 := by positivity
  set Ms : ℝ := ∑ r, (Mr N α lam r).toReal + 1
  have hMs : 0 < Ms := by
    have : 0 ≤ ∑ r, (Mr N α lam r).toReal := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    linarith
  have hMr : ∀ r, (Mr N α lam r).toReal ≤ Ms := by
    intro r
    have := Finset.single_le_sum (f := fun r => (Mr N α lam r).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ r)
    simp only [Ms]; linarith
  obtain ⟨C', hC', hcf⟩ := cfac_le hα (η := δ / (2 * Ms)) (by positivity)
  set C3 : ℝ := C0 + Fintype.card R * (C' * Ms)
  have hC3 : 0 ≤ C3 := by positivity
  -- drift bound for the Lyapunov function
  have hdrift : ∀ q, drift (queueChain lam tie) (Lq α) q ≤ -(δ / 2 * ∑ r, (q r : ℝ) ^ α) + C3 := by
    intro q
    rw [L_drift N α hα lam tie htie q]
    have h1 := drift_main N α hα lam δ c hc0 hc1 hcle tie htie q
    have h2 : ∑ r, ∑' j, (queueChain lam tie q j).toReal * err α (q r) (j r) ≤
        ∑ r, (δ / 2 * (q r : ℝ) ^ α + C' * Ms) := by
      refine Finset.sum_le_sum (fun r _ => ?_)
      refine (err_exp_real N α hα lam tie htie q r).trans ?_
      have hc := cfac_nonneg hα (Nat.cast_nonneg (q r) : (0:ℝ) ≤ q r)
      calc cfac α (q r) * (Mr N α lam r).toReal ≤ cfac α (q r) * Ms :=
            mul_le_mul_of_nonneg_left (hMr r) hc
        _ ≤ (δ / (2 * Ms) * (q r : ℝ) ^ α + C') * Ms :=
            mul_le_mul_of_nonneg_right (hcf _ (Nat.cast_nonneg _)) hMs.le
        _ = δ / 2 * (q r : ℝ) ^ α + C' * Ms := by field_simp
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h2
    simp only [C3]
    linarith
  -- the finite exceptional set
  set T : ℝ := 2 * (C3 + 1) / δ
  have hT : 0 ≤ T := by positivity
  set M0 : ℕ := ⌈T ^ α⁻¹⌉₊
  set K : Finset (R → ℕ) := Fintype.piFinset (fun _ => Finset.range (M0 + 1))
  have hbound : ∀ q, drift (queueChain lam tie) (Lq α) q ≤ if q ∈ K then (C3 + 1) - 1 else -1 := by
    intro q
    have hS : 0 ≤ ∑ r, (q r : ℝ) ^ α :=
      Finset.sum_nonneg (fun r _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    split_ifs with hq
    · have := hdrift q; nlinarith
    · simp only [K, Fintype.mem_piFinset, Finset.mem_range, not_forall, not_lt] at hq
      obtain ⟨r, hr⟩ := hq
      have hr' : T ^ α⁻¹ ≤ (q r : ℝ) := by
        calc T ^ α⁻¹ ≤ (M0 : ℝ) := Nat.le_ceil _
          _ ≤ q r := by exact_mod_cast (by omega : M0 ≤ q r)
      have h1 : T ≤ (q r : ℝ) ^ α := by
        calc T = (T ^ α⁻¹) ^ α := (Real.rpow_inv_rpow hT hα.ne').symm
          _ ≤ (q r : ℝ) ^ α := Real.rpow_le_rpow (Real.rpow_nonneg hT _) hr' hα.le
      have h2 : (q r : ℝ) ^ α ≤ ∑ r, (q r : ℝ) ^ α :=
        Finset.single_le_sum (f := fun r => (q r : ℝ) ^ α)
          (fun r _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.mem_univ r)
      have hTd : δ / 2 * T = C3 + 1 := by simp only [T]; field_simp
      have := hdrift q
      have : δ / 2 * T ≤ δ / 2 * ∑ r, (q r : ℝ) ^ α :=
        mul_le_mul_of_nonneg_left (le_trans h1 h2) (by linarith)
      linarith
  exact (X5FL.main (queueChain lam tie) (irreducible N α hα lam hlam tie htie) (Lq α)
    (Lq_nonneg α hα) 1 (C3 + 1) one_pos K (L_integrable N α hα lam tie htie)
    (fun q => by convert hbound q using 2)).2

end X5PR


open KellyStochasticNetworks.MaxWeight in
theorem solution {R : Type*} [Fintype R] [Nonempty R]
    (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) :
    PositiveRecurrent (queueChain lam tie) :=
  X5PR.main N α hα lam hlam tie htie
