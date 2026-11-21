-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T19:51:01.771685+00:00
-- url     : https://prove2.me/submissions/6253df0d-bd4c-477b-90ac-ab2f92484a9f

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings

section
/-! Helpers for Lemma B.1: a maximal separated subset of an integer grid, counted with a
discrete Gaussian (Markov) bound, and real pigeonhole. -/

namespace MulticlassOmni.Dev.B1

open Finset

theorem exp_neg_sq_le (i : ℕ) : Real.exp (-(i:ℝ) ^ 2) ≤ (1 / 2 : ℝ) ^ i := by
  have h1 : Real.exp (-(i:ℝ) ^ 2) ≤ Real.exp (-(i:ℝ)) := by
    apply Real.exp_le_exp.2
    have : (i:ℝ) ≤ (i:ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · simp [h]
      · have : (1:ℝ) ≤ i := by exact_mod_cast h
        nlinarith
    linarith
  have h2 : Real.exp (-(i:ℝ)) = (Real.exp (-1)) ^ i := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h3 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have := Real.add_one_le_exp 1
    linarith
  rw [h2] at h1
  exact h1.trans (pow_le_pow_left₀ (by positivity) h3 i)

theorem coord_sum (m a : ℕ) : ∑ j ∈ range m, Real.exp (-((j:ℝ) - a) ^ 2) ≤ 4 := by
  set g1 : ℕ → ℝ := fun j => if a ≤ j then (1 / 2 : ℝ) ^ (j - a) else 0 with hg1
  set g2 : ℕ → ℝ := fun j => if j < a then (1 / 2 : ℝ) ^ (a - j) else 0 with hg2
  have hg1n : ∀ j, 0 ≤ g1 j := fun j => by simp only [hg1]; split_ifs <;> positivity
  have hg2n : ∀ j, 0 ≤ g2 j := fun j => by simp only [hg2]; split_ifs <;> positivity
  have hpt : ∀ j : ℕ, Real.exp (-((j:ℝ) - a) ^ 2) ≤ g1 j + g2 j := by
    intro j
    by_cases h : a ≤ j
    · have e : (j:ℝ) - a = ((j - a : ℕ) : ℝ) := by push_cast [Nat.cast_sub h]; ring
      have : g2 j = 0 := by simp only [hg2]; rw [if_neg (by omega)]
      rw [this, add_zero, e]
      simp only [hg1, if_pos h]
      exact exp_neg_sq_le _
    · have e : ((j:ℝ) - a) ^ 2 = ((a - j : ℕ) : ℝ) ^ 2 := by
        push_cast [Nat.cast_sub (by omega : j ≤ a)]; ring
      have : g1 j = 0 := by simp only [hg1]; rw [if_neg h]
      rw [this, zero_add, e]
      simp only [hg2, if_pos (by omega : j < a)]
      exact exp_neg_sq_le _
  have hsum1 : ∑ j ∈ range m, g1 j ≤ 2 := by
    calc ∑ j ∈ range m, g1 j ≤ ∑ j ∈ range (a + m), g1 j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) (fun j _ _ => hg1n j)
      _ = ∑ j ∈ range a, g1 j + ∑ j ∈ range m, g1 (a + j) := sum_range_add _ _ _
      _ = ∑ j ∈ range m, (1 / 2 : ℝ) ^ j := by
          rw [sum_eq_zero (fun j hj => by
            simp only [hg1]; rw [if_neg (by simp at hj; omega)]), zero_add]
          apply sum_congr rfl
          intro j _
          simp only [hg1]; rw [if_pos (by omega)]; congr 1; omega
      _ ≤ 2 := sum_geometric_two_le m
  have hsum2 : ∑ j ∈ range m, g2 j ≤ 2 := by
    calc ∑ j ∈ range m, g2 j ≤ ∑ j ∈ range (a + m), g2 j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) (fun j _ _ => hg2n j)
      _ = ∑ j ∈ range a, g2 j + ∑ j ∈ range m, g2 (a + j) := sum_range_add _ _ _
      _ = ∑ j ∈ range a, (1 / 2 : ℝ) ^ (a - j) := by
          rw [sum_eq_zero (s := range m) (fun j _ => by
            simp only [hg2]; rw [if_neg (by omega)]), add_zero]
          apply sum_congr rfl
          intro j hj
          simp only [hg2]; rw [if_pos (by simp at hj; omega)]
      _ = ∑ j ∈ range a, (1 / 2 : ℝ) ^ (j + 1) := by
          rw [← sum_range_reflect (fun j => (1 / 2 : ℝ) ^ (j + 1)) a]
          apply sum_congr rfl
          intro j hj
          simp at hj
          congr 1; omega
      _ ≤ ∑ j ∈ range a, (1 / 2 : ℝ) ^ j :=
          sum_le_sum (fun j _ => pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
      _ ≤ 2 := sum_geometric_two_le a
  calc ∑ j ∈ range m, Real.exp (-((j:ℝ) - a) ^ 2) ≤ ∑ j ∈ range m, (g1 j + g2 j) :=
        sum_le_sum (fun j _ => hpt j)
    _ = ∑ j ∈ range m, g1 j + ∑ j ∈ range m, g2 j := sum_add_distrib
    _ ≤ 4 := by linarith

/-- the grid `{0, …, m-1}^k` -/
def grid (k m : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ => range m)

/-- squared Euclidean distance of two grid points -/
noncomputable def D {k : ℕ} (a b : Fin k → ℕ) : ℝ := ∑ y, ((a y : ℝ) - b y) ^ 2

theorem D_comm {k : ℕ} (a b : Fin k → ℕ) : D a b = D b a := by
  unfold D; exact sum_congr rfl (fun y _ => by ring)

theorem ball_card (k m : ℕ) (u : Fin k → ℕ) :
    ((((grid k m).filter (fun n => D n u < k)).card : ℕ) : ℝ) ≤ (4 * Real.exp 1) ^ k := by
  classical
  have h1 : ((((grid k m).filter (fun n => D n u < k)).card : ℕ) : ℝ)
      ≤ ∑ n ∈ grid k m, Real.exp (k - D n u) := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    calc ∑ n ∈ (grid k m).filter (fun n => D n u < k), ((1 : ℕ) : ℝ)
        ≤ ∑ n ∈ (grid k m).filter (fun n => D n u < k), Real.exp (k - D n u) := by
          apply sum_le_sum
          intro n hn
          rw [mem_filter] at hn
          push_cast
          exact Real.one_le_exp (by linarith [hn.2])
      _ ≤ ∑ n ∈ grid k m, Real.exp (k - D n u) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have h2 : ∑ n ∈ grid k m, Real.exp (k - D n u)
      = Real.exp k * ∏ y : Fin k, ∑ j ∈ range m, Real.exp (-((j:ℝ) - u y) ^ 2) := by
    rw [prod_univ_sum, mul_sum]
    apply sum_congr rfl
    intro n _
    rw [sub_eq_add_neg, Real.exp_add, D, ← sum_neg_distrib, Real.exp_sum]
  rw [h2] at h1
  calc _ ≤ _ := h1
    _ ≤ Real.exp k * ∏ _y : Fin k, (4:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact prod_le_prod (fun y _ => sum_nonneg (fun j _ => (Real.exp_pos _).le))
          (fun y _ => coord_sum m (u y))
    _ = (4 * Real.exp 1) ^ k := by
        rw [prod_const, card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul, mul_one]
        ring

/-- grid points pairwise at squared distance `≥ k` -/
def Sep {k : ℕ} (U : Finset (Fin k → ℕ)) : Prop := ∀ a ∈ U, ∀ b ∈ U, a ≠ b → (k:ℝ) ≤ D a b

theorem exists_sep (k m : ℕ) (hk : 0 < k) :
    ∃ U ⊆ grid k m, Sep U ∧ (m:ℝ) ^ k ≤ U.card * (4 * Real.exp 1) ^ k := by
  classical
  let P := (grid k m).powerset.filter (fun U => Sep U)
  have hP : P.Nonempty := ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by intro a ha; simp at ha⟩⟩
  obtain ⟨U, hU, hmax⟩ := exists_max_image P card hP
  rw [mem_filter, mem_powerset] at hU
  refine ⟨U, hU.1, hU.2, ?_⟩
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hcov : grid k m ⊆ U.biUnion (fun u => (grid k m).filter (fun n => D n u < k)) := by
    intro n hn
    by_cases hnU : n ∈ U
    · exact mem_biUnion.2 ⟨n, hnU, mem_filter.2 ⟨hn, by simp [D]; exact hk⟩⟩
    · by_contra hno
      have hfar : ∀ u ∈ U, (k:ℝ) ≤ D n u := by
        intro u hu
        by_contra hlt
        push Not at hlt
        exact hno (mem_biUnion.2 ⟨u, hu, mem_filter.2 ⟨hn, hlt⟩⟩)
      have hS : Sep (insert n U) := by
        intro a ha b hb hab
        rw [mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hfar b hb
        · rw [D_comm]; exact hfar a ha
        · exact hU.2 a ha b hb hab
      have := hmax (insert n U)
        (mem_filter.2 ⟨mem_powerset.2 (insert_subset hn hU.1), hS⟩)
      rw [card_insert_of_notMem hnU] at this
      omega
  have hcard : (((grid k m).card : ℕ) : ℝ)
      ≤ ∑ u ∈ U, ((((grid k m).filter (fun n => D n u < k)).card : ℕ) : ℝ) := by
    exact_mod_cast (card_le_card hcov).trans card_biUnion_le
  have hg : (grid k m).card = m ^ k := by simp [grid]
  rw [hg] at hcard
  push_cast at hcard
  calc (m:ℝ) ^ k ≤ _ := hcard
    _ ≤ ∑ _u ∈ U, (4 * Real.exp 1) ^ k := sum_le_sum (fun u _ => ball_card k m u)
    _ = U.card * (4 * Real.exp 1) ^ k := by rw [sum_const, nsmul_eq_mul]

/-- real-valued pigeonhole -/
theorem pigeon {α β : Type} [DecidableEq β] (s : Finset α) (hs : s.Nonempty) (t : Finset β)
    (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (B : ℝ) (hB : 0 < B) (ht : (t.card : ℝ) ≤ B) :
    ∃ b, (s.card : ℝ) / B ≤ ((s.filter (fun a => f a = b)).card : ℝ) := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := hs
  have htne : t.Nonempty := ⟨f a, hf a ha⟩
  have e := card_eq_sum_card_fiberwise hf
  set c := (s.card : ℝ) / B with hc
  have : ((s.card : ℕ) : ℝ) < ∑ _b ∈ t, c := by
    rw [e, Nat.cast_sum]
    exact sum_lt_sum_of_nonempty htne (fun b _ => h b)
  rw [sum_const, nsmul_eq_mul] at this
  have h2 : (t.card : ℝ) * ((s.card : ℝ) / B) ≤ B * ((s.card : ℝ) / B) :=
    mul_le_mul_of_nonneg_right ht (by positivity)
  rw [mul_div_cancel₀ _ hB.ne'] at h2
  linarith

/-- alternating `±1` with a final `0` when `k` is odd -/
noncomputable def sv (k : ℕ) (y : Fin k) : ℝ := if (y:ℕ) < 2 * (k / 2) then (-1) ^ (y:ℕ) else 0

theorem alt_sum (j : ℕ) : ∑ i ∈ range (2 * j), (-1 : ℝ) ^ i = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    rw [pow_succ, pow_mul]; simp

theorem sv_sum (k : ℕ) : ∑ y, sv k y = 0 := by
  unfold sv
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < 2 * (k / 2) then (-1 : ℝ) ^ i else 0) k]
  rw [← sum_range_add_sum_Ico _ (show 2 * (k / 2) ≤ k by omega)]
  rw [sum_congr rfl (fun i hi => if_pos (mem_range.1 hi)), alt_sum,
    sum_eq_zero (fun i hi => if_neg (by simp at hi; omega))]
  simp

theorem sv_sq (k : ℕ) : (k:ℝ) - 1 ≤ ∑ y, sv k y ^ 2 := by
  unfold sv
  have : ∀ y : Fin k, (if (y:ℕ) < 2 * (k / 2) then (-1 : ℝ) ^ (y:ℕ) else 0) ^ 2
      = (fun i : ℕ => if i < 2 * (k / 2) then (1:ℝ) else 0) y := by
    intro y; simp only; split_ifs <;> simp [← pow_mul, pow_mul']
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < 2 * (k / 2) then (1 : ℝ) else 0) k]
  rw [← sum_range_add_sum_Ico _ (show 2 * (k / 2) ≤ k by omega)]
  rw [sum_congr rfl (fun i hi => if_pos (mem_range.1 hi)),
    sum_eq_zero (fun i hi => if_neg (by simp at hi; omega))]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one, add_zero]
  have : k ≤ 2 * (k / 2) + 1 := by omega
  have : (k:ℝ) ≤ ((2 * (k / 2) : ℕ) : ℝ) + 1 := by exact_mod_cast this
  linarith

theorem sv_abs (k : ℕ) (y : Fin k) : |sv k y| ≤ 1 := by
  unfold sv; split_ifs <;> simp

end MulticlassOmni.Dev.B1
end

section
namespace MulticlassOmni.Dev.B1

open MulticlassOmni.Lipschitz Finset

theorem floor_close {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ⌊a⌋₊ = ⌊b⌋₊) : |a - b| < 1 := by
  have h1 := Nat.floor_le ha
  have h2 := Nat.lt_floor_add_one a
  have h3 := Nat.floor_le hb
  have h4 := Nat.lt_floor_add_one b
  rw [h] at h1 h2
  rw [abs_lt]; constructor <;> linarith

theorem le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih => have := Nat.one_le_two_pow (n := n); rw [pow_succ]; omega

set_option maxHeartbeats 1600000 in
/-- The core construction at grid scale `g`: a zero-sum packing at scale `g² / 25600`. -/
theorem core (k : ℕ) (hk : 3 ≤ k) (g : ℝ) (hg : 0 < g) (hg16 : g ≤ 1 / 16) :
    ∃ X : Finset (Fin k → ℝ), IsZeroSumPacking k (g ^ 2 / 25600) X ∧
      (1 / (64 * Real.exp 1 * g)) ^ k * (8 * g / k) * (g / 5) ≤ (X.card : ℝ) := by
  classical
  have hk0 : 0 < k := by omega
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  set m := ⌊1 / (8 * g)⌋₊ with hm
  have hm1 : (m:ℝ) ≤ 1 / (8 * g) := Nat.floor_le (by positivity)
  have hm2 : 1 / (16 * g) ≤ (m:ℝ) := by
    have := Nat.lt_floor_add_one (1 / (8 * g))
    have h1 : 1 ≤ 1 / (16 * g) := by rw [le_div_iff₀ (by positivity)]; linarith
    have : 1 / (8 * g) = 2 * (1 / (16 * g)) := by field_simp; ring
    linarith
  have hgm : g * m ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_left hm1 hg.le
    rwa [show g * (1 / (8 * g)) = 1 / 8 by field_simp] at this
  have hmpos : (0:ℝ) < m := lt_of_lt_of_le (by positivity) hm2
  obtain ⟨U, hUg, hUsep, hUcard⟩ := exists_sep k m hk0
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hUpos : (0:ℝ) < U.card := by
    by_contra h
    push Not at h
    have h1 : (U.card:ℝ) * (4 * Real.exp 1) ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    have : (0:ℝ) < (m:ℝ) ^ k := by positivity
    linarith
  have hUne : U.Nonempty := by rw [← card_pos]; exact_mod_cast hUpos
  have hgrid : ∀ n ∈ U, ∀ y, n y < m := by
    intro n hn y
    have := hUg hn
    simp only [grid, Fintype.mem_piFinset, mem_range] at this
    exact this y
  -- pigeonhole on the coordinate sum
  obtain ⟨A, hA⟩ := pigeon U hUne (range (k * m)) (fun n => ∑ y, n y) (by
      intro n hn
      rw [mem_range]
      calc ∑ y, n y < ∑ _y : Fin k, m :=
            sum_lt_sum_of_nonempty ⟨⟨0, hk0⟩, mem_univ _⟩ (fun y _ => hgrid n hn y)
        _ = k * m := by simp)
    ((k:ℝ) * m) (by positivity) (by simp)
  set U₁ := U.filter (fun n => ∑ y, n y = A) with hU₁
  have hA1 : (U.card : ℝ) / (k * m) ≤ U₁.card := hA
  have hU₁U : U₁ ⊆ U := filter_subset _ _
  set z : (Fin k → ℕ) → Fin k → ℝ := fun n y => sv k y + g * ((n y : ℝ) - (A:ℝ) / k) with hz
  set r : (Fin k → ℕ) → ℝ := fun n => Real.sqrt ((∑ y, z n y ^ 2) / k) with hr
  have hAsum : ∀ n ∈ U₁, (A:ℝ) = ∑ y, (n y : ℝ) := by
    intro n hn
    rw [← (mem_filter.1 hn).2]; push_cast; rfl
  have hv : ∀ n ∈ U₁, ∀ y, |g * ((n y : ℝ) - (A:ℝ) / k)| ≤ 1 / 8 := by
    intro n hn y
    have hnU := hU₁U hn
    have h1 : (n y : ℝ) ≤ m := by exact_mod_cast (hgrid n hnU y).le
    have h2 : (A:ℝ) / k ≤ m := by
      rw [div_le_iff₀ hkpos, hAsum n hn]
      calc ∑ y, (n y:ℝ) ≤ ∑ _y : Fin k, (m:ℝ) :=
            sum_le_sum (fun y _ => by exact_mod_cast (hgrid n hnU y).le)
        _ = m * k := by simp; ring
    have h3 : 0 ≤ (A:ℝ) / k := by positivity
    have h4 : (0:ℝ) ≤ n y := by positivity
    rw [abs_mul, abs_of_pos hg]
    have : |(n y : ℝ) - A / k| ≤ m := by rw [abs_le]; constructor <;> linarith
    calc g * |(n y : ℝ) - A / k| ≤ g * m := mul_le_mul_of_nonneg_left this hg.le
      _ ≤ 1 / 8 := hgm
  have hzsum : ∀ n ∈ U₁, ∑ y, z n y = 0 := by
    intro n hn
    simp only [hz, sum_add_distrib, sv_sum, ← mul_sum, sum_sub_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← hAsum n hn]
    field_simp
    ring
  have hzabs : ∀ n ∈ U₁, ∀ y, |z n y| ≤ 9 / 8 := by
    intro n hn y
    simp only [hz]
    calc _ ≤ |sv k y| + |g * ((n y : ℝ) - (A:ℝ) / k)| := abs_add_le _ _
      _ ≤ 1 + 1 / 8 := add_le_add (sv_abs k y) (hv n hn y)
      _ = 9 / 8 := by norm_num
  have hzup : ∀ n ∈ U₁, ∑ y, z n y ^ 2 ≤ 81 / 64 * k := by
    intro n hn
    calc ∑ y, z n y ^ 2 ≤ ∑ _y : Fin k, (81 / 64 : ℝ) := by
          apply sum_le_sum
          intro y _
          have := hzabs n hn y
          have h0 := abs_nonneg (z n y)
          rw [← sq_abs]
          nlinarith
      _ = 81 / 64 * k := by simp; ring
  have hzlo : ∀ n ∈ U₁, 5 / 12 * (k:ℝ) ≤ ∑ y, z n y ^ 2 := by
    intro n hn
    have hpt : ∀ y, sv k y ^ 2 - 1 / 4 ≤ z n y ^ 2 := by
      intro y
      have h1 := sv_abs k y
      have h2 := hv n hn y
      simp only [hz]
      set a := sv k y
      set b := g * ((n y : ℝ) - A / k)
      have : |a * b| ≤ 1 / 8 := by
        rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]
      have := neg_abs_le (a * b)
      nlinarith [sq_nonneg b]
    have := sv_sq k
    calc 5 / 12 * (k:ℝ) ≤ ∑ y, (sv k y ^ 2 - 1 / 4) := by
          rw [sum_sub_distrib]; simp; nlinarith
      _ ≤ _ := sum_le_sum (fun y _ => hpt y)
  have hr2 : ∀ n ∈ U₁, r n ^ 2 = (∑ y, z n y ^ 2) / k := by
    intro n hn
    exact Real.sq_sqrt (div_nonneg (sum_nonneg (fun y _ => sq_nonneg _)) hkpos.le)
  have hS : ∀ n ∈ U₁, ∑ y, z n y ^ 2 = k * r n ^ 2 := by
    intro n hn; rw [hr2 n hn]; field_simp
  have hrlo : ∀ n ∈ U₁, 5 / 12 ≤ r n ^ 2 := by
    intro n hn; rw [hr2 n hn, le_div_iff₀ hkpos]; linarith [hzlo n hn]
  have hrhi : ∀ n ∈ U₁, r n ^ 2 ≤ 81 / 64 := by
    intro n hn; rw [hr2 n hn, div_le_iff₀ hkpos]; linarith [hzup n hn]
  have hr0 : ∀ n, 0 ≤ r n := fun n => Real.sqrt_nonneg _
  have hrpos : ∀ n ∈ U₁, 9 / 16 ≤ r n := by
    intro n hn; nlinarith [hrlo n hn, hr0 n]
  have hr98 : ∀ n ∈ U₁, r n ≤ 9 / 8 := by
    intro n hn; nlinarith [hrhi n hn, hr0 n]
  -- pigeonhole on the bin of `r`
  have hU₁pos : (0:ℝ) < U₁.card := lt_of_lt_of_le (by positivity) hA1
  have hU₁ne : U₁.Nonempty := by rw [← card_pos]; exact_mod_cast hU₁pos
  obtain ⟨b, hb⟩ := pigeon U₁ hU₁ne (range (⌊9 / (2 * g)⌋₊ + 1)) (fun n => ⌊4 * r n / g⌋₊)
    (by
      intro n hn
      rw [mem_range, Nat.lt_add_one_iff]
      apply Nat.floor_le_floor
      rw [div_le_div_iff₀ hg (by positivity)]
      nlinarith [hr98 n hn])
    (5 / g) (by positivity)
    (by
      simp only [card_range]
      push_cast
      have := Nat.floor_le (show (0:ℝ) ≤ 9 / (2 * g) by positivity)
      have e : 5 / g = 9 / (2 * g) + 1 / (2 * g) := by field_simp; ring
      have : 1 ≤ 1 / (2 * g) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith)
  set U₂ := U₁.filter (fun n => ⌊4 * r n / g⌋₊ = b) with hU₂
  have hb2 : (U₁.card : ℝ) / (5 / g) ≤ U₂.card := hb
  have hU₂U₁ : U₂ ⊆ U₁ := filter_subset _ _
  set x : (Fin k → ℕ) → Fin k → ℝ := fun n y => z n y / (2 * r n) with hx
  set ε := g ^ 2 / 25600 with hε
  have hεpos : 0 < ε := by positivity
  have hsepz : ∀ n ∈ U₂, ∀ n' ∈ U₂, n ≠ n' → (k:ℝ) * g ^ 2 ≤ ∑ y, (z n y - z n' y) ^ 2 := by
    intro n hn n' hn' hne
    have h1 := hUsep n (hU₁U (hU₂U₁ hn)) n' (hU₁U (hU₂U₁ hn')) hne
    have : ∀ y, (z n y - z n' y) ^ 2 = g ^ 2 * (((n y : ℝ) - n' y) ^ 2) := by
      intro y; simp only [hz]; ring
    simp only [this, ← mul_sum]
    unfold D at h1
    nlinarith [sq_nonneg g]
  have hclose : ∀ n ∈ U₂, ∀ n' ∈ U₂, (r n - r n') ^ 2 ≤ g ^ 2 / 16 := by
    intro n hn n' hn'
    have e : ⌊4 * r n / g⌋₊ = ⌊4 * r n' / g⌋₊ := by
      rw [(mem_filter.1 hn).2, (mem_filter.1 hn').2]
    have := floor_close (by have := hr0 n; positivity) (by have := hr0 n'; positivity) e
    rw [abs_lt] at this
    have h1 : 4 * r n / g - 4 * r n' / g = 4 * (r n - r n') / g := by ring
    rw [h1, lt_div_iff₀ hg, div_lt_iff₀ hg] at this
    have hp1 : 0 < g - 4 * (r n - r n') := by linarith
    have hp2 : 0 < g + 4 * (r n - r n') := by linarith
    nlinarith [mul_pos hp1 hp2]
  have hdot : ∀ n ∈ U₂, ∀ n' ∈ U₂, n ≠ n' → dot (x n) (x n') ≤ (k:ℝ) / 4 * (1 - 8000 * ε) := by
    intro n hn n' hn' hne
    have hn1 := hU₂U₁ hn
    have hn1' := hU₂U₁ hn'
    have hexp : ∑ y, (z n y - z n' y) ^ 2
        = ∑ y, z n y ^ 2 + ∑ y, z n' y ^ 2 - 2 * ∑ y, z n y * z n' y := by
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl (fun y _ => by ring)
    have hrp := hrpos n hn1
    have hrp' := hrpos n' hn1'
    have hxx : ∀ y, x n y * x n' y = z n y * z n' y / (4 * r n * r n') := by
      intro y; simp only [hx]; field_simp; ring
    simp only [dot, hxx, ← sum_div]
    rw [div_le_iff₀ (by positivity)]
    have hsep := hsepz n hn n' hn' hne
    rw [hexp, hS n hn1, hS n' hn1'] at hsep
    have hcl := hclose n hn n' hn'
    have h1 : (k:ℝ) * (r n - r n') ^ 2 ≤ k * (g ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left hcl hkpos.le
    have hrr : r n * r n' ≤ 81 / 64 := by
      have := mul_le_mul (hr98 n hn1) (hr98 n' hn1') (hr0 n') (by norm_num)
      linarith
    have h2 : (k:ℝ) * (r n * r n') * g ^ 2 ≤ k * (81 / 64) * g ^ 2 := by
      have := mul_le_mul_of_nonneg_left hrr hkpos.le
      exact mul_le_mul_of_nonneg_right this (sq_nonneg g)
    have hkg : 0 ≤ (k:ℝ) * g ^ 2 := by positivity
    rw [hε]
    linear_combination (1 / 2 : ℝ) * hsep + (1 / 2 : ℝ) * h1 + (5 / 16 : ℝ) * h2 + (75 / 1024 : ℝ) * hkg
  have hinj : Set.InjOn x U₂ := by
    intro n hn n' hn' heq
    by_contra hne
    have := hdot n hn n' hn' hne
    rw [← heq] at this
    have hsq : dot (x n) (x n) = (k:ℝ) / 4 := by
      have hn1 := hU₂U₁ hn
      have hrp := hrpos n hn1
      have : ∀ y, x n y * x n y = z n y ^ 2 / (4 * r n ^ 2) := by
        intro y; simp only [hx]; field_simp; ring
      simp only [dot, this, ← sum_div]
      rw [hS n hn1]; field_simp
    rw [hsq] at this
    have e : (k:ℝ) / 4 * (1 - 8000 * ε) = k / 4 - k / 4 * (8000 * ε) := by ring
    have : 0 < (k:ℝ) / 4 * (8000 * ε) := by positivity
    linarith
  refine ⟨U₂.image x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp y
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hp
    have hn1 := hU₂U₁ hn
    have h1 := abs_le.1 (hzabs n hn1 y)
    have h2 := hrpos n hn1
    simp only [hx]
    constructor
    · rw [le_div_iff₀ (by linarith)]; linarith
    · rw [div_le_iff₀ (by linarith)]; linarith
  · intro p hp
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hp
    simp only [hx, ← sum_div, hzsum n (hU₂U₁ hn), zero_div]
  · intro p hp
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hp
    have hn1 := hU₂U₁ hn
    have hrp := hrpos n hn1
    have : ∀ y, (z n y / (2 * r n)) ^ 2 = z n y ^ 2 / (4 * r n ^ 2) := by
      intro y; rw [div_pow]; ring
    simp only [hx, this, ← sum_div]
    rw [hS n hn1]; field_simp
  · intro p hp p' hp' hne
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hp
    obtain ⟨n', hn', rfl⟩ := mem_image.1 hp'
    exact hdot n hn n' hn' (fun h => hne (by rw [h]))
  · rw [card_image_of_injOn hinj]
    have hU : (1 / (64 * Real.exp 1 * g)) ^ k ≤ U.card := by
      have e : (1 / (64 * Real.exp 1 * g)) ^ k = (1 / (16 * g)) ^ k / (4 * Real.exp 1) ^ k := by
        rw [← div_pow]; congr 1; field_simp; ring
      rw [e, div_le_iff₀ (by positivity)]
      calc (1 / (16 * g)) ^ k ≤ (m:ℝ) ^ k := pow_le_pow_left₀ (by positivity) hm2 k
        _ ≤ _ := hUcard
    have hkm : (U.card : ℝ) * (8 * g / k) ≤ (U.card : ℝ) / (k * m) := by
      rw [div_eq_mul_one_div (U.card : ℝ)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ hkpos (by positivity)]
      nlinarith
    calc (1 / (64 * Real.exp 1 * g)) ^ k * (8 * g / k) * (g / 5)
        ≤ (U.card : ℝ) * (8 * g / k) * (g / 5) := by gcongr
      _ ≤ (U.card : ℝ) / (k * m) * (g / 5) := by gcongr
      _ ≤ (U₁.card : ℝ) * (g / 5) := by gcongr
      _ = (U₁.card : ℝ) / (5 / g) := by field_simp
      _ ≤ _ := hb2

theorem rpow_eps (q : ℝ) (hq : 0 < q) (k : ℕ) (hk : 2 ≤ k) :
    ((q ^ 2)⁻¹ : ℝ) ^ (-((k : ℝ) - 2) / 2) = q ^ (k - 2) := by
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast q 2, ← Real.rpow_mul hq.le,
    ← Real.rpow_neg hq.le, ← Real.rpow_natCast q (k - 2)]
  congr 1
  push_cast [Nat.cast_sub hk]
  ring

theorem two_rpow (k : ℕ) : (2 : ℝ) ^ (-17 * (k : ℝ)) = (((2 : ℝ) ^ 17) ^ k)⁻¹ := by
  rw [show -17 * (k:ℝ) = -((17 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
    Real.rpow_natCast, pow_mul]

end MulticlassOmni.Dev.B1

namespace MulticlassOmni.Lipschitz

open MulticlassOmni.Dev.B1 in
theorem chk_lemma_B_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ X : Finset (Fin k → ℝ),
          (2 : ℝ) ^ (-C * k) * ε ^ (-((k : ℝ) - 2) / 2) ≤ (X.card : ℝ) ∧
          IsZeroSumPacking k ε X ∧ 4 ∣ X.card ∧ M < (X.card : ℝ) := by
  refine ⟨17, by norm_num, fun M => ?_⟩
  set Q := (2 : ℝ) ^ 51 * (|M| + 3) with hQ
  have hQpos : 0 < Q := by positivity
  refine ⟨(Q ^ 2)⁻¹, by positivity, ?_⟩
  intro k hk ε hε hεle
  set q := 1 / Real.sqrt ε with hqdef
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hq : 0 < q := by positivity
  have hεq : ε = (q ^ 2)⁻¹ := by
    rw [hqdef, div_pow, Real.sq_sqrt hε.le]; simp
  clear_value q
  have hqQ : Q ≤ q := by
    by_contra h
    push Not at h
    have h1 : q ^ 2 < Q ^ 2 := by nlinarith
    have h2 : (Q ^ 2)⁻¹ < (q ^ 2)⁻¹ := (inv_lt_inv₀ (by positivity) (by positivity)).2 h1
    rw [← hεq] at h2
    linarith
  have hQbig : (2 : ℝ) ^ 51 * 3 ≤ Q := by
    rw [hQ]; have := abs_nonneg M; nlinarith
  set g := 160 / q with hgdef
  have hg : 0 < g := by positivity
  have hg16 : g ≤ 1 / 16 := by
    rw [hgdef, div_le_div_iff₀ hq (by norm_num)]; norm_num at hQbig; linarith
  have hεg : ε = g ^ 2 / 25600 := by
    rw [hεq, hgdef]; field_simp; ring
  clear_value g
  obtain ⟨X₀, hpack, hcard⟩ := core k hk g hg hg16
  rw [← hεg] at hpack
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hL : (1 / (64 * Real.exp 1 * g)) ^ k * (8 * g / k) * (g / 5)
      = q ^ (k - 2) * (40960 / (k * (10240 * Real.exp 1) ^ k)) := by
    have hqk : q ^ k = q ^ (k - 2) * q ^ 2 := by rw [← pow_add]; congr 1; omega
    have e1 : 1 / (64 * Real.exp 1 * g) = q / (10240 * Real.exp 1) := by
      rw [hgdef]; field_simp; ring
    rw [e1, div_pow, hqk, hgdef]
    field_simp
    ring
  have hbig : 2 * (k:ℝ) * (10240 * Real.exp 1) ^ k ≤ 40960 * ((2 : ℝ) ^ 17) ^ k := by
    have h1 : (k:ℝ) ≤ 2 ^ k := by exact_mod_cast le_two_pow k
    have h2 : (10240 * Real.exp 1) ^ k ≤ ((2 : ℝ) ^ 16) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      have := Real.exp_one_lt_d9
      norm_num
      linarith
    calc 2 * (k:ℝ) * (10240 * Real.exp 1) ^ k ≤ 2 * 2 ^ k * ((2 : ℝ) ^ 16) ^ k := by gcongr
      _ = 2 * ((2 : ℝ) ^ 17) ^ k := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ 40960 * ((2 : ℝ) ^ 17) ^ k := by
          have : (0:ℝ) ≤ ((2 : ℝ) ^ 17) ^ k := by positivity
          linarith
  set T := q ^ (k - 2) / ((2 : ℝ) ^ 17) ^ k with hT
  have hX0 : 2 * T ≤ X₀.card := by
    calc 2 * T = q ^ (k - 2) * (2 / ((2 : ℝ) ^ 17) ^ k) := by rw [hT]; ring
      _ ≤ q ^ (k - 2) * (40960 / (k * (10240 * Real.exp 1) ^ k)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
      _ = _ := hL.symm
      _ ≤ _ := hcard
  have hTM : |M| + 3 ≤ T := by
    have e1 : ((2 : ℝ) ^ 17) ^ k = ((2 : ℝ) ^ 17) ^ (k - 3) * 2 ^ 51 := by
      rw [show (2 : ℝ) ^ 51 = ((2 : ℝ) ^ 17) ^ 3 by norm_num, ← pow_add]; congr 1; omega
    have e2 : q ^ (k - 2) = q ^ (k - 3) * q := by rw [← pow_succ]; congr 1; omega
    have e3 : T = (q / 2 ^ 17) ^ (k - 3) * (q / 2 ^ 51) := by
      rw [hT, e1, e2, div_pow, mul_div_mul_comm]
    have h1 : 1 ≤ q / 2 ^ 17 := by
      rw [le_div_iff₀ (by positivity)]; norm_num at hQbig; linarith
    have h2 : |M| + 3 ≤ q / 2 ^ 51 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    rw [e3]
    have h3 : 1 ≤ (q / 2 ^ 17) ^ (k - 3) := one_le_pow₀ h1
    nlinarith
  obtain ⟨X, hXsub, hXcard⟩ := Finset.exists_subset_card_eq (show 4 * (X₀.card / 4) ≤ X₀.card by omega)
  have hXlow : (X₀.card : ℝ) ≤ X.card + 3 := by
    rw [hXcard]
    have : X₀.card ≤ 4 * (X₀.card / 4) + 3 := by omega
    exact_mod_cast this
  have hTX : T ≤ X.card := by
    have := abs_nonneg M
    linarith
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hpack
  refine ⟨X, ?_, ⟨fun x hx => hb1 x (hXsub hx), fun x hx => hb2 x (hXsub hx),
    fun x hx => hb3 x (hXsub hx), fun x hx x' hx' => hb4 x (hXsub hx) x' (hXsub hx')⟩, ?_, ?_⟩
  · rw [hεq, rpow_eps q hq k (by omega), two_rpow, hT, div_eq_inv_mul] at *
    exact hTX
  · rw [hXcard]; exact Nat.dvd_mul_right 4 _
  · have := le_abs_self M
    linarith

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_lemma_B_1 := @MulticlassOmni.Lipschitz.chk_lemma_B_1
