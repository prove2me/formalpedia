-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.Supplement.limiting_weights
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:45:48.637447+00:00
-- url     : https://prove2.me/submissions/052a4022-4919-4c48-9cdb-8e20ab289e70

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace LWAux

open MomentAmbiguitySecretary.Secretary.Supplement

def N (n B i : ℕ) : ℕ := if i = 0 then 1 else if i = 1 then B else (n * B) ^ (B ^ (i - 2))

lemma node_eq (n B i : ℕ) : (binaryNode n B i : ℝ) = (N n B i : ℝ) := by
  unfold binaryNode N
  split_ifs <;> simp

lemma N_strictMono (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) : StrictMono (N n B) := by
  have hnB : 1 < n * B := by nlinarith
  apply strictMono_nat_of_lt_succ
  intro i
  rcases i with _ | _ | i
  · simp [N]; omega
  · simp [N]; nlinarith
  · simp only [N, show i + 2 ≠ 0 by omega, show i + 2 ≠ 1 by omega,
      show i + 1 + 2 ≠ 0 by omega, show i + 1 + 2 ≠ 1 by omega, if_false]
    apply Nat.pow_lt_pow_right hnB
    apply Nat.pow_lt_pow_right (by omega)
    omega

lemma N_ge (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) (i : ℕ) : 2 ^ i ≤ N n B i := by
  rcases i with _ | _ | i
  · simp [N]
  · simp [N]; omega
  · simp only [N, show i + 2 ≠ 0 by omega, show i + 2 ≠ 1 by omega, if_false]
    have h1 : i + 1 ≤ B ^ i := by
      have := Nat.lt_pow_self (show 1 < B by omega) (n := i)
      omega
    have h4 : 4 ≤ n * B := by nlinarith
    calc 2 ^ (i + 2) ≤ 4 ^ (i + 1) := by
          rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          apply Nat.pow_le_pow_right (by norm_num); omega
      _ ≤ (n * B) ^ (i + 1) := Nat.pow_le_pow_left h4 _
      _ ≤ (n * B) ^ (B ^ (i + 2 - 2)) := by
          apply Nat.pow_le_pow_right (by omega); simpa using h1

end LWAux

open MomentAmbiguitySecretary.Secretary.Supplement LWAux

theorem solution (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) (j : ℕ) :
    Tendsto (fun K : ℕ => finiteWeight n B K j) atTop (𝓝 (binaryWeight n B j)) := by
  classical
  unfold binaryWeight
  apply tendsto_nhds_limUnder
  set x : ℕ → ℝ := fun i => (N n B i : ℝ) with hx
  have hmono : StrictMono x := by
    intro a b hab
    simp only [hx]
    exact_mod_cast N_strictMono n B hn hB hab
  have hinj : Function.Injective x := hmono.injective
  have hge : ∀ i, (2:ℝ) ^ i ≤ x i := fun i => by
    simp only [hx]; exact_mod_cast N_ge n B hn hB i
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le (by positivity) (hge i)
  -- rewrite finiteWeight in terms of x
  have hfw : ∀ K, finiteWeight n B K j =
      (∏ i ∈ (Finset.range (K + 3)).erase 2, (x 2 - x i)) /
        ∏ i ∈ (Finset.range (K + 3)).erase j, (x j - x i) := by
    intro K
    unfold finiteWeight barycentric
    simp only [node_eq, hx]
    rw [inv_div_inv]
  by_cases hj2 : j = 2
  · subst hj2
    refine ⟨1, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards with K
    rw [hfw, div_self]
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hi) (hinj h).symm)
  -- general case
  set f : ℕ → ℝ := fun i => if i = 2 ∨ i = j then 0 else (x 2 - x j) / (x j - x i) with hf
  have hsum : Summable f := by
    have hg : Summable (fun i : ℕ => (|x 2 - x j| * 2) * (1 / 2 : ℝ) ^ i) :=
      summable_geometric_two.mul_left _
    apply hg.of_norm_bounded_eventually_nat
    have ht : Tendsto (fun i : ℕ => (2:ℝ) ^ i) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    filter_upwards [ht.eventually_ge_atTop (2 * x j)] with i hi
    simp only [hf]
    split_ifs
    · simp
    · rw [Real.norm_eq_abs, abs_div]
      have hxi : 2 * x j ≤ x i := le_trans hi (hge i)
      have hd : |x j - x i| = x i - x j := by
        rw [abs_sub_comm, abs_of_pos]; linarith [hxpos j]
      rw [hd, div_le_iff₀ (by linarith [hxpos j])]
      have h2i : (0:ℝ) < 2 ^ i := by positivity
      have : (1 / 2 : ℝ) ^ i * 2 ^ i = 1 := by
        rw [← mul_pow]; norm_num
      have habs := abs_nonneg (x 2 - x j)
      have key : (1 / 2 : ℝ) ^ i * (x i - x j) ≥ 1 / 2 := by
        have : (1/2:ℝ) ^ i * x i ≥ 1 := by
          calc (1/2:ℝ)^i * x i ≥ (1/2:ℝ)^i * 2^i := by gcongr; exact hge i
            _ = 1 := this
        have h3 : (1/2:ℝ) ^ i * x j ≤ (1/2:ℝ) ^ i * x i / 2 := by
          have : (0:ℝ) ≤ (1/2) ^ i := by positivity
          nlinarith
        nlinarith
      nlinarith
  have hmul : Multipliable (fun i => 1 + f i) := Real.multipliable_one_add_of_summable hsum
  have ht := hmul.hasProd.tendsto_prod_nat
  refine ⟨-(∏' i, (1 + f i)), ?_⟩
  have ht2 := (ht.comp (tendsto_add_atTop_nat 3)).neg
  apply ht2.congr'
  filter_upwards [eventually_ge_atTop j] with K hK
  simp only [Function.comp]
  rw [hfw]
  have hjR : j ∈ Finset.range (K + 3) := Finset.mem_range.mpr (by omega)
  have h2R : 2 ∈ Finset.range (K + 3) := Finset.mem_range.mpr (by omega)
  set R := Finset.range (K + 3)
  have hj2' : j ∈ R.erase 2 := Finset.mem_erase.mpr ⟨hj2, hjR⟩
  have h2j' : 2 ∈ R.erase j := Finset.mem_erase.mpr ⟨Ne.symm hj2, h2R⟩
  rw [← Finset.mul_prod_erase _ _ hj2', ← Finset.mul_prod_erase _ _ h2j']
  have hcomm : (R.erase j).erase 2 = (R.erase 2).erase j := Finset.erase_right_comm
  rw [hcomm]
  set S := (R.erase 2).erase j
  rw [← Finset.mul_prod_erase _ _ h2R, ← Finset.mul_prod_erase _ _ hj2']
  have hf2 : f 2 = 0 := by simp [hf]
  have hfj : f j = 0 := by simp [hf]
  rw [hf2, hfj]
  have hne : x 2 - x j ≠ 0 := sub_ne_zero.mpr (fun h => hj2 (hinj h).symm)
  have hS : ∏ i ∈ S, (1 + f i) = (∏ i ∈ S, (x 2 - x i)) / ∏ i ∈ S, (x j - x i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hi2 : i ≠ 2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hd : x j - x i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h).symm)
    simp only [hf, hi2, hij, or_self, if_false]
    field_simp
    ring
  rw [hS, show x j - x 2 = -(x 2 - x j) by ring]
  have hC : ∏ i ∈ S, (x j - x i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hi) (hinj h).symm)
  field_simp
  ring
