-- Prove2me | solution 1 for MasulloRH.finite_prime_support_probability_escape
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:20:54.185769+00:00
-- url     : https://prove2.me/submissions/c6fb0022-47b4-4a2f-b547-e3a1dbb00c7c

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
section

open Filter Finset
open scoped Topology

/-- Omitting finitely many primes does not prevent the partial Euler product from
vanishing in the strip with real exponent between zero and one, including one. -/
private theorem prime_void_bound (S : Finset ℕ) {a : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) :
    Tendsto (fun B : ℕ ↦ ∏ l ∈ (range (B+1)).filter (fun l ↦ l.Prime ∧ l ∉ S),
      (1 - (l : ℝ)^(-a))) atTop (𝓝 0) := by
  let f (n : ℕ) : ℝ := if n.Prime ∧ n ∉ S then (n : ℝ)^(-a) else 0
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hf₁ (n : ℕ) : f n ≤ 1 := by
    dsimp [f]
    split_ifs with h
    · exact (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h.1.one_lt) (neg_neg_of_pos ha)).le
    · norm_num
  have hns : ¬ Summable f := by
    intro h
    have hsum : Summable (fun n : ℕ ↦ if n.Prime then (n : ℝ)^(-a) else 0) :=
      h.congr_cofinite (by
        filter_upwards [S.finite_toSet.compl_mem_cofinite] with n hn
        have hn' : n ∉ S := hn
        simp only [f, hn', not_false_eq_true, and_true])
    have hbad := Nat.Primes.summable_rpow.mp <|
      (Nat.Primes.summable_iff_summable_ite (fun n : ℕ ↦ (n : ℝ)^(-a))).mpr hsum
    linarith
  have htop := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp hns
  have htop' : Tendsto (fun B : ℕ ↦ ∑ i ∈ range (B+1), f i) atTop atTop :=
    htop.comp (tendsto_add_atTop_nat 1)
  have hzero := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htop')
  have hprod (B : ℕ) : (∏ l ∈ (range (B+1)).filter (fun l ↦ l.Prime ∧ l ∉ S),
        (1 - (l : ℝ)^(-a))) = ∏ l ∈ range (B+1), (1-f l) := by
    rw [prod_filter]
    apply prod_congr rfl
    intro l hl
    by_cases h : l.Prime ∧ l ∉ S <;> simp [f, h]
  simp_rw [hprod]
  apply squeeze_zero (fun _ ↦ prod_nonneg (fun n _ ↦ sub_nonneg.mpr (hf₁ n))) _
    (show Tendsto (fun B : ℕ ↦ Real.exp (-(∑ i ∈ range (B+1), f i))) atTop (𝓝 0) from hzero)
  intro B
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod (fun n _ ↦ sub_nonneg.mpr (hf₁ n))
  intro n hn
  linarith [Real.add_one_le_exp (-f n)]

end

open Filter Finset
open scoped Topology

theorem solution {X : Type*} (supp : X → Finset ℕ) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : Summable w) (hm : ∑' x, w x = 1)
    (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ S : Finset ℕ, ∀ᶠ B : ℕ in atTop,
      let Q := (range (B+1)).filter (fun p => p.Prime ∧ p ∉ S)
      (∏ p ∈ Q, (1 - (p:ℝ)^(-a))) <
        ∑' x, (if Disjoint (supp x) Q then w x else 0) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, 0 < w x := by
    by_contra! h
    have hz : w = 0 := funext fun x => le_antisymm (h x) (hw x)
    simp [hz] at hm
  refine ⟨supp x, ?_⟩
  filter_upwards [(prime_void_bound (supp x) ha ha₁).eventually_lt_const hx] with B hB
  let Q := (range (B+1)).filter (fun p => p.Prime ∧ p ∉ supp x)
  let v (y : X) := if Disjoint (supp y) Q then w y else 0
  have hd : Disjoint (supp x) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_filter.mp hq).2.2 hp
  have hn (y : X) : 0 ≤ v y := by simp only [v]; split_ifs <;> simp [hw]
  have hv : Summable v := hs.of_nonneg_of_le hn (fun y => by simp only [v]; split_ifs <;> simp [hw])
  have hle := hv.le_tsum x (fun y _ => hn y)
  change _ < ∑' y, v y
  have hfinal : w x ≤ ∑' y, v y := by simpa only [show v x = w x by simp [v, hd]] using hle
  exact hB.trans_le hfinal
