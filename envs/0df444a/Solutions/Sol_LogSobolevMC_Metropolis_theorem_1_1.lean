-- Prove2me | solution 1 for LogSobolevMC.Metropolis.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T02:46:34.901565+00:00
-- url     : https://prove2.me/submissions/4db849a1-4da7-47db-82d2-c0d4f41cb8d3

-- Complete checked reconstruction of the native binomial Metropolis mixing theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains
import Definitions.Def_mm_mixing
import Mathlib


-- Begin Canonical
section ModuleScope_Canonical

end ModuleScope_Canonical
-- End Canonical

-- Begin BinomialBasic
section ModuleScope_BinomialBasic

open scoped BigOperators
open Finset

namespace LogSobolevMC.Metropolis.Proof

noncomputable section

def bWeight (n k : ℕ) : ℝ := (n.choose k : ℝ) / 2 ^ n

def bAvg (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), bWeight n k * f k

lemma bWeight_nonneg (n k : ℕ) : 0 ≤ bWeight n k := by
  unfold bWeight
  positivity

lemma bWeight_pos {n k : ℕ} (h : k ≤ n) : 0 < bWeight n k := by
  exact div_pos (by exact_mod_cast Nat.choose_pos h) (by positivity)

lemma bWeight_zero (n : ℕ) : bWeight n 0 = (2 ^ n : ℝ)⁻¹ := by
  simp [bWeight, one_div]

lemma bWeight_above {n k : ℕ} (h : n < k) : bWeight n k = 0 := by
  simp [bWeight, Nat.choose_eq_zero_of_lt h]

lemma bWeight_pascal (n k : ℕ) :
    bWeight (n + 1) (k + 1) = (bWeight n k + bWeight n (k + 1)) / 2 := by
  simp only [bWeight, Nat.choose_succ_succ', Nat.cast_add, pow_succ]
  field_simp

lemma bAvg_zero (f : ℕ → ℝ) : bAvg 0 f = f 0 := by
  simp [bAvg, bWeight]

lemma bAvg_add (n : ℕ) (f g : ℕ → ℝ) :
    bAvg n (fun k => f k + g k) = bAvg n f + bAvg n g := by
  simp [bAvg, mul_add, sum_add_distrib]

lemma bAvg_sub (n : ℕ) (f g : ℕ → ℝ) :
    bAvg n (fun k => f k - g k) = bAvg n f - bAvg n g := by
  simp [bAvg, mul_sub, sum_sub_distrib]

lemma bAvg_smul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    bAvg n (fun k => c * f k) = c * bAvg n f := by
  simp only [bAvg, mul_sum]
  apply sum_congr rfl
  intro k _
  ring

lemma bAvg_nonneg (n : ℕ) {f : ℕ → ℝ} (h : ∀ k ≤ n, 0 ≤ f k) :
    0 ≤ bAvg n f := by
  apply sum_nonneg
  intro k hk
  exact mul_nonneg (bWeight_nonneg n k) (h k (Nat.le_of_lt_succ (mem_range.mp hk)))

lemma bAvg_mono (n : ℕ) {f g : ℕ → ℝ} (h : ∀ k ≤ n, f k ≤ g k) :
    bAvg n f ≤ bAvg n g := by
  apply sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (h k (Nat.le_of_lt_succ (mem_range.mp hk)))
    (bWeight_nonneg n k)

lemma bAvg_congr (n : ℕ) {f g : ℕ → ℝ} (h : ∀ k ≤ n, f k = g k) :
    bAvg n f = bAvg n g := by
  apply sum_congr rfl
  intro k hk
  rw [h k (Nat.le_of_lt_succ (mem_range.mp hk))]

lemma bAvg_succ (n : ℕ) (f : ℕ → ℝ) :
    bAvg (n + 1) f = (bAvg n f + bAvg n (fun k => f (k + 1))) / 2 := by
  have hs : (∑ k ∈ range (n + 1), bWeight n (k + 1) * f (k + 1)) +
      bWeight n 0 * f 0 = bAvg n f := by
    have hh := sum_range_succ' (fun k => bWeight n k * f k) (n + 1)
    rw [sum_range_succ] at hh
    simpa [bWeight_above (Nat.lt_succ_self n), bAvg] using hh.symm
  unfold bAvg at *
  rw [sum_range_succ']
  simp_rw [bWeight_pascal]
  have h0 : bWeight (n + 1) 0 = bWeight n 0 / 2 := by
    simp [bWeight, pow_succ]
    ring
  rw [h0]
  simp_rw [add_div, add_mul, div_mul_eq_mul_div]
  rw [sum_add_distrib]
  simp_rw [← sum_div]
  linarith

lemma bAvg_const (n : ℕ) (c : ℝ) : bAvg n (fun _ => c) = c := by
  induction n with
  | zero => exact bAvg_zero _
  | succ n ih => rw [bAvg_succ, ih]; linarith

lemma bAvg_sq_nonneg (n : ℕ) (f : ℕ → ℝ) : 0 ≤ bAvg n (fun k => (f k)^2) :=
  bAvg_nonneg n (fun k _ => sq_nonneg (f k))

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_BinomialBasic
-- End BinomialBasic

-- Begin NativeBinomial
section ModuleScope_NativeBinomial

open scoped BigOperators
open Finset

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

lemma bAvg_eq_fin (n : ℕ) (f : ℕ → ℝ) :
    bAvg n f = ∑ k : Fin (n+1), binomPi n k * f k := by
  unfold bAvg
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

lemma binomPi_pos (n : ℕ) (k : Fin (n+1)) : 0 < binomPi n k := by
  exact bWeight_pos (Nat.le_of_lt_succ k.isLt)

lemma binomPi_dist (n : ℕ) : MarkovMixing.IsDist (binomPi n) := by
  refine ⟨fun k => (binomPi_pos n k).le, ?_⟩
  have h := bAvg_const n 1
  rw [bAvg_eq_fin] at h
  simpa using h

lemma binomPi_lower (n : ℕ) (k : Fin (n+1)) : (2^n:ℝ)⁻¹ ≤ binomPi n k := by
  have h : (1:ℝ) ≤ n.choose (k:ℕ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ k.isLt)
  exact (by simpa [binomPi, one_div] using
    div_le_div_of_nonneg_right h (by positivity : (0:ℝ) ≤ 2^n))

lemma binomPi_zero (n : ℕ) : binomPi n (0 : Fin (n+1)) = (2^n:ℝ)⁻¹ := by
  simp [binomPi, one_div]

lemma binomPi_zero_lt_one {n : ℕ} (hn : 1 ≤ n) :
    binomPi n (0 : Fin (n+1)) < 1 := by
  rw [binomPi_zero]
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by omega))

lemma bWeight_succ_balance (n k : ℕ) :
    bWeight n k * ((n:ℝ)-k) = bWeight n (k+1) * (k+1) := by
  by_cases hk : k < n
  · have h := Nat.choose_succ_right_eq n k
    have hh : (n.choose k:ℝ)*((n:ℝ)-k) = (n.choose (k+1):ℝ)*(k+1) := by
      have hh : (n.choose k:ℝ)*((n-k:ℕ):ℝ) = (n.choose (k+1):ℝ)*((k+1:ℕ):ℝ) := by
        exact_mod_cast h.symm
      simpa [Nat.cast_sub hk.le] using hh
    unfold bWeight
    calc
      _ = ((n.choose k:ℝ)*((n:ℝ)-k))/2^n := by ring
      _ = _ := by rw [hh]; ring
  · have hk' : n ≤ k := by omega
    rcases eq_or_lt_of_le hk' with h | h
    · subst k
      simp [bWeight_above (Nat.lt_succ_self n)]
    · simp [bWeight_above h, bWeight_above (by omega : n < k+1)]

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_NativeBinomial
-- End NativeBinomial

-- Begin MetropolisBasic
section ModuleScope_MetropolisBasic

open scoped BigOperators
open Finset

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma metropolis_nonneg {Q : Matrix V V ℝ} {π : V → ℝ}
    (hQ : ∀ x y, 0 ≤ Q x y) (hrow : ∀ x, ∑ y ∈ ({x}ᶜ : Finset V), Q x y ≤ 1)
    (hπ : ∀ x, 0 < π x) : ∀ x y, 0 ≤ MarkovMixing.metropolis Q π x y := by
  intro x y
  unfold MarkovMixing.metropolis
  split_ifs with h
  · have hh : (∑ z ∈ ({x}ᶜ : Finset V), Q x z*min 1 (π z/π x)) ≤
        ∑ z ∈ ({x}ᶜ : Finset V), Q x z := by
      apply sum_le_sum
      intro z _
      exact mul_le_of_le_one_right (hQ x z) (min_le_left _ _)
    linarith [hrow x]
  · exact mul_nonneg (hQ x y) (le_min (by norm_num) (div_nonneg (hπ y).le (hπ x).le))

lemma metropolis_row (Q : Matrix V V ℝ) (π : V → ℝ) (x : V) :
    ∑ y, MarkovMixing.metropolis Q π x y = 1 := by
  have h := sum_erase_add (s := (univ : Finset V))
    (f := fun y => MarkovMixing.metropolis Q π x y) (mem_univ x)
  have he : (∑ y ∈ univ.erase x, MarkovMixing.metropolis Q π x y) =
      ∑ y ∈ ({x}ᶜ : Finset V), Q x y*min 1 (π y/π x) := by
    have hs : (univ.erase x : Finset V) = {x}ᶜ := by ext y; simp
    rw [hs]
    apply sum_congr rfl
    intro y hy
    simp only [mem_compl, mem_singleton] at hy
    simp [MarkovMixing.metropolis, hy]
  rw [he] at h
  have hd : MarkovMixing.metropolis Q π x x = 1 -
      ∑ y ∈ ({x}ᶜ : Finset V), Q x y*min 1 (π y/π x) := by
    simp [MarkovMixing.metropolis]
  rw [hd] at h
  linarith

lemma metropolis_balance {Q : Matrix V V ℝ} {π : V → ℝ}
    (hQ : ∀ x y, Q x y = Q y x) (hπ : ∀ x, 0 < π x) :
    MarkovMixing.DetailedBalance (MarkovMixing.metropolis Q π) π := by
  intro x y
  by_cases h : y=x
  · subst y
    rfl
  have hx : π x ≠ 0 := ne_of_gt (hπ x)
  have hy : π y ≠ 0 := ne_of_gt (hπ y)
  have h1 : π x*min 1 (π y/π x)=min (π x) (π y) := by
    rw [mul_min_of_nonneg _ _ (hπ x).le]
    simp only [mul_one]
    congr 1
    field_simp
  have h2 : π y*min 1 (π x/π y)=min (π y) (π x) := by
    rw [mul_min_of_nonneg _ _ (hπ y).le]
    simp only [mul_one]
    congr 1
    field_simp
  simp only [MarkovMixing.metropolis, if_neg h, if_neg (Ne.symm h)]
  calc
    _ = Q x y * (π x*min 1 (π y/π x)) := by ring
    _ = Q y x * (π y*min 1 (π x/π y)) := by rw [h1,h2,hQ,min_comm]
    _ = _ := by ring

omit [DecidableEq V] in
lemma stationary_of_stochastic_balance {Q : Matrix V V ℝ} {π : V → ℝ}
    (hQ : MarkovMixing.IsStochastic Q) (hπ : MarkovMixing.IsDist π)
    (hbal : MarkovMixing.DetailedBalance Q π) : MarkovMixing.IsStationary Q π := by
  refine ⟨hπ, ?_⟩
  ext y
  change (∑ x, π x*Q x y)=π y
  calc
    _ = ∑ x, π y*Q y x := sum_congr rfl (fun x _ => hbal x y)
    _ = _ := by rw [← mul_sum, hQ.2 y, mul_one]

lemma fin_val_indicator_sum_le (N k : ℕ) :
    (∑ y : Fin N, if (y:ℕ)=k then (1:ℝ) else 0) ≤ 1 := by
  by_cases hk : k<N
  · have he : ∀ y : Fin N, (y:ℕ)=k ↔ y=⟨k,hk⟩ := by
      intro y
      constructor
      · intro h
        exact Fin.ext h
      · intro h
        exact congrArg Fin.val h
    simp_rw [he]
    simp
  · have he : ∀ y : Fin N, (y:ℕ)≠k := by
      intro y h
      have := y.isLt
      omega
    simp [he]

lemma baseWalk_nonneg (n : ℕ) (x y : Fin (n+1)) : 0 ≤ baseWalk n x y := by
  unfold baseWalk
  split_ifs <;> norm_num

lemma baseWalk_symmetric (n : ℕ) (x y : Fin (n+1)) :
    baseWalk n x y = baseWalk n y x := by
  unfold baseWalk
  by_cases h : x=y
  · subst y
    rfl
  have he : ((y:ℕ)=(x:ℕ)+1 ∨ (y:ℕ)+1=(x:ℕ)) ↔
      ((x:ℕ)=(y:ℕ)+1 ∨ (x:ℕ)+1=(y:ℕ)) := by omega
  simp [he, h, Ne.symm h]

lemma baseWalk_off_sum_le (n : ℕ) (x : Fin (n+1)) :
    (∑ y ∈ ({x}ᶜ : Finset (Fin (n+1))), baseWalk n x y) ≤ 1 := by
  let R : Fin (n+1) → ℝ := fun y =>
    (if (y:ℕ)=(x:ℕ)+1 then 1/2 else 0) +
    (if (y:ℕ)+1=(x:ℕ) then 1/2 else 0)
  have hR : ∀ y, 0 ≤ R y := by intro y; dsimp [R]; split_ifs <;> norm_num
  have he : ∀ y ∈ ({x}ᶜ : Finset (Fin (n+1))), baseWalk n x y = R y := by
    intro y hy
    have hyx : y≠x := by simpa using hy
    unfold baseWalk R
    split_ifs <;> simp_all
    omega
  have hu : (∑ y : Fin (n+1), if (y:ℕ)=(x:ℕ)+1 then (1/2:ℝ) else 0) ≤ 1/2 := by
    have h := fin_val_indicator_sum_le (n+1) ((x:ℕ)+1)
    have he : (∑ y : Fin (n+1), if (y:ℕ)=(x:ℕ)+1 then (1/2:ℝ) else 0) =
        (∑ y : Fin (n+1), if (y:ℕ)=(x:ℕ)+1 then (1:ℝ) else 0)/2 := by
      rw [sum_div]
      apply sum_congr rfl
      intro y _
      split_ifs <;> norm_num
    rw [he]
    linarith
  have hd : (∑ y : Fin (n+1), if (y:ℕ)+1=(x:ℕ) then (1/2:ℝ) else 0) ≤ 1/2 := by
    by_cases hx : (x:ℕ)=0
    · simp [hx]
    · have he : ∀ y : Fin (n+1), (y:ℕ)+1=(x:ℕ) ↔ (y:ℕ)=(x:ℕ)-1 := by
        intro y
        omega
      simp_rw [he]
      have h := fin_val_indicator_sum_le (n+1) ((x:ℕ)-1)
      have he' : (∑ y : Fin (n+1), if (y:ℕ)=(x:ℕ)-1 then (1/2:ℝ) else 0) =
          (∑ y : Fin (n+1), if (y:ℕ)=(x:ℕ)-1 then (1:ℝ) else 0)/2 := by
        rw [sum_div]
        apply sum_congr rfl
        intro y _
        split_ifs <;> norm_num
      rw [he']
      linarith
  calc
    _ = ∑ y ∈ ({x}ᶜ : Finset (Fin (n+1))), R y := sum_congr rfl he
    _ ≤ ∑ y, R y := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => hR y)
    _ ≤ 1 := by dsimp [R]; rw [sum_add_distrib]; linarith

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_MetropolisBasic
-- End MetropolisBasic

-- Begin NativeChain
section ModuleScope_NativeChain

open scoped BigOperators
open Finset

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

def birth (n k : ℕ) : ℝ := min 1 (((n:ℝ)-k)/(k+1))/2

def death (n k : ℕ) : ℝ := min 1 ((k:ℝ)/((n:ℝ)-k+1))/2

lemma binom_stochastic (n : ℕ) : MarkovMixing.IsStochastic (binomMetropolis n) := by
  exact ⟨metropolis_nonneg (baseWalk_nonneg n) (baseWalk_off_sum_le n)
    (binomPi_pos n), metropolis_row _ _⟩

lemma binom_balance (n : ℕ) :
    MarkovMixing.DetailedBalance (binomMetropolis n) (binomPi n) :=
  metropolis_balance (baseWalk_symmetric n) (binomPi_pos n)

lemma binom_stationary (n : ℕ) :
    MarkovMixing.IsStationary (binomMetropolis n) (binomPi n) :=
  stationary_of_stochastic_balance (binom_stochastic n) (binomPi_dist n) (binom_balance n)

lemma binom_ratio_up {n : ℕ} (x y : Fin (n+1)) (h : (y:ℕ)=(x:ℕ)+1) :
    binomPi n y / binomPi n x = ((n:ℝ)-(x:ℕ))/((x:ℕ)+1) := by
  have hb := bWeight_succ_balance n (x:ℕ)
  have hx : binomPi n x ≠ 0 := ne_of_gt (binomPi_pos n x)
  have hd : ((x:ℕ):ℝ)+1 ≠ 0 := by positivity
  change bWeight n (y:ℕ)/bWeight n (x:ℕ) = _
  rw [h]
  change bWeight n (x:ℕ) ≠ 0 at hx
  apply (div_eq_div_iff hx hd).2
  nlinarith

lemma binom_ratio_down {n : ℕ} (x y : Fin (n+1)) (h : (y:ℕ)+1=(x:ℕ)) :
    binomPi n y / binomPi n x = ((x:ℕ):ℝ)/((n:ℝ)-(x:ℕ)+1) := by
  have hb := bWeight_succ_balance n (y:ℕ)
  have hx : binomPi n x ≠ 0 := ne_of_gt (binomPi_pos n x)
  have hxn : ((x:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ x.isLt
  have hd : (n:ℝ)-(x:ℕ)+1 ≠ 0 := by linarith
  have hr : ((y:ℕ):ℝ)+1=(x:ℕ) := by exact_mod_cast h
  apply (div_eq_div_iff hx hd).2
  change bWeight n (y:ℕ)*((n:ℝ)-(x:ℕ)+1) = (x:ℕ)*bWeight n (x:ℕ)
  rw [h] at hb
  rw [← hr]
  nlinarith only [hb]

lemma binom_off {n : ℕ} (x y : Fin (n+1)) (h : y≠x) :
    binomMetropolis n x y =
      (if (y:ℕ)=(x:ℕ)+1 then birth n x else 0) +
      (if (y:ℕ)+1=(x:ℕ) then death n x else 0) := by
  unfold binomMetropolis MarkovMixing.metropolis
  rw [if_neg h]
  by_cases hu : (y:ℕ)=(x:ℕ)+1
  · have hd : ¬ (y:ℕ)+1=(x:ℕ) := by omega
    rw [binom_ratio_up x y hu]
    have hb : baseWalk n x y=1/2 := by simp [baseWalk, hu]
    rw [hb, if_pos hu, if_neg hd]
    unfold birth
    ring
  · by_cases hd : (y:ℕ)+1=(x:ℕ)
    · rw [binom_ratio_down x y hd]
      have hb : baseWalk n x y=1/2 := by simp [baseWalk, hd]
      rw [hb, if_neg hu, if_pos hd]
      unfold death
      ring
    · simp [baseWalk, hu, hd, Ne.symm h]

lemma fin_sum_at_val (N k : ℕ) (c : ℝ) :
    (∑ y : Fin N, if (y:ℕ)=k then c else 0) = if k<N then c else 0 := by
  by_cases hk : k<N
  · have he : ∀ y : Fin N, (y:ℕ)=k ↔ y=⟨k,hk⟩ := by
      intro y
      constructor
      · exact fun h => Fin.ext h
      · exact fun h => congrArg Fin.val h
    simp [he, hk]
  · have he : ∀ y : Fin N, (y:ℕ)≠k := by intro y h; have := y.isLt; omega
    simp [he, hk]

lemma birth_boundary (n : ℕ) : birth n n = 0 := by simp [birth]
lemma death_boundary (n : ℕ) : death n 0 = 0 := by simp [death]

lemma neighbor_sum (n : ℕ) (x : Fin (n+1)) :
    (∑ y : Fin (n+1),
      ((if (y:ℕ)=(x:ℕ)+1 then birth n x else 0) +
       (if (y:ℕ)+1=(x:ℕ) then death n x else 0))) = birth n x + death n x := by
  rw [sum_add_distrib, fin_sum_at_val]
  have hu : (if (x:ℕ)+1<n+1 then birth n x else 0) = birth n x := by
    split_ifs with h
    · rfl
    · have he : (x:ℕ)=n := by omega
      simp [he, birth_boundary]
  rw [hu]
  congr 1
  by_cases hx : (x:ℕ)=0
  · simp [hx, death_boundary]
  · have he : ∀ y : Fin (n+1), (y:ℕ)+1=(x:ℕ) ↔ (y:ℕ)=(x:ℕ)-1 := by intro y; omega
    simp_rw [he]
    rw [fin_sum_at_val, if_pos (by omega)]

lemma binom_diagonal (n : ℕ) (x : Fin (n+1)) :
    binomMetropolis n x x = 1-birth n x-death n x := by
  have hs := sum_erase_add (s := (univ : Finset (Fin (n+1))))
    (f := fun y => binomMetropolis n x y) (mem_univ x)
  have he : (∑ y ∈ univ.erase x, binomMetropolis n x y) = birth n x+death n x := by
    have hh := sum_erase_add (s := (univ : Finset (Fin (n+1))))
      (f := fun y => (if (y:ℕ)=(x:ℕ)+1 then birth n x else 0)+
        (if (y:ℕ)+1=(x:ℕ) then death n x else 0)) (mem_univ x)
    rw [neighbor_sum] at hh
    have hu0 : ¬(x:ℕ)=(x:ℕ)+1 := by omega
    have hd0 : ¬(x:ℕ)+1=(x:ℕ) := by omega
    simp only [if_neg hu0, if_neg hd0, add_zero] at hh
    rw [← hh]
    apply sum_congr rfl
    intro y hy
    exact binom_off x y (mem_erase.mp hy).1
  rw [he, (binom_stochastic n).2 x] at hs
  linarith

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_NativeChain
-- End NativeChain

-- Begin HoldingBound
section ModuleScope_HoldingBound

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

def holdExpr (a b : ℕ) : ℝ :=
  1 - min 1 ((b:ℝ)/(a+1))/2 - min 1 ((a:ℝ)/(b+1))/2

lemma holdExpr_comm (a b : ℕ) : holdExpr a b = holdExpr b a := by
  unfold holdExpr
  ring

lemma holdExpr_lower (a b : ℕ) : 2/((a:ℝ)+b+3) ≤ holdExpr a b := by
  have aux : ∀ a b : ℕ, a<b → 2/((a:ℝ)+b+3) ≤ holdExpr a b := by
    intro a b hab
    have hab' : (a:ℝ)+1 ≤ b := by exact_mod_cast hab
    have ha : (0:ℝ) ≤ a := by positivity
    have hb : (0:ℝ) ≤ b := by positivity
    have hu : 1 ≤ (b:ℝ)/(a+1) := (le_div_iff₀ (by positivity)).2 (by linarith)
    have hd : (a:ℝ)/(b+1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have he : holdExpr a b = ((b:ℝ)+1-a)/(2*((b:ℝ)+1)) := by
      unfold holdExpr
      rw [min_eq_left hu, min_eq_right hd]
      field_simp
      ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (show 0 ≤ (b:ℝ)-a-1 by linarith)
      (show 0 ≤ (a:ℝ)+b+1 by positivity)]
  rcases lt_trichotomy a b with h | h | h
  · exact aux a b h
  · subst b
    have ha : (0:ℝ) ≤ a := by positivity
    have hd : (a:ℝ)/(a+1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have he : holdExpr a a = 1/((a:ℝ)+1) := by
      unfold holdExpr
      rw [min_eq_right hd]
      field_simp
      ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith
  · simpa [holdExpr_comm, add_comm] using aux b a h

lemma binom_holding (n : ℕ) (x : Fin (n+1)) :
    2/((n:ℝ)+3) ≤ binomMetropolis n x x := by
  have hx : (x:ℕ) ≤ n := Nat.le_of_lt_succ x.isLt
  have h := holdExpr_lower (x:ℕ) (n-(x:ℕ))
  rw [binom_diagonal]
  have he : ((x:ℕ):ℝ)+((n-(x:ℕ):ℕ):ℝ)+3=(n:ℝ)+3 := by
    rw [Nat.cast_sub hx]
    ring
  rw [he] at h
  simpa [holdExpr, birth, death, Nat.cast_sub hx, sub_add_cancel] using h

lemma birth_lower {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) :
    ((n:ℝ)-k)/(2*n) ≤ birth n k := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hk' : (k:ℝ)+1 ≤ n := by exact_mod_cast hk
  have hkn : (k:ℝ) ≤ n := by linarith
  have h1 : ((n:ℝ)-k)/n ≤ 1 := (div_le_one hn').2 (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have h2 : ((n:ℝ)-k)/n ≤ ((n:ℝ)-k)/(k+1) := by
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hkn) (by positivity) hk'
  have h : ((n:ℝ)-k)/n ≤ min 1 (((n:ℝ)-k)/(k+1)) := le_min h1 h2
  unfold birth
  have he : ((n:ℝ)-k)/(2*n)=(((n:ℝ)-k)/n)/2 := by ring
  rw [he]
  linarith

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_HoldingBound
-- End HoldingBound

-- Begin SymmetricCalculus
section ModuleScope_SymmetricCalculus

namespace LogSobolevMC.Metropolis.Proof
open Set
noncomputable section

def symH (t : ℝ) : ℝ :=
  (t^2 * Real.log (t^2) - (t^2+1)*Real.log ((t^2+1)/2) - (t-1)^2)/2

def symD (t : ℝ) : ℝ :=
  t * Real.log (t^2) - t * Real.log ((t^2+1)/2) - t + 1

def symDD (t : ℝ) : ℝ :=
  Real.log (t^2) - Real.log ((t^2+1)/2) + 2/(t^2+1) - 1

lemma symH_deriv {t : ℝ} (ht : 0 < t) : HasDerivAt symH (symD t) t := by
  have hsq : t^2 ≠ 0 := ne_of_gt (sq_pos_of_pos ht)
  have hp : (t^2+1)/2 ≠ 0 := by positivity
  have ha := ((hasDerivAt_id t).pow 2).log hsq
  have hb := (((hasDerivAt_id t).pow 2).add_const 1 |>.div_const 2).log hp
  have hh := (((((hasDerivAt_id t).pow 2).mul ha).sub
    ((((hasDerivAt_id t).pow 2).add_const 1).mul hb)).sub
    (((hasDerivAt_id t).sub_const 1).pow 2)).div_const 2
  change HasDerivAt symH _ t at hh
  convert hh using 1
  dsimp [symD]
  field_simp
  ring

lemma symD_deriv {t : ℝ} (ht : 0 < t) : HasDerivAt symD (symDD t) t := by
  have hsq : t^2 ≠ 0 := ne_of_gt (sq_pos_of_pos ht)
  have hp : (t^2+1)/2 ≠ 0 := by positivity
  have ha := ((hasDerivAt_id t).pow 2).log hsq
  have hb := (((hasDerivAt_id t).pow 2).add_const 1 |>.div_const 2).log hp
  have hh := ((((hasDerivAt_id t).mul ha).sub ((hasDerivAt_id t).mul hb)).sub
    (hasDerivAt_id t)).add_const 1
  change HasDerivAt symD _ t at hh
  convert hh using 1
  dsimp [symDD]
  field_simp
  ring

lemma symDD_nonpos {t : ℝ} (ht : 0 < t) : symDD t ≤ 0 := by
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hm : 0 < (t^2+1)/2 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos ht2 hm)
  rw [Real.log_div (ne_of_gt ht2) (ne_of_gt hm)] at h
  have he : t^2 / ((t^2+1)/2) + 2/(t^2+1) = 2 := by
    field_simp
  unfold symDD
  linarith

lemma symD_antitone : AntitoneOn symD (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
  · intro t ht
    exact (symD_deriv ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (symD_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact symDD_nonpos (interior_subset ht)

lemma symH_nonpos_pos {t : ℝ} (ht : 0 < t) : symH t ≤ 0 := by
  have h1 : symH 1 = 0 := by norm_num [symH]
  have hd1 : symD 1 = 0 := by norm_num [symD]
  rcases le_total t 1 with hle | hle
  · have hm : MonotoneOn symH (Icc t 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t 1)
      · intro z hz
        exact (symH_deriv (lt_of_lt_of_le ht hz.1)).continuousAt.continuousWithinAt
      · intro z hz
        exact (symH_deriv (lt_of_lt_of_le ht (interior_subset hz).1)).hasDerivWithinAt
      · intro z hz
        have hh := symD_antitone (lt_of_lt_of_le ht (interior_subset hz).1)
          (by norm_num : (1:ℝ) ∈ Ioi 0) (interior_subset hz).2
        simpa [hd1] using hh
    simpa [h1] using hm ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
  · have hm : AntitoneOn symH (Icc 1 t) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 1 t)
      · intro z hz
        exact (symH_deriv (lt_of_lt_of_le (by norm_num) hz.1)).continuousAt.continuousWithinAt
      · intro z hz
        exact (symH_deriv (lt_of_lt_of_le (by norm_num) (interior_subset hz).1)).hasDerivWithinAt
      · intro z hz
        have hh := symD_antitone (by norm_num : (1:ℝ) ∈ Ioi 0)
          (lt_of_lt_of_le (by norm_num) (interior_subset hz).1) (interior_subset hz).1
        simpa [hd1] using hh
    simpa [h1] using hm ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle

lemma symH_nonpos {t : ℝ} (ht : 0 ≤ t) : symH t ≤ 0 := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num [symH, Real.log_div] at *
    linarith
  · exact symH_nonpos_pos h

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_SymmetricCalculus
-- End SymmetricCalculus

-- Begin SymmetricEntropy
section ModuleScope_SymmetricEntropy

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

def xLog (x : ℝ) : ℝ := x * Real.log x

def symEntropy (a b : ℝ) : ℝ :=
  (xLog (a^2) + xLog (b^2))/2 - xLog ((a^2+b^2)/2)

lemma xLog_mul (a b : ℝ) : xLog (a*b) = b*xLog a + a*xLog b := by
  by_cases ha : a = 0
  · simp [ha, xLog]
  by_cases hb : b = 0
  · simp [hb, xLog]
  rw [xLog, Real.log_mul ha hb]
  unfold xLog
  ring

lemma symEntropy_comm (a b : ℝ) : symEntropy a b = symEntropy b a := by
  simp [symEntropy, add_comm]

lemma symEntropy_smul (c a b : ℝ) :
    symEntropy (c*a) (c*b) = c^2 * symEntropy a b := by
  have he : ((c*a)^2+(c*b)^2)/2 = c^2*((a^2+b^2)/2) := by ring
  unfold symEntropy
  rw [he]
  simp only [mul_pow, xLog_mul]
  ring

lemma symEntropy_one (t : ℝ) : symEntropy t 1 - (t-1)^2/2 = symH t := by
  simp [symEntropy, xLog, symH]
  ring

lemma symEntropy_nonneg_args {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    symEntropy a b ≤ (a-b)^2/2 := by
  have main : ∀ a b : ℝ, 0 ≤ a → 0 < b → symEntropy a b ≤ (a-b)^2/2 := by
    intro a b ha hb
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b)
      (symH_nonpos (div_nonneg ha hb.le))
    rw [← symEntropy_one] at hh
    have hs := symEntropy_smul b (a/b) 1
    have he : b*(a/b)=a := by field_simp
    rw [he, mul_one] at hs
    rw [mul_sub, ← hs] at hh
    have he2 : b^2*((a/b-1)^2/2)=(a-b)^2/2 := by
      field_simp
    rw [he2] at hh
    linarith
  rcases eq_or_lt_of_le hb with h | h
  · subst b
    rcases eq_or_lt_of_le ha with h | h
    · subst a
      simp [symEntropy, xLog]
    · have hh := main 0 a (by norm_num) h
      rw [symEntropy_comm] at hh
      simpa using hh
  · exact main a b ha h

lemma symEntropy_le (a b : ℝ) : symEntropy a b ≤ (a-b)^2/2 := by
  have hh := symEntropy_nonneg_args (abs_nonneg a) (abs_nonneg b)
  have he : symEntropy |a| |b| = symEntropy a b := by
    simp [symEntropy, sq_abs]
  rw [he] at hh
  have hab := abs_abs_sub_abs_le_abs_sub a b
  have hs : (|a|-|b|)^2 ≤ (a-b)^2 := by
    nlinarith [sq_abs (|a|-|b|), sq_abs (a-b), abs_nonneg (|a|-|b|), abs_nonneg (a-b)]
  linarith

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_SymmetricEntropy
-- End SymmetricEntropy

-- Begin BinomialMoments
section ModuleScope_BinomialMoments

open scoped BigOperators
open Finset

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

lemma bAvg_mul_sq_le (n : ℕ) (f g : ℕ → ℝ) :
    (bAvg n (fun k => f k*g k))^2 ≤
      bAvg n (fun k => (f k)^2) * bAvg n (fun k => (g k)^2) := by
  unfold bAvg
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro k _
    exact mul_nonneg (bWeight_nonneg n k) (sq_nonneg _)
  · intro k _
    exact mul_nonneg (bWeight_nonneg n k) (sq_nonneg _)
  · intro k _
    apply le_of_eq
    ring

lemma bAvg_sq_mean_le (n : ℕ) (f : ℕ → ℝ) :
    (bAvg n f)^2 ≤ bAvg n (fun k => (f k)^2) := by
  simpa [bAvg_const] using bAvg_mul_sq_le n f (fun _ => 1)

lemma bAvg_sub_sq (n : ℕ) (f g : ℕ → ℝ) :
    bAvg n (fun k => (f k-g k)^2) = bAvg n (fun k => (f k)^2) +
      bAvg n (fun k => (g k)^2) - 2*bAvg n (fun k => f k*g k) := by
  unfold bAvg
  rw [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  ring

lemma bAvg_norm_sub_sq (n : ℕ) (f g : ℕ → ℝ) :
    (Real.sqrt (bAvg n (fun k => (f k)^2)) -
      Real.sqrt (bAvg n (fun k => (g k)^2)))^2 ≤
        bAvg n (fun k => (f k-g k)^2) := by
  have ha := bAvg_sq_nonneg n f
  have hb := bAvg_sq_nonneg n g
  have hc := bAvg_mul_sq_le n f g
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hsp := mul_nonneg (Real.sqrt_nonneg (bAvg n (fun k => (f k)^2)))
    (Real.sqrt_nonneg (bAvg n (fun k => (g k)^2)))
  have hsqprod : (Real.sqrt (bAvg n (fun k => (f k)^2))*
      Real.sqrt (bAvg n (fun k => (g k)^2)))^2 =
      bAvg n (fun k => (f k)^2)*bAvg n (fun k => (g k)^2) := by
    rw [mul_pow, hsa, hsb]
  have hprod : bAvg n (fun k => f k*g k) ≤
      Real.sqrt (bAvg n (fun k => (f k)^2))*Real.sqrt (bAvg n (fun k => (g k)^2)) := by
    nlinarith [sq_nonneg (bAvg n (fun k => f k*g k) -
      Real.sqrt (bAvg n (fun k => (f k)^2))*Real.sqrt (bAvg n (fun k => (g k)^2)))]
  rw [bAvg_sub_sq]
  nlinarith

def bEntropy (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  bAvg n (fun k => xLog ((f k)^2)) - xLog (bAvg n (fun k => (f k)^2))

def bVariance (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  bAvg n (fun k => (f k)^2) - (bAvg n f)^2

lemma bEntropy_zero (f : ℕ → ℝ) : bEntropy 0 f = 0 := by
  simp [bEntropy, bAvg_zero]

lemma bVariance_zero (f : ℕ → ℝ) : bVariance 0 f = 0 := by
  simp [bVariance, bAvg_zero]

lemma bEntropy_succ (n : ℕ) (f : ℕ → ℝ) :
    bEntropy (n+1) f = (bEntropy n f + bEntropy n (fun k => f (k+1)))/2 +
      symEntropy (Real.sqrt (bAvg n (fun k => (f k)^2)))
        (Real.sqrt (bAvg n (fun k => (f (k+1))^2))) := by
  simp only [bEntropy, bAvg_succ, symEntropy,
    Real.sq_sqrt (bAvg_sq_nonneg n f),
    Real.sq_sqrt (bAvg_sq_nonneg n (fun k => f (k+1)))]
  ring

lemma bVariance_succ (n : ℕ) (f : ℕ → ℝ) :
    bVariance (n+1) f = (bVariance n f + bVariance n (fun k => f (k+1)))/2 +
      (bAvg n f-bAvg n (fun k => f (k+1)))^2/4 := by
  simp only [bVariance, bAvg_succ]
  ring

lemma bEntropy_step (n : ℕ) (f : ℕ → ℝ) :
    bEntropy (n+1) f ≤ (bEntropy n f+bEntropy n (fun k => f (k+1)))/2 +
      bAvg n (fun k => (f (k+1)-f k)^2)/2 := by
  rw [bEntropy_succ]
  have h := symEntropy_le (Real.sqrt (bAvg n (fun k => (f k)^2)))
    (Real.sqrt (bAvg n (fun k => (f (k+1))^2)))
  have hh := bAvg_norm_sub_sq n f (fun k => f (k+1))
  have he : bAvg n (fun k => (f k-f (k+1))^2) =
      bAvg n (fun k => (f (k+1)-f k)^2) := by
    apply bAvg_congr
    intro k _
    ring
  rw [he] at hh
  linarith

lemma bVariance_step (n : ℕ) (f : ℕ → ℝ) :
    bVariance (n+1) f ≤ (bVariance n f+bVariance n (fun k => f (k+1)))/2 +
      bAvg n (fun k => (f (k+1)-f k)^2)/4 := by
  rw [bVariance_succ]
  have h := bAvg_sq_mean_le n (fun k => f (k+1)-f k)
  rw [bAvg_sub] at h
  nlinarith

lemma bEntropy_bound (n : ℕ) (f : ℕ → ℝ) :
    bEntropy n f ≤ (n:ℝ)/2*bAvg (n-1) (fun k => (f (k+1)-f k)^2) := by
  induction n generalizing f with
  | zero => simp [bEntropy_zero]
  | succ n ih =>
    have h := bEntropy_step n f
    rcases n with _ | n
    · simpa [bEntropy_zero, div_eq_mul_inv, mul_comm] using h
    · have h0 := ih f
      have h1 := ih (fun k => f (k+1))
      simp only [Nat.add_sub_cancel] at h0 h1 ⊢
      rw [bAvg_succ] at h ⊢
      push_cast at *
      nlinarith

lemma bVariance_bound (n : ℕ) (f : ℕ → ℝ) :
    bVariance n f ≤ (n:ℝ)/4*bAvg (n-1) (fun k => (f (k+1)-f k)^2) := by
  induction n generalizing f with
  | zero => simp [bVariance_zero]
  | succ n ih =>
    have h := bVariance_step n f
    rcases n with _ | n
    · simpa [bVariance_zero, div_eq_mul_inv, mul_comm] using h
    · have h0 := ih f
      have h1 := ih (fun k => f (k+1))
      simp only [Nat.add_sub_cancel] at h0 h1 ⊢
      rw [bAvg_succ] at h ⊢
      push_cast at *
      nlinarith

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_BinomialMoments
-- End BinomialMoments

-- Begin WeightedBasic
section ModuleScope_WeightedBasic

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof

variable {V : Type*} [Fintype V]

def mean (π f : V → ℝ) : ℝ := ∑ x, π x * f x

def squareMean (π f : V → ℝ) : ℝ := ∑ x, π x * (f x)^2

theorem squareMean_nonneg {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    0 ≤ squareMean π f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hπ x) (sq_nonneg _)

theorem mean_const {π : V → ℝ} (hπ : ∑ x, π x = 1) (c : ℝ) :
    mean π (fun _ => c) = c := by
  simp only [mean, ← Finset.sum_mul, hπ, one_mul]

theorem mean_sub (π f g : V → ℝ) :
    mean π (fun x => f x-g x) = mean π f-mean π g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_smul (π f : V → ℝ) (c : ℝ) :
    mean π (fun x => c*f x) = c*mean π f := by
  simp only [mean, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem squareMean_smul (π f : V → ℝ) (c : ℝ) :
    squareMean π (fun x => c*f x) = c^2*squareMean π f := by
  simp only [squareMean, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem variance_eq_squareMean {π : V → ℝ} (hπ : ∑ x, π x = 1) (f : V → ℝ) :
    MarkovMixing.distVar π f = squareMean π f - (mean π f)^2 := by
  have hm : MarkovMixing.distExp π f = mean π f := by
    simp only [MarkovMixing.distExp, mean, mul_comm]
  rw [MarkovMixing.distVar, hm]
  calc
    _ = ∑ x, (π x*(f x)^2 - 2*mean π f*(π x*f x) + (mean π f)^2*π x) := by
      apply Finset.sum_congr rfl; intro x _; ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hπ, mul_one]
      unfold mean squareMean; ring

theorem squareMean_eq_zero_iff {π : V → ℝ} (hπ : ∀ x, 0 < π x) (f : V → ℝ) :
    squareMean π f = 0 ↔ ∀ x, f x=0 := by
  constructor
  · intro h x
    have hx : π x*(f x)^2 ≤ squareMean π f :=
      Finset.single_le_sum (fun y _ => mul_nonneg (hπ y).le (sq_nonneg _)) (Finset.mem_univ x)
    rw [h] at hx
    have : (f x)^2 ≤ 0 := by nlinarith [hπ x]
    nlinarith [sq_nonneg (f x)]
  · intro h; simp [squareMean,h]

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_WeightedBasic
-- End WeightedBasic

-- Begin EntropyBasic
section ModuleScope_EntropyBasic

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem log_term_lower {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    a-m ≤ a*Real.log (a/m) := by
  by_cases h : a=0
  · subst a; simp; exact hm.le
  have ha' : 0<a := lt_of_le_of_ne ha (Ne.symm h)
  have hl := Real.log_le_sub_one_of_pos (div_pos hm ha')
  have he : Real.log (m/a) = -Real.log (a/m) := by
    rw [Real.log_div hm.ne' ha'.ne', Real.log_div ha'.ne' hm.ne']; ring
  rw [he] at hl
  have hh := mul_le_mul_of_nonneg_left hl ha
  have he' : a*(m/a-1)=m-a := by field_simp
  rw [he'] at hh; linarith

theorem log_term_upper {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    a*Real.log (a/m) ≤ a^2/m-a := by
  by_cases h : a=0
  · subst a; simp
  have ha' : 0<a := lt_of_le_of_ne ha (Ne.symm h)
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ha' hm)) ha
  calc
    _ ≤ a*(a/m-1) := hh
    _ = _ := by ring

theorem lpNorm_two_sq {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    (lpNorm π 2 f)^2 = squareMean π f := by
  have hs : (∑ x, |f x|^(2:ℝ)*π x) = squareMean π f := by
    simp only [Real.rpow_two, sq_abs, squareMean, mul_comm]
  unfold lpNorm
  rw [hs, ← Real.sqrt_eq_rpow, Real.sq_sqrt (squareMean_nonneg hπ f)]

theorem entL_eq {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    entL π f = ∑ x, π x*(f x)^2*Real.log ((f x)^2/squareMean π f) := by
  simp only [entL, Real.rpow_two, sq_abs, lpNorm_two_sq hπ]
  apply Finset.sum_congr rfl; intro x _; ring

theorem entL_nonneg_dist {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀ x, 0 < π x) (f : V → ℝ) : 0 ≤ entL π f := by
  rw [entL_eq hπ.1]
  by_cases hm : squareMean π f=0
  · have hf := (squareMean_eq_zero_iff hpos f).mp hm
    simp [hf]
  have hm' := lt_of_le_of_ne (squareMean_nonneg hπ.1 f) (Ne.symm hm)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (log_term_lower (sq_nonneg (f x)) hm') (hπ.1 x))
  have he : (∑ x, π x*((f x)^2-squareMean π f)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.2, one_mul]
    change squareMean π f-squareMean π f=0; ring
  rw [he] at h
  simpa only [mul_assoc] using h

theorem entL_nonneg {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (hpos : ∀ x, 0 < π x) (f : V → ℝ) :
    0 ≤ entL π f := entL_nonneg_dist hπ.1 hpos f

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_EntropyBasic
-- End EntropyBasic

-- Begin NativeFunctional
section ModuleScope_NativeFunctional

open scoped BigOperators
open Finset
open LogSobolevMC.ChiSquare

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

def extendState {n : ℕ} (f : Fin (n+1) → ℝ) (k : ℕ) : ℝ :=
  f ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma extendState_eq {n : ℕ} (f : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    extendState f k = f k := by
  unfold extendState
  congr 1
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ k.isLt)

lemma bAvg_extend {n : ℕ} (f : Fin (n+1) → ℝ) :
    bAvg n (extendState f) = ∑ k, binomPi n k*f k := by
  rw [bAvg_eq_fin]
  simp only [extendState_eq]

lemma native_entropy_expansion {V : Type*} [Fintype V] {π : V → ℝ}
    (hπ : ∀ k, 0 < π k) (f : V → ℝ) :
    entL π f = (∑ k, π k*xLog ((f k)^2)) -
      xLog (∑ k, π k*(f k)^2) := by
  rw [ChiSquare.Proof.entL_eq (fun k => (hπ k).le)]
  by_cases hm : ChiSquare.Proof.squareMean π f=0
  · have hf := (ChiSquare.Proof.squareMean_eq_zero_iff hπ f).mp hm
    simp [hf, xLog]
  have hm' : 0 < ChiSquare.Proof.squareMean π f :=
    lt_of_le_of_ne (ChiSquare.Proof.squareMean_nonneg (fun k => (hπ k).le) f) (Ne.symm hm)
  have he : ∀ k, π k*(f k)^2*Real.log ((f k)^2/ChiSquare.Proof.squareMean π f) =
      π k*xLog ((f k)^2) - (π k*(f k)^2)*Real.log (ChiSquare.Proof.squareMean π f) := by
    intro k
    by_cases hk : f k=0
    · simp [hk, xLog]
    · rw [Real.log_div (pow_ne_zero _ hk) (ne_of_gt hm')]
      unfold xLog
      ring
  simp_rw [he]
  rw [sum_sub_distrib, ← sum_mul]
  rfl

lemma bEntropy_native {n : ℕ} (f : Fin (n+1) → ℝ) :
    bEntropy n (extendState f) = entL (binomPi n) f := by
  rw [native_entropy_expansion (binomPi_pos n)]
  unfold bEntropy
  rw [bAvg_eq_fin, bAvg_eq_fin]
  simp only [extendState_eq]

lemma bVariance_native {n : ℕ} (f : Fin (n+1) → ℝ) :
    bVariance n (extendState f) = MarkovMixing.distVar (binomPi n) f := by
  rw [ChiSquare.Proof.variance_eq_squareMean (binomPi_dist n).2]
  unfold bVariance ChiSquare.Proof.squareMean ChiSquare.Proof.mean
  rw [bAvg_eq_fin, bAvg_eq_fin]
  simp only [extendState_eq]

def edgeMoment (n : ℕ) (f : Fin (n+1) → ℝ) : ℝ :=
  bAvg (n-1) (fun k => (extendState f (k+1)-extendState f k)^2)

lemma entropy_edge_bound (n : ℕ) (f : Fin (n+1) → ℝ) :
    entL (binomPi n) f ≤ (n:ℝ)/2*edgeMoment n f := by
  rw [← bEntropy_native]
  exact bEntropy_bound n (extendState f)

lemma variance_edge_bound (n : ℕ) (f : Fin (n+1) → ℝ) :
    MarkovMixing.distVar (binomPi n) f ≤ (n:ℝ)/4*edgeMoment n f := by
  rw [← bVariance_native]
  exact bVariance_bound n (extendState f)

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_NativeFunctional
-- End NativeFunctional

-- Begin StochasticPowers
section ModuleScope_StochasticPowers

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem stochastic_one : MarkovMixing.IsStochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro x y; by_cases h : x=y <;> simp [Matrix.one_apply,h]
  · intro x
    simp [Matrix.one_apply]

omit [DecidableEq V] in
theorem stochastic_mul {A B : Matrix V V ℝ} (hA : MarkovMixing.IsStochastic A)
    (hB : MarkovMixing.IsStochastic B) : MarkovMixing.IsStochastic (A*B) := by
  constructor
  · intro x y; exact Finset.sum_nonneg fun z _ => mul_nonneg (hA.1 x z) (hB.1 z y)
  · intro x
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hB.2, mul_one, hA.2]

theorem stochastic_pow {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K) (n : ℕ) :
    MarkovMixing.IsStochastic (K^n) := by
  induction n with
  | zero => simpa using (stochastic_one (V := V))
  | succ n ih => rw [pow_succ]; exact stochastic_mul ih hK

theorem stationary_pow {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (n : ℕ) : Matrix.vecMul π (K^n) = π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

omit [DecidableEq V] in
theorem stochastic_entry_le_one {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (x y : V) : K x y ≤ 1 := by
  rw [← hK.2 x]
  exact Finset.single_le_sum (fun z _ => hK.1 x z) (Finset.mem_univ y)

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_StochasticPowers
-- End StochasticPowers

-- Begin DirichletBasic
section ModuleScope_DirichletBasic

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem stationary_sum {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (y : V) : ∑ x, π x*K x y = π y := by
  exact congrFun hπ.2 y

theorem dirichlet_expand (K : Matrix V V ℝ) (π f g : V → ℝ) :
    dirichlet K π f g = ∑ x, π x*f x*g x - ∑ x, ∑ y, π x*K x y*f y*g x := by
  simp only [dirichlet, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x _
  · ring
  · apply Finset.sum_congr rfl; intro y _; ring

theorem dirichlet_square {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) :
    2*dirichlet K π f f = ∑ x, ∑ y, π x*K x y*(f x-f y)^2 := by
  have hleft : (∑ x, ∑ y, π x*K x y*(f x)^2) = squareMean π f := by
    apply Finset.sum_congr rfl; intro x _
    calc
      _ = π x*(f x)^2 * ∑ y, K x y := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
      _ = _ := by rw [hK.2,mul_one]
  have hright : (∑ x, ∑ y, π x*K x y*(f y)^2) = squareMean π f := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [← Finset.sum_mul, stationary_sum hπ y]
  have hexpand : (∑ x, ∑ y, π x*K x y*(f x-f y)^2) =
      (∑ x, ∑ y, π x*K x y*(f x)^2) + (∑ x, ∑ y, π x*K x y*(f y)^2) -
      2*(∑ x, ∑ y, π x*K x y*f y*f x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _; ring
  rw [hexpand,hleft,hright,dirichlet_expand]
  have hs : (∑ x, π x*f x*f x) = squareMean π f := by
    apply Finset.sum_congr rfl; intro x _; ring
  rw [hs]; ring

theorem dirichlet_nonneg {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) : 0 ≤ dirichlet K π f f := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun x _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun y _ =>
      mul_nonneg (mul_nonneg (hπ.1.1 x) (hK.1 x y)) (sq_nonneg (f x-f y))))
  rw [← dirichlet_square hK hπ f] at h; linarith

theorem dirichlet_smul (K : Matrix V V ℝ) (π f : V → ℝ) (c : ℝ) :
    dirichlet K π (fun x => c*f x) (fun x => c*f x) = c^2*dirichlet K π f f := by
  rw [dirichlet_expand,dirichlet_expand]
  simp only [Finset.mul_sum, mul_sub]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x _
  · ring
  · apply Finset.sum_congr rfl; intro y _; ring

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_DirichletBasic
-- End DirichletBasic

-- Begin EdgeEnergy
section ModuleScope_EdgeEnergy

open scoped BigOperators
open Finset
open LogSobolevMC.ChiSquare

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

def upEnergy (n : ℕ) (f : Fin (n+1) → ℝ) : ℝ :=
  ∑ k : Fin n, binomPi n k.castSucc * binomMetropolis n k.castSucc k.succ *
    (f k.castSucc-f k.succ)^2

lemma upEnergy_le (n : ℕ) (f : Fin (n+1) → ℝ) :
    upEnergy n f ≤ dirichlet (binomMetropolis n) (binomPi n) f f := by
  let T := fun x y : Fin (n+1) => binomPi n x*binomMetropolis n x y*(f x-f y)^2
  let U := fun x y : Fin (n+1) => if (y:ℕ)=(x:ℕ)+1 then T x y else 0
  have ht : ∀ x y, T x y = T y x := by
    intro x y
    dsimp [T]
    rw [binom_balance n x y]
    ring
  have hpos : ∀ x y, 0 ≤ T x y := by
    intro x y
    exact mul_nonneg (mul_nonneg (binomPi_pos n x).le ((binom_stochastic n).1 x y)) (sq_nonneg _)
  have hp : ∀ x y, U x y+U y x ≤ T x y := by
    intro x y
    dsimp [U]
    split_ifs with h1 h2
    · omega
    · simp
    · rw [ht]
      simp
    · simpa using hpos x y
  have hs := sum_le_sum (s := (univ : Finset (Fin (n+1)))) (fun x _ =>
    sum_le_sum (s := (univ : Finset (Fin (n+1)))) (fun y _ => hp x y))
  simp only [sum_add_distrib] at hs
  have hswap : (∑ x, ∑ y, U y x) = ∑ x, ∑ y, U x y := by rw [sum_comm]
  rw [hswap] at hs
  have hu : (∑ x, ∑ y, U x y) = upEnergy n f := by
    rw [Fin.sum_univ_castSucc]
    have hlast : (∑ y, U (Fin.last n) y) = 0 := by
      apply sum_eq_zero
      intro y _
      have hn : ¬(y:ℕ)=n+1 := by have := y.isLt; omega
      simp [U, hn]
    rw [hlast, add_zero]
    unfold upEnergy
    apply sum_congr rfl
    intro k _
    have he : ∀ y : Fin (n+1), (y:ℕ)=(k.castSucc:ℕ)+1 ↔ y=k.succ := by
      intro y
      constructor
      · intro h
        exact Fin.ext h
      · intro h
        subst y
        rfl
    simp only [U, he, sum_ite_eq', mem_univ, if_true]
    rfl
  rw [hu] at hs
  have he := ChiSquare.Proof.dirichlet_square (binom_stochastic n) (binom_stationary n) f
  change 2*dirichlet (binomMetropolis n) (binomPi n) f f = ∑ x, ∑ y, T x y at he
  linarith

lemma binom_up (n : ℕ) (k : Fin n) :
    binomMetropolis n k.castSucc k.succ = birth n k := by
  have hne : k.succ ≠ k.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  have h := binom_off k.castSucc k.succ hne
  have hd : ¬(k.succ:ℕ)+1=(k.castSucc:ℕ) := by simp; omega
  rw [if_pos (by rfl), if_neg hd, add_zero] at h
  exact h

lemma weighted_birth_lower (m k : ℕ) (hk : k ≤ m) :
    bWeight m k / 4 ≤ bWeight (m+1) k * birth (m+1) k := by
  have h := birth_lower (by omega : 1 ≤ m + 1) (by omega : k < m + 1)
  have hh := mul_le_mul_of_nonneg_left h (bWeight_nonneg (m+1) k)
  have hc : (m.choose k:ℝ)*((m:ℝ)+1) = ((m+1).choose k:ℝ)*((m:ℝ)+1-k) := by
    have he := Nat.choose_mul_succ_eq m k
    have he' : (m.choose k:ℝ)*((m+1:ℕ):ℝ) =
        ((m+1).choose k:ℝ)*((m+1-k:ℕ):ℝ) := by exact_mod_cast he
    simpa [Nat.cast_sub (show k ≤ m + 1 by omega)] using he'
  have he : bWeight (m+1) k * (((m+1:ℕ):ℝ)-k)/(2*((m+1:ℕ):ℝ)) =
      bWeight m k / 4 := by
    unfold bWeight
    push_cast
    rw [pow_succ]
    field_simp
    nlinarith [hc]
  rw [← he]
  simpa [mul_div_assoc] using hh

lemma edgeMoment_le_energy (n : ℕ) (hn : 1 ≤ n) (f : Fin (n+1) → ℝ) :
    edgeMoment n f ≤ 4*dirichlet (binomMetropolis n) (binomPi n) f f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have hu := upEnergy_le (m+1) f
  have he : edgeMoment (m+1) f / 4 ≤ upEnergy (m+1) f := by
    unfold edgeMoment upEnergy
    simp only [Nat.add_sub_cancel]
    rw [bAvg_eq_fin, sum_div]
    apply sum_le_sum
    intro k _
    rw [binom_up]
    have h0 : extendState f (k:ℕ)=f k.castSucc := extendState_eq f k.castSucc
    have h1 : extendState f ((k:ℕ)+1)=f k.succ := extendState_eq f k.succ
    rw [h0,h1]
    have hh := mul_le_mul_of_nonneg_right
      (weighted_birth_lower m k (Nat.le_of_lt_succ k.isLt)) (sq_nonneg (f k.castSucc-f k.succ))
    change _ ≤ bWeight (m+1) k*birth (m+1) k*(f k.castSucc-f k.succ)^2
    change bWeight m k*(f k.succ-f k.castSucc)^2/4 ≤ _
    nlinarith
  linarith

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_EdgeEnergy
-- End EdgeEnergy

-- Begin IndicatorMoments
section ModuleScope_IndicatorMoments

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

def pointIndicator (x : V) : V → ℝ := fun y => if y=x then 1 else 0

theorem mean_pointIndicator (π : V → ℝ) (x : V) : mean π (pointIndicator x)=π x := by
  simp [mean,pointIndicator]

theorem squareMean_pointIndicator (π : V → ℝ) (x : V) : squareMean π (pointIndicator x)=π x := by
  simp [squareMean,pointIndicator]

theorem variance_pointIndicator {π : V → ℝ} (hπ : MarkovMixing.IsDist π) (x : V) :
    MarkovMixing.distVar π (pointIndicator x)=π x*(1-π x) := by
  rw [variance_eq_squareMean hπ.2,squareMean_pointIndicator,mean_pointIndicator]; ring

theorem entL_pointIndicator {π : V → ℝ} (hπ : ∀ x, 0≤π x) (x : V) :
    entL π (pointIndicator x)=π x*Real.log (1/π x) := by
  rw [entL_eq hπ,squareMean_pointIndicator]
  simp [pointIndicator]

theorem variance_pointIndicator_pos {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (x : V) (hpos : 0<π x) (hx : π x<1) :
    0<MarkovMixing.distVar π (pointIndicator x) := by
  rw [variance_pointIndicator hπ]; exact mul_pos hpos (sub_pos.mpr hx)

theorem entL_pointIndicator_pos {π : V → ℝ} (hπ : ∀ x, 0≤π x)
    (x : V) (hpos : 0<π x) (hx : π x<1) : 0<entL π (pointIndicator x) := by
  rw [entL_pointIndicator hπ]
  exact mul_pos hpos (Real.log_pos ((one_lt_div hpos).mpr hx))

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_IndicatorMoments
-- End IndicatorMoments

-- Begin NativeConstants
section ModuleScope_NativeConstants

open scoped BigOperators
open LogSobolevMC.ChiSquare

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

lemma binom_entropy_bound (n : ℕ) (hn : 1 ≤ n) (f : Fin (n+1) → ℝ) :
    entL (binomPi n) f ≤ 2*(n:ℝ)*dirichlet (binomMetropolis n) (binomPi n) f f := by
  have h := entropy_edge_bound n f
  have he := edgeMoment_le_energy n hn f
  have hn' : (0:ℝ) ≤ n := by positivity
  nlinarith

lemma binom_variance_bound (n : ℕ) (hn : 1 ≤ n) (f : Fin (n+1) → ℝ) :
    MarkovMixing.distVar (binomPi n) f ≤
      (n:ℝ)*dirichlet (binomMetropolis n) (binomPi n) f f := by
  have h := variance_edge_bound n f
  have he := edgeMoment_le_energy n hn f
  have hn' : (0:ℝ) ≤ n := by positivity
  nlinarith

lemma binom_poincare (n : ℕ) (hn : 1 ≤ n) (f : Fin (n+1) → ℝ) :
    (1/(n:ℝ))*MarkovMixing.distVar (binomPi n) f ≤
      dirichlet (binomMetropolis n) (binomPi n) f f := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ hn').2 (by simpa [mul_comm] using binom_variance_bound n hn f)

lemma binom_logSobolev_lower (n : ℕ) (hn : 1 ≤ n) :
    1/(2*(n:ℝ)) ≤ logSobolev (binomMetropolis n) (binomPi n) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  let f := ChiSquare.Proof.pointIndicator (0 : Fin (n+1))
  have hf : 0 < entL (binomPi n) f := ChiSquare.Proof.entL_pointIndicator_pos
    (fun k => (binomPi_pos n k).le) 0 (binomPi_pos n 0) (binomPi_zero_lt_one hn)
  unfold logSobolev
  apply le_csInf
  · exact ⟨_, ⟨f, ne_of_gt hf, rfl⟩⟩
  · rintro r ⟨g, hg, rfl⟩
    have hg' : 0 < entL (binomPi n) g := lt_of_le_of_ne
      (ChiSquare.Proof.entL_nonneg_dist (binomPi_dist n) (binomPi_pos n) g) (Ne.symm hg)
    apply (le_div_iff₀ hg').2
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*n)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using binom_entropy_bound n hn g

lemma binom_gap_lower (n : ℕ) (hn : 1 ≤ n) :
    1/(n:ℝ) ≤ gap (binomMetropolis n) (binomPi n) := by
  let f := ChiSquare.Proof.pointIndicator (0 : Fin (n+1))
  have hf : 0 < MarkovMixing.distVar (binomPi n) f := ChiSquare.Proof.variance_pointIndicator_pos
    (binomPi_dist n) 0 (binomPi_pos n 0) (binomPi_zero_lt_one hn)
  unfold gap
  apply le_csInf
  · exact ⟨_, ⟨f, ne_of_gt hf, rfl⟩⟩
  · rintro r ⟨g, hg, rfl⟩
    have hnon : 0 ≤ MarkovMixing.distVar (binomPi n) g := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (sq_nonneg _) (binomPi_pos n k).le
    have hg' : 0 < MarkovMixing.distVar (binomPi n) g := lt_of_le_of_ne hnon (Ne.symm hg)
    exact (le_div_iff₀ hg').2 (binom_poincare n hn g)

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_NativeConstants
-- End NativeConstants

-- Begin TVComparison
section ModuleScope_TVComparison

open scoped BigOperators
open Finset

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma dist_event_bounds {μ : V → ℝ} (hμ : MarkovMixing.IsDist μ) (A : Finset V) :
    0 ≤ ∑ x ∈ A, μ x ∧ ∑ x ∈ A, μ x ≤ 1 := by
  refine ⟨sum_nonneg (fun x _ => hμ.1 x), ?_⟩
  rw [← hμ.2]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => hμ.1 x)

omit [DecidableEq V] in
lemma tv_nonneg (μ π : V → ℝ) : 0 ≤ MarkovMixing.tvDist μ π := by
  unfold MarkovMixing.tvDist
  have h := le_ciSup (Set.finite_range (fun A : Finset V =>
    |∑ x ∈ A, μ x - ∑ x ∈ A, π x|)).bddAbove (∅ : Finset V)
  simpa using h

omit [DecidableEq V] in
lemma tv_le_one {μ π : V → ℝ} (hμ : MarkovMixing.IsDist μ)
    (hπ : MarkovMixing.IsDist π) : MarkovMixing.tvDist μ π ≤ 1 := by
  unfold MarkovMixing.tvDist
  apply ciSup_le
  intro A
  have hm := dist_event_bounds hμ A
  have hp := dist_event_bounds hπ A
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma event_le_half_l1 {μ π : V → ℝ} (hμ : MarkovMixing.IsDist μ)
    (hπ : MarkovMixing.IsDist π) (A : Finset V) :
    |∑ x ∈ A, μ x-∑ x ∈ A, π x| ≤ (∑ x, |μ x-π x|)/2 := by
  have hz : (∑ x ∈ A, (μ x-π x)) + (∑ x ∈ Aᶜ, (μ x-π x))=0 := by
    rw [sum_add_sum_compl, sum_sub_distrib, hμ.2, hπ.2]
    ring
  have ha := abs_sum_le_sum_abs (fun x => μ x-π x) A
  have hb := abs_sum_le_sum_abs (fun x => μ x-π x) Aᶜ
  have he : (∑ x ∈ Aᶜ, (μ x-π x))=-(∑ x ∈ A, (μ x-π x)) := by linarith
  rw [he, abs_neg] at hb
  have hs := sum_add_sum_compl A (fun x => |μ x-π x|)
  rw [← sum_sub_distrib]
  linarith

omit [DecidableEq V] in
lemma l1_sq_le_chi {μ π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀ x, 0<π x) :
    (∑ x, |μ x-π x|)^2 ≤
      LogSobolevMC.ChiSquare.Proof.squareMean π (fun x => μ x/π x-1) := by
  have hc : (∑ x, |μ x-π x|)^2 ≤ (∑ x, (μ x-π x)^2/π x)*(∑ x, π x) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro x _
      exact div_nonneg (sq_nonneg _) (hpos x).le
    · intro x _
      exact (hpos x).le
    · intro x _
      rw [sq_abs, div_mul_cancel₀ _ (ne_of_gt (hpos x))]
  rw [hπ.2, mul_one] at hc
  have he : (∑ x, (μ x-π x)^2/π x) =
      LogSobolevMC.ChiSquare.Proof.squareMean π (fun x => μ x/π x-1) := by
    apply sum_congr rfl
    intro x _
    have hp : π x ≠ 0 := ne_of_gt (hpos x)
    field_simp
  rwa [he] at hc

lemma tv_le_half_sqrt {μ π : V → ℝ} (hμ : MarkovMixing.IsDist μ)
    (hπ : MarkovMixing.IsDist π) (hpos : ∀ x, 0<π x) :
    MarkovMixing.tvDist μ π ≤
      Real.sqrt (LogSobolevMC.ChiSquare.Proof.squareMean π (fun x => μ x/π x-1))/2 := by
  have hq := LogSobolevMC.ChiSquare.Proof.squareMean_nonneg hπ.1 (fun x => μ x/π x-1)
  have hc := l1_sq_le_chi (μ := μ) hπ hpos
  have hl : (∑ x, |μ x-π x|) ≤
      Real.sqrt (LogSobolevMC.ChiSquare.Proof.squareMean π (fun x => μ x/π x-1)) := by
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg
      (LogSobolevMC.ChiSquare.Proof.squareMean π (fun x => μ x/π x-1)),
      sum_nonneg (s := (univ : Finset V)) (fun x _ => abs_nonneg (μ x-π x))]
  unfold MarkovMixing.tvDist
  apply ciSup_le
  intro A
  have h := event_le_half_l1 hμ hπ A
  linarith

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_TVComparison
-- End TVComparison

-- Begin WeightedConjugation
section ModuleScope_WeightedConjugation

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

noncomputable def weightVector (π f : V → ℝ) : V → ℝ :=
  fun x => Real.sqrt (π x) * f x

noncomputable def unweightVector (π u : V → ℝ) : V → ℝ :=
  fun x => u x / Real.sqrt (π x)

noncomputable def conjugated (K : Matrix V V ℝ) (π : V → ℝ) : Matrix V V ℝ :=
  fun x y => Real.sqrt (π x) * K x y / Real.sqrt (π y)

omit [Fintype V] in
theorem weight_unweight {π : V → ℝ} (hp : ∀ x, 0 < π x) (u : V → ℝ) :
    weightVector π (unweightVector π u) = u := by
  funext x
  simp only [weightVector, unweightVector]
  field_simp [ne_of_gt (Real.sqrt_pos.2 (hp x))]

omit [Fintype V] in
theorem unweight_weight {π : V → ℝ} (hp : ∀ x, 0 < π x) (f : V → ℝ) :
    unweightVector π (weightVector π f) = f := by
  funext x
  simp only [weightVector, unweightVector]
  field_simp [ne_of_gt (Real.sqrt_pos.2 (hp x))]

theorem conjugated_mulVec {π : V → ℝ} (hp : ∀ x, 0 < π x)
    (K : Matrix V V ℝ) (f : V → ℝ) :
    (conjugated K π).mulVec (weightVector π f) = weightVector π (K.mulVec f) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, conjugated, weightVector, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [ne_of_gt (Real.sqrt_pos.2 (hp y))]

 theorem weight_square {π : V → ℝ} (hp : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    ∑ x, (weightVector π f x)^2 = squareMean π f := by
  apply Finset.sum_congr rfl
  intro x _
  simp only [weightVector, mul_pow, Real.sq_sqrt (hp x)]

omit [Fintype V] in
theorem conjugated_symm {K : Matrix V V ℝ} {π : V → ℝ}
    (hp : ∀ x, 0 < π x) (hr : ∀ x y, π x * K x y = π y * K y x) :
    (conjugated K π).IsHermitian := by
  ext x y
  change Real.sqrt (π y) * K y x / Real.sqrt (π x) =
    Real.sqrt (π x) * K x y / Real.sqrt (π y)
  apply (div_eq_div_iff (ne_of_gt (Real.sqrt_pos.2 (hp x)))
    (ne_of_gt (Real.sqrt_pos.2 (hp y)))).2
  calc
    _ = π y * K y x := by rw [mul_right_comm, ← pow_two, Real.sq_sqrt (hp y).le]
    _ = π x * K x y := (hr x y).symm
    _ = _ := by rw [mul_right_comm, ← pow_two, Real.sq_sqrt (hp x).le]

end LogSobolevMC.Metropolis.Proof
end ModuleScope_WeightedConjugation
-- End WeightedConjugation

-- Begin WeightedSpectrum
section ModuleScope_WeightedSpectrum

open scoped BigOperators RealInnerProductSpace
namespace LogSobolevMC.Metropolis.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

structure WeightedSpectrum (K : Matrix V V ℝ) (π : V → ℝ) where
  value : V → ℝ
  vector : V → V → ℝ
  eigen : ∀ i, K.mulVec (vector i) = value i • vector i
  ortho : ∀ i j, ∑ x, π x * vector i x * vector j x = if i = j then 1 else 0
  expand : ∀ (f : V → ℝ) (x : V), ∑ i, (∑ y, π y * vector i y * f y) * vector i x = f x

noncomputable def weightedSpectrum {K : Matrix V V ℝ} {π : V → ℝ}
    (hp : ∀ x, 0 < π x) (hr : ∀ x y, π x * K x y = π y * K y x) :
    WeightedSpectrum K π := by
  let hS := conjugated_symm hp hr
  let b := hS.eigenvectorBasis
  let e : V → V → ℝ := fun i => unweightVector π (b i)
  have he : ∀ i, weightVector π (e i) = ⇑(b i) := fun i => weight_unweight hp _
  have hi : ∀ i j, ∑ x, π x * e i x * e j x = ⟪b i, b j⟫ := by
    intro i j
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro x _
    simp only [RCLike.inner_apply, conj_trivial]
    dsimp [e, unweightVector]
    have hs := Real.sq_sqrt (hp x).le
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hp x))]
    rw [hs]
    ring
  refine ⟨hS.eigenvalues, e, ?_, ?_, ?_⟩
  · intro i
    apply_fun weightVector π
    · rw [← conjugated_mulVec hp, he, hS.mulVec_eigenvectorBasis]
      funext x
      simp only [weightVector, Pi.smul_apply, smul_eq_mul]
      have hx := congrFun (he i) x
      dsimp [weightVector] at hx
      rw [← hx]
      ring
    · intro f g h
      have := congrArg (unweightVector π) h
      simpa only [unweight_weight hp] using this
  · intro i j
    rw [hi, b.inner_eq_ite]
  · intro f x
    have hh := congrArg (fun z : EuclideanSpace ℝ V => z x)
      (b.sum_repr' (WithLp.toLp 2 (weightVector π f)))
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    have hc : ∀ i, ⟪b i, WithLp.toLp 2 (weightVector π f)⟫ = ∑ y, π y * e i y * f y := by
      intro i
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro y _
      simp only [RCLike.inner_apply, conj_trivial, weightVector]
      dsimp [e, unweightVector]
      field_simp [ne_of_gt (Real.sqrt_pos.2 (hp y))]
      rw [Real.sq_sqrt (hp y).le]
      ring
    simp only [hc] at hh
    have hx := Real.sqrt_pos.2 (hp x)
    apply (mul_left_cancel₀ (ne_of_gt hx))
    rw [Finset.mul_sum]
    calc
      _ = ∑ i, (∑ y, π y * e i y * f y) * (b i) x := by
        apply Finset.sum_congr rfl
        intro i _
        have he' := congrFun (he i) x
        dsimp [weightVector] at he'
        rw [← he']; ring
      _ = _ := hh

end LogSobolevMC.Metropolis.Proof
end ModuleScope_WeightedSpectrum
-- End WeightedSpectrum

-- Begin HeatExponential
section ModuleScope_HeatExponential

open scoped BigOperators Matrix.Norms.Operator
open NormedSpace
namespace LogSobolevMC.ChiSquare.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def matrixEntry (x y : V) : Matrix V V ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem heatKernel_series (K : Matrix V V ℝ) (t : ℝ) (x y : V) :
    HasSum (fun n : ℕ => Real.exp (-t)*t^n/(n.factorial:ℝ)*(K^n) x y)
      (Real.exp (-t) * (exp (t • K)) x y) := by
  have h := (matrixEntry x y).hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) (t • K))
  have hh := h.mul_left (Real.exp (-t))
  change HasSum (fun n : ℕ => Real.exp (-t) * (((n.factorial : ℝ)⁻¹ • (t • K)^n) x y))
    (Real.exp (-t) * (exp (t • K)) x y) at hh
  have he : (fun n : ℕ => Real.exp (-t)*t^n/(n.factorial:ℝ)*(K^n) x y) =
      (fun n : ℕ => Real.exp (-t) * (((n.factorial : ℝ)⁻¹ • (t • K)^n) x y)) := by
    funext n
    simp only [smul_pow, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact hh

theorem heatKernel_eq_exp (K : Matrix V V ℝ) (t : ℝ) :
    MarkovMixing.heatKernel K t = Real.exp (-t) • exp (t • K) := by
  ext x y
  exact (heatKernel_series K t x y).tsum_eq

theorem heatKernel_hasSum (K : Matrix V V ℝ) (t : ℝ) (x y : V) :
    HasSum (fun n : ℕ => Real.exp (-t)*t^n/(n.factorial:ℝ)*(K^n) x y)
      (MarkovMixing.heatKernel K t x y) := by
  convert heatKernel_series K t x y using 1
  rw [heatKernel_eq_exp]; rfl

theorem heatKernel_zero (K : Matrix V V ℝ) : MarkovMixing.heatKernel K 0 = 1 := by
  rw [heatKernel_eq_exp]
  simp

theorem heatKernel_add (K : Matrix V V ℝ) (s t : ℝ) :
    MarkovMixing.heatKernel K (s+t) = MarkovMixing.heatKernel K s * MarkovMixing.heatKernel K t := by
  rw [heatKernel_eq_exp, heatKernel_eq_exp, heatKernel_eq_exp, add_smul,
    Matrix.exp_add_of_commute _ _ ((Commute.refl K).smul_left s |>.smul_right t)]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [neg_add, Real.exp_add]

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_HeatExponential
-- End HeatExponential

-- Begin EigenEvolution
section ModuleScope_EigenEvolution

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem eigen_pow {K : Matrix V V ℝ} {f : V → ℝ} {b : ℝ}
    (hf : K.mulVec f = b • f) (l : ℕ) : (K^l).mulVec f = b^l • f := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hf]
    simp only [smul_smul, pow_succ', mul_comm]

 theorem eigen_heat {K : Matrix V V ℝ} {f : V → ℝ} {b : ℝ}
    (hf : K.mulVec f = b • f) (t : ℝ) :
    (MarkovMixing.heatKernel K t).mulVec f = Real.exp (t*(b-1)) • f := by
  funext x
  have hs : HasSum (fun n : ℕ => ∑ y : V,
      (Real.exp (-t) * t^n / (n.factorial : ℝ) * (K^n) x y) * f y)
      ((MarkovMixing.heatKernel K t).mulVec f x) := by
    convert! hasSum_sum (s := Finset.univ) (fun y _ => (heatKernel_hasSum K t x y).mul_right (f y)) using 1
  have hn (n : ℕ) : (∑ y : V,
      (Real.exp (-t) * t^n / (n.factorial : ℝ) * (K^n) x y) * f y) =
      (t*b)^n / (n.factorial : ℝ) * (Real.exp (-t)*f x) := by
    have he := congrFun (eigen_pow hf n) x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at he
    calc
      _ = (Real.exp (-t) * t^n / (n.factorial : ℝ)) *
          (∑ y, (K^n) x y * f y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [he, mul_pow]; ring
  have hs' := (NormedSpace.expSeries_div_hasSum_exp (t*b)).mul_right (Real.exp (-t)*f x)
  rw [← Real.exp_eq_exp_ℝ] at hs'
  have hs'' : HasSum (fun n : ℕ => ∑ y : V,
      (Real.exp (-t) * t^n / (n.factorial : ℝ) * (K^n) x y) * f y)
      (Real.exp (t*b) * (Real.exp (-t)*f x)) := by
    convert! hs' using 1
    funext n
    exact hn n
  have hh := hs.unique hs''
  rw [hh]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← Real.exp_add]
  rw [show t*b + -t = t*(b-1) by ring]

end LogSobolevMC.Metropolis.Proof
end ModuleScope_EigenEvolution
-- End EigenEvolution

-- Begin SpectralExpansion
section ModuleScope_SpectralExpansion

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace WeightedSpectrum
variable {K : Matrix V V ℝ} {π : V → ℝ}

def coeff (s : WeightedSpectrum K π) (f : V → ℝ) (i : V) : ℝ :=
  ∑ y, π y * s.vector i y * f y

theorem parseval (s : WeightedSpectrum K π) (f g : V → ℝ) :
    ∑ i, s.coeff f i * s.coeff g i = ∑ y, π y * f y * g y := by
  simp only [coeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = π y * (∑ i, (∑ z, π z * s.vector i z * f z) * s.vector i y) * g y := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [s.expand]

theorem pow_expand (s : WeightedSpectrum K π) (f : V → ℝ) (l : ℕ) (x : V) :
    (K^l).mulVec f x = ∑ i, s.coeff f i * s.value i^l * s.vector i x := by
  have he : f = ∑ i, s.coeff f i • s.vector i := by
    funext y
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coeff] using (s.expand f y).symm
  conv_lhs => rw [he, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, eigen_pow (s.eigen _), Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem heat_expand (s : WeightedSpectrum K π) (f : V → ℝ) (t : ℝ) (x : V) :
    (MarkovMixing.heatKernel K t).mulVec f x =
      ∑ i, s.coeff f i * Real.exp (t*(s.value i-1)) * s.vector i x := by
  have he : f = ∑ i, s.coeff f i • s.vector i := by
    funext y
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coeff] using (s.expand f y).symm
  conv_lhs => rw [he, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, eigen_heat (s.eigen _), Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem coeff_combination (s : WeightedSpectrum K π) (a : V → ℝ) (j : V) :
    s.coeff (fun x => ∑ i, a i * s.vector i x) j = a j := by
  simp only [coeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, a i * (∑ y, π y * s.vector j y * s.vector i y) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by simp [s.ortho]

 theorem pow_pair (s : WeightedSpectrum K π) (f g : V → ℝ) (l : ℕ) :
    (∑ y, π y * f y * (K^l).mulVec g y) =
      ∑ i, s.coeff f i * s.coeff g i * s.value i^l := by
  rw [← s.parseval]
  apply Finset.sum_congr rfl
  intro i _
  have he : (K^l).mulVec g = fun x => ∑ j, (s.coeff g j * s.value j^l) * s.vector j x :=
    funext (s.pow_expand g l)
  rw [he, s.coeff_combination]
  ring

end WeightedSpectrum
end LogSobolevMC.Metropolis.Proof
end ModuleScope_SpectralExpansion
-- End SpectralExpansion

-- Begin HeatStochastic
section ModuleScope_HeatStochastic

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem poisson_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-t)*t^n/(n.factorial:ℝ)) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp t).mul_left (Real.exp (-t)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]

theorem heatKernel_nonneg {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (x y : V) : 0 ≤ MarkovMixing.heatKernel K t x y := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (by positivity) ((stochastic_pow hK n).1 x y)

theorem heatKernel_row_sum {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (t : ℝ) (x : V) : ∑ y, MarkovMixing.heatKernel K t x y = 1 := by
  have h := hasSum_sum (s := Finset.univ) (fun y _ => heatKernel_hasSum K t x y)
  simp only [← Finset.mul_sum, (stochastic_pow hK _).2, mul_one] at h
  exact h.unique (poisson_hasSum t)

theorem heatKernel_stationary {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (t : ℝ) (y : V) :
    ∑ x, π x*MarkovMixing.heatKernel K t x y = π y := by
  have h := hasSum_sum (s := Finset.univ) (fun x _ => (heatKernel_hasSum K t x y).mul_left (π x))
  have he (n : ℕ) :
      (∑ x, π x*(Real.exp (-t)*t^n/(n.factorial:ℝ)*(K^n) x y)) =
      Real.exp (-t)*t^n/(n.factorial:ℝ)*π y := by
    have hp := congrFun (stationary_pow hπ n) y
    change ∑ x, π x*(K^n) x y = π y at hp
    rw [← hp, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; ring
  simp only [he] at h
  simpa using h.unique ((poisson_hasSum t).mul_right (π y))

theorem heatKernel_diag_pos {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (x : V) : 0 < MarkovMixing.heatKernel K t x x := by
  have h := (heatKernel_hasSum K t x x).summable.le_tsum 0
    (fun n _ => mul_nonneg (by positivity) ((stochastic_pow hK n).1 x x))
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, Matrix.one_apply_eq] at h
  exact (Real.exp_pos (-t)).trans_le h

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_HeatStochastic
-- End HeatStochastic

-- Begin PointSpectrum
section ModuleScope_PointSpectrum

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def pointCentered (π : V → ℝ) (x : V) : V → ℝ :=
  fun y => (if y=x then 1/π x else 0)-1

namespace WeightedSpectrum
variable {K : Matrix V V ℝ} {π : V → ℝ}

theorem point_coeff (s : WeightedSpectrum K π) (hp : ∀ x, 0 < π x) (x i : V) :
    s.coeff (pointCentered π x) i = s.vector i x - mean π (s.vector i) := by
  simp only [coeff, pointCentered, mul_sub, mul_one, Finset.sum_sub_distrib]
  have h : (∑ y, π y * s.vector i y * (if y=x then 1/π x else 0)) = s.vector i x := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp [ne_of_gt (hp x)]
  rw [h]
  rfl

theorem pow_kernel (s : WeightedSpectrum K π) (l : ℕ) (x y : V) :
    (K^l) x y = π y * (∑ i, s.value i^l * s.vector i x * s.vector i y) := by
  have h := s.pow_expand (Pi.single y 1) l x
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coeff, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem heat_kernel (s : WeightedSpectrum K π) (t : ℝ) (x y : V) :
    MarkovMixing.heatKernel K t x y =
      π y * (∑ i, Real.exp (t*(s.value i-1)) * s.vector i x * s.vector i y) := by
  have h := s.heat_expand (Pi.single y 1) t x
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coeff, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem pow_reversible (s : WeightedSpectrum K π) (l : ℕ) (x y : V) :
    π x * (K^l) x y = π y * (K^l) y x := by
  rw [s.pow_kernel, s.pow_kernel]
  have h : (∑ i, s.value i^l * s.vector i x * s.vector i y) =
      ∑ i, s.value i^l * s.vector i y * s.vector i x := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h]; ring

theorem pow_point (s : WeightedSpectrum K π) (hp : ∀ x, 0 < π x)
    (hK : MarkovMixing.IsStochastic K) (l : ℕ) (x y : V) :
    (K^l).mulVec (pointCentered π x) y = (K^l) x y / π y - 1 := by
  have h := s.pow_reversible l x y
  simp only [Matrix.mulVec, dotProduct, pointCentered, mul_sub, mul_one,
    Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, (stochastic_pow hK l).2]
  congr 1
  rw [mul_one_div]
  apply (div_eq_div_iff (ne_of_gt (hp x)) (ne_of_gt (hp y))).2
  nlinarith

end WeightedSpectrum
end LogSobolevMC.Metropolis.Proof
end ModuleScope_PointSpectrum
-- End PointSpectrum

-- Begin SpectralNorms
section ModuleScope_SpectralNorms

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace WeightedSpectrum
variable {K : Matrix V V ℝ} {π : V → ℝ}

theorem square_parseval (s : WeightedSpectrum K π) (f : V → ℝ) :
    squareMean π f = ∑ i, s.coeff f i ^ 2 := by
  have h := s.parseval f f
  simpa only [squareMean, pow_two, mul_assoc] using h.symm

theorem pow_square (s : WeightedSpectrum K π) (f : V → ℝ) (l : ℕ) :
    squareMean π ((K^l).mulVec f) = ∑ i, s.value i^(2*l) * s.coeff f i^2 := by
  rw [s.square_parseval]
  apply Finset.sum_congr rfl
  intro i _
  have he : (K^l).mulVec f = fun x => ∑ j, (s.coeff f j * s.value j^l) * s.vector j x :=
    funext (s.pow_expand f l)
  rw [he, s.coeff_combination]
  rw [mul_pow, ← pow_mul, show l*2=2*l by omega]
  ring

theorem heat_square (s : WeightedSpectrum K π) (f : V → ℝ) (t : ℝ) :
    squareMean π ((MarkovMixing.heatKernel K t).mulVec f) =
      ∑ i, Real.exp (2*t*(s.value i-1)) * s.coeff f i^2 := by
  rw [s.square_parseval]
  apply Finset.sum_congr rfl
  intro i _
  have he : (MarkovMixing.heatKernel K t).mulVec f = fun x =>
      ∑ j, (s.coeff f j * Real.exp (t*(s.value j-1))) * s.vector j x :=
    funext (s.heat_expand f t)
  rw [he, s.coeff_combination, mul_pow, show (Real.exp (t*(s.value i-1)))^2 = Real.exp (t*(s.value i-1)+t*(s.value i-1)) by rw [pow_two, Real.exp_add]]
  rw [show t*(s.value i-1)+t*(s.value i-1)=2*t*(s.value i-1) by ring]
  ring

theorem heat_point (s : WeightedSpectrum K π) (hp : ∀ x, 0 < π x)
    (hK : MarkovMixing.IsStochastic K) (t : ℝ) (x y : V) :
    (MarkovMixing.heatKernel K t).mulVec (pointCentered π x) y =
      density K π t x y - 1 := by
  have h : π x * MarkovMixing.heatKernel K t x y =
      π y * MarkovMixing.heatKernel K t y x := by
    rw [s.heat_kernel, s.heat_kernel]
    have he : (∑ i, Real.exp (t*(s.value i-1)) * s.vector i x * s.vector i y) =
        ∑ i, Real.exp (t*(s.value i-1)) * s.vector i y * s.vector i x := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [he]; ring
  simp only [Matrix.mulVec, dotProduct, pointCentered, mul_sub, mul_one,
    Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, heatKernel_row_sum hK, density]
  congr 1
  rw [mul_one_div]
  apply (div_eq_div_iff (ne_of_gt (hp x)) (ne_of_gt (hp y))).2
  nlinarith

theorem point_mass (s : WeightedSpectrum K π) (hp : ∀ x, 0 < π x)
    (hπ : ∑ x, π x=1) (x : V) :
    ∑ i, s.coeff (pointCentered π x) i^2 = 1/π x-1 := by
  rw [← s.square_parseval]
  have he : ∀ y, π y * (pointCentered π x y)^2 =
      (if y=x then 1/π x-2 else 0)+π y := by
    intro y
    by_cases h : y=x
    · subst y
      simp only [pointCentered, ite_true]
      field_simp [ne_of_gt (hp x)]
      ring
    · simp [pointCentered,h]
  simp only [squareMean,he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,
    if_true,hπ]
  ring

end WeightedSpectrum
end LogSobolevMC.Metropolis.Proof
end ModuleScope_SpectralNorms
-- End SpectralNorms

-- Begin EigenBounds
section ModuleScope_EigenBounds

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem eigen_abs_le_rows {K : Matrix V V ℝ} {f : V → ℝ} {b r : ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = r)
    (hf : f ≠ 0) (he : K.mulVec f = b • f) : |b| ≤ r := by
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hf
  have hz' : f z ≠ 0 := hz
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ (fun x => |f x|)
    ⟨z, Finset.mem_univ z⟩
  have hpos : 0 < |f x| := (abs_pos.2 hz').trans_le (hx z (Finset.mem_univ z))
  have h : |b| * |f x| ≤ r * |f x| := by
    rw [← abs_mul]
    have he' := congrFun he x
    simp only [Pi.smul_apply, smul_eq_mul] at he'
    rw [← he']
    calc
      _ ≤ ∑ y, |K x y * f y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, K x y * |f y| := by simp only [abs_mul, abs_of_nonneg (hK x _)]
      _ ≤ ∑ y, K x y * |f x| := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hx y (Finset.mem_univ y)) (hK x y)
      _ = _ := by rw [← Finset.sum_mul, hrow]
  nlinarith

theorem eigen_lower_hold {K : Matrix V V ℝ} {f : V → ℝ} {b h : ℝ}
    (hK : MarkovMixing.IsStochastic K) (hhold : ∀ x, h ≤ K x x)
    (hf : f ≠ 0) (he : K.mulVec f = b • f) : 2*h-1 ≤ b := by
  let R := K - h • (1 : Matrix V V ℝ)
  have hR : ∀ x y, 0 ≤ R x y := by
    intro x y
    by_cases hxy : x = y
    · subst y; simpa [R] using sub_nonneg.mpr (hhold x)
    · simpa [R, Matrix.one_apply, hxy] using hK.1 x y
  have hrow : ∀ x, ∑ y, R x y = 1-h := by
    intro x
    simp only [R, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hK.2]
    simp [Matrix.one_apply]
  have he' : R.mulVec f = (b-h) • f := by
    simp only [R, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he,
      sub_smul]
  have hh := eigen_abs_le_rows hR hrow hf he'
  have := (abs_le.mp hh).1
  linarith

namespace WeightedSpectrum
variable {K : Matrix V V ℝ} {π : V → ℝ}

theorem vector_ne_zero (s : WeightedSpectrum K π) (i : V) : s.vector i ≠ 0 := by
  intro h
  have := s.ortho i i
  simp [h] at this

theorem eigen_mean (s : WeightedSpectrum K π) (hπ : MarkovMixing.IsStationary K π)
    (i : V) : (s.value i-1)*mean π (s.vector i) = 0 := by
  have h : mean π (K.mulVec (s.vector i)) = mean π (s.vector i) := by
    simp only [mean, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← Finset.sum_mul, stationary_sum hπ]
  rw [s.eigen] at h
  change mean π (fun x => s.value i * s.vector i x) = _ at h
  rw [mean_smul] at h
  nlinarith

theorem eigen_energy (s : WeightedSpectrum K π) (i : V) :
    dirichlet K π (s.vector i) (s.vector i) = 1-s.value i := by
  have hn : (∑ x, π x * s.vector i x * s.vector i x)=1 := by simpa using s.ortho i i
  rw [dirichlet, s.eigen]
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    _ = (1-s.value i) * (∑ x, π x * s.vector i x * s.vector i x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hn, mul_one]

end WeightedSpectrum
end LogSobolevMC.Metropolis.Proof
end ModuleScope_EigenBounds
-- End EigenBounds

-- Begin PointOdd
section ModuleScope_PointOdd

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mean_point {π : V → ℝ} (hp : ∀ x, 0 < π x) (hπ : ∑ x, π x=1) (x : V) :
    mean π (pointCentered π x)=0 := by
  simp only [mean,pointCentered,mul_sub,mul_one,Finset.sum_sub_distrib,
    mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,hπ]
  field_simp [ne_of_gt (hp x)]
  ring

theorem point_pair {π : V → ℝ} (hp : ∀ x, 0 < π x) (x : V) (f : V → ℝ) :
    (∑ y, π y * pointCentered π x y * f y) = f x-mean π f := by
  simp only [pointCentered,mul_sub,mul_one,sub_mul,Finset.sum_sub_distrib,
    mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  congr 1
  field_simp [ne_of_gt (hp x)]

theorem mean_pow {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (f : V → ℝ) (l : ℕ) :
    mean π ((K^l).mulVec f)=mean π f := by
  have hs (y : V) : ∑ x, π x*(K^l) x y=π y := congrFun (stationary_pow hπ l) y
  simp only [mean,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc,← Finset.sum_mul,hs]

namespace WeightedSpectrum
variable {K : Matrix V V ℝ} {π : V → ℝ}

theorem point_odd (s : WeightedSpectrum K π) (hp : ∀ x, 0 < π x)
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (x : V) (j : ℕ) :
    -1 ≤ ∑ i, s.value i^(2*j+1)*s.coeff (pointCentered π x) i^2 := by
  have he := s.pow_pair (pointCentered π x) (pointCentered π x) (2*j+1)
  rw [point_pair hp,mean_pow hπ,mean_point hp hπ.1.2,s.pow_point hp hK] at he
  have hh : 0 ≤ (K^(2*j+1)) x x / π x := div_nonneg ((stochastic_pow hK _).1 x x) (hp x).le
  have ht : (∑ i, s.coeff (pointCentered π x) i * s.coeff (pointCentered π x) i * s.value i^(2*j+1)) =
      ∑ i, s.value i^(2*j+1)*s.coeff (pointCentered π x) i^2 := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [ht] at he
  linarith

 theorem constant_eigen_coeff (s : WeightedSpectrum K π)
    (hp : ∀ x, 0 < π x)
    (g : ℝ) (hg : 0<g)
    (hgap : ∀ f, g*MarkovMixing.distVar π f ≤ dirichlet K π f f)
    (i : V) (hi : s.value i=1) (x : V) : s.coeff (pointCentered π x) i=0 := by
  rw [s.point_coeff hp]
  have h := hgap (s.vector i)
  rw [s.eigen_energy,hi,sub_self] at h
  have hv : MarkovMixing.distVar π (s.vector i) ≤ 0 := by nlinarith
  have hs : 0 ≤ ∑ y, π y*(s.vector i y-mean π (s.vector i))^2 :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hp y).le (sq_nonneg _)
  have he : MarkovMixing.distVar π (s.vector i) =
      ∑ y, π y*(s.vector i y-mean π (s.vector i))^2 := by
    simp only [MarkovMixing.distVar,MarkovMixing.distExp,mean,mul_comm]
  rw [he] at hv
  have hx := Finset.single_le_sum (fun y _ => mul_nonneg (hp y).le (sq_nonneg (s.vector i y-mean π (s.vector i)))) (Finset.mem_univ x)
  have hz : (s.vector i x-mean π (s.vector i))^2≤0 := by nlinarith [hp x]
  nlinarith [sq_nonneg (s.vector i x-mean π (s.vector i))]

end WeightedSpectrum
end LogSobolevMC.Metropolis.Proof
end ModuleScope_PointOdd
-- End PointOdd

-- Begin SpectralScalar
section ModuleScope_SpectralScalar

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof

theorem nonneg_pow_le_exp {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    a^m ≤ Real.exp ((m:ℝ)*(a-1)) := by
  have h : a ≤ Real.exp (a-1) := by linarith [Real.add_one_le_exp (a-1)]
  calc
    _ ≤ (Real.exp (a-1))^m := pow_le_pow_left₀ ha h m
    _ = _ := (Real.exp_nat_mul (a-1) m).symm

theorem negative_even_le_odd {a : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 0) (j : ℕ) :
    a^(2*j+2) ≤ -a^(2*j+1) := by
  have hp : 0 ≤ a^(2*j) := by rw [Nat.mul_comm 2 j, pow_mul]; exact sq_nonneg _
  have hs : a^2 ≤ -a := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ a+1) ha']
  have hh := mul_le_mul_of_nonneg_left hs hp
  simpa only [pow_add, pow_one, pow_two, mul_neg] using hh

theorem positive_odd_le_heat {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (j : ℕ) :
    a^(2*j+1) ≤ Real.exp (2*(j:ℝ)*(a-1)) := by
  calc
    _ = a^(2*j)*a := by rw [pow_succ]
    _ ≤ a^(2*j) := mul_le_of_le_one_right (pow_nonneg ha _) ha'
    _ ≤ _ := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using nonneg_pow_le_exp ha (2*j)

theorem spectral_comparison {I : Type*} [Fintype I]
    (β z : I → ℝ) (hz : ∀ i, 0 ≤ z i) (hβ : ∀ i, |β i| ≤ 1)
    (b : ℝ) (hb : 0 ≤ b) (hneg : ∀ i, β i < 0 → |β i| ≤ b)
    (j k : ℕ) (hodd : -1 ≤ ∑ i, β i^(2*j+1)*z i) :
    (∑ i, β i^(2*(j+k+1))*z i) ≤
      b^(2*k)*(1+∑ i, Real.exp (2*(j:ℝ)*(β i-1))*z i) +
        ∑ i, Real.exp (2*((j+k+1:ℕ):ℝ)*(β i-1))*z i := by
  classical
  let N := ∑ i, if β i < 0 then -β i^(2*j+1)*z i else 0
  let P := ∑ i, if β i < 0 then 0 else β i^(2*j+1)*z i
  have hNP : P-N = ∑ i, β i^(2*j+1)*z i := by
    dsimp [N,P]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hN : N ≤ 1+P := by linarith
  have hP : P ≤ ∑ i, Real.exp (2*(j:ℝ)*(β i-1))*z i := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · exact mul_nonneg (Real.exp_pos _).le (hz i)
    · exact mul_le_mul_of_nonneg_right
        (positive_odd_le_heat (le_of_not_gt hi) (abs_le.mp (hβ i)).2 j) (hz i)
  have hbase : (∑ i, if β i < 0 then β i^(2*j+2)*z i else 0) ≤
      1+∑ i, Real.exp (2*(j:ℝ)*(β i-1))*z i := by
    apply le_trans _ (hN.trans (add_le_add (le_refl 1) hP))
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · exact mul_le_mul_of_nonneg_right
        (negative_even_le_odd (abs_le.mp (hβ i)).1 hi.le j) (hz i)
    · rfl
  have hterm : ∀ i, β i^(2*(j+k+1))*z i ≤
      b^(2*k)*(if β i < 0 then β i^(2*j+2)*z i else 0) +
        Real.exp (2*((j+k+1:ℕ):ℝ)*(β i-1))*z i := by
    intro i
    by_cases hi : β i < 0
    · rw [if_pos hi]
      have hpow : β i^(2*k) ≤ b^(2*k) := by
        have hh := pow_le_pow_left₀ (abs_nonneg (β i)) (hneg i hi) (2*k)
        simpa only [pow_mul, sq_abs] using hh
      have he : 2*(j+k+1)=2*k+(2*j+2) := by omega
      rw [he,pow_add]
      have hq : 0 ≤ β i^(2*j+2)*z i := mul_nonneg (by rw [show 2*j+2=(j+1)*2 by omega, pow_mul]; exact sq_nonneg _) (hz i)
      have hh := mul_le_mul_of_nonneg_right hpow hq
      have ht : 0 ≤ Real.exp (2*((j+k+1:ℕ):ℝ)*(β i-1))*z i := mul_nonneg (Real.exp_pos _).le (hz i)
      nlinarith
    · rw [if_neg hi,mul_zero,zero_add]
      apply mul_le_mul_of_nonneg_right _ (hz i)
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using nonneg_pow_le_exp (le_of_not_gt hi) (2*(j+k+1))
  calc
    _ ≤ ∑ i, (b^(2*k)*(if β i < 0 then β i^(2*j+2)*z i else 0) +
        Real.exp (2*((j+k+1:ℕ):ℝ)*(β i-1))*z i) := Finset.sum_le_sum fun i _ => hterm i
    _ = b^(2*k)*(∑ i, if β i < 0 then β i^(2*j+2)*z i else 0) +
        ∑ i, Real.exp (2*((j+k+1:ℕ):ℝ)*(β i-1))*z i := by rw [Finset.sum_add_distrib,← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hbase (pow_nonneg hb _)) (le_refl _)

end LogSobolevMC.Metropolis.Proof
end ModuleScope_SpectralScalar
-- End SpectralScalar

-- Begin CenteredBounds
section ModuleScope_CenteredBounds

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace WeightedSpectrum
variable {K : Matrix V V ℝ} {π : V → ℝ}

theorem nonconstant_upper (s : WeightedSpectrum K π)
    (hπ : MarkovMixing.IsStationary K π) (g : ℝ)
    (hgap : ∀ f, g*MarkovMixing.distVar π f ≤ dirichlet K π f f)
    (i : V) (hi : s.value i ≠ 1) : s.value i ≤ 1-g := by
  have hm : mean π (s.vector i)=0 :=
    (mul_eq_zero.mp (s.eigen_mean hπ i)).resolve_left (sub_ne_zero.mpr hi)
  have hn : squareMean π (s.vector i)=1 := by
    have hh := s.ortho i i
    simpa [squareMean,pow_two,mul_assoc] using hh
  have hv : MarkovMixing.distVar π (s.vector i)=1 := by
    rw [variance_eq_squareMean hπ.1.2,hn,hm]; norm_num
  have hh := hgap (s.vector i)
  rw [hv,s.eigen_energy,mul_one] at hh
  linarith

theorem centered_abs_bound (s : WeightedSpectrum K π)
    (hp : ∀ x, 0 < π x) (hK : MarkovMixing.IsStochastic K)
    (hπ : MarkovMixing.IsStationary K π) (g : ℝ) (hg : 0<g)
    (hgap : ∀ f, g*MarkovMixing.distVar π f ≤ dirichlet K π f f)
    (hhold : ∀ y, g/2 ≤ K y y) (x i : V)
    (hi : s.coeff (pointCentered π x) i ≠ 0) : |s.value i| ≤ 1-g := by
  have hne : s.value i ≠ 1 := fun h => hi (s.constant_eigen_coeff hp g hg hgap i h x)
  have hu := s.nonconstant_upper hπ g hgap i hne
  have hl := eigen_lower_hold hK hhold (s.vector_ne_zero i) (s.eigen i)
  rw [abs_le]
  constructor <;> linarith

theorem coarse_square (s : WeightedSpectrum K π)
    (hp : ∀ x, 0 < π x) (hK : MarkovMixing.IsStochastic K)
    (hπ : MarkovMixing.IsStationary K π) (g : ℝ) (hg : 0<g)
    (hgap : ∀ f, g*MarkovMixing.distVar π f ≤ dirichlet K π f f)
    (hhold : ∀ y, g/2 ≤ K y y) (x : V) (l : ℕ) :
    squareMean π (fun y => (K^l) x y / π y-1) ≤
      (1/π x-1)*Real.exp (-2*(l:ℝ)*g) := by
  have he : (fun y => (K^l) x y / π y-1) = (K^l).mulVec (pointCentered π x) :=
    funext fun y => (s.pow_point hp hK l x y).symm
  rw [he,s.pow_square,← s.point_mass hp hπ.1.2 x,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : s.coeff (pointCentered π x) i=0
  · simp [hi]
  · have hb := s.centered_abs_bound hp hK hπ g hg hgap hhold x i hi
    have hpow : s.value i^(2*l) ≤ Real.exp (-2*(l:ℝ)*g) := by
      calc
        _ = |s.value i|^(2*l) := by rw [pow_mul,pow_mul,sq_abs]
        _ ≤ Real.exp (((2*l:ℕ):ℝ)*(|s.value i|-1)) := nonneg_pow_le_exp (abs_nonneg _) _
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          simp only [Nat.cast_mul,Nat.cast_ofNat]
          nlinarith [Nat.cast_nonneg (α := ℝ) l]
    have hh := mul_le_mul_of_nonneg_right hpow (sq_nonneg (s.coeff (pointCentered π x) i))
    nlinarith

end WeightedSpectrum
end LogSobolevMC.Metropolis.Proof
end ModuleScope_CenteredBounds
-- End CenteredBounds

-- Begin DiscreteHeatComparison
section ModuleScope_DiscreteHeatComparison

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem discrete_heat_comparison {K : Matrix V V ℝ} {π : V → ℝ}
    (hp : ∀ x, 0 < π x) (hK : MarkovMixing.IsStochastic K)
    (hπ : MarkovMixing.IsStationary K π)
    (hr : ∀ x y, π x*K x y=π y*K y x) (b : ℝ) (hb : 0≤b)
    (hhold : ∀ y, (1-b)/2 ≤ K y y) (x : V) (j k : ℕ) :
    squareMean π (fun y => (K^(j+k+1)) x y / π y-1) ≤
      b^(2*k)*(1+squareMean π (fun y => density K π j x y-1)) +
      squareMean π (fun y => density K π (j+k+1 : ℕ) x y-1) := by
  let s := weightedSpectrum hp hr
  have hab : ∀ i, |s.value i|≤1 := fun i =>
    eigen_abs_le_rows hK.1 hK.2 (s.vector_ne_zero i) (s.eigen i)
  have hneg : ∀ i, s.value i<0 → |s.value i|≤b := by
    intro i hi
    have hh := eigen_lower_hold hK hhold (s.vector_ne_zero i) (s.eigen i)
    rw [abs_of_neg hi]
    linarith
  have h := spectral_comparison s.value
    (fun i => s.coeff (pointCentered π x) i^2) (fun i => sq_nonneg _) hab b hb hneg j k
    (s.point_odd hp hK hπ x j)
  have hd : squareMean π (fun y => (K^(j+k+1)) x y / π y-1) =
      ∑ i, s.value i^(2*(j+k+1))*s.coeff (pointCentered π x) i^2 := by
    have he : (fun y => (K^(j+k+1)) x y / π y-1) =
        (K^(j+k+1)).mulVec (pointCentered π x) := funext fun y =>
      (s.pow_point hp hK _ x y).symm
    rw [he,s.pow_square]
  have ht (t : ℝ) : squareMean π (fun y => density K π t x y-1) =
      ∑ i, Real.exp (2*t*(s.value i-1))*s.coeff (pointCentered π x) i^2 := by
    have he : (fun y => density K π t x y-1) =
        (MarkovMixing.heatKernel K t).mulVec (pointCentered π x) := funext fun y =>
      (s.heat_point hp hK t x y).symm
    rw [he,s.heat_square]
  rw [hd,ht,ht]
  exact h

end LogSobolevMC.Metropolis.Proof
end ModuleScope_DiscreteHeatComparison
-- End DiscreteHeatComparison

-- Begin HeatDerivative
section ModuleScope_HeatDerivative

open scoped BigOperators Matrix.Norms.Operator
open NormedSpace
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem heatKernel_hasDerivAt (K : Matrix V V ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => MarkovMixing.heatKernel K s)
      (K*MarkovMixing.heatKernel K t - MarkovMixing.heatKernel K t) t := by
  have h := ((hasDerivAt_id t).neg.exp).smul (hasDerivAt_exp_smul_const' K t)
  apply (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => heatKernel_eq_exp K s)).congr_deriv
  rw [heatKernel_eq_exp]
  simp only [Pi.neg_apply, id_eq, Matrix.mul_smul, mul_neg, mul_one, neg_smul]
  simp only [sub_eq_add_neg]
  rfl

theorem heatKernel_entry_hasDerivAt (K : Matrix V V ℝ) (t : ℝ) (x y : V) :
    HasDerivAt (fun s : ℝ => MarkovMixing.heatKernel K s x y)
      ((K*MarkovMixing.heatKernel K t) x y - MarkovMixing.heatKernel K t x y) t := by
  exact (matrixEntry x y).hasFDerivAt.comp_hasDerivAt t (heatKernel_hasDerivAt K t)

theorem heatOp_hasDerivAt (K : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) (x : V) :
    HasDerivAt (fun s : ℝ => heatOp K s f x)
      (K.mulVec (heatOp K t f) x-heatOp K t f x) t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun y _ =>
    (heatKernel_entry_hasDerivAt K t x y).mul_const (f y))
  have he : (∑ y, fun s : ℝ => MarkovMixing.heatKernel K s x y*f y) =
      (fun s : ℝ => heatOp K s f x) := by
    funext s; simp only [Finset.sum_apply, heatOp, Matrix.mulVec, dotProduct]
  rw [he] at h
  apply h.congr_deriv
  change _ = K.mulVec ((MarkovMixing.heatKernel K t).mulVec f) x -
    (MarkovMixing.heatKernel K t).mulVec f x
  rw [Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_HeatDerivative
-- End HeatDerivative

-- Begin HeatCalculus
section ModuleScope_HeatCalculus

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem heatOp_zero (K : Matrix V V ℝ) (f : V → ℝ) : heatOp K 0 f = f := by
  unfold heatOp; rw [heatKernel_zero]; exact Matrix.one_mulVec f

theorem heatOp_add (K : Matrix V V ℝ) (s t : ℝ) (f : V → ℝ) :
    heatOp K (s+t) f = heatOp K s (heatOp K t f) := by
  unfold heatOp; rw [heatKernel_add, Matrix.mulVec_mulVec]

theorem heatOp_pos {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) {f : V → ℝ} (hf : ∀ x, 0 < f x) (x : V) :
    0 < heatOp K t f x := by
  have h : 0 < MarkovMixing.heatKernel K t x x*f x :=
    mul_pos (heatKernel_diag_pos hK ht x) (hf x)
  exact h.trans_le (Finset.single_le_sum
    (fun y _ => mul_nonneg (heatKernel_nonneg hK ht x y) (hf y).le) (Finset.mem_univ x))

theorem heatOp_abs_le {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {t : ℝ} (ht : 0 ≤ t) (f : V → ℝ) (x : V) :
    |heatOp K t f x| ≤ heatOp K t (fun y => |f y|) x := by
  unfold heatOp Matrix.mulVec dotProduct
  calc
    _ ≤ ∑ y, |MarkovMixing.heatKernel K t x y*f y| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (heatKernel_nonneg hK ht _ _)]

theorem heatOp_add_const {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (t : ℝ) (f : V → ℝ) (ε : ℝ) :
    heatOp K t (fun y => f y+ε) = fun x => heatOp K t f x+ε := by
  funext x
  simp only [heatOp, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, heatKernel_row_sum hK, one_mul]

theorem heatOp_mean {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (t : ℝ) (f : V → ℝ) :
    mean π (heatOp K t f) = mean π f := by
  simp only [mean, heatOp, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  simp only [← mul_assoc, ← Finset.sum_mul, heatKernel_stationary hπ]

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_HeatCalculus
-- End HeatCalculus

-- Begin Centering
section ModuleScope_Centering

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem mean_center {π : V → ℝ} (hπ : ∑ x, π x=1) (f : V → ℝ) :
    mean π (fun x => f x-mean π f)=0 := by rw [mean_sub,mean_const hπ,sub_self]

theorem dirichlet_center {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) (c : ℝ) :
    dirichlet K π (fun x => f x-c) (fun x => f x-c)=dirichlet K π f f := by
  have ha := dirichlet_square hK hπ (fun x => f x-c)
  have hb := dirichlet_square hK hπ f
  have hs : (∑ x, ∑ y, π x*K x y*((f x-c)-(f y-c))^2) =
      ∑ x, ∑ y, π x*K x y*(f x-f y)^2 := by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _; ring
  rw [hs] at ha; linarith

theorem squareMean_le_norm_sq {π : V → ℝ} (hπ : MarkovMixing.IsDist π) (f : V → ℝ) :
    squareMean π f ≤ ‖f‖^2 := by
  calc
    _ ≤ ∑ x, π x*‖f‖^2 := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hπ.1 x)
      have h := norm_le_pi_norm f x
      rw [Real.norm_eq_abs] at h
      nlinarith [abs_nonneg (f x),sq_abs (f x),norm_nonneg f]
    _ = _ := by rw [← Finset.sum_mul,hπ.2,one_mul]

theorem continuous_mean (π : V → ℝ) : Continuous (mean π) := by unfold mean; fun_prop

theorem continuous_dirichlet_square (K : Matrix V V ℝ) (π : V → ℝ) :
    Continuous (fun f : V → ℝ => dirichlet K π f f) := by
  simp only [dirichlet,Matrix.mulVec,dotProduct]
  fun_prop

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_Centering
-- End Centering

-- Begin DirichletKernel
section ModuleScope_DirichletKernel

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem constant_on_positive_powers {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    {f : V → ℝ} (hf : ∀ x y, 0<K x y → f x=f y) (n : ℕ) :
    ∀ x y, 0<(K^n) x y → f x=f y := by
  induction n with
  | zero =>
    intro x y h
    have : x=y := by by_contra hn; simp [hn] at h
    simp [this]
  | succ n ih =>
    intro x y h
    rw [pow_succ,Matrix.mul_apply] at h
    obtain ⟨z,_,hz⟩ := (Finset.sum_pos_iff_of_nonneg (fun z _ => mul_nonneg ((stochastic_pow hK n).1 x z) (hK.1 z y))).mp h
    have ha := (stochastic_pow hK n).1 x z
    have hb := hK.1 z y
    have ha' : 0<(K^n) x z := by nlinarith
    have hb' : 0<K z y := by nlinarith
    exact (ih x z ha').trans (hf z y hb')

theorem dirichlet_zero_constant {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (hirr : MarkovMixing.Irreducible K)
    {f : V → ℝ} (he : dirichlet K π f f=0) : ∀ x y, f x=f y := by
  have hs : (∑ x, ∑ y, π x*K x y*(f x-f y)^2)=0 := by
    rw [← dirichlet_square hK hπ f,he,mul_zero]
  have hn (x y : V) : 0≤π x*K x y*(f x-f y)^2 :=
    mul_nonneg (mul_nonneg (hpos x).le (hK.1 x y)) (sq_nonneg _)
  have hf (x y : V) (hxy : 0<K x y) : f x=f y := by
    have h1 := Finset.single_le_sum (fun z _ => hn x z) (Finset.mem_univ y)
    have h2 := Finset.single_le_sum
      (fun z _ => Finset.sum_nonneg (s := Finset.univ) fun w _ => hn z w) (Finset.mem_univ x)
    have hb := h1.trans h2
    rw [hs] at hb
    have hp := mul_pos (hpos x) hxy
    have : (f x-f y)^2=0 := by nlinarith [sq_nonneg (f x-f y)]
    nlinarith
  intro x y
  obtain ⟨n,hn⟩ := hirr x y
  exact constant_on_positive_powers hK hf n x y hn

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_DirichletKernel
-- End DirichletKernel

-- Begin GapSphere
section ModuleScope_GapSphere

open scoped BigOperators
open Set Metric
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

def centeredSphere (π : V → ℝ) : Set (V → ℝ) :=
  {f | mean π f=0} ∩ sphere 0 1

omit [DecidableEq V] in
theorem centeredSphere_compact (π : V → ℝ) : IsCompact (centeredSphere π) := by
  exact (isCompact_sphere (0 : V → ℝ) 1).inter_left
    (isClosed_eq (continuous_mean π) continuous_const)

omit [DecidableEq V] in
theorem normalize_mem_centeredSphere {π f : V → ℝ} (hf : mean π f=0) (hne : f≠0) :
    (fun x => ‖f‖⁻¹*f x) ∈ centeredSphere π := by
  refine ⟨?_,?_⟩
  · change mean π (fun x => ‖f‖⁻¹*f x)=0
    rw [mean_smul,hf,mul_zero]
  rw [mem_sphere_zero_iff_norm]
  change ‖‖f‖⁻¹ • f‖=1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

theorem centeredSphere_nonempty {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (x : V) (hx : π x<1) : (centeredSphere π).Nonempty := by
  let f : V → ℝ := fun y => (if y=x then 1 else 0)-π x
  have hmean : mean π (fun y => if y=x then 1 else 0)=π x := by simp [mean]
  have hf : mean π f=0 := by
    dsimp [f]; rw [mean_sub,mean_const hπ.2,hmean,sub_self]
  have hne : f≠0 := by
    intro h; have hh := congrFun h x
    simp only [f,ite_true,Pi.zero_apply] at hh
    linarith
  exact ⟨_,normalize_mem_centeredSphere hf hne⟩

theorem exists_positive_energy_min {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (hirr : MarkovMixing.Irreducible K)
    (x : V) (hx : π x<1) :
    ∃ δ : ℝ, 0<δ ∧ ∀ f ∈ centeredSphere π, δ≤dirichlet K π f f := by
  obtain ⟨f,hf,hmin⟩ := (centeredSphere_compact π).exists_isMinOn
    (centeredSphere_nonempty hπ.1 x hx) (continuous_dirichlet_square K π).continuousOn
  refine ⟨dirichlet K π f f,?_,hmin⟩
  have hn := dirichlet_nonneg hK hπ f
  by_contra h
  have he : dirichlet K π f f=0 := by linarith
  have hc := dirichlet_zero_constant hK hπ hpos hirr he
  have hfx : mean π f=f x := by
    have heq : f=(fun _ => f x) := funext (fun y => hc y x)
    rw [heq,mean_const hπ.1.2]
  have hx0 : f x=0 := by rw [← hfx]; exact hf.1
  have hf0 : f=0 := funext (fun y => (hc y x).trans hx0)
  have hs := hf.2
  rw [hf0,mem_sphere_zero_iff_norm,norm_zero] at hs
  norm_num at hs

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_GapSphere
-- End GapSphere

-- Begin GapPositive
section ModuleScope_GapPositive

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem energy_coercive {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    {δ : ℝ} (hδ : 0≤δ) (hb : ∀ f ∈ centeredSphere π, δ≤dirichlet K π f f)
    (f : V → ℝ) : δ*MarkovMixing.distVar π f ≤ dirichlet K π f f := by
  let g : V → ℝ := fun x => f x-mean π f
  have hg : mean π g=0 := mean_center hπ.1.2 f
  have he : dirichlet K π g g=dirichlet K π f f := dirichlet_center hK hπ f (mean π f)
  have hv : MarkovMixing.distVar π f=squareMean π g := by
    have hm : MarkovMixing.distExp π f=mean π f := by
      simp only [MarkovMixing.distExp,mean,mul_comm]
    simp only [MarkovMixing.distVar,hm,squareMean,g,mul_comm]
  rw [hv,← he]
  by_cases hz : g=0
  · rw [hz]
    simpa [squareMean] using (dirichlet_nonneg hK hπ (0 : V → ℝ))
  have hn : ‖g‖≠0 := norm_ne_zero_iff.mpr hz
  have hb' := hb _ (normalize_mem_centeredSphere hg hz)
  rw [dirichlet_smul] at hb'
  have hm := mul_le_mul_of_nonneg_right hb' (sq_nonneg ‖g‖)
  have hid : (‖g‖⁻¹)^2*dirichlet K π g g*‖g‖^2=dirichlet K π g g := by
    field_simp
  rw [hid] at hm
  exact (mul_le_mul_of_nonneg_left (squareMean_le_norm_sq hπ.1 g) hδ).trans hm

theorem gap_pos {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (hirr : MarkovMixing.Irreducible K)
    (x : V) (hx : π x<1) : 0<gap K π := by
  obtain ⟨δ,hδ,hb⟩ := exists_positive_energy_min hK hπ hpos hirr x hx
  have hne : {r : ℝ | ∃ f : V → ℝ, MarkovMixing.distVar π f≠0 ∧
      r=dirichlet K π f f/MarkovMixing.distVar π f}.Nonempty :=
    ⟨_,pointIndicator x,(variance_pointIndicator_pos hπ.1 x (hpos x) hx).ne',rfl⟩
  apply hδ.trans_le
  apply le_csInf hne
  rintro r ⟨f,hf,rfl⟩
  have hv : 0<MarkovMixing.distVar π f := by
    have hn : 0≤MarkovMixing.distVar π f :=
      Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hpos y).le
    exact lt_of_le_of_ne hn (Ne.symm hf)
  exact (le_div_iff₀ hv).mpr (energy_coercive hK hπ hδ.le hb f)

omit [DecidableEq V] in
theorem gap_mul_variance_le {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) : gap K π*MarkovMixing.distVar π f≤dirichlet K π f f := by
  by_cases hv : MarkovMixing.distVar π f=0
  · rw [hv,mul_zero]; exact dirichlet_nonneg hK hπ f
  have hn : 0≤MarkovMixing.distVar π f :=
    Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hπ.1.1 y)
  have hp := lt_of_le_of_ne hn (Ne.symm hv)
  apply (le_div_iff₀ hp).mp
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro r ⟨g,_,rfl⟩
    exact div_nonneg (dirichlet_nonneg hK hπ g)
      (Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hπ.1.1 y))
  · exact ⟨f,hv,rfl⟩

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_GapPositive
-- End GapPositive

-- Begin LpNormBasic
section ModuleScope_LpNormBasic

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem lpNorm_nonneg {π : V → ℝ} (hπ : ∀ x,0≤π x) (p : ℝ) (f : V → ℝ) :
    0≤lpNorm π p f := by
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg fun x _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ x)

theorem lpNorm_point {π : V → ℝ} (hπ : ∀ x,0<π x) {q : ℝ} (hq : 0<q)
    (f : V → ℝ) (x : V) : |f x| ≤ (π x)^(-(1/q))*lpNorm π q f := by
  have ht : |f x|^q*π x ≤ ∑ y, |f y|^q*π y :=
    Finset.single_le_sum
      (fun y _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ y).le) (Finset.mem_univ x)
  have h := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ x).le)
    ht (by positivity : 0≤1/q)
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (hπ x).le,
    ← Real.rpow_mul (abs_nonneg _)] at h
  have hq' : q*(1/q)=1 := by field_simp
  rw [hq',Real.rpow_one] at h
  change |f x| *(π x)^(1/q) ≤ lpNorm π q f at h
  have hp := Real.rpow_pos_of_pos (hπ x) (1/q)
  have hh := (le_div_iff₀ hp).mpr h
  simpa only [Real.rpow_neg (hπ x).le,div_eq_mul_inv,mul_comm] using hh

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_LpNormBasic
-- End LpNormBasic

-- Begin HeatEnergy
section ModuleScope_HeatEnergy

open scoped BigOperators
open Set
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem squareMean_heat_deriv (K : Matrix V V ℝ) (π f : V → ℝ) (t : ℝ) :
    HasDerivAt (fun s => squareMean π (heatOp K s f))
      (-2*dirichlet K π (heatOp K t f) (heatOp K t f)) t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun x _ =>
    ((heatOp_hasDerivAt K f t x).pow 2).const_mul (π x))
  apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
    simp only [squareMean,Finset.sum_apply,Pi.pow_apply])).congr_deriv
  simp only [dirichlet,Finset.mul_sum,Nat.cast_ofNat]
  apply Finset.sum_congr rfl; intro x _; ring

theorem squareMean_heat_decay {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) (hf : mean π f=0) {t : ℝ} (ht : 0≤t) :
    squareMean π (heatOp K t f) ≤ Real.exp (-2*gap K π*t)*squareMean π f := by
  let S : ℝ → ℝ := fun s => squareMean π (heatOp K s f)
  let F : ℝ → ℝ := fun s => Real.exp (2*gap K π*s)*S s
  have hd (s : ℝ) : HasDerivAt F
      (Real.exp (2*gap K π*s)*(2*gap K π*S s -
        2*dirichlet K π (heatOp K s f) (heatOp K s f))) s := by
    have h := (((hasDerivAt_id s).const_mul (2*gap K π)).exp).mul (squareMean_heat_deriv K π f s)
    apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)).congr_deriv
    dsimp only [S,id_eq]
    ring
  have hb (s : ℝ) : gap K π*S s ≤ dirichlet K π (heatOp K s f) (heatOp K s f) := by
    have h := gap_mul_variance_le hK hπ (heatOp K s f)
    rw [variance_eq_squareMean hπ.1.2,heatOp_mean hπ,hf,zero_pow (by norm_num : 2≠0),sub_zero] at h
    exact h
  have hm : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro s _;exact (hd s).continuousAt.continuousWithinAt
    · intro s _;exact (hd s).differentiableAt.differentiableWithinAt
    · intro s _;rw [(hd s).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hb s])
  have hh := hm (show (0:ℝ)∈Ici 0 from by simp) ht ht
  have hz : F 0=squareMean π f := by simp [F,S,heatOp_zero]
  rw [hz] at hh
  have hm' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*gap K π*t)).le
  have he : Real.exp (-2*gap K π*t)*F t=S t := by
    dsimp only [F];rw [← mul_assoc,← Real.exp_add]
    ring_nf; simp
  rw [he] at hm'
  exact hm'

theorem heat_l2_decay {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) (hf : mean π f=0) {t : ℝ} (ht : 0≤t) :
    lpNorm π 2 (heatOp K t f) ≤ Real.exp (-gap K π*t)*lpNorm π 2 f := by
  have h := squareMean_heat_decay hK hπ f hf ht
  rw [← lpNorm_two_sq hπ.1.1,← lpNorm_two_sq hπ.1.1] at h
  have he : (Real.exp (-gap K π*t))^2=Real.exp (-2*gap K π*t) := by
    rw [← Real.exp_nat_mul];congr 1;ring
  have hp := mul_nonneg (Real.exp_pos (-gap K π*t)).le (lpNorm_nonneg hπ.1.1 2 f)
  nlinarith [he]

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_HeatEnergy
-- End HeatEnergy

-- Begin DensityRow
section ModuleScope_DensityRow

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem density_mean {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hpos : ∀ x, 0<π x) (t : ℝ) (x : V) :
    mean π (density K π t x)=1 := by
  unfold mean density
  have he : (∑ y, π y*(MarkovMixing.heatKernel K t x y/π y)) =
      ∑ y, MarkovMixing.heatKernel K t x y := by
    apply Finset.sum_congr rfl;intro y _;field_simp [(hpos y).ne']
  rw [he,heatKernel_row_sum hK]

theorem density_error_mean {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (t : ℝ) (x : V) :
    mean π (fun y => density K π t x y-1)=0 := by
  rw [mean_sub,mean_const hπ.1.2,density_mean hK hpos,sub_self]

theorem density_error_energy {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (t : ℝ) (x : V) :
    squareMean π (fun y => density K π t x y-1) =
      heatOp K t (fun y => density K π t x y-1) x := by
  let f : V → ℝ := fun y => density K π t x y-1
  have hm : mean π f=0 := density_error_mean hK hπ hpos t x
  change squareMean π f = heatOp K t f x
  calc
    _ = squareMean π f+mean π f := by rw [hm,add_zero]
    _ = _ := by
      simp only [squareMean,mean,heatOp,Matrix.mulVec,dotProduct,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro y _
      dsimp only [f,density]
      field_simp [(hpos y).ne']
      ring

theorem row_norm_bound {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) {s t q : ℝ} (ht : 0≤t) (hq : 0<q)
    (hhyper : ∀ g : V → ℝ, lpNorm π q (heatOp K s g) ≤ lpNorm π 2 g) (x : V) :
    lpNorm π 2 (fun y => density K π (s+t) x y-1) ≤
      (π x)^(-(1/q))*Real.exp (-gap K π*t) := by
  let f : V → ℝ := fun y => density K π (s+t) x y-1
  have hm : mean π f=0 := density_error_mean hK hπ hpos (s+t) x
  have he : (lpNorm π 2 f)^2=heatOp K (s+t) f x := by
    rw [lpNorm_two_sq hπ.1.1];exact density_error_energy hK hπ hpos (s+t) x
  have hpoint := lpNorm_point hpos hq (heatOp K s (heatOp K t f)) x
  have hh := hhyper (heatOp K t f)
  have hd := heat_l2_decay hK hπ f hm ht
  have hp : 0≤(π x)^(-(1/q)) := (Real.rpow_pos_of_pos (hpos x) _).le
  have hn : (lpNorm π 2 f)^2 ≤
      ((π x)^(-(1/q))*Real.exp (-gap K π*t))*lpNorm π 2 f := by
    rw [he,heatOp_add]
    calc
      _ ≤ |heatOp K s (heatOp K t f) x| := le_abs_self _
      _ ≤ _ := hpoint
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hp
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd hp
  have ha := mul_nonneg hp (Real.exp_pos (-gap K π*t)).le
  have hf := lpNorm_nonneg hπ.1.1 2 f
  change lpNorm π 2 f ≤ _
  nlinarith

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_DensityRow
-- End DensityRow

-- Begin MixingTimes
section ModuleScope_MixingTimes

namespace LogSobolevMC.ChiSquare.Proof

theorem mixing_time_nonneg {p α r : ℝ} (hp : 0<p) (hp' : p≤Real.exp (-1))
    (ha : 0<α) (hr : 0<r) :
    0≤(r*α)⁻¹*Real.log (Real.log (1/p)) := by
  have h := Real.log_le_log hp hp'
  rw [Real.log_exp] at h
  have hz : 1≤Real.log (1/p) := by rw [one_div,Real.log_inv];linarith
  exact mul_nonneg (inv_nonneg.mpr (mul_pos hr ha).le) (Real.log_nonneg hz)

theorem mixing_factor_bound {p α ell r c : ℝ} (hp : 0<p) (hp' : p≤Real.exp (-1))
    (ha : 0<α) (hl : 0<ell) (hr : 0<r) :
    p^(-(1/(1+Real.exp (r*α*((r*α)⁻¹*Real.log (Real.log (1/p)))))))*
      Real.exp (-ell*(c/ell)) ≤ Real.exp (1-c) := by
  have h := Real.log_le_log hp hp'
  rw [Real.log_exp] at h
  have hz : 1≤Real.log (1/p) := by rw [one_div,Real.log_inv];linarith
  have hzpos : 0<Real.log (1/p) := lt_of_lt_of_le zero_lt_one hz
  have hs : r*α*((r*α)⁻¹*Real.log (Real.log (1/p)))=Real.log (Real.log (1/p)) := by
    rw [← mul_assoc,mul_inv_cancel₀ (mul_pos hr ha).ne',one_mul]
  rw [hs,Real.exp_log hzpos]
  have ht : -ell*(c/ell) = -c := by field_simp
  rw [ht,Real.rpow_def_of_pos hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq : 0<1+Real.log (1/p) := by linarith
  have hh : Real.log (1/p)/(1+Real.log (1/p))≤1 := by
    apply (div_le_one hq).mpr;linarith
  have he : Real.log p * -(1/(1+Real.log (1/p))) =
      Real.log (1/p)/(1+Real.log (1/p)) := by
    simp only [one_div,Real.log_inv];ring
  rw [he];linarith

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_MixingTimes
-- End MixingTimes

-- Begin MixingFromHypercontractivity
section ModuleScope_MixingFromHypercontractivity

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mixing_from_hypercontractivity {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0<π x) (ha : 0<logSobolev K π) (hl : 0<gap K π)
    (r : ℝ) (hr : 0<r)
    (hhyper : ∀ s : ℝ, 0 ≤ s → ∀ f : V → ℝ,
      lpNorm π (1+Real.exp (r*logSobolev K π*s)) (heatOp K s f) ≤ lpNorm π 2 f)
    (x : V) (hx : π x≤Real.exp (-1)) (c : ℝ) (hc : 0<c) :
    lpNorm π 2 (fun y => density K π
      ((r*logSobolev K π)⁻¹*Real.log (Real.log (1/π x))+c/gap K π) x y-1) ≤
      Real.exp (1-c) := by
  let s := (r*logSobolev K π)⁻¹*Real.log (Real.log (1/π x))
  have hs : 0 ≤ s := mixing_time_nonneg (hpos x) hx ha hr
  have ht : 0≤c/gap K π := (div_pos hc hl).le
  have hq : 0<1+Real.exp (r*logSobolev K π*s) := by positivity
  have h := row_norm_bound hK hπ hpos (s := s) ht hq (hhyper s hs) x
  exact h.trans (mixing_factor_bound (hpos x) hx ha hl hr)

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_MixingFromHypercontractivity
-- End MixingFromHypercontractivity

-- Begin PositiveNorm
section ModuleScope_PositiveNorm

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

noncomputable def positiveMoment (π : V → ℝ) (p : ℝ) (f : V → ℝ) : ℝ := ∑x,f x^p*π x
noncomputable def positiveNorm (π : V → ℝ) (p : ℝ) (f : V → ℝ) : ℝ :=
  Real.exp (Real.log (positiveMoment π p f)/p)

lemma positiveMoment_pos [Nonempty V] {π f : V → ℝ} {p : ℝ}
    (hπ : ∀x,0<π x) (hf : ∀x,0<f x) : 0<positiveMoment π p f := by
  apply Finset.sum_pos
  · intro x _
    exact mul_pos (Real.rpow_pos_of_pos (hf x) _) (hπ x)
  · exact Finset.univ_nonempty

lemma positiveNorm_eq_lpNorm [Nonempty V] {π f : V → ℝ} {p : ℝ}
    (hπ : ∀x,0<π x) (hf : ∀x,0<f x) : positiveNorm π p f=lpNorm π p f := by
  unfold positiveNorm lpNorm
  simp_rw [abs_of_pos (hf _)]
  change Real.exp (Real.log (positiveMoment π p f)/p) = (positiveMoment π p f)^(1/p)
  rw [Real.rpow_def_of_pos (positiveMoment_pos hπ hf)]
  congr 1
  dsimp [positiveMoment]
  ring

lemma positiveMoment_deriv {π : V → ℝ} {u : ℝ → V → ℝ} {p : ℝ → ℝ}
    {t pd : ℝ} {ud : V → ℝ} (hu : ∀x,HasDerivAt (fun s=>u s x) (ud x) t)
    (hp : HasDerivAt p pd t) (hpos : ∀x,0<u t x) :
    HasDerivAt (fun s=>positiveMoment π (p s) (u s))
      (p t*(∑x,ud x*u t x^(p t-1)*π x)+pd*(∑x,u t x^(p t)*Real.log (u t x)*π x)) t := by
  have hd := HasDerivAt.sum (u:=Finset.univ) (fun x _ => ((hu x).rpow hp (hpos x)).mul_const (π x))
  convert! hd using 1
  · funext s
    simp [positiveMoment]
  · simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring

lemma positiveNorm_deriv {π : V → ℝ} {u : ℝ → V → ℝ} {p : ℝ → ℝ}
    {t pd gd : ℝ} (hG : HasDerivAt (fun s=>positiveMoment π (p s) (u s)) gd t)
    (hp : HasDerivAt p pd t) (hpos : 0<positiveMoment π (p t) (u t)) (hp0 : p t≠0) :
    HasDerivAt (fun s=>positiveNorm π (p s) (u s))
      (positiveNorm π (p t) (u t) *
        (gd / positiveMoment π (p t) (u t) / p t - pd * Real.log (positiveMoment π (p t) (u t))/(p t)^2)) t := by
  have hd := ((hG.log hpos.ne').div hp hp0).exp
  convert! hd using 1
  dsimp [positiveNorm]
  field_simp [hp0,hpos.ne']

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_PositiveNorm
-- End PositiveNorm

-- Begin PositiveEntropy
section ModuleScope_PositiveEntropy

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [Nonempty V]

lemma lpNorm_rpow_positive {π g : V → ℝ} (hπ : ∀x,0<π x) (hg : ∀x,0<g x)
    {p : ℝ} (hp : p≠0) : (lpNorm π p g)^p=positiveMoment π p g := by
  unfold lpNorm
  simp_rw [abs_of_pos (hg _)]
  change (positiveMoment π p g ^ (1/p))^p=positiveMoment π p g
  rw [←Real.rpow_mul (positiveMoment_pos hπ hg).le]
  simp [hp]

lemma entLp_positive_formula {π g : V → ℝ} (hπ : ∀x,0<π x) (hg : ∀x,0<g x)
    {p : ℝ} (hp : p≠0) : entLp π p g =
      p*(∑x,g x^p*Real.log (g x)*π x) - positiveMoment π p g*Real.log (positiveMoment π p g) := by
  unfold entLp
  rw [lpNorm_rpow_positive hπ hg hp]
  simp_rw [abs_of_pos (hg _),Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (hg _) _))
    (positiveMoment_pos hπ hg).ne',Real.log_rpow (hg _)]
  simp only [positiveMoment,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma ent_power_identity {π g : V → ℝ} (hπ : ∀x,0<π x) (hg : ∀x,0<g x)
    {p : ℝ} (hp : p≠0) : entL π (fun x=>g x^(p/2))=entLp π p g := by
  have hg' : ∀x,0<g x^(p/2) := fun x=>Real.rpow_pos_of_pos (hg x) _
  have he : ∀x,(g x^(p/2))^(2:ℝ)=g x^p := by
    intro x
    rw [←Real.rpow_mul (hg x).le]
    congr 1
    ring
  unfold entL entLp
  rw [lpNorm_rpow_positive hπ hg' (by norm_num : (2:ℝ)≠0),lpNorm_rpow_positive hπ hg hp]
  simp_rw [abs_of_pos (hg' _),abs_of_pos (hg _),he]
  simp only [positiveMoment,he]

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_PositiveEntropy
-- End PositiveEntropy

-- Begin NormEntropyDerivative
section ModuleScope_NormEntropyDerivative

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [Nonempty V]

lemma positiveNorm_deriv_entropy {π : V → ℝ} (hπ : ∀x,0<π x)
    {u : ℝ → V → ℝ} {p : ℝ → ℝ} {t pd D : ℝ} {ud : V → ℝ}
    (hu : ∀x,HasDerivAt (fun s=>u s x) (ud x) t) (hp : HasDerivAt p pd t)
    (hpos : ∀x,0<u t x) (hp0 : p t≠0)
    (hD : (∑x,ud x*u t x^(p t-1)*π x) = -D) :
    HasDerivAt (fun s=>positiveNorm π (p s) (u s))
      (positiveNorm π (p t) (u t)/positiveMoment π (p t) (u t) *
        (pd/(p t)^2*entLp π (p t) (u t)-D)) t := by
  have hG := positiveMoment_deriv (π:=π) hu hp hpos
  have hd := positiveNorm_deriv hG hp (positiveMoment_pos hπ hpos) hp0
  rw [hD] at hd
  convert hd using 1
  rw [entLp_positive_formula hπ hpos hp0]
  field_simp [hp0,(positiveMoment_pos hπ hpos).ne']
  ring

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_NormEntropyDerivative
-- End NormEntropyDerivative

-- Begin NormMonotonicity
section ModuleScope_NormMonotonicity

open Set
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [Nonempty V]

lemma positiveNorm_antitone {π : V → ℝ} (hπ : ∀x,0<π x)
    (u : ℝ → V → ℝ) (p pd D : ℝ → ℝ) (ud : ℝ → V → ℝ)
    (hu : ∀t,0≤t→∀x,HasDerivAt (fun s=>u s x) (ud t x) t)
    (hp : ∀t,0≤t→HasDerivAt p (pd t) t)
    (hpos : ∀t,0≤t→∀x,0<u t x) (hp0 : ∀t,0≤t→p t≠0)
    (hD : ∀t,0≤t→(∑x,ud t x*u t x^(p t-1)*π x) = -D t)
    (hbound : ∀t,0≤t→pd t/(p t)^2*entLp π (p t) (u t)≤D t) :
    AntitoneOn (fun t=>positiveNorm π (p t) (u t)) (Ici 0) := by
  have hd (t : ℝ) (ht : 0≤t) := positiveNorm_deriv_entropy hπ (hu t ht) (hp t ht)
    (hpos t ht) (hp0 t ht) (hD t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0≤t := interior_subset ht
    rw [(hd t ht0).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact div_nonneg (Real.exp_pos _).le (positiveMoment_pos hπ (hpos t ht0)).le
    · exact sub_nonpos.mpr (hbound t ht0)

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_NormMonotonicity
-- End NormMonotonicity

-- Begin HeatNormFlow
section ModuleScope_HeatNormFlow

open scoped BigOperators
open Set
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma heat_hypercontractive_positive {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀x,0<π x) {A : ℝ} (hA : 0≤A)
    (hbound : ∀ g : V → ℝ,(∀x,0<g x)→∀ p : ℝ,2≤ p→
      A*(p-1)/p^2*entLp π p g ≤ dirichlet K π g (fun x=>g x^(p-1)))
    (f : V → ℝ) (hf : ∀x,0<f x) {s : ℝ} (hs : 0≤ s) :
    lpNorm π (1+Real.exp (A*s)) (heatOp K s f) ≤ lpNorm π 2 f := by
  let p : ℝ → ℝ := fun t=>1+Real.exp (A*t)
  let pd : ℝ → ℝ := fun t=>A*Real.exp (A*t)
  let u : ℝ → V → ℝ := fun t=>heatOp K t f
  let ud : ℝ → V → ℝ := fun t x=>K.mulVec (u t) x-u t x
  let D : ℝ → ℝ := fun t=>dirichlet K π (u t) (fun x=>u t x^(p t-1))
  have hp2 (t : ℝ) (ht : 0≤t) : 2≤ p t := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hA ht)
    dsimp [p]
    linarith
  have hu (t : ℝ) (ht : 0≤t) (x : V) : 0<u t x := heatOp_pos hK ht hf x
  have hpder (t : ℝ) : HasDerivAt p (pd t) t := by
    convert! ((hasDerivAt_id t).const_mul A).exp.const_add 1 using 1
    simp [pd,mul_comm]
  have hanti : AntitoneOn (fun t=>positiveNorm π (p t) (u t)) (Ici 0) := by
    apply positiveNorm_antitone hπ u p pd D ud
    · intro t _ x
      exact heatOp_hasDerivAt K f t x
    · intro t _
      exact hpder t
    · exact hu
    · intro t ht
      linarith [hp2 t ht]
    · intro t _
      dsimp [ud,D,dirichlet]
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · intro t ht
      simpa only [pd,p,D,add_sub_cancel_left] using hbound (u t) (hu t ht) (p t) (hp2 t ht)
  have h := hanti (show 0∈Ici (0:ℝ) by simp) hs hs
  change positiveNorm π (p s) (u s) ≤ positiveNorm π (p 0) (u 0) at h
  rw [positiveNorm_eq_lpNorm hπ (hu s hs),positiveNorm_eq_lpNorm hπ (hu 0 (by simp))] at h
  simpa [p,u,heatOp_zero, show (1:ℝ)+1=2 by norm_num] using h

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_HeatNormFlow
-- End HeatNormFlow

-- Begin LpContinuity
section ModuleScope_LpContinuity

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

lemma continuous_lpNorm (π : V → ℝ) {p : ℝ} (hp : 0≤p) :
    Continuous (fun f : V → ℝ => lpNorm π p f) := by
  unfold lpNorm
  apply (Real.continuous_rpow_const (div_nonneg zero_le_one hp)).comp
  apply continuous_finsetSum
  intro x _
  exact (((continuous_apply x).abs).rpow_const (fun _=>Or.inr hp)).mul continuous_const

lemma lpNorm_mono_abs {π : V → ℝ} (hπ : ∀x,0≤π x) {p : ℝ} (hp : 0≤p)
    {f g : V → ℝ} (h : ∀x,|f x|≤|g x|) : lpNorm π p f≤lpNorm π p g := by
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg (fun x _=>mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ x))
  · exact Finset.sum_le_sum (fun x _=>mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (h x) hp) (hπ x))
  · exact div_nonneg zero_le_one hp

lemma lpNorm_abs (π f : V → ℝ) (p : ℝ) : lpNorm π p (fun x=>|f x|)=lpNorm π p f := by
  simp only [lpNorm,abs_abs]

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_LpContinuity
-- End LpContinuity

-- Begin HeatNormExtension
section ModuleScope_HeatNormExtension

open Filter
open scoped Topology
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma heat_hypercontractive_epsilon {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀ x, 0 < π x) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ g : V → ℝ, (∀ x, 0 < g x) → ∀ p : ℝ, 2 ≤ p →
      A*(p-1)/p^2*entLp π p g ≤ dirichlet K π g (fun x => g x^(p-1)))
    (f : V → ℝ) {s : ℝ} (hs : 0 ≤ s) (ε : ℝ) (he : 0 < ε) :
    lpNorm π (1+Real.exp (A*s)) (heatOp K s f) ≤ lpNorm π 2 (fun x => |f x|+ε) := by
  have hq : 0 ≤ 1+Real.exp (A*s) := by positivity
  have hp : ∀ x, 0 < |f x|+ε := fun x => add_pos_of_nonneg_of_pos (abs_nonneg _) he
  apply le_trans _ (heat_hypercontractive_positive hK hπ hA hbound _ hp hs)
  apply lpNorm_mono_abs (fun x => (hπ x).le) hq
  intro x
  rw [abs_of_pos (heatOp_pos hK hs hp x)]
  have hc := congrFun (heatOp_add_const hK s (fun y => |f y|) ε) x
  rw [hc]
  exact (heatOp_abs_le hK hs f x).trans (le_add_of_nonneg_right he.le)

lemma heat_hypercontractive {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀x,0<π x) {A : ℝ} (hA : 0≤A)
    (hbound : ∀ g : V → ℝ,(∀x,0<g x)→∀ p : ℝ,2≤ p→
      A*(p-1)/p^2*entLp π p g ≤ dirichlet K π g (fun x=>g x^(p-1)))
    (f : V → ℝ) {s : ℝ} (hs : 0≤ s) :
    lpNorm π (1+Real.exp (A*s)) (heatOp K s f) ≤ lpNorm π 2 f := by
  have hseq : Tendsto (fun n : ℕ => fun x : V => |f x|+1/((n:ℝ)+1)) atTop (𝓝 (fun x : V => |f x|)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => |f x|+1/((n:ℝ)+1)) atTop (𝓝 (|f x|+0)))
  have hlim : Tendsto (fun n : ℕ => lpNorm π 2 (fun x => |f x|+1/((n:ℝ)+1)))
      atTop (𝓝 (lpNorm π 2 (fun x => |f x|))) :=
    ((continuous_lpNorm π (by norm_num : (0:ℝ) ≤ 2)).tendsto (fun x => |f x|)).comp hseq
  have hle : lpNorm π (1+Real.exp (A*s)) (heatOp K s f) ≤ lpNorm π 2 (fun x => |f x|) := by
    apply ge_of_tendsto hlim
    exact Eventually.of_forall (fun n => heat_hypercontractive_epsilon hK hπ hA hbound f hs
      (1/((n:ℝ)+1)) (by positivity))
  simpa only [lpNorm_abs] using hle

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_HeatNormExtension
-- End HeatNormExtension

-- Begin ScalarPower
section ModuleScope_ScalarPower

open MeasureTheory Set
namespace LogSobolevMC.ChiSquare.Proof

lemma interval_square_bound {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, g x)^2 ≤ (b-a)*(∫ x in a..b, (g x)^2) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab.le
  have hi2 : IntervalIntegrable (fun x => (g x)^2) volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc hab.le
  let c := (∫ x in a..b, g x)/(b-a)
  have hn := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hab.le
    (fun x : ℝ => sq_nonneg (g x-c))
  have he : (∫ x in a..b, (g x-c)^2) =
      (∫ x in a..b, (g x)^2) - 2*c*(∫ x in a..b,g x) + (b-a)*c^2 := by
    simp_rw [show ∀x,(g x-c)^2=(g x)^2-(2*c)*g x+c^2 by intro x; ring]
    rw [intervalIntegral.integral_add (hi2.sub (hi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hi2 (hi.const_mul _),intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    rfl
  rw [he] at hn
  have hc : c*(b-a)=(∫ x in a..b,g x) := by
    dsimp [c];field_simp
  nlinarith [mul_nonneg hn (sub_pos.mpr hab).le]

lemma rpow_tangent {a b r : ℝ} (ha : 0<a) (hb : 0<b) (hr : 1≤r) :
    b^r + r*b^(r-1)*(a-b) ≤ a^r := by
  have h := one_add_mul_self_le_rpow_one_add
    (s:=a/b-1) (p:=r) (by have := div_pos ha hb; linarith) hr
  rw [add_sub_cancel] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hb.le r)
  rw [Real.div_rpow ha.le hb.le] at hm
  have hp : b^r/b=b^(r-1) := by rw [Real.rpow_sub hb];simp
  have hbpow : b^r≠0 := ne_of_gt (Real.rpow_pos_of_pos hb r)
  field_simp at hm
  rw [←hp]
  field_simp
  nlinarith

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_ScalarPower
-- End ScalarPower

-- Begin ScalarGeneral
section ModuleScope_ScalarGeneral

namespace LogSobolevMC.ChiSquare.Proof

lemma general_power_scalar {a b p : ℝ} (ha : 0<a) (hb : 0<b) (hp : 2≤p) :
    (2/p)*(b^(p/2)-a^(p/2))*b^(p/2) ≤ (b-a)*b^(p-1) := by
  have h := rpow_tangent ha hb (by linarith : 1≤p/2)
  have hh := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hb.le (p/2))
  have he : b^(p/2-1)*b^(p/2)=b^(p-1) := by
    rw [←Real.rpow_add hb]
    congr 1
    ring
  rw [show (b^(p/2)+p/2*b^(p/2-1)*(a-b))*b^(p/2) =
    b^(p/2)*b^(p/2)+(p/2)*(a-b)*(b^(p/2-1)*b^(p/2)) by ring,he] at hh
  have hh' : (b^(p/2)-a^(p/2))*b^(p/2) ≤ (p/2)*(b-a)*b^(p-1) := by
    nlinarith only [hh]
  have hp0 : 0<p := by linarith
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (div_le_iff₀ hp0).mpr
  nlinarith

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_ScalarGeneral
-- End ScalarGeneral

-- Begin ScalarReversible
section ModuleScope_ScalarReversible

open MeasureTheory Set
namespace LogSobolevMC.ChiSquare.Proof

lemma reversible_power_scalar_ordered {a b p : ℝ} (ha : 0<a) (hab : a≤b) (hp : 2≤p) :
    (4*(p-1)/p^2)*(b^(p/2)-a^(p/2))^2 ≤ (b-a)*(b^(p-1)-a^(p-1)) := by
  have hb : 0<b := lt_of_lt_of_le ha hab
  have hhalf : 0<p/2 := by linarith
  have hm : 0<p-1 := by linarith
  have hcont : ContinuousOn (fun x : ℝ => x^(p/2-1)) (Icc a b) := by
    apply continuousOn_id.rpow_const
    intro x hx
    exact Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1))
  have hcs := interval_square_bound hab (fun x => x^(p/2-1)) hcont
  have hsq : (∫ x in a..b, (x^(p/2-1))^2) = ∫ x in a..b,x^(p-2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0≤x := le_trans ha.le ((by simpa only [uIcc_of_le hab] using hx : x ∈ Icc a b).1)
    change (x^(p/2-1))^2=x^(p-2)
    rw [←Real.rpow_natCast,←Real.rpow_mul hx0]
    congr 1
    ring
  rw [hsq,integral_rpow (Or.inl (by linarith : -1<p/2-1)),
    integral_rpow (Or.inl (by linarith : -1<p-2))] at hcs
  have h1 : p/2-1+1=p/2 := by ring
  have h2 : p-2+1=p-1 := by ring
  rw [h1,h2,div_pow,←mul_div_assoc] at hcs
  have hh := (div_le_div_iff₀ (sq_pos_of_pos hhalf) hm).mp hcs
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0<p))).mpr
  nlinarith

lemma reversible_power_scalar {a b p : ℝ} (ha : 0<a) (hb : 0<b) (hp : 2≤p) :
    (4*(p-1)/p^2)*(a^(p/2)-b^(p/2))^2 ≤ (a-b)*(a^(p-1)-b^(p-1)) := by
  rcases le_total a b with hab|hba
  · have h := reversible_power_scalar_ordered ha hab hp
    nlinarith
  · exact reversible_power_scalar_ordered hb hba hp

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_ScalarReversible
-- End ScalarReversible

-- Begin DirichletPowers
section ModuleScope_DirichletPowers

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

lemma dirichlet_pair {K : Matrix V V ℝ} (hK : MarkovMixing.IsStochastic K)
    (π f g : V → ℝ) :
    dirichlet K π f g = ∑x,∑y,π x*K x y*(f x-f y)*g x := by
  unfold dirichlet
  apply Finset.sum_congr rfl
  intro x _
  have hr : ∑y,π x*K x y*f x*g x = f x*g x*π x := by
    calc
      _ = (f x*g x*π x)*(∑y,K x y) := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro y _;ring
      _ = _ := by rw [hK.2,mul_one]
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib]
  rw [hr]
  simp only [Matrix.mulVec,dotProduct,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma dirichlet_pair_reversible {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hrev : MarkovMixing.DetailedBalance K π)
    (f g : V → ℝ) :
    2*dirichlet K π f g = ∑x,∑y,π x*K x y*(f x-f y)*(g x-g y) := by
  have hs : (∑x,∑y,π x*K x y*(f x-f y)*g y) = -dirichlet K π f g := by
    rw [dirichlet_pair hK,Finset.sum_comm]
    simp only [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hrev y x]
    ring
  have he : (∑x,∑y,π x*K x y*(f x-f y)*(g x-g y)) =
      (∑x,∑y,π x*K x y*(f x-f y)*g x) - (∑x,∑y,π x*K x y*(f x-f y)*g y) := by
    simp only [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro x _
    apply Finset.sum_congr rfl;intro y _;ring
  rw [he,←dirichlet_pair hK,hs]
  ring

lemma dirichlet_power_general {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀x,0≤π x)
    (g : V → ℝ) (hg : ∀x,0<g x) {p : ℝ} (hp : 2≤p) :
    (2/p)*dirichlet K π (fun x=>g x^(p/2)) (fun x=>g x^(p/2)) ≤
      dirichlet K π g (fun x=>g x^(p-1)) := by
  rw [dirichlet_pair hK,dirichlet_pair hK]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  have h := mul_le_mul_of_nonneg_left (general_power_scalar (hg y) (hg x) hp)
    (mul_nonneg (hπ x) (hK.1 x y))
  nlinarith only [h]

lemma dirichlet_power_reversible {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : ∀x,0≤π x)
    (hrev : MarkovMixing.DetailedBalance K π)
    (g : V → ℝ) (hg : ∀x,0<g x) {p : ℝ} (hp : 2≤p) :
    (4*(p-1)/p^2)*dirichlet K π (fun x=>g x^(p/2)) (fun x=>g x^(p/2)) ≤
      dirichlet K π g (fun x=>g x^(p-1)) := by
  have hsum : (4*(p-1)/p^2)*(∑x,∑y,π x*K x y*(g x^(p/2)-g y^(p/2))^2) ≤
      ∑x,∑y,π x*K x y*(g x-g y)*(g x^(p-1)-g y^(p-1)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    have h := mul_le_mul_of_nonneg_left (reversible_power_scalar (hg x) (hg y) hp)
      (mul_nonneg (hπ x) (hK.1 x y))
    nlinarith only [h]
  simp only [sq,←mul_assoc] at hsum
  rw [←dirichlet_pair_reversible hK hrev,←dirichlet_pair_reversible hK hrev] at hsum
  simp only [sq] at ⊢
  nlinarith only [hsum]

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_DirichletPowers
-- End DirichletPowers

-- Begin LogSobolevInf
section ModuleScope_LogSobolevInf

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem logSobolev_nonneg {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0 < π x) : 0 ≤ logSobolev K π := by
  apply Real.sInf_nonneg
  rintro r ⟨f,_,rfl⟩
  exact div_nonneg (dirichlet_nonneg hK hπ f) (entL_nonneg hπ hpos f)

theorem logSobolev_mul_entL_le {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀ x, 0 < π x) (f : V → ℝ) :
    logSobolev K π * entL π f ≤ dirichlet K π f f := by
  by_cases he : entL π f=0
  · rw [he,mul_zero]; exact dirichlet_nonneg hK hπ f
  have hepos := lt_of_le_of_ne (entL_nonneg hπ hpos f) (Ne.symm he)
  have hb : BddBelow {r : ℝ | ∃ g : V → ℝ, entL π g ≠ 0 ∧
      r=dirichlet K π g g/entL π g} := by
    refine ⟨0,?_⟩
    rintro r ⟨g,_,rfl⟩
    exact div_nonneg (dirichlet_nonneg hK hπ g) (entL_nonneg hπ hpos g)
  exact (le_div_iff₀ hepos).mp (csInf_le hb ⟨f,he,rfl⟩)

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_LogSobolevInf
-- End LogSobolevInf

-- Begin Hypercontractivity
section ModuleScope_Hypercontractivity

namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma hypercontractivity_general {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀x,0<π x) (f : V → ℝ) {s : ℝ} (hs : 0≤ s) :
    lpNorm π (1+Real.exp (2*logSobolev K π*s)) (heatOp K s f) ≤ lpNorm π 2 f := by
  have ha := logSobolev_nonneg hK hπ hpos
  apply heat_hypercontractive hK hpos (mul_nonneg (by norm_num) ha) _ f hs
  intro g hg p hp
  have hp0 : 0<p := by linarith
  have hE := logSobolev_mul_entL_le hK hπ hpos (fun x=>g x^(p/2))
  rw [ent_power_identity hpos hg hp0.ne'] at hE
  have hL : 0≤entLp π p g := by
    rw [←ent_power_identity hpos hg hp0.ne']
    exact entL_nonneg hπ hpos _
  have hc : 2*logSobolev K π*(p-1)/p^2 ≤ (2/p)*logSobolev K π := by
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    field_simp
    nlinarith
  calc
    _ ≤ ((2/p)*logSobolev K π)*entLp π p g := mul_le_mul_of_nonneg_right hc hL
    _ = (2/p)*(logSobolev K π*entLp π p g) := by ring
    _ ≤ (2/p)*dirichlet K π (fun x=>g x^(p/2)) (fun x=>g x^(p/2)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ _ := dirichlet_power_general hK hπ.1.1 g hg hp

lemma hypercontractivity_reversible {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hpos : ∀x,0<π x) (hrev : MarkovMixing.DetailedBalance K π)
    (f : V → ℝ) {s : ℝ} (hs : 0≤ s) :
    lpNorm π (1+Real.exp (4*logSobolev K π*s)) (heatOp K s f) ≤ lpNorm π 2 f := by
  have ha := logSobolev_nonneg hK hπ hpos
  apply heat_hypercontractive hK hpos (mul_nonneg (by norm_num) ha) _ f hs
  intro g hg p hp
  have hp0 : 0<p := by linarith
  have hE := logSobolev_mul_entL_le hK hπ hpos (fun x=>g x^(p/2))
  rw [ent_power_identity hpos hg hp0.ne'] at hE
  calc
    _ = (4*(p-1)/p^2)*(logSobolev K π*entLp π p g) := by ring
    _ ≤ (4*(p-1)/p^2)*dirichlet K π (fun x=>g x^(p/2)) (fun x=>g x^(p/2)) :=
      mul_le_mul_of_nonneg_left hE (div_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg p))
    _ ≤ _ := dirichlet_power_reversible hK hπ.1.1 hrev g hg hp

end LogSobolevMC.ChiSquare.Proof
end ModuleScope_Hypercontractivity
-- End Hypercontractivity

-- Begin HeatUpper
section ModuleScope_HeatUpper

open scoped BigOperators
namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem heat_upper_at_larger_time {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hp : ∀ x, 0 < π x) (hr : MarkovMixing.DetailedBalance K π)
    (ha : 0<logSobolev K π) (hg : 0<gap K π)
    (x : V) (hx : π x≤Real.exp (-1)) (c t : ℝ) (hc : 0<c)
    (ht : (4*logSobolev K π)⁻¹*Real.log (Real.log (1/π x))+c/gap K π ≤ t) :
    squareMean π (fun y => density K π t x y-1) ≤ Real.exp (2*(1-c)) := by
  let : Nonempty V := ⟨x⟩
  let s := (4*logSobolev K π)⁻¹*Real.log (Real.log (1/π x))
  let c' := (t-s)*gap K π
  have hcc : c≤c' := by
    dsimp [c']
    have h := (div_le_iff₀ hg).mp (show c/gap K π≤t-s by dsimp [s]; linarith)
    linarith
  have hc' : 0<c' := hc.trans_le hcc
  have he : s+c'/gap K π=t := by dsimp [c']; field_simp [ne_of_gt hg]; ring
  have h := mixing_from_hypercontractivity hK hπ hp ha hg 4 (by norm_num)
    (fun s hs f => hypercontractivity_reversible hK hπ hp hr f hs) x hx c' hc'
  change lpNorm π 2 (fun y => density K π (s+c'/gap K π) x y-1) ≤ _ at h
  rw [he] at h
  have hn : 0≤lpNorm π 2 (fun y => density K π t x y-1) := lpNorm_nonneg (fun y => (hp y).le) _ _
  have hsq : (lpNorm π 2 (fun y => density K π t x y-1))^2 ≤ (Real.exp (1-c'))^2 :=
    sq_le_sq₀ hn (Real.exp_pos _).le |>.2 h
  rw [lpNorm_two_sq (fun y => (hp y).le)] at hsq
  apply hsq.trans
  rw [pow_two,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end LogSobolevMC.Metropolis.Proof
end ModuleScope_HeatUpper
-- End HeatUpper

-- Begin LogTimeBounds
section ModuleScope_LogTimeBounds

namespace LogSobolevMC.Metropolis.Proof

theorem loglog_binomial_bound {n : ℕ} (hn : 1≤n) {p : ℝ}
    (hp : 0<p) (hsmall : p≤Real.exp (-1)) (hlower : 1/(2:ℝ)^n≤p) :
    0≤Real.log (Real.log (1/p)) ∧
      Real.log (Real.log (1/p))≤Real.log n-1/4 := by
  have hpn := Real.log_le_log hp hsmall
  rw [Real.log_exp] at hpn
  have hz : 1≤Real.log (1/p) := by rw [one_div,Real.log_inv]; linarith
  have hn' : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hi : 1/p≤(2:ℝ)^n := by
    have h := one_div_le_one_div_of_le (by positivity : 0<1/(2:ℝ)^n) hlower
    simpa only [one_div_one_div] using h
  have hlog : Real.log (1/p)≤(n:ℝ)*Real.log 2 := by
    have h := Real.log_le_log (div_pos zero_lt_one hp) hi
    simpa only [Real.log_pow] using h
  have hlog2' : Real.log 2≤Real.exp (-(1/4:ℝ)) := by
    have h := Real.log_two_lt_d9
    have he := Real.add_one_le_exp (-(1/4:ℝ))
    linarith
  have hll : Real.log (Real.log 2)≤-(1/4:ℝ) := by
    have h := Real.log_le_log hlog2 hlog2'
    simpa only [Real.log_exp] using h
  refine ⟨Real.log_nonneg hz, ?_⟩
  have h := Real.log_le_log (lt_of_lt_of_le zero_lt_one hz) hlog
  rw [Real.log_mul hn'.ne' hlog2.ne'] at h
  linarith

theorem smoothing_time_bound {n : ℕ} (hn : 1≤n) {p a : ℝ}
    (hp : 0<p) (hsmall : p≤Real.exp (-1)) (hlower : 1/(2:ℝ)^n≤p)
    (ha : 1/(2*(n:ℝ))≤a) :
    (4*a)⁻¹*Real.log (Real.log (1/p))≤(n:ℝ)/2*Real.log n-(n:ℝ)/8 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha' : 0<a := (by positivity : 0<1/(2*(n:ℝ))).trans_le ha
  have hi : (4*a)⁻¹≤(n:ℝ)/2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : 0<4*a)).2
    have h := (div_le_iff₀ (by positivity : 0<2*(n:ℝ))).mp ha
    nlinarith
  obtain ⟨h0,h1⟩ := loglog_binomial_bound hn hp hsmall hlower
  calc
    _ ≤ (n:ℝ)/2*Real.log (Real.log (1/p)) := mul_le_mul_of_nonneg_right hi h0
    _ ≤ (n:ℝ)/2*(Real.log n-1/4) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

theorem gap_time_bound {n : ℕ} (hn : 1≤n) {g c : ℝ}
    (hg : 1/(n:ℝ)≤g) (hc : 0≤c) : c/g≤c*n := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hg' : 0<g := (by positivity : 0<1/(n:ℝ)).trans_le hg
  apply (div_le_iff₀ hg').2
  have h := (div_le_iff₀ hn').mp hg
  nlinarith

end LogSobolevMC.Metropolis.Proof
end ModuleScope_LogTimeBounds
-- End LogTimeBounds

-- Begin HeatWindow
section ModuleScope_HeatWindow

namespace LogSobolevMC.Metropolis.Proof
open LogSobolevMC.ChiSquare LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem heat_window {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hp : ∀ x, 0<π x) (hr : MarkovMixing.DetailedBalance K π)
    (n : ℕ) (hn : 1≤n)
    (ha : 1/(2*(n:ℝ))≤logSobolev K π) (hg : 1/(n:ℝ)≤gap K π)
    (x : V) (hx : π x≤Real.exp (-1)) (hlower : 1/(2:ℝ)^n≤π x)
    (c t : ℝ) (hc : 0<c) (ht : (n:ℝ)/2*Real.log n+c*n≤t) :
    squareMean π (fun y => density K π t x y-1) ≤ Real.exp (2*(1-c)) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha' : 0<logSobolev K π := (by positivity : 0<1/(2*(n:ℝ))).trans_le ha
  have hg' : 0<gap K π := (by positivity : 0<1/(n:ℝ)).trans_le hg
  apply heat_upper_at_larger_time hK hπ hp hr ha' hg' x hx c t hc
  have hs := smoothing_time_bound hn (hp x) hx hlower ha
  have hgtime := gap_time_bound hn hg hc.le
  linarith

theorem heat_smoothing {K : Matrix V V ℝ} {π : V → ℝ}
    (hK : MarkovMixing.IsStochastic K) (hπ : MarkovMixing.IsStationary K π)
    (hp : ∀ x, 0<π x) (hr : MarkovMixing.DetailedBalance K π)
    (n : ℕ) (hn : 1≤n)
    (ha : 1/(2*(n:ℝ))≤logSobolev K π) (hg : 1/(n:ℝ)≤gap K π)
    (x : V) (hx : π x≤Real.exp (-1)) (hlower : 1/(2:ℝ)^n≤π x)
    (t : ℝ) (ht : (n:ℝ)/2*Real.log n≤t) :
    squareMean π (fun y => density K π t x y-1) ≤ Real.exp 2 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha' : 0<logSobolev K π := (by positivity : 0<1/(2*(n:ℝ))).trans_le ha
  have hg' : 0<gap K π := (by positivity : 0<1/(n:ℝ)).trans_le hg
  have hs := smoothing_time_bound hn (hp x) hx hlower ha
  have hgtime := gap_time_bound hn hg (by norm_num : 0≤(1/8:ℝ))
  have h := heat_upper_at_larger_time hK hπ hp hr ha' hg' x hx (1/8) t
    (by norm_num) (by linarith)
  exact h.trans (Real.exp_le_exp.mpr (by norm_num))

end LogSobolevMC.Metropolis.Proof
end ModuleScope_HeatWindow
-- End HeatWindow

-- Begin RoundedWindow
section ModuleScope_RoundedWindow

namespace LogSobolevMC.Metropolis.Proof

theorem rounded_window (n : ℕ) (hn : 4≤n) (c : ℝ) (hc : 1<c) (l : ℕ)
    (hl : (n:ℝ)/2*(Real.log n+2*c)≤l) :
    ∃ j k : ℕ, l=j+k+1 ∧ (n:ℝ)/2*Real.log n≤j ∧
      (1-2/(n:ℝ))^(2*k)≤Real.exp (2-4*c) := by
  have hn4 : (4:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  let s := (n:ℝ)/2*Real.log n
  have hs : 0 ≤ s := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  let j := Nat.ceil s
  have hj : s ≤ (j:ℝ) := Nat.le_ceil s
  have hj' : (j:ℝ)<s+1 := Nat.ceil_lt_add_one hs
  have hl' : s+c*n≤(l:ℝ) := by dsimp [s]; nlinarith
  have hcn : 4<c*n := by nlinarith
  have hjl : j+1≤l := by
    have h : (j:ℝ)+1≤l := by linarith
    exact_mod_cast h
  let k := l-j-1
  have he : l=j+k+1 := by dsimp [k]; omega
  have he' : (l:ℝ)=(j:ℝ)+(k:ℝ)+1 := by exact_mod_cast he
  have hk : c*n-2≤(k:ℝ) := by linarith
  refine ⟨j,k,he,hj,?_⟩
  have hb : 0≤1-2/(n:ℝ) := by
    have h : 2/(n:ℝ)≤1 := (div_le_one hn0).2 (by linarith)
    linarith
  calc
    _ ≤ Real.exp (((2*k:ℕ):ℝ)*((1-2/(n:ℝ))-1)) := nonneg_pow_le_exp hb _
    _ ≤ Real.exp (2-4*c) := by
      apply Real.exp_le_exp.mpr
      simp only [Nat.cast_mul,Nat.cast_ofNat]
      have h : (2*(k:ℝ))*((1-2/(n:ℝ))-1) = -4*(k:ℝ)/(n:ℝ) := by ring
      rw [h]
      apply (div_le_iff₀ hn0).2
      nlinarith

theorem comparison_constant {c : ℝ} (hc : 1≤c) :
    Real.exp (2-4*c)*(1+Real.exp 2)+Real.exp (2*(1-c)) ≤
      4*Real.exp (2*(1-c)) := by
  have h1 : Real.exp (2-4*c)≤Real.exp (2*(1-c)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (2-4*c)*Real.exp 2≤Real.exp (2*(1-c)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hp := Real.exp_pos (2*(1-c))
  nlinarith

end LogSobolevMC.Metropolis.Proof
end ModuleScope_RoundedWindow
-- End RoundedWindow

-- Begin NativeMixing
section ModuleScope_NativeMixing

open scoped BigOperators
open LogSobolevMC.ChiSquare LogSobolevMC.ChiSquare.Proof

namespace LogSobolevMC.Metropolis.Proof
noncomputable section

lemma native_row_dist (n l : ℕ) (x : Fin (n+1)) :
    MarkovMixing.IsDist (MarkovMixing.rowDist (binomMetropolis n) l x) :=
  ⟨(stochastic_pow (binom_stochastic n) l).1 x,
    (stochastic_pow (binom_stochastic n) l).2 x⟩

lemma native_tv_of_square (n l : ℕ) (x : Fin (n+1)) (c : ℝ)
    (h : squareMean (binomPi n)
      (fun y => (binomMetropolis n ^ l) x y / binomPi n y - 1) ≤
        4*Real.exp (2*(1-c))) :
    MarkovMixing.tvDist (MarkovMixing.rowDist (binomMetropolis n) l x) (binomPi n) ≤
      Real.exp (1-c) := by
  have ht := tv_le_half_sqrt (native_row_dist n l x) (binomPi_dist n) (binomPi_pos n)
  have hn := tv_nonneg (MarkovMixing.rowDist (binomMetropolis n) l x) (binomPi n)
  have hq := squareMean_nonneg (binomPi_dist n).1
    (fun y => (binomMetropolis n ^ l) x y / binomPi n y - 1)
  have hs := Real.sq_sqrt hq
  have hsn := Real.sqrt_nonneg (squareMean (binomPi n)
    (fun y => (binomMetropolis n ^ l) x y / binomPi n y - 1))
  have he : (Real.exp (1-c))^2=Real.exp (2*(1-c)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change MarkovMixing.tvDist _ _ ≤ Real.sqrt (squareMean (binomPi n)
    (fun y => (binomMetropolis n ^ l) x y / binomPi n y - 1))/2 at ht
  nlinarith [Real.exp_pos (1-c)]

lemma coarse_holding (n : ℕ) (hn : 1 ≤ n) (x : Fin (n+1)) :
    (1/(n:ℝ))/2 ≤ binomMetropolis n x x := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  apply le_trans _ (binom_holding n x)
  rw [show (1/(n:ℝ))/2=1/(2*(n:ℝ)) by ring]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  linarith

lemma native_coarse (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (x : Fin (n+1)) (l : ℕ)
    (hl : (n:ℝ)/2*(Real.log n+2*c)≤l)
    (hx : 1/binomPi n x-1 ≤ 4*Real.exp 2) :
    MarkovMixing.tvDist (MarkovMixing.rowDist (binomMetropolis n) l x) (binomPi n) ≤
      Real.exp (1-c) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  let s := weightedSpectrum (binomPi_pos n) (binom_balance n)
  have h := s.coarse_square (binomPi_pos n) (binom_stochastic n) (binom_stationary n)
    (1/(n:ℝ)) (by positivity) (binom_poincare n hn) (coarse_holding n hn) x l
  have htime : c*n ≤ (l:ℝ) := by nlinarith [Real.log_nonneg hn']
  have hexp : Real.exp (-2*(l:ℝ)*(1/(n:ℝ))) ≤ Real.exp (-2*c) := by
    apply Real.exp_le_exp.mpr
    have hh : c ≤ (l:ℝ)/n := (le_div_iff₀ hn0).2 (by simpa [mul_comm] using htime)
    rw [show -2*(l:ℝ)*(1/(n:ℝ)) = -2*((l:ℝ)/n) by ring]
    linarith
  have hpi : binomPi n x ≤ 1 := by
    have hh := Finset.single_le_sum (fun y _ => (binomPi_pos n y).le) (Finset.mem_univ x)
    simpa [(binomPi_dist n).2] using hh
  have ha : 0 ≤ 1/binomPi n x-1 := by
    have hh : 1 ≤ 1/binomPi n x := (le_div_iff₀ (binomPi_pos n x)).2 (by simpa using hpi)
    linarith
  apply native_tv_of_square
  calc
    _ ≤ (1/binomPi n x-1)*Real.exp (-2*(l:ℝ)*(1/(n:ℝ))) := h
    _ ≤ (4*Real.exp 2)*Real.exp (-2*c) := mul_le_mul hx hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma binomial_mixing (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c)
    (x : Fin (n+1)) (l : ℕ)
    (hl : (n:ℝ)/2*(Real.log n+2*c)≤(l:ℝ)) :
    MarkovMixing.tvDist (MarkovMixing.rowDist (binomMetropolis n) l x) (binomPi n) ≤
      Real.exp (1-c) := by
  by_cases hc1 : c ≤ 1
  · exact (tv_le_one (native_row_dist n l x) (binomPi_dist n)).trans
      (Real.one_le_exp (by linarith))
  have hc' : 1<c := lt_of_not_ge hc1
  by_cases hn3 : n ≤ 3
  · apply native_coarse n hn c x l hl
    have hp : (2:ℝ)^n ≤ 8 := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn3
      norm_num at hh ⊢
      exact hh
    have hxlow : (1/8:ℝ) ≤ binomPi n x :=
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hp).trans
        (by simpa [one_div] using binomPi_lower n x)
    have hi : 1/binomPi n x ≤ 8 := (div_le_iff₀ (binomPi_pos n x)).2 (by linarith)
    nlinarith [Real.add_one_le_exp (2:ℝ)]
  have hn4 : 4≤n := by omega
  by_cases hx : binomPi n x ≤ Real.exp (-1)
  · obtain ⟨j,k,he,hj,hpow⟩ := rounded_window n hn4 c hc' l hl
    have hn' : (4:ℝ) ≤ n := by exact_mod_cast hn4
    have hb : 0≤1-2/(n:ℝ) := by
      have hh : 2/(n:ℝ)≤1 := (div_le_one (by positivity)).2 (by linarith)
      linarith
    have hh : ∀ y : Fin (n+1), (1-(1-2/(n:ℝ)))/2 ≤ binomMetropolis n y y := by
      intro y
      apply le_trans _ (binom_holding n y)
      rw [show (1-(1-2/(n:ℝ)))/2=1/(n:ℝ) by ring]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      linarith
    have hlow : 1/(2:ℝ)^n≤binomPi n x := by simpa [one_div] using binomPi_lower n x
    have hs := heat_smoothing (binom_stochastic n) (binom_stationary n) (binomPi_pos n)
      (binom_balance n) n hn (binom_logSobolev_lower n hn) (binom_gap_lower n hn) x hx hlow j hj
    have ht := heat_window (binom_stochastic n) (binom_stationary n) (binomPi_pos n)
      (binom_balance n) n hn (binom_logSobolev_lower n hn) (binom_gap_lower n hn) x hx hlow c l hc
      (by nlinarith)
    have hd := discrete_heat_comparison (binomPi_pos n) (binom_stochastic n) (binom_stationary n)
      (binom_balance n) (1-2/(n:ℝ)) hb hh x j k
    rw [← he] at hd
    apply native_tv_of_square
    apply hd.trans
    apply le_trans _ (comparison_constant hc'.le)
    have hnon : 0≤1+squareMean (binomPi n) (fun y => density (binomMetropolis n) (binomPi n) j x y-1) := by
      have hq := squareMean_nonneg (binomPi_dist n).1 (fun y => density (binomMetropolis n) (binomPi n) j x y-1)
      linarith
    exact add_le_add (mul_le_mul hpow (by linarith) hnon (Real.exp_pos _).le) ht
  · apply native_coarse n hn c x l hl
    have hp : Real.exp (-1) ≤ binomPi n x := (lt_of_not_ge hx).le
    have hi := one_div_le_one_div_of_le (Real.exp_pos (-1)) hp
    simp only [one_div, ← Real.exp_neg, neg_neg] at hi
    have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    rw [one_div]
    nlinarith [Real.exp_pos 2]

end
end LogSobolevMC.Metropolis.Proof
end ModuleScope_NativeMixing
-- End NativeMixing

-- Begin RootAssembly
section ModuleScope_RootAssembly

namespace LogSobolevMC.Metropolis

/-- Theorem 1.1, p. 698 (upper bound): the Metropolis chain `M` of (1.9) for the binomial
distribution `π(x) = 2⁻ⁿ C(n, x)` on `{0, …, n}` satisfies
`‖M_xˡ − π‖_TV ≤ e^{1−c}` for every starting state `x`, every `c > 0` and every
`l ≥ (n/2)(log n + 2c)`. -/
theorem theorem_1_1 (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c) (x : Fin (n + 1)) (l : ℕ)
    (hl : (n : ℝ) / 2 * (Real.log n + 2 * c) ≤ (l : ℝ)) :
    MarkovMixing.tvDist (MarkovMixing.rowDist (binomMetropolis n) l x) (binomPi n) ≤
      Real.exp (1 - c) := by
  exact Proof.binomial_mixing n hn c hc x l hl

end LogSobolevMC.Metropolis
end ModuleScope_RootAssembly
-- End RootAssembly

-- Begin Solution
section ModuleScope_Solution
open LogSobolevMC.Metropolis

theorem solution (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c) (x : Fin (n + 1)) (l : ℕ)
    (hl : (n : ℝ) / 2 * (Real.log n + 2 * c) ≤ (l : ℝ)) :
    MarkovMixing.tvDist (MarkovMixing.rowDist (binomMetropolis n) l x) (binomPi n) ≤
      Real.exp (1 - c) := by
  exact LogSobolevMC.Metropolis.theorem_1_1 n hn c hc x l hl
end ModuleScope_Solution
-- End Solution
