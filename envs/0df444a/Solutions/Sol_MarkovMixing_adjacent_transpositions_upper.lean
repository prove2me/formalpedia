-- Prove2me | solution 1 for MarkovMixing.adjacent_transpositions_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-23T18:15:41.536767+00:00
-- url     : https://prove2.me/submissions/aef66817-98d5-4257-83f0-9ef52eea3efc

import Definitions.Def_mm_shuffle
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
LPW §16.1.2: upper bound `t_mix(ε) ≤ 2 n³ log₂ n` for the lazy random
adjacent transpositions shuffle, via Aldous' coupling.
-/

namespace AdjT

open scoped BigOperators
open MarkovMixing Finset

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

abbrev Pm (n : ℕ) := Equiv.Perm (Fin n)
abbrev St (n : ℕ) := Pm n × Pm n

/-- The successor position `i+1` (mod `n`), matching `adjacentTranspositionDist`. -/
def nx {n : ℕ} (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ i.pos⟩

/-- The interior positions `i` with `i+1 < n`. -/
def Idx (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val + 1 < n)

/-- The adjacent transposition `(i, i+1)`. -/
def tau {n : ℕ} (i : Fin n) : Pm n := Equiv.swap i (nx i)

variable {n : ℕ}

lemma mem_Idx {i : Fin n} : i ∈ Idx n ↔ i.val + 1 < n := by
  simp [Idx]

lemma nx_val {i : Fin n} (h : i.val + 1 < n) : (nx i).val = i.val + 1 := by
  simp [nx, Nat.mod_eq_of_lt h]

lemma nx_ne {i : Fin n} (h : i.val + 1 < n) : nx i ≠ i := by
  intro hc
  have := congrArg Fin.val hc
  rw [nx_val h] at this
  omega

lemma Idx_card (hn : 1 ≤ n) : (Idx n).card = n - 1 := by
  have hlt : n - 1 < n := by omega
  have hset : Idx n = Finset.univ.erase (⟨n - 1, hlt⟩ : Fin n) := by
    ext i
    have hi := i.isLt
    simp only [mem_Idx, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h hc
      have hv : i.val = n - 1 := by rw [hc]
      omega
    · intro h
      by_contra hcon
      exact h (Fin.val_injective (show i.val = n - 1 by omega))
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

lemma tau_ne_one {i : Fin n} (h : i.val + 1 < n) : tau i ≠ 1 := by
  intro hc
  have : (tau i) i = i := by rw [hc]; rfl
  rw [tau, Equiv.swap_apply_left] at this
  exact nx_ne h this

lemma tau_injOn {i j : Fin n} (hi : i.val + 1 < n) (hj : j.val + 1 < n)
    (h : tau i = tau j) : i = j := by
  by_contra hne
  have h1 : (tau i) i = (tau j) i := by rw [h]
  rw [tau, Equiv.swap_apply_left] at h1
  rw [tau, Equiv.swap_apply_def] at h1
  rw [if_neg hne] at h1
  by_cases hik : i = nx j
  · rw [if_pos hik] at h1
    have e1 : i.val = j.val + 1 := by rw [hik, nx_val hj]
    have e2 : i.val + 1 = j.val := by rw [← nx_val hi, h1]
    omega
  · rw [if_neg hik] at h1
    exact nx_ne hi h1

/-! ### The increment distribution -/

lemma mu_eq (g : Pm n) :
    adjacentTranspositionDist n g
      = (if g = 1 then (1:ℝ)/2 else 0)
        + (if g ∈ (Idx n).image tau then 1 / (2 * ((n:ℝ) - 1)) else 0) := by
  have himg : ∀ h : Pm n, h ∈ (Idx n).image tau ↔
      ∃ i : Fin n, i.val + 1 < n ∧ h = Equiv.swap i ⟨(i.val + 1) % n, Nat.mod_lt _ i.pos⟩ := by
    intro h
    constructor
    · intro hh
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hh
      exact ⟨i, mem_Idx.1 hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_image.2 ⟨i, mem_Idx.2 hi, rfl⟩
  by_cases h1 : g = 1
  · subst h1
    have : (1 : Pm n) ∉ (Idx n).image tau := by
      intro hc
      obtain ⟨i, hi, he⟩ := Finset.mem_image.1 hc
      exact tau_ne_one (mem_Idx.1 hi) he
    simp [adjacentTranspositionDist, this]
  · simp only [adjacentTranspositionDist, h1, if_false, zero_add]
    by_cases h2 : g ∈ (Idx n).image tau
    · rw [if_pos h2, if_pos ((himg g).1 h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 ((himg g).2 hc))]

lemma sum_mu_mul (hn : 2 ≤ n) (f : Pm n → ℝ) :
    ∑ g : Pm n, adjacentTranspositionDist n g * f g
      = f 1 / 2 + (∑ i ∈ Idx n, f (tau i)) / (2 * ((n:ℝ) - 1)) := by
  have hinj : ∀ x ∈ Idx n, ∀ y ∈ Idx n, tau x = tau y → x = y := by
    intro a ha b hb hab
    exact tau_injOn (mem_Idx.1 ha) (mem_Idx.1 hb) hab
  calc ∑ g : Pm n, adjacentTranspositionDist n g * f g
      = ∑ g : Pm n, ((if g = 1 then (1:ℝ)/2 else 0) * f g
          + (if g ∈ (Idx n).image tau then 1 / (2 * ((n:ℝ) - 1)) else 0) * f g) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [mu_eq g]; ring
    _ = (∑ g : Pm n, (if g = 1 then (1:ℝ)/2 else 0) * f g)
        + ∑ g : Pm n, (if g ∈ (Idx n).image tau then 1 / (2 * ((n:ℝ) - 1)) else 0) * f g :=
        Finset.sum_add_distrib
    _ = f 1 / 2 + (∑ i ∈ Idx n, f (tau i)) / (2 * ((n:ℝ) - 1)) := by
        congr 1
        · rw [Finset.sum_congr rfl (fun g _ => by
              by_cases h : g = 1 <;> simp [h] <;> ring : ∀ g ∈ Finset.univ,
              (if g = 1 then (1:ℝ)/2 else 0) * f g = if g = 1 then f 1 / 2 else 0)]
          simp
        · rw [Finset.sum_congr rfl (fun g _ => by
              by_cases h : g ∈ (Idx n).image tau
              · rw [if_pos h, if_pos h]; ring
              · rw [if_neg h, if_neg h, zero_mul] : ∀ g ∈ Finset.univ,
              (if g ∈ (Idx n).image tau then 1 / (2 * ((n:ℝ) - 1)) else 0) * f g
                = if g ∈ (Idx n).image tau then f g / (2 * ((n:ℝ) - 1)) else 0)]
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image hinj,
            ← Finset.sum_div]

lemma sum_P_mul (hn : 2 ≤ n) (x : Pm n) (f : Pm n → ℝ) :
    ∑ y : Pm n, (groupWalk (adjacentTranspositionDist n)) x y * f y
      = f x / 2 + (∑ i ∈ Idx n, f (tau i * x)) / (2 * ((n:ℝ) - 1)) := by
  have : ∑ y : Pm n, (groupWalk (adjacentTranspositionDist n)) x y * f y
      = ∑ g : Pm n, adjacentTranspositionDist n g * f (g * x) := by
    refine (Fintype.sum_equiv (Equiv.mulRight x) _ _ ?_).symm
    intro g
    simp [groupWalk, Equiv.mulRight]
  rw [this, sum_mu_mul hn (fun g => f (g * x)), one_mul]

/-! ### The Aldous coupling -/

/-- The "crossing pair" test at locations `(i, i+1)`: LPW's condition
`σ(i) = σ'(i+1)` or `σ(i+1) = σ'(i)`, written with `σ` sending cards to
positions. -/
def sp (z : St n) (i : Fin n) : Bool :=
  decide (z.1.symm i = z.2.symm (nx i) ∨ z.1.symm (nx i) = z.2.symm i)

/-- One step of the coupling: the left deck performs the transposition iff
`c`, the right deck iff `c` differs from the crossing test. -/
def step (z : St n) (i : Fin n) (c : Bool) : St n :=
  ((if c then tau i * z.1 else z.1), if xor c (sp z i) then tau i * z.2 else z.2)

/-- The coupled transition matrix. -/
noncomputable def Cpl (n : ℕ) : Matrix (St n) (St n) ℝ :=
  fun z w => (∑ i ∈ Idx n, ∑ c : Bool, if w = step z i c then (1:ℝ) else 0) /
    (2 * ((n:ℝ) - 1))

lemma two_le_cast (hn : 2 ≤ n) : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn

lemma denom_pos (hn : 2 ≤ n) : (0:ℝ) < 2 * ((n:ℝ) - 1) := by
  have := two_le_cast hn; linarith

lemma Cpl_nonneg (hn : 2 ≤ n) (z w : St n) : 0 ≤ Cpl n z w := by
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => ?_)
    (le_of_lt (denom_pos hn))
  split <;> norm_num

lemma sum_Cpl_mul (F : St n → ℝ) (z : St n) :
    ∑ w, Cpl n z w * F w
      = (∑ i ∈ Idx n, ∑ c : Bool, F (step z i c)) / (2 * ((n:ℝ) - 1)) := by
  calc ∑ w, Cpl n z w * F w
      = (∑ w : St n, ∑ i ∈ Idx n, ∑ c : Bool,
            (if w = step z i c then F w else 0)) / (2 * ((n:ℝ) - 1)) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Cpl, div_mul_eq_mul_div]
        congr 1
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases h : w = step z i c <;> simp [h]
    _ = (∑ i ∈ Idx n, ∑ c : Bool, F (step z i c)) / (2 * ((n:ℝ) - 1)) := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp

lemma Idx_card_cast (hn : 2 ≤ n) : ((Idx n).card : ℝ) = (n:ℝ) - 1 := by
  rw [Idx_card (by omega)]
  have h1 : (1:ℕ) ≤ n := by omega
  push_cast [Nat.cast_sub h1]
  ring

lemma Cpl_marg1 (hn : 2 ≤ n) (z : St n) (f : Pm n → ℝ) :
    ∑ w, Cpl n z w * f w.1
      = ∑ y : Pm n, (groupWalk (adjacentTranspositionDist n)) z.1 y * f y := by
  rw [sum_P_mul hn, sum_Cpl_mul (fun w => f w.1)]
  have hstep : ∀ i : Fin n, (∑ c : Bool, f (step z i c).1) = f (tau i * z.1) + f z.1 := by
    intro i; simp [step, Fintype.sum_bool]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Idx n) => hstep i), Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, Idx_card_cast hn]
  have hd : ((n:ℝ) - 1) ≠ 0 := by have := two_le_cast hn; linarith
  field_simp
  ring

lemma Cpl_marg2 (hn : 2 ≤ n) (z : St n) (f : Pm n → ℝ) :
    ∑ w, Cpl n z w * f w.2
      = ∑ y : Pm n, (groupWalk (adjacentTranspositionDist n)) z.2 y * f y := by
  rw [sum_P_mul hn, sum_Cpl_mul (fun w => f w.2)]
  have hstep : ∀ i : Fin n, (∑ c : Bool, f (step z i c).2) = f (tau i * z.2) + f z.2 := by
    intro i
    cases hs : sp z i <;> simp [step, hs, Fintype.sum_bool] <;> ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Idx n) => hstep i), Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, Idx_card_cast hn]
  have hd : ((n:ℝ) - 1) ≠ 0 := by have := two_le_cast hn; linarith
  field_simp
  ring

/-! ### Powers of the coupling and the coupling inequality -/

/-- The lazy random adjacent transposition shuffle. -/
noncomputable def Pw (n : ℕ) : Matrix (Pm n) (Pm n) ℝ := groupWalk (adjacentTranspositionDist n)

lemma sum_Pw_mul (hn : 2 ≤ n) (x : Pm n) (f : Pm n → ℝ) :
    ∑ y : Pm n, Pw n x y * f y
      = f x / 2 + (∑ i ∈ Idx n, f (tau i * x)) / (2 * ((n:ℝ) - 1)) := sum_P_mul hn x f

lemma Cpl_marg1' (hn : 2 ≤ n) (z : St n) (f : Pm n → ℝ) :
    ∑ w, Cpl n z w * f w.1 = ∑ y : Pm n, Pw n z.1 y * f y := Cpl_marg1 hn z f

lemma Cpl_marg2' (hn : 2 ≤ n) (z : St n) (f : Pm n → ℝ) :
    ∑ w, Cpl n z w * f w.2 = ∑ y : Pm n, Pw n z.2 y * f y := Cpl_marg2 hn z f

lemma Cpl_pow_nonneg (hn : 2 ≤ n) (t : ℕ) (z w : St n) : 0 ≤ (Cpl n ^ t) z w := by
  induction t generalizing z w with
  | zero => simp only [pow_zero, Matrix.one_apply]; split <;> norm_num
  | succ t ih =>
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun v _ => mul_nonneg (Cpl_nonneg hn z v) (ih v w)

lemma Cpl_pow_marg1 (hn : 2 ≤ n) (t : ℕ) (z : St n) (f : Pm n → ℝ) :
    ∑ w, (Cpl n ^ t) z w * f w.1 = ∑ y : Pm n, (Pw n ^ t) z.1 y * f y := by
  induction t generalizing z with
  | zero => simp [Matrix.one_apply, Finset.sum_ite_eq]
  | succ t ih =>
      have hL : ∑ w, (Cpl n ^ (t+1)) z w * f w.1
          = ∑ v, Cpl n z v * (∑ w, (Cpl n ^ t) v w * f w.1) := by
        rw [pow_succ']
        simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      rw [hL]
      simp only [ih]
      rw [Cpl_marg1' hn z (fun v => ∑ y : Pm n, (Pw n ^ t) v y * f y), pow_succ']
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm

lemma Cpl_pow_marg2 (hn : 2 ≤ n) (t : ℕ) (z : St n) (f : Pm n → ℝ) :
    ∑ w, (Cpl n ^ t) z w * f w.2 = ∑ y : Pm n, (Pw n ^ t) z.2 y * f y := by
  induction t generalizing z with
  | zero => simp [Matrix.one_apply, Finset.sum_ite_eq]
  | succ t ih =>
      have hL : ∑ w, (Cpl n ^ (t+1)) z w * f w.2
          = ∑ v, Cpl n z v * (∑ w, (Cpl n ^ t) v w * f w.2) := by
        rw [pow_succ']
        simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      rw [hL]
      simp only [ih]
      rw [Cpl_marg2' hn z (fun v => ∑ y : Pm n, (Pw n ^ t) v y * f y), pow_succ']
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm

lemma sum_mu_one (hn : 2 ≤ n) : ∑ g : Pm n, adjacentTranspositionDist n g = 1 := by
  have h := sum_mu_mul hn (fun _ : Pm n => (1:ℝ))
  simp only [mul_one] at h
  rw [h, Finset.sum_const, nsmul_eq_mul, mul_one, Idx_card_cast hn]
  have hd : ((n:ℝ) - 1) ≠ 0 := by have := two_le_cast hn; linarith
  field_simp
  norm_num

lemma Pw_col_sum (hn : 2 ≤ n) (y : Pm n) : ∑ x : Pm n, Pw n x y = 1 := by
  have : ∑ x : Pm n, Pw n x y = ∑ g : Pm n, adjacentTranspositionDist n g := by
    exact Fintype.sum_equiv ((Equiv.inv (Pm n)).trans (Equiv.mulLeft y)) _ _ (fun x => rfl)
  rw [this, sum_mu_one hn]

lemma Pw_pow_col_sum (hn : 2 ≤ n) (t : ℕ) (y : Pm n) : ∑ x : Pm n, (Pw n ^ t) x y = 1 := by
  induction t generalizing y with
  | zero => simp [Matrix.one_apply, Finset.sum_ite_eq']
  | succ t ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      have : ∀ v : Pm n, ∑ x : Pm n, (Pw n ^ t) x v * Pw n v y
          = Pw n v y := by
        intro v; rw [← Finset.sum_mul, ih v, one_mul]
      rw [Finset.sum_congr rfl (fun v _ => this v), Pw_col_sum hn]

lemma coupling_ineq (hn : 2 ≤ n) (t : ℕ) (z : St n) (A : Finset (Pm n)) :
    |∑ y ∈ A, (Pw n ^ t) z.1 y - ∑ y ∈ A, (Pw n ^ t) z.2 y|
      ≤ ∑ w, (Cpl n ^ t) z w * (if w.1 = w.2 then (0:ℝ) else 1) := by
  set ind : Pm n → ℝ := fun y => if y ∈ A then (1:ℝ) else 0 with hind
  have e1 : ∀ (x : Pm n), ∑ y : Pm n, (Pw n ^ t) x y * ind y = ∑ y ∈ A, (Pw n ^ t) x y := by
    intro x
    have : ∀ y : Pm n, (Pw n ^ t) x y * ind y = if y ∈ A then (Pw n ^ t) x y else 0 := by
      intro y; by_cases h : y ∈ A <;> simp [hind, h]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_ite_mem, Finset.univ_inter]
  rw [← e1, ← e1, ← Cpl_pow_marg1 hn t z ind, ← Cpl_pow_marg2 hn t z ind,
    ← Finset.sum_sub_distrib]
  calc |∑ w : St n, ((Cpl n ^ t) z w * ind w.1 - (Cpl n ^ t) z w * ind w.2)|
      ≤ ∑ w : St n, |(Cpl n ^ t) z w * ind w.1 - (Cpl n ^ t) z w * ind w.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : St n, (Cpl n ^ t) z w * (if w.1 = w.2 then (0:ℝ) else 1) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (Cpl_pow_nonneg hn t z w)]
        refine mul_le_mul_of_nonneg_left ?_ (Cpl_pow_nonneg hn t z w)
        by_cases h : w.1 = w.2
        · rw [if_pos h, h]; simp
        · rw [if_neg h]
          rcases (by by_cases h1 : w.1 ∈ A <;> by_cases h2 : w.2 ∈ A <;>
            simp [hind, h1, h2] : |ind w.1 - ind w.2| = 0 ∨ |ind w.1 - ind w.2| = 1) with h0 | h0
          · rw [h0]; norm_num
          · rw [h0]

lemma dstat_le (hn : 2 ≤ n) (t : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ z : St n, ∑ w, (Cpl n ^ t) z w * (if w.1 = w.2 then (0:ℝ) else 1) ≤ B) :
    distStationary (Pw n) (uniformDist (Pm n)) t ≤ B := by
  have hcard : (0:ℝ) < (Fintype.card (Pm n) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpi_nonneg : ∀ x : Pm n, 0 ≤ uniformDist (Pm n) x := by
    intro x; simp only [uniformDist]; positivity
  have hpi_sum : ∑ x : Pm n, uniformDist (Pm n) x = 1 := by
    simp only [uniformDist, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  refine ciSup_le fun x => ?_
  refine ciSup_le fun A => ?_
  have hrepr : ∑ y ∈ A, uniformDist (Pm n) y
      = ∑ u : Pm n, uniformDist (Pm n) u * (∑ y ∈ A, (Pw n ^ t) u y) := by
    have hexp : ∀ u : Pm n, uniformDist (Pm n) u * (∑ y ∈ A, (Pw n ^ t) u y)
        = ∑ y ∈ A, uniformDist (Pm n) u * (Pw n ^ t) u y := fun u => Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hexp u), Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [uniformDist]
    rw [← Finset.mul_sum, Pw_pow_col_sum hn t y, mul_one]
  have hsplit : ∑ y ∈ A, (Pw n ^ t) x y - ∑ y ∈ A, uniformDist (Pm n) y
      = ∑ u : Pm n, uniformDist (Pm n) u
          * (∑ y ∈ A, (Pw n ^ t) x y - ∑ y ∈ A, (Pw n ^ t) u y) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hpi_sum, one_mul]
    rw [← hrepr]
  show |∑ y ∈ A, rowDist (Pw n) t x y - ∑ y ∈ A, uniformDist (Pm n) y| ≤ B
  have : ∀ y : Pm n, rowDist (Pw n) t x y = (Pw n ^ t) x y := fun _ => rfl
  rw [Finset.sum_congr rfl (fun y _ => this y), hsplit]
  calc |∑ u : Pm n, uniformDist (Pm n) u
          * (∑ y ∈ A, (Pw n ^ t) x y - ∑ y ∈ A, (Pw n ^ t) u y)|
      ≤ ∑ u : Pm n, |uniformDist (Pm n) u
          * (∑ y ∈ A, (Pw n ^ t) x y - ∑ y ∈ A, (Pw n ^ t) u y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u : Pm n, uniformDist (Pm n) u * B := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [abs_mul, abs_of_nonneg (hpi_nonneg u)]
        exact mul_le_mul_of_nonneg_left
          (le_trans (coupling_ineq hn t (x, u) A) (hbd (x, u))) (hpi_nonneg u)
    _ = B := by rw [← Finset.sum_mul, hpi_sum, one_mul]

/-! ### The quadratic Lyapunov weight -/

noncomputable def phi (n : ℕ) (k : ℕ) : ℝ :=
  ((n:ℝ) - 1) / 2 * (k:ℝ) * (2 * (n:ℝ) - 1 - (k:ℝ))

lemma phi_zero : phi n 0 = 0 := by simp [phi]

lemma phi_succ_sub (k : ℕ) : phi n (k + 1) - phi n k = ((n:ℝ) - 1) * ((n:ℝ) - 1 - (k:ℝ)) := by
  unfold phi; push_cast; ring

lemma phi_le_succ (hn : 2 ≤ n) {k : ℕ} (hk : k + 1 ≤ n) : phi n k ≤ phi n (k + 1) := by
  have h := phi_succ_sub (n := n) k
  have hk' : (k:ℝ) ≤ (n:ℝ) - 1 := by
    have : ((k:ℝ) + 1) ≤ (n:ℝ) := by exact_mod_cast hk
    linarith
  have hn' : (0:ℝ) ≤ (n:ℝ) - 1 := by have := two_le_cast hn; linarith
  nlinarith

lemma phi_mono (hn : 2 ≤ n) : ∀ {j k : ℕ}, j ≤ k → k ≤ n → phi n j ≤ phi n k := by
  intro j k
  induction k with
  | zero => intro h _; have hj : j = 0 := Nat.le_zero.1 h; subst hj; exact le_refl _
  | succ k ih =>
      intro hjk hk
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact le_trans (ih (Nat.lt_succ_iff.1 h) (by omega)) (phi_le_succ hn hk)
      · have hj : j = k + 1 := le_antisymm hjk h
        subst hj; exact le_refl _

lemma phi_nonneg (hn : 2 ≤ n) {k : ℕ} (hk : k ≤ n) : 0 ≤ phi n k := by
  have := phi_mono hn (Nat.zero_le k) hk
  rwa [phi_zero] at this

lemma phi_second_diff (hn : 2 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    (phi n (k + 1) - phi n k) - (phi n k - phi n (k - 1)) = -((n:ℝ) - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [phi_succ_sub, phi_succ_sub]
  push_cast
  ring

/-! ### The Lyapunov function for one card -/

def dv (x y : Fin n) : ℕ := max x.val y.val - min x.val y.val

def dcard (a : Fin n) (z : St n) : ℕ := dv (z.1 a) (z.2 a)

/-- The action of `tau i` on positions, read off on values. -/
def fvn (j k : ℕ) : ℕ := if k = j then j + 1 else if k = j + 1 then j else k

lemma tau_fix {i x : Fin n} (h1 : x ≠ i) (h2 : x ≠ nx i) : (tau i) x = x :=
  Equiv.swap_apply_of_ne_of_ne h1 h2

lemma tau_left (i : Fin n) : (tau i) i = nx i := Equiv.swap_apply_left _ _

lemma tau_right (i : Fin n) : (tau i) (nx i) = i := Equiv.swap_apply_right _ _

lemma tau_val {i : Fin n} (hi : i.val + 1 < n) (x : Fin n) :
    ((tau i) x).val = fvn i.val x.val := by
  have hnxv : (nx i).val = i.val + 1 := nx_val hi
  by_cases h1 : x = i
  · subst h1
    rw [tau_left, hnxv]
    simp [fvn]
  · by_cases h2 : x = nx i
    · subst h2
      rw [tau_right, hnxv]
      simp [fvn]
    · rw [tau_fix h1 h2]
      have hne1 : x.val ≠ i.val := fun hc => h1 (Fin.ext hc)
      have hne2 : x.val ≠ i.val + 1 := fun hc => h2 (Fin.ext (by rw [hnxv]; exact hc))
      simp [fvn, hne1, hne2]

lemma dv_tau_eq {i : Fin n} (hi : i.val + 1 < n) (x y : Fin n) :
    dv ((tau i) x) ((tau i) y)
      = max (fvn i.val x.val) (fvn i.val y.val) - min (fvn i.val x.val) (fvn i.val y.val) := by
  unfold dv
  rw [tau_val hi, tau_val hi]

lemma step_fst_apply (z : St n) (i : Fin n) (c : Bool) (a : Fin n) :
    (step z i c).1 a = if c then (tau i) (z.1 a) else z.1 a := by
  cases c <;> simp [step]

lemma step_snd_apply (z : St n) (i : Fin n) (c : Bool) (a : Fin n) :
    (step z i c).2 a = if xor c (sp z i) then (tau i) (z.2 a) else z.2 a := by
  cases c <;> cases h : sp z i <;> simp [step, h]

/-- Off the coalescing configuration, the two coupled outcomes contribute
`φ` at the jointly-transposed distance and at the current distance. -/
lemma Psi_generic (a : Fin n) (z : St n) (i : Fin n)
    (hnb : ¬ ((z.1 a = i ∨ z.1 a = nx i) ∧ (z.2 a = i ∨ z.2 a = nx i))) :
    (∑ c : Bool, phi n (dcard a (step z i c)))
      = phi n (dv ((tau i) (z.1 a)) ((tau i) (z.2 a))) + phi n (dcard a z) := by
  have hL : (∑ c : Bool, phi n (dcard a (step z i c)))
      = phi n (dcard a (step z i true)) + phi n (dcard a (step z i false)) :=
    Fintype.sum_bool _
  have e1 : (step z i true).1 a = (tau i) (z.1 a) := by simp [step]
  have e2 : (step z i false).1 a = z.1 a := by simp [step]
  cases hs : sp z i
  · have e3 : (step z i true).2 a = (tau i) (z.2 a) := by simp [step, hs]
    have e4 : (step z i false).2 a = z.2 a := by simp [step, hs]
    rw [hL]
    unfold dcard
    rw [e1, e2, e3, e4]
  · have e3 : (step z i true).2 a = z.2 a := by simp [step, hs]
    have e4 : (step z i false).2 a = (tau i) (z.2 a) := by simp [step, hs]
    rw [hL]
    unfold dcard
    rw [e1, e2, e3, e4]
    rcases not_and_or.1 hnb with h | h
    · have hp : (tau i) (z.1 a) = z.1 a :=
        tau_fix (fun hc => h (Or.inl hc)) (fun hc => h (Or.inr hc))
      rw [hp]; ring
    · have hq : (tau i) (z.2 a) = z.2 a :=
        tau_fix (fun hc => h (Or.inl hc)) (fun hc => h (Or.inr hc))
      rw [hq]

lemma dv_self (x : Fin n) : dv x x = 0 := by unfold dv; omega

/-- On the coalescing configuration the crossing test fires and both
outcomes match card `a` up. -/
lemma Psi_coal (a : Fin n) (z : St n) (i : Fin n) (hi : i.val + 1 < n)
    (h1 : z.1 a = i ∨ z.1 a = nx i) (h2 : z.2 a = i ∨ z.2 a = nx i)
    (hne : z.1 a ≠ z.2 a) :
    (∑ c : Bool, phi n (dcard a (step z i c))) = 2 * phi n 0 := by
  have hnxi : nx i ≠ i := nx_ne hi
  have hL : (∑ c : Bool, phi n (dcard a (step z i c)))
      = phi n (dcard a (step z i true)) + phi n (dcard a (step z i false)) :=
    Fintype.sum_bool _
  have e1 : (step z i true).1 a = (tau i) (z.1 a) := by simp [step]
  have e2 : (step z i false).1 a = z.1 a := by simp [step]
  rcases h1 with hp | hp <;> rcases h2 with hq | hq
  · exact absurd (hp.trans hq.symm) hne
  · have hs : sp z i = true := by
      refine decide_eq_true (Or.inl ?_)
      rw [(Equiv.symm_apply_eq z.1).2 hp.symm, (Equiv.symm_apply_eq z.2).2 hq.symm]
    have e3 : (step z i true).2 a = z.2 a := by simp [step, hs]
    have e4 : (step z i false).2 a = (tau i) (z.2 a) := by simp [step, hs]
    rw [hL]
    unfold dcard
    rw [e1, e2, e3, e4, hp, hq, tau_left, tau_right, dv_self, dv_self]
    ring
  · have hs : sp z i = true := by
      refine decide_eq_true (Or.inr ?_)
      rw [(Equiv.symm_apply_eq z.1).2 hp.symm, (Equiv.symm_apply_eq z.2).2 hq.symm]
    have e3 : (step z i true).2 a = z.2 a := by simp [step, hs]
    have e4 : (step z i false).2 a = (tau i) (z.2 a) := by simp [step, hs]
    rw [hL]
    unfold dcard
    rw [e1, e2, e3, e4, hp, hq, tau_right, tau_left, dv_self, dv_self]
    ring
  · exact absurd (hp.trans hq.symm) hne

/-! ### The one-step drift -/

noncomputable def Dp (n : ℕ) (D : ℕ) : ℝ := phi n (D + 1) - phi n D
noncomputable def Dm (n : ℕ) (D : ℕ) : ℝ := phi n D - phi n (D - 1)

noncomputable def cA (i : Fin n) (k : ℕ) : ℝ := if i.val = k then 1 else 0
noncomputable def cB (i : Fin n) (k : ℕ) : ℝ := if i.val + 1 = k then 1 else 0

lemma cA_nonneg (i : Fin n) (k : ℕ) : 0 ≤ cA i k := by unfold cA; split <;> norm_num
lemma cB_nonneg (i : Fin n) (k : ℕ) : 0 ≤ cB i k := by unfold cB; split <;> norm_num

lemma sum_cA_le (s : Finset (Fin n)) (k : ℕ) : ∑ i ∈ s, cA i k ≤ 1 := by
  rcases lt_or_ge k n with hk | hk
  · have h : ∀ i ∈ s, cA i k = if i = (⟨k, hk⟩ : Fin n) then (1:ℝ) else 0 := by
      intro i _
      unfold cA
      by_cases hc : i = (⟨k, hk⟩ : Fin n)
      · rw [if_pos hc, if_pos (by rw [hc])]
      · rw [if_neg hc, if_neg (fun hv => hc (Fin.val_injective hv))]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' s (⟨k, hk⟩ : Fin n) (fun _ => (1:ℝ))]
    split <;> norm_num
  · have h : ∀ i ∈ s, cA i k = 0 := by
      intro i _
      have := i.isLt
      unfold cA; exact if_neg (by omega)
    rw [Finset.sum_congr rfl h, Finset.sum_const_zero]
    norm_num

lemma sum_cB_le (s : Finset (Fin n)) (k : ℕ) : ∑ i ∈ s, cB i k ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · have h : ∀ i ∈ s, cB i k = 0 := by
      intro i _; unfold cB; exact if_neg (by omega)
    rw [Finset.sum_congr rfl h, Finset.sum_const_zero]; norm_num
  · have h : ∀ i ∈ s, cB i k = cA i (k - 1) := by
      intro i _
      unfold cA cB
      by_cases hc : i.val + 1 = k
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]
    rw [Finset.sum_congr rfl h]
    exact sum_cA_le s (k - 1)

lemma sum_cA_eq (k : ℕ) (hk : k + 1 < n) : ∑ i ∈ Idx n, cA i k = 1 := by
  have hk' : k < n := by omega
  have h : ∀ i ∈ Idx n, cA i k = if i = (⟨k, hk'⟩ : Fin n) then (1:ℝ) else 0 := by
    intro i _
    unfold cA
    by_cases hc : i = (⟨k, hk'⟩ : Fin n)
    · rw [if_pos hc, if_pos (by rw [hc])]
    · rw [if_neg hc, if_neg (fun hv => hc (Fin.val_injective hv))]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Idx n) (⟨k, hk'⟩ : Fin n) (fun _ => (1:ℝ)),
    if_pos (mem_Idx.2 hk)]

lemma sum_cB_eq (k : ℕ) (hk1 : 1 ≤ k) (hk : k < n) : ∑ i ∈ Idx n, cB i k = 1 := by
  have h : ∀ i ∈ Idx n, cB i k = cA i (k - 1) := by
    intro i _
    unfold cA cB
    by_cases hc : i.val + 1 = k
    · rw [if_pos hc, if_pos (by omega)]
    · rw [if_neg hc, if_neg (by omega)]
  rw [Finset.sum_congr rfl h]
  exact sum_cA_eq (k - 1) (by omega)

lemma Psi_bound (hn : 2 ≤ n) (a : Fin n) (z : St n) (hne : z.1 a ≠ z.2 a)
    (i : Fin n) (hi : i ∈ Idx n) :
    (∑ c : Bool, phi n (dcard a (step z i c)))
      ≤ 2 * phi n (dcard a z)
        + Dp n (dcard a z)
            * (cB i (min (z.1 a).val (z.2 a).val) + cA i (max (z.1 a).val (z.2 a).val))
        - Dm n (dcard a z)
            * (cA i (min (z.1 a).val (z.2 a).val) + cB i (max (z.1 a).val (z.2 a).val)) := by
  have hi' : i.val + 1 < n := mem_Idx.1 hi
  have hnxv : (nx i).val = i.val + 1 := nx_val hi'
  have hu : (z.1 a).val < n := (z.1 a).isLt
  have hv : (z.2 a).val < n := (z.2 a).isLt
  have huv : (z.1 a).val ≠ (z.2 a).val := fun hc => hne (Fin.val_injective hc)
  have hDdef : dcard a z = max (z.1 a).val (z.2 a).val - min (z.1 a).val (z.2 a).val := rfl
  have hD1 : 1 ≤ dcard a z := by rw [hDdef]; omega
  have hDn : dcard a z + 1 ≤ n := by rw [hDdef]; omega
  have hplus : 0 ≤ Dp n (dcard a z) := by
    have := phi_le_succ hn (k := dcard a z) hDn
    unfold Dp; linarith
  have hminus : 0 ≤ Dm n (dcard a z) := by
    have hx : dcard a z - 1 + 1 = dcard a z := by omega
    have h2 := phi_le_succ hn (k := dcard a z - 1) (by omega)
    rw [hx] at h2
    unfold Dm; linarith
  have hmk : ∀ x : Fin n, x.val = i.val ∨ x.val = i.val + 1 → (x = i ∨ x = nx i) := by
    intro x hx
    rcases hx with h | h
    · exact Or.inl (Fin.val_injective h)
    · exact Or.inr (Fin.val_injective (by rw [hnxv]; exact h))
  unfold cA cB
  by_cases hboth : (z.1 a = i ∨ z.1 a = nx i) ∧ (z.2 a = i ∨ z.2 a = nx i)
  · have hvals : ((z.1 a).val = i.val ∨ (z.1 a).val = i.val + 1)
        ∧ ((z.2 a).val = i.val ∨ (z.2 a).val = i.val + 1) := by
      refine ⟨?_, ?_⟩
      · rcases hboth.1 with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h, hnxv])
      · rcases hboth.2 with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h, hnxv])
    have hminv : min (z.1 a).val (z.2 a).val = i.val := by omega
    have hmaxv : max (z.1 a).val (z.2 a).val = i.val + 1 := by omega
    have hD : dcard a z = 1 := by rw [hDdef, hminv, hmaxv]; omega
    rw [Psi_coal a z i hi' hboth.1 hboth.2 hne, hminv, hmaxv, hD]
    rw [if_neg (by omega : ¬ (i.val + 1 = i.val)), if_neg (by omega : ¬ (i.val = i.val + 1)),
      if_pos rfl, if_pos rfl]
    unfold Dp Dm
    simp only [Nat.sub_self]
    linarith
  · rw [Psi_generic a z i hboth, dv_tau_eq hi' (z.1 a) (z.2 a)]
    have hnb2 : ¬ (i.val = min (z.1 a).val (z.2 a).val
        ∧ i.val + 1 = max (z.1 a).val (z.2 a).val) := by
      rintro ⟨e1, e2⟩
      exact hboth ⟨hmk _ (by omega), hmk _ (by omega)⟩
    by_cases hA : i.val = min (z.1 a).val (z.2 a).val
    · have hB : ¬ (i.val + 1 = max (z.1 a).val (z.2 a).val) := fun hc => hnb2 ⟨hA, hc⟩
      have hE : max (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val)
          - min (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val) = dcard a z - 1 := by
        rw [hDdef]; unfold fvn; split_ifs <;> omega
      rw [hE, if_pos hA, if_neg hB,
        if_neg (by omega : ¬ (i.val + 1 = min (z.1 a).val (z.2 a).val)),
        if_neg (by omega : ¬ (i.val = max (z.1 a).val (z.2 a).val))]
      unfold Dp Dm
      linarith
    · by_cases hB : i.val + 1 = max (z.1 a).val (z.2 a).val
      · have hE : max (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val)
            - min (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val) = dcard a z - 1 := by
          rw [hDdef]; unfold fvn; split_ifs <;> omega
        rw [hE, if_neg hA, if_pos hB,
          if_neg (by omega : ¬ (i.val + 1 = min (z.1 a).val (z.2 a).val)),
          if_neg (by omega : ¬ (i.val = max (z.1 a).val (z.2 a).val))]
        unfold Dp Dm
        linarith
      · by_cases hC : i.val + 1 = min (z.1 a).val (z.2 a).val
        · have hE : max (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val)
              - min (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val) = dcard a z + 1 := by
            rw [hDdef]; unfold fvn; split_ifs <;> omega
          rw [hE, if_neg hA, if_neg hB, if_pos hC,
            if_neg (by omega : ¬ (i.val = max (z.1 a).val (z.2 a).val))]
          unfold Dp Dm
          linarith
        · by_cases hEE : i.val = max (z.1 a).val (z.2 a).val
          · have hE : max (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val)
                - min (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val) = dcard a z + 1 := by
              rw [hDdef]; unfold fvn; split_ifs <;> omega
            rw [hE, if_neg hA, if_neg hB, if_neg hC, if_pos hEE]
            unfold Dp Dm
            linarith
          · have hE : max (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val)
                - min (fvn i.val (z.1 a).val) (fvn i.val (z.2 a).val) = dcard a z := by
              rw [hDdef]; unfold fvn; split_ifs <;> omega
            rw [hE, if_neg hA, if_neg hB, if_neg hC, if_neg hEE]
            unfold Dp Dm
            linarith

lemma drift (hn : 2 ≤ n) (a : Fin n) (z : St n) (hne : z.1 a ≠ z.2 a) :
    ∑ w, Cpl n z w * phi n (dcard a w) ≤ phi n (dcard a z) - 1 := by
  have hu : (z.1 a).val < n := (z.1 a).isLt
  have hv : (z.2 a).val < n := (z.2 a).isLt
  have huv : (z.1 a).val ≠ (z.2 a).val := fun hc => hne (Fin.val_injective hc)
  have hDdef : dcard a z = max (z.1 a).val (z.2 a).val - min (z.1 a).val (z.2 a).val := rfl
  have hD1 : 1 ≤ dcard a z := by rw [hDdef]; omega
  have hDn : dcard a z + 1 ≤ n := by rw [hDdef]; omega
  have hplus : 0 ≤ Dp n (dcard a z) := by
    have := phi_le_succ hn (k := dcard a z) hDn
    unfold Dp; linarith
  have hminus : 0 ≤ Dm n (dcard a z) := by
    have hx : dcard a z - 1 + 1 = dcard a z := by omega
    have h2 := phi_le_succ hn (k := dcard a z - 1) (by omega)
    rw [hx] at h2
    unfold Dm; linarith
  have hsA : ∑ i ∈ Idx n, cA i (min (z.1 a).val (z.2 a).val) = 1 :=
    sum_cA_eq _ (by omega)
  have hsB : ∑ i ∈ Idx n, cB i (max (z.1 a).val (z.2 a).val) = 1 :=
    sum_cB_eq _ (by omega) (by omega)
  have hsC : ∑ i ∈ Idx n, cB i (min (z.1 a).val (z.2 a).val) ≤ 1 := sum_cB_le _ _
  have hsE : ∑ i ∈ Idx n, cA i (max (z.1 a).val (z.2 a).val) ≤ 1 := sum_cA_le _ _
  have hsC0 : 0 ≤ ∑ i ∈ Idx n, cB i (min (z.1 a).val (z.2 a).val) :=
    Finset.sum_nonneg fun i _ => cB_nonneg i _
  have hsE0 : 0 ≤ ∑ i ∈ Idx n, cA i (max (z.1 a).val (z.2 a).val) :=
    Finset.sum_nonneg fun i _ => cA_nonneg i _
  have h5 : Dp n (dcard a z) - Dm n (dcard a z) = -((n:ℝ) - 1) := by
    have := phi_second_diff hn (k := dcard a z) hD1
    unfold Dp Dm; linarith
  rw [sum_Cpl_mul (fun w => phi n (dcard a w)) z, div_le_iff₀ (denom_pos hn)]
  calc ∑ i ∈ Idx n, (∑ c : Bool, phi n (dcard a (step z i c)))
      ≤ ∑ i ∈ Idx n, (2 * phi n (dcard a z)
          + Dp n (dcard a z)
              * (cB i (min (z.1 a).val (z.2 a).val) + cA i (max (z.1 a).val (z.2 a).val))
          - Dm n (dcard a z)
              * (cA i (min (z.1 a).val (z.2 a).val) + cB i (max (z.1 a).val (z.2 a).val))) :=
        Finset.sum_le_sum fun i hi => Psi_bound hn a z hne i hi
    _ = ((n:ℝ) - 1) * (2 * phi n (dcard a z))
          + Dp n (dcard a z) * ((∑ i ∈ Idx n, cB i (min (z.1 a).val (z.2 a).val))
              + (∑ i ∈ Idx n, cA i (max (z.1 a).val (z.2 a).val)))
          - Dm n (dcard a z) * ((∑ i ∈ Idx n, cA i (min (z.1 a).val (z.2 a).val))
              + (∑ i ∈ Idx n, cB i (max (z.1 a).val (z.2 a).val))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Idx_card_cast hn, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
    _ ≤ (phi n (dcard a z) - 1) * (2 * ((n:ℝ) - 1)) := by
        rw [hsA, hsB]
        have hkey : Dp n (dcard a z)
            * ((∑ i ∈ Idx n, cB i (min (z.1 a).val (z.2 a).val))
              + (∑ i ∈ Idx n, cA i (max (z.1 a).val (z.2 a).val)))
            ≤ Dp n (dcard a z) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hplus
        nlinarith [h5]

/-! ### Matched cards stay matched -/

noncomputable def hcard (a : Fin n) (z : St n) : ℝ := if z.1 a = z.2 a then 0 else 1

lemma hcard_nonneg (a : Fin n) (z : St n) : 0 ≤ hcard a z := by
  unfold hcard; split <;> norm_num

lemma hcard_le_one (a : Fin n) (z : St n) : hcard a z ≤ 1 := by
  unfold hcard; split <;> norm_num

lemma sp_false_of_matched (z : St n) (a : Fin n) (h : z.1 a = z.2 a) (i : Fin n)
    (hi : i.val + 1 < n) (hin : z.1 a = i ∨ z.1 a = nx i) : sp z i = false := by
  have hnxi : nx i ≠ i := nx_ne hi
  have h2 : z.2 a = z.1 a := h.symm
  refine decide_eq_false ?_
  rcases hin with hp | hp
  · have e1 : z.1.symm i = a := by rw [← hp]; exact z.1.symm_apply_apply a
    have hq : z.2 a = i := by rw [h2, hp]
    have e2 : z.2.symm i = a := by rw [← hq]; exact z.2.symm_apply_apply a
    rw [e1, e2]
    rintro (he | he)
    · have hx : z.2 a = nx i := by rw [he]; exact z.2.apply_symm_apply _
      rw [hq] at hx; exact hnxi hx.symm
    · have hx : z.1 a = nx i := by rw [← he]; exact z.1.apply_symm_apply _
      rw [hp] at hx; exact hnxi hx.symm
  · have e1 : z.1.symm (nx i) = a := by rw [← hp]; exact z.1.symm_apply_apply a
    have hq : z.2 a = nx i := by rw [h2, hp]
    have e2 : z.2.symm (nx i) = a := by rw [← hq]; exact z.2.symm_apply_apply a
    rw [e1, e2]
    rintro (he | he)
    · have hx : z.1 a = i := by rw [← he]; exact z.1.apply_symm_apply _
      rw [hp] at hx; exact hnxi hx
    · have hx : z.2 a = i := by rw [he]; exact z.2.apply_symm_apply _
      rw [hq] at hx; exact hnxi hx

lemma absorbing (a : Fin n) (z : St n) (h : z.1 a = z.2 a) (i : Fin n) (hi : i ∈ Idx n)
    (c : Bool) : (step z i c).1 a = (step z i c).2 a := by
  have hi' : i.val + 1 < n := mem_Idx.1 hi
  rw [step_fst_apply, step_snd_apply]
  by_cases hin : z.1 a = i ∨ z.1 a = nx i
  · rw [sp_false_of_matched z a h i hi' hin, Bool.xor_false, h]
  · push_neg at hin
    rw [tau_fix hin.1 hin.2, tau_fix (show z.2 a ≠ i by rw [← h]; exact hin.1)
        (show z.2 a ≠ nx i by rw [← h]; exact hin.2)]
    simp [h]

lemma Cpl_row_sum (hn : 2 ≤ n) (z : St n) : ∑ w, Cpl n z w = 1 := by
  have h := sum_Cpl_mul (fun _ => (1:ℝ)) z
  simp only [mul_one] at h
  rw [h, Finset.sum_congr rfl (fun i (_ : i ∈ Idx n) => (by simp : (∑ _c : Bool, (1:ℝ)) = 2)),
    Finset.sum_const, nsmul_eq_mul, Idx_card_cast hn]
  have hd : ((n:ℝ) - 1) ≠ 0 := by have := two_le_cast hn; linarith
  field_simp

lemma Cpl_hcard_le (hn : 2 ≤ n) (a : Fin n) (z : St n) :
    ∑ w, Cpl n z w * hcard a w ≤ hcard a z := by
  by_cases h : z.1 a = z.2 a
  · have hz : hcard a z = 0 := by unfold hcard; rw [if_pos h]
    rw [hz, sum_Cpl_mul]
    have hall : ∀ i ∈ Idx n, (∑ c : Bool, hcard a (step z i c)) = 0 := by
      intro i hi
      refine Finset.sum_eq_zero fun c _ => ?_
      unfold hcard
      rw [if_pos (absorbing a z h i hi c)]
    rw [Finset.sum_congr rfl hall, Finset.sum_const_zero, zero_div]
  · have hz : hcard a z = 1 := by unfold hcard; rw [if_neg h]
    rw [hz]
    calc ∑ w, Cpl n z w * hcard a w ≤ ∑ w, Cpl n z w * 1 :=
          Finset.sum_le_sum fun w _ =>
            mul_le_mul_of_nonneg_left (hcard_le_one a w) (Cpl_nonneg hn z w)
      _ = 1 := by simp only [mul_one]; exact Cpl_row_sum hn z

lemma drift_all (hn : 2 ≤ n) (a : Fin n) (z : St n) :
    ∑ w, Cpl n z w * phi n (dcard a w) ≤ phi n (dcard a z) - hcard a z := by
  by_cases h : z.1 a = z.2 a
  · have hz : hcard a z = 0 := by unfold hcard; rw [if_pos h]
    have hd : dcard a z = 0 := by unfold dcard dv; rw [h]; omega
    rw [hz, hd, phi_zero, sub_zero, sum_Cpl_mul]
    have hall : ∀ i ∈ Idx n, (∑ c : Bool, phi n (dcard a (step z i c))) = 0 := by
      intro i hi
      refine Finset.sum_eq_zero fun c _ => ?_
      have hzz : dcard a (step z i c) = 0 := by
        unfold dcard dv; rw [absorbing a z h i hi c]; omega
      rw [hzz, phi_zero]
    rw [Finset.sum_congr rfl hall, Finset.sum_const_zero, zero_div]
  · have hz : hcard a z = 1 := by unfold hcard; rw [if_neg h]
    rw [hz]
    exact drift hn a z h

/-! ### Iterating -/

noncomputable def ap (n : ℕ) (t : ℕ) (F : St n → ℝ) (z : St n) : ℝ :=
  ∑ w, (Cpl n ^ t) z w * F w

lemma ap_zero (F : St n → ℝ) (z : St n) : ap n 0 F z = F z := by
  simp [ap, Matrix.one_apply, Finset.sum_ite_eq]

lemma ap_one (F : St n → ℝ) (z : St n) : ap n 1 F z = ∑ w, Cpl n z w * F w := by
  simp [ap]

lemma ap_mono (hn : 2 ≤ n) (t : ℕ) {F G : St n → ℝ} (h : ∀ z, F z ≤ G z) (z : St n) :
    ap n t F z ≤ ap n t G z :=
  Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (Cpl_pow_nonneg hn t z w)

lemma ap_nonneg (hn : 2 ≤ n) (t : ℕ) {F : St n → ℝ} (h : ∀ z, 0 ≤ F z) (z : St n) :
    0 ≤ ap n t F z :=
  Finset.sum_nonneg fun w _ => mul_nonneg (Cpl_pow_nonneg hn t z w) (h w)

lemma ap_sub (t : ℕ) (F G : St n → ℝ) (z : St n) :
    ap n t (fun w => F w - G w) z = ap n t F z - ap n t G z := by
  unfold ap
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun w _ => by ring

lemma ap_smul (t : ℕ) (c : ℝ) (F : St n → ℝ) (z : St n) :
    ap n t (fun w => c * F w) z = c * ap n t F z := by
  simp only [ap, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

lemma ap_comp (s t : ℕ) (F : St n → ℝ) (z : St n) :
    ap n (s + t) F z = ap n s (ap n t F) z := by
  simp only [ap]
  rw [pow_add]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma ap_finsum (t : ℕ) (F : Fin n → St n → ℝ) (z : St n) :
    ap n t (fun w => ∑ a, F a w) z = ∑ a, ap n t (F a) z := by
  simp only [ap, Finset.mul_sum]
  exact Finset.sum_comm

lemma phi_dcard_nonneg (hn : 2 ≤ n) (a : Fin n) (z : St n) : 0 ≤ phi n (dcard a z) := by
  have h : dcard a z ≤ n := by
    have h1 := (z.1 a).isLt; have h2 := (z.2 a).isLt
    unfold dcard dv; omega
  exact phi_nonneg hn h

lemma drift_iter (hn : 2 ≤ n) (a : Fin n) (t : ℕ) (z : St n) :
    ap n t (fun w => phi n (dcard a w)) z
      ≤ phi n (dcard a z) - ∑ s ∈ Finset.range t, ap n s (hcard a) z := by
  induction t generalizing z with
  | zero => simp [ap_zero]
  | succ t ih =>
      have hstep : ∀ v : St n, ap n 1 (fun w => phi n (dcard a w)) v
          ≤ phi n (dcard a v) - hcard a v := by
        intro v; rw [ap_one]; exact drift_all hn a v
      have h1 : ap n (t + 1) (fun w => phi n (dcard a w)) z
          = ap n t (ap n 1 (fun w => phi n (dcard a w))) z := ap_comp t 1 _ z
      rw [h1]
      have h2 : ap n t (ap n 1 (fun w => phi n (dcard a w))) z
          ≤ ap n t (fun v => phi n (dcard a v) - hcard a v) z := ap_mono hn t hstep z
      have h3 : ap n t (fun v => phi n (dcard a v) - hcard a v) z
          = ap n t (fun w => phi n (dcard a w)) z - ap n t (hcard a) z := ap_sub t _ _ z
      rw [Finset.sum_range_succ]
      linarith [ih z, h2, h3.le, h3.ge]

lemma ap_h_le (hn : 2 ≤ n) (a : Fin n) : ∀ (s : ℕ) (z : St n),
    ap n (s + 1) (hcard a) z ≤ ap n s (hcard a) z := by
  intro s z
  rw [ap_comp s 1]
  refine ap_mono hn s (fun v => ?_) z
  rw [ap_one]
  exact Cpl_hcard_le hn a v

lemma ap_h_anti (hn : 2 ≤ n) (a : Fin n) : ∀ {s t : ℕ}, s ≤ t → ∀ z : St n,
    ap n t (hcard a) z ≤ ap n s (hcard a) z := by
  intro s t
  induction t with
  | zero => intro h z; have hs : s = 0 := Nat.le_zero.1 h; subst hs; exact le_refl _
  | succ t ih =>
      intro hst z
      rcases Nat.lt_or_ge s (t + 1) with h | h
      · exact le_trans (ap_h_le hn a t z) (ih (Nat.lt_succ_iff.1 h) z)
      · have hs : s = t + 1 := le_antisymm hst h
        subst hs; exact le_refl _

lemma ap_h_markov (hn : 2 ≤ n) (a : Fin n) (t : ℕ) (z : St n) :
    (t:ℝ) * ap n t (hcard a) z ≤ phi n (n - 1) := by
  have hlow : ∀ s ∈ Finset.range t, ap n t (hcard a) z ≤ ap n s (hcard a) z := by
    intro s hs
    exact ap_h_anti hn a (le_of_lt (Finset.mem_range.1 hs)) z
  have h1 : (t:ℝ) * ap n t (hcard a) z ≤ ∑ s ∈ Finset.range t, ap n s (hcard a) z := by
    have := Finset.sum_le_sum hlow
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  have h2 : ∑ s ∈ Finset.range t, ap n s (hcard a) z ≤ phi n (dcard a z) := by
    have h3 := drift_iter hn a t z
    have h4 : 0 ≤ ap n t (fun w => phi n (dcard a w)) z :=
      ap_nonneg hn t (fun w => phi_dcard_nonneg hn a w) z
    linarith
  have h5 : phi n (dcard a z) ≤ phi n (n - 1) := by
    refine phi_mono hn ?_ (by omega)
    have h1' := (z.1 a).isLt; have h2' := (z.2 a).isLt
    unfold dcard dv; omega
  linarith

lemma ap_block (hn : 2 ≤ n) (a : Fin n) (z : St n) :
    ap n (n ^ 3) (hcard a) z ≤ (1/2) * hcard a z := by
  have hn' := two_le_cast hn
  have hmk := ap_h_markov hn a (n ^ 3) z
  have hcast : ((n ^ 3 : ℕ) : ℝ) = (n:ℝ) ^ 3 := by push_cast; ring
  rw [hcast] at hmk
  have hphi : phi n (n - 1) = (n:ℝ) * ((n:ℝ) - 1) ^ 2 / 2 := by
    have hc : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
      have h1 : (1:ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub h1]; ring
    unfold phi
    rw [hc]
    ring
  rw [hphi] at hmk
  have h3 : (0:ℝ) < (n:ℝ) ^ 3 := by positivity
  have hbase : ap n (n ^ 3) (hcard a) z ≤ 1 / 2 := by
    have hstep : (n:ℝ) ^ 3 * ap n (n ^ 3) (hcard a) z ≤ (n:ℝ) ^ 3 * (1/2) := by
      refine le_trans hmk ?_
      nlinarith [hn', mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ)) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2)]
    exact le_of_mul_le_mul_left hstep h3
  have hle : ap n (n ^ 3) (hcard a) z ≤ hcard a z := by
    have := ap_h_anti hn a (Nat.zero_le (n ^ 3)) z
    rwa [ap_zero] at this
  have hpos : 0 ≤ ap n (n ^ 3) (hcard a) z :=
    ap_nonneg hn _ (fun w => hcard_nonneg a w) z
  by_cases h : z.1 a = z.2 a
  · have hz : hcard a z = 0 := by unfold hcard; rw [if_pos h]
    rw [hz] at hle ⊢
    linarith
  · have hz : hcard a z = 1 := by unfold hcard; rw [if_neg h]
    rw [hz]
    linarith

lemma ap_blocks (hn : 2 ≤ n) (a : Fin n) : ∀ (m : ℕ) (z : St n),
    ap n (m * n ^ 3) (hcard a) z ≤ (1/2 : ℝ) ^ m * hcard a z := by
  intro m
  induction m with
  | zero => intro z; simp [ap_zero]
  | succ m ih =>
      intro z
      have hidx : (m + 1) * n ^ 3 = m * n ^ 3 + n ^ 3 := by ring
      rw [hidx, ap_comp (m * n ^ 3) (n ^ 3)]
      have h1 : ap n (m * n ^ 3) (ap n (n ^ 3) (hcard a)) z
          ≤ ap n (m * n ^ 3) (fun v => (1/2 : ℝ) * hcard a v) z :=
        ap_mono hn _ (fun v => ap_block hn a v) z
      have h2 : ap n (m * n ^ 3) (fun v => (1/2 : ℝ) * hcard a v) z
          = (1/2 : ℝ) * ap n (m * n ^ 3) (hcard a) z := ap_smul _ _ _ z
      have h3 := ih z
      have h4 : (0:ℝ) ≤ (1/2 : ℝ) := by norm_num
      calc ap n (m * n ^ 3) (ap n (n ^ 3) (hcard a)) z
          ≤ (1/2 : ℝ) * ap n (m * n ^ 3) (hcard a) z := by rw [← h2]; exact h1
        _ ≤ (1/2 : ℝ) * ((1/2 : ℝ) ^ m * hcard a z) := by
              exact mul_le_mul_of_nonneg_left h3 h4
        _ = (1/2 : ℝ) ^ (m + 1) * hcard a z := by ring

lemma neq_le_sum (z : St n) : (if z.1 = z.2 then (0:ℝ) else 1) ≤ ∑ a, hcard a z := by
  by_cases h : z.1 = z.2
  · rw [if_pos h]
    exact Finset.sum_nonneg fun a _ => hcard_nonneg a z
  · rw [if_neg h]
    obtain ⟨a, ha⟩ : ∃ a, z.1 a ≠ z.2 a := by
      by_contra hc
      push_neg at hc
      exact h (Equiv.ext hc)
    have h1 : (1:ℝ) = hcard a z := by unfold hcard; rw [if_neg ha]
    rw [h1]
    exact Finset.single_le_sum (fun b _ => hcard_nonneg b z) (Finset.mem_univ a)

lemma final_bound (hn : 2 ≤ n) (m : ℕ) (z : St n) :
    ∑ w, (Cpl n ^ (m * n ^ 3)) z w * (if w.1 = w.2 then (0:ℝ) else 1)
      ≤ (n:ℝ) * (1/2 : ℝ) ^ m := by
  have h0 : ∑ w, (Cpl n ^ (m * n ^ 3)) z w * (if w.1 = w.2 then (0:ℝ) else 1)
      = ap n (m * n ^ 3) (fun w => if w.1 = w.2 then (0:ℝ) else 1) z := rfl
  rw [h0]
  calc ap n (m * n ^ 3) (fun w => if w.1 = w.2 then (0:ℝ) else 1) z
      ≤ ap n (m * n ^ 3) (fun w => ∑ a, hcard a w) z :=
        ap_mono hn _ (fun w => neq_le_sum w) z
    _ = ∑ a, ap n (m * n ^ 3) (hcard a) z := ap_finsum _ _ z
    _ ≤ ∑ _a : Fin n, (1/2 : ℝ) ^ m := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine le_trans (ap_blocks hn a m z) ?_
        have : hcard a z ≤ 1 := hcard_le_one a z
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) m]
    _ = (n:ℝ) * (1/2 : ℝ) ^ m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The main estimate -/

theorem main (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hnε : 2 / (n:ℝ) ≤ ε) :
    (mixingTime (Pw n) (uniformDist (Pm n)) ε : ℝ) ≤ 2 * (n:ℝ) ^ 3 * Real.logb 2 n := by
  have hn' := two_le_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hlogpos : 0 ≤ 2 * Real.logb 2 (n:ℝ) := by
    have : (1:ℝ) ≤ (n:ℝ) := by linarith
    have := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) this
    linarith
  set m := ⌊2 * Real.logb 2 (n:ℝ)⌋₊ with hm
  have hm_le : (m:ℝ) ≤ 2 * Real.logb 2 (n:ℝ) := Nat.floor_le hlogpos
  have hm_gt : 2 * Real.logb 2 (n:ℝ) < (m:ℝ) + 1 := by
    have := Nat.lt_floor_add_one (2 * Real.logb 2 (n:ℝ))
    rw [← hm] at this
    push_cast at this ⊢
    linarith
  have hkey : (n:ℝ) ^ 2 / 2 < (2:ℝ) ^ m := by
    have h1 : (2:ℝ) ^ (2 * Real.logb 2 (n:ℝ) - 1) < (2:ℝ) ^ ((m:ℝ)) := by
      exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).2 (by linarith)
    have h2 : (2:ℝ) ^ (2 * Real.logb 2 (n:ℝ) - 1) = (n:ℝ) ^ 2 / 2 := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]
      congr 1
      rw [show (2:ℝ) * Real.logb 2 (n:ℝ) = Real.logb 2 (n:ℝ) * 2 by ring,
        Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hnpos,
        show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.rpow_natCast] at h1
    rw [← h2]
    exact h1
  have h2m : (0:ℝ) < (2:ℝ) ^ m := by positivity
  have hpow : (n:ℝ) * (1/2 : ℝ) ^ m ≤ ε := by
    have hq : (1/2 : ℝ) ^ m = 1 / (2:ℝ) ^ m := by rw [div_pow, one_pow]
    have h1 : (n:ℝ) * (1/2 : ℝ) ^ m * (n:ℝ) = ((n:ℝ) * (n:ℝ)) / (2:ℝ) ^ m := by
      rw [hq, mul_one_div, div_mul_eq_mul_div]
    have h2 : (n:ℝ) * (1/2 : ℝ) ^ m ≤ 2 / (n:ℝ) := by
      rw [le_div_iff₀ hnpos, h1, div_le_iff₀ h2m]
      nlinarith [hkey]
    linarith
  have hd : distStationary (Pw n) (uniformDist (Pm n)) (m * n ^ 3) ≤ ε :=
    dstat_le hn _ ε (le_of_lt hε) (fun z => le_trans (final_bound hn m z) hpow)
  have hmix : mixingTime (Pw n) (uniformDist (Pm n)) ε ≤ m * n ^ 3 := Nat.sInf_le hd
  have hcast : ((mixingTime (Pw n) (uniformDist (Pm n)) ε : ℕ) : ℝ) ≤ ((m * n ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hmix
  refine le_trans hcast ?_
  have hc2 : ((m * n ^ 3 : ℕ) : ℝ) = (m:ℝ) * (n:ℝ) ^ 3 := by push_cast; ring
  rw [hc2]
  calc (m:ℝ) * (n:ℝ) ^ 3 ≤ (2 * Real.logb 2 (n:ℝ)) * (n:ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_right hm_le (by positivity)
    _ = 2 * (n:ℝ) ^ 3 * Real.logb 2 (n:ℝ) := by ring

end AdjT

open MarkovMixing in
theorem solution (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (mixingTime (groupWalk (adjacentTranspositionDist n))
        (uniformDist (Equiv.Perm (Fin n))) ε : ℝ) ≤
        2 * (n : ℝ) ^ 3 * Real.logb 2 n := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 / ε)
  refine ⟨max 2 N0, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N0 ≤ n := le_trans (le_max_right _ _) hn
  have hge : 2 / ε ≤ (n:ℝ) := le_trans (le_of_lt hN0) (by exact_mod_cast hnN)
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
    linarith
  have hnε : 2 / (n:ℝ) ≤ ε := by
    rw [div_le_iff₀ hnpos]
    rw [div_le_iff₀ hε] at hge
    linarith
  exact AdjT.main hn2 ε hε hnε
