-- Prove2me | solution 2 for Green_Tao_Theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-06T02:16:29.32184+00:00
-- url     : https://prove2.me/submissions/92398f8d-fd02-45e9-81bd-8de0cf8c6029
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Theorems.Thm_GreenTao_varnavides_set_count
import Theorems.Thm_GreenTao_bounded_model_for_progression_counts
import Theorems.Thm_GreenTao_prime_majorant_package

namespace GreenTaoDM

def IsAPOfLengthWithDM (s : Set ℕ) (l : ℕ∞) (a d : ℕ) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < l)}

def IsAPOfLengthDM (s : Set ℕ) (l : ℕ∞) : Prop := ∃ a d : ℕ, IsAPOfLengthWithDM s l a d

def primeArithmeticProgressionsDM : Set (Set ℕ) :=
  {s | (∀ p ∈ s, p.Prime) ∧ ∃ l > (0 : ℕ∞), IsAPOfLengthDM s l}

end GreenTaoDM

open scoped BigOperators Topology
open Filter GreenTao GreenTaoDM

private lemma uniform_avg_mono {α : Type} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

private lemma progression_avg_mono {m : ℕ+} (k : ℕ)
    {f g : ZMod (m : ℕ) → ℝ} (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    apAvg k f ≤ apAvg k g := by
  apply uniform_avg_mono
  intro x
  apply uniform_avg_mono
  intro r
  exact Finset.prod_le_prod (fun j _ => hf _) (fun j _ => hfg _)

private lemma progression_avg_scale {m : ℕ+} (k : ℕ)
    (c : ℝ) (f : ZMod (m : ℕ) → ℝ) :
    apAvg k (fun x => c * f x) = c ^ k * apAvg k f := by
  simp only [apAvg, avg, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
  ring

/-- Thresholding at half the mean converts a set-count bound into a weighted bound. -/
private lemma bounded_weighted_szemeredi
    (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ,
      ∀ (m : ℕ+) (_ : Nat.Prime (m : ℕ)) (_ : B ≤ (m : ℕ))
        (g : ZMod (m : ℕ) → ℝ),
        (∀ x, 0 ≤ g x ∧ g x ≤ 1) → δ ≤ avg g → c ≤ apAvg k g := by
  classical
  have ht : 0 < δ / 2 := by positivity
  obtain ⟨c, hc, B, hsets⟩ := GreenTao.varnavides_set_count k hk (δ / 2) ht (by linarith)
  refine ⟨(δ / 2) ^ k * c, mul_pos (pow_pos ht _) hc, B, ?_⟩
  intro m hm hB g hg hmean
  let A : Finset (ZMod (m : ℕ)) := Finset.univ.filter fun x => δ / 2 ≤ g x
  let indicator : ZMod (m : ℕ) → ℝ := fun x => if x ∈ A then 1 else 0
  have hmem (x : ZMod (m : ℕ)) : x ∈ A ↔ δ / 2 ≤ g x := by simp [A]
  have hsum_indicator : (∑ x, indicator x) = (A.card : ℝ) := by simp [indicator]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.pos
  have hpoint (x : ZMod (m : ℕ)) : g x ≤ δ / 2 + indicator x := by
    by_cases hx : x ∈ A
    · simp only [indicator, if_pos hx]
      linarith [(hg x).2]
    · have hx' : g x < δ / 2 := lt_of_not_ge ((hmem x).not.mp hx)
      simpa [indicator, hx] using hx'.le
  have hsum_upper : (∑ x, g x) ≤ δ / 2 * (m : ℝ) + (A.card : ℝ) := by
    calc
      _ ≤ ∑ x, (δ / 2 + indicator x) := Finset.sum_le_sum fun x _ => hpoint x
      _ = _ := by rw [Finset.sum_add_distrib, hsum_indicator]; simp [ZMod.card, mul_comm]
  have havg : avg g = (∑ x, g x) / (m : ℝ) := by
    simp [avg, ZMod.card, div_eq_mul_inv, mul_comm]
  have hsum_lower : δ * (m : ℝ) ≤ ∑ x, g x := by
    rwa [havg, le_div_iff₀ hmpos] at hmean
  have hdensity : δ / 2 * (m : ℝ) ≤ (A.card : ℝ) := by linarith
  have hcount : c ≤ apAvg k indicator := hsets m hm hB A hdensity
  have hnonneg (x : ZMod (m : ℕ)) : 0 ≤ δ / 2 * indicator x := by
    dsimp [indicator]
    split_ifs <;> positivity
  have hbelow (x : ZMod (m : ℕ)) : δ / 2 * indicator x ≤ g x := by
    by_cases hx : x ∈ A
    · simpa [indicator, hx] using (hmem x).mp hx
    · simpa [indicator, hx] using (hg x).1
  calc
    (δ / 2) ^ k * c ≤ (δ / 2) ^ k * apAvg k indicator :=
      mul_le_mul_of_nonneg_left hcount (pow_nonneg ht.le _)
    _ = apAvg k (fun x => δ / 2 * indicator x) := (progression_avg_scale k _ _).symm
    _ ≤ apAvg k g := progression_avg_mono k hnonneg hbelow

private lemma relative_szemeredi_from_models
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (ν f : GreenTao.Family M) (hν : GreenTao.Pseudorandom k M ν)
    (hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x)
    (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hdensity : ∀ᶠ n in atTop, δ ≤ GreenTao.avg (f n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ GreenTao.apAvg k (f n) := by
  obtain ⟨c, hc, B, hweighted⟩ :=
    bounded_weighted_szemeredi k hk (δ / 2) (by positivity) (by linarith)
  let η := min (δ / 2) (c / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hmodel := GreenTao.bounded_model_for_progression_counts k hk M hprime hM ν f hν hf η hη
  have hlarge : ∀ᶠ n in atTop, B ≤ (M n : ℕ) := hM.eventually (eventually_ge_atTop B)
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hdensity, hmodel, hlarge] with n hnmean hnmodel hnlarge
  obtain ⟨g, hg, hgmean, hgcount⟩ := hnmodel
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  have hηc : η ≤ c / 2 := min_le_right _ _
  have hgdensity : δ / 2 ≤ avg g := by linarith
  have hpositive := hweighted (M n) (hprime n) hnlarge g hg hgdensity
  linarith


private lemma avg_mono {α : Type} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- A count larger than its diagonal contains a positive nonconstant progression. -/
private lemma nonzero_progression {m : ℕ+} (k : ℕ) (f : ZMod (m : ℕ) → ℝ)
    (h : diagonalAvg k f < apAvg k f) :
    ∃ x r : ZMod (m : ℕ), r ≠ 0 ∧
      0 < ∏ j : Fin k, f (x + (j.val : ZMod (m : ℕ)) * r) := by
  classical
  by_contra hn
  push Not at hn
  have hsum (x : ZMod (m : ℕ)) :
      (∑ r : ZMod (m : ℕ), ∏ j : Fin k, f (x + (j.val : ZMod (m : ℕ)) * r)) ≤
        f x ^ k := by
    calc
      _ ≤ ∑ r : ZMod (m : ℕ), if r = 0 then f x ^ k else 0 := by
        apply Finset.sum_le_sum
        intro r _
        by_cases hr : r = 0
        · simp [hr]
        · simpa [hr] using hn x r hr
      _ = _ := by simp
  have hbound : apAvg k f ≤ avg (fun x => (m : ℝ)⁻¹ * f x ^ k) := by
    apply avg_mono
    intro x
    simpa [avg, ZMod.card] using
      mul_le_mul_of_nonneg_left (hsum x) (inv_nonneg.mpr (show (0 : ℝ) ≤ m by positivity))
  have heq : avg (fun x => (m : ℝ)⁻¹ * f x ^ k) = diagonalAvg k f := by
    simp [avg, diagonalAvg, div_eq_mul_inv, Finset.mul_sum, mul_left_comm, mul_comm]
  exact (not_lt_of_ge (heq ▸ hbound)) h

/-- A finite natural sequence with vanishing second differences can be oriented
as an increasing arithmetic progression. -/
private lemma orient_progression (k : ℕ) (hk : 2 ≤ k) (y : ℕ → ℕ) (P : ℕ → Prop)
    (hP : ∀ j < k, P (y j)) (hne : y 0 ≠ y 1)
    (hrec : ∀ j, j + 2 < k → y j + y (j + 2) = 2 * y (j + 1)) :
    ∃ a d : ℕ, 0 < d ∧ ∀ j < k, P (a + j * d) := by
  have hlinear (j : ℕ) : j < k →
      (y j : ℤ) = (y 0 : ℤ) + (j : ℤ) * ((y 1 : ℤ) - (y 0 : ℤ)) := by
    induction j using Nat.twoStepInduction with
    | zero => intro _; simp
    | one => intro _; simp
    | more j ih₀ ih₁ =>
      intro hj
      have he : (y j : ℤ) + (y (j + 2) : ℤ) = 2 * (y (j + 1) : ℤ) := by
        exact_mod_cast hrec j hj
      have hi₀ := ih₀ (by omega)
      have hi₁ := ih₁ (by omega)
      push_cast at hi₁ ⊢
      nlinarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨y 0, y 1 - y 0, Nat.sub_pos_of_lt hlt, ?_⟩
    intro j hj
    have heq : y 0 + j * (y 1 - y 0) = y j := by
      have hs : ((y 1 - y 0 : ℕ) : ℤ) = (y 1 : ℤ) - (y 0 : ℤ) := by omega
      zify
      rw [hs]
      exact (hlinear j hj).symm
    rw [heq]
    exact hP j hj
  · refine ⟨y (k - 1), y 0 - y 1, Nat.sub_pos_of_lt hgt, ?_⟩
    intro j hj
    have hi : k - 1 - j < k := by omega
    have hlast : k - 1 < k := by omega
    have heq : y (k - 1) + j * (y 0 - y 1) = y (k - 1 - j) := by
      have hs : ((y 0 - y 1 : ℕ) : ℤ) = (y 0 : ℤ) - (y 1 : ℤ) := by omega
      have hind : ((k - 1 - j : ℕ) : ℤ) + (j : ℤ) = ((k - 1 : ℕ) : ℤ) := by omega
      have h₁ := hlinear (k - 1) hlast
      have h₂ := hlinear (k - 1 - j) hi
      zify
      rw [hs]
      nlinarith
    rw [heq]
    exact hP _ hi

/-- Progressions supported below half the modulus lift to natural progressions;
reversing the order handles a negative lifted common difference. -/
private lemma lift_progression {m : ℕ+} (k : ℕ) (hk : 3 ≤ k)
    (x r : ZMod (m : ℕ)) (hr : r ≠ 0) (P : ℕ → Prop)
    (hP : ∀ j < k, P (x + (j : ZMod (m : ℕ)) * r).val)
    (hshort : ∀ j < k, 2 * (x + (j : ZMod (m : ℕ)) * r).val < (m : ℕ)) :
    ∃ a d : ℕ, 0 < d ∧ ∀ j < k, P (a + j * d) := by
  let y : ℕ → ℕ := fun j => (x + (j : ZMod (m : ℕ)) * r).val
  apply orient_progression k (by omega) y P hP
  · intro heq
    have he : x = x + r := by
      apply ZMod.val_injective
      simpa [y] using heq
    apply hr
    linear_combination -he
  · intro j hj
    have h₀ := hshort j (by omega)
    have h₁ := hshort (j + 1) (by omega)
    have h₂ := hshort (j + 2) hj
    have he : ((y j + y (j + 2) : ℕ) : ZMod (m : ℕ)) =
        ((2 * y (j + 1) : ℕ) : ZMod (m : ℕ)) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, y, ZMod.natCast_zmod_val]
      push_cast
      ring
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (show y j + y (j + 2) < (m : ℕ) by dsimp [y]; omega),
      ZMod.val_natCast_of_lt (show 2 * y (j + 1) < (m : ℕ) from h₁)] at hv
    exact hv

private lemma prime_progression (k : ℕ) (hk : 3 ≤ k) :
    ∃ a d : ℕ, 0 < d ∧ ∀ j < k, Nat.Prime (a + j * d) := by
  classical
  obtain ⟨M, W, ν, f, δ, hprime, hM, hW, hν, hf, hδ, hδ₁, hdensity, hdiag, hsupp⟩ :=
    GreenTao.prime_majorant_package k hk
  obtain ⟨c, hc, hcount⟩ :=
    relative_szemeredi_from_models k hk M hprime hM ν f hν hf δ hδ hδ₁ hdensity
  have hsmall : ∀ᶠ n in atTop, diagonalAvg k (f n) < c :=
    hdiag.eventually (gt_mem_nhds hc)
  obtain ⟨n, hncount, hnsmall⟩ := (hcount.and hsmall).exists
  obtain ⟨x, r, hr, hprod⟩ :=
    nonzero_progression k (f n) (lt_of_lt_of_le hnsmall hncount)
  have hpositive (j : ℕ) (hj : j < k) :
      0 < f n (x + (j : ZMod (M n : ℕ)) * r) := by
    have hne := (Finset.prod_ne_zero_iff.mp (ne_of_gt hprod)) ⟨j, hj⟩ (Finset.mem_univ _)
    exact lt_of_le_of_ne (hf n _).1 (Ne.symm hne)
  obtain ⟨a, d, hd, hAP⟩ := lift_progression k hk x r hr
    (fun z => Nat.Prime (W n * z + 1))
    (fun j hj => (hsupp n _ (hpositive j hj)).1)
    (fun j hj => (hsupp n _ (hpositive j hj)).2)
  refine ⟨W n * a + 1, W n * d, Nat.mul_pos (hW n) hd, ?_⟩
  intro j hj
  convert hAP j hj using 1
  ring

theorem solution :
    ∀ N : ℕ, ∃ s ∈ primeArithmeticProgressionsDM, (N : ℕ∞) ≤ ENat.card s := by
  intro N
  let k := N + 3
  obtain ⟨a, d, hd, hp⟩ := prime_progression k (by dsimp [k]; omega)
  let g : Fin k → ℕ := fun j => a + j.val * d
  have hg : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have hmul : i.val * d = j.val * d := Nat.add_left_cancel hij
    exact Nat.eq_of_mul_eq_mul_right hd hmul
  let s : Set ℕ := Set.range g
  have hcard : ENat.card s = (k : ℕ∞) := by
    rw [ENat.card_congr (Equiv.ofInjective g hg).symm]
    simp
  refine ⟨s, ?_, ?_⟩
  · change (∀ p ∈ s, p.Prime) ∧ ∃ l > (0 : ℕ∞), IsAPOfLengthDM s l
    refine ⟨?_, (k : ℕ∞), ?_, a, d, hcard, ?_⟩
    · rintro p ⟨j, rfl⟩
      exact hp j.val j.isLt
    · exact_mod_cast (show 0 < k by dsimp [k]; omega)
    · ext p
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j.val, by exact_mod_cast j.isLt, by simp [g]⟩
      · rintro ⟨j, hj, rfl⟩
        refine ⟨⟨j, by exact_mod_cast hj⟩, ?_⟩
        simp [g]
  · rw [hcard]
    exact_mod_cast (show N ≤ k by dsimp [k]; omega)
