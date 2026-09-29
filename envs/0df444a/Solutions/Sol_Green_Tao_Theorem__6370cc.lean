-- Prove2me | solution 1 for Green_Tao_Theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-06T02:04:44.507056+00:00
-- url     : https://prove2.me/submissions/09803535-bec3-4261-a0ac-e2a6cfe30a11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Theorems.Thm_GreenTao_relative_szemeredi
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
    GreenTao.relative_szemeredi k hk M hprime hM ν f hν hf δ hδ hδ₁ hdensity
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
