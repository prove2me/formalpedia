-- Prove2me | solution 1 for MarkovMixing.sep_tv_relation
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:22:35.620154+00:00
-- url     : https://prove2.me/submissions/fc3fb7bb-59d5-4406-a3fe-2414e34963d9

import Definitions.Def_mm_cutoff
import Theorems.Thm_MarkovMixing_exists_stationary_pos
import Theorems.Thm_MarkovMixing_stationary_unique
import Theorems.Thm_MarkovMixing_tv_eq_half_l1

/-!
# Separation after `2t` steps from pairwise total variation after `t`

For a reversible chain, `π(z) P^t(z,y) = π(y) P^t(y,z)`, so

`P^{2t}(x,y)/π(y) = ∑_z P^t(x,z) P^t(y,z) / π(z)`.

Cauchy–Schwarz in the form `sum_sq_le_sum_mul_sum_of_sq_le_mul`, applied with
`r(z) = min(P^t(x,z), P^t(y,z))`, `f(z) = P^t(x,z)P^t(y,z)/π(z)` and `g = π`
(the hypothesis `r² ≤ f g` being `min(a,b)² ≤ ab`), bounds the square of
`∑_z min(P^t(x,z),P^t(y,z)) = 1 − ‖P^t(x,·) − P^t(y,·)‖_TV` by that sum.
Since the total variation is at most `d̄(t) ≤ 1`, this gives
`P^{2t}(x,y)/π(y) ≥ (1 − d̄(t))²` for all `x,y`, which is the claim after
taking suprema.
-/

namespace MarkovMixing

open scoped BigOperators

private lemma pow_isStochastic {V : Type*} [Fintype V] [DecidableEq V]
    {P : Matrix V V ℝ} (hP : IsStochastic P) (t : ℕ) : IsStochastic (P ^ t) := by
  induction t with
  | zero =>
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · by_cases h : x = y <;> simp [Matrix.one_apply, h]
      · simp [Matrix.one_apply]
  | succ n ih =>
      rw [pow_succ]
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · simp only [Matrix.mul_apply]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih.1 x z) (hP.1 z y)
      · simp only [Matrix.mul_apply]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hP.2, mul_one]
        exact ih.2 x

private lemma rev_pow {V : Type*} [Fintype V] [DecidableEq V] {P : Matrix V V ℝ}
    {π : V → ℝ} (hrev : DetailedBalance P π) (t : ℕ) :
    ∀ x y : V, π x * ((P ^ t) x y) = π y * ((P ^ t) y x) := by
  induction t with
  | zero =>
      intro x y
      by_cases h : x = y
      · subst h; rfl
      · simp [Matrix.one_apply, h, Ne.symm h]
  | succ n ih =>
      intro x y
      calc π x * ((P ^ (n + 1)) x y)
          = ∑ z : V, (π x * (P ^ n) x z) * P z y := by
            rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
        _ = ∑ z : V, (π z * (P ^ n) z x) * P z y :=
            Finset.sum_congr rfl fun z _ => by rw [ih x z]
        _ = ∑ z : V, (π y * P y z) * (P ^ n) z x := by
            refine Finset.sum_congr rfl fun z _ => ?_
            have hb := hrev z y
            calc (π z * (P ^ n) z x) * P z y = (π z * P z y) * (P ^ n) z x := by ring
              _ = (π y * P y z) * (P ^ n) z x := by rw [hb]
        _ = π y * ((P ^ (n + 1)) y x) := by
            rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring

private lemma tvDist_le_one {V : Type*} [Fintype V] [DecidableEq V] {μ ν : V → ℝ}
    (hμ : IsDist μ) (hν : IsDist ν) : tvDist μ ν ≤ 1 := by
  refine ciSup_le fun A => ?_
  have hμ1 : ∑ x ∈ A, μ x ≤ 1 := by
    rw [← hμ.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun x _ _ => hμ.1 x)
  have hν1 : ∑ x ∈ A, ν x ≤ 1 := by
    rw [← hν.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun x _ _ => hν.1 x)
  have hμ0 : 0 ≤ ∑ x ∈ A, μ x := Finset.sum_nonneg fun x _ => hμ.1 x
  have hν0 : 0 ≤ ∑ x ∈ A, ν x := Finset.sum_nonneg fun x _ => hν.1 x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma sum_min_eq {V : Type*} [Fintype V] [DecidableEq V] {μ ν : V → ℝ}
    (hμ : IsDist μ) (hν : IsDist ν) :
    ∑ x : V, min (μ x) (ν x) = 1 - tvDist μ ν := by
  have h := (tv_eq_half_l1 μ ν hμ hν).1
  have h2 : ∑ x : V, |μ x - ν x| = 2 * tvDist μ ν := by rw [h]; ring
  have hmin : ∀ x : V, min (μ x) (ν x) = 2⁻¹ * (μ x + ν x - |μ x - ν x|) := by
    intro x
    rcases le_total (μ x) (ν x) with hle | hle
    · rw [min_eq_left hle, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right hle, abs_of_nonneg (by linarith)]; ring
  have hsum : ∑ x : V, (μ x + ν x - |μ x - ν x|) = 2 - 2 * tvDist μ ν := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hμ.2, hν.2, h2]
    ring
  simp only [hmin, ← Finset.mul_sum]
  rw [hsum]
  ring

private lemma key {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hpos : ∀ z : V, 0 < π z) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (t : ℕ) (x y : V) :
    (1 - distPairs P t) ^ 2 ≤ ((P ^ (2 * t)) x y) / π y := by
  have hPt : IsStochastic (P ^ t) := pow_isStochastic hP t
  have hdx : IsDist (rowDist P t x) := ⟨fun z => hPt.1 x z, hPt.2 x⟩
  have hdy : IsDist (rowDist P t y) := ⟨fun z => hPt.1 y z, hPt.2 y⟩
  have hsplit : (P ^ (2 * t)) x y = ∑ z : V, (P ^ t) x z * (P ^ t) z y := by
    rw [two_mul, pow_add, Matrix.mul_apply]
  have hzy : ∀ z : V, (P ^ t) z y = π y * (P ^ t) y z / π z := by
    intro z
    have h := rev_pow hrev t z y
    have hz : π z ≠ 0 := ne_of_gt (hpos z)
    field_simp
    linarith [h]
  have hval : (P ^ (2 * t)) x y = π y * ∑ z : V, (P ^ t) x z * (P ^ t) y z / π z := by
    rw [hsplit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hzy z]
    ring
  have hdiv : (P ^ (2 * t)) x y / π y = ∑ z : V, (P ^ t) x z * (P ^ t) y z / π z := by
    rw [hval, mul_comm, mul_div_assoc, div_self (ne_of_gt (hpos y)), mul_one]
  have hcs : (∑ z : V, min ((P ^ t) x z) ((P ^ t) y z)) ^ 2
      ≤ (∑ z : V, (P ^ t) x z * (P ^ t) y z / π z) * (∑ z : V, π z) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ?_ ?_ ?_
    · intro z _
      exact div_nonneg (mul_nonneg (hPt.1 x z) (hPt.1 y z)) (le_of_lt (hpos z))
    · intro z _
      exact le_of_lt (hpos z)
    · intro z _
      have hz : π z ≠ 0 := ne_of_gt (hpos z)
      have hprod : (P ^ t) x z * (P ^ t) y z / π z * π z
          = (P ^ t) x z * (P ^ t) y z := by field_simp
      rw [hprod]
      rcases le_total ((P ^ t) x z) ((P ^ t) y z) with h | h
      · rw [min_eq_left h, sq]
        exact mul_le_mul_of_nonneg_left h (hPt.1 x z)
      · rw [min_eq_right h, sq]
        exact mul_le_mul_of_nonneg_right h (hPt.1 y z)
  rw [hπ.1.2, mul_one] at hcs
  have hmin2 : ∑ z : V, min ((P ^ t) x z) ((P ^ t) y z)
      = 1 - tvDist (rowDist P t x) (rowDist P t y) := sum_min_eq hdx hdy
  have hdle : tvDist (rowDist P t x) (rowDist P t y) ≤ distPairs P t :=
    le_ciSup (f := fun p : V × V => tvDist (rowDist P t p.1) (rowDist P t p.2))
      (Set.Finite.bddAbove (Set.finite_range _)) (x, y)
  have hd1 : distPairs P t ≤ 1 := by
    refine ciSup_le fun p => ?_
    exact tvDist_le_one ⟨fun z => hPt.1 p.1 z, hPt.2 p.1⟩ ⟨fun z => hPt.1 p.2 z, hPt.2 p.2⟩
  have h1d : 0 ≤ 1 - distPairs P t := by linarith
  have hle : 1 - distPairs P t ≤ ∑ z : V, min ((P ^ t) x z) ((P ^ t) y z) := by
    rw [hmin2]; linarith
  have hsq : (1 - distPairs P t) ^ 2
      ≤ (∑ z : V, min ((P ^ t) x z) ((P ^ t) y z)) ^ 2 := by nlinarith
  rw [hdiv]
  linarith

end MarkovMixing

open MarkovMixing

/-- **Lemma 19.3** (LPW): separation after `2t` steps is controlled by the
pairwise total-variation distance after `t` steps. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (t : ℕ) :
    sepSup P π (2 * t) ≤ 1 - (1 - distPairs P t) ^ 2 := by
  obtain ⟨π₀, hπ₀, hpos₀, _⟩ := exists_stationary_pos P hP hirr
  have hEq : π = π₀ := stationary_unique P hP hirr π π₀ hπ hπ₀
  have hpos : ∀ z : V, 0 < π z := by rw [hEq]; exact hpos₀
  simp only [sepSup, sepDist]
  refine ciSup_le fun x => ?_
  refine ciSup_le fun y => ?_
  have hk := key P hP π hpos hπ hrev t x y
  linarith
