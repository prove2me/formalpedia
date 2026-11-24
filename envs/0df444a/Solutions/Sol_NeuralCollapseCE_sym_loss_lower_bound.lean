-- Prove2me | solution 1 for NeuralCollapseCE.sym_loss_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:20:56.671267+00:00
-- url     : https://prove2.me/submissions/c8bb2473-0159-4d16-a495-5f48be5f1bc2

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic
set_option autoImplicit false
open MeasureTheory Filter Topology Asymptotics
open NeuralCollapseCE

/-- `y ↦ log (1 + c eʸ)` is convex for `c > 0`: its derivative `c eʸ / (1 + c eʸ)` is monotone. -/
private lemma sp_convex (c : ℝ) (hc : 0 < c) :
    ConvexOn ℝ Set.univ (fun y : ℝ => Real.log (1 + c * Real.exp y)) := by
  have hpos : ∀ y : ℝ, 0 < 1 + c * Real.exp y := fun y => by positivity
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.log (1 + c * Real.exp y))
      (c * Real.exp y / (1 + c * Real.exp y)) y := fun y => by
    have := (((Real.hasDerivAt_exp y).const_mul c).const_add 1).log (hpos y).ne'
    simpa using this
  apply Monotone.convexOn_univ_of_deriv
  · exact fun y => (hd y).differentiableAt
  · intro a b hab
    rw [(hd a).deriv, (hd b).deriv, div_le_div_iff₀ (hpos a) (hpos b)]
    have : c * Real.exp a ≤ c * Real.exp b :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hab) hc.le
    nlinarith

/-- Jensen for `exp` on a nonempty finset: `k · exp (mean x) ≤ ∑ exp x`. -/
private lemma exp_jensen {ι : Type} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ) :
    (s.card : ℝ) * Real.exp ((1 / (s.card : ℝ)) * ∑ j ∈ s, x j) ≤ ∑ j ∈ s, Real.exp (x j) := by
  have hk : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := convexOn_exp.map_sum_le (t := s) (w := fun _ => 1 / (s.card : ℝ)) (p := x)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  calc (s.card : ℝ) * Real.exp ((1 / (s.card : ℝ)) * ∑ j ∈ s, x j)
      ≤ (s.card : ℝ) * ((1 / (s.card : ℝ)) * ∑ j ∈ s, Real.exp (x j)) :=
        mul_le_mul_of_nonneg_left h hk.le
    _ = ∑ j ∈ s, Real.exp (x j) := by field_simp

/-- The two-step Jensen bound shared by both losses. -/
private lemma key_bound {n : ℕ} (hn : 2 ≤ n) (x : Fin n → Fin n → ℝ) :
    (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp ((1 / (n : ℝ)) *
        ∑ i, (1 / ((n : ℝ) - 1)) * ∑ j ∈ Finset.univ.erase i, x i j)) ≤
      ∑ i, Real.log (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (x i j)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set f : ℝ → ℝ := fun y => Real.log (1 + ((n : ℝ) - 1) * Real.exp y) with hf
  set y : Fin n → ℝ := fun i => (1 / ((n : ℝ) - 1)) * ∑ j ∈ Finset.univ.erase i, x i j with hy
  -- outer Jensen
  have h1 : f ((1 / (n : ℝ)) * ∑ i, y i) ≤ (1 / (n : ℝ)) * ∑ i, f (y i) := by
    have h := (sp_convex ((n : ℝ) - 1) hc).map_sum_le (t := Finset.univ)
      (w := fun _ => 1 / (n : ℝ)) (p := y) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun _ _ => Set.mem_univ _)
    simpa only [smul_eq_mul, ← Finset.mul_sum] using h
  -- inner Jensen
  have h2 : ∀ i, f (y i) ≤ Real.log (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (x i j)) := by
    intro i
    have hcard : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub (by omega), Nat.cast_one]
    have hne : (Finset.univ.erase i).Nonempty := by
      rw [← Finset.card_pos]; rw [← Nat.cast_pos (α := ℝ), hcard]; exact hc
    have hj := exp_jensen (Finset.univ.erase i) hne (x i)
    rw [hcard] at hj
    apply Real.log_le_log (by positivity)
    simp only [hy]
    linarith
  calc (n : ℝ) * f ((1 / (n : ℝ)) * ∑ i, y i)
      ≤ (n : ℝ) * ((1 / (n : ℝ)) * ∑ i, f (y i)) := mul_le_mul_of_nonneg_left h1 hn0.le
    _ = ∑ i, f (y i) := by field_simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => h2 i)

theorem solution {n d : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α)
    (u : Fin n → Vec d) (hu : IsUnitConfig u) :
    (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp (-((n : ℝ) * α / ((n : ℝ) - 1)))) ≤
      symLoss α u := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hkey := key_bound hn (fun i j => α * (inner ℝ (u j) (u i) - 1))
  refine le_trans ?_ hkey
  apply mul_le_mul_of_nonneg_left _ hn0.le
  apply Real.log_le_log (by positivity)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply Real.exp_le_exp.2
  set U := ∑ j, u j with hU
  have hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, α * (inner ℝ (u j) (u i) - 1) =
      α * (inner ℝ U (u i) - n) := by
    intro i
    rw [Finset.sum_erase _ (by rw [real_inner_self_eq_norm_sq, hu i]; ring), ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← sum_inner, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  simp only [hrow]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, ← inner_sum, ← hU,
    real_inner_self_eq_norm_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hUn : 0 ≤ α * ‖U‖ ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
  have : 1 / (n : ℝ) * (1 / ((n : ℝ) - 1) * (α * (‖U‖ ^ 2 - (n : ℝ) * n))) =
      -((n : ℝ) * α / ((n : ℝ) - 1)) + α * ‖U‖ ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp
    ring
  rw [this]
  linarith
