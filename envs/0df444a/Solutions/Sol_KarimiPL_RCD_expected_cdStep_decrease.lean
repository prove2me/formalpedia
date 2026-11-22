-- Prove2me | solution 1 for KarimiPL.RCD.expected_cdStep_decrease
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:39:30.73215+00:00
-- url     : https://prove2.me/submissions/890b2660-7ae3-41b4-a1c3-4e49490cee07

import Definitions.Def_KarimiPL_RCD_Setting
import Definitions.Def_ShiOptrates_FunctionClass

open KarimiPL.RCD
open scoped BigOperators

namespace TwentyAnalysis.RCD

lemma step {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (L : ℝ)
    (hL : 0 < L) (hcoord : CoordLipschitz f L)
    (x : KarimiPL.Rel.E d) (i : Fin d) :
    f (cdStep f L x i) ≤ f x - 1 / (2 * L) * (gradient f x i) ^ 2 := by
  have h := hcoord x i (-(1 / L * gradient f x i))
  rw [neg_smul, ← sub_eq_add_neg] at h
  change f (cdStep f L x i) ≤ _ at h
  calc
    f (cdStep f L x i) ≤
        f x + -(1 / L * gradient f x i) * gradient f x i +
          L / 2 * (-(1 / L * gradient f x i)) ^ 2 := h
    _ = f x - 1 / (2 * L) * (gradient f x i) ^ 2 := by
      field_simp
      <;> ring

lemma average {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (L : ℝ)
    (hL : 0 < L) (hcoord : CoordLipschitz f L) (x : KarimiPL.Rel.E d) :
    (1 / (d : ℝ)) * ∑ i : Fin d, f (cdStep f L x i) ≤
      f x - 1 / (2 * (d : ℝ) * L) * ‖gradient f x‖ ^ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    (1 / (d : ℝ)) * ∑ i : Fin d, f (cdStep f L x i) ≤
        (1 / (d : ℝ)) * ∑ i : Fin d,
          (f x - 1 / (2 * L) * (gradient f x i) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun i _ => step f L hL hcoord x i
      · positivity
    _ = f x - 1 / (2 * (d : ℝ) * L) * ‖gradient f x‖ ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [EuclideanSpace.real_norm_sq_eq]
      field_simp
      <;> ring

lemma contraction {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (L : ℝ)
    (hL : 0 < L) (hcoord : CoordLipschitz f L)
    (xstar : KarimiPL.Rel.E d) (mu : ℝ)
    (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) mu (f xstar))
    (x : KarimiPL.Rel.E d) :
    (1 / (d : ℝ)) * ∑ i : Fin d, (f (cdStep f L x i) - f xstar) ≤
      (1 - mu / ((d : ℝ) * L)) * (f x - f xstar) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h := average hd f L hL hcoord x
  have hp := mul_le_mul_of_nonneg_left (hPL x)
    (show 0 ≤ 1 / (2 * (d : ℝ) * L) by positivity)
  have havg : (1 / (d : ℝ)) * ∑ i : Fin d, (f (cdStep f L x i) - f xstar) =
      (1 / (d : ℝ)) * ∑ i : Fin d, f (cdStep f L x i) - f xstar := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  rw [havg]
  calc
    (1 / (d : ℝ)) * ∑ i : Fin d, f (cdStep f L x i) - f xstar ≤
      f x - 1 / (2 * (d : ℝ) * L) * (2 * mu * (f x - f xstar)) - f xstar := by
        linarith
    _ = (1 - mu / ((d : ℝ) * L)) * (f x - f xstar) := by
      field_simp
      <;> ring

lemma sum_words_succ (k d : ℕ) (F : (Fin (k + 1) → Fin d) → ℝ) :
    ∑ w, F w = ∑ w : Fin k → Fin d, ∑ i : Fin d, F (Fin.snoc w i) := by
  classical
  symm
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    ((Equiv.prodComm (Fin k → Fin d) (Fin d)).trans (Fin.snocEquiv (fun _ => Fin d)))
    _ _ (fun _ => rfl)

lemma geometric (u : ℕ → ℝ) (q : ℝ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ q * u k) : ∀ k, u k ≤ q ^ k * u 0 := by
  by_cases hq : 0 ≤ q
  · intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        u (k + 1) ≤ q * u k := hstep k
        _ ≤ q * (q ^ k * u 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (k + 1) * u 0 := by rw [pow_succ]; ring
  · have hz : ∀ k, u k = 0 := by
      intro k
      have hn := hu (k + 1)
      have hs := hstep k
      have hk := hu k
      have hq' : q < 0 := lt_of_not_ge hq
      nlinarith
    simp [hz]

lemma expected_recurrence {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ)
    (L : ℝ) (x0 : KarimiPL.Rel.E d) (fstar q : ℝ)
    (hstep : ∀ x, (1 / (d : ℝ)) * ∑ i : Fin d, (f (cdStep f L x i) - fstar) ≤
      q * (f x - fstar)) (k : ℕ) :
    expectedGap f L x0 fstar (k + 1) ≤ q * expectedGap f L x0 fstar k := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold expectedGap
  rw [sum_words_succ]
  simp only [cdRun, Fin.init_snoc, Fin.snoc_last]
  have heq : (1 / (d : ℝ) ^ (k + 1)) *
      ∑ w : Fin k → Fin d, ∑ i : Fin d,
        (f (cdStep f L (cdRun f L x0 k w) i) - fstar) =
      (1 / (d : ℝ) ^ k) * ∑ w : Fin k → Fin d,
        ((1 / (d : ℝ)) * ∑ i : Fin d,
          (f (cdStep f L (cdRun f L x0 k w) i) - fstar)) := by
    rw [← Finset.mul_sum, ← mul_assoc, pow_succ]
    congr 1
    field_simp
  rw [heq]
  calc
    (1 / (d : ℝ) ^ k) * ∑ w : Fin k → Fin d,
        ((1 / (d : ℝ)) * ∑ i : Fin d,
          (f (cdStep f L (cdRun f L x0 k w) i) - fstar)) ≤
      (1 / (d : ℝ) ^ k) * ∑ w : Fin k → Fin d,
        (q * (f (cdRun f L x0 k w) - fstar)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun w _ => hstep _
      · positivity
    _ = q * ((1 / (d : ℝ) ^ k) * ∑ w : Fin k → Fin d,
        (f (cdRun f L x0 k w) - fstar)) := by rw [← Finset.mul_sum]; ring

end TwentyAnalysis.RCD

theorem solution {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (L : ℝ)
    (hL : 0 < L) (hcoord : CoordLipschitz f L) :
    ∀ x : KarimiPL.Rel.E d,
      (1 / (d : ℝ)) * ∑ i : Fin d, f (cdStep f L x i) ≤
        f x - 1 / (2 * (d : ℝ) * L) * ‖gradient f x‖ ^ 2 := by
  exact TwentyAnalysis.RCD.average hd f L hL hcoord
