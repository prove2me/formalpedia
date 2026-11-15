-- Prove2me | solution 1 for Kyprianou.Ch01.pmfLaplaceConvolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:29:55.844493+00:00
-- url     : https://prove2.me/submissions/345f3fcb-e012-43ec-b5d4-f30a000b266f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

private theorem pmf_weighted_map (q : PMF ℕ) (k : ℕ)
    (w : ℕ → ENNReal) :
    (∑' n : ℕ, (q.map (fun m => k + m) n) * w n) =
      ∑' m : ℕ, q m * w (k + m) := by
  calc
    (∑' n : ℕ, (q.map (fun m => k + m) n) * w n) =
        (∑' n : ℕ,
          (∑' m : ℕ, if n = k + m then q m else 0) * w n) := by
      apply tsum_congr
      intro n; congr 1
      rw [PMF.map_apply]
      apply tsum_congr
      intro m; by_cases h : n = k + m <;> simp [h]
    _ =
        ∑' n : ℕ, ∑' m : ℕ,
           (if n = k + m then q m else 0) * w n := by
      apply tsum_congr
      intro n; rw [ENNReal.tsum_mul_right]
    _ = ∑' m : ℕ, ∑' n : ℕ,
          (if n = k + m then q m else 0) * w n :=
      ENNReal.tsum_comm
    _ = ∑' m : ℕ, q m * w (k + m) := by
      apply tsum_congr
      intro m
      rw [tsum_eq_single (k + m)]
      · simp
      · intro n hn; simp [hn]

private theorem pmf_weighted_bind (p q : PMF ℕ)
    (w : ℕ → ENNReal)
    (hw : ∀ k m : ℕ, w (k + m) = w k * w m) :
    (∑' n : ℕ, (p.bind (fun k => q.map (fun m => k + m)) n) * w n) =
       (∑' k : ℕ, p k * w k) * (∑' m : ℕ, q m * w m) := by
  simp only [PMF.bind_apply]
  calc
    (∑' n : ℕ, (∑' k : ℕ, p k * (q.map (fun m => k + m) n)) * w n) =
      ∑' n : ℕ, ∑' k : ℕ,
        (p k * (q.map (fun m => k + m) n)) * w n := by
      apply tsum_congr
      intro n; rw [ENNReal.tsum_mul_right]
    _ = ∑' k : ℕ, ∑' n : ℕ,
         (p k * (q.map (fun m => k + m) n)) * w n :=
      ENNReal.tsum_comm
    _ = ∑' k : ℕ, p k * (∑' n : ℕ,
        (q.map (fun m => k + m) n) * w n) := by
      congr 1
      funext k
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext n; ring
    _ = ∑' k : ℕ, p k * (∑' m : ℕ, q m * w (k + m)) := by
      simp_rw [pmf_weighted_map]
    _ = ∑' k : ℕ, (p k * w k) * (∑' m : ℕ, q m * w m) := by
      congr 1
      funext k
      simp_rw [hw k]
      calc
        p k * (∑' m : ℕ, q m * (w k * w m)) =
          p k * (∑' m : ℕ, w k * (q m * w m)) := by
            congr 1
            apply tsum_congr
            intro m
            ring
        _ = p k * (w k * (∑' m : ℕ, q m * w m)) := by
            rw [ENNReal.tsum_mul_left]
        _ = (p k * w k) * (∑' m : ℕ, q m * w m) := by ring
    _ = (∑' k : ℕ, p k * w k) * (∑' m : ℕ, q m * w m) :=
      ENNReal.tsum_mul_right

theorem solution
    (p q : PMF ℕ) (phi : ℝ) (hphi : 0 < phi) :
    (∑' n : ℕ, ((p.bind (fun k => q.map (fun m => k + m))) n).toReal *
       Real.exp (-phi * (n : ℝ))) =
      (∑' k : ℕ, (p k).toReal * Real.exp (-phi * (k : ℝ))) *
      (∑' m : ℕ, (q m).toReal * Real.exp (-phi * (m : ℝ))) := by
  let w : ℕ → ENNReal := fun n => ENNReal.ofReal (Real.exp (-phi * (n : ℝ)))
  have hw : ∀ k m : ℕ, w (k + m) = w k * w m := by
    intro k m
    dsimp [w]
    rw [show -phi * ((k + m : ℕ) : ℝ) =
        -phi * (k : ℝ) + -phi * (m : ℝ) by simp [Nat.cast_add, mul_add],
      Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hpmf := pmf_weighted_bind p q w hw
  have hterm (r : PMF ℕ) (n : ℕ) :
      (r n * w n).toReal =
        (r n).toReal * Real.exp (-phi * (n : ℝ)) := by
    rw [ENNReal.toReal_mul]
    simp [w, (Real.exp_pos _).le]
  have hfinite (r : PMF ℕ) (n : ℕ) : r n * w n ≠ ⊤ := by
    exact ENNReal.mul_ne_top (r.apply_ne_top n) (by simp [w])
  have hcast (r : PMF ℕ) :
      (∑' n : ℕ, r n * w n).toReal =
        ∑' n : ℕ, (r n).toReal * Real.exp (-phi * (n : ℝ)) := by
    rw [ENNReal.tsum_toReal_eq (hfinite r)]
    exact tsum_congr (hterm r)
  have heq := congrArg ENNReal.toReal hpmf
  rw [ENNReal.toReal_mul, hcast p, hcast q] at heq
  rw [hcast] at heq
  exact heq
