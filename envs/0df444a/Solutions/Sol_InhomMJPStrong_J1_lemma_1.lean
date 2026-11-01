-- Prove2me | solution 1 for InhomMJPStrong.J1.lemma_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:35:16.534794+00:00
-- url     : https://prove2.me/submissions/d731566c-d7ec-4dc9-b78b-0e4386bef9f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model
import Theorems.Thm_InhomMJPStrong_J1_eq_17

open MeasureTheory ProbabilityTheory Filter Asymptotics
open InhomMJPStrong.J1

namespace J1Lemma1

lemma maxGap_triangle (T U V : ℕ → ℝ) (m : ℕ) :
    maxGap T U m ≤ maxGap T V m + maxGap U V m := by
  by_cases hne : (Finset.Icc 1 m).Nonempty
  · have hT : ∀ l ∈ Finset.Icc 1 m, |T l - V l| ≤ maxGap T V m := fun l hl => by
      rw [maxGap, dif_pos hne]; exact Finset.le_sup' (fun l => |T l - V l|) hl
    have hU : ∀ l ∈ Finset.Icc 1 m, |U l - V l| ≤ maxGap U V m := fun l hl => by
      rw [maxGap, dif_pos hne]; exact Finset.le_sup' (fun l => |U l - V l|) hl
    rw [maxGap, dif_pos hne]
    refine Finset.sup'_le hne _ fun l hl => ?_
    calc |T l - U l| = |(T l - V l) - (U l - V l)| := by ring_nf
      _ ≤ |T l - V l| + |U l - V l| := abs_sub _ _
      _ ≤ _ := add_le_add (hT l hl) (hU l hl)
  · simp only [maxGap, dif_neg hne]; norm_num

end J1Lemma1

open J1Lemma1 in
theorem solution {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (q eps : ℝ) (hq : 0 < q) (heps : 0 < eps) (heps1 : eps < 1) :
    (fun n : ℕ =>
      (P {ω | kappa q eps * Real.log (n : ℝ) *
        (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) ≤
        maxGap (theta (lam0 Lam) n X ω) (chi (lam0 Lam) n X ω)
          (gridSize n eps)}).toReal)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-q)) := by
  have h17 := eq_17 hp Lam hLam hBound hPos alpha hAlpha P X hX q eps hq heps heps1
  dsimp only at h17
  obtain ⟨hEq, hO⟩ := h17
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (hO.const_mul_left 2)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (lam0 Lam)] with n hn
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg
    (mul_nonneg (by norm_num) ENNReal.toReal_nonneg), one_mul]
  have h2 : (2:ℝ) * (P {ω | 2 * Real.exp (1 / 2 + eps / 2 + 2 * q) * Real.log (n : ℝ) *
        (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) ≤
        maxGap (theta (lam0 Lam) n X ω) (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)}).toReal
      = (P {ω | 2 * Real.exp (1 / 2 + eps / 2 + 2 * q) * Real.log (n : ℝ) *
        (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) ≤
        maxGap (theta (lam0 Lam) n X ω) (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)} +
        P {ω | 2 * Real.exp (1 / 2 + eps / 2 + 2 * q) * Real.log (n : ℝ) *
        (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) ≤
        maxGap (chi (lam0 Lam) n X ω) (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)}).toReal := by
    rw [← hEq n hn, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]; ring
  rw [h2]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) ?_
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
  have htri := maxGap_triangle (theta (lam0 Lam) n X ω) (chi (lam0 Lam) n X ω)
    (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)
  have hk : kappa q eps = 2 * (2 * Real.exp (1 / 2 + eps / 2 + 2 * q)) := by unfold kappa; ring
  rw [hk] at hω
  linarith [hcon.1, hcon.2]
