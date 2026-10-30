-- Prove2me | solution 1 for OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:12:41.864951+00:00
-- url     : https://prove2.me/submissions/6f25dc1a-ce22-4c9a-a7e8-0c15155a5f08

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_HierarchyVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-root logarithmic variation bound for shifted angular blocks. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem sliding_window_sum_le (P : ℕ → ℝ) (N K : ℕ)
    (hP : ∀ j < N, 0 ≤ P j) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico (i + 1 - K) (i + 1), P j) ≤
      (K : ℝ) * ∑ j ∈ Finset.range N, P j := by
  classical
  have hrow (i : ℕ) (hi : i ∈ Finset.range N) :
      (∑ j ∈ Finset.Ico (i + 1 - K) (i + 1), P j) =
        ∑ j ∈ Finset.range N, if j ∈ Finset.Ico (i + 1 - K) (i + 1) then P j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at *
    omega
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hP j (Finset.mem_range.mp hj))
  have hsub : (Finset.range N).filter (fun i => j ∈ Finset.Ico (i + 1 - K) (i + 1)) ⊆
      Finset.Ico j (j + K) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at *
    omega
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
  exact_mod_cast hcard

theorem sum_log_ratios (n : ℕ → ℝ) (N : ℕ) (hn : ∀ j ≤ N, 0 < n j) :
    (∑ j ∈ Finset.range N, Real.log (n j / n (j + 1))) = Real.log (n 0 / n N) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      Real.log (n j / n (j + 1)) = Real.log (n j) - Real.log (n (j + 1)) :=
    Real.log_div (hn j (by have := Finset.mem_range.mp hj; omega)).ne'
      (hn (j + 1) (by have := Finset.mem_range.mp hj; omega)).ne'
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  exact (Real.log_div (hn 0 (Nat.zero_le N)).ne' (hn N le_rfl).ne').symm

theorem sum_log_ratios_Ico (n : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hn : ∀ j ≤ b, 0 < n j) :
    (∑ j ∈ Finset.Ico a b, Real.log (n j / n (j + 1))) = Real.log (n a / n b) := by
  rw [Finset.sum_Ico_eq_sub _ hab, sum_log_ratios n b hn,
    sum_log_ratios n a (fun j hj => hn j (hj.trans hab))]
  rw [Real.log_div (hn 0 (Nat.zero_le b)).ne' (hn b le_rfl).ne',
    Real.log_div (hn 0 (Nat.zero_le b)).ne' (hn a hab).ne',
    Real.log_div (hn a hab).ne' (hn b le_rfl).ne']
  ring

theorem full_root_log_variation (n R : ℕ → ℝ) (N K : ℕ)
    (hn : ∀ j ≤ N, 0 < n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR : ∀ i < N, R i ≤ Real.log (n (i + 1 - K) / n (i + 1))) :
    (∑ i ∈ Finset.range N, R i) ≤ (K : ℝ) * Real.log (n 0 / n N) := by
  have hP (j : ℕ) (hj : j < N) : 0 ≤ Real.log (n j / n (j + 1)) := by
    apply Real.log_nonneg
    exact (one_le_div (hn (j + 1) (by omega))).2
      (hmono (by change j ≤ N; omega) (by change j + 1 ≤ N; omega) (by omega))
  have hwindow (i : ℕ) (hi : i ∈ Finset.range N) :
      R i ≤ ∑ j ∈ Finset.Ico (i + 1 - K) (i + 1), Real.log (n j / n (j + 1)) := by
    rw [sum_log_ratios_Ico n _ _ (Nat.sub_le _ _) (fun j hj => hn j
      (hj.trans (by have := Finset.mem_range.mp hi; omega)))]
    exact hR i (Finset.mem_range.mp hi)
  calc
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico (i + 1 - K) (i + 1),
        Real.log (n j / n (j + 1)) := Finset.sum_le_sum hwindow
    _ ≤ (K : ℝ) * ∑ j ∈ Finset.range N, Real.log (n j / n (j + 1)) :=
      sliding_window_sum_le _ N K hP
    _ = _ := by rw [sum_log_ratios n N hn]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ExponentialVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variation of exponential weights from variation of their logarithms. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem norm_exp_sub_le_of_re_le (a b : ℂ) (C : ℝ) (ha : a.re ≤ C) (hb : b.re ≤ C) :
    ‖Complex.exp b - Complex.exp a‖ ≤ Real.exp C * ‖b - a‖ := by
  have hconvex : Convex ℝ {z : ℂ | z.re ≤ C} := by
    intro x hx y hy u v hu hv huv
    change (u • x + v • y).re ≤ C
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    change x.re ≤ C at hx
    change y.re ≤ C at hy
    have huC := mul_le_mul_of_nonneg_left hx hu
    have hvC := mul_le_mul_of_nonneg_left hy hv
    have htotal : u * C + v * C = C := by rw [← add_mul, huv, one_mul]
    linarith
  apply hconvex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => Complex.differentiableAt_exp) _ ha hb
  intro z hz
  rw [Complex.deriv_exp, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hz

theorem logarithm_increment_bound (a P R : ℝ) (z : ℂ)
    (ha : 0 ≤ a) (hP : 0 ≤ P) (hR : 0 ≤ R) :
    ‖((a * P : ℝ) : ℂ) - z * (R : ℂ)‖ ≤ a * P + ‖z‖ * R := by
  calc
    _ ≤ ‖((a * P : ℝ) : ℂ)‖ + ‖z * (R : ℂ)‖ := norm_sub_le _ _
    _ = _ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha hP),
        abs_of_nonneg hR]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PhaseMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Motion of diagonal Fourier predictions

Bounded frequencies give explicit Lipschitz bounds for the actual characters
and Hilbert-valued phase sums. Together with logarithmic energy control these
give the multiplicative cell-supremum bound required by §9.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem character_motion (frequency s t : ℝ) :
    ‖character frequency t - character frequency s‖ ≤ |frequency| * |t - s| := by
  have h := norm_exp_sub_le_of_re_le
    (((frequency * s : ℝ) : ℂ) * Complex.I)
    (((frequency * t : ℝ) : ℂ) * Complex.I) 0 (by simp) (by simp)
  have hd : (((frequency * t : ℝ) : ℂ) * Complex.I) -
      (((frequency * s : ℝ) : ℂ) * Complex.I) =
      ((frequency * (t - s) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hd, Real.exp_zero, one_mul, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, abs_mul] at h
  exact h

omit [Fintype ι] in
theorem diagonalModulation_motion (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ)
    {L : ℝ} (hL : 0 ≤ L) (hfrequency : ∀ j, |frequency j| ≤ L) (s t : ℝ) :
    ‖diagonalModulation frequency a t - diagonalModulation frequency a s‖ ≤
      L * ‖a‖ * |t - s| := by
  have hcoordinate (j : κ) :
      ‖(diagonalModulation frequency a t - diagonalModulation frequency a s) j‖ ≤
        ‖a j‖ * (L * |t - s|) := by
    have heq : (diagonalModulation frequency a t - diagonalModulation frequency a s) j =
        a j * (character (frequency j) t - character (frequency j) s) := by
      simp only [PiLp.sub_apply, diagonalModulation]
      ring
    rw [heq, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((character_motion (frequency j) s t).trans
        (mul_le_mul_of_nonneg_right (hfrequency j) (abs_nonneg _))) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ L * ‖a‖ * |t - s|)).mp
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ j, (‖a j‖ * (L * |t - s|)) ^ 2 :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcoordinate j) 2
    _ = (L * ‖a‖ * |t - s|) ^ 2 := by
      simp_rw [mul_pow]
      rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq]
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CarrierSlopeMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing a top's carrier by its angular child-center carrier costs
only the child width, not the width of an earlier block ancestor. -/

noncomputable section
namespace LipschitzHilbert
open PhaseCombinatorics

variable {κ : Type*} [Fintype κ]

theorem diagonalModulation_change_slope (frequency : κ → ℝ)
    (v : EuclideanSpace ℂ κ) (F : ℝ) (hF : 0 ≤ F)
    (hfrequency : ∀ k, |frequency k| ≤ F) (reference top center b : ℝ) :
    ‖diagonalModulation frequency v ((reference-top)*b)-
      diagonalModulation frequency v ((reference-center)*b)‖ ≤
      F*‖v‖*|top-center| * |b| := by
  have h := diagonalModulation_motion frequency v hF hfrequency
    ((reference-center)*b) ((reference-top)*b)
  have heq : (reference-top)*b-(reference-center)*b = (center-top)*b := by ring
  rw [heq, abs_mul, abs_sub_comm center top] at h
  simpa only [mul_assoc] using h

/-- A bound in the top carrier transfers to the one common child carrier. -/
theorem carrier_replacement_motion (frequency : κ → ℝ)
    (v0 v1 : EuclideanSpace ℂ κ) (F B E : ℝ) (hF : 0 ≤ F)
    (hfrequency : ∀ k, |frequency k| ≤ F) (hB : ‖v0‖ ≤ B)
    (reference top center b : ℝ)
    (hmotion : ‖v1-diagonalModulation frequency v0 ((reference-top)*b)‖ ≤ E) :
    ‖v1-diagonalModulation frequency v0 ((reference-center)*b)‖ ≤
      E+F*B*|top-center| * |b| := by
  apply (norm_sub_le_norm_sub_add_norm_sub v1
    (diagonalModulation frequency v0 ((reference-top)*b))
    (diagonalModulation frequency v0 ((reference-center)*b))).trans
  apply add_le_add hmotion
  apply (diagonalModulation_change_slope frequency v0 F hF hfrequency reference top center b).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hF) (abs_nonneg _)) (abs_nonneg _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SummationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation by parts for the weighted vector amplitudes of the hierarchy. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_weighted_sum_le_variation (w : ℕ → ℂ) (f : ℕ → E) (N : ℕ) (B : ℝ)
    (hB : ∀ k ≤ N, ‖∑ i ∈ Finset.range (k + 1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (N + 1), w i • f i‖ ≤
      (‖w N‖ + ∑ i ∈ Finset.range N, ‖w (i + 1) - w i‖) * B := by
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel]
  calc
    _ ≤ ‖w N • ∑ i ∈ Finset.range (N + 1), f i‖ +
        ‖∑ i ∈ Finset.range N, (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), f j‖ :=
      norm_sub_le _ _
    _ ≤ ‖w N‖ * B + ∑ i ∈ Finset.range N, ‖w (i + 1) - w i‖ * B := by
      apply add_le_add
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hB N le_rfl) (norm_nonneg _)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hB i (by have := Finset.mem_range.mp hi; omega))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SegmentWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight variation on a later segment, paid for by full-root mass loss. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem boundaryLog_nonnegative (n m : ℕ → ℝ) (i : ℕ)
    (hn : 0 < n (i + 1)) (hm : n (i + 1) ≤ m i) : 0 ≤ boundaryLog n m i := by
  exact Real.log_nonneg ((one_le_div hn).2 hm)

theorem boundaryLog_le_root_ratio (n m : ℕ → ℝ) (i K : ℕ)
    (hn : 0 < n (i + 1)) (hm : 0 < m i) (hmn : m i ≤ n (i + 1 - K)) :
    boundaryLog n m i ≤ Real.log (n (i + 1 - K) / n (i + 1)) := by
  exact Real.log_le_log (div_pos hm hn) (div_le_div_of_nonneg_right hmn hn.le)

theorem segmentLog_re_le (n R : ℕ → ℝ) (z : ℕ → ℂ) (a lower : ℝ) (start k : ℕ)
    (ha : 0 ≤ a) (hlower : 0 < lower) (hn : lower ≤ n k)
    (hR : ∀ i < k, 0 ≤ R i) (hz : ∀ i < k, 0 ≤ (z i).re) :
    (segmentLog n R z a start k).re ≤ -a * Real.log lower := by
  have hlog : Real.log lower ≤ Real.log (n k) := Real.log_le_log hlower hn
  have hsum : 0 ≤ ∑ i ∈ Finset.Ico start k, (z i).re * R i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hz i (Finset.mem_Ico.mp hi).2)
      (hR i (Finset.mem_Ico.mp hi).2))
  simp only [segmentLog, Complex.sub_re, Complex.ofReal_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith

theorem segmentLog_increment (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (start k : ℕ)
    (hstart : start ≤ k) (hn : 0 < n k) (hn' : 0 < n (k + 1)) :
    segmentLog n R z a start (k + 1) - segmentLog n R z a start k =
      ((a * Real.log (n k / n (k + 1)) : ℝ) : ℂ) - z k * (R k : ℂ) := by
  rw [segmentLog, segmentLog, Finset.sum_Ico_succ_top hstart, Real.log_div hn.ne' hn'.ne']
  push_cast
  ring

theorem segmentLog_variation (n R : ℕ → ℝ) (z : ℕ → ℂ)
    (start N K : ℕ) (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, 0 < n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j + 1 - K) / n (j + 1)))
    (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    (∑ j ∈ Finset.Ico start N,
      ‖segmentLog n R z a start (j + 1) - segmentLog n R z a start j‖) ≤
      (a + Z * K) * Real.log (n 0 / n N) := by
  have hP (j : ℕ) (hj : j < N) : 0 ≤ Real.log (n j / n (j + 1)) := by
    apply Real.log_nonneg
    exact (one_le_div (hn (j + 1) (by omega))).2
      (hmono (by change j ≤ N; omega) (by change j + 1 ≤ N; omega) (by omega))
  calc
    _ ≤ ∑ j ∈ Finset.Ico start N, (a * Real.log (n j / n (j + 1)) + Z * R j) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hsj, hjN⟩ := Finset.mem_Ico.mp hj
      rw [segmentLog_increment n R z a start j hsj (hn j (by omega)) (hn (j + 1) (by omega))]
      exact (logarithm_increment_bound a _ _ _ ha (hP j hjN) (hR0 j hjN)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hz j hjN) (hR0 j hjN)))
    _ ≤ ∑ j ∈ Finset.range N, (a * Real.log (n j / n (j + 1)) + Z * R j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      · intro j hj _
        have hjN := Finset.mem_range.mp hj
        exact add_nonneg (mul_nonneg ha (hP j hjN)) (mul_nonneg hZ (hR0 j hjN))
    _ = a * Real.log (n 0 / n N) + Z * ∑ j ∈ Finset.range N, R j := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_log_ratios n N hn]
    _ ≤ a * Real.log (n 0 / n N) + Z * ((K : ℝ) * Real.log (n 0 / n N)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (full_root_log_variation n R N K hn hmono hR) hZ)
    _ = _ := by ring

theorem segmentWeight_variation (n R : ℕ → ℝ) (z : ℕ → ℂ)
    (start N K : ℕ) (a lower Z : ℝ) (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j + 1 - K) / n (j + 1)))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    ‖segmentWeight n R z a start N‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖segmentWeight n R z a start (j + 1) - segmentWeight n R z a start j‖) ≤
      lower ^ (-a) * (1 + (a + Z * K) * Real.log (n 0 / n N)) := by
  let C := -a * Real.log lower
  have hn0 : ∀ j ≤ N, 0 < n j := fun j hj => hlower.trans_le (hn j hj)
  have hbound (j : ℕ) (hj : j ≤ N) : (segmentLog n R z a start j).re ≤ C :=
    segmentLog_re_le n R z a lower start j ha hlower (hn j hj)
      (fun i hi => hR0 i (hi.trans_le hj)) (fun i hi => hz0 i (hi.trans_le hj))
  have hend : ‖segmentWeight n R z a start N‖ ≤ Real.exp C := by
    rw [segmentWeight, Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hbound N le_rfl)
  have hsum : (∑ j ∈ Finset.Ico start N,
      ‖segmentWeight n R z a start (j + 1) - segmentWeight n R z a start j‖) ≤
        Real.exp C * ∑ j ∈ Finset.Ico start N,
          ‖segmentLog n R z a start (j + 1) - segmentLog n R z a start j‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjN := (Finset.mem_Ico.mp hj).2
    exact norm_exp_sub_le_of_re_le _ _ C (hbound j (by omega)) (hbound (j + 1) (by omega))
  have hcost := segmentLog_variation n R z start N K a Z ha hZ hn0 hmono hR0 hR hz
  have htotal := add_le_add hend (hsum.trans (mul_le_mul_of_nonneg_left hcost (Real.exp_pos C).le))
  have heq : Real.exp C = lower ^ (-a) := by
    rw [Real.rpow_def_of_pos hlower]
    simp only [C]
    congr 1
    ring
  rw [heq] at htotal
  nlinarith

theorem boundary_weight_variation (n m : ℕ → ℝ) (z : ℕ → ℂ)
    (start N K : ℕ) (a lower Z : ℝ) (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hm : ∀ j < N, n (j + 1) ≤ m j ∧ m j ≤ n (j + 1 - K))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    ‖segmentWeight n (boundaryLog n m) z a start N‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖segmentWeight n (boundaryLog n m) z a start (j + 1) -
          segmentWeight n (boundaryLog n m) z a start j‖) ≤
      lower ^ (-a) * (1 + (a + Z * K) * Real.log (n 0 / n N)) := by
  have hn0 (j : ℕ) (hj : j < N) : 0 < n (j + 1) :=
    hlower.trans_le (hn (j + 1) (by omega))
  exact segmentWeight_variation n (boundaryLog n m) z start N K a lower Z
    ha hlower hZ hn hmono
    (fun j hj => boundaryLog_nonnegative n m j (hn0 j hj) (hm j hj).1)
    (fun j hj => boundaryLog_le_root_ratio n m j K (hn0 j hj)
      ((hn0 j hj).trans_le (hm j hj).1) (hm j hj).2) hz0 hz

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopLogAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic endpoint factor is absorbed by the spare decay of
an actual top weight, without any positive lower cutoff on that weight. -/

noncomputable section
namespace LipschitzHilbert

theorem bounded_weight_rpow_le_linear {h C q : ℝ} {d : ℕ}
    (hh : 0 < h) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hq : 1 ≤ q) (hqd : q ≤ (d : ℝ)+1) :
    h^q ≤ C^d*h := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hbase : h^(q-1) ≤ C^d := by
    apply (Real.rpow_le_rpow hh.le hhC (by linarith : 0 ≤ q-1)).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc
    h^q = h^((q-1)+1) := by congr 1; ring
    _ = h^(q-1)*h := by rw [Real.rpow_add hh, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase hh.le

/-- Small weights have no logarithmic singularity after the available
polynomial decay is used. The total mass enters only through its logarithm. -/
theorem top_log_absorption {h S C Q q : ℝ} {d : ℕ}
    (hh : 0 < h) (hS : 0 < S) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hQ : 0 ≤ Q) (hq : 2 ≤ q) (hqd : q ≤ (d : ℝ)+1) :
    h^q * (1+Q*Real.log (S/h)) ≤
      C^d * (1+Q*(Real.log (max 1 S)+1))*h := by
  have hp := bounded_weight_rpow_le_linear hh hC hhC (by linarith : 1 ≤ q) hqd
  have hp' := bounded_weight_rpow_le_linear hh hC hhC (by linarith : 1 ≤ q-1)
    (by linarith : q-1 ≤ (d : ℝ)+1)
  have hlog : Real.log (S/h) ≤ Real.log (max 1 S)+h⁻¹ := by
    have hSlog : Real.log S ≤ Real.log (max 1 S) := Real.log_le_log hS (le_max_right _ _)
    have hhlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hh)
    rw [Real.log_inv] at hhlog
    rw [Real.log_div hS.ne' hh.ne']
    linarith
  have hlog0 : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hinv : h^q*h⁻¹ = h^(q-1) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hh]
    congr 1
  calc
    _ ≤ h^q * (1+Q*(Real.log (max 1 S)+h⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hh.le _)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hQ)
    _ = h^q*(1+Q*Real.log (max 1 S))+Q*h^(q-1) := by
      rw [← hinv]
      ring
    _ ≤ (C^d*h)*(1+Q*Real.log (max 1 S))+Q*(C^d*h) :=
      add_le_add (mul_le_mul_of_nonneg_right hp (by positivity))
        (mul_le_mul_of_nonneg_left hp' hQ)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopMovingLogAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squared logarithmic loss in moving endpoint weights is absorbed
by four inverse powers of the original positive top weight. -/

noncomputable section
namespace LipschitzHilbert

theorem top_inverse_log_squared_absorption {h S C Q a : ℝ}
    (hh : 0 < h) (hhS : h ≤ S) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hQ : 0 ≤ Q) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    h^(-a)*(1+Q*Real.log (S/h))^2 ≤
      C^4*(1+Q*(Real.log (max 1 S)+1))^2*h^(-(4:ℝ)) := by
  have hS : 0 < S := hh.trans_le hhS
  have hlog : 0 ≤ Real.log (S/h) := Real.log_nonneg ((one_le_div hh).mpr hhS)
  have hlogS : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hlinear : h*(1+Q*Real.log (S/h)) ≤
      C*(1+Q*(Real.log (max 1 S)+1)) := by
    have hb := top_log_absorption (q := 2) (d := 1) hh hS hC hhC hQ
      (by norm_num) (by norm_num)
    apply (mul_le_mul_iff_left₀ hh).mp
    convert hb using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
    ring
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ h*(1+Q*Real.log (S/h))) hlinear 2
  have hp : h^(2-a) ≤ C^2 := by
    apply (Real.rpow_le_rpow hh.le hhC (by linarith : 0 ≤ 2-a)).trans
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hC
    norm_num
    linarith
  have heq : h^(4-a) = h^(2-a)*h^2 := by
    rw [← Real.rpow_natCast h 2, ← Real.rpow_add hh]
    congr 1
    norm_num
    ring
  have hmain : h^(4-a)*(1+Q*Real.log (S/h))^2 ≤
      C^4*(1+Q*(Real.log (max 1 S)+1))^2 := by
    calc
      _ = h^(2-a)*(h*(1+Q*Real.log (S/h)))^2 := by rw [heq]; ring
      _ ≤ C^2*(C*(1+Q*(Real.log (max 1 S)+1)))^2 :=
        mul_le_mul hp hsq (sq_nonneg _) (sq_nonneg C)
      _ = _ := by ring
  have hsplit : h^(-a) = h^(-(4:ℝ))*h^(4-a) := by
    rw [← Real.rpow_add hh]
    congr 1
    ring
  calc
    _ = h^(-(4:ℝ))*(h^(4-a)*(1+Q*Real.log (S/h))^2) := by rw [hsplit]; ring
    _ ≤ h^(-(4:ℝ))*(C^4*(1+Q*(Real.log (max 1 S)+1))^2) :=
      mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hh.le _)
    _ = _ := by ring

/-- The precise polynomial produced by moving endpoint variation has the
four-inverse-power envelope used in the amplitude-motion argument. -/
theorem moving_weight_budget_absorption {A h S C Q a δ ε V : ℝ}
    (hh : 0 < h) (hhS : h ≤ S) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hQ : 0 ≤ Q) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hV : 0 ≤ V) (hVQ : V ≤ Q*Real.log (S/h))
    (hA : A ≤ (Real.exp (a*δ)*h^(-a))*((a*δ+ε*V)+ε*V+(a*δ+ε*V)*V)) :
    A ≤ Real.exp (a*δ)*(δ+ε)*C^4*(1+Q*(Real.log (max 1 S)+1))^2*h^(-(4:ℝ)) := by
  have hpoly : (a*δ+ε*V)+ε*V+(a*δ+ε*V)*V ≤ (δ+ε)*(1+V)^2 := by
    have haδ := mul_le_mul_of_nonneg_right ha1 hδ
    have hlinear := mul_le_mul_of_nonneg_right haδ (by positivity : 0 ≤ 1+V)
    have hquad : ε*V*(2+V) ≤ ε*(1+V)^2 := by nlinarith
    have hδquad : δ*(1+V) ≤ δ*(1+V)^2 := by
      have hx : 1+V ≤ (1+V)^2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hx hδ
    nlinarith
  have hsquare : (1+V)^2 ≤ (1+Q*Real.log (S/h))^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have htop := top_inverse_log_squared_absorption hh hhS hC hhC hQ ha0 ha1
  calc
    A ≤ (Real.exp (a*δ)*h^(-a))*((a*δ+ε*V)+ε*V+(a*δ+ε*V)*V) := hA
    _ ≤ (Real.exp (a*δ)*h^(-a))*((δ+ε)*(1+V)^2) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = (Real.exp (a*δ)*(δ+ε))*(h^(-a)*(1+V)^2) := by ring
    _ ≤ (Real.exp (a*δ)*(δ+ε))*(h^(-a)*(1+Q*Real.log (S/h))^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsquare
        (Real.rpow_nonneg hh.le _)) (by positivity)
    _ ≤ (Real.exp (a*δ)*(δ+ε))*(C^4*(1+Q*(Real.log (max 1 S)+1))^2*h^(-(4:ℝ))) :=
      mul_le_mul_of_nonneg_left htop (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EndpointWeightBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint variation bounds in the inverse-fourth-power form used by
the source amplitude motion argument. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem endpoint_variation_le_add (w w' : ℕ → ℂ) (start N : ℕ) :
    ‖w' N‖+(∑ j ∈ Finset.Ico start N, ‖w' (j+1)-w' j‖) ≤
      (‖w N‖+(∑ j ∈ Finset.Ico start N, ‖w (j+1)-w j‖)) +
      (‖w' N-w N‖+(∑ j ∈ Finset.Ico start N,
        ‖(w' (j+1)-w (j+1))-(w' j-w j)‖)) := by
  have hend : ‖w' N‖ ≤ ‖w N‖+‖w' N-w N‖ := by
    calc
      _ = ‖w N+(w' N-w N)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hsum : (∑ j ∈ Finset.Ico start N, ‖w' (j+1)-w' j‖) ≤
      (∑ j ∈ Finset.Ico start N, ‖w (j+1)-w j‖)+
      (∑ j ∈ Finset.Ico start N, ‖(w' (j+1)-w (j+1))-(w' j-w j)‖) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    calc
      _ = ‖(w (j+1)-w j)+((w' (j+1)-w (j+1))-(w' j-w j))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith

theorem boundary_weight_variation_fourth (n m : ℕ → ℝ) (phase : ℕ → ℂ)
    (start N K : ℕ) (a h S C Z : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hh : 0 < h) (hZ : 0 ≤ Z)
    (hC : 1 ≤ C) (hhC : h ≤ C)
    (hn : ∀ j ≤ N, h ≤ n j) (hnS : n 0 ≤ S) (hmono : AntitoneOn n (Set.Iic N))
    (hm : ∀ j < N, n (j+1) ≤ m j ∧ m j ≤ n (j+1-K))
    (hz0 : ∀ j < N, 0 ≤ (phase j).re) (hz : ∀ j < N, ‖phase j‖ ≤ Z) :
    ‖segmentWeight n (boundaryLog n m) phase a start N‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖segmentWeight n (boundaryLog n m) phase a start (j+1)-
          segmentWeight n (boundaryLog n m) phase a start j‖) ≤
      C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2*h^(-(4:ℝ)) := by
  have hn0 : 0 < n 0 := hh.trans_le (hn 0 (Nat.zero_le N))
  have hnN : 0 < n N := hh.trans_le (hn N le_rfl)
  have hhS : h ≤ S := (hn 0 (Nat.zero_le N)).trans hnS
  have hS : 0 < S := hh.trans_le hhS
  have hQ : 0 ≤ a+Z*K := by positivity
  have hlog : Real.log (n 0/n N) ≤ Real.log (S/h) := by
    apply Real.log_le_log (div_pos hn0 hnN)
    exact (div_le_div_of_nonneg_right hnS hnN.le).trans
      (div_le_div_of_nonneg_left hS.le hh (hn N le_rfl))
  have hF : 1 ≤ 1+(a+Z*K)*Real.log (S/h) := by
    have := Real.log_nonneg ((one_le_div hh).mpr hhS)
    exact le_add_of_nonneg_right (mul_nonneg hQ this)
  have hsq : 1+(a+Z*K)*Real.log (n 0/n N) ≤ (1+(a+Z*K)*Real.log (S/h))^2 := by
    have hh' := mul_le_mul_of_nonneg_left hlog hQ
    nlinarith
  exact (boundary_weight_variation n m phase start N K a h Z ha0 hh hZ hn hmono hm hz0 hz).trans
    ((mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hh.le _)).trans
      (top_inverse_log_squared_absorption hh hhS hC hhC hQ ha0 ha1))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive polynomial weights used to localize annular packets on a
reference line. Their construction and Fourier support preservation are
proved here for the actual Schwartz functions. -/

noncomputable section

open Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem polynomialWeight_one_le (a r : ℝ) (q : ℕ) (x : ℝ) :
    1 ≤ polynomialWeight a r q x := by
  have hbase : 1 ≤ 1 + (x - a) ^ 2 / r ^ 2 := by
    have h := div_nonneg (sq_nonneg (x - a)) (sq_nonneg r)
    linarith
  exact one_le_pow₀ hbase

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth about a box is absorbed by a slower packet envelope.
The integrated envelope has the packet length as its only scale factor. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem polynomial_base_le (x s a l r : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    1 + (x - a) ^ 2 / r ^ 2 ≤ 4 * (1 + ((x - s) / l) ^ 2) := by
  have hu : |(x - s) / r| ≤ |(x - s) / l| := by
    rw [abs_div, abs_div, abs_of_pos hr, abs_of_pos hl]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl hlr
  have hv : |(s - a) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hsa
  have hu2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hu
  have hv2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hv
  simp only [sq_abs, one_pow] at hu2 hv2
  have heq : (x - a) / r = (x - s) / r + (s - a) / r := by ring
  rw [← div_pow, heq]
  nlinarith [sq_nonneg ((x - s) / r - (s - a) / r), sq_nonneg ((x - s) / l)]

theorem polynomialWeight_sq_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    polynomialWeight a r q x ^ 2 * lineEnvelope s l (n + 2 * q) x ≤
      16 ^ q * lineEnvelope s l n x := by
  let B := 1 + ((x - s) / l) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbase := polynomial_base_le x s a l r hl hr hlr hsa
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (x - a) ^ 2 / r ^ 2)
    hbase (2 * q)
  have hweight : polynomialWeight a r q x ^ 2 = (1 + (x - a) ^ 2 / r ^ 2) ^ (2 * q) := by
    simp only [polynomialWeight, ← pow_mul, Nat.mul_comm q 2]
  rw [hweight]
  calc
    _ ≤ (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 16 ^ q * lineEnvelope s l n x := by
      change (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ = 16 ^ q * (B ^ n)⁻¹
      rw [mul_pow, pow_add, mul_inv_rev, ← mul_assoc]
      have hz : B ^ (2 * q) ≠ 0 := pow_ne_zero _ hB.ne'
      have hc : (4 : ℝ) ^ (2 * q) = 16 ^ q := by rw [pow_mul]; norm_num
      rw [mul_assoc ((4 : ℝ) ^ (2 * q)), mul_inv_cancel₀ hz, mul_one, hc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MovingExponentialWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variation of differences of exponential endpoint weights. The bound
is polynomial in logarithmic variation; it never exponentiates the size
of a top's logarithmic loss. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

private theorem complexSegment_re_le (a b : ℂ) (C t : ℝ)
    (ha : a.re ≤ C) (hb : b.re ≤ C) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (complexSegment a b t).re ≤ C := by
  simp only [complexSegment, Complex.add_re, Complex.smul_re, smul_eq_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha),
    mul_nonneg ht0 (sub_nonneg.mpr hb)]

private theorem complexSegment_difference (a b c d : ℂ) (D t : ℝ)
    (ha : ‖c-a‖ ≤ D) (hb : ‖d-b‖ ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖complexSegment c d t-complexSegment a b t‖ ≤ D := by
  have heq : complexSegment c d t-complexSegment a b t =
      (1-t) • (c-a) + t • (d-b) := by simp [complexSegment, smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖(1-t) • (c-a)‖ + ‖t • (d-b)‖ := norm_add_le _ _
    _ = (1-t)*‖c-a‖ + t*‖d-b‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
    _ ≤ (1-t)*D + t*D := add_le_add
      (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hb ht0)
    _ = D := by ring

private theorem hasDerivAt_complexSegment (a b : ℂ) (t : ℝ) :
    HasDerivAt (complexSegment a b) (b-a) t := by
  have h := (((hasDerivAt_const t (1:ℝ)).fun_sub (hasDerivAt_id t)).smul_const a).fun_add
    ((hasDerivAt_id t).smul_const b)
  change HasDerivAt (fun y : ℝ => (1-y) • a+y • b) (b-a) t
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp [neg_add_eq_sub])

/-- A four-point exponential estimate on a left half-plane. Only the
uniform real-part bound is exponentiated. -/
theorem exp_increment_difference_bound (a b c d : ℂ) (C D : ℝ)
    (ha : a.re ≤ C) (hb : b.re ≤ C) (hc : c.re ≤ C) (hd : d.re ≤ C)
    (hac : ‖c-a‖ ≤ D) (hbd : ‖d-b‖ ≤ D) :
    ‖(Complex.exp d-Complex.exp c)-(Complex.exp b-Complex.exp a)‖ ≤
      Real.exp C*(‖(d-c)-(b-a)‖+D*‖b-a‖) := by
  let F := fun t : ℝ => Complex.exp (complexSegment c d t)-
    Complex.exp (complexSegment a b t)
  let F' := fun t : ℝ => Complex.exp (complexSegment c d t)*(d-c)-
    Complex.exp (complexSegment a b t)*(b-a)
  have hderiv (t : ℝ) : HasDerivAt F (F' t) t :=
    (hasDerivAt_complexSegment c d t).cexp.sub (hasDerivAt_complexSegment a b t).cexp
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) 1) :
      ‖F' t‖ ≤ Real.exp C*(‖(d-c)-(b-a)‖+D*‖b-a‖) := by
    have hcd := complexSegment_re_le c d C t hc hd ht.1 ht.2.le
    have hab := complexSegment_re_le a b C t ha hb ht.1 ht.2.le
    have hdiff := (norm_exp_sub_le_of_re_le (complexSegment a b t)
      (complexSegment c d t) C hab hcd).trans
      (mul_le_mul_of_nonneg_left
        (complexSegment_difference a b c d D t hac hbd ht.1 ht.2.le)
        (Real.exp_pos C).le)
    have hexp : ‖Complex.exp (complexSegment c d t)‖ ≤ Real.exp C := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr hcd
    have heq : F' t = Complex.exp (complexSegment c d t)*((d-c)-(b-a)) +
        (Complex.exp (complexSegment c d t)-Complex.exp (complexSegment a b t))*(b-a) := by
      dsimp [F']; ring
    rw [heq]
    calc
      _ ≤ ‖Complex.exp (complexSegment c d t)*((d-c)-(b-a))‖ +
          ‖(Complex.exp (complexSegment c d t)-Complex.exp (complexSegment a b t))*(b-a)‖ :=
        norm_add_le _ _
      _ ≤ Real.exp C*‖(d-c)-(b-a)‖ + (Real.exp C*D)*‖b-a‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
      _ = _ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound
  have heq : (Complex.exp d-Complex.exp c)-(Complex.exp b-Complex.exp a) =
      (Complex.exp d-Complex.exp b)-(Complex.exp c-Complex.exp a) := by ring
  rw [heq]
  simpa only [F, complexSegment, sub_self, zero_smul, one_smul, zero_add,
    sub_zero, add_zero] using h

/-- The endpoint-plus-variation norm of a moving exponential difference
is controlled by the logarithmic differences and their variation. -/
theorem exponential_sequence_difference_variation (L M : ℕ → ℂ) (N : ℕ)
    (C D V W : ℝ) (hD : 0 ≤ D)
    (hL : ∀ j ≤ N, (L j).re ≤ C) (hM : ∀ j ≤ N, (M j).re ≤ C)
    (hdiff : ∀ j ≤ N, ‖M j-L j‖ ≤ D)
    (hvar : (∑ j ∈ Finset.range N, ‖L (j+1)-L j‖) ≤ V)
    (hdvar : (∑ j ∈ Finset.range N, ‖(M (j+1)-M j)-(L (j+1)-L j)‖) ≤ W) :
    ‖Complex.exp (M N)-Complex.exp (L N)‖ +
      (∑ j ∈ Finset.range N,
        ‖(Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
          (Complex.exp (M j)-Complex.exp (L j))‖) ≤
      Real.exp C*(D+W+D*V) := by
  have hend := (norm_exp_sub_le_of_re_le (L N) (M N) C (hL N le_rfl) (hM N le_rfl)).trans
    (mul_le_mul_of_nonneg_left (hdiff N le_rfl) (Real.exp_pos C).le)
  have hsum : (∑ j ∈ Finset.range N,
      ‖(Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
        (Complex.exp (M j)-Complex.exp (L j))‖) ≤ Real.exp C*(W+D*V) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, Real.exp C*
          (‖(M (j+1)-M j)-(L (j+1)-L j)‖+D*‖L (j+1)-L j‖) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN := Finset.mem_range.mp hj
        have heq : (Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
            (Complex.exp (M j)-Complex.exp (L j)) =
            (Complex.exp (M (j+1))-Complex.exp (M j))-
            (Complex.exp (L (j+1))-Complex.exp (L j)) := by ring
        rw [heq]
        exact exp_increment_difference_bound (L j) (L (j+1)) (M j) (M (j+1)) C D
          (hL j (by omega)) (hL (j+1) (by omega)) (hM j (by omega))
          (hM (j+1) (by omega)) (hdiff j (by omega)) (hdiff (j+1) (by omega))
      _ = Real.exp C*((∑ j ∈ Finset.range N, ‖(M (j+1)-M j)-(L (j+1)-L j)‖) +
          D*(∑ j ∈ Finset.range N, ‖L (j+1)-L j‖)) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      _ ≤ Real.exp C*(W+D*V) := mul_le_mul_of_nonneg_left
        (add_le_add hdvar (mul_le_mul_of_nonneg_left hvar hD)) (Real.exp_pos C).le
  calc
    _ ≤ Real.exp C*D + Real.exp C*(W+D*V) := add_le_add hend hsum
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_ComplementaryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative motion of a mass fraction retains its complementary mass. -/

noncomputable section

namespace LipschitzHilbert

/-- The logarithm is Lipschitz on a positive half-line, with the sharp
reciprocal lower-bound constant. -/
theorem log_motion_of_lower_bound {x y c : ℝ} (hc : 0 < c)
    (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have hdir (a b : ℝ) (ha : c ≤ a) (hb : c ≤ b) :
      Real.log a - Real.log b ≤ |a - b| / c := by
    have ha0 : 0 < a := hc.trans_le ha
    have hb0 : 0 < b := hc.trans_le hb
    calc
      Real.log a - Real.log b = Real.log (a / b) :=
        (Real.log_div ha0.ne' hb0.ne').symm
      _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
      _ ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hb
  apply abs_le.mpr
  constructor
  · have h := hdir y x hy hx
    rw [abs_sub_comm y x] at h
    linarith
  · exact hdir x y hx hy

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

theorem radius_line_motion (T : SlopeBox) (s t : ℝ) (z : ℝ × ℝ) :
    |T.radius (lineShift s t z) - T.radius z| ≤
      |t| * (1 / T.length + |s - T.slope| / T.width) := by
  have hx : T.horizontal (lineShift s t z) - T.horizontal z = t / T.length := by
    unfold horizontal lineShift
    dsimp
    ring
  have hy : T.transverse (lineShift s t z) - T.transverse z =
      (s - T.slope) * t / T.width := by
    unfold transverse lineShift
    dsimp
    ring
  calc
    _ = |(|T.horizontal (lineShift s t z)| - |T.horizontal z|) +
        (|T.transverse (lineShift s t z)| - |T.transverse z|)| := by
      congr 1
      unfold radius
      ring
    _ ≤ |(|T.horizontal (lineShift s t z)| - |T.horizontal z|)| +
        |(|T.transverse (lineShift s t z)| - |T.transverse z|)| := abs_add_le _ _
    _ ≤ |T.horizontal (lineShift s t z) - T.horizontal z| +
        |T.transverse (lineShift s t z) - T.transverse z| :=
      add_le_add (abs_abs_sub_abs_le_abs_sub _ _) (abs_abs_sub_abs_le_abs_sub _ _)
    _ = _ := by
      rw [hx, hy, abs_div, abs_div, abs_mul, abs_of_pos T.length_pos,
        abs_of_pos T.width_pos]
      ring

theorem log_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    Real.log (T.weight K D z) = D * Real.log 2 - D * Real.log (1 + T.radius z / K) := by
  have hr := T.radius_nonnegative z
  have hbase : 0 < 1 + T.radius z / K := by positivity
  rw [weight, Real.log_mul (Real.rpow_pos_of_pos (by norm_num) D).ne'
    (Real.rpow_pos_of_pos hbase (-D)).ne', Real.log_rpow (by norm_num), Real.log_rpow hbase]
  ring

/-- No differentiability of absolute values is needed: the logarithm of the
actual weight has this global reference-line motion bound. -/
theorem log_weight_line_motion (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 0 ≤ D)
    (s t : ℝ) (z : ℝ × ℝ) :
    |Real.log (T.weight K D (lineShift s t z)) - Real.log (T.weight K D z)| ≤
      (D / K) * (1 / T.length + |s - T.slope| / T.width) * |t| := by
  have hb (w : ℝ × ℝ) : 1 ≤ 1 + T.radius w / K := by
    exact le_add_of_nonneg_right (div_nonneg (T.radius_nonnegative w) hK.le)
  have hlog := log_motion_of_lower_bound (by norm_num : (0 : ℝ) < 1)
    (hb (lineShift s t z)) (hb z)
  have heq : (1 + T.radius (lineShift s t z) / K) - (1 + T.radius z / K) =
      (T.radius (lineShift s t z) - T.radius z) / K := by ring
  rw [div_one, heq, abs_div, abs_of_pos hK] at hlog
  have hmove := T.radius_line_motion s t z
  rw [T.log_weight hK, T.log_weight hK]
  calc
    _ = |-(D * (Real.log (1 + T.radius (lineShift s t z) / K) -
        Real.log (1 + T.radius z / K)))| := by congr 1; ring
    _ = D * |Real.log (1 + T.radius (lineShift s t z) / K) -
        Real.log (1 + T.radius z / K)| := by
      rw [abs_neg, abs_mul, abs_of_nonneg hD]
    _ ≤ D * (|T.radius (lineShift s t z) - T.radius z| / K) :=
      mul_le_mul_of_nonneg_left hlog hD
    _ ≤ D * ((|t| * (1 / T.length + |s - T.slope| / T.width)) / K) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmove hK.le) hD
    _ = _ := by ring

end SlopeBox

/-- Termwise logarithmic motion is inherited by every nonempty positive
subsum, with the same constant. This applies equally to complementary masses. -/
theorem positive_sum_log_motion {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (a b : ι → ℝ) {δ : ℝ}
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i)
    (hmotion : ∀ i ∈ s, |Real.log (b i) - Real.log (a i)| ≤ δ) :
    |Real.log (∑ i ∈ s, b i) - Real.log (∑ i ∈ s, a i)| ≤ δ := by
  have hsumA : 0 < ∑ i ∈ s, a i := Finset.sum_pos ha hne
  have hsumB : 0 < ∑ i ∈ s, b i := Finset.sum_pos hb hne
  have hupper (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
      (h : Real.log x - Real.log y ≤ δ) : x ≤ Real.exp δ * y := by
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ ≤ Real.exp (δ + Real.log y) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hy]
  have hBA : (∑ i ∈ s, b i) ≤ Real.exp δ * ∑ i ∈ s, a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hupper (b i) (a i) (hb i hi) (ha i hi)
      (abs_le.mp (hmotion i hi)).2
  have hAB : (∑ i ∈ s, a i) ≤ Real.exp δ * ∑ i ∈ s, b i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hupper (a i) (b i) (ha i hi) (hb i hi) (by
      have h := (abs_le.mp (hmotion i hi)).1
      linarith)
  have hlogBA := Real.log_le_log hsumB hBA
  have hlogAB := Real.log_le_log hsumA hAB
  rw [Real.log_mul (Real.exp_pos _).ne' hsumA.ne', Real.log_exp] at hlogBA
  rw [Real.log_mul (Real.exp_pos _).ne' hsumB.ne', Real.log_exp] at hlogAB
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The manuscript's mass motion bound for any fixed nonempty top set,
proved directly from its actual weights on every reference line. -/
theorem top_mass_log_line_motion {ι : Type*} (tops : ι → SlopeBox) (a : Finset ι)
    (hne : a.Nonempty) {K D C : ℝ} (hK : 0 < K) (hD : 0 ≤ D)
    (s t : ℝ) (z : ℝ × ℝ)
    (hlocal : ∀ i ∈ a,
      (D / K) * (1 / (tops i).length + |s - (tops i).slope| / (tops i).width) ≤ C) :
    |Real.log (∑ i ∈ a, (tops i).weight K D (SlopeBox.lineShift s t z)) -
      Real.log (∑ i ∈ a, (tops i).weight K D z)| ≤ C * |t| := by
  apply positive_sum_log_motion a hne
    (fun i => (tops i).weight K D z)
    (fun i => (tops i).weight K D (SlopeBox.lineShift s t z))
    (fun i _ => (tops i).weight_pos hK D z)
    (fun i _ => (tops i).weight_pos hK D _)
  intro i hi
  exact ((tops i).log_weight_line_motion hK hD s t z).trans
    (mul_le_mul_of_nonneg_right (hlocal i hi) (abs_nonneg t))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated nested angular grids and their actual eligible-top masses. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace AngularGrid

theorem index_parent (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.index (level + 1) slope / (g.branching : ℤ) = g.index level slope := by
  have hG : g.branching ≠ 0 := by have h := g.branching_ge_two; omega
  simpa only [index, pow_succ, mul_assoc] using
    (Int.mul_natCast_floor_div_cancel hG
      (((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level))

variable {ι X : Type*}

theorem cellTops_subset_parent (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (level : ℕ) (child : ℤ) :
    g.cellTops tops slope precision cutoff (level + 1) child ⊆
      g.cellTops tops slope precision cutoff level (child / (g.branching : ℤ)) := by
  intro i hi
  obtain ⟨hit, hindex, heligible⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  apply (g.mem_cellTops _ _ _ _ _ _ _).2
  refine ⟨hit, ?_, g.eligible_parent (hp i hit) level heligible⟩
  rw [← g.index_parent level (slope i), hindex]

theorem mass_pos_of_member (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (cell : ℤ) (x : X) {i : ι}
    (hi : i ∈ g.cellTops tops slope precision cutoff level cell) :
    0 < g.mass tops slope precision cutoff weight level cell x := by
  classical
  exact (hw i x).trans_le (Finset.single_le_sum (fun j _ => (hw j x).le) hi)

/-- An eligible top supplies a strictly positive summand on its own path. -/
theorem path_mass_pos (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (top : ι) (htop : top ∈ tops) (heligible : g.eligible cutoff (precision top) level)
    (x : X) : 0 < g.mass tops slope precision cutoff weight level (g.index level (slope top)) x :=
  g.mass_pos_of_member tops slope precision cutoff weight hw level _ x
    ((g.mem_cellTops _ _ _ _ _ _ _).2 ⟨htop, rfl, heligible⟩)

/-- Every angular mass is a submass of the fixed total top weight. -/
theorem mass_le_total (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (level : ℕ) (cell : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight level cell x ≤ ∑ i ∈ tops, weight i x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro i _ _
    exact hw i x

/-- Child mass is at most parent mass, with the eligibility restriction
already built into both finite sums. -/
theorem mass_le_parent (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (level : ℕ) (child : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) child x ≤
      g.mass tops slope precision cutoff weight level (child / (g.branching : ℤ)) x := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (g.cellTops_subset_parent tops slope precision cutoff hp level child) (fun i _ _ => hw i x)

/-- Along any fixed top's angular path the actual mass is antitone. -/
theorem path_mass_antitone (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (top : ι) (x : X) :
    Antitone fun level => g.mass tops slope precision cutoff weight level (g.index level (slope top)) x := by
  apply antitone_nat_of_succ_le
  intro level
  simpa only [g.index_parent] using
    g.mass_le_parent tops slope precision cutoff weight hp hw level (g.index (level + 1) (slope top)) x

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric separation in the actual translated angular grid. -/

noncomputable section

namespace LipschitzHilbert.AngularGrid

/-- The floor assignment is exactly the half-open translated interval. -/
theorem slope_mem_cell (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.left level (g.index level slope) ≤ slope ∧
      slope < g.left level (g.index level slope) + g.width level := by
  let a := ((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level
  have hlow := Int.floor_le a
  have hhigh := Int.lt_floor_add_one a
  have heq : g.width level * a = slope - g.origin := by
    unfold width a
    have hG : (g.branching : ℝ) ≠ 0 := by
      exact_mod_cast (show g.branching ≠ 0 by have h := g.branching_ge_two; omega)
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
  have hlow' := mul_le_mul_of_nonneg_left hlow (g.width_pos level).le
  have hhigh' := mul_lt_mul_of_pos_left hhigh (g.width_pos level)
  rw [heq] at hlow' hhigh'
  change g.origin + g.width level * (⌊a⌋ : ℝ) ≤ slope ∧
    slope < g.origin + g.width level * (⌊a⌋ : ℝ) + g.width level
  constructor <;> nlinarith

theorem slope_dist_center_le (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    |slope - g.center level (g.index level slope)| ≤ g.width level / 2 := by
  obtain ⟨hl, hr⟩ := g.slope_mem_cell level slope
  unfold center
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem same_cell_diameter (g : AngularGrid) (level : ℕ) {s t : ℝ}
    (hcell : g.index level s = g.index level t) : |s - t| ≤ g.width level := by
  obtain ⟨hs0, hs1⟩ := g.slope_mem_cell level s
  obtain ⟨ht0, ht1⟩ := g.slope_mem_cell level t
  rw [hcell] at hs0 hs1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem eligible_iff_precision_le (g : AngularGrid) (cutoff precision : ℝ) (level : ℕ) :
    g.eligible cutoff precision level ↔ precision ≤ cutoff / (g.branching : ℝ) ^ level := by
  have hG : (0 : ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have h := g.branching_ge_two; omega)
  exact (le_div_iff₀ (pow_pos hG level)).symm

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses formed from actual top sets in a common angular ancestor. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_eq_of_add (g : AngularGrid) (base steps : ℕ) {s t : ℝ}
    (h : g.index (base + steps) s = g.index (base + steps) t) :
    g.index base s = g.index base t := by
  induction steps with
  | zero => simpa using h
  | succ steps ih =>
    apply ih
    rw [← g.index_parent (base + steps) s, ← g.index_parent (base + steps) t]
    simpa only [Nat.add_succ] using congrArg (fun a : ℤ => a / g.branching) h

theorem index_eq_of_le (g : AngularGrid) {base level : ℕ} (hle : base ≤ level)
    {s t : ℝ} (h : g.index level s = g.index level t) :
    g.index base s = g.index base t := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact g.index_eq_of_add base steps h

/-- Tops in a descendant cell remain eligible and lie in its actual ancestor. -/
theorem cellTops_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  intro i hi
  obtain ⟨hit, hindex, he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  exact (g.mem_cellTops _ _ _ _ _ _ _).2
    ⟨hit, g.index_eq_of_le hle hindex, g.eligible_of_le (hp i hit) hle he⟩

theorem parent_subset_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.boundaryTops tops slope precision cutoff base level gap s := by
  classical
  exact Finset.subset_union_left

theorem boundary_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) :
    g.boundaryTops tops slope precision cutoff base level gap s ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  classical
  apply Finset.union_subset
  · exact g.cellTops_subset_ancestor tops slope precision cutoff hp hle s
  · exact Finset.filter_subset _ _

/-- The immediate child, parent, boundary and block ancestor have ordered masses. -/
theorem boundary_mass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) (g.index (level + 1) s) x ≤
        g.mass tops slope precision cutoff weight level (g.index level s) x ∧
    g.mass tops slope precision cutoff weight level (g.index level s) x ≤
        g.boundaryMass tops slope precision cutoff weight base level gap s x ∧
    g.boundaryMass tops slope precision cutoff weight base level gap s x ≤
        g.mass tops slope precision cutoff weight base (g.index base s) x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := g.mass_le_parent tops slope precision cutoff weight hp hw level
      (g.index (level + 1) s) x
    simpa only [g.index_parent] using h
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.parent_subset_boundary tops slope precision cutoff base level gap s)
      (fun i _ _ => hw i x)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.boundary_subset_ancestor tops slope precision cutoff hp hle gap s)
      (fun i _ _ => hw i x)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundaryLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality of every top entering a boundary mass, including boundaries
whose block ancestor starts before the current path cell. The estimate uses
the immediate child-neighbor relation and therefore does not depend on that
ancestor's width. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem width_antitone (g : AngularGrid) : Antitone g.width := by
  intro h i hhi
  have hG : (1:ℝ) ≤ g.branching := by
    exact_mod_cast (show 1 ≤ g.branching by have := g.branching_ge_two; omega)
  unfold width
  exact div_le_div_of_nonneg_left g.rootWidth_pos.le (by positivity)
    (pow_le_pow_right₀ hG hhi)

/-- Neighboring children control all slopes in those children. -/
theorem slopes_close_of_neighbors (g : AngularGrid) (level : ℕ) (gap s t : ℝ)
    (hnear : g.neighbors level gap (g.index level s) (g.index level t)) :
    |s-t| ≤ gap + 2*g.width level := by
  have hs := g.slope_dist_center_le level s
  have ht := g.slope_dist_center_le level t
  have hc : |g.center level (g.index level s)-g.center level (g.index level t)| <
      gap+g.width level := hnear
  have htriangle : |s-t| ≤ |s-g.center level (g.index level s)| +
      |g.center level (g.index level s)-g.center level (g.index level t)| +
      |g.center level (g.index level t)-t| := by
    calc
      _ = |(s-g.center level (g.index level s)) +
          (g.center level (g.index level s)-g.center level (g.index level t)) +
          (g.center level (g.index level t)-t)| := by congr 1; ring
      _ ≤ |(s-g.center level (g.index level s)) +
          (g.center level (g.index level s)-g.center level (g.index level t))| +
          |g.center level (g.index level t)-t| := abs_add_le _ _
      _ ≤ _ := add_le_add
        (abs_add_le (s-g.center level (g.index level s))
          (g.center level (g.index level s)-g.center level (g.index level t))) le_rfl
  rw [abs_sub_comm (g.center level (g.index level t)) t] at htriangle
  linarith

/-- The immediate-child neighborhood gives locality even when `base < h`.
All such tops are also eligible at the current path level `h`. -/
theorem boundaryTop_locality (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap : 0 ≤ gap)
    (s sR : ℝ) (hs : g.index h s = g.index h sR) {t : ι}
    (ht : t ∈ g.boundaryTops tops slope precision cutoff base i gap s) :
    t ∈ tops ∧ g.eligible cutoff (precision t) h ∧
      |slope t-sR| ≤ 3*g.width h+gap := by
  have hwidth := g.width_pos h
  rcases Finset.mem_union.mp ht with hparent | hnear
  · obtain ⟨htt,hcell,he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp hparent
    have hcellh : g.index h (slope t) = g.index h sR :=
      (g.index_eq_of_le hhi hcell).trans hs
    refine ⟨htt,g.eligible_of_le (hp t htt) hhi he,?_⟩
    have hd := g.same_cell_diameter h hcellh
    linarith
  · obtain ⟨hbase,he,hneighbors,_⟩ := Finset.mem_filter.mp hnear
    have htt := ((g.mem_cellTops _ _ _ _ _ _ _).mp hbase).1
    have hd := g.slopes_close_of_neighbors (i+1) gap s (slope t) hneighbors
    have hsR := g.same_cell_diameter h hs
    have hw := g.width_antitone (hhi.trans (Nat.le_succ i))
    refine ⟨htt,g.eligible_of_le (hp t htt) (hhi.trans (Nat.le_succ i)) he,?_⟩
    have htriangle : |slope t-sR| ≤ |slope t-s|+|s-sR| := by
      simpa only [sub_add_sub_cancel] using abs_add_le (slope t-s) (s-sR)
    rw [abs_sub_comm (slope t) s] at htriangle
    linarith

/-- Every nonempty submass, including a complementary top set, inherits
its logarithmic line-motion bound from the concrete boundary locality. -/
theorem boundary_submass_log_line_motion (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w W cutoff K D : ℝ) (hw : 0 < w) (hW : 0 < W)
    (hK : 0 < K) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, W ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap : 0 ≤ gap)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (A : Finset ι) (hA : A.Nonempty)
    (hsub : A ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cutoff base i gap s)
    (a : ℝ) (z : ℝ × ℝ) :
    |Real.log (∑ t ∈ A, (T t).weight K D (SlopeBox.lineShift sR a z)) -
      Real.log (∑ t ∈ A, (T t).weight K D z)| ≤
        ((D/K) * (cutoff/((g.branching:ℝ)^h*w) + (3*g.width h+gap)/W)) * |a| := by
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ w/(T t).length :=
    (div_pos hw (T t).length_pos).le
  apply top_mass_log_line_motion T A hA hK hD sR a z
  intro t ht
  have hlocal := g.boundaryTop_locality tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cutoff hp base h i hhi gap hgap s sR hs (hsub ht)
  have hprec := (g.eligible_iff_precision_le cutoff (w/(T t).length) h).mp hlocal.2.1
  have hlength : 1/(T t).length ≤ cutoff/((g.branching:ℝ)^h*w) := by
    calc
      1/(T t).length = (w/(T t).length)/w := by
        field_simp [hw.ne', (T t).length_pos.ne']
      _ ≤ (cutoff/(g.branching:ℝ)^h)/w := div_le_div_of_nonneg_right hprec hw.le
      _ = _ := div_div _ _ _
  have hR : 0 ≤ 3*g.width h+gap := by have := g.width_pos h; positivity
  have hslope : |sR-(T t).slope|/(T t).width ≤ (3*g.width h+gap)/W := by
    calc
      _ ≤ (3*g.width h+gap)/(T t).width :=
        div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hlocal.2.2)
          (T t).width_pos.le
      _ ≤ _ := div_le_div_of_nonneg_left hR hW (hwidth t hlocal.1)
  exact mul_le_mul_of_nonneg_left (add_le_add hlength hslope) (div_nonneg hD hK.le)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual last eligible angular level exists for every positive
precision. Packet stopping precedes the stopping of its assigned top. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem eligible_iff_le_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) (n : ℕ) :
    g.eligible cutoff precision n ↔ n ≤ g.lastEligible cutoff precision hp := by
  let h := g.exists_ineligible cutoff precision hp
  have hfirst : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    apply Nat.find_spec h
    simpa only [hz] using hstart
  constructor
  · intro hn
    by_contra hle
    have hfind : Nat.find h ≤ n := by
      change ¬n ≤ Nat.find h - 1 at hle
      omega
    exact Nat.find_spec h (g.eligible_of_le hp.le hfind hn)
  · intro hn
    have hlt : n < Nat.find h := by
      change n ≤ Nat.find h - 1 at hn
      omega
    exact Classical.not_not.mp (Nat.find_min h hlt)

theorem eligible_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) :
    g.eligible cutoff precision (g.lastEligible cutoff precision hp) :=
  (g.eligible_iff_le_lastEligible cutoff precision hp hstart _).mpr le_rfl

theorem lastEligible_antitone_precision (g : AngularGrid) (cutoff p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q)
    (hstartp : g.eligible cutoff p 0) (hstartq : g.eligible cutoff q 0) :
    g.lastEligible cutoff q hq ≤ g.lastEligible cutoff p hp := by
  apply (g.eligible_iff_le_lastEligible cutoff p hp hstartp _).mp
  have hqelig := g.eligible_lastEligible cutoff q hq hstartq
  exact (mul_le_mul_of_nonneg_right hpq (by positivity)).trans hqelig

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses and logarithmic variation along actual eligible top
paths. Every boundary uses the start of the block whose last transition
is the current level, in the shared family of all shifted groupings. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_center (g : AngularGrid) (level : ℕ) (cell : ℤ) :
    g.index level (g.center level cell) = cell := by
  have hG : (g.branching : ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have heq : ((g.center level cell - g.origin) / g.rootWidth) *
      (g.branching : ℝ)^level = (cell : ℝ) + 1/2 := by
    unfold center left width
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
    ring
  unfold index
  rw [heq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num

theorem boundaryTops_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) {base level : ℕ} (hle : base ≤ level)
    (gap : ℝ) {s t : ℝ} (hc : g.index (level+1) s = g.index (level+1) t) :
    g.boundaryTops tops slope precision cutoff base level gap s =
      g.boundaryTops tops slope precision cutoff base level gap t := by
  have hp := g.index_eq_of_le (Nat.le_succ level) hc
  have ha := g.index_eq_of_le (hle.trans (Nat.le_succ level)) hc
  simp only [boundaryTops, outsideNearTops, hp, ha, hc]

theorem boundaryMass_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {base level : ℕ} (hle : base ≤ level) (gap : ℝ) {s t : ℝ}
    (hc : g.index (level+1) s = g.index (level+1) t) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.boundaryMass tops slope precision cutoff weight base level gap t x := by
  unfold boundaryMass
  rw [g.boundaryTops_eq_of_cell tops slope precision cutoff hle gap hc]

theorem sourceBoundaryMass_path (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level
        (g.index (level+1) s) x =
      g.boundaryMass tops slope precision cutoff weight (level+1-K) level (gap level) s x := by
  apply g.boundaryMass_eq_of_cell tops slope precision cutoff weight (by omega)
  exact g.index_center (level+1) _

theorem sourceBoundaryMass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level+1) (g.index (level+1) s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ∧
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ≤
      g.mass tops slope precision cutoff weight (level+1-K) (g.index (level+1-K) s) x := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK gap]
  have h := g.boundary_mass_bounds tops slope precision cutoff weight hp hw
    (by omega : level+1-K ≤ level) (gap level) s x
  exact ⟨h.1.trans h.2.1, h.2.2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularMassMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source averaging scale makes every boundary submass move
by order G^(-1/2), including submasses from other shifted blocks. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- The two locality terms are small on the manuscript's averaging cell.
The stronger B² eligibility and width hypotheses retain a spare factor B. -/
theorem source_mass_motion_budget {rho child w B G gap a : ℝ}
    (_hrho : 0 < rho) (hchild : 0 < child) (hw : 0 < w)
    (hB : 1 ≤ B) (hG : 0 < G) (hgap : gap ≤ rho)
    (hblock : rho ≤ B*child) (ha : |a| ≤ w/(child*Real.sqrt G)) :
    (rho/(B^2*w)+(3*rho+gap)/(B^2*w))*|a| ≤ 5/Real.sqrt G := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hroot : 0 < Real.sqrt G := Real.sqrt_pos.mpr hG
  have hden : 0 < B^2*w := mul_pos (sq_pos_of_pos hB0) hw
  have hra : rho*|a| ≤ B*w/Real.sqrt G := by
    calc
      _ ≤ (B*child)*(w/(child*Real.sqrt G)) :=
        mul_le_mul hblock ha (abs_nonneg _) (mul_pos hB0 hchild).le
      _ = _ := by field_simp [hchild.ne', hroot.ne']
  calc
    _ = ((4*rho+gap)*|a|)/(B^2*w) := by ring
    _ ≤ (5*(rho*|a|))/(B^2*w) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith [abs_nonneg a]
    _ ≤ (5*(B*w/Real.sqrt G))/(B^2*w) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hra (by norm_num)) hden.le
    _ = (5/Real.sqrt G)/B := by field_simp [hB0.ne', hw.ne', hroot.ne']
    _ ≤ 5/Real.sqrt G := div_le_self (by positivity) hB

namespace AngularGrid

variable {ι : Type*}

/-- At H=w/(child sqrt G), concrete boundary submasses have uniformly
small logarithmic motion. Here the top width lower bound is exactly the
consequence W=m w≥B²w used in the source. -/
theorem boundary_submass_source_motion (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (A : Finset ι) (hA : A.Nonempty)
    (hsub : A ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (a : ℝ) (ha : |a| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    |Real.log (∑ t ∈ A, (T t).weight K D (SlopeBox.lineShift sR a z)) -
      Real.log (∑ t ∈ A, (T t).weight K D z)| ≤
        (5*D/K)/Real.sqrt (g.branching:ℝ) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hG : (0:ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have := g.branching_ge_two; omega)
  have hmotion := g.boundary_submass_log_line_motion tops T w (B^2*w) (g.rootWidth/B^2)
    K D hw (mul_pos (sq_pos_of_pos hB0) hw) hK hD hwidth base h i hhi gap hgap0
    s sR hs A hA hsub a z
  have heq : (g.rootWidth/B^2)/((g.branching:ℝ)^h*w) = g.width h/(B^2*w) := by
    simp only [width, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at hmotion
  have hbudget := source_mass_motion_budget (g.width_pos h) hchild hw hB hG hgap hblock ha
  calc
    _ ≤ (D/K)*(g.width h/(B^2*w)+(3*g.width h+gap)/(B^2*w))*|a| := hmotion
    _ = (D/K)*((g.width h/(B^2*w)+(3*g.width h+gap)/(B^2*w))*|a|) := by ring
    _ ≤ (D/K)*(5/Real.sqrt (g.branching:ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget (div_nonneg hD hK.le)
    _ = _ := by ring

end AngularGrid

/-- Moving numerator and denominator logarithms give the exact uniform
bound needed for one child-to-boundary ratio. -/
theorem positive_ratio_log_motion {a b a' b' delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hA : |Real.log a'-Real.log a| ≤ delta)
    (hB : |Real.log b'-Real.log b| ≤ delta) :
    |Real.log (a'/b')-Real.log (a/b)| ≤ 2*delta := by
  rw [Real.log_div ha'.ne' hb'.ne', Real.log_div ha.ne' hb.ne']
  calc
    _ = |(Real.log a'-Real.log a)-(Real.log b'-Real.log b)| := by congr 1; ring
    _ ≤ |Real.log a'-Real.log a|+|Real.log b'-Real.log b| := abs_sub _ _
    _ ≤ _ := by linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MovingSegmentLogs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial value and loss budget for the actual moving segment
logarithms. The total cost is paid by the full-root loss, including when
another shift's block begins before the segment. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- At the starting endpoint the transition product is empty, so only
the one initial mass logarithm moves. -/
theorem segmentLog_initial_motion (n n' R R' : ℕ → ℝ) (phase : ℕ → ℂ)
    (a delta : ℝ) (start : ℕ) (ha : 0 ≤ a)
    (hlog : |Real.log (n' start)-Real.log (n start)| ≤ delta) :
    ‖segmentLog n' R' phase a start start-segmentLog n R phase a start start‖ ≤ a*delta := by
  have heq : segmentLog n' R' phase a start start-segmentLog n R phase a start start =
      ((-a*(Real.log (n' start)-Real.log (n start)) : ℝ) : ℂ) := by
    simp only [segmentLog, Finset.Ico_self, Finset.sum_empty, sub_zero]
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left hlog ha

theorem segmentCost_nonnegative (n R : ℕ → ℝ) (a Z : ℝ) (j : ℕ)
    (ha : 0 ≤ a) (hZ : 0 ≤ Z) (hn : 0 < n (j+1)) (hm : n (j+1) ≤ n j) (hR : 0 ≤ R j) :
    0 ≤ segmentCost n R a Z j := by
  exact add_nonneg (mul_nonneg ha (Real.log_nonneg ((one_le_div hn).mpr hm))) (mul_nonneg hZ hR)

theorem segmentLog_increment_le_cost (n R : ℕ → ℝ) (phase : ℕ → ℂ)
    (a Z : ℝ) (start j : ℕ) (hs : start ≤ j) (ha : 0 ≤ a) (_hZ : 0 ≤ Z)
    (hn : 0 < n (j+1)) (hm : n (j+1) ≤ n j) (hR : 0 ≤ R j) (hz : ‖phase j‖ ≤ Z) :
    ‖segmentLog n R phase a start (j+1)-segmentLog n R phase a start j‖ ≤
      segmentCost n R a Z j := by
  rw [segmentLog_increment n R phase a start j hs (hn.trans_le hm) hn]
  exact (logarithm_increment_bound a _ _ _ ha
    (Real.log_nonneg ((one_le_div hn).mpr hm)) hR).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hz hR))

/-- Summing the nonnegative costs on any later segment uses the full-root
logarithm rather than a factor counting hierarchy levels. -/
theorem segmentCost_sum_le_full_root (n R : ℕ → ℝ) (start N K : ℕ)
    (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, 0 < n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j+1-K)/n (j+1))) :
    (∑ j ∈ Finset.Ico start N, segmentCost n R a Z j) ≤
      (a+Z*K)*Real.log (n 0/n N) := by
  have hnonneg (j : ℕ) (hj : j < N) : 0 ≤ segmentCost n R a Z j :=
    segmentCost_nonnegative n R a Z j ha hZ (hn (j+1) (by omega))
      (hmono (by change j ≤ N; omega) (by change j+1 ≤ N; omega) (by omega)) (hR0 j hj)
  calc
    _ ≤ ∑ j ∈ Finset.range N, segmentCost n R a Z j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      · intro j hj _
        exact hnonneg j (Finset.mem_range.mp hj)
    _ = a*Real.log (n 0/n N)+Z*(∑ j ∈ Finset.range N, R j) := by
      simp only [segmentCost, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [sum_log_ratios n N hn]
    _ ≤ a*Real.log (n 0/n N)+Z*((K:ℝ)*Real.log (n 0/n N)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (full_root_log_variation n R N K hn hmono hR) hZ)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MovingWeightBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite endpoint transport from the actual logarithmic loss budget.
Small relative errors are summed against losses, without charging a fixed
error for every hierarchy level. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem exponential_weight_motion_from_increments (L M : ℕ → ℂ) (cost : ℕ → ℝ)
    (N : ℕ) (C D ε V : ℝ) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hL : ∀ j ≤ N, (L j).re ≤ C) (hM : ∀ j ≤ N, (M j).re ≤ C)
    (hzero : ‖M 0-L 0‖ ≤ D)
    (hcost : ∀ j < N, 0 ≤ cost j)
    (hincr : ∀ j < N, ‖L (j+1)-L j‖ ≤ cost j)
    (hmove : ∀ j < N, ‖(M (j+1)-M j)-(L (j+1)-L j)‖ ≤ ε*cost j)
    (hbudget : (∑ j ∈ Finset.range N, cost j) ≤ V) :
    ‖Complex.exp (M N)-Complex.exp (L N)‖ +
      (∑ j ∈ Finset.range N,
        ‖(Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
          (Complex.exp (M j)-Complex.exp (L j))‖) ≤
      Real.exp C*((D+ε*V)+ε*V+(D+ε*V)*V) := by
  have hpartial (k : ℕ) (hk : k ≤ N) :
      ‖M k-L k‖ ≤ D+ε*(∑ j ∈ Finset.range k, cost j) := by
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have hkN : k < N := by omega
      have heq : M (k+1)-L (k+1) = (M k-L k)+((M (k+1)-M k)-(L (k+1)-L k)) := by ring
      rw [heq, Finset.sum_range_succ]
      calc
        _ ≤ ‖M k-L k‖+‖(M (k+1)-M k)-(L (k+1)-L k)‖ := norm_add_le _ _
        _ ≤ (D+ε*(∑ j ∈ Finset.range k, cost j))+ε*cost k :=
          add_le_add (ih (by omega)) (hmove k hkN)
        _ = _ := by ring
  have hdiff (k : ℕ) (hk : k ≤ N) : ‖M k-L k‖ ≤ D+ε*V := by
    apply (hpartial k hk).trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ hε
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun j hj _ => hcost j (Finset.mem_range.mp hj))).trans hbudget
  apply exponential_sequence_difference_variation L M N C (D+ε*V) V (ε*V)
    (by positivity) hL hM hdiff
  · exact (Finset.sum_le_sum (fun j hj => hincr j (Finset.mem_range.mp hj))).trans hbudget
  · calc
      _ ≤ ∑ j ∈ Finset.range N, ε*cost j :=
        Finset.sum_le_sum (fun j hj => hmove j (Finset.mem_range.mp hj))
      _ = ε*(∑ j ∈ Finset.range N, cost j) := (Finset.mul_sum _ _ _).symm
      _ ≤ ε*V := mul_le_mul_of_nonneg_left hbudget hε

/-- The same transport bound on any interval of later endpoints. -/
theorem exponential_weight_motion_on_interval (L M : ℕ → ℂ) (cost : ℕ → ℝ)
    (start N : ℕ) (hstart : start ≤ N) (C D ε V : ℝ)
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hL : ∀ j, start ≤ j → j ≤ N → (L j).re ≤ C)
    (hM : ∀ j, start ≤ j → j ≤ N → (M j).re ≤ C)
    (hzero : ‖M start-L start‖ ≤ D)
    (hcost : ∀ j ∈ Finset.Ico start N, 0 ≤ cost j)
    (hincr : ∀ j ∈ Finset.Ico start N, ‖L (j+1)-L j‖ ≤ cost j)
    (hmove : ∀ j ∈ Finset.Ico start N,
      ‖(M (j+1)-M j)-(L (j+1)-L j)‖ ≤ ε*cost j)
    (hbudget : (∑ j ∈ Finset.Ico start N, cost j) ≤ V) :
    ‖Complex.exp (M N)-Complex.exp (L N)‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖(Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
          (Complex.exp (M j)-Complex.exp (L j))‖) ≤
      Real.exp C*((D+ε*V)+ε*V+(D+ε*V)*V) := by
  have hshift (j : ℕ) (hj : j < N-start) : start+j ∈ Finset.Ico start N :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hb : (∑ j ∈ Finset.range (N-start), cost (start+j)) ≤ V := by
    simpa only [Finset.sum_Ico_eq_sum_range] using hbudget
  have h := exponential_weight_motion_from_increments
    (fun j => L (start+j)) (fun j => M (start+j)) (fun j => cost (start+j))
    (N-start) C D ε V hD hε hV
    (fun j hj => hL _ (by omega) (by omega))
    (fun j hj => hM _ (by omega) (by omega)) (by simpa using hzero)
    (fun j hj => hcost _ (hshift j hj))
    (fun j hj => by simpa only [Nat.add_assoc] using hincr _ (hshift j hj))
    (fun j hj => by simpa only [Nat.add_assoc] using hmove _ (hshift j hj)) hb
  have hend : start+(N-start)=N := by omega
  simpa only [Finset.sum_Ico_eq_sum_range, hend, Nat.add_assoc] using h

/-- A moving endpoint increment is controlled by relative errors in the
parent loss and boundary loss, with exactly the original weighted cost. -/
theorem segmentLog_increment_motion (n n' R R' : ℕ → ℝ) (phase : ℕ → ℂ)
    (a ε Z : ℝ) (start j : ℕ) (hs : start ≤ j)
    (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hn : 0 < n j) (hn1 : 0 < n (j+1))
    (hn' : 0 < n' j) (hn1' : 0 < n' (j+1))
    (hP : |Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1))| ≤
      ε*Real.log (n j/n (j+1)))
    (hR : |R' j-R j| ≤ ε*R j) (hz : ‖phase j‖ ≤ Z) :
    ‖(segmentLog n' R' phase a start (j+1)-segmentLog n' R' phase a start j)-
      (segmentLog n R phase a start (j+1)-segmentLog n R phase a start j)‖ ≤
      ε*(a*Real.log (n j/n (j+1))+Z*R j) := by
  rw [segmentLog_increment n' R' phase a start j hs hn' hn1',
    segmentLog_increment n R phase a start j hs hn hn1]
  have heq : (((a*Real.log (n' j/n' (j+1)):ℝ):ℂ)-phase j*(R' j:ℂ))-
      (((a*Real.log (n j/n (j+1)):ℝ):ℂ)-phase j*(R j:ℂ)) =
      (a:ℂ)*((Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1)):ℝ):ℂ)-
        phase j*((R' j-R j:ℝ):ℂ) := by push_cast; ring
  rw [heq]
  calc
    _ ≤ ‖(a:ℂ)*((Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1)):ℝ):ℂ)‖+
        ‖phase j*((R' j-R j:ℝ):ℂ)‖ := norm_sub_le _ _
    _ = a*|Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1))|+
        ‖phase j‖*|R' j-R j| := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ a*(ε*Real.log (n j/n (j+1)))+Z*(ε*R j) := add_le_add
      (mul_le_mul_of_nonneg_left hP ha)
      (mul_le_mul hz hR (abs_nonneg _) hZ)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MovingSegmentWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint weight motion from the relative parent and boundary losses.
The full-root loss is used only at the snapshot. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem segmentLog_re_le_of_log_motion (n n' R' : ℕ → ℝ) (phase : ℕ → ℂ)
    (a δ lower : ℝ) (start k : ℕ) (ha : 0 ≤ a) (hlower : 0 < lower)
    (hn : lower ≤ n k) (hmove : |Real.log (n' k)-Real.log (n k)| ≤ δ)
    (hR : ∀ i < k, 0 ≤ R' i) (hz : ∀ i < k, 0 ≤ (phase i).re) :
    (segmentLog n' R' phase a start k).re ≤ a*δ-a*Real.log lower := by
  have hlog := Real.log_le_log hlower hn
  have hlow : Real.log lower-δ ≤ Real.log (n' k) := by
    have hm := (abs_le.mp hmove).1
    linarith
  have hsum : 0 ≤ ∑ i ∈ Finset.Ico start k, (phase i).re*R' i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hz i (Finset.mem_Ico.mp hi).2)
      (hR i (Finset.mem_Ico.mp hi).2))
  simp only [segmentLog, Complex.sub_re, Complex.ofReal_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith

/-- The moving endpoint-plus-variation estimate on any later segment.
All error factors multiply the original loss budget, never the depth. -/
theorem moving_segmentWeight_variation (n n' R R' : ℕ → ℝ) (phase : ℕ → ℂ)
    (start N K : ℕ) (hstart : start ≤ N) (a Z δ ε lower : ℝ)
    (ha : 0 ≤ a) (hZ : 0 ≤ Z) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hlower : 0 < lower)
    (hn : ∀ j ≤ N, lower ≤ n j) (hn' : ∀ j ≤ N, 0 < n' j)
    (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j) (hR0' : ∀ j < N, 0 ≤ R' j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j+1-K)/n (j+1)))
    (hz0 : ∀ j < N, 0 ≤ (phase j).re) (hz : ∀ j < N, ‖phase j‖ ≤ Z)
    (hmass : ∀ j, start ≤ j → j ≤ N → |Real.log (n' j)-Real.log (n j)| ≤ δ)
    (hPmove : ∀ j ∈ Finset.Ico start N,
      |Real.log (n' j/n' (j+1))-Real.log (n j/n (j+1))| ≤ ε*Real.log (n j/n (j+1)))
    (hRmove : ∀ j ∈ Finset.Ico start N, |R' j-R j| ≤ ε*R j) :
    let V := (a+Z*K)*Real.log (n 0/n N)
    ‖segmentWeight n' R' phase a start N-segmentWeight n R phase a start N‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖(segmentWeight n' R' phase a start (j+1)-segmentWeight n R phase a start (j+1))-
          (segmentWeight n' R' phase a start j-segmentWeight n R phase a start j)‖) ≤
      (Real.exp (a*δ)*lower^(-a))*((a*δ+ε*V)+ε*V+(a*δ+ε*V)*V) := by
  dsimp only
  let V := (a+Z*K)*Real.log (n 0/n N)
  have hn0 (j : ℕ) (hj : j ≤ N) : 0 < n j := hlower.trans_le (hn j hj)
  have hparent (j : ℕ) (hj : j < N) : n (j+1) ≤ n j :=
    hmono (by change j ≤ N; omega) (by change j+1 ≤ N; omega) (by omega)
  have hlog : 0 ≤ Real.log (n 0/n N) :=
    Real.log_nonneg ((one_le_div (hn0 N le_rfl)).mpr
      (hmono (by change 0 ≤ N; omega) (by change N ≤ N; omega) (Nat.zero_le N)))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hL (j : ℕ) (_hj : start ≤ j) (hjN : j ≤ N) :
      (segmentLog n R phase a start j).re ≤ a*δ-a*Real.log lower := by
    apply (segmentLog_re_le n R phase a lower start j ha hlower (hn j hjN)
      (fun i hi => hR0 i (hi.trans_le hjN))
      (fun i hi => hz0 i (hi.trans_le hjN))).trans
    nlinarith
  have hM (j : ℕ) (hj : start ≤ j) (hjN : j ≤ N) :
      (segmentLog n' R' phase a start j).re ≤ a*δ-a*Real.log lower :=
    segmentLog_re_le_of_log_motion n n' R' phase a δ lower start j ha hlower (hn j hjN)
      (hmass j hj hjN) (fun i hi => hR0' i (hi.trans_le hjN))
      (fun i hi => hz0 i (hi.trans_le hjN))
  have h := exponential_weight_motion_on_interval
    (segmentLog n R phase a start) (segmentLog n' R' phase a start)
    (segmentCost n R a Z) start N hstart (a*δ-a*Real.log lower) (a*δ) ε V
    (mul_nonneg ha hδ) hε hV hL hM
    (segmentLog_initial_motion n n' R R' phase a δ start ha (hmass start le_rfl hstart))
    (fun j hj => segmentCost_nonnegative n R a Z j ha hZ
      (hn0 (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega))
      (hparent j (Finset.mem_Ico.mp hj).2) (hR0 j (Finset.mem_Ico.mp hj).2))
    (fun j hj => segmentLog_increment_le_cost n R phase a Z start j
      (Finset.mem_Ico.mp hj).1 ha hZ
      (hn0 (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega))
      (hparent j (Finset.mem_Ico.mp hj).2) (hR0 j (Finset.mem_Ico.mp hj).2)
      (hz j (Finset.mem_Ico.mp hj).2))
    (fun j hj => segmentLog_increment_motion n n' R R' phase a ε Z start j
      (Finset.mem_Ico.mp hj).1 ha hZ
      (hn0 j (Nat.le_of_lt (Finset.mem_Ico.mp hj).2))
      (hn0 (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega))
      (hn' j (Nat.le_of_lt (Finset.mem_Ico.mp hj).2))
      (hn' (j+1) (by have := (Finset.mem_Ico.mp hj).2; omega))
      (hPmove j hj) (hRmove j hj) (hz j (Finset.mem_Ico.mp hj).2))
    (segmentCost_sum_le_full_root n R start N K a Z ha hZ hn0 hmono hR0 hR)
  have heq : Real.exp (a*δ-a*Real.log lower) = Real.exp (a*δ)*lower^(-a) := by
    rw [Real.rpow_def_of_pos hlower, ← Real.exp_add]
    congr 1
    ring
  simpa only [segmentWeight, heq] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SegmentAmplitudes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector summation by parts on arbitrary hierarchy segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_weighted_Ico_le_variation (w : ℕ → ℂ) (f : ℕ → E)
    (start N : ℕ) (B : ℝ) (hstart : start ≤ N)
    (hB : ∀ k, start ≤ k → k ≤ N → ‖∑ i ∈ Finset.Ico start (k + 1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.Ico start (N + 1), w i • f i‖ ≤
      (‖w N‖ + ∑ i ∈ Finset.Ico start N, ‖w (i + 1) - w i‖) * B := by
  have hpartial (k : ℕ) (hk : k ≤ N - start) :
      ‖∑ i ∈ Finset.range (k + 1), f (start + i)‖ ≤ B := by
    have hb := hB (start + k) (by omega) (by omega)
    rw [Finset.sum_Ico_eq_sum_range, show start + k + 1 - start = k + 1 by omega] at hb
    exact hb
  have h := norm_weighted_sum_le_variation (fun i => w (start + i))
    (fun i => f (start + i)) (N - start) B hpartial
  have hlength : N + 1 - start = N - start + 1 := by omega
  have hend : start + (N - start) = N := by omega
  simpa only [Finset.sum_Ico_eq_sum_range, hlength, hend, Nat.add_assoc] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineTiling
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many actual finite line meshes cover a reference line. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

theorem tiledLineGrid_root (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) :
    (tiledLineGrid origin H hH G N hG k).root =
      Ico (origin + k * H) (origin + (k + 1 : ℤ) * H) := by
  unfold FiniteLineGrid.root tiledLineGrid
  congr 1
  push_cast
  ring

theorem tiledLineGrid_pairwise_disjoint (origin H : ℝ) (hH : 0 < H) (G N : ℕ)
    (hG : 0 < G) :
    Pairwise fun i j => Disjoint (tiledLineGrid origin H hH G N hG i).root
      (tiledLineGrid origin H hH G N hG j).root := by
  intro i j hij
  simp only [tiledLineGrid_root]
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hi.2, hj.1]
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hj.2, hi.1]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite lattice overlap bound from the actual line integral of
the rational envelope. No cardinality factor or implicit lattice assumption
is used. -/

noncomputable section

open Set MeasureTheory Function
open scoped BigOperators

namespace LipschitzHilbert

theorem lineEnvelope_cell_comparison (x k y : ℝ) (hy : y ∈ Ico k (k + 1)) :
    lineEnvelope x 1 1 k ≤ 4 * lineEnvelope x 1 1 y := by
  have hdelta : (y - k) ^ 2 ≤ 1 := by
    have ha : |y - k| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr ha
    simpa only [sq_abs, one_pow] using hs
  have hb : 1 + (y - x) ^ 2 ≤ 4 * (1 + (k - x) ^ 2) := by
    nlinarith [sq_nonneg ((k - x) - (y - k)), sq_nonneg (k - x)]
  simp only [lineEnvelope, div_one, pow_one]
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hb)

theorem lineEnvelope_le_cell_integral (x k : ℝ) :
    lineEnvelope x 1 1 k ≤ 4 * ∫ y in Ico k (k + 1), lineEnvelope x 1 1 y := by
  have hint : IntegrableOn (lineEnvelope x 1 1) (Ico k (k + 1)) :=
    (integrable_lineEnvelope_one x 1 (by norm_num)).integrableOn
  have hfinite : volume (Ico k (k + 1)) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have h := setIntegral_mono_on (integrableOn_const hfinite : IntegrableOn
      (fun _ : ℝ => lineEnvelope x 1 1 k) (Ico k (k + 1)) volume)
    (hint.const_mul 4) measurableSet_Ico (fun y hy => lineEnvelope_cell_comparison x k y hy)
  rw [integral_const_mul] at h
  simpa [setIntegral_const, Real.volume_Ico, measureReal_def] using h

theorem finite_line_lattice_overlap (x : ℝ) (s : Finset ℤ) :
    (∑ k ∈ s, lineEnvelope x 1 1 k) ≤ 4 * Real.pi := by
  classical
  have hint := integrable_lineEnvelope_one x 1 (by norm_num)
  have hd : (s : Set ℤ).Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) (k + 1)) := by
    intro i _ j _ hij
    have h := tiledLineGrid_pairwise_disjoint 0 1 (by norm_num) 2 0 (by norm_num) hij
    simpa only [tiledLineGrid_root, Int.cast_add, Int.cast_one, mul_one, zero_add] using h
  have hsum := integral_biUnion_finset s (fun _ _ => measurableSet_Ico) hd
    (fun _ _ => hint.integrableOn)
  calc
    _ ≤ ∑ k ∈ s, 4 * ∫ y in Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y :=
      Finset.sum_le_sum (fun k _ => lineEnvelope_le_cell_integral x k)
    _ = 4 * ∫ y in ⋃ k ∈ s, Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ 4 * ∫ y, lineEnvelope x 1 1 y := by
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hint
        (Filter.Eventually.of_forall (lineEnvelope_nonneg x 1 1))) (by norm_num)
    _ = 4 * Real.pi := by rw [integral_lineEnvelope_one x 1 (by norm_num), mul_one]

theorem lineEnvelope_lattice_rescale (a l x : ℝ) (hl : l ≠ 0) (k : ℤ) (n : ℕ) :
    lineEnvelope (a + l * k) l n x = lineEnvelope ((x - a) / l) 1 n k := by
  unfold lineEnvelope
  congr 3
  simp only [div_one]
  have h : (x - (a + l * k)) / l = -((k : ℝ) - (x - a) / l) := by
    field_simp
    ring
  rw [h, neg_sq]

theorem finite_plane_lattice_overlap (x y : ℝ) (s : Finset (ℤ × ℤ)) :
    (∑ p ∈ s, lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2) ≤
      (4 * Real.pi) ^ 2 := by
  classical
  have hsub : s ⊆ (s.image Prod.fst) ×ˢ (s.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  calc
    _ ≤ ∑ p ∈ (s.image Prod.fst) ×ˢ (s.image Prod.snd),
        lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    _ = (∑ i ∈ s.image Prod.fst, lineEnvelope x 1 1 i) *
        ∑ j ∈ s.image Prod.snd, lineEnvelope y 1 1 j := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ (4 * Real.pi) * (4 * Real.pi) :=
      mul_le_mul (finite_line_lattice_overlap x _) (finite_line_lattice_overlap y _)
        (Finset.sum_nonneg (fun j _ => lineEnvelope_nonneg _ _ _ _)) (by positivity)
    _ = _ := (pow_two _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TileLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform overlap for actual rectangular tile-center lattices, allowing
arbitrary horizontal and vertical scales and finite subfamilies. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem finite_scaled_plane_lattice_overlap (a b l W x y : ℝ)
    (hl : l ≠ 0) (hW : W ≠ 0) (s : Finset (ℤ × ℤ)) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ p ∈ s, lineEnvelope (a + l * p.1) l m x *
      lineEnvelope (b + W * p.2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  calc
    _ ≤ ∑ p ∈ s, lineEnvelope ((x - a) / l) 1 1 p.1 *
        lineEnvelope ((y - b) / W) 1 1 p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [lineEnvelope_lattice_rescale a l x hl p.1 m,
        lineEnvelope_lattice_rescale b W y hW p.2 n]
      exact mul_le_mul (lineEnvelope_antitone _ _ _ hm) (lineEnvelope_antitone _ _ _ hn)
        (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
    _ ≤ _ := finite_plane_lattice_overlap _ _ s

theorem injective_tile_lattice_overlap {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y : ℝ) (hl : l ≠ 0) (hW : W ≠ 0)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ i, lineEnvelope (a + l * (index i).1) l m x *
      lineEnvelope (b + W * (index i).2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  classical
  have h := finite_scaled_plane_lattice_overlap a b l W x y hl hW
    (Finset.univ.image index) hm hn
  rw [Finset.sum_image (fun _ _ _ _ heq => hinj heq)] at h
  exact h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketVectorDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-free synthesis and derivative estimates on a reference line.
The multiplication of a Hilbert coefficient by a packet is componentwise. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem vectorPacketSynthesis_hasDerivAt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (vectorPacketSynthesis c f)
      (WithLp.toLp 2 (fun k => ∑ i, c i k * deriv (f i k) x)) x := by
  have hd : HasDerivAt (fun x k => packetSynthesis (fun i => c i k) (fun i => f i k) x)
      (fun k => ∑ i, c i k * deriv (f i k) x) x := by
    apply hasDerivAt_pi.mpr
    intro k
    simp only [packetSynthesis_apply]
    have heq : (fun x => ∑ i, c i k * f i k x) = ∑ i, (fun x => c i k * f i k x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq]
    exact HasDerivAt.sum (u := Finset.univ)
      (fun i _ => ((f i k).differentiable x).hasDerivAt.const_mul (c i k))
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hd

theorem vectorPacketSynthesis_deriv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (vectorPacketSynthesis c f) x =
      ∑ i, WithLp.toLp 2 (fun k => c i k * deriv (f i k) x) := by
  rw [(vectorPacketSynthesis_hasDerivAt c f x).deriv]
  ext k
  simp only [WithLp.ofLp_sum, Finset.sum_apply]

theorem vectorPacketSynthesis_deriv_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (w : ι → ℝ) {C D : ℝ} (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hover : ∑ i, w i ≤ D) (x : ℝ)
    (hf : ∀ i k, ‖deriv (f i k) x‖ ≤ C * w i) :
    ‖deriv (vectorPacketSynthesis c f) x‖ ≤ C * D := by
  rw [vectorPacketSynthesis_deriv]
  calc
    _ ≤ ∑ i, ‖WithLp.toLp 2 (fun k => c i k * deriv (f i k) x)‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact (diagonal_packet_norm (c i) _ (mul_nonneg hC (hw i)) (hf i)).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hc i) (mul_nonneg hC (hw i)))
    _ ≤ C * D := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hover hC

theorem tile_vectorPacketSynthesis_deriv_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y C : ℝ) (hl : 0 < l) (hW : W ≠ 0) (hC : 0 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ 1)
    (hf : ∀ i k, ‖deriv (f i k) x‖ ≤ (C / l) *
      (lineEnvelope (a + l * (index i).1) l 3 x *
        lineEnvelope (b + W * (index i).2) W 2 y)) :
    ‖deriv (vectorPacketSynthesis c f) x‖ ≤ (C / l) * (4 * Real.pi) ^ 2 := by
  exact vectorPacketSynthesis_deriv_bound c f _ (div_nonneg hC hl.le)
    (fun i => mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)) hc
    (injective_tile_lattice_overlap index hinj a b l W x y hl.ne' hW (by decide) (by decide)) x hf

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SelectedScaleDerivative
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal derivative bound for arbitrary selected scales above
a lower length cutoff. It is independent of scale count and dimension. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem selected_dyadic_reciprocals (N : ℕ) (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (s : Finset (Fin N)) (hs : ∀ j ∈ s, r ≤ L/(2:ℝ)^j.val) :
    (∑ j ∈ s, (L/(2:ℝ)^j.val)⁻¹) ≤ 4/r := by
  have hp : 0 < r/2 := by positivity
  calc
    _ ≤ ∑ j : Fin N, if r/2 < L/(2:ℝ)^j.val then (L/(2:ℝ)^j.val)⁻¹ else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun j _ _ => by split_ifs <;> positivity) |>.trans' ?_
      apply Finset.sum_le_sum
      intro j hj
      rw [ite_eq_left (lt_of_lt_of_le (by linarith) (hs j hj))]
    _ ≤ 2/(r/2) := sum_long_dyadic_reciprocals N L (r/2) hL hp
    _ = 4/r := by ring

theorem tile_weighted_vector_derivative_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y C w : ℝ) (hl : 0 < l) (hW : W ≠ 0) (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hc : ∀ i, ‖c i‖ ≤ 1)
    (hf : ∀ i k, w*‖deriv (f i k) x‖ ≤ (C/l)*
      (lineEnvelope (a+l*(index i).1) l 3 x * lineEnvelope (b+W*(index i).2) W 2 y)) :
    w*‖deriv (vectorPacketSynthesis c f) x‖ ≤ (C/l)*(4*Real.pi)^2 := by
  by_cases hw0 : w = 0
  · simp only [hw0, zero_mul]
    positivity
  have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hscaled (i : ι) (k : κ) : ‖deriv (f i k) x‖ ≤ ((C/w)/l)*
      (lineEnvelope (a+l*(index i).1) l 3 x * lineEnvelope (b+W*(index i).2) W 2 y) := by
    apply (mul_le_mul_iff_right₀ hwp).mp
    calc
      _ ≤ (C/l)*(lineEnvelope (a+l*(index i).1) l 3 x *
          lineEnvelope (b+W*(index i).2) W 2 y) := hf i k
      _ = _ := by field_simp
  have h := tile_vectorPacketSynthesis_deriv_bound c f index hinj a b l W x y (C/w)
    hl hW (div_nonneg hC hw) hc hscaled
  have hh := mul_le_mul_of_nonneg_left h hw
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp


theorem selected_scale_weighted_derivative_bound {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W x y C w r : ℝ) (hL : 0 < L) (hW : W ≠ 0)
    (hC : 0 ≤ C) (hw : 0 ≤ w) (hr : 0 < r)
    (hc : ∀ j i, ‖c j i‖ ≤ 1)
    (s : Finset (Fin N)) (hs : ∀ j ∈ s, r ≤ L/(2:ℝ)^j.val)
    (hf : ∀ j i k, w*‖deriv (f j i k) x‖ ≤ (C/(L/(2:ℝ)^j.val))*
      (lineEnvelope (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) 3 x *
        lineEnvelope (b+W*(site j i).2) W 2 y)) :
    w*‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖ ≤
      4*(C*(4*Real.pi)^2)/r := by
  have hd := HasDerivAt.fun_sum (u := s) (fun j _ =>
    (vectorPacketSynthesis_hasDerivAt (c j) (f j) x).differentiableAt.hasDerivAt)
  rw [hd.deriv]
  calc
    _ ≤ w*(∑ j ∈ s, ‖deriv (vectorPacketSynthesis (c j) (f j)) x‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ = ∑ j ∈ s, w*‖deriv (vectorPacketSynthesis (c j) (f j)) x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ s, (C/(L/(2:ℝ)^j.val))*(4*Real.pi)^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact tile_weighted_vector_derivative_bound (c j) (f j) (site j) (hinj j)
        a b (L/(2:ℝ)^j.val) W x y C w (div_pos hL (by positivity)) hW hC hw (hc j) (hf j)
    _ = (C*(4*Real.pi)^2)*(∑ j ∈ s, (L/(2:ℝ)^j.val)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_eq_mul_inv]
      ring
    _ ≤ (C*(4*Real.pi)^2)*(4/r) :=
      mul_le_mul_of_nonneg_left (selected_dyadic_reciprocals N L r hL hr s hs) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PolynomialPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial weights preserve the required packet decay and
horizontal derivative bounds, after choosing the original packet order. -/

noncomputable section

namespace LipschitzHilbert

theorem polynomialWeight_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s-a| ≤ r) :
    polynomialWeight a r q x * lineEnvelope s l (n+2*q) x ≤
      16^q * lineEnvelope s l n x := by
  have hP := polynomialWeight_one_le a r q x
  have hsq : polynomialWeight a r q x ≤ polynomialWeight a r q x^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hsq (lineEnvelope_nonneg _ _ _ _)).trans
    (polynomialWeight_sq_mul_envelope x s a l r q n hl hr hlr hsa)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopEnvelopeDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed top weights preserve the pointwise derivative envelopes needed
for the unconditional horizontal derivative estimate. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem topWeight_mul_envelope (x y a r b R s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C) :
    (polynomialWeight a r q x*polynomialWeight b R q y)*
      (C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y)) ≤
    (16^q*(16^q*C))*(lineEnvelope s l m x*lineEnvelope t W n y) := by
  have hx := polynomialWeight_mul_envelope x s a l r q m hl hr hlr hs
  have hy := polynomialWeight_mul_envelope y t b W R q n hW hR hWR ht
  have hy0 : 0 ≤ polynomialWeight b R q y*lineEnvelope t W (n+2*q) y :=
    mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _)) (lineEnvelope_nonneg _ _ _ _)
  have hb := mul_le_mul hx hy hy0 (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
  have h := mul_le_mul_of_nonneg_left hb hC
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))


end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SelectedCoefficientDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted horizontal derivative bound with the original, uniformly
bounded coefficients, without normalizing the resulting synthesis. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem vectorPacketSynthesis_deriv_coeff_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (s x : ℝ) :
    deriv (vectorPacketSynthesis (fun i => s • c i) f) x =
      s • deriv (vectorPacketSynthesis c f) x := by
  rw [vectorPacketSynthesis_deriv,vectorPacketSynthesis_deriv]
  ext k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    Complex.real_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopLatticeDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the lattice decay in the global concentration estimate into
the eighth power of the manuscript's actual slope-box weight. -/

noncomputable section
namespace LipschitzHilbert

namespace SlopeBox

theorem weight_nat_eighth (T : SlopeBox) (K : ℝ) (hK : 0 < K) (d : ℕ) (z : ℝ × ℝ) :
    (T.weight K (d:ℝ) z)^8 = (2:ℝ)^(8*d)/(1+T.radius z/K)^(8*d) := by
  have hb : 0 ≤ 1+T.radius z/K := by
    have := T.radius_nonnegative z
    positivity
  simp only [weight, Real.rpow_neg hb, Real.rpow_natCast, mul_pow, inv_pow, ← pow_mul]
  rw [mul_comm d 8]
  simp only [div_eq_mul_inv]

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopPolynomialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse of the fixed polynomial top weight is bounded by the
eighth power of the physical slope-box weight. -/

noncomputable section
namespace LipschitzHilbert.SlopeBox

theorem inverse_polynomial_le_weight (T : SlopeBox) (K : ℝ) (hK : 0 < K)
    (D : ℕ) (z : ℝ × ℝ) :
    (polynomialWeight T.x (K*T.length) (8*D+1) z.1 *
      polynomialWeight (T.y-T.slope*T.x) (K*T.width) (8*D+1) (z.2-T.slope*z.1))⁻¹ ≤
        (T.weight K (D:ℝ) z)^8 := by
  let X := (z.1-T.x)/(K*T.length)
  let Y := ((z.2-T.slope*z.1)-(T.y-T.slope*T.x))/(K*T.width)
  let B := (1+X^2)*(1+Y^2)
  have hB : 1 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg X,sq_nonneg Y,mul_nonneg (sq_nonneg X) (sq_nonneg Y)]
  have hsum : 1+|X|+|Y| ≤ 2*B := by
    have hx : 2*|X| ≤ 1+X^2 := by nlinarith [sq_nonneg (|X|-1),sq_abs X]
    have hy : 2*|Y| ≤ 1+Y^2 := by nlinarith [sq_nonneg (|Y|-1),sq_abs Y]
    dsimp [B]
    nlinarith [sq_nonneg X,sq_nonneg Y,mul_nonneg (sq_nonneg X) (sq_nonneg Y)]
  have hr : 1+T.radius z/K = 1+|X|+|Y| := by
    symm
    unfold radius horizontal transverse
    dsimp [X,Y]
    rw [abs_div,abs_div,abs_of_pos (mul_pos hK T.length_pos),
      abs_of_pos (mul_pos hK T.width_pos),abs_div,abs_div,
      abs_of_pos T.length_pos,abs_of_pos T.width_pos]
    have heq : (z.2-T.slope*z.1)-(T.y-T.slope*T.x) =
        (z.2-T.y)-T.slope*(z.1-T.x) := by ring
    rw [heq]
    ring
  have hpoly : polynomialWeight T.x (K*T.length) (8*D+1) z.1 *
      polynomialWeight (T.y-T.slope*T.x) (K*T.width) (8*D+1) (z.2-T.slope*z.1) =
        B^(8*D+1) := by
    simp only [polynomialWeight,← mul_pow]
    simp only [B,X,Y,div_pow]
  rw [hpoly,T.weight_nat_eighth K hK,hr]
  have hden : 0 < (1+|X|+|Y|)^(8*D) := by positivity
  have hpow : (1+|X|+|Y|)^(8*D) ≤ 2^(8*D)*B^(8*D+1) := by
    calc
      _ ≤ (2*B)^(8*D) := pow_le_pow_left₀ (by positivity) hsum _
      _ = 2^(8*D)*B^(8*D) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hB (Nat.le_add_right _ _)) (by positivity)
  apply (le_div_iff₀ hden).mpr
  have hd := (div_le_iff₀ (pow_pos (zero_lt_one.trans_le hB) (8*D+1))).mpr hpow
  simpa only [div_eq_mul_inv,mul_comm] using hd

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DemodulatedVertical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the vertical carrier before applying the interval Sobolev
estimate. The derivative norm is exactly the covariant derivative norm,
independently of the carrier frequencies and Hilbert dimension. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert
open PhaseCombinatorics

theorem character_hasDerivAt (frequency y : ℝ) :
    HasDerivAt (character frequency) ((frequency:ℂ)*Complex.I*character frequency y) y := by
  have h := (((hasDerivAt_id y).const_mul frequency).ofReal_comp.mul_const Complex.I).cexp
  refine h.congr_deriv ?_
  · simp only [id_eq, mul_one]
    symm
    change (frequency:ℂ)*Complex.I*character frequency y =
      character frequency y*((frequency:ℂ)*Complex.I)
    ring

theorem demodulatedSignal_hasDerivAt {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) :
    HasDerivAt (demodulatedSignal frequency f)
      (diagonalModulation (fun k => -frequency k) (covariantSignal frequency f y) y) y := by
  have hc : HasDerivAt (fun t k => f k t * character (-frequency k) t)
      (fun k => (deriv (f k) y - (frequency k:ℂ)*Complex.I*f k y) *
        character (-frequency k) y) y := by
    apply hasDerivAt_pi.mpr
    intro k
    have h := (hf k).hasDerivAt.mul (character_hasDerivAt (-frequency k) y)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y hc

theorem demodulatedSignal_deriv_norm {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) :
    ‖deriv (demodulatedSignal frequency f) y‖ = ‖covariantSignal frequency f y‖ := by
  rw [(demodulatedSignal_hasDerivAt frequency f y hf).deriv, norm_diagonalModulation]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteBandDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical differentiation commutes with the actual finite band sums.
The covariant derivative uses the same carrier in every band of a fixed
coordinate, so no carrier-frequency factor is lost. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem scalarBandPartial_hasDerivAt {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    HasDerivAt (scalarBandPartial F n)
      (scalarBandPartial (fun j => deriv (F j)) n y) y := by
  apply HasDerivAt.fun_sum
  intro j _
  by_cases hj : j.val < n
  · simpa only [hj, ite_true, if_true] using (hF j).hasDerivAt
  · simpa only [hj, ite_false, if_false] using (hasDerivAt_const y (0:ℂ))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketDifferentiation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vertical derivatives of packet syntheses. Coefficients stay
fixed during differentiation, including when they are analyzing integrals. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketBand_hasDerivAt (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    HasDerivAt (planarPacketBand coeff wave j k x)
      (∑ i, coeff j i k * deriv (fun t => wave j i k t x) y) y := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hw i).hasDerivAt.const_mul _

omit [Fintype κ] in
theorem planarPacketInterval_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j i k t z => (s:ℂ)*wave j i k t z) a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  have hs (j : Fin N) (k : κ) :
      planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y =
        (s:ℂ)*planarPacketBand coeff wave j k x y := by
    simp only [planarPacketBand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp (n : ℕ) (k : κ) :
      scalarBandPartial (fun j => planarPacketBand coeff
        (fun j i k t z => (s:ℂ)*wave j i k t z) j k x) n y =
      (s:ℂ)*scalarBandPartial (fun j => planarPacketBand coeff wave j k x) n y := by
    simp only [scalarBandPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [hs, mul_zero]
  ext k
  change _ = (s:ℂ)*(_-_)
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, hp, mul_sub]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity and local square integrability for actual packet
interval sums and their covariant derivatives. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_component_differentiable
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ) (k : κ)
    (hd : ∀ j i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    DifferentiableAt ℝ (fun t => planarPacketInterval coeff wave a b x t k) y := by
  change DifferentiableAt ℝ (fun t =>
    scalarBandPartial (fun j => planarPacketBand coeff wave j k x) b t -
    scalarBandPartial (fun j => planarPacketBand coeff wave j k x) a t) y
  have hb (n : ℕ) := (scalarBandPartial_hasDerivAt
    (fun j => planarPacketBand coeff wave j k x) n y (fun j =>
      (planarPacketBand_hasDerivAt coeff wave j k x y (hd j)).differentiableAt)).differentiableAt
  exact (hb b).sub (hb a)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the coefficient normalization after the packet concentration
estimate, preserving the original integral-defined analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_coeff_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval (fun j i => s • coeff j i) wave a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  rw [← planarPacketInterval_smul coeff wave s a b x y]
  have hb (j : Fin N) (k : κ) (y : ℝ) :
      planarPacketBand (fun j i => s • coeff j i) wave j k x y =
        planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y := by
    apply Finset.sum_congr rfl
    intro i _
    change ((s:ℂ)*coeff j i k)*wave j i k y x = coeff j i k*((s:ℂ)*wave j i k y x)
    ring
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, scalarBandPartial, hb]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SelectedTopInterval
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the finite band interval with the selected
scale sum, preserving the actual analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem planarPacketInterval_eq_selected
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (a b : ℕ) (hab : a ≤ b) (x y : ℝ) :
    planarPacketInterval c (fun j u k t s => f j u k t s) a b x y =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => a ≤ j.val ∧ j.val < b),
        vectorPacketSynthesis (c j) (fun u k => f j u k y) x := by
  ext k
  simp only [planarPacketInterval,bandIntervalSignal,WithLp.ofLp_toLp,scalarBandPartial,
    WithLp.ofLp_sum,Finset.sum_apply,vectorPacketSynthesis,packetSynthesis_apply,
    planarPacketBand,Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j.val < a
  · have hjb : j.val < b := hja.trans_le hab
    simp only [hja,hjb,ite_true, if_true,sub_self,not_le.mpr hja,false_and,ite_false, if_false,WithLp.ofLp_zero,Pi.zero_apply]
  · by_cases hjb : j.val < b
    · simp only [hja,hjb,ite_true, if_true,ite_false, if_false,sub_zero,not_lt.mp hja,true_and]
    · simp only [hja,hjb,ite_false, if_false,sub_self,and_false,WithLp.ofLp_zero,Pi.zero_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopMaskApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript mask at its actual scale. Inside the prescribed
near region its error is at most a fixed constant times L^(1-A). -/

noncomputable section

namespace LipschitzHilbert

theorem topSincMask_nonneg (L A x y : ℝ) : 0 ≤ topSincMask L A x y :=
  sincProductMask_nonneg _ _ _

theorem topSincMask_le_one (L A x y : ℝ) : topSincMask L A x y ≤ 1 :=
  sincProductMask_le_one _ _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem labelAtSlot_at {A : Type*} {B : ℕ} (e : A ↪ Fin B) (i : A) :
    labelAtSlot e (e i) = some i := by
  classical
  unfold labelAtSlot
  split_ifs with h
  · congr 1
    exact e.injective h.choose_spec
  · exact (h ⟨i, rfl⟩).elim

theorem labelAtSlot_eq_some {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    (b : Fin B) (i : A) : labelAtSlot e b = some i ↔ e i = b := by
  classical
  constructor
  · unfold labelAtSlot
    split_ifs with h
    · intro hi
      have heq : h.choose = i := Option.some.inj hi
      simpa only [heq] using h.choose_spec
    · simp
  · intro hi
    rw [← hi]
    exact labelAtSlot_at e i

theorem slotItem_label {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    {Item : A → Type*} {b : Fin B} (p : SlotItem e Item b) :
    labelAtSlot e b = some p.1.1 :=
  (labelAtSlot_eq_some e b p.1.1).mpr p.2

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedLattice
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual source lattices with several labels at each scale split into
the uniformly many slots constructed in `SourceSlopeLabels`. No packets
are inserted at an empty scale. The selected profiles, physical centers,
carrier frequencies and spectra are unchanged. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

/-- Splitting by slots is an exact identity for arbitrary finite packet
sums, not an estimate and not a change to the waves. -/
theorem sum_slotted {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E) :
    (∑ b : Fin B, ∑ p : P.SlotItem hcard b j, f p.1.1 p.1.2) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have h := Equiv.sum_comp (P.slotItemsEquiv hcard j)
    (fun p : Σ l : P.labels j, Item j l => f p.1 p.2)
  change (∑ p : Σ b : Fin B, P.SlotItem hcard b j, f p.2.1.1 p.2.1.2) =
    ∑ p : Σ l : P.labels j, Item j l, f p.1 p.2 at h
  simpa only [Fintype.sum_sigma] using h

theorem slotValue_item (b : Fin B) (j : Fin N) (f : P.labels j → ℝ)
    (p : P.SlotItem hcard b j) : P.slotValue hcard b j f = f p.1.1 := by
  unfold slotValue
  rw [SourceSlopeLabels.slotItem_label (P.slotEmbedding hcard j) p]
  rfl

@[simp] theorem slotted_actualX (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).actualX j p = P.actualX j p.1.1 p.1.2 := by
  change P.slotValue hcard b j (P.originX j) + P.length j * (P.site j p.1.1 p.1.2).1 = _
  rw [P.slotValue_item hcard b j (P.originX j) p]
  rfl

@[simp] theorem slotted_actualZ (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).actualZ j p = P.actualZ j p.1.1 p.1.2 := by
  change P.slotValue hcard b j (P.originZ j) +
    P.slotValue hcard b j (P.rowSlope j) * P.length j * (P.site j p.1.1 p.1.2).1 +
      P.width * (P.site j p.1.1 p.1.2).2 = _
  rw [P.slotValue_item hcard b j (P.originZ j) p,
    P.slotValue_item hcard b j (P.rowSlope j) p]
  rfl

theorem slotted_rowSlope (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).rowSlope j = P.rowSlope j p.1.1 :=
  P.slotValue_item hcard b j (P.rowSlope j) p

@[simp] theorem slotted_raw (b : Fin B) (i : Fin 3) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) (y : ℝ) :
    (P.slotted hcard b).raw i j p k y = P.raw i j p.1.1 p.1.2 k y := by
  unfold SourceLatticePacket.raw raw
  simp only [P.slotted_actualX hcard, P.slotted_actualZ hcard, P.slotted_length hcard,
    P.slotted_rowSlope hcard b j p]
  rfl

@[simp] theorem slotted_physicalPacket (b : Fin B) (t : ℝ) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) :
    (P.slotted hcard b).physicalPacket t j p k = P.physicalPacket t j p.1.1 p.1.2 k := by
  unfold SourceLatticePacket.physicalPacket physicalPacket
  simp only [P.slotted_actualX hcard, P.slotted_actualZ hcard, P.slotted_length hcard,
    P.slotted_rowSlope hcard b j p]
  rfl

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of selected analyzing integrals and cross-profile
packet sums through the finite slope-label splitting. These are algebraic
identities and require no concentration or integrability assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j l u k,
    planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)

/-- Profile replacement commutes with the actual slot constructor. -/
theorem withProfile_slotted (b : Fin B) :
    (P.withProfile alt hAlt).slotted hcard b =
      (P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b) := by
  rfl

omit alt hAlt in
theorem sum_slotted_rawInterval
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    (∑ b : Fin B, (P.slotted hcard b).rawInterval
      (fun j p => coeff j p.1.1 p.1.2) i lower upper x y) =
      P.rawInterval coeff i lower upper x y := by
  have hband (j : Fin N) (k : κ) (y : ℝ) :
      (∑ b : Fin B, ∑ p : P.SlotItem hcard b j,
        coeff j p.1.1 p.1.2 k * (P.slotted hcard b).raw i j p k y x) =
      ∑ p : Σ l : P.labels j, Item j l, coeff j p.1 p.2 k * P.raw i j p.1 p.2 k y x := by
    simp_rw [P.slotted_raw hcard]
    simpa only [Fintype.sum_sigma] using
      P.sum_slotted hcard j (fun l u => coeff j l u k * P.raw i j l u k y x)
  have hpartial (n : ℕ) (k : κ) :
      (∑ b : Fin B, scalarBandPartial (fun j =>
        planarPacketBand (ι := P.SlotItem hcard b) (fun j p => coeff j p.1.1 p.1.2)
          (fun j p k t s => (P.slotted hcard b).raw i j p k t s) j k x) n y) =
      scalarBandPartial (fun j => planarPacketBand (ι := fun j => Σ l : P.labels j, Item j l)
        (fun j p => coeff j p.1 p.2)
        (fun j p k t s => P.raw i j p.1 p.2 k t s) j k x) n y := by
    unfold scalarBandPartial
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < n
    · simp only [hj, ite_true, if_true, planarPacketBand]
      exact hband j k y
    · simp only [hj, ite_false, if_false, Finset.sum_const_zero]
  ext k
  simp only [SourceLatticePacket.rawInterval, rawInterval, planarPacketInterval,
    bandIntervalSignal, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp]
  rw [Finset.sum_sub_distrib, hpartial, hpartial]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppingScaleIntervals
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopping-level bands are intervals of the original source length
index. This is the bridge from interval concentration to summation by
parts over angular stopping levels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem antitone_stopping_band_interval {N : ℕ} (stop : Fin N → ℕ)
    (hstop : Antitone stop) (a b : ℕ) :
    ∃ lower upper : ℕ, lower ≤ upper ∧ upper ≤ N ∧
      ∀ j : Fin N, (a ≤ stop j ∧ stop j < b) ↔ lower ≤ j.val ∧ j.val < upper := by
  let s := Finset.univ.filter (fun j : Fin N => a ≤ stop j ∧ stop j < b)
  by_cases hs : s.Nonempty
  · let lo := s.min' hs
    let hi := s.max' hs
    have hlo : lo ∈ s := s.min'_mem hs
    have hhi : hi ∈ s := s.max'_mem hs
    have hlh : lo ≤ hi := s.min'_le hi hhi
    refine ⟨lo.val, hi.val+1, by omega, by omega, ?_⟩
    intro j
    constructor
    · intro hj
      have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hl := s.min'_le j hjs
      have hr := s.le_max' j hjs
      exact ⟨hl, by change j.val ≤ hi.val at hr; omega⟩
    · intro hj
      have hlj : lo ≤ j := hj.1
      have hjh : j ≤ hi := by change j.val ≤ hi.val; omega
      have hstoplo := (Finset.mem_filter.mp hlo).2.2
      have hstophi := (Finset.mem_filter.mp hhi).2.1
      exact ⟨hstophi.trans (hstop hjh), (hstop hlj).trans_lt hstoplo⟩
  · refine ⟨0,0,le_rfl,Nat.zero_le _,?_⟩
    intro j
    constructor
    · intro hj
      exact False.elim (hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
    · intro hj
      omega

/-- Summing fibers of the actual stopping map loses neither packets nor
multiplicity. -/
theorem sum_stopping_fibers {N : ℕ} {E : Type*} [AddCommMonoid E]
    (stop : Fin N → ℕ) (f : Fin N → E) (a b : ℕ) :
    (∑ k ∈ Finset.Ico a b, ∑ j ∈ Finset.univ.filter (fun j => stop j = k), f j) =
      ∑ j ∈ Finset.univ.filter (fun j => a ≤ stop j ∧ stop j < b), f j := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : stop j ∈ Finset.Ico a b
  · rw [Finset.sum_eq_single_of_mem (stop j) hj]
    · simp only [ite_true, if_true, ite_eq_left (Finset.mem_Ico.mp hj)]
    · intro k _ hkj
      exact ite_eq_right (Ne.symm hkj)
  · rw [Finset.sum_eq_zero]
    · exact (ite_eq_right (fun h => hj (Finset.mem_Ico.mpr h))).symm
    · intro k hk
      exact ite_eq_right (fun (heq : stop j = k) => hj (by simpa only [heq] using hk))

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem length_antitone (P : SourceLabeledLattice N κ Label Item) : Antitone P.length := by
  intro i j hij
  unfold length
  exact div_le_div_of_nonneg_left P.topLength_pos.le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)

theorem precision_monotone (P : SourceLabeledLattice N κ Label Item) (w : ℝ) (hw : 0 ≤ w) :
    Monotone (fun j => w / P.length j) := by
  intro i j hij
  exact div_le_div_of_nonneg_left hw (P.length_pos j) (P.length_antitone hij)

theorem stopping_antitone (P : SourceLabeledLattice N κ Label Item) (grid : AngularGrid)
    (cutoff w : ℝ) (hw : 0 < w)
    (hstart : ∀ j, grid.eligible cutoff (w / P.length j) 0) :
    Antitone (fun j => grid.lastEligible cutoff (w / P.length j) (div_pos hw (P.length_pos j))) := by
  intro i j hij
  exact grid.lastEligible_antitone_precision cutoff (w / P.length i) (w / P.length j)
    (div_pos hw (P.length_pos i)) (div_pos hw (P.length_pos j))
    (P.precision_monotone w hw.le hij) (hstart i) (hstart j)

theorem rawInterval_eq_band_sum (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    P.rawInterval coeff i lower upper x y =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        P.rawBand coeff i j x y := by
  have h := planarPacketInterval_eq_selected
    (ι := fun j => Σ l : P.labels j, Item j l)
    (fun j p => coeff j p.1 p.2)
    (fun j p k t => P.raw i j p.1 p.2 k t) lower upper hlu x y
  exact h

/-- Every partial sum over a band of angular stopping levels is one of
the source intervals already controlled by the concentration theorem. -/
theorem stopping_band_eq_rawInterval (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (a b : ℕ) (x y : ℝ) :
    ∃ lower upper : ℕ, lower ≤ upper ∧ upper ≤ N ∧
      (∑ j ∈ Finset.univ.filter (fun j => a ≤ stop j ∧ stop j < b),
        P.rawBand coeff i j x y) = P.rawInterval coeff i lower upper x y := by
  obtain ⟨lower,upper,hlu,hu,hband⟩ := antitone_stopping_band_interval stop hstop a b
  refine ⟨lower,upper,hlu,hu,?_⟩
  rw [P.rawInterval_eq_band_sum coeff i lower upper hlu x y]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hband j

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_CovariantLineMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Demodulated line motion from the horizontal derivative and vertical
covariant derivative. The carrier frequencies do not enter the bound. -/

noncomputable section
open Set
namespace LipschitzHilbert
open PhaseCombinatorics

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
theorem diagonalModulation_sub (frequency : κ → ℝ) (a b : EuclideanSpace ℂ κ) (t : ℝ) :
    diagonalModulation frequency (a-b) t =
      diagonalModulation frequency a t - diagonalModulation frequency b t := by
  ext k
  simp only [diagonalModulation, WithLp.ofLp_toLp, PiLp.sub_apply]
  ring

theorem modulation_difference_norm (frequency : κ → ℝ) (a b : EuclideanSpace ℂ κ)
    (s t : ℝ) :
    ‖a - diagonalModulation frequency b (t-s)‖ =
      ‖diagonalModulation (fun k => -frequency k) a t -
        diagonalModulation (fun k => -frequency k) b s‖ := by
  have hcancel (k : κ) : character (frequency k) (t-s) * character (-frequency k) t =
      character (-frequency k) s := by
    unfold character
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heq : diagonalModulation (fun k => -frequency k)
      (a-diagonalModulation frequency b (t-s)) t =
      diagonalModulation (fun k => -frequency k) a t -
        diagonalModulation (fun k => -frequency k) b s := by
    ext k
    simp only [diagonalModulation, WithLp.ofLp_toLp, PiLp.sub_apply]
    rw [sub_mul, mul_assoc, hcancel]
  rw [← heq, norm_diagonalModulation]

/-- The two coordinate segments suffice, so no bound on a mixed
partial derivative is needed. -/
theorem covariant_line_motion (F : ℝ → ℝ → EuclideanSpace ℂ κ) (frequency : κ → ℝ)
    (x0 x1 y0 y1 Cx Cy : ℝ)
    (hx : ∀ t ∈ uIcc x0 x1, DifferentiableAt ℝ (fun x => F x y1) t)
    (hy : ∀ t ∈ uIcc y0 y1, ∀ k, DifferentiableAt ℝ (fun y => F x0 y k) t)
    (hDx : ∀ t ∈ uIcc x0 x1, ‖deriv (fun x => F x y1) t‖ ≤ Cx)
    (hDy : ∀ t ∈ uIcc y0 y1,
      ‖covariantSignal frequency (fun k y => F x0 y k) t‖ ≤ Cy) :
    ‖F x1 y1 - diagonalModulation frequency (F x0 y0) (y1-y0)‖ ≤
      Cx*|x1-x0| + Cy*|y1-y0| := by
  have hhorizontal : ‖F x1 y1 - F x0 y1‖ ≤ Cx*|x1-x0| := by
    simpa only [Real.norm_eq_abs] using
      (convex_uIcc x0 x1).norm_image_sub_le_of_norm_deriv_le hx hDx
        (left_mem_uIcc) (right_mem_uIcc)
  have hvertical :
      ‖demodulatedSignal frequency (fun k y => F x0 y k) y1 -
        demodulatedSignal frequency (fun k y => F x0 y k) y0‖ ≤ Cy*|y1-y0| := by
    apply (convex_uIcc y0 y1).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (demodulatedSignal_hasDerivAt frequency _ t (hy t ht)).differentiableAt)
      (fun t ht => ?_) (left_mem_uIcc) (right_mem_uIcc)
    rw [demodulatedSignal_deriv_norm frequency _ t (hy t ht)]
    exact hDy t ht
  rw [modulation_difference_norm frequency (F x1 y1) (F x0 y0) y0 y1]
  calc
    _ ≤ ‖diagonalModulation (fun k => -frequency k) (F x1 y1) y1 -
          diagonalModulation (fun k => -frequency k) (F x0 y1) y1‖ +
        ‖diagonalModulation (fun k => -frequency k) (F x0 y1) y1 -
          diagonalModulation (fun k => -frequency k) (F x0 y0) y0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖F x1 y1 - F x0 y1‖ +
        ‖demodulatedSignal frequency (fun k y => F x0 y k) y1 -
          demodulatedSignal frequency (fun k y => F x0 y k) y0‖ := by
      rw [← diagonalModulation_sub, norm_diagonalModulation]
      rfl
    _ ≤ _ := add_le_add hhorizontal hvertical

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interval concentration controls the actual source sums weighted by
angular stopping levels. The finite regrouping and summation by parts
introduce no factor depending on the number of scales. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem stopping_weighted_sum_eq {N : ℕ} (stop : Fin N → ℕ) (f : Fin N → E)
    (w : ℕ → ℂ) (start M : ℕ) (hstop : ∀ j, stop j ≤ M) :
    (∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j), w (stop j) • f j) =
      ∑ k ∈ Finset.Ico start (M+1), w k •
        ∑ j ∈ Finset.univ.filter (fun j => stop j = k), f j := by
  have heq : (∑ k ∈ Finset.Ico start (M+1), w k •
      ∑ j ∈ Finset.univ.filter (fun j => stop j = k), f j) =
      ∑ k ∈ Finset.Ico start (M+1),
        ∑ j ∈ Finset.univ.filter (fun j => stop j = k), w (stop j) • f j := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  rw [heq, sum_stopping_fibers]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h, by have := hstop j; omega⟩, And.left⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedAmplitudeMotion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation by parts for moving packet amplitudes. The unweighted
interval motion and the endpoint-weight motion are charged separately. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem weighted_interval_motion (w w' : ℕ → ℂ) (f f' : ℕ → E)
    (start N : ℕ) (hstart : start ≤ N) (A D B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hweight : ‖w' N‖+(∑ j ∈ Finset.Ico start N, ‖w' (j+1)-w' j‖) ≤ A)
    (hweightdiff : ‖w' N-w N‖+
      (∑ j ∈ Finset.Ico start N, ‖(w' (j+1)-w (j+1))-(w' j-w j)‖) ≤ D)
    (hpartial : ∀ k, start ≤ k → k ≤ N → ‖∑ j ∈ Finset.Ico start (k+1), f j‖ ≤ B)
    (hmotion : ∀ k, start ≤ k → k ≤ N →
      ‖∑ j ∈ Finset.Ico start (k+1), (f' j-f j)‖ ≤ ε) :
    ‖(∑ j ∈ Finset.Ico start (N+1), w' j • f' j)-
      (∑ j ∈ Finset.Ico start (N+1), w j • f j)‖ ≤ A*ε+D*B := by
  have heq : (∑ j ∈ Finset.Ico start (N+1), w' j • f' j)-
      (∑ j ∈ Finset.Ico start (N+1), w j • f j) =
      (∑ j ∈ Finset.Ico start (N+1), w' j • (f' j-f j))+
      (∑ j ∈ Finset.Ico start (N+1), (w' j-w j) • f j) := by
    simp only [smul_sub, sub_smul, Finset.sum_sub_distrib]
    abel
  have hfirst := norm_weighted_Ico_le_variation w' (fun j => f' j-f j)
    start N ε hstart hmotion
  have hsecond := norm_weighted_Ico_le_variation (fun j => w' j-w j) f
    start N B hstart hpartial
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    (hfirst.trans (mul_le_mul_of_nonneg_right hweight hε))
    (hsecond.trans (mul_le_mul_of_nonneg_right hweightdiff hB)))

namespace SourceLabeledLattice

attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- Motion of all original intervals controls the stopped source sum.
The unitary may be the common diagonal carrier on the reference line. -/
theorem stopping_amplitude_motion (P : SourceLabeledLattice N κ Label Item)
    (coeff coeff' : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start M : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (w w' : ℕ → ℂ) (x0 y0 x1 y1 A D B ε : ℝ)
    (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hweight : ‖w' M‖+(∑ j ∈ Finset.Ico start M, ‖w' (j+1)-w' j‖) ≤ A)
    (hweightdiff : ‖w' M-w M‖+
      (∑ j ∈ Finset.Ico start M, ‖(w' (j+1)-w (j+1))-(w' j-w j)‖) ≤ D)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff jet l u x0 y0‖ ≤ B)
    (hmotion : ∀ l u, l ≤ u → u ≤ N →
      (∀ j : Fin N, l ≤ j.val → j.val < u → start ≤ stop j) →
      ‖P.rawInterval coeff' jet l u x1 y1-U (P.rawInterval coeff jet l u x0 y0)‖ ≤ ε) :
    ‖(∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
        w' (stop j) • P.rawBand coeff' jet j x1 y1)-
      U (∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
        w (stop j) • P.rawBand coeff jet j x0 y0)‖ ≤ A*ε+D*B := by
  let f0 := fun k => ∑ j ∈ Finset.univ.filter (fun j => stop j = k), P.rawBand coeff jet j x0 y0
  let f1 := fun k => ∑ j ∈ Finset.univ.filter (fun j => stop j = k), P.rawBand coeff' jet j x1 y1
  have hpartial (k : ℕ) (_hsk : start ≤ k) (_hk : k ≤ M) :
      ‖∑ i ∈ Finset.Ico start (k+1), U (f0 i)‖ ≤ B := by
    rw [← map_sum]
    rw [U.norm_map]
    dsimp only [f0]
    rw [sum_stopping_fibers]
    obtain ⟨l,u,hlu,hu,heq⟩ := P.stopping_band_eq_rawInterval coeff jet stop hstop start (k+1) x0 y0
    rw [heq]
    exact hinterval l u hlu hu
  have hpartialdiff (k : ℕ) (_hsk : start ≤ k) (_hk : k ≤ M) :
      ‖∑ i ∈ Finset.Ico start (k+1), (f1 i-U (f0 i))‖ ≤ ε := by
    rw [Finset.sum_sub_distrib, ← map_sum]
    dsimp only [f0,f1]
    rw [sum_stopping_fibers, sum_stopping_fibers]
    -- The same stopping-band bounds are used at both spatial points.
    have hcommon := antitone_stopping_band_interval stop hstop start (k+1)
    obtain ⟨lo,hi,hlo,hhi,hband⟩ := hcommon
    have hb (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (x y : ℝ) :
        (∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j ∧ stop j < k+1),
          P.rawBand c jet j x y) = P.rawInterval c jet lo hi x y := by
      rw [P.rawInterval_eq_band_sum c jet lo hi hlo x y]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hband j
    rw [hb coeff' x1 y1, hb coeff x0 y0]
    exact hmotion lo hi hlo hhi (fun j hjl hju => ((hband j).mpr ⟨hjl,hju⟩).1)
  rw [stopping_weighted_sum_eq stop (fun j => P.rawBand coeff' jet j x1 y1) w' start M hmax,
    stopping_weighted_sum_eq stop (fun j => P.rawBand coeff jet j x0 y0) w start M hmax,
    map_sum]
  simp only [map_smul]
  exact weighted_interval_motion w w' (fun k => U (f0 k)) f1 start M hstart A D B ε
    hB hε hweight hweightdiff hpartial hpartialdiff

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SincMaskMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global motion of the actual sinc-product mask.  The integral formula
handles the origin without a quotient singularity. -/

noncomputable section
open scoped Interval

namespace LipschitzHilbert

theorem topSincMask_motion (L A x₁ y₁ x₀ y₀ : ℝ) (hL : 0 < L) :
    |topSincMask L A x₁ y₁-topSincMask L A x₀ y₀| ≤
      (2*(⌈L⌉₊:ℝ)/L^A)*(|x₁-x₀|+|y₁-y₀|) := by
  have h := sincProductMask_motion ⌈L⌉₊ (x₁/L^A) (y₁/L^A) (x₀/L^A) (y₀/L^A)
  rw [← sub_div, ← sub_div, abs_div, abs_div,
    abs_of_pos (Real.rpow_pos_of_pos hL A)] at h
  change |sincProductMask _ _ _-sincProductMask _ _ _| ≤ _
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

namespace SlopeBox

/-- Motion in the two actual normalized coordinates of the top. -/
theorem mask_motion (T : SlopeBox) (L A : ℝ) (hL : 0 < L) (z₁ z₀ : ℝ × ℝ) :
    |T.mask L A z₁-T.mask L A z₀| ≤ (2*(⌈L⌉₊:ℝ)/L^A)*
      (|(z₁.1-z₀.1)/T.length|+
        |((z₁.2-z₀.2)-T.slope*(z₁.1-z₀.1))/T.width|) := by
  have hx : T.horizontal z₁-T.horizontal z₀ = (z₁.1-z₀.1)/T.length := by
    unfold horizontal
    ring
  have hy : T.transverse z₁-T.transverse z₀ =
      ((z₁.2-z₀.2)-T.slope*(z₁.1-z₀.1))/T.width := by
    unfold transverse
    ring
  simpa only [mask, hx, hy] using topSincMask_motion L A
    (T.horizontal z₁) (T.transverse z₁) (T.horizontal z₀) (T.transverse z₀) hL

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictableLength
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packets surviving a child level have the original horizontal length
needed by the unconditional derivative estimate on its averaging cell. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

theorem source_eligible_length_lower (g : AngularGrid) {w B length : ℝ}
    (_hw : 0 < w) (hB : 0 < B) (hlength : 0 < length) (level : ℕ)
    (he : g.eligible (g.rootWidth/B^2) (w/length) level) :
    B^2*w/g.width level ≤ length := by
  have hprec := (g.eligible_iff_precision_le (g.rootWidth/B^2) (w/length) level).mp he
  have heq : (g.rootWidth/B^2)/(g.branching:ℝ)^level = g.width level/B^2 := by
    simp only [width]
    ring
  rw [heq] at hprec
  have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ hlength).mp hprec) (sq_nonneg B)
  have hcancel : B^2*((g.width level/B^2)*length) = g.width level*length := by
    field_simp [(sq_pos_of_pos hB).ne']
  rw [hcancel] at hm
  exact (div_le_iff₀ (g.width_pos level)).mpr (by simpa only [mul_comm] using hm)

end LipschitzHilbert.AngularGrid

namespace LipschitzHilbert.SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The stopping level is the actual last eligible level of the original
packet length; surviving it implies the predictable-length lower bound. -/
theorem source_stopping_length_lower (P : SourceLabeledLattice N κ Label Item)
    (g : AngularGrid) {w B : ℝ} (hw : 0 < w) (hB : 0 < B)
    (hzero : ∀ j, g.eligible (g.rootWidth/B^2) (w/P.length j) 0)
    (level : ℕ) (j : Fin N)
    (hstop : level ≤ g.lastEligible (g.rootWidth/B^2) (w/P.length j)
      (div_pos hw (P.length_pos j))) :
    B^2*w/g.width level ≤ P.length j := by
  apply g.source_eligible_length_lower hw hB (P.length_pos j) level
  exact (g.eligible_iff_le_lastEligible _ _ (div_pos hw (P.length_pos j)) (hzero j) level).mpr hstop

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal interval derivative bound for the original labeled
source collection. Actual physical analyzing coefficients are retained;
the fixed number of lattice slots costs one power of the large parameter. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.SourceLabeledLattice

theorem planarPacketInterval_horizontal_differentiable_schwartz
    {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    DifferentiableAt ℝ (fun x => planarPacketInterval coeff
      (fun j u k t s => wave j u k t s) lower upper x y) x := by
  have heq : (fun x => planarPacketInterval coeff (fun j u k t s => wave j u k t s)
      lower upper x y) = fun x =>
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        vectorPacketSynthesis (coeff j) (fun u k => wave j u k y) x := by
    funext x
    exact planarPacketInterval_eq_selected coeff wave lower upper hlu x y
  rw [heq]
  exact DifferentiableAt.fun_sum (fun j _ =>
    (vectorPacketSynthesis_hasDerivAt (coeff j) (fun u k => wave j u k y) x).differentiableAt)

theorem lattice_rawInterval_horizontal_differentiable
    {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]
    (P : SourceLatticePacket N κ ι) (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    DifferentiableAt ℝ (fun x => P.rawInterval coeff i lower upper x y) x := by
  exact planarPacketInterval_horizontal_differentiable_schwartz
    coeff (fun j u k t => P.raw i j u k t) lower upper hlu x y

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMotion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local motion of the actual labeled interval sums after removing the
common vertical carrier. The concentration estimate is used only on the
vertical segment through the initial point; horizontal derivatives are
unconditional. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert
open PhaseCombinatorics

namespace SlopeBox

/-- Comparing the two normalized coordinates controls the actual top
weight, including away from the significant region. -/
theorem weight_slope_coordinates_le (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 0 ≤ D) (x0 x1 y0 y1 : ℝ) :
    T.weight K D (x1, y1 + T.slope*x1) ≤
      Real.exp ((D/K) * (|x1-x0|/T.length + |y1-y0|/T.width)) *
        T.weight K D (x0, y0 + T.slope*x0) := by
  let z0 := (x0, y0 + T.slope*x0)
  let z1 := (x1, y1 + T.slope*x1)
  have hx : T.horizontal z1 - T.horizontal z0 = (x1-x0)/T.length := by
    dsimp [horizontal, z0, z1]
    ring
  have hy : T.transverse z1 - T.transverse z0 = (y1-y0)/T.width := by
    dsimp [transverse, z0, z1]
    ring
  have hr : |T.radius z1 - T.radius z0| ≤ |x1-x0|/T.length + |y1-y0|/T.width := by
    calc
      _ = |(|T.horizontal z1|-|T.horizontal z0|) +
          (|T.transverse z1|-|T.transverse z0|)| := by unfold radius; congr 1; ring
      _ ≤ |(|T.horizontal z1|-|T.horizontal z0|)| +
          |(|T.transverse z1|-|T.transverse z0|)| := abs_add_le _ _
      _ ≤ |T.horizontal z1-T.horizontal z0| + |T.transverse z1-T.transverse z0| :=
        add_le_add (abs_abs_sub_abs_le_abs_sub _ _) (abs_abs_sub_abs_le_abs_sub _ _)
      _ = _ := by rw [hx, hy, abs_div, abs_div, abs_of_pos T.length_pos, abs_of_pos T.width_pos]
  have hb (z : ℝ × ℝ) : 1 ≤ 1 + T.radius z/K := by
    exact le_add_of_nonneg_right (div_nonneg (T.radius_nonnegative z) hK.le)
  have hl := log_motion_of_lower_bound (by norm_num : (0:ℝ)<1) (hb z1) (hb z0)
  have heq : (1+T.radius z1/K)-(1+T.radius z0/K) = (T.radius z1-T.radius z0)/K := by ring
  rw [div_one, heq, abs_div, abs_of_pos hK] at hl
  have hlog : |Real.log (T.weight K D z1)-Real.log (T.weight K D z0)| ≤
      (D/K) * (|x1-x0|/T.length + |y1-y0|/T.width) := by
    rw [T.log_weight hK, T.log_weight hK]
    calc
      _ = D * |Real.log (1+T.radius z1/K)-Real.log (1+T.radius z0/K)| := by
        rw [show D*Real.log 2-D*Real.log (1+T.radius z1/K) -
          (D*Real.log 2-D*Real.log (1+T.radius z0/K)) =
          -(D*(Real.log (1+T.radius z1/K)-Real.log (1+T.radius z0/K))) by ring,
          abs_neg, abs_mul, abs_of_nonneg hD]
      _ ≤ D * (|T.radius z1-T.radius z0|/K) := mul_le_mul_of_nonneg_left hl hD
      _ ≤ D * ((|x1-x0|/T.length + |y1-y0|/T.width)/K) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr hK.le) hD
      _ = _ := by ring
  calc
    _ = Real.exp (Real.log (T.weight K D z1)) := (Real.exp_log (T.weight_pos hK D z1)).symm
    _ ≤ Real.exp ((D/K)*(|x1-x0|/T.length + |y1-y0|/T.width) +
        Real.log (T.weight K D z0)) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hlog).2])
    _ = _ := by rw [Real.exp_add, Real.exp_log (T.weight_pos hK D z0)]

/-- Motion through one top length and width costs only a fixed factor. -/
theorem weight_slope_coordinates_local (T : SlopeBox) {K D : ℝ}
    (hK : 1 ≤ K) (hD : 0 ≤ D) {x0 x1 y0 y1 : ℝ}
    (hx : |x1-x0| ≤ T.length) (hy : |y1-y0| ≤ T.width) :
    T.weight K D (x1, y1 + T.slope*x1) ≤
      Real.exp (2*D) * T.weight K D (x0, y0 + T.slope*x0) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  apply (T.weight_slope_coordinates_le hK0 hD x0 x1 y0 y1).trans
  apply mul_le_mul_of_nonneg_right _ (T.weight_pos hK0 D _).le
  apply Real.exp_le_exp.mpr
  have hx' : |x1-x0|/T.length ≤ 1 := (div_le_one T.length_pos).mpr hx
  have hy' : |y1-y0|/T.width ≤ 1 := (div_le_one T.width_pos).mpr hy
  calc
    _ ≤ (D/K)*2 := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hD hK0.le)
    _ ≤ D*2 := mul_le_mul_of_nonneg_right (div_le_self hD hK) (by norm_num)
    _ = _ := by ring

end SlopeBox

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawInterval_horizontal_differentiable
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    DifferentiableAt ℝ (fun x => P.rawInterval coeff i lower upper x y) x := by
  exact planarPacketInterval_horizontal_differentiable_schwartz
    (ι := fun j => Σ l : P.labels j, Item j l) (fun j p => coeff j p.1 p.2)
    (fun j p k t => P.raw i j p.1 p.2 k t) lower upper hlu x y

theorem rawInterval_vertical_differentiable
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) (k : κ) :
    DifferentiableAt ℝ (fun y => P.rawInterval coeff i lower upper x y k) y := by
  apply planarPacketInterval_component_differentiable
    (ι := fun j => Σ l : P.labels j, Item j l)
  intro j p
  exact modulatedPlanarJet_differentiable (P.profile j p.1 p.2 k)
    (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
    (-P.rowSlope j p.1) (P.frequency k) P.scale y (P.length_pos j).ne' i x

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskMotion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual top mask preserves interval motion.  Only absolute mask
differences occur, so no nonvanishing hypothesis is imposed on the mask. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert
open PhaseCombinatorics

variable {κ : Type} [Fintype κ]

theorem masked_isometry_motion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E →ₗᵢ[ℝ] E) (v₁ v₀ : E) (q₁ q₀ B ε δ : ℝ)
    (hq : |q₁| ≤ 1) (hδ : 0 ≤ δ) (hmask : |q₁-q₀| ≤ δ)
    (hbase : ‖v₀‖ ≤ B) (hmove : ‖v₁-U v₀‖ ≤ ε) :
    ‖q₁ • v₁-U (q₀ • v₀)‖ ≤ ε+δ*B := by
  have heq : q₁ • v₁-U (q₀ • v₀) =
      q₁ • (v₁-U v₀)+(q₁-q₀) • U v₀ := by
    rw [U.map_smul, smul_sub, sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖q₁ • (v₁-U v₀)‖+‖(q₁-q₀) • U v₀‖ := norm_add_le _ _
    _ = |q₁| * ‖v₁-U v₀‖+|q₁-q₀| * ‖v₀‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, U.norm_map]
    _ ≤ 1*ε+δ*B := add_le_add
      (mul_le_mul hq hmove (norm_nonneg _) zero_le_one)
      (mul_le_mul hmask hbase (norm_nonneg _) hδ)
    _ = _ := by ring

namespace SlopeBox

theorem mask_slope_coordinates_motion (T : SlopeBox) (L A x₀ x₁ y₀ y₁ : ℝ)
    (hL : 0 < L) :
    |T.mask L A (x₁,y₁+T.slope*x₁)-T.mask L A (x₀,y₀+T.slope*x₀)| ≤
      (2*(⌈L⌉₊:ℝ)/L^A)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width) := by
  have h := T.mask_motion L A hL (x₁,y₁+T.slope*x₁) (x₀,y₀+T.slope*x₀)
  have heq : (y₁+T.slope*x₁)-(y₀+T.slope*x₀)-T.slope*(x₁-x₀) = y₁-y₀ := by ring
  simpa only [heq, abs_div, abs_of_pos T.length_pos, abs_of_pos T.width_pos] using h

end SlopeBox

namespace SourceLabeledLattice

variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]

theorem rawInterval_coeff_smul (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : ℝ) (jet : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    P.rawInterval (fun j l u => q • coeff j l u) jet lower upper x y =
      q • P.rawInterval coeff jet lower upper x y := by
  exact planarPacketInterval_coeff_smul (ι := fun j => Σ l : P.labels j, Item j l)
    (fun j p => coeff j p.1 p.2) (fun j p k t s => P.raw jet j p.1 p.2 k t s)
    q lower upper x y

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketMotionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit packet-motion coefficient at the angular averaging scale.
All three spatial ratios are bounded before applying polynomial absorption. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

theorem source_packet_displacement_ratios (g : AngularGrid) (T : SlopeBox)
    {w B : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (hwidth : B^2*w ≤ T.width)
    (h start : ℕ) (sR b : ℝ)
    (hs : g.index h sR = g.index h T.slope)
    (hblock : g.width h ≤ B*g.width start)
    (he : g.eligible (g.rootWidth/B^2) (w/T.length) start)
    (hb : |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ))) :
    let r := B^2*w/g.width start
    |b|/r ≤ 1/Real.sqrt (g.branching:ℝ) ∧
    |b|/T.length ≤ 1/Real.sqrt (g.branching:ℝ) ∧
    |(sR-T.slope)*b|/T.width ≤ 1/Real.sqrt (g.branching:ℝ) ∧
    |b| ≤ T.length ∧ |(sR-T.slope)*b| ≤ T.width := by
  dsimp only
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hG : (1:ℝ) ≤ g.branching := by
    exact_mod_cast (show 1 ≤ g.branching by have := g.branching_ge_two; omega)
  have hsqrt : 0 < Real.sqrt (g.branching:ℝ) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le hG)
  have hsqrt1 : 1 ≤ Real.sqrt (g.branching:ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hG
  have hc := g.width_pos start
  have hBsq : 1 ≤ B^2 := by nlinarith
  have hBsqw : 0 < B^2*w := mul_pos (sq_pos_of_pos hB0) hw
  have hr : 0 < B^2*w/g.width start := div_pos hBsqw hc
  have hlen := g.source_eligible_length_lower hw hB0 T.length_pos start he
  have hsmall : 1/Real.sqrt (g.branching:ℝ) ≤ 1 :=
    (div_le_one hsqrt).mpr hsqrt1
  have hratio : |b|/(B^2*w/g.width start) ≤ 1/Real.sqrt (g.branching:ℝ) := by
    calc
      _ ≤ (w/(g.width start*Real.sqrt (g.branching:ℝ)))/(B^2*w/g.width start) :=
        div_le_div_of_nonneg_right hb hr.le
      _ = (1/B^2)/Real.sqrt (g.branching:ℝ) := by
        field_simp [hw.ne',hc.ne',hB0.ne',hsqrt.ne']
      _ ≤ 1/Real.sqrt (g.branching:ℝ) :=
        div_le_div_of_nonneg_right ((div_le_one (sq_pos_of_pos hB0)).mpr hBsq) hsqrt.le
  have hlenratio : |b|/T.length ≤ 1/Real.sqrt (g.branching:ℝ) :=
    (div_le_div_of_nonneg_left (abs_nonneg b) hr hlen).trans hratio
  have hslope : |sR-T.slope| ≤ B*g.width start :=
    (g.same_cell_diameter h hs).trans hblock
  have htrans : |(sR-T.slope)*b|/T.width ≤ 1/Real.sqrt (g.branching:ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ ((B*g.width start)*(w/(g.width start*Real.sqrt (g.branching:ℝ))))/T.width :=
        div_le_div_of_nonneg_right
          (mul_le_mul hslope hb (abs_nonneg b) (mul_nonneg hB0.le hc.le)) T.width_pos.le
      _ ≤ ((B*g.width start)*(w/(g.width start*Real.sqrt (g.branching:ℝ))))/(B^2*w) :=
        div_le_div_of_nonneg_left (by positivity) hBsqw hwidth
      _ = (1/B)/Real.sqrt (g.branching:ℝ) := by
        field_simp [hw.ne',hc.ne',hB0.ne',hsqrt.ne']
      _ ≤ 1/Real.sqrt (g.branching:ℝ) :=
        div_le_div_of_nonneg_right ((div_le_one hB0).mpr hB) hsqrt.le
  refine ⟨hratio,hlenratio,htrans,?_,?_⟩
  · exact (div_le_one T.length_pos).mp (hlenratio.trans hsmall)
  · exact (div_le_one T.width_pos).mp (htrans.trans hsmall)

theorem source_packet_motion_coefficient (g : AngularGrid) (T : SlopeBox)
    {w B L A F Cfreq : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (hL : 0 < L)
    (hA : 0 ≤ A) (hCfreq : 0 ≤ Cfreq) (hF : F ≤ Cfreq/w)
    (hwidth : B^2*w ≤ T.width) (h start : ℕ) (sR b : ℝ)
    (hs : g.index h sR = g.index h T.slope)
    (hblock : g.width h ≤ B*g.width start)
    (he : g.eligible (g.rootWidth/B^2) (w/T.length) start)
    (hb : |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)))
    (p maskExponent D : ℝ) :
    let r := B^2*w/g.width start
    let center := g.center start (g.index start T.slope)
    (L^(2*p+4)/r)*Real.exp (16*D)*|b|+(A/T.width)*|(sR-T.slope)*b|+
      (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
        (|b|/T.length+|(sR-T.slope)*b|/T.width)*A+
      F*A*|T.slope-center| * |b| ≤
    (L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A)/
      Real.sqrt (g.branching:ℝ) := by
  dsimp only
  obtain ⟨hratio,hlenratio,htrans,-,-⟩ :=
    g.source_packet_displacement_ratios T hw hB hwidth h start sR b hs hblock he hb
  have hc := g.width_pos start
  have hG : (0:ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have := g.branching_ge_two; omega)
  have hsqrt := Real.sqrt_pos.mpr hG
  have hcenter : |T.slope-g.center start (g.index start T.slope)| ≤ g.width start :=
    (g.slope_dist_center_le start T.slope).trans (by linarith)
  have hcarrier : F*|T.slope-g.center start (g.index start T.slope)| * |b| ≤
      Cfreq/Real.sqrt (g.branching:ℝ) := by
    calc
      _ ≤ (Cfreq/w)*g.width start*(w/(g.width start*Real.sqrt (g.branching:ℝ))) :=
        mul_le_mul (mul_le_mul hF hcenter (abs_nonneg _) (div_nonneg hCfreq hw.le))
          hb (abs_nonneg _) (mul_nonneg (div_nonneg hCfreq hw.le) hc.le)
      _ = _ := by field_simp [hw.ne',hc.ne',hsqrt.ne']
  have hfirst := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (Real.rpow_nonneg hL.le (2*p+4)) (Real.exp_pos (16*D)).le)
  have hsecond := mul_le_mul_of_nonneg_left htrans hA
  have hthird := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hlenratio htrans)
      (show 0 ≤ 2*(⌈L⌉₊:ℝ)/L^maskExponent by positivity)) hA
  have hfourth := mul_le_mul_of_nonneg_right hcarrier hA
  calc
    _ = (L^(2*p+4)*Real.exp (16*D))*(|b|/(B^2*w/g.width start))+
        A*(|(sR-T.slope)*b|/T.width)+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|b|/T.length+|(sR-T.slope)*b|/T.width)*A+
        (F*|T.slope-g.center start (g.index start T.slope)| * |b|)*A := by ring
    _ ≤ (L^(2*p+4)*Real.exp (16*D))*(1/Real.sqrt (g.branching:ℝ))+
        A*(1/Real.sqrt (g.branching:ℝ))+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (1/Real.sqrt (g.branching:ℝ)+1/Real.sqrt (g.branching:ℝ))*A+
        (Cfreq/Real.sqrt (g.branching:ℝ))*A :=
      add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y t : ℝ) :
    P.raw i j l u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j l u k) (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u+t*P.actualX j l u) (P.length j) P.width
    (t+P.rowSlope j l) (P.frequency k) P.scale y t (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j l u+t*P.actualX j l u-t*P.actualX j l u = P.actualZ j l u := by ring
  have hd : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  simpa only [hc,hd,raw,physicalPacket] using h.symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSegmentWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact exponential form of a source path product beginning at
an arbitrary angular level. This connects the shared family with the
full-root-paid segment variation estimate. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem segmentWeight_eq_path_product (n b : ℕ → ℝ) (phase : ℕ → ℂ)
    (a : ℝ) (start N : ℕ) (hn : 0 < n N)
    (hn' : ∀ j ∈ Finset.Ico start N, 0 < n (j+1))
    (hb : ∀ j ∈ Finset.Ico start N, 0 < b j) :
    segmentWeight n (boundaryLog n b) phase a start N =
      ((n N ^ (-a) : ℝ) : ℂ) * ∏ j ∈ Finset.Ico start N,
        Complex.exp (phase j * (Real.log (n (j+1) / b j) : ℂ)) := by
  have hpow : ((n N ^ (-a) : ℝ) : ℂ) =
      Complex.exp ((-a * Real.log (n N) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hn, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hpow, ← Complex.exp_sum, ← Complex.exp_add, segmentWeight, segmentLog]
  congr 1
  have hsum : (∑ j ∈ Finset.Ico start N, phase j * (Real.log (n (j+1) / b j) : ℂ)) =
      -(∑ j ∈ Finset.Ico start N, phase j * (boundaryLog n b j : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [boundaryLog, Real.log_div (hn' j hj).ne' (hb j hj).ne',
      Real.log_div (hb j hj).ne' (hn' j hj).ne']
    push_cast
    ring
  rw [hsum]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of each single-top contribution to the shared
analytic family with the stopping-weighted source band sum. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
attribute [local instance] Classical.propDecidable

theorem sourcePacketAmplitude_single_top (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) M) (a : ℝ) (x : X)
    {N : ℕ} (stop : Fin N → ℕ) (hstop : ∀ j, stop j ≤ M)
    (value : Fin N → E) (start : ℕ) :
    let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
    let b := fun j => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (g.index (j+1) (slope top)) x
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
      (fun _ => top) stop value phase a x start (g.index start (slope top)) =
      ∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
        segmentWeight n (boundaryLog n b) phase a start (stop j) • value j := by
  dsimp only
  let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  let b := fun j => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
    (g.index (j+1) (slope top)) x
  have hn (j : ℕ) (hj : j ≤ M) : 0 < n j :=
    g.path_mass_pos tops slope precision cutoff weight hw j top htop
      (g.eligible_of_le (hp top htop) hj he) x
  have hb (j : ℕ) (hj : j < M) : 0 < b j :=
    (hn (j+1) (by omega)).trans_le
      (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
        (fun i x => (hw i x).le) hK gap j (slope top) x).1
  have hset : g.packetSet Finset.univ (fun _ : Fin N => slope top) stop start
      (g.index start (slope top)) = Finset.univ.filter (fun j => start ≤ stop j) := by
    ext j
    simp only [packetSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold sourcePacketAmplitude packetAmplitude
  rw [hset]
  apply Finset.sum_congr rfl
  intro j _
  have heq := segmentWeight_eq_path_product n b phase a start (stop j) (hn _ (hstop j))
    (fun k hk => hn (k+1) (by have := (Finset.mem_Ico.mp hk).2; have := hstop j; omega))
    (fun k hk => hb k (by have := (Finset.mem_Ico.mp hk).2; have := hstop j; omega))
  simp only [sourcePacketBase, smul_smul]
  rw [heq]
  congr 1
  exact mul_comm _ _

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic amplitude of one source top has an envelope linear in
its original top weight. This retains integrability and can be summed
over an angular node without a factor counting its tops. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

variable {ι X : Type*}

/-- Summing the linear envelope over a node charges its actual eligible
mass and introduces no cardinality factor. -/
theorem node_amplitude_linear_envelope {E : Type*} [NormedAddCommGroup E]
    (grid : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (amplitude : ι → E)
    (level : ℕ) (cell : ℤ) (z : X) (C : ℝ)
    (hamp : ∀ i ∈ grid.cellTops tops slope precision cutoff level cell,
      ‖amplitude i‖ ≤ C*weight i z) :
    ‖∑ i ∈ grid.cellTops tops slope precision cutoff level cell, amplitude i‖ ≤
      C*grid.mass tops slope precision cutoff weight level cell z := by
  apply (norm_sum_le _ _).trans
  change (∑ i ∈ grid.cellTops tops slope precision cutoff level cell, ‖amplitude i‖) ≤ _
  rw [mass, Finset.mul_sum]
  exact Finset.sum_le_sum hamp

/-- The individual four-power envelope implies the node's linear-mass
bound with only the fixed upper bound for a single top weight. -/
theorem node_amplitude_fourth_envelope {E : Type*} [NormedAddCommGroup E]
    (grid : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (amplitude : ι → E)
    (level : ℕ) (cell : ℤ) (z : X) (A C : ℝ) (hA : 0 ≤ A)
    (hw : ∀ i ∈ grid.cellTops tops slope precision cutoff level cell, 0 ≤ weight i z)
    (hC : ∀ i ∈ grid.cellTops tops slope precision cutoff level cell, weight i z ≤ C)
    (hamp : ∀ i ∈ grid.cellTops tops slope precision cutoff level cell,
      ‖amplitude i‖ ≤ A*(weight i z)^4) :
    ‖∑ i ∈ grid.cellTops tops slope precision cutoff level cell, amplitude i‖ ≤
      (A*C^3)*grid.mass tops slope precision cutoff weight level cell z := by
  apply grid.node_amplitude_linear_envelope tops slope precision cutoff weight amplitude
    level cell z (A*C^3)
  intro i hi
  have hpow : (weight i z)^4 ≤ C^3*weight i z := by
    calc
      _ = (weight i z)^3*weight i z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw i hi) (hC i hi) 3) (hw i hi)
  calc
    ‖amplitude i‖ ≤ A*(weight i z)^4 := hamp i hi
    _ ≤ A*(C^3*weight i z) := mul_le_mul_of_nonneg_left hpow hA
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact assembly of the single-top source amplitudes into the shared
finite analytic family. All masses retain the original top index set. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Regrouping the actual packet family by assigned top introduces exactly
the eligible tops in the angular node. Empty packet fibers contribute zero. -/
theorem sourcePacketAmplitude_top_fibers (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (K : ℕ) (gap : ℕ → ℝ)
    (bands : Finset σ) (stop : ι → σ → ℕ) (value : ι → σ → E)
    (he : ∀ t ∈ tops, ∀ j ∈ bands, g.eligible cutoff (precision t) (stop t j))
    (phase : ℕ → ℂ) (a : ℝ) (z : X) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap (tops ×ˢ bands)
      Prod.fst (fun p => stop p.1 p.2) (fun p => value p.1 p.2) phase a z level cell =
      ∑ t ∈ g.cellTops tops slope precision cutoff level cell,
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
          (fun _ => t) (stop t) (value t) phase a z level (g.index level (slope t)) := by
  simp only [sourcePacketAmplitude, packetAmplitude, packetSet, Finset.sum_filter,
    Finset.sum_product, cellTops]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : g.index level (slope t) = cell
  · by_cases hel : g.eligible cutoff (precision t) level
    · simp [hc, hel, sourcePacketBase]
    · have hnone (j : σ) (hj : j ∈ bands) : ¬level ≤ stop t j := by
        intro hle
        exact hel (g.eligible_of_le (hp t ht) hle (he t ht j hj))
      simp only [hc, hel, and_false, ite_false, if_false]
      apply Finset.sum_eq_zero
      intro j hj
      simp [hnone j hj]
  · simp [hc]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalSingleScale
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single length of original physical packets has a uniform positive
summation bound. Selector overlap is counted before convolution. The
analyzing coefficients remain those of the original profiles, while the
synthesis profiles may be any profiles with the same seminorm bound. -/

noncomputable section
open MeasureTheory
open Filter
open scoped BigOperators ComplexConjugate Topology
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The shear changes coordinates, not the original analyzing coefficient. -/
theorem physicalMultiplierCoefficient_shear (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    analyzingCoefficient volume (fun _ : Item j l => P.length j*P.width)
      (fun u k z => b j l k (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
      (fun z => g (slopeShear t z)) u =
        P.physicalMultiplierCoefficient t b v g j l u := by
  ext k
  simp only [analyzingCoefficient,physicalMultiplierCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g (slopeShear t z) k*conj
      (b j l k (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
        ∂volume.prod volume) = _
  have hw (z : ℝ×ℝ) : P.raw 0 j l u k z.2 z.1 =
      P.physicalPacket t j l u k (slopeShear t z) := by
    exact congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
      (P.raw_eq_physical_slice 0 j l u k z.2 t)
  simp_rw [hw]
  congr 1
  exact (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding
    (fun z => g z k*conj (b j l k (v z)*P.physicalPacket t j l u k z))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorCoefficientNorm
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient normalization for the original smooth selectors.
It uses the physical analyzing packet, with no replacement of its selector
by a sharp cutoff and no dependence on the number of coordinates. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalMultiplierCoefficient_norm (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    ‖P.physicalMultiplierCoefficient t b v g j l u‖ ≤ P.constant*Real.pi^2 := by
  let C : ℝ := (2^P.order*P.profileBound)*P.ratioBound^2
  let W : ℝ×ℝ → ℝ := fun z => C*
    (lineEnvelope (P.actualX j l u) (P.length j) 1 z.1*
      lineEnvelope (P.actualZ j l u) P.width 1 z.2)
  have hC : 0 < C := by
    have hR := zero_lt_one.trans_le P.ratioBound_ge_one
    have hP := P.profileBound_pos
    dsimp [C]
    positivity
  have hW : Integrable W :=
    ((integrable_lineEnvelope_one _ _ (P.length_pos j)).mul_prod
      (integrable_lineEnvelope_one _ _ P.width_pos)).const_mul C
  have hW0 (z : ℝ×ℝ) : 0 ≤ W z := by
    dsimp [W]
    exact mul_nonneg hC.le (mul_nonneg (lineEnvelope_nonneg _ _ _ _)
      (lineEnvelope_nonneg _ _ _ _))
  let test := fun z => g (slopeShear t z)
  let wave := fun (u : Item j l) (k : κ) (z : ℝ×ℝ) =>
    b j l k (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1
  have htest : Measurable test := hg.comp (slopeShear t).measurable
  have hwave (k : κ) : Measurable (wave u k) :=
    ((hb j l k).comp (hv.comp (slopeShear t).measurable)).mul
      (P.raw_swapped_joint_measurable 0 j l u k)
  have hbound (k : κ) (z : ℝ×ℝ) : ‖wave u k z‖ ≤ W z := by
    have hr := P.raw_absolute_envelope 0 j l u k z.2 z.1
    have ho : 1 ≤ P.order := by have := P.order_ge_three; omega
    have he : lineEnvelope (P.actualX j l u) (P.length j) P.order z.1*
        lineEnvelope (P.actualZ j l u) P.width P.order z.2 ≤
      lineEnvelope (P.actualX j l u) (P.length j) 1 z.1*
        lineEnvelope (P.actualZ j l u) P.width 1 z.2 :=
      mul_le_mul (lineEnvelope_antitone _ _ _ ho) (lineEnvelope_antitone _ _ _ ho)
        (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
    have hr' : ‖P.raw 0 j l u k z.2 z.1‖ ≤ W z :=
      hr.trans (mul_le_mul_of_nonneg_left he hC.le)
    dsimp only [wave]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hb1 j l k _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hr')
  have hint (k : κ) : Integrable (fun z => test z k*conj (wave u k z)) := by
    have hgm : Measurable (fun z => test z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp htest)
    apply hW.mono' (hgm.mul (continuous_star.measurable.comp (hwave k))).aestronglyMeasurable
    filter_upwards [] with z
    change ‖test z k*conj (wave u k z)‖ ≤ W z
    rw [norm_mul,Complex.norm_conj]
    have hk : ‖test z k‖ ≤ 1 := (PiLp.norm_apply_le (test z) k).trans (hg1 _)
    exact (mul_le_mul_of_nonneg_right hk (norm_nonneg _)).trans
      (by simpa only [one_mul] using hbound k z)
  have hn := analyzingCoefficient_norm_le volume (fun _ : Item j l => P.length j*P.width)
    wave test u W (mul_pos (P.length_pos j) P.width_pos) hW hW0 hint
    (fun z => hg1 _) hbound
  have hI : (∫ z, W z) = (C*Real.pi^2)*(P.length j*P.width) := by
    dsimp only [W]
    rw [integral_const_mul,Measure.volume_eq_prod,integral_prod_mul,
      integral_lineEnvelope_one _ _ (P.length_pos j),
      integral_lineEnvelope_one _ _ P.width_pos]
    ring
  rw [hI] at hn
  have hn' : ‖P.physicalMultiplierCoefficient t b v g j l u‖ ≤ C*Real.pi^2 := by
    have harea : P.length j*P.width ≠ 0 := (mul_pos (P.length_pos j) P.width_pos).ne'
    have hcancel : (P.length j*P.width)⁻¹*(C*Real.pi^2*(P.length j*P.width)) =
        C*Real.pi^2 := by
      calc
        _ = (C*Real.pi^2)*((P.length j*P.width)⁻¹*(P.length j*P.width)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ harea,mul_one]
    rw [hcancel] at hn
    rw [← P.physicalMultiplierCoefficient_shear t b v g j l u]
    exact hn
  have hc : C ≤ P.constant := by
    have hcar : 1 ≤ P.carrierBound+2 := by linarith [P.carrierBound_nonneg]
    have hpow : (1:ℝ) ≤ 3^(2*P.order) := one_le_pow₀ (by norm_num)
    calc
      C = C*1*1 := by ring
      _ ≤ C*(P.carrierBound+2)*3^(2*P.order) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcar hC.le) hpow
          (by norm_num) (mul_nonneg hC.le (by linarith))
      _ = P.constant := by dsimp [C,constant]; ring
  exact hn'.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularLossMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative motion of nonnegative logarithmic losses. Both the submass
and its complement are actual positive sums. Vanishing complements give
identically zero loss and need no logarithmic positivity assumption. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- Concavity of the logarithm controls multiplicative changes in its
nonnegative argument, uniformly even at argument zero. -/
theorem log_one_add_scaled_le {c q : ℝ} (hc : 1 ≤ c) (hq : 0 ≤ q) :
    Real.log (1+c*q) ≤ c*Real.log (1+q) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hi : 0 ≤ 1/c := by positivity
  have hi1 : 1/c ≤ 1 := (div_le_one hc0).mpr hc
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1+c*q ∈ Set.Ioi 0 by change 0 < 1+c*q; positivity)
    (sub_nonneg.mpr hi1) hi (by ring : (1-1/c)+1/c=1)
  have heq : (1-1/c)*1+(1/c)*(1+c*q)=1+q := by field_simp [hc0.ne']; ring
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  rw [heq] at h
  have hm := mul_le_mul_of_nonneg_left h hc0.le
  have hcancel : c*((1/c)*Real.log (1+c*q))=Real.log (1+c*q) := by field_simp [hc0.ne']
  rw [hcancel] at hm
  exact hm

theorem positive_le_exp_mul_of_log_motion {a b delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : |Real.log b-Real.log a| ≤ delta) :
    b ≤ Real.exp delta*a := by
  calc
    b = Real.exp (Real.log b) := (Real.exp_log hb).symm
    _ ≤ Real.exp (delta+Real.log a) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp h).2])
    _ = _ := by rw [Real.exp_add, Real.exp_log ha]

/-- The loss log((a+b)/a) varies relatively with the positive submass and
complement, instead of paying a constant independent of that loss. -/
theorem positive_complement_loss_motion {a b a' b' delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hdelta : 0 ≤ delta)
    (hA : |Real.log a'-Real.log a| ≤ delta)
    (hB : |Real.log b'-Real.log b| ≤ delta) :
    |Real.log ((a'+b')/a')-Real.log ((a+b)/a)| ≤
      (Real.exp (2*delta)-1)*Real.log ((a+b)/a) := by
  let c := Real.exp (2*delta)
  have hc : 1 ≤ c := Real.one_le_exp (by positivity)
  have ha0 : 0 < b/a := div_pos hb ha
  have ha1 : 0 < b'/a' := div_pos hb' ha'
  have hodds := positive_ratio_log_motion hb ha hb' ha' hB hA
  have hforward : b'/a' ≤ c*(b/a) :=
    positive_le_exp_mul_of_log_motion ha0 ha1 hodds
  have hreverse : b/a ≤ c*(b'/a') := positive_le_exp_mul_of_log_motion ha1 ha0 (by
    simpa only [abs_sub_comm] using hodds)
  have hup : Real.log (1+b'/a') ≤ c*Real.log (1+b/a) := by
    exact (Real.log_le_log (by positivity) (show 1+b'/a' ≤ 1+c*(b/a) from add_le_add le_rfl hforward)).trans
      (log_one_add_scaled_le hc ha0.le)
  have hrev : Real.log (1+b/a) ≤ c*Real.log (1+b'/a') := by
    exact (Real.log_le_log (by positivity) (show 1+b/a ≤ 1+c*(b'/a') from add_le_add le_rfl hreverse)).trans
      (log_one_add_scaled_le hc ha1.le)
  have hnonneg : 0 ≤ Real.log (1+b/a) := Real.log_nonneg (by linarith)
  have hnonneg' : 0 ≤ Real.log (1+b'/a') := Real.log_nonneg (by linarith)
  have habs : |Real.log (1+b'/a')-Real.log (1+b/a)| ≤
      (c-1)*Real.log (1+b/a) := by
    apply abs_le.mpr
    constructor
    · by_cases hle : Real.log (1+b'/a') ≤ Real.log (1+b/a)
      · have hm := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hc)
        nlinarith
      · have hm : 0 ≤ (c-1)*Real.log (1+b/a) := mul_nonneg (sub_nonneg.mpr hc) hnonneg
        linarith
    · nlinarith
  simpa only [add_div, div_self ha.ne', div_self ha'.ne'] using habs

/-- A finite submass and its actual set complement give relative loss
motion. Empty complements are handled exactly, as zero loss. -/
theorem finite_submass_loss_motion {ι : Type*} [DecidableEq ι] (C A : Finset ι) (hsub : A ⊆ C)
    (hA : A.Nonempty) (w0 w1 : ι → ℝ)
    (hw0 : ∀ t ∈ C, 0 < w0 t) (hw1 : ∀ t ∈ C, 0 < w1 t)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hmass : |Real.log (∑ t ∈ A, w1 t)-Real.log (∑ t ∈ A, w0 t)| ≤ delta)
    (hcomplement : (C\A).Nonempty →
      |Real.log (∑ t ∈ C\A, w1 t)-Real.log (∑ t ∈ C\A, w0 t)| ≤ delta) :
    |Real.log ((∑ t ∈ C, w1 t)/(∑ t ∈ A, w1 t)) -
      Real.log ((∑ t ∈ C, w0 t)/(∑ t ∈ A, w0 t))| ≤
        (Real.exp (2*delta)-1)*Real.log ((∑ t ∈ C, w0 t)/(∑ t ∈ A, w0 t)) := by
  classical
  have hpos0 : 0 < ∑ t ∈ A, w0 t := Finset.sum_pos (fun t ht => hw0 t (hsub ht)) hA
  have hpos1 : 0 < ∑ t ∈ A, w1 t := Finset.sum_pos (fun t ht => hw1 t (hsub ht)) hA
  have hsum (w : ι → ℝ) : (∑ t ∈ C, w t) = (∑ t ∈ A, w t)+(∑ t ∈ C\A, w t) := by
    have h := Finset.sum_sdiff (f := w) hsub
    linarith
  rw [hsum w0, hsum w1]
  by_cases hnonempty : (C\A).Nonempty
  · have hc0 : 0 < ∑ t ∈ C\A, w0 t :=
      Finset.sum_pos (fun t ht => hw0 t (Finset.mem_sdiff.mp ht).1) hnonempty
    have hc1 : 0 < ∑ t ∈ C\A, w1 t :=
      Finset.sum_pos (fun t ht => hw1 t (Finset.mem_sdiff.mp ht).1) hnonempty
    exact positive_complement_loss_motion hpos0 hc0 hpos1 hc1 hdelta hmass
      (hcomplement hnonempty)
  · have he : C\A=∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [he, Finset.sum_empty, add_zero, div_self hpos0.ne', div_self hpos1.ne',
      Real.log_one, sub_self, abs_zero, mul_zero, le_refl]

namespace AngularGrid

/-- At the source mesh scale, the child-to-containing-mass loss has a
relative error of order G^(-1/2), including identically zero losses. -/
theorem source_relative_loss_motion {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hK : 0 < K) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (C A : Finset ι) (hsub : A ⊆ C) (hA : A.Nonempty)
    (hC : C ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (a : ℝ) (ha : |a| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    let loss := fun x => Real.log ((∑ t ∈ C, (T t).weight K D x)/(∑ t ∈ A, (T t).weight K D x))
    let delta := (5*D/K)/Real.sqrt (g.branching:ℝ)
    |loss (SlopeBox.lineShift sR a z)-loss z| ≤ (Real.exp (2*delta)-1)*loss z := by
  classical
  dsimp only
  apply finite_submass_loss_motion C A hsub hA
    (fun t => (T t).weight K D z) (fun t => (T t).weight K D (SlopeBox.lineShift sR a z))
    (fun t _ => (T t).weight_pos hK D z) (fun t _ => (T t).weight_pos hK D _)
  · positivity
  · exact g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A hA (hsub.trans hC) a ha z
  · intro hnonempty
    exact g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock (C\A) hnonempty
      (fun t ht => hC (Finset.mem_sdiff.mp ht).1) a ha z

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedTopEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned packets need length bounds only on their nonempty scales.
Clipping empty-scale stopping levels preserves the exact source amplitude.
The original-selector concentration then supplies the needed intervals. -/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawBand_eq_zero_of_no_item (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (j : Fin N) (x y : ℝ)
    (hempty : ∀ (l : P.labels j), Item j l → False) :
    P.rawBand coeff i j x y = 0 := by
  ext k
  simp only [rawBand,vectorPacketSynthesis,packetSynthesis_apply,PiLp.zero_apply]
  apply Finset.sum_eq_zero
  intro u _
  exact False.elim (hempty u.1 u.2)

end LipschitzHilbert.SourceLabeledLattice

namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable


variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Stopping times may change freely for zero packets. -/
theorem sourcePacketAmplitude_stop_congr_of_zero
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cut : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop stop' : σ → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (z : X) (level : ℕ) (cell : ℤ)
    (h : ∀ p ∈ packets, stop p = stop' p ∨ value p = 0) :
    g.sourcePacketAmplitude tops slope precision cut weight K gap packets assigned stop
      value phase a z level cell =
    g.sourcePacketAmplitude tops slope precision cut weight K gap packets assigned stop'
      value phase a z level cell := by
  simp only [sourcePacketAmplitude,packetAmplitude,packetSet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rcases h p hp with he | hz
  · simp only [sourcePacketBase,he]
  · simp only [sourcePacketBase,hz,smul_zero,ite_self]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedBandStops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipping a band's stopping level changes no packet when that band
has no items. This permits itemwise shortness in every later motion bound. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {ι : Type*} {N : ℕ} {κ : Type} {Label : Fin N → Type}
  {Item : ∀ j, Label j → Type} [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem sourceBandAmplitude_clip_stop (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cut : ℝ)
    (weight : ι → (ℝ×ℝ) → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (rawStop : ι → Fin N → ℕ) (M : ι → ℕ)
    (hstop : ∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l), rawStop t j ≤ M t)
    (x y : ι → ℝ) (phase : ℕ → ℂ) (a : ℝ) (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => rawStop p.1 p.2)
      (fun p => (P p.1).rawBand (coeff p.1) i p.2 (x p.1) (y p.1)) phase a z level cell =
    g.sourcePacketAmplitude tops slope precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst
      (fun p => min (rawStop p.1 p.2) (M p.1))
      (fun p => (P p.1).rawBand (coeff p.1) i p.2 (x p.1) (y p.1)) phase a z level cell := by
  apply g.sourcePacketAmplitude_stop_congr_of_zero
  intro p hp
  by_cases hs : rawStop p.1 p.2 ≤ M p.1
  · exact Or.inl (min_eq_left hs).symm
  · right
    apply (P p.1).rawBand_eq_zero_of_no_item
    intro l u
    exact hs (hstop p.1 (Finset.mem_product.mp hp).1 p.2 l u)

/-- The actual eligibility stop is bounded whenever an item exists. -/
theorem source_length_stop_le_of_item (g : AngularGrid)
    (tops : Finset ι) (T : ι → SlopeBox) (P : ι → SourceLabeledLattice N κ Label Item)
    (w cut : ℝ) (hw : 0 < w) (M : ι → ℕ)
    (hzero : ∀ t ∈ tops, ∀ j, g.eligible cut (w/(P t).length j) 0)
    (hshort : ∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length)
    (hmax : ∀ t ∈ tops, ∀ k, g.eligible cut (w/(T t).length) k → k ≤ M t)
    (t : ι) (ht : t ∈ tops) (j : Fin N) (l : (P t).labels j) (u : Item j l) :
    g.lastEligible cut (w/(P t).length j) (div_pos hw ((P t).length_pos j)) ≤ M t := by
  apply hmax t ht
  have hj := g.eligible_lastEligible cut (w/(P t).length j)
    (div_pos hw ((P t).length_pos j)) (hzero t ht j)
  exact (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hw.le ((P t).length_pos j) (hshort t ht j l u))
    (by positivity)).trans hj

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedLabeledGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packetwise top geometry survives slotting and frozen-active label
restriction. These operations keep every retained center and length. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem slotted_supportedTopGeometry
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
    {T : SlopeBox} {K : ℝ} {D : ℕ} (G : SourceSupportedLabeledTopGeometry P T K D)
    (b : Fin B) : SourceSupportedLatticeTopGeometry (P.slotted hcard b) T K D where
  length_le := fun j p => G.length_le j p.1.1 p.1.2
  width_le := G.width_le
  centerX_le := by
    intro j p
    rw [P.slotted_actualX hcard, P.slotted_length hcard]
    exact G.centerX_le j p.1.1 p.1.2
  centerZ_le := by
    intro j p
    rw [P.slotted_actualZ hcard]
    exact G.centerZ_le j p.1.1 p.1.2
  order_le := G.order_le
  scale_eq := G.scale_eq

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedWeightedDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative estimate uses upper scale bounds only at
actual packet items. Empty scales do not constrain the top window. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
theorem top_weighted_selected_derivative_of_supported {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W u v r R x y C cutoff : ℝ) (q : ℕ)
    (hL : 0 < L) (hW : 0 < W) (hr : 0 < r) (hR : 0 < R)
    (hLr : ∀ j (_i : ι j), L/(2:ℝ)^j.val ≤ r) (hWR : W ≤ R) (hC : 0 ≤ C) (hcutoff : 0 < cutoff)
    (hc : ∀ j i, ‖c j i‖ ≤ 1)
    (hcx : ∀ j i, |a+(L/(2:ℝ)^j.val)*(site j i).1-u| ≤ r)
    (hcy : ∀ j i, |b+W*(site j i).2-v| ≤ R)
    (s : Finset (Fin N)) (hs : ∀ j ∈ s, cutoff ≤ L/(2:ℝ)^j.val)
    (hf : ∀ j i k, ‖deriv (f j i k) x‖ ≤ (C/(L/(2:ℝ)^j.val))*
      (lineEnvelope (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) (3+2*q) x *
        lineEnvelope (b+W*(site j i).2) W (2+2*q) y)) :
    (polynomialWeight u r q x*polynomialWeight v R q y)*
      ‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖ ≤
        4*((16^q*(16^q*C))*(4*Real.pi)^2)/cutoff := by
  apply selected_scale_weighted_derivative_bound c f site hinj a b L W x y
    (16^q*(16^q*C)) (polynomialWeight u r q x*polynomialWeight v R q y) cutoff
    hL hW.ne' (by positivity)
    (mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))) hcutoff hc s hs
  intro j i k
  have hlen : 0 < L/(2:ℝ)^j.val := div_pos hL (by positivity)
  have h := topWeight_mul_envelope x y u r v R
    (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) (b+W*(site j i).2) W
    (C/(L/(2:ℝ)^j.val)) q 3 2 hlen hr hW hR (hLr j i) hWR
    (hcx j i) (hcy j i) (div_nonneg hC hlen.le)
  have hw : 0 ≤ polynomialWeight u r q x*polynomialWeight v R q y :=
    mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
  exact (mul_le_mul_of_nonneg_left (hf j i k) hw).trans (by convert h using 1 <;> first | rfl | ring)


theorem top_weighted_selected_derivative_bounded_of_supported {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W u v r R x y C B cutoff : ℝ) (q : ℕ)
    (hL : 0 < L) (hW : 0 < W) (hr : 0 < r) (hR : 0 < R)
    (hLr : ∀ j (_i : ι j), L/(2:ℝ)^j.val ≤ r) (hWR : W ≤ R) (hC : 0 ≤ C) (hB : 0 < B) (hcutoff : 0 < cutoff)
    (hc : ∀ j i, ‖c j i‖ ≤ B)
    (hcx : ∀ j i, |a+(L/(2:ℝ)^j.val)*(site j i).1-u| ≤ r)
    (hcy : ∀ j i, |b+W*(site j i).2-v| ≤ R)
    (s : Finset (Fin N)) (hs : ∀ j ∈ s, cutoff ≤ L/(2:ℝ)^j.val)
    (hf : ∀ j i k, ‖deriv (f j i k) x‖ ≤ (C/(L/(2:ℝ)^j.val))*
      (lineEnvelope (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) (3+2*q) x *
        lineEnvelope (b+W*(site j i).2) W (2+2*q) y)) :
    (polynomialWeight u r q x*polynomialWeight v R q y)*
      ‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖ ≤
        B*(4*((16^q*(16^q*C))*(4*Real.pi)^2)/cutoff) := by
  have hn (j : Fin N) (i : ι j) : ‖B⁻¹ • c j i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    exact (mul_le_mul_of_nonneg_left (hc j i) (inv_nonneg.mpr hB.le)).trans_eq
      (inv_mul_cancel₀ hB.ne')
  have h := top_weighted_selected_derivative_of_supported (fun j i => B⁻¹ • c j i) f site hinj
    a b L W u v r R x y C cutoff q hL hW hr hR hLr hWR hC hcutoff hn hcx hcy s hs hf
  have hd := HasDerivAt.fun_sum (u := s) (fun j _ =>
    (vectorPacketSynthesis_hasDerivAt (c j) (f j) x).differentiableAt.hasDerivAt)
  have hdn := HasDerivAt.fun_sum (u := s) (fun j _ =>
    (vectorPacketSynthesis_hasDerivAt (fun i => B⁻¹ • c j i) (f j) x).differentiableAt.hasDerivAt)
  have hdscaled : deriv
      (fun t => ∑ j ∈ s, vectorPacketSynthesis (fun i => B⁻¹ • c j i) (f j) t) x =
      B⁻¹ • deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x := by
    rw [hdn.deriv,hd.deriv]
    simp only [vectorPacketSynthesis_deriv_coeff_smul,Finset.smul_sum]
  rw [hdscaled, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)] at h
  have hh := mul_le_mul_of_nonneg_left h hB.le
  calc
    _ = B*((polynomialWeight u r q x*polynomialWeight v R q y)*
        (B⁻¹*‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖)) := by
      rw [show B*((polynomialWeight u r q x*polynomialWeight v R q y)*
        (B⁻¹*‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖)) =
        (B*B⁻¹)*((polynomialWeight u r q x*polynomialWeight v R q y)*
          ‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖) by ring,
        mul_inv_cancel₀ hB.ne', one_mul]
    _ ≤ _ := hh

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedSelectorDerivative
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal derivative estimate uses the coefficient norm bound
for the original smooth selector. It supplies the horizontal term in the
motion and prediction estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem boundedSelectedTopSum_horizontal_bound_of_supported (P : SourceLatticePacket N κ ι)
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)
    {K : ℝ} {D : ℕ} (T : SlopeBox) (hK : 0 < K)
    (G : SourceSupportedLatticeTopGeometry P T K D)
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (hcoeff : ∀ j u, ‖coeff j u‖ ≤ P.constant*Real.pi^2)
    (s : Finset (Fin N)) (r : ℝ) (hr : 0 < r) (hs : ∀ j ∈ s, r ≤ P.length j)
    (z : ℝ × ℝ) :
    ‖deriv (fun x => P.boundedSelectedTopSum alt hAlt s coeff x (z.2-T.slope*z.1)) z.1‖ ≤
      (P.crossDerivativeConstant D/r)*(T.weight K (D:ℝ) z)^8 := by
  let y := z.2-T.slope*z.1
  let w := polynomialWeight T.x (K*T.length) (8*D+1) z.1 *
    polynomialWeight (T.y-T.slope*T.x) (K*T.width) (8*D+1) y
  have hw : 0 < w := mul_pos
    (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
    (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
  have hderiv (j : Fin N) (u : ι j) (k : κ) :
      ‖deriv ((P.withProfile alt hAlt).raw 0 j u k y) z.1‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.family.centerX j u) (P.length j) (3+2*(8*D+1)) z.1 *
          lineEnvelope (P.family.centerZ j u) P.width (2+2*(8*D+1)) y) := by
    exact (P.withProfile alt hAlt).raw_top_derivative_bound D G.order_le 0 j u k y z.1
  have hb := top_weighted_selected_derivative_bounded_of_supported
    (coeff) (fun j u k => (P.withProfile alt hAlt).raw 0 j u k y) P.family.site P.family.site_injective
    P.family.baseX P.family.baseZ P.topLength P.width T.x (T.y-T.slope*T.x)
    (K*T.length) (K*T.width) z.1 y P.constant (P.constant*Real.pi^2) r (8*D+1)
    P.topLength_pos P.width_pos (mul_pos hK T.length_pos) (mul_pos hK T.width_pos)
    G.length_le G.width_le P.constant_pos.le (mul_pos P.constant_pos (sq_pos_of_pos Real.pi_pos)) hr
    hcoeff
    (fun j u => P.family_centerX_local j u T.x (K * T.length) (G.centerX_le j u))
    (fun j u => P.family_centerZ_local j u (T.y - T.slope * T.x) (K * T.width) (G.centerZ_le j u)) s hs hderiv
  change w*‖deriv (fun x => P.boundedSelectedTopSum alt hAlt s coeff x y) z.1‖ ≤ _ at hb
  have hbudget : w*‖deriv (fun x => P.boundedSelectedTopSum alt hAlt s coeff x y) z.1‖ ≤
      P.crossDerivativeConstant D/r := by
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    unfold crossDerivativeConstant
    ring
  have hinv : w⁻¹ ≤ (T.weight K (D:ℝ) z)^8 := T.inverse_polynomial_le_weight K hK D z
  calc
    _ = w⁻¹*(w*‖deriv (fun x => P.boundedSelectedTopSum alt hAlt s coeff x y) z.1‖) := by
      rw [← mul_assoc,inv_mul_cancel₀ hw.ne',one_mul]
    _ ≤ w⁻¹*(P.crossDerivativeConstant D/r) :=
      mul_le_mul_of_nonneg_left hbudget (inv_nonneg.mpr hw.le)
    _ ≤ (T.weight K (D:ℝ) z)^8*(P.crossDerivativeConstant D/r) :=
      mul_le_mul_of_nonneg_right hinv (by have := P.constant_pos; unfold crossDerivativeConstant; positivity)
    _ = _ := mul_comm _ _

theorem source_bounded_coefficient_derivative_of_supported (p : ℝ) (D : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type) [Fintype κ] [∀ j, Fintype (ι j)]
        (P : SourceLatticePacket N κ ι), P.constant ≤ L^p →
      ∀ (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 0 < K → SourceSupportedLatticeTopGeometry P T K D →
      ∀ (coeff : ∀ j, ι j → EuclideanSpace ℂ κ),
        (∀ j u, ‖coeff j u‖ ≤ P.constant*Real.pi^2) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ z : ℝ × ℝ,
      ‖deriv (fun x => planarPacketInterval (coeff)
        (fun j u k t y => (P.withProfile alt hAlt).raw 0 j u k t y) lower upper x (z.2-T.slope*z.1)) z.1‖ ≤
          (L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 := by
  let C : ℝ := Real.pi^2*(4*((16^(8*D+1)*16^(8*D+1))*(4*Real.pi)^2))
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro L hL N κ ι _ _ P hP alt hAlt T K hK G coeff hcoeff lower upper hlu r hr hs z
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hCL : C ≤ L := (le_max_right _ _).trans hL
  have hconst : P.crossDerivativeConstant D ≤ L^(2*p+3) := by
    have hsq := pow_le_pow_left₀ P.constant_pos.le hP 2
    calc
      _ = C*P.constant^2 := by unfold crossDerivativeConstant; dsimp [C]; ring
      _ ≤ L*(L^p)^2 := mul_le_mul hCL hsq (sq_nonneg _) hLpos.le
      _ = L^(2*p+1) := by
        rw [← Real.rpow_mul_natCast hLpos.le]
        calc
          _ = L^(1+p*2) := by rw [Real.rpow_add hLpos,Real.rpow_one]; norm_num
          _ = _ := by congr 1; ring
      _ ≤ L^(2*p+3) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  let selected := Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper)
  have hselected (j : Fin N) (hj : j ∈ selected) : r ≤ P.length j := by
    have hj' := (Finset.mem_filter.mp hj).2
    exact hs j hj'.1 hj'.2
  have hb := P.boundedSelectedTopSum_horizontal_bound_of_supported alt hAlt T hK G coeff hcoeff selected r hr hselected z
  have heq : (fun x => planarPacketInterval (coeff)
      (fun j u k t y => (P.withProfile alt hAlt).raw 0 j u k t y) lower upper x (z.2-T.slope*z.1)) =
      fun x => P.boundedSelectedTopSum alt hAlt selected coeff x (z.2-T.slope*z.1) := by
    funext x
    exact planarPacketInterval_eq_selected (coeff) (fun j u k t => (P.withProfile alt hAlt).raw 0 j u k t) lower upper hlu x _
  rw [heq]
  exact hb.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hconst hr.le)
    (by positivity))


end LipschitzHilbert.SourceLatticePacket

namespace LipschitzHilbert.SourceLabeledLattice

theorem source_selector_top_derivative_of_supported (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 0 < K → SourceSupportedLabeledTopGeometry P T K D →
      ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
        (∀ j l k, Measurable (selector j l k)) →
        (∀ j l k s, ‖selector j l k s‖ ≤ 1) →
      ∀ (v : ℝ×ℝ → ℝ), Measurable v →
      ∀ (test : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ z : ℝ×ℝ,
      ‖deriv (fun x => (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient T.slope selector v test) 0 lower upper
        x (z.2-T.slope*z.1)) z.1‖ ≤
          (L^(2*p+4)/r)*(T.weight K (D:ℝ) z)^8 := by
  classical
  obtain ⟨L1,hL1,hderivative⟩ := SourceLatticePacket.source_bounded_coefficient_derivative_of_supported p D
  refine ⟨max L1 B,hL1.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G selector hs hs1 v hv
    test htest htest1 lower upper hlu r hr hlength z
  have hLpos : 0 < L := zero_lt_one.trans_le (hL1.trans ((le_max_left _ _).trans hLL))
  have hBL : (B:ℝ) ≤ L := (le_max_right _ _).trans hLL
  let Q := P.withProfile alt hAlt
  let coeff := P.physicalMultiplierCoefficient T.slope selector v test
  let y := z.2-T.slope*z.1
  let F := fun b : Fin B =>
    ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
      (P.slottedAlt_bound hcard alt hAlt b)).rawInterval
      (fun j a => coeff j a.1.1 a.1.2) 0 lower upper
  have hdiff (b : Fin B) : DifferentiableAt ℝ (fun x => F b x y) z.1 :=
    lattice_rawInterval_horizontal_differentiable
      ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b))
      (fun j a => coeff j a.1.1 a.1.2) 0 lower upper hlu z.1 y
  have hsum : (fun x => Q.rawInterval coeff 0 lower upper x y) =
      fun x => ∑ b : Fin B, F b x y := by
    funext x
    have h := (P.withProfile alt hAlt).sum_slotted_rawInterval hcard coeff 0 lower upper x y
    simp only [P.withProfile_slotted hcard alt hAlt] at h
    convert h.symm using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have hdiffsum : deriv (fun x => Q.rawInterval coeff 0 lower upper x y) z.1 =
      ∑ b : Fin B, deriv (fun x => F b x y) z.1 := by
    rw [hsum]
    exact deriv_fun_sum (fun b _ => hdiff b)
  have hb (b : Fin B) : ‖deriv (fun x => F b x y) z.1‖ ≤
      (L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 := by
    have hR : (P.slotted hcard b).constant ≤ L^p := by
      simpa only [P.slotted_constant hcard] using hP
    have hc (j : Fin N) (a : P.SlotItem hcard b j) :
        ‖coeff j a.1.1 a.1.2‖ ≤ (P.slotted hcard b).constant*Real.pi^2 :=
      P.physicalMultiplierCoefficient_norm T.slope selector hs hs1 v hv test htest htest1
        j a.1.1 a.1.2
    exact hderivative L ((le_max_left _ _).trans hLL) N κ (P.SlotItem hcard b)
      (P.slotted hcard b) hR (P.slottedAlt hcard alt b) (P.slottedAlt_bound hcard alt hAlt b)
      T K hK (P.slotted_supportedTopGeometry hcard G b) (fun j a => coeff j a.1.1 a.1.2) hc
      lower upper hlu r hr hlength z
  change ‖deriv (fun x => Q.rawInterval coeff 0 lower upper x y) z.1‖ ≤ _
  rw [hdiffsum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b : Fin B, (L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 :=
      Finset.sum_le_sum (fun b _ => hb b)
    _ = ((B:ℝ)*L^(2*p+3)/r)*(T.weight K (D:ℝ) z)^8 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hpower : (B:ℝ)*L^(2*p+3) ≤ L^(2*p+4) := by
        calc
          _ ≤ L*L^(2*p+3) := mul_le_mul_of_nonneg_right hBL (Real.rpow_nonneg hLpos.le _)
          _ = L^(2*p+4) := by
            calc
              _ = L^(1:ℝ)*L^(2*p+3) := by rw [Real.rpow_one]
              _ = L^(1+(2*p+3)) := (Real.rpow_add hLpos _ _).symm
              _ = _ := by congr 1; ring
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpower hr.le) (by positivity)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedSelectorIntervalMotion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier and top-mask motion for the original smooth-selector
coefficients. The snapshot concentration premise remains the original
one; the horizontal derivative is proved from the original packets. -/

noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.SourceLabeledLattice
open PhaseCombinatorics

theorem source_selector_interval_motion_of_supported (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceSupportedLabeledTopGeometry P T K D →
      ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
        (∀ j l k, Measurable (selector j l k)) →
        (∀ j l k s, ‖selector j l k s‖ ≤ 1) →
      ∀ (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ x0 x1 y0 y1 A : ℝ, |x1-x0| ≤ T.length → |y1-y0| ≤ T.width →
      let F := (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient T.slope selector v g) 0 lower upper
      (∀ y, |y-y0| ≤ T.width → ‖F x0 y‖ + T.width *
        ‖covariantSignal P.frequency (fun k t => F x0 t k) y‖ ≤
          A*(T.weight K (D:ℝ) (x0, y0+T.slope*x0))^8) →
      ‖F x1 y1 - diagonalModulation P.frequency (F x0 y0) (y1-y0)‖ ≤
        ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x1-x0| +
          (A/T.width)*|y1-y0|) * (T.weight K (D:ℝ) (x0, y0+T.slope*x0))^8 := by
  obtain ⟨L0,hL0,hB,hderiv⟩ := source_selector_top_derivative_of_supported p D B
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G selector hselector hselector1 v hv g hg hg1
    lower upper hlu r hr hs x0 x1 y0 y1 A hx hy
  dsimp only
  intro hconcentration
  let Q := P.withProfile alt hAlt
  let coeff := P.physicalMultiplierCoefficient T.slope selector v g
  let F := Q.rawInterval coeff 0 lower upper
  let w0 := (T.weight K (D:ℝ) (x0, y0+T.slope*x0))^8
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hLp : 0 < L := zero_lt_one.trans_le (hL0.trans hLL)
  have hDx (x : ℝ) (hxx : x ∈ uIcc x0 x1) :
      ‖deriv (fun t => F t y1) x‖ ≤ (L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*w0 := by
    have hxlocal : |x-x0| ≤ T.length := (abs_sub_left_of_mem_uIcc hxx).trans hx
    have hw := T.weight_slope_coordinates_local hK (Nat.cast_nonneg D) hxlocal hy
    have hw8 := pow_le_pow_left₀ (T.weight_pos hK0 (D:ℝ) _).le hw 8
    have hexp : (Real.exp (2*(D:ℝ)))^8 = Real.exp (16*(D:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, hexp] at hw8
    have hd := hderiv L hLL N κ Label Item P hcard hP alt hAlt T K hK0 G
      selector hselector hselector1 v hv g hg hg1 lower upper hlu r hr hs (x, y1+T.slope*x)
    have heq : y1+T.slope*x-T.slope*x = y1 := by ring
    simp only [heq] at hd
    change ‖deriv (fun t => F t y1) x‖ ≤ _ at hd
    exact hd.trans (by
      convert mul_le_mul_of_nonneg_left hw8 (div_nonneg (Real.rpow_nonneg hLp.le _) hr.le) using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  have hDy (y : ℝ) (hyy : y ∈ uIcc y0 y1) :
      ‖covariantSignal P.frequency (fun k t => F x0 t k) y‖ ≤ (A/T.width)*w0 := by
    have h := hconcentration y ((abs_sub_left_of_mem_uIcc hyy).trans hy)
    have hb : T.width * ‖covariantSignal P.frequency (fun k t => F x0 t k) y‖ ≤ A*w0 := by
      change ‖F x0 y‖ + _ ≤ _ at h
      linarith [norm_nonneg (F x0 y)]
    calc
      _ ≤ (A*w0)/T.width := (le_div_iff₀ T.width_pos).mpr (by simpa only [mul_comm] using hb)
      _ = _ := by ring
  have h := covariant_line_motion F P.frequency x0 x1 y0 y1
    ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*w0) ((A/T.width)*w0)
    (fun x _ => Q.rawInterval_horizontal_differentiable coeff 0 lower upper hlu x y1)
    (fun y _ k => Q.rawInterval_vertical_differentiable coeff 0 lower upper x0 y k)
    hDx hDy
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [w0]
  ring


theorem source_selector_masked_interval_motion_of_supported (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceSupportedLabeledTopGeometry P T K D →
      ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
        (∀ j l k, Measurable (selector j l k)) →
        (∀ j l k s, ‖selector j l k s‖ ≤ 1) →
      ∀ (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ x₀ x₁ y₀ y₁ A maskExponent : ℝ,
      |x₁-x₀| ≤ T.length → |y₁-y₀| ≤ T.width →
      let F := (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient T.slope selector v g) 0 lower upper
      let w₀ := (T.weight K (D:ℝ) (x₀,y₀+T.slope*x₀))^8
      (∀ y, |y-y₀| ≤ T.width → ‖F x₀ y‖+T.width*
        ‖covariantSignal P.frequency (fun k t => F x₀ t k) y‖ ≤ A*w₀) →
      ‖T.mask L maskExponent (x₁,y₁+T.slope*x₁) • F x₁ y₁-
        diagonalModulation P.frequency
          (T.mask L maskExponent (x₀,y₀+T.slope*x₀) • F x₀ y₀) (y₁-y₀)‖ ≤
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|x₁-x₀|/T.length+|y₁-y₀|/T.width)*A)*w₀ := by
  obtain ⟨L0,hL0,hB,hmotion⟩ := source_selector_interval_motion_of_supported p D B
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G selector hselector hselector1 v hv g hg hg1
    lower upper hlu r hr hs x₀ x₁ y₀ y₁ A maskExponent hx hy
  dsimp only
  intro hc
  let F := (P.withProfile alt hAlt).rawInterval
    (P.physicalMultiplierCoefficient T.slope selector v g) 0 lower upper
  let w₀ := (T.weight K (D:ℝ) (x₀,y₀+T.slope*x₀))^8
  have hL : 0 < L := zero_lt_one.trans_le (hL0.trans hLL)
  have hm := hmotion L hLL N κ Label Item P hcard hP alt hAlt T K hK G
    selector hselector hselector1 v hv g hg hg1 lower upper hlu r hr hs x₀ x₁ y₀ y₁ A hx hy hc
  have hbase : ‖F x₀ y₀‖ ≤ A*w₀ := by
    have hb := hc y₀ (by simp [T.width_pos.le])
    have hn := mul_nonneg T.width_pos.le
      (norm_nonneg (covariantSignal P.frequency (fun k t => F x₀ t k) y₀))
    change ‖F x₀ y₀‖+_ ≤ A*w₀ at hb
    linarith
  have hq : |T.mask L maskExponent (x₁,y₁+T.slope*x₁)| ≤ 1 := by
    change |topSincMask L maskExponent _ _| ≤ 1
    rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
    exact topSincMask_le_one _ _ _ _
  have hlength := T.length_pos
  have hwidth := T.width_pos
  have h := masked_isometry_motion
    (diagonalModulationRealIsometry P.frequency (y₁-y₀))
    (F x₁ y₁) (F x₀ y₀)
    (T.mask L maskExponent (x₁,y₁+T.slope*x₁))
    (T.mask L maskExponent (x₀,y₀+T.slope*x₀)) (A*w₀)
    (((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|)*w₀)
    ((2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width))
    hq (by positivity) (T.mask_slope_coordinates_motion L maskExponent x₀ x₁ y₀ y₁ hL)
    hbase hm
  have heq :
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|)*w₀+
        ((2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width))*(A*w₀) =
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width)*A)*w₀ := by
    ring
  rw [heq] at h
  simpa only [diagonalModulationRealIsometry_apply] using h


theorem source_selector_predictable_masked_interval_motion_of_supported (p : ℝ) (D Bslots : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ Bslots), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceSupportedLabeledTopGeometry P T K D →
      ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
        (∀ j l k, Measurable (selector j l k)) →
        (∀ j l k s, ‖selector j l k s‖ ≤ 1) →
      ∀ (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ),
        Measurable test → (∀ z, ‖test z‖ ≤ 1) →
      ∀ (grid : AngularGrid) (w Bscale : ℝ) (hw : 0 < w), 0 < Bscale →
      (∀ j, grid.eligible (grid.rootWidth/Bscale^2) (w/P.length j) 0) →
      ∀ (start lower upper : ℕ), lower ≤ upper →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper →
        start ≤ grid.lastEligible (grid.rootWidth/Bscale^2) (w/P.length j)
          (div_pos hw (P.length_pos j))) →
      ∀ (sR center b A maskExponent Fbound : ℝ) (z : ℝ × ℝ),
      0 ≤ Fbound → (∀ k, |P.frequency k| ≤ Fbound) →
      |b| ≤ T.length → |(sR-T.slope)*b| ≤ T.width →
      let coeff := P.physicalMultiplierCoefficient T.slope selector v test
      let Q := P.withProfile alt hAlt
      let F := Q.rawInterval coeff 0 lower upper
      let S := fun zz : ℝ × ℝ => Q.rawInterval
        (fun j l u => T.mask L maskExponent zz • coeff j l u) 0 lower upper
        zz.1 (zz.2-T.slope*zz.1)
      let h₀ := T.weight K (D:ℝ) z
      let r := Bscale^2*w/grid.width start
      (∀ y, |y-(z.2-T.slope*z.1)| ≤ T.width →
        ‖F z.1 y‖+T.width*‖covariantSignal P.frequency (fun k t => F z.1 t k) y‖ ≤ A*h₀^8) →
      ‖S z‖ ≤ A*h₀^8 ∧
      ‖S (SlopeBox.lineShift sR b z)-
        diagonalModulation P.frequency (S z) ((sR-center)*b)‖ ≤
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|b|+(A/T.width)*|(sR-T.slope)*b|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|b|/T.length+|(sR-T.slope)*b|/T.width)*A+
        Fbound*A*|T.slope-center| * |b|)*h₀^8 := by
  obtain ⟨L0,hL0,hB,hmotion⟩ := source_selector_masked_interval_motion_of_supported p D Bslots
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK hgeom
    selector hselector hselector1 v hv test htest htest1 grid w Bscale hw hBscale hzero start lower upper hlu
    hactive sR center b A maskExponent Fbound z hFbound hfreq hbx hby
  dsimp only
  intro hc
  let coeff := P.physicalMultiplierCoefficient T.slope selector v test
  let Q := P.withProfile alt hAlt
  let F := Q.rawInterval coeff 0 lower upper
  let S := fun zz : ℝ × ℝ => Q.rawInterval
    (fun j l u => T.mask L maskExponent zz • coeff j l u) 0 lower upper
    zz.1 (zz.2-T.slope*zz.1)
  let h₀ := T.weight K (D:ℝ) z
  let r := Bscale^2*w/grid.width start
  let y₀ := z.2-T.slope*z.1
  let y₁ := (SlopeBox.lineShift sR b z).2-T.slope*(SlopeBox.lineShift sR b z).1
  have hr : 0 < r := div_pos (mul_pos (sq_pos_of_pos hBscale) hw) (grid.width_pos start)
  have hlength (j : Fin N) (hjl : lower ≤ j.val) (hju : j.val < upper) : r ≤ P.length j :=
    P.source_stopping_length_lower grid hw hBscale hzero start j (hactive j hjl hju)
  have hxy₀ : (z.1,y₀+T.slope*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp [y₀]
      ring
  have hxy₁ : ((SlopeBox.lineShift sR b z).1,
      y₁+T.slope*(SlopeBox.lineShift sR b z).1) = SlopeBox.lineShift sR b z := by
    apply Prod.ext
    · rfl
    · dsimp [y₁]
      ring
  have hx : (SlopeBox.lineShift sR b z).1-z.1 = b := by simp [SlopeBox.lineShift]
  have hy : y₁-y₀ = (sR-T.slope)*b := by dsimp [y₁,y₀,SlopeBox.lineShift]; ring
  have hc' : ∀ y, |y-y₀| ≤ T.width →
      ‖F z.1 y‖+T.width*‖covariantSignal P.frequency (fun k t => F z.1 t k) y‖ ≤
        A*(T.weight K (D:ℝ) (z.1,y₀+T.slope*z.1))^8 := by
    simpa only [hxy₀] using hc
  have hm := hmotion L hLL N κ Label Item P hcard hP alt hAlt T K hK hgeom
    selector hselector hselector1 v hv test htest htest1 lower upper hlu r hr hlength
    z.1 (SlopeBox.lineShift sR b z).1 y₀ y₁ A maskExponent
    (by simpa only [hx] using hbx) (by simpa only [hy] using hby) hc'
  have hS (zz : ℝ × ℝ) : S zz = T.mask L maskExponent zz • F zz.1 (zz.2-T.slope*zz.1) :=
    Q.rawInterval_coeff_smul coeff (T.mask L maskExponent zz) 0 lower upper _ _
  have hbase : ‖F z.1 y₀‖ ≤ A*h₀^8 := by
    have h := hc y₀ (by simp [y₀,T.width_pos.le])
    have hnonneg := mul_nonneg T.width_pos.le
      (norm_nonneg (covariantSignal P.frequency (fun k t => F z.1 t k) y₀))
    change ‖F z.1 y₀‖+_ ≤ A*h₀^8 at h
    linarith
  have hmask : |T.mask L maskExponent z| ≤ 1 := by
    change |topSincMask L maskExponent _ _| ≤ 1
    rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
    exact topSincMask_le_one _ _ _ _
  have hSbase : ‖S z‖ ≤ A*h₀^8 := by
    rw [hS, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hmask (norm_nonneg _)).trans
      (by simpa only [one_mul] using hbase)
  have htop : ‖S (SlopeBox.lineShift sR b z)-
      diagonalModulation P.frequency (S z) ((sR-T.slope)*b)‖ ≤
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|b|+(A/T.width)*|(sR-T.slope)*b|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|b|/T.length+|(sR-T.slope)*b|/T.width)*A)*h₀^8 := by
    rw [hS, hS]
    simpa only [hx,hy,hxy₀,hxy₁] using hm
  refine ⟨hSbase,?_⟩
  have h := carrier_replacement_motion P.frequency (S z) (S (SlopeBox.lineShift sR b z))
    Fbound (A*h₀^8)
    (((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|b|+(A/T.width)*|(sR-T.slope)*b|+
      (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
        (|b|/T.length+|(sR-T.slope)*b|/T.width)*A)*h₀^8)
    hFbound hfreq hSbase sR T.slope center b htop
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeMotion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact source analytic family inherits motion from its endpoint
weights and original interval packet sums. Different endpoint coefficients
allow the common top mask to be evaluated at each spatial point. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem sourcePacketAmplitude_single_top_motion (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) M) (a : ℝ) (z0 z1 : X)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff0 coeff1 : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (x0 y0 x1 y1 A D B ε : ℝ)
    (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff0 jet l u x0 y0‖ ≤ B)
    (hmotion : ∀ l u, l ≤ u → u ≤ N →
      (∀ j : Fin N, l ≤ j.val → j.val < u → start ≤ stop j) →
      ‖P.rawInterval coeff1 jet l u x1 y1-U (P.rawInterval coeff0 jet l u x0 y0)‖ ≤ ε) :
    let n := fun z j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) z
    let m := fun z j => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (g.index (j+1) (slope top)) z
    let w0 := segmentWeight (n z0) (boundaryLog (n z0) (m z0)) phase a start
    let w1 := segmentWeight (n z1) (boundaryLog (n z1) (m z1)) phase a start
    ‖w1 M‖+(∑ j ∈ Finset.Ico start M, ‖w1 (j+1)-w1 j‖) ≤ A →
    ‖w1 M-w0 M‖+(∑ j ∈ Finset.Ico start M,
      ‖(w1 (j+1)-w0 (j+1))-(w1 j-w0 j)‖) ≤ D →
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
        (fun _ : Fin N => top) stop (fun j => P.rawBand coeff1 jet j x1 y1)
        phase a z1 start (g.index start (slope top))-
      U (g.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
        (fun _ : Fin N => top) stop (fun j => P.rawBand coeff0 jet j x0 y0)
        phase a z0 start (g.index start (slope top)))‖ ≤ A*ε+D*B := by
  dsimp only
  intro hweight hweightdiff
  rw [g.sourcePacketAmplitude_single_top tops slope precision cutoff weight hp hw hK gap
    phase M top htop he a z1 stop hmax]
  rw [g.sourcePacketAmplitude_single_top tops slope precision cutoff weight hp hw hK gap
    phase M top htop he a z0 stop hmax]
  exact P.stopping_amplitude_motion coeff0 coeff1 jet stop hstop start M hstart hmax
    _ _ x0 y0 x1 y1 A D B ε U hB hε hweight hweightdiff hinterval hmotion

/-- Summing the actual single-top motion bounds charges the snapshot
mass of the node, with no loss from the number of eligible tops. -/
theorem sourcePacketAmplitude_node_motion {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (K : ℕ) (gap : ℕ → ℝ) (bands : Finset σ) (stop : ι → σ → ℕ)
    (value0 value1 : ι → σ → E)
    (he : ∀ t ∈ tops, ∀ j ∈ bands, g.eligible cutoff (precision t) (stop t j))
    (phase : ℕ → ℂ) (a : ℝ) (z0 z1 : X) (level : ℕ) (cell : ℤ)
    (U : E →ₗᵢ[ℂ] E) (A C : ℝ) (hA : 0 ≤ A)
    (hw : ∀ t ∈ g.cellTops tops slope precision cutoff level cell, 0 ≤ weight t z0)
    (hC : ∀ t ∈ g.cellTops tops slope precision cutoff level cell, weight t z0 ≤ C)
    (hmotion : ∀ t ∈ g.cellTops tops slope precision cutoff level cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
          (fun _ => t) (stop t) (value1 t) phase a z1 level (g.index level (slope t))-
        U (g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
          (fun _ => t) (stop t) (value0 t) phase a z0 level (g.index level (slope t)))‖ ≤
        A*(weight t z0)^4) :
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap (tops ×ˢ bands)
        Prod.fst (fun p => stop p.1 p.2) (fun p => value1 p.1 p.2) phase a z1 level cell-
      U (g.sourcePacketAmplitude tops slope precision cutoff weight K gap (tops ×ˢ bands)
        Prod.fst (fun p => stop p.1 p.2) (fun p => value0 p.1 p.2) phase a z0 level cell)‖ ≤
      (A*C^3)*g.mass tops slope precision cutoff weight level cell z0 := by
  rw [g.sourcePacketAmplitude_top_fibers tops slope precision cutoff weight hp K gap
    bands stop value1 he phase a z1 level cell,
    g.sourcePacketAmplitude_top_fibers tops slope precision cutoff weight hp K gap
    bands stop value0 he phase a z0 level cell, map_sum, ← Finset.sum_sub_distrib]
  exact g.node_amplitude_fourth_envelope tops slope precision cutoff weight _
    level cell z0 A C hA hw hC hmotion

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularPathLossMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two logarithmic losses in an actual endpoint increment inherit
relative motion from their concrete child, parent, and boundary top sets. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

/-- Both P_i=log(n_i/n_(i+1)) and R_i=log(m_i/n_(i+1)) have relative
motion at the source averaging scale. The second statement allows the
boundary ancestor to begin before the current block. -/
theorem source_path_loss_motion {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hKw : 0 < Kw) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ)
    (h i : ℕ) (hhi : h ≤ i) (hgap0 : 0 ≤ gap i) (hgap : gap i ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (i+1))
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (a : ℝ) (ha : |a| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    let weight := fun t x => (T t).weight Kw D x
    let n := fun k x => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight k (g.index k (T top).slope) x
    let m := fun x => g.sourceBoundaryMass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight Kb gap i (g.index (i+1) (T top).slope) x
    let z' := SlopeBox.lineShift sR a z
    let epsilon := Real.exp (2*((5*D/Kw)/Real.sqrt (g.branching:ℝ)))-1
    |Real.log (n i z'/n (i+1) z')-Real.log (n i z/n (i+1) z)| ≤
      epsilon*Real.log (n i z/n (i+1) z) ∧
    |Real.log (m z'/n (i+1) z')-Real.log (m z/n (i+1) z)| ≤
      epsilon*Real.log (m z/n (i+1) z) := by
  classical
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let childSet := g.cellTops tops slope precision cutoff (i+1) (g.index (i+1) (T top).slope)
  let parentSet := g.cellTops tops slope precision cutoff i (g.index i (T top).slope)
  let boundarySet := g.boundaryTops tops slope precision cutoff (i+1-Kb) i (gap i) (T top).slope
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hchildSet : childSet.Nonempty := by
    refine ⟨top,?_⟩
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩
  have hparent : parentSet ⊆ boundarySet :=
    g.parent_subset_boundary tops slope precision cutoff (i+1-Kb) i (gap i) (T top).slope
  have hchildParent : childSet ⊆ parentSet :=
    g.cellTops_subset_ancestor tops slope precision cutoff hp (Nat.le_succ i) (T top).slope
  have hP := g.source_relative_loss_motion tops T w B Kw D hw hB hKw hD hwidth
    (i+1-Kb) h i hhi (gap i) hgap0 hgap (T top).slope sR hs child hchild hblock
    parentSet childSet hchildParent hchildSet hparent a ha z
  have hR := g.source_relative_loss_motion tops T w B Kw D hw hB hKw hD hwidth
    (i+1-Kb) h i hhi (gap i) hgap0 hgap (T top).slope sR hs child hchild hblock
    boundarySet childSet (hchildParent.trans hparent) hchildSet (Finset.Subset.refl _) a ha z
  constructor
  · simpa only [parentSet, childSet, mass] using hP
  · have hboundary (x : ℝ × ℝ) :
        g.sourceBoundaryMass tops slope precision cutoff weight Kb gap i
          (g.index (i+1) (T top).slope) x = ∑ t ∈ boundarySet, weight t x := by
      rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hKb gap]
      rfl
    dsimp only [slope, precision, cutoff, weight] at hboundary
    simpa only [hboundary, childSet, mass] using hR

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMovingWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving endpoint weights for the actual source masses. Every motion
hypothesis is derived from the physical top weights and angular locality. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem source_moving_weight_variation {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hKw : 0 < Kw) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ)
    (h start M : ℕ) (hstart : start ≤ M) (hbase : h ≤ start)
    (hgap : ∀ j, h ≤ j → j ≤ M → 0 ≤ gap j ∧ gap j ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) M)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (phase : ℕ → ℂ) (a Z C : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hZ : 0 ≤ Z) (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    (hC : 1 ≤ C) (htC : (T top).weight Kw D z ≤ C) :
    let weight := fun t x => (T t).weight Kw D x
    let n := fun x k => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight k (g.index k (T top).slope) x
    let m := fun x k => g.sourceBoundaryMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap k
      (g.index (k+1) (T top).slope) x
    let z' := SlopeBox.lineShift sR b z
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    let ε := Real.exp (2*δ)-1
    ‖segmentWeight (n z') (boundaryLog (n z') (m z')) phase a start M-
        segmentWeight (n z) (boundaryLog (n z) (m z)) phase a start M‖ +
      (∑ j ∈ Finset.Ico start M,
        ‖(segmentWeight (n z') (boundaryLog (n z') (m z')) phase a start (j+1)-
            segmentWeight (n z) (boundaryLog (n z) (m z)) phase a start (j+1))-
          (segmentWeight (n z') (boundaryLog (n z') (m z')) phase a start j-
            segmentWeight (n z) (boundaryLog (n z) (m z)) phase a start j)‖) ≤
      Real.exp (a*δ)*(δ+ε)*C^4*
        (1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2*
        (weight top z)^(-(4:ℝ)) := by
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let n := fun x k => g.mass tops slope precision cutoff weight k (g.index k (T top).slope) x
  let m := fun x k => g.sourceBoundaryMass tops slope precision cutoff weight Kb gap k
    (g.index (k+1) (T top).slope) x
  let z' := SlopeBox.lineShift sR b z
  let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
  let ε := Real.exp (2*δ)-1
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hweight (t : ι) (x : ℝ × ℝ) : 0 < weight t x := (T t).weight_pos hKw D x
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hmasspos (x : ℝ × ℝ) (j : ℕ) (hj : j ≤ M) : 0 < n x j :=
    g.path_mass_pos tops slope precision cutoff weight hweight j top htop
      (g.eligible_of_le (hp top htop) hj he) x
  have hlower (j : ℕ) (hj : j ≤ M) : weight top z ≤ n z j := by
    apply Finset.single_le_sum (fun t _ => (hweight t z).le)
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,g.eligible_of_le (hp top htop) hj he⟩
  have hmono (x : ℝ × ℝ) : Antitone (n x) :=
    g.path_mass_antitone tops slope precision cutoff weight hp (fun t x => (hweight t x).le) top x
  have hmbounds (x : ℝ × ℝ) (j : ℕ) :
      n x (j+1) ≤ m x j ∧ m x j ≤ n x (j+1-Kb) :=
    g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun t x => (hweight t x).le) hKb gap j (T top).slope x
  have hR0 (x : ℝ × ℝ) (j : ℕ) (hj : j < M) : 0 ≤ boundaryLog (n x) (m x) j :=
    boundaryLog_nonnegative (n x) (m x) j (hmasspos x (j+1) (by omega)) (hmbounds x j).1
  have hR (j : ℕ) (hj : j < M) : boundaryLog (n z) (m z) j ≤
      Real.log (n z (j+1-Kb)/n z (j+1)) :=
    boundaryLog_le_root_ratio (n z) (m z) j Kb (hmasspos z (j+1) (by omega))
      ((hmasspos z (j+1) (by omega)).trans_le (hmbounds z j).1) (hmbounds z j).2
  have hmass (j : ℕ) (hjs : start ≤ j) (hjM : j ≤ M) :
      |Real.log (n z' j)-Real.log (n z j)| ≤ δ := by
    let A := g.cellTops tops slope precision cutoff j (g.index j (T top).slope)
    have hA : A.Nonempty := ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,g.eligible_of_le (hp top htop) hjM he⟩⟩
    exact g.boundary_submass_source_motion tops T w B Kw D hw hB hKw hD hwidth
      0 h j (hbase.trans hjs) (gap j) (hgap j (hbase.trans hjs) hjM).1
      (hgap j (hbase.trans hjs) hjM).2 (T top).slope sR hs child hchild hblock A hA
      (g.parent_subset_boundary tops slope precision cutoff 0 j (gap j) (T top).slope) b hb z
  have hloss (j : ℕ) (hj : j ∈ Finset.Ico start M) :=
    g.source_path_loss_motion tops T w B Kw D hw hB hKw hD hwidth hKb gap h j
      (hbase.trans (Finset.mem_Ico.mp hj).1)
      (hgap j (hbase.trans (Finset.mem_Ico.mp hj).1) (Nat.le_of_lt (Finset.mem_Ico.mp hj).2)).1
      (hgap j (hbase.trans (Finset.mem_Ico.mp hj).1) (Nat.le_of_lt (Finset.mem_Ico.mp hj).2)).2
      top htop (g.eligible_of_le (hp top htop)
        (by have := (Finset.mem_Ico.mp hj).2; omega) he) sR hs child hchild hblock b hb z
  have hv := moving_segmentWeight_variation (n z) (n z') (boundaryLog (n z) (m z))
    (boundaryLog (n z') (m z')) phase start M Kb hstart a Z δ ε (weight top z)
    ha0 hZ hδ hε (hweight top z) hlower (hmasspos z') ((hmono z).antitoneOn _)
    (hR0 z) (hR0 z') hR hz0 hz hmass (fun j hj => (hloss j hj).1)
    (fun j hj => (hloss j hj).2)
  have htotal : n z 0 ≤ ∑ t ∈ tops, weight t z :=
    g.mass_le_total tops slope precision cutoff weight (fun t x => (hweight t x).le) 0 _ z
  have hS : weight top z ≤ ∑ t ∈ tops, weight t z := (hlower 0 (Nat.zero_le M)).trans htotal
  have hQ : 0 ≤ a+Z*Kb := by positivity
  have hV : 0 ≤ (a+Z*Kb)*Real.log (n z 0/n z M) := by
    apply mul_nonneg hQ
    exact Real.log_nonneg ((one_le_div (hmasspos z M le_rfl)).mpr (hmono z (Nat.zero_le M)))
  have hVQ : (a+Z*Kb)*Real.log (n z 0/n z M) ≤
      (a+Z*Kb)*Real.log ((∑ t ∈ tops, weight t z)/weight top z) := by
    apply mul_le_mul_of_nonneg_left _ hQ
    apply Real.log_le_log (div_pos (hmasspos z 0 (Nat.zero_le M)) (hmasspos z M le_rfl))
    exact (div_le_div_of_nonneg_right htotal (hmasspos z M le_rfl).le).trans
      (div_le_div_of_nonneg_left ((hweight top z).le.trans hS) (hweight top z) (hlower M le_rfl))
  exact moving_weight_budget_absorption (hweight top z) hS hC htC hQ ha0 ha1
    hδ hε hV hVQ hv

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictableAmplitudeMotion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source's predictable amplitude estimate before absorbing the fixed
polynomial factors into the branching scale. The moving weights below are
the actual angular masses, including all shifted-boundary losses. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

/-- The per-top estimate retains four powers of the snapshot weight.
Only the unweighted interval estimate is an input; the weight motion is
derived from the physical geometry. -/
theorem source_single_top_predictable_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ)
    (h start M : ℕ) (hstart : start ≤ M) (hbase : h ≤ start)
    (hgap : ∀ j, h ≤ j → j ≤ M → 0 ≤ gap j ∧ gap j ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) M)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (phase : ℕ → ℂ) (a Z C : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    (hC : 1 ≤ C) (htC : (T top).weight Kw D z ≤ C)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff0 coeff1 : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (hmax : ∀ j, stop j ≤ M) (x0 y0 x1 y1 A E : ℝ)
    (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hinterval : ∀ l u, l ≤ u → u ≤ N →
      ‖P.rawInterval coeff0 jet l u x0 y0‖ ≤ A*((T top).weight Kw D z)^8)
    (hmotion : ∀ l u, l ≤ u → u ≤ N →
      (∀ j : Fin N, l ≤ j.val → j.val < u → start ≤ stop j) →
      ‖P.rawInterval coeff1 jet l u x1 y1-U (P.rawInterval coeff0 jet l u x0 y0)‖ ≤
        E*((T top).weight Kw D z)^8) :
    let weight := fun t x => (T t).weight Kw D x
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
    ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap Finset.univ (fun _ : Fin N => top) stop
        (fun j => P.rawBand coeff1 jet j x1 y1) phase a (SlopeBox.lineShift sR b z)
        start (g.index start (T top).slope)-
      U (g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap Finset.univ (fun _ : Fin N => top) stop
        (fun j => P.rawBand coeff0 jet j x0 y0) phase a z
        start (g.index start (T top).slope))‖ ≤
      (V*((1+d)*E+d*A))*((T top).weight Kw D z)^4 := by
  dsimp only
  let weight := fun t x => (T t).weight Kw D x
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let n := fun x j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  let m := fun x j => g.sourceBoundaryMass tops slope precision cutoff weight Kb gap j
    (g.index (j+1) (slope top)) x
  let z' := SlopeBox.lineShift sR b z
  let v0 := segmentWeight (n z) (boundaryLog (n z) (m z)) phase a start
  let v1 := segmentWeight (n z') (boundaryLog (n z') (m z')) phase a start
  let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
  let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
  let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
  let q := weight top z
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hweight (t : ι) (x : ℝ × ℝ) : 0 < weight t x := (T t).weight_pos hKw D x
  have hq : 0 < q := hweight top z
  have hn (j : ℕ) (hj : j ≤ M) : q ≤ n z j := by
    apply Finset.single_le_sum (fun t _ => (hweight t z).le)
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,g.eligible_of_le (hp top htop) hj he⟩
  have hv0 : ‖v0 M‖+(∑ j ∈ Finset.Ico start M, ‖v0 (j+1)-v0 j‖) ≤ V*q^(-(4:ℝ)) :=
    boundary_weight_variation_fourth (n z) (m z) phase start M Kb a q
      (∑ t ∈ tops, weight t z) C Z ha0 ha1 hq hZ hC htC hn
      (g.mass_le_total tops slope precision cutoff weight (fun t x => (hweight t x).le) 0 _ z)
      ((g.path_mass_antitone tops slope precision cutoff weight hp
        (fun t x => (hweight t x).le) top z).antitoneOn _)
      (fun j _ => g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
        (fun t x => (hweight t x).le) hKb gap j (slope top) z) hz0 hz
  have hvd : ‖v1 M-v0 M‖+(∑ j ∈ Finset.Ico start M,
      ‖(v1 (j+1)-v0 (j+1))-(v1 j-v0 j)‖) ≤ (d*V)*q^(-(4:ℝ)) := by
    have hv := g.source_moving_weight_variation tops T w B Kw D hw hB hKw hD hwidth
      hKb gap h start M hstart hbase hgap top htop he sR hs child hchild hblock b hb z
      phase a Z C ha0 ha1 hZ hz0 hz hC htC
    convert hv using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [v0,v1,n,m,z',d,V,δ,q,weight,slope,precision,cutoff]
    ring
  have hv1 : ‖v1 M‖+(∑ j ∈ Finset.Ico start M, ‖v1 (j+1)-v1 j‖) ≤
      ((1+d)*V)*q^(-(4:ℝ)) := by
    calc
      _ ≤ (‖v0 M‖+(∑ j ∈ Finset.Ico start M, ‖v0 (j+1)-v0 j‖))+
          (‖v1 M-v0 M‖+(∑ j ∈ Finset.Ico start M,
            ‖(v1 (j+1)-v0 (j+1))-(v1 j-v0 j)‖)) := endpoint_variation_le_add v0 v1 start M
      _ ≤ V*q^(-(4:ℝ))+(d*V)*q^(-(4:ℝ)) := add_le_add hv0 hvd
      _ = _ := by ring
  have hbnd := g.sourcePacketAmplitude_single_top_motion tops slope precision cutoff weight
    hp hweight hKb gap phase M top htop he a z z' P coeff0 coeff1 jet stop hstop
    start hstart hmax x0 y0 x1 y1 (((1+d)*V)*q^(-(4:ℝ))) ((d*V)*q^(-(4:ℝ)))
    (A*q^8) (E*q^8) U (by positivity) (by positivity) hinterval hmotion hv1 hvd
  have hcancel : q^(-(4:ℝ))*q^8 = q^4 := by
    rw [← Real.rpow_natCast q 8, ← Real.rpow_add hq]
    norm_num
  calc
    _ ≤ (((1+d)*V)*q^(-(4:ℝ)))*(E*q^8)+((d*V)*q^(-(4:ℝ)))*(A*q^8) := hbnd
    _ = (V*((1+d)*E+d*A))*(q^(-(4:ℝ))*q^8) := by ring
    _ = _ := by rw [hcancel]

/-- The complete family of actual packets has motion proportional to
the mass of its angular node, independently of the number of tops. -/
theorem source_node_predictable_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ)
    (h start : ℕ) (hbase : h ≤ start) (M : ι → ℕ)
    (hM : ∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t))
    (hMmax : ∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t)
    (hgap : ∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h)
    (sR : ℝ) (cell : ℤ) (hs : ∀ t ∈ g.cellTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) start cell,
      g.index h (T t).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (phase : ℕ → ℂ) (a Z C : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re)
    (hz : ∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z)
    (hC : 1 ≤ C) (htC : ∀ t ∈ tops, (T t).weight Kw D z ≤ C)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff0 coeff1 : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : ι → Fin N → ℕ)
    (hstop : ∀ t ∈ tops, Antitone (stop t)) (hmax : ∀ t ∈ tops, ∀ j, stop t j ≤ M t)
    (x0 y0 x1 y1 : ι → ℝ) (A E : ℝ)
    (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hinterval : ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
      ‖(P t).rawInterval (coeff0 t) jet l u (x0 t) (y0 t)‖ ≤ A*((T t).weight Kw D z)^8)
    (hmotion : ∀ t ∈ g.cellTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) start cell,
      ∀ l u, l ≤ u → u ≤ N →
      (∀ j : Fin N, l ≤ j.val → j.val < u → start ≤ stop t j) →
      ‖(P t).rawInterval (coeff1 t) jet l u (x1 t) (y1 t)-
        U ((P t).rawInterval (coeff0 t) jet l u (x0 t) (y0 t))‖ ≤
        E*((T t).weight Kw D z)^8) :
    let weight := fun t x => (T t).weight Kw D x
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
    ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
        Prod.fst (fun p => stop p.1 p.2)
        (fun p => (P p.1).rawBand (coeff1 p.1) jet p.2 (x1 p.1) (y1 p.1))
        phase a (SlopeBox.lineShift sR b z) start cell-
      U (g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
        Prod.fst (fun p => stop p.1 p.2)
        (fun p => (P p.1).rawBand (coeff0 p.1) jet p.2 (x0 p.1) (y0 p.1))
        phase a z start cell)‖ ≤
      (V*((1+d)*E+d*A)*C^3)*g.mass tops (fun t => (T t).slope)
        (fun t => w/(T t).length) (g.rootWidth/B^2) weight start cell z := by
  dsimp only
  let weight := fun t x => (T t).weight Kw D x
  let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
  let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
  let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hd : 0 ≤ d := by
    have he := Real.one_le_exp (show 0 ≤ 2*δ by positivity)
    dsimp [d]
    positivity
  apply g.sourcePacketAmplitude_node_motion tops (fun t => (T t).slope)
    (fun t => w/(T t).length) (g.rootWidth/B^2) weight
    (fun t _ => (div_pos hw (T t).length_pos).le) Kb gap Finset.univ stop
    (fun t j => (P t).rawBand (coeff0 t) jet j (x0 t) (y0 t))
    (fun t j => (P t).rawBand (coeff1 t) jet j (x1 t) (y1 t))
    (fun t ht j _ => g.eligible_of_le (div_pos hw (T t).length_pos).le
      (hmax t ht j) (hM t ht)) phase a z (SlopeBox.lineShift sR b z) start cell U
    (V*((1+d)*E+d*A)) C (by dsimp [V]; positivity)
    (fun t _ => ((T t).weight_pos hKw D z).le)
    (fun t ht => htC t ((g.mem_cellTops _ _ _ _ _ _ _).mp ht).1)
  intro t ht
  obtain ⟨htt,_,hel⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
  exact g.source_single_top_predictable_motion tops T w B Kw D hw hB hKw hD hwidth
    hKb gap h start (M t) (hMmax t htt start hel) hbase (hgap t htt) t htt (hM t htt)
    sR (hs t ht) child hchild hblock b hb z phase a Z C ha0 ha1 hZ
    (hz0 t htt) (hz t htt) hC (htC t htt) (P t) (coeff0 t) (coeff1 t) jet
    (stop t) (hstop t htt) (hmax t htt) (x0 t) (y0 t) (x1 t) (y1 t) A E U
    hA hE (hinterval t htt) (hmotion t ht)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedSelectorMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source motion only requires shortness for actual packet items. Empty
long bands have unchanged amplitude when their formal stops are clipped.
The original coefficients, scale parameters and conclusions are retained. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem source_supported_selector_amplitude_motion_oai (p : ℝ) (D Bslots : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → SourceLabeledLattice N κ Label Item),
    (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
    (∀ t ∈ tops, (P t).constant ≤ L^p) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound)
      (Kw : ℝ), 1 ≤ Kw →
    (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw D) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w B : ℝ) (hw : 0 < w), 1 ≤ B →
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → ∀ (gap : ℕ → ℝ) (h start : ℕ), h ≤ start →
    ∀ (M : ι → ℕ),
    (∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t)) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t) →
    (∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h) →
    ∀ (sR : ℝ) (cell : ℤ),
    (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) start cell, g.index h (T t).slope = g.index h sR) →
    g.width h ≤ B*g.width start →
    ∀ (b : ℝ), |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)) →
    ∀ (z : ℝ × ℝ) (frequency : κ → ℝ) (Cfreq : ℝ), 0 ≤ Cfreq →
    (∀ k, |frequency k| ≤ Cfreq/w) → (∀ t ∈ tops, (P t).frequency = frequency) →
    ∀ (phase : ℕ → ℂ) (a Z C A maskExponent : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z →
    (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
    (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    1 ≤ C → (∀ t ∈ tops, (T t).weight Kw (D:ℝ) z ≤ C) → 0 ≤ A →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let stop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
      (div_pos hw ((P t).length_pos j))
    let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤
        A*(weight t z)^8) →
    let J := L^(2*p+4)*Real.exp (16*(D:ℝ))+A+
      (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
    let δ := (5*(D:ℝ)/Kw)/Real.sqrt (g.branching:ℝ)
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
    let value := fun zz t j => (Q t).rawBand
      (fun j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 j
      zz.1 (zz.2-(T t).slope*zz.1)
    ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
        Prod.fst (fun p => stop p.1 p.2) (fun p => value (SlopeBox.lineShift sR b z) p.1 p.2)
        phase a (SlopeBox.lineShift sR b z) start cell-
      diagonalModulationIsometry frequency ((sR-g.center start cell)*b)
        (g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
          Prod.fst (fun p => stop p.1 p.2) (fun p => value z p.1 p.2)
          phase a z start cell)‖ ≤
      (V*((1+d)*(J/Real.sqrt (g.branching:ℝ))+d*A)*C^3)*
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/B^2) weight start cell z := by
  obtain ⟨L0,hL0,hslots,hpacket⟩ :=
    SourceLabeledLattice.source_selector_predictable_masked_interval_motion_of_supported p D Bslots
  refine ⟨L0,hL0,hslots,?_⟩
  intro L hLL ι tops T N κ Label Item _ _ P hcard hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w B hw hB hwidth hlength hzero Kb hKb gap h start hbase M hM
    hMmax hgap sR cell hs hblock b hb z frequency Cfreq hCfreq hfreq hPfreq phase a Z C A
    maskExponent ha0 ha1 hZ hz0 hz hC htC hA
  dsimp only
  intro hconc
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
    (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
  let z' := SlopeBox.lineShift sR b z
  let J := L^(2*p+4)*Real.exp (16*(D:ℝ))+A+
    (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
  have hL : 0 < L := zero_lt_one.trans_le (hL0.trans hLL)
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hsupported : ∀ t ∈ tops, ∀ j (l : (Q t).labels j) (_u : Item j l),
      rawStop t j ≤ M t := by
    intro t ht j l u
    exact g.source_length_stop_le_of_item tops T P w (g.rootWidth/B^2) hw M
      hzero hlength hMmax t ht j l u
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    intro i j hij
    exact min_le_min ((P t).stopping_antitone g (g.rootWidth/B^2) w hw (hzero t ht) hij) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := min_le_right _ _
  have hmasked (t : ι) (ht : t ∈ tops) (l u : ℕ) (hlu : l ≤ u) (hu : u ≤ N) :
      ‖(Q t).rawInterval (fun j k v => (T t).mask L maskExponent z • coeff t j k v)
        0 l u z.1 (z.2-(T t).slope*z.1)‖ ≤ A*(weight t z)^8 := by
    rw [(Q t).rawInterval_coeff_smul, norm_smul, Real.norm_eq_abs]
    have hmask : |(T t).mask L maskExponent z| ≤ 1 := by
      change |topSincMask L maskExponent _ _| ≤ 1
      rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
      exact topSincMask_le_one _ _ _ _
    have hc := hconc t ht l u hlu hu (z.2-(T t).slope*z.1) (by simp [(T t).width_pos.le])
    have hraw : ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-(T t).slope*z.1)‖ ≤
        A*(weight t z)^8 := by
      exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hc
    exact (mul_le_mul_of_nonneg_right hmask (norm_nonneg _)).trans (by simpa using hraw)
  have heq (zz : ℝ×ℝ) := g.sourceBandAmplitude_clip_stop tops
    (fun t => (T t).slope) (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap Q
    (fun t j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 rawStop M hsupported
    (fun _ => zz.1) (fun t => zz.2-(T t).slope*zz.1) phase a zz start cell
  rw [heq z',heq z]
  apply g.source_node_predictable_motion tops T w B Kw (D:ℝ) hw hB hKw0
    (Nat.cast_nonneg D) hwidth hKb gap h start hbase M hM hMmax hgap sR cell hs
    (g.width start) (g.width_pos start) hblock b hb z phase a Z C ha0 ha1 hZ hz0 hz hC htC
    Q (fun t j l u => (T t).mask L maskExponent z • coeff t j l u)
    (fun t j l u => (T t).mask L maskExponent z' • coeff t j l u)
    0 stop hstop hmax (fun _ => z.1) (fun t => z.2-(T t).slope*z.1)
    (fun _ => z'.1) (fun t => z'.2-(T t).slope*z'.1) A (J/Real.sqrt (g.branching:ℝ))
    (diagonalModulationIsometry frequency ((sR-g.center start cell)*b)) hA
    (by positivity) hmasked
  intro t ht l u hlu hu hactive
  obtain ⟨htt,hcell,hel⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
  obtain ⟨_,_,_,hbx,hby⟩ := g.source_packet_displacement_ratios (T t) hw hB
    (hwidth t htt) h start sR b (hs t ht).symm hblock hel hb
  have hf : ∀ k, |(P t).frequency k| ≤ Cfreq/w := by rw [hPfreq t htt]; exact hfreq
  have hm := (hpacket L hLL N κ Label Item (P t) (hcard t htt) (hP t htt)
    (alt t) (hAlt t) (T t) Kw hKw (hgeom t htt) (selector t) (hselector t) (hselector1 t) v hv test htest htest1
    g w B hw hB0 (hzero t htt) start l u hlu
    (fun j hjl hju => (hactive j hjl hju).trans (min_le_left _ _)) sR (g.center start cell) b A
    maskExponent (Cfreq/w) z (by positivity) hf hbx hby (hconc t htt l u hlu hu)).2
  have hbudget := g.source_packet_motion_coefficient (T t) hw hB hL hA hCfreq le_rfl
    (hwidth t htt) h start sR b (hs t ht).symm hblock hel hb p maskExponent (D:ℝ)
  rw [hcell] at hbudget
  rw [hPfreq t htt] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right hbudget (pow_nonneg ((T t).weight_pos hKw0 _ z).le 8))


end LipschitzHilbert.AngularGrid

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion_oai := @OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion_oai
