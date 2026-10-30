-- Prove2me | solution 1 for OAI.LipschitzHilbert.AngularGrid.source_supported_selector_normalized_motion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:13:31.632716+00:00
-- url     : https://prove2.me/submissions/bf0829c8-8832-4104-9980-0ae3c5ca7bab

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_source_supported_selector_amplitude_motion

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

theorem boundary_segment_amplitude_bound (n m : ℕ → ℝ) (z : ℕ → ℂ) (f : ℕ → E)
    (start N K : ℕ) (a lower Z B : ℝ) (hstart : start ≤ N)
    (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z) (hB0 : 0 ≤ B)
    (hn : ∀ j ≤ N, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hm : ∀ j < N, n (j + 1) ≤ m j ∧ m j ≤ n (j + 1 - K))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z)
    (hB : ∀ k, start ≤ k → k ≤ N → ‖∑ i ∈ Finset.Ico start (k + 1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.Ico start (N + 1), segmentWeight n (boundaryLog n m) z a start i • f i‖ ≤
      (lower ^ (-a) * (1 + (a + Z * K) * Real.log (n 0 / n N))) * B :=
  (norm_weighted_Ico_le_variation _ f start N B hstart hB).trans
    (mul_le_mul_of_nonneg_right
      (boundary_weight_variation n m z start N K a lower Z ha hlower hZ hn hmono hm hz0 hz) hB0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional exponent comparison used in the Fourier gain. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem phaseConstant_pos : 0 < phaseConstant := by norm_num [phaseConstant]

omit [Fintype ι] in
theorem phaseParameter_range {D : ℝ} (hD : 1 ≤ D) :
    0 < phaseConstant / Real.log (2 * D) ∧
      phaseConstant / Real.log (2 * D) ≤ 1 / 3 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * D) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpos : 0 < Real.log (2 * D) := by linarith
  refine ⟨div_pos phaseConstant_pos hpos, (div_le_iff₀ hpos).2 ?_⟩
  have hc : phaseConstant ≤ (1 / 6 : ℝ) := by norm_num [phaseConstant]
  linarith

end LipschitzHilbert.PhaseCombinatorics

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

theorem mass_nonnegative (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (level : ℕ) (cell : ℤ) (x : X) :
    0 ≤ g.mass tops slope precision cutoff weight level cell x :=
  Finset.sum_nonneg fun i _ => hw i x

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

/-- The four powers retained in the manuscript's individual-top bound. -/
theorem top_log_absorption_four {h S C Q a : ℝ}
    (hh : 0 < h) (hS : 0 < S) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hQ : 0 ≤ Q) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    h^(8-a) * (1+Q*Real.log (S/h)) ≤
      C^8 * (1+Q*(Real.log (max 1 S)+1))*h^4 := by
  have hb := top_log_absorption (q := 5-a) (d := 8) hh hS hC hhC hQ
    (by linarith) (by norm_num; linarith)
  have heq : h^(8-a) = h^3*h^(5-a) := by
    rw [← Real.rpow_natCast h 3, ← Real.rpow_add hh]
    congr 1
    norm_num
    ring
  calc
    _ = h^3*(h^(5-a)*(1+Q*Real.log (S/h))) := by rw [heq]; ring
    _ ≤ h^3*(C^8*(1+Q*(Real.log (max 1 S)+1))*h) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The normalized source amplitude retains four powers of the top
weight, uniformly down to arbitrarily small positive weights. -/
theorem normalized_top_amplitude_bound_four {E : Type*} [NormedAddCommGroup E]
    (v : E) {h n0 nM S C B Q a : ℝ}
    (hh : 0 < h) (hhn : h ≤ nM) (hn : nM ≤ n0) (hnS : n0 ≤ S)
    (hC : 1 ≤ C) (hhC : h ≤ C) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hv : ‖v‖ ≤ (h^(-a)*(1+Q*Real.log (n0/nM)))*(B*h^8)) :
    ‖v‖ ≤ (C^8*B*(1+Q*(Real.log (max 1 S)+1)))*h^4 := by
  have hnM : 0 < nM := hh.trans_le hhn
  have hn0 : 0 < n0 := hnM.trans_le hn
  have hS : 0 < S := hn0.trans_le hnS
  have hlog : Real.log (n0/nM) ≤ Real.log (S/h) :=
    Real.log_le_log (div_pos hn0 hnM)
      ((div_le_div_of_nonneg_right hnS hnM.le).trans
        (div_le_div_of_nonneg_left hS.le hh hhn))
  have hpw : h^(-a)*h^8 = h^(8-a) := by
    rw [← Real.rpow_natCast h 8, ← Real.rpow_add hh]
    congr 1
    norm_num
    ring
  have hb := top_log_absorption_four hh hS hC hhC hQ ha0 ha1
  calc
    ‖v‖ ≤ (h^(-a)*(1+Q*Real.log (n0/nM)))*(B*h^8) := hv
    _ = B*(h^(8-a)*(1+Q*Real.log (n0/nM))) := by rw [← hpw]; ring
    _ ≤ B*(h^(8-a)*(1+Q*Real.log (S/h))) := by gcongr
    _ ≤ B*(C^8*(1+Q*(Real.log (max 1 S)+1))*h^4) :=
      mul_le_mul_of_nonneg_left hb hB
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

end LipschitzHilbert.SourceParameters

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularAnalyticWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic transition weights for the shared angular packet family.
The exact modulus is the child-to-boundary mass ratio raised to the
real part of the corresponding complex parameter. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem analyticTransition_norm (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell) :
    ‖analyticTransition mass boundary phase level cell‖ =
      (mass (level + 1) cell / boundary level cell) ^ (phase level).re := by
  rw [analyticTransition, Complex.norm_exp, Real.rpow_def_of_pos (div_pos hm hb)]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem analyticTransition_norm_le_one (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell)
    (hle : mass (level + 1) cell ≤ boundary level cell) (hphase : 0 ≤ (phase level).re) :
    ‖analyticTransition mass boundary phase level cell‖ ≤ 1 := by
  rw [analyticTransition_norm mass boundary phase level cell hm hb]
  exact Real.rpow_le_one (div_nonneg hm.le hb.le) ((div_le_one hb).mpr hle) hphase

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared source amplitude uses the packet's stopping mass and the
actual boundary mass at each transition. The assigned top supplies the
positive mass required by every logarithm along the packet's path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

theorem sourceTransition_norm_le_one (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (x : X) (level : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (level+1)) (hz : 0 ≤ (phase level).re) :
    ‖g.sourceTransition tops slope precision cutoff weight K gap phase x level
      (g.index (level+1) (slope top))‖ ≤ 1 := by
  have hn := g.path_mass_pos tops slope precision cutoff weight hw (level+1) top htop he x
  have hb := (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) hK gap level (slope top) x).1
  exact analyticTransition_norm_le_one _ _ phase level _ hn (hn.trans_le hb) hb hz

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

/-- A logarithmic perturbation of a nonzero exponential gives relative
complex motion; the bound does not involve the original logarithm. -/
theorem exponential_relative_motion {a b : ℂ} {E : ℝ}
    (hE : 0 ≤ E) (hmove : ‖b-a‖ ≤ E) :
    ‖Complex.exp b/Complex.exp a-1‖ ≤ Real.exp E*E := by
  have harg : (b-a).re ≤ E := (Complex.re_le_norm _).trans hmove
  have h := norm_exp_sub_le_of_re_le 0 (b-a) E hE harg
  rw [Complex.exp_zero, sub_zero] at h
  have heq : Complex.exp b/Complex.exp a = Complex.exp (b-a) := by
    rw [Complex.exp_sub]
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_left hmove (Real.exp_pos E).le)

/-- A finite product of transition exponentials depends only on the
motion of its specified logarithms, never their magnitudes. -/
theorem transition_product_relative_motion {J : Type*} (s : Finset J)
    (phase : J → ℂ) (loss0 loss1 : J → ℝ) (Z delta : ℝ)
    (hZ : 0 ≤ Z) (hdelta : 0 ≤ delta)
    (hphase : ∀ j ∈ s, ‖phase j‖ ≤ Z)
    (hloss : ∀ j ∈ s, |loss1 j-loss0 j| ≤ delta) :
    ‖(∏ j ∈ s, Complex.exp (phase j*(loss1 j:ℂ))) /
        (∏ j ∈ s, Complex.exp (phase j*(loss0 j:ℂ))) - 1‖ ≤
      Real.exp ((s.card:ℝ)*Z*delta)*((s.card:ℝ)*Z*delta) := by
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  apply exponential_relative_motion (by positivity)
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ s, ‖phase j*(loss1 j:ℂ)-phase j*(loss0 j:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, Z*delta := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hphase j hj) (hloss j hj) (abs_nonneg _) hZ
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

namespace AngularGrid

/-- The actual block transition product has small relative motion once
its concrete child and boundary masses have the preceding local bounds. -/
theorem source_path_relative_motion {ι X : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (lower upper : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) upper) (x0 x1 : X)
    (Z delta : ℝ) (hZ : 0 ≤ Z) (hdelta : 0 ≤ delta)
    (hphase : ∀ j ∈ Finset.Ico lower upper, ‖phase j‖ ≤ Z)
    (hmass : ∀ j ∈ Finset.Ico lower upper,
      |Real.log (g.mass tops slope precision cutoff weight (j+1) (g.index (j+1) (slope top)) x1) -
        Real.log (g.mass tops slope precision cutoff weight (j+1) (g.index (j+1) (slope top)) x0)| ≤ delta)
    (hboundary : ∀ j ∈ Finset.Ico lower upper,
      |Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K gap j
          (g.index (j+1) (slope top)) x1) -
        Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K gap j
          (g.index (j+1) (slope top)) x0)| ≤ delta) :
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x1)
        lower upper (slope top) /
      g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x0)
        lower upper (slope top) - 1‖ ≤
      Real.exp ((upper-lower:ℕ)*Z*(2*delta))*((upper-lower:ℕ)*Z*(2*delta)) := by
  let n := fun j x => g.mass tops slope precision cutoff weight (j+1)
    (g.index (j+1) (slope top)) x
  let b := fun j x => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
    (g.index (j+1) (slope top)) x
  have hn (j : ℕ) (hj : j ∈ Finset.Ico lower upper) (x : X) : 0 < n j x := by
    apply g.path_mass_pos tops slope precision cutoff weight hw (j+1) top htop
    exact g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he
  have hb (j : ℕ) (hj : j ∈ Finset.Ico lower upper) (x : X) : 0 < b j x :=
    (hn j hj x).trans_le (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) hK gap j (slope top) x).1
  have h := transition_product_relative_motion (Finset.Ico lower upper) phase
    (fun j => Real.log (n j x0/b j x0)) (fun j => Real.log (n j x1/b j x1))
    Z (2*delta) hZ (by positivity) hphase (fun j hj =>
      positive_ratio_log_motion (hn j hj x0) (hb j hj x0) (hn j hj x1) (hb j hj x1)
        (hmass j hj) (hboundary j hj))
  simpa only [packetPathProduct, sourceTransition, analyticTransition, n, b, Nat.card_Ico] using h

end AngularGrid

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mass rescaling and block-transition motion for the snapshot prediction.
Every estimate is relative to the positive snapshot masses; no positive
lower cutoff is imposed on a mass. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem massPowerScale_pos {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (a b : ℝ) :
    0 < massPowerScale n c a b := mul_pos (Real.rpow_pos_of_pos hn a) (Real.rpow_pos_of_pos hc b)

theorem massPowerScale_exp {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (a b : ℝ) :
    massPowerScale n c a b = Real.exp (a*Real.log n+b*Real.log c) := by
  rw [massPowerScale, Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hc, ← Real.exp_add]
  congr 1
  ring

theorem massPowerScale_relative_motion {n n' c c' δ : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c') (hδ : 0 ≤ δ)
    (hN : |Real.log n'-Real.log n| ≤ δ) (hC : |Real.log c'-Real.log c| ≤ δ)
    (a b : ℝ) :
    let E := (|a|+|b|)*δ
    |massPowerScale n' c' a b/massPowerScale n c a b-1| ≤ Real.exp E*E := by
  dsimp only
  have harg : |(a*Real.log n'+b*Real.log c')-(a*Real.log n+b*Real.log c)| ≤
      (|a|+|b|)*δ := by
    calc
      _ = |a*(Real.log n'-Real.log n)+b*(Real.log c'-Real.log c)| := by congr 1; ring
      _ ≤ |a*(Real.log n'-Real.log n)|+|b*(Real.log c'-Real.log c)| := abs_add_le _ _
      _ = |a| * |Real.log n'-Real.log n|+|b| * |Real.log c'-Real.log c| := by
        rw [abs_mul,abs_mul]
      _ ≤ |a| * δ+|b| * δ := add_le_add (mul_le_mul_of_nonneg_left hN (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hC (abs_nonneg _))
      _ = _ := by ring
  have h := exponential_relative_motion
    (a := ((a*Real.log n+b*Real.log c : ℝ):ℂ))
    (b := ((a*Real.log n'+b*Real.log c' : ℝ):ℂ))
    (show 0 ≤ (|a|+|b|)*δ by positivity)
    (by simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using harg)
  rw [massPowerScale_exp hn' hc',massPowerScale_exp hn hc]
  simpa only [← Complex.ofReal_exp,← Complex.ofReal_div,← Complex.ofReal_one,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h

theorem positive_relative_motion_to_sub {s s' q : ℝ} (hs : 0 < s)
    (h : |s'/s-1| ≤ q) : |s'-s| ≤ q*s := by
  have heq : s'/s-1 = (s'-s)/s := by field_simp [hs.ne']
  rw [heq,abs_div,abs_of_pos hs] at h
  exact (div_le_iff₀ hs).mp h

theorem complex_relative_motion_to_sub {lam lam' : ℂ} {q : ℝ} (hlam : lam ≠ 0)
    (h : ‖lam'/lam-1‖ ≤ q) : ‖lam'-lam‖ ≤ q*‖lam‖ := by
  have heq : lam'/lam-1 = (lam'-lam)/lam := by field_simp [hlam]
  rw [heq,norm_div] at h
  exact (div_le_iff₀ (norm_pos_iff.mpr hlam)).mp h

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar and vector errors are kept separate until the final product.
The reference vector may already have been rotated by a diagonal isometry. -/
theorem scalar_rescaling_motion {s s' c q η C : ℝ}
    (hs : 0 < s) (hs' : 0 ≤ s') (_hc : 0 ≤ c) (hq : 0 ≤ q)
    (_hη : 0 ≤ η) (_hC : 0 ≤ C) (hscale : |s'/s-1| ≤ q)
    (v' v : E) (hv : ‖v‖ ≤ C*c) (hmotion : ‖v'-v‖ ≤ η*c) :
    ‖s' • v'-s • v‖ ≤ ((1+q)*η+q*C)*s*c := by
  have hsub := positive_relative_motion_to_sub hs hscale
  have hsbound : s' ≤ (1+q)*s := by linarith [(abs_le.mp hsub).2]
  have heq : s' • v'-s • v = s' • (v'-v)+(s'-s) • v := by
    rw [smul_sub,sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖s' • (v'-v)‖+‖(s'-s) • v‖ := norm_add_le _ _
    _ = s'*‖v'-v‖+|s'-s| * ‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hs']
    _ ≤ ((1+q)*s)*(η*c)+(q*s)*(C*c) := add_le_add
      (mul_le_mul hsbound hmotion (norm_nonneg _) (by positivity))
      (mul_le_mul hsub hv (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem massPowerScale_amplitude_motion {n n' c c' δ η C : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c')
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hN : |Real.log n'-Real.log n| ≤ δ) (hchild : |Real.log c'-Real.log c| ≤ δ)
    (a b : ℝ) (v' v : E) (hv : ‖v‖ ≤ C*c) (hmotion : ‖v'-v‖ ≤ η*c) :
    let q := Real.exp ((|a|+|b|)*δ)*((|a|+|b|)*δ)
    ‖massPowerScale n' c' a b • v'-massPowerScale n c a b • v‖ ≤
      ((1+q)*η+q*C)*massPowerScale n c a b*c := by
  dsimp only
  exact scalar_rescaling_motion (massPowerScale_pos hn hc a b)
    (massPowerScale_pos hn' hc' a b).le hc.le (by positivity) hη hC
    (massPowerScale_relative_motion hn hn' hc hc' hδ hN hchild a b) v' v hv hmotion

end Vector

/-- The scalar in `pred:scaled-motion` times the snapshot child mass. -/
theorem prediction_mass_scale_identity {n c : ℝ} (hn : 0 < n) (hc : 0 < c)
    (p μ : ℝ) :
    massPowerScale n c (-(1/p)) (μ-1+1/p)*c = (c/n)^(1/p)*c^μ := by
  rw [massPowerScale,Real.rpow_neg hn.le,Real.div_rpow hc.le hn.le]
  have heq : c^(μ-1+1/p)*c = c^(1/p)*c^μ := by
    calc
      _ = c^(μ-1+1/p)*c^(1:ℝ) := by rw [Real.rpow_one]
      _ = c^((μ-1+1/p)+1) := (Real.rpow_add hc _ _).symm
      _ = c^(1/p+μ) := by congr 1; ring
      _ = _ := Real.rpow_add hc _ _
  calc
    (n^(1/p))⁻¹*c^(μ-1+1/p)*c = (n^(1/p))⁻¹*(c^(μ-1+1/p)*c) := by ring
    _ = (n^(1/p))⁻¹*(c^(1/p)*c^μ) := by rw [heq]
    _ = _ := by ring

theorem prediction_numerator_scale_identity {n c : ℝ} (hn : 0 < n) (μ : ℝ) :
    n^(μ-1)*c = n^μ*(c/n) := by
  rw [Real.rpow_sub hn,Real.rpow_one]
  ring

theorem complex_product_relative_motion {s s' q η : ℝ} (hs : 0 < s) (hs' : 0 ≤ s')
    (hq : 0 ≤ q) (_hη : 0 ≤ η) (hscale : |s'/s-1| ≤ q)
    (lam lam' : ℂ) (hlam : ‖lam‖ ≤ 1) (hlammove : ‖lam'-lam‖ ≤ η) :
    ‖(s':ℂ)*lam'-(s:ℂ)*lam‖ ≤ (q+η+q*η)*s := by
  have hsub := positive_relative_motion_to_sub hs hscale
  have hsbound : s' ≤ (1+q)*s := by linarith [(abs_le.mp hsub).2]
  have heq : (s':ℂ)*lam'-(s:ℂ)*lam = ((s':ℂ)-(s:ℂ))*lam+(s':ℂ)*(lam'-lam) := by ring
  rw [heq]
  calc
    _ ≤ ‖((s':ℂ)-(s:ℂ))*lam‖+‖(s':ℂ)*(lam'-lam)‖ := norm_add_le _ _
    _ = |s'-s| * ‖lam‖+s'*‖lam'-lam‖ := by
      rw [norm_mul,norm_mul,← Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hs']
    _ ≤ (q*s)*1+((1+q)*s)*η := add_le_add
      (mul_le_mul hsub hlam (norm_nonneg _) (by positivity))
      (mul_le_mul hsbound hlammove (norm_nonneg _) (by positivity))
    _ = _ := by ring

section ComplexVector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem complex_coefficient_amplitude_motion {s c q η C : ℝ}
    (hs : 0 ≤ s) (_hc : 0 ≤ c) (hq : 0 ≤ q) (_hη : 0 ≤ η) (_hC : 0 ≤ C)
    (lam lam' : ℂ) (hlam : ‖lam‖ ≤ s) (hlammove : ‖lam'-lam‖ ≤ q*s)
    (v' v : E) (hv : ‖v‖ ≤ C*c) (hmotion : ‖v'-v‖ ≤ η*c) :
    ‖lam' • v'-lam • v‖ ≤ ((1+q)*η+q*C)*s*c := by
  have hlam' : ‖lam'‖ ≤ (1+q)*s := by
    have ht := norm_add_le (lam'-lam) lam
    rw [sub_add_cancel] at ht
    nlinarith
  have heq : lam' • v'-lam • v = lam' • (v'-v)+(lam'-lam) • v := by
    rw [smul_sub,sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖lam' • (v'-v)‖+‖(lam'-lam) • v‖ := norm_add_le _ _
    _ = ‖lam'‖*‖v'-v‖+‖lam'-lam‖*‖v‖ := by rw [norm_smul,norm_smul]
    _ ≤ ((1+q)*s)*(η*c)+(q*s)*(C*c) := add_le_add
      (mul_le_mul hlam' hmotion (norm_nonneg _) (by positivity))
      (mul_le_mul hlammove hv (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- The numerator rescaling in `pred:numerator-motion`. Its coefficient
is expressed relative to `n^μ*(c/n)`, exactly the snapshot parent scale
times the child fraction. -/
theorem prediction_numerator_motion {n n' c δ qlam η C : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hqlam : 0 ≤ qlam) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hN : |Real.log n'-Real.log n| ≤ δ) (μ : ℝ)
    (lam lam' : ℂ) (hlam : ‖lam‖ ≤ 1) (hlammove : ‖lam'-lam‖ ≤ qlam)
    (v' v : E) (hv : ‖v‖ ≤ C*c) (hmotion : ‖v'-v‖ ≤ η*c) :
    let qn := Real.exp (|μ-1| * δ)*(|μ-1| * δ)
    let q := qn+qlam+qn*qlam
    ‖((n'^(μ-1):ℝ):ℂ) • (lam' • v')-((n^(μ-1):ℝ):ℂ) • (lam • v)‖ ≤
      ((1+q)*η+q*C)*n^μ*(c/n) := by
  dsimp only
  let qn := Real.exp (|μ-1| * δ)*(|μ-1| * δ)
  have hqn : 0 ≤ qn := by dsimp [qn]; positivity
  have hscale : |n'^(μ-1)/n^(μ-1)-1| ≤ qn := by
    simpa only [massPowerScale,Real.rpow_zero,mul_one,abs_zero,add_zero] using
      massPowerScale_relative_motion hn hn' (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<1) hδ hN (by simp; exact hδ) (μ-1) 0
  have hproduct := complex_product_relative_motion (Real.rpow_pos_of_pos hn (μ-1))
    (Real.rpow_pos_of_pos hn' (μ-1)).le hqn hqlam hscale lam lam' hlam hlammove
  have hnorm : ‖((n^(μ-1):ℝ):ℂ)*lam‖ ≤ n^(μ-1) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hn (μ-1))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlam
      (Real.rpow_pos_of_pos hn (μ-1)).le
  have h := complex_coefficient_amplitude_motion (Real.rpow_pos_of_pos hn (μ-1)).le hc
    (show 0 ≤ qn+qlam+qn*qlam by positivity) hη hC _ _ hnorm hproduct v' v hv hmotion
  rw [smul_smul,smul_smul]
  calc
    _ ≤ ((1+(qn+qlam+qn*qlam))*η+(qn+qlam+qn*qlam)*C)*n^(μ-1)*c := h
    _ = _ := by rw [mul_assoc, prediction_numerator_scale_identity hn]; ring

end ComplexVector

namespace AngularGrid

theorem source_path_product_ne_zero {ι X : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (phase : ℕ → ℂ) (x : X)
    (lower upper : ℕ) (s : ℝ) :
    g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower upper s ≠ 0 := by
  unfold packetPathProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact Complex.exp_ne_zero _

theorem source_path_product_norm_le_one {ι X : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ) (x : X)
    (lower upper : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) upper)
    (hphase : ∀ j ∈ Finset.Ico lower upper, 0 ≤ (phase j).re) :
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower upper (slope top)‖ ≤ 1 := by
  rw [packetPathProduct,norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.Ico lower upper, (1:ℝ) := by
      apply Finset.prod_le_prod
      · intro j _
        exact norm_nonneg _
      · intro j hj
        exact g.sourceTransition_norm_le_one tops slope precision cutoff weight hp hw hK gap phase x j top
          htop (g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he) (hphase j hj)
    _ = _ := by simp

/-- The actual finite source transition product has relative motion
obtained from physical child and boundary masses, without any mass cutoff. -/
theorem source_block_transition_relative_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (h lower upper : ℕ) (hbase : h ≤ lower)
    (hgap : ∀ j ∈ Finset.Ico lower upper, 0 ≤ gap j ∧ gap j ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) upper)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (Z : ℝ) (hZ : 0 ≤ Z) (hphase : ∀ j ∈ Finset.Ico lower upper, ‖phase j‖ ≤ Z) :
    let weight := fun t x => (T t).weight K D x
    let lam := fun x => g.packetPathProduct (g.sourceTransition tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap phase x)
      lower upper (T top).slope
    let e := (upper-lower:ℕ)*Z*(2*((5*D/K)/Real.sqrt (g.branching:ℝ)))
    ‖lam (SlopeBox.lineShift sR b z)/lam z-1‖ ≤ Real.exp e*e := by
  classical
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight K D x
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  apply g.source_path_relative_motion tops slope precision cutoff weight hp
    (fun t x => (T t).weight_pos hK D x) hKb gap phase lower upper top htop he
    z (SlopeBox.lineShift sR b z) Z ((5*D/K)/Real.sqrt (g.branching:ℝ)) hZ
    (by positivity) hphase
  · intro j hj
    let A := g.cellTops tops slope precision cutoff (j+1) (g.index (j+1) (T top).slope)
    have hA : A.Nonempty := ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he⟩⟩
    exact g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      0 h (j+1) (by have := (Finset.mem_Ico.mp hj).1; omega)
      (gap j) (hgap j hj).1 (hgap j hj).2 (T top).slope sR hs child hchild hblock
      A hA (g.parent_subset_boundary tops slope precision cutoff 0 (j+1) (gap j) (T top).slope) b hb z
  · intro j hj
    let A := g.boundaryTops tops slope precision cutoff (j+1-Kb) j (gap j) (T top).slope
    have hA : A.Nonempty := by
      apply Finset.Nonempty.mono (g.parent_subset_boundary tops slope precision cutoff
        (j+1-Kb) j (gap j) (T top).slope)
      exact ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr
        ⟨htop,rfl,g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he⟩⟩
    have hmass := g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      (j+1-Kb) h j (by have := (Finset.mem_Ico.mp hj).1; omega)
      (gap j) (hgap j hj).1 (hgap j hj).2 (T top).slope sR hs child hchild hblock
      A hA (Finset.Subset.refl _) b hb z
    rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hKb gap,
      g.sourceBoundaryMass_path tops slope precision cutoff weight hKb gap]
    exact hmass

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed near-uniform averaging at the actual rounded source scale. -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem source_step_tendsto_atTop : Tendsto SourceParameters.step atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ ((Real.tendsto_exp_atTop).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  have h := Real.exp_le_exp.mpr (SourceParameters.log_step_bounds hL).1
  simpa only [Function.comp_apply, Real.exp_log (SourceParameters.step_pos L)] using h

end LipschitzHilbert

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

/-- On the small-motion range the relative loss factor is linear in
that motion, with an absolute constant. -/
theorem relative_loss_factor_le {delta : ℝ} (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1/2) :
    Real.exp (2*delta)-1 ≤ (2*Real.exp 1)*delta := by
  have h := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => Real.differentiableAt_exp)
    (fun x hx => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_exp.mpr hx.2)
    (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show 2*delta ∈ Set.Icc (0:ℝ) 1 by constructor <;> linarith)
  have hnonneg : 0 ≤ Real.exp (2*delta)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  simp only [Real.exp_zero, Real.norm_eq_abs, sub_zero] at h
  rw [abs_of_nonneg hnonneg, abs_of_nonneg (show 0 ≤ 2*delta by positivity)] at h
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase and amplitude estimates at the actual source parameters. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem phaseMu_positive_le {D p : ℝ} (hD : 1 ≤ D) (hp : 0 < p) :
    0 < phaseMu D p ∧ phaseMu D p ≤ (4 / 3 : ℝ) / p := by
  have hθ := phaseParameter_range hD
  change 0 < phaseParameter D ∧ phaseParameter D ≤ 1 / 3 at hθ
  constructor
  · exact div_pos (by linarith [hθ.1]) hp
  · exact div_le_div_of_nonneg_right (by linarith [hθ.2]) hp.le

/-- The source's global top-mass bound grows by at most `exp(3 sqrt L)`
after taking the phase power, uniformly in the direction-count parameter. -/
theorem source_phase_mass_bound {D L N : ℝ}
    (hD : 1 ≤ D) (hL : 1 ≤ L) (hN : 0 < N) (hlogN : Real.log N ≤ 2 * L) :
    N ^ phaseMu D (Real.sqrt L) ≤ Real.exp (3 * Real.sqrt L) := by
  have hL0 : 0 ≤ L := by linarith
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hμ := phaseMu_positive_le hD hp
  have hsq := Real.sq_sqrt hL0
  rw [Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.mpr
  calc
    Real.log N * phaseMu D (Real.sqrt L) ≤ (2 * L) * phaseMu D (Real.sqrt L) :=
      mul_le_mul_of_nonneg_right hlogN hμ.1.le
    _ ≤ (2 * L) * ((4 / 3 : ℝ) / Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hμ.2 (by positivity)
    _ = (8 / 3 : ℝ) * Real.sqrt L := by
      field_simp [hp.ne']
      nlinarith
    _ ≤ 3 * Real.sqrt L := by nlinarith [Real.sqrt_nonneg L]

/-- The amplitude scale `L^C (1+N^mu)` is smaller than every fixed
positive power of the actual rounded dyadic step. This is the source's
subpower estimate used to absorb all marked-cell comparison errors. -/
theorem eventually_source_subpower_amplitude (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 2 * L →
      L ^ C * (1 + N ^ phaseMu D (Real.sqrt L)) ≤ SourceParameters.step L ^ δ := by
  have hpow := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)
  have hlog : Tendsto (fun L : ℝ => Real.log L / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).tendsto_div_nhds_zero
  have hroot : Tendsto (fun L : ℝ => Real.sqrt L / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hL]
    norm_num
  have hconst : Tendsto (fun L : ℝ => Real.log 2 / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := Real.log 2)).mul (tendsto_inv_atTop_zero.comp hpow)
  have hsum := ((hlog.const_mul C).add hconst).add (hroot.const_mul 3)
  simp only [mul_zero, add_zero] at hsum
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsum.eventually (gt_mem_nhds hδ)] with L hL hsmall
  intro D N hD hN hlogN
  have hL0 : 0 < L := by linarith
  have hpower : 0 < L ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hbudget : C * Real.log L + Real.log 2 + 3 * Real.sqrt L ≤ δ * L ^ (7 / 10 : ℝ) := by
    apply (div_le_iff₀ hpower).mp
    convert hsmall.le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hmass := source_phase_mass_bound hD hL hN hlogN
  have hone : 1 ≤ Real.exp (3 * Real.sqrt L) := Real.one_le_exp (by positivity)
  calc
    _ ≤ L ^ C * (2 * Real.exp (3 * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hL0.le _)
    _ = Real.exp (C * Real.log L + Real.log 2 + 3 * Real.sqrt L) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos hL0]
      rw [mul_comm C (Real.log L)]
      ring
    _ ≤ Real.exp (δ * L ^ (7 / 10 : ℝ)) := Real.exp_le_exp.mpr hbudget
    _ ≤ SourceParameters.step L ^ δ := by
      rw [Real.rpow_def_of_pos (SourceParameters.step_pos L)]
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left (SourceParameters.log_step_bounds hL0.le).1 hδ.le).trans_eq
        (mul_comm δ _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMotionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative small factors in predictable motion. Fixed powers
and constants are absorbed only after the packet and weight estimates. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem source_moving_weight_factor_le {a δ : ℝ}
    (ha1 : a ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1)) ≤
      (Real.exp 1*(1+2*Real.exp 1))*δ := by
  have he : Real.exp (a*δ) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right ha1 hδ0
    linarith
  have hnonneg : 0 ≤ δ+(Real.exp (2*δ)-1) := by
    have := Real.one_le_exp (show 0 ≤ 2*δ by positivity)
    linarith
  have hrel := relative_loss_factor_le hδ0 hδ1
  calc
    _ ≤ Real.exp 1*(δ+(Real.exp (2*δ)-1)) :=
      mul_le_mul_of_nonneg_right he hnonneg
    _ ≤ Real.exp 1*(δ+(2*Real.exp 1)*δ) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hrel) (Real.exp_pos 1).le
    _ = _ := by ring

/-- The two summation-by-parts errors have a common inverse-square-root
factor as soon as their independent packet and weight bounds do. -/
theorem source_predictable_coefficient_le {V A E d W J G : ℝ}
    (hV : 0 ≤ V) (hA : 0 ≤ A) (hE : 0 ≤ E) (hW : 0 ≤ W) (hG : 1 ≤ G)
    (hd : d ≤ W/Real.sqrt G) (hpacket : E ≤ J/Real.sqrt G) :
    V*((1+d)*E+d*A) ≤ (V*((1+W)*J+W*A))/Real.sqrt G := by
  have hs : 1 ≤ Real.sqrt G := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    simpa using hG
  have hdW : d ≤ W := hd.trans (div_le_self hW hs)
  have hfirst : (1+d)*E ≤ (1+W)*(J/Real.sqrt G) := by
    calc
      _ ≤ (1+W)*E := mul_le_mul_of_nonneg_right (by linarith) hE
      _ ≤ _ := mul_le_mul_of_nonneg_left hpacket (by positivity)
  calc
    _ ≤ V*((1+W)*(J/Real.sqrt G)+(W/Real.sqrt G)*A) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hfirst (mul_le_mul_of_nonneg_right hd hA)) hV
    _ = _ := by ring

/-- Every fixed polynomial prefactor in the exact source motion bounds
is dominated by a quarter-power gain of the actual rounded dyadic step. -/
theorem eventually_source_polynomial_motion (C p : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      C*L^p/Real.sqrt (SourceParameters.step L) ≤
        SourceParameters.step L^(-(1/4:ℝ)) := by
  have hsub := eventually_source_subpower_amplitude (p+1) (1/4) (by norm_num)
  filter_upwards [hsub, eventually_ge_atTop (max 1 C)] with L hL hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hCL : C ≤ L := (le_max_right _ _).trans hlarge
  have hpower : L^(p+1) ≤ SourceParameters.step L^(1/4:ℝ) := by
    have h := hL 1 1 (by norm_num) (by norm_num) (by simp; positivity)
    have hn : 0 ≤ L^(p+1) := Real.rpow_nonneg hL0.le _
    norm_num at h
    linarith
  have hpoly : C*L^p ≤ SourceParameters.step L^(1/4:ℝ) := by
    calc
      _ ≤ L*L^p := mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL0.le _)
      _ = L^(p+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
      _ ≤ _ := hpower
  calc
    _ ≤ SourceParameters.step L^(1/4:ℝ)/Real.sqrt (SourceParameters.step L) :=
      div_le_div_of_nonneg_right hpoly (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub (SourceParameters.step_pos L)]
      norm_num

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictableDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the source predictable-motion
coefficient, before its dyadic gain is absorbed. -/

noncomputable section
namespace LipschitzHilbert

theorem source_amplitude_log_factor {L S a Z C : ℝ} {K : ℕ}
    (hL : 1 ≤ L) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 2*L^2)
    (hK : (K:ℝ) ≤ L^2) (hS : Real.log (max 1 S) ≤ 3*L) :
    C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2 ≤ (169*C^4)*L^10 := by
  have hL0 : 0 ≤ L := by linarith
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  have hL5 : 1 ≤ L^5 := one_le_pow₀ hL
  have hlog0 : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hzk : Z*(K:ℝ) ≤ (2*L^2)*L^2 := mul_le_mul hZ hK (Nat.cast_nonneg _) (by positivity)
  have haq : a+Z*K ≤ 3*L^4 := by nlinarith
  have hlog : Real.log (max 1 S)+1 ≤ 4*L := by linarith
  have hproduct := mul_le_mul haq hlog (by positivity : 0 ≤ Real.log (max 1 S)+1)
    (by positivity : 0 ≤ 3*L^4)
  have hfactor : 1+(a+Z*K)*(Real.log (max 1 S)+1) ≤ 13*L^5 := by
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(a+Z*K)*(Real.log (max 1 S)+1))
    hfactor 2
  calc
    _ ≤ C^4*(13*L^5)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

theorem source_packet_polynomial {L A p q maskExponent Cfreq D : ℝ}
    (hL : 1 ≤ L) (hA0 : 0 ≤ A) (hA : A ≤ L^q) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hmask : 0 ≤ maskExponent) (hCfreq : 0 ≤ Cfreq) :
    L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A ≤
      (Real.exp (16*D)+9+Cfreq)*L^(2*p+q+6) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr (r s : ℝ) (hrs : r ≤ s) : L^r ≤ L^s :=
    Real.rpow_le_rpow_of_exponent_le hL hrs
  have hlarge : 0 ≤ L^(2*p+q+6) := Real.rpow_nonneg hL0.le _
  have hfirst := mul_le_mul_of_nonneg_right
    (hr (2*p+4) (2*p+q+6) (by linarith)) (Real.exp_pos (16*D)).le
  have hplain : A ≤ L^(2*p+q+6) := hA.trans (hr q _ (by linarith))
  have hden : 1 ≤ L^maskExponent := Real.one_le_rpow hL hmask
  have hceil : (⌈L⌉₊:ℝ) ≤ 2*L := by
    have := (Nat.ceil_lt_add_one hL0.le).le
    linarith
  have hmaskfactor : 4*(⌈L⌉₊:ℝ)/L^maskExponent ≤ 8*L := by
    calc
      _ ≤ 4*(⌈L⌉₊:ℝ) := div_le_self (by positivity) hden
      _ ≤ _ := by linarith
  have hmasked : (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A ≤ 8*L^(2*p+q+6) := by
    calc
      _ ≤ (8*L)*L^q := mul_le_mul hmaskfactor hA hA0 (by positivity)
      _ = 8*L^(q+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr (q+1) _ (by linarith)) (by norm_num)
  have hlast := mul_le_mul_of_nonneg_left hplain hCfreq
  nlinarith

theorem source_predictable_polynomial_bound {L A p q maskExponent Cfreq D Kw G S a Z C : ℝ}
    {K : ℕ} (hL : 1 ≤ L) (hA0 : 0 ≤ A) (hA : A ≤ L^q)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hmask : 0 ≤ maskExponent) (hCfreq : 0 ≤ Cfreq)
    (hD : 0 ≤ D) (hKw : 1 ≤ Kw) (hG : 1 ≤ G) (hsmall : (5*D/Kw)/Real.sqrt G ≤ 1/2)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 2*L^2)
    (hK : (K:ℝ) ≤ L^2) (hS : Real.log (max 1 S) ≤ 3*L) (hC : 1 ≤ C) :
    let J := L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
    let δ := (5*D/Kw)/Real.sqrt G
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2
    let W := 5*D*(Real.exp 1*(1+2*Real.exp 1))
    V*((1+d)*(J/Real.sqrt G)+d*A)*C^3 ≤
      ((169*C^7)*((1+W)*(Real.exp (16*D)+9+Cfreq)+W))*L^(2*p+q+16)/Real.sqrt G := by
  dsimp only
  let J := L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
  let δ := (5*D/Kw)/Real.sqrt G
  let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
  let V := C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2
  let W := 5*D*(Real.exp 1*(1+2*Real.exp 1))
  let CJ := Real.exp (16*D)+9+Cfreq
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hd : d ≤ W/Real.sqrt G := by
    calc
      _ ≤ (Real.exp 1*(1+2*Real.exp 1))*δ := source_moving_weight_factor_le ha1 hδ hsmall
      _ ≤ (Real.exp 1*(1+2*Real.exp 1))*((5*D)/Real.sqrt G) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (div_le_self (by positivity) hKw) (Real.sqrt_nonneg _))
          (by positivity)
      _ = _ := by dsimp [W]; ring
  have hVbound : V ≤ (169*C^4)*L^10 := source_amplitude_log_factor hL ha0 ha1 hZ0 hZ hK hS
  have hJbound : J ≤ CJ*L^(2*p+q+6) := source_packet_polynomial hL hA0 hA hp hq hmask hCfreq
  have hAbound : A ≤ L^(2*p+q+6) := hA.trans
    (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
  have hinner : (1+W)*J+W*A ≤ ((1+W)*CJ+W)*L^(2*p+q+6) := by
    calc
      _ ≤ (1+W)*(CJ*L^(2*p+q+6))+W*L^(2*p+q+6) :=
        add_le_add (mul_le_mul_of_nonneg_left hJbound (by positivity))
          (mul_le_mul_of_nonneg_left hAbound hW)
      _ = _ := by ring
  have hmotion := source_predictable_coefficient_le hV hA0
    (show 0 ≤ J/Real.sqrt G by positivity) hW hG hd (le_refl (J/Real.sqrt G))
  calc
    _ ≤ ((V*((1+W)*J+W*A))/Real.sqrt G)*C^3 :=
      mul_le_mul_of_nonneg_right hmotion (by positivity)
    _ ≤ ((((169*C^4)*L^10)*(((1+W)*CJ+W)*L^(2*p+q+6)))/Real.sqrt G)*C^3 :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul hVbound hinner (by positivity) (by positivity))
          (Real.sqrt_nonneg _)) (by positivity)
    _ = (((169*C^7)*((1+W)*CJ+W))*(L^10*L^(2*p+q+6)))/Real.sqrt G := by ring
    _ = _ := by
      rw [← Real.rpow_natCast L 10, ← Real.rpow_add hL0]
      congr 2
      congr 1
      norm_num
      ring

/-- At the actual source step, the full predictable-motion coefficient
is at most `G^(-1/4)`, uniformly in the allowed phase and mass parameters. -/
theorem eventually_source_predictable_coefficient (p q D C Cfreq : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hD : 0 ≤ D) (hC : 1 ≤ C) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in Filter.atTop,
      ∀ (A maskExponent Kw S a Z : ℝ) (K : ℕ),
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 1 ≤ Kw →
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (K:ℝ) ≤ L^2 →
      Real.log (max 1 S) ≤ 3*L →
      let G := SourceParameters.step L
      let J := L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
      let δ := (5*D/Kw)/Real.sqrt G
      let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
      let V := C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2
      V*((1+d)*(J/Real.sqrt G)+d*A)*C^3 ≤ G^(-(1/4:ℝ)) := by
  let W := 5*D*(Real.exp 1*(1+2*Real.exp 1))
  let CP := (169*C^7)*((1+W)*(Real.exp (16*D)+9+Cfreq)+W)
  have hpoly := eventually_source_polynomial_motion CP (2*p+q+16)
  have hsqrt := (Real.tendsto_sqrt_atTop.comp source_step_tendsto_atTop).eventually_ge_atTop (10*D)
  filter_upwards [hpoly,hsqrt,Filter.eventually_ge_atTop (1:ℝ)] with L hpoly hsqrt hL
  change 10*D ≤ Real.sqrt (SourceParameters.step L) at hsqrt
  intro A maskExponent Kw S a Z K hA0 hA hmask hKw ha0 ha1 hZ0 hZ hK hS
  dsimp only
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hroot : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hsmall : (5*D/Kw)/Real.sqrt (SourceParameters.step L) ≤ 1/2 := by
    apply (div_le_iff₀ hroot).mpr
    have hb := div_le_self (show 0 ≤ 5*D by positivity) hKw
    linarith
  exact (source_predictable_polynomial_bound hL hA0 hA hp hq hmask hCfreq hD hKw
    hG hsmall ha0 ha1 hZ0 hZ hK hS hC).trans hpoly

end LipschitzHilbert

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularAmplitude
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
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

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem angular_stopping_amplitude_bound (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start M K : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (n m : ℕ → ℝ) (phase : ℕ → ℂ) (a lower Z B : ℝ)
    (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hn : ∀ j ≤ M, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic M))
    (hm : ∀ j < M, n (j+1) ≤ m j ∧ m j ≤ n (j+1-K))
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    (x y : ℝ)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff jet l u x y‖ ≤ B) :
    ‖∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
      segmentWeight n (boundaryLog n m) phase a start (stop j) •
        P.rawBand coeff jet j x y‖ ≤
      (lower^(-a) * (1+(a+Z*K)*Real.log (n 0/n M))) * B := by
  let f := fun k => ∑ j ∈ Finset.univ.filter (fun j => stop j = k), P.rawBand coeff jet j x y
  have hpartial (k : ℕ) (_hsk : start ≤ k) (_hk : k ≤ M) :
      ‖∑ i ∈ Finset.Ico start (k+1), f i‖ ≤ B := by
    dsimp only [f]
    rw [sum_stopping_fibers]
    obtain ⟨l,u,hlu,hu,heq⟩ := P.stopping_band_eq_rawInterval coeff jet stop hstop start (k+1) x y
    rw [heq]
    exact hinterval l u hlu hu
  rw [stopping_weighted_sum_eq stop (fun j => P.rawBand coeff jet j x y) _ start M hmax]
  exact boundary_segment_amplitude_bound n m phase f start M K a lower Z B hstart
    ha hlower hZ hB hn hmono hm hz0 hz hpartial

end SourceLabeledLattice

/-- Specialization to the actual angular mass and boundary sets. The
individual top weight supplies the positive endpoint normalization. -/
theorem source_angular_stopping_amplitude_bound
    {ι X : Type*} (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i z, 0 < weight i z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : grid.eligible cutoff (precision top) M) (z : X)
    (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (x y B : ℝ) (hB : 0 ≤ B)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff jet l u x y‖ ≤ B) :
    let n := fun j => grid.mass tops slope precision cutoff weight j (grid.index j (slope top)) z
    let m := fun j => grid.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (grid.index (j+1) (slope top)) z
    ‖∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
      segmentWeight n (boundaryLog n m) phase a start (stop j) • P.rawBand coeff jet j x y‖ ≤
      ((weight top z)^(-a) * (1+(a+Z*K)*Real.log (n 0/n M))) * B := by
  dsimp only
  let n := fun j => grid.mass tops slope precision cutoff weight j (grid.index j (slope top)) z
  have hn (j : ℕ) (hj : j ≤ M) : weight top z ≤ n j := by
    apply Finset.single_le_sum (fun i _ => (hw i z).le)
    exact (grid.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,grid.eligible_of_le (hp top htop) hj he⟩
  apply P.angular_stopping_amplitude_bound coeff jet stop hstop start M K hstart hmax
    n _ phase a (weight top z) Z B ha (hw top z) hZ hB hn
    ((grid.path_mass_antitone tops slope precision cutoff weight hp
      (fun i z => (hw i z).le) top z).antitoneOn _)
  · intro j _
    exact grid.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun i z => (hw i z).le) hK gap j (slope top) z
  · exact hz0
  · exact hz
  · exact hinterval

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularIdentity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
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

/-- The interval concentration bound now controls the actual single-top
contribution to the shared analytic family, on every starting level. -/
theorem sourcePacketAmplitude_single_top_bound (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i z, 0 < weight i z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : grid.eligible cutoff (precision top) M) (z : X)
    (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (x y B : ℝ) (hB : 0 ≤ B)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff jet l u x y‖ ≤ B) :
    ‖grid.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
      (fun _ : Fin N => top) stop (fun j => P.rawBand coeff jet j x y) phase a z start
      (grid.index start (slope top))‖ ≤
      ((weight top z)^(-a) * (1+(a+Z*K)*Real.log
        (grid.mass tops slope precision cutoff weight 0 (grid.index 0 (slope top)) z /
          grid.mass tops slope precision cutoff weight M (grid.index M (slope top)) z))) * B := by
  rw [grid.sourcePacketAmplitude_single_top tops slope precision cutoff weight hp hw hK gap
    phase M top htop he a z stop hmax]
  exact source_angular_stopping_amplitude_bound grid tops slope precision cutoff weight hp hw
    hK gap phase M top htop he z a Z ha hZ hz0 hz P coeff jet stop hstop start hstart hmax
    x y B hB hinterval

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
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

theorem sourcePacketAmplitude_fourth_envelope (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i z, 0 < weight i z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : grid.eligible cutoff (precision top) M) (z : X)
    (a Z : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (x y B C : ℝ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hweight : weight top z ≤ C)
    (hinterval : ∀ l u, l ≤ u → u ≤ N →
      ‖P.rawInterval coeff jet l u x y‖ ≤ B*(weight top z)^8) :
    ‖grid.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
      (fun _ : Fin N => top) stop (fun j => P.rawBand coeff jet j x y) phase a z start
      (grid.index start (slope top))‖ ≤
      (C^8*B*(1+(a+Z*K)*(Real.log (max 1 (∑ i ∈ tops, weight i z))+1)))*(weight top z)^4 := by
  let n := fun j => grid.mass tops slope precision cutoff weight j (grid.index j (slope top)) z
  have hnM : weight top z ≤ n M := by
    apply Finset.single_le_sum (fun i _ => (hw i z).le)
    exact (grid.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩
  have hmono := grid.path_mass_antitone tops slope precision cutoff weight hp
    (fun i z => (hw i z).le) top z
  have hn0 : n M ≤ n 0 := hmono (Nat.zero_le M)
  have htotal : n 0 ≤ ∑ i ∈ tops, weight i z :=
    grid.mass_le_total tops slope precision cutoff weight (fun i z => (hw i z).le) 0 _ z
  have hraw := grid.sourcePacketAmplitude_single_top_bound tops slope precision cutoff weight
    hp hw hK gap phase M top htop he z a Z ha0 hZ hz0 hz P coeff jet stop hstop
    start hstart hmax x y (B*(weight top z)^8) (by positivity) hinterval
  exact normalized_top_amplitude_bound_four _ (hw top z) hnM hn0 htotal hC hweight hB
    (by positivity : 0 ≤ a+Z*K) ha0 ha1 hraw

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLengthRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting to an interval of original packet lengths preserves all
interval concentration bounds. The resulting coefficients are explicit
zero extensions of the original analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawBand_restrictCoefficient (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (jet : Fin 3) (j : Fin N) (x y : ℝ) :
    P.rawBand (P.restrictCoefficient coeff lower upper) jet j x y =
      if lower ≤ j.val ∧ j.val < upper then P.rawBand coeff jet j x y else 0 := by
  by_cases hj : lower ≤ j.val ∧ j.val < upper
  · simp [rawBand, restrictCoefficient, hj]
  · simp only [rawBand, restrictCoefficient, hj, ite_false, if_false]
    ext k
    simp only [vectorPacketSynthesis, packetSynthesis_apply, PiLp.zero_apply,
      zero_mul, Finset.sum_const_zero]

theorem restricted_rawInterval_eq (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lengthLower lengthUpper : ℕ) (jet : Fin 3) (lower upper : ℕ)
    (hlu : lower ≤ upper) (hu : upper ≤ N) (x y : ℝ) :
    ∃ l u : ℕ, l ≤ u ∧ u ≤ N ∧
      P.rawInterval (P.restrictCoefficient coeff lengthLower lengthUpper) jet lower upper x y =
        P.rawInterval coeff jet l u x y := by
  let l := min N (max lower lengthLower)
  let u := max l (min upper lengthUpper)
  have hlN : l ≤ N := min_le_left _ _
  have hlu' : l ≤ u := le_max_left _ _
  have huN : u ≤ N := max_le hlN ((min_le_left _ _).trans hu)
  refine ⟨l,u,hlu',huN,?_⟩
  rw [P.rawInterval_eq_band_sum _ jet lower upper hlu x y,
    P.rawInterval_eq_band_sum _ jet l u hlu' x y]
  simp_rw [P.rawBand_restrictCoefficient]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp only [l,u]
  have hjN := j.isLt
  omega

/-- Every restricted source interval is an original interval, including
when the two length ranges are disjoint. -/
theorem restricted_rawInterval_bound (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lengthLower lengthUpper : ℕ) (jet : Fin 3) (x y B : ℝ)
    (hbound : ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖P.rawInterval coeff jet lower upper x y‖ ≤ B) :
    ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖P.rawInterval (P.restrictCoefficient coeff lengthLower lengthUpper)
        jet lower upper x y‖ ≤ B := by
  intro lower upper hlu hu
  obtain ⟨l,u,hlu',hu',heq⟩ := P.restricted_rawInterval_eq coeff lengthLower lengthUpper
    jet lower upper hlu hu x y
  rw [heq]
  exact hbound l u hlu' hu'

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedAmplitude
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original length restrictions and the common top mask in the actual
source analytic amplitude. Small masks retain their full gain when the
single-top bounds are summed over an eligible angular node. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

variable {ι X : Type*}

theorem sourcePacketAmplitude_smul_value {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (top : σ → ι) (stop : σ → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (z : X) (level : ℕ) (cell : ℤ) (q : ℂ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets top stop
      (fun p => q • value p) phase a z level cell =
      q • g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets top stop
        value phase a z level cell := by
  unfold sourcePacketAmplitude packetAmplitude sourcePacketBase
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [smul_smul]
  congr 1
  ring

/-- The bound uses the original analyzing coefficients and their interval
concentration, even after any interval of original lengths is retained. -/
theorem sourcePacketAmplitude_masked_restricted_envelope
    (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i z, 0 < weight i z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : grid.eligible cutoff (precision top) M) (z : X)
    (a Z : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (x y B C : ℝ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hweight : weight top z ≤ C)
    (hinterval : ∀ l u, l ≤ u → u ≤ N →
      ‖P.rawInterval coeff jet l u x y‖ ≤ B*(weight top z)^8)
    (lower upper : ℕ) (q : ℂ) :
    ‖grid.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
      (fun _ : Fin N => top) stop
      (fun j => q • P.rawBand (P.restrictCoefficient coeff lower upper) jet j x y)
      phase a z start (grid.index start (slope top))‖ ≤
      (C^8*B*(1+(a+Z*K)*(Real.log (max 1 (∑ i ∈ tops, weight i z))+1))) *
        ‖q‖*(weight top z)^4 := by
  rw [grid.sourcePacketAmplitude_smul_value, norm_smul]
  have hb := grid.sourcePacketAmplitude_fourth_envelope tops slope precision cutoff weight
    hp hw hK gap phase M top htop he z a Z ha0 ha1 hZ hz0 hz P
    (P.restrictCoefficient coeff lower upper) jet stop hstop start hstart hmax x y B C
    hB hC hweight (P.restricted_rawInterval_bound coeff lower upper jet x y
      (B*(weight top z)^8) hinterval)
  calc
    _ ≤ ‖q‖*((C^8*B*(1+(a+Z*K)*
        (Real.log (max 1 (∑ i ∈ tops, weight i z))+1)))*(weight top z)^4) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg q)
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeAssembly
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
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

/-- The complete source family satisfies the linear node-mass envelope,
including arbitrary original-length restrictions and insignificant masks. -/
theorem sourcePacketAmplitude_node_envelope (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t z, 0 < weight t z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ι → ℕ) (hM : ∀ t ∈ tops, grid.eligible cutoff (precision t) (M t))
    (hMmax : ∀ t ∈ tops, ∀ k, grid.eligible cutoff (precision t) k → k ≤ M t)
    (a Z : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re)
    (hz : ∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : ι → Fin N → ℕ)
    (hstop : ∀ t ∈ tops, Antitone (stop t))
    (hmax : ∀ t ∈ tops, ∀ j, stop t j ≤ M t)
    (x y : ι → ℝ) (B C ε : ℝ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hε : 0 ≤ ε)
    (z : X) (hweight : ∀ t ∈ tops, weight t z ≤ C)
    (hinterval : ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
      ‖(P t).rawInterval (coeff t) jet l u (x t) (y t)‖ ≤ B*(weight t z)^8)
    (lower upper : ℕ) (q : ι → ℂ) (level : ℕ) (cell : ℤ)
    (hq : ∀ t ∈ grid.cellTops tops slope precision cutoff level cell, ‖q t‖ ≤ ε) :
    ‖grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => q p.1 • (P p.1).rawBand
        ((P p.1).restrictCoefficient (coeff p.1) lower upper) jet p.2 (x p.1) (y p.1))
      phase a z level cell‖ ≤
      (C^8*B*(1+(a+Z*K)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*ε*C^3) *
        grid.mass tops slope precision cutoff weight level cell z := by
  let A := C^8*B*(1+(a+Z*K)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))
  have hlog : 0 ≤ Real.log (max 1 (∑ t ∈ tops, weight t z)) :=
    Real.log_nonneg (le_max_left _ _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he (t : ι) (ht : t ∈ tops) (j : Fin N) (_hj : j ∈ Finset.univ) :
      grid.eligible cutoff (precision t) (stop t j) :=
    grid.eligible_of_le (hp t ht) (hmax t ht j) (hM t ht)
  rw [grid.sourcePacketAmplitude_top_fibers tops slope precision cutoff weight hp K gap
    Finset.univ stop (fun t j => q t • (P t).rawBand
      ((P t).restrictCoefficient (coeff t) lower upper) jet j (x t) (y t))
    he phase a z level cell]
  apply grid.node_amplitude_fourth_envelope tops slope precision cutoff weight _
    level cell z (A*ε) C (mul_nonneg hA hε)
  · intro t _
    exact (hw t z).le
  · intro t ht
    exact hweight t ((grid.mem_cellTops _ _ _ _ _ _ _).mp ht).1
  · intro t ht
    obtain ⟨htt,hcell,hel⟩ := (grid.mem_cellTops _ _ _ _ _ _ _).mp ht
    have hb := grid.sourcePacketAmplitude_masked_restricted_envelope tops slope precision
      cutoff weight hp hw hK gap phase (M t) t htt (hM t htt) z a Z ha0 ha1 hZ
      (hz0 t htt) (hz t htt) (P t) (coeff t) jet (stop t) (hstop t htt) level
      (hMmax t htt level hel) (hmax t htt) (x t) (y t) B C hB hC (hweight t htt)
      (hinterval t htt) lower upper (q t)
    have hq' : ‖q t‖ ≤ ε := hq t ((grid.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htt,hcell,hel⟩)
    calc
      _ ≤ A*‖q t‖*(weight t z)^4 := hb
      _ ≤ A*ε*(weight t z)^4 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq' hA) (by positivity)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSnapshotSize
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Snapshot sizes for the source prediction. The node bound retains
the original coefficient family; normalization costs only the parent mass
raised to the small phase exponent. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem restrictCoefficient_full (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    P.restrictCoefficient coeff 0 N = coeff := by
  funext j l u
  simp only [restrictCoefficient, Nat.zero_le, j.isLt, and_self, ite_true, if_true]

end SourceLabeledLattice

namespace AngularGrid
attribute [local instance] Classical.propDecidable

/-- Full length range, with the actual endpoint masks placed in the
original coefficients. No bound on the number of tops is used. -/
theorem source_snapshot_masked_node_bound {ι X : Type*}
    (grid : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t z, 0 < weight t z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ι → ℕ) (hM : ∀ t ∈ tops, grid.eligible cutoff (precision t) (M t))
    (hMmax : ∀ t ∈ tops, ∀ k, grid.eligible cutoff (precision t) k → k ≤ M t)
    (a Z : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re)
    (hz : ∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : ι → Fin N → ℕ) (hstop : ∀ t ∈ tops, Antitone (stop t))
    (hmax : ∀ t ∈ tops, ∀ j, stop t j ≤ M t) (x y : ι → ℝ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 1 ≤ C) (z : X)
    (hweight : ∀ t ∈ tops, weight t z ≤ C)
    (hinterval : ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
      ‖(P t).rawInterval (coeff t) jet l u (x t) (y t)‖ ≤ A*(weight t z)^8)
    (q : ι → ℝ) (level : ℕ) (cell : ℤ)
    (hq : ∀ t ∈ tops, |q t| ≤ 1) :
    ‖grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => (P p.1).rawBand (fun j l u => q p.1 • coeff p.1 j l u)
        jet p.2 (x p.1) (y p.1)) phase a z level cell‖ ≤
      (C^8*A*(1+(a+Z*K)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*C^3)*
        grid.mass tops slope precision cutoff weight level cell z := by
  have hmasked (t : ι) (ht : t ∈ tops) (l u : ℕ) (hlu : l ≤ u) (hu : u ≤ N) :
      ‖(P t).rawInterval (fun j k v => q t • coeff t j k v) jet l u (x t) (y t)‖ ≤
        A*(weight t z)^8 := by
    rw [(P t).rawInterval_coeff_smul, norm_smul, Real.norm_eq_abs]
    have hb := mul_le_mul (hq t ht) (hinterval t ht l u hlu hu) (norm_nonneg _) zero_le_one
    simpa only [one_mul] using hb
  have hb := grid.sourcePacketAmplitude_node_envelope tops slope precision cutoff weight hp hw
    hK gap phase M hM hMmax a Z ha0 ha1 hZ hz0 hz P
    (fun t j l u => q t • coeff t j l u) jet stop hstop hmax x y A C 1
    hA hC zero_le_one z hweight hmasked 0 N (fun _ => (1:ℂ)) level cell
    (fun _ _ => by simp)
  simpa only [SourceLabeledLattice.restrictCoefficient_full, mul_one, one_smul] using hb

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSnapshotPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source snapshot envelope is a fixed polynomial in L.
This supplies the unnormalized size input for the normalized-motion theorem. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem source_snapshot_envelope_polynomial {L C A q a Z S : ℝ} {K : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (_hA : 0 ≤ A) (hAq : A ≤ L^q)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 2*L^2)
    (hK : (K:ℝ) ≤ L^2) (hS : Real.log (max 1 S) ≤ 3*L) :
    (C^8*A*(1+(a+Z*K)*(Real.log (max 1 S)+1)))*C^3 ≤
      (13*C^11)*L^(q+5) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  have hL5 : 1 ≤ L^5 := one_le_pow₀ hL
  have hZK : Z*K ≤ 2*L^4 := by
    have hb := mul_le_mul hZ hK (Nat.cast_nonneg K) (by positivity : 0 ≤ 2*L^2)
    nlinarith
  have hlog : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hfirst : a+Z*K ≤ 3*L^4 := by linarith
  have hsecond : Real.log (max 1 S)+1 ≤ 4*L := by linarith
  have hcore : 1+(a+Z*K)*(Real.log (max 1 S)+1) ≤ 13*L^5 := by
    have hb := mul_le_mul hfirst hsecond (by positivity : 0 ≤ Real.log (max 1 S)+1)
      (by positivity : 0 ≤ 3*L^4)
    nlinarith
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hAq (by positivity : 0 ≤ C^8)) hcore
      (by positivity : 0 ≤ 1+(a+Z*K)*(Real.log (max 1 S)+1))
      (by positivity : 0 ≤ C^8*L^q)) (by positivity : 0 ≤ C^3)
  calc
    _ ≤ (C^8*L^q*(13*L^5))*C^3 := hbound
    _ = (13*C^11)*(L^q*L^(5:ℕ)) := by ring
    _ = _ := by
      rw [← Real.rpow_natCast L 5,← Real.rpow_add hL0]
      norm_num only [Nat.cast_ofNat]

theorem eventually_source_snapshot_envelope (C q : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (A a Z S : ℝ) (K : ℕ),
      0 ≤ A → A ≤ L^q → 0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 →
      (K:ℝ) ≤ L^2 → Real.log (max 1 S) ≤ 3*L →
      (C^8*A*(1+(a+Z*K)*(Real.log (max 1 S)+1)))*C^3 ≤ L^(q+6) := by
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (13*C^11)] with L hL hconst
  intro A a Z S K hA hAq ha0 ha1 hZ0 hZ hK hS
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  calc
    _ ≤ (13*C^11)*L^(q+5) :=
      source_snapshot_envelope_polynomial hL hC hA hAq ha0 ha1 hZ0 hZ hK hS
    _ ≤ L*L^(q+5) := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hL0.le _)
    _ = L^(1:ℝ)*L^(q+5) := by rw [Real.rpow_one]
    _ = L^((1:ℝ)+(q+5)) := (Real.rpow_add hL0 _ _).symm
    _ = L^(q+6) := by congr 1; ring

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smaller fixed power gain used after mass normalization in the
prediction argument. The constants and polynomial exponents remain fixed. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem relative_exponential_error_le {E B : ℝ} (hE : E ≤ 1)
    (hbound : E ≤ B) (hE0 : 0 ≤ E) : Real.exp E*E ≤ Real.exp 1*B :=
  mul_le_mul (Real.exp_le_exp.mpr hE) hbound hE0 (Real.exp_pos 1).le

/-- Packet motion of order `G^(-1/4)` and any fixed polynomial times
`G^(-1/2)` from the mass factors leave a uniform `G^(-1/8)` gain. -/
theorem eventually_source_rescaled_motion (B b c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ η q C : ℝ,
      0 ≤ η → η ≤ SourceParameters.step L^(-(1/4:ℝ)) →
      0 ≤ q → q ≤ B*L^b/Real.sqrt (SourceParameters.step L) →
      0 ≤ C → C ≤ L^c →
      (1+q)*η+q*C ≤ SourceParameters.step L^(-(1/8:ℝ)) := by
  have hpoly := eventually_source_polynomial_motion (2*B) (b+c)
  have hpower := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    source_step_tendsto_atTop).eventually_ge_atTop 2
  filter_upwards [hpoly,hpower,eventually_ge_atTop (1:ℝ)] with L hpoly hpower hL
  intro η q C hη0 hη hq0 hq hC0 hC
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hG0 := SourceParameters.step_pos L
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hη1 : η ≤ 1 := hη.trans (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num))
  have hc1 : 1 ≤ L^c := Real.one_le_rpow hL hc
  have hCsum : η+C ≤ 2*L^c := by linarith
  have hsmall : 2*SourceParameters.step L^(-(1/4:ℝ)) ≤
      SourceParameters.step L^(-(1/8:ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hpower
      (Real.rpow_nonneg hG0.le (-(1/4:ℝ)))
    have heq : SourceParameters.step L^(1/8:ℝ)*
        SourceParameters.step L^(-(1/4:ℝ)) =
        SourceParameters.step L^(-(1/8:ℝ)) := by
      rw [← Real.rpow_add hG0]
      norm_num
    exact hm.trans_eq heq
  calc
    _ = η+q*(η+C) := by ring
    _ ≤ SourceParameters.step L^(-(1/4:ℝ))+
        (B*L^b/Real.sqrt (SourceParameters.step L))*(2*L^c) :=
      add_le_add hη (mul_le_mul hq hCsum (by positivity) (by positivity))
    _ = SourceParameters.step L^(-(1/4:ℝ))+
        (2*B)*L^(b+c)/Real.sqrt (SourceParameters.step L) := by
      rw [Real.rpow_add hL0]
      ring
    _ ≤ SourceParameters.step L^(-(1/4:ℝ))+SourceParameters.step L^(-(1/4:ℝ)) :=
      add_le_add le_rfl hpoly
    _ = 2*SourceParameters.step L^(-(1/4:ℝ)) := by ring
    _ ≤ _ := hsmall

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNormalizedDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the source parameters, the exact mass-rescaling errors are
bounded by a fixed polynomial times the inverse square root of the step. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem source_scale_exponent_bound {p μ : ℝ} (hp : 1 ≤ p)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) : |-(1/p)|+|μ-1+1/p| ≤ 2 := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hi0 : 0 ≤ 1/p := by positivity
  have hi1 : 1/p ≤ 1 := (div_le_one hp0).mpr hp
  have ha : |μ-1+1/p| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [abs_neg,abs_of_nonneg hi0]
  linarith

theorem eventually_source_mass_rescaling_error (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ p μ Kw : ℝ, 1 ≤ p → 0 ≤ μ → μ ≤ 1 → 1 ≤ Kw →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let e := (|-(1/p)|+|μ-1+1/p|)*δ
      Real.exp e*e ≤ (10*D*Real.exp 1)/Real.sqrt (SourceParameters.step L) := by
  have hroot := (Real.tendsto_sqrt_atTop.comp source_step_tendsto_atTop).eventually_ge_atTop (10*D)
  filter_upwards [hroot] with L hroot
  change 10*D ≤ Real.sqrt (SourceParameters.step L) at hroot
  intro p μ Kw hp hμ0 hμ1 hKw
  dsimp only
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hs : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hδ0 : 0 ≤ (5*D/Kw)/Real.sqrt (SourceParameters.step L) := by positivity
  have he : (|-(1/p)|+|μ-1+1/p|)*((5*D/Kw)/Real.sqrt (SourceParameters.step L)) ≤
      (10*D)/Real.sqrt (SourceParameters.step L) := by
    calc
      _ ≤ 2*((5*D/Kw)/Real.sqrt (SourceParameters.step L)) :=
        mul_le_mul_of_nonneg_right (source_scale_exponent_bound hp hμ0 hμ1) hδ0
      _ ≤ 2*((5*D)/Real.sqrt (SourceParameters.step L)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (div_le_self (by positivity) hKw) hs.le) (by norm_num)
      _ = _ := by ring
  have he1 := he.trans ((div_le_one hs).mpr hroot)
  have hb := relative_exponential_error_le he1 he (by positivity)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem eventually_source_transition_error (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ (steps : ℕ) (Z Kw : ℝ),
      (steps:ℝ) ≤ L^2 → 0 ≤ Z → Z ≤ 2*L^2 → 1 ≤ Kw →
      let e := (steps:ℝ)*Z*(2*((5*D/Kw)/Real.sqrt (SourceParameters.step L)))
      Real.exp e*e ≤ (20*D*Real.exp 1)*L^4/Real.sqrt (SourceParameters.step L) := by
  have hsmall := eventually_source_polynomial_motion (20*D) 4
  filter_upwards [hsmall] with L hsmall
  intro steps Z Kw hsteps hZ0 hZ hKw
  dsimp only
  have hs : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hstepZ : (steps:ℝ)*Z ≤ 2*L^4 := by
    have hb := mul_le_mul hsteps hZ hZ0 (sq_nonneg L)
    nlinarith
  have he : (steps:ℝ)*Z*(2*((5*D/Kw)/Real.sqrt (SourceParameters.step L))) ≤
      (20*D)*L^4/Real.sqrt (SourceParameters.step L) := by
    calc
      _ ≤ (2*L^4)*(2*((5*D)/Real.sqrt (SourceParameters.step L))) :=
        mul_le_mul hstepZ
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (div_le_self (by positivity) hKw) hs.le) (by norm_num))
          (by positivity) (by positivity)
      _ = _ := by ring
  rw [Real.rpow_ofNat] at hsmall
  have he1 := he.trans (hsmall.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)))
  have hb := relative_exponential_error_le he1 he (by positivity)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- Multiplying the parent-mass and transition factors preserves the
same polynomial inverse-square-root scale. -/
theorem eventually_source_relative_product (B b : ℝ) (_hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      q ≤ B*L^b/Real.sqrt (SourceParameters.step L) →
      r ≤ B*L^b/Real.sqrt (SourceParameters.step L) →
      q+r+q*r ≤ (3*B)*L^b/Real.sqrt (SourceParameters.step L) := by
  filter_upwards [eventually_source_polynomial_motion B b] with L hsmall
  intro q r hq0 hr0 hq hr
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hsmall1 : B*L^b/Real.sqrt (SourceParameters.step L) ≤ 1 := hsmall.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num))
  have hr1 : r ≤ 1 := hr.trans hsmall1
  have hqr : q*r ≤ q := by nlinarith
  calc
    _ ≤ 2*q+r := by linarith
    _ ≤ 2*(B*L^b/Real.sqrt (SourceParameters.step L))+
        B*L^b/Real.sqrt (SourceParameters.step L) := by linarith
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNormalizedMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mass normalization of the proved physical amplitude power gain.
The local input is the raw physical motion, before multiplying by any
mass power or hierarchy transition. No normalized motion is assumed. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

/-- Both exact normalization coefficients have the smaller fixed power
gain, uniformly over the source phase and block parameters. -/
theorem eventually_source_normalization_coefficients (D Q : ℝ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw p μ : ℝ) (steps : ℕ) (Z : ℝ),
      1 ≤ Kw → 1 ≤ p → 0 ≤ μ → μ ≤ 1 →
      (steps:ℝ) ≤ L^2 → 0 ≤ Z → Z ≤ 2*L^2 →
      let G := SourceParameters.step L
      let δ := (5*D/Kw)/Real.sqrt G
      let es := (|-(1/p)|+|μ-1+1/p|)*δ
      let qs := Real.exp es*es
      let en := |μ-1| * δ
      let qn := Real.exp en*en
      let el := (steps:ℝ)*Z*(2*δ)
      let ql := Real.exp el*el
      let qt := qn+ql+qn*ql
      ((1+qs)*G^(-(1/4:ℝ))+qs*L^Q ≤ G^(-(1/8:ℝ))) ∧
      ((1+qt)*G^(-(1/4:ℝ))+qt*L^Q ≤ G^(-(1/8:ℝ))) := by
  have hs := eventually_source_mass_rescaling_error D hD
  have ht := eventually_source_transition_error D hD
  have hp := eventually_source_relative_product (20*D*Real.exp 1) 4 (by positivity)
  have hds := eventually_source_rescaled_motion (10*D*Real.exp 1) 0 Q (by positivity) hQ
  have hdt := eventually_source_rescaled_motion (3*(20*D*Real.exp 1)) 4 Q (by positivity) hQ
  filter_upwards [hs,ht,hp,hds,hdt,eventually_ge_atTop (1:ℝ)] with L hs ht hp hds hdt hL
  intro Kw p μ steps Z hKw hp1 hμ0 hμ1 hsteps hZ0 hZ
  dsimp only
  let G := SourceParameters.step L
  let δ := (5*D/Kw)/Real.sqrt G
  let en := |μ-1| * δ
  let qn := Real.exp en*en
  let el := (steps:ℝ)*Z*(2*δ)
  let ql := Real.exp el*el
  have hG : 0 < G := SourceParameters.step_pos L
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hqn0 : 0 ≤ qn := by dsimp [qn,en]; positivity
  have hql0 : 0 ≤ ql := by dsimp [ql,el]; positivity
  have hmu : |μ-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : en ≤ (|-(1/(1:ℝ))|+|μ-1+1/(1:ℝ)|)*δ := by
    apply mul_le_mul_of_nonneg_right _ hδ
    refine hmu.trans ?_
    have hb : (1:ℝ) ≤ 1+|μ-1+1/(1:ℝ)| :=
      le_add_of_nonneg_right (abs_nonneg _)
    simpa only [div_one,abs_neg,abs_one] using hb
  have hqn : qn ≤ (10*D*Real.exp 1)/Real.sqrt G := by
    exact (mul_le_mul (Real.exp_le_exp.mpr he) he
      (by dsimp [en]; positivity) (Real.exp_pos _).le).trans
      (hs 1 μ Kw (by norm_num) hμ0 hμ1 hKw)
  have hL4 : (1:ℝ) ≤ L^4 := one_le_pow₀ hL
  have hqnPoly : qn ≤ (20*D*Real.exp 1)*L^4/Real.sqrt G := by
    apply hqn.trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg G)
    have hx := mul_le_mul_of_nonneg_left hL4 (show 0 ≤ 20*D*Real.exp 1 by positivity)
    nlinarith [show 0 ≤ D*Real.exp 1 by positivity]
  have hqlPoly : ql ≤ (20*D*Real.exp 1)*L^4/Real.sqrt G :=
    ht steps Z Kw hsteps hZ0 hZ hKw
  have hprod := hp qn ql hqn0 hql0
    (by simpa only [Real.rpow_ofNat] using hqnPoly)
    (by simpa only [Real.rpow_ofNat] using hqlPoly)
  constructor
  · apply hds _ _ (L^Q) (by positivity) le_rfl (by positivity)
      (by simpa only [Real.rpow_zero,mul_one] using hs p μ Kw hp1 hμ0 hμ1 hKw)
      (by positivity) le_rfl
  · exact hdt _ _ (L^Q) (by positivity) le_rfl (by positivity) hprod
      (by positivity) le_rfl

/-- The source raw amplitude power gain, physical mass log motion and
actual transition quotient estimate imply both normalized motion bounds.
The raw bound is the conclusion of `source_physical_amplitude_power_gain`. -/
theorem eventually_source_normalized_motion
    (D Q : ℝ) (hD : 0 ≤ D) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (κ : Type) [Fintype κ],
    ∀ (Kw p μ n n' c c' : ℝ) (steps : ℕ) (Z : ℝ),
      1 ≤ Kw → 1 ≤ p → 0 ≤ μ → μ ≤ 1 →
      0 < n → 0 < n' → 0 < c → 0 < c' →
      (steps:ℝ) ≤ L^2 → 0 ≤ Z → Z ≤ 2*L^2 →
    ∀ (frequency : κ → ℝ) (b : ℝ) (A A' : EuclideanSpace ℂ κ) (lam lam' : ℂ),
      lam ≠ 0 → ‖lam‖ ≤ 1 →
      let G := SourceParameters.step L
      let δ := (5*D/Kw)/Real.sqrt G
      let el := (steps:ℝ)*Z*(2*δ)
      |Real.log n'-Real.log n| ≤ δ →
      |Real.log c'-Real.log c| ≤ δ →
      ‖A‖ ≤ L^Q*c →
      ‖A'-diagonalModulation frequency A b‖ ≤ G^(-(1/4:ℝ))*c →
      ‖lam'/lam-1‖ ≤ Real.exp el*el →
      (‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
        diagonalModulation frequency (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b‖ ≤
        G^(-(1/8:ℝ))*(c/n)^(1/p)*c^μ) ∧
      (‖((n'^(μ-1):ℝ):ℂ) • (lam' • A')-
        ((n^(μ-1):ℝ):ℂ) • (lam • diagonalModulation frequency A b)‖ ≤
        G^(-(1/8:ℝ))*n^μ*(c/n)) := by
  filter_upwards [eventually_source_normalization_coefficients D Q hD hQ,
    eventually_ge_atTop (1:ℝ)] with L hcoeff hL
  intro κ _ Kw p μ n n' c c' steps Z hKw hp hμ0 hμ1 hn hn' hc hc' hsteps hZ0 hZ
    frequency b A A' lam lam' hlam0 hlam
  dsimp only
  intro hN hchild hA hraw hlamMove
  let G := SourceParameters.step L
  let δ := (5*D/Kw)/Real.sqrt G
  let el := (steps:ℝ)*Z*(2*δ)
  let ql := Real.exp el*el
  have hG : 0 < G := SourceParameters.step_pos L
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hcoeff' := hcoeff Kw p μ steps Z hKw hp hμ0 hμ1 hsteps hZ0 hZ
  have hbase : ‖diagonalModulation frequency A b‖ ≤ L^Q*c := by
    simpa only [norm_diagonalModulation] using hA
  have hscaled := massPowerScale_amplitude_motion hn hn' hc hc' hδ
    (show 0 ≤ G^(-(1/4:ℝ)) by positivity) (show 0 ≤ L^Q by positivity)
    hN hchild (-(1/p)) (μ-1+1/p) A' (diagonalModulation frequency A b) hbase hraw
  have hlamAbs : ‖lam'-lam‖ ≤ ql := by
    have hm := complex_relative_motion_to_sub hlam0 hlamMove
    exact hm.trans ((mul_le_mul_of_nonneg_left hlam (show 0 ≤ ql by dsimp [ql,el]; positivity)).trans_eq
      (mul_one ql))
  have hnum := prediction_numerator_motion hn hn' hc.le hδ
    (show 0 ≤ ql by dsimp [ql,el]; positivity)
    (show 0 ≤ G^(-(1/4:ℝ)) by positivity) (show 0 ≤ L^Q by positivity)
    hN μ lam lam' hlam hlamAbs A' (diagonalModulation frequency A b) hbase hraw
  constructor
  · have hcomm : diagonalModulation frequency
        (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b =
        massPowerScale n c (-(1/p)) (μ-1+1/p) • diagonalModulation frequency A b :=
      (diagonalModulationRealIsometry frequency b).map_smul _ _
    rw [hcomm]
    apply hscaled.trans
    have hb := mul_le_mul_of_nonneg_right hcoeff'.1
      (show 0 ≤ (c/n)^(1/p)*c^μ by positivity)
    rw [mul_assoc,prediction_mass_scale_identity hn hc]
    simpa only [mul_assoc] using hb
  · exact hnum.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff'.2 (Real.rpow_nonneg hn.le μ))
      (div_pos hc hn).le)

end LipschitzHilbert

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


theorem source_supported_selector_amplitude_power_gain (p q : ℝ) (D Bslots : ℕ) (C Cfreq : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hC : 1 ≤ C) (hCfreq : 0 ≤ Cfreq) :
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
    (g.branching:ℝ) = SourceParameters.step L →
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → (Kb:ℝ) ≤ L^2 → ∀ (gap : ℕ → ℝ) (h start : ℕ), h ≤ start →
    ∀ (M : ι → ℕ),
    (∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t)) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t) →
    (∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h) →
    ∀ (sR : ℝ) (cell : ℤ),
    (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) start cell, g.index h (T t).slope = g.index h sR) →
    g.width h ≤ B*g.width start →
    ∀ (b : ℝ), |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)) →
    ∀ (z : ℝ × ℝ) (frequency : κ → ℝ),
    (∀ k, |frequency k| ≤ Cfreq/w) → (∀ t ∈ tops, (P t).frequency = frequency) →
    ∀ (phase : ℕ → ℂ) (a Z A maskExponent : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 ≤ maskExponent →
    (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
    (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    (∀ t ∈ tops, (T t).weight Kw (D:ℝ) z ≤ C) → 0 ≤ A → A ≤ L^q →
    Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (D:ℝ) z)) ≤ 3*L →
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
      (SourceParameters.step L)^(-(1/4:ℝ))*
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/B^2) weight start cell z := by
  obtain ⟨Lbase,hbase1,hbaseSlots,hphysical⟩ := source_supported_selector_amplitude_motion p D Bslots
  obtain ⟨Ldecay,hdecay⟩ := Filter.eventually_atTop.mp
    (eventually_source_predictable_coefficient p q (D:ℝ) C Cfreq hp hq (Nat.cast_nonneg D) hC hCfreq)
  refine ⟨max Lbase Ldecay, hbase1.trans (le_max_left _ _),
    hbaseSlots.trans (le_max_left _ _), ?_⟩
  intro L hLL ι tops T N κ Label Item _ _ P hcard hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w B hw hB hbranch hwidth hlength hzero Kb hKb hK gap h start hbase
    M hM hMmax hgap sR cell hs hblock b hb z frequency hfreq hPfreq phase a Z A maskExponent
    ha0 ha1 hZ hZL hmask hz0 hz htC hA hAL htotal
  dsimp only
  intro hconc
  have hraw := hphysical L ((le_max_left _ _).trans hLL) ι tops T N κ Label Item P hcard hP
    alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w B hw hB hwidth hlength hzero
    Kb hKb gap h start hbase M hM hMmax hgap sR cell hs hblock b hb z frequency Cfreq
    hCfreq hfreq hPfreq phase a Z C A maskExponent ha0 ha1 hZ hz0 hz hC htC hA hconc
  have hbudget := hdecay L ((le_max_right _ _).trans hLL) A maskExponent Kw
    (∑ t ∈ tops, (T t).weight Kw (D:ℝ) z) a Z Kb hA hAL hmask hKw ha0 ha1 hZ hZL hK htotal
  rw [← hbranch] at hbudget
  simpa only [hbranch] using hraw.trans (mul_le_mul_of_nonneg_right hbudget
    (g.mass_nonnegative tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) (fun t zz => (T t).weight Kw (D:ℝ) zz)
      (fun t zz => ((T t).weight_pos (zero_lt_one.trans_le hKw) _ zz).le) start cell z))


theorem source_supported_selector_normalized_motion_oai (p q : ℝ) (D Bslots : ℕ) (C Cfreq : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hC : 1 ≤ C) (hCfreq : 0 ≤ Cfreq) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots:ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → SourceLabeledLattice N κ Label Item),
    (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
    (∀ t ∈ tops, (P t).constant ≤ L^p) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound) (Kw : ℝ), 1 ≤ Kw →
    (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw D) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w B : ℝ) (hw : 0 < w), 1 ≤ B →
    (g.branching:ℝ) = SourceParameters.step L →
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → (Kb:ℝ) ≤ L^2 → ∀ (gap : ℕ → ℝ) (h start : ℕ), h ≤ start →
    ∀ (M : ι → ℕ),
    (∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t)) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t) →
    (∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h) →
    ∀ (sR : ℝ) (cell : ℤ),
    (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) start cell, g.index h (T t).slope = g.index h sR) →
    g.width h ≤ B*g.width start →
    ∀ (b : ℝ), |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)) →
    ∀ (z : ℝ × ℝ) (frequency : κ → ℝ),
    (∀ k, |frequency k| ≤ Cfreq/w) → (∀ t ∈ tops, (P t).frequency = frequency) →
    ∀ (phase : ℕ → ℂ) (a Z A maskExponent : ℝ),
    0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 ≤ maskExponent →
    (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
    (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    (∀ t ∈ tops, (T t).weight Kw (D:ℝ) z ≤ C) →
    0 ≤ A → A ≤ L^q →
    Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (D:ℝ) z)) ≤ 3*L →
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
    ∀ (lower : ℕ), h ≤ lower → lower ≤ start → ((start-lower:ℕ):ℝ) ≤ L^2 →
    ∀ (top : ι), top ∈ g.cellTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) start cell →
    ∀ (r μ : ℝ), 1 ≤ r → 0 ≤ μ → μ ≤ 1 →
    let value := fun zz t j => (Q t).rawBand
      (fun j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 j
      zz.1 (zz.2-(T t).slope*zz.1)
    let amplitude := fun zz => g.sourcePacketAmplitude tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => value zz p.1 p.2) phase a zz start cell
    let parentMass := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight lower (g.index lower (T top).slope) zz
    let childMass := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight start cell zz
    let lam := fun zz => g.packetPathProduct (g.sourceTransition tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap phase zz)
      lower start (T top).slope
    let z' := SlopeBox.lineShift sR b z
    let carrier := (sR-g.center start cell)*b
    (‖massPowerScale (parentMass z') (childMass z') (-(1/r)) (μ-1+1/r) • amplitude z'-
        diagonalModulation frequency
          (massPowerScale (parentMass z) (childMass z) (-(1/r)) (μ-1+1/r) • amplitude z)
          carrier‖ ≤
      SourceParameters.step L^(-(1/8:ℝ))*(childMass z/parentMass z)^(1/r)*(childMass z)^μ) ∧
    (‖(((parentMass z')^(μ-1):ℝ):ℂ) • (lam z' • amplitude z')-
        (((parentMass z)^(μ-1):ℝ):ℂ) •
          (lam z • diagonalModulation frequency (amplitude z) carrier)‖ ≤
      SourceParameters.step L^(-(1/8:ℝ))*(parentMass z)^μ*(childMass z/parentMass z)) := by
  obtain ⟨Lp,hLp,hSlots,hphysical⟩ := source_supported_selector_amplitude_power_gain p q D Bslots C Cfreq
    hp hq hC hCfreq
  obtain ⟨Ln,hnormal⟩ := eventually_atTop.mp
    (eventually_source_normalized_motion (D:ℝ) (q+6) (Nat.cast_nonneg D) (by linarith))
  obtain ⟨Ls,hsnapshot⟩ := eventually_atTop.mp (eventually_source_snapshot_envelope C q (by linarith))
  refine ⟨max Lp (max Ln Ls),hLp.trans (le_max_left _ _),hSlots.trans (le_max_left _ _),?_⟩
  intro L hLL ι tops T N κ Label Item _ _ P hcard hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w B hw hB hbranch hwidth hlength hzero Kb hKb hKbL gap h start hbase
    M hM hMmax hgap sR cell hs hblock b hb z frequency hfreq hPfreq phase a Z A maskExponent
    ha0 ha1 hZ hZL hmask hz0 hz htC hA hAL htotal
  dsimp only
  intro hconc lower hhlower hlower hsteps top htopCell r μ hr hμ0 hμ1
  have hLnL : Ln ≤ L := (le_max_left Ln Ls).trans ((le_max_right Lp _).trans hLL)
  have hLsL : Ls ≤ L := (le_max_right Ln Ls).trans ((le_max_right Lp _).trans hLL)
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff0 := g.rootWidth/B^2
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible cutoff0 (w/(P t).length j) (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
  let value := fun zz t j => (Q t).rawBand
    (fun j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 j
    zz.1 (zz.2-slope t*zz.1)
  let amplitude := fun zz => g.sourcePacketAmplitude tops slope precision cutoff0 weight Kb gap
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => rawStop p.1 p.2)
    (fun p => value zz p.1 p.2) phase a zz start cell
  let n := fun zz => g.mass tops slope precision cutoff0 weight lower (g.index lower (slope top)) zz
  let c := fun zz => g.mass tops slope precision cutoff0 weight start cell zz
  let lam := fun zz => g.packetPathProduct (g.sourceTransition tops slope precision cutoff0 weight Kb gap phase zz)
    lower start (slope top)
  let z' := SlopeBox.lineShift sR b z
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hprec (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hwpos (t : ι) (zz : ℝ × ℝ) : 0 < weight t zz := (T t).weight_pos hKw0 _ zz
  obtain ⟨htop,hindex,heligible⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp htopCell
  have htopM : start ≤ M top := hMmax top htop start heligible
  have hn (zz : ℝ × ℝ) : 0 < n zz :=
    g.path_mass_pos tops slope precision cutoff0 weight hwpos lower top htop
      (g.eligible_of_le (hprec top htop) hlower heligible) zz
  have hc (zz : ℝ × ℝ) : 0 < c zz :=
    g.mass_pos_of_member tops slope precision cutoff0 weight hwpos start cell zz htopCell
  have hlog (level : ℕ) (hlevel : h ≤ level) (helevel : g.eligible cutoff0 (precision top) level) :
      |Real.log (g.mass tops slope precision cutoff0 weight level (g.index level (slope top)) z')-
        Real.log (g.mass tops slope precision cutoff0 weight level (g.index level (slope top)) z)| ≤
        (5*(D:ℝ)/Kw)/Real.sqrt (SourceParameters.step L) := by
    have he := g.boundary_submass_source_motion tops T w B Kw (D:ℝ) hw hB hKw0
      (Nat.cast_nonneg D) hwidth 0 h level hlevel 0 (by norm_num) (g.width_pos h).le
      (slope top) sR (hs top htopCell) (g.width start) (g.width_pos start) hblock
      (g.cellTops tops slope precision cutoff0 level (g.index level (slope top)))
      ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,helevel⟩⟩
      (g.parent_subset_boundary tops slope precision cutoff0 0 level 0 (slope top)) b hb z
    simpa only [hbranch,mass,weight,z'] using he
  have hN := hlog lower hhlower (g.eligible_of_le (hprec top htop) hlower heligible)
  have hchild := hlog start hbase heligible
  rw [hindex] at hchild
  have hgapBlock (j : ℕ) (hj : j ∈ Finset.Ico lower start) :
      0 ≤ gap j ∧ gap j ≤ g.width h := hgap top htop j
        (hhlower.trans (Finset.mem_Ico.mp hj).1) ((Finset.mem_Ico.mp hj).2.le.trans htopM)
  have hphaseBlock (j : ℕ) (hj : j ∈ Finset.Ico lower start) : ‖phase j‖ ≤ Z :=
    hz top htop j ((Finset.mem_Ico.mp hj).2.trans_le htopM)
  have hlamMove := g.source_block_transition_relative_motion tops T w B Kw (D:ℝ)
    hw hB hKw0 (Nat.cast_nonneg D) hwidth hKb gap phase h lower start hhlower hgapBlock
    top htop heligible sR (hs top htopCell) (g.width start) (g.width_pos start) hblock b hb z
    Z hZ hphaseBlock
  rw [hbranch] at hlamMove
  have hlam0 : lam z ≠ 0 := g.source_path_product_ne_zero tops slope precision cutoff0 weight
    Kb gap phase z lower start (slope top)
  have hlam : ‖lam z‖ ≤ 1 := g.source_path_product_norm_le_one tops slope precision cutoff0 weight
    hprec hwpos hKb gap phase z lower start top htop heligible
      (fun j hj => hz0 top htop j ((Finset.mem_Ico.mp hj).2.trans_le htopM))
  have hraw := hphysical L ((le_max_left _ _).trans hLL) ι tops T N κ Label Item P hcard hP
    alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w B hw hB hbranch hwidth hlength hzero
    Kb hKb hKbL gap h start hbase M hM hMmax hgap sR cell hs hblock b hb z frequency hfreq hPfreq
    phase a Z A maskExponent ha0 ha1 hZ hZL hmask hz0 hz htC hA hAL htotal hconc
  have hsupported : ∀ t ∈ tops, ∀ j (l : (Q t).labels j) (_u : Item j l),
      rawStop t j ≤ M t := by
    intro t ht j l u
    exact g.source_length_stop_le_of_item tops T P w (cutoff0) hw M
      hzero hlength hMmax t ht j l u
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    intro i j hij
    exact min_le_min ((P t).stopping_antitone g (cutoff0) w hw (hzero t ht) hij) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := min_le_right _ _
  have hinterval (t : ι) (ht : t ∈ tops) (l u : ℕ) (hlu : l ≤ u) (hu : u ≤ N) :
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-slope t*z.1)‖ ≤ A*(weight t z)^8 := by
    have hb0 := hconc t ht l u hlu hu (z.2-slope t*z.1)
      (by simpa only [slope,sub_self,abs_zero] using (T t).width_pos.le)
    exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hb0
  have hmaskBound (t : ι) (_ht : t ∈ tops) : |(T t).mask L maskExponent z| ≤ 1 := by
    change |topSincMask L maskExponent _ _| ≤ 1
    rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
    exact topSincMask_le_one _ _ _ _
  have hsnap := g.source_snapshot_masked_node_bound tops slope precision cutoff0 weight hprec hwpos
    hKb gap phase M hM hMmax a Z ha0 ha1 hZ hz0 hz Q coeff 0 stop hstop hmax
    (fun _ => z.1) (fun t => z.2-slope t*z.1) A C hA hC z htC hinterval
    (fun t => (T t).mask L maskExponent z) start cell hmaskBound
  have heq := g.sourceBandAmplitude_clip_stop tops slope precision cutoff0 weight Kb gap Q
    (fun t j l u => (T t).mask L maskExponent z • coeff t j l u) 0 rawStop M hsupported
    (fun _ => z.1) (fun t => z.2-slope t*z.1) phase a z start cell
  rw [← heq] at hsnap
  have henv := hsnapshot L hLsL
    A a Z (∑ t ∈ tops, weight t z) Kb hA hAL ha0 ha1 hZ hZL hKbL htotal
  have hsnapPoly : ‖amplitude z‖ ≤ L^(q+6)*c z :=
    hsnap.trans (mul_le_mul_of_nonneg_right henv (hc z).le)
  have hnormalL := hnormal L hLnL
  exact hnormalL κ Kw r μ (n z) (n z') (c z) (c z') (start-lower) Z hKw hr hμ0 hμ1
    (hn z) (hn z') (hc z) (hc z') hsteps hZ hZL frequency ((sR-g.center start cell)*b)
    (amplitude z) (amplitude z') (lam z) (lam z') hlam0 hlam hN hchild hsnapPoly hraw hlamMove


end LipschitzHilbert.AngularGrid

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.AngularGrid.source_supported_selector_normalized_motion_oai := @OAI.LipschitzHilbert.AngularGrid.source_supported_selector_normalized_motion_oai
