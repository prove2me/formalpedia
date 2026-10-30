-- Prove2me | solution 1 for OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:10:37.530527+00:00
-- url     : https://prove2.me/submissions/cb635cfc-697a-46ab-bb13-2305ed5fc95f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_eventually_source_block_path_motion
import Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_source_supported_selector_normalized_motion
import Theorems.Thm_OAI_LipschitzHilbert_eventually_source_grid_parameters

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RadialShrink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Radial snapshot shrinkage and the balanced prediction comparison

Section 9 shrinks each snapshot amplitude radially by a controlled distance.
The exact norm formula makes its denominator smaller than every nearby moved
denominator. The numerator motion and the logarithmic-energy Lipschitz bound
then give the balanced-case comparison, with its relative path-drop factor.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial truncation removes exactly the smaller of `δ` and the norm. -/
theorem norm_radialShrink {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    ‖radialShrink δ x‖ = max (‖x‖ - δ) 0 := by
  by_cases hx : x = 0
  · subst x
    simp [max_eq_right (neg_nonpos.mpr hδ)]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [radialShrink, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  by_cases hsmall : δ ≤ ‖x‖
  · have hfactor : 0 ≤ 1 - δ / ‖x‖ := by
      exact sub_nonneg.mpr ((div_le_one hxnorm).2 hsmall)
    rw [max_eq_left hfactor, max_eq_left (sub_nonneg.mpr hsmall)]
    field_simp
  · have hlarge : ‖x‖ ≤ δ := le_of_lt (lt_of_not_ge hsmall)
    have hfactor : 1 - δ / ‖x‖ ≤ 0 := by
      exact sub_nonpos.mpr ((one_le_div hxnorm).2 hlarge)
    rw [max_eq_right hfactor, max_eq_right (sub_nonpos.mpr hlarge), zero_mul]

/-- Vectors already within the discarded radius are suppressed completely. -/
theorem radialShrink_eq_zero_iff {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    radialShrink δ x = 0 ↔ ‖x‖ ≤ δ := by
  rw [← norm_eq_zero, norm_radialShrink hδ]
  constructor
  · intro h
    have hle := le_max_left (‖x‖ - δ) 0
    rw [h] at hle
    linarith
  · intro h
    exact max_eq_right (sub_nonpos.mpr h)

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

theorem vectorPacketSynthesis_coeff_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (s x : ℝ) :
    vectorPacketSynthesis (fun i => s • c i) f x = s • vectorPacketSynthesis c f x := by
  ext k
  simp only [vectorPacketSynthesis, packetSynthesis_apply, WithLp.ofLp_toLp,
    PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

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

end SlopeBox

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

theorem neighbors_symmetric (g : AngularGrid) (level : ℕ) (gap : ℝ) :
    ∀ ⦃i j⦄, g.neighbors level gap i j → g.neighbors level gap j i := by
  intro i j h
  simpa only [neighbors, abs_sub_comm] using h

/-- Non-neighboring cells separate every pair of slopes they contain. -/
theorem slopes_separated_of_not_neighbors (g : AngularGrid) (level : ℕ)
    (gap s t : ℝ) (hfar : ¬g.neighbors level gap (g.index level s) (g.index level t)) :
    gap ≤ |s - t| := by
  have hcenters : gap + g.width level ≤
      |g.center level (g.index level s) - g.center level (g.index level t)| :=
    le_of_not_gt hfar
  have hs := g.slope_dist_center_le level s
  have ht := g.slope_dist_center_le level t
  have htriangle : |g.center level (g.index level s) - g.center level (g.index level t)| ≤
      |s - g.center level (g.index level s)| + |s - t| +
        |t - g.center level (g.index level t)| := by
    calc
      _ = |(g.center level (g.index level s) - s) + (s - t) +
          (t - g.center level (g.index level t))| := by congr 1; ring
      _ ≤ |(g.center level (g.index level s) - s) + (s - t)| +
          |t - g.center level (g.index level t)| := abs_add_le _ _
      _ ≤ (|g.center level (g.index level s) - s| + |s - t|) +
          |t - g.center level (g.index level t)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_sub_comm (g.center level (g.index level s)) s]
  linarith

theorem centers_separated_of_not_neighbors (g : AngularGrid) (level : ℕ)
    (gap : ℝ) {i j : ℤ} (hfar : ¬g.neighbors level gap i j) :
    gap ≤ |g.center level i - g.center level j| := by
  have h := le_of_not_gt hfar
  have hw := g.width_pos level
  linarith

/-- The actual carrier frequencies inherit separation in each Hilbert
component from non-neighboring angular cells. -/
theorem carrier_frequency_separated (g : AngularGrid) (level : ℕ)
    {gap ηmin η s : ℝ} (hηmin : 0 ≤ ηmin) (hη : ηmin ≤ |η|)
    {i j : ℤ} (hfar : ¬g.neighbors level gap i j) :
    gap * ηmin ≤ |(s - g.center level i) * η - (s - g.center level j) * η| := by
  have hc := g.centers_separated_of_not_neighbors level gap hfar
  calc
    gap * ηmin ≤ |g.center level i - g.center level j| * |η| :=
      mul_le_mul hc hη hηmin (abs_nonneg _)
    _ = _ := by
      rw [← abs_mul]
      have heq : (s - g.center level i) * η - (s - g.center level j) * η =
          -((g.center level i - g.center level j) * η) := by ring
      rw [heq, abs_neg]

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

/-- Each neighboring child within the block ancestor is fully included in
this boundary mass. This is the inclusion used by weighted selection. -/
theorem neighbor_cell_subset_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (gap s t : ℝ)
    (hancestor : g.index base t = g.index base s)
    (hnear : g.neighbors (level + 1) gap (g.index (level + 1) s) (g.index (level + 1) t)) :
    g.cellTops tops slope precision cutoff (level + 1) (g.index (level + 1) t) ⊆
      g.boundaryTops tops slope precision cutoff base level gap s := by
  classical
  intro i hi
  have ht := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  by_cases hparent : g.index level (slope i) = g.index level s
  · apply Finset.mem_union_left
    exact (g.mem_cellTops _ _ _ _ _ _ _).2
      ⟨ht.1, hparent, g.eligible_parent (hp i ht.1) level ht.2.2⟩
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨?_, ht.2.2, ?_, hparent⟩
    · have ha := g.cellTops_subset_ancestor tops slope precision cutoff hp
        (hle.trans (Nat.le_succ level)) t hi
      simpa only [hancestor] using ha
    · simpa only [ht.2.1] using hnear

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

/-- Distinct angular cells have disjoint eligible top sets. -/
theorem cellTops_disjoint (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (level : ℕ) {a b : ℤ} (hab : a ≠ b) :
    Disjoint (g.cellTops tops slope precision cutoff level a)
      (g.cellTops tops slope precision cutoff level b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i ha hb
  exact hab (((g.mem_cellTops _ _ _ _ _ _ _).1 ha).2.1.symm.trans
    ((g.mem_cellTops _ _ _ _ _ _ _).1 hb).2.1)

/-- A finite collection of child cells included in the boundary consumes
at most its mass. In particular this pays for a closed graph neighborhood. -/
theorem sum_cell_mass_le_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ i x, 0 ≤ weight i x) (base level : ℕ) (gap s : ℝ) (cells : Finset ℤ)
    (hsub : ∀ c ∈ cells, g.cellTops tops slope precision cutoff (level + 1) c ⊆
      g.boundaryTops tops slope precision cutoff base level gap s) (x : X) :
    (∑ c ∈ cells, g.mass tops slope precision cutoff weight (level + 1) c x) ≤
      g.boundaryMass tops slope precision cutoff weight base level gap s x := by
  classical
  have hdisjoint : (cells : Set ℤ).PairwiseDisjoint
      (g.cellTops tops slope precision cutoff (level + 1)) := by
    intro a _ b _ hab
    exact g.cellTops_disjoint tops slope precision cutoff (level + 1) hab
  change (∑ c ∈ cells, ∑ i ∈ g.cellTops tops slope precision cutoff (level + 1) c,
    weight i x) ≤ _
  rw [← Finset.sum_biUnion hdisjoint]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.biUnion_subset.mpr hsub)
    (fun i _ _ => hw i x)

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

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShiftedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted block endpoints of §8. The first block is allowed
to be shorter. Every transition has one phase tag, and each completed
block contains its distinguished phase exactly at the last transition. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

theorem lastTransition_succ (σ : Fin K) (j : ℕ) :
    lastTransition σ j + 1 = endpoint σ (j + 1) := by
  rw [lastTransition_eq, endpoint_succ]
  omega

theorem endpoint_first_bounds (σ : Fin K) : 1 ≤ endpoint σ 1 ∧ endpoint σ 1 ≤ K := by
  simp only [endpoint_succ, Nat.zero_mul, Nat.add_zero]
  have hs := σ.isLt
  omega

theorem endpoint_step (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 2) = endpoint σ (j + 1) + K := by
  simp only [show j + 2 = (j + 1) + 1 by omega, endpoint_succ, Nat.add_mul, Nat.one_mul]
  omega

theorem endpoint_width_le (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 1) ≤ endpoint σ j + K := by
  cases j with
  | zero => simpa using (endpoint_first_bounds σ).2
  | succ j => exact le_of_eq (endpoint_step σ j)

theorem lastTransition_mem (hK : 0 < K) (σ : Fin K) (j : ℕ) :
    lastTransition σ j ∈ block σ j := by
  have h := endpoint_strictMono hK σ (Nat.lt_succ_self j)
  change endpoint σ j < endpoint σ (j + 1) at h
  have hl := lastTransition_succ σ j
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem tag_lastTransition (hK : 0 < K) (σ : Fin K) (j : ℕ) :
    tag hK (lastTransition σ j) = σ := by
  apply Fin.ext
  simp [tag, lastTransition_eq, Nat.add_mod, Nat.mod_eq_of_lt σ.isLt]

/-- The block ending at transition i starts at the source's shared
boundary ancestor i+1-K, with truncated subtraction at the root. -/
theorem endpoint_eq_last_sub (σ : Fin K) (j : ℕ) :
    endpoint σ j = lastTransition σ j + 1 - K := by
  cases j with
  | zero =>
    simp only [endpoint_zero, lastTransition_eq, Nat.zero_mul, Nat.add_zero]
    have hs := σ.isLt
    omega
  | succ j =>
    simp only [endpoint_succ, lastTransition_eq, Nat.succ_mul]
    omega

theorem tag_injective_on_block (hK : 0 < K) (σ : Fin K) (j : ℕ) :
    Set.InjOn (tag hK) (block σ j) := by
  intro i hi k hk heq
  have hwidth := endpoint_width_le σ j
  have him := Finset.mem_Ico.mp hi
  have hkm := Finset.mem_Ico.mp hk
  apply Nat.mod_injOn_Ico (endpoint σ j) K
    (Finset.mem_Ico.mpr ⟨him.1, him.2.trans_le hwidth⟩)
    (Finset.mem_Ico.mpr ⟨hkm.1, hkm.2.trans_le hwidth⟩)
  exact congrArg Fin.val heq

theorem tag_eq_shift_iff (hK : 0 < K) (σ : Fin K) (j i : ℕ) (hi : i ∈ block σ j) :
    tag hK i = σ ↔ i = lastTransition σ j := by
  constructor
  · intro heq
    exact tag_injective_on_block hK σ j hi (lastTransition_mem hK σ j)
      (heq.trans (tag_lastTransition hK σ j).symm)
  · rintro rfl
    exact tag_lastTransition hK σ j

theorem prod_block_eq_last {M : Type*} [CommMonoid M] (hK : 0 < K) (σ : Fin K)
    (j : ℕ) (f : ℕ → M) (h : ∀ i ∈ block σ j, tag hK i ≠ σ → f i = 1) :
    (∏ i ∈ block σ j, f i) = f (lastTransition σ j) := by
  apply Finset.prod_eq_single_of_mem (lastTransition σ j) (lastTransition_mem hK σ j)
  intro i hi hne
  exact h i hi (fun htag => hne ((tag_eq_shift_iff hK σ j i hi).mp htag))

theorem packetPathProduct_norm_eq_last (hK : 0 < K) (σ : Fin K) (j : ℕ)
    (g : AngularGrid) (transition : ℕ → ℤ → ℂ) (slope : ℝ)
    (h : ∀ i ∈ block σ j, tag hK i ≠ σ →
      ‖transition i (g.index (i + 1) slope)‖ = 1) :
    ‖g.packetPathProduct transition (endpoint σ j) (endpoint σ (j + 1)) slope‖ =
      ‖transition (lastTransition σ j) (g.index (endpoint σ (j + 1)) slope)‖ := by
  rw [AngularGrid.packetPathProduct, norm_prod]
  have hp := prod_block_eq_last hK σ j
    (fun i => ‖transition i (g.index (i + 1) slope)‖) h
  simpa only [block, lastTransition_succ] using hp

/-- At a vertex parameter, the modulus of a complete block product is
the modulus contributed by its final transition alone. Other phase
coordinates may still have arbitrary imaginary parts. -/
theorem analytic_block_norm (hK : 0 < K) (σ : Fin K) (j : ℕ)
    (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ) (phase : Fin K → ℂ) (slope : ℝ)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0)
    (hm : ∀ i ∈ block σ j, 0 < mass (i + 1) (g.index (i + 1) slope))
    (hb : ∀ i ∈ block σ j, 0 < boundary i (g.index (i + 1) slope)) :
    ‖g.packetPathProduct (AngularGrid.analyticTransition mass boundary (fun i => phase (tag hK i)))
      (endpoint σ j) (endpoint σ (j + 1)) slope‖ =
      (mass (endpoint σ (j + 1)) (g.index (endpoint σ (j + 1)) slope) /
        boundary (lastTransition σ j) (g.index (endpoint σ (j + 1)) slope)) ^ (phase σ).re := by
  rw [packetPathProduct_norm_eq_last hK σ j g _ slope]
  · have hlast := lastTransition_mem hK σ j
    have hnorm := AngularGrid.analyticTransition_norm mass boundary
      (fun i => phase (tag hK i)) (lastTransition σ j)
      (g.index (lastTransition σ j + 1) slope) (hm _ hlast) (hb _ hlast)
    simpa only [lastTransition_succ, tag_lastTransition] using hnorm
  · intro i hi htag
    rw [AngularGrid.analyticTransition_norm mass boundary (fun i => phase (tag hK i))
      i _ (hm i hi) (hb i hi), hphase _ htag, Real.rpow_zero]

end LipschitzHilbert.ShiftedBlocks

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convolution and the exact averaging mixture

Convolution preserves the proved Fourier gap. A central mass of the kernel
minorizes the uniform law on a smaller interval. The remaining measure is
normalized into the probability used in the prediction-mixture argument.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory ENNReal

namespace LipschitzHilbert

open PhaseCombinatorics

theorem intervalProbability_isProbability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalProbability a b) := by
  constructor
  simp only [intervalProbability, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))
    ENNReal.ofReal_ne_top

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionShrink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source snapshot shrinkage gives the one-sided denominator
comparison and preserves numerator motion with its child-mass factor. -/

noncomputable section
namespace LipschitzHilbert

section RealVector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem source_prediction_shrink_zero {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : E) (hA : ‖A‖ ≤ ε*c) : radialShrink (2*ε*c) A = 0 := by
  apply (radialShrink_eq_zero_iff (by positivity) A).mpr
  exact hA.trans (by nlinarith)

end RealVector

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

theorem source_phaseMu_small {D L : ℝ} (hD : 1 ≤ D) (hL : 256 ≤ L) :
    0 < phaseMu D (Real.sqrt L) ∧ phaseMu D (Real.sqrt L) ≤ 1 / 12 := by
  have hroot : (16 : ℝ) ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hL
  have hp : 0 < Real.sqrt L := by linarith
  have hμ := phaseMu_positive_le hD hp
  refine ⟨hμ.1, hμ.2.trans ?_⟩
  exact (div_le_iff₀ hp).mpr (by linarith)

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

theorem rawBand_coeff_real_smul (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : ℝ) (jet : Fin 3) (j : Fin N) (x y : ℝ) :
    P.rawBand (fun j l u => q • coeff j l u) jet j x y = q • P.rawBand coeff jet j x y := by
  exact vectorPacketSynthesis_coeff_smul
    (fun p : Σ l : P.labels j, Item j l => coeff j p.1 p.2)
    (fun p k => P.raw jet j p.1 p.2 k y) q x

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceInsignificantShrink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Insignificant children are removed by the same radial shrink used in
the denominator comparison. There is no extra exceptional-child premise. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_insignificant_error (Q : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      L^Q*Real.exp (-L*Real.log L) ≤ SourceParameters.step L^(-(1/8:ℝ)) := by
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (2*Q),hlog]
    with L hL hQ hlog
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have h07 : L^(7/10:ℝ) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (7/10:ℝ) ≤ 1)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hb := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hstep : Real.log (SourceParameters.step L) ≤ 3*L := by
    have hb := (SourceParameters.log_step_bounds hL0.le).2
    linarith
  have hexponent : (Q-L)*Real.log L ≤ -(L/2) := by
    have hQL : Q-L ≤ -(L/2) := by linarith
    calc
      _ ≤ (-(L/2))*Real.log L := mul_le_mul_of_nonneg_right hQL (by linarith)
      _ ≤ -(L/2) := by nlinarith
  rw [Real.rpow_def_of_pos hL0,← Real.exp_add,
    Real.rpow_def_of_pos (SourceParameters.step_pos L)]
  apply Real.exp_le_exp.mpr
  calc
    _ = (Q-L)*Real.log L := by ring
    _ ≤ -(L/2) := hexponent
    _ ≤ Real.log (SourceParameters.step L)*(-(1/8:ℝ)) := by linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source sinc mask is exponentially small outside the prescribed
polynomial enlargement of its top. The estimate includes points on either
coordinate axis and uses the actual even exponent `2 * ceil L`. -/

noncomputable section
namespace LipschitzHilbert

theorem abs_sinc_le_reciprocal_of_large {L x : ℝ} (hL : 0 < L)
    (hx : L ≤ |x|) : |Real.sinc x| ≤ 1/L := by
  have hx0 : x ≠ 0 := abs_pos.mp (hL.trans_le hx)
  rw [Real.sinc_of_ne_zero hx0,abs_div]
  calc
    _ ≤ 1/|x| := div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (abs_nonneg x)
    _ ≤ 1/L := one_div_le_one_div_of_le hL hx

theorem sincProductMask_tail {L x y : ℝ} (hL : 1 ≤ L)
    (hlarge : L ≤ |x| ∨ L ≤ |y|) :
    |sincProductMask ⌈L⌉₊ x y| ≤ Real.exp (-L*Real.log L) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hproduct : |Real.sinc x*Real.sinc y| ≤ 1/L := by
    rw [abs_mul]
    rcases hlarge with hx | hy
    · have hb := mul_le_mul (abs_sinc_le_reciprocal_of_large hL0 hx)
        (Real.abs_sinc_le_one y) (abs_nonneg _) (by positivity : 0 ≤ 1/L)
      simpa only [mul_one] using hb
    · have hb := mul_le_mul (Real.abs_sinc_le_one x)
        (abs_sinc_le_reciprocal_of_large hL0 hy) (abs_nonneg _) zero_le_one
      simpa only [one_mul] using hb
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hproduct (2*⌈L⌉₊)
  have hexponent : L ≤ ((2*⌈L⌉₊:ℕ):ℝ) := by
    have hc := Nat.le_ceil L
    have hn : (0:ℝ) ≤ (⌈L⌉₊:ℝ) := Nat.cast_nonneg _
    push_cast
    linarith
  calc
    _ ≤ (1/L)^(2*⌈L⌉₊) := by simpa only [sincProductMask,abs_pow] using hpow
    _ = (1/L)^((2*⌈L⌉₊:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (1/L)^L := Real.rpow_le_rpow_of_exponent_ge (by positivity)
      ((div_le_one hL0).mpr hL) hexponent
    _ = Real.exp (-L*Real.log L) := by
      rw [Real.rpow_def_of_pos (by positivity : 0 < 1/L),Real.log_div one_ne_zero hL0.ne',
        Real.log_one]
      congr 1
      ring

theorem topSincMask_tail {L A x y : ℝ} (hL : 2 ≤ L)
    (hlarge : L^(A+2) ≤ |x|+|y|) :
    |topSincMask L A x y| ≤ Real.exp (-L*Real.log L) := by
  have hL0 : 0 < L := by linarith
  have hscale : 0 < L^A := Real.rpow_pos_of_pos hL0 _
  have hthreshold : 2*(L*L^A) ≤ L^(A+2) := by
    rw [Real.rpow_add hL0,Real.rpow_two]
    have hm := mul_le_mul_of_nonneg_left hL hL0.le
    have hp := mul_le_mul_of_nonneg_right hm hscale.le
    nlinarith
  have hcoordinate : L*L^A ≤ |x| ∨ L*L^A ≤ |y| := by
    by_contra hnone
    push Not at hnone
    linarith
  have hscaled : L ≤ |x/L^A| ∨ L ≤ |y/L^A| := by
    simp only [abs_div,abs_of_pos hscale]
    rcases hcoordinate with hx | hy
    · exact Or.inl ((le_div_iff₀ hscale).mpr hx)
    · exact Or.inr ((le_div_iff₀ hscale).mpr hy)
  exact sincProductMask_tail (by linarith) hscaled

theorem SlopeBox.mask_tail (T : SlopeBox) {L A : ℝ} (hL : 2 ≤ L)
    (z : ℝ × ℝ) (hlarge : L^(A+2) ≤ T.radius z) :
    |T.mask L A z| ≤ Real.exp (-L*Real.log L) :=
  topSincMask_tail hL hlarge

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a vertex of the phase simplex, a complete shifted source block
has only one nonunit transition modulus. Its coefficient is exactly the
child-to-boundary power used in the dominant-path comparison. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem source_shifted_block_norm {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hK : 0 < K) (gap : ℕ → ℝ)
    (phase : Fin K → ℂ) (σ : Fin K) (j : ℕ)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) (x : X) :
    ‖g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap
        (fun i => phase (ShiftedBlocks.tag hK i)) x)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) (slope top)‖ =
    (g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1))
        (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x /
      g.sourceBoundaryMass tops slope precision cutoff weight K gap (ShiftedBlocks.lastTransition σ j)
        (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x) ^ (phase σ).re := by
  apply ShiftedBlocks.analytic_block_norm hK σ j g
    (fun level cell => g.mass tops slope precision cutoff weight level cell x)
    (fun level cell => g.sourceBoundaryMass tops slope precision cutoff weight K gap level cell x)
    phase (slope top) hphase
  · intro i hi
    exact g.path_mass_pos tops slope precision cutoff weight hw (i+1) top htop
      (g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hi).2; omega) he) x
  · intro i hi
    have hm := g.path_mass_pos tops slope precision cutoff weight hw (i+1) top htop
      (g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hi).2; omega) he) x
    exact hm.trans_le (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) hK gap i (slope top) x).1

theorem source_shifted_block_mass_bounds {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hK : 0 < K) (gap : ℕ → ℝ)
    (σ : Fin K) (j : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1))
        (g.index (ShiftedBlocks.endpoint σ (j+1)) s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap (ShiftedBlocks.lastTransition σ j)
        (g.index (ShiftedBlocks.endpoint σ (j+1)) s) x ∧
    g.sourceBoundaryMass tops slope precision cutoff weight K gap (ShiftedBlocks.lastTransition σ j)
        (g.index (ShiftedBlocks.endpoint σ (j+1)) s) x ≤
      g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) s) x := by
  have hb := g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp hw hK gap
    (ShiftedBlocks.lastTransition σ j) s x
  rw [← ShiftedBlocks.endpoint_eq_last_sub σ j] at hb
  simpa only [ShiftedBlocks.lastTransition_succ] using hb

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path mass at shifted block endpoints is set to zero as soon as
the distinguished top becomes ineligible, even if other tops continue.
The actual drop has the same factor-two reference-window comparison,
including this terminal block. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem shiftedPathMass_pos {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 < weight t x)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j)) :
    0 < g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  rw [shiftedPathMass,ite_eq_left he]
  exact g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x

theorem shiftedPathDrop_terminal {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 < weight t x)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j))
    (hnext : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) :
    pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j = 1 := by
  have hpos := g.shiftedPathMass_pos tops slope precision cutoff weight hw σ top htop x j he
  have hzero : g.shiftedPathMass tops slope precision cutoff weight σ top x (j+1) = 0 := by
    rw [shiftedPathMass,ite_eq_right hnext]
  unfold pathDrop
  rw [hzero,sub_zero,div_self hpos.ne']

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGraphMass
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual boundary masses dominate the graph's closed-neighborhood mass. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

theorem closed_neighborhood_mass_le_boundary {ι X : Type*}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {base level : ℕ} (hle : base ≤ level) {gap : ℝ} (hgap : 0 ≤ gap)
    (cells : Finset ℤ) (representative : cells → ℝ) (parent : ℤ)
    (hcell : ∀ c, g.index (level + 1) (representative c) = c.val)
    (hancestor : ∀ c, g.index base (representative c) = parent)
    (i : cells) (x : X) :
    orderMass (fun c : cells => g.mass tops slope precision cutoff weight (level + 1) c.val x)
      (closedNeighborhood (fun c e : cells => g.neighbors (level + 1) gap c.val e.val) i) ≤
      g.boundaryMass tops slope precision cutoff weight base level gap (representative i) x := by
  classical
  let neighbors := closedNeighborhood
    (fun c e : cells => g.neighbors (level + 1) gap c.val e.val) i
  have hsub : ∀ c ∈ neighbors.image Subtype.val,
      g.cellTops tops slope precision cutoff (level + 1) c ⊆
        g.boundaryTops tops slope precision cutoff base level gap (representative i) := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    have hnear : g.neighbors (level + 1) gap i.val j.val := by
      obtain hji | hij := (mem_closedNeighborhood _ _ _).mp hj
      · subst j
        unfold AngularGrid.neighbors
        simp only [sub_self, abs_zero]
        linarith [g.width_pos (level + 1)]
      · exact hij
    have h := g.neighbor_cell_subset_boundary tops slope precision cutoff hp hle
      gap (representative i) (representative j)
      ((hancestor j).trans (hancestor i).symm)
      (by simpa only [hcell] using hnear)
    simpa only [hcell] using h
  have h := g.sum_cell_mass_le_boundary tops slope precision cutoff weight hw
    base level gap (representative i) (neighbors.image Subtype.val) hsub x
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at h
  exact h

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockChildren
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual block children are the nonempty eligible-top cells. Their
canonical representatives are slopes of eligible tops, including cells
whose packet amplitude is zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem sourceBlockTop_spec {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    let t := g.sourceBlockTop tops slope precision cutoff lower upper parent c
    t ∈ tops ∧ g.index lower (slope t) = parent ∧
      g.eligible cutoff (precision t) upper ∧ g.index upper (slope t) = c.val := by
  have h := (Finset.mem_image.mp c.property).choose_spec
  obtain ⟨hc,he⟩ := Finset.mem_filter.mp h.1
  have ht := (g.mem_cellTops tops slope precision cutoff lower parent _).mp hc
  exact ⟨ht.1,ht.2.1,he,h.2⟩

theorem sourceBlockTop_mem_child {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    g.sourceBlockTop tops slope precision cutoff lower upper parent c ∈
      g.cellTops tops slope precision cutoff upper c.val := by
  obtain ⟨ht,_,he,hi⟩ := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent c
  exact (g.mem_cellTops tops slope precision cutoff upper c.val _).mpr ⟨ht,hi,he⟩

theorem sourceBlockCells_nonempty_child {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    (g.cellTops tops slope precision cutoff upper c.val).Nonempty :=
  ⟨_,g.sourceBlockTop_mem_child tops slope precision cutoff lower upper parent c⟩

/-- Every eligible top in the parent selects one of these children. -/
theorem mem_sourceBlockCells_of_top {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hle : lower ≤ upper)
    (top : ι) (htop : top ∈ tops) (hparent : g.index lower (slope top) = parent)
    (he : g.eligible cutoff (precision top) upper) :
    g.index upper (slope top) ∈ g.sourceBlockCells tops slope precision cutoff lower upper parent := by
  apply Finset.mem_image.mpr
  refine ⟨top,Finset.mem_filter.mpr ⟨?_,he⟩,rfl⟩
  exact (g.mem_cellTops tops slope precision cutoff lower parent top).mpr
    ⟨htop,hparent,g.eligible_of_le (hp top htop) hle he⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineGrid
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nested line grid with the rounded manuscript step. A single
refinement has mesh H/G, small enough to retain the G^(-1/16) error when
the carrier spread times H is at most G^(15/16). -/

noncomputable section
namespace LipschitzHilbert

theorem sourceLineGrid_mesh (L origin width : ℝ) (depth level : ℕ) (hwidth : 0 < width) :
    (sourceLineGrid L origin width depth hwidth).meshWidth level =
      width/(SourceParameters.step L)^level := by
  simp only [FiniteLineGrid.meshWidth,sourceLineGrid,SourceParameters.step,Nat.cast_pow,Nat.cast_ofNat]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source line scales for a whole angular block. Refinement from the
child scale to the parent scale cancels the angular branching exactly. -/

noncomputable section
namespace LipschitzHilbert

theorem source_block_line_mesh (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (lower start : ℕ) (hle : lower ≤ start)
    (hbranch : (g.branching : ℝ) = SourceParameters.step L) :
    (sourceLineGrid L origin (sourceLineScale g L w start) (start-lower)
      (sourceLineScale_pos g L hw start)).meshWidth (start-lower) =
      sourceLineScale g L w lower := by
  rw [sourceLineGrid_mesh]
  have hG := SourceParameters.step_pos L
  have hpow : SourceParameters.step L ^ start =
      SourceParameters.step L ^ lower * SourceParameters.step L ^ (start-lower) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  unfold sourceLineScale AngularGrid.width
  rw [hbranch, hpow]
  field_simp

theorem source_block_line_carrier (g : AngularGrid) (L origin : ℝ) {w F C : ℝ}
    (hw : 0 < w) (lower start : ℕ) (hle : lower ≤ start)
    (hbranch : (g.branching : ℝ) = SourceParameters.step L)
    (hF : F ≤ C*g.width lower/w) :
    F*(sourceLineGrid L origin (sourceLineScale g L w start) (start-lower)
      (sourceLineScale_pos g L hw start)).meshWidth (start-lower) ≤
      C*SourceParameters.step L^(-(1/2:ℝ)) := by
  rw [source_block_line_mesh g L origin hw lower start hle hbranch]
  calc
    _ ≤ (C*g.width lower/w)*sourceLineScale g L w lower :=
      mul_le_mul_of_nonneg_right hF (sourceLineScale_pos g L hw lower).le
    _ = C*SourceParameters.step L^(-(1/2:ℝ)) := by
      rw [Real.rpow_neg (SourceParameters.step_pos L).le]
      unfold sourceLineScale
      field_simp [(g.width_pos lower).ne']

/-- At the source window size, the angular gap times the transverse
frequency clears the exact Fourier threshold used by near-uniform averaging. -/
theorem source_line_fourier_threshold (g : AngularGrid) (L : ℝ)
    {w c0 : ℝ} (hw : 0 < w) (level : ℕ)
    (hc0 : SourceParameters.step L^(-(1/8:ℝ)) ≤ c0) :
    1/(sourceLineScale g L w level*SourceParameters.step L^(-(1/8:ℝ))) ≤
      (SourceParameters.step L^(3/4:ℝ)*g.width level)*(c0/w) := by
  have hG := SourceParameters.step_pos L
  have hwidth := g.width_pos level
  have hpow : SourceParameters.step L^(3/4:ℝ)*SourceParameters.step L^(-(1/8:ℝ)) =
      SourceParameters.step L^(1/2:ℝ)/SourceParameters.step L^(-(1/8:ℝ)) := by
    rw [← Real.rpow_add hG, ← Real.rpow_sub hG]
    norm_num
  calc
    _ = (SourceParameters.step L^(3/4:ℝ)*g.width level)*
        (SourceParameters.step L^(-(1/8:ℝ))/w) := by
      unfold sourceLineScale
      calc
        _ = (g.width level/w)*(SourceParameters.step L^(1/2:ℝ)/
            SourceParameters.step L^(-(1/8:ℝ))) := by
          field_simp
        _ = (g.width level/w)*(SourceParameters.step L^(3/4:ℝ)*
            SourceParameters.step L^(-(1/8:ℝ))) := by rw [hpow]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc0 hw.le)
      (mul_pos (Real.rpow_pos_of_pos hG _) hwidth).le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier spread and Fourier separation at the actual source block windows. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

namespace AngularGrid

theorem sourceGap_pos (g : AngularGrid) (L : ℝ) (child : ℕ) :
    0 < g.sourceGap L child :=
  mul_pos (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _) (g.width_pos child)

/-- Both hypotheses of the separated-top count hold at the actual block
neighbor radius, including the initial shorter block. -/
theorem source_block_count_scales (g : AngularGrid) (L : ℝ) {B : ℝ}
    (hB : 0 < B) (base child : ℕ) (hblock : g.width base ≤ B*g.width child) :
    (g.rootWidth/B^2)/(g.branching:ℝ)^child ≤ g.sourceGap L child/B^2 ∧
      g.width base ≤ B*g.sourceGap L child := by
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hg : 1 ≤ SourceParameters.step L^(3/4:ℝ) := Real.one_le_rpow hG (by norm_num)
  have hw : g.width child ≤ g.sourceGap L child := by
    exact le_mul_of_one_le_left (g.width_pos child).le hg
  constructor
  · have heq : (g.rootWidth/B^2)/(g.branching:ℝ)^child = g.width child/B^2 := by
      unfold width
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hw (sq_nonneg B)
  · exact hblock.trans (mul_le_mul_of_nonneg_left hw hB.le)

theorem centers_close_in_ancestor (g : AngularGrid) {base level : ℕ}
    (hle : base ≤ level) (s t : ℝ) (hcell : g.index base s = g.index base t) :
    |g.center level (g.index level s)-g.center level (g.index level t)| ≤
      2*g.width base := by
  have hs := g.slope_dist_center_le level s
  have ht := g.slope_dist_center_le level t
  have hst := g.same_cell_diameter base hcell
  have hw := g.width_antitone hle
  have htri : |g.center level (g.index level s)-g.center level (g.index level t)| ≤
      |s-g.center level (g.index level s)|+|s-t|+
        |t-g.center level (g.index level t)| := by
    calc
      _ = |(g.center level (g.index level s)-s)+(s-t)+
          (t-g.center level (g.index level t))| := by congr 1; ring
      _ ≤ |(g.center level (g.index level s)-s)+(s-t)|+
          |t-g.center level (g.index level t)| := abs_add_le _ _
      _ ≤ (|g.center level (g.index level s)-s|+|s-t|)+
          |t-g.center level (g.index level t)| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_sub_comm (g.center level (g.index level s)) s]
  linarith

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted angular blocks meet the source scale conditions.
The first block is included with its original shorter length. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

/-- The ratio of actual angular widths is exactly the iterated step. -/
theorem source_width_ratio (g : AngularGrid) (L : ℝ) {lower upper : ℕ}
    (hle : lower ≤ upper) (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    g.width lower = SourceParameters.step L^(upper-lower)*g.width upper := by
  have hp : SourceParameters.step L^upper =
      SourceParameters.step L^lower*SourceParameters.step L^(upper-lower) := by
    rw [← pow_add,Nat.add_sub_of_le hle]
  unfold width
  rw [hbranch,hp]
  field_simp [(SourceParameters.step_pos L).ne']

/-- Every source block has width ratio between G and B, with exactly the
same conclusion for the initial block. -/
theorem source_shifted_width_bounds (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) :
    SourceParameters.step L*g.width (ShiftedBlocks.endpoint σ (j+1)) ≤
        g.width (ShiftedBlocks.endpoint σ j) ∧
      g.width (ShiftedBlocks.endpoint σ j) ≤
        SourceParameters.branching L*g.width (ShiftedBlocks.endpoint σ (j+1)) := by
  have hle := (ShiftedBlocks.endpoint_strictMono hK σ) (Nat.lt_succ_self j)
  change ShiftedBlocks.endpoint σ j < ShiftedBlocks.endpoint σ (j+1) at hle
  have hlen := ShiftedBlocks.endpoint_width_le σ j
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  rw [g.source_width_ratio L hle.le hbranch]
  constructor
  · apply mul_le_mul_of_nonneg_right _ (g.width_pos _).le
    calc
      SourceParameters.step L = SourceParameters.step L^1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hG (by omega)
  · apply mul_le_mul_of_nonneg_right _ (g.width_pos _).le
    exact pow_le_pow_right₀ hG (by omega)

/-- Consequently the geometric precision and span hypotheses for the
simultaneous count follow from the shifted source block itself. -/
theorem source_shifted_count_scales (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) :
    (g.rootWidth/(SourceParameters.branching L)^2)/
        (g.branching:ℝ)^(ShiftedBlocks.endpoint σ (j+1)) ≤
      g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))/(SourceParameters.branching L)^2 ∧
    g.width (ShiftedBlocks.endpoint σ j) ≤ SourceParameters.branching L*
      g.sourceGap L (ShiftedBlocks.endpoint σ (j+1)) :=
  g.source_block_count_scales L (SourceParameters.branching_pos L) _ _
    (g.source_shifted_width_bounds L hbranch hK σ j).2

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularCountBridge
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simultaneous top count supplies the graph's independence bound. -/

noncomputable section

open Set

namespace LipschitzHilbert.AngularGrid

/-- Select one significant top in each nonempty angular cell. Disjoint
cells make this selection injective, and nonneighbors make its slopes
separated. Thus the previously proved simultaneous list bound applies
to every independent cell collection. -/
theorem independent_cells_card_le {ι : Type*} [DecidableEq ι]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (z : ℝ × ℝ) (cutoff : ℝ) (base level : ℕ) (parent : ℤ)
    (cells : Finset ℤ) {rho B K D : ℝ}
    (hprecision : cutoff / (g.branching : ℝ) ^ level ≤ rho / B ^ 2)
    (hspan : g.width base ≤ B * rho)
    (hancestor : ∀ c ∈ cells,
      g.cellTops tops (fun i => (T i).slope) d cutoff level c ⊆
        g.cellTops tops (fun i => (T i).slope) d cutoff base parent)
    (hsignificant : ∀ c ∈ cells, ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff level c,
      (T i).radius z ≤ K)
    (hindependent : (cells : Set ℤ).Pairwise (fun c e => ¬g.neighbors level rho c e))
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ rho / B ^ 2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
      (I.card : ℝ) ≤ D) : (cells.card : ℝ) ≤ D := by
  classical
  choose rep hrep hsig using fun c : cells => hsignificant c.val c.property
  have hindex (c : cells) : g.index level (T (rep c)).slope = c.val :=
    ((g.mem_cellTops _ _ _ _ _ _ _).mp (hrep c)).2.1
  have hbase (c : cells) : g.index base (T (rep c)).slope = parent :=
    ((g.mem_cellTops _ _ _ _ _ _ _).mp (hancestor c.val c.property (hrep c))).2.1
  have hinj : Function.Injective rep := by
    intro c e h
    apply Subtype.ext
    rw [← hindex c, ← hindex e, h]
  let I : Finset ι := Finset.univ.image rep
  have hmem {i : ι} (hi : i ∈ I) : ∃ c : cells, rep c = i := by
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hi
    exact ⟨c, hc⟩
  have hcard : I.card = cells.card := by
    change (Finset.univ.image rep).card = cells.card
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  rw [← hcard]
  apply hcount I
  · intro i hi
    obtain ⟨c, rfl⟩ := hmem hi
    exact ((g.mem_cellTops _ _ _ _ _ _ _).mp (hrep c)).1
  · intro i hi
    obtain ⟨c, rfl⟩ := hmem hi
    exact hsig c
  · intro i hi
    obtain ⟨c, rfl⟩ := hmem hi
    exact ((g.eligible_iff_precision_le cutoff (d (rep c)) level).mp
      ((g.mem_cellTops _ _ _ _ _ _ _).mp (hrep c)).2.2).trans hprecision
  · intro i hi j hj
    obtain ⟨c, rfl⟩ := hmem hi
    obtain ⟨e, rfl⟩ := hmem hj
    exact (g.same_cell_diameter base ((hbase c).trans (hbase e).symm)).trans hspan
  · intro i hi j hj hij
    obtain ⟨c, rfl⟩ := hmem hi
    obtain ⟨e, rfl⟩ := hmem hj
    have hne : c.val ≠ e.val := fun h => hij (congrArg rep (Subtype.ext h))
    have hfar := hindependent c.property e.property hne
    apply g.slopes_separated_of_not_neighbors level rho
    simpa only [hindex c, hindex e] using hfar

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularExceptionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unshrunk path child costs at most one additional retained cell. -/

noncomputable section

open Set

namespace LipschitzHilbert.AngularGrid

theorem independent_cells_card_le_one_exception {ι : Type*} [DecidableEq ι]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (z : ℝ × ℝ) (cutoff : ℝ) (base level : ℕ) (parent : ℤ)
    (cells : Finset ℤ) (exception : ℤ) {rho B K D : ℝ}
    (hprecision : cutoff / (g.branching : ℝ) ^ level ≤ rho / B ^ 2)
    (hspan : g.width base ≤ B * rho)
    (hancestor : ∀ c ∈ cells,
      g.cellTops tops (fun i => (T i).slope) d cutoff level c ⊆
        g.cellTops tops (fun i => (T i).slope) d cutoff base parent)
    (hsignificant : ∀ c ∈ cells, c ≠ exception →
      ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff level c, (T i).radius z ≤ K)
    (hindependent : (cells : Set ℤ).Pairwise (fun c e => ¬g.neighbors level rho c e))
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ rho / B ^ 2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
      (I.card : ℝ) ≤ D) : (cells.card : ℝ) ≤ D + 1 := by
  classical
  have herase := g.independent_cells_card_le tops T d z cutoff base level parent
    (cells.erase exception) hprecision hspan
    (fun c hc => hancestor c (Finset.mem_of_mem_erase hc))
    (fun c hc => hsignificant c (Finset.mem_of_mem_erase hc)
      (Finset.ne_of_mem_erase hc))
    (hindependent.mono (by intro c hc; exact Finset.mem_of_mem_erase hc)) hcount
  by_cases he : exception ∈ cells
  · have hcard := Finset.card_erase_add_one he
    have hreal : (cells.card : ℝ) = ((cells.erase exception).card : ℝ) + 1 := by
      exact_mod_cast hcard.symm
    linarith
  · simpa only [Finset.erase_eq_of_notMem he] using herase.trans (by linarith : D ≤ D + 1)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSnapshot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier prediction with actual snapshot masses and one path exception. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem sum_cell_mass_le_ancestor {ι X : Type*}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (base level : ℕ) (parent : ℤ) (cells : Finset ℤ)
    (hsub : ∀ c ∈ cells, g.cellTops tops slope precision cutoff level c ⊆
      g.cellTops tops slope precision cutoff base parent) (x : X) :
    (∑ c ∈ cells, g.mass tops slope precision cutoff weight level c x) ≤
      g.mass tops slope precision cutoff weight base parent x := by
  classical
  have hdisjoint : (cells : Set ℤ).PairwiseDisjoint
      (g.cellTops tops slope precision cutoff level) := by
    intro a _ b _ hab
    exact g.cellTops_disjoint tops slope precision cutoff level hab
  change (∑ c ∈ cells, ∑ i ∈ g.cellTops tops slope precision cutoff level c,
    weight i x) ≤ _
  rw [← Finset.sum_biUnion hdisjoint]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.biUnion_subset.mpr hsub)
    (fun i _ _ => hw i x)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockPathMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source predictor's off-child fractions are bounded by the actual
forward path drop. The final ineligible path has drop one even if other
children still continue. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

namespace AngularGrid
variable {ι X : Type*}

theorem sourceBlock_child_fractions (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (lower upper : ℕ) (hlu : lower ≤ upper) (parent : ℤ) (x : X)
    (hn : 0 < g.mass tops slope precision cutoff weight lower parent x) :
    (∑ i : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      g.mass tops slope precision cutoff weight upper i.val x /
        g.mass tops slope precision cutoff weight lower parent x) ≤ 1 := by
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hsub (cell : ℤ) (hc : cell ∈ cells) :
      g.cellTops tops slope precision cutoff upper cell ⊆
        g.cellTops tops slope precision cutoff lower parent := by
    let top := g.sourceBlockTop tops slope precision cutoff lower upper parent ⟨cell,hc⟩
    have htop := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent ⟨cell,hc⟩
    have hs := g.cellTops_subset_ancestor tops slope precision cutoff hp hlu (slope top)
    simpa only [top,htop.2.1,htop.2.2.2] using hs
  have hs := g.sum_cell_mass_le_ancestor tops slope precision cutoff weight hw
    lower upper parent cells hsub x
  rw [Finset.sum_subtype cells (p := fun j => j ∈ cells) (by simp)] at hs
  rw [← Finset.sum_div,div_le_one hn]
  exact hs

theorem sourceBlock_off_fractions (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (lower upper : ℕ) (hlu : lower ≤ upper) (parent : ℤ) (x : X)
    (hn : 0 < g.mass tops slope precision cutoff weight lower parent x)
    (i₀ : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    (∑ i : RemainderIndex i₀,
      g.mass tops slope precision cutoff weight upper i.val.val x /
        g.mass tops slope precision cutoff weight lower parent x) ≤
      1-g.mass tops slope precision cutoff weight upper i₀.val x /
        g.mass tops slope precision cutoff weight lower parent x := by
  have hs := g.sourceBlock_child_fractions tops slope precision cutoff weight hp hw
    lower upper hlu parent x hn
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀] at hs
  linarith

/-- A continuing path selects its actual child cell; its lost fraction
pays for every other continuing child and every terminated top. -/
theorem sourceBlock_continuing_drop {K : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) (x : X)
    (i₀ : g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
      (ShiftedBlocks.endpoint σ (j+1)) (g.index (ShiftedBlocks.endpoint σ j) (slope top)))
    (hi : i₀.val = g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) :
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x
    let c := fun i => g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i x
    let u := pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j
    1-c i₀.val/n = u ∧ (∑ i : RemainderIndex i₀, c i.val.val/n) ≤ u := by
  dsimp only
  have hlu := (ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)
  have he0 := g.eligible_of_le (hp top htop) hlu he
  have hn := g.path_mass_pos tops slope precision cutoff weight hw _ top htop he0 x
  have hdrop : pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j =
      1-g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i₀.val x /
        g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
          (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x := by
    simp only [pathDrop,shiftedPathMass,ite_eq_left he0,ite_eq_left he,hi,sub_div,div_self hn.ne']
  refine ⟨hdrop.symm,?_⟩
  rw [hdrop]
  exact g.sourceBlock_off_fractions tops slope precision cutoff weight hp
    (fun t z => (hw t z).le) _ _ hlu _ x hn i₀

/-- At the terminal block any remaining child can serve as the graph's
exception: both its complement and its defect are bounded by drop one. -/
theorem sourceBlock_terminal_drop {K : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j))
    (hnext : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) (x : X)
    (i₀ : g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
      (ShiftedBlocks.endpoint σ (j+1)) (g.index (ShiftedBlocks.endpoint σ j) (slope top))) :
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x
    let c := fun i => g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i x
    let u := pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j
    1-c i₀.val/n ≤ u ∧ (∑ i : RemainderIndex i₀, c i.val.val/n) ≤ u := by
  dsimp only
  rw [g.shiftedPathDrop_terminal tops slope precision cutoff weight hw σ top htop x j he hnext]
  have hn := g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x
  have hc := g.mass_nonnegative tops slope precision cutoff weight (fun t z => (hw t z).le)
    (ShiftedBlocks.endpoint σ (j+1)) i₀.val x
  have hd : 1-g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i₀.val x /
      g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x ≤ 1 := by
    exact sub_le_self _ (div_nonneg hc hn.le)
  refine ⟨hd,?_⟩
  exact (g.sourceBlock_off_fractions tops slope precision cutoff weight hp
    (fun t z => (hw t z).le) _ _
    ((ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)) _ x hn i₀).trans hd

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedSelectorInsignificant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Insignificant source nodes: the actual physical analyzing coefficients,
alternate synthesis profiles, original length stopping and actual top masks
give an exponentially small amplitude. The same radial shrink therefore
removes the entire node, including the case of an empty eligible top set. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_insignificant_node (C q : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → SourceLabeledLattice N κ Label Item)
      (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound)
      (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ) (v : ℝ × ℝ → ℝ)
      (test : ℝ × ℝ → EuclideanSpace ℂ κ)
      (g : AngularGrid) (w cut Kw D : ℝ) (hw : 0 < w),
      0 < Kw →
      (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
      (∀ t ∈ tops, ∀ j, g.eligible cut (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → (Kb:ℝ) ≤ L^2 →
    ∀ (gap : ℕ → ℝ) (phase : ℕ → ℂ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible cut (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ j, g.eligible cut (w/(T t).length) j → j ≤ M t) →
    ∀ (a Z A maskExponent : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 ≤ A → A ≤ L^q →
      (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
      (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    ∀ (z : ℝ × ℝ),
      (∀ t ∈ tops, (T t).weight Kw D z ≤ C) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D z)) ≤ 3*L →
      let Q := fun t => (P t).withProfile (alt t) (hAlt t)
      let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
      let stop := fun t j => g.lastEligible cut (w/(P t).length j)
        (div_pos hw ((P t).length_pos j))
      let weight := fun t zz => (T t).weight Kw D zz
      (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
        ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-(T t).slope*z.1)‖ ≤
          A*(weight t z)^8) →
      ∀ (level : ℕ) (cell : ℤ),
        (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut level cell, L^(maskExponent+2) ≤ (T t).radius z) →
      let value := fun t j => (Q t).rawBand
        (fun j l u => (T t).mask L maskExponent z • coeff t j l u) 0 j
        z.1 (z.2-(T t).slope*z.1)
      let amplitude := g.sourcePacketAmplitude tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cut weight Kb gap
        (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
        (fun p => value p.1 p.2) phase a z level cell
      let mass := g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight level cell z
      ‖amplitude‖ ≤ (L^(q+6)*Real.exp (-L*Real.log L))*mass ∧
        radialShrink (2*SourceParameters.step L^(-(1/8:ℝ))*mass) amplitude = 0 := by
  have hpoly := eventually_source_snapshot_envelope C q (by linarith)
  have hsmall := eventually_source_insignificant_error (q+6)
  filter_upwards [hpoly,hsmall,eventually_ge_atTop (2:ℝ)] with L hpoly hsmall hL
  intro ι tops T N κ Label Item _ _ P alt hAlt selector v test g w cut Kw D hw hKw
    hlength hzero Kb hKb hKbL gap phase M hM hMmax a Z A maskExponent
    ha0 ha1 hZ hZL hA hAq hz0 hz z hweight htotal
  dsimp only
  intro hinterval level cell hinsignificant
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible cut (w/(P t).length j)
    (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight Kw D zz
  let ε := Real.exp (-L*Real.log L)
  let amplitude := g.sourcePacketAmplitude tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut weight Kb gap
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => rawStop p.1 p.2)
    (fun p => (Q p.1).rawBand
      (fun j l u => (T p.1).mask L maskExponent z • coeff p.1 j l u) 0 p.2
      z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell
  let mass := g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
    cut weight level cell z
  have hprecision (t : ι) (_ht : t ∈ tops) : 0 ≤ w/(T t).length :=
    (div_pos hw (T t).length_pos).le
  have hwpos (t : ι) (zz : ℝ × ℝ) : 0 < weight t zz := (T t).weight_pos hKw D zz
  have hsupported : ∀ t ∈ tops, ∀ j (l : (Q t).labels j) (_u : Item j l),
      rawStop t j ≤ M t := by
    intro t ht j l u
    exact g.source_length_stop_le_of_item tops T P w cut hw M hzero hlength hMmax t ht j l u
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    intro i j hij
    exact min_le_min ((P t).stopping_antitone g cut w hw (hzero t ht) hij) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := min_le_right _ _
  have hmask (t : ι)
      (ht : t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut level cell) : ‖((T t).mask L maskExponent z : ℂ)‖ ≤ ε := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact (T t).mask_tail hL z (hinsignificant t ht)
  have hb := g.sourcePacketAmplitude_node_envelope tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut weight hprecision hwpos hKb gap phase M hM hMmax
    a Z ha0 ha1 hZ hz0 hz Q coeff 0 stop hstop hmax
    (fun _ => z.1) (fun t => z.2-(T t).slope*z.1) A C ε hA hC (Real.exp_pos _).le z
    hweight hinterval 0 N (fun t => ((T t).mask L maskExponent z : ℂ)) level cell hmask
  have hclip := g.sourceBandAmplitude_clip_stop tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut weight Kb gap Q
    (fun t j l u => (T t).mask L maskExponent z • coeff t j l u) 0 rawStop M hsupported
    (fun _ => z.1) (fun t => z.2-(T t).slope*z.1) phase a z level cell
  have heq : amplitude = g.sourcePacketAmplitude tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut weight Kb gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ((T p.1).mask L maskExponent z : ℂ) •
        (Q p.1).rawBand ((Q p.1).restrictCoefficient (coeff p.1) 0 N) 0 p.2
          z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell := by
    dsimp only [amplitude]
    rw [hclip]
    congr 1
    funext p
    rw [SourceLabeledLattice.restrictCoefficient_full,
      SourceLabeledLattice.rawBand_coeff_real_smul]
    exact (IsScalarTower.algebraMap_smul ℂ _ _).symm
  have henv := hpoly A a Z (∑ t ∈ tops, weight t z) Kb
    hA hAq ha0 ha1 hZ hZL hKbL htotal
  have hmass : 0 ≤ mass := by
    unfold mass AngularGrid.mass
    exact Finset.sum_nonneg fun t _ => (hwpos t z).le
  have hbound : ‖amplitude‖ ≤ (L^(q+6)*ε)*mass := by
    rw [← heq] at hb
    calc
      _ ≤ (C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*ε*C^3)*mass := hb
      _ = ((C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*C^3)*ε)*mass := by ring
      _ ≤ (L^(q+6)*ε)*mass := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right henv (Real.exp_pos _).le) hmass
  refine ⟨hbound,?_⟩
  apply source_prediction_shrink_zero hmass
    (Real.rpow_nonneg (SourceParameters.step_pos L).le _) amplitude
  exact hbound.trans (mul_le_mul_of_nonneg_right hsmall hmass)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simultaneous top count supplies exactly the graph bound used after
zero snapshot children are removed. The unshrunk path is the sole exception. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

/-- Only supported snapshot children need significant top representatives. -/
theorem supported_snapshot_independence {ι κ : Type} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (z : ℝ × ℝ) (cutoff : ℝ) (base level : ℕ) (parent : ℤ)
    (cells : Finset ℤ) (representative : cells → ℝ)
    (hcell : ∀ c, g.index (level+1) (representative c) = c.val)
    (hancestor : ∀ c, g.index base (representative c) = parent)
    (hd : ∀ i ∈ tops, 0 ≤ d i) (hle : base ≤ level)
    (X : cells → EuclideanSpace ℂ κ) (path : cells)
    {gap B K D : ℝ} (hD : 2 ≤ D)
    (hprecision : cutoff/(g.branching:ℝ)^(level+1) ≤ gap/B^2)
    (hspan : g.width base ≤ B*gap)
    (hsignificant : ∀ c, X c ≠ 0 → (c:ℤ) ≠ path.val →
      ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff (level+1) c.val,
        (T i).radius z ≤ K)
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ gap/B^2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ B*gap) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → gap ≤ |(T i).slope-(T j).slope|) →
      (I.card:ℝ) ≤ D/100) :
    ∀ S : Finset cells, (∀ c ∈ S, X c ≠ 0 ∨ c = path) →
      (S : Set cells).Pairwise (fun c e => ¬g.neighbors (level+1) gap c.val e.val) →
      (S.card:ℝ) ≤ D := by
  classical
  intro S hsupport hindependent
  have h := g.independent_cells_card_le_one_exception tops T d z cutoff base
    (level+1) parent (S.image Subtype.val) path.val hprecision hspan
    (by
      intro c hc
      obtain ⟨c',_,rfl⟩ := Finset.mem_image.mp hc
      have ha := g.cellTops_subset_ancestor tops (fun i => (T i).slope) d cutoff hd
        (hle.trans (Nat.le_succ _)) (representative c')
      simpa only [hcell,hancestor] using ha)
    (by
      intro c hc hne
      obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
      rcases hsupport c' hc' with hx | he
      · exact hsignificant c' hx hne
      · exact (hne (congrArg Subtype.val he)).elim)
    (by
      intro c hc e he hne
      obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp he
      exact hindependent hc' he' (fun h => hne (congrArg Subtype.val h))) hcount
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  linarith

/-- The shrink threshold makes every supported non-path cell eligible for
this count; no significant representative is imposed on a zero amplitude. -/
theorem supported_shrink_significant {ι κ : Type} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (z : ℝ × ℝ) (cutoff : ℝ) (level : ℕ) (cells : Finset ℤ)
    (A : cells → EuclideanSpace ℂ κ) (c : cells → ℝ) (path : cells)
    {K ε : ℝ} (hε : 0 ≤ ε) (hc : ∀ i, 0 ≤ c i)
    (hsmall : ∀ j, (∀ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff level j.val,
      K < (T i).radius z) → ‖A j‖ ≤ 2*ε*c j) :
    ∀ j, (if j = path then A j else radialShrink (2*ε*c j) (A j)) ≠ 0 →
      j.val ≠ path.val →
      ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff level j.val,
        (T i).radius z ≤ K := by
  classical
  intro j hactive hpath
  have hne : j ≠ path := fun h => hpath (congrArg Subtype.val h)
  rw [ite_eq_right hne] at hactive
  by_contra hnone
  have hsmall' := hsmall j (by
    intro i hi
    exact lt_of_not_ge (fun h => hnone ⟨i,hi,h⟩))
  exact hactive ((radialShrink_eq_zero_iff
    (mul_nonneg (mul_nonneg (by norm_num) hε) (hc j)) (A j)).mpr hsmall')

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All graph hypotheses for the source predictor are supplied by the actual
angular cells, top masses and common separated-top count. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

/-- Geometric data for a nonempty block, using exactly its eligible tops.
The counting conclusion concerns only the shrunken support and the path. -/
theorem source_angular_prediction_data {ι κ : Type} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (cutoff : ℝ) (weight : ι → (ℝ × ℝ) → ℝ)
    (hd : ∀ i ∈ tops, 0 ≤ d i) (hw : ∀ i z, 0 < weight i z)
    (z : ℝ × ℝ) (base level : ℕ) (hle : base ≤ level) (parent : ℤ)
    (cells : Finset ℤ) (representative : cells → ℝ)
    (hcell : ∀ c, g.index (level+1) (representative c) = c.val)
    (hancestor : ∀ c, g.index base (representative c) = parent)
    (hnonempty : ∀ c : cells,
      (g.cellTops tops (fun i => (T i).slope) d cutoff (level+1) c.val).Nonempty)
    (path : cells) (A : cells → EuclideanSpace ℂ κ)
    {gap B K D ε threshold etaMin sR : ℝ}
    (hgap : 0 < gap) (hD : 2 ≤ D) (hε : 0 ≤ ε)
    (hprecision : cutoff/(g.branching:ℝ)^(level+1) ≤ gap/B^2)
    (hspan : g.width base ≤ B*gap)
    (hsmall : ∀ c : cells,
      (∀ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff (level+1) c.val,
        K < (T i).radius z) →
      ‖A c‖ ≤ 2*ε*g.mass tops (fun i => (T i).slope) d cutoff weight (level+1) c.val z)
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ gap/B^2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ B*gap) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → gap ≤ |(T i).slope-(T j).slope|) →
      (I.card:ℝ) ≤ D/100)
    (eta : κ → ℝ) (hetaMin : 0 ≤ etaMin) (heta : ∀ k, etaMin ≤ |eta k|)
    (hthreshold : threshold ≤ gap*etaMin) :
    let c := fun j : cells => g.mass tops (fun i => (T i).slope) d cutoff weight (level+1) j.val z
    let n := g.mass tops (fun i => (T i).slope) d cutoff weight base parent z
    let m := fun j : cells => g.boundaryMass tops (fun i => (T i).slope) d cutoff weight
      base level gap (representative j) z
    let G := fun i j : cells => g.neighbors (level+1) gap i.val j.val
    let f := fun j k => (sR-g.center (level+1) j.val)*eta k
    (∀ j, 0 < c j) ∧ 0 < n ∧ (∑ j, c j/n) ≤ 1 ∧
      (∀ j, orderMass c (closedNeighborhood G j) ≤ m j) ∧
      (∀ i j, i ≠ j → ¬G i j → ∀ k, threshold ≤ |f i k-f j k|) ∧
      (∀ S : Finset cells, (∀ j ∈ S, radialShrink (2*ε*c j) (A j) ≠ 0 ∨ j = path) →
        (S:Set cells).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) := by
  classical
  dsimp only
  let c := fun j : cells => g.mass tops (fun i => (T i).slope) d cutoff weight (level+1) j.val z
  let n := g.mass tops (fun i => (T i).slope) d cutoff weight base parent z
  have hsub (j : ℤ) (hj : j ∈ cells) :
      g.cellTops tops (fun i => (T i).slope) d cutoff (level+1) j ⊆
        g.cellTops tops (fun i => (T i).slope) d cutoff base parent := by
    have h := g.cellTops_subset_ancestor tops (fun i => (T i).slope) d cutoff hd
      (hle.trans (Nat.le_succ _)) (representative ⟨j,hj⟩)
    simpa only [hcell,hancestor] using h
  have hc (j : cells) : 0 < c j := by
    obtain ⟨i,hi⟩ := hnonempty j
    exact g.mass_pos_of_member tops (fun i => (T i).slope) d cutoff weight hw
      (level+1) j.val z hi
  have hn : 0 < n := by
    obtain ⟨i,hi⟩ := hnonempty path
    exact g.mass_pos_of_member tops (fun i => (T i).slope) d cutoff weight hw
      base parent z (hsub path.val path.property hi)
  have htotal : (∑ j : cells, c j/n) ≤ 1 := by
    rw [← Finset.sum_div,div_le_one hn]
    have h := g.sum_cell_mass_le_ancestor tops (fun i => (T i).slope) d cutoff weight
      (fun i z => (hw i z).le) base (level+1) parent cells hsub z
    change (∑ j : cells, g.mass tops (fun i => (T i).slope) d cutoff weight
      (level+1) j.val z) ≤ n
    rw [Finset.sum_subtype cells (p := fun j => j ∈ cells) (by simp)] at h
    exact h
  refine ⟨hc,hn,htotal,?_,?_,?_⟩
  · intro j
    exact g.closed_neighborhood_mass_le_boundary tops (fun i => (T i).slope)
      d cutoff weight hd (fun i z => (hw i z).le) hle hgap.le cells representative parent
      hcell hancestor j z
  · intro i j _ hfar k
    exact hthreshold.trans (g.carrier_frequency_separated (level+1) hetaMin (heta k) hfar)
  · let X := fun j => if j = path then A j else radialShrink (2*ε*c j) (A j)
    have hsig := g.supported_shrink_significant tops T d z cutoff (level+1) cells A c path
      hε (fun j => (hc j).le) hsmall
    intro S hsupport hind
    apply g.supported_snapshot_independence tops T d z cutoff base level parent cells
      representative hcell hancestor hd hle X path hD hprecision hspan hsig hcount S _ hind
    intro j hj
    rcases hsupport j hj with ha | he
    · by_cases he : j = path
      · exact Or.inr he
      · exact Or.inl (by simpa only [X,ite_eq_right he] using ha)
    · exact Or.inr he

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's boundary radius is G^(-1/4) times the parent width.
At a last transition this is exactly G^(3/4) times the child width. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

theorem sourceBoundaryGap_pos (g : AngularGrid) (L : ℝ) (level : ℕ) :
    0 < g.sourceBoundaryGap L level :=
  mul_pos (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _) (g.width_pos level)

theorem sourceBoundaryGap_le_width (g : AngularGrid) (L : ℝ) {h level : ℕ}
    (hle : h ≤ level) : g.sourceBoundaryGap L level ≤ g.width h := by
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  exact (mul_le_of_le_one_left (g.width_pos level).le
    (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num))).trans (g.width_antitone hle)

theorem sourceBoundaryGap_eq_sourceGap (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (level : ℕ) :
    g.sourceBoundaryGap L level = g.sourceGap L (level+1) := by
  have hw := g.source_width_ratio L (Nat.le_succ level) hbranch
  change g.width level = SourceParameters.step L^((level+1)-level)*g.width (level+1) at hw
  simp only [Nat.add_sub_cancel_left,pow_one] at hw
  have hp : SourceParameters.step L^(-(1/4:ℝ))*SourceParameters.step L =
      SourceParameters.step L^(3/4:ℝ) := by
    calc
      _ = SourceParameters.step L^(-(1/4:ℝ))*SourceParameters.step L^(1:ℝ) := by
        rw [Real.rpow_one]
      _ = SourceParameters.step L^(-(1/4:ℝ)+1) :=
        (Real.rpow_add (SourceParameters.step_pos L) _ _).symm
      _ = _ := by norm_num
  rw [sourceBoundaryGap,hw,← mul_assoc,hp]
  rfl

/-- The boundary mass in the shared analytic family is exactly the
neighborhood mass used in the shifted block's graph predictor. -/
theorem source_shifted_boundary_mass {ι X : Type*}
    (g : AngularGrid) (L : ℝ) (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
    (j : ℕ) (s : ℝ) (x : X) :
    g.sourceBoundaryMass tops slope precision cutoff weight (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) (ShiftedBlocks.lastTransition σ j)
      (g.index (ShiftedBlocks.endpoint σ (j+1)) s) x =
    g.boundaryMass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (ShiftedBlocks.lastTransition σ j) (g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) s x := by
  rw [← ShiftedBlocks.lastTransition_succ σ j,
    g.sourceBoundaryMass_path tops slope precision cutoff weight hK,
    ← ShiftedBlocks.endpoint_eq_last_sub σ j,
    g.sourceBoundaryGap_eq_sourceGap L hbranch,ShiftedBlocks.lastTransition_succ]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact eligible-top block family supplies the graph input of the
source predictor. Its boundary masses and transition moduli are the ones
in the shared analytic amplitude. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

/-- The transition coefficient on each actual child satisfies the graph
bound with the actual source boundary mass. -/
theorem source_block_coefficient_bounds {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → (ℝ × ℝ) → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t z, 0 < weight t z) {Kb : ℕ} (hKb : 0 < Kb)
    (gap : ℕ → ℝ) (phase : Fin Kb → ℂ) (σ : Fin Kb) (j : ℕ)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0) (μ : ℝ) (hμ : 0 ≤ μ)
    (hreal : (phase σ).re = μ) (parent : ℤ) (z : ℝ × ℝ) :
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
    let c := fun i : cells => g.mass tops slope precision cutoff weight upper i.val z
    let m := fun i : cells => g.sourceBoundaryMass tops slope precision cutoff weight Kb gap
      (ShiftedBlocks.lastTransition σ j) i.val z
    let lam := fun i : cells => g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight Kb gap
        (fun k => phase (ShiftedBlocks.tag hKb k)) z) lower upper
      (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i))
    (∀ i, ‖lam i‖ = (c i/m i)^μ) ∧ (∀ i, ‖lam i‖ ≤ 1) := by
  dsimp only
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have heq (i : cells) := g.source_shifted_block_norm tops slope precision cutoff weight hp hw
    hKb gap phase σ j hphase (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).1
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).2.2.1 z
  have hindex (i : cells) :=
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).2.2.2
  dsimp only [lower,upper] at hindex heq
  have hnorm (i : cells) :
      ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight Kb gap
        (fun k => phase (ShiftedBlocks.tag hKb k)) z) lower upper
          (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i))‖ =
      (g.mass tops slope precision cutoff weight upper i.val z /
        g.sourceBoundaryMass tops slope precision cutoff weight Kb gap
          (ShiftedBlocks.lastTransition σ j) i.val z)^μ := by
    simpa only [hreal,hindex i] using heq i
  refine ⟨hnorm,?_⟩
  intro i
  have hc := g.path_mass_pos tops slope precision cutoff weight hw upper
    (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).1
    (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i).2.2.1 z
  have hb := (g.source_shifted_block_mass_bounds tops slope precision cutoff weight
    hp (fun t z => (hw t z).le) hKb gap σ j
    (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)) z).1
  dsimp only [lower,upper] at hc hb
  rw [hindex i] at hc hb
  rw [hnorm]
  exact Real.rpow_le_one (div_pos hc (hc.trans_le hb)).le
    ((div_le_one (hc.trans_le hb)).mpr hb) hμ

/-- All positivity, graph-mass, separated-frequency, and supported-count
premises follow from the actual shifted block and the separated-top count. -/
theorem source_block_graph_data {ι κ : Type} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (L : ℝ) (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hKb : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L)) (j : ℕ)
    (tops : Finset ι) (T : ι → SlopeBox) (w : ℝ) (hw : 0 < w)
    (weight : ι → (ℝ × ℝ) → ℝ) (hweight : ∀ t z, 0 < weight t z)
    (parent : ℤ) (z : ℝ × ℝ)
    (path : g.sourceBlockCells tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) parent)
    (A : g.sourceBlockCells tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) parent → EuclideanSpace ℂ κ)
    (K D c0 sR : ℝ) (hD : 2 ≤ D) (hc0 : SourceParameters.step L^(-(1/8:ℝ)) ≤ c0)
    (eta : κ → ℝ) (heta : ∀ k, c0/w ≤ |eta k|)
    (hsmall : ∀ c,
      (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/(SourceParameters.branching L)^2) (ShiftedBlocks.endpoint σ (j+1)) c.val,
        K < (T t).radius z) →
      ‖A c‖ ≤ 2*SourceParameters.step L^(-(1/8:ℝ))*
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/(SourceParameters.branching L)^2) weight
          (ShiftedBlocks.endpoint σ (j+1)) c.val z)
    (hcount : ∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ K) →
      (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤
        SourceParameters.branching L*g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1)) ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ D/100) :
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cells := g.sourceBlockCells tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) lower upper parent
    let c := fun i : cells => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight upper i.val z
    let n := g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight lower parent z
    let m := fun i : cells => g.boundaryMass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight lower (ShiftedBlocks.lastTransition σ j)
      (g.sourceGap L upper) ((T (g.sourceBlockTop tops (fun t => (T t).slope)
        (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2) lower upper parent i)).slope) z
    let G := fun i k : cells => g.neighbors upper (g.sourceGap L upper) i.val k.val
    let f := fun i k => (sR-g.center upper i.val)*eta k
    (∀ i, 0 < c i) ∧ 0 < n ∧ (∑ i, c i/n) ≤ 1 ∧
    (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) ∧
    (∀ i k, i ≠ k → ¬G i k → ∀ v,
      1/(sourceLineScale g L w upper*SourceParameters.step L^(-(1/8:ℝ))) ≤ |f i v-f k v|) ∧
    (∀ S : Finset cells,
      (∀ i ∈ S, radialShrink (2*SourceParameters.step L^(-(1/8:ℝ))*c i) (A i) ≠ 0 ∨ i = path) →
      (S:Set cells).Pairwise (fun i k => ¬G i k) → (S.card:ℝ) ≤ D) := by
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/(SourceParameters.branching L)^2
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let last := ShiftedBlocks.lastTransition σ j
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  let representative := fun i : cells =>
    slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
  have hrep (i : cells) := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i
  have hscales := g.source_shifted_count_scales L hbranch hKb σ j
  have hc00 : 0 ≤ c0 := (Real.rpow_nonneg (SourceParameters.step_pos L).le _).trans hc0
  have hlast : lower ≤ last := (Finset.mem_Ico.mp (ShiftedBlocks.lastTransition_mem hKb σ j)).1
  have hresult := g.source_angular_prediction_data (sR := sR) tops T precision cutoff weight
    (fun t _ => (div_pos hw (T t).length_pos).le) hweight z lower last hlast parent cells
    representative (fun i => by simpa only [last,upper,representative,ShiftedBlocks.lastTransition_succ] using (hrep i).2.2.2)
    (fun i => (hrep i).2.1)
    (fun i => by simpa only [last,upper,ShiftedBlocks.lastTransition_succ] using
      g.sourceBlockCells_nonempty_child tops slope precision cutoff lower upper parent i)
    path A (g.sourceGap_pos L upper) hD
    (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
    (by simpa only [cutoff,last,upper,ShiftedBlocks.lastTransition_succ] using hscales.1)
    hscales.2 (by simpa only [last,upper,ShiftedBlocks.lastTransition_succ] using hsmall)
    hcount eta (div_nonneg hc00 hw.le) heta
    (source_line_fourier_threshold g L hw upper hc0)
  simpa only [last,upper,lower,representative,ShiftedBlocks.lastTransition_succ] using hresult

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSnapshotAmplitudeScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual concentration bound n <= N L^C supplies the amplitude
scale used in the marked prediction, with no extra mass-size premise. -/

noncomputable section
namespace LipschitzHilbert

/-- Raising the concentration mass bound to a phase in [0,1] preserves
its fixed polynomial factor and the manuscript's single power N^mu. -/
theorem source_concentration_phase_power {L N n C μ : ℝ}
    (hL : 1 ≤ L) (hN : 0 < N) (hn : 0 < n) (hC : 0 ≤ C)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hmass : n ≤ L^C*N) :
    n^μ ≤ L^C*(1+N^μ) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  calc
    _ ≤ (L^C*N)^μ := Real.rpow_le_rpow hn.le hmass hμ0
    _ = L^(C*μ)*N^μ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hL0 C) hN.le,← Real.rpow_mul hL0]
    _ ≤ L^C*N^μ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hL (mul_le_of_le_one_right hC hμ1))
      (Real.rpow_nonneg hN.le μ)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hL0 C)

/-- Both mass and node-size premises of the source predictor follow with
C_* = C + Q from the concentration and actual node-amplitude bounds. -/
theorem source_snapshot_amplitude_scale {L N n C Q μ : ℝ}
    (hL : 1 ≤ L) (hN : 0 < N) (hn : 0 < n) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hmass : n ≤ L^C*N) :
    n^μ ≤ L^(Q+C)*(1+N^μ) ∧ L^Q*n^μ ≤ L^(Q+C)*(1+N^μ) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hb := source_concentration_phase_power hL hN hn hC hμ0 hμ1 hmass
  have hproduct : L^Q*(L^C*(1+N^μ)) = L^(Q+C)*(1+N^μ) := by
    rw [← mul_assoc,← Real.rpow_add hL0]
  have hsize : L^Q*n^μ ≤ L^(Q+C)*(1+N^μ) := by
    rw [← hproduct]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL0.le Q)
  exact ⟨(le_mul_of_one_le_left (Real.rpow_nonneg hn.le μ)
    (Real.one_le_rpow hL hQ)).trans hsize,hsize⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceBlockPredictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the normalized predictor to actual eligible-top block masses,
canonical top representatives, and coefficients of the shared source family. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_block_predictor (C Q Cfreq c0 : ℝ)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 2 ≤ D → 0 < N → Real.log N ≤ 2*L →
    ∀ (ι κ : Type) [DecidableEq ι] [Fintype κ]
      (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
    ∀ (hKb : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L)) (j : ℕ)
      (tops : Finset ι) (T : ι → SlopeBox) (w : ℝ) (hw : 0 < w),
    ∀ (weight : ι → (ℝ × ℝ) → ℝ), (∀ t z, 0 < weight t z) →
    ∀ (parent : ℤ) (z : ℝ × ℝ) (origin sR : ℝ) (eta : κ → ℝ),
      (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ),
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cutoff := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
    let representative := fun i : cells => slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
    let c := fun i : cells => g.mass tops slope precision cutoff weight upper i.val z
    let n := g.mass tops slope precision cutoff weight lower parent z
    let lam := fun i : cells => g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) z)
      lower upper (representative i)
    let p := Real.sqrt L
    let μ := phaseMu D p
    let ε := SourceParameters.step L^(-(1/8:ℝ))
    let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
      (sourceLineScale_pos g L hw upper)
    ∀ (i₀ : cells) (A : cells → EuclideanSpace ℂ κ) (K u q : ℝ),
      0 ≤ u → n ≤ L^C*N → (∀ i, ‖A i‖ ≤ L^Q*c i) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      (∀ i : cells, (∀ t ∈ g.cellTops tops slope precision cutoff upper i.val,
        K < (T t).radius z) → ‖A i‖ ≤ 2*ε*c i) →
      (∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ K) →
        (∀ t ∈ I, precision t ≤ g.sourceGap L upper/(SourceParameters.branching L)^2) →
        (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*g.sourceGap L upper) →
        (∀ t ∈ I, ∀ v ∈ I, t ≠ v → g.sourceGap L upper ≤ |slope t-slope v|) →
        (I.card:ℝ) ≤ D/100) →
    ∀ (n' : ℝ → ℝ) (c' : ℝ → cells → ℝ) (A' : ℝ → cells → EuclideanSpace ℂ κ)
      (lam' : ℝ → cells → ℂ),
      (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
      (∀ b ∈ grid.root, ∀ i,
        ‖massPowerScale (n' b) (c' b i) (-(1/p)) (μ-1+1/p) • A' b i-
          diagonalModulation (fun k => (sR-g.center upper i.val)*eta k)
            (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
          ε*(c i/n)^(1/p)*(c i)^μ) →
      (∀ b ∈ grid.root, ∀ i,
        ‖(((n' b)^(μ-1):ℝ):ℂ) • (lam' b i • A' b i)-
          ((n^(μ-1):ℝ):ℂ) • (lam i •
            diagonalModulation (fun k => (sR-g.center upper i.val)*eta k) (A i) b)‖ ≤
          ε*(L^(Q+C)*(1+N^μ))*(c i/n)) →
      (u < 1/2 → lam i₀ ≠ 0 ∧ 0 ≤ q ∧ q < 1 ∧ q ≤ ε ∧
        0 ≤ (c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ∧
        (c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 1 ∧
        1-(c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 2*u ∧
        (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) ∧
        (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-μ-1/p)*‖lam' b i₀‖-
          (c i₀/n)^(1-μ-1/p)*‖lam i₀‖| ≤ 24*ε*u)) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ b d, grid.index (upper-lower) b = grid.index (upper-lower) d → Γ b = Γ d) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p μ (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp
    source_step_tendsto_atTop).eventually (gt_mem_nhds hc0)
  filter_upwards [eventually_source_grid_parameters (Q+C) (2*Cfreq) (by positivity) (by positivity),
    hsmall,eventually_ge_atTop (256:ℝ)] with L hgrid hsmall hL
  intro D N hD hN hlog ι κ _ _ g hbranch hKb σ j tops T w hw weight hweight parent z origin sR eta
    hetaLo hetaHi phase hphase hreal
  dsimp only
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/(SourceParameters.branching L)^2
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  let representative := fun i : cells => slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)
  let c := fun i : cells => g.mass tops slope precision cutoff weight upper i.val z
  let n := g.mass tops slope precision cutoff weight lower parent z
  let m := fun i : cells => g.boundaryMass tops slope precision cutoff weight lower
    (ShiftedBlocks.lastTransition σ j) (g.sourceGap L upper) (representative i) z
  let lam := fun i : cells => g.packetPathProduct
    (g.sourceTransition tops slope precision cutoff weight (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) z)
    lower upper (representative i)
  let p := Real.sqrt L
  let μ := phaseMu D p
  let ε := SourceParameters.step L^(-(1/8:ℝ))
  let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
    (sourceLineScale_pos g L hw upper)
  let frequency := fun i : cells => fun k => (sR-g.center upper i.val)*eta k
  let freqBound := (2*Cfreq)*g.width lower/w
  intro i₀ A K u q hu hmass hA hoff hzero hcount n' c' A' lam' hn' hc' hscaled hnum hdom
  have hlu : lower ≤ upper := (ShiftedBlocks.endpoint_strictMono hKb σ).monotone (Nat.le_succ j)
  obtain ⟨hc,hn,htotal,hm,hsep,hcard⟩ := g.source_block_graph_data L hbranch hKb σ j tops T w hw
    weight hweight parent z i₀ A K D c0 sR hD hsmall.le eta hetaLo hzero hcount
  have hμ := source_phaseMu_small (show 1 ≤ D by linarith) hL
  have hsize := source_snapshot_amplitude_scale (show 1 ≤ L by linarith) hN hn hC hQ
    hμ.1.le (by linarith : μ ≤ 1) hmass
  have hcoefficient := g.source_block_coefficient_bounds tops slope precision cutoff weight
    (fun t _ => (div_pos hw (T t).length_pos).le) hweight hKb (g.sourceBoundaryGap L)
    phase σ j hphase μ hμ.1.le hreal parent z
  have hrep (i : cells) := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent i
  have hmeq (i : cells) :
      g.sourceBoundaryMass tops slope precision cutoff weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (ShiftedBlocks.lastTransition σ j) i.val z = m i := by
    have h := g.source_shifted_boundary_mass L hbranch tops slope precision cutoff weight hKb σ j
      (representative i) z
    have hi : g.index (ShiftedBlocks.endpoint σ (j+1)) (representative i) = i.val := (hrep i).2.2.2
    rwa [hi] at h
  have hlam : ∀ i : cells, ‖lam i‖ ≤ 1 := hcoefficient.2
  have hlamGraph : ∀ i : cells, ‖lam i‖ ≤ (c i/m i)^μ := by
    intro i
    have h := hcoefficient.1 i
    dsimp only at h
    rw [hmeq i] at h
    exact h.le
  have hfreq : 0 ≤ freqBound := by
    dsimp [freqBound]
    exact div_nonneg (mul_nonneg (by positivity) (g.width_pos lower).le) hw.le
  have hspread (i : RemainderIndex i₀) (k : κ) :
      |frequency i.val k-frequency i₀ k| ≤ freqBound := by
    have hcenters := g.centers_close_in_ancestor hlu (representative i.val) (representative i₀)
      ((hrep i.val).2.1.trans (hrep i₀).2.1.symm)
    rw [(hrep i.val).2.2.2,(hrep i₀).2.2.2] at hcenters
    calc
      _ = |g.center upper i.val.val-g.center upper i₀.val| * |eta k| := by
        dsimp only [frequency]
        rw [show (sR-g.center upper i.val.val)*eta k-(sR-g.center upper i₀.val)*eta k =
          -(g.center upper i.val.val-g.center upper i₀.val)*eta k by ring,abs_mul,abs_neg]
      _ ≤ (2*g.width lower)*(Cfreq/w) := mul_le_mul hcenters (hetaHi k)
        (abs_nonneg _) (mul_nonneg (by norm_num) (g.width_pos lower).le)
      _ = freqBound := by dsimp only [freqBound]; ring
  have hmesh : freqBound*(grid.width/(grid.branching:ℝ)^(upper-lower)) ≤
      (2*Cfreq)*SourceParameters.step L^(-(1/16:ℝ)) := by
    have h := source_block_line_carrier g L origin hw lower upper hlu hbranch
      (le_refl ((2*Cfreq)*g.width lower/w))
    apply h.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le
        (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) (by norm_num : -(1/2:ℝ) ≤ -(1/16:ℝ)))
      (by positivity)
  let : DecidableEq cells := fun a b => Classical.propDecidable (a = b)
  have hm' : ∀ i : cells, orderMass c
      (closedNeighborhood (fun i k : cells => g.neighbors upper (g.sourceGap L upper) i.val k.val) i) ≤ m i := by
    intro i
    convert hm i using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext k
    simp only [mem_closedNeighborhood]
    rfl
  have hoff' : (∑ i : RemainderIndex i₀, c i/n) ≤ u := by
    convert hoff using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext i
    simp only [Finset.mem_univ]
  exact hgrid D N (by linarith) hN hlog cells κ grid (upper-lower) le_rfl
    (fun i k => g.neighbors upper (g.sourceGap L upper) i.val k.val)
    (fun _ _ h => g.neighbors_symmetric upper (g.sourceGap L upper) h) c m n hc hn hm' htotal frequency A lam i₀
    (L^Q) freqBound u q (Real.rpow_nonneg (by linarith) _) hfreq hu hsize.1 hsize.2
    hA hlam hlamGraph hoff' hsep hcard hspread hmesh n' c' A' lam' hn' hc' hscaled hnum hdom

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceEmptyPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A block with no continuing eligible-top child has prediction one.
It does not require selecting a fictitious child for the graph argument. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

 theorem source_empty_prediction {ι κ : Type} [Fintype ι] [IsEmpty ι] [Fintype κ]
    (p μ n : ℝ) (hp : 0 < p) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) :
    sourcePredictionValue p μ n c A lam = 1 := by
  simp only [sourcePredictionValue,Finset.univ_eq_empty,Finset.sum_empty,add_zero,
    energyRatio,norm_zero,Real.zero_rpow hp.ne',div_one]

/-- The same normalized local factor API covers an empty continuing
family, even when the distinguished path has ended. -/
theorem source_empty_grid_prediction {ι κ : Type} [Fintype ι] [IsEmpty ι] [Fintype κ]
    (grid : FiniteLineGrid) (level : ℕ) (p μ e : ℝ) (hp : 0 < p) (he : 0 ≤ e)
    (n : ℝ → ℝ) (c : ℝ → ι → ℝ) (A : ℝ → ι → EuclideanSpace ℂ κ)
    (lam : ℝ → ι → ℂ) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧
      Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
      (∀ b, 0 ≤ Γ b) ∧
      (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
      (∀ b d, grid.index level b = grid.index level d → Γ b = Γ d) ∧
      ∀ b ∈ grid.root, sourcePredictionValue p μ (n b) (c b) (A b) (lam b) ≤ Real.exp e*Γ b := by
  let := intervalProbability_isProbability
    (show grid.origin < grid.origin+grid.width by linarith [grid.width_pos])
  refine ⟨fun _ => 1,measurable_const,integrable_const 1,fun _ => zero_le_one,?_,?_,?_⟩
  · simp
  · intro b d _
    rfl
  · intro b _
    rw [source_empty_prediction p μ (n b) hp,mul_one]
    exact Real.one_le_exp_iff.mpr he

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceSupportedSelectorBlockPredictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local source predictor for the original physical packet family.
Its normalized motion and insignificant-child hypotheses are discharged
by the actual packet estimates and the snapshot concentration bounds. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

private theorem modulation_rescale_p1 {κ : Type} [Fintype κ]
    (eta : κ → ℝ) (v : EuclideanSpace ℂ κ) (d b : ℝ) :
    diagonalModulation eta v (d*b) = diagonalModulation (fun k => d*eta k) v b := by
  ext k
  have h : eta k*(d*b) = (d*eta k)*b := by ring
  simp only [diagonalModulation,WithLp.ofLp_toLp,character,h]

theorem eventually_source_supported_selector_block_predictor
    (pProfile q Cmass Cweight Cfreq c0 : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι κ : Type) [Fintype κ]
      (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : ι → SourceLabeledLattice N κ Label Item),
      (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
      (∀ t ∈ tops, (P t).constant ≤ L^pProfile) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound) (Kw : ℝ), 1 ≤ Kw →
      (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw Dweight) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w : ℝ) (hw : 0 < w),
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
      (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(P t).length j) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ × ℝ) (eta : κ → ℝ),
      (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
      (∀ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z ≤ Cweight) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z)) ≤ 3*L →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let wave := fun zz c => g.sourcePacketAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => (Q p.1).rawBand
        (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
        0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1))
      (fun k => phase (ShiftedBlocks.tag hKb k)) a zz upper c
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤ A*(weight t z)^8) →
    ∀ (parent : ℤ) (sR origin u : ℝ), g.index lower sR = parent →
    let cells := g.sourceBlockCells tops slope precision cut lower upper parent
    let n := fun zz => g.mass tops slope precision cut weight lower parent zz
    let c := fun zz (i : cells) => g.mass tops slope precision cut weight upper i.val zz
    let lam := fun zz (i : cells) => g.packetPathProduct
      (g.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
      lower upper (slope (g.sourceBlockTop tops slope precision cut lower upper parent i))
    let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
      (sourceLineScale_pos g L hw upper)
    ∀ i₀ : cells, 0 ≤ u → n z ≤ L^Cmass*Nmass →
      1-c z i₀/n z ≤ u →
      origin ≤ 0 → 0 ≤ origin+grid.width →
      (∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
        (∀ t ∈ I, precision t ≤ g.sourceGap L upper/(SourceParameters.branching L)^2) →
        (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*g.sourceGap L upper) →
        (∀ t ∈ I, ∀ v ∈ I, t ≠ v → g.sourceGap L upper ≤ |slope t-slope v|) →
        (I.card:ℝ) ≤ D/100) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ b d, grid.index (upper-lower) b = grid.index (upper-lower) d → Γ b = Γ d) ∧
        ∀ b ∈ grid.root,
          sourcePredictionValue (Real.sqrt L) (phaseMu D (Real.sqrt L))
            (n (SlopeBox.lineShift sR b z)) (c (SlopeBox.lineShift sR b z))
            (fun i => wave (SlopeBox.lineShift sR b z) i.val) (lam (SlopeBox.lineShift sR b z)) ≤
            Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  obtain ⟨Lm,_,_,hmotion⟩ := source_supported_selector_normalized_motion pProfile q Dweight Bslots
    Cweight Cfreq hpProfile hq hCweight hCfreq
  filter_upwards [eventually_ge_atTop Lm,eventually_ge_atTop (256:ℝ),
    eventually_source_block_predictor Cmass (q+6) Cfreq c0 hCmass (by linarith) hCfreq hc0,
    eventually_source_block_path_motion (Dweight:ℝ) (Nat.cast_nonneg Dweight),
    eventually_source_snapshot_envelope Cweight q (by linarith),
    eventually_source_supported_selector_insignificant_node Cweight q hCweight,
    eventually_source_insignificant_error (q+6)]
    with L hLm hL hpred hpath hpoly hinsig hsmallError
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ j M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN z eta hetaLo hetaHi hPeta hweight htotal
  dsimp only
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
  let stop := fun t k => min (rawStop t k) (M t)
  let wave := fun zz c => g.sourcePacketAmplitude tops slope precision cut weight
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => rawStop p.1 p.2)
    (fun p => (Q p.1).rawBand
      (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
      0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1))
    (fun k => phase (ShiftedBlocks.tag hKb k)) a zz upper c
  intro hconc parent sR origin u hparent
  let cells := g.sourceBlockCells tops slope precision cut lower upper parent
  let n := fun zz => g.mass tops slope precision cut weight lower parent zz
  let c := fun zz (i : cells) => g.mass tops slope precision cut weight upper i.val zz
  let lam := fun zz (i : cells) => g.packetPathProduct
    (g.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
    lower upper (slope (g.sourceBlockTop tops slope precision cut lower upper parent i))
  let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
    (sourceLineScale_pos g L hw upper)
  intro i₀ hu hmass hdrop horigin0 horigin1 hcount
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hB : 1 ≤ SourceParameters.branching L :=
    one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hlu : lower ≤ upper := (ShiftedBlocks.endpoint_strictMono hKb σ).monotone (Nat.le_succ j)
  have hsteps : ((upper-lower:ℕ):ℝ) ≤ L^2 :=
    (Nat.cast_le.mpr (show upper-lower ≤ SourceParameters.blockCount L by
      have ht := ShiftedBlocks.endpoint_width_le σ j
      dsimp only [upper,lower]
      omega)).trans hKbL
  have hmu := source_phaseMu_small (show 1 ≤ D by linarith) hL
  have hp : 2 ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    nlinarith
  have hphase0 (k : ℕ) : 0 ≤ (phase (ShiftedBlocks.tag hKb k)).re := by
    by_cases heq : ShiftedBlocks.tag hKb k = σ
    · simpa only [heq,hreal] using hmu.1.le
    · rw [hother _ heq]
  have hwpos (t : ι) (zz : ℝ × ℝ) : 0 < weight t zz := (T t).weight_pos hKw0 _ zz
  have hprecision (t : ι) (_ : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hsupported : ∀ t ∈ tops, ∀ k (l : (Q t).labels k) (_u : Item k l),
      rawStop t k ≤ M t := by
    intro t ht k l u
    exact g.source_length_stop_le_of_item tops T P w cut hw M hzero hlength hMmax t ht k l u
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    intro i k hik
    exact min_le_min ((P t).stopping_antitone g cut w hw (hzero t ht) hik) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (k : Fin N) : stop t k ≤ M t := min_le_right _ _
  have hconc0 (t : ι) (ht : t ∈ tops) (l u : ℕ) (hlu : l ≤ u) (huN : u ≤ N) :
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-slope t*z.1)‖ ≤ A*(weight t z)^8 := by
    have hc := hconc t ht l u hlu huN (z.2-slope t*z.1) (by
      change |(z.2-slope t*z.1)-(z.2-slope t*z.1)| ≤ (T t).width
      rw [sub_self,abs_zero]
      exact (T t).width_pos.le)
    exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hc
  have hsize (i : cells) : ‖wave z i.val‖ ≤ L^(q+6)*c z i := by
    have he := g.source_snapshot_masked_node_bound tops slope precision cut weight hprecision hwpos
      hKb (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) M hM hMmax
      a Z ha0 ha1 hZ0 (fun _ _ k _ => hphase0 k)
      (fun _ _ k _ => hphase _) Q coeff 0 stop hstop hmax
      (fun _ => z.1) (fun t => z.2-slope t*z.1) A Cweight hA0 hCweight z hweight hconc0
      (fun t => (T t).mask L maskExponent z) upper i.val
      (fun t _ => by
        change |topSincMask L maskExponent _ _| ≤ 1
        rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
        exact topSincMask_le_one _ _ _ _)
    have heq := g.sourceBandAmplitude_clip_stop tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) Q
      (fun t j l u => (T t).mask L maskExponent z • coeff t j l u) 0 rawStop M hsupported
      (fun _ => z.1) (fun t => z.2-slope t*z.1)
      (fun k => phase (ShiftedBlocks.tag hKb k)) a z upper i.val
    rw [← heq] at he
    exact he.trans (mul_le_mul_of_nonneg_right
      (hpoly A a Z (∑ t ∈ tops, weight t z) (SourceParameters.blockCount L)
        hA0 hAq ha0 ha1 hZ0 hZ hKbL htotal)
      (g.mass_nonnegative tops slope precision cut weight (fun t zz => (hwpos t zz).le) upper i.val z))
  have hsmall (i : cells)
      (hi : ∀ t ∈ g.cellTops tops slope precision cut upper i.val,
        L^(maskExponent+2) < (T t).radius z) :
      ‖wave z i.val‖ ≤ 2*SourceParameters.step L^(-(1/8:ℝ))*c z i := by
    have he := hinsig ι tops T N κ Label Item P alt hAlt selector v test g w cut Kw
      (Dweight:ℝ) hw hKw0 hlength hzero (SourceParameters.blockCount L) hKb hKbL
      (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) M hM hMmax
      a Z A maskExponent ha0 ha1 hZ0 hZ hA0 hAq
      (fun _ _ k _ => hphase0 k) (fun _ _ k _ => hphase _) z hweight htotal hconc0
      upper i.val (fun t ht => (hi t ht).le)
    exact he.1.trans (mul_le_mul_of_nonneg_right
      (hsmallError.trans (by nlinarith [Real.rpow_nonneg (SourceParameters.step_pos L).le (-(1/8:ℝ))]))
      (g.mass_nonnegative tops slope precision cut weight (fun t zz => (hwpos t zz).le) upper i.val z))
  have hrep (i : cells) := g.sourceBlockTop_spec tops slope precision cut lower upper parent i
  have hchild (zz : ℝ × ℝ) (i : cells) : 0 < c zz i := by
    have he := g.path_mass_pos tops slope precision cut weight hwpos upper
      (g.sourceBlockTop tops slope precision cut lower upper parent i)
      (hrep i).1 (hrep i).2.2.1 zz
    simpa only [(hrep i).2.2.2] using he
  have hn (zz : ℝ × ℝ) : 0 < n zz := by
    have he := g.path_mass_pos tops slope precision cut weight hwpos lower
      (g.sourceBlockTop tops slope precision cut lower upper parent i₀) (hrep i₀).1
      (g.eligible_of_le (hprecision _ (hrep i₀).1) hlu (hrep i₀).2.2.1) zz
    simpa only [(hrep i₀).2.1] using he
  have hoff : (∑ i : RemainderIndex i₀, c z i/n z) ≤ u :=
    (g.sourceBlock_off_fractions tops slope precision cut weight hprecision
      (fun t zz => (hwpos t zz).le) lower upper hlu parent z (hn z) i₀).trans hdrop
  have hroot (b : ℝ) (hb : b ∈ grid.root) : |b| ≤ sourceLineScale g L w upper := by
    change origin ≤ b ∧ b < origin+sourceLineScale g L w upper at hb
    change 0 ≤ origin+sourceLineScale g L w upper at horigin1
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hroot' (b : ℝ) (hb : b ∈ grid.root) :
      |b| ≤ w/(g.width upper*Real.sqrt (g.branching:ℝ)) := by
    simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using hroot b hb
  have hblock := (g.source_shifted_width_bounds L hbranch hKb σ j).2
  have hmove (b : ℝ) (hb : b ∈ grid.root) (i : cells) := by
    have hs (t : ι) (ht : t ∈ g.cellTops tops slope precision cut upper i.val) :
        g.index lower (slope t) = g.index lower sR := by
      have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
      rw [hparent,← (hrep i).2.1]
      exact g.index_eq_of_le hlu (ht'.2.1.trans (hrep i).2.2.2.symm)
    have hm := hmotion L hLm ι tops T N κ Label Item P hslots hP alt hAlt Kw hKw hgeom
      selector hselector hselector1 v hv test htest htest1 g w (SourceParameters.branching L) hw hB hbranch
      hwidth hlength hzero (SourceParameters.blockCount L) hKb hKbL (g.sourceBoundaryGap L)
      lower upper hlu M hM hMmax
      (fun _ _ k hk _ => ⟨(g.sourceBoundaryGap_pos L k).le,g.sourceBoundaryGap_le_width L hk⟩)
      sR i.val hs hblock b (hroot' b hb) z eta hetaHi hPeta
      (fun k => phase (ShiftedBlocks.tag hKb k)) a Z A maskExponent ha0 ha1 hZ0 hZ hmask
      (fun _ _ k _ => hphase0 k) (fun _ _ k _ => hphase _) hweight hA0 hAq htotal hconc
      lower le_rfl hlu hsteps (g.sourceBlockTop tops slope precision cut lower upper parent i)
      (g.sourceBlockTop_mem_child tops slope precision cut lower upper parent i)
      (Real.sqrt L) (phaseMu D (Real.sqrt L)) (by linarith) hmu.1.le (by linarith)
    dsimp only at hm
    have hi : g.index lower (T (g.sourceBlockTop tops slope precision cut lower upper parent i)).slope =
        parent := (hrep i).2.1
    rw [hi] at hm
    simpa only [modulation_rescale_p1] using hm
  have hsizePower := source_snapshot_amplitude_scale (show 1 ≤ L by linarith) hNmass (hn z)
    hCmass (show 0 ≤ q+6 by linarith) hmu.1.le (by linarith : phaseMu D (Real.sqrt L) ≤ 1) hmass
  have ha : 0 ≤ 1-phaseMu D (Real.sqrt L)-1/Real.sqrt L := by
    have hi : 1/Real.sqrt L ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hp
    linarith
  have hpdata := hpath ι g tops T w Kw hw hKw hbranch hwidth hKb σ j hsteps
    phase Z (phaseMu D (Real.sqrt L)) (Real.sqrt L) u hZ0 hZ hphase hother hreal
    hmu.1.le (by linarith) (by linarith) ha hu
    (g.sourceBlockTop tops slope precision cut lower upper parent i₀)
    (hrep i₀).1 (hrep i₀).2.2.1 sR ((hrep i₀).2.1.trans hparent.symm) z
  dsimp only at hpdata
  rw [(hrep i₀).2.1,(hrep i₀).2.2.2] at hpdata
  obtain ⟨err,herr0,herr1,herrε,hlam0,hcoef0,hcoef1,hdef,hpathMove⟩ := hpdata hdrop
  apply hpred D Nmass hD hNmass hlogN ι κ g hbranch hKb σ j tops T w hw weight hwpos
    parent z origin sR eta hetaLo hetaHi phase hother hreal i₀ (fun i => wave z i.val)
    (L^(maskExponent+2)) u err hu hmass hsize hoff hsmall hcount
    (fun b => n (SlopeBox.lineShift sR b z))
    (fun b => c (SlopeBox.lineShift sR b z))
    (fun b i => wave (SlopeBox.lineShift sR b z) i.val)
    (fun b => lam (SlopeBox.lineShift sR b z))
    (fun b _ => hn _) (fun b _ i => hchild _ i)
  · intro b hb i
    exact (hmove b hb i).1
  · intro b hb i
    exact (hmove b hb i).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsizePower.1
        (Real.rpow_nonneg (SourceParameters.step_pos L).le _))
      (div_pos (hchild z i) (hn z)).le)
  · intro _
    exact ⟨hlam0,herr0,herr1,herrε,hcoef0,hcoef1,hdef,
      fun b hb => (hpathMove b (hroot b hb)).1,
      fun b hb => (hpathMove b (hroot b hb)).2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSnapshotWindow
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The predictor uses displacement from a chosen good snapshot. Translate
its exact probability law and line-grid indices back to physical coordinates. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

/-- Translation of the normalized interval law, with its full remainder
already included in the original predictor construction. -/
theorem intervalProbability_map_add (a b t : ℝ) :
    (intervalProbability (a-t) (b-t)).map (fun x => x+t) = intervalProbability a b := by
  have hpre : (fun x : ℝ => x+t) ⁻¹' Icc a b = Icc (a-t) (b-t) := by
    ext x
    simp only [mem_preimage,mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  unfold intervalProbability
  rw [Measure.map_smul,← hpre,
    ← Measure.restrict_map (by fun_prop) measurableSet_Icc,
    Measure.IsAddRightInvariant.map_add_right_eq_self]
  rw [show b-t-(a-t) = b-a by ring]

namespace FiniteLineGrid

theorem atSnapshot_mem_root (g : FiniteLineGrid) (x₀ x : ℝ) :
    x-x₀ ∈ (g.atSnapshot x₀).root ↔ x ∈ g.root := by
  change (g.origin-x₀ ≤ x-x₀ ∧ x-x₀ < (g.origin-x₀)+g.width) ↔
    (g.origin ≤ x ∧ x < g.origin+g.width)
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem atSnapshot_rawIndex (g : FiniteLineGrid) (x₀ x : ℝ) (level : ℕ) :
    (g.atSnapshot x₀).rawIndex level (x-x₀) = g.rawIndex level x := by
  classical
  unfold rawIndex
  rw [g.atSnapshot_mem_root]
  simp only [atSnapshot,show x-x₀-(g.origin-x₀) = x-g.origin by ring]

theorem atSnapshot_index (g : FiniteLineGrid) (x₀ x : ℝ) (level : ℕ) :
    (g.atSnapshot x₀).index level (x-x₀) = g.index level x := by
  apply Fin.ext
  exact g.atSnapshot_rawIndex x₀ x (min level g.depth)

/-- A predictor built in displacement coordinates has exactly the same
normalized average and fine-cell constancy in the physical window. -/
theorem snapshot_factor_transfer (g : FiniteLineGrid) (x₀ : ℝ) (level : ℕ)
    (P : ℝ → ℝ) (hP : Measurable P)
    (hint : Integrable P (intervalProbability (g.atSnapshot x₀).origin
      ((g.atSnapshot x₀).origin+(g.atSnapshot x₀).width)))
    (hpos : ∀ b, 0 ≤ P b)
    (havg : (∫ b, P b ∂intervalProbability (g.atSnapshot x₀).origin
      ((g.atSnapshot x₀).origin+(g.atSnapshot x₀).width)) ≤ 1)
    (hconst : ∀ b c, (g.atSnapshot x₀).index level b =
      (g.atSnapshot x₀).index level c → P b = P c) :
    Measurable (fun x => P (x-x₀)) ∧
    Integrable (fun x => P (x-x₀)) (intervalProbability g.origin (g.origin+g.width)) ∧
    (∀ x, 0 ≤ P (x-x₀)) ∧
    (∫ x, P (x-x₀) ∂intervalProbability g.origin (g.origin+g.width)) ≤ 1 ∧
    (∀ x z, g.index level x = g.index level z → P (x-x₀) = P (z-x₀)) := by
  have hmap : (intervalProbability (g.atSnapshot x₀).origin
      ((g.atSnapshot x₀).origin+(g.atSnapshot x₀).width)).map (fun b => b+x₀) =
      intervalProbability g.origin (g.origin+g.width) := by
    simpa only [atSnapshot,sub_add_eq_add_sub] using
      intervalProbability_map_add g.origin (g.origin+g.width) x₀
  have hemb : MeasurableEmbedding (fun b : ℝ => b+x₀) :=
    (Homeomorph.addRight x₀).isClosedEmbedding.measurableEmbedding
  refine ⟨hP.comp (by fun_prop),?_,fun x => hpos _,?_,?_⟩
  · rw [← hmap]
    exact hemb.integrable_map_iff.mpr (by simpa only [Function.comp_def,add_sub_cancel_right] using hint)
  · rw [← hmap,hemb.integral_map]
    simpa only [add_sub_cancel_right] using havg
  · intro x z hxz
    exact hconst _ _ (by rw [g.atSnapshot_index,g.atSnapshot_index,hxz])

end FiniteLineGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceSupportedSelectorWindowPredictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical source predictor transported from its chosen snapshot
to an arbitrary line window containing that snapshot. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_window_predictor
    (pProfile q Cmass Cweight Cfreq c0 : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι κ : Type) [Fintype κ]
      (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : ι → SourceLabeledLattice N κ Label Item),
      (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
      (∀ t ∈ tops, (P t).constant ≤ L^pProfile) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound) (Kw : ℝ), 1 ≤ Kw →
      (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw Dweight) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w : ℝ) (hw : 0 < w),
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
      (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(P t).length j) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ × ℝ) (eta : κ → ℝ),
      (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
      (∀ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z ≤ Cweight) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z)) ≤ 3*L →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let wave := fun zz c => g.sourcePacketAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => (Q p.1).rawBand
        (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
        0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1))
      (fun k => phase (ShiftedBlocks.tag hKb k)) a zz upper c
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤ A*(weight t z)^8) →
    ∀ (parent : ℤ) (sR origin u : ℝ), g.index lower sR = parent →
    let cells := g.sourceBlockCells tops slope precision cut lower upper parent
    let n := fun zz => g.mass tops slope precision cut weight lower parent zz
    let c := fun zz (i : cells) => g.mass tops slope precision cut weight upper i.val zz
    let lam := fun zz (i : cells) => g.packetPathProduct
      (g.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
      lower upper (slope (g.sourceBlockTop tops slope precision cut lower upper parent i))
    let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
      (sourceLineScale_pos g L hw upper)
    ∀ i₀ : cells, 0 ≤ u → n z ≤ L^Cmass*Nmass →
      1-c z i₀/n z ≤ u →
      origin ≤ z.1 → z.1 ≤ origin+grid.width →
      (∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
        (∀ t ∈ I, precision t ≤ g.sourceGap L upper/(SourceParameters.branching L)^2) →
        (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*g.sourceGap L upper) →
        (∀ t ∈ I, ∀ v ∈ I, t ≠ v → g.sourceGap L upper ≤ |slope t-slope v|) →
        (I.card:ℝ) ≤ D/100) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ b d, grid.index (upper-lower) b = grid.index (upper-lower) d → Γ b = Γ d) ∧
        ∀ b ∈ grid.root,
          sourcePredictionValue (Real.sqrt L) (phaseMu D (Real.sqrt L))
            (n ((b,z.2+sR*(b-z.1)))) (c ((b,z.2+sR*(b-z.1))))
            (fun i => wave ((b,z.2+sR*(b-z.1))) i.val) (lam ((b,z.2+sR*(b-z.1)))) ≤
            Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  filter_upwards [eventually_source_supported_selector_block_predictor pProfile q Cmass Cweight Cfreq c0
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0] with L hpred
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ j M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN z eta hetaLo hetaHi hPeta hweight htotal
  dsimp only
  intro hconc parent sR origin u hparent i₀ hu hmass hdrop horigin0 horigin1 hcount
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
    (sourceLineScale_pos g L hw upper)
  obtain ⟨P0,hP0,hint,hpos,havg,hconst,hcompare⟩ := hpred ι κ tops T N Label Item P
    hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w hw hbranch
    hwidth hlength hzero hKb hKbL σ j M hM hMmax phase a Z A maskExponent D Nmass
    ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask hD hNmass hlogN z eta
    hetaLo hetaHi hPeta hweight htotal hconc parent sR (origin-z.1) u hparent i₀
    hu hmass hdrop (by linarith) (by
      change 0 ≤ origin-z.1+sourceLineScale g L w upper
      change z.1 ≤ origin+sourceLineScale g L w upper at horigin1
      linarith) hcount
  obtain ⟨hm,hi,hp,ha,hc⟩ := grid.snapshot_factor_transfer z.1 (upper-lower)
    P0 hP0 hint hpos havg hconst
  refine ⟨fun x => P0 (x-z.1),hm,hi,hp,ha,hc,?_⟩
  intro x hx
  have hb : x-z.1 ∈ (grid.atSnapshot z.1).root :=
    (grid.atSnapshot_mem_root z.1 x).mpr hx
  have he := hcompare (x-z.1) hb
  have heq : SlopeBox.lineShift sR (x-z.1) z = (x,z.2+sR*(x-z.1)) := by
    unfold SlopeBox.lineShift
    congr 1; ring
  rw [heq] at he
  exact he

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the actual continuing path child when it exists. In the terminal
block any existing child may be used as the graph exception, since the path
drop is one. A genuinely empty child family remains a separate case. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem sourceBlock_exists_path_exception {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hK : 0 < K) (σ : Fin K) (j : ℕ)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j))
    (hne : (g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
      (ShiftedBlocks.endpoint σ (j+1))
      (g.index (ShiftedBlocks.endpoint σ j) (slope top))).Nonempty) :
    ∃ i₀ : g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
        (ShiftedBlocks.endpoint σ (j+1))
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)),
      ∀ x : X,
      let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x
      let c := fun i => g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i x
      let u := pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j
      1-c i₀.val/n ≤ u ∧ (∑ i : PhaseCombinatorics.RemainderIndex i₀, c i.val.val/n) ≤ u := by
  by_cases hnext : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))
  · let i₀ : g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
        (ShiftedBlocks.endpoint σ (j+1)) (g.index (ShiftedBlocks.endpoint σ j) (slope top)) :=
      ⟨g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top),
        g.mem_sourceBlockCells_of_top tops slope precision cutoff _ _ _ hp
          ((ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)) top htop rfl hnext⟩
    refine ⟨i₀,fun x => ?_⟩
    have h := g.sourceBlock_continuing_drop tops slope precision cutoff weight hp hw hK σ j
      top htop hnext x i₀ rfl
    exact ⟨h.1.le,h.2⟩
  · obtain ⟨i,hi⟩ := hne
    refine ⟨⟨i,hi⟩,fun x => ?_⟩
    exact g.sourceBlock_terminal_drop tops slope precision cutoff weight hp hw hK σ j
      top htop he hnext x ⟨i,hi⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceSupportedSelectorPathPredictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual path drop pays for the physical source predictor. The
continuing, terminal, and empty-child cases are all included. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_path_predictor_oai
    (pProfile q Cmass Cweight Cfreq c0 : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι κ : Type) [Fintype κ]
      (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : ι → SourceLabeledLattice N κ Label Item),
      (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
      (∀ t ∈ tops, (P t).constant ≤ L^pProfile) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound) (Kw : ℝ), 1 ≤ Kw →
      (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw Dweight) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w : ℝ) (hw : 0 < w),
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
      (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(P t).length j) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ × ℝ) (eta : κ → ℝ),
      (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
      (∀ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z ≤ Cweight) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z)) ≤ 3*L →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let wave := fun zz c => g.sourcePacketAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => (Q p.1).rawBand
        (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
        0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1))
      (fun k => phase (ShiftedBlocks.tag hKb k)) a zz upper c
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤ A*(weight t z)^8) →
    ∀ (parent : ℤ) (sR origin u : ℝ), g.index lower sR = parent →
    let cells := g.sourceBlockCells tops slope precision cut lower upper parent
    let n := fun zz => g.mass tops slope precision cut weight lower parent zz
    let c := fun zz (i : cells) => g.mass tops slope precision cut weight upper i.val zz
    let lam := fun zz (i : cells) => g.packetPathProduct
      (g.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
      lower upper (slope (g.sourceBlockTop tops slope precision cut lower upper parent i))
    let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
      (sourceLineScale_pos g L hw upper)
    ∀ (top : ι), top ∈ tops → g.index lower (slope top) = parent →
      g.eligible cut (precision top) lower →
      0 ≤ u → n z ≤ L^Cmass*Nmass →
      pathDrop (g.shiftedPathMass tops slope precision cut weight σ top z) j ≤ u →
      origin ≤ z.1 → z.1 ≤ origin+grid.width →
      (∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
        (∀ t ∈ I, precision t ≤ g.sourceGap L upper/(SourceParameters.branching L)^2) →
        (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*g.sourceGap L upper) →
        (∀ t ∈ I, ∀ v ∈ I, t ≠ v → g.sourceGap L upper ≤ |slope t-slope v|) →
        (I.card:ℝ) ≤ D/100) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ b d, grid.index (upper-lower) b = grid.index (upper-lower) d → Γ b = Γ d) ∧
        ∀ b ∈ grid.root,
          sourcePredictionValue (Real.sqrt L) (phaseMu D (Real.sqrt L))
            (n ((b,z.2+sR*(b-z.1)))) (c ((b,z.2+sR*(b-z.1))))
            (fun i => wave ((b,z.2+sR*(b-z.1))) i.val) (lam ((b,z.2+sR*(b-z.1)))) ≤
            Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  filter_upwards [eventually_source_supported_selector_window_predictor pProfile q Cmass Cweight Cfreq c0
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0,eventually_ge_atTop (1:ℝ)]
    with L hpred hL
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ j M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN z eta hetaLo hetaHi hPeta hweight htotal
  dsimp only
  intro hconc parent sR origin u hparent top htop htopParent helower hu hmass hpathdrop
    horigin0 horigin1 hcount
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
  let cells := g.sourceBlockCells tops slope precision cut lower upper parent
  let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
    (sourceLineScale_pos g L hw upper)
  by_cases hne : cells.Nonempty
  · have hprec (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
    have hwpos (t : ι) (zz : ℝ × ℝ) : 0 < weight t zz :=
      (T t).weight_pos (zero_lt_one.trans_le hKw) _ zz
    have hchoice : ∃ i₀ : cells,
        1-g.mass tops slope precision cut weight upper i₀.val z /
          g.mass tops slope precision cut weight lower parent z ≤
        pathDrop (g.shiftedPathMass tops slope precision cut weight σ top z) j := by
      clear hparent
      subst parent
      obtain ⟨i₀,hi₀⟩ := g.sourceBlock_exists_path_exception tops slope precision cut weight
        hprec hwpos hKb σ j top htop helower hne
      exact ⟨i₀,(hi₀ z).1⟩
    obtain ⟨i₀,hi₀⟩ := hchoice
    have hidrop := hi₀.trans hpathdrop
    exact hpred ι κ tops T N Label Item P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
      test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ j M hM hMmax
      phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq
      hmask hD hNmass hlogN z eta hetaLo hetaHi hPeta hweight htotal hconc parent sR
      origin u hparent i₀ hu hmass hidrop horigin0 horigin1 hcount
  · let : IsEmpty cells := ⟨fun i => hne ⟨i.val,i.property⟩⟩
    have hp : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
    exact source_empty_grid_prediction grid (upper-lower) (Real.sqrt L)
      (phaseMu D (Real.sqrt L)) (SourceParameters.step L^(-(1/32:ℝ))*u)
      hp (mul_nonneg (Real.rpow_nonneg (SourceParameters.step_pos L).le _) hu) _ _ _ _

end LipschitzHilbert.AngularGrid

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor_oai := @OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor_oai
