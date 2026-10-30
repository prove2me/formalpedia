-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T19:54:29.216822+00:00
-- url     : https://prove2.me/submissions/27ee6996-84fe-4673-8866-fe755600acc2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_eventually_source_central_from_paths_types
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_assigned_parent_vertex_integral

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

theorem planeDivide_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℝ × ℝ) :
    planeDivide a b ha hb z = (z.1 / a, z.2 / b) := by
  rfl

theorem map_planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.map (planeDivide a b ha hb) (volume.prod volume) =
      (ENNReal.ofReal |a| * ENNReal.ofReal |b|) • (volume.prod volume) := by
  have hmap (c : ℝ) (hc : c ≠ 0) :
      Measure.map (fun x : ℝ => x * c⁻¹) volume = ENNReal.ofReal |c| • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, inv_inv, mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hc))
  change Measure.map (Prod.map (fun x => x * a⁻¹) (fun y => y * b⁻¹)) _ = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop), hmap a ha, hmap b hb,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

theorem integrable_planeDivide (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun z => f (planeDivide a b ha hb z)) (volume.prod volume) := by
  apply (integrable_map_equiv (planeDivide a b ha hb) f).mp
  rw [map_planeDivide]
  exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

theorem topProfile_nonnegative (D : ℝ) (z : ℝ × ℝ) : 0 ≤ topProfile D z :=
  Real.rpow_nonneg (by positivity) _

theorem topProfile_continuous (D : ℝ) : Continuous (topProfile D) := by
  unfold topProfile
  apply Continuous.rpow_const (by fun_prop)
  intro z
  left
  positivity

/-- The fixed normalized profile is integrable once its decay exponent exceeds
its two-dimensional domain. -/
theorem topProfile_integrable {D : ℝ} (hD : 2 < D) :
    Integrable (topProfile D) (volume.prod volume) := by
  have hd : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < D := by simpa using hD
  have h := integrable_one_add_norm (μ := (volume.prod volume)) hd
  apply h.mono' (topProfile_continuous D).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (topProfile_nonnegative D z)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have hmax : max |z.1| |z.2| ≤ |z.1| + |z.2| :=
    max_le (by linarith [abs_nonneg z.2]) (by linarith [abs_nonneg z.1])
  linarith

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- The actual top weight is integrable, uniformly over positions and slopes. -/
theorem weight_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 2 < D) :
    Integrable (T.weight K D) (volume.prod volume) := by
  have hf := integrable_planeDivide (topProfile D) (topProfile_integrable hD)
    (K * T.length) (K * T.width)
    (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne')
  have hs := (slopeShear_measurePreserving (-T.slope)).integrable_comp_of_integrable hf
  have ht := hs.comp_sub_right (T.x, T.y)
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq]
  exact ht.const_mul _

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeBoxMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sinc mask in the manuscript's actual slope coordinates, with
parameters fixed uniformly before choosing the finite top family. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
namespace SlopeBox

theorem mask_continuous (T : SlopeBox) (L A : ℝ) : Continuous (T.mask L A) := by
  unfold mask topSincMask sincProductMask horizontal transverse
  apply Continuous.pow
  apply Continuous.mul
  · apply Real.continuous_sinc.comp
    fun_prop
  · apply Real.continuous_sinc.comp
    fun_prop

end SlopeBox

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineWeightAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested line averaging against the manuscript's actual top weight. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem continuous_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    Continuous (T.weight K D) := by
  have hr : Continuous (fun z => 1 + T.radius z / K) := by
    unfold radius horizontal transverse
    fun_prop
  unfold weight
  apply continuous_const.mul
  exact hr.rpow_const fun z => Or.inl (ne_of_gt (by
    have h := T.radius_nonnegative z
    positivity))

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeData
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_actualZ (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).actualZ j l u = P.actualZ j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u +
      (oldSlope - newSlope) * P.actualX j
        (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [SourceLabeledLattice.actualZ, actualZ, actualX, referenceFamily,
    SourceLabeledLattice.length, length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (k : κ) :
    (Q).physicalPacket newSlope j l u k = P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  let l₀ := P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l
  have hx := P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  have hz := P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx, hz]
  have hc : P.actualZ j l₀ u + (oldSlope - newSlope) * P.actualX j l₀ u +
      newSlope * P.actualX j l₀ u = P.actualZ j l₀ u + oldSlope * P.actualX j l₀ u := by ring
  have hs : newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope)) =
      oldSlope + P.rowSlope j l₀ := by ring
  change physicalPlanarPacket (P.profile j l₀ u k) _ _ (P.length j) P.width
    (newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope))) (P.frequency k) _ _ = _
  rw [hc, hs]

end PacketLatticeData
end LipschitzHilbert

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_multiplier_coefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l u =
    P.physicalMultiplierCoefficient oldSlope b v g j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  ext k
  simp only [SourceLabeledLattice.physicalMultiplierCoefficient,physicalMultiplierCoefficient,
    analyzingCoefficient,WithLp.ofLp_toLp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
    (P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency j l u k)
  dsimp only [referenceSelector]
  rw [hp]

end LipschitzHilbert.PacketLatticeData

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTerminalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least ineligible shifted endpoint provides a finite terminal
generation without enlarging the source root line window past its top.
This includes exactly one final block after the last eligible endpoint. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem firstIneligibleShiftedBlock_spec {K : ℕ} (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hK : 0 < K) (σ : Fin K) :
    ¬g.eligible cutoff precision
      (ShiftedBlocks.endpoint σ (g.firstIneligibleShiftedBlock cutoff precision hp hK σ)) :=
  Nat.find_spec (g.exists_shifted_terminal cutoff precision hp hK σ)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledStoppingVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original masked physical packets, grouped by their actual stopping
levels, have the same fixed length-variation bound used in the reference
event. This includes clamped prefixes and every disjoint unary run. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem physicalMaskedValue_length_sum (y x : ℝ) (j : Fin N) :
    (∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
      P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q) =
        P.physicalMaskedBand alt hAlt t b v g T L A y j x := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true, if_true]
    ext k
    simp only [Fintype.sum_sigma,physicalMaskedValue,physicalMaskedBand,
      WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  · intro k _ hkj
    simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
  · simp

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mask in §4 is dominated by the actual hierarchy weight with
dilation `L^(A+2)`. Consequently the negative weight power in every
residual coefficient costs at most one, uniformly in the spatial point. -/

noncomputable section
namespace LipschitzHilbert

theorem topSincMask_abs_le_one (L A x y : ℝ) : |topSincMask L A x y| ≤ 1 := by
  simpa only [abs_of_nonneg (topSincMask_nonneg L A x y)] using
    topSincMask_le_one L A x y

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketRegroup
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of original packet amplitudes by assigned top and
length. This connects the individual-packet residual estimates to the
same top-band amplitudes appearing in the physical path integrals. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem weighted_sum_fibers {σ ι E : Type*} [AddCommMonoid E] [Module ℂ E]
    (packets : Finset σ) (groups : Finset ι) (key : σ → ι)
    (hkey : ∀ q ∈ packets, key q ∈ groups) (weight : ι → ℂ) (value : σ → E) :
    (∑ i ∈ groups, weight i • ∑ q ∈ packets.filter (fun q => key q = i), value q) =
      ∑ q ∈ packets, weight (key q) • value q := by
  calc
    _ = ∑ i ∈ groups, ∑ q ∈ packets.filter (fun q => key q = i), weight (key q) • value q := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hkey _

namespace AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sourcePacketAmplitude_grouped_sum {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (lengthIndex : σ → Fin N) (stop : ι → Fin N → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned
      (fun q => stop (assigned q) (lengthIndex q)) value phase a x level cell =
    ∑ q ∈ packets, g.sourceGroupedCoefficient tops slope precision cutoff weight K gap
      stop phase a x level cell (assigned q,lengthIndex q) • value q := by
  simp only [sourcePacketAmplitude,packetAmplitude,packetSet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  unfold sourceGroupedCoefficient sourcePacketBase
  split_ifs <;> simp only [smul_smul,zero_smul]

/-- The original packet amplitude equals its literal top/length regrouping.
No estimate, choice of signs, or bound on the number of fibers is used. -/
theorem sourcePacketAmplitude_regroup {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (lengthIndex : σ → Fin N) (stop : ι → Fin N → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned
      (fun q => stop (assigned q) (lengthIndex q)) value phase a x level cell =
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ∑ q ∈ packets.filter (fun q => (assigned q,lengthIndex q) = p), value q)
      phase a x level cell := by
  rw [g.sourcePacketAmplitude_grouped_sum tops slope precision cutoff weight K gap packets
    assigned lengthIndex stop value phase a x level cell,
    g.sourcePacketAmplitude_grouped_sum tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst Prod.snd stop]
  symm
  convert weighted_sum_fibers packets (tops ×ˢ (Finset.univ : Finset (Fin N)))
    (fun q => (assigned q,lengthIndex q))
    (fun q hq => Finset.mem_product.mpr ⟨hassigned q hq,Finset.mem_univ _⟩)
    (g.sourceGroupedCoefficient tops slope precision cutoff weight K gap stop phase a x level cell)
    value using 1; congr 1; ext q; simp
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

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

theorem eventually_source_supported_selector_node_envelope (C q : ℝ) (hC : 1 ≤ C) :
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
      let value := fun t j => (Q t).rawBand
        (fun j l u => (T t).mask L maskExponent z • coeff t j l u) 0 j
        z.1 (z.2-(T t).slope*z.1)
      let amplitude := g.sourcePacketAmplitude tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cut weight Kb gap
        (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
        (fun p => value p.1 p.2) phase a z level cell
      let mass := g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight level cell z
      ‖amplitude‖ ≤ L^(q+6)*mass := by
  have hpoly := eventually_source_snapshot_envelope C q (by linarith)
  filter_upwards [hpoly,eventually_ge_atTop (2:ℝ)] with L hpoly hL
  intro ι tops T N κ Label Item _ _ P alt hAlt selector v test g w cut Kw D hw hKw
    hlength hzero Kb hKb hKbL gap phase M hM hMmax a Z A maskExponent
    ha0 ha1 hZ hZL hA hAq hz0 hz z hweight htotal
  dsimp only
  intro hinterval level cell
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible cut (w/(P t).length j)
    (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight Kw D zz
  let ε : ℝ := 1
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
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    have hanti := (P t).stopping_antitone g cut w hw (hzero t ht)
    intro i j hij
    exact min_le_min (hanti hij) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := min_le_right _ _
  have hsupported (t : ι) (ht : t ∈ tops) (j : Fin N) (l : (P t).labels j)
      (u : Item j l) : rawStop t j ≤ M t := by
    apply hMmax t ht
    have hj := g.eligible_lastEligible cut (w/(P t).length j)
      (div_pos hw ((P t).length_pos j)) (hzero t ht j)
    exact (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hw.le ((P t).length_pos j) (hlength t ht j l u))
      (by positivity)).trans hj
  have hmask (t : ι)
      (_ht : t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut level cell) : ‖((T t).mask L maskExponent z : ℂ)‖ ≤ ε := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact topSincMask_abs_le_one L maskExponent ((T t).horizontal z) ((T t).transverse z)
  have hb := g.sourcePacketAmplitude_node_envelope tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut weight hprecision hwpos hKb gap phase M hM hMmax
    a Z ha0 ha1 hZ hz0 hz Q coeff 0 stop hstop hmax
    (fun _ => z.1) (fun t => z.2-(T t).slope*z.1) A C ε hA hC (show 0 ≤ ε by norm_num [ε]) z
    hweight hinterval 0 N (fun t => ((T t).mask L maskExponent z : ℂ)) level cell hmask
  have heq : amplitude = g.sourcePacketAmplitude tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut weight Kb gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ((T p.1).mask L maskExponent z : ℂ) •
        (Q p.1).rawBand ((Q p.1).restrictCoefficient (coeff p.1) 0 N) 0 p.2
          z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell := by
    dsimp only [amplitude]
    apply Eq.trans ?_
      (show g.sourcePacketAmplitude tops (fun t => (T t).slope)
          (fun t => w/(T t).length) cut weight Kb gap
          (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
          (fun p => (Q p.1).rawBand
            (fun j l u => (T p.1).mask L maskExponent z • coeff p.1 j l u) 0 p.2
            z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell = _ from ?_)
    · apply g.sourcePacketAmplitude_stop_congr_of_zero
      intro p hp
      have ht : p.1 ∈ tops := (Finset.mem_product.mp hp).1
      by_cases hs : rawStop p.1 p.2 ≤ M p.1
      · exact Or.inl (min_eq_left hs).symm
      · right
        apply (Q p.1).rawBand_eq_zero_of_no_item
        intro l u
        exact hs (hsupported p.1 ht p.2 l u)
    · congr 1
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
        (mul_le_mul_of_nonneg_right henv (show 0 ≤ ε by norm_num [ε])) hmass
  simpa only [ε,mul_one] using hbound

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported assigned-top estimates apply to the original individual
physical packets. These identities retain their analyzing coefficients,
alternate profiles, stopping levels, masks and source transitions. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- A constant top mask can be placed in the raw coefficients exactly. -/
theorem physicalMaskedBand_const_eq_rawBand (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : SlopeBox) (L A : ℝ)
    (z : ℝ×ℝ) (j : Fin N) :
    P.physicalMaskedBand alt hAlt t b v f (fun _ _ _ => T) L A (z.2-t*z.1) j z.1 =
      (P.withProfile alt hAlt).rawBand
        (fun j l u => T.mask L A z • P.physicalMultiplierCoefficient t b v f j l u)
        0 j z.1 (z.2-t*z.1) := by
  ext k
  have hpoint : (z.1,(z.2-t*z.1)+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  simp only [physicalMaskedBand,rawBand,vectorPacketSynthesis,packetSynthesis_apply,
    WithLp.ofLp_toLp,Fintype.sum_sigma,hpoint]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro u _
  have hp := congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
    ((P.withProfile alt hAlt).raw_eq_physical_slice 0 j l u k (z.2-t*z.1) t)
  change (P.withProfile alt hAlt).raw 0 j l u k (z.2-t*z.1) z.1 =
    (P.withProfile alt hAlt).physicalPacket t j l u k (z.1,(z.2-t*z.1)+t*z.1) at hp
  rw [hpoint] at hp
  simp only [PiLp.smul_apply,Complex.real_smul,hp]
  ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataMaskedBand
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical length bands of unrestricted masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

theorem physicalMaskedValue_length_sum (y x : ℝ) (j : Fin N) :
    (∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
      P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q) =
        P.physicalMaskedBand alt hAlt t b v g T L A y j x := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true, if_true]
    ext k
    simp only [Fintype.sum_sigma,physicalMaskedValue,physicalMaskedBand,
      WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  · intro k _ hkj
    simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
  · simp

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedPhysical
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact assignment and length regrouping of the physical packet sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)

theorem assignedPhysicalBands_eq (z : ℝ×ℝ) (p : τ×Fin N) :
    P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z p =
      ∑ q∈packets.filter (fun q => (assigned q,q.1)=p),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A finite source sum supported on the reference labels equals the
sum in the literal restricted family. -/
theorem sum_referenceLabels_of_zero {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l →
      ∀ u, f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have hrestrict := Equiv.sum_comp (P.referenceLabelsEquiv oldSlope newSlope referenceLength cone w j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j //
      ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero (fun u _ => hzero l.val l.property u)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (P.referenceCondition oldSlope newSlope referenceLength cone w j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact hrestrict.trans hsum

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top restrictions with common label and item types. The top
is part of the label, so each top family contains exactly its own packets
and the family-valued concentration and path estimates apply literally. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem sum_assignedTopPackets {E : Type*} [AddCommMonoid E]
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (f : P.PacketIndex → E) :
    (∑ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      f ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩) =
      ∑ q ∈ packets.filter (fun q => assigned q = top), f q := by
  have h := Equiv.sum_comp (P.assignedTopPacketEquiv packets assigned top)
    (fun q => f q.val)
  exact h.trans (Finset.sum_subtype _ (p := fun q =>
    q ∈ packets.filter (fun q => assigned q = top)) (by simp) f).symm

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopAlternate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-type assigned top families have exactly the original
physical bands, including original selector coefficients and top masks. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem sum_assignedTopPackets_filter {E : Type*} [AddCommMonoid E]
    (top : τ) (f : P.PacketIndex → E) (keep : P.PacketIndex → Prop) :
    (∑ q ∈ Finset.univ.filter (fun q : (P.assignedTopFamily packets assigned top).PacketIndex =>
      keep ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩),
      f ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩) =
      ∑ q ∈ (packets.filter (fun q => assigned q = top)).filter keep, f q := by
  simpa only [Finset.sum_filter] using
    P.sum_assignedTopPackets packets assigned top (fun q => if keep q then f q else 0)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceProperties
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical selector centers are invariant under recentering.
Restricting to the reference cone can only decrease their local count. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u :=
  P.referenceFamily_multiplier_coefficient oldSlope newSlope R cone w F hw hcone hF hwide hfrequency b v f j l u

theorem referenceFamily_alternate_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))).physicalPacket
      newSlope j l u k = (P.withProfile alt hAlt).physicalPacket oldSlope j (orig j l) u k :=
  (P.withProfile alt hAlt).referenceFamily_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l u k

/-- A selected set supported in the reference cone has the identical
sum after the literal label restriction, including empty item fibers. -/
theorem sum_referenceFamily_selected {E : Type*} [AddCommMonoid E]
    (S : Finset P.PacketIndex) (f : P.PacketIndex → E)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    (∑ u ∈ (Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S),
      f ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) = ∑ u ∈ S, f u := by
  have hs : (Finset.univ.filter fun u : P.PacketIndex => u ∈ S) = S := by
    ext u
    simp
  conv_rhs => rw [← hs,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact P.sum_referenceLabels_of_zero oldSlope newSlope R cone w j
    (fun l u => if (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ S then f ⟨j,⟨l,u⟩⟩ else 0)
    (by
      intro l hl u
      rw [ite_eq_right]
      exact fun hu => hl (hS ⟨j,⟨l,u⟩⟩ hu))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assigned-top constructor preserves the original selectors,
packet spectra, and local label count. Its geometry is supplied by the
actual selected packets; the global longest-scale bound remains explicit. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

theorem assignedTopLabel_first (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j) : l.val.1 = top :=
  Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1

theorem assignedTopItem_mem (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (⟨j,⟨l.val.2,u.val⟩⟩ : P.PacketIndex) ∈ packets := u.property.1

theorem assignedTopItem_assignment (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    assigned ⟨j,⟨l.val.2,u.val⟩⟩ = top :=
  u.property.2.trans (P.assignedTopLabel_first packets assigned top j l)


section Reference
variable (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
  (hF : 0 ≤ F) (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w

theorem assignedTopReference_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : (Q).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l).val.2) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l).val.2 u.val :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency (P.assignedTopSelector packets assigned top b) v f j l u

end Reference

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top bands retain the actual top mask and physical packet. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem assignedTopFamily_physicalMaskedValue (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (q : (P.assignedTopFamily packets assigned top).PacketIndex) :
    (P.assignedTopFamily packets assigned top).physicalMaskedValue
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val) L A z q =
      P.physicalMaskedValue alt hAlt t b v f T L A z
        ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩ := rfl

theorem assignedTopFamily_physicalMaskedBand (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).physicalMaskedBand
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val)
      L A (z.2-t*z.1) j z.1 =
      P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z (top,j) := by
  let Q := P.assignedTopFamily packets assigned top
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hband := Q.physicalMaskedValue_length_sum
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
    (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val) L A
    (z.2-t*z.1) z.1 j
  rw [hpoint] at hband
  apply hband.symm.trans
  have hs := P.sum_assignedTopPackets_filter packets assigned top
    (P.physicalMaskedValue alt hAlt t b v f T L A z) (fun q => q.1 = j)
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q : Q.PacketIndex => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v f T L A z
          ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩ := by
      apply Finset.sum_congr rfl
      intro q _
      exact P.assignedTopFamily_physicalMaskedValue packets assigned alt hAlt top t b v f T L A z q
    _ = ∑ q ∈ (packets.filter (fun q => assigned q = top)).filter (fun q => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := by
      convert hs using 1 <;> first | (with_reducible_and_instances rfl) | (apply Finset.sum_congr)
      · ext q
        simp
      · intro q _
        rfl
      · ext q
        simp
      · intro q _
        rfl
    _ = _ := by
      rw [P.assignedPhysicalBands_eq alt hAlt t b v f T L A packets assigned z (top,j)]
      apply Finset.sum_congr
      · ext q
        simp only [Finset.mem_filter,Prod.mk.injEq,and_assoc]
      · intro q _
        rfl

/-- The mask on an assigned family is its single assigned top mask. -/
theorem assignedTopFamily_single_mask (top : τ) (T : τ → SlopeBox) :
    (fun j (l : (P.assignedTopFamily packets assigned top).labels j)
      (u : P.AssignedTopItem packets assigned j l) =>
        T (assigned ⟨j,⟨l.val.2,u.val⟩⟩)) = fun _ _ _ => T top := by
  funext j l u
  have ht : l.val.1 = top := Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1
  rw [u.property.2,ht]

theorem assignedTopFamily_topMaskBand (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : τ → SlopeBox)
    (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).physicalMaskedBand
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun _ _ _ => T top) L A (z.2-t*z.1) j z.1 =
      P.assignedPhysicalBands alt hAlt t b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) := by
  have h := P.assignedTopFamily_physicalMaskedBand packets assigned alt hAlt top t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z j
  rw [P.assignedTopFamily_single_mask packets assigned top T] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original assigned-packet cone condition gives the full-family
condition required to recenter each common-type top family. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assignedTopFamily_referenceCondition (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (oldSlope newSlope R cone w : ℝ)
    (hcondition : ∀ u ∈ packets, assigned u = top →
      P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    ∀ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      (P.assignedTopFamily packets assigned top).referenceCondition
        oldSlope newSlope R cone w q.1 q.2.1 := by
  intro q
  have hq := (P.assignedTopPacketEquiv packets assigned top q).property
  change P.referenceCondition oldSlope newSlope R cone w q.1 q.2.1.val.2
  exact hcondition _ (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceMasked
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact masked amplitudes and residuals survive the local reference change. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F)
  (hwide : cone*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMaskedValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (u : (Q).PacketIndex) :
    (Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A z u =
    P.physicalMaskedValue alt hAlt oldSlope b v f T L A z ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ := by
  ext k
  simp only [physicalMaskedValue,SourceLabeledLattice.physicalMaskedValue,WithLp.ofLp_toLp]
  rw [P.referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]
  rw [P.referenceFamily_alternate_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceBand
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recentring an entire already-selected top family preserves its
physical length bands. Only the literal short-cone membership is needed. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceFamily_physicalMaskedBand_all (P : PacketLatticeData N κ Label Item)
    (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hcondition : ∀ u : P.PacketIndex,
      P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    Q.physicalMaskedBand (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l))
      L A (z.2-newSlope*z.1) j z.1 =
    P.physicalMaskedBand alt hAlt oldSlope b v f T L A (z.2-oldSlope*z.1) j z.1 := by
  intro Q orig
  have hpoint (s : ℝ) : (z.1,z.2-s*z.1+s*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hQ := Q.physicalMaskedValue_length_sum (fun j l => alt j (orig j l))
    (fun j l => hAlt j (orig j l)) newSlope (fun j l => b j (orig j l)) v f
    (fun j l => T j (orig j l)) L A (z.2-newSlope*z.1) z.1 j
  rw [hpoint newSlope] at hQ
  have hP := P.physicalMaskedValue_length_sum alt hAlt oldSlope b v f T L A
    (z.2-oldSlope*z.1) z.1 j
  rw [hpoint oldSlope] at hP
  apply hQ.symm.trans
  apply Eq.trans _ hP
  have h := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency Finset.univ
    (fun u => if u.1 = j then P.physicalMaskedValue alt hAlt oldSlope b v f T L A z u else 0)
    (fun u _ => hcondition u)
  simp only [Finset.sum_filter,Finset.mem_univ,ite_true, if_true] at h
  simp only [Finset.sum_filter]
  calc
    _ = ∑ q : Q.PacketIndex, if q.1 = j then
        P.physicalMaskedValue alt hAlt oldSlope b v f T L A z
          ⟨q.1,⟨orig q.1 q.2.1,q.2.2⟩⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split_ifs
      · exact P.referenceFamily_physicalMaskedValue oldSlope newSlope R cone w F
          hw hcone hF hwide hfrequency alt hAlt b v f T L A z q
      · rfl
    _ = _ := by convert h using 1

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only nonempty assigned scales impose a reference length restriction. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
  (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (T : τ → SlopeBox)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w

/-- Empty long scales impose no artificial restriction on the global
longest-scale field. Every retained packet has the true assigned length. -/
theorem assignedTopReference_supported_length
    (hshort : ∀ q ∈ packets, P.length q.1 ≤ (T (assigned q)).length)
    (j : Fin N) (l : (Q).labels j) (u : P.AssignedTopItem packets assigned j l) :
    (Q).length j ≤ (T top).length := by
  have h := hshort ⟨j,⟨(orig j l).val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j (orig j l) u)
  have ht := P.assignedTopItem_assignment packets assigned top j (orig j l) u
  change P.length j ≤ (T top).length
  simpa only [ht] using h


/-- The supported assigned/reference bands remain the original physical
synthesis with its original top mask, including empty scales. -/
theorem assignedTopReference_topMaskBand_all
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope R cone w q.1 q.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L maskExponent : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (Q).physicalMaskedBand
      (fun j l u k => alt j (orig j l).val.2 u.val k)
      (fun j l u k => hAlt j (orig j l).val.2 u.val k)
      (T top).slope (fun j l => b j (orig j l).val.2) v f
      (fun _ _ _ => T top) L maskExponent (z.2-(T top).slope*z.1) j z.1 =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent packets assigned z (top,j) := by
  have href := (P.assignedTopFamily packets assigned top).referenceFamily_physicalMaskedBand_all
    oldSlope (T top).slope R cone w F hw hcone hF hwide hfrequency
    (P.assignedTopFamily_referenceCondition packets assigned top oldSlope (T top).slope
      R cone w hcondition)
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top)
    (P.assignedTopSelector packets assigned top b) v f (fun _ _ _ => T top) L maskExponent z j
  exact href.trans (P.assignedTopFamily_topMaskBand packets assigned alt hAlt top oldSlope
    b v f T L maskExponent z j)


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual masked packet sum agrees with the bounded reference
families used in the supported stopped-path estimates. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

/-- The common-type recentered family used in the actual top envelopes. -/
local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

local notation "halt" => assignedReferenceAlternate_bound P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt

variable (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

local notation "selector" => assignedReferenceSelector P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency b

theorem assignedReference_rawBand_original (L A : ℝ) (z : ℝ×ℝ) (top : τ) (j : Fin N)
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1) :
    ((Q top).withProfile (alts top) (halt top)).rawBand
      (fun j l u => (T top).mask L A z •
        (Q top).physicalMultiplierCoefficient (T top).slope (selector top) v f j l u)
      0 j z.1 (z.2-(T top).slope*z.1) =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) := by
  have hr := (Q top).physicalMaskedBand_const_eq_rawBand (alts top) (halt top)
    (T top).slope (selector top) v f (T top) L A z j
  exact hr.symm.trans (P.assignedTopReference_topMaskBand_all packets assigned top
    oldSlope (R top) cone w F hw hcone hF hwide hfrequency T hcondition alt hAlt b v f L A z j)

/-- Original packets, their literal top/length fibers and the recentered
raw bands have exactly the same source amplitude. -/
theorem assignedReference_packetAmplitude_original
    (grid : AngularGrid) (tops : Finset τ) (precision : τ → ℝ) (cut : ℝ)
    (weight : τ → (ℝ×ℝ) → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (hcondition : ∀ q ∈ packets,
      P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a L A : ℝ)
    (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) :
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      packets assigned (fun q => stop (assigned q) q.1)
      (P.physicalMaskedValue alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) phase a z level cell =
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ((Q p.1).withProfile (alts p.1) (halt p.1)).rawBand
        (fun j l u => (T p.1).mask L A z •
          (Q p.1).physicalMultiplierCoefficient (T p.1).slope (selector p.1) v f j l u)
        0 p.2 z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell := by
  rw [grid.sourcePacketAmplitude_regroup tops (fun t => (T t).slope) precision cut weight K gap
    packets assigned hassigned (fun q => q.1) stop
    (P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) phase a z level cell]
  apply congrArg (fun values : τ×Fin N → EuclideanSpace ℂ κ =>
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      values phase a z level cell)
  funext p
  rw [P.assignedReference_rawBand_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z p.1 p.2
    (fun q hq hqt => by simpa only [hqt] using hcondition q hq)]
  exact (P.assignedPhysicalBands_eq alt hAlt oldSlope b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z p).symm


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedVertexPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assigned-reference concentration supplies the actual original
packet envelope used in stopped paths and the finite-tree vertex bound.
All constants are chosen before the packet family. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_original_node_envelope (C q : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ : Type) (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
      (f : ℝ×ℝ → EuclideanSpace ℂ κ)
      (grid : AngularGrid) (cut Kw D : ℝ), 0 < Kw →
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
      (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
        (R (assigned u)) cone w u.1 u.2.1) →
      (∀ j, grid.eligible cut (w/P.length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → (Kb:ℝ) ≤ L^2 →
    ∀ (gap : ℕ → ℝ) (phase : ℕ → ℂ) (M : τ → ℕ),
      (∀ t ∈ tops, grid.eligible cut (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ j, grid.eligible cut (w/(T t).length) j → j ≤ M t) →
    ∀ (a Z A maskExponent : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 ≤ A → A ≤ L^q →
      (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
      (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    ∀ (z : ℝ×ℝ),
      (∀ t ∈ tops, (T t).weight Kw D z ≤ C) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D z)) ≤ 3*L →
      let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency
      let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency
      let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt
      let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt
      (∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
        ‖((Q t).withProfile (alts t) (halt t)).rawInterval
          (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
            j (orig t j l) u.val) 0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤
            A*((T t).weight Kw D z)^8) →
      ∀ level cell,
        ‖grid.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut (fun t zz => (T t).weight Kw D zz) Kb gap packets assigned
          (fun u => grid.lastEligible cut (w/P.length u.1) (div_pos hw (P.length_pos u.1)))
          (P.physicalMaskedValue alt hAlt oldSlope b v f
            (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent z)
          phase a z level cell‖ ≤
            L^(q+6)*grid.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
              cut (fun t zz => (T t).weight Kw D zz) level cell z := by
  filter_upwards [AngularGrid.eventually_source_supported_selector_node_envelope C q hC]
    with L hbound
  intro τ tops T N κ Label Item _ _ P packets assigned oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f grid cut Kw D hKw
    hassigned hshort hcondition hzero Kb hKb hKbL gap phase M hM hMmax
    a Z A maskExponent ha0 ha1 hZ hZL hA hAq hz0 hz z hweight htotal
  dsimp only
  intro hinterval level cell
  let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency
  let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency
  let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt
  let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt
  let selector := P.assignedReferenceSelector packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency b
  have hcoeff t : (Q t).physicalMultiplierCoefficient (T t).slope (selector t) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned t
      oldSlope (T t).slope (R t) cone w F hw hcone hF hwide hfrequency b v f j l u
  have hi t (ht : t ∈ tops) (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N) :
      ‖((Q t).withProfile (alts t) (halt t)).rawInterval
        ((Q t).physicalMultiplierCoefficient (T t).slope (selector t) v f)
        0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤ A*((T t).weight Kw D z)^8 := by
    rw [hcoeff t]
    exact hinterval t ht lower upper hlu hu
  have hb := hbound τ tops T N κ (fun j => τ×P.labels j)
    (P.AssignedTopItem packets assigned) Q alts halt selector v f grid w cut Kw D hw hKw
    (fun t _ j l u => P.assignedTopReference_supported_length packets assigned t
      oldSlope (R t) cone w F hw hcone hF hwide hfrequency T hshort j l u)
    (fun _ _ => hzero) Kb hKb hKbL gap phase M hM hMmax
    a Z A maskExponent ha0 ha1 hZ hZL hA hAq hz0 hz z hweight htotal hi level cell
  have heq := P.assignedReference_packetAmplitude_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f grid tops (fun t => w/(T t).length)
    cut (fun t zz => (T t).weight Kw D zz) Kb gap hassigned hcondition
    (fun _ j => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j)))
    phase a L maskExponent z level cell
  exact (congrArg norm heq).le.trans hb

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedLinearEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported-scale node estimate with its explicit linear phase
factor. No restriction is placed on the size of the imaginary phases;
this is the bound used for the Gaussian tail in §11. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem source_supported_selector_linear_envelope (C L : ℝ) (hC : 1 ≤ C) :
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
    ∀ (Kb : ℕ), 0 < Kb →
    ∀ (gap : ℕ → ℝ) (phase : ℕ → ℂ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible cut (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ j, g.eligible cut (w/(T t).length) j → j ≤ M t) →
    ∀ (a Z A maskExponent : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → 0 ≤ A →
      (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
      (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    ∀ (z : ℝ × ℝ),
      (∀ t ∈ tops, (T t).weight Kw D z ≤ C) →
      let Q := fun t => (P t).withProfile (alt t) (hAlt t)
      let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
      let stop := fun t j => g.lastEligible cut (w/(P t).length j)
        (div_pos hw ((P t).length_pos j))
      let weight := fun t zz => (T t).weight Kw D zz
      (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
        ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-(T t).slope*z.1)‖ ≤
          A*(weight t z)^8) →
      ∀ (level : ℕ) (cell : ℤ),
      let value := fun t j => (Q t).rawBand
        (fun j l u => (T t).mask L maskExponent z • coeff t j l u) 0 j
        z.1 (z.2-(T t).slope*z.1)
      let amplitude := g.sourcePacketAmplitude tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cut weight Kb gap
        (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
        (fun p => value p.1 p.2) phase a z level cell
      let mass := g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight level cell z
      ‖amplitude‖ ≤
        (C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*C^3)*mass := by
  intro ι tops T N κ Label Item _ _ P alt hAlt selector v test g w cut Kw D hw hKw
    hlength hzero Kb hKb gap phase M hM hMmax a Z A maskExponent
    ha0 ha1 hZ hA hz0 hz z hweight
  dsimp only
  intro hinterval level cell
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible cut (w/(P t).length j)
    (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight Kw D zz
  let ε : ℝ := 1
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
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    have hanti := (P t).stopping_antitone g cut w hw (hzero t ht)
    intro i j hij
    exact min_le_min (hanti hij) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := min_le_right _ _
  have hsupported (t : ι) (ht : t ∈ tops) (j : Fin N) (l : (P t).labels j)
      (u : Item j l) : rawStop t j ≤ M t := by
    apply hMmax t ht
    have hj := g.eligible_lastEligible cut (w/(P t).length j)
      (div_pos hw ((P t).length_pos j)) (hzero t ht j)
    exact (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hw.le ((P t).length_pos j) (hlength t ht j l u))
      (by positivity)).trans hj
  have hmask (t : ι)
      (_ht : t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut level cell) : ‖((T t).mask L maskExponent z : ℂ)‖ ≤ ε := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact topSincMask_abs_le_one L maskExponent ((T t).horizontal z) ((T t).transverse z)
  have hb := g.sourcePacketAmplitude_node_envelope tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut weight hprecision hwpos hKb gap phase M hM hMmax
    a Z ha0 ha1 hZ hz0 hz Q coeff 0 stop hstop hmax
    (fun _ => z.1) (fun t => z.2-(T t).slope*z.1) A C ε hA hC (show 0 ≤ ε by norm_num [ε]) z
    hweight hinterval 0 N (fun t => ((T t).mask L maskExponent z : ℂ)) level cell hmask
  have heq : amplitude = g.sourcePacketAmplitude tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut weight Kb gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ((T p.1).mask L maskExponent z : ℂ) •
        (Q p.1).rawBand ((Q p.1).restrictCoefficient (coeff p.1) 0 N) 0 p.2
          z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell := by
    dsimp only [amplitude]
    apply Eq.trans ?_
      (show g.sourcePacketAmplitude tops (fun t => (T t).slope)
          (fun t => w/(T t).length) cut weight Kb gap
          (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
          (fun p => (Q p.1).rawBand
            (fun j l u => (T p.1).mask L maskExponent z • coeff p.1 j l u) 0 p.2
            z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell = _ from ?_)
    · apply g.sourcePacketAmplitude_stop_congr_of_zero
      intro p hp
      have ht : p.1 ∈ tops := (Finset.mem_product.mp hp).1
      by_cases hs : rawStop p.1 p.2 ≤ M p.1
      · exact Or.inl (min_eq_left hs).symm
      · right
        apply (Q p.1).rawBand_eq_zero_of_no_item
        intro l u
        exact hs (hsupported p.1 ht p.2 l u)
    · congr 1
      funext p
      rw [SourceLabeledLattice.restrictCoefficient_full,
        SourceLabeledLattice.rawBand_coeff_real_smul]
      exact (IsScalarTower.algebraMap_smul ℂ _ _).symm
  rw [← heq] at hb
  simpa only [ε,mul_one] using hb

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedLinearEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arbitrary-phase linear envelope for the original assigned
packet amplitudes. Recentring, masks and original analyzing coefficients
are retained exactly. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem assigned_original_linear_envelope (C L : ℝ) (hC : 1 ≤ C) :
    ∀ (τ : Type) (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
      (f : ℝ×ℝ → EuclideanSpace ℂ κ)
      (grid : AngularGrid) (cut Kw D : ℝ), 0 < Kw →
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
      (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
        (R (assigned u)) cone w u.1 u.2.1) →
      (∀ j, grid.eligible cut (w/P.length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb →
    ∀ (gap : ℕ → ℝ) (phase : ℕ → ℂ) (M : τ → ℕ),
      (∀ t ∈ tops, grid.eligible cut (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ j, grid.eligible cut (w/(T t).length) j → j ≤ M t) →
    ∀ (a Z A maskExponent : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → 0 ≤ A →
      (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
      (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    ∀ (z : ℝ×ℝ),
      (∀ t ∈ tops, (T t).weight Kw D z ≤ C) →
      let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency
      let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency
      let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt
      let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt
      (∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
        ‖((Q t).withProfile (alts t) (halt t)).rawInterval
          (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
            j (orig t j l) u.val) 0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤
            A*((T t).weight Kw D z)^8) →
      ∀ level cell,
        ‖grid.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut (fun t zz => (T t).weight Kw D zz) Kb gap packets assigned
          (fun u => grid.lastEligible cut (w/P.length u.1) (div_pos hw (P.length_pos u.1)))
          (P.physicalMaskedValue alt hAlt oldSlope b v f
            (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent z)
          phase a z level cell‖ ≤
            (C^8*A*(1+(a+Z*Kb)*
              (Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D z))+1))*C^3)*grid.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
              cut (fun t zz => (T t).weight Kw D zz) level cell z := by
  have hbound := AngularGrid.source_supported_selector_linear_envelope C L hC
  intro τ tops T N κ Label Item _ _ P packets assigned oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f grid cut Kw D hKw
    hassigned hshort hcondition hzero Kb hKb gap phase M hM hMmax
    a Z A maskExponent ha0 ha1 hZ hA hz0 hz z hweight
  dsimp only
  intro hinterval level cell
  let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency
  let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency
  let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt
  let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt
  let selector := P.assignedReferenceSelector packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency b
  have hcoeff t : (Q t).physicalMultiplierCoefficient (T t).slope (selector t) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned t
      oldSlope (T t).slope (R t) cone w F hw hcone hF hwide hfrequency b v f j l u
  have hi t (ht : t ∈ tops) (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N) :
      ‖((Q t).withProfile (alts t) (halt t)).rawInterval
        ((Q t).physicalMultiplierCoefficient (T t).slope (selector t) v f)
        0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤ A*((T t).weight Kw D z)^8 := by
    rw [hcoeff t]
    exact hinterval t ht lower upper hlu hu
  have hb := hbound τ tops T N κ (fun j => τ×P.labels j)
    (P.AssignedTopItem packets assigned) Q alts halt selector v f grid w cut Kw D hw hKw
    (fun t _ j l u => P.assignedTopReference_supported_length packets assigned t
      oldSlope (R t) cone w F hw hcone hF hwide hfrequency T hshort j l u)
    (fun _ _ => hzero) Kb hKb gap phase M hM hMmax
    a Z A maskExponent ha0 ha1 hZ hA hz0 hz z hweight hi level cell
  have heq := P.assignedReference_packetAmplitude_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f grid tops (fun t => w/(T t).length)
    cut (fun t zz => (T t).weight Kw D zz) Kb gap hassigned hcondition
    (fun _ j => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j)))
    phase a L maskExponent z level cell
  exact (congrArg norm heq).le.trans hb


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPathRegularity
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selected coefficients are fixed integrals. Spatial
regularity of the masked packets therefore requires no regularity of
the selecting direction field beyond that used to define them. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem physicalMaskedValue_continuous (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (q : P.PacketIndex) :
    Continuous (fun z => P.physicalMaskedValue alt hAlt t b v f T L A z q) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    ((T q.1 q.2.1 q.2.2).mask_continuous L A))).mul
    ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).continuous

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathCountInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A terminal path is independent of how far the finite hierarchy is
extended. Thus the individual terminal counts used by the plane theorem
can be replaced by one finite count for every top in a root. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

namespace AngularGrid
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

/-- The maximum of the actual individual terminal counts is terminal
for every top in the finite root family. -/
theorem source_common_terminal {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hKb : 0 < Kb) (shift : Fin Kb) (count : τ → ℕ)
    (hterminal : ∀ t ∈ tops, ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift (count t))) :
    ∀ t ∈ tops, ¬g.eligible cutoff (precision t)
      (ShiftedBlocks.endpoint shift (tops.sup count)) := by
  intro t ht he
  have hle : ShiftedBlocks.endpoint shift (count t) ≤
      ShiftedBlocks.endpoint shift (tops.sup count) :=
    (ShiftedBlocks.endpoint_strictMono hKb shift).monotone (Finset.le_sup ht)
  exact hterminal t ht (g.eligible_of_le (hp t ht) hle he)

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonnegative shift simplex and its vertex geometry. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem sourceShiftSimplex_vertex [DecidableEq ι] {mu : ℝ} (hmu : 0 ≤ mu) (i : ι) :
    Pi.single i mu ∈ sourceShiftSimplex mu := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j; simpa using hmu
    · simp [hji]
  · simp [Pi.single_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePhaseNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate bounds on the actual shift simplex, and the polynomial
budget for the linear node envelope at arbitrary imaginary phases. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem sourceShiftSimplex_phase_norm {mu : ℝ} (a eta : ι → ℝ)
    (ha : a ∈ sourceShiftSimplex mu) (i : ι) :
    ‖phaseTubePoint a eta i‖ ≤ mu+Real.sqrt (∑ j, (eta j)^2) := by
  have hai : a i ≤ mu := by
    calc
      a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)
      _ = mu := ha.2
  have hsq : (eta i)^2 ≤ ∑ j, (eta j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (eta j)) (Finset.mem_univ i)
  have heta : |eta i| ≤ Real.sqrt (∑ j, (eta j)^2) :=
    (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)).mpr
      (by simpa only [sq_abs] using hsq)
  calc
    ‖phaseTubePoint a eta i‖ ≤ ‖(a i:ℂ)‖+‖(eta i:ℂ)*Complex.I‖ := norm_add_le _ _
    _ = a i+|eta i| := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha.1 i),norm_mul,
        Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    _ ≤ _ := add_le_add hai heta

theorem sourceShiftSimplex_phase_re {mu : ℝ} (a eta : ι → ℝ)
    (ha : a ∈ sourceShiftSimplex mu) (i : ι) :
    0 ≤ (phaseTubePoint a eta i).re := by
  simpa only [phaseTubePoint,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,
    mul_zero,zero_mul,sub_zero,add_zero] using ha.1 i

/-- The explicit node-envelope coefficient grows at most linearly in
 the imaginary norm; its remaining factors are fixed powers of L. -/
theorem eventually_source_linear_phase_budget (C q : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (a Z A r H : ℝ) (K : ℕ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → 0 ≤ r → Z ≤ 1+r →
      0 ≤ A → A ≤ L^q → (K:ℝ) ≤ L^2 → 0 ≤ H → H ≤ 3*L →
      C^8*A*(1+(a+Z*K)*(H+1))*C^3 ≤ L^(q+4)*(1+r) := by
  filter_upwards [eventually_ge_atTop (max 1 (9*C^11))] with L hLlarge
  intro a Z A r H K ha ha1 hZ hr hZr hA hAq hK hH hHL
  have hL : 1 ≤ L := (le_max_left _ _).trans hLlarge
  have hCL : 9*C^11 ≤ L := (le_max_right _ _).trans hLlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpoly : 1+(a+Z*K)*(H+1) ≤ 9*(1+r)*L^3 := by
    have hZK : Z*(K:ℝ) ≤ (1+r)*L^2 :=
      mul_le_mul hZr hK (Nat.cast_nonneg K) (by positivity)
    have hprod := mul_le_mul
      (show a+Z*K ≤ 1+(1+r)*L^2 by linarith)
      (show H+1 ≤ 4*L by linarith)
      (by linarith : 0 ≤ H+1) (by positivity : 0 ≤ 1+(1+r)*L^2)
    have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
    have hL3 : L ≤ L^3 := by nlinarith
    have hrL : 0 ≤ r*L^3 := by positivity
    nlinarith
  calc
    _ = C^11*A*(1+(a+Z*K)*(H+1)) := by ring
    _ ≤ C^11*(L^q)*(9*(1+r)*L^3) := mul_le_mul
      (mul_le_mul_of_nonneg_left hAq (by positivity)) hpoly
      (by positivity) (by positivity)
    _ = (9*C^11)*L^q*L^3*(1+r) := by ring
    _ ≤ L*L^q*L^3*(1+r) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCL (by positivity))
          (by positivity)) (by positivity)
    _ = L^(q+4)*(1+r) := by
      have he : L*L^q*L^3 = L^(q+4) := by
        rw [mul_assoc,← Real.rpow_natCast,← Real.rpow_add hL0]
        calc
          L*L^(q+3) = L^(1:ℝ)*L^(q+3) := by rw [Real.rpow_one]
          _ = L^(q+4) := by rw [← Real.rpow_add hL0]; congr 1; ring
      rw [he]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVertexPlaneParameters
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual simplex vertex satisfies every scalar phase condition
of the original physical plane estimate, uniformly in the shift count. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem source_vertex_plane_parameters (L D : ℝ) (K : ℕ)
    (hL : 256 ≤ L) (hD : 2 ≤ D) (hK : 0 < K)
    (i : Fin K) (eta : Fin K → ℝ)
    (heta : Real.sqrt (∑ j, (eta j)^2) ≤ L^2) :
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu D p
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let a := mu/(K:ℝ)
    let phase := phaseTubePoint (Pi.single i mu) eta
    0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ alpha ∧ alpha ≤ 3 ∧
      (alpha-1)/p ≤ 1/12 ∧ p*mu = alpha-1 ∧
      (∀ j, ‖phase j‖ ≤ 2*L^2) ∧
      (∀ j, j ≠ i → (phase j).re = 0) ∧ (phase i).re = mu := by
  classical
  dsimp only
  let mu := PhaseCombinatorics.phaseMu D (Real.sqrt L)
  let alpha := 2+PhaseCombinatorics.phaseParameter D
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hmu : 0 < mu ∧ mu ≤ 1/12 := source_phaseMu_small (by linarith) hL
  have htheta := PhaseCombinatorics.phaseParameter_range (by linarith : 1 ≤ D)
  change 0 < PhaseCombinatorics.phaseParameter D ∧
    PhaseCombinatorics.phaseParameter D ≤ 1/3 at htheta
  have hKreal : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K from hK)
  have halpha : 1 ≤ alpha ∧ alpha ≤ 3 := by
    dsimp only [alpha]
    constructor <;> linarith [htheta.1,htheta.2]
  have hquot : (alpha-1)/Real.sqrt L = mu := by
    dsimp only [alpha,mu,PhaseCombinatorics.phaseMu]
    congr 1
    ring
  have hrelation : Real.sqrt L*mu = alpha-1 := by
    rw [←hquot]
    exact mul_div_cancel₀ _ hp.ne'
  have ha0 : 0 ≤ mu/(K:ℝ) := div_nonneg hmu.1.le (zero_le_one.trans hKreal)
  have ha1 : mu/(K:ℝ) ≤ 1 :=
    (div_le_self hmu.1.le hKreal).trans (by linarith)
  refine ⟨ha0,ha1,halpha.1,halpha.2,?_,hrelation,?_,?_,?_⟩
  · rw [hquot]
    exact hmu.2
  · intro j
    have hn := sourceShiftSimplex_phase_norm (Pi.single i mu) eta
      (sourceShiftSimplex_vertex hmu.1.le i) j
    have hL2 : 1 ≤ L^2 := one_le_pow₀ (by linarith : 1 ≤ L)
    exact hn.trans (by linarith [hmu.2,heta])
  · intro j hji
    simp [phaseTubePoint,hji]
  · simp [phaseTubePoint]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTubeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original assigned packet envelope on the entire phase tube.
Its growth in the imaginary norm is linear, with the exact polynomial
factor needed by the Gaussian vertex extension. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_original_tube_envelope (C q : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ : Type) (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
      (f : ℝ×ℝ → EuclideanSpace ℂ κ)
      (grid : AngularGrid) (cut Kw D : ℝ), 0 < Kw →
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
      (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
        (R (assigned u)) cone w u.1 u.2.1) →
      (∀ j, grid.eligible cut (w/P.length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → (Kb:ℝ) ≤ L^2 →
    ∀ (gap : ℕ → ℝ) (phase : ℕ → ℂ) (M : τ → ℕ),
      (∀ t ∈ tops, grid.eligible cut (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ j, grid.eligible cut (w/(T t).length) j → j ≤ M t) →
    ∀ (a Z A maskExponent r : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → 0 ≤ r → Z ≤ 1+r → 0 ≤ A → A ≤ L^q →
      (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
      (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    ∀ (z : ℝ×ℝ),
      (∀ t ∈ tops, (T t).weight Kw D z ≤ C) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D z)) ≤ 3*L →
      let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency
      let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency
      let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt
      let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt
      (∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
        ‖((Q t).withProfile (alts t) (halt t)).rawInterval
          (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
            j (orig t j l) u.val) 0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤
            A*((T t).weight Kw D z)^8) →
      ∀ level cell,
        ‖grid.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut (fun t zz => (T t).weight Kw D zz) Kb gap packets assigned
          (fun u => grid.lastEligible cut (w/P.length u.1) (div_pos hw (P.length_pos u.1)))
          (P.physicalMaskedValue alt hAlt oldSlope b v f
            (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent z)
          phase a z level cell‖ ≤
            (L^(q+4)*(1+r))*grid.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
              cut (fun t zz => (T t).weight Kw D zz) level cell z := by
  filter_upwards [eventually_source_linear_phase_budget C q hC] with L hbudget
  intro τ tops T N κ Label Item _ _ P packets assigned oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f grid cut Kw D hKw
    hassigned hshort hcondition hzero Kb hKb hKbL gap phase M hM hMmax
    a Z A maskExponent r ha0 ha1 hZ hr hZr hA hAq hz0 hz z hweight htotal
  dsimp only
  intro hinterval level cell
  have hbound := assigned_original_linear_envelope C L hC τ tops T N κ Label Item P
    packets assigned oldSlope R cone w F hw hcone hF hwide hfrequency alt hAlt b v f
    grid cut Kw D hKw hassigned hshort hcondition hzero Kb hKb gap phase M hM hMmax
    a Z A maskExponent ha0 ha1 hZ hA hz0 hz z hweight hinterval level cell
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right
  · apply hbudget a Z A r _ Kb ha0 ha1 hZ hr hZr hA hAq hKbL
    · exact Real.log_nonneg (le_max_left _ _)
    · exact htotal
  · exact grid.mass_nonnegative tops (fun t => (T t).slope) (fun t => w/(T t).length)
      cut (fun t zz => (T t).weight Kw D zz)
      (fun t zz => ((T t).weight_pos hKw D zz).le) level cell z

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStopCostBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual terminal cost remains negligible against the bad-top
threshold, for every fixed mass-cutoff exponent. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

 theorem eventually_source_stop_cost_small (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ α : ℝ, 1 ≤ α → α ≤ 3 →
      (1+(L^C)^(Real.sqrt L)*(L^A+1)^(α-1))*Real.exp (-L) ≤ 1/2 := by
  let d := C+2*A+1
  have hd : 0 < d := by dsimp [d]; linarith
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).bound
    (show 0 < 1/(4*d) by positivity)
  have hdecay1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 1 (by norm_num : (0:ℝ) < 1)
  have hdecay2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (3/4)
    (by norm_num : (0:ℝ) < 3/4)
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog,
    hdecay1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
    hdecay2.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/16))]
    with L hL hl hsmall1 hsmall2
  intro α hα hα3
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hs : 1 ≤ Real.sqrt L := (Real.one_le_sqrt).mpr hL
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _),← Real.sqrt_eq_rpow] at hl
  have hexponent : C*Real.sqrt L*Real.log L+2*A*Real.log L ≤ L/4 := by
    have h1 : C*Real.sqrt L+2*A ≤ d*Real.sqrt L := by
      have hA' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*A)
      dsimp [d]
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ d*Real.sqrt L)
    have hsquare := Real.sq_sqrt hL0.le
    have heq : d*Real.sqrt L*(1/(4*d)*Real.sqrt L) = L/4 := by
      field_simp [hd.ne']
      nlinarith
    calc
      _ = (C*Real.sqrt L+2*A)*Real.log L := by ring
      _ ≤ (d*Real.sqrt L)*Real.log L := mul_le_mul_of_nonneg_right h1 hlog0
      _ ≤ L/4 := h2.trans_eq heq
  have hbase : 1 ≤ L^A+1 := by
    have := Real.rpow_nonneg hL0.le A
    linarith
  have hpow : (L^A+1)^(α-1) ≤ 4*L^(2*A) := by
    calc
      _ ≤ (L^A+1)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ ≤ (2*L^A)^(2:ℝ) := Real.rpow_le_rpow (by positivity)
        (by have := Real.one_le_rpow hL hA; linarith) (by norm_num)
      _ = 4*L^(2*A) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hL0.le _),
          Real.rpow_two,← Real.rpow_mul hL0.le]
        norm_num [show A*2 = 2*A by ring]
  have hcost : (L^C)^(Real.sqrt L)*(L^A+1)^(α-1) ≤ 4*Real.exp (L/4) := by
    calc
      _ ≤ (L^C)^(Real.sqrt L)*(4*L^(2*A)) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (Real.rpow_nonneg hL0.le _) _)
      _ = 4*((L^C)^(Real.sqrt L)*L^(2*A)) := by ring
      _ = 4*Real.exp (C*Real.sqrt L*Real.log L+2*A*Real.log L) := by
        congr 1
        rw [← Real.rpow_mul hL0.le,← Real.rpow_add hL0,Real.rpow_def_of_pos hL0]
        congr 1
        ring
      _ ≤ 4*Real.exp (L/4) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
  simp only [Real.rpow_zero,one_mul,neg_mul] at hsmall1 hsmall2
  calc
    _ ≤ (1+4*Real.exp (L/4))*Real.exp (-L) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hcost) (Real.exp_pos _).le
    _ = Real.exp (-L)+4*Real.exp (-(3/4:ℝ)*L) := by
      rw [add_mul,one_mul,mul_assoc,← Real.exp_add,
        show L/4 + -L = -(3/4:ℝ)*L by ring]
    _ ≤ 1/2 := by
      simp only [neg_mul]
      linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGoodPathSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source good set controls the pointwise total bad-top mass.
Its measure estimate follows from the full weighted bad-path integral. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable
variable {ι X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem sourceBadPathMass_eq_filter (tops : Finset ι) (weight : ι → X → ℝ)
    (bad : ι → Set X) (x : X) :
    sourceBadPathMass tops weight bad x = ∑ t ∈ tops.filter (fun t => x ∈ bad t), weight t x := by
  simp only [sourceBadPathMass,Finset.sum_filter,indicator_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedParentCentralInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual concentration and reference good set supplies every local
input used by central interpolation: the original node bounds, weighted
bad-path budget and common-count original vertex integrals. No moment,
path-product or plane estimate is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_central_inputs
    (pProfile qEnv Cmass Cweight F c0 A_M : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ]
      (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (maskExponent shortVariation : ℝ), 0 ≤ maskExponent →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    ∀ (hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
    cone ≤ Kcount →
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu Dphase p
    let alpha := 2+PhaseCombinatorics.phaseParameter Dphase
    let a := mu/(SourceParameters.blockCount L:ℝ)
    let phase := fun (shift : Fin (SourceParameters.blockCount L)) eta j =>
      phaseTubePoint (Pi.single shift mu) eta (ShiftedBlocks.tag hKb j)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let countTop := fun shift => g.sourceTopTerminalCount T cut w hw hKb shift
    let count := fun shift => tops.sup (countTop shift)
    let cost := 1+(L^(qEnv+6))^p*(L^A_M+1)^(alpha-1)
    ∀ (Z0 : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ)), MeasurableSet Z0 →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
    let good := sourceGoodPathSet Z0 tops weight bad L
    (∀ z ∈ Z0, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ Z0, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ Z0, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ Z0, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ shift, ∀ j < count shift, ∀ z ∈ Z0, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ Dphase/100) →
    let squarePackets := fun t => sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (R t) (T t).slope
      (cone+(SourceParameters.branching L)^3) w
    let Qsquare := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w F hw
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hF hwideParent hfrequency
    let origSquare := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w
    let squareSelected := fun t => (Finset.univ : Finset (Qsquare t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets t)
    let S := fun shift t => g.fixedPathResidualPackets tops (fun u => (T u).slope)
      (fun u => w/(T u).length) cut packets assigned (fun u => stop u.1)
      (ShiftedBlocks.endpoint shift) (countTop shift t-1) (T t).slope
    let Qref := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
    let origRef := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w
    let selected := fun shift t => (Finset.univ : Finset (Qref t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origRef t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S shift t)
    (∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qsquare t).restrictPackets (squareSelected t)).physicalReferenceBad
      ((Qsquare t).restrictedAlternate (fun j l => alt j (origSquare t j l)) (squareSelected t))
      ((Qsquare t).restrictedAlternate_bound (fun j l => alt j (origSquare t j l))
        (fun j l => hAlt j (origSquare t j l)) (squareSelected t))
      (T t).slope (w/P.topLength) (fun j l => b j (origSquare t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
    (∀ shift, ∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qref t).restrictPackets (selected shift t)).physicalReferenceBad
      ((Qref t).restrictedAlternate (fun j l => alt j (origRef t j l)) (selected shift t))
      ((Qref t).restrictedAlternate_bound (fun j l => alt j (origRef t j l))
        (fun j l => hAlt j (origRef t j l)) (selected shift t))
      (T t).slope (w/P.topLength) (fun j l => b j (origRef t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origRef t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
    MeasurableSet good ∧ good ⊆ Z0 ∧
    (∀ (shift : Fin (SourceParameters.blockCount L))
      (eta' : Fin (SourceParameters.blockCount L) → ℝ) z, z ∈ good → ∀ level cell,
      ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
        (fun u => stop u.1) (original z)
        (phase shift eta')
        a z level cell‖ ≤
          L^(2*(qEnv+6))*(1+Real.sqrt (∑ j, (eta' j)^2))*
            g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
              cut weight level cell z) ∧
    ∀ (shift : Fin (SourceParameters.blockCount L)) (eta : Fin (SourceParameters.blockCount L) → ℝ),
      Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
    (∀ z ∈ good, ∀ level cell,
      ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
        (fun u => stop u.1) (original z) (phase shift eta) a z level cell‖ ≤
          L^(qEnv+6)*g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
            cut weight level cell z) ∧
    (∀ z ∈ good, cost*(∑ t ∈ tops.filter (fun t => z ∈ bad t), weight t z) ≤ 1/2) ∧
    ∀ top ∈ tops,
      Integrable ((good \ bad top).indicator (fun z => weight top z*
        g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
          (fun u => stop u.1) original (phase shift eta) a alpha p (L^A_M) shift top (count shift) z))
        (volume.prod volume) ∧
      (∫ z, (good \ bad top).indicator (fun x => weight top x*
        g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
          (fun u => stop u.1) original (phase shift eta) a alpha p (L^A_M) shift top (count shift) x) z
        ∂volume.prod volume) ≤
        Real.exp (4+2*(Dweight:ℝ))*cost*(∫ z, weight top z ∂volume.prod volume) := by
  filter_upwards [eventually_assigned_parent_vertex_integral pProfile qEnv Cmass Cweight F c0 A_M
    Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice hDweight,
    eventually_assigned_original_node_envelope Cweight qEnv hCweight,
    eventually_assigned_original_tube_envelope Cweight qEnv hCweight,
    eventually_source_stop_cost_small (qEnv+6) A_M (by linarith) hAM.le,
    eventually_ge_atTop (256:ℝ)] with L hvertex hnode htube hbudget hL
  intro τ κ _ tops T N Label Item _ P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask Kw R Q orig alts halt hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hNmass hlogN hA hAq p mu alpha a phase cut weight stop
    original countTop count cost Z0 bad hZ0 hbad good hweight htotal hmass hconc hcount
    squarePackets Qsquare origSquare squareSelected S Qref origRef selected hsquareEvent hrefEvent
  have hL1 : 1 ≤ L := by linarith
  have hKw : 0 < Kw := Real.rpow_pos_of_pos (by linarith) _
  have hmu0 : 0 ≤ mu := (source_phaseMu_small (by linarith) hL).1.le
  have hmu1 : mu ≤ 1 := (source_phaseMu_small (by linarith) hL).2.trans (by norm_num)
  have hKreal : (1:ℝ) ≤ SourceParameters.blockCount L := by
    exact_mod_cast (show 1 ≤ SourceParameters.blockCount L from hKb)
  have ha : 0 ≤ a := div_nonneg hmu0 (zero_le_one.trans hKreal)
  have ha1 : a ≤ 1 := (div_le_self hmu0 hKreal).trans hmu1
  have htheta := PhaseCombinatorics.phaseParameter_range (by linarith : 1 ≤ Dphase)
  change 0 < PhaseCombinatorics.phaseParameter Dphase ∧
    PhaseCombinatorics.phaseParameter Dphase ≤ 1/3 at htheta
  have halpha : 1 ≤ alpha := by dsimp only [alpha]; linarith [htheta.1]
  have halpha3 : alpha ≤ 3 := by dsimp only [alpha]; linarith [htheta.2]
  have hwpos (t : τ) (z : ℝ×ℝ) : 0 < weight t z := (T t).weight_pos hKw _ z
  have hw0 (t : τ) (z : ℝ×ℝ) : 0 ≤ weight t z := (hwpos t z).le
  have hwmeas (t : τ) : Measurable (weight t) := ((T t).continuous_weight hKw _).measurable
  have hbadMass : Measurable (sourceBadPathMass tops weight bad) :=
    Finset.measurable_sum tops (fun t ht => (hwmeas t).indicator (hbad t ht))
  have hgood : MeasurableSet good :=
    hZ0.inter (measurableSet_le hbadMass measurable_const)
  have hsub : good ⊆ Z0 := Set.inter_subset_left
  have hraw (z : ℝ×ℝ) (hz : z ∈ good) (t : τ) (ht : t ∈ tops)
      (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N) :
      ‖((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤ A*(weight t z)^8 := by
    have hc := hconc z (hsub hz) t ht lower upper hlu hu
      (z.2-(T t).slope*z.1) (by simpa using (T t).width_pos.le)
    exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hc
  let M := fun t => g.lastEligible cut (w/(T t).length) (div_pos hw (T t).length_pos)
  have hM (t : τ) (ht : t ∈ tops) : g.eligible cut (w/(T t).length) (M t) :=
    g.eligible_lastEligible cut (w/(T t).length) (div_pos hw (T t).length_pos) (hroot t ht)
  have hMmax (t : τ) (ht : t ∈ tops) (j : ℕ)
      (hj : g.eligible cut (w/(T t).length) j) : j ≤ M t :=
    (g.eligible_iff_le_lastEligible cut (w/(T t).length)
      (div_pos hw (T t).length_pos) (hroot t ht) j).mp hj
  have hre (shift : Fin (SourceParameters.blockCount L)) (eta' : Fin (SourceParameters.blockCount L) → ℝ) (j : ℕ) :
      0 ≤ (phaseTubePoint (Pi.single shift mu) eta' (ShiftedBlocks.tag hKb j)).re :=
    sourceShiftSimplex_phase_re (Pi.single shift mu) eta'
      (sourceShiftSimplex_vertex hmu0 shift) _
  refine ⟨hgood,hsub,?_,?_⟩
  · intro shift eta' z hz level cell
    let r := Real.sqrt (∑ j, (eta' j)^2)
    let Z := mu+r
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hZ0 : 0 ≤ Z := add_nonneg hmu0 hr
    have hZr : Z ≤ 1+r := by dsimp only [Z]; linarith
    have hnorm (j : ℕ) :
        ‖phaseTubePoint (Pi.single shift mu) eta' (ShiftedBlocks.tag hKb j)‖ ≤ Z :=
      sourceShiftSimplex_phase_norm (Pi.single shift mu) eta'
        (sourceShiftSimplex_vertex hmu0 shift) _
    have ht := htube τ tops T N κ Label Item P packets assigned oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f g cut Kw (Dweight:ℝ) hKw
      hassigned hshort hcondition hzero (SourceParameters.blockCount L) hKb hKbL
      (g.sourceBoundaryGap L)
      (fun j => phaseTubePoint (Pi.single shift mu) eta' (ShiftedBlocks.tag hKb j))
      M hM hMmax a Z A maskExponent r ha ha1 hZ0 hr hZr hA hAq
      (fun _ _ j _ => hre shift eta' j) (fun _ _ j _ => hnorm j) z
      (hweight z (hsub hz)) (htotal z (hsub hz)) (hraw z hz) level cell
    apply ht.trans
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : qEnv+4 ≤ 2*(qEnv+6)))
        (by positivity)
    · exact g.mass_nonnegative tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight hw0 level cell z
  · intro shift eta heta
    have hparams := source_vertex_plane_parameters L Dphase (SourceParameters.blockCount L)
      hL hD hKb shift eta heta
    change 0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ alpha ∧ alpha ≤ 3 ∧ (alpha-1)/p ≤ 1/12 ∧
      p*mu = alpha-1 ∧ (∀ j, ‖phaseTubePoint (Pi.single shift mu) eta j‖ ≤ 2*L^2) ∧
      (∀ j, j ≠ shift → (phaseTubePoint (Pi.single shift mu) eta j).re = 0) ∧
      (phaseTubePoint (Pi.single shift mu) eta shift).re = mu at hparams
    obtain ⟨_,_,_,_,_,_,hphase,_,_⟩ := hparams
    refine ⟨?_,?_,?_⟩
    · intro z hz level cell
      exact hnode τ tops T N κ Label Item P packets assigned oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt b v f g cut Kw (Dweight:ℝ) hKw
        hassigned hshort hcondition hzero (SourceParameters.blockCount L) hKb hKbL
        (g.sourceBoundaryGap L) (phase shift eta) M hM hMmax a (2*L^2) A maskExponent
        ha ha1 (by positivity) le_rfl hA hAq
        (fun _ _ j _ => hre shift eta j) (fun _ _ j _ => hphase _)
        z (hweight z (hsub hz)) (htotal z (hsub hz)) (hraw z hz) level cell
    · intro z hz
      have hmassBad : (∑ t ∈ tops.filter (fun t => z ∈ bad t), weight t z) ≤ Real.exp (-L) := by
        rw [←sourceBadPathMass_eq_filter]
        exact hz.2
      exact (mul_le_mul_of_nonneg_left hmassBad (by dsimp only [cost]; positivity)).trans
        (hbudget alpha halpha halpha3)
    · exact hvertex τ κ tops T N Label Item P packets assigned oldSlope cone w hw hcone hwide
        hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
        hmask hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
        g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A hD hNmass hlogN hA hAq shift eta heta
        good bad hgood hbad (fun z hz => hweight z (hsub hz)) (fun z hz => htotal z (hsub hz))
        (fun z hz => hmass z (hsub hz)) (fun z hz => hconc z (hsub hz))
        (fun j hj z hz => hcount shift j hj z (hsub hz))
        (fun t ht z hz => hsquareEvent t ht z ⟨hsub hz.1,hz.2⟩)
        (fun t ht z hz => hrefEvent shift t ht z ⟨hsub hz.1,hz.2⟩)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedParentCentralGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original-packet central gain has one numerical threshold chosen
before the finite types and packet family. Its estimate follows from the
type-uniform moment bounds. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_central_gain_oai
    (pProfile qEnv Cmass Cweight F c0 A_M d m decay : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hqm : 2*(qEnv+6)+2 ≤ m) (hCmassM : Cmass ≤ m) (hdecay : 0 ≤ decay) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item),
    ∀ (tops : Finset τ) (T : τ → SlopeBox)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (maskExponent shortVariation : ℝ), 0 ≤ maskExponent →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    ∀ (hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
    cone ≤ Kcount →
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → Dphase ≤ L^d → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu Dphase p
    let a := mu/(SourceParameters.blockCount L:ℝ)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let countTop := fun shift => g.sourceTopTerminalCount T cut w hw hKb shift
    let count := fun shift => tops.sup (countTop shift)
    ∀ (Z0 : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ)), MeasurableSet Z0 →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
    let good := sourceGoodPathSet Z0 tops weight bad L
    (∀ z ∈ Z0, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ Z0, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ Z0, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ Z0, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ shift, ∀ j < count shift, ∀ z ∈ Z0, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ Dphase/100) →
    let squarePackets := fun t => sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (R t) (T t).slope
      (cone+(SourceParameters.branching L)^3) w
    let Qsquare := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w F hw
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hF hwideParent hfrequency
    let origSquare := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w
    let squareSelected := fun t => (Finset.univ : Finset (Qsquare t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets t)
    let S := fun shift t => g.fixedPathResidualPackets tops (fun u => (T u).slope)
      (fun u => w/(T u).length) cut packets assigned (fun u => stop u.1)
      (ShiftedBlocks.endpoint shift) (countTop shift t-1) (T t).slope
    let Qref := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
    let origRef := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w
    let selected := fun shift t => (Finset.univ : Finset (Qref t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origRef t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S shift t)
    (∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qsquare t).restrictPackets (squareSelected t)).physicalReferenceBad
      ((Qsquare t).restrictedAlternate (fun j l => alt j (origSquare t j l)) (squareSelected t))
      ((Qsquare t).restrictedAlternate_bound (fun j l => alt j (origSquare t j l))
        (fun j l => hAlt j (origSquare t j l)) (squareSelected t))
      (T t).slope (w/P.topLength) (fun j l => b j (origSquare t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
    (∀ shift, ∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qref t).restrictPackets (selected shift t)).physicalReferenceBad
      ((Qref t).restrictedAlternate (fun j l => alt j (origRef t j l)) (selected shift t))
      ((Qref t).restrictedAlternate_bound (fun j l => alt j (origRef t j l))
        (fun j l => hAlt j (origRef t j l)) (selected shift t))
      (T t).slope (w/P.topLength) (fun j l => b j (origRef t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origRef t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
    ∀ (start Fmass : ℝ), 0 < Fmass → L/2 ≤ Real.log Nmass →
      (volume.prod volume) Z0 ≠ ∞ → (volume.prod volume).real Z0 ≤ Fmass →
      (∀ t ∈ tops, start ≤ (T t).slope ∧ (T t).slope ≤ start+g.rootWidth) →
      (∑ t ∈ tops, ∫ z, weight t z ∂volume.prod volume) ≤ L^m*Nmass^2*Fmass →
    let W := fun z => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
        (stop s.1) (assigned s) a z : ℝ):ℂ) • original z s
    IntegrableOn (fun z => ‖W z‖) good (volume.prod volume) ∧
      (∫ z in good, ‖W z‖ ∂volume.prod volume) ≤ L^(-decay)*Nmass*Fmass := by
  filter_upwards [eventually_assigned_parent_central_inputs pProfile qEnv Cmass Cweight F c0 A_M
    Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice hDweight,
    AngularGrid.eventually_source_central_from_paths_types
      (qEnv+6) A_M 0
      (Real.exp (4+2*(Dweight:ℝ))) d m decay
      (by linarith) hAM.le (by norm_num) (Real.exp_pos _).le hd hm hqm hdecay,
    eventually_ge_atTop (256:ℝ)] with L hinputs hcentral hL
  intro τ κ _ N Label Item _ P tops T packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask Kw R Q orig alts halt hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hDL hNmass hlogN hA hAq p mu a cut weight stop
    original countTop count Z0 bad hZ0 hbad good hweight htotal hmass hconc hcount
    squarePackets Qsquare origSquare squareSelected S Qref origRef selected hsquareEvent hrefEvent start Fmass hFmass hloglo
    hZ0finite hmeasure hslope hweightTotal W
  have hL1 : 1 ≤ L := by linarith
  have hKw : 0 < Kw := Real.rpow_pos_of_pos (by linarith) _
  have hresult := hinputs τ κ tops T N Label Item P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A hD hNmass hlogN hA hAq
    Z0 bad hZ0 hbad hweight htotal hmass hconc hcount hsquareEvent hrefEvent
  obtain ⟨hgood,hsub,hcrude,hpaths⟩ := hresult
  have hfinite : (volume.prod volume) good ≠ ∞ :=
    ne_top_of_le_ne_top hZ0finite (measure_mono hsub)
  have : IsFiniteMeasure ((volume.prod volume).restrict good) :=
    isFiniteMeasure_restrict.mpr hfinite
  have hmeasureGood : ((volume.prod volume).restrict good).real univ ≤ Fmass := by
    rw [measureReal_restrict_apply_univ]
    exact (measureReal_mono hsub hZ0finite).trans hmeasure
  have hp (t : τ) (_ht : t ∈ tops) : 0 ≤ w/(T t).length :=
    (div_pos hw (T t).length_pos).le
  have hwpos (t : τ) (z : ℝ×ℝ) : 0 < weight t z := (T t).weight_pos hKw _ z
  have hwint (t : τ) (_ht : t ∈ tops) : Integrable (weight t) (volume.prod volume) :=
    (T t).weight_integrable hKw hDweight
  have hwmeas (t : τ) : Measurable (weight t) := ((T t).continuous_weight hKw _).measurable
  have hvalue (s : P.PacketIndex) : Measurable (fun z => original z s) :=
    (P.physicalMaskedValue_continuous alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent s).measurable
  have heligible (s : P.PacketIndex) (hs : s ∈ packets) :
      g.eligible cut (w/(T (assigned s)).length) (stop s.1) := by
    have hle : w/(T (assigned s)).length ≤ w/P.length s.1 :=
      div_le_div_of_nonneg_left hw.le (P.length_pos s.1) (hshort s hs)
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans
      (g.eligible_lastEligible cut (w/P.length s.1) (div_pos hw (P.length_pos s.1)) (hzero s.1))
  have hterminal (i : Fin (SourceParameters.blockCount L)) :
      ∀ t ∈ tops, ¬g.eligible cut (w/(T t).length) (ShiftedBlocks.endpoint i (count i)) := by
    apply g.source_common_terminal tops (fun t => w/(T t).length) cut hp hKb i (countTop i)
    intro t _
    exact g.firstIneligibleShiftedBlock_spec cut (w/(T t).length)
      (div_pos hw (T t).length_pos) hKb i
  have hmass' (z : ℝ×ℝ) (hz : z ∈ good) :
      (∑ t ∈ tops, weight t z) ≤ L^m*Nmass := by
    apply (hmass z (hsub hz)).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hL1 hCmassM) hNmass.le
  have hc := hcentral τ P.PacketIndex (ℝ×ℝ) κ Dphase (by linarith) hDL (volume.prod volume) g tops
    (fun t => (T t).slope) (fun t => w/(T t).length) cut weight hp hwpos hwint hwmeas
    (g.sourceBoundaryGap L) packets assigned (fun s => stop s.1) original hvalue hassigned heligible
    start Nmass Fmass hNmass hFmass hloglo hlogN hslope good hgood hmeasureGood hmass'
    hweightTotal hKb (fun i eta z hz c => hcrude i eta z hz 0 c) count (fun _ _ => bad)
    hterminal (by
      intro i eta heta
      obtain ⟨hnode,hbadMass,hint⟩ := hpaths i eta heta
      refine ⟨?_,hbadMass,?_,?_⟩
      · intro z hz j _ c
        exact hnode z hz (ShiftedBlocks.endpoint i j) c
      · intro t ht
        exact (hint t ht).1
      · intro t ht
        simpa only [Real.rpow_zero,mul_one] using (hint t ht).2)
  exact hc

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain_oai := @OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain_oai
