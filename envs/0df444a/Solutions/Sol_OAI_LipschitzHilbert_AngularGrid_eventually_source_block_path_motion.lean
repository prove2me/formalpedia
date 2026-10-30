-- Prove2me | solution 1 for OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T19:53:10.172191+00:00
-- url     : https://prove2.me/submissions/9a7b044c-9903-400c-a172-2eb8b9abc375

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

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

/-- Two positive groups of mass moving relatively by at most `ε` have a
fraction error proportional to `r*(1-r)`, including a vanishing complement. -/
theorem complementary_mass_fraction_motion {A B A' B' ε : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hAmove : |A' - A| ≤ ε * A) (hBmove : |B' - B| ≤ ε * B) :
    0 < A' ∧ 0 < A' + B' ∧
      |A' / (A' + B') - A / (A + B)| ≤
        4 * ε * (A / (A + B)) * (1 - A / (A + B)) := by
  have hAlo : (1 - ε) * A ≤ A' := by linarith [(abs_le.mp hAmove).1]
  have hBlo : (1 - ε) * B ≤ B' := by linarith [(abs_le.mp hBmove).1]
  have hAp : 0 < A' := lt_of_lt_of_le (mul_pos (by linarith) hA) hAlo
  have hBp : 0 ≤ B' := (mul_nonneg (by linarith) hB).trans hBlo
  have hS : 0 < A + B := add_pos_of_pos_of_nonneg hA hB
  have hS' : 0 < A' + B' := add_pos_of_pos_of_nonneg hAp hBp
  have hslow : (A + B) / 2 ≤ A' + B' := by
    have hεA := mul_le_mul_of_nonneg_right hε1 hA.le
    have hεB := mul_le_mul_of_nonneg_right hε1 hB
    nlinarith
  have hnum : |(A' - A) * B - A * (B' - B)| ≤ 2 * ε * A * B := by
    calc
      _ ≤ |(A' - A) * B| + |A * (B' - B)| := abs_sub _ _
      _ = |A' - A| * B + A * |B' - B| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hB, abs_of_pos hA]
      _ ≤ (ε * A) * B + A * (ε * B) :=
        add_le_add (mul_le_mul_of_nonneg_right hAmove hB)
          (mul_le_mul_of_nonneg_left hBmove hA.le)
      _ = _ := by ring
  have hdiff : A' / (A' + B') - A / (A + B) =
      ((A' - A) * B - A * (B' - B)) / ((A' + B') * (A + B)) := by
    field_simp
    ring
  refine ⟨hAp, hS', ?_⟩
  rw [hdiff, abs_div, abs_of_pos (mul_pos hS' hS)]
  calc
    _ ≤ (2 * ε * A * B) / ((A' + B') * (A + B)) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg hS'.le hS.le)
    _ ≤ (2 * ε * A * B) / (((A + B) / 2) * (A + B)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hslow hS.le
    _ = _ := by
      field_simp
      ring

/-- The logarithmic fraction motion is proportional to the missing mass,
even if the complement vanishes. The constant is independent of the masses. -/
theorem complementary_mass_log_motion {A B A' B' ε : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hAmove : |A' - A| ≤ ε * A) (hBmove : |B' - B| ≤ ε * B) :
    |Real.log (A' / (A' + B')) - Real.log (A / (A + B))| ≤
      12 * ε * (1 - A / (A + B)) := by
  obtain ⟨hAp, hS', hmotion⟩ := complementary_mass_fraction_motion hA hB hε0 hε1 hAmove hBmove
  have hS : 0 < A + B := add_pos_of_pos_of_nonneg hA hB
  have hr : 0 < A / (A + B) := div_pos hA hS
  have hAlo : A / 2 ≤ A' := by
    have hmul := mul_le_mul_of_nonneg_right hε1 hA.le
    linarith [(abs_le.mp hAmove).1]
  have hShi : A' + B' ≤ (3 / 2) * (A + B) := by
    have hmulA := mul_le_mul_of_nonneg_right hε1 hA.le
    have hmulB := mul_le_mul_of_nonneg_right hε1 hB
    linarith [(abs_le.mp hAmove).2, (abs_le.mp hBmove).2]
  have hrlo : (A / (A + B)) / 3 ≤ A' / (A' + B') := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hS (by norm_num)) hS').2
    have h1 := mul_le_mul_of_nonneg_left hShi hA.le
    have h2 := mul_le_mul_of_nonneg_right hAlo hS.le
    nlinarith
  calc
    _ ≤ |A' / (A' + B') - A / (A + B)| / ((A / (A + B)) / 3) :=
      log_motion_of_lower_bound (div_pos hr (by norm_num)) hrlo (by linarith)
    _ ≤ (4 * ε * (A / (A + B)) * (1 - A / (A + B))) /
        ((A / (A + B)) / 3) := div_le_div_of_nonneg_right hmotion (by positivity)
    _ = _ := by field_simp; ring

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

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical parameters for the source prediction comparison.
All thresholds are uniform in the top family, phase dimension and mass. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

theorem eventually_source_mass_error_small (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ Kw : ℝ, 1 ≤ Kw →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      Real.exp δ*δ ≤ 1/8 := by
  have hm := eventually_source_mass_rescaling_error D hD
  have hs := (Real.tendsto_sqrt_atTop.comp source_step_tendsto_atTop).eventually_ge_atTop
    (80*D*Real.exp 1)
  filter_upwards [hm,hs] with L hm hs
  intro Kw hKw
  dsimp only
  have hb := hm 1 0 Kw (by norm_num) (by norm_num) (by norm_num) hKw
  norm_num at hb
  apply hb.trans
  have hroot : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  apply (div_le_iff₀ hroot).mpr
  change 80*D*Real.exp 1 ≤ Real.sqrt (SourceParameters.step L) at hs
  nlinarith

/-- Both relative errors used by the actual path comparison are smaller
than the chosen prediction error, uniformly in the block length. -/
theorem eventually_source_path_errors_small (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw Z : ℝ) (steps : ℕ),
      1 ≤ Kw → 0 ≤ Z → Z ≤ 2*L^2 → (steps:ℝ) ≤ L^2 →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let E := (steps:ℝ)*Z*(2*δ)
      let ε := SourceParameters.step L^(-(1/8:ℝ))
      (Real.exp δ*δ ≤ 1/8 ∧ Real.exp δ*δ ≤ ε) ∧
        Real.exp E*E ≤ ε := by
  have hm := eventually_source_mass_rescaling_error D hD
  have ht := eventually_source_transition_error D hD
  have hpm := eventually_source_polynomial_motion (10*D*Real.exp 1) 0
  have hpt := eventually_source_polynomial_motion (20*D*Real.exp 1) 4
  filter_upwards [hm,ht,hpm,hpt,eventually_source_mass_error_small D hD]
    with L hm ht hpm hpt hsmall
  intro Kw Z steps hKw hZ0 hZ hsteps
  dsimp only
  have hb := hm 1 0 Kw (by norm_num) (by norm_num) (by norm_num) hKw
  norm_num at hb hpm
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hpow : SourceParameters.step L^(-(1/4:ℝ)) ≤
      SourceParameters.step L^(-(1/8:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hG (by norm_num)
  refine ⟨⟨hsmall Kw hKw,hb.trans (hpm.trans hpow)⟩,?_⟩
  have hphase := ht steps Z Kw hsteps hZ0 hZ hKw
  rw [Real.rpow_ofNat] at hpt
  exact hphase.trans (hpt.trans hpow)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_PathCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The dominant-path coefficient from complementary masses

For the path child in §9 the coefficient is
`l^(1-α/p) * r^μ`, where `l=nₐ/n` and `r=nₐ/mₐ`.
Its defect from one and its variation retain the relative path drop.
-/

noncomputable section

namespace LipschitzHilbert

theorem pathCoefficient_pos {a b l r : ℝ} (hl : 0 < l) (hr : 0 < r) :
    0 < pathCoefficient a b l r := by
  unfold pathCoefficient
  positivity

theorem pathCoefficient_le_one {a b l r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    pathCoefficient a b l r ≤ 1 := by
  unfold pathCoefficient
  calc
    l ^ a * r ^ b ≤ 1 * r ^ b :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_one hl0 hl1 ha) (Real.rpow_nonneg hr0 _)
    _ ≤ 1 := by simpa only [one_mul] using Real.rpow_le_one hr0 hr1 hb

/-- Both mass fractions lie above `1-u`, so two exponents in `[0,1]`
give a coefficient defect at most `2u`. -/
theorem pathCoefficient_defect {a b l r u : ℝ}
    (ha : a ≤ 1) (hb : b ≤ 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hl : 1 - l ≤ u) (hr : 1 - r ≤ u) :
    1 - pathCoefficient a b l r ≤ 2 * u := by
  have hpowL := Real.self_le_rpow_of_le_one hl0 hl1 ha
  have hpowR := Real.self_le_rpow_of_le_one hr0 hr1 hb
  have hprod : l * r ≤ pathCoefficient a b l r := by
    exact mul_le_mul hpowL hpowR hr0 (Real.rpow_nonneg hl0 _)
  have hcompl := mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hr1)
  nlinarith

/-- Exponentiation is one-Lipschitz on the nonpositive real half-line. -/
theorem exp_nonpositive_lipschitz {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have h := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => Real.differentiableAt_exp)
    (fun x hx => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_one_iff.mpr hx) hy hx
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem positive_unit_interval_motion {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    |x - y| ≤ |Real.log x - Real.log y| := by
  have h := exp_nonpositive_lipschitz (Real.log_nonpos hx0.le hx1) (Real.log_nonpos hy0.le hy1)
  simpa only [Real.exp_log hx0, Real.exp_log hy0] using h

/-- Variation of the coefficient is controlled by the two complementary-mass
logarithm variations, with the exact exponent weights. -/
theorem pathCoefficient_motion {a b l r l' r' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl0 : 0 < l) (hl1 : l ≤ 1) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hl'0 : 0 < l') (hl'1 : l' ≤ 1) (hr'0 : 0 < r') (hr'1 : r' ≤ 1) :
    |pathCoefficient a b l' r' - pathCoefficient a b l r| ≤
      a * |Real.log l' - Real.log l| + b * |Real.log r' - Real.log r| := by
  have h := positive_unit_interval_motion (pathCoefficient_pos hl'0 hr'0)
    (pathCoefficient_le_one ha hb hl'0.le hl'1 hr'0.le hr'1)
    (pathCoefficient_pos hl0 hr0) (pathCoefficient_le_one ha hb hl0.le hl1 hr0.le hr1)
  have hlog (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
      Real.log (pathCoefficient a b x y) = a * Real.log x + b * Real.log y := by
    unfold pathCoefficient
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hy _).ne',
      Real.log_rpow hx, Real.log_rpow hy]
  rw [hlog l' r' hl'0 hr'0, hlog l r hl0 hr0] at h
  refine h.trans ?_
  calc
    _ = |a * (Real.log l' - Real.log l) + b * (Real.log r' - Real.log r)| := by congr 1; ring
    _ ≤ |a * (Real.log l' - Real.log l)| + |b * (Real.log r' - Real.log r)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- The actual shared child mass and its two complementary masses imply all
coefficient hypotheses used by the dominant prediction comparison. -/
theorem pathCoefficient_from_complementary_masses
    {a b n B D n' B' D' ε u : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hn : 0 < n) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hnmove : |n' - n| ≤ ε * n) (hBmove : |B' - B| ≤ ε * B)
    (hDmove : |D' - D| ≤ ε * D)
    (hBdrop : 1 - n / (n + B) ≤ u) (hDdrop : 1 - n / (n + D) ≤ u) :
    let C := pathCoefficient a b (n / (n + B)) (n / (n + D))
    let C' := pathCoefficient a b (n' / (n' + B')) (n' / (n' + D'))
    0 < C ∧ C ≤ 1 ∧ 1 - C ≤ 2 * u ∧ 0 < C' ∧ C' ≤ 1 ∧ |C' - C| ≤ 24 * ε * u := by
  dsimp only
  obtain ⟨hn', hnB', _⟩ := complementary_mass_fraction_motion hn hB hε0 hε1 hnmove hBmove
  obtain ⟨_, hnD', _⟩ := complementary_mass_fraction_motion hn hD hε0 hε1 hnmove hDmove
  have hB' : 0 ≤ B' := by
    have hmul := mul_le_mul_of_nonneg_right hε1 hB
    linarith [(abs_le.mp hBmove).1]
  have hD' : 0 ≤ D' := by
    have hmul := mul_le_mul_of_nonneg_right hε1 hD
    linarith [(abs_le.mp hDmove).1]
  have hl0 : 0 < n / (n + B) := div_pos hn (by linarith)
  have hr0 : 0 < n / (n + D) := div_pos hn (by linarith)
  have hl1 : n / (n + B) ≤ 1 := (div_le_one (by linarith : 0 < n + B)).2 (by linarith)
  have hr1 : n / (n + D) ≤ 1 := (div_le_one (by linarith : 0 < n + D)).2 (by linarith)
  have hl'0 : 0 < n' / (n' + B') := div_pos hn' hnB'
  have hr'0 : 0 < n' / (n' + D') := div_pos hn' hnD'
  have hl'1 : n' / (n' + B') ≤ 1 := (div_le_one hnB').2 (by linarith)
  have hr'1 : n' / (n' + D') ≤ 1 := (div_le_one hnD').2 (by linarith)
  refine ⟨pathCoefficient_pos hl0 hr0, pathCoefficient_le_one ha0 hb0 hl0.le hl1 hr0.le hr1,
    pathCoefficient_defect ha1 hb1 hl0.le hl1 hr0.le hr1 hBdrop hDdrop,
    pathCoefficient_pos hl'0 hr'0, pathCoefficient_le_one ha0 hb0 hl'0.le hl'1 hr'0.le hr'1, ?_⟩
  have hlmove := (complementary_mass_log_motion hn hB hε0 hε1 hnmove hBmove).trans
    (mul_le_mul_of_nonneg_left hBdrop (by positivity : 0 ≤ 12 * ε))
  have hrmove := (complementary_mass_log_motion hn hD hε0 hε1 hnmove hDmove).trans
    (mul_le_mul_of_nonneg_left hDdrop (by positivity : 0 ≤ 12 * ε))
  have h := pathCoefficient_motion ha0 hb0 hl0 hl1 hr0 hr1 hl'0 hl'1 hr'0 hr'1
  have hfirst := mul_le_mul_of_nonneg_left hlmove ha0
  have hsecond := mul_le_mul_of_nonneg_left hrmove hb0
  have hunitL := mul_le_mul_of_nonneg_right ha1 (abs_nonneg (Real.log (n' / (n' + B')) - Real.log (n / (n + B))))
  have hunitR := mul_le_mul_of_nonneg_right hb1 (abs_nonneg (Real.log (n' / (n' + D')) - Real.log (n / (n + D))))
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathCoefficientMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dominant path coefficient from actual complementary top masses.
Empty complementary sets contribute zero and retain the path-drop factor. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem source_submass_relative_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (A : Finset ι) (hA : A ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    let mass := fun x => ∑ t ∈ A, (T t).weight K D x
    let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
    |mass (SlopeBox.lineShift sR b z)-mass z| ≤ Real.exp δ*δ*mass z := by
  classical
  dsimp only
  by_cases hne : A.Nonempty
  · have hm := g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A hne hA b hb z
    have hp (x : ℝ × ℝ) : 0 < ∑ t ∈ A, (T t).weight K D x :=
      Finset.sum_pos (fun t _ => (T t).weight_pos hK D x) hne
    have hrel := massPowerScale_relative_motion (hp z) (hp (SlopeBox.lineShift sR b z))
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
      (show 0 ≤ (5*D/K)/Real.sqrt (g.branching:ℝ) by positivity)
      hm (by simp; positivity) 1 0
    simp only [massPowerScale,Real.rpow_one,Real.rpow_zero,mul_one,one_mul,
      abs_one,abs_zero,add_zero] at hrel
    exact positive_relative_motion_to_sub (hp z) hrel
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.sum_empty,sub_self,abs_zero,mul_zero,le_refl]

/-- The two complements are actual finite top sums. The parent drop
alone controls the coefficient drop and its motion. -/
theorem source_path_coefficient_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (parentSet boundarySet childSet : Finset ι)
    (hchildBoundary : childSet ⊆ boundarySet) (hboundaryParent : boundarySet ⊆ parentSet)
    (hne : childSet.Nonempty)
    (hparent : parentSet ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (a e u : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hsmall : Real.exp ((5*D/K)/Real.sqrt (g.branching:ℝ))*
      ((5*D/K)/Real.sqrt (g.branching:ℝ)) ≤ 1/2) :
    let mass := fun A x => ∑ t ∈ A, (T t).weight K D x
    let C := fun x => pathCoefficient a e
      (mass childSet x/mass parentSet x) (mass childSet x/mass boundarySet x)
    let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
    let q := Real.exp δ*δ
    1-mass childSet z/mass parentSet z ≤ u →
    0 < C z ∧ C z ≤ 1 ∧ 1-C z ≤ 2*u ∧
      0 < C (SlopeBox.lineShift sR b z) ∧ C (SlopeBox.lineShift sR b z) ≤ 1 ∧
      |C (SlopeBox.lineShift sR b z)-C z| ≤ 24*q*u := by
  classical
  dsimp only
  intro hdrop
  let mass := fun (A : Finset ι) x => ∑ t ∈ A, (T t).weight K D x
  let z' := SlopeBox.lineShift sR b z
  let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
  let q := Real.exp δ*δ
  have hq : 0 ≤ q := by dsimp [q,δ]; positivity
  have hchildParent : childSet ⊆ parentSet := hchildBoundary.trans hboundaryParent
  have hpos : 0 < mass childSet z :=
    Finset.sum_pos (fun t _ => (T t).weight_pos hK D z) hne
  have hboundaryPos : 0 < mass boundarySet z :=
    Finset.sum_pos (fun t _ => (T t).weight_pos hK D z) (hne.mono hchildBoundary)
  have hboundaryLe : mass boundarySet z ≤ mass parentSet z := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hboundaryParent
      (fun t _ _ => (T t).weight_pos hK D z |>.le)
  have hsplit (A : Finset ι) (hA : childSet ⊆ A) (x : ℝ × ℝ) :
      mass A x = mass childSet x+mass (A\childSet) x := by
    have hsum := Finset.sum_sdiff (f := fun t => (T t).weight K D x) hA
    dsimp [mass]
    linarith
  have hrelative (A : Finset ι) (hA : A ⊆ parentSet) :
      |mass A z'-mass A z| ≤ q*mass A z :=
    g.source_submass_relative_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A (hA.trans hparent) b hb z
  have hdropBoundary : 1-mass childSet z/(mass childSet z+mass (boundarySet\childSet) z) ≤ u := by
    rw [← hsplit boundarySet hchildBoundary]
    exact (sub_le_sub_left
      (div_le_div_of_nonneg_left hpos.le hboundaryPos hboundaryLe) 1).trans hdrop
  have hdropParent : 1-mass childSet z/(mass childSet z+mass (parentSet\childSet) z) ≤ u := by
    rw [← hsplit parentSet hchildParent]
    exact hdrop
  have hresult := pathCoefficient_from_complementary_masses ha0 ha1 he0 he1 hpos
    (show 0 ≤ mass (parentSet\childSet) z from Finset.sum_nonneg
      (fun t _ => (T t).weight_pos hK D z |>.le))
    (show 0 ≤ mass (boundarySet\childSet) z from Finset.sum_nonneg
      (fun t _ => (T t).weight_pos hK D z |>.le)) hq hsmall
    (hrelative childSet hchildParent)
    (hrelative (parentSet\childSet) Finset.sdiff_subset)
    (hrelative (boundarySet\childSet) (Finset.sdiff_subset.trans hboundaryParent))
    hdropParent hdropBoundary
  simpa only [← hsplit parentSet hchildParent z,← hsplit parentSet hchildParent z',
    ← hsplit boundarySet hchildBoundary z,← hsplit boundarySet hchildBoundary z'] using hresult

end LipschitzHilbert.AngularGrid

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

theorem source_shifted_path_coefficient_eq {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hK : 0 < K) (gap : ℕ → ℝ)
    (phase : Fin K → ℂ) (σ : Fin K) (j : ℕ) (μ r : ℝ)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0) (hreal : (phase σ).re = μ)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) (x : X) :
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x
    let c := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1))
      (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x
    let m := g.sourceBoundaryMass tops slope precision cutoff weight K gap
      (ShiftedBlocks.lastTransition σ j) (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x
    let lam := g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap
        (fun i => phase (ShiftedBlocks.tag hK i)) x)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) (slope top)
    (c/n)^(1-μ-1/r)*‖lam‖ = pathCoefficient (1-μ-1/r) μ (c/n) (c/m) := by
  dsimp only
  rw [g.source_shifted_block_norm tops slope precision cutoff weight hp hw hK gap phase σ j
    hphase top htop he x,hreal]
  rfl

/-- The actual shifted-block coefficient inherits the complementary-mass
motion estimate, with the path drop left as a factor. -/
theorem source_shifted_path_coefficient_motion {ι : Type*} {Kb : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hKb : 0 < Kb) (gap : ℕ → ℝ) (phase : Fin Kb → ℂ) (σ : Fin Kb) (j : ℕ)
    (μ r u : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hr : 1 ≤ r)
    (ha : 0 ≤ 1-μ-1/r)
    (hphase : ∀ τ, τ ≠ σ → (phase τ).re = 0) (hreal : (phase σ).re = μ)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ (j+1)))
    (h : ℕ) (hbase : h ≤ ShiftedBlocks.endpoint σ j)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (hblock : g.width h ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (b : ℝ) (hb : |b| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (z : ℝ × ℝ)
    (hsmall : Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ)) ≤ 1/2) :
    let weight := fun t x => (T t).weight Kw D x
    let n := fun x => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (T top).slope) x
    let c := fun x => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight (ShiftedBlocks.endpoint σ (j+1))
      (g.index (ShiftedBlocks.endpoint σ (j+1)) (T top).slope) x
    let lam := fun x => g.packetPathProduct
      (g.sourceTransition tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (fun i => phase (ShiftedBlocks.tag hKb i)) x)
      (ShiftedBlocks.endpoint σ j) (ShiftedBlocks.endpoint σ (j+1)) (T top).slope
    let C := fun x => (c x/n x)^(1-μ-1/r)*‖lam x‖
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    1-c z/n z ≤ u →
    0 < C z ∧ C z ≤ 1 ∧ 1-C z ≤ 2*u ∧
      0 < C (SlopeBox.lineShift sR b z) ∧ C (SlopeBox.lineShift sR b z) ≤ 1 ∧
      |C (SlopeBox.lineShift sR b z)-C z| ≤ 24*(Real.exp δ*δ)*u := by
  classical
  dsimp only
  intro hdrop
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let lo := ShiftedBlocks.endpoint σ j
  let hi := ShiftedBlocks.endpoint σ (j+1)
  let last := ShiftedBlocks.lastTransition σ j
  let parentSet := g.cellTops tops slope precision cutoff lo (g.index lo (slope top))
  let childSet := g.cellTops tops slope precision cutoff hi (g.index hi (slope top))
  let boundarySet := g.boundaryTops tops slope precision cutoff lo last (gap last) (slope top)
  let total := fun (A : Finset ι) x => ∑ t ∈ A, weight t x
  let C := fun x => (total childSet x/total parentSet x)^(1-μ-1/r)*
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight Kb gap
      (fun i => phase (ShiftedBlocks.tag hKb i)) x) lo hi (slope top)‖
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hwpos (t : ι) (x : ℝ × ℝ) : 0 < weight t x := (T t).weight_pos hKw D x
  have hlast : lo ≤ last := (Finset.mem_Ico.mp (ShiftedBlocks.lastTransition_mem hKb σ j)).1
  have hchildBoundary : childSet ⊆ boundarySet := by
    have hc := g.cellTops_subset_ancestor tops slope precision cutoff hp (Nat.le_succ last) (slope top)
    have hb0 := g.parent_subset_boundary tops slope precision cutoff lo last (gap last) (slope top)
    have hc' : childSet ⊆ g.cellTops tops slope precision cutoff last (g.index last (slope top)) := by
      simpa only [childSet,hi,last,Nat.succ_eq_add_one,ShiftedBlocks.lastTransition_succ] using hc
    exact hc'.trans hb0
  have hboundaryParent : boundarySet ⊆ parentSet :=
    g.boundary_subset_ancestor tops slope precision cutoff hp hlast (gap last) (slope top)
  have hne : childSet.Nonempty :=
    ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩⟩
  have hboundary (x : ℝ × ℝ) : g.sourceBoundaryMass tops slope precision cutoff weight Kb gap last
      (g.index hi (slope top)) x = total boundarySet x := by
    change g.sourceBoundaryMass tops slope precision cutoff weight Kb gap
      (ShiftedBlocks.lastTransition σ j)
      (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) x = total boundarySet x
    rw [← ShiftedBlocks.lastTransition_succ σ j,g.sourceBoundaryMass_path tops slope precision cutoff weight hKb,
      ← ShiftedBlocks.endpoint_eq_last_sub σ j]
    rfl
  have hC (x : ℝ × ℝ) : C x = pathCoefficient (1-μ-1/r) μ
      (total childSet x/total parentSet x) (total childSet x/total boundarySet x) := by
    have heq := g.source_shifted_path_coefficient_eq tops slope precision cutoff weight hp hwpos hKb gap
      phase σ j μ r hphase hreal top htop he x
    change C x = pathCoefficient (1-μ-1/r) μ
      (total childSet x/total parentSet x)
      (total childSet x/g.sourceBoundaryMass tops slope precision cutoff weight Kb gap last
        (g.index hi (slope top)) x) at heq
    rw [hboundary] at heq
    exact heq
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hresult := g.source_path_coefficient_motion tops T w B Kw D hw hB hKw hD hwidth
    0 h lo hbase 0 (by norm_num) (g.width_pos h).le (slope top) sR hs
    (g.width hi) (g.width_pos hi) hblock parentSet boundarySet childSet hchildBoundary hboundaryParent hne
    (g.parent_subset_boundary tops slope precision cutoff 0 lo 0 (slope top)) b hb z
    (1-μ-1/r) μ u ha (by have : 0 ≤ 1/r := div_nonneg zero_le_one hr0.le; linarith)
    hμ0 hμ1 hsmall hdrop
  change 0 < C z ∧ C z ≤ 1 ∧ 1-C z ≤ 2*u ∧
    0 < C (SlopeBox.lineShift sR b z) ∧ C (SlopeBox.lineShift sR b z) ≤ 1 ∧
    |C (SlopeBox.lineShift sR b z)-C z| ≤
      24*(Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
        ((5*D/Kw)/Real.sqrt (g.branching:ℝ)))*u
  rw [hC z,hC (SlopeBox.lineShift sR b z)]
  exact hresult

end LipschitzHilbert.AngularGrid

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

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockPathMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted source coefficients supply every dominant-path
motion premise. The relative drop is retained even when it is zero. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid

 theorem eventually_source_block_path_motion_oai (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ), 0 < w → 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hKb : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (j : ℕ), ((ShiftedBlocks.endpoint σ (j+1)-ShiftedBlocks.endpoint σ j:ℕ):ℝ) ≤ L^2 →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (Z μ p u : ℝ),
      0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) → (phase σ).re = μ →
      0 ≤ μ → μ ≤ 1 → 1 ≤ p → 0 ≤ 1-μ-1/p → 0 ≤ u →
    ∀ (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length)
        (ShiftedBlocks.endpoint σ (j+1)) →
    ∀ (sR : ℝ), g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR →
    ∀ (z : ℝ × ℝ),
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let weight := fun t zz => (T t).weight Kw D zz
    let n := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight lower (g.index lower (T top).slope) zz
    let c := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight upper (g.index upper (T top).slope) zz
    let lam := fun zz => g.packetPathProduct
      (g.sourceTransition tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/(SourceParameters.branching L)^2) weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
      lower upper (T top).slope
    let coeff := fun zz => (c zz/n zz)^(1-μ-1/p)*‖lam zz‖
    1-c z/n z ≤ u →
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ q ≤ SourceParameters.step L^(-(1/8:ℝ)) ∧
      lam z ≠ 0 ∧ 0 ≤ coeff z ∧ coeff z ≤ 1 ∧ 1-coeff z ≤ 2*u ∧
      ∀ b : ℝ, |b| ≤ sourceLineScale g L w upper →
        ‖lam (SlopeBox.lineShift sR b z)-lam z‖ ≤ q*‖lam z‖ ∧
        |coeff (SlopeBox.lineShift sR b z)-coeff z| ≤
          24*SourceParameters.step L^(-(1/8:ℝ))*u := by
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp
    source_step_tendsto_atTop).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_source_path_errors_small D hD,hsmall] with L herrors hsmall
  intro ι g tops T w Kw hw hKw hbranch hwidth hKb σ j hsteps phase Z μ p u
    hZ0 hZ hphase hother hreal hμ0 hμ1 hp ha hu top htop he sR hs z
  dsimp only
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
  let e := (upper-lower:ℕ)*Z*(2*δ)
  let q := Real.exp e*e
  have herror := herrors Kw Z (upper-lower) hKw hZ0 hZ hsteps
  have hB : 1 ≤ SourceParameters.branching L := by
    exact one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hblock := (g.source_shifted_width_bounds L hbranch hKb σ j).2
  have hq0 : 0 ≤ q := by dsimp [q,e,δ]; positivity
  have hqε : q ≤ SourceParameters.step L^(-(1/8:ℝ)) := herror.2
  have hq1 : q < 1 := hqε.trans_lt hsmall
  intro hdrop
  have hcoef := g.source_shifted_path_coefficient_motion tops T w (SourceParameters.branching L)
    Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hKb (g.sourceBoundaryGap L)
    phase σ j μ p u hμ0 hμ1 hp ha hother hreal top htop he lower le_rfl sR hs
    hblock 0 (by
      rw [abs_zero]
      exact (div_pos hw (mul_pos (g.width_pos _)
        (Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) g.branching_ge_two)))).le) z
    (by simpa only [hbranch] using herror.1.1.trans (by norm_num : (1/8:ℝ)≤1/2)) hdrop
  dsimp only at hcoef
  refine ⟨q,hq0,hq1,hqε,?_,hcoef.1.le,hcoef.2.1,hcoef.2.2.1,?_⟩
  · exact g.source_path_product_ne_zero _ _ _ _ _ _ _ _ _ _ _ _
  · intro b hb
    have hb' : |b| ≤ w/(g.width upper*Real.sqrt (g.branching:ℝ)) := by
      simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using hb
    have hrelative := g.source_block_transition_relative_motion tops T w (SourceParameters.branching L)
      Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hKb (g.sourceBoundaryGap L)
      (fun k => phase (ShiftedBlocks.tag hKb k)) lower lower upper le_rfl
      (fun k hk => ⟨(g.sourceBoundaryGap_pos L k).le,
        g.sourceBoundaryGap_le_width L (Finset.mem_Ico.mp hk).1⟩)
      top htop he sR hs (g.width upper) (g.width_pos upper) hblock b hb' z Z hZ0
      (fun k _ => hphase (ShiftedBlocks.tag hKb k))
    have hmove := g.source_shifted_path_coefficient_motion tops T w (SourceParameters.branching L)
      Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hKb (g.sourceBoundaryGap L)
      phase σ j μ p u hμ0 hμ1 hp ha hother hreal top htop he lower le_rfl sR hs
      hblock b hb' z
      (by simpa only [hbranch] using herror.1.1.trans (by norm_num : (1/8:ℝ)≤1/2)) hdrop
    refine ⟨?_,hmove.2.2.2.2.2.trans ?_⟩
    · exact complex_relative_motion_to_sub
        (g.source_path_product_ne_zero _ _ _ _ _ _ _ _ _ _ _ _)
        (by simpa only [hbranch] using hrelative)
    · simpa only [hbranch] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left herror.1.2 (by norm_num : (0:ℝ)≤24)) hu

end LipschitzHilbert.AngularGrid

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion_oai := @OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion_oai
