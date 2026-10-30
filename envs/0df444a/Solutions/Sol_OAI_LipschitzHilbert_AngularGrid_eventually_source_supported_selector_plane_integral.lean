-- Prove2me | solution 1 for OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_plane_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:12:16.046763+00:00
-- url     : https://prove2.me/submissions/29a9f393-e8f8-4cc3-892c-4893172f0ddd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_eventually_source_supported_selector_path_predictor

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

theorem sum_log_ratios (n : ℕ → ℝ) (N : ℕ) (hn : ∀ j ≤ N, 0 < n j) :
    (∑ j ∈ Finset.range N, Real.log (n j / n (j + 1))) = Real.log (n 0 / n N) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      Real.log (n j / n (j + 1)) = Real.log (n j) - Real.log (n (j + 1)) :=
    Real.log_div (hn j (by have := Finset.mem_range.mp hj; omega)).ne'
      (hn (j + 1) (by have := Finset.mem_range.mp hj; omega)).ne'
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  exact (Real.log_div (hn 0 (Nat.zero_le N)).ne' (hn N le_rfl).ne').symm

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

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LogEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Logarithmic energy and relative prediction deficits

The exact `p`-Lipschitz estimate for `log (1 + ‖x‖^p)` from §§9–10.
A fixed denominator then cancels from differences of log predictions,
so bounded off-path motion gives a deficit proportional to the path drop.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E]

theorem energyRatio_pos {p denominator : ℝ} (hd : 0 < denominator) (x : E) :
    0 < energyRatio p denominator x := div_pos (by positivity) hd

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NestedAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Products of nested conditional-average factors

Finite measurable partitions model the nested mesh inside one fixed root cell.
Each factor is constant on the next partition and has average at most one on
every current cell. The product estimate below is an actual integral estimate.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

/-- Decompose a finite-profile multiplier over its measurable cells. -/
theorem integral_finite_profile_mul (μ : Measure α) (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) (f : α → ℝ)
    (hf : Integrable f μ) :
    (∫ x, c (P x) * f x ∂μ) = ∑ i, c i * ∫ x in {x | P x = i}, f x ∂μ := by
  classical
  have hpoint (x : α) : c (P x) * f x =
      ∑ i, c i * ({y | P y = i}.indicator f) x := by
    symm
    rw [Finset.sum_eq_single (P x)]
    · simp
    · intro i _ hi
      simp [Set.indicator_of_notMem (show x ∉ {y | P y = i} from fun h => hi h.symm)]
    · simp
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_indicator (hP i)]
  · intro i _
    exact (hf.indicator (hP i)).const_mul _

theorem integral_finite_profile (μ : Measure α) [IsFiniteMeasure μ]
    (P : α → κ) (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) :
    (∫ x, c (P x) ∂μ) = ∑ i, c i * μ.real {x | P x = i} := by
  simpa only [mul_one, integral_const, smul_eq_mul, one_mul, measureReal_restrict_apply_univ] using
    integral_finite_profile_mul μ P hP c (fun _ => 1) (integrable_const 1)

theorem integrable_finite_profile (μ : Measure α) [IsFiniteMeasure μ]
    (P : α → κ) (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) :
    Integrable (fun x => c (P x)) μ := by
  classical
  have heq : (fun x => c (P x)) =
      fun x => ∑ i, ({y | P y = i}.indicator (fun _ => c i)) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (P x)]
    · simp
    · intro i _ hi
      exact Set.indicator_of_notMem (show x ∉ {y | P y = i} from fun h => hi h.symm) _
    · simp
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (integrable_const _).indicator (hP i)

/-- Conditional cell-average domination contracts the integral of each
nonnegative factor constant on the coarse partition. -/
theorem integral_profile_mul_le (μ : Measure α) [IsFiniteMeasure μ]
    (P : α → κ) (hP : ∀ i, MeasurableSet {x | P x = i})
    (c : κ → ℝ) (hc : ∀ i, 0 ≤ c i) (f : α → ℝ) (hf : Integrable f μ)
    (haverage : ∀ i, (∫ x in {x | P x = i}, f x ∂μ) ≤ μ.real {x | P x = i}) :
    (∫ x, c (P x) * f x ∂μ) ≤ ∫ x, c (P x) ∂μ := by
  rw [integral_finite_profile_mul μ P hP c f hf, integral_finite_profile μ P hP c]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (haverage i) (hc i)

omit [MeasurableSpace α] [Fintype κ] in
theorem nestedProductProfile_nonnegative (R : ℕ → κ → κ) (g : ℕ → κ → ℝ)
    {N : ℕ} (hg : ∀ n < N, ∀ i, 0 ≤ g n i) :
    ∀ n ≤ N, ∀ i, 0 ≤ nestedProductProfile R g n i := by
  intro n hn
  induction n with
  | zero => intro i; exact zero_le_one
  | succ n ih =>
    intro i
    exact mul_nonneg (ih (Nat.le_of_succ_le hn) (R n i))
      (hg n (Nat.lt_of_succ_le hn) i)

omit [MeasurableSpace α] [Fintype κ] in
theorem nestedProductProfile_eq_product (P : ℕ → α → κ) (R : ℕ → κ → κ)
    (g : ℕ → κ → ℝ) {N : ℕ}
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x)) :
    ∀ n ≤ N, ∀ x, nestedProductProfile R g n (P n x) =
      ∏ j ∈ Finset.range n, g j (P (j + 1) x) := by
  intro n hn
  induction n with
  | zero => intro x; simp [nestedProductProfile]
  | succ n ih =>
    intro x
    rw [nestedProductProfile, ← hrefine n (Nat.lt_of_succ_le hn) x,
      ih (Nat.le_of_succ_le hn) x, Finset.prod_range_succ]

theorem integrable_nested_product (μ : Measure α) [IsFiniteMeasure μ]
    (P : ℕ → α → κ) (R : ℕ → κ → κ) (g : ℕ → κ → ℝ) (N : ℕ)
    (hP : ∀ i, MeasurableSet {x | P N x = i})
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x)) :
    Integrable (fun x => ∏ j ∈ Finset.range N, g j (P (j + 1) x)) μ := by
  have heq : (fun x => ∏ j ∈ Finset.range N, g j (P (j + 1) x)) =
      fun x => nestedProductProfile R g N (P N x) := by
    funext x
    exact (nestedProductProfile_eq_product P R g hrefine N le_rfl x).symm
  rw [heq]
  exact integrable_finite_profile μ (P N) hP (nestedProductProfile R g N)

/-- Products of nonnegative next-step factors with conditional cell averages
at most one have total integral at most the measure of the root space. -/
theorem nested_average_product_le (μ : Measure α) [IsFiniteMeasure μ]
    (P : ℕ → α → κ) (R : ℕ → κ → κ) (g : ℕ → κ → ℝ) (N : ℕ)
    (hP : ∀ n ≤ N, ∀ i, MeasurableSet {x | P n x = i})
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x))
    (hg : ∀ n < N, ∀ i, 0 ≤ g n i)
    (haverage : ∀ n < N, ∀ i,
      (∫ x in {x | P n x = i}, g n (P (n + 1) x) ∂μ) ≤ μ.real {x | P n x = i}) :
    (∫ x, ∏ j ∈ Finset.range N, g j (P (j + 1) x) ∂μ) ≤ μ.real Set.univ := by
  have hstep : ∀ n < N,
      (∫ x, nestedProductProfile R g (n + 1) (P (n + 1) x) ∂μ) ≤
        ∫ x, nestedProductProfile R g n (P n x) ∂μ := by
    intro n hn
    have heq : (fun x => nestedProductProfile R g (n + 1) (P (n + 1) x)) =
        fun x => nestedProductProfile R g n (P n x) * g n (P (n + 1) x) := by
      funext x
      rw [nestedProductProfile, ← hrefine n hn x]
    rw [heq]
    exact integral_profile_mul_le μ (P n) (hP n hn.le) (nestedProductProfile R g n)
      (nestedProductProfile_nonnegative R g hg n hn.le)
      (fun x => g n (P (n + 1) x))
      (integrable_finite_profile μ (P (n + 1)) (hP (n + 1) (Nat.succ_le_of_lt hn)) (g n))
      (haverage n hn)
  have hbound : ∀ n ≤ N,
      (∫ x, nestedProductProfile R g n (P n x) ∂μ) ≤ μ.real Set.univ := by
    intro n hn
    induction n with
    | zero => simp [nestedProductProfile, integral_const]
    | succ n ih => exact (hstep n (Nat.lt_of_succ_le hn)).trans (ih (Nat.le_of_succ_le hn))
  simpa only [nestedProductProfile_eq_product P R g hrefine N le_rfl] using hbound N le_rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ProductPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Accumulating pointwise prediction errors without a loss per level. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

omit [MeasurableSpace α] in
theorem product_le_exp_sum (β γ e : ι → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (hcomparison : ∀ i, β i ≤ Real.exp (e i) * γ i) :
    (∏ i, β i) ≤ Real.exp (∑ i, e i) * ∏ i, γ i := by
  calc
    _ ≤ ∏ i, Real.exp (e i) * γ i := Finset.prod_le_prod
      (fun i _ => hβ i) (fun i _ => hcomparison i)
    _ = _ := by rw [Finset.prod_mul_distrib, Real.exp_sum]

omit [MeasurableSpace α] in
theorem product_le_of_error_budget (β γ e : ι → ℝ) (B : ℝ)
    (hβ : ∀ i, 0 ≤ β i) (hγ : ∀ i, 0 ≤ γ i)
    (hcomparison : ∀ i, β i ≤ Real.exp (e i) * γ i) (hbudget : ∑ i, e i ≤ B) :
    (∏ i, β i) ≤ Real.exp B * ∏ i, γ i :=
  (product_le_exp_sum β γ e hβ hcomparison).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbudget)
      (Finset.prod_nonneg (fun i _ => hγ i)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_PathDrops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic budget for relative drops on an active hierarchy path. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem pathDrop_le_log (n : ℕ → ℝ) (i : ℕ)
    (hi : 0 < n i) (hi' : 0 < n (i + 1)) :
    pathDrop n i ≤ Real.log (n i / n (i + 1)) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hi hi')
  rw [inv_div] at h
  calc
    _ = 1 - n (i + 1) / n i := by unfold pathDrop; field_simp
    _ ≤ _ := h

theorem pathDrop_le_one (n : ℕ → ℝ) (i : ℕ) (hi : 0 < n i)
    (hi' : 0 ≤ n (i + 1)) : pathDrop n i ≤ 1 := by
  exact (div_le_one hi).2 (by linarith)

theorem pathDrop_nonnegative (n : ℕ → ℝ) (i : ℕ) (hi : 0 < n i)
    (hmono : n (i + 1) ≤ n i) : 0 ≤ pathDrop n i :=
  div_nonneg (sub_nonneg.mpr hmono) hi.le

theorem active_path_drop_budget (n : ℕ → ℝ) (N : ℕ) {M : ℝ}
    (hM : 0 < M) (hactive : ∀ i < N, M < n i) (hlast : 0 ≤ n N) :
    (∑ i ∈ Finset.range N, pathDrop n i) ≤ 1 + max 0 (Real.log (n 0 / M)) := by
  cases N with
  | zero => simp only [Finset.sum_range_zero]; positivity
  | succ N =>
    have hn (i : ℕ) (hi : i ≤ N) : 0 < n i := hM.trans (hactive i (by omega))
    have hpre : (∑ i ∈ Finset.range N, pathDrop n i) ≤ Real.log (n 0 / n N) := by
      calc
        _ ≤ ∑ i ∈ Finset.range N, Real.log (n i / n (i + 1)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hiN := Finset.mem_range.mp hi
          exact pathDrop_le_log n i (hn i (by omega)) (hn (i + 1) (by omega))
        _ = _ := sum_log_ratios n N hn
    have hlog : Real.log (n 0 / n N) ≤ Real.log (n 0 / M) := by
      apply Real.log_le_log (div_pos (hn 0 (Nat.zero_le N)) (hn N le_rfl))
      exact div_le_div_of_nonneg_left (hn 0 (Nat.zero_le N)).le hM
        (hactive N (by omega)).le
    have hlastdrop := pathDrop_le_one n N (hn N le_rfl) hlast
    rw [Finset.sum_range_succ]
    linarith [le_max_right 0 (Real.log (n 0 / M))]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NestedPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested prediction products with an explicit total logarithmic-error budget. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

omit [MeasurableSpace α] [Fintype κ] in
theorem stopped_error_budget (n e : ℕ → ℝ) (N stop : ℕ) (hstop : stop ≤ N)
    {M C L : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    (hactive : ∀ j < stop, M < n j) (hlast : 0 ≤ n stop)
    (hlog : max 0 (Real.log (n 0 / M)) ≤ L)
    (he : ∀ j < N, e j ≤ if j < stop then C * pathDrop n j else 0) :
    (∑ j ∈ Finset.range N, e j) ≤ C * (1 + L) := by
  have hfilter : (Finset.range N).filter (fun j => j < stop) = Finset.range stop := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ ≤ ∑ j ∈ Finset.range N, if j < stop then C * pathDrop n j else 0 :=
      Finset.sum_le_sum (fun j hj => he j (Finset.mem_range.mp hj))
    _ = C * ∑ j ∈ Finset.range stop, pathDrop n j := by
      rw [← Finset.sum_filter, hfilter, Finset.mul_sum]
    _ ≤ C * (1 + max 0 (Real.log (n 0 / M))) :=
      mul_le_mul_of_nonneg_left (active_path_drop_budget n stop hM hactive hlast) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog) hC

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PartitionIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing nonnegative cell estimates over a countable measurable partition. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α ι : Type*} [MeasurableSpace α] [Countable ι]

/-- Summable control on partition cells proves global integrability as well
as the global estimate; no integrability of the left side is assumed. -/
theorem integral_le_of_partition (μ : Measure α) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcover : (⋃ i, s i) = Set.univ) (f g : α → ℝ) {C : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hgint : Integrable g μ)
    (hf : ∀ i, IntegrableOn f (s i) μ)
    (hbound : ∀ i, (∫ x in s i, f x ∂μ) ≤ C * ∫ x in s i, g x ∂μ) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C * ∫ x, g x ∂μ := by
  have hgsum : Summable (fun i => ∫ x in s i, g x ∂μ) :=
    (hasSum_integral_iUnion hs hd hgint.integrableOn).summable
  have hfsum : Summable (fun i => ∫ x in s i, f x ∂μ) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg hf0) hbound (hgsum.mul_left C)
  have hnorm : Summable (fun i => ∫ x in s i, ‖f x‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hfsum
  have hfint := integrableOn_iUnion_of_summable_integral_norm hf hnorm
  rw [hcover, integrableOn_univ] at hfint
  have hfi := integral_iUnion hs hd hfint.integrableOn
  have hgi := integral_iUnion hs hd hgint.integrableOn
  rw [hcover, setIntegral_univ] at hfi hgi
  refine ⟨hfint, ?_⟩
  calc
    (∫ x, f x ∂μ) = ∑' i, ∫ x in s i, f x ∂μ := hfi
    _ ≤ ∑' i, C * ∫ x in s i, g x ∂μ := hfsum.tsum_le_tsum hbound (hgsum.mul_left C)
    _ = C * ∑' i, ∫ x in s i, g x ∂μ := tsum_mul_left
    _ = C * ∫ x, g x ∂μ := congrArg (C * ·) hgi.symm

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteLineCells
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact intervals underlying the finite line-mesh index maps. -/

noncomputable section

open Set

namespace LipschitzHilbert.FiniteLineGrid

theorem index_eq_iff_mem_cell (g : FiniteLineGrid) {level : ℕ}
    (hl : level ≤ g.depth) {x : ℝ} (hx : x ∈ g.root) (i : ℕ) :
    (g.index level x).val = i ↔ x ∈ g.cell level i := by
  have hG : (0 : ℝ) < g.branching := by exact_mod_cast g.branching_pos
  have hrep : (x - g.origin) / g.width * (g.branching : ℝ) ^ level =
      (x - g.origin) / g.meshWidth level := by
    unfold meshWidth
    field_simp
  have hn : 0 ≤ (x - g.origin) / g.meshWidth level :=
    div_nonneg (sub_nonneg.mpr hx.1) (g.meshWidth_pos level).le
  simp only [index, rawIndex, Nat.min_eq_left hl, ite_eq_left hx, hrep]
  rw [Nat.floor_eq_iff hn]
  change (i : ℝ) ≤ (x - g.origin) / g.meshWidth level ∧
      (x - g.origin) / g.meshWidth level < i + 1 ↔
    g.origin + g.meshWidth level * i ≤ x ∧ x < g.origin + g.meshWidth level * (i + 1)
  rw [le_div_iff₀ (g.meshWidth_pos level), div_lt_iff₀ (g.meshWidth_pos level)]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> nlinarith

theorem cell_subset_root (g : FiniteLineGrid) (level : ℕ) {i : ℕ}
    (hi : i < g.branching ^ level) : g.cell level i ⊆ g.root := by
  have hwidth := g.meshWidth_pos level
  have hG : (0 : ℝ) < g.branching := by exact_mod_cast g.branching_pos
  have hupper : (i : ℝ) + 1 ≤ (g.branching : ℝ) ^ level := by
    exact_mod_cast (show i + 1 ≤ g.branching ^ level by omega)
  have hmul := mul_le_mul_of_nonneg_left hupper hwidth.le
  have hrestore : g.meshWidth level * (g.branching : ℝ) ^ level = g.width := by
    exact div_mul_cancel₀ _ (pow_pos hG _).ne'
  rw [hrestore] at hmul
  intro x hx
  change g.origin + g.meshWidth level * i ≤ x ∧
    x < g.origin + g.meshWidth level * (i + 1) at hx
  change g.origin ≤ x ∧ x < g.origin + g.width
  have hzero : 0 ≤ g.meshWidth level * i := mul_nonneg hwidth.le (Nat.cast_nonneg _)
  constructor <;> linarith [hx.1, hx.2]

/-- Restricting the coarse-index fiber to the root gives exactly its
half-open mesh interval. -/
theorem index_fiber_inter_root (g : FiniteLineGrid) {level : ℕ}
    (hl : level ≤ g.depth) {i : ℕ} (hi : i < g.branching ^ level) :
    {x ∈ g.root | (g.index level x).val = i} = g.cell level i := by
  ext x
  constructor
  · intro hx
    exact (g.index_eq_iff_mem_cell hl hx.1 i).mp hx.2
  · intro hx
    have hr := g.cell_subset_root level hi hx
    exact ⟨hr, (g.index_eq_iff_mem_cell hl hr i).mpr hx⟩

end LipschitzHilbert.FiniteLineGrid

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

/-- On a cell of length at most the top length, the logarithm of its weight
varies by an absolute constant along its own reference direction. -/
theorem log_weight_same_slope (T : SlopeBox) {K D t : ℝ}
    (hK : 1 ≤ K) (hD : 0 ≤ D) (ht : |t| ≤ T.length) (z : ℝ × ℝ) :
    |Real.log (T.weight K D (lineShift T.slope t z)) - Real.log (T.weight K D z)| ≤ D := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hlength := T.length_pos
  have h := T.log_weight_line_motion hK0 hD T.slope t z
  simp only [sub_self, abs_zero, zero_div, add_zero] at h
  calc
    _ ≤ (D / K) * (1 / T.length) * |t| := h
    _ ≤ (D / K) * (1 / T.length) * T.length :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = D / K := by field_simp [T.length_pos.ne']
    _ ≤ D := (div_le_self hD hK)

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

end LipschitzHilbert.ShiftedBlocks

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlicedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From almost-everywhere line estimates to planar estimates, including
the area-preserving coordinates of a fixed reference slope. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- For a nonnegative measurable integrand, integrable slices and a common
integrable bound on their integrals prove the full product estimate. -/
theorem integral_le_of_slices (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (f g : α × β → ℝ) {C : ℝ}
    (hfmeas : AEStronglyMeasurable f (μ.prod ν)) (hf0 : ∀ z, 0 ≤ f z)
    (hg : Integrable g (μ.prod ν))
    (hfslice : ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ)
    (hbound : ∀ᵐ y ∂ν, (∫ x, f (x, y) ∂μ) ≤ C * ∫ x, g (x, y) ∂μ) :
    Integrable f (μ.prod ν) ∧
      (∫ z, f z ∂μ.prod ν) ≤ C * ∫ z, g z ∂μ.prod ν := by
  have hi : Integrable (fun y => ∫ x, f (x, y) ∂μ) ν :=
    (hg.integral_prod_right.const_mul C).mono'
      hfmeas.prod_swap.integral_prod_right' (by
        filter_upwards [hbound] with y hy
        have hnonneg : 0 ≤ ∫ x, f (x, y) ∂μ := integral_nonneg fun x => hf0 (x, y)
        simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hy)
  have hinorm : Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hi
  have hf : Integrable f (μ.prod ν) := (integrable_prod_iff' hfmeas).2 ⟨hfslice, hinorm⟩
  refine ⟨hf, ?_⟩
  rw [integral_prod_symm f hf, integral_prod_symm g hg, ← integral_const_mul]
  exact integral_mono_ae hi (hg.integral_prod_right.const_mul C) hbound

theorem integral_slopeShear (s : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f (slopeShear s z) ∂volume.prod volume) = ∫ z, f z ∂volume.prod volume :=
  (slopeShear_measurePreserving s).integral_comp (slopeShear s).measurableEmbedding f

/-- The slice argument applies in the reference-line coordinates without
requiring a jointly measurable family of auxiliary prediction functions. -/
theorem integral_le_of_slope_slices (s : ℝ) (f g : ℝ × ℝ → ℝ) {C : ℝ}
    (hfmeas : AEStronglyMeasurable f (volume.prod volume)) (hf0 : ∀ z, 0 ≤ f z)
    (hg : Integrable g (volume.prod volume))
    (hfslice : ∀ᵐ y ∂volume, Integrable (fun x => f (x, y + s * x)) volume)
    (hbound : ∀ᵐ y ∂volume,
      (∫ x, f (x, y + s * x)) ≤ C * ∫ x, g (x, y + s * x)) :
    Integrable f (volume.prod volume) ∧
      (∫ z, f z ∂volume.prod volume) ≤ C * ∫ z, g z ∂volume.prod volume := by
  have hpres := slopeShear_measurePreserving s
  obtain ⟨hfi, hle⟩ := integral_le_of_slices volume volume
    (f ∘ slopeShear s) (g ∘ slopeShear s)
    (hfmeas.comp_measurePreserving hpres) (fun z => hf0 _)
    (hpres.integrable_comp_of_integrable hg) hfslice hbound
  refine ⟨(hpres.integrable_comp hfmeas).1 hfi, ?_⟩
  simpa only [Function.comp_apply, integral_slopeShear] using hle

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

theorem integral_planeDivide (f : ℝ × ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ z, f (planeDivide a b ha hb z) ∂volume.prod volume) =
      (|a| * |b|) * ∫ z, f z ∂volume.prod volume := by
  rw [← integral_map_equiv (planeDivide a b ha hb), map_planeDivide, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

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

/-- Exact area scaling: all dependence on the box and the dilation is
`K² * length * width`, while the remaining integral is a fixed constant. -/
theorem integral_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    (∫ z, T.weight K D z ∂volume.prod volume) =
      (2 ^ D * ∫ z, topProfile D z ∂volume.prod volume) *
        K ^ 2 * T.length * T.width := by
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq, integral_const_mul, integral_sub_right_eq_self]
  simp only [Function.comp_apply]
  rw [integral_slopeShear (-T.slope) (fun z => topProfile D
    (planeDivide (K * T.length) (K * T.width)
      (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)),
    integral_planeDivide, abs_of_pos (mul_pos hK T.length_pos),
    abs_of_pos (mul_pos hK T.width_pos)]
  ring

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

theorem weight_continuous (T : SlopeBox) (K D : ℝ) (hK : 0 < K) : Continuous (T.weight K D) := by
  unfold weight radius horizontal transverse
  apply Continuous.mul continuous_const
  apply Continuous.rpow_const
  · fun_prop
  · intro z
    left
    have h : 0 ≤ |(z.1-T.x)/T.length|+|((z.2-T.y)-T.slope*(z.1-T.x))/T.width| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    positivity

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cellwise weighted averaging step in §10. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α]

/-- A nonnegative factor of average at most one may be integrated against
a weight comparable to a constant, with the same comparison loss. -/
theorem weighted_average_le (μ : Measure α) [IsFiniteMeasure μ]
    (w f : α → ℝ) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hw : AEStronglyMeasurable w μ) (hf : Integrable f μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hlower : ∀ᵐ x ∂μ, c ≤ w x)
    (hupper : ∀ᵐ x ∂μ, w x ≤ C * c)
    (haverage : (∫ x, f x ∂μ) ≤ μ.real Set.univ) :
    Integrable (fun x => w x * f x) μ ∧
      (∫ x, w x * f x ∂μ) ≤ C * ∫ x, w x ∂μ := by
  have hw0 : ∀ᵐ x ∂μ, 0 ≤ w x := hlower.mono fun _ hx => hc.trans hx
  have hwint : Integrable w μ := (integrable_const (C * c)).mono' hw (by
    filter_upwards [hw0, hupper] with x hx0 hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hx)
  have hprod : Integrable (fun x => w x * f x) μ :=
    (hf.const_mul (C * c)).mono' (hw.mul hf.aestronglyMeasurable) (by
      filter_upwards [hw0, hf0, hupper] with x hx0 hf0x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 hf0x)]
      exact mul_le_mul_of_nonneg_right hx hf0x)
  have hlowint : c * μ.real Set.univ ≤ ∫ x, w x ∂μ := by
    simpa only [integral_const, smul_eq_mul, mul_comm] using
      integral_mono_ae (integrable_const c) hwint hlower
  refine ⟨hprod, ?_⟩
  calc
    (∫ x, w x * f x ∂μ) ≤ ∫ x, (C * c) * f x ∂μ :=
      integral_mono_ae hprod (hf.const_mul _) (by
        filter_upwards [hf0, hupper] with x hx0 hx
        exact mul_le_mul_of_nonneg_right hx hx0)
    _ = (C * c) * ∫ x, f x ∂μ := integral_const_mul _ _
    _ ≤ (C * c) * μ.real Set.univ :=
      mul_le_mul_of_nonneg_left haverage (mul_nonneg hC hc)
    _ = C * (c * μ.real Set.univ) := mul_assoc _ _ _
    _ ≤ C * ∫ x, w x ∂μ := mul_le_mul_of_nonneg_left hlowint hC

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PredictionCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable step-supremum prediction factors

Inside one root cell, a finite measurable partition gives an explicit
step supremum. Logarithmic cell oscillation controls its normalization,
producing the actual nonnegative, measurable, average-one factor.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

theorem measurable_finite_profile (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) :
    Measurable (fun x => c (P x)) := by
  classical
  have heq : (fun x => c (P x)) =
      fun x => ∑ i, ({y | P y = i}.indicator (fun _ => c i)) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (P x)]
    · simp
    · intro i _ hi
      exact Set.indicator_of_notMem (show x ∉ {y | P y = i} from fun h => hi h.symm) _
    · simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hP i)

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

/-- The top weight is comparable on a reference-line cell no longer
than the top. The constant depends only on the fixed decay exponent. -/
theorem line_weight_comparable (T : SlopeBox) (origin transverse x : ℝ)
    {K D H : ℝ} (hK : 1 ≤ K) (hD : 0 ≤ D) (hH : H ≤ T.length)
    (hx : x ∈ Ico origin (origin + H)) :
    Real.exp (-D) * T.weight K D (origin, transverse + T.slope * origin) ≤
      T.weight K D (x, transverse + T.slope * x) ∧
    T.weight K D (x, transverse + T.slope * x) ≤
      Real.exp D * T.weight K D (origin, transverse + T.slope * origin) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hshift : lineShift T.slope (x - origin) (origin, transverse + T.slope * origin) =
      (x, transverse + T.slope * x) := by
    ext <;> dsimp only [lineShift] <;> ring
  have hdist : |x - origin| ≤ T.length := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2]
  have hlog := T.log_weight_same_slope hK hD hdist
    (origin, transverse + T.slope * origin)
  rw [hshift] at hlog
  obtain ⟨hl, hu⟩ := abs_le.mp hlog
  have hl' : -D + Real.log (T.weight K D (origin, transverse + T.slope * origin)) ≤
      Real.log (T.weight K D (x, transverse + T.slope * x)) := by linarith
  have hu' : Real.log (T.weight K D (x, transverse + T.slope * x)) ≤
      D + Real.log (T.weight K D (origin, transverse + T.slope * origin)) := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr hl'
    simpa only [Real.exp_add, Real.exp_log (T.weight_pos hK0 _ _)] using h
  · have h := Real.exp_le_exp.mpr hu'
    simpa only [Real.exp_add, Real.exp_log (T.weight_pos hK0 _ _)] using h

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SkippedLineAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging along selected generations of the actual line grid. Angular
blocks may have different numbers of steps; no uniform block length is needed. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.FiniteLineGrid

theorem rawIndex_add_div (g : FiniteLineGrid) (level steps : ℕ) (x : ℝ) :
    g.rawIndex (level+steps) x/g.branching^steps = g.rawIndex level x := by
  induction steps with
  | zero => simp
  | succ steps ih =>
    rw [pow_succ,mul_comm (g.branching^steps) g.branching,← Nat.div_div_eq_div_mul]
    rw [show level+(steps+1) = (level+steps)+1 by omega,g.rawIndex_parent,ih]

theorem index_ancestor (g : FiniteLineGrid) {coarse fine : ℕ}
    (hcf : coarse ≤ fine) (hf : fine ≤ g.depth) (x : ℝ) :
    g.index coarse x = g.ancestor (fine-coarse) (g.index fine x) := by
  apply Fin.ext
  change g.rawIndex (min coarse g.depth) x =
    g.rawIndex (min fine g.depth) x/g.branching^(fine-coarse)
  rw [Nat.min_eq_left (hcf.trans hf),Nat.min_eq_left hf]
  have h := g.rawIndex_add_div coarse (fine-coarse) x
  rw [Nat.add_sub_of_le hcf] at h
  exact h.symm

private theorem nonnegative_profile {α κ : Type} (P : α → κ) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hconstant : ∀ x y, P x = P y → f x = f y) :
    ∃ c : κ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ x, f x = c (P x) := by
  classical
  let c := fun i => if h : ∃ x, P x = i then f h.choose else 0
  refine ⟨c,?_,?_⟩
  · intro i
    dsimp only [c]
    split_ifs with h
    · exact hf _
    · exact le_rfl
  · intro x
    have h : ∃ y, P y = P x := ⟨x,rfl⟩
    dsimp only [c]
    rw [dite_eq_left h]
    exact hconstant x h.choose h.choose_spec.symm

/-- The conditional-average product estimate on any increasing list of
actual generations, including the initial short angular block. -/
theorem skipped_product_average (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (level : ℕ → ℕ) (N : ℕ) (hlevel : ∀ n ≤ N, level n ≤ g.depth)
    (hmono : ∀ n < N, level n ≤ level (n+1)) (Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < N, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < N, ∀ x y,
      g.index (level (n+1)) x = g.index (level (n+1)) y → Γ n x = Γ n y)
    (haverage : ∀ n < N, ∀ i : Fin (g.branching^g.depth),
      (∫ x in {x | g.index (level n) x = i}, Γ n x ∂μ) ≤
        μ.real {x | g.index (level n) x = i}) :
    Integrable (fun x => ∏ n ∈ Finset.range N, Γ n x) μ ∧
      (∫ x, ∏ n ∈ Finset.range N, Γ n x ∂μ) ≤ μ.real Set.univ := by
  classical
  have hprofile : ∀ n : ℕ, ∃ c : Fin (g.branching^g.depth) → ℝ,
      (∀ i, 0 ≤ c i) ∧
        ∀ x, (if n < N then Γ n x else 1) = c (g.index (level (n+1)) x) := by
    intro n
    apply nonnegative_profile
    · intro x
      split_ifs with hn
      · exact hΓ n hn x
      · exact zero_le_one
    · intro x y hxy
      split_ifs with hn
      · exact hconstant n hn x y hxy
      · rfl
  choose c hc heq using hprofile
  let P := fun n => g.index (level n)
  let R := fun n => g.ancestor (level (n+1)-level n)
  have hrefine : ∀ n < N, ∀ x, P n x = R n (P (n+1) x) := by
    intro n hn x
    exact g.index_ancestor (hmono n hn) (hlevel (n+1) (by omega)) x
  have hprod : (fun x => ∏ n ∈ Finset.range N, Γ n x) =
      fun x => ∏ n ∈ Finset.range N, c n (P (n+1) x) := by
    funext x
    apply Finset.prod_congr rfl
    intro n hn
    simpa only [ite_eq_left (Finset.mem_range.mp hn)] using heq n x
  rw [hprod]
  refine ⟨integrable_nested_product μ P R c N (g.measurable_index_fiber _) hrefine,?_⟩
  apply nested_average_product_le μ P R c N
    (fun n _ => g.measurable_index_fiber (level n)) hrefine (fun n _ => hc n)
  intro n hn i
  simpa only [P,← heq n,ite_eq_left hn] using haverage n hn i

/-- The same skipped-generation product can be integrated against the
original decaying top weight. -/
theorem top_weight_skipped_average (g : FiniteLineGrid) (T : SlopeBox) (y : ℝ)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (N : ℕ) (hlevel : ∀ n ≤ N, level n ≤ g.depth)
    (hmono : ∀ n < N, level n ≤ level (n+1)) (Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < N, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < N, ∀ x z,
      g.index (level (n+1)) x = g.index (level (n+1)) z → Γ n x = Γ n z)
    (haverage : ∀ n < N, ∀ i : Fin (g.branching^g.depth),
      (∫ x in {x | g.index (level n) x = i}, Γ n x ∂volume.restrict g.root) ≤
        (volume.restrict g.root).real {x | g.index (level n) x = i}) :
    Integrable (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ n ∈ Finset.range N, Γ n x) (volume.restrict g.root) ∧
      (∫ x in g.root, T.weight K D (x,y+T.slope*x)*∏ n ∈ Finset.range N, Γ n x) ≤
        Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  let : IsFiniteMeasure (volume.restrict g.root) := isFiniteMeasure_restrict.mpr (by
    simp only [root,Real.volume_Ico,ENNReal.ofReal_ne_top,ne_eq,not_false_eq_true])
  let c := Real.exp (-D)*T.weight K D (g.origin,y+T.slope*g.origin)
  have hc : 0 ≤ c := (mul_pos (Real.exp_pos _) (T.weight_pos (by linarith) _ _)).le
  have hcompare : ∀ᵐ x ∂volume.restrict g.root,
      c ≤ T.weight K D (x,y+T.slope*x) ∧
      T.weight K D (x,y+T.slope*x) ≤ Real.exp (2*D)*c := by
    filter_upwards [ae_restrict_mem (show MeasurableSet g.root from measurableSet_Ico)] with x hx
    have h := T.line_weight_comparable g.origin y x hK hD hwidth hx
    refine ⟨h.1,h.2.trans_eq ?_⟩
    dsimp only [c]
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  obtain ⟨hint,havg⟩ := g.skipped_product_average (volume.restrict g.root) level N hlevel hmono
    Γ hΓ hconstant haverage
  exact weighted_average_le (volume.restrict g.root)
    (fun x => T.weight K D (x,y+T.slope*x)) _ hc (Real.exp_pos _).le
    ((T.continuous_weight (by linarith) D).comp (by fun_prop)).aestronglyMeasurable
    hint (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun n hn =>
      hΓ n (Finset.mem_range.mp hn) x)
    (hcompare.mono fun _ h => h.1) (hcompare.mono fun _ h => h.2) havg

end LipschitzHilbert.FiniteLineGrid

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

end LipschitzHilbert

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

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathDropMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path drop in §9 is comparable throughout the reference cell.
The complement may be empty: relative motion then fixes its zero mass. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem complementary_mass_drop_motion {A B A' B' q : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hq : 0 ≤ q) (hqsmall : q ≤ 1/8)
    (hAmove : |A'-A| ≤ q*A) (hBmove : |B'-B| ≤ q*B) :
    let u := 1-A/(A+B)
    let u' := 1-A'/(A'+B')
    0 ≤ u ∧ |u'-u| ≤ 4*q*u ∧ u/2 ≤ u' ∧ u' ≤ 2*u := by
  dsimp only
  have hden : 0 < A+B := by linarith
  have hr1 : A/(A+B) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hu : 0 ≤ 1-A/(A+B) := by linarith
  obtain ⟨_,_,hm⟩ := complementary_mass_fraction_motion hA hB hq
    (show q ≤ 1/2 by linarith) hAmove hBmove
  have herr : |(1-A'/(A'+B'))-(1-A/(A+B))| ≤ 4*q*(1-A/(A+B)) := by
    calc
      _ = |A'/(A'+B')-A/(A+B)| := by
        rw [show (1-A'/(A'+B'))-(1-A/(A+B)) = -(A'/(A'+B')-A/(A+B)) by ring,abs_neg]
      _ ≤ 4*q*(A/(A+B))*(1-A/(A+B)) := hm
      _ ≤ 4*q*1*(1-A/(A+B)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr1 (by positivity)) hu
      _ = _ := by ring
  have hsmall : 4*q*(1-A/(A+B)) ≤ (1-A/(A+B))/2 := by
    have hm := mul_le_mul_of_nonneg_right hqsmall hu
    nlinarith
  have habs := abs_le.mp (herr.trans hsmall)
  refine ⟨hu,herr,?_,?_⟩ <;> linarith

namespace AngularGrid

/-- Actual child and complementary top sums give the source's
`pred:drop-comparability`, retaining the exact drop in the error. -/
theorem source_path_drop_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (parentSet childSet : Finset ι) (hsub : childSet ⊆ parentSet) (hne : childSet.Nonempty)
    (hparent : parentSet ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (hsmall : Real.exp ((5*D/K)/Real.sqrt (g.branching:ℝ))*
      ((5*D/K)/Real.sqrt (g.branching:ℝ)) ≤ 1/8) :
    let mass := fun A x => ∑ t ∈ A, (T t).weight K D x
    let u := fun x => 1-mass childSet x/mass parentSet x
    let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
    let q := Real.exp δ*δ
    0 ≤ u z ∧ |u (SlopeBox.lineShift sR b z)-u z| ≤ 4*q*u z ∧
      u z/2 ≤ u (SlopeBox.lineShift sR b z) ∧ u (SlopeBox.lineShift sR b z) ≤ 2*u z := by
  classical
  dsimp only
  let mass := fun (A : Finset ι) x => ∑ t ∈ A, (T t).weight K D x
  let z' := SlopeBox.lineShift sR b z
  let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
  let q := Real.exp δ*δ
  have hpos : 0 < mass childSet z :=
    Finset.sum_pos (fun t _ => (T t).weight_pos hK D z) hne
  have hcomp : 0 ≤ mass (parentSet\childSet) z :=
    Finset.sum_nonneg fun t _ => (T t).weight_pos hK D z |>.le
  have hsplit (x : ℝ × ℝ) : mass parentSet x = mass childSet x+mass (parentSet\childSet) x := by
    have hm := Finset.sum_sdiff (f := fun t => (T t).weight K D x) hsub
    dsimp [mass]
    linarith
  have hmove (A : Finset ι) (hA : A ⊆ parentSet) :
      |mass A z'-mass A z| ≤ q*mass A z :=
    g.source_submass_relative_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A (hA.trans hparent) b hb z
  have hresult := complementary_mass_drop_motion hpos hcomp
    (show 0 ≤ q by dsimp [q,δ]; positivity) hsmall
    (hmove childSet hsub) (hmove (parentSet\childSet) Finset.sdiff_subset)
  simpa only [← hsplit z,← hsplit z'] using hresult

end AngularGrid
end LipschitzHilbert

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

theorem shiftedPathMass_nonneg {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (σ : Fin K) (top : ι) (x : X) (j : ℕ) :
    0 ≤ g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  unfold shiftedPathMass
  split_ifs
  · exact Finset.sum_nonneg fun t _ => hw t x
  · exact le_rfl

theorem shiftedPathMass_pos {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 < weight t x)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j)) :
    0 < g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  rw [shiftedPathMass,ite_eq_left he]
  exact g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x

theorem shiftedPathMass_le_total {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (σ : Fin K) (top : ι) (x : X) (j : ℕ) :
    g.shiftedPathMass tops slope precision cutoff weight σ top x j ≤
      ∑ t ∈ tops, weight t x := by
  unfold shiftedPathMass
  split_ifs
  · exact g.mass_le_total tops slope precision cutoff weight hw _ _ x
  · exact Finset.sum_nonneg fun t _ => hw t x

theorem shiftedPathMass_antitone {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hK : 0 < K)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) :
    Antitone (g.shiftedPathMass tops slope precision cutoff weight σ top x) := by
  intro j k hjk
  have hlevel := (ShiftedBlocks.endpoint_strictMono hK σ).monotone hjk
  by_cases hk : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ k)
  · have hj := g.eligible_of_le (hp top htop) hlevel hk
    rw [shiftedPathMass,ite_eq_left hk,shiftedPathMass,ite_eq_left hj]
    exact g.path_mass_antitone tops slope precision cutoff weight hp hw top x hlevel
  · rw [shiftedPathMass,ite_eq_right hk]
    exact g.shiftedPathMass_nonneg tops slope precision cutoff weight hw σ top x j

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

/-- Exact shifted source blocks satisfy the drop comparison used in the
stopped error budget. A final block with no eligible path child has drop
one at both endpoints and needs no fictitious child top. -/
theorem source_shifted_path_drop_motion {ι : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ j))
    (h : ℕ) (hbase : h ≤ ShiftedBlocks.endpoint σ j)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (hblock : g.width h ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (b : ℝ) (hb : |b| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (z : ℝ × ℝ)
    (hsmall : Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ)) ≤ 1/8) :
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight Kw D x) σ top x
    let u := fun x => pathDrop (n x) j
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    let z' := SlopeBox.lineShift sR b z
    0 ≤ u z ∧ |u z'-u z| ≤ 4*(Real.exp δ*δ)*u z ∧
      u z/2 ≤ u z' ∧ u z' ≤ 2*u z := by
  classical
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let n := fun x => g.shiftedPathMass tops slope precision cutoff weight σ top x
  let lo := ShiftedBlocks.endpoint σ j
  let hi := ShiftedBlocks.endpoint σ (j+1)
  let u := fun x => pathDrop (n x) j
  let z' := SlopeBox.lineShift sR b z
  let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hwpos (t : ι) (x : ℝ × ℝ) : 0 < weight t x := (T t).weight_pos hKw D x
  by_cases hnext : g.eligible cutoff (precision top) hi
  · let parent := g.cellTops tops slope precision cutoff lo (g.index lo (slope top))
    let child := g.cellTops tops slope precision cutoff hi (g.index hi (slope top))
    have hlevel : lo ≤ hi := (ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)
    have hsub : child ⊆ parent := g.cellTops_subset_ancestor tops slope precision cutoff hp hlevel _
    have hne : child.Nonempty :=
      ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,hnext⟩⟩
    have hdrop (x : ℝ × ℝ) : u x =
        1-(∑ t ∈ child, weight t x)/(∑ t ∈ parent, weight t x) := by
      have hpos := g.path_mass_pos tops slope precision cutoff weight hwpos lo top htop he x
      have he0 : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j) := he
      have he1 : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1)) := hnext
      change (n x j-n x (j+1))/n x j = _
      simp only [n,shiftedPathMass,he0,he1,ite_true, if_true]
      rw [sub_div,div_self hpos.ne']
      rfl
    have hresult := g.source_path_drop_motion tops T w B Kw D hw hB hKw hD hwidth
      0 h lo hbase 0 (by norm_num) (g.width_pos h).le (slope top) sR hs
      (g.width hi) (g.width_pos hi) hblock parent child hsub hne
      (g.parent_subset_boundary tops slope precision cutoff 0 lo 0 (slope top)) b hb z hsmall
    change 0 ≤ u z ∧ |u z'-u z| ≤ 4*(Real.exp δ*δ)*u z ∧ u z/2 ≤ u z' ∧ u z' ≤ 2*u z
    simpa only [hdrop] using hresult
  · have hterminal (x : ℝ × ℝ) : u x = 1 :=
      g.shiftedPathDrop_terminal tops slope precision cutoff weight hwpos σ top htop x j he hnext
    change 0 ≤ u z ∧ |u z'-u z| ≤ 4*(Real.exp δ*δ)*u z ∧ u z/2 ≤ u z' ∧ u z' ≤ 2*u z
    rw [hterminal z,hterminal z']
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    have hq : 0 ≤ Real.exp δ*δ := mul_nonneg (Real.exp_pos _).le hδ
    refine ⟨by norm_num,?_,by norm_num,by norm_num⟩
    simpa only [sub_self,abs_zero,mul_one] using
      mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hq

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

theorem sourcePredictionValue_pos {ι κ : Type} [Fintype ι] [Fintype κ]
    (p μ n : ℝ) (hn : 0 < n) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) :
    0 < sourcePredictionValue p μ n c A lam := by
  unfold sourcePredictionValue
  apply energyRatio_pos
  have hs : 0 ≤ ∑ i, (c i/n)*‖(c i)^(μ-1) • A i‖^p :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (div_nonneg (hc i) hn.le)
      (Real.rpow_nonneg (norm_nonneg _) _))
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual finite source packet amplitudes. The
angular cells and packet stopping levels are fixed; only the spatial
weights and packet values vary. Vanishing masses are allowed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
namespace AngularGrid

variable {ι σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem measurable_mass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (level : ℕ) (cell : ℤ) :
    Measurable (g.mass tops slope precision cutoff weight level cell) :=
  Finset.measurable_sum _ (fun t _ => hw t)

theorem measurable_boundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (base level : ℕ) (gap s : ℝ) :
    Measurable (g.boundaryMass tops slope precision cutoff weight base level gap s) :=
  Finset.measurable_sum _ (fun t _ => hw t)

theorem measurable_sourceBoundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (level : ℕ) (cell : ℤ) :
    Measurable (g.sourceBoundaryMass tops slope precision cutoff weight K gap level cell) :=
  g.measurable_boundaryMass tops slope precision cutoff weight hw _ _ _ _

theorem measurable_sourceTransition (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (phase : ℕ → ℂ) (level : ℕ) (cell : ℤ) :
    Measurable (fun x =>
      g.sourceTransition tops slope precision cutoff weight K gap phase x level cell) := by
  unfold sourceTransition analyticTransition
  exact (measurable_const.mul (Complex.measurable_ofReal.comp
    ((g.measurable_mass tops slope precision cutoff weight hw (level+1) cell).div
      (g.measurable_sourceBoundaryMass tops slope precision cutoff weight hw K gap level cell)).log)).cexp

theorem measurable_packetPathProduct (g : AngularGrid) (transition : X → ℕ → ℤ → ℂ)
    (ht : ∀ level cell, Measurable (fun x => transition x level cell))
    (lower upper : ℕ) (slope : ℝ) :
    Measurable (fun x => g.packetPathProduct (transition x) lower upper slope) :=
  Finset.measurable_prod _ (fun j _ => ht j _)

theorem measurable_sourcePacketBase (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (assigned : σ → ι) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (a : ℝ) (s : σ) :
    Measurable (fun x => g.sourcePacketBase tops slope precision cutoff weight assigned stop
      (value x) a x s) := by
  unfold sourcePacketBase
  exact (Complex.measurable_ofReal.comp
    ((g.measurable_mass tops slope precision cutoff weight hw _ _).pow_const (-a))).smul (hv s)

theorem measurable_sourcePacketAmplitude (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (phase : ℕ → ℂ)
    (a : ℝ) (level : ℕ) (cell : ℤ) :
    Measurable (fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x level cell) := by
  unfold sourcePacketAmplitude packetAmplitude
  apply Finset.measurable_sum
  intro s _
  exact (g.measurable_packetPathProduct _
    (g.measurable_sourceTransition tops slope precision cutoff weight hw K gap phase) _ _ _).smul
    (g.measurable_sourcePacketBase tops slope precision cutoff weight hw assigned stop value hv a s)

end AngularGrid

theorem measurable_sourcePredictionValue {X : Type*} {ι κ : Type} [MeasurableSpace X]
    [Fintype ι] [Fintype κ] (p μ : ℝ) (n : X → ℝ) (c : X → ι → ℝ)
    (A : X → ι → EuclideanSpace ℂ κ) (lam : X → ι → ℂ)
    (hn : Measurable n) (hc : ∀ i, Measurable (fun x => c x i))
    (hA : ∀ i, Measurable (fun x => A x i)) (hlam : ∀ i, Measurable (fun x => lam x i)) :
    Measurable (fun x => sourcePredictionValue p μ (n x) (c x) (A x) (lam x)) := by
  unfold sourcePredictionValue energyRatio
  fun_prop

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMassStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite mass stopping index. A terminal ineligible top has
zero path mass, so the source cutoff is attained without a positive lower
bound on any individual top weight. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem firstMassStop_spec (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) :
    firstMassStop n count M ≤ count ∧ n (firstMassStop n count M) ≤ M ∧
      ∀ j < firstMassStop n count M, M < n j := by
  have hex : ∃ j : ℕ, j ≤ count ∧ n j ≤ M := ⟨count,le_rfl,hlast⟩
  rw [firstMassStop,dite_eq_left hex]
  refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
  intro j hj
  have hn := Nat.find_min hex hj
  have hcount := (Nat.le_of_lt hj).trans (Nat.find_spec hex).1
  exact lt_of_not_ge fun h => hn ⟨hcount,h⟩

theorem firstMassStop_after (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) {j : ℕ}
    (hj : firstMassStop n count M ≤ j) : n j ≤ M :=
  (hanti hj).trans (firstMassStop_spec n count M hlast).2.1

theorem firstMassStop_active_iff (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) (j : ℕ) :
    j < firstMassStop n count M ↔ M < n j := by
  constructor
  · exact (firstMassStop_spec n count M hlast).2.2 j
  · intro hj
    by_contra hn
    exact (not_lt_of_ge (firstMassStop_after n count M hlast hanti (Nat.le_of_not_gt hn))) hj

namespace AngularGrid

theorem shiftedPathMass_terminal_zero {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (σ : Fin K) (top : ι) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ count))
    (x : X) : g.shiftedPathMass tops slope precision cutoff weight σ top x count = 0 := by
  rw [shiftedPathMass,ite_eq_right hterminal]

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePathPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual-free predictor on the actual packet path. Its child
family and coefficients are the same ones used by the physical estimate. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

theorem sourceBlockPrediction_measurable (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s))
    (phase : ℕ → ℂ) (a p μ : ℝ) (lower upper : ℕ) (parent : ℤ) :
    Measurable (g.sourceBlockPrediction tops slope precision cutoff weight K gap packets
      assigned stop value phase a p μ lower upper parent) := by
  apply measurable_sourcePredictionValue
  · exact g.measurable_mass tops slope precision cutoff weight hw lower parent
  · intro i
    exact g.measurable_mass tops slope precision cutoff weight hw upper i.val
  · intro i
    exact g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hw K gap
      packets assigned stop value hv phase a upper i.val
  · intro i
    exact g.measurable_packetPathProduct _
      (g.measurable_sourceTransition tops slope precision cutoff weight hw K gap phase) _ _ _

theorem sourceShiftedPathPrediction_measurable {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s))
    (phase : ℕ → ℂ) (a p μ : ℝ) (tag : Fin Kb) (top : τ) (j : ℕ) :
    Measurable (fun x => g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
      packets assigned stop value phase a p μ tag top x j) :=
  g.sourceBlockPrediction_measurable tops slope precision cutoff weight hw K gap packets
    assigned stop value hv phase a p μ _ _ _

omit [MeasurableSpace X] in
theorem sourceShiftedPathPrediction_pos {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 < weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a p μ : ℝ) (tag : Fin Kb) (top : τ)
    (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    0 < g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets
      assigned stop value phase a p μ tag top x j := by
  unfold sourceShiftedPathPrediction sourceBlockPrediction
  apply sourcePredictionValue_pos
  · exact g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x
  · intro i
    exact g.mass_nonnegative tops slope precision cutoff weight (fun t x => (hw t x).le)
      _ i.val x

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineWindow
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual coarse line cell carries a local grid with exactly the same
fine partitions as the global line grid. This identifies the local
prediction factors before they are patched over coarse cells. -/

noncomputable section
open Set
namespace LipschitzHilbert.FiniteLineGrid

theorem lineWindow_root (g : FiniteLineGrid) (coarse i depth : ℕ) :
    (g.lineWindow coarse i depth).root = g.cell coarse i := by
  change Ico (g.origin+g.meshWidth coarse*i)
      ((g.origin+g.meshWidth coarse*i)+g.meshWidth coarse) =
    Ico (g.origin+g.meshWidth coarse*i) (g.origin+g.meshWidth coarse*((i:ℝ)+1))
  congr 1
  ring

theorem lineWindow_meshWidth (g : FiniteLineGrid) (coarse i depth k : ℕ) :
    (g.lineWindow coarse i depth).meshWidth k = g.meshWidth (coarse+k) := by
  simp only [meshWidth,lineWindow,pow_add,div_div]

/-- The local normalized coordinate differs from the global one by an
integer number of fine cells, with the same integer branching power. -/
theorem lineWindow_coordinate (g : FiniteLineGrid) (coarse i depth k : ℕ) (x : ℝ) :
    ((x-(g.lineWindow coarse i depth).origin)/(g.lineWindow coarse i depth).width)*
        ((g.lineWindow coarse i depth).branching:ℝ)^k+
      ((i*g.branching^k:ℕ):ℝ) =
        ((x-g.origin)/g.width)*(g.branching:ℝ)^(coarse+k) := by
  have hG : (g.branching:ℝ) ≠ 0 := by exact_mod_cast g.branching_pos.ne'
  simp only [lineWindow,meshWidth,Nat.cast_mul,Nat.cast_pow,pow_add]
  field_simp [g.width_pos.ne',hG]
  ring

theorem lineWindow_rawIndex (g : FiniteLineGrid) (coarse i depth k : ℕ)
    (hi : i < g.branching^coarse) {x : ℝ} (hx : x ∈ g.cell coarse i) :
    (g.lineWindow coarse i depth).rawIndex k x+i*g.branching^k =
      g.rawIndex (coarse+k) x := by
  classical
  have hlocal : x ∈ (g.lineWindow coarse i depth).root := by
    rwa [g.lineWindow_root]
  have hglobal : x ∈ g.root := g.cell_subset_root coarse hi hx
  have hcoord : 0 ≤ ((x-(g.lineWindow coarse i depth).origin)/
      (g.lineWindow coarse i depth).width)*((g.lineWindow coarse i depth).branching:ℝ)^k := by
    exact mul_nonneg
      (div_nonneg (sub_nonneg.mpr hlocal.1) (g.lineWindow coarse i depth).width_pos.le)
      (pow_nonneg (Nat.cast_nonneg _) _)
  rw [rawIndex,ite_eq_left hlocal,rawIndex,ite_eq_left hglobal,
    ← Nat.floor_add_natCast hcoord,g.lineWindow_coordinate]

/-- On the coarse cell, equality of the actual global fine indices is
exactly strong enough to preserve a local prediction's constancy. -/
theorem lineWindow_index_of_global (g : FiniteLineGrid) (coarse i depth k : ℕ)
    (hi : i < g.branching^coarse) (hk : k ≤ depth) (hglobal : coarse+k ≤ g.depth)
    {x y : ℝ} (hx : x ∈ g.cell coarse i) (hy : y ∈ g.cell coarse i)
    (hxy : g.index (coarse+k) x = g.index (coarse+k) y) :
    (g.lineWindow coarse i depth).index k x = (g.lineWindow coarse i depth).index k y := by
  have hv := congrArg Fin.val hxy
  change g.rawIndex (min (coarse+k) g.depth) x =
    g.rawIndex (min (coarse+k) g.depth) y at hv
  rw [Nat.min_eq_left hglobal] at hv
  have hix := g.lineWindow_rawIndex coarse i depth k hi hx
  have hiy := g.lineWindow_rawIndex coarse i depth k hi hy
  apply Fin.ext
  change (g.lineWindow coarse i depth).rawIndex (min k depth) x =
    (g.lineWindow coarse i depth).rawIndex (min k depth) y
  rw [Nat.min_eq_left hk]
  omega

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWindowAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the constructed probability-normalized source factors to
Lebesgue cell averages on the exact local line windows. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.FiniteLineGrid

private theorem window_probability (g : FiniteLineGrid) :
    intervalProbability g.origin (g.origin+g.width) =
      (ENNReal.ofReal g.width)⁻¹ • volume.restrict g.root := by
  unfold intervalProbability root
  rw [show g.origin+g.width-g.origin = g.width by ring,
    restrict_Ico_eq_restrict_Icc]

theorem window_integrable_iff (g : FiniteLineGrid) (F : ℝ → ℝ) :
    Integrable F (intervalProbability g.origin (g.origin+g.width)) ↔
      IntegrableOn F g.root volume := by
  rw [window_probability]
  exact integrable_smul_measure (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr g.width_pos))

theorem window_probability_integral (g : FiniteLineGrid) (F : ℝ → ℝ) :
    (∫ x, F x ∂intervalProbability g.origin (g.origin+g.width)) =
      (g.width)⁻¹*(∫ x in g.root, F x) := by
  rw [window_probability,integral_smul_measure,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal g.width_pos.le,smul_eq_mul]

/-- The constructed normalized factor has the required ordinary cell
average, with the half-open source window retained exactly. -/
theorem window_average_le (g : FiniteLineGrid) (F : ℝ → ℝ)
    (hint : Integrable F (intervalProbability g.origin (g.origin+g.width)))
    (havg : (∫ x, F x ∂intervalProbability g.origin (g.origin+g.width)) ≤ 1) :
    IntegrableOn F g.root volume ∧
      (∫ x in g.root, F x) ≤ volume.real g.root := by
  refine ⟨(g.window_integrable_iff F).mp hint,?_⟩
  have hwidth : volume.real g.root = g.width := by
    rw [measureReal_def,root,Real.volume_Ico]
    rw [show g.origin+g.width-g.origin = g.width by ring,
      ENNReal.toReal_ofReal g.width_pos.le]
  rw [hwidth]
  calc
    _ = g.width*(∫ x, F x ∂intervalProbability g.origin (g.origin+g.width)) := by
      rw [g.window_probability_integral]
      field_simp [ne_of_gt g.width_pos]
    _ ≤ g.width*1 := mul_le_mul_of_nonneg_left havg g.width_pos.le
    _ = _ := mul_one _

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_LocalSkippedPrediction
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Patch local source predictions by the actual global fine-cell profile.
Points outside the root share the first fiber's value, so global constancy
is preserved without any extra measurable-choice requirement. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.FiniteLineGrid

private theorem nonnegative_profile_on (P : ℝ → ℕ) (s : Set ℝ) (F : ℝ → ℝ)
    (hF : ∀ x ∈ s, 0 ≤ F x)
    (hconstant : ∀ x ∈ s, ∀ y ∈ s, P x = P y → F x = F y) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ x ∈ s, F x = c (P x) := by
  classical
  let c := fun i => if h : ∃ x ∈ s, P x = i then F h.choose else 0
  refine ⟨c,?_,?_⟩
  · intro i
    dsimp only [c]
    split_ifs with h
    · exact hF _ h.choose_spec.1
    · exact le_rfl
  · intro x hx
    have h : ∃ y ∈ s, P y = P x := ⟨x,hx,rfl⟩
    dsimp only [c]
    rw [dite_eq_left h]
    exact hconstant x hx h.choose h.choose_spec.1 h.choose_spec.2.symm

/-- Local window factors assemble into one globally fine-cell-constant
nonnegative function, with the correct average on every coarse cell. -/
theorem exists_patched_window_factor (g : FiniteLineGrid) (coarse fine : ℕ)
    (hcf : coarse ≤ fine) (hf : fine ≤ g.depth)
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ i < g.branching^coarse, ∀ x ∈ g.cell coarse i, 0 ≤ F i x)
    (hconstant : ∀ i < g.branching^coarse, ∀ x ∈ g.cell coarse i,
      ∀ y ∈ g.cell coarse i, g.index fine x = g.index fine y → F i x = F i y)
    (haverage : ∀ i < g.branching^coarse,
      (∫ x in g.cell coarse i, F i x) ≤ volume.real (g.cell coarse i)) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x y, g.index fine x = g.index fine y → Γ x = Γ y) ∧
      (∀ x ∈ g.root, Γ x = F (g.index coarse x).val x) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index coarse x = i}, Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index coarse x = i}) := by
  classical
  let f := fun x => F (g.index coarse x).val x
  have hidx (x : ℝ) : (g.index coarse x).val < g.branching^coarse := by
    change g.rawIndex (min coarse g.depth) x < g.branching^coarse
    rw [Nat.min_eq_left (hcf.trans hf)]
    have h := rawIndex_lt (g := {g with depth := coarse}) (le_refl coarse) x
    exact h
  have hmem (x : ℝ) (hx : x ∈ g.root) : x ∈ g.cell coarse (g.index coarse x).val :=
    (g.index_eq_iff_mem_cell (hcf.trans hf) hx _).mp rfl
  obtain ⟨c,hc,heq⟩ := nonnegative_profile_on (fun x => (g.index fine x).val) g.root f
    (fun x hx => hF _ (hidx x) x (hmem x hx)) (by
      intro x hx y hy hxy
      have hxy' : g.index fine x = g.index fine y := Fin.ext hxy
      have hcoarse : g.index coarse x = g.index coarse y := by
        rw [g.index_ancestor hcf hf x,g.index_ancestor hcf hf y,hxy']
      dsimp only [f]
      rw [← hcoarse]
      exact hconstant _ (hidx x) x (hmem x hx) y (by simpa only [hcoarse] using hmem y hy) hxy')
  let Γ := fun x => c (g.index fine x).val
  refine ⟨Γ,?_,fun x => hc _,?_,?_,?_⟩
  · exact measurable_finite_profile (g.index fine) (g.measurable_index_fiber fine) (fun i => c i.val)
  · intro x y hxy
    dsimp only [Γ]
    rw [hxy]
  · intro x hx
    exact (heq x hx).symm
  · intro i
    have hset : {x | g.index coarse x = i} ∩ g.root =
        {x ∈ g.root | (g.index coarse x).val = i.val} := by
      ext x
      simp only [mem_inter_iff,mem_ofPred_eq,Fin.ext_iff]
      tauto
    rw [measureReal_restrict_apply (g.measurable_index_fiber coarse i),
      Measure.restrict_restrict (g.measurable_index_fiber coarse i),hset]
    by_cases hi : i.val < g.branching^coarse
    · rw [g.index_fiber_inter_root (hcf.trans hf) hi]
      have heq' : (∫ x in g.cell coarse i.val, Γ x) =
          ∫ x in g.cell coarse i.val, F i.val x := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        have hroot := g.cell_subset_root coarse hi hx
        have hix := (g.index_eq_iff_mem_cell (hcf.trans hf) hroot i.val).mpr hx
        exact (heq x hroot).symm.trans (by dsimp only [f]; rw [hix])
      rw [heq']
      exact haverage i.val hi
    · have hempty : {x ∈ g.root | (g.index coarse x).val = i.val} = ∅ := by
        ext x
        simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false,not_and]
        intro _ hix
        exact hi (hix ▸ hidx x)
      rw [hempty]
      simp

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStoppedError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The marked prediction errors have a uniform total logarithmic budget
along an active path. The source cutoff is exactly `M = L^A_M`; the last
active index is included even when its drop crosses the cutoff. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
open PhaseCombinatorics

/-- Transfer from the fixed snapshot drop to the moving point, using the
factor two furnished by actual source path-drop comparability. -/
theorem source_error_of_drop_comparability {error ρ snapshotDrop pointDrop : ℝ}
    (hρ : 0 ≤ ρ) (hdrop : snapshotDrop/2 ≤ pointDrop)
    (herror : error ≤ ρ*snapshotDrop) : error ≤ (2*ρ)*pointDrop := by
  have h := mul_le_mul_of_nonneg_left hdrop hρ
  nlinarith

theorem stopped_source_error_transfer (n e snapshot : ℕ → ℝ)
    (count stop : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdrop : ∀ j < stop, snapshot j/2 ≤ pathDrop n j)
    (he : ∀ j < count, e j ≤ if j < stop then ρ*snapshot j else 0) :
    ∀ j < count, e j ≤ if j < stop then (2*ρ)*pathDrop n j else 0 := by
  intro j hj
  by_cases hjs : j < stop
  · rw [ite_eq_left hjs]
    exact source_error_of_drop_comparability hρ (hdrop j hjs)
      (by simpa only [ite_eq_left hjs] using he j hj)
  · simpa only [ite_eq_right hjs] using he j hj

theorem eventually_source_drop_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      2*SourceParameters.step L^(-(1/32:ℝ))*(1+(C+4)*L) ≤ 1 := by
  have hsub := eventually_source_subpower_amplitude 2 (1/64) (by norm_num)
  filter_upwards [hsub,eventually_ge_atTop (max 1 (2*(C+5)))] with L hsub hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hCL : 2*(C+5) ≤ L := (le_max_right _ _).trans hlarge
  have hb := hsub 1 1 (by norm_num) (by norm_num) (by simp; linarith)
  norm_num only [Real.one_rpow,Real.rpow_ofNat] at hb
  have hpoly : 2*(1+(C+4)*L) ≤ L^2 := by nlinarith
  have hpower : L^2 ≤ SourceParameters.step L^(1/64:ℝ) := by nlinarith [sq_nonneg L]
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  calc
    _ = (2*(1+(C+4)*L))*SourceParameters.step L^(-(1/32:ℝ)) := by ring
    _ ≤ SourceParameters.step L^(1/64:ℝ)*SourceParameters.step L^(-(1/32:ℝ)) :=
      mul_le_mul_of_nonneg_right (hpoly.trans hpower)
        (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
    _ = SourceParameters.step L^(-(1/64:ℝ)) := by
      rw [← Real.rpow_add (SourceParameters.step_pos L)]
      norm_num
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)

/-- The original mass bound `L^C N^2` gives the source active-drop estimate.
No lower bound on the initial mass is required when there are no active
indices. The terminal mass is allowed to be zero. -/
theorem eventually_source_stopped_error (C A_M : ℝ) (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n e : ℕ → ℝ) (count stop : ℕ), stop ≤ count →
      ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L → n 0 ≤ L^C*N^2 →
      (∀ j < stop, L^A_M < n j) → 0 ≤ n stop →
      (∀ j < count, e j ≤ if j < stop then
        (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop n j else 0) →
      (∑ j ∈ Finset.range count, e j) ≤ 1 := by
  filter_upwards [eventually_source_drop_budget C hC,eventually_ge_atTop (1:ℝ)]
    with L hbudget hL
  intro n e count stop hstop N hN hlogN hmass hactive hlast he
  by_cases hs : stop = 0
  · have hz : (∑ j ∈ Finset.range count, e j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      simpa only [hs,Nat.not_lt_zero,ite_false, if_false] using he j (Finset.mem_range.mp hj)
    exact hz.trans zero_le_one
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hM : 1 ≤ L^A_M := Real.one_le_rpow hL hAM
  have hM0 : 0 < L^A_M := zero_lt_one.trans_le hM
  have hn : 0 < n 0 := hM0.trans (hactive 0 (Nat.pos_of_ne_zero hs))
  have hratio : 0 < n 0/L^A_M := div_pos hn hM0
  have hratioBound : n 0/L^A_M ≤ L^C*N^2 := (div_le_self hn.le hM).trans hmass
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hL0
    linarith
  have hlog : Real.log (n 0/L^A_M) ≤ (C+4)*L := by
    calc
      _ ≤ Real.log (L^C*N^2) := Real.log_le_log hratio hratioBound
      _ = C*Real.log L+2*Real.log N := by
        rw [Real.log_mul (Real.rpow_pos_of_pos hL0 C).ne' (pow_pos hN 2).ne',
          Real.log_rpow hL0,Real.log_pow]
        ring
      _ ≤ C*L+2*(2*L) := add_le_add (mul_le_mul_of_nonneg_left hlogL hC)
        (mul_le_mul_of_nonneg_left hlogN (by norm_num))
      _ = (C+4)*L := by ring
  have hmaxlog : max 0 (Real.log (n 0/L^A_M)) ≤ (C+4)*L :=
    max_le (mul_nonneg (by linarith) hL0.le) hlog
  exact (stopped_error_budget n e count stop hstop hM0
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (SourceParameters.step_pos L).le _))
    hactive hlast hmaxlog he).trans hbudget

/-- Snapshot errors from the marked-cell comparison have total cost at most
one after the actual factor-two drop comparison. -/
theorem eventually_source_snapshot_stopped_error (C A_M : ℝ)
    (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n e snapshot : ℕ → ℝ) (count stop : ℕ), stop ≤ count →
      ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L → n 0 ≤ L^C*N^2 →
      (∀ j < stop, L^A_M < n j) → 0 ≤ n stop →
      (∀ j < stop, snapshot j/2 ≤ pathDrop n j) →
      (∀ j < count, e j ≤ if j < stop then
        SourceParameters.step L^(-(1/32:ℝ))*snapshot j else 0) →
      (∑ j ∈ Finset.range count, e j) ≤ 1 := by
  filter_upwards [eventually_source_stopped_error C A_M hC hAM] with L hL
  intro n e snapshot count stop hstop N hN hlogN hmass hactive hlast hdrop he
  exact hL n e count stop hstop N hN hlogN hmass hactive hlast
    (stopped_source_error_transfer n e snapshot count stop
      (Real.rpow_nonneg (SourceParameters.step_pos L).le _) hdrop he)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceMarkedPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marking belongs to an entire coarse line cell. On every unmarked
cell the prediction factor is exactly one. In particular a cell containing
an inactive point cannot contribute a marked factor. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace LipschitzHilbert.FiniteLineGrid
attribute [local instance] Classical.propDecidable

theorem measurableSet_marked (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop) :
    MeasurableSet {x | marked (g.index coarse x).val} := by
  have hm := measurable_finite_profile (g.index coarse) (g.measurable_index_fiber coarse)
    (fun i => if marked i.val then (1:ℝ) else 0)
  convert hm (measurableSet_singleton (1:ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

theorem measurable_markedValue (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop)
    (value : ℝ → ℝ) (hvalue : Measurable value) : Measurable (g.markedValue coarse marked value) :=
  Measurable.ite (g.measurableSet_marked coarse marked) hvalue measurable_const

/-- Only marked cells require an analytic predictor. The other cells
have factor one, retaining exact normalization and fine-cell constancy. -/
theorem exists_marked_source_prediction (g : FiniteLineGrid) (coarse fine : ℕ)
    (hcf : coarse ≤ fine) (hf : fine ≤ g.depth)
    (marked : ℕ → Prop) (good : Set ℝ) (beta error : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hF : ∀ i < g.branching^coarse, marked i → ∀ x, 0 ≤ F i x)
    (hint : ∀ i < g.branching^coarse, marked i →
      Integrable (F i) (intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
        ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)))
    (haverage : ∀ i < g.branching^coarse, marked i →
      (∫ x, F i x ∂intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
        ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ≤ 1)
    (hconstant : ∀ i < g.branching^coarse, marked i → ∀ x z,
      (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) x =
        (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) z → F i x = F i z)
    (hcompare : ∀ i < g.branching^coarse, marked i →
      ∀ x ∈ g.cell coarse i ∩ good, beta x ≤ Real.exp (error x)*F i x) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, g.index fine x = g.index fine z → Γ x = Γ z) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index coarse x = i}, Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index coarse x = i}) ∧
      (∀ x ∈ g.root, ¬marked (g.index coarse x).val → Γ x = 1) ∧
      ∀ x ∈ g.root ∩ good, g.markedValue coarse marked beta x ≤
        Real.exp (g.markedError coarse marked error x)*Γ x := by
  let F0 := fun i x => if marked i then F i x else 1
  have hpos (i : ℕ) (hi : i < g.branching^coarse) (x : ℝ)
      (_hx : x ∈ g.cell coarse i) : 0 ≤ F0 i x := by
    by_cases hm : marked i
    · simpa only [F0,ite_eq_left hm] using hF i hi hm x
    · simp only [F0,ite_eq_right hm]; norm_num
  have havg (i : ℕ) (hi : i < g.branching^coarse) :
      (∫ x in g.cell coarse i, F0 i x) ≤ volume.real (g.cell coarse i) := by
    by_cases hm : marked i
    · have ha := ((g.lineWindow coarse i (fine-coarse)).window_average_le (F i)
        (hint i hi hm) (haverage i hi hm)).2
      simpa only [F0,ite_eq_left hm,lineWindow_root] using ha
    · simp [F0,hm,integral_const,measureReal_def]
  obtain ⟨Γ,hmeas,hΓ,hconst,heq,hav⟩ := g.exists_patched_window_factor coarse fine hcf hf
    F0 hpos (by
      intro i hi x hx z hz hix
      by_cases hm : marked i
      · simp only [F0,ite_eq_left hm]
        apply hconstant i hi hm x z
        apply g.lineWindow_index_of_global coarse i (fine-coarse) (fine-coarse) hi le_rfl
          (by omega) hx hz
        simpa only [Nat.add_sub_of_le hcf] using hix
      · simp only [F0,ite_eq_right hm]) havg
  refine ⟨Γ,hmeas,hΓ,hconst,hav,?_,?_⟩
  · intro x hx hm
    rw [heq x hx]
    simp only [F0,ite_eq_right hm]
  · intro x hx
    have hi : (g.index coarse x).val < g.branching^coarse := by
      change g.rawIndex (min coarse g.depth) x < g.branching^coarse
      rw [Nat.min_eq_left (hcf.trans hf)]
      exact rawIndex_lt (g := {g with depth := coarse}) le_rfl x
    have hmem := (g.index_eq_iff_mem_cell (hcf.trans hf) hx.1 (g.index coarse x).val).mp rfl
    rw [heq x hx.1]
    by_cases hm : marked (g.index coarse x).val
    · simpa only [markedValue,markedError,F0,ite_eq_left hm] using
        hcompare _ hi hm x ⟨hmem,hx.2⟩
    · simp only [markedValue,markedError,F0,ite_eq_right hm,Real.exp_zero,one_mul,le_refl]

end LipschitzHilbert.FiniteLineGrid

namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

/-- Marked errors are a subfamily of the active forward mass-path errors.
No claim that pointwise stopping is itself a coarse-cell condition is used. -/
theorem eventually_source_marked_error (C A_M : ℝ) (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n e snapshot : ℕ → ℝ) (count : ℕ) (marked : ℕ → Prop),
    ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L → n 0 ≤ L^C*N^2 →
      (∀ j, 0 ≤ n j) → Antitone n → n count ≤ L^A_M →
      (∀ j < count, marked j → L^A_M < n j) →
      (∀ j < count, marked j → snapshot j/2 ≤ pathDrop n j) →
      (∀ j < count, marked j → e j ≤ SourceParameters.step L^(-(1/32:ℝ))*snapshot j) →
      (∑ j ∈ Finset.range count, if marked j then e j else 0) ≤ 1 := by
  classical
  filter_upwards [eventually_source_snapshot_stopped_error C A_M hC hAM,
    eventually_ge_atTop (1:ℝ)] with L hL hlarge
  intro n e snapshot count marked N hN hlog hmass hn hanti hlast hmarked hdrop he
  let stop := firstMassStop n count (L^A_M)
  have hstop := firstMassStop_spec n count (L^A_M) hlast
  apply hL n (fun j => if marked j then e j else 0)
    (fun j => if marked j then snapshot j else 0) count stop hstop.1
    N hN hlog hmass hstop.2.2 (hn stop)
  · intro j hj
    by_cases hm : marked j
    · simpa only [ite_eq_left hm] using hdrop j (hj.trans_le hstop.1) hm
    · have hnj : 0 < n j :=
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hlarge) A_M).trans (hstop.2.2 j hj)
      simpa only [ite_eq_right hm,zero_div] using
        pathDrop_nonnegative n j hnj (hanti (Nat.le_succ j))
  · intro j hj
    by_cases hm : marked j
    · have hjstop : j < stop :=
        (firstMassStop_active_iff n count (L^A_M) hlast hanti j).mpr (hmarked j hj hm)
      simpa only [ite_eq_left hm,ite_eq_left hjstop] using he j hj hm
    · simp only [ite_eq_right hm,mul_zero,ite_self,le_refl]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCellMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's marking rule uses the infimum of the parent mass
and the supremum of its absolute drop over the entire line cell. The
possible unmarked large drop is the last active index, hence is unique. -/

noncomputable section
open Set
namespace LipschitzHilbert

theorem sourceMarkedCell_active {I : Set ℝ} {n h : ℝ → ℝ} {M x : ℝ}
    (hn : ∀ y ∈ I, 0 ≤ n y) (hm : sourceMarkedCell I n h M) (hx : x ∈ I) :
    M < n x :=
  hm.1.trans_le (csInf_le ⟨0,by rintro _ ⟨y,hy,rfl⟩; exact hn y hy⟩ ⟨x,hx,rfl⟩)

/-- Relative motion on the entire cell turns the supremum condition
into a uniform positive absolute drop, also for a half-open cell. -/
theorem sourceMarkedCell_drop {I : Set ℝ} {n h : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hm : sourceMarkedCell I n h M) (hx : x ∈ I)
    (hmove : ∀ y ∈ I, h y ≤ E*h x) : (1/2:ℝ)/E ≤ h x := by
  apply (div_le_iff₀ hE).mpr
  have hs : sSup (h '' I) ≤ E*h x :=
    csSup_le ⟨h x,⟨x,hx,rfl⟩⟩ (by rintro _ ⟨y,hy,rfl⟩; exact hmove y hy)
  linarith [hm.2]

/-- If an unmarked cell contains a drop of at least one, its mass
infimum is at most M. Relative motion bounds every mass by E*M. -/
theorem source_unmarked_large_drop {I : Set ℝ} {n h : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hx : x ∈ I) (hm : ¬ sourceMarkedCell I n h M)
    (hlarge : 1 ≤ h x) (hbounded : BddAbove (h '' I))
    (hmove : ∀ y ∈ I, n x ≤ E*n y) : n x ≤ E*M := by
  have hsup : (1/2:ℝ) ≤ sSup (h '' I) :=
    (by norm_num : (1/2:ℝ) ≤ 1).trans (hlarge.trans (le_csSup hbounded ⟨x,hx,rfl⟩))
  have hinf : sInf (n '' I) ≤ M := le_of_not_gt (fun he => hm ⟨he,hsup⟩)
  have hlo : n x/E ≤ sInf (n '' I) :=
    le_csInf ⟨n x,⟨x,hx,rfl⟩⟩ (by
      rintro _ ⟨y,hy,rfl⟩
      apply (div_le_iff₀ hE).mpr
      simpa only [mul_comm] using hmove y hy)
  have he := mul_le_mul_of_nonneg_left (hlo.trans hinf) hE.le
  calc
    n x = E*(n x/E) := by field_simp
    _ ≤ E*M := he

/-- A unit absolute drop from a mass below M+1 crosses the stopping
threshold. This is the exceptional index in the source decomposition. -/
theorem source_unmarked_crosses_cutoff {I : Set ℝ} {n next : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hx : x ∈ I)
    (hm : ¬ sourceMarkedCell I n (fun y => n y-next y) M)
    (hlarge : 1 ≤ n x-next x)
    (hbounded : BddAbove ((fun y => n y-next y) '' I))
    (hmove : ∀ y ∈ I, n x ≤ E*n y) (hsmall : E*M < M+1) : next x < M := by
  have hn := source_unmarked_large_drop hE hx hm hlarge hbounded hmove
  linarith

/-- The marked/unmarked dichotomy under the quantitative relative motion
used for the actual source weights. -/
theorem source_cell_marking_cases (I : Set ℝ) (n next : ℝ → ℝ) (M q : ℝ)
    (hn : ∀ y ∈ I, 0 ≤ n y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsmall : (1+q)*M < M+1)
    (hmove : ∀ x ∈ I, ∀ y ∈ I,
      n x ≤ (1+q)*n y ∧ n x-next x ≤ (1+q)*(n y-next y))
    (x : ℝ) (hx : x ∈ I) :
    (sourceMarkedCell I n (fun y => n y-next y) M →
      M < n x ∧ (1/4:ℝ) ≤ n x-next x) ∧
    (¬ sourceMarkedCell I n (fun y => n y-next y) M →
      1 ≤ n x-next x → n x < M+1 ∧ next x < M) := by
  have hE : 0 < 1+q := by linarith
  have hbounded : BddAbove ((fun y => n y-next y) '' I) :=
    ⟨(1+q)*(n x-next x),by rintro _ ⟨y,hy,rfl⟩; exact (hmove y hy x hx).2⟩
  constructor
  · intro hm
    refine ⟨sourceMarkedCell_active hn hm hx,?_⟩
    have hl := sourceMarkedCell_drop hE hm hx (fun y hy => (hmove y hy x hx).2)
    have hlo : (1/4:ℝ) ≤ (1/2:ℝ)/(1+q) := by
      apply (le_div_iff₀ hE).mpr
      linarith
    exact hlo.trans hl
  · intro hm hlarge
    have hnlarge := source_unmarked_large_drop hE hx hm hlarge hbounded
      (fun y hy => (hmove x hx y hy).1)
    exact ⟨hnlarge.trans_lt hsmall,source_unmarked_crosses_cutoff hE hx hm hlarge hbounded
      (fun y hy => (hmove x hx y hy).1) hsmall⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictableLength
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

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The marked-factor integral for unequal source blocks. The error is paid
through its path sum; all averaging remains on the original nested line grid. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem source_skipped_path_integral
    (g : FiniteLineGrid) (T : SlopeBox) (K D y E : ℝ)
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (N : ℕ) (hlevel : ∀ n ≤ N, level n ≤ g.depth)
    (hmono : ∀ n < N, level n ≤ level (n+1))
    (good : Set ℝ) (beta error Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < N, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < N, ∀ x z,
      g.index (level (n+1)) x = g.index (level (n+1)) z → Γ n x = Γ n z)
    (haverage : ∀ n < N, ∀ i : Fin (g.branching^g.depth),
      (∫ x in {x | g.index (level n) x = i}, Γ n x ∂volume.restrict g.root) ≤
        (volume.restrict g.root).real {x | g.index (level n) x = i})
    (hbeta : ∀ x ∈ g.root ∩ good, ∀ n < N, 0 ≤ beta n x)
    (hcomparison : ∀ x ∈ g.root ∩ good, ∀ n < N,
      beta n x ≤ Real.exp (error n x)*Γ n x)
    (hbudget : ∀ x ∈ g.root ∩ good, (∑ n ∈ Finset.range N, error n x) ≤ E)
    (hf : AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*∏ n ∈ Finset.range N, beta n x)) volume) :
    IntegrableOn (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ n ∈ Finset.range N, beta n x)) g.root volume ∧
    (∫ x in g.root, good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ n ∈ Finset.range N, beta n x) x) ≤
      Real.exp E*Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  let f := good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
    ∏ n ∈ Finset.range N, beta n x)
  let W := fun x => T.weight K D (x,y+T.slope*x)*∏ n ∈ Finset.range N, Γ n x
  obtain ⟨hW,hWbound⟩ := g.top_weight_skipped_average T y hK hD hwidth level N hlevel
    hmono Γ hΓ hconstant haverage
  have hpoint (x : ℝ) (hx : x ∈ g.root) : 0 ≤ f x ∧ f x ≤ Real.exp E*W x := by
    have hw := (T.weight_pos (zero_lt_one.trans_le hK) D (x,y+T.slope*x)).le
    by_cases hg : x ∈ good
    · have hmem : x ∈ g.root ∩ good := ⟨hx,hg⟩
      have hp := product_le_of_error_budget (fun n : Fin N => beta n.val x)
        (fun n : Fin N => Γ n.val x) (fun n : Fin N => error n.val x) E
        (fun n => hbeta x hmem n.val n.isLt) (fun n => hΓ n.val n.isLt x)
        (fun n => hcomparison x hmem n.val n.isLt)
        (by simpa only [Finset.sum_range] using hbudget x hmem)
      have hp' : (∏ n ∈ Finset.range N, beta n x) ≤
          Real.exp E*∏ n ∈ Finset.range N, Γ n x := by
        simpa only [Finset.prod_range] using hp
      dsimp only [f,W]
      rw [Set.indicator_of_mem hg]
      refine ⟨mul_nonneg hw (Finset.prod_nonneg fun n hn =>
        hbeta x hmem n (Finset.mem_range.mp hn)),?_⟩
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hp' hw
    · simp only [f,Set.indicator_of_notMem hg]
      exact ⟨le_rfl,mul_nonneg (Real.exp_pos E).le
        (mul_nonneg hw (Finset.prod_nonneg fun n hn => hΓ n (Finset.mem_range.mp hn) x))⟩
  have hpointAE : ∀ᵐ x ∂volume.restrict g.root, 0 ≤ f x ∧ f x ≤ Real.exp E*W x := by
    filter_upwards [ae_restrict_mem (show MeasurableSet g.root from measurableSet_Ico)] with x hx
    exact hpoint x hx
  have hfi : Integrable f (volume.restrict g.root) := (hW.const_mul (Real.exp E)).mono'
    hf.restrict (hpointAE.mono fun x hx => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ x in g.root, Real.exp E*W x :=
      integral_mono_ae hfi (hW.const_mul _) (hpointAE.mono fun _ h => h.2)
    _ = Real.exp E*∫ x in g.root, W x := integral_const_mul _ _
    _ ≤ Real.exp E*(Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x)) :=
      mul_le_mul_of_nonneg_left hWbound (Real.exp_pos _).le
    _ = _ := (mul_assoc _ _ _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseBlocks
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source line windows grow along the angular path. Reading those
windows in reverse gives increasing levels in one finite line grid. Only
the factors are reordered: the stopping budget retains its forward mass
path, including the possibility of a zero terminal mass. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

theorem reverseLevel_le (σ : Fin K) (count k : ℕ) :
    reverseLevel σ count k ≤ endpoint σ count := Nat.sub_le _ _

theorem reverseLevel_monotone (hK : 0 < K) (σ : Fin K) (count : ℕ) :
    Monotone (reverseLevel σ count) := by
  intro a b hab
  exact Nat.sub_le_sub_left ((endpoint_strictMono hK σ).monotone
    (Nat.sub_le_sub_left hab count)) _

theorem reverseIndex_lt {count j : ℕ} (hj : j < count) :
    reverseIndex count j < count := by
  unfold reverseIndex
  omega

theorem reverseIndex_involutive {count j : ℕ} (hj : j < count) :
    reverseIndex count (reverseIndex count j) = j := by
  unfold reverseIndex
  omega

theorem reverseLevel_block_start (σ : Fin K) {count j : ℕ} (hj : j < count) :
    reverseLevel σ count (reverseIndex count j) =
      endpoint σ count-endpoint σ (j+1) := by
  unfold reverseLevel reverseIndex
  congr 2
  omega

theorem reverseLevel_block_end (σ : Fin K) {count j : ℕ} (hj : j < count) :
    reverseLevel σ count (reverseIndex count j+1) =
      endpoint σ count-endpoint σ j := by
  unfold reverseLevel reverseIndex
  congr 2
  omega

theorem reverseLevel_block_length (hK : 0 < K) (σ : Fin K) {count j : ℕ}
    (hj : j < count) :
    reverseLevel σ count (reverseIndex count j+1)-
        reverseLevel σ count (reverseIndex count j) =
      endpoint σ (j+1)-endpoint σ j := by
  rw [reverseLevel_block_start σ hj,reverseLevel_block_end σ hj]
  have h1 := (endpoint_strictMono hK σ).monotone (show j+1 ≤ count by omega)
  have h2 := (endpoint_strictMono hK σ).monotone (Nat.le_succ j)
  omega

theorem sum_reverseIndex {M : Type*} [AddCommMonoid M] (f : ℕ → M) (count : ℕ) :
    (∑ j ∈ Finset.range count, f (reverseIndex count j)) =
      ∑ j ∈ Finset.range count, f j :=
  Finset.sum_range_reflect f count

theorem prod_reverseIndex {M : Type*} [CommMonoid M] (f : ℕ → M) (count : ℕ) :
    (∏ j ∈ Finset.range count, f (reverseIndex count j)) =
      ∏ j ∈ Finset.range count, f j :=
  Finset.prod_range_reflect f count

end LipschitzHilbert.ShiftedBlocks

namespace LipschitzHilbert

theorem sourceReverseLineGrid_levels {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) (count : ℕ) :
    (∀ k ≤ count, ShiftedBlocks.reverseLevel σ count k ≤
      (sourceReverseLineGrid g L origin hw σ count).depth) ∧
    (∀ k < count, ShiftedBlocks.reverseLevel σ count k ≤
      ShiftedBlocks.reverseLevel σ count (k+1)) := by
  exact ⟨fun k _ => ShiftedBlocks.reverseLevel_le σ count k,
    fun k _ => ShiftedBlocks.reverseLevel_monotone hK σ count (Nat.le_succ k)⟩

theorem source_reverse_line_mesh {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) (count k : ℕ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count k) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (count-k)) := by
  have hle := (ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.sub_le count k)
  have hm := source_block_line_mesh g L origin hw
    (ShiftedBlocks.endpoint σ (count-k)) (ShiftedBlocks.endpoint σ count) hle hbranch
  simpa only [sourceReverseLineGrid,ShiftedBlocks.reverseLevel,sourceLineGrid_mesh] using hm

/-- The coarse side of original block j is its child window. -/
theorem source_reverse_block_coarse {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) := by
  rw [source_reverse_line_mesh g L origin hw σ hK count _ hbranch]
  congr 2
  unfold ShiftedBlocks.reverseIndex
  omega

/-- Refining that child window across the block gives its parent mesh. -/
theorem source_reverse_block_fine {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ j) := by
  rw [source_reverse_line_mesh g L origin hw σ hK count _ hbranch]
  congr 2
  unfold ShiftedBlocks.reverseIndex
  omega

theorem source_reverse_local_mesh {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (i : ℕ) :
    let grid := sourceReverseLineGrid g L origin hw σ count
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
    (grid.lineWindow coarse i (fine-coarse)).width =
        sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) ∧
      (grid.lineWindow coarse i (fine-coarse)).meshWidth (fine-coarse) =
        sourceLineScale g L w (ShiftedBlocks.endpoint σ j) := by
  dsimp only
  constructor
  · exact source_reverse_block_coarse g L origin hw σ hK hj hbranch
  · rw [FiniteLineGrid.lineWindow_meshWidth,
      Nat.add_sub_of_le (ShiftedBlocks.reverseLevel_monotone hK σ count (Nat.le_succ _))]
    exact source_reverse_block_fine g L origin hw σ hK hj hbranch

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

end LipschitzHilbert.AngularGrid

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

theorem eligible_before_firstIneligibleShiftedBlock {K : ℕ}
    (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) (hK : 0 < K)
    (σ : Fin K) {j : ℕ} (hj : j < g.firstIneligibleShiftedBlock cutoff precision hp hK σ) :
    g.eligible cutoff precision (ShiftedBlocks.endpoint σ j) := by
  exact Classical.not_not.mp
    (Nat.find_min (g.exists_shifted_terminal cutoff precision hp hK σ) hj)

theorem firstIneligibleShiftedBlock_pos {K : ℕ}
    (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) (hK : 0 < K)
    (σ : Fin K) (hzero : g.eligible cutoff precision 0) :
    0 < g.firstIneligibleShiftedBlock cutoff precision hp hK σ := by
  by_contra hn
  have hz : g.firstIneligibleShiftedBlock cutoff precision hp hK σ = 0 := by omega
  have hs := g.firstIneligibleShiftedBlock_spec cutoff precision hp hK σ
  apply hs
  simpa only [hz,ShiftedBlocks.endpoint_zero] using hzero

/-- Even the terminal block, whose upper endpoint need no longer be
eligible, has line window at most the original top length. Eligibility is
only used at the lower endpoint and the block width jump is at most B. -/
theorem source_block_line_scale_le_length (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
    (j : ℕ) {w length : ℝ} (hw : 0 < w) (hlength : 0 < length)
    (he : g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/length)
      (ShiftedBlocks.endpoint σ j)) :
    sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) ≤ length := by
  let B := SourceParameters.branching L
  let R := SourceParameters.step L^(1/2:ℝ)
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hB : 1 ≤ B := one_le_pow₀ hG
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hR : 1 ≤ R := Real.one_le_rpow hG (by norm_num)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hwidth : g.width lower ≤ B*g.width upper :=
    (g.source_shifted_width_bounds L hbranch hK σ j).2
  have hden : g.width lower ≤ B^2*(g.width upper*R) := by
    have hb2 : B ≤ B^2 := by nlinarith
    calc
      _ ≤ B*g.width upper := hwidth
      _ ≤ B^2*g.width upper := mul_le_mul_of_nonneg_right hb2 (g.width_pos upper).le
      _ ≤ (B^2*g.width upper)*R :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg B) (g.width_pos upper).le) hR
      _ = _ := by ring
  have hlengthBound := g.source_eligible_length_lower hw hB0 hlength lower he
  calc
    sourceLineScale g L w upper = w/(g.width upper*R) := rfl
    _ ≤ B^2*w/g.width lower := by
      apply (div_le_div_iff₀ (mul_pos (g.width_pos upper) hR0) (g.width_pos lower)).mpr
      calc
        w*g.width lower ≤ w*(B^2*(g.width upper*R)) :=
          mul_le_mul_of_nonneg_left hden hw.le
        _ = (B^2*w)*(g.width upper*R) := by ring
    _ ≤ length := hlengthBound

/-- The concrete reverse grid ending at the first ineligible endpoint
satisfies the width hypothesis of the weighted path integral. -/
theorem source_first_terminal_grid_width (g : AngularGrid) (L origin : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
    {w length : ℝ} (hw : 0 < w) (hlength : 0 < length)
    (hzero : g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/length) 0) :
    let count := g.firstIneligibleShiftedBlock (g.rootWidth/(SourceParameters.branching L)^2)
      (w/length) (div_pos hw hlength) hK σ
    (sourceReverseLineGrid g L origin hw σ count).width ≤ length := by
  dsimp only
  let count := g.firstIneligibleShiftedBlock (g.rootWidth/(SourceParameters.branching L)^2)
    (w/length) (div_pos hw hlength) hK σ
  have hc : 0 < count := g.firstIneligibleShiftedBlock_pos _ _ _ hK σ hzero
  have he := g.eligible_before_firstIneligibleShiftedBlock
    (g.rootWidth/(SourceParameters.branching L)^2) (w/length)
    (div_pos hw hlength) hK σ (show count-1 < count by omega)
  have hscale := g.source_block_line_scale_le_length L hbranch hK σ (count-1) hw hlength he
  have hcEq : count-1+1 = count := by omega
  change sourceLineScale g L w (ShiftedBlocks.endpoint σ count) ≤ length
  simpa only [hcEq] using hscale

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalAmplitudeMeasurable
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The masked physical packet family is measurable in the spatial
point. Its analyzing coefficients are fixed integrals; no continuity of
the direction selector is required. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

private theorem vectorPacketSynthesis_joint_continuous {ι κ : Type*}
    [Fintype ι] [Fintype κ] (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → ℝ → SchwartzMap ℝ ℂ)
    (hf : ∀ i k, Continuous (fun z : ℝ × ℝ => f i k z.1 z.2)) :
    Continuous (fun z : ℝ × ℝ => vectorPacketSynthesis c (fun i k => f i k z.1) z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  simp only [packetSynthesis_apply]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hf i k))

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawBand_slope_continuous (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (j : Fin N) (slope : ℝ) :
    Continuous (fun z : ℝ × ℝ => P.rawBand coeff jet j z.1 (z.2-slope*z.1)) := by
  have hc := vectorPacketSynthesis_joint_continuous
    (fun u : Σ l : P.labels j, Item j l => coeff j u.1 u.2)
    (fun u k y => P.raw jet j u.1 u.2 k y)
    (fun u k => modulatedPlanarJet_continuous (P.profile j u.1 u.2 k)
      (P.actualX j u.1 u.2) (P.actualZ j u.1 u.2) (P.length j) P.width
      (-P.rowSlope j u.1) (P.frequency k) P.scale (P.length_pos j).ne' jet)
  have hs := hc.comp
    (show Continuous (fun z : ℝ × ℝ => (z.2-slope*z.1,z.1)) by fun_prop)
  change Continuous (fun z : ℝ × ℝ => vectorPacketSynthesis
    (fun u : Σ l : P.labels j, Item j l => coeff j u.1 u.2)
    (fun u k => P.raw jet j u.1 u.2 k (z.2-slope*z.1)) z.1)
  exact hs

theorem masked_rawBand_continuous (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (T : SlopeBox) (L A : ℝ) (jet : Fin 3) (j : Fin N) :
    Continuous (fun z : ℝ × ℝ =>
      P.rawBand (fun j l u => T.mask L A z • coeff j l u) jet j z.1 (z.2-T.slope*z.1)) := by
  have hc := (T.mask_continuous L A).smul (P.rawBand_slope_continuous coeff jet j T.slope)
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact P.rawBand_coeff_real_smul coeff (T.mask L A z) jet j z.1 (z.2-T.slope*z.1)

end SourceLabeledLattice

end LipschitzHilbert

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

namespace FiniteLineGrid

theorem snapshot_displacement_le_width (g : FiniteLineGrid) {x₀ x : ℝ}
    (h₀ : x₀ ∈ g.root) (hx : x ∈ g.root) : |x-x₀| ≤ g.width := by
  rw [abs_le]
  constructor <;> linarith [h₀.1,h₀.2,hx.1,hx.2]

end FiniteLineGrid

/-- Both parameterizations name the same physical point of the reference
line, so packet-motion estimates apply to the chosen snapshot. -/
theorem lineShift_snapshot (s y x₀ x : ℝ) :
    SlopeBox.lineShift s (x-x₀) (x₀,y+s*x₀) = (x,y+s*x) := by
  unfold SlopeBox.lineShift
  congr 1 <;> ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseSnapshot
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local grid used by physical packet prediction is exactly a translated
window of the single reverse angular grid. No replacement partition or
rounding of a block length is required. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

namespace FiniteLineGrid

private theorem eq_of_fields (g h : FiniteLineGrid)
    (hb : g.branching = h.branching) (ho : g.origin = h.origin)
    (hw : g.width = h.width) (hd : g.depth = h.depth) : g = h := by
  cases g
  cases h
  simp_all

end FiniteLineGrid

/-- The physical block predictor uses this very translated reverse-grid
window, including the shorter initial angular block. -/
theorem source_reverse_snapshot_window {K : ℕ} (g : AngularGrid) (L origin : ℝ)
    {w : ℝ} (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ}
    (hj : j < count) (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (i : ℕ) (x₀ : ℝ) :
    let grid := sourceReverseLineGrid g L origin hw σ count
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
    (grid.lineWindow coarse i (fine-coarse)).atSnapshot x₀ =
      sourceLineGrid L ((grid.lineWindow coarse i (fine-coarse)).origin-x₀)
        (sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)))
        (ShiftedBlocks.endpoint σ (j+1)-ShiftedBlocks.endpoint σ j)
        (sourceLineScale_pos g L hw (ShiftedBlocks.endpoint σ (j+1))) := by
  dsimp only
  apply FiniteLineGrid.eq_of_fields
  · rfl
  · rfl
  · exact (source_reverse_local_mesh g L origin hw σ hK hj hbranch i).1
  · exact ShiftedBlocks.reverseLevel_block_length hK σ hj

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMarkingParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual relative mass-motion error is small even after multiplication
by the polynomial stopping threshold. These fixed-parameter bounds supply
the source's exceptional-cell argument. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_marking_parameters (D Kw A_M : ℝ)
    (hD : 0 ≤ D) (hKw : 0 < Kw) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let q := Real.exp δ*δ
      q ≤ 1/8 ∧ (1+q)*L^A_M < L^A_M+1 := by
  let C := 5*D/Kw
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_source_polynomial_motion (8*Real.exp C*C) A_M,
    eventually_ge_atTop (1:ℝ)] with L hpoly hL
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hs : 1 ≤ Real.sqrt (SourceParameters.step L) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    simpa using hG
  have hδ : C/Real.sqrt (SourceParameters.step L) ≤ C := div_le_self hC hs
  have hδ0 : 0 ≤ C/Real.sqrt (SourceParameters.step L) := div_nonneg hC (Real.sqrt_nonneg _)
  have hM : 1 ≤ L^A_M := Real.one_le_rpow hL hAM
  have he := Real.exp_le_exp.mpr hδ
  have hqM : (Real.exp (C/Real.sqrt (SourceParameters.step L))*
      (C/Real.sqrt (SourceParameters.step L)))*L^A_M ≤ 1/8 := by
    have hgain : SourceParameters.step L^(-(1/4:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
    have hbound := hpoly.trans hgain
    have hq := mul_le_mul_of_nonneg_right he hδ0
    have hm := mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg (by linarith : 0 ≤ L) A_M)
    have heq : (8*Real.exp C*C)*L^A_M/Real.sqrt (SourceParameters.step L) =
        8*((Real.exp C*(C/Real.sqrt (SourceParameters.step L)))*L^A_M) := by ring
    rw [heq] at hbound
    linarith
  have hq0 : 0 ≤ Real.exp (C/Real.sqrt (SourceParameters.step L))*
      (C/Real.sqrt (SourceParameters.step L)) := mul_nonneg (Real.exp_pos _).le hδ0
  have hq := (mul_le_mul_of_nonneg_left hM hq0).trans hqM
  dsimp only
  change Real.exp (C/Real.sqrt (SourceParameters.step L))*(C/Real.sqrt (SourceParameters.step L)) ≤ 1/8 ∧ _
  refine ⟨by simpa only [mul_one] using hq,?_⟩
  change (1+Real.exp (C/Real.sqrt (SourceParameters.step L))*
    (C/Real.sqrt (SourceParameters.step L)))*L^A_M < L^A_M+1
  nlinarith

/-- The conclusion is uniform over the source weight scale Kw≥1. -/
theorem eventually_source_marking_parameters_uniform (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ Kw : ℝ, 1 ≤ Kw →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let q := Real.exp δ*δ
      q ≤ 1/8 ∧ (1+q)*L^A_M < L^A_M+1 := by
  filter_upwards [eventually_source_marking_parameters D 1 A_M hD (by norm_num) hAM,
    eventually_ge_atTop (1:ℝ)] with L hbase hL
  intro Kw hKw
  have hs : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hd0 : 0 ≤ (5*D/Kw)/Real.sqrt (SourceParameters.step L) := by positivity
  have hd : (5*D/Kw)/Real.sqrt (SourceParameters.step L) ≤
      (5*D/1)/Real.sqrt (SourceParameters.step L) := by
    apply div_le_div_of_nonneg_right _ hs.le
    simpa only [div_one] using div_le_self (show 0 ≤ 5*D by positivity) hKw
  have hq := mul_le_mul (Real.exp_le_exp.mpr hd) hd hd0 (Real.exp_pos _).le
  dsimp only at hbase ⊢
  refine ⟨hq.trans hbase.1,?_⟩
  have hq1 : 1+Real.exp ((5*D/Kw)/Real.sqrt (SourceParameters.step L))*
      ((5*D/Kw)/Real.sqrt (SourceParameters.step L)) ≤
      1+Real.exp ((5*D/1)/Real.sqrt (SourceParameters.step L))*
        ((5*D/1)/Real.sqrt (SourceParameters.step L)) := by linarith
  have hm := mul_le_mul_of_nonneg_right hq1
    (Real.rpow_nonneg (by linarith : 0 ≤ L) A_M)
  exact hm.trans_lt hbase.2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedCellMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute path drops are sums over the actual lost tops. This gives
the cellwise relative motion needed by the source's infimum/supremum
marking rule, including a terminal block with no continuing path child. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem shiftedPathLossTops_subset {ι : Type*} {K : ℕ} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (σ : Fin K) (top : ι) (j : ℕ) :
    g.shiftedPathLossTops tops slope precision cutoff σ top j ⊆
      g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)) := by
  unfold shiftedPathLossTops
  split_ifs
  · exact Finset.sdiff_subset
  · exact Finset.Subset.refl _

theorem shiftedPathMass_difference {ι X : Type*} {K : ℕ} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hK : 0 < K) (σ : Fin K)
    (top : ι) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j)) (x : X) :
    g.shiftedPathMass tops slope precision cutoff weight σ top x j-
        g.shiftedPathMass tops slope precision cutoff weight σ top x (j+1) =
      ∑ t ∈ g.shiftedPathLossTops tops slope precision cutoff σ top j, weight t x := by
  rw [shiftedPathMass,ite_eq_left he]
  unfold shiftedPathLossTops
  split_ifs with hn
  · rw [shiftedPathMass,ite_eq_left hn]
    exact sub_eq_iff_eq_add.mpr (Finset.sum_sdiff (f := fun t => weight t x)
      (g.cellTops_subset_ancestor tops slope precision cutoff hp
        ((ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)) (slope top))).symm
  · rw [shiftedPathMass,ite_eq_right hn,sub_zero]
    rfl

/-- Parent mass and absolute loss have the same relative motion bound:
each is a positive sum over a subset of the parent tops. -/
theorem source_shifted_absolute_motion {ι : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ j))
    (sR : ℝ) (hs : g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR)
    (hblock : g.width (ShiftedBlocks.endpoint σ j) ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (b : ℝ) (hb : |b| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (z : ℝ × ℝ) :
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight Kw D x) σ top x
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    |n (SlopeBox.lineShift sR b z) j-n z j| ≤ Real.exp δ*δ*n z j ∧
      |(n (SlopeBox.lineShift sR b z) j-n (SlopeBox.lineShift sR b z) (j+1))-
        (n z j-n z (j+1))| ≤ Real.exp δ*δ*(n z j-n z (j+1)) := by
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cut := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let lo := ShiftedBlocks.endpoint σ j
  let hi := ShiftedBlocks.endpoint σ (j+1)
  let parent := g.cellTops tops slope precision cut lo (g.index lo (slope top))
  let loss := g.shiftedPathLossTops tops slope precision cut σ top j
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hparent := g.parent_subset_boundary tops slope precision cut 0 lo 0 (slope top)
  have hm (A : Finset ι) (hA : A ⊆ parent) :=
    g.source_submass_relative_motion tops T w B Kw D hw hB hKw hD hwidth
      0 lo lo le_rfl 0 (by norm_num) (g.width_pos lo).le (slope top) sR hs
      (g.width hi) (g.width_pos hi) hblock A (hA.trans hparent) b hb z
  have hn (x : ℝ × ℝ) :
      g.shiftedPathMass tops slope precision cut weight σ top x j = ∑ t ∈ parent, weight t x := by
    rw [shiftedPathMass,ite_eq_left he]
    rfl
  have hl (x : ℝ × ℝ) :=
    g.shiftedPathMass_difference tops slope precision cut weight hp hK σ top j he x
  change |g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) j-
    g.shiftedPathMass tops slope precision cut weight σ top z j| ≤
      (Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*((5*D/Kw)/Real.sqrt (g.branching:ℝ)))*
        g.shiftedPathMass tops slope precision cut weight σ top z j ∧
    |(g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) j-
      g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) (j+1))-
      (g.shiftedPathMass tops slope precision cut weight σ top z j-
        g.shiftedPathMass tops slope precision cut weight σ top z (j+1))| ≤
      (Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*((5*D/Kw)/Real.sqrt (g.branching:ℝ)))*
        (g.shiftedPathMass tops slope precision cut weight σ top z j-
          g.shiftedPathMass tops slope precision cut weight σ top z (j+1))
  constructor
  · simpa only [hn] using hm parent (Finset.Subset.refl _)
  · simpa only [hl] using hm loss (g.shiftedPathLossTops_subset tops slope precision cut σ top j)

/-- Every pair of physical points in one reference cell has the above
motion bound. This is uniform over cells and their position on the line. -/
theorem source_shifted_line_cell_motion {ι : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ j))
    (sR y : ℝ) (hs : g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR)
    (hblock : g.width (ShiftedBlocks.endpoint σ j) ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (grid : FiniteLineGrid)
    (hgrid : grid.width ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (x z : ℝ) (hx : x ∈ grid.root) (hz : z ∈ grid.root) :
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight Kw D x)
      σ top (x,y+sR*x)
    let q := Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ))
    n x j ≤ (1+q)*n z j ∧
      n x j-n x (j+1) ≤ (1+q)*(n z j-n z (j+1)) := by
  have hb := (grid.snapshot_displacement_le_width hz hx).trans hgrid
  have hm := g.source_shifted_absolute_motion tops T w B Kw D hw hB hKw hD hwidth
    hK σ j top he sR hs hblock (x-z) hb (z,y+sR*z)
  rw [lineShift_snapshot] at hm
  dsimp only
  constructor
  · have h := (abs_le.mp hm.1).2
    linarith
  · have h := (abs_le.mp hm.2).2
    linarith

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalCellMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source marking dichotomy for actual top weights on an arbitrary
reference-line cell of the prescribed block length. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_physical_cell_marking (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ), 0 < w → 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (j : ℕ) (top : ι),
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length)
        (ShiftedBlocks.endpoint σ j) →
    ∀ (y : ℝ) (grid : FiniteLineGrid),
      grid.width ≤ sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) →
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x)
    let mark := sourceMarkedCell grid.root (fun x => n x j)
      (fun x => n x j-n x (j+1)) (L^A_M)
    ∀ x ∈ grid.root,
      (mark → L^A_M < n x j ∧ (1/4:ℝ) ≤ n x j-n x (j+1)) ∧
      (¬mark → 1 ≤ n x j-n x (j+1) → n x j < L^A_M+1 ∧ n x (j+1) < L^A_M) := by
  filter_upwards [eventually_source_marking_parameters_uniform D A_M hD hAM]
    with L hnumeric
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ j top he y grid hgrid
  dsimp only
  intro x hx
  let q := Real.exp ((5*D/Kw)/Real.sqrt (SourceParameters.step L))*
    ((5*D/Kw)/Real.sqrt (SourceParameters.step L))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hnum := hnumeric Kw hKw
  apply source_cell_marking_cases grid.root
    (fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x) j)
    (fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x) (j+1))
    (L^A_M) q
  · intro z _
    exact g.shiftedPathMass_nonneg tops _ _ _ _
      (fun t z => ((T t).weight_pos (zero_lt_one.trans_le hKw) D z).le) σ top _ j
  · exact hq0
  · exact hnum.1.trans (by norm_num)
  · exact hnum.2
  · intro a ha b hb
    have hB : 1 ≤ SourceParameters.branching L :=
      one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    have hg : grid.width ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*
        Real.sqrt (g.branching:ℝ)) := by
      simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using hgrid
    have hm := g.source_shifted_line_cell_motion tops T w (SourceParameters.branching L)
      Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hK σ j top he
      (T top).slope y rfl (g.source_shifted_width_bounds L hbranch hK σ j).2
      grid hg a b ha hb
    simpa only [hbranch] using hm
  · exact hx

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseCellMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal source marking rule on every nested reverse-grid cell.
Eligibility is derived from the actual first terminal block. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_reverse_cell_marking (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (top : ι) (origin y : ℝ),
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      σ top (x,y+(T top).slope*x)
    ∀ j < count, ∀ i : ℕ,
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let mark := sourceMarkedCell (grid.cell coarse i) (fun x => n x j)
      (fun x => n x j-n x (j+1)) (L^A_M)
    ∀ x ∈ grid.cell coarse i,
      (mark → L^A_M < n x j ∧ (1/4:ℝ) ≤ n x j-n x (j+1)) ∧
      (¬mark → 1 ≤ n x j-n x (j+1) → n x j < L^A_M+1 ∧ n x (j+1) < L^A_M) := by
  filter_upwards [eventually_source_physical_cell_marking D A_M hD hAM]
    with L hmark
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ top origin y
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  intro j hj i x hx
  let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
  let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
  have he := g.eligible_before_firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ hj
  have hwgrid : (grid.lineWindow coarse i (fine-coarse)).width ≤
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) :=
    (source_reverse_local_mesh g L origin hw σ hK hj hbranch i).1.le
  have hxgrid : x ∈ (grid.lineWindow coarse i (fine-coarse)).root := by
    rwa [FiniteLineGrid.lineWindow_root]
  have hm := hmark ι g tops T w Kw hw hKw hbranch hwidth hK σ j top he y
    (grid.lineWindow coarse i (fine-coarse)) hwgrid x hxgrid
  simpa only [FiniteLineGrid.lineWindow_root] using hm

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseDropComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual path-drop comparison between any two points of one reverse
line cell. This supplies the snapshot-to-point error transfer used when
patching the physical predictors. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_reverse_drop_comparison (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (top : ι), top ∈ tops → ∀ origin y : ℝ,
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      σ top (x,y+(T top).slope*x)
    ∀ j < count, ∀ i : ℕ,
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    ∀ x ∈ grid.cell coarse i, ∀ z ∈ grid.cell coarse i,
      pathDrop (n z) j/2 ≤ pathDrop (n x) j ∧
        pathDrop (n x) j ≤ 2*pathDrop (n z) j := by
  filter_upwards [eventually_source_marking_parameters_uniform D 0 hD (by norm_num)]
    with L hnumeric
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ top htop origin y
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  intro j hj i x hx z hz
  let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
  let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
  let win := grid.lineWindow coarse i (fine-coarse)
  have hxw : x ∈ win.root := by
    change x ∈ (grid.lineWindow coarse i (fine-coarse)).root
    rwa [FiniteLineGrid.lineWindow_root]
  have hzw : z ∈ win.root := by
    change z ∈ (grid.lineWindow coarse i (fine-coarse)).root
    rwa [FiniteLineGrid.lineWindow_root]
  have hb : |x-z| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)) := by
    have h := win.snapshot_displacement_le_width hzw hxw
    have hwid := (source_reverse_local_mesh g L origin hw σ hK hj hbranch i).1
    change win.width = sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) at hwid
    rw [hwid] at h
    simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using h
  have he := g.eligible_before_firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ hj
  have hB : 1 ≤ SourceParameters.branching L :=
    one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hsmall : Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ)) ≤ 1/8 := by
    simpa only [hbranch] using (hnumeric Kw hKw).1
  have hm := g.source_shifted_path_drop_motion tops T w (SourceParameters.branching L)
    Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hK σ j top htop he
    (ShiftedBlocks.endpoint σ j) le_rfl (T top).slope rfl
    (g.source_shifted_width_bounds L hbranch hK σ j).2 (x-z) hb
    (z,y+(T top).slope*z) hsmall
  rw [lineShift_snapshot] at hm
  exact ⟨hm.2.2.1,hm.2.2.2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSnapshotChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Snapshots are chosen only on one fixed line. A cell missing the good
set has the constant factor one. No measurable choice across lines is used. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.FiniteLineGrid
attribute [local instance] Classical.propDecidable

/-- Patch local predictors selected at good snapshots. Factor-two drop
comparison converts their snapshot errors into actual pointwise errors. -/
theorem exists_marked_prediction_from_snapshots (g : FiniteLineGrid)
    (coarse fine : ℕ) (hcf : coarse ≤ fine) (hf : fine ≤ g.depth)
    (marked : ℕ → Prop) (good : Set ℝ) (beta u : ℝ → ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hpredict : ∀ i < g.branching^coarse, marked i →
      ∀ x₀ ∈ g.cell coarse i ∩ good,
      ∃ F : ℝ → ℝ,
        (∀ x, 0 ≤ F x) ∧
        Integrable F (intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
          ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ∧
        (∫ x, F x ∂intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
          ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ≤ 1 ∧
        (∀ x z, (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) x =
          (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) z → F x = F z) ∧
        ∀ x ∈ g.cell coarse i ∩ good, beta x ≤ Real.exp (ρ*u x₀)*F x)
    (hdrop : ∀ i < g.branching^coarse, marked i →
      ∀ x₀ ∈ g.cell coarse i ∩ good, ∀ x ∈ g.cell coarse i ∩ good,
        u x₀/2 ≤ u x) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, g.index fine x = g.index fine z → Γ x = Γ z) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index coarse x = i}, Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index coarse x = i}) ∧
      (∀ x ∈ g.root, ¬marked (g.index coarse x).val → Γ x = 1) ∧
      ∀ x ∈ g.root ∩ good, g.markedValue coarse marked beta x ≤
        Real.exp (g.markedError coarse marked (fun x => (2*ρ)*u x) x)*Γ x := by
  have hlocal (i : ℕ) (hi : i < g.branching^coarse) (hm : marked i) :
      ∃ F : ℝ → ℝ,
        (∀ x, 0 ≤ F x) ∧
        Integrable F (intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
          ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ∧
        (∫ x, F x ∂intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
          ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ≤ 1 ∧
        (∀ x z, (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) x =
          (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) z → F x = F z) ∧
        ∀ x ∈ g.cell coarse i ∩ good, beta x ≤ Real.exp ((2*ρ)*u x)*F x := by
    by_cases hne : (g.cell coarse i ∩ good).Nonempty
    · obtain ⟨x₀,hx₀⟩ := hne
      obtain ⟨F,hpos,hint,havg,hconst,hcomp⟩ := hpredict i hi hm x₀ hx₀
      refine ⟨F,hpos,hint,havg,hconst,?_⟩
      intro x hx
      have herr := source_error_of_drop_comparability hρ (hdrop i hi hm x₀ hx₀ x hx)
        (le_refl (ρ*u x₀))
      exact (hcomp x hx).trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr herr) (hpos x))
    · let := intervalProbability_isProbability
        (show (g.lineWindow coarse i (fine-coarse)).origin <
          (g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width by
          linarith [(g.lineWindow coarse i (fine-coarse)).width_pos])
      refine ⟨fun _ => 1,fun _ => zero_le_one,integrable_const 1,?_,fun _ _ _ => rfl,?_⟩
      · simp
      · intro x hx
        exact (hne ⟨x,hx⟩).elim
  choose F hF using hlocal
  exact g.exists_marked_source_prediction coarse fine hcf hf marked good beta
    (fun x => (2*ρ)*u x) (fun i => if hi : i < g.branching^coarse then
      if hm : marked i then F i hi hm else fun _ => 1 else fun _ => 1)
    (fun i hi hm x => by simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).1 x)
    (fun i hi hm => by simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).2.1)
    (fun i hi hm => by simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).2.2.1)
    (fun i hi hm x z hxz => by
      simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).2.2.2.1 x z hxz)
    (fun i hi hm x hx => by
      simpa only [dite_eq_left hi,dite_eq_left hm] using (hF i hi hm).2.2.2.2 x hx)

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMarkedFactorsIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrate the already patched source factors. Their normalizations
are exact, while the forward mass path pays the pointwise marked errors. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem source_marked_factors_integral
    (g : FiniteLineGrid) (T : SlopeBox) (K D y E : ℝ)
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (count : ℕ) (hlevel : ∀ k ≤ count, level k ≤ g.depth)
    (hmono : ∀ k < count, level k ≤ level (k+1))
    (good : Set ℝ) (marked : ℕ → ℕ → Prop) (beta error Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ j < count, ∀ x, 0 ≤ Γ j x)
    (hconst : ∀ j < count, ∀ x z,
      g.index (level (ShiftedBlocks.reverseIndex count j+1)) x =
        g.index (level (ShiftedBlocks.reverseIndex count j+1)) z → Γ j x = Γ j z)
    (havg : ∀ j < count, ∀ i : Fin (g.branching^g.depth),
      (∫ x in {x | g.index (level (ShiftedBlocks.reverseIndex count j)) x = i},
        Γ j x ∂volume.restrict g.root) ≤
        (volume.restrict g.root).real {x | g.index (level (ShiftedBlocks.reverseIndex count j)) x = i})
    (hbeta : ∀ x ∈ g.root ∩ good, ∀ j < count, 0 ≤ beta j x)
    (hcompare : ∀ x ∈ g.root ∩ good, ∀ j < count,
      reverseMarkedValue g level count marked beta j x ≤
        Real.exp (reverseMarkedError g level count marked error j x)*Γ j x)
    (hbudget : ∀ x ∈ g.root ∩ good,
      (∑ j ∈ Finset.range count, reverseMarkedError g level count marked error j x) ≤ E)
    (hf : AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*
        ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x)) volume) :
    IntegrableOn (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x)) g.root volume ∧
    (∫ x in g.root, good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x) x) ≤
      Real.exp E*Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  let B := reverseMarkedValue g level count marked beta
  let e := reverseMarkedError g level count marked error
  have hprod (x : ℝ) := ShiftedBlocks.prod_reverseIndex (fun j => B j x) count
  have hsum (x : ℝ) := ShiftedBlocks.sum_reverseIndex (fun j => e j x) count
  have hf' : AEStronglyMeasurable (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, B (ShiftedBlocks.reverseIndex count j) x)) volume := by
    simpa only [hprod] using hf
  have hi := source_skipped_path_integral g T K D y E hK hD hwidth level count hlevel hmono
    good (fun k => B (ShiftedBlocks.reverseIndex count k))
    (fun k => e (ShiftedBlocks.reverseIndex count k))
    (fun k => Γ (ShiftedBlocks.reverseIndex count k))
    (fun k hk => hΓ _ (ShiftedBlocks.reverseIndex_lt hk))
    (fun k hk => by
      simpa only [ShiftedBlocks.reverseIndex_involutive hk] using
        hconst _ (ShiftedBlocks.reverseIndex_lt hk))
    (fun k hk => by
      simpa only [ShiftedBlocks.reverseIndex_involutive hk] using
        havg _ (ShiftedBlocks.reverseIndex_lt hk))
    (fun x hx k hk => by
      dsimp only [B,reverseMarkedValue,FiniteLineGrid.markedValue]
      split_ifs
      · exact hbeta x hx _ (ShiftedBlocks.reverseIndex_lt hk)
      · norm_num)
    (fun x hx k hk => hcompare x hx _ (ShiftedBlocks.reverseIndex_lt hk))
    (fun x hx => by simpa only [hsum] using hbudget x hx) hf'
  simpa only [hprod] using hi

/-- Actual pointwise drops can pay the doubled snapshot error. -/
theorem eventually_source_marked_drop_budget (C A_M : ℝ)
    (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ → ℝ) (count : ℕ) (marked : ℕ → Prop),
      ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L → n 0 ≤ L^C*N^2 →
        (∀ j, 0 ≤ n j) → Antitone n → n count ≤ L^A_M →
        (∀ j < count, marked j → L^A_M < n j) →
        (∑ j ∈ Finset.range count, if marked j then
          (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop n j else 0) ≤ 1 := by
  filter_upwards [eventually_source_marked_error C A_M hC hAM] with L hL
  intro n count marked N hN hlog hmass hn hanti hlast hmarked
  apply hL n (fun j => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop n j)
    (fun j => 2*pathDrop n j) count marked N hN hlog hmass hn hanti hlast hmarked
  · intro j hj hm
    linarith
  · intro j hj hm
    exact le_of_eq (by ring)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseMarkedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration on the actual first-terminal reverse grid. Literal cell
marking and the actual path mass discharge every stopping-budget premise. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem eventually_source_reverse_marked_integral (D C A_M : ℝ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length) 0 →
    ∀ (origin y Nmass : ℝ), 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (good : Set ℝ), MeasurableSet good →
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let level := ShiftedBlocks.reverseLevel σ count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      σ top (x,y+(T top).slope*x)
    let marked := fun j i => sourceMarkedCell
      (grid.cell (level (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
    ∀ beta : ℕ → ℝ → ℝ, (∀ j, Measurable (beta j)) →
      (∀ x ∈ grid.root ∩ good, ∀ j < count, 0 ≤ beta j x) →
    (∀ j < count, ∃ Γ : ℝ → ℝ, (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, grid.index (level (ShiftedBlocks.reverseIndex count j+1)) x =
        grid.index (level (ShiftedBlocks.reverseIndex count j+1)) z → Γ x = Γ z) ∧
      (∀ i : Fin (grid.branching^grid.depth),
        (∫ x in {x | grid.index (level (ShiftedBlocks.reverseIndex count j)) x = i},
          Γ x ∂volume.restrict grid.root) ≤
          (volume.restrict grid.root).real {x | grid.index (level (ShiftedBlocks.reverseIndex count j)) x = i}) ∧
      ∀ x ∈ grid.root ∩ good, reverseMarkedValue grid level count marked beta j x ≤
        Real.exp (reverseMarkedError grid level count marked
          (fun j x => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop (n x) j) j x)*Γ x) →
    (∀ x ∈ good, (∑ t ∈ tops, (T t).weight Kw D (x,y+(T top).slope*x)) ≤ L^C*Nmass^2) →
    IntegrableOn (good.indicator (fun x => (T top).weight Kw D (x,y+(T top).slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue grid level count marked beta j x)) grid.root volume ∧
    (∫ x in grid.root, good.indicator (fun x => (T top).weight Kw D (x,y+(T top).slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue grid level count marked beta j x) x) ≤
      Real.exp 1*Real.exp (2*D)*∫ x in grid.root, (T top).weight Kw D (x,y+(T top).slope*x) := by
  filter_upwards [eventually_source_reverse_cell_marking D A_M hD hAM,
    eventually_source_marked_drop_budget C A_M hC hAM,eventually_ge_atTop (1:ℝ)]
    with L hmark hbudget hL
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ top htop hzero
    origin y Nmass hN hlog good hgood
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  let level := ShiftedBlocks.reverseLevel σ count
  let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
    σ top (x,y+(T top).slope*x)
  let marked := fun j i => sourceMarkedCell
    (grid.cell (level (ShiftedBlocks.reverseIndex count j)) i)
    (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
  intro beta hbeta hnonneg hpredict hmass
  have hfactor : ∀ j : ℕ, ∃ Γ : ℝ → ℝ, j < count →
      (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, grid.index (level (ShiftedBlocks.reverseIndex count j+1)) x =
        grid.index (level (ShiftedBlocks.reverseIndex count j+1)) z → Γ x = Γ z) ∧
      (∀ i : Fin (grid.branching^grid.depth),
        (∫ x in {x | grid.index (level (ShiftedBlocks.reverseIndex count j)) x = i},
          Γ x ∂volume.restrict grid.root) ≤
          (volume.restrict grid.root).real {x | grid.index (level (ShiftedBlocks.reverseIndex count j)) x = i}) ∧
      ∀ x ∈ grid.root ∩ good, reverseMarkedValue grid level count marked beta j x ≤
        Real.exp (reverseMarkedError grid level count marked
          (fun j x => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop (n x) j) j x)*Γ x := by
    intro j
    by_cases hj : j < count
    · obtain ⟨Γ,hΓ⟩ := hpredict j hj
      exact ⟨Γ,fun _ => hΓ⟩
    · exact ⟨fun _ => 1,fun h => (hj h).elim⟩
  choose Γ hΓ using hfactor
  have hwp (t : ι) (z : ℝ × ℝ) : 0 ≤ (T t).weight Kw D z :=
    ((T t).weight_pos (zero_lt_one.trans_le hKw) D z).le
  have hlevels := sourceReverseLineGrid_levels g L origin hw σ hK count
  apply source_marked_factors_integral grid (T top) Kw D y 1 hKw hD
    (g.source_first_terminal_grid_width L origin hbranch hK σ hw (T top).length_pos hzero)
    level count hlevels.1 hlevels.2 good marked beta
    (fun j x => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop (n x) j) Γ
    (fun j hj => (hΓ j hj).1) (fun j hj => (hΓ j hj).2.1)
    (fun j hj => (hΓ j hj).2.2.1) hnonneg
    (fun x hx j hj => (hΓ j hj).2.2.2 x hx)
  · intro x hx
    apply hbudget (n x) count
      (fun j => marked j (grid.index (level (ShiftedBlocks.reverseIndex count j)) x).val)
      Nmass hN hlog
    · exact (g.shiftedPathMass_le_total tops _ _ cut _ hwp σ top _ 0).trans (hmass x hx.2)
    · exact g.shiftedPathMass_nonneg tops _ _ cut _ hwp σ top _
    · exact g.shiftedPathMass_antitone tops _ _ cut _
        (fun t _ => (div_pos hw (T t).length_pos).le) hwp hK σ top htop _
    · have hz := g.shiftedPathMass_terminal_zero tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z) σ top count
        (g.firstIneligibleShiftedBlock_spec cut (w/(T top).length)
          (div_pos hw (T top).length_pos) hK σ) (x,y+(T top).slope*x)
      exact hz.trans_le (Real.rpow_nonneg (by linarith : 0 ≤ L) _)
    · intro j hj hm
      let coarse := level (ShiftedBlocks.reverseIndex count j)
      have hc : coarse ≤ grid.depth := ShiftedBlocks.reverseLevel_le σ count _
      have hxcell : x ∈ grid.cell coarse (grid.index coarse x).val :=
        (grid.index_eq_iff_mem_cell hc hx.1 _).mp rfl
      exact (hmark ι g tops T w Kw hw hKw hbranch hwidth hK σ top origin y
        j hj (grid.index coarse x).val x hxcell).1 hm |>.1
  · apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ hgood
    apply Measurable.mul
    · exact ((T top).continuous_weight (zero_lt_one.trans_le hKw) D).measurable.comp (by fun_prop)
    · apply Finset.measurable_prod
      intro j _
      exact grid.measurable_markedValue _ _ _ (hbeta j)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTiledLineIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the source root-window estimates over the actual half-open tiling
of a line. Local integrability comes from the marked-window theorem; it
is not inferred from a vacuous Bochner-integral inequality. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem sourceLineTile_measurable (H : ℝ) (k : ℤ) : MeasurableSet (sourceLineTile H k) :=
  measurableSet_Ico

theorem sourceLineTile_mem (H : ℝ) (hH : 0 < H) (x : ℝ) :
    x ∈ sourceLineTile H ⌊x/H⌋ := by
  have hl := mul_le_mul_of_nonneg_left (Int.floor_le (x/H)) hH.le
  have hr := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x/H)) hH
  have heq : H*(x/H) = x := by field_simp
  rw [heq] at hl hr
  exact ⟨hl,hr⟩

theorem sourceLineTile_pairwise (H : ℝ) (hH : 0 < H) :
    Pairwise (fun k j : ℤ => Disjoint (sourceLineTile H k) (sourceLineTile H j)) := by
  intro k j hkj
  apply Set.disjoint_left.mpr
  intro x hk hj
  rcases lt_or_gt_of_ne hkj with h | h
  · have hij : (k:ℝ)+1 ≤ j := by exact_mod_cast (show k+1 ≤ j by omega)
    have hmul := mul_le_mul_of_nonneg_left hij hH.le
    exact (not_lt_of_ge (hmul.trans hj.1)) hk.2
  · have hji : (j:ℝ)+1 ≤ k := by exact_mod_cast (show j+1 ≤ k by omega)
    have hmul := mul_le_mul_of_nonneg_left hji hH.le
    exact (not_lt_of_ge (hmul.trans hk.1)) hj.2

theorem sourceLineTile_cover (H : ℝ) (hH : 0 < H) :
    (⋃ k : ℤ, sourceLineTile H k) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⌊x/H⌋,sourceLineTile_mem H hH x⟩

theorem finiteLineGrid_root_tile (g : FiniteLineGrid) (k : ℤ)
    (ho : g.origin = g.width*k) : g.root = sourceLineTile g.width k := by
  rw [FiniteLineGrid.root,ho,sourceLineTile]
  congr 1
  ring

/-- Summable control of the local integrals gives global integrability
and the same constant, with no dependence on the number of root windows. -/
theorem source_tiled_line_integral (H : ℝ) (hH : 0 < H) (f weight : ℝ → ℝ) (C : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hw : Integrable weight volume)
    (hlocal : ∀ k : ℤ, IntegrableOn f (sourceLineTile H k) volume ∧
      (∫ x in sourceLineTile H k, f x) ≤ C*∫ x in sourceLineTile H k, weight x) :
    Integrable f volume ∧ (∫ x, f x) ≤ C*∫ x, weight x :=
  integral_le_of_partition volume (sourceLineTile H) (sourceLineTile_measurable H)
    (sourceLineTile_pairwise H hH) (sourceLineTile_cover H hH) f weight hf hw
    (fun k => (hlocal k).1) (fun k => (hlocal k).2)

namespace SlopeBox

/-- Every actual top-weight slice is integrable, including along a slope
different from the top's own slope. Horizontal decay alone suffices. -/
theorem weight_line_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 1 < D)
    (s y : ℝ) : Integrable (fun x => T.weight K D (x,y+s*x)) volume := by
  have hbase : Integrable (fun x : ℝ => (1+‖x‖)^(-D)) volume :=
    integrable_one_add_norm (by simpa using hD)
  have hscale := (hbase.comp_div (mul_pos hK T.length_pos).ne').comp_sub_right T.x
  have hint := hscale.const_mul ((2:ℝ)^D)
  apply hint.mono' ((T.weight_continuous K D hK).comp
    (show Continuous (fun x : ℝ => (x,y+s*x)) by fun_prop)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simp only [Function.comp_apply,Real.norm_eq_abs]
  rw [abs_of_pos (T.weight_pos hK D _)]
  change (2:ℝ)^D*(1+T.radius (x,y+s*x)/K)^(-D) ≤
    (2:ℝ)^D*(1+‖(x-T.x)/(K*T.length)‖)^(-D)
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  have hnorm : ‖(x-T.x)/(K*T.length)‖ = |T.horizontal (x,y+s*x)|/K := by
    simp only [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hK,
      abs_of_pos T.length_pos,horizontal]
    ring
  rw [hnorm]
  apply add_le_add (le_refl (1:ℝ))
  apply div_le_div_of_nonneg_right _ hK.le
  exact le_add_of_nonneg_right (abs_nonneg (T.transverse (x,y+s*x)))

end SlopeBox

/-- Specialization to the original top weight removes the last auxiliary
integrability premise in the source's whole-line gluing step. -/
theorem source_top_tiled_line_integral (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 1 < D) (s y H C : ℝ) (hH : 0 < H)
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hlocal : ∀ k : ℤ, IntegrableOn f (sourceLineTile H k) volume ∧
      (∫ x in sourceLineTile H k, f x) ≤
        C*∫ x in sourceLineTile H k, T.weight K D (x,y+s*x)) :
    Integrable f volume ∧ (∫ x, f x) ≤ C*∫ x, T.weight K D (x,y+s*x) :=
  source_tiled_line_integral H hH f (fun x => T.weight K D (x,y+s*x)) C hf
    (T.weight_line_integrable hK hD s y) hlocal

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlaneIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original measurable source integrand passes from separately chosen
line predictors to the plane. No joint measurability of those auxiliary
predictors is required, and no global integrability of the integrand is
assumed. The final scale dependence is exactly the top area. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem source_plane_integral_of_tiled_lines (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 2 < D) (s H C : ℝ) (hH : 0 < H)
    (f : ℝ × ℝ → ℝ) (hfmeas : AEStronglyMeasurable f (volume.prod volume))
    (hf : ∀ z, 0 ≤ f z)
    (hlocal : ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      IntegrableOn (fun x => f (x,y+s*x)) (sourceLineTile H k) volume ∧
      (∫ x in sourceLineTile H k, f (x,y+s*x)) ≤
        C*∫ x in sourceLineTile H k, T.weight K D (x,y+s*x)) :
    Integrable f (volume.prod volume) ∧
      (∫ z, f z ∂volume.prod volume) ≤ C*∫ z, T.weight K D z ∂volume.prod volume := by
  have hlines : ∀ᵐ y : ℝ ∂volume,
      Integrable (fun x => f (x,y+s*x)) volume ∧
      (∫ x, f (x,y+s*x)) ≤ C*∫ x, T.weight K D (x,y+s*x) := by
    filter_upwards [hlocal] with y hy
    exact source_top_tiled_line_integral T hK (by linarith) s y H C hH
      (fun x => f (x,y+s*x)) (fun x => hf _) hy
  exact integral_le_of_slope_slices s f (T.weight K D) hfmeas hf
    (T.weight_integrable hK hD) (hlines.mono fun _ h => h.1) (hlines.mono fun _ h => h.2)

/-- The actual top-weight integral contributes precisely K² times its
area and a fixed profile integral depending only on D. -/
theorem source_plane_area_bound (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 2 < D) (s H C : ℝ) (hH : 0 < H)
    (f : ℝ × ℝ → ℝ) (hfmeas : AEStronglyMeasurable f (volume.prod volume))
    (hf : ∀ z, 0 ≤ f z)
    (hlocal : ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      IntegrableOn (fun x => f (x,y+s*x)) (sourceLineTile H k) volume ∧
      (∫ x in sourceLineTile H k, f (x,y+s*x)) ≤
        C*∫ x in sourceLineTile H k, T.weight K D (x,y+s*x)) :
    Integrable f (volume.prod volume) ∧
      (∫ z, f z ∂volume.prod volume) ≤
        (C*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2*T.length*T.width := by
  obtain ⟨hint,hbound⟩ := source_plane_integral_of_tiled_lines T hK hD s H C hH f hfmeas hf hlocal
  refine ⟨hint,?_⟩
  calc
    _ ≤ C*∫ z, T.weight K D z ∂volume.prod volume := hbound
    _ = _ := by rw [T.integral_weight hK D]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorPlaneIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original-selector marked bounds pass from each terminal line window
 to the plane. The measurable integrand is the original active path;
 the locally chosen marked factors need no joint measurability. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

/-- A measurable nonnegative integrand can be dominated only on the
 integration set. No comparison outside that set is needed. -/
theorem source_path_integral_transfer_on {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s good : Set X) (hs : MeasurableSet s)
    (w active marked : X → ℝ) (C P : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x ∈ good, 0 ≤ active x)
    (hmeas : AEStronglyMeasurable (good.indicator (fun x => w x*active x)) (μ.restrict s))
    (hint : IntegrableOn (good.indicator (fun x => w x*marked x)) s μ)
    (hbound : (∫ x in s, good.indicator (fun y => w y*marked y) x ∂μ) ≤
      P*(∫ x in s, w x ∂μ))
    (hpath : ∀ x ∈ s, x ∈ good → active x ≤ C*marked x) :
    IntegrableOn (good.indicator (fun x => w x*active x)) s μ ∧
      (∫ x in s, good.indicator (fun y => w y*active y) x ∂μ) ≤
        (C*P)*(∫ x in s, w x ∂μ) := by
  have hpos (x : X) : 0 ≤ good.indicator (fun y => w y*active y) x :=
    indicator_nonneg (fun y hy => mul_nonneg (hw y) (ha y hy)) x
  have hpoint : ∀ᵐ x ∂μ.restrict s,
      good.indicator (fun y => w y*active y) x ≤
        C*good.indicator (fun y => w y*marked y) x := by
    filter_upwards [ae_restrict_mem hs] with x hx
    by_cases hg : x ∈ good
    · simp only [indicator_of_mem hg]
      exact (mul_le_mul_of_nonneg_left (hpath x hx hg) (hw x)).trans_eq (by ring)
    · simp only [indicator_of_notMem hg,mul_zero,le_refl]
  have hi : IntegrableOn (good.indicator (fun x => w x*active x)) s μ :=
    (hint.const_mul C).mono' hmeas (hpoint.mono fun x hx => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hpos x)]
      exact hx)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x in s, C*good.indicator (fun y => w y*marked y) x ∂μ :=
      integral_mono_ae hi (hint.const_mul C) hpoint
    _ = C*(∫ x in s, good.indicator (fun y => w y*marked y) x ∂μ) :=
      integral_const_mul _ _
    _ ≤ C*(P*(∫ x in s, w x ∂μ)) := mul_le_mul_of_nonneg_left hbound hC
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceSupportedSelectorReversePathPredictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical packet prediction patched on the literal marked cells of
the single reverse grid. Snapshots are chosen on each fixed physical line. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_reverse_path_predictor
    (pProfile q Cmass Cweight Cfreq c0 A_M : ℝ) (Dweight Bslots : ℕ)
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
    ∀ (σ : Fin (SourceParameters.blockCount L)) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (eta : κ → ℝ), (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
    ∀ (top : ι), top ∈ tops → ∀ (origin y : ℝ) (good : Set ℝ),
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
      (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
      0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
    let count := g.firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let n := fun x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
    let beta := fun j x => g.sourceShiftedPathPrediction tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
      (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
      σ top (x,y+slope top*x) j
    let marked := fun j i => sourceMarkedCell
      (grid.cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
    (∀ x ∈ good, ∀ t ∈ tops, weight t (x,y+slope top*x) ≤ Cweight) →
    (∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t (x,y+slope top*x))) ≤ 3*L) →
    (∀ x ∈ good, (∑ t ∈ tops, weight t (x,y+slope top*x)) ≤ L^Cmass*Nmass) →
    (∀ x ∈ good, ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ z,
      |z-((y+slope top*x)-(T t).slope*x)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u x z‖+(T t).width*
        ‖covariantSignal (P t).frequency (fun k zz => (Q t).rawInterval (coeff t) 0 l u x zz k) z‖ ≤
          A*(weight t (x,y+slope top*x))^8) →
    (∀ j < count, ∀ x ∈ good, ∀ I : Finset ι, I ⊆ tops →
      (∀ t ∈ I, (T t).radius (x,y+slope top*x) ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, precision t ≤ g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) →
      (∀ t ∈ I, ∀ v ∈ I, t ≠ v →
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1)) ≤ |slope t-slope v|) →
      (I.card:ℝ) ≤ D/100) →
    ∀ j < count,
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, grid.index fine x = grid.index fine z → Γ x = Γ z) ∧
      (∀ i : Fin (grid.branching^grid.depth),
        (∫ x in {x | grid.index coarse x = i}, Γ x ∂volume.restrict grid.root) ≤
          (volume.restrict grid.root).real {x | grid.index coarse x = i}) ∧
      (∀ x ∈ grid.root, ¬marked j (grid.index coarse x).val → Γ x = 1) ∧
      ∀ x ∈ grid.root ∩ good, grid.markedValue coarse (marked j) (beta j) x ≤
        Real.exp (grid.markedError coarse (marked j)
          (fun x => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop (n x) j) x)*Γ x := by
  filter_upwards [eventually_source_supported_selector_path_predictor pProfile q Cmass Cweight Cfreq c0
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0,
    eventually_source_reverse_drop_comparison (Dweight:ℝ) (by positivity)] with L hpred hdrop
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN eta hetaLo hetaHi hPeta top htop origin y good
  dsimp only
  intro hweight htotal hmass hconc hcount
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
  let count := g.firstIneligibleShiftedBlock cut (precision top)
    (div_pos hw (T top).length_pos) hKb σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  let n := fun x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
  let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
    (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
    0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
  let beta := fun j x => g.sourceShiftedPathPrediction tops slope precision cut weight
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
    (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
    σ top (x,y+slope top*x) j
  let marked := fun j i => sourceMarkedCell
    (grid.cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
    (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
  intro j hj
  let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
  let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
  apply grid.exists_marked_prediction_from_snapshots coarse fine
    (ShiftedBlocks.reverseLevel_monotone hKb σ count (Nat.le_succ _))
    (ShiftedBlocks.reverseLevel_le σ count _) (marked j) good (beta j)
    (fun x => pathDrop (n x) j)
    (SourceParameters.step L^(-(1/32:ℝ)))
    (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
  · intro i hi _hm x₀ hx₀
    let win := grid.lineWindow coarse i (fine-coarse)
    have hxwin : x₀ ∈ win.root := by
      change x₀ ∈ (grid.lineWindow coarse i (fine-coarse)).root
      rw [FiniteLineGrid.lineWindow_root]
      exact hx₀.1
    have hwin : win = sourceLineGrid L win.origin
        (sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)))
        (ShiftedBlocks.endpoint σ (j+1)-ShiftedBlocks.endpoint σ j)
        (sourceLineScale_pos g L hw (ShiftedBlocks.endpoint σ (j+1))) := by
      simpa only [FiniteLineGrid.atSnapshot,sub_zero] using
        source_reverse_snapshot_window g L origin hw σ hKb hj hbranch i 0
    have he := g.eligible_before_firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb σ hj
    have hwp (t : ι) (z : ℝ × ℝ) : 0 < weight t z :=
      (T t).weight_pos (zero_lt_one.trans_le hKw) _ z
    have hu : 0 ≤ pathDrop (n x₀) j := pathDrop_nonnegative (n x₀) j
      (g.shiftedPathMass_pos tops slope precision cut weight hwp σ top htop _ j he)
      (g.shiftedPathMass_antitone tops slope precision cut weight
        (fun t _ => (div_pos hw (T t).length_pos).le) (fun t z => (hwp t z).le)
        hKb σ top htop _ (Nat.le_succ j))
    have hmass₀ := (g.mass_le_total tops slope precision cut weight
      (fun t z => (hwp t z).le) (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) (x₀,y+slope top*x₀)).trans
      (hmass x₀ hx₀.2)
    obtain ⟨F,_hFm,hFi,hFp,hFa,hFc,hFb⟩ := hpred ι κ tops T N Label Item P hslots hP
      alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w hw hbranch hwidth
      hlength hzero hKb hKbL σ j M hM hMmax phase a Z A maskExponent D Nmass
      ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask hD hNmass hlogN
      (x₀,y+slope top*x₀) eta hetaLo hetaHi hPeta (hweight x₀ hx₀.2)
      (htotal x₀ hx₀.2) (hconc x₀ hx₀.2)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) (slope top) win.origin
      (pathDrop (n x₀) j) rfl top htop rfl he hu hmass₀ le_rfl
      hxwin.1 (by rw [← hwin]; exact hxwin.2.le) (hcount j hj x₀ hx₀.2)
    rw [← hwin] at hFi hFa hFc hFb
    have hlen := ShiftedBlocks.reverseLevel_block_length hKb σ hj
    refine ⟨F,hFp,hFi,hFa,?_,?_⟩
    · intro x z hxz
      change win.index (fine-coarse) x = win.index (fine-coarse) z at hxz
      exact hFc x z (by simpa only [show fine-coarse = _ from hlen] using hxz)
    · intro x hx
      have hxx : x ∈ win.root := by
        change x ∈ (grid.lineWindow coarse i (fine-coarse)).root
        rw [FiniteLineGrid.lineWindow_root]
        exact hx.1
      have hb := hFb x hxx
      have hpoint : y+slope top*x₀+slope top*(x-x₀) = y+slope top*x := by ring
      simpa only [beta,sourceShiftedPathPrediction,sourceBlockPrediction,hpoint] using hb
  · intro i _hi _hm x₀ hx₀ x hx
    exact (hdrop ι g tops T w Kw hw hKw hbranch hwidth hKb σ top htop origin y
      j hj i x hx.1 x₀ hx₀.1).1

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedSelectorMarkedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original masked physical packet predictor has a uniform marked
path integral on each terminal root interval. All cell factors and their
normalizations are constructed from the physical data. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_marked_integral
    (pProfile q Cmass Cweight Cfreq c0 A_M : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0)
    (hAM : 0 ≤ A_M) :
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
    ∀ (σ : Fin (SourceParameters.blockCount L)) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (eta : κ → ℝ), (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
    ∀ (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length) 0 →
    ∀ (origin y : ℝ) (good : Set ℝ), MeasurableSet good →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
      (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
      0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
    let count := g.firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let n := fun x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
    let beta := fun j x => g.sourceShiftedPathPrediction tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
      (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
      σ top (x,y+slope top*x) j
    let marked := fun j i => sourceMarkedCell
      (grid.cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
    (∀ x ∈ good, ∀ t ∈ tops, weight t (x,y+slope top*x) ≤ Cweight) →
    (∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t (x,y+slope top*x))) ≤ 3*L) →
    (∀ x ∈ good, (∑ t ∈ tops, weight t (x,y+slope top*x)) ≤ L^Cmass*Nmass) →
    (∀ x ∈ good, ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ z,
      |z-((y+slope top*x)-(T t).slope*x)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u x z‖+(T t).width*
        ‖covariantSignal (P t).frequency (fun k zz => (Q t).rawInterval (coeff t) 0 l u x zz k) z‖ ≤
          A*(weight t (x,y+slope top*x))^8) →
    (∀ j < count, ∀ x ∈ good, ∀ I : Finset ι, I ⊆ tops →
      (∀ t ∈ I, (T t).radius (x,y+slope top*x) ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, precision t ≤ g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) →
      (∀ t ∈ I, ∀ v ∈ I, t ≠ v →
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1)) ≤ |slope t-slope v|) →
      (I.card:ℝ) ≤ D/100) →
    IntegrableOn (good.indicator (fun x => weight top (x,y+slope top*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue grid (ShiftedBlocks.reverseLevel σ count)
        count marked beta j x)) grid.root volume ∧
    (∫ x in grid.root, good.indicator (fun x => weight top (x,y+slope top*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue grid (ShiftedBlocks.reverseLevel σ count)
        count marked beta j x) x) ≤
      Real.exp 1*Real.exp (2*(Dweight:ℝ))*∫ x in grid.root, weight top (x,y+slope top*x) := by
  filter_upwards [eventually_source_supported_selector_reverse_path_predictor pProfile q Cmass Cweight Cfreq c0 A_M
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0,
    eventually_source_reverse_marked_integral (Dweight:ℝ) Cmass A_M (by positivity) hCmass hAM,
    eventually_ge_atTop (1:ℝ)] with L hpred hint hL
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN eta hetaLo hetaHi hPeta top htop htop0 origin y good hgood
  dsimp only
  intro hweight htotal hmass hconc hcount
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
  let count := g.firstIneligibleShiftedBlock cut (precision top)
    (div_pos hw (T top).length_pos) hKb σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  let n := fun x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
  let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
    (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
    0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
  let beta := fun j x => g.sourceShiftedPathPrediction tops slope precision cut weight
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
    (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
    σ top (x,y+slope top*x) j
  have hvv (p : ι × Fin N) : Measurable (fun zz => value zz p) :=
    ((Q p.1).masked_rawBand_continuous (coeff p.1) (T p.1) L maskExponent 0 p.2).measurable
  have hwm (t : ι) : Measurable (weight t) :=
    ((T t).continuous_weight (zero_lt_one.trans_le hKw) _).measurable
  have hwp (t : ι) (z : ℝ × ℝ) : 0 < weight t z :=
    (T t).weight_pos (zero_lt_one.trans_le hKw) _ z
  have hbeta (j : ℕ) : Measurable (beta j) :=
    (g.sourceShiftedPathPrediction_measurable tops slope precision cut weight hwm
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      value hvv (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L)
      (phaseMu D (Real.sqrt L)) σ top j).comp (by fun_prop)
  have hlogroot : Real.log (Real.sqrt Nmass) ≤ 2*L := by
    rw [Real.log_sqrt hNmass.le]
    linarith
  apply hint ι g tops T w Kw hw hKw hbranch hwidth hKb σ top htop htop0 origin y
    (Real.sqrt Nmass) (Real.sqrt_pos.mpr hNmass) hlogroot good hgood beta hbeta
  · intro x _hx j hj
    have he := g.eligible_before_firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb σ hj
    exact (g.sourceShiftedPathPrediction_pos tops slope precision cut weight hwp
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      value (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L)
      (phaseMu D (Real.sqrt L)) σ top htop (x,y+slope top*x) j he).le
  · intro j hj
    obtain ⟨Γ,_hmeas,hpos,hconst,havg,_hone,hcomp⟩ := hpred ι κ tops T N Label Item P
      hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w hw hbranch hwidth
      hlength hzero hKb hKbL σ M hM hMmax phase a Z A maskExponent D Nmass
      ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask hD hNmass hlogN eta hetaLo
      hetaHi hPeta top htop origin y good hweight htotal hmass hconc hcount j hj
    exact ⟨Γ,hpos,hconst,havg,hcomp⟩
  · intro x hx
    simpa only [Real.sq_sqrt hNmass.le] using hmass x hx

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedSelectorPlaneIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original-selector marked bounds pass from each terminal line window
 to the plane. The measurable integrand is the original active path;
 the locally chosen marked factors need no joint measurability. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

namespace AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_plane_integral_oai
    (pProfile q Cmass Cweight Cfreq c0 A_M : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0)
    (hAM : 0 ≤ A_M) (hDweight : 2 < (Dweight:ℝ)) :
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
    ∀ (σ : Fin (SourceParameters.blockCount L)) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (eta : κ → ℝ), (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
    ∀ (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length) 0 →
    ∀ (good : Set (ℝ×ℝ)), MeasurableSet good →
    ∀ (active : ℝ×ℝ → ℝ), Measurable active →
      (∀ z ∈ good, 0 ≤ active z) →
    ∀ (Cpath : ℝ), 0 ≤ Cpath →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
      (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
      0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
    let count := g.firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb σ
    let H := sourceLineScale g L w (ShiftedBlocks.endpoint σ count)
    let grid := fun k : ℤ => sourceReverseLineGrid g L (H*k) hw σ count
    let n := fun y x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
    let beta := fun y j x => g.sourceShiftedPathPrediction tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
      (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
      σ top (x,y+slope top*x) j
    let marked := fun k y j i => sourceMarkedCell
      ((grid k).cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n y x j) (fun x => n y x j-n y x (j+1)) (L^A_M)
    (∀ z ∈ good, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ good, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ good, ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 yy‖+(T t).width*
        ‖covariantSignal (P t).frequency (fun k zz => (Q t).rawInterval (coeff t) 0 l u z.1 zz k) yy‖ ≤
          A*(weight t z)^8) →
    (∀ j < count, ∀ z ∈ good, ∀ I : Finset ι, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, precision t ≤ g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) →
      (∀ t ∈ I, ∀ v ∈ I, t ≠ v →
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1)) ≤ |slope t-slope v|) →
      (I.card:ℝ) ≤ D/100) →
    (∀ (k : ℤ) (y x : ℝ), x ∈ (grid k).root → (x,y+slope top*x) ∈ good →
      active (x,y+slope top*x) ≤ Cpath*
        ∏ j ∈ Finset.range count, reverseMarkedValue (grid k) (ShiftedBlocks.reverseLevel σ count)
          count (marked k y) (beta y) j x) →
    Integrable (good.indicator (fun z => weight top z*active z)) (volume.prod volume) ∧
      (∫ z, good.indicator (fun z => weight top z*active z) z ∂volume.prod volume) ≤
        ((Cpath*(Real.exp 1*Real.exp (2*(Dweight:ℝ))))*
          (2^(Dweight:ℝ)*∫ z, topProfile (Dweight:ℝ) z ∂volume.prod volume))*
            Kw^2*(T top).length*(T top).width := by
  filter_upwards [eventually_source_supported_selector_marked_integral pProfile q Cmass Cweight Cfreq c0 A_M
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0 hAM] with L hmarked
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN eta hetaLo hetaHi hPeta top htop htop0 good hgood active hactive
    hactive0 Cpath hCpath
  dsimp only
  intro hweight htotal hmass hconc hcount hpath
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
  let count := g.firstIneligibleShiftedBlock cut (precision top)
    (div_pos hw (T top).length_pos) hKb σ
  let H := sourceLineScale g L w (ShiftedBlocks.endpoint σ count)
  let grid := fun k : ℤ => sourceReverseLineGrid g L (H*k) hw σ count
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
  let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
    (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
    0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
  let n := fun y x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
  let beta := fun y j x => g.sourceShiftedPathPrediction tops slope precision cut weight
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
    (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
    σ top (x,y+slope top*x) j
  let marked := fun k y j i => sourceMarkedCell
    ((grid k).cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
    (fun x => n y x j) (fun x => n y x j-n y x (j+1)) (L^A_M)
  let f := good.indicator (fun z => weight top z*active z)
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hfmeas : Measurable f :=
    (((T top).continuous_weight hKw0 _).measurable.mul hactive).indicator hgood
  have hf0 (z : ℝ×ℝ) : 0 ≤ f z :=
    indicator_nonneg (fun z hz => mul_nonneg ((T top).weight_pos hKw0 _ z).le
      (hactive0 z hz)) z
  apply source_plane_area_bound (T top) hKw0 hDweight (slope top) H
    (Cpath*(Real.exp 1*Real.exp (2*(Dweight:ℝ))))
    (sourceLineScale_pos g L hw _) f hfmeas.aestronglyMeasurable hf0
  apply Filter.Eventually.of_forall
  intro y k
  let goodLine : Set ℝ := {x | (x,y+slope top*x) ∈ good}
  have hgoodLine : MeasurableSet goodLine := hgood.preimage (by fun_prop)
  have hroot : (grid k).root = sourceLineTile H k :=
    finiteLineGrid_root_tile (grid k) k rfl
  have hl := hmarked ι κ tops T N Label Item P hslots hP alt hAlt Kw hKw hgeom
    selector hselector hselector1 v hv test htest htest1 g w hw hbranch hwidth hlength hzero
    hKb hKbL σ M hM hMmax phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase
    hother hreal hA0 hAq hmask hD hNmass hlogN eta hetaLo hetaHi hPeta top htop htop0
    (H*k) y goodLine hgoodLine
    (fun x hx => hweight _ hx) (fun x hx => htotal _ hx) (fun x hx => hmass _ hx)
    (fun x hx => hconc _ hx) (fun j hj x hx => hcount j hj _ hx)
  change IntegrableOn (goodLine.indicator (fun x => weight top (x,y+slope top*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue (grid k) (ShiftedBlocks.reverseLevel σ count)
        count (marked k y) (beta y) j x)) (grid k).root volume ∧ _ at hl
  rw [hroot] at hl
  have ha : Measurable (fun x => active (x,y+slope top*x)) := hactive.comp (by fun_prop)
  have hwmeas : Measurable (fun x => weight top (x,y+slope top*x)) :=
    (T top).continuous_weight hKw0 (Dweight:ℝ) |>.comp (by fun_prop) |>.measurable
  have ht := source_path_integral_transfer_on volume (sourceLineTile H k) goodLine
    (sourceLineTile_measurable H k) (fun x => weight top (x,y+slope top*x))
    (fun x => active (x,y+slope top*x))
    (fun x => ∏ j ∈ Finset.range count,
      reverseMarkedValue (grid k) (ShiftedBlocks.reverseLevel σ count)
        count (marked k y) (beta y) j x)
    Cpath (Real.exp 1*Real.exp (2*(Dweight:ℝ))) hCpath
    (fun x => ((T top).weight_pos hKw0 _ _).le)
    (fun x hx => hactive0 _ hx)
    ((hwmeas.mul ha).indicator hgoodLine).aestronglyMeasurable
    hl.1 hl.2 (fun x hx hxgood => hpath k y x (hroot.symm ▸ hx) hxgood)
  have hindicator : goodLine.indicator (fun x =>
      weight top (x,y+slope top*x)*active (x,y+slope top*x)) =
        fun x => f (x,y+slope top*x) := by
    funext x
    rfl
  rw [hindicator] at ht
  exact ht

end AngularGrid
end LipschitzHilbert

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_plane_integral_oai := @OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_plane_integral_oai
