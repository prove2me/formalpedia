-- Prove2me | solution 1 for OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:34:46.67244+00:00
-- url     : https://prove2.me/submissions/88ddae85-5966-44ff-8167-9a5ac58e3eed

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_eventually_physical_reference_good_spectral_tail

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic variation and its dimension-free Euclidean comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : 0 ≤ finiteCubicVariation F N := by
  classical
  apply Finset.le_sup'_of_le (f := fun p : Fin (N + 1) → Fin (N + 1) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
    (Finset.mem_univ (fun _ => 0))
  simp

theorem partition_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ≤
      finiteCubicVariation F N := by
  classical
  simpa only [finiteCubicVariation, ite_eq_left hp] using
    (Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
      (Finset.mem_univ p))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationSubsequence
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling partial sums at increasing times cannot increase variation. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem finiteCubicVariation_comp_le {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (q : ℕ → ℕ) (hq : Monotone q) (hN : q N ≤ N) :
    finiteCubicVariation (fun n => F (q n)) N ≤ finiteCubicVariation F N := by
  classical
  unfold finiteCubicVariation
  apply Finset.sup'_le
  intro p _
  by_cases hp : Monotone p
  · rw [ite_eq_left hp]
    let r : Fin (N + 1) → Fin (N + 1) := fun k =>
      ⟨q (p k).val, by have := (hq (show (p k).val ≤ N by omega)).trans hN; omega⟩
    have hr : Monotone r := by
      intro i j hij
      exact hq (hp hij)
    exact partition_le_finiteCubicVariation F N r hr
  · rw [ite_eq_right hp]
    exact finiteCubicVariation_nonneg F N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FiniteLineGrid
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite line partitions, nested at an integer branching ratio. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

namespace FiniteLineGrid

attribute [local instance] Classical.propDecidable

/-- Two points of one finer cell differ by at most its mesh width. -/
theorem same_index_distance (g : FiniteLineGrid) {level : ℕ} (hlevel : level ≤ g.depth)
    {x y : ℝ} (hx : x ∈ g.root) (hy : y ∈ g.root)
    (hxy : g.index level x = g.index level y) :
    |x - y| ≤ g.width / (g.branching : ℝ) ^ level := by
  have hG : 0 < (g.branching : ℝ) := by exact_mod_cast g.branching_pos
  have hp : 0 < (g.branching : ℝ) ^ level := pow_pos hG _
  have hxn : 0 ≤ ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hx.1) g.width_pos.le) hp.le
  have hyn : 0 ≤ ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hy.1) g.width_pos.le) hp.le
  have hf : ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ =
      ⌊((y - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ := by
    have h := congrArg Fin.val hxy
    simpa only [index, Nat.min_eq_left hlevel, rawIndex, ite_eq_left hx, ite_eq_left hy] using h
  have hxlo := Nat.floor_le hxn
  have hylo := Nat.floor_le hyn
  have hxhi := Nat.lt_floor_add_one (((x - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  have hyhi := Nat.lt_floor_add_one (((y - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  rw [hf] at hxlo hxhi
  have hnorm : |((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level =
      (x - y) * ((g.branching : ℝ) ^ level / g.width) := by ring
  rw [heq, abs_mul, abs_of_pos (div_pos hp g.width_pos)] at hnorm
  apply (le_div_iff₀ hp).mpr
  have h := mul_le_mul_of_nonneg_right hnorm g.width_pos.le
  calc
    |x - y| * (g.branching : ℝ) ^ level =
        (|x - y| * ((g.branching : ℝ) ^ level / g.width)) * g.width := by
          field_simp [g.width_pos.ne']
    _ ≤ 1 * g.width := h
    _ = g.width := one_mul _

end FiniteLineGrid
end LipschitzHilbert

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridMartingale
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The martingale of actual nested line-cell averages. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem average_martingale (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) : Martingale (g.average μ f) g.filtration μ :=
  martingale_condExp f g.filtration μ

theorem average_constant (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ)
    (n : ℕ) {x y : ℝ} (hxy : g.index n x = g.index n y) :
    g.average μ f n x = g.average μ f n y := by
  exact (show StronglyMeasurable[g.filtration n] (g.average μ f n) from
    stronglyMeasurable_condExp).factorsThrough hxy

/-- Conditional expectation is the actual integral average on every
positive-measure index fiber, pointwise for its canonical representative. -/
theorem average_eq_fiber_mean (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (n : ℕ) (x : ℝ)
    (hpos : μ.real {y | g.index n y = g.index n x} ≠ 0) :
    g.average μ f n x =
      (∫ y in {y | g.index n y = g.index n x}, f y ∂μ) /
        μ.real {y | g.index n y = g.index n x} := by
  let s := {y | g.index n y = g.index n x}
  have hs : MeasurableSet[g.filtration n] s :=
    (comap_measurable (g.index n)) (measurableSet_singleton _)
  have hsambient : MeasurableSet s := (g.filtration.le n) _ hs
  apply (eq_div_iff hpos).mpr
  calc
    g.average μ f n x * μ.real s = ∫ y in s, g.average μ f n x ∂μ := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ = ∫ y in s, g.average μ f n y ∂μ := by
      apply setIntegral_congr_fun hsambient
      intro y hy
      exact g.average_constant μ f n hy.symm
    _ = ∫ y in s, f y ∂μ := setIntegral_condExp (g.filtration.le n) hf hs

theorem lineMeasure_fiber (g : FiniteLineGrid) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    g.lineMeasure {x | (g.index level x).val = i} = ENNReal.ofReal (g.meshWidth level) := by
  rw [lineMeasure, Measure.restrict_apply]
  · have heq : {x | (g.index level x).val = i} ∩ g.root = g.cell level i := by
      rw [inter_comm]
      exact g.index_fiber_inter_root hl hi
    rw [heq, cell, Real.volume_Ico]
    congr 1
    ring
  · exact ((measurable_of_countable (fun j : Fin (g.branching ^ g.depth) => j.val)).comp
      (g.measurable_index level)) (measurableSet_singleton i)

/-- On a nonempty mesh interval, the canonical dyadic conditional
expectation is exactly the usual Lebesgue average over that interval. -/
theorem average_eq_cell_mean (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure f level x =
      (∫ y in g.cell level i, f y) / g.meshWidth level := by
  have hix : (g.index level x).val = i :=
    (g.index_eq_iff_mem_cell hl (g.cell_subset_root level hi hx) i).mpr hx
  have hfiber : {y | g.index level y = g.index level x} =
      {y | (g.index level y).val = i} := by
    ext y
    simp only [Fin.ext_iff, hix, Set.mem_ofPred_eq]
  have hmass : g.lineMeasure.real {y | g.index level y = g.index level x} =
      g.meshWidth level := by
    rw [measureReal_def, hfiber, g.lineMeasure_fiber hl hi,
      ENNReal.toReal_ofReal (g.meshWidth_pos level).le]
  rw [g.average_eq_fiber_mean g.lineMeasure f hf level x
    (by rw [hmass]; exact (g.meshWidth_pos level).ne'), hmass]
  congr 1
  rw [lineMeasure, Measure.restrict_restrict (g.measurable_index_fiber level _)]
  congr 1
  rw [hfiber, inter_comm]
  congr 1
  exact g.index_fiber_inter_root hl hi

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interval energy estimate needed for the low-frequency part of
the smooth-convolution versus cell-average comparison. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem norm_sub_mean_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (hf : Integrable f μ)
    (hm : 0 < μ.real univ) (v : E) (B : ℝ)
    (hbound : ∀ᵐ y ∂μ, ‖v - f y‖ ≤ B) :
    ‖v - (μ.real univ)⁻¹ • ∫ y, f y ∂μ‖ ≤ B := by
  have heq : v - (μ.real univ)⁻¹ • ∫ y, f y ∂μ =
      (μ.real univ)⁻¹ • ∫ y, (v - f y) ∂μ := by
    rw [integral_sub (integrable_const v) hf, integral_const,
      smul_sub, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ (μ.real univ)⁻¹ * (B * μ.real univ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hbound) (inv_nonneg.mpr hm.le)
    _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridPoincare
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-frequency averaging errors on the actual nested line grid. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem index_lt_level (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) (x : ℝ) :
    (g.index level x).val < g.branching ^ level := by
  let h : FiniteLineGrid := { g with depth := level }
  have ht := h.rawIndex_lt (le_refl level) x
  change g.rawIndex level x < g.branching ^ level at ht
  simpa only [index, Nat.min_eq_left hl] using ht

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxPolynomialWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial localization lower bound on a reference interval, with
the horizontal box offset retained explicitly. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem box_polynomial_base (u r k x : ℝ) (hr : 0 < r) (hx : |x - u| ≤ r) :
    (1 + |k|) ^ 2 / 8 ≤ 1 + (x - (u + r * k)) ^ 2 / r ^ 2 := by
  let v := (x - (u + r * k)) / r
  have hunit : |(x - u) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hx
  have heq : k = (x - u) / r - v := by
    dsimp [v]
    field_simp
    ring
  have hk : |k| ≤ 1 + |v| := by
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add hunit le_rfl)
  have hk2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |k|)
    (add_le_add (le_rfl : (1 : ℝ) ≤ 1) hk) 2
  have habs : |v| ^ 2 = v ^ 2 := sq_abs v
  have hs := sq_nonneg (|v| - 2)
  have hv : 1 + (x - (u + r * k)) ^ 2 / r ^ 2 = 1 + v ^ 2 := by
    dsimp [v]
    rw [div_pow]
  rw [hv]
  nlinarith

theorem box_polynomial_weight (u r k x : ℝ) (q : ℕ)
    (hr : 0 < r) (hx : |x - u| ≤ r) :
    ((1 + |k|) ^ 2 / 8) ^ q ≤ polynomialWeight (u + r * k) r q x := by
  exact pow_le_pow_left₀ (by positivity) (box_polynomial_base u r k x hr hx) q

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TailLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict tail bounds pass to almost-everywhere limits. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LipschitzHilbert

theorem strict_tail_bound_of_ae_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : ℕ → X → ℝ) (g : X → ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (t C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, μ.real {x | t < f n x} ≤ C) :
    μ.real {x | t < g x} ≤ C := by
  let S := fun m : ℕ => {x | ∀ n ≥ m, t < f n x}
  have hmono : Monotone S := by
    intro m n hmn x hx i hi
    exact hx i (hmn.trans hi)
  have hsub : ∀ᵐ x ∂μ, x ∈ {x | t < g x} → x ∈ ⋃ m, S m := by
    filter_upwards [hlim] with x hx ht
    have h := (tendsto_order.mp hx).1 t ht
    obtain ⟨m,hm⟩ := eventually_atTop.mp h
    exact mem_iUnion.mpr ⟨m,hm⟩
  have hmass : μ {x | t < g x} ≤ ENNReal.ofReal C := by
    calc
      _ ≤ μ (⋃ m, S m) := measure_mono_ae hsub
      _ = ⨆ m, μ (S m) := hmono.directed_le.measure_iUnion
      _ ≤ ENNReal.ofReal C := by
        apply iSup_le
        intro m
        have hle := ENNReal.ofReal_le_ofReal (hbound m)
        rw [ofReal_measureReal] at hle
        exact (measure_mono (show S m ⊆ {x | t < f m x} from fun _ hx => hx m le_rfl)).trans hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [measureReal_def, ENNReal.toReal_ofReal hC] using hreal

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FirstExceed
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint first-crossing events for a finite scalar process. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem firstExceed_disjoint {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) :
    Pairwise (fun i j => Disjoint (firstExceed U lambda i) (firstExceed U lambda j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hxj.2 i h)) hxi.1
  · exact (not_lt_of_ge (hxi.2 j h)) hxj.1

theorem firstExceed_union {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ) :
    (⋃ i : Fin (N + 1), firstExceed U lambda i.val) = finiteMaxEvent U lambda N := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, by omega, hi.1⟩
  · rintro ⟨i, hi, hUi⟩
    have hex : ∃ n, lambda < U n x := ⟨i,hUi⟩
    let n := Nat.find hex
    have hn : n ≤ i := Nat.find_min' hex hUi
    apply mem_iUnion.mpr
    refine ⟨⟨n,by omega⟩, Nat.find_spec hex, ?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)

theorem measurableSet_firstExceed {X : Type*} [MeasurableSpace X]
    (U : ℕ → X → ℝ) (lambda : ℝ) (n : ℕ) (hU : ∀ i ≤ n, Measurable (U i)) :
    MeasurableSet (firstExceed U lambda n) := by
  unfold firstExceed
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_lt measurable_const (hU n le_rfl)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
      measurableSet_le (hU i hi.le) measurable_const)

theorem firstExceed_measure_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ)
    (hU : ∀ i ≤ N, Measurable (U i)) :
    (∑ i : Fin (N + 1), μ.real (firstExceed U lambda i.val)) =
      μ.real (finiteMaxEvent U lambda N) := by
  rw [← firstExceed_union]
  symm
  apply measureReal_iUnion_fintype
  · intro i j hij
    exact firstExceed_disjoint U lambda (fun h => hij (Fin.ext h))
  · intro i
    exact measurableSet_firstExceed U lambda i (fun j hj => hU j (by omega))
  · intro i
    exact measure_ne_top μ _

theorem firstExceed_norm_overshoot {X E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → E) (x : X) {lambda D : ℝ} (hlambda : 0 ≤ lambda)
    (n : ℕ) (hjump : ∀ i < n, ‖F (i + 1) x - F i x‖ ≤ D)
    (hx : x ∈ firstExceed (fun i y => ‖F i y - F 0 y‖) lambda n) :
    ‖F n x - F 0 x‖ ≤ lambda + D := by
  have hn : n ≠ 0 := by
    intro hn
    have hh := hx.1
    simp only [hn, sub_self, norm_zero] at hh
    linarith
  have hp := hx.2 (n - 1) (by omega)
  have hj := hjump (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at hj
  exact (norm_sub_le_norm_sub_add_norm_sub (F n x) (F (n - 1) x) (F 0 x)).trans
    (by linarith)

theorem firstExceed_large_subset {X E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → E) (N n : ℕ) (hn : n ≤ N) {lambda D δ : ℝ}
    (hlambda : 0 ≤ lambda) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) :
    finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) (lambda + D + δ) N ∩
        firstExceed (fun i x => ‖F i x - F 0 x‖) lambda n ⊆
      {x | ∃ i ≤ N - n, δ ≤ ‖F (n + i) x - F n x‖} ∩
        firstExceed (fun i x => ‖F i x - F 0 x‖) lambda n := by
  rintro x ⟨⟨k,hk,hlarge⟩,hx⟩
  refine ⟨?_,hx⟩
  have hkn : n ≤ k := by
    by_contra h
    have hb := hx.2 k (lt_of_not_ge h)
    linarith
  have hstop := firstExceed_norm_overshoot F x hlambda n
    (fun i hi => hjump i (hi.trans_le hn) x) hx
  refine ⟨k - n, by omega, ?_⟩
  rw [show n + (k - n) = k by omega]
  have htri := norm_sub_le_norm_sub_add_norm_sub (F k x) (F n x) (F 0 x)
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleLocalMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and time shift for a martingale, and the local weak-L1
maximal estimate used in the dyadic John--Nirenberg stopping argument. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

omit [IsFiniteMeasure μ] in
theorem martingale_timeShift (hF : Martingale F ℱ μ) (n : ℕ) :
    Martingale (fun i => F (n + i)) (timeShiftFiltration ℱ n) μ :=
  ⟨fun i => hF.stronglyMeasurable (n + i),
    fun _i _j hij => hF.condExp_ae_eq (Nat.add_le_add_left hij n)⟩

theorem martingale_restrict_initial (hF : Martingale F ℱ μ)
    {s : Set X} (hs : MeasurableSet[ℱ 0] s) : Martingale F ℱ (μ.restrict s) := by
  apply martingale_of_setIntegral_eq_succ hF.stronglyAdapted
    (fun i => (hF.integrable i).integrableOn)
  intro i t ht
  rw [Measure.restrict_restrict (ℱ.le i t ht)]
  exact hF.setIntegral_eq (Nat.le_succ i) (ht.inter (ℱ.mono (Nat.zero_le i) _ hs))

omit [IsFiniteMeasure μ] in
theorem martingale_abs (hF : Martingale F ℱ μ) :
    Submartingale (fun i x => |F i x|) ℱ μ := by
  have heq : (fun i x => |F i x|) = F ⊔ -F := by
    funext i x
    exact abs_eq_max_neg
  rw [heq]
  exact hF.submartingale.sup hF.neg.submartingale

theorem martingale_maximal_L1 (hF : Martingale F ℱ μ)
    {lambda : ℝ} (hlambda : 0 < lambda) (N : ℕ) :
    μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤ lambda⁻¹ * ∫ x, |F N x| ∂μ := by
  have hmax := maximal_ineq (martingale_abs hF) (fun i x => abs_nonneg (F i x))
    (ε := ⟨lambda,hlambda.le⟩) N
  change _ * μ {x | lambda ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun i => |F i x|)} ≤
    ENNReal.ofReal (∫ x in {x | lambda ≤ (Finset.range (N + 1)).sup'
      Finset.nonempty_range_add_one (fun i => |F i x|)}, |F N x| ∂μ) at hmax
  have hevent : {x | lambda ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun i => |F i x|)} = {x | ∃ i ≤ N, lambda ≤ |F i x|} := by
    ext x
    simp only [mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
  rw [hevent] at hmax
  have hwhole : (∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ) ≤
      ∫ x, |F N x| ∂μ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => abs_nonneg (F N x)) (hF.integrable N).abs
  have hsetnonneg : 0 ≤ ∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ :=
    integral_nonneg (fun x => abs_nonneg (F N x))
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  have hreal : lambda * μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤
      ∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hsetnonneg] at ht
    exact ht
  have hfinal : μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤
      (∫ x, |F N x| ∂μ) / lambda := by
    apply (le_div_iff₀ hlambda).mpr
    simpa only [mul_comm] using hreal.trans hwhole
  simpa only [div_eq_mul_inv, mul_comm] using hfinal

theorem martingale_local_maximal_L1 (hF : Martingale F ℱ μ) (n N : ℕ)
    {s : Set X} (hs : MeasurableSet[ℱ n] s) {lambda : ℝ} (hlambda : 0 < lambda) :
    (μ.restrict s).real {x | ∃ i ≤ N, lambda ≤ |F (n + i) x - F n x|} ≤
      lambda⁻¹ * ∫ x in s, |F (n + N) x - F n x| ∂μ := by
  have hshift := martingale_timeShift hF n
  have hconst : Martingale (fun _ => F n) (timeShiftFiltration ℱ n) μ :=
    martingale_const_fun _ _ (by
      change StronglyMeasurable[ℱ n] (F n)
      exact hF.stronglyMeasurable n) (hF.integrable n)
  have hcenter : Martingale (fun i x => F (n + i) x - F n x)
      (timeShiftFiltration ℱ n) μ := hshift.sub hconst
  exact martingale_maximal_L1 (martingale_restrict_initial hcenter
    (by change MeasurableSet[ℱ n] s; exact hs)) hlambda N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleGoodLambda
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A first-crossing contraction for a finite martingale with bounded
conditional mean oscillation. This is the finite stopping step in the
John--Nirenberg proof; no exponential-tail theorem is assumed. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

theorem martingale_goodLambda (hF : Martingale F ℱ μ) (N : ℕ)
    {A D lambda : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hlambda : 0 ≤ lambda)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) :
    μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) (lambda + D + 2 * A) N) ≤
      (1 / 2 : ℝ) * μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) lambda N) := by
  let U := fun i x => ‖F i x - F 0 x‖
  let B := fun n => firstExceed U lambda n
  have hUm (i : ℕ) : Measurable (U i) :=
    ((hF.stronglyMeasurable i).measurable.le (ℱ.le i)).sub
      ((hF.stronglyMeasurable 0).measurable.le (ℱ.le 0)) |>.norm
  have hBm (n : ℕ) : MeasurableSet[ℱ n] (B n) := by
    let : MeasurableSpace X := ℱ n
    apply measurableSet_firstExceed U lambda n
    intro i hi
    exact ((hF.stronglyMeasurable i).mono (ℱ.mono hi)).measurable.sub
      ((hF.stronglyMeasurable 0).mono (ℱ.mono (Nat.zero_le n))).measurable |>.norm
  have hcell (n : Fin (N + 1)) :
      μ.real (finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) ≤
        (1 / 2 : ℝ) * μ.real (B n) := by
    let S := {x | ∃ i ≤ N - n.val, 2 * A ≤ |F (n.val + i) x - F n x|}
    have hSm : MeasurableSet S := by
      change MeasurableSet {x | ∃ i, i ≤ N - n.val ∧ 2 * A ≤ |F (n.val + i) x - F n x|}
      simp only [ofPred_exists, ofPred_and]
      apply MeasurableSet.iUnion
      intro i
      have hd : Measurable (fun x => F (n.val + i) x - F n x) :=
        ((hF.stronglyMeasurable (n.val + i)).measurable.le (ℱ.le _)).sub
          ((hF.stronglyMeasurable n.val).measurable.le (ℱ.le _))
      simpa only [Real.norm_eq_abs] using
        (MeasurableSet.const (i ≤ N - n.val)).inter
          (measurableSet_le measurable_const hd.norm)
    have hlocal := martingale_local_maximal_L1 hF n.val (N - n.val) (hBm n) (by positivity : 0 < 2 * A)
    have hbudget := hBMO n.val (by omega) (B n) (hBm n)
    have hindex : n.val + (N - n.val) = N := by omega
    rw [hindex] at hlocal
    have hsub : finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n ⊆ S ∩ B n := by
      simpa only [S, U, B, Real.norm_eq_abs] using
        firstExceed_large_subset F N n.val (by omega) hlambda hD
          (by positivity : 0 ≤ 2 * A) hjump
    calc
      _ ≤ μ.real (S ∩ B n) := measureReal_mono hsub
      _ = (μ.restrict (B n)).real S := (measureReal_restrict_apply hSm).symm
      _ ≤ (2 * A)⁻¹ * ∫ x in B n, |F N x - F n x| ∂μ := hlocal
      _ ≤ (2 * A)⁻¹ * (A * μ.real (B n)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by field_simp [hA.ne']
  have hcover : finiteMaxEvent U (lambda + D + 2 * A) N ⊆
      ⋃ n : Fin (N + 1), finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n := by
    intro x hx
    obtain ⟨i,hi,hUi⟩ := hx
    have hxsmall : x ∈ finiteMaxEvent U lambda N := ⟨i,hi,by linarith⟩
    rw [← firstExceed_union] at hxsmall
    obtain ⟨n,hn⟩ := mem_iUnion.mp hxsmall
    exact mem_iUnion.mpr ⟨n,⟨i,hi,hUi⟩,hn⟩
  calc
    _ ≤ μ.real (⋃ n : Fin (N + 1), finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) :=
      measureReal_mono hcover
    _ ≤ ∑ n : Fin (N + 1), μ.real (finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ n : Fin (N + 1), (1 / 2 : ℝ) * μ.real (B n) := Finset.sum_le_sum (fun n _ => hcell n)
    _ = (1 / 2 : ℝ) * μ.real (finiteMaxEvent U lambda N) := by
      rw [← Finset.mul_sum, firstExceed_measure_sum μ U lambda N (fun i _ => hUm i)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleGeometricTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating the first-crossing contraction gives a geometric tail with
constants independent of the number of time steps. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

theorem martingale_geometric_tail (hF : Martingale F ℱ μ) (N : ℕ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) (k : ℕ) :
    μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) ((k : ℝ) * (D + 2 * A)) N) ≤
      (1 / 2 : ℝ) ^ k * μ.real univ := by
  induction k with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, pow_zero, one_mul] using
      (measureReal_mono (μ := μ) (subset_univ
        (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) 0 N)))
  | succ k ih =>
    have hlambda : 0 ≤ (k : ℝ) * (D + 2 * A) := mul_nonneg (Nat.cast_nonneg k) (by linarith)
    have h := martingale_goodLambda hF N hA hD hlambda hBMO hjump
    have heq : (k : ℝ) * (D + 2 * A) + D + 2 * A =
        ((k + 1 : ℕ) : ℝ) * (D + 2 * A) := by push_cast; ring
    rw [heq] at h
    exact h.trans (by simpa only [pow_succ, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2))

theorem martingale_terminal_geometric_tail (hF : Martingale F ℱ μ) (N : ℕ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) (k : ℕ) :
    μ.real {x | (k : ℝ) * (D + 2 * A) < ‖F N x - F 0 x‖} ≤
      (1 / 2 : ℝ) ^ k * μ.real univ := by
  apply (measureReal_mono (μ := μ) (show
    {x | (k : ℝ) * (D + 2 * A) < ‖F N x - F 0 x‖} ⊆
      finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) ((k : ℝ) * (D + 2 * A)) N from
        fun _ hx => ⟨N,le_rfl,hx⟩)).trans
  exact martingale_geometric_tail hF N hA hD hBMO hjump k

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MeanOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local mean oscillation estimates used before John--Nirenberg.
The short part is controlled in mean and the long part by its oscillation.
All constants are independent of the dimension of the range. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_average_sub_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (hf : Integrable f μ) (hm : 0 < μ.real univ) (c : E) :
    ‖integralAverage μ f - c‖ ≤ (μ.real univ)⁻¹ * ∫ x, ‖f x - c‖ ∂μ := by
  have heq : integralAverage μ f - c = (μ.real univ)⁻¹ • ∫ x, (f x - c) ∂μ := by
    rw [integral_sub hf (integrable_const c), integral_const, smul_sub,
      smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hm.le)

theorem integral_oscillation_le_twice (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (hf : Integrable f μ) (hm : 0 < μ.real univ) (c : E) :
    (∫ x, ‖f x - integralAverage μ f‖ ∂μ) ≤ 2 * ∫ x, ‖f x - c‖ ∂μ := by
  have hpoint (x : X) : ‖f x - integralAverage μ f‖ ≤
      ‖f x - c‖ + ‖integralAverage μ f - c‖ := by
    simpa only [norm_sub_rev] using
      norm_sub_le_norm_sub_add_norm_sub (f x) c (integralAverage μ f)
  calc
    _ ≤ ∫ x, (‖f x - c‖ + ‖integralAverage μ f - c‖) ∂μ :=
      integral_mono (hf.sub (integrable_const _)).norm
        ((hf.sub (integrable_const c)).norm.add (integrable_const _)) hpoint
    _ = (∫ x, ‖f x - c‖ ∂μ) + μ.real univ * ‖integralAverage μ f - c‖ := by
      rw [integral_add (show Integrable (fun x => ‖f x - c‖) μ from
        (hf.sub (integrable_const c)).norm) (integrable_const _),
        integral_const, smul_eq_mul]
    _ ≤ (∫ x, ‖f x - c‖ ∂μ) +
        μ.real univ * ((μ.real univ)⁻¹ * ∫ x, ‖f x - c‖ ∂μ) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_average_sub_le μ f hf hm c) hm.le)
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hm.ne']; ring

omit [CompleteSpace E] in
theorem integralAverage_add (μ : Measure X) (f g : X → E)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    integralAverage μ (fun x => f x + g x) = integralAverage μ f + integralAverage μ g := by
  simp only [integralAverage, integral_add hf hg, smul_add]

theorem short_long_mean_oscillation (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → E) (hf : Integrable f μ) (hg : Integrable g μ)
    (hm : 0 < μ.real univ) {K L : ℝ}
    (hshort : (∫ x, ‖f x‖ ∂μ) ≤ K * μ.real univ)
    (hlong : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖g x - g y‖ ≤ L) :
    (∫ x, ‖f x + g x - integralAverage μ (fun y => f y + g y)‖ ∂μ) ≤
      (2 * K + L) * μ.real univ := by
  have hgpoint : ∀ᵐ x ∂μ, ‖g x - integralAverage μ g‖ ≤ L := by
    filter_upwards [hlong] with x hx
    exact norm_sub_mean_le μ g hg hm (g x) L hx
  have hfmean := integral_oscillation_le_twice μ f hf hm (0 : E)
  simp only [sub_zero] at hfmean
  have hgmean : (∫ x, ‖g x - integralAverage μ g‖ ∂μ) ≤ L * μ.real univ := by
    simpa only [integral_const, smul_eq_mul, mul_comm, Pi.sub_apply] using
      integral_mono_ae (hg.sub (integrable_const _)).norm (integrable_const L) hgpoint
  calc
    _ ≤ ∫ x, (‖f x - integralAverage μ f‖ + ‖g x - integralAverage μ g‖) ∂μ := by
      apply integral_mono
        (show Integrable (fun x => ‖f x + g x - integralAverage μ (fun y => f y + g y)‖) μ from
          ((hf.add hg).sub (integrable_const _)).norm)
        (show Integrable (fun x => ‖f x - integralAverage μ f‖ +
            ‖g x - integralAverage μ g‖) μ from
          (hf.sub (integrable_const _)).norm.add (hg.sub (integrable_const _)).norm)
      intro x
      rw [integralAverage_add μ f g hf hg]
      dsimp only
      rw [add_sub_add_comm]
      exact norm_add_le (f x - integralAverage μ f) (g x - integralAverage μ g)
    _ = (∫ x, ‖f x - integralAverage μ f‖ ∂μ) +
        ∫ x, ‖g x - integralAverage μ g‖ ∂μ := by
      exact integral_add (show Integrable (fun x => ‖f x - integralAverage μ f‖) μ from
        (hf.sub (integrable_const _)).norm)
        (show Integrable (fun x => ‖g x - integralAverage μ g‖) μ from
          (hg.sub (integrable_const _)).norm)
    _ ≤ (2 * K + L) * μ.real univ := by linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mean oscillation on the actual line cells controls every martingale
jump by the branching factor. This supplies the overshoot bound in the
dyadic stopping proof of John--Nirenberg. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

theorem cell_mass (g : FiniteLineGrid) (level i : ℕ) :
    (volume.restrict (g.cell level i)).real univ = g.meshWidth level := by
  rw [measureReal_def, Measure.restrict_apply_univ, cell, Real.volume_Ico]
  have heq : g.origin + g.meshWidth level * (i + 1) -
      (g.origin + g.meshWidth level * i) = g.meshWidth level := by ring
  rw [heq, ENNReal.toReal_ofReal (g.meshWidth_pos level).le]

theorem cellMean_eq_integralAverage (g : FiniteLineGrid) (f : ℝ → ℝ) (level i : ℕ) :
    g.cellMean f level i = integralAverage (volume.restrict (g.cell level i)) f := by
  simp only [integralAverage, g.cell_mass, cellMean, smul_eq_mul]

theorem cellMean_sub_constant_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    {level i : ℕ} (hf : IntegrableOn f (g.cell level i)) (c : ℝ) :
    |g.cellMean f level i - c| ≤
      (g.meshWidth level)⁻¹ * ∫ x in g.cell level i, |f x - c| := by
  rw [g.cellMean_eq_integralAverage]
  simpa only [Real.norm_eq_abs, g.cell_mass] using
    norm_average_sub_le (volume.restrict (g.cell level i)) f hf
      (by rw [g.cell_mass]; exact g.meshWidth_pos level) c

theorem cell_subset_parent (g : FiniteLineGrid) {level i : ℕ}
    (hl : level + 1 ≤ g.depth) (hi : i < g.branching ^ (level + 1)) :
    g.cell (level + 1) i ⊆ g.cell level (i / g.branching) := by
  intro x hx
  have hr := g.cell_subset_root (level + 1) hi hx
  have hix := (g.index_eq_iff_mem_cell hl hr i).mpr hx
  have hp := congrArg Fin.val (g.index_parent (by omega : level < g.depth) x)
  change (g.index level x).val = (g.index (level + 1) x).val / g.branching at hp
  rw [hix] at hp
  exact (g.index_eq_iff_mem_cell (by omega) hr (i / g.branching)).mp hp

theorem parent_index_lt (g : FiniteLineGrid) {level i : ℕ}
    (hi : i < g.branching ^ (level + 1)) : i / g.branching < g.branching ^ level := by
  apply (Nat.div_lt_iff_lt_mul g.branching_pos).mpr
  simpa only [pow_succ] using hi

theorem meshWidth_succ (g : FiniteLineGrid) (level : ℕ) :
    g.meshWidth (level + 1) = g.meshWidth level / g.branching := by
  simp only [meshWidth, pow_succ, div_div]

theorem cellMean_parent_jump (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level i : ℕ} (hl : level + 1 ≤ g.depth) (hi : i < g.branching ^ (level + 1)) :
    |g.cellMean f (level + 1) i - g.cellMean f level (i / g.branching)| ≤
      g.branching * A := by
  have hip := g.parent_index_lt hi
  have hsub := g.cell_subset_parent hl hi
  have hfp : IntegrableOn f (g.cell level (i / g.branching)) :=
    hf.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root level hip))
  have hfc := hfp.mono_set hsub
  have hnorm : IntegrableOn (fun x => |f x - g.cellMean f level (i / g.branching)|)
      (g.cell level (i / g.branching)) := by
    simpa only [IntegrableOn, Real.norm_eq_abs, Pi.sub_apply] using
      (hfp.sub (integrable_const _)).norm
  have hmono : (∫ x in g.cell (level + 1) i, |f x - g.cellMean f level (i / g.branching)|) ≤
      ∫ x in g.cell level (i / g.branching), |f x - g.cellMean f level (i / g.branching)| :=
    setIntegral_mono_set hnorm (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  calc
    _ ≤ (g.meshWidth (level + 1))⁻¹ *
        ∫ x in g.cell (level + 1) i, |f x - g.cellMean f level (i / g.branching)| :=
      g.cellMean_sub_constant_le f hfc _
    _ ≤ (g.meshWidth (level + 1))⁻¹ * (A * g.meshWidth level) :=
      mul_le_mul_of_nonneg_left (hmono.trans (hA level (i / g.branching) (by omega) hip))
        (inv_nonneg.mpr (g.meshWidth_pos _).le)
    _ = _ := by rw [g.meshWidth_succ]; field_simp [(g.meshWidth_pos level).ne']

theorem average_eq_cellMean (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure f level x = g.cellMean f level i := by
  rw [g.average_eq_cell_mean f hf hl hi hx, cellMean, div_eq_mul_inv, mul_comm]

theorem average_jump_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level : ℕ} (hl : level < g.depth) {x : ℝ} (hx : x ∈ g.root) :
    |g.average g.lineMeasure f (level + 1) x - g.average g.lineMeasure f level x| ≤
      g.branching * A := by
  let i := (g.index (level + 1) x).val
  have hi : i < g.branching ^ (level + 1) := g.index_lt_level (by omega) x
  have hxc : x ∈ g.cell (level + 1) i :=
    (g.index_eq_iff_mem_cell (by omega) hx i).mp rfl
  rw [g.average_eq_cellMean f hf (by omega) hi hxc,
    g.average_eq_cellMean f hf (by omega) (g.parent_index_lt hi)
      (g.cell_subset_parent (by omega) hi hxc)]
  exact g.cellMean_parent_jump f hf hA (by omega) hi

theorem average_jump_le_everywhere (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level : ℕ} (hl : level < g.depth) (x : ℝ) :
    |g.average g.lineMeasure f (level + 1) x - g.average g.lineMeasure f level x| ≤
      g.branching * A := by
  by_cases hx : x ∈ g.root
  · exact g.average_jump_le f hf hA hl hx
  · have ho : g.origin ∈ g.root := ⟨le_rfl, by linarith [g.width_pos]⟩
    have hidx (n : ℕ) : g.index n x = g.index n g.origin := by
      apply Fin.ext
      simp only [index, rawIndex, ite_eq_right hx, ite_eq_left ho, sub_self,
        zero_div, zero_mul, Nat.floor_zero]
    rw [g.average_constant g.lineMeasure f (level + 1) (hidx _),
      g.average_constant g.lineMeasure f level (hidx _)]
    exact g.average_jump_le f hf hA hl ho

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridConditionalBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete cellwise mean-oscillation bound implies the conditional
oscillation hypothesis used by the finite martingale stopping argument. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

theorem integrated_oscillation_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {n : ℕ} (hn : n ≤ g.depth) {s : Set ℝ} (hs : MeasurableSet[g.filtration n] s) :
    (∫ x in s, |f x - g.average g.lineMeasure f n x| ∂g.lineMeasure) ≤
      A * g.lineMeasure.real s := by
  let G := fun x => |f x - g.average g.lineMeasure f n x|
  have havg : Integrable (g.average g.lineMeasure f n) g.lineMeasure :=
    (g.average_martingale g.lineMeasure f).integrable n
  have hG : Integrable G g.lineMeasure := (hf.sub havg).abs
  have hb : ∀ᵐ x ∂g.lineMeasure, g.average g.lineMeasure G n x ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    let i := (g.index n x).val
    have hi : i < g.branching ^ n := g.index_lt_level hn x
    have hxc : x ∈ g.cell n i := (g.index_eq_iff_mem_cell hn hx i).mp rfl
    rw [g.average_eq_cell_mean G hG hn hi hxc]
    have heq : (∫ y in g.cell n i, G y) =
        ∫ y in g.cell n i, |f y - g.cellMean f n i| := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro y hy
      simp only [G, g.average_eq_cellMean f hf hn hi hy]
    rw [heq]
    exact (div_le_iff₀ (g.meshWidth_pos n)).mpr (hA n i hn hi)
  change (∫ x in s, G x ∂g.lineMeasure) ≤ _
  rw [← setIntegral_condExp (g.filtration.le n) hG hs]
  have h := integral_mono_ae (μ := g.lineMeasure.restrict s)
    integrable_condExp.integrableOn (integrable_const A)
    (ae_restrict_of_ae hb)
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using h

theorem terminal_mean_oscillation (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {N : ℕ} (hN : N ≤ g.depth) :
    TerminalMeanOscillationBound (g.average g.lineMeasure f) g.filtration g.lineMeasure N A := by
  intro n hn s hs
  have hsm : MeasurableSet[g.filtration N] s := g.filtration.mono hn _ hs
  have havg : Integrable (g.average g.lineMeasure f n) g.lineMeasure :=
    (g.average_martingale g.lineMeasure f).integrable n
  have heq : g.lineMeasure[(fun x => f x - g.average g.lineMeasure f n x) | g.filtration N] =ᵐ[g.lineMeasure]
      (fun x => g.average g.lineMeasure f N x - g.average g.lineMeasure f n x) := by
    have hsub := condExp_sub hf havg (g.filtration N)
    have hmeas : StronglyMeasurable[g.filtration N] (g.average g.lineMeasure f n) :=
      (g.average_martingale g.lineMeasure f).stronglyMeasurable n |>.mono (g.filtration.mono hn)
    rw [condExp_of_stronglyMeasurable (g.filtration.le N) hmeas havg] at hsub
    exact hsub
  calc
    _ = ∫ x in s, |g.lineMeasure[(fun x => f x - g.average g.lineMeasure f n x) | g.filtration N] x|
        ∂g.lineMeasure := by
      apply setIntegral_congr_ae (g.filtration.le n _ hs)
      filter_upwards [heq] with x hx _
      rw [hx]
    _ ≤ ∫ x in s, |f x - g.average g.lineMeasure f n x| ∂g.lineMeasure :=
      setIntegral_abs_condExp_le hsm _
    _ ≤ _ := g.integrated_oscillation_le f hf hA (hn.trans hN) hs

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridBMO_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric John--Nirenberg tails for the concrete line-cell averages. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert.FiniteLineGrid

theorem mean_oscillation_average_tail (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasMeanOscillationBound f A) {N : ℕ} (hN : N ≤ g.depth) (k : ℕ) :
    g.lineMeasure.real {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
      |g.average g.lineMeasure f N x - g.average g.lineMeasure f 0 x|} ≤
        (1 / 2 : ℝ) ^ k * g.lineMeasure.real univ := by
  have htail := martingale_terminal_geometric_tail (g.average_martingale g.lineMeasure f) N hA
    (mul_nonneg (Nat.cast_nonneg g.branching) hA.le)
    (g.terminal_mean_oscillation f hf hBMO hN)
    (fun i hi x => by
      simpa only [Real.norm_eq_abs] using
        g.average_jump_le_everywhere f hf hBMO (hi.trans_le hN) x) k
  have hscale : (k : ℝ) * ((g.branching : ℝ) * A + 2 * A) =
      (k : ℝ) * ((g.branching : ℝ) + 2) * A := by ring
  simpa only [hscale, Real.norm_eq_abs] using htail

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cell averages converge at every continuity point in the root.
Only this continuous-function specialization of differentiation is needed
for the finite smooth packet and variation functions. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

theorem cell_zero (g : FiniteLineGrid) : g.cell 0 0 = g.root := by
  simp only [cell, meshWidth, pow_zero, div_one, Nat.cast_zero, mul_zero,
    add_zero, zero_add, mul_one, root]

theorem average_zero_eq_integralAverage (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {x : ℝ} (hx : x ∈ g.root) :
    g.average g.lineMeasure f 0 x = integralAverage g.lineMeasure f := by
  rw [g.average_eq_cellMean (i := 0) f hf (Nat.zero_le _) (by simp)
    (by simpa only [g.cell_zero] using hx), g.cellMean_eq_integralAverage, g.cell_zero]
  rfl

theorem average_close_of_mesh (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {n : ℕ} (hn : n ≤ g.depth)
    {x : ℝ} (hx : x ∈ g.root) {epsilon delta : ℝ}
    (hlocal : ∀ y, dist y x < delta → |f y - f x| ≤ epsilon)
    (hmesh : g.meshWidth n < delta) :
    |g.average g.lineMeasure f n x - f x| ≤ epsilon := by
  let i := (g.index n x).val
  have hi : i < g.branching ^ n := g.index_lt_level hn x
  have hxc : x ∈ g.cell n i := (g.index_eq_iff_mem_cell hn hx i).mp rfl
  have hfc : IntegrableOn f (g.cell n i) :=
    hf.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root n hi))
  have hpoint : ∀ᵐ y ∂volume.restrict (g.cell n i), ‖f x - f y‖ ≤ epsilon := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    have hyr := g.cell_subset_root n hi hy
    have hiy := (g.index_eq_iff_mem_cell hn hyr i).mpr hy
    have heq : g.index n y = g.index n x := Fin.ext hiy
    have hd := g.same_index_distance hn hyr hx heq
    have hdist : dist y x < delta := by
      rw [Real.dist_eq]
      exact hd.trans_lt hmesh
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hlocal y hdist
  have h := norm_sub_mean_le (volume.restrict (g.cell n i)) f hfc
    (by rw [g.cell_mass]; exact g.meshWidth_pos n) (f x) epsilon hpoint
  rw [g.average_eq_cellMean f hf hn hi hxc, g.cellMean_eq_integralAverage]
  simpa only [integralAverage, Real.norm_eq_abs, abs_sub_comm] using h

theorem meshWidth_tendsto_zero (g : FiniteLineGrid) (hb : 1 < g.branching) :
    Tendsto g.meshWidth atTop (𝓝 0) := by
  change Tendsto (fun n => g.width / (g.branching : ℝ) ^ n) atTop (𝓝 0)
  have hbR : (1 : ℝ) < g.branching := by exact_mod_cast hb
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (r := (g.branching : ℝ)⁻¹) (by rw [abs_of_pos (inv_pos.mpr (by linarith))]; exact inv_lt_one_of_one_lt₀ hbR)
  have h : Tendsto (fun n : ℕ => g.width * ((g.branching : ℝ)⁻¹) ^ n)
      atTop (𝓝 (g.width * 0)) := tendsto_const_nhds.mul hpow
  simpa only [mul_zero, meshWidth, div_eq_mul_inv, inv_pow] using
    (h : Tendsto (fun n : ℕ => g.width * ((g.branching : ℝ)⁻¹) ^ n) atTop (𝓝 (g.width * 0)))

theorem average_tendsto_at_continuity (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hf : Integrable f g.lineMeasure)
    {x : ℝ} (hx : x ∈ g.root) (hcont : ContinuousAt f x) :
    Tendsto (fun N => (g.withDepth N).average (g.withDepth N).lineMeasure f N x)
      atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨delta,hdelta,hlocal⟩ := Metric.continuousAt_iff.mp hcont (epsilon / 2) (by positivity)
  have hmesh := (tendsto_order.mp (g.meshWidth_tendsto_zero hb)).2 delta hdelta
  filter_upwards [hmesh] with N hN
  rw [Real.dist_eq]
  apply lt_of_le_of_lt ((g.withDepth N).average_close_of_mesh f hf le_rfl hx
    (fun y hy => (by simpa only [Real.dist_eq] using (hlocal hy).le)) hN)
  linarith

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ContinuousBMOTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! John--Nirenberg's geometric distribution bound for a continuous
function on an actual finite interval. The proof passes the uniform finite
grid estimate to the function, using pointwise convergence of cell means. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_mean_oscillation_tail (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasFullMeanOscillationBound f A) (k : ℕ) :
    g.lineMeasure.real {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
      |f x - integralAverage g.lineMeasure f|} ≤
        (1 / 2 : ℝ) ^ k * g.lineMeasure.real univ := by
  let F := fun N x => |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
    integralAverage g.lineMeasure f|
  have hlim : ∀ᵐ x ∂g.lineMeasure,
      Tendsto (fun N => F N x) atTop (𝓝 |f x - integralAverage g.lineMeasure f|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have h := (g.average_tendsto_at_continuity hb f hf hx (hc x hx)).sub_const
      (integralAverage g.lineMeasure f)
    simpa only [F, Real.norm_eq_abs] using h.norm
  apply strict_tail_bound_of_ae_tendsto g.lineMeasure F _ hlim _ _ (by positivity)
  intro N
  have hBN : (g.withDepth N).HasMeanOscillationBound f A := by
    intro n i _ hi
    exact hBMO n i hi
  have htail := (g.withDepth N).mean_oscillation_average_tail f hf hA hBN le_rfl k
  have heq : {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A < F N x} =ᵐ[g.lineMeasure]
      {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
        |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
          (g.withDepth N).average (g.withDepth N).lineMeasure f 0 x|} := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    change ((k : ℝ) * ((g.branching : ℝ) + 2) * A < F N x) = ((k : ℝ) * ((g.branching : ℝ) + 2) * A <
        |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
          (g.withDepth N).average (g.withDepth N).lineMeasure f 0 x|)
    simp only [F, (g.withDepth N).average_zero_eq_integralAverage f hf hx]
    rfl
  have hm := congrArg ENNReal.toReal (measure_congr heq)
  exact hm.trans_le htail

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricTailExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A geometric distribution bound gives an exponential moment by summing
the level strips. The factor is absolute and no boundedness hypothesis is
needed for the function. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

theorem geometric_tail_exponential {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {H : ℝ} (hH : 0 < H)
    (htail : ∀ n : ℕ, μ.real {x | (n : ℝ) * H < f x} ≤
      (1 / 2 : ℝ) ^ n * μ.real univ) :
    (∫⁻ x, ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ) ≤ 7 * μ univ := by
  classical
  let S := fun n : ℕ => {x | (n : ℝ) * H < f x}
  let F := fun n : ℕ => (S n).indicator (fun _ => (3 / 2 : ℝ≥0∞) ^ (n + 1))
  have hSm (n : ℕ) : MeasurableSet (S n) := measurableSet_lt measurable_const hf
  have hFm (n : ℕ) : Measurable (F n) := measurable_const.indicator (hSm n)
  have hpoint (x : X) : ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ≤ 1 + ∑' n, F n x := by
    by_cases hx : f x = 0
    · simp [hx]
    · have hfx : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hx)
      have hk : 0 < ⌈f x / H⌉₊ := Nat.ceil_pos.mpr (div_pos hfx hH)
      let n := ⌈f x / H⌉₊ - 1
      have hn : n + 1 = ⌈f x / H⌉₊ := by dsimp [n]; omega
      have hns : x ∈ S n := by
        apply (lt_div_iff₀ hH).mp
        apply Nat.lt_ceil.mp
        dsimp [n]
        omega
      have hr : (3 / 2 : ℝ) ^ (f x / H) ≤ (3 / 2 : ℝ) ^ (n + 1) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hn]
        exact Nat.le_ceil _
      have hterm : ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ≤ F n x := by
        dsimp only [F]
        rw [indicator_of_mem hns]
        have h := ENNReal.ofReal_le_ofReal hr
        simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 2),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_ofNat] using h
      have hsum : F n x ≤ ∑' j, F j x := ENNReal.le_tsum (f := fun j => F j x) n
      exact hterm.trans (hsum.trans le_add_self)
  have ht (n : ℕ) : μ (S n) ≤ (1 / 2 : ℝ≥0∞) ^ n * μ univ := by
    have h := ENNReal.ofReal_le_ofReal (htail n)
    rw [ofReal_measureReal, ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
      ofReal_measureReal] at h
    norm_num only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] at h
    exact h
  calc
    _ ≤ ∫⁻ x, 1 + ∑' n, F n x ∂μ := lintegral_mono hpoint
    _ = μ univ + ∑' n, ∫⁻ x, F n x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
        lintegral_tsum (fun n => (hFm n).aemeasurable)]
    _ = μ univ + ∑' n, (3 / 2 : ℝ≥0∞) ^ (n + 1) * μ (S n) := by
      congr 1
      apply tsum_congr
      intro n
      exact lintegral_indicator_const (hSm n) _
    _ ≤ μ univ + ∑' n, (3 / 2 : ℝ≥0∞) ^ (n + 1) * ((1 / 2 : ℝ≥0∞) ^ n * μ univ) := by
      gcongr with n
      exact ht n
    _ = μ univ + (3 / 2 : ℝ≥0∞) * (∑' n : ℕ, (3 / 4 : ℝ≥0∞) ^ n) * μ univ := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro n
      rw [pow_succ]
      have hp : (3 / 4 : ℝ≥0∞) ^ n = (3 / 2 : ℝ≥0∞) ^ n * (1 / 2 : ℝ≥0∞) ^ n := by
        rw [← mul_pow]
        congr 1
        have hnn : (3 / 4 : ℝ≥0) = (3 / 2 : ℝ≥0) * (1 / 2 : ℝ≥0) := by norm_num
        have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
        simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
          ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hc
      rw [hp]
      ring
    _ = 7 * μ univ := by
      rw [ENNReal.tsum_geometric]
      have hc : (3 / 2 : ℝ≥0∞) * (1 - 3 / 4)⁻¹ = 6 := by
        have hquarter : (1 - 3 / 4 : ℝ≥0) = 1 / 4 := by
          apply NNReal.eq
          rw [NNReal.coe_sub (by exact_mod_cast (show (3 / 4 : ℝ) ≤ 1 by norm_num))]
          norm_num
        have hne : (1 - 3 / 4 : ℝ≥0) ≠ 0 := by rw [hquarter]; norm_num
        have hnn : (3 / 2 : ℝ≥0) * (1 - 3 / 4)⁻¹ = 6 := by rw [hquarter]; norm_num
        have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
        simpa only [ENNReal.coe_mul, ENNReal.coe_inv hne,
          ENNReal.coe_sub, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
          ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hc
      calc
        _ = (1 + (3 / 2 : ℝ≥0∞) * (1 - 3 / 4)⁻¹) * μ univ := by ring
        _ = _ := by rw [hc]; norm_num

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricTailMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-power moment bounds from the geometric distribution estimate. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem geometric_tail_rpow_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {H : ℝ} (hH : 0 < H)
    (htail : ∀ n : ℕ, μ.real {x | (n : ℝ) * H < f x} ≤
      (1 / 2 : ℝ) ^ n * μ.real univ) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤
      7 * ENNReal.ofReal ((p * H / Real.log (3 / 2)) ^ p) * μ univ := by
  let t : ℝ := Real.log (3 / 2) / H
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have ht : 0 < t := div_pos hlog hH
  have hcoef : p / t = p * H / Real.log (3 / 2) := by
    dsimp [t]
    field_simp
  let K : ℝ := (p * H / Real.log (3 / 2)) ^ p
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hpoint (x : X) : f x ^ p ≤ K * ((3 / 2 : ℝ) ^ (f x / H)) := by
    have h := ProbabilityTheory.rpow_abs_le_mul_exp_abs (f x) hp ht.ne'
    rw [abs_of_pos ht, abs_of_nonneg (hf0 x), hcoef] at h
    have hexp : Real.exp (t * f x) = (3 / 2 : ℝ) ^ (f x / H) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      dsimp [t]
      ring
    simpa only [hexp, K] using h
  have hpoint' (x : X) : ENNReal.ofReal (f x ^ p) ≤
      ENNReal.ofReal K * ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) := by
    simpa only [ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal (hpoint x)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal K * ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ :=
      lintegral_mono hpoint'
    _ = ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (7 * μ univ) :=
      mul_le_mul_right (geometric_tail_exponential μ f hf hf0 hH htail) _
    _ = _ := by dsimp [K]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ContinuousBMOMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-power John--Nirenberg moments on an actual interval. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_mean_oscillation_moment (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hm : Measurable f) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasFullMeanOscillationBound f A) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (|f x - integralAverage g.lineMeasure f| ^ p) ∂g.lineMeasure) ≤
      7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) *
        g.lineMeasure univ := by
  have hmeas : Measurable (fun x => |f x - integralAverage g.lineMeasure f|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub measurable_const).norm
  apply geometric_tail_rpow_moment g.lineMeasure _ hmeas (fun _ => abs_nonneg _)
    (mul_pos (by positivity) hA) _ hp
  intro n
  simpa only [mul_assoc] using g.continuous_mean_oscillation_tail hb f hf hc hA hBMO n

end LipschitzHilbert.FiniteLineGrid

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal derivatives of the fixed rational packet envelope. -/

noncomputable section

namespace LipschitzHilbert

theorem lineEnvelope_three_derivative_bound (a l x : ℝ) (hl : 0 < l) :
    |deriv (lineEnvelope a l 3) x| ≤ (6 / l) * lineEnvelope a l 3 x := by
  rw [(lineEnvelope_three_hasDerivAt a l x).deriv]
  let t := (x-a)/l
  have hb : 0 < 1+t^2 := by positivity
  have ht : |t| ≤ 1+t^2 := by nlinarith [sq_nonneg (|t|-1), sq_abs t]
  have heq : |(-6/l) * t * ((1+t^2)^4)⁻¹| =
      (6/l) * |t| * ((1+t^2)^4)⁻¹ := by
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 6),
      abs_of_pos hl, abs_of_nonneg (by positivity : 0 ≤ ((1+t^2)^4)⁻¹)]
  change |(-6/l) * t * ((1+t^2)^4)⁻¹| ≤ (6/l) * ((1+t^2)^3)⁻¹
  rw [heq]
  calc
    _ ≤ (6/l) * (1+t^2) * ((1+t^2)^4)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by positivity)) (by positivity)
    _ = _ := by field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RawBMOMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uncentered interval moments from the proved John--Nirenberg estimate
and a bound for the interval mean. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_raw_moment (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hm : Measurable f) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A B p : ℝ}
    (hA : 0 < A) (hBMO : g.HasFullMeanOscillationBound f A)
    (hmean : |integralAverage g.lineMeasure f| ≤ B) (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal |f x|) ^ p ∂g.lineMeasure) ≤
      (2 : ℝ≥0∞) ^ p *
        (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) +
          (ENNReal.ofReal B) ^ p) * g.lineMeasure univ := by
  let m := integralAverage g.lineMeasure f
  have hcenter := g.continuous_mean_oscillation_moment hb f hm hf hc hA hBMO hp
  have hpoint (x : ℝ) : (ENNReal.ofReal |f x|) ^ p ≤
      (2 : ℝ≥0∞) ^ p * ((ENNReal.ofReal |f x - m|) ^ p + (ENNReal.ofReal B) ^ p) := by
    have habs : |f x| ≤ |f x - m| + B := by
      have ha := norm_add_le (f x - m) m
      simp only [Real.norm_eq_abs] at ha
      rw [sub_add_cancel] at ha
      exact ha.trans (add_le_add le_rfl hmean)
    have hB : 0 ≤ B := (abs_nonneg m).trans hmean
    have h0 : ENNReal.ofReal |f x| ≤ ENNReal.ofReal |f x - m| + ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_add (abs_nonneg _) hB]
      exact ENNReal.ofReal_le_ofReal habs
    exact (ENNReal.rpow_le_rpow h0 hp).trans
      (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp)
  have hmcenter : Measurable (fun x => (ENNReal.ofReal |f x - m|) ^ p) := by
    apply Measurable.pow_const
    apply Measurable.ennreal_ofReal
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub measurable_const).norm
  have heq : (fun x => (ENNReal.ofReal |f x - m|) ^ p) =
      (fun x => ENNReal.ofReal (|f x - m| ^ p)) := by
    funext x
    exact ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp
  calc
    _ ≤ ∫⁻ x, (2 : ℝ≥0∞) ^ p * ((ENNReal.ofReal |f x - m|) ^ p +
          (ENNReal.ofReal B) ^ p) ∂g.lineMeasure := lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) ^ p * ((∫⁻ x, ENNReal.ofReal (|f x - m| ^ p) ∂g.lineMeasure) +
          (ENNReal.ofReal B) ^ p * g.lineMeasure univ) := by
      rw [lintegral_const_mul (f := fun x => (ENNReal.ofReal |f x - m|) ^ p +
          (ENNReal.ofReal B) ^ p) _ (hmcenter.add measurable_const),
        lintegral_add_left hmcenter, lintegral_const, heq]
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ≥0∞) ^ p *
            (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) *
              g.lineMeasure univ + (ENNReal.ofReal B) ^ p * g.lineMeasure univ) := by
          gcongr
        _ = _ := by ring

end LipschitzHilbert.FiniteLineGrid

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing localized packet variations with summable box weights. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem cubicVariation_nonneg {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) :
    0 ≤ cubicVariation F N := Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_TransverseBoxDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transverse decay of the reference-line envelope for centers in an
actual offset box. -/

noncomputable section

namespace LipschitzHilbert

theorem box_decay_le_line_envelope (b : ℝ) :
    (((1 + |b|) ^ 2 / 8) ^ 2)⁻¹ ≤ 64 * lineEnvelope 0 1 1 b ^ 2 := by
  have hbase : 1 + b ^ 2 ≤ (1 + |b|) ^ 2 := by nlinarith [abs_nonneg b, sq_abs b]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + b ^ 2) hbase 2
  have hinv := inv_anti₀ (by positivity : 0 < (1 + b ^ 2) ^ 2) hp
  have heq : (((1 + |b|) ^ 2 / 8) ^ 2)⁻¹ = 64 * (((1 + |b|) ^ 2) ^ 2)⁻¹ := by
    rw [div_pow, inv_div]
    norm_num
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 64)
  simpa only [lineEnvelope, sub_zero, div_one, pow_one, inv_pow] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LocalizedEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local line integrals of a packet envelope, retaining both center-box
offsets. This is the positive estimate for the square-function argument. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem local_lineEnvelope_weighted (s u l r k : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hs : |s - (u + r*k)| ≤ r) :
    (((1 + |k|) ^ 2 / 8) ^ 2) * (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
      16 * (Real.pi * l) := by
  have hi : IntegrableOn (lineEnvelope s l 3) (Icc (u-r) (u+r)) :=
    (integrable_lineEnvelope s l hl (by decide : 1 ≤ 3)).restrict
  have hpoint : ∀ x ∈ Icc (u-r) (u+r),
      (((1 + |k|) ^ 2 / 8) ^ 2) * lineEnvelope s l 3 x ≤ 16 * lineEnvelope s l 1 x := by
    intro x hx
    have hxu : |x-u| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hweight : (1 + |k|)^2/8 ≤ polynomialWeight (u+r*k) r 1 x := by
      simpa only [pow_one] using box_polynomial_weight u r k x 1 hr hxu
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |k|)^2/8) hweight 2
    calc
      _ ≤ polynomialWeight (u+r*k) r 1 x ^ 2 * lineEnvelope s l 3 x :=
        mul_le_mul_of_nonneg_right hp (lineEnvelope_nonneg _ _ _ _)
      _ ≤ _ := by
        simpa only [pow_one] using polynomialWeight_sq_mul_envelope x s (u+r*k) l r 1 1 hl hr hlr hs
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ x in Icc (u-r) (u+r), 16 * lineEnvelope s l 1 x :=
      setIntegral_mono_on (hi.const_mul _) ((integrable_lineEnvelope_one s l hl).restrict.const_mul _)
        measurableSet_Icc hpoint
    _ ≤ ∫ x, 16 * lineEnvelope s l 1 x :=
      setIntegral_le_integral ((integrable_lineEnvelope_one s l hl).const_mul _)
        (Filter.Eventually.of_forall (fun _ => mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _)))
    _ = _ := by rw [integral_const_mul, integral_lineEnvelope_one s l hl]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveLineKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive horizontal convolution kernel used for the error
majorant, with its short-interval integral bound. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem local_lineKernel_integral (l u r s : ℝ) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) :
    (∫ x in Icc (u-r) (u+r), lineKernel l (x-s)) ≤
      (1024 * Real.pi) * lineEnvelope u r 2 s := by
  let k := (s-u)/r
  have hs : |s-(u+r*k)| ≤ r := by
    have heq : s-(u+r*k) = 0 := by dsimp [k]; field_simp; ring
    rw [heq, abs_zero]
    exact hr.le
  have hloc := local_lineEnvelope_weighted s u l r k hl hr hlr hs
  have hw : 0 < ((1+|k|)^2/8)^2 := by positivity
  have hhor : (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
      (16 * (Real.pi*l)) * (((1+|k|)^2/8)^2)⁻¹ := by
    have h : (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
        (16 * (Real.pi*l)) / (((1+|k|)^2/8)^2) :=
      (le_div_iff₀ hw).mpr (by nlinarith [hloc])
    simpa only [div_eq_mul_inv] using h
  have hweight : lineEnvelope 0 1 1 k ^ 2 = lineEnvelope u r 2 s := by
    simp only [lineEnvelope, sub_zero, div_one, pow_one, ← inv_pow, k]
  simp_rw [lineKernel_shift]
  rw [integral_const_mul]
  calc
    _ ≤ l⁻¹ * ((16 * (Real.pi*l)) * (((1+|k|)^2/8)^2)⁻¹) :=
      mul_le_mul_of_nonneg_left hhor (by positivity)
    _ = (16 * Real.pi) * (((1+|k|)^2/8)^2)⁻¹ := by field_simp
    _ ≤ (16 * Real.pi) * (64 * lineEnvelope 0 1 1 k ^ 2) :=
      mul_le_mul_of_nonneg_left (box_decay_le_line_envelope k) (by positivity)
    _ = _ := by rw [hweight]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integrable pointwise majorant for translations of a long-scale
kernel. It is used before integrating against a bounded source. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem lineEnvelope_nearby (s l x z : ℝ) (hl : 0 < l) (hz : |z-x| ≤ 2*l) :
    lineEnvelope s l 1 z ≤ 10 * lineEnvelope s l 1 x := by
  have hv : |(x-z)/l| ≤ 2 := by
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl, abs_sub_comm]
    exact hz
  have hv2 : ((x-z)/l)^2 ≤ 4 := by nlinarith [sq_abs ((x-z)/l), (abs_le.mp hv).1, (abs_le.mp hv).2]
  have heq : (x-s)/l = (z-s)/l + (x-z)/l := by ring
  have hbase : 1+((x-s)/l)^2 ≤ 10*(1+((z-s)/l)^2) := by
    rw [heq]
    nlinarith [sq_nonneg ((z-s)/l-(x-z)/l), sq_nonneg ((z-s)/l)]
  simp only [lineEnvelope, pow_one]
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < 1+((z-s)/l)^2)
    (by positivity : 0 < 1+((x-s)/l)^2)).mpr
  simpa only [one_mul] using hbase

theorem lineKernel_shift_hasDerivAt (l s x : ℝ) :
    HasDerivAt (fun z => lineKernel l (z-s))
      (l⁻¹ * deriv (lineEnvelope s l 3) x) x := by
  have h := (lineEnvelope_three_hasDerivAt s l x).differentiableAt.hasDerivAt.const_mul l⁻¹
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact lineKernel_shift l s z

theorem lineKernel_shift_derivative_bound (l s x z : ℝ) (hl : 0 < l)
    (hz : |z-x| ≤ 2*l) :
    ‖deriv (fun v => lineKernel l (v-s)) z‖ ≤ (60/l^2) * lineEnvelope s l 1 x := by
  rw [(lineKernel_shift_hasDerivAt l s z).deriv, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hl.le), Real.norm_eq_abs]
  calc
    _ ≤ l⁻¹ * ((6/l) * lineEnvelope s l 3 z) :=
      mul_le_mul_of_nonneg_left (lineEnvelope_three_derivative_bound s l z hl) (by positivity)
    _ ≤ l⁻¹ * ((6/l) * (10 * lineEnvelope s l 1 x)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (lineEnvelope_antitone s l z (by decide : 1 ≤ 3)).trans (lineEnvelope_nearby s l x z hl hz)
    _ = _ := by ring

theorem lineKernel_translation_bound (l s x y : ℝ) (hl : 0 < l) (hxy : |x-y| ≤ 2*l) :
    |lineKernel l (x-s) - lineKernel l (y-s)| ≤
      ((60/l^2) * |x-y|) * lineEnvelope s l 1 x := by
  have hx : x ∈ Icc (x-2*l) (x+2*l) := ⟨by linarith, by linarith⟩
  have hy : y ∈ Icc (x-2*l) (x+2*l) := by
    have h := abs_le.mp hxy
    constructor <;> linarith
  have hd (z : ℝ) (hz : z ∈ Icc (x-2*l) (x+2*l)) :
      ‖deriv (fun v => lineKernel l (v-s)) z‖ ≤ (60/l^2) * lineEnvelope s l 1 x :=
    lineKernel_shift_derivative_bound l s x z hl (abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  have h := (convex_Icc (x-2*l) (x+2*l)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (lineKernel_shift_hasDerivAt l s z).differentiableAt) hd hy hx
  simp only [Real.norm_eq_abs] at h
  exact h.trans_eq (by ring)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual convolution of the positive error source with the horizontal
kernel. Bounded measurable sources need not be globally integrable. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem positiveConvolution_joint_integrable {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (_hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    Integrable (fun p : ℝ × ℝ => lineKernel l (p.2-p.1) * f p.1)
      (volume.prod (volume.restrict (Icc (u-r) (u+r)))) := by
  let μ := volume.restrict (Icc (u-r) (u+r))
  have hm : Measurable (fun p : ℝ × ℝ => lineKernel l (p.2-p.1) * f p.1) :=
    ((lineKernel_continuous l).measurable.comp (measurable_snd.sub measurable_fst)).mul
      (hf.comp measurable_fst)
  have hpart (s : ℝ) : Integrable (fun x => lineKernel l (x-s) * f s) μ :=
    ((lineKernel_integrable l s hl).mul_const _).restrict
  have hinner (s : ℝ) : (∫ x, ‖lineKernel l (x-s) * f s‖ ∂μ) ≤
      (C * (1024 * Real.pi)) * lineEnvelope u r 2 s := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (lineKernel_nonneg _ _ hl) (hf0 s))]
    rw [integral_mul_const]
    calc
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * f s :=
        mul_le_mul_of_nonneg_right (local_lineKernel_integral l u r s hl hr hlr) (hf0 s)
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * C :=
        mul_le_mul_of_nonneg_left (hbound s)
          (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
      _ = _ := by ring
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hpart, ?_⟩
  apply ((integrable_lineEnvelope u r hr (by decide : 1 ≤ 2)).const_mul
    (C * (1024 * Real.pi))).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact hinner s

theorem positiveConvolution_interval_integrable {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    IntegrableOn (positiveConvolution l f) (Icc (u-r) (u+r)) :=
  (positiveConvolution_joint_integrable hf hC hl hr hlr hf0 hbound u).integral_prod_right

theorem integral_positiveConvolution_interval {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    (∫ x in Icc (u-r) (u+r), positiveConvolution l f x) =
      ∫ s, f s * (∫ x in Icc (u-r) (u+r), lineKernel l (x-s)) := by
  have h := integral_integral_swap (f := fun s x => lineKernel l (x-s) * f s)
    (μ := volume) (ν := volume.restrict (Icc (u-r) (u+r)))
    (positiveConvolution_joint_integrable hf hC hl hr hlr hf0 hbound u)
  unfold positiveConvolution
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [integral_mul_const, mul_comm]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveConvolutionOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Lipschitz continuity of the actual error convolution, obtained
by an integrable bound for kernel translations. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem positiveConvolution_oscillation {f : ℝ → ℝ} (hf : Measurable f)
    {C l : ℝ} (_hC : 0 ≤ C) (hl : 0 < l) (hbound : ∀ s, ‖f s‖ ≤ C)
    (x y : ℝ) (hxy : |x-y| ≤ 2*l) :
    |positiveConvolution l f x - positiveConvolution l f y| ≤
      ((60 * Real.pi * C) / l) * |x-y| := by
  have hm : Integrable (fun s => ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s) :=
    (integrable_lineEnvelope_one x l hl).const_mul _
  have hp (s : ℝ) : ‖lineKernel l (x-s) * f s - lineKernel l (y-s) * f s‖ ≤
      ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    have h := mul_le_mul (lineKernel_translation_bound l s x y hl hxy) (hbound s)
      (norm_nonneg _) (mul_nonneg (by positivity : 0 ≤ (60/l^2) * |x-y|)
        (lineEnvelope_nonneg _ _ _ _))
    have heq : lineEnvelope s l 1 x = lineEnvelope x l 1 s := by
      simp only [lineEnvelope, div_pow, sub_sq_comm]
    rw [heq] at h
    apply h.trans_eq
    ring
  rw [positiveConvolution, positiveConvolution,
    ← integral_sub (positiveConvolution_integrable_at hf hl hbound x)
      (positiveConvolution_integrable_at hf hl hbound y), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s, ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s :=
      norm_integral_le_of_norm_le hm (Filter.Eventually.of_forall hp)
    _ = ((C * (60/l^2)) * |x-y|) * (Real.pi*l) := by
      rw [integral_const_mul, integral_lineEnvelope_one x l hl]
    _ = _ := by field_simp

theorem positiveConvolution_continuous {f : ℝ → ℝ} (hf : Measurable f)
    {C l : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hbound : ∀ s, ‖f s‖ ≤ C) :
    Continuous (positiveConvolution l f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A := (60 * Real.pi * C) / l
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨min l (ε/(A+1)), lt_min hl (div_pos hε (by positivity)), ?_⟩
  intro y hy
  have hdist : |y-x| < min l (ε/(A+1)) := by simpa only [Real.dist_eq] using hy
  have hsmall : |y-x| ≤ 2*l := by linarith [lt_of_lt_of_le hdist (min_le_left _ _)]
  have h := positiveConvolution_oscillation hf hC hl hbound y x hsmall
  have he : (A+1)*|y-x| < ε := by
    have h := (lt_div_iff₀ (by positivity : 0 < A+1)).mp
      (lt_of_lt_of_le hdist (min_le_right _ _))
    nlinarith
  rw [Real.dist_eq]
  change |positiveConvolution l f y - positiveConvolution l f x| < ε
  change _ ≤ A*|y-x| at h
  nlinarith [abs_nonneg (y-x)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LongPositiveConvolution
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform long-scale oscillation of the actual positive error majorant. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem long_positiveConvolution_oscillation {N : ℕ}
    (f : Fin N → ℝ → ℝ) (hf : ∀ j, Measurable (f j)) {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 < L) (hbound : ∀ j s, ‖f j s‖ ≤ C)
    (u r : ℝ) (hr : 0 < r) {x y : ℝ}
    (hx : x ∈ Icc (u-r) (u+r)) (hy : y ∈ Icc (u-r) (u+r)) :
    |(∑ j : Fin N, if r < L / (2 : ℝ)^j.val then
      positiveConvolution (L / (2 : ℝ)^j.val) (f j) x else 0) -
      (∑ j : Fin N, if r < L / (2 : ℝ)^j.val then
      positiveConvolution (L / (2 : ℝ)^j.val) (f j) y else 0)| ≤
      240 * Real.pi * C := by
  let len := fun j : Fin N => L / (2 : ℝ)^j.val
  have hlen (j : Fin N) : 0 < len j := by dsimp [len]; positivity
  have hdist : |x-y| ≤ 2*r := abs_le.mpr ⟨by linarith [hx.1,hy.2], by linarith [hx.2,hy.1]⟩
  have heq : (∑ j : Fin N, if r < len j then
      ((60 * Real.pi * C) / len j) * |x-y| else 0) =
      ((60 * Real.pi * C) * |x-y|) * ∑ j : Fin N, if r < len j then (len j)⁻¹ else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : r < len j <;> simp only [hj, ite_true, if_true, ite_false, if_false, mul_zero]
    rw [div_eq_mul_inv]
    ring
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |(if r < len j then positiveConvolution (len j) (f j) x else 0) -
        (if r < len j then positiveConvolution (len j) (f j) y else 0)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ)
        (f := fun j : Fin N => (if r < len j then positiveConvolution (len j) (f j) x else 0) -
          (if r < len j then positiveConvolution (len j) (f j) y else 0))
    _ ≤ ∑ j : Fin N, if r < len j then ((60 * Real.pi * C) / len j) * |x-y| else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : r < len j
      · simp only [ite_eq_left hj]
        exact positiveConvolution_oscillation (hf j) hC (hlen j) (hbound j) x y (by linarith)
      · simp only [ite_eq_right hj, sub_zero, abs_zero, le_refl]
    _ = _ := heq
    _ ≤ ((60 * Real.pi * C) * (2*r)) * (2/r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdist (by positivity))
        (sum_long_dyadic_reciprocals N L r hL hr)
        (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)) (by positivity)
    _ = _ := by field_simp; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortPositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short-scale convolution control by the sum of the actual source
functions before integration. This avoids a factor counting the scales. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem short_positiveConvolution_integral {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (len : ι → ℝ) (hlen : ∀ j, 0 < len j)
    (hf : ∀ j, Measurable (f j)) (hf0 : ∀ j s, 0 ≤ f j s)
    {M : ℝ} (hM : 0 ≤ M) (hsum : ∀ s, ∑ j, f j s ≤ M)
    (u r : ℝ) (hr : 0 < r) :
    (∫ x in Icc (u-r) (u+r),
      ∑ j, if len j ≤ r then positiveConvolution (len j) (f j) x else 0) ≤
      (1024 * Real.pi ^ 2) * M * r := by
  have hbound (j : ι) (s : ℝ) : f j s ≤ M :=
    (Finset.single_le_sum (fun i _ => hf0 i s) (Finset.mem_univ j)).trans (hsum s)
  let H := fun j s => if len j ≤ r then
    f j s * (∫ x in Icc (u-r) (u+r), lineKernel (len j) (x-s)) else 0
  have hH (j : ι) : Integrable (H j) := by
    by_cases hj : len j ≤ r
    · have hi := (positiveConvolution_joint_integrable (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u).integral_prod_left
      apply hi.congr
      filter_upwards [] with s
      change (∫ x in Icc (u-r) (u+r), lineKernel (len j) (x-s) * f j s) = H j s
      dsimp only [H]
      rw [ite_eq_left hj, integral_mul_const, mul_comm]
    · simp only [H, ite_eq_right hj]
      exact integrable_zero _ _ _
  have hG (j : ι) : IntegrableOn
      (fun x => if len j ≤ r then positiveConvolution (len j) (f j) x else 0) (Icc (u-r) (u+r)) := by
    by_cases hj : len j ≤ r
    · simpa only [ite_eq_left hj] using
        positiveConvolution_interval_integrable (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u
    · simp only [ite_eq_right hj]
      exact integrable_zero _ _ _
  have heq (j : ι) : (∫ x in Icc (u-r) (u+r),
      if len j ≤ r then positiveConvolution (len j) (f j) x else 0) = ∫ s, H j s := by
    by_cases hj : len j ≤ r
    · simp only [ite_eq_left hj, H]
      exact integral_positiveConvolution_interval (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u
    · simp only [ite_eq_right hj, H, integral_zero]
  have hpoint (s : ℝ) : (∑ j, H j s) ≤
      ((1024 * Real.pi) * M) * lineEnvelope u r 2 s := by
    have hpart : (∑ j, if len j ≤ r then f j s else 0) ≤ M := by
      apply le_trans _ (hsum s)
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> simp only [le_refl, hf0]
    calc
      _ ≤ ∑ j, ((1024 * Real.pi) * lineEnvelope u r 2 s) *
          (if len j ≤ r then f j s else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : len j ≤ r
        · simp only [H, ite_eq_left hj]
          exact (mul_le_mul_of_nonneg_left
            (local_lineKernel_integral (len j) u r s (hlen j) hr hj) (hf0 j s)).trans_eq (mul_comm _ _)
        · simp only [H, ite_eq_right hj, mul_zero, le_refl]
      _ = ((1024 * Real.pi) * lineEnvelope u r 2 s) *
          ∑ j, if len j ≤ r then f j s else 0 := by rw [Finset.mul_sum]
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * M :=
        mul_le_mul_of_nonneg_left hpart (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
      _ = _ := by ring
  rw [integral_finsetSum _ (fun j _ => hG j)]
  simp_rw [heq]
  rw [← integral_finsetSum _ (fun j _ => hH j)]
  calc
    _ ≤ ∫ s, ((1024 * Real.pi) * M) * lineEnvelope u r 2 s :=
      integral_mono (integrable_finsetSum _ (fun j _ => hH j))
        ((integrable_lineEnvelope u r hr (by decide : 1 ≤ 2)).const_mul _) hpoint
    _ = ((1024 * Real.pi) * M) * ∫ s, lineEnvelope u r 2 s := integral_const_mul _ _
    _ ≤ ((1024 * Real.pi) * M) * (Real.pi*r) :=
      mul_le_mul_of_nonneg_left (integral_lineEnvelope_le u r hr (by decide : 1 ≤ 2)) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationContinuous
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual finite variation function. This permits
pointwise interval John--Nirenberg bounds, without exceptional lines. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem continuous_finiteCubicVariation {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => finiteCubicVariation (fun n => F n x) N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : X) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Continuous (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact continuous_finsetSum _ (fun i _ => ((hF _).sub (hF _)).norm.pow 3)
    · simp only [g, ite_eq_right hp]
      exact continuous_const
  have hs := Continuous.finset_sup' Finset.univ_nonempty (fun p _ => hg p)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [finiteCubicVariation, g, Finset.sup'_apply]

theorem continuous_cubicVariation {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => cubicVariation (fun n => F n x) N) := by
  apply (continuous_finiteCubicVariation F hF N).rpow_const
  intro x
  exact Or.inr (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VariationLineBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the interval John--Nirenberg theorem to a finite packet
variation, using the actual short/long decomposition on each cell. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_integrable_cell (g : FiniteLineGrid) {f : ℝ → ℝ}
    (hf : Continuous f) (level i : ℕ) : IntegrableOn f (g.cell level i) := by
  unfold cell
  exact hf.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PositiveErrorMajorant
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive convolution majorant for the error terms. Source
size and source-sum bounds remain explicit; BMO is derived for this
majorant rather than assumed for every function it dominates. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

namespace LineErrorSources

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

theorem length_pos (P : LineErrorSources N) (j : Fin N) : 0 < P.length j := by
  exact div_pos P.topLength_pos (pow_pos (by norm_num) _)

theorem source_norm_bound (P : LineErrorSources N) (j : Fin N) (s : ℝ) :
    ‖P.source j s‖ ≤ P.sourceBound := by
  rw [Real.norm_eq_abs, abs_of_nonneg (P.source_nonneg j s)]
  exact P.source_bound j s

theorem term_nonneg (P : LineErrorSources N) (j : Fin N) (x : ℝ) : 0 ≤ P.term j x :=
  positiveConvolution_nonneg (P.length_pos j) (P.source_nonneg j) x

theorem term_continuous (P : LineErrorSources N) (j : Fin N) : Continuous (P.term j) :=
  positiveConvolution_continuous (P.measurable_source j) P.sourceBound_nonneg (P.length_pos j) (P.source_norm_bound j)

theorem majorant_nonneg (P : LineErrorSources N) (x : ℝ) : 0 ≤ P.majorant x :=
  Finset.sum_nonneg (fun j _ => P.term_nonneg j x)

theorem majorant_continuous (P : LineErrorSources N) : Continuous P.majorant :=
  continuous_finsetSum _ (fun j _ => P.term_continuous j)

theorem shortPart_nonneg (P : LineErrorSources N) (r x : ℝ) : 0 ≤ P.shortPart r x :=
  Finset.sum_nonneg (fun j _ => by split_ifs; exact P.term_nonneg j x; exact le_rfl)

theorem shortPart_continuous (P : LineErrorSources N) (r : ℝ) : Continuous (P.shortPart r) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : P.length j ≤ r
  · simpa only [ite_eq_left hj] using P.term_continuous j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem longPart_continuous (P : LineErrorSources N) (r : ℝ) : Continuous (P.longPart r) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : r < P.length j
  · simpa only [ite_eq_left hj] using P.term_continuous j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem majorant_split (P : LineErrorSources N) (r x : ℝ) :
    P.majorant x = P.shortPart r x + P.longPart r x := by
  unfold majorant shortPart longPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : P.length j ≤ r
  · simp only [ite_eq_left hj, ite_eq_right (not_lt.mpr hj), add_zero]
  · simp only [ite_eq_right hj, ite_eq_left (lt_of_not_ge hj), zero_add]

theorem shortPart_integral (P : LineErrorSources N) (u r : ℝ) (hr : 0 < r) :
    (∫ x in Icc (u-r) (u+r), P.shortPart r x) ≤ P.meanConstant * r :=
  short_positiveConvolution_integral P.source P.length P.length_pos P.measurable_source
    P.source_nonneg P.sumBound_nonneg P.source_sum u r hr

theorem longPart_oscillation (P : LineErrorSources N) (u r : ℝ) (hr : 0 < r)
    {x y : ℝ} (hx : x ∈ Icc (u-r) (u+r)) (hy : y ∈ Icc (u-r) (u+r)) :
    |P.longPart r x - P.longPart r y| ≤ P.oscillationConstant :=
  long_positiveConvolution_oscillation P.source P.measurable_source P.sourceBound_nonneg
    P.topLength_pos P.source_norm_bound u r hr hx hy

theorem majorant_mean_oscillation (P : LineErrorSources N) (g : FiniteLineGrid) :
    g.HasFullMeanOscillationBound P.majorant (2 * P.meanConstant + P.oscillationConstant) := by
  intro level i _
  let r := g.meshWidth level / 2
  let u := g.origin + g.meshWidth level * i + r
  have hr : 0 < r := half_pos (g.meshWidth_pos level)
  have hcell : g.cell level i = Ico (u-r) (u+r) := by
    dsimp [FiniteLineGrid.cell,u,r]
    congr 1 <;> ring
  have hs := g.continuous_integrable_cell (P.shortPart_continuous r) level i
  have hl := g.continuous_integrable_cell (P.longPart_continuous r) level i
  have hshort : (∫ x in g.cell level i, ‖P.shortPart r x‖) ≤
      P.meanConstant * (volume.restrict (g.cell level i)).real univ := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (P.shortPart_nonneg r _)]
    rw [g.cell_mass, hcell, ← integral_Icc_eq_integral_Ico]
    apply (P.shortPart_integral u r hr).trans
    have hK : 0 ≤ P.meanConstant := by
      have := P.sumBound_nonneg
      unfold meanConstant
      positivity
    exact mul_le_mul_of_nonneg_left (by dsimp [r]; linarith [g.meshWidth_pos level]) hK
  have hlong : ∀ᵐ x ∂volume.restrict (g.cell level i), ∀ᵐ y ∂volume.restrict (g.cell level i),
      ‖P.longPart r x - P.longPart r y‖ ≤ P.oscillationConstant := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    rw [hcell] at hx hy
    simpa only [Real.norm_eq_abs] using P.longPart_oscillation u r hr
      (Ico_subset_Icc_self hx) (Ico_subset_Icc_self hy)
  have h := short_long_mean_oscillation (volume.restrict (g.cell level i))
    (P.shortPart r) (P.longPart r) hs hl (by rw [g.cell_mass]; exact g.meshWidth_pos level) hshort hlong
  simp_rw [← P.majorant_split r] at h
  simpa only [Real.norm_eq_abs, g.cellMean_eq_integralAverage, g.cell_mass] using h

end LineErrorSources
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

theorem log_branching_le {L : ℝ} (hL : 0 ≤ L) :
    Real.log (branching L) ≤
      (Real.log L ^ 2 + 1) * (L ^ (7 / 10 : ℝ) + 2 * Real.log 2) := by
  rw [branching, Real.log_pow]
  have hK : (blockCount L : ℝ) ≤ Real.log L ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact mul_le_mul hK (log_step_bounds hL).2
    (Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) (by positivity)

/-- The actual rounded dyadic branching satisfies the scale separation
`B^100 ≤ exp(L^0.9)` eventually, with no real-valued stand-in for `B`. -/
theorem eventually_branching_separation :
    ∀ᶠ L : ℝ in atTop, branching L ^ 100 ≤ Real.exp (L ^ (9 / 10 : ℝ)) := by
  have hlog := isLittleO_log_rpow_rpow_atTop (r := 2) (s := 1 / 5) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop (2 * Real.log 2),
    hlog.bound (by norm_num : (0 : ℝ) < 1 / 400)] with L hL hlogL hpow hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp7 : 0 ≤ L ^ (7 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
  have hp2 : 0 ≤ L ^ (1 / 5 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlogsq : 1 ≤ Real.log L ^ 2 := by nlinarith
  rw [Real.rpow_two] at hsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log L)),
    abs_of_nonneg hp2] at hsmall
  have hcrude : Real.log (branching L) ≤ 4 * L ^ (7 / 10 : ℝ) * Real.log L ^ 2 := by
    apply (log_branching_le hL0.le).trans
    nlinarith [mul_le_mul (show Real.log L ^ 2 + 1 ≤ 2 * Real.log L ^ 2 by linarith)
      (show L ^ (7 / 10 : ℝ) + 2 * Real.log 2 ≤ 2 * L ^ (7 / 10 : ℝ) by linarith)
      (by positivity : 0 ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2)
      (by positivity : 0 ≤ 2 * Real.log L ^ 2)]
  have hpower : L ^ (7 / 10 : ℝ) * L ^ (1 / 5 : ℝ) = L ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hbound : 100 * Real.log (branching L) ≤ L ^ (9 / 10 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num : (0 : ℝ) ≤ 400) hp7)
    nlinarith
  calc
    branching L ^ 100 = Real.exp (100 * Real.log (branching L)) := by
      have heq : Real.log (branching L ^ (100 : ℕ)) = (100 : ℝ) * Real.log (branching L) := by
        simpa only [Nat.cast_ofNat] using (Real.log_pow (branching L) 100)
      rw [← heq, Real.exp_log (pow_pos (branching_pos L) _)]
    _ ≤ Real.exp (L ^ (9 / 10 : ℝ)) := Real.exp_le_exp.mpr hbound

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ErrorSourceBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the line error data from the manuscript's actual
two-coordinate direction profile and common vertical averaging kernel. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem actualErrorSources_log_sumBound {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2 : ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) :
    (actualErrorSources (N := N) J E direction hdirection t a c C' A topLength W y ha hc hA hC hL hW).sumBound =
      (A * ((J+1 : ℕ)+4*c+(4/Real.log 2)*Real.log ((2 : ℝ)^E))) * Real.pi := by
  change (A*((J+4*E+1 : ℕ)+4*c))*Real.pi = _
  rw [Real.log_pow]
  push_cast
  field_simp
  ring

theorem source_branching_eq_two_pow (L : ℝ) :
    SourceParameters.branching L =
      (2 : ℝ)^(SourceParameters.stepExponent L * SourceParameters.blockCount L) := by
  simp only [SourceParameters.branching, SourceParameters.step, pow_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the explicit John--Nirenberg moment expression in the polynomial
form needed when the moment order grows with the manuscript parameter. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

theorem polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ)^n * (7*((n:ℝ)*Q)^n+R^n) ≤ (16*(Q+R+1)*(n:ℝ))^n := by
  let S := Q+R+1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hA : (n:ℝ)*Q ≤ (n:ℝ)*S := by dsimp [S]; nlinarith
  have hB : R ≤ (n:ℝ)*S := by
    have h := mul_le_mul_of_nonneg_right hnR hS
    dsimp [S] at h ⊢
    nlinarith
  have hAn := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) hQ) hA n
  have hBn := pow_le_pow_left₀ hR hB n
  have h8 : (8:ℝ) ≤ 8^n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 8) hn
  calc
    _ ≤ 2^n * (8*((n:ℝ)*S)^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ ≤ 2^n * (8^n*((n:ℝ)*S)^n) := by gcongr
    _ = (16*(Q+R+1)*(n:ℝ))^n := by
      rw [← mul_assoc, ← mul_pow, ← mul_pow]
      congr 1
      dsimp [S]
      ring

theorem ennreal_polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ≥0∞)^(n:ℝ) * (7*ENNReal.ofReal (((n:ℝ)*Q)^(n:ℝ)) +
      (ENNReal.ofReal R)^(n:ℝ)) ≤ ENNReal.ofReal ((16*(Q+R+1)*(n:ℝ))^n) := by
  have h := ENNReal.ofReal_le_ofReal (polynomial_moment_majorant Q R hQ hR n hn)
  simpa only [Real.rpow_natCast, ENNReal.rpow_natCast,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2^n),
    ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 7*((n:ℝ)*Q)^n) (pow_nonneg hR n),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 7),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_pow hR,
    ENNReal.ofReal_ofNat] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MomentSuperlevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Use a natural moment at its chosen order to obtain a geometric
exceptional-set bound. No asymptotic or unspecified tail input is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem moment_superlevel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hF : Measurable F) (n : ℕ)
    (A threshold : ℝ) (ht : 0 < threshold) (M : ℝ≥0∞)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^n ∂μ) ≤ (ENNReal.ofReal A)^n*M) :
    μ {x | threshold ≤ |F x|} ≤
      ((ENNReal.ofReal A)/(ENNReal.ofReal threshold))^n*M := by
  have hsub : {x | threshold ≤ |F x|} ⊆
      {x | (ENNReal.ofReal threshold)^n ≤ (ENNReal.ofReal |F x|)^n} := by
    intro x hx
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hx) n
  have hmark := (mul_le_mul' le_rfl (measure_mono hsub)).trans
    ((mul_meas_ge_le_lintegral (hF.norm.ennreal_ofReal.pow_const n) _).trans hm)
  have he0 : (ENNReal.ofReal threshold)^n ≠ 0 :=
    pow_ne_zero n (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
  have het : (ENNReal.ofReal threshold)^n ≠ ⊤ := by finiteness
  calc
    _ = ((ENNReal.ofReal threshold)^n)⁻¹ *
        ((ENNReal.ofReal threshold)^n * μ {x | threshold ≤ |F x|}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel he0 het, one_mul]
    _ ≤ ((ENNReal.ofReal threshold)^n)⁻¹ * ((ENNReal.ofReal A)^n*M) :=
      mul_le_mul' le_rfl hmark
    _ = _ := by rw [ENNReal.div_eq_inv_mul, mul_pow, ENNReal.inv_pow]; ring

theorem moment_superlevel_quarter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hF : Measurable F) (n : ℕ)
    (A : ℝ) (hA : 0 < A) (M : ℝ≥0∞)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^n ∂μ) ≤ (ENNReal.ofReal A)^n*M) :
    μ {x | 4*A ≤ |F x|} ≤ (1/4:ℝ≥0∞)^n*M := by
  have h := moment_superlevel μ F hF n A (4*A) (by positivity) M hm
  have hr : (ENNReal.ofReal A)/(ENNReal.ofReal (4*A)) = (1/4:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 4*A)]
    have ha : A/(4*A) = (1/4:ℝ) := by field_simp [hA.ne']
    rw [ha]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
    norm_num
  simpa only [hr] using h

theorem quarter_pow_exp (n : ℕ) :
    (1/4:ℝ)^n = Real.exp (-(Real.log 4)*(n:ℝ)) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0), Real.log_one]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MultiplierError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular multiplier error is bounded by the actual annulus-plus-
small-angle-ratio source from the manuscript. -/

noncomputable section

namespace LipschitzHilbert

theorem multiplierError_bound (b : ℝ → ℂ) (t d c R M L u : ℝ)
    (hd : 0 < d) (_hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ s, ‖b s‖ ≤ M)
    (hnear : |u-t| ≤ c*d → ‖b u-b t‖ ≤ L * (|u-t|/d))
    (hfar : R*d < |u-t| → b u = 0) :
    ‖multiplierError b t d u‖ ≤ (2*M+L) * errorSourceProfile c R d |u-t| := by
  have hA : 0 ≤ 2*M+L := by positivity
  have hprofile := errorSourceProfile_nonneg c R d |u-t| hd (abs_nonneg _)
  by_cases hn : |u-t| ≤ c*d
  · have hsel : |u-t| ≤ d := hn.trans (by nlinarith)
    have hratio : 0 ≤ |u-t|/d := div_nonneg (abs_nonneg _) hd.le
    have hp : |u-t|/d ≤ errorSourceProfile c R d |u-t| := by
      unfold errorSourceProfile
      rw [ite_eq_left hn]
      split_ifs <;> linarith
    calc
      _ = ‖b u-b t‖ := by rw [multiplierError, ite_eq_left hsel]
      _ ≤ L * (|u-t|/d) := hnear hn
      _ ≤ (2*M+L) * (|u-t|/d) := mul_le_mul_of_nonneg_right (by linarith) hratio
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hA
  · by_cases hf : |u-t| ≤ R*d
    · have hp : errorSourceProfile c R d |u-t| = 1 := by
        unfold errorSourceProfile
        rw [ite_eq_left ⟨(lt_of_not_ge hn).le,hf⟩, ite_eq_right hn, add_zero]
      rw [hp,mul_one]
      unfold multiplierError
      split_ifs
      · exact (norm_sub_le _ _).trans (by linarith [hb u,hb t])
      · simpa only [sub_zero] using (hb u).trans (by linarith)
    · have hfar' : R*d < |u-t| := lt_of_not_ge hf
      have hsel : ¬ |u-t| ≤ d := by nlinarith
      rw [multiplierError, hfar hfar', ite_eq_right hsel, sub_self, norm_zero]
      exact mul_nonneg hA hprofile

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

theorem window_card_le (labels : Finset ι) (slope : ι → ℝ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K) :
    (window labels slope t d radius).card ≤ (2 * K + 1) * M := by
  classical
  let active := window labels slope t d radius
  let bin : ι → ℤ := fun i => ⌊(slope i - t) / d⌋
  let bins : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hmaps : (active : Set ι).MapsTo bin bins := by
    intro i hi
    have hwin : |slope i - t| ≤ radius * d := (Finset.mem_filter.mp hi).2
    have habs : |slope i - t| ≤ (K : ℝ) * d :=
      hwin.trans (mul_le_mul_of_nonneg_right hK hd.le)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hlow : -(K : ℝ) ≤ (slope i - t) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hupp : (slope i - t) / d < (K : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hlow),
      Int.floor_le_iff.mpr (by simpa using hupp)⟩
  have hfiber (b : ℤ) : (active.filter (fun i => bin i = b)).card ≤ M := by
    apply (Finset.card_le_card (show active.filter (fun i => bin i = b) ⊆
      labels.filter (fun i => t + (b : ℝ) * d ≤ slope i ∧
        slope i < (t + (b : ℝ) * d) + d) from ?_)).trans
      (hlocal (t + (b : ℝ) * d))
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_filter.mp hi
    have hil : i ∈ labels := (Finset.mem_filter.mp hia).1
    have h0 := Int.floor_le ((slope i - t) / d)
    have h1 := Int.lt_floor_add_one ((slope i - t) / d)
    change ⌊(slope i - t) / d⌋ = b at hib
    rw [hib] at h0 h1
    have h0' := (le_div_iff₀ hd).mp h0
    have h1' := (div_lt_iff₀ hd).mp h1
    exact Finset.mem_filter.mpr ⟨hil, by constructor <;> nlinarith⟩
  have hcount : bins.card = 2 * K + 1 := by
    have hcount' : (bins.card : ℤ) = 2 * (K : ℤ) + 1 := by
      dsimp [bins]
      rw [Int.card_Icc_of_le (a := -(K : ℤ)) (b := (K : ℤ)) (by omega)]
      omega
    exact_mod_cast hcount'
  calc
    active.card = ∑ b ∈ bins, (active.filter (fun i => bin i = b)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ bins, M := Finset.sum_le_sum fun b _ => hfiber b
    _ = (2 * K + 1) * M := by simp [hcount]

theorem active_card_le (labels : Finset ι) (slope : ι → ℝ)
    {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K)
    (hsupport : ∀ i ∈ labels, ∀ k, selector i k t ≠ 0 →
      |t - slope i| ≤ radius * d) :
    (active labels selector t).card ≤ (2 * K + 1) * M := by
  classical
  apply (Finset.card_le_card (show active labels selector t ⊆
    window labels slope t d radius from ?_)).trans
    (window_card_le labels slope hd hlocal hK)
  intro i hi
  obtain ⟨hil, k, hk⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hil, by simpa only [abs_sub_comm] using hsupport i hil k hk⟩

/-- For coefficient errors the original and frozen selectors contribute
at most twice the same absolute label bound. -/
theorem active_union_card_le (labels : Finset ι) (slope : ι → ℝ)
    {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    {t u d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K)
    (hsupport : ∀ i ∈ labels, ∀ k x, selector i k x ≠ 0 →
      |x - slope i| ≤ radius * d) :
    ((active labels selector u) ∪ (active labels selector t)).card ≤
      2 * ((2 * K + 1) * M) := by
  classical
  calc
    _ ≤ (active labels selector u).card + (active labels selector t).card :=
      Finset.card_union_le _ _
    _ ≤ (2 * K + 1) * M + (2 * K + 1) * M := Nat.add_le_add
      (active_card_le labels slope selector hd hlocal hK (fun i hi k => hsupport i hi k u))
      (active_card_le labels slope selector hd hlocal hK (fun i hi k => hsupport i hi k t))
    _ = _ := by omega

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppingScaleIntervals
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

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TwoPointEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-point decay estimate behind the positive error convolution.
Only fixed exponents six and three are needed. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem envelope_triangle_base (s l x y : ℝ) :
    1 + ((x-y)/l)^2 ≤ 2 * (1+((x-s)/l)^2) * (1+((y-s)/l)^2) := by
  have heq : (x-y)/l = (x-s)/l - (y-s)/l := by ring
  rw [heq]
  nlinarith [sq_nonneg ((x-s)/l + (y-s)/l),
    sq_nonneg (((x-s)/l)*((y-s)/l))]

theorem envelope_three_product (s l x y : ℝ) :
    lineEnvelope s l 3 x * lineEnvelope s l 3 y ≤ 8 * lineEnvelope y l 3 x := by
  let A := 1+((x-s)/l)^2
  let B := 1+((y-s)/l)^2
  let D := 1+((x-y)/l)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have h := pow_le_pow_left₀ hD.le (envelope_triangle_base s l x y) 3
  change (A^3)⁻¹ * (B^3)⁻¹ ≤ 8 * (D^3)⁻¹
  rw [← mul_inv, ← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hA 3) (pow_pos hB 3)) (pow_pos hD 3)).mpr
  simpa only [mul_pow, show (2:ℝ)^3=8 by norm_num, one_mul, mul_assoc] using h

theorem envelope_six_product (s l x y : ℝ) :
    lineEnvelope s l 6 x * lineEnvelope s l 6 y ≤
      8 * lineEnvelope y l 3 x * lineEnvelope s l 3 x := by
  have hsmall : lineEnvelope s l 3 y ≤ 1 := by
    simpa only [lineEnvelope, pow_zero, inv_one] using
      lineEnvelope_antitone s l y (by decide : 0 ≤ 3)
  have hpow (z : ℝ) : lineEnvelope s l 6 z = lineEnvelope s l 3 z ^ 2 := by
    unfold lineEnvelope
    rw [show (6:ℕ) = 3*2 from rfl, pow_mul, inv_pow]
  have heq : lineEnvelope s l 6 x * lineEnvelope s l 6 y =
      (lineEnvelope s l 3 x * lineEnvelope s l 3 y) *
        (lineEnvelope s l 3 x * lineEnvelope s l 3 y) := by
    rw [hpow x, hpow y]
    ring
  rw [heq]
  have h1 := envelope_three_product s l x y
  have h2 : lineEnvelope s l 3 x * lineEnvelope s l 3 y ≤ lineEnvelope s l 3 x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (lineEnvelope_nonneg _ _ _ _)
  calc
    _ ≤ (8 * lineEnvelope y l 3 x) * lineEnvelope s l 3 x :=
      mul_le_mul h1 h2 (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
        (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))
    _ = _ := by ring

theorem two_point_tile_envelope {ι : Type*} [Fintype ι]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site)
    (a b l W x y x' y' : ℝ) (hl : 0 < l) (hW : 0 < W) :
    (∑ i, (lineEnvelope (a+l*(site i).1) l 6 x * lineEnvelope (b+W*(site i).2) W 6 y) *
      (lineEnvelope (a+l*(site i).1) l 6 x' * lineEnvelope (b+W*(site i).2) W 6 y')) ≤
    (64 * (4 * Real.pi)^2) * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y := by
  have hterm (i : ι) :
      (lineEnvelope (a+l*(site i).1) l 6 x * lineEnvelope (b+W*(site i).2) W 6 y) *
      (lineEnvelope (a+l*(site i).1) l 6 x' * lineEnvelope (b+W*(site i).2) W 6 y') ≤
      (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
      (lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y) := by
    have hx := envelope_six_product (a+l*(site i).1) l x x'
    have hy := envelope_six_product (b+W*(site i).2) W y y'
    have h := mul_le_mul hx hy
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
      (mul_nonneg (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _)) (lineEnvelope_nonneg _ _ _ _))
    first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  calc
    _ ≤ ∑ i, (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
        (lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
        ∑ i, lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) * (4*Real.pi)^2 :=
      mul_le_mul_of_nonneg_left (injective_tile_lattice_overlap site hinj a b l W x y
        hl.ne' hW.ne' (by decide : 1 ≤ 3) (by decide : 1 ≤ 3))
        (mul_nonneg (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))
          (lineEnvelope_nonneg _ _ _ _))
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationDisjointExact
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint intervals fit into a partition of the original finite
horizon. Each interval is collapsed to one jump at its right endpoint;
the gaps contribute additional nonnegative variation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

private theorem intervalCollapse_mono (a b : ℕ) : Monotone (intervalCollapse a b) := by
  intro k l hkl
  unfold intervalCollapse
  split_ifs with hk hl
  · exact min_le_min hkl le_rfl
  · exact (min_le_left _ _).trans hkl
  · omega
  · exact hkl

private theorem disjointCollapse_mono {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    Monotone (disjointCollapse a b) := by
  intro k l hkl
  apply Finset.le_inf'
  intro q _
  have h := Finset.inf'_le
    (fun q : Option ι => q.elim k (fun i => intervalCollapse (a i) (b i) k))
    (Finset.mem_univ q)
  apply h.trans
  cases q with
  | none => exact hkl
  | some i => exact intervalCollapse_mono (a i) (b i) hkl

private theorem disjointCollapse_le {ι : Type*} [Fintype ι] (a b : ι → ℕ) (k : ℕ) :
    disjointCollapse a b k ≤ k :=
  Finset.inf'_le_of_le (f := fun q : Option ι =>
    q.elim k (fun i => intervalCollapse (a i) (b i) k))
    (Finset.mem_univ none) le_rfl

private theorem disjointCollapse_endpoints {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (hab : ∀ i, a i < b i)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) (i : ι) :
    disjointCollapse a b (b i) = b i ∧
      disjointCollapse a b (b i-1) = a i := by
  constructor
  · apply le_antisymm (disjointCollapse_le a b _)
    apply Finset.le_inf'
    intro q _
    cases q with
    | none => exact le_rfl
    | some j =>
      dsimp only [Option.elim_some]
      by_cases hij : i = j
      · subst j
        simp [intervalCollapse]
      · rcases hdisjoint i j hij with h | h
        · have hi : b i ≤ a j := h
          unfold intervalCollapse
          split_ifs <;> omega
        · have hj := hab i
          have hbji : b j ≤ b i := h.trans hj.le
          simp [intervalCollapse,not_lt.mpr hbji]
  · apply le_antisymm
    · have heq : intervalCollapse (a i) (b i) (b i-1) = a i := by
        have hi := hab i
        unfold intervalCollapse
        rw [ite_eq_left (by omega),min_eq_right (by omega)]
      exact (Finset.inf'_le
        (fun q : Option ι => q.elim (b i-1) (fun j => intervalCollapse (a j) (b j) (b i-1)))
        (Finset.mem_univ (some i))).trans_eq heq
    · apply Finset.le_inf'
      intro q _
      have hi := hab i
      cases q with
      | none => dsimp only [Option.elim_none]; omega
      | some j =>
        dsimp only [Option.elim_some]
        by_cases hij : i = j
        · subst j
          unfold intervalCollapse
          split_ifs <;> omega
        · rcases hdisjoint i j hij with h | h
          · unfold intervalCollapse
            split_ifs <;> omega
          · have hbji : b j ≤ b i-1 := by omega
            simp only [intervalCollapse,not_lt.mpr hbji,ite_false, if_false]
            omega

/-- No padding or multiplicative loss is needed for disjoint intervals
inside the original finite horizon. -/
theorem disjoint_increment_cube_sum_exact {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) (a b : ι → ℕ)
    (hab : ∀ i, a i < b i) (hb : ∀ i, b i ≤ N)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖F (b i)-F (a i)‖^3) ≤ finiteCubicVariation F N := by
  classical
  let p : Fin (N+1) → Fin (N+1) := fun k =>
    ⟨disjointCollapse a b k.val, (disjointCollapse_le a b k.val).trans_lt k.isLt⟩
  have hp : Monotone p := fun _ _ h => disjointCollapse_mono a b h
  let e : ι → Fin N := fun i => ⟨b i-1, by have := hab i; have := hb i; omega⟩
  have he : Function.Injective e := by
    intro i j hij
    have heq := congrArg Fin.val hij
    dsimp only [e] at heq
    by_contra hne
    have hi := hab i
    have hj := hab j
    rcases hdisjoint i j hne with h | h <;> omega
  have hpa (i : ι) : (p (e i).castSucc).val = a i :=
    (disjointCollapse_endpoints a b hab hdisjoint i).2
  have hpb (i : ι) : (p (e i).succ).val = b i := by
    have hi := hab i
    change disjointCollapse a b (b i-1+1) = b i
    rw [Nat.sub_add_cancel (by omega)]
    exact (disjointCollapse_endpoints a b hab hdisjoint i).1
  have hselect : (∑ i, ‖F (b i)-F (a i)‖^3) ≤
      ∑ j : Fin N, ‖F (p j.succ)-F (p j.castSucc)‖^3 := by
    refine OAI.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
      e (fun i _ j _ h => he h) (Finset.subset_univ _) ?_ ?_
    · intro i _
      rw [hpa,hpb]
    · intro j _ _
      positivity
  exact hselect.trans (partition_le_finiteCubicVariation F N p hp)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarPositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive planar kernel in coordinates (x,Y), and its exact
factorization into the two line convolutions used for concentration. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem planarPositiveConvolution_integrable (l W : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (hl : 0 < l) (hW : 0 < W) {C : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ C) (x y : ℝ) :
    Integrable (fun z : ℝ × ℝ => (lineKernel l (x-z.1) * lineKernel W (y-z.2)) * f z) := by
  have hx : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  have hy : Integrable (fun s => lineKernel W (y-s)) := by
    simp_rw [lineKernel_sub_comm W y]
    exact lineKernel_integrable W y hW
  exact (hx.mul_prod hy).mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem planarPositiveConvolution_eq_iterated (l W : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (hl : 0 < l) (hW : 0 < W) {C : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ C) (x y : ℝ) :
    planarPositiveConvolution l W f x y =
      positiveConvolution l (fun s => positiveConvolution W (fun t => f (s,t)) y) x := by
  unfold planarPositiveConvolution
  rw [Measure.volume_eq_prod, integral_prod _ (planarPositiveConvolution_integrable l W f hf hl hW hbound x y)]
  simp_rw [mul_assoc, integral_const_mul]
  rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ActualErrorConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact planar convolution interpretation of each constructed line
error source, including scalar normalization. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem planarPositiveConvolution_const_mul (l W c : ℝ) (f : ℝ × ℝ → ℝ) (x y : ℝ) :
    planarPositiveConvolution l W (fun z => c*f z) x y =
      c * planarPositiveConvolution l W f x y := by
  unfold planarPositiveConvolution
  simp_rw [mul_left_comm _ c, integral_const_mul]

theorem actualErrorSources_term_eq {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2:ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) (j : Fin N) (x : ℝ) :
    (actualErrorSources J E direction hdirection t a c C' A topLength W y ha hc hA hC hL hW).term j x =
      planarPositiveConvolution (topLength/(2:ℝ)^j.val) W
        (fun p => A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
          (a*(2:ℝ)^j.val) |direction p-t|) x y := by
  have hf : Measurable (fun p => A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
      (a*(2:ℝ)^j.val) |direction p-t|) := by
    apply Measurable.const_mul
    apply errorSourceProfile_measurable
    simpa only [Real.norm_eq_abs] using (hdirection.sub_const t).norm
  have hb (p : ℝ × ℝ) : ‖A*errorSourceProfile c (C'*((2:ℝ)^E)^4)
      (a*(2:ℝ)^j.val) |direction p-t|‖ ≤ A*(1+c) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA
      (errorSourceProfile_nonneg _ _ _ _ (mul_pos ha (pow_pos (by norm_num) _)) (abs_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (errorSourceProfile_bound _ _ _ _ hc
      (mul_pos ha (pow_pos (by norm_num) _)) (abs_nonneg _)) hA
  exact (planarPositiveConvolution_eq_iterated _ _ _ hf
    (div_pos hL (pow_pos (by norm_num) _)) hW hb x y).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_TileEnvelopeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point lattice overlap after normalization by tile area. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem tileEnvelope_nonneg (a b l W : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    0 ≤ tileEnvelope a b l W n z :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem tileEnvelope_measurable (a b l W : ℝ) (n : ℕ) :
    Measurable (tileEnvelope a b l W n) := by
  unfold tileEnvelope lineEnvelope
  fun_prop

theorem tileEnvelope_integrable (a b l W : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hl : 0 < l) (hW : 0 < W) : Integrable (tileEnvelope a b l W n) :=
  (integrable_lineEnvelope a l hl hn).mul_prod (integrable_lineEnvelope b W hW hn)

theorem two_point_tile_kernel {ι : Type*} [Fintype ι]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site)
    (a b l W : ℝ) (hl : 0 < l) (hW : 0 < W) (z z' : ℝ × ℝ) :
    (∑ i, tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z *
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z') / (l*W) ≤
    (64 * (4*Real.pi)^2) * (lineKernel l (z.1-z'.1) * lineKernel W (z.2-z'.2)) := by
  have h := div_le_div_of_nonneg_right
    (two_point_tile_envelope site hinj a b l W z.1 z.2 z'.1 z'.2 hl hW)
    (mul_nonneg hl.le hW.le)
  convert h using 1
  all_goals first | rfl | (rw [lineKernel_shift, lineKernel_shift]; ring)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LatticeCoefficientConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual analyzing coefficients controlled by a common scalar source
satisfy the fixed-scale positive convolution estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert

theorem lattice_coefficient_convolution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site) (a b l W : ℝ)
    (hl : 0 < l) (hW : 0 < W) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) {M : ℝ} (hfb : ∀ z, ‖f z‖ ≤ M)
    (wave : ι → κ → ℝ × ℝ → ℂ) (hw : ∀ i k, Measurable (wave i k))
    (hwf : ∀ i k z, ‖wave i k z‖ ≤
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z * f z)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ × ℝ) :
    (∑ i, ‖analyzingCoefficient volume (fun _ : ι => l*W) wave g i‖ *
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z) ≤
      (64 * (4*Real.pi)^2) * planarPositiveConvolution l W f z.1 z.2 := by
  let E := fun i => tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6
  have hEi (i : ι) : Integrable (fun p => E i p * f p) :=
    (tileEnvelope_integrable _ _ _ _ (by decide : 1 ≤ 6) hl hW).mul_bdd
      hf.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have hEn (i : ι) (p : ℝ × ℝ) : 0 ≤ E i p := tileEnvelope_nonneg _ _ _ _ _ _
  have hint (i : ι) (k : κ) : Integrable (fun p => g p k * conj (wave i k p)) := by
    have hgm : Measurable (fun p => g p k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    apply (hEi i).mono' (hgm.mul (continuous_star.measurable.comp (hw i k))).aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, norm_star]
    have hgk := (PiLp.norm_apply_le (g p) k).trans (hg1 p)
    exact (mul_le_mul_of_nonneg_right hgk (norm_nonneg _)).trans
      (by simpa only [one_mul] using hwf i k p)
  have ha (i : ι) : ‖analyzingCoefficient volume (fun _ : ι => l*W) wave g i‖ ≤
      (l*W)⁻¹ * ∫ p, E i p * f p :=
    analyzingCoefficient_norm_le volume (fun _ : ι => l*W) wave g i (fun p => E i p * f p)
      (mul_pos hl hW) (hEi i) (fun p => mul_nonneg (hEn i p) (hf0 p))
      (hint i) hg1 (hwf i)
  have hsumI : Integrable (fun p => ∑ i, (E i z * E i p / (l*W)) * f p) := by
    apply integrable_finsetSum
    intro i _
    convert (hEi i).const_mul (E i z / (l*W)) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    ring
  have hkerI := planarPositiveConvolution_integrable l W f hf hl hW hfb z.1 z.2
  calc
    _ ≤ ∑ i, ((l*W)⁻¹ * ∫ p, E i p * f p) * E i z :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ha i) (hEn i z))
    _ = ∫ p, ∑ i, (E i z * E i p / (l*W)) * f p := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        have heq : (fun p => (E i z * E i p / (l*W)) * f p) =
            (fun p => (E i z / (l*W)) * (E i p * f p)) := by funext p; ring
        rw [heq, integral_const_mul]
        ring
      · intro i _
        convert (hEi i).const_mul (E i z / (l*W)) using 1
        all_goals try with_reducible_and_instances rfl
        funext p
        ring
    _ ≤ ∫ p, (64*(4*Real.pi)^2) *
        ((lineKernel l (z.1-p.1) * lineKernel W (z.2-p.2)) * f p) := by
      apply integral_mono hsumI (hkerI.const_mul _)
      intro p
      have h := mul_le_mul_of_nonneg_right
        (two_point_tile_kernel site hinj a b l W hl hW z p) (hf0 p)
      convert h using 1
      · simp only [Finset.sum_mul, Finset.sum_div]
        rfl
      · ring
    _ = _ := integral_const_mul _ _

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceTailOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A moment order proportional to the source parameter gives any fixed
exponential tail while its threshold loses only two polynomial powers. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_reference_tail_order (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop, ∃ n : ℕ, 1 ≤ n ∧ 4*(n:ℝ) ≤ L^2 ∧
      (1/4:ℝ)^n ≤ Real.exp (-J*L) := by
  let d := J/Real.log 4+1
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : 0 < d := by dsimp [d]; positivity
  filter_upwards [eventually_ge_atTop (max 1 (4*d+4))] with L hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hLd : 4*d+4 ≤ L := (le_max_right _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let n := ⌈d*L⌉₊
  have hlo : d*L ≤ (n:ℝ) := Nat.le_ceil _
  have hhi : (n:ℝ) ≤ d*L+1 := (Nat.ceil_lt_add_one (mul_pos hd hL0).le).le
  refine ⟨n,Nat.ceil_pos.mpr (mul_pos hd hL0),?_,?_⟩
  · nlinarith
  · rw [quarter_pow_exp]
    apply Real.exp_le_exp.mpr
    have hmult := mul_le_mul_of_nonneg_left hlo hlog.le
    have heq : Real.log 4*(d*L) = (J+Real.log 4)*L := by
      dsimp [d]
      field_simp [hlog.ne']
    rw [heq] at hmult
    nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBadEventUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finitely many deterministic residual events may be combined
before selecting a spatial point or a mass cutoff. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

/-- Fixed polynomial losses are absorbed by one extra unit in the
exponential decay rate. -/
theorem eventually_source_polynomial_exp (C a J : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, C*L^a*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 (by norm_num : (0:ℝ) < 1)
  filter_upwards [hdecay.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 1/C))] with L hL
  have hsmall : C*(L^a*Real.exp (-L)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hL.le hC.le
    have heq : C*(1/C) = 1 := by field_simp
    simpa only [one_mul,neg_mul,heq] using h
  calc
    _ = (C*(L^a*Real.exp (-L)))*Real.exp (-J*L) := by
      rw [show (C*(L^a*Real.exp (-L)))*Real.exp (-J*L) =
        C*L^a*(Real.exp (-L)*Real.exp (-J*L)) by ring,← Real.exp_add]
      congr 2
      ring
    _ ≤ 1*Real.exp (-J*L) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = _ := one_mul _

/-- Union measure on an actual interval, with the exact number of
square/error/shift events retained until exponential absorption. -/
theorem source_bad_event_union {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (events : Finset ι) (bad : ι → Set X) (δ : ℝ)
    (htail : ∀ i ∈ events, μ (bad i) ≤ ENNReal.ofReal δ*μ univ) :
    μ (⋃ i ∈ events, bad i) ≤ ENNReal.ofReal ((events.card:ℝ)*δ)*μ univ := by
  calc
    _ ≤ ∑ i ∈ events, μ (bad i) := measure_biUnion_finset_le events bad
    _ ≤ ∑ _i ∈ events, ENNReal.ofReal δ*μ univ := Finset.sum_le_sum htail
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg events.card)]
      norm_cast
      ring


/-- The polynomial number of shift events loses one unit of exponential
rate, uniformly in all measurable spaces and finite event lists. -/
theorem eventually_source_bad_event_tail (a J : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι X : Type*) [MeasurableSpace X]
      (μ : Measure X) (events : Finset ι) (bad : ι → Set X),
      (events.card:ℝ) ≤ L^a →
      (∀ i ∈ events, μ (bad i) ≤ ENNReal.ofReal (Real.exp (-(J+1)*L))*μ univ) →
      μ (⋃ i ∈ events, bad i) ≤ ENNReal.ofReal (Real.exp (-J*L))*μ univ := by
  filter_upwards [eventually_source_polynomial_exp 1 a J (by norm_num)] with L hL
  intro ι X _ μ events bad hcard htail
  apply (source_bad_event_union μ events bad (Real.exp (-(J+1)*L)) htail).trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans
    (by simpa only [one_mul] using hL)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularErrorConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-scale convolution majorant for coefficients of the actual
angular multiplier error, including its two-coordinate direction profile. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem angularErrorWave_measurable {ι κ : Type*}
    (b : ι → κ → ℝ → ℂ) (ψ : ι → κ → ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (hb : ∀ i k, Measurable (b i k)) (hψ : ∀ i k, Measurable (ψ i k))
    (hu : Measurable u) (i : ι) (k : κ) :
    Measurable (angularErrorWave b ψ u t d i k) := by
  have huabs : Measurable (fun z => |u z-t|) := by
    simpa only [Real.norm_eq_abs] using (hu.sub_const t).norm
  have hsel : MeasurableSet {z | |u z-t| ≤ d} :=
    measurableSet_le huabs measurable_const
  exact ((hb i k |>.comp hu).sub
    (Measurable.ite hsel measurable_const measurable_const)).mul (hψ i k)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSingleScaleEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The single-scale estimate in §5, `conc:original-positive`.
The lattice estimate is summed at the source point before integrating.
Only pointwise overlap of the label multipliers appears, so the estimate
has no factor counting the available labels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planarPositiveConvolution_sum {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b))
    {l W B : ℝ} (hl : 0 < l) (hW : 0 < W)
    (hbound : ∀ b z, ‖f b z‖ ≤ B) (x y : ℝ) :
    planarPositiveConvolution l W (fun z => ∑ b, f b z) x y =
      ∑ b, planarPositiveConvolution l W (f b) x y := by
  unfold planarPositiveConvolution
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun b _ =>
    planarPositiveConvolution_integrable l W (f b) (hf b) hl hW (hbound b) x y)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular errors are summed over their active labels at the source
point, before the lattice convolution. Consequently the wide reference
cone contributes no factor counting all available labels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

/-- Pointwise domination of the sum of sources passes through the
common positive convolution, with the same constant. -/
theorem sum_planarPositiveConvolution_le_source {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b)) (hf0 : ∀ b z, 0 ≤ f b z)
    (source : ℝ×ℝ → ℝ) (hs : Measurable source) (hs0 : ∀ z, 0 ≤ source z)
    {l W C B : ℝ} (hl : 0 < l) (hW : 0 < W) (hC : 0 ≤ C) (_hB : 0 ≤ B)
    (hsB : ∀ z, source z ≤ B) (hoverlap : ∀ z, ∑ b, f b z ≤ C*source z)
    (x y : ℝ) :
    (∑ b, planarPositiveConvolution l W (f b) x y) ≤
      C*planarPositiveConvolution l W source x y := by
  have hsum0 (z : ℝ×ℝ) : 0 ≤ ∑ b, f b z := Finset.sum_nonneg (fun b _ => hf0 b z)
  have hsumB (z : ℝ×ℝ) : (∑ b, f b z) ≤ C*B :=
    (hoverlap z).trans (mul_le_mul_of_nonneg_left (hsB z) hC)
  have hfb (b : Λ) (z : ℝ×ℝ) : ‖f b z‖ ≤ C*B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 b z)]
    exact (Finset.single_le_sum (fun a _ => hf0 a z) (Finset.mem_univ b)).trans (hsumB z)
  rw [← planarPositiveConvolution_sum f hf hl hW hfb]
  calc
    _ ≤ planarPositiveConvolution l W (fun z => C*source z) x y := by
      apply integral_mono
        (planarPositiveConvolution_integrable l W _
          (Finset.measurable_sum _ (fun b _ => hf b)) hl hW
          (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hsum0 z)]; exact hsumB z) x y)
        (planarPositiveConvolution_integrable l W _ (hs.const_mul C) hl hW
          (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (hs0 z))]
                       exact mul_le_mul_of_nonneg_left (hsB z) hC) x y)
      intro z
      exact mul_le_mul_of_nonneg_left (hoverlap z)
        (mul_nonneg (lineKernel_nonneg _ _ hl) (lineKernel_nonneg _ _ hW))
    _ = _ := planarPositiveConvolution_const_mul l W C source x y

/-- The actual coefficient error for a finite family of translated
lattices. Only active selector labels enter the source overlap. -/
theorem source_labeled_error_convolution {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    (ι : Λ → Type*) [∀ b, Fintype (ι b)]
    (site : ∀ b, ι b → ℤ×ℤ) (hinj : ∀ b, Function.Injective (site b))
    (originX originY slope : Λ → ℝ) {l W d radius C M Lip small wide : ℝ} {K H : ℕ}
    (hl : 0 < l) (hW : 0 < W) (hd : 0 < d)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hLip : 0 ≤ Lip)
    (hsmall : 0 < small) (hsmall1 : small ≤ 1) (hwide : 1 ≤ wide)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ slope d H) (hK : radius ≤ K)
    (selector : Λ → κ → ℝ → ℂ) (hselector : ∀ b k, Measurable (selector b k))
    (hselectorBound : ∀ b k s, ‖selector b k s‖ ≤ M)
    (hsupport : ∀ b k s, selector b k s ≠ 0 → |s-slope b| ≤ radius*d)
    (direction : ℝ×ℝ → ℝ) (hdirection : Measurable direction) (t : ℝ)
    (hnear : ∀ b k s, |s-t| ≤ small*d →
      ‖selector b k s-selector b k t‖ ≤ Lip*(|s-t|/d))
    (hfar : ∀ b k s, wide*d < |s-t| → selector b k s = 0)
    (wave : ∀ b, ι b → κ → ℝ×ℝ → ℂ) (hwave : ∀ b i k, Measurable (wave b i k))
    (hwaveBound : ∀ b i k z, ‖wave b i k z‖ ≤
      C*tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ×ℝ) :
    (∑ b, ∑ i, ‖analyzingCoefficient volume (fun _ : ι b => l*W)
      (angularErrorWave (fun _ k => selector b k) (wave b) direction t d) g i‖*
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z) ≤
      (64*(4*Real.pi)^2)*
        (2*((2*K+1)*H):ℕ)*
        planarPositiveConvolution l W
          (fun p => (C*(2*M+Lip))*errorSourceProfile small wide d |direction p-t|) z.1 z.2 := by
  classical
  let active := fun (b : Λ) (p : ℝ×ℝ) =>
    (∃ k, selector b k (direction p) ≠ 0) ∨ (∃ k, selector b k t ≠ 0)
  let common := fun p : ℝ×ℝ => (C*(2*M+Lip))*errorSourceProfile small wide d |direction p-t|
  let source := fun b p => if active b p then common p else 0
  have hA : 0 ≤ C*(2*M+Lip) := mul_nonneg hC (by linarith)
  have hcommon0 (p : ℝ×ℝ) : 0 ≤ common p :=
    mul_nonneg hA (errorSourceProfile_nonneg _ _ _ _ hd (abs_nonneg _))
  have hcommon : Measurable common := by
    apply Measurable.const_mul
    apply errorSourceProfile_measurable
    simpa only [Real.norm_eq_abs] using (hdirection.sub_const t).norm
  have hcommonB (p : ℝ×ℝ) : common p ≤ (C*(2*M+Lip))*(1+small) :=
    mul_le_mul_of_nonneg_left (errorSourceProfile_bound _ _ _ _ hsmall hd (abs_nonneg _)) hA
  have hsource0 (b : Λ) (p : ℝ×ℝ) : 0 ≤ source b p := by
    dsimp [source]
    split_ifs
    · exact hcommon0 p
    · exact le_rfl
  have hsourceMeas (b : Λ) : Measurable (source b) := by
    have ha : MeasurableSet {p : ℝ×ℝ | ∃ k, selector b k (direction p) ≠ 0} := by
      have heq : {p : ℝ×ℝ | ∃ k, selector b k (direction p) ≠ 0} =
          ⋃ k : κ, {p | selector b k (direction p) ≠ 0} := by ext p; simp
      rw [heq]
      exact MeasurableSet.iUnion fun k =>
        (measurableSet_eq_fun ((hselector b k).comp hdirection) measurable_const).compl
    have hb : MeasurableSet {p : ℝ×ℝ | ∃ k, selector b k t ≠ 0} := by
      by_cases hb : ∃ k, selector b k t ≠ 0 <;> simp [hb]
    exact Measurable.ite (ha.union hb) hcommon measurable_const
  have hoverlap (p : ℝ×ℝ) : (∑ b, source b p) ≤ (2*((2*K+1)*H):ℕ)*common p := by
    let U := SourceSlopeLabels.active Finset.univ selector (direction p) ∪
      SourceSlopeLabels.active Finset.univ selector t
    have hmem (b : Λ) : active b p ↔ b ∈ U := by
      simp only [active,U,SourceSlopeLabels.active,Finset.mem_union,Finset.mem_filter,
        Finset.mem_univ,true_and]
    have hsum : (∑ b, source b p) = (U.card:ℝ)*common p := by
      simp only [source,hmem]
      rw [← Finset.sum_filter]
      have heq : Finset.univ.filter (fun b => b ∈ U) = U := by ext b; simp
      rw [heq]
      simp only [Finset.sum_const,nsmul_eq_mul]
    rw [hsum]
    apply mul_le_mul_of_nonneg_right _ (hcommon0 p)
    exact_mod_cast SourceSlopeLabels.active_union_card_le Finset.univ slope selector
      hd hlocal hK (fun b _ k s => hsupport b k s)
  have hbound (b : Λ) (i : ι b) (k : κ) (p : ℝ×ℝ) :
      ‖angularErrorWave (fun _ k => selector b k) (wave b) direction t d i k p‖ ≤
        tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 p*source b p := by
    by_cases ha : active b p
    · have he := multiplierError_bound (selector b k) t d small wide M Lip (direction p)
        hd hsmall hsmall1 hwide hM hLip (hselectorBound b k)
        (hnear b k (direction p)) (hfar b k (direction p))
      rw [angularErrorWave,norm_mul]
      have hm := mul_le_mul he (hwaveBound b i k p) (norm_nonneg _)
        (mul_nonneg (by linarith) (errorSourceProfile_nonneg _ _ _ _ hd (abs_nonneg _)))
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [source,common]
      rw [ite_eq_left ha]
      ring
    · have hu : selector b k (direction p) = 0 := by
        by_contra hu
        exact ha (Or.inl ⟨k,hu⟩)
      have ht : selector b k t = 0 := by
        by_contra ht
        exact ha (Or.inr ⟨k,ht⟩)
      simp only [angularErrorWave,multiplierError,hu,ht,ite_self,sub_self,zero_mul,norm_zero]
      exact mul_nonneg (tileEnvelope_nonneg _ _ _ _ _ _) (hsource0 b p)
  have hB : 0 ≤ (C*(2*M+Lip))*(1+small) := mul_nonneg hA (by linarith)
  have hfb (b : Λ) (p : ℝ×ℝ) : ‖source b p‖ ≤ (C*(2*M+Lip))*(1+small) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hsource0 b p)]
    dsimp [source]
    split_ifs
    · exact hcommonB p
    · exact hB
  calc
    _ ≤ ∑ b, (64*(4*Real.pi)^2)*planarPositiveConvolution l W (source b) z.1 z.2 := by
      apply Finset.sum_le_sum
      intro b _
      exact lattice_coefficient_convolution (site b) (hinj b) (originX b) (originY b) l W
        hl hW (source b) (hsourceMeas b) (hsource0 b) (hfb b)
        _ (angularErrorWave_measurable _ _ _ _ _ (fun i k => hselector b k) (hwave b) hdirection)
        (hbound b) g hg hg1 z
    _ = (64*(4*Real.pi)^2)*∑ b, planarPositiveConvolution l W (source b) z.1 z.2 :=
      (Finset.mul_sum ..).symm
    _ ≤ (64*(4*Real.pi)^2)*((2*((2*K+1)*H):ℕ)*planarPositiveConvolution l W common z.1 z.2) :=
      mul_le_mul_of_nonneg_left
        (sum_planarPositiveConvolution_le_source source hsourceMeas hsource0 common hcommon hcommon0
          hl hW (by positivity) hB hcommonB hoverlap z.1 z.2) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic angular errors on translated lattices with bounded local
multiplicity of slope labels. The common source is counted before integration. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem scaleError_le (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (y x : ℝ) :
    P.scaleError j y x ≤ (P.sources y).term j x := by
  have h := source_labeled_error_convolution (ι j) (P.site j) (P.site_injective j)
    (P.originX j) (P.originY j) (P.slope j)
    (div_pos P.topLength_pos (pow_pos (by norm_num) _)) P.width_pos
    (mul_pos P.angleBase_pos (pow_pos (by norm_num) _))
    P.packetBound_nonneg P.multiplierBound_nonneg P.multiplierLip_nonneg
    P.smallRatio_pos P.smallRatio_le P.wideRatio_ge (P.localMultiplicity j) P.radius_le
    (P.multiplier j) (P.multiplier_measurable j) (P.multiplier_bounded j)
    (P.multiplier_support j) P.direction P.direction_measurable P.referenceSlope
    (P.multiplier_near j) (P.multiplier_far j) (P.wave j) (P.wave_measurable j)
    (P.wave_bound j) P.test P.test_measurable P.test_bound (x,y)
  change P.scaleError j y x ≤ _ at h
  apply h.trans_eq
  rw [sources,actualErrorSources_term_eq]
  rw [← planarPositiveConvolution_const_mul]
  congr 1
  funext z
  unfold sourceAmplitude
  ring

theorem sources_log_budget (P : LabeledAngularErrorFamily N Λ κ ι) (y : ℝ) :
    (P.sources y).sumBound =
      (P.sourceAmplitude*((P.wideExponent+1:ℕ)+4*P.smallRatio+
        (4/Real.log 2)*Real.log ((2:ℝ)^P.exponent)))*Real.pi :=
  actualErrorSources_log_sumBound P.wideExponent P.exponent P.direction P.direction_measurable
    P.referenceSlope P.angleBase P.smallRatio P.wideConstant P.sourceAmplitude P.topLength P.width y
    P.angleBase_pos P.smallRatio_pos P.sourceAmplitude_nonneg P.wideConstant_le P.topLength_pos P.width_pos

end LabeledAngularErrorFamily
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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceLabeledAngularErrorData
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The labeled dyadic error family formed from the original physical
packets and selectors, with an exact measure-preserving coefficient identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem angularErrorFamily_coefficient (j : Fin N) (l : P.labels j) (u : Item j l) :
    (P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
      hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1).coefficient j l u =
      P.physicalAngularErrorCoefficient t a b v g j l u := by
  ext k
  simp only [LabeledAngularErrorFamily.coefficient,physicalAngularErrorCoefficient,analyzingCoefficient,
    WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g (slopeShear t z) k * conj
      (multiplierError (b j l k) t (a*(2:ℝ)^j.val) (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
        ∂volume.prod volume) = _
  have hw (z : ℝ×ℝ) : P.raw 0 j l u k z.2 z.1 = P.physicalPacket t j l u k (slopeShear t z) := by
    have h := congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
      (P.raw_eq_physical_slice 0 j l u k z.2 t)
    exact h
  simp_rw [hw]
  congr 1
  exact (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding
    (fun z => g z k * conj
      (multiplierError (b j l k) t (a*(2:ℝ)^j.val) (v z)*P.physicalPacket t j l u k z))

theorem angularErrorFamily_error (z : ℝ×ℝ) :
    (P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
      hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1).error z.2 z.1 =
      P.physicalAngularError t a b v g (slopeShear t z) := by
  unfold LabeledAngularErrorFamily.error LabeledAngularErrorFamily.scaleError physicalAngularError
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro u _
  rw [P.angularErrorFamily_coefficient horder t a c Cwide M Lip radius E J K H ha hc hc1
    hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1]
  have hy : (slopeShear t z).2-t*(slopeShear t z).1 = z.2 := by
    change z.2+t*z.1-t*z.1 = z.2
    ring
  simp only [hy,angularErrorFamily,LabeledAngularErrorFamily.length,zero_add]
  rfl

theorem physicalAngularError_measurable (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Measurable (P.physicalAngularError t a b v g) := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro l _
  apply Finset.measurable_sum
  intro u _
  apply measurable_const.mul
  exact (tileEnvelope_measurable _ _ _ _ _).comp
    (measurable_fst.prodMk (measurable_snd.sub (measurable_fst.const_mul t)))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledVariationSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed masked variation uses the full original analyzing
coefficients. Its centered main part has the narrow-slot variation
bound; its angular error is bounded by the positive physical error
sum, using the carrier-free synthesis envelope. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

theorem physicalMaskedBand_physical_continuous (j : Fin N) :
    Continuous (fun z : ℝ×ℝ => P.physicalMaskedBand
      alt hAlt t b v g T L A (z.2-t*z.1) j z.1) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  have hpoint : Continuous (fun z : ℝ×ℝ => (z.1,(z.2-t*z.1)+t*z.1)) := by fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (((T j l u).mask_continuous L A).comp hpoint))).mul
    (((P.withProfile alt hAlt).physicalPacket t j l u k).continuous.comp hpoint)

theorem physicalMaskedVariation_physical_continuous :
    Continuous (fun z : ℝ×ℝ => P.physicalMaskedVariation
      alt hAlt t b v g T L A (z.2-t*z.1) z.1) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalMaskedBand_physical_continuous alt hAlt t b v g T L A j
  · simp only [ite_eq_right hj]
    exact continuous_const

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed residual collection is grouped by stopping level in the
unary recurrence and by packet length in the reference-line variation.
Antitone stopping transports every disjoint collection of level bands
to disjoint length bands. Empty bands contribute zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem packetPartialSum_sub_eq_band {N : ℕ} {E : Type*} [AddCommGroup E]
    (f : Fin N → E) {a b : ℕ} (hab : a ≤ b) :
    packetPartialSum f b-packetPartialSum f a =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => a ≤ j.val ∧ j.val < b), f j := by
  simp only [packetPartialSum,Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j.val < a
  · have hjb : j.val < b := hja.trans_le hab
    simp [hja,hjb,not_le.mpr hja]
  · by_cases hjb : j.val < b
    · simp [hja,hjb,not_lt.mp hja]
    · simp [hja,hjb]

/-- Exact regrouping by stopping levels for any fixed packet subset. -/
theorem sum_packet_stopping_fibers {σ E : Type*} [AddCommMonoid E]
    (Q : Finset σ) (stop : σ → ℕ) (value : σ → E) (a b : ℕ) :
    (∑ k ∈ Finset.Ico a b, ∑ q ∈ Q.filter (fun q => stop q = k), value q) =
      ∑ q ∈ Q.filter (fun q => a ≤ stop q ∧ stop q < b), value q := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : stop q ∈ Finset.Ico a b
  · rw [Finset.sum_eq_single_of_mem (stop q) hq]
    · simp only [ite_true, if_true,ite_eq_left (Finset.mem_Ico.mp hq)]
    · intro k _ hk
      exact ite_eq_right (Ne.symm hk)
  · rw [Finset.sum_eq_zero]
    · exact (ite_eq_right (fun h => hq (Finset.mem_Ico.mpr h))).symm
    · intro k hk
      exact ite_eq_right (fun heq => hq (by simpa only [heq] using hk))

/-- Grouping by packet length preserves multiplicities and arbitrary
fixed packet selection. -/
theorem packet_stopping_band_eq_length_band {σ E : Type*} [AddCommMonoid E]
    {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N) (stop : Fin N → ℕ)
    (value : σ → E) (a b : ℕ) :
    (∑ q ∈ Q.filter (fun q => a ≤ stop (lengthIndex q) ∧ stop (lengthIndex q) < b), value q) =
      ∑ j ∈ Finset.univ.filter (fun j => a ≤ stop j ∧ stop j < b),
        ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q := by
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
    (Finset.sum_fiberwise_eq_sum_filter Q
      (Finset.univ.filter (fun j => a ≤ stop j ∧ stop j < b)) lengthIndex value).symm

/-- Zero-length intervals may be discarded before applying the finite
disjoint-interval variation bound. -/
theorem disjoint_increment_cube_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) (a b : ι → ℕ)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (hdisjoint : ∀ i j, i ≠ j → a i < b i → a j < b j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖F (b i)-F (a i)‖^3) ≤ finiteCubicVariation F N := by
  let active := Finset.univ.filter (fun i : ι => a i < b i)
  have hzero (i : ι) (hi : i ∈ Finset.univ) (hni : i ∉ active) :
      ‖F (b i)-F (a i)‖^3 = 0 := by
    have hn : ¬a i < b i := fun h => hni (Finset.mem_filter.mpr ⟨hi,h⟩)
    have heq : a i = b i := le_antisymm (hab i) (not_lt.mp hn)
    simp [heq]
  calc
    _ = ∑ i ∈ active, ‖F (b i)-F (a i)‖^3 :=
      (Finset.sum_subset (Finset.subset_univ active) hzero).symm
    _ = ∑ i : active, ‖F (b i.val)-F (a i.val)‖^3 := by
      exact (Finset.sum_subtype active (p := fun i => i ∈ active) (by simp)
        (fun i : ι => ‖F (b i)-F (a i)‖^3))
    _ ≤ _ := disjoint_increment_cube_sum_exact F N
      (fun i : active => a i.val) (fun i => b i.val)
      (fun i => (Finset.mem_filter.mp i.property).2) (fun i => hb i.val)
      (fun i j hij => hdisjoint i.val j.val (fun h => hij (Subtype.ext h))
        (Finset.mem_filter.mp i.property).2 (Finset.mem_filter.mp j.property).2)

/-- Disjoint stopping-level intervals become disjoint intervals of the
one fixed length sequence, including when some length fibers are empty. -/
theorem disjoint_stopping_band_cube_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] {N : ℕ} (f : Fin N → E)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (a b : ι → ℕ)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖∑ j ∈ Finset.univ.filter (fun j => a i ≤ stop j ∧ stop j < b i), f j‖^3) ≤
      finiteCubicVariation (packetPartialSum f) N := by
  choose lower upper hlu hu hband using fun i =>
    antitone_stopping_band_interval stop hstop (a i) (b i)
  have hdis (i j : ι) (hij : i ≠ j) (hi : lower i < upper i)
      (hj : lower j < upper j) : upper i ≤ lower j ∨ upper j ≤ lower i := by
    by_contra hn
    have h1 : lower j < upper i := by omega
    have h2 : lower i < upper j := by omega
    have hmaxi : max (lower i) (lower j) < upper i := max_lt_iff.mpr ⟨hi,h1⟩
    have hmaxj : max (lower i) (lower j) < upper j := max_lt_iff.mpr ⟨h2,hj⟩
    let k : Fin N := ⟨max (lower i) (lower j), hmaxi.trans_le (hu i)⟩
    have hki : a i ≤ stop k ∧ stop k < b i := (hband i k).mpr ⟨le_max_left _ _,hmaxi⟩
    have hkj : a j ≤ stop k ∧ stop k < b j := (hband j k).mpr ⟨le_max_right _ _,hmaxj⟩
    rcases hdisjoint i j hij with h | h <;> omega
  have heq (i : ι) :
      (∑ j ∈ Finset.univ.filter (fun j => a i ≤ stop j ∧ stop j < b i), f j) =
        packetPartialSum f (upper i)-packetPartialSum f (lower i) := by
    rw [packetPartialSum_sub_eq_band f (hlu i)]
    apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact hband i j
    · intro j _
      rfl
  simp_rw [heq]
  exact disjoint_increment_cube_sum (packetPartialSum f) N lower upper hlu hu hdis

/-- The cubic variation of the stop-grouped raw prefix is controlled by
the original length-grouped raw prefix, independently of angular depth. -/
theorem stopping_prefix_cubic_variation {σ E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (value : σ → E) (H : ℕ) :
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q
    let bands := fun j => ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q
    finiteCubicVariation (packetPrefix raw) H ≤
      finiteCubicVariation (packetPartialSum bands) N := by
  dsimp only
  apply Finset.sup'_le
  intro p _
  split_ifs with hp
  · have hband (i : Fin H) :
        packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q)
          (p i.succ)-
        packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q)
          (p i.castSucc) =
        ∑ j ∈ Finset.univ.filter (fun j => (p i.castSucc).val ≤ stop j ∧ stop j < (p i.succ).val),
          ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q := by
      rw [packetPrefix,packetPrefix,← Finset.sum_Ico_eq_sub _ (hp (Fin.castSucc_le_succ i)),
        sum_packet_stopping_fibers,packet_stopping_band_eq_length_band]
    simp_rw [hband]
    apply disjoint_stopping_band_cube_sum _ stop hstop
      (fun i : Fin H => (p i.castSucc).val) (fun i => (p i.succ).val)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hp (show i.succ ≤ j.castSucc by
        change i.val+1 ≤ j.val
        exact Nat.succ_le_of_lt h))
    · exact Or.inr (hp (show j.succ ≤ i.castSucc by
        change j.val+1 ≤ i.val
        exact Nat.succ_le_of_lt h))
  · exact finiteCubicVariation_nonneg _ _

end LipschitzHilbert

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

theorem cubicVariation_cube {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : cubicVariation F N ^ 3 = finiteCubicVariation F N := by
  rw [cubicVariation, ← Real.rpow_natCast, ← Real.rpow_mul (finiteCubicVariation_nonneg F N)]
  norm_num

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

/-- One fixed original variation controls the stopping prefix at every
angular horizon, without a factor depending on that horizon. -/
theorem physicalStoppingPrefix_variation_le (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) :
    finiteCubicVariation (P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x)) H ≤
      P.physicalMaskedVariation alt hAlt t b v g T L A y x ^ 3 := by
  have h := stopping_prefix_cubic_variation (Finset.univ : Finset P.PacketIndex)
    (fun q => q.1) stop hstop (P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x)) H
  dsimp only at h
  simp_rw [P.physicalMaskedValue_length_sum alt hAlt t b v g T L A y x] at h
  rw [physicalMaskedVariation,cubicVariation_cube]
  exact h

/-- The clamping in the stopped path theorem preserves this bound. -/
theorem physicalStoppingPrefix_clamped_variation_le (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) :
    finiteCubicVariation (fun k =>
      P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x) (min k H)) (2*H) ≤
        P.physicalMaskedVariation alt hAlt t b v g T L A y x ^ 3 := by
  apply (finiteCubicVariation_comp_le _ _ (fun k => min k H)
    (fun _ _ h => min_le_min h le_rfl) (min_le_left _ _)).trans
  exact P.physicalStoppingPrefix_variation_le alt hAlt t b v g T L A stop hstop y x (2*H)

theorem physicalStoppingPrefix_good_bound (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) {V : ℝ}
    (hV : P.physicalMaskedVariation alt hAlt t b v g T L A y x ≤ V) :
    finiteCubicVariation (fun k =>
      P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x) (min k H)) (2*H) ≤ V^3 := by
  exact (P.physicalStoppingPrefix_clamped_variation_le alt hAlt t b v g T L A
    stop hstop y x H).trans (pow_le_pow_left₀ (cubicVariation_nonneg _ _) hV 3)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceLabeledPacketRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any fixed residual packet subset is itself a lattice family, with
unchanged geometry, analyzing integrals and alternate synthesis waves.
Restricting the item fibers preserves the lattice constants exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Exact scalar/vector sums over the selected packet family. -/
theorem sum_restrictPackets {E : Type*} [AddCommMonoid E] (Q : Finset P.PacketIndex)
    (f : P.PacketIndex → E) :
    (∑ q : (P.restrictPackets Q).PacketIndex, f ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩) =
      ∑ q ∈ Q, f q := by
  have h := Equiv.sum_comp (P.restrictedPacketEquiv Q) (fun q : Q => f q.val)
  exact h.trans (Finset.sum_subtype Q (p := fun q => q ∈ Q) (by simp) f).symm

theorem sum_restrictPackets_filter {E : Type*} [AddCommMonoid E] (Q : Finset P.PacketIndex)
    (f : P.PacketIndex → E) (keep : P.PacketIndex → Prop) :
    (∑ q ∈ Finset.univ.filter (fun q : (P.restrictPackets Q).PacketIndex =>
      keep ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩), f ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩) =
      ∑ q ∈ Q.filter keep, f q := by
  simp only [Finset.sum_filter]
  exact P.sum_restrictPackets Q (fun q => if keep q then f q else 0)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem restrictPackets_physicalMaskedValue (Q : Finset P.PacketIndex)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (q : (P.restrictPackets Q).PacketIndex) :
    (P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val) L A z q =
      P.physicalMaskedValue alt hAlt t b v g T L A z ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩ := rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceErrorSupported
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error moments on a reference interval only use retained packet
lengths. Empty longer scales do not enlarge the interval. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.LineErrorSources
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

theorem restrictLength_source_zero (P : LineErrorSources N) (H : ℝ) (j : Fin N)
    (h : H < (P.restrictLength H).length j) : (P.restrictLength H).source j = 0 := by
  have hn : ¬ P.length j ≤ H := not_le.mpr h
  funext x
  simp only [restrictLength,ite_eq_right hn,Pi.zero_apply]

theorem majorant_root_integral_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hsource : ∀ j, g.width < P.length j → P.source j = 0) :
    (∫ x, P.majorant x ∂g.lineMeasure) ≤ P.meanConstant*g.width := by
  have heq : P.shortPart g.width = P.majorant := by
    funext x
    unfold shortPart majorant
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : P.length j ≤ g.width
    · exact ite_eq_left h
    · rw [ite_eq_right h]
      simp only [term,hsource j (lt_of_not_ge h),positiveConvolution]
      simp
  have h := P.shortPart_integral g.origin g.width g.width_pos
  rw [heq] at h
  have hi : IntegrableOn P.majorant (Icc (g.origin-g.width) (g.origin+g.width)) :=
    P.majorant_continuous.continuousOn.integrableOn_Icc
  have hsub : g.root ⊆ Icc (g.origin-g.width) (g.origin+g.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,g.width_pos],hx.2.le⟩
  exact (setIntegral_mono_set hi (Filter.Eventually.of_forall P.majorant_nonneg)
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))).trans h

theorem majorant_mean_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hsource : ∀ j, g.width < P.length j → P.source j = 0) :
    |integralAverage g.lineMeasure P.majorant| ≤ P.meanConstant := by
  have hmass : g.lineMeasure.real univ = g.width := by
    change (volume.restrict g.root).real univ = g.width
    simpa only [g.cell_zero,FiniteLineGrid.meshWidth,pow_zero,div_one] using g.cell_mass 0 0
  rw [integralAverage,smul_eq_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg),
    abs_of_nonneg (integral_nonneg P.majorant_nonneg),hmass]
  calc
    _ ≤ g.width⁻¹*(P.meanConstant*g.width) := mul_le_mul_of_nonneg_left
      (P.majorant_root_integral_of_supported g hsource) (inv_nonneg.mpr g.width_pos.le)
    _ = _ := by field_simp [g.width_pos.ne']

theorem majorant_moment_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hb : 1 < g.branching) (hsource : ∀ j, g.width < P.length j → P.source j = 0)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal (P.majorant x))^p ∂g.lineMeasure) ≤
      (2:ℝ≥0∞)^p*(7*ENNReal.ofReal
        ((p*(((g.branching:ℝ)+2)*(2*P.meanConstant+P.oscillationConstant+1))/Real.log (3/2))^p)+
        (ENNReal.ofReal P.meanConstant)^p)*g.lineMeasure univ := by
  have hi : Integrable P.majorant g.lineMeasure := by
    have h := g.continuous_integrable_cell P.majorant_continuous 0 0
    rwa [g.cell_zero] at h
  have hmean : 0 ≤ P.meanConstant := by
    unfold meanConstant
    exact mul_nonneg (by positivity) P.sumBound_nonneg
  have hosc : 0 ≤ P.oscillationConstant := by
    unfold oscillationConstant
    exact mul_nonneg (by positivity) P.sourceBound_nonneg
  have hA : 0 < 2*P.meanConstant+P.oscillationConstant+1 := by positivity
  have hBMO : g.HasFullMeanOscillationBound P.majorant
      (2*P.meanConstant+P.oscillationConstant+1) := by
    intro level i hi
    exact (P.majorant_mean_oscillation g level i hi).trans
      (mul_le_mul_of_nonneg_right (by linarith) (g.meshWidth_pos level).le)
  have h := g.continuous_raw_moment hb P.majorant P.majorant_continuous.measurable hi
    (fun _ _ => P.majorant_continuous.continuousAt) hA hBMO
    (P.majorant_mean_of_supported g hsource) hp
  simpa only [abs_of_nonneg (P.majorant_nonneg _)] using h

end LipschitzHilbert.LineErrorSources

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceErrorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial thresholds for the actual positive convolution error.
Only the source bound and its logarithmic scale sum enter the constants. -/

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace LipschitzHilbert.LineErrorSources

variable {N : ℕ}

theorem momentBase_pos (P : LineErrorSources N) (grid : FiniteLineGrid) :
    0 < P.momentBase grid := by
  have hsum := P.sumBound_nonneg
  have hsource := P.sourceBound_nonneg
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold momentBase meanConstant oscillationConstant
  positivity

theorem majorant_moment_natural (P : LineErrorSources N) (grid : FiniteLineGrid)
    (hb : 1 < grid.branching) (hsource : ∀ j, grid.width < P.length j → P.source j = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x, (ENNReal.ofReal (P.majorant x))^n ∂grid.lineMeasure) ≤
      ENNReal.ofReal ((P.momentBase grid*(n:ℝ))^n)*grid.lineMeasure univ := by
  have hmean : 0 ≤ P.meanConstant := by
    unfold meanConstant
    exact mul_nonneg (by positivity) P.sumBound_nonneg
  have hosc : 0 ≤ P.oscillationConstant := by
    unfold oscillationConstant
    exact mul_nonneg (by positivity) P.sourceBound_nonneg
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have h := ennreal_polynomial_moment_majorant
    ((((grid.branching:ℝ)+2)*(2*P.meanConstant+P.oscillationConstant+1))/Real.log (3/2))
    P.meanConstant (by positivity) hmean n hn
  have hm := P.majorant_moment_of_supported grid hb hsource (p := n) (Nat.cast_nonneg n)
  simp only [ENNReal.rpow_natCast] at hm
  exact hm.trans (mul_le_mul' (by simpa only [momentBase,mul_div_assoc,ENNReal.rpow_natCast] using h) le_rfl)

/-- A single order, chosen before the source family and interval, gives
the desired tail. No error majorant or concentration estimate is assumed. -/
theorem eventually_error_polynomial_tail (a J : ℝ) (ha : 0 ≤ a) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (P : LineErrorSources N)
      (grid : FiniteLineGrid), grid.branching = 2 →
      (∀ j, grid.width < P.length j → P.source j = 0) → P.sourceBound ≤ L^a → P.sumBound ≤ L^a →
      grid.lineMeasure {x | L^(a+4) ≤ P.majorant x} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ := by
  let K : ℝ := 16*((4*(2*(1024*Real.pi^2)+240*Real.pi+1))/Real.log (3/2)+
    1024*Real.pi^2+1)
  have hK : 0 < K := by
    have : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
    dsimp [K]
    positivity
  filter_upwards [eventually_source_reference_tail_order J hJ,
    eventually_ge_atTop (max 1 K)] with L hn hlarge
  obtain ⟨n,hn,hnL,hdecay⟩ := hn
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hKL : K ≤ L := (le_max_right _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hLa : 1 ≤ L^a := Real.one_le_rpow hL ha
  intro N P grid hb hsource hs hsum
  have hb' : 1 < grid.branching := by omega
  have hbase : P.momentBase grid ≤ K*L^a := by
    have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
    calc
      _ ≤ 16*((4*(2*((1024*Real.pi^2)*L^a)+(240*Real.pi)*L^a+L^a))/
          Real.log (3/2)+(1024*Real.pi^2)*L^a+L^a) := by
        unfold momentBase meanConstant oscillationConstant
        rw [hb]
        norm_num only [Nat.cast_ofNat]
        gcongr
      _ = _ := by dsimp [K]; ring
  have hthreshold : 4*(P.momentBase grid*(n:ℝ)) ≤ L^(a+4) := by
    calc
      _ = P.momentBase grid*(4*(n:ℝ)) := by ring
      _ ≤ (K*L^a)*L^2 := mul_le_mul hbase hnL (by positivity)
        (mul_nonneg hK.le (Real.rpow_nonneg hL0.le _))
      _ ≤ (L*L^a)*L^2 := by gcongr
      _ = L^(a+3) := by
        rw [Real.rpow_add hL0,show L^(3:ℝ) = L^(3:ℕ) from Real.rpow_natCast L 3]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hm := P.majorant_moment_natural grid hb' hsource n hn
  rw [ENNReal.ofReal_pow (mul_pos (P.momentBase_pos grid) hn0).le] at hm
  have ht := moment_superlevel_quarter grid.lineMeasure P.majorant P.majorant_continuous.measurable
    n (P.momentBase grid*(n:ℝ)) (mul_pos (P.momentBase_pos grid) hn0)
    (grid.lineMeasure univ) (by simpa only [abs_of_nonneg (P.majorant_nonneg _)] using hm)
  have hdecay' : (1/4:ℝ≥0∞)^n ≤ ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal hdecay
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at h
    norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat] at h
    simpa using h
  exact (measure_mono (fun x hx => by
    change 4*(P.momentBase grid*(n:ℝ)) ≤ |P.majorant x|
    rw [abs_of_nonneg (P.majorant_nonneg x)]
    exact hthreshold.trans hx)).trans (ht.trans (mul_le_mul' hdecay' le_rfl))

end LipschitzHilbert.LineErrorSources

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularErrorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The wide source cone costs only the proved logarithmic source sum.
Empty scales are removed before the reference-interval moment estimate. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

namespace LineErrorSources
variable {N : ℕ}

theorem restrictLength_term_eq (P : LineErrorSources N) (H : ℝ) (j : Fin N) (x : ℝ) :
    (P.restrictLength H).term j x = if P.length j ≤ H then P.term j x else 0 := by
  change positiveConvolution (P.length j)
    (fun x => if P.length j ≤ H then P.source j x else 0) x =
      if P.length j ≤ H then positiveConvolution (P.length j) (P.source j) x else 0
  by_cases h : P.length j ≤ H
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h,positiveConvolution,mul_zero,integral_zero]

end LineErrorSources

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTiledLineIntegral
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

/-- Finite top sums retain the same area constant. All original
integrands are integrable before their integrals are interchanged. -/
theorem source_plane_finite_area_sum {ι : Type*} (tops : Finset ι) (T : ι → SlopeBox)
    {K D : ℝ} (hK : 0 < K) (hD : 2 < D) (s H : ι → ℝ) (hH : ∀ i ∈ tops, 0 < H i)
    (C : ℝ) (f : ι → ℝ × ℝ → ℝ)
    (hfmeas : ∀ i ∈ tops, AEStronglyMeasurable (f i) (volume.prod volume))
    (hf : ∀ i ∈ tops, ∀ z, 0 ≤ f i z)
    (hlocal : ∀ i ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      IntegrableOn (fun x => f i (x,y+s i*x)) (sourceLineTile (H i) k) volume ∧
      (∫ x in sourceLineTile (H i) k, f i (x,y+s i*x)) ≤
        C*∫ x in sourceLineTile (H i) k, (T i).weight K D (x,y+s i*x)) :
    Integrable (fun z => ∑ i ∈ tops, f i z) (volume.prod volume) ∧
      (∫ z, ∑ i ∈ tops, f i z ∂volume.prod volume) ≤
        ((C*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2)*
          ∑ i ∈ tops, (T i).length*(T i).width := by
  have hi (i : ι) (hit : i ∈ tops) := source_plane_area_bound (T i) hK hD
    (s i) (H i) C (hH i hit) (f i) (hfmeas i hit) (hf i hit) (hlocal i hit)
  refine ⟨integrable_finsetSum tops (fun i hit => (hi i hit).1),?_⟩
  rw [integral_finsetSum tops (fun i hit => (hi i hit).1)]
  calc
    _ ≤ ∑ i ∈ tops, (C*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2*
        (T i).length*(T i).width := Finset.sum_le_sum fun i hit => (hi i hit).2
    _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedBadPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A reference-interval tail estimate retains the complete decaying top
weight. No restriction to the central part of the top is used. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

variable {X : Type*} [MeasurableSpace X]

theorem weighted_small_set_le (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (bad : Set X) (hbad : MeasurableSet bad) {c C δ : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hw : AEStronglyMeasurable w μ)
    (hlo : ∀ᵐ x ∂μ, c ≤ w x) (hhi : ∀ᵐ x ∂μ, w x ≤ C*c)
    (hsmall : μ.real bad ≤ δ*μ.real univ) :
    Integrable (bad.indicator w) μ ∧
      (∫ x, bad.indicator w x ∂μ) ≤ (C*δ)*(∫ x, w x ∂μ) := by
  have hw0 := hlo.mono fun _ hx => hc.trans hx
  have hwi : Integrable w μ := (integrable_const (C*c)).mono' hw (by
    filter_upwards [hw0,hhi] with x hx0 hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx0] using hx)
  have hlow : c*μ.real univ ≤ ∫ x, w x ∂μ := by
    simpa only [integral_const,smul_eq_mul,mul_comm] using
      integral_mono_ae (integrable_const c) hwi hlo
  refine ⟨hwi.indicator hbad,?_⟩
  have hupper : (∫ x, bad.indicator w x ∂μ) ≤ C*c*μ.real bad := by
    calc
      _ ≤ ∫ x, bad.indicator (fun _ => C*c) x ∂μ :=
        integral_mono_ae (hwi.indicator hbad) ((integrable_const (C*c)).indicator hbad)
          (hhi.mono fun x hx => by
            by_cases hxb : x ∈ bad
            · simpa only [indicator_of_mem hxb] using hx
            · simp only [indicator_of_notMem hxb,le_refl])
      _ = _ := by rw [integral_indicator hbad,integral_const]; simp [Measure.real,smul_eq_mul,mul_comm]
  calc
    _ ≤ C*c*μ.real bad := hupper
    _ ≤ C*c*(δ*μ.real univ) := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hC hc)
    _ = (C*δ)*(c*μ.real univ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (mul_nonneg hC hδ)

/-- On every interval of top length, an unweighted relative tail becomes
an equally small weighted tail, up to the fixed weight comparison factor. -/
theorem source_line_weighted_bad (T : SlopeBox) (origin y H : ℝ) {K D δ : ℝ}
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hH : 0 < H) (hHT : H ≤ T.length)
    (hδ : 0 ≤ δ) (bad : Set ℝ) (hbad : MeasurableSet bad)
    (hsmall : (volume.restrict (Ico origin (origin+H))).real bad ≤ δ*H) :
    IntegrableOn (bad.indicator (fun x => T.weight K D (x,y+T.slope*x)))
      (Ico origin (origin+H)) volume ∧
      (∫ x in Ico origin (origin+H), bad.indicator
        (fun x => T.weight K D (x,y+T.slope*x)) x) ≤
        (Real.exp (2*D)*δ)*(∫ x in Ico origin (origin+H), T.weight K D (x,y+T.slope*x)) := by
  let μ := volume.restrict (Ico origin (origin+H))
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp)
  let c := Real.exp (-D)*T.weight K D (origin,y+T.slope*origin)
  have hc : 0 ≤ c := by
    exact mul_nonneg (Real.exp_pos _).le (T.weight_pos (zero_lt_one.trans_le hK) _ _).le
  apply weighted_small_set_le μ _ bad hbad hc (Real.exp_pos _).le hδ
    (((T.continuous_weight (zero_lt_one.trans_le hK) D).comp (by fun_prop)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact (T.line_weight_comparable origin y x hK hD hHT hx).1
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    apply (T.line_weight_comparable origin y x hK hD hHT hx).2.trans_eq
    dsimp [c]
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  · have hu : μ.real univ = H := by
      simp only [μ,Measure.real,Measure.restrict_apply_univ,Real.volume_Ico,
        add_sub_cancel_left,ENNReal.toReal_ofReal hH.le]
    rwa [hu]

/-- Summing the line estimates over all tiles and then all tops retains
exactly the total top area and the full spatial weight. -/
theorem source_weighted_bad_path_area {ι : Type*} (tops : Finset ι)
    (T : ι → SlopeBox) (bad : ι → Set (ℝ × ℝ))
    (hbad : ∀ t ∈ tops, MeasurableSet (bad t)) {K D δ : ℝ}
    (hK : 1 ≤ K) (hD : 2 < D) (hδ : 0 ≤ δ)
    (htail : ∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      (volume.restrict (sourceLineTile (T t).length k)).real
        {x | (x,y+(T t).slope*x) ∈ bad t} ≤ δ*(T t).length) :
    Integrable (fun z => ∑ t ∈ tops, (bad t).indicator ((T t).weight K D) z)
      (volume.prod volume) ∧
      (∫ z, ∑ t ∈ tops, (bad t).indicator ((T t).weight K D) z ∂volume.prod volume) ≤
        (((Real.exp (2*D)*δ)*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2)*
          ∑ t ∈ tops, (T t).length*(T t).width := by
  apply source_plane_finite_area_sum tops T (zero_lt_one.trans_le hK) hD
    (fun t => (T t).slope) (fun t => (T t).length) (fun t _ => (T t).length_pos)
    (Real.exp (2*D)*δ) (fun t => (bad t).indicator ((T t).weight K D))
  · intro t ht
    exact (((T t).continuous_weight (zero_lt_one.trans_le hK) D).measurable.indicator
      (hbad t ht)).aestronglyMeasurable
  · intro t _ z
    exact indicator_nonneg (fun x _ => ((T t).weight_pos (zero_lt_one.trans_le hK) D x).le) z
  · intro t ht
    filter_upwards [htail t ht] with y hy
    intro k
    let B : Set ℝ := {x | (x,y+(T t).slope*x) ∈ bad t}
    have hB : MeasurableSet B := (hbad t ht).preimage (by fun_prop)
    have heq : sourceLineTile (T t).length k =
        Ico ((T t).length*k) ((T t).length*k+(T t).length) := by
      unfold sourceLineTile
      congr 1
      ring
    have hf : (fun x => (bad t).indicator ((T t).weight K D) (x,y+(T t).slope*x)) =
        B.indicator (fun x => (T t).weight K D (x,y+(T t).slope*x)) := by
      funext x
      by_cases hx : (x,y+(T t).slope*x) ∈ bad t
      · simp only [indicator_of_mem hx,indicator_of_mem (show x ∈ B from hx)]
      · simp only [indicator_of_notMem hx,indicator_of_notMem (show x ∉ B from hx)]
    have hb := source_line_weighted_bad (K := K) (D := D) (δ := δ)
      (T t) ((T t).length*k) y (T t).length
      hK (by linarith) (T t).length_pos le_rfl hδ B hB
      (by simpa only [← heq] using hy k)
    simpa only [hf,heq] using hb

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

theorem source_good_path_set_area (μ : Measure X) (base : Set X) (hbase : MeasurableSet base)
    (tops : Finset ι) (weight : ι → X → ℝ) (bad : ι → Set X)
    (hw : ∀ t ∈ tops, Measurable (weight t)) (hw0 : ∀ t x, 0 ≤ weight t x)
    (hbad : ∀ t ∈ tops, MeasurableSet (bad t)) (L S : ℝ)
    (hint : Integrable (sourceBadPathMass tops weight bad) μ)
    (hbound : (∫ x, sourceBadPathMass tops weight bad x ∂μ) ≤ S*Real.exp (-10*L)) :
    MeasurableSet (sourceGoodPathSet base tops weight bad L) ∧
      sourceGoodPathSet base tops weight bad L ⊆ base ∧
      μ (base \ sourceGoodPathSet base tops weight bad L) ≤ ENNReal.ofReal (S*Real.exp (-9*L)) := by
  let f := sourceBadPathMass tops weight bad
  have hf : Measurable f := Finset.measurable_sum _ (fun t ht => (hw t ht).indicator (hbad t ht))
  have hf0 (x : X) : 0 ≤ f x := Finset.sum_nonneg fun t _ =>
    indicator_nonneg (fun z _ => hw0 t z) x
  have heps : 0 < Real.exp (-L) := Real.exp_pos _
  have hfinite : μ {x | Real.exp (-L) ≤ f x} ≠ ∞ :=
    (hint.measure_ge_lt_top heps).ne
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hint
    (Real.exp (-L))
  have hreal : μ.real {x | Real.exp (-L) ≤ f x} ≤ S*Real.exp (-9*L) := by
    apply (mul_le_mul_iff_right₀ heps).mp
    have hexp : Real.exp (-L)*(S*Real.exp (-9*L)) = S*Real.exp (-10*L) := by
      rw [show Real.exp (-L)*(S*Real.exp (-9*L)) =
        S*(Real.exp (-9*L)*Real.exp (-L)) by ring,← Real.exp_add]
      congr 2
      ring
    rw [hexp]
    exact hm.trans hbound
  refine ⟨hbase.inter (measurableSet_le hf measurable_const),inter_subset_left,?_⟩
  apply (measure_mono (show base \ sourceGoodPathSet base tops weight bad L ⊆
      {x | Real.exp (-L) ≤ f x} from ?_)).trans
  · rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hreal
  · intro x hx
    have hn : ¬f x ≤ Real.exp (-L) := fun h => hx.2 ⟨hx.1,h⟩
    exact (lt_of_not_ge hn).le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledActiveCardTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only frozen-active labels need slots in the main reference tail.
Their cardinality follows from the original local slope multiplicity,
uniformly over the number of vector coordinates and inactive labels. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem frozenActiveLabels_card_local (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (j : Fin N) {d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d M)
    (hK : radius ≤ K)
    (hsupport : ∀ l k, b j l k t ≠ 0 →
      |t-(t+P.rowSlope j l)| ≤ radius*d) :
    (P.frozenActiveLabels t b j).card ≤ (2*K+1)*M := by
  have h := SourceSlopeLabels.active_card_le Finset.univ
    (fun l : P.labels j => t+P.rowSlope j l) (b j) hd hlocal hK
    (fun l _ k hk => hsupport l k hk)
  have hc := Fintype.card_congr (P.frozenActiveLabelsEquiv t b j)
  rw [Fintype.card_coe,Fintype.card_subtype] at hc
  apply hc.trans_le
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext l
  simp only [SourceSlopeLabels.active,Finset.mem_filter,Finset.mem_univ,true_and]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded active-label overlap gives the same logarithmic dyadic
source budget and exponential error tail, with no total-label count. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

/-- Every actual packet is short, even if the original index horizon
contains empty longer scales. -/
theorem error_le_restricted_majorant (P : LabeledAngularErrorFamily N Λ κ ι) (H : ℝ)
    (hshort : ∀ j b (_u : ι j b), P.length j ≤ H) (y x : ℝ) :
    P.error y x ≤ ((P.sources y).restrictLength H).majorant x := by
  apply Finset.sum_le_sum
  intro j _
  rw [LineErrorSources.restrictLength_term_eq]
  change P.scaleError j y x ≤ if P.length j ≤ H then (P.sources y).term j x else 0
  by_cases h : P.length j ≤ H
  · rw [ite_eq_left h]
    exact P.scaleError_le j y x
  · rw [ite_eq_right h]
    have heq : P.scaleError j y x = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro u _
      exact False.elim (h (hshort j b u))
    exact le_of_eq heq

/-- The exact dyadic source branching gives polynomial error-source
budgets without any dependence on the wide carrier constant. -/
theorem eventually_source_error_budgets (p : ℝ) (J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type) (ι : ∀ j, Λ j → Type)
      [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)] (P : LabeledAngularErrorFamily N Λ κ ι),
      P.sourceAmplitude ≤ L^p → P.wideExponent ≤ J₀ →
      P.exponent = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      ∀ y, (P.sources y).sourceBound ≤ L^(p+3) ∧ (P.sources y).sumBound ≤ L^(p+3) := by
  let c : ℝ := (J₀+1:ℕ)+4+4/Real.log 2
  have hc : 0 < c := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [c]
    positivity
  filter_upwards [SourceParameters.eventually_branching_separation,
    eventually_ge_atTop (max 1 (max (2*Real.pi) (c*Real.pi)))] with L hsep hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpi : 2*Real.pi ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hcpi : c*Real.pi ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hlogB : Real.log (SourceParameters.branching L) ≤ L := by
    have h := Real.log_le_log (pow_pos (SourceParameters.branching_pos L) 100) hsep
    rw [Real.log_pow,Real.log_exp] at h
    have hpow : L^(9/10:ℝ) ≤ L := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
        (by norm_num : (9/10:ℝ) ≤ 1)
    norm_num only [Nat.cast_ofNat] at h
    linarith
  intro N Λ κ ι _ _ _ P hP hJ hE y
  have hAmp := P.sourceAmplitude_nonneg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (P.sources y).sourceBound ≤ 2*Real.pi*L^p := by
    change (P.sourceAmplitude*(1+P.smallRatio))*Real.pi ≤ _
    have h := mul_le_mul hP (add_le_add_left P.smallRatio_le 1)
      (by linarith [P.smallRatio_pos]) (Real.rpow_nonneg hL0.le p)
    calc
      _ = (P.sourceAmplitude*(P.smallRatio+1))*Real.pi := by ring
      _ ≤ (L^p*(1+1))*Real.pi := mul_le_mul_of_nonneg_right h Real.pi_pos.le
      _ = _ := by ring
  have hwide : ((P.wideExponent+1:ℕ):ℝ)+4*P.smallRatio+
      (4/Real.log 2)*Real.log ((2:ℝ)^P.exponent) ≤ c*L := by
    have hJ' : ((P.wideExponent+1:ℕ):ℝ) ≤ (J₀+1:ℕ) := by exact_mod_cast Nat.add_le_add_right hJ 1
    have hlog : Real.log ((2:ℝ)^P.exponent) ≤ L := by
      rw [hE,← source_branching_eq_two_pow]
      exact hlogB
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4/Real.log 2)
    have hsmall := P.smallRatio_le
    have hconstant := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ ((J₀+1:ℕ):ℝ)+4 by positivity)
    dsimp [c]
    nlinarith
  have hsmall0 := P.smallRatio_pos.le
  have hlog0 : 0 ≤ Real.log ((2:ℝ)^P.exponent) :=
    Real.log_nonneg (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hsum : (P.sources y).sumBound ≤ c*Real.pi*L^(p+1) := by
    rw [P.sources_log_budget]
    calc
      _ ≤ (L^p*(c*L))*Real.pi := by gcongr
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
  have hpow : L^(p+2) ≤ L^(p+3) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  constructor
  · apply hs.trans
    calc
      _ ≤ L*L^p := mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg hL0.le _)
      _ = L^(p+1) := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  · apply hsum.trans
    calc
      _ ≤ L*L^(p+1) := mul_le_mul_of_nonneg_right hcpi (Real.rpow_nonneg hL0.le _)
      _ = L^((p+1)+1) := by
        conv_rhs => rw [Real.rpow_add hL0,Real.rpow_one]
        ring
      _ = L^(p+2) := by congr 1; ring
      _ ≤ _ := hpow

/-- The actual angular error has a polynomial threshold and arbitrary
exponential tail on every binary reference interval of retained lengths. -/
theorem eventually_source_error_tail (p J : ℝ) (hp : 0 ≤ p) (hJ : 0 ≤ J) (J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type) (ι : ∀ j, Λ j → Type)
      [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)] (P : LabeledAngularErrorFamily N Λ κ ι),
      P.sourceAmplitude ≤ L^p → P.wideExponent ≤ J₀ →
      P.exponent = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      ∀ (y : ℝ) (grid : FiniteLineGrid), grid.branching = 2 →
      (∀ j b (_u : ι j b), P.length j ≤ grid.width) →
      grid.lineMeasure {x | L^(p+7) ≤ P.error y x} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ := by
  filter_upwards [eventually_source_error_budgets p J₀,
    LineErrorSources.eventually_error_polynomial_tail (p+3) J (by linarith) hJ]
    with L hbudget htail
  intro N Λ κ ι _ _ _ P hP hJ₀ hE y grid hb hshort
  have hbud := hbudget N Λ κ ι P hP hJ₀ hE y
  let Q := (P.sources y).restrictLength grid.width
  have ht := htail N Q grid hb
    ((P.sources y).restrictLength_source_zero grid.width) hbud.1 hbud.2
  have hsub : {x | L^(p+7) ≤ P.error y x} ⊆ {x | L^((p+3)+4) ≤ Q.majorant x} := by
    intro x hx
    rw [show (p+3)+4 = p+7 by ring]
    exact hx.trans (P.error_le_restricted_majorant grid.width hshort y x)
  exact (measure_mono hsub).trans ht

/-- The labeled error tail on every original physical interval. -/
theorem eventually_source_error_physical_tail (p J : ℝ) (hp : 0 ≤ p) (hJ : 0 ≤ J)
    (J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type) (ι : ∀ j, Λ j → Type)
      [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]
      (P : LabeledAngularErrorFamily N Λ κ ι),
      P.sourceAmplitude ≤ L^p → P.wideExponent ≤ J₀ →
      P.exponent = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      ∀ (y u H : ℝ), 0 < H → (∀ j b (_i : ι j b), P.length j ≤ H) →
      (volume.restrict (Ico u (u+H))) {x | L^(p+7) ≤ P.error y x} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [eventually_source_error_tail p J hp hJ J₀] with L htail
  intro N Λ κ ι _ _ _ P hP hJ₀ hE y u H hH hshort
  let grid : FiniteLineGrid :=
    { branching := 2, branching_pos := by decide, origin := u,
      width := H, width_pos := hH, depth := 0 }
  have ht := htail N Λ κ ι P hP hJ₀ hE y grid rfl hshort
  have hm : grid.lineMeasure univ = ENNReal.ofReal H := by
    change (volume.restrict (Ico u (u+H))) univ = _
    rw [Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  rwa [hm] at ht

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed profile order, geometric bounds, and selector multiplicity give
polynomial source constants without a factor counting the available labels. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

namespace LabeledAngularErrorFamily

theorem eventually_sourceAmplitude_le (K H : ℕ) (M D p : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type)
      (ι : ∀ j, Λ j → Type) [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]
      (P : LabeledAngularErrorFamily N Λ κ ι),
      P.radiusBound ≤ K → P.multiplicity ≤ H →
      P.multiplierBound ≤ M → P.multiplierLip ≤ D → P.packetBound ≤ L^p →
      P.sourceAmplitude ≤ L^(p+1) := by
  let C : ℝ := ((64*(4*Real.pi)^2)*(2*((2*K+1)*H):ℕ))*(2*M+D)
  filter_upwards [eventually_ge_atTop (max 1 C)] with L hlarge
  have hL : 0 < L := zero_lt_one.trans_le ((le_max_left _ _).trans hlarge)
  have hC : C ≤ L := (le_max_right _ _).trans hlarge
  intro N Λ κ ι _ _ _ P hK hH hPM hPD hP
  have hn : 2*((2*P.radiusBound+1)*P.multiplicity) ≤ 2*((2*K+1)*H) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hK) 1) hH)
  have hn' : (2*((2*P.radiusBound+1)*P.multiplicity):ℕ) ≤
      (2*((2*K+1)*H):ℕ) := hn
  have hr : ((2*((2*P.radiusBound+1)*P.multiplicity):ℕ):ℝ) ≤
      (2*((2*K+1)*H):ℕ) := by exact_mod_cast hn'
  have hB : 0 ≤ 2*P.multiplierBound+P.multiplierLip := by
    linarith [P.multiplierBound_nonneg,P.multiplierLip_nonneg]
  calc
    P.sourceAmplitude ≤ ((64*(4*Real.pi)^2)*(2*((2*K+1)*H):ℕ))*(L^p*(2*M+D)) := by
      unfold sourceAmplitude
      exact mul_le_mul (mul_le_mul_of_nonneg_left hr (by positivity))
        (mul_le_mul hP (by linarith) hB (Real.rpow_nonneg hL.le _))
        (mul_nonneg P.packetBound_nonneg hB) (by positivity)
    _ = C*L^p := by dsimp [C]; ring
    _ ≤ L*L^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL.le _)
    _ = L^(p+1) := by rw [Real.rpow_add hL,Real.rpow_one]; ring

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodQuantities
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability of the actual reference quantities is needed
before weighted bad-path sets are integrated over the physical plane. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem lineEnvelope_continuous (a l : ℝ) (n : ℕ) : Continuous (lineEnvelope a l n) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalMainScale_joint_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) :
    Continuous (fun z : ℝ×ℝ => P.physicalMainScale t a b v g j z.2 z.1) := by
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  apply Continuous.mul continuous_const
  exact ((lineEnvelope_continuous _ _ _).comp continuous_fst).mul
    ((lineEnvelope_continuous _ _ _).comp continuous_snd)

theorem physicalMainSquare_joint_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Continuous (fun z : ℝ×ℝ => P.physicalMainSquare t a b v g z.2 z.1) := by
  apply Continuous.sqrt
  exact continuous_finsetSum _ (fun j _ =>
    (P.physicalMainScale_joint_continuous t a b v g j).pow 2)

theorem physicalMainSquareOnPlane_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Continuous (P.physicalMainSquareOnPlane t a b v g) := by
  let shear : ℝ×ℝ → ℝ×ℝ := fun z => (z.1,z.2-t*z.1)
  have hs : Continuous shear :=
    continuous_fst.prodMk (continuous_snd.sub (continuous_const.mul continuous_fst))
  have h := (P.physicalMainSquare_joint_continuous t a b v g).comp hs
  change Continuous ((fun z : ℝ×ℝ =>
    P.physicalMainSquare t a b v g z.2 z.1) ∘ shear)
  exact h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodEvents
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable reference events for the original error, positive main
square and full masked variation. All three thresholds are fixed before
the angular path or mass cutoff is selected. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

theorem physicalReferenceEvent_measurable (i : Fin 3) :
    MeasurableSet (P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i) := by
  unfold physicalReferenceEvent
  split_ifs
  · exact measurableSet_le measurable_const (P.physicalAngularError_measurable t a b v g)
  · exact measurableSet_le measurable_const (P.physicalMainSquareOnPlane_continuous t a b v g).measurable
  · exact measurableSet_le measurable_const
      (P.physicalMaskedVariation_physical_continuous alt hAlt t b v g T L A).measurable

theorem physicalReferenceBad_measurable :
    MeasurableSet (P.physicalReferenceBad alt hAlt t a b v g T L A e s r) :=
  MeasurableSet.iUnion (P.physicalReferenceEvent_measurable alt hAlt t a b v g T L A e s r)

theorem physicalReferenceBad_compl_bounds (z : ℝ×ℝ)
    (hz : z ∉ P.physicalReferenceBad alt hAlt t a b v g T L A e s r) :
    P.physicalAngularError t a b v g z < L^e ∧
    P.physicalMainSquareOnPlane t a b v g z < L^s ∧
    P.physicalMaskedVariation alt hAlt t b v g T L A (z.2-t*z.1) z.1 < L^r := by
  have h (i : Fin 3) : z ∉ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i :=
    fun hi => hz (mem_iUnion.mpr ⟨i,hi⟩)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [physicalReferenceEvent,ite_true, if_true,Set.mem_ofPred_eq] at h0
  simp only [physicalReferenceEvent,show (1 : Fin 3) ≠ 0 by decide,ite_false, if_false,ite_true, if_true,
    Set.mem_ofPred_eq] at h1
  simp only [physicalReferenceEvent,show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide,ite_false, if_false,Set.mem_ofPred_eq] at h2
  exact ⟨lt_of_not_ge h0,lt_of_not_ge h1,lt_of_not_ge h2⟩

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledSelectedVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact stopping prefixes for the fixed residual subset. The variation
is that of its literal restricted physical family; subset selection causes
no additional factor in any profile or geometric constant. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem selectedPhysicalPrefix_eq_restricted (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop z =
      (P.restrictPackets Q).physicalStoppingPrefix (P.restrictedAlternate alt Q)
        (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
        L A stop z := by
  unfold selectedPhysicalPrefix physicalStoppingPrefix
  congr 1
  funext k
  symm
  simp_rw [P.restrictPackets_physicalMaskedValue alt hAlt Q]
  ext i
  simp only [WithLp.ofLp_sum,Finset.sum_apply]
  convert P.sum_restrictPackets_filter Q
    (fun q => P.physicalMaskedValue alt hAlt t b v g T L A z q i)
    (fun q => stop q.1 = k) using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> ext q <;> simp)

/-- The original fixed residual subset has the required clamped prefix
bound on its own reference event, for every angular horizon. -/
theorem selectedPhysicalPrefix_good_bound (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (y x : ℝ) (H : ℕ) {V : ℝ}
    (hV : (P.restrictPackets Q).physicalMaskedVariation (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
      L A y x ≤ V) :
    finiteCubicVariation (fun k =>
      P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop (x,y+t*x) (min k H)) (2*H) ≤ V^3 := by
  rw [P.selectedPhysicalPrefix_eq_restricted alt hAlt t b v g T L A Q stop]
  exact (P.restrictPackets Q).physicalStoppingPrefix_good_bound (P.restrictedAlternate alt Q)
    (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
    L A stop hstop y x H hV

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledUniformErrorTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original physical error tail, uniform before choosing the packet
family and the reference line. Fixed selector multiplicity and Lipschitz
bounds absorb the source-amplitude factor in one polynomial power. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

/-- Uniform physical error tail with its source-amplitude budget discharged.
The geometric hypotheses are exactly those of the labeled error family. -/
theorem eventually_uniform_physicalAngularError_tail
    (q rate M Lip : ℝ) (hq : 0 ≤ q) (hrate : 0 ≤ rate)
    (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (K H J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (_horder : 6 ≤ P.order),
      P.absoluteConstant ≤ L^q →
    ∀ (t a c Cwide radius : ℝ) (E J : ℕ)
      (_ha : 0 < a) (_hc : 0 < c) (_hc1 : c ≤ 1)
      (_hC : Cwide ≤ c*(2:ℝ)^J) (_hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
      (_hradius : radius ≤ K)
      (_hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k))
      (_hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
      (_hsupport : ∀ j l k s, b j l k s ≠ 0 →
        |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
      (_hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
      (_hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| →
        b j l k s = 0)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∀ (y u W : ℝ), 0 < W → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ W) →
      (volume.restrict (Ico u (u+W)))
        {x | L^(q+8) ≤ P.physicalAngularError t a b v g (x,y+t*x)} ≤
          ENNReal.ofReal (Real.exp (-rate*L))*ENNReal.ofReal W := by
  filter_upwards [LabeledAngularErrorFamily.eventually_source_error_physical_tail
      (q+1) rate (by linarith) hrate J₀,
    LabeledAngularErrorFamily.eventually_sourceAmplitude_le K H M Lip q]
    with L htail hbudget
  intro N κ Label Item _ _ P horder hP t a c Cwide radius E J
    ha hc hc1 hC hwide hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
    hJ hE y u W hW hshort
  let Q := P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
    hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
  have hAmp : Q.sourceAmplitude ≤ L^(q+1) :=
    hbudget N (fun j => P.labels j) κ (fun j l => Item j l) Q
      le_rfl le_rfl le_rfl le_rfl hP
  have ht := htail N (fun j => P.labels j) κ (fun j l => Item j l) Q
    hAmp hJ hE y u W hW hshort
  have heq (x : ℝ) : Q.error y x = P.physicalAngularError t a b v g (x,y+t*x) := by
    exact P.angularErrorFamily_error horder t a c Cwide M Lip radius E J K H
      ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1 (x,y)
  simpa only [heq,show q+1+7 = q+8 by ring] using ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledUniformGoodTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform local tails for the actual physical reference bad set.
All three component tails follow from original packet spectra, selector
bounds and slope multiplicity. No tail or active-cardinality premise is
retained, and the threshold is selected before the packet family. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_uniform_physical_reference_good_tail (hVariation : LepingleInput)
    (q J A F cStar cEta CEta cb Cb maskCone Lip : ℝ) (K Hlabels J₀ : ℕ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hLip : 0 ≤ Lip) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (_horder : 6 ≤ P.order),
      P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t cutoff c Cwide radius : ℝ) (E Jcut : ℕ)
      (_hcutoff : 0 < cutoff) (_hc : 0 < c) (_hc1 : c ≤ 1)
      (_hC : Cwide ≤ c*(2:ℝ)^Jcut) (_hwideError : 1 ≤ Cwide*((2:ℝ)^E)^4)
      (_hradius : radius ≤ K)
      (_hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (cutoff*(2:ℝ)^j.val) Hlabels)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
      (_hsupport : ∀ j l k s, b j l k s ≠ 0 →
        |s-(t+P.rowSlope j l)| ≤ radius*(cutoff*(2:ℝ)^j.val))
      (_hnear : ∀ j l k s, |s-t| ≤ c*(cutoff*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(cutoff*(2:ℝ)^j.val)))
      (_hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(cutoff*(2:ℝ)^j.val) < |s-t| →
        b j l k s = 0)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      Jcut ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∀ (w : ℝ), 0 < w → Cb*w ≤ P.width → (∀ k, |P.frequency k| ≤ F/w) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
    ∀ (y u W : ℝ), 0 < W → (∀ j (_l : P.labels j), P.length j ≤ W) →
      (∀ j l u, P.length j ≤ W → |P.rowSlope j l| ≤ Cb*w/P.length j →
        |t-(T j l u).slope| ≤ maskCone*(T j l u).width/P.length j) →
      (volume.restrict (Ico u (u+W)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t cutoff b v g T L A
          (q+8) (2*q+9) (2*q+11)} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal W := by
  filter_upwards [eventually_physical_reference_good_spectral_tail hVariation
      ((2*K+1)*Hlabels) q q (q+1) J A F cStar cEta CEta cb Cb maskCone
      hq hJ hA hF hcStar hcEta hCEta hcb hCb hmaskCone hgap,
    eventually_uniform_physicalAngularError_tail q (J+2) 1 Lip hq (by linarith)
      (by norm_num) hLip K Hlabels J₀] with L hgood herror
  intro N κ Label Item _ _ P horder hP alt hAlt t cutoff c Cwide radius E Jcut
    hcutoff hc hc1 hC hwideError hradius hlocal b hb hb1 hsupport hnear hfar v hv g hg hg1
    hJcut hE w hw hwide hfrequency hspectrum haltSpectrum hselector T hlength
    y u W hW hshort hangle
  have hcard (j : Fin N) : (P.frozenActiveLabels t b j).card ≤ (2*K+1)*Hlabels :=
    P.frozenActiveLabels_card_local t b j (mul_pos hcutoff (by positivity)) (hlocal j)
      hradius (fun l k hk => hsupport j l k t hk)
  have he := herror N κ Label Item P horder hP t cutoff c Cwide radius E Jcut
    hcutoff hc hc1 hC hwideError hradius hlocal b hb hb1 hsupport hnear hfar v hv g hg hg1
    hJcut hE y u W hW (fun j l _i => hshort j l)
  have ht := hgood N κ Label Item P horder hP hP alt hAlt t W w hw hwide hfrequency
    cutoff hcutoff.le b hb hb1 v hv g hg hg1 (fun j l _k _hk => hshort j l) hcard
    hspectrum haltSpectrum hselector T hlength hangle y u W hW le_rfl
      (by simpa only [show q+1+7 = q+8 by ring] using he)
  have hexp : max (2*q+10) (q+(q+1)+7)+1 = 2*q+11 := by
    rw [max_eq_left (by linarith)]
    ring
  simpa only [hexp,show q+1+7 = q+8 by ring] using ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalGoodPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted good-path construction for actual physical reference
packets. A reference bundle only packages the original formulas; it has
no probabilistic or path estimate as a field. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert

namespace PhysicalReferenceData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PhysicalReferenceData N κ Label Item)

theorem bad_measurable (L A e s r : ℝ) : MeasurableSet (P.bad L A e s r) :=
  P.family.physicalReferenceBad_measurable P.alternate P.alternate_bound P.slope P.angle
    P.selector P.direction P.test P.packetTop L A e s r

end PhysicalReferenceData

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePolynomialGoodPathArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weight scales are admitted before forming the common
reference bad set. The weighted bad mass retains its integral bound,
and Markov's inequality gives the same area loss for the common good set. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

theorem eventually_source_polynomial_good_path_area
    (D eventPower weightPower : ℝ) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (K : ℝ), 1 ≤ K → K ≤ L^weightPower →
    ∀ (ι σ : Type*) (tops : Finset ι) (T : ι → SlopeBox)
      (events : ι → Finset σ) (event : ι → σ → Set (ℝ×ℝ))
      (bad : ι → Set (ℝ×ℝ)) (base : Set (ℝ×ℝ)), MeasurableSet base →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
      (∀ t ∈ tops, bad t ⊆ ⋃ i ∈ events t, event t i) →
      (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^eventPower) →
      (∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ, ∀ i ∈ events t,
        (volume.restrict (sourceLineTile (T t).length k))
          {x | (x,y+(T t).slope*x) ∈ event t i} ≤
        ENNReal.ofReal (Real.exp (-12*L))*
          (volume.restrict (sourceLineTile (T t).length k)) univ) →
    let weight := fun t => (T t).weight K D
    let S := ∑ t ∈ tops, (T t).length*(T t).width
    let good := sourceGoodPathSet base tops weight bad L
    Integrable (sourceBadPathMass tops weight bad) (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops weight bad z ∂volume.prod volume) ≤
        S*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal (S*Real.exp (-9*L)) := by
  let c := Real.exp (2*D)*(2^D*∫ z, topProfile D z ∂volume.prod volume)
  filter_upwards [eventually_source_bad_event_tail eventPower 11,
    eventually_source_polynomial_exp (|c|+1) (2*weightPower) 10 (by positivity),
    eventually_ge_atTop (1:ℝ)] with L htail hsmall hL
  intro K hK hKL ι σ tops T events event bad base hbase hbad hcover hcard hevent
    weight S good
  have hlocal : ∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      (volume.restrict (sourceLineTile (T t).length k)).real
        {x | (x,y+(T t).slope*x) ∈ bad t} ≤ Real.exp (-11*L)*(T t).length := by
    intro t ht
    filter_upwards [hevent t ht] with y hy
    intro k
    let μ := volume.restrict (sourceLineTile (T t).length k)
    have h := htail σ ℝ μ (events t)
      (fun i => {x | (x,y+(T t).slope*x) ∈ event t i}) (hcard t ht) (by
        intro i hi
        simpa only [show -(11+1:ℝ)*L = -12*L by ring] using hy k i hi)
    have hsub : {x | (x,y+(T t).slope*x) ∈ bad t} ⊆
        ⋃ i ∈ events t, {x | (x,y+(T t).slope*x) ∈ event t i} := by
      intro x hx
      simpa only [mem_iUnion,mem_ofPred_eq] using hcover t ht hx
    have hlen : μ univ = ENNReal.ofReal (T t).length := by
      simp only [μ,Measure.restrict_apply_univ,sourceLineTile,Real.volume_Ico]
      congr 1
      ring
    have hb := (measure_mono hsub).trans h
    rw [hlen,← ENNReal.ofReal_mul (Real.exp_pos _).le] at hb
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (T t).length_pos.le))
  have hweighted := source_weighted_bad_path_area tops T bad hbad hK hD
    (Real.exp_pos (-11*L)).le hlocal
  have hKsq : K^2 ≤ L^(2*weightPower) := by
    calc
      K^2 ≤ (L^weightPower)^2 := pow_le_pow_left₀ (by linarith) hKL 2
      _ = L^(2*weightPower) := by
        rw [← Real.rpow_two,← Real.rpow_mul (zero_le_one.trans hL)]
        congr 1
        ring
  have hconstant : c*K^2*Real.exp (-11*L) ≤ Real.exp (-10*L) := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul (show c ≤ |c|+1 from (le_abs_self c).trans (by linarith)) hKsq
        (sq_nonneg K) (by positivity)) (Real.exp_pos _).le).trans
    simpa only [show -(10+1:ℝ)*L = -11*L by ring] using hsmall
  have hbound : (∫ z, sourceBadPathMass tops weight bad z ∂volume.prod volume) ≤
      S*Real.exp (-10*L) := by
    calc
      _ ≤ (((Real.exp (2*D)*Real.exp (-11*L))*
        (2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2)*S := hweighted.2
      _ = (c*K^2*Real.exp (-11*L))*S := by dsimp only [c]; ring
      _ ≤ Real.exp (-10*L)*S := mul_le_mul_of_nonneg_right hconstant
        (Finset.sum_nonneg fun t _ => mul_nonneg (T t).length_pos.le (T t).width_pos.le)
      _ = _ := mul_comm _ _
  have hgood := source_good_path_set_area (volume.prod volume) base hbase tops weight bad
    (fun t _ => ((T t).continuous_weight (zero_lt_one.trans_le hK) D).measurable)
    (fun t z => ((T t).weight_pos (zero_lt_one.trans_le hK) D z).le)
    hbad L S hweighted.1 hbound
  exact ⟨hweighted.1,hbound,hgood⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSelectedGoodEvent
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference event of a fixed selected packet family controls its
actual stopped prefixes and every disjoint unary run at the same point. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

/-- A good reference point bounds the selected physical stopping prefix
at every angular horizon, with its original analyzing coefficients. -/
theorem selectedPhysicalPrefix_good_event_bound (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (z : ℝ×ℝ)
    (hz : z ∉ (P.restrictPackets Q).physicalReferenceBad (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t a b v g (fun j l u => T j l u.val)
      L A e s r) (H : ℕ) :
    finiteCubicVariation (fun k => P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop z
      (min k H)) (2*H) ≤ (L^r)^3 := by
  have hgood := (P.restrictPackets Q).physicalReferenceBad_compl_bounds
    (P.restrictedAlternate alt Q) (P.restrictedAlternate_bound alt hAlt Q)
    t a b v g (fun j l u => T j l u.val) L A e s r z hz
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have h := P.selectedPhysicalPrefix_good_bound alt hAlt t b v g T L A Q stop hstop
    (z.2-t*z.1) z.1 H hgood.2.2.le
  simpa only [hpoint] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSelectedReferenceData
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected reference family retains the original physical packets,
coefficients and top masks. Its spatial item type depends on the selected
finite subset, while its good event directly controls the original
selected stopping prefixes and all unary runs. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert
namespace PhysicalReferenceData

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PhysicalReferenceData N κ Label Item)

theorem selectedPrefix_good_bound (Q : Finset P.family.PacketIndex) (L A e s r : ℝ)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (z : ℝ×ℝ)
    (hz : z ∉ (P.restrictPackets Q).bad L A e s r) (H : ℕ) :
    finiteCubicVariation (fun k => P.family.selectedPhysicalPrefix P.alternate P.alternate_bound
      P.slope P.selector P.direction P.test P.packetTop L A Q stop z (min k H)) (2*H) ≤
        (L^r)^3 :=
  P.family.selectedPhysicalPrefix_good_event_bound P.alternate P.alternate_bound
    P.slope P.angle P.selector P.direction P.test P.packetTop L A e s r Q stop hstop z hz H

end PhysicalReferenceData

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePolynomialReferenceArea
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference-event construction with a polynomially growing top-weight
scale. The same finite union controls the original selected prefixes and
retains its weighted integral, not only the area of the removed set. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

theorem eventually_polynomial_selected_reference_prefix_area
    (D eventPower weightPower : ℝ) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (K : ℝ), 1 ≤ K → K ≤ L^weightPower →
    ∀ (ι σ : Type*) (tops : Finset ι) (T : ι → SlopeBox)
      (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → σ → PhysicalReferenceData N κ Label Item)
      (Q : ∀ t i, Finset (P t i).family.PacketIndex)
      (A e s r : ℝ) (base : Set (ℝ×ℝ)),
      MeasurableSet base → (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^eventPower) →
      (∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ, ∀ i ∈ events t,
        (volume.restrict (sourceLineTile (T t).length k))
          {x | (x,y+(T t).slope*x) ∈ ((P t i).restrictPackets (Q t i)).bad L A e s r} ≤
        ENNReal.ofReal (Real.exp (-12*L))*
          (volume.restrict (sourceLineTile (T t).length k)) univ) →
      let bad := fun t => ⋃ i ∈ events t, ((P t i).restrictPackets (Q t i)).bad L A e s r
      let weight := fun t => (T t).weight K D
      let good := sourceGoodPathSet base tops weight bad L
      Integrable (sourceBadPathMass tops weight bad) (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops weight bad z ∂volume.prod volume) ≤
        (∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      ∀ t, ∀ z ∉ bad t, ∀ i ∈ events t,
        z ∉ ((P t i).restrictPackets (Q t i)).bad L A e s r ∧
        ∀ (stop : Fin N → ℕ), Antitone stop → ∀ H : ℕ,
          finiteCubicVariation (fun k => (P t i).family.selectedPhysicalPrefix
            (P t i).alternate (P t i).alternate_bound (P t i).slope (P t i).selector
            (P t i).direction (P t i).test (P t i).packetTop L A (Q t i) stop z (min k H))
            (2*H) ≤ (L^r)^3 := by
  filter_upwards [eventually_source_polynomial_good_path_area D eventPower weightPower hD]
    with L harea
  intro K hK hKL ι σ tops T events N κ Label Item _ _ P Q A e s r base hbase hcard htail
    bad weight good
  have hbad (t : ι) : MeasurableSet (bad t) :=
    MeasurableSet.biUnion (Finset.countable_toSet (events t))
      (fun i _ => ((P t i).restrictPackets (Q t i)).bad_measurable L A e s r)
  have ha := harea K hK hKL ι σ tops T events
    (fun t i => ((P t i).restrictPackets (Q t i)).bad L A e s r)
    bad base hbase (fun t _ => hbad t) (fun _ _ => Subset.rfl) hcard htail
  refine ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2,?_⟩
  intro t z hz i hi
  have hzi : z ∉ ((P t i).restrictPackets (Q t i)).bad L A e s r := by
    intro hmem
    exact hz (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hmem⟩⟩)
  exact ⟨hzi,fun stop hstop H =>
    (P t i).selectedPrefix_good_bound (Q t i) L A e s r stop hstop z hzi H⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePolynomialSelectedGoodPath
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-reference weighted good set follows from original
packet spectra and selector hypotheses. The component event estimates
are proved internally, including the exact reference/path slope change.
No exceptional-set or variation estimate is supplied as source data. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

theorem eventually_polynomial_uniform_selected_reference_good_path_oai
    (hVariation : LepingleInput)
    (D eventPower weightPower q A F cStar cEta CEta cb Cb maskCone Lip : ℝ)
    (K Hlabels J₀ : ℕ) (hD : 2 < D)
    (hq : 0 ≤ q) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hLip : 0 ≤ Lip) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw : ℝ), 1 ≤ Kw → Kw ≤ L^weightPower →
    ∀ (ι σ : Type*) (tops : Finset ι) (pathTop : ι → SlopeBox)
      (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → σ → PhysicalReferenceData N κ Label Item)
      (Q : ∀ t i, Finset (P t i).family.PacketIndex) (base : Set (ℝ×ℝ)),
      MeasurableSet base → (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^eventPower) →
      (∀ t ∈ tops, ∀ i ∈ events t,
        let R := P t i
        6 ≤ R.family.order ∧ R.family.absoluteConstant ≤ L^q ∧ R.slope = (pathTop t).slope ∧
        ∃ (c Cwide radius : ℝ) (E Jcut : ℕ) (w : ℝ),
          0 < R.angle ∧ 0 < c ∧ c ≤ 1 ∧ Cwide ≤ c*(2:ℝ)^Jcut ∧
          1 ≤ Cwide*((2:ℝ)^E)^4 ∧ radius ≤ K ∧
          (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
            (fun l : R.family.labels j => R.slope+R.family.rowSlope j l)
            (R.angle*(2:ℝ)^j.val) Hlabels) ∧
          (∀ j l k, Measurable (R.selector j l k)) ∧
          (∀ j l k s, ‖R.selector j l k s‖ ≤ 1) ∧
          (∀ j l k s, R.selector j l k s ≠ 0 →
            |s-(R.slope+R.family.rowSlope j l)| ≤ radius*(R.angle*(2:ℝ)^j.val)) ∧
          (∀ j l k s, |s-R.slope| ≤ c*(R.angle*(2:ℝ)^j.val) →
            ‖R.selector j l k s-R.selector j l k R.slope‖ ≤
              Lip*(|s-R.slope|/(R.angle*(2:ℝ)^j.val))) ∧
          (∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(R.angle*(2:ℝ)^j.val) < |s-R.slope| →
            R.selector j l k s = 0) ∧
          Measurable R.direction ∧ Measurable R.test ∧ (∀ z, ‖R.test z‖ ≤ 1) ∧
          Jcut ≤ J₀ ∧ E = SourceParameters.stepExponent L*SourceParameters.blockCount L ∧
          0 < w ∧ Cb*w ≤ R.family.width ∧ (∀ k, |R.family.frequency k| ≤ F/w) ∧
          (∀ j l u k xi eta,
            planarAngularFourier (R.family.physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
              |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
                cEta ≤ w*eta ∧ w*eta ≤ CEta) ∧
          (∀ j l u k xi eta,
            planarAngularFourier ((R.family.withProfile R.alternate R.alternate_bound).physicalPacket
              R.slope j l u k) (xi,eta) ≠ 0 →
              |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
                cEta ≤ w*eta ∧ w*eta ≤ CEta) ∧
          (∀ j l, (∃ k, R.selector j l k R.slope ≠ 0) →
            cb*w/R.family.length j ≤ |R.family.rowSlope j l| ∧
              |R.family.rowSlope j l| ≤ Cb*w/R.family.length j) ∧
          (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ Q t i →
            R.family.length j ≤ (R.packetTop j l u).length) ∧
          (∀ j (_l : R.family.labels j), R.family.length j ≤ (pathTop t).length) ∧
          (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ Q t i →
            R.family.length j ≤ (pathTop t).length →
            |R.family.rowSlope j l| ≤ Cb*w/R.family.length j →
            |R.slope-(R.packetTop j l u).slope| ≤
              maskCone*(R.packetTop j l u).width/R.family.length j)) →
      let bad := fun t => ⋃ i ∈ events t, ((P t i).restrictPackets (Q t i)).bad
        L A (q+8) (2*q+9) (2*q+11)
      let good := sourceGoodPathSet base tops (fun t => (pathTop t).weight Kw D) bad L
      Integrable (sourceBadPathMass tops (fun t => (pathTop t).weight Kw D) bad)
        (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops (fun t => (pathTop t).weight Kw D) bad z
        ∂volume.prod volume) ≤
        (∑ t ∈ tops, (pathTop t).length*(pathTop t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (pathTop t).length*(pathTop t).width)*Real.exp (-9*L)) ∧
      ∀ t, ∀ z ∉ bad t, ∀ i ∈ events t,
        z ∉ ((P t i).restrictPackets (Q t i)).bad L A (q+8) (2*q+9) (2*q+11) ∧
        ∀ (stop : Fin N → ℕ), Antitone stop → ∀ H : ℕ,
          finiteCubicVariation (fun k => (P t i).family.selectedPhysicalPrefix
            (P t i).alternate (P t i).alternate_bound (P t i).slope (P t i).selector
            (P t i).direction (P t i).test (P t i).packetTop L A (Q t i) stop z (min k H))
            (2*H) ≤ (L^(2*q+11))^3 := by
  filter_upwards [SourceLabeledLattice.eventually_uniform_physical_reference_good_tail
      hVariation q 12 A F cStar cEta CEta cb Cb maskCone Lip K Hlabels J₀
      hq (by norm_num) hA hF hcStar hcEta hCEta hcb hCb hmaskCone hLip hgap,
    eventually_polynomial_selected_reference_prefix_area D eventPower weightPower hD] with L htail harea
  intro Kw hKw hKwL ι σ tops pathTop events N κ Label Item _ _ P Q base hbase hcard hdata
  apply harea Kw hKw hKwL ι σ tops pathTop events N κ Label Item P Q A (q+8) (2*q+9) (2*q+11)
    base hbase hcard
  intro t ht
  filter_upwards [] with y
  intro tile i hi
  obtain ⟨horder,hP,hslope,c,Cwide,radius,E,Jcut,w,hcutoff,hc,hc1,hC,hwideError,hradius,
    hlocal,hb,hb1,hsupport,hnear,hfar,hv,hg,hg1,hJcut,hE,hw,hwide,hfrequency,
    hspectrum,haltSpectrum,hselector,hlength,hshort,hangle⟩ := hdata t ht i hi
  let R := P t i
  let Fsel := R.family.restrictPackets (Q t i)
  let alt := R.family.restrictedAlternate R.alternate (Q t i)
  have hmem (j : Fin N) (l : Fsel.labels j)
      (u : R.family.RestrictedPacketItem (Q t i) j l) :
      (⟨j,⟨l,u.val⟩⟩ : R.family.PacketIndex) ∈ Q t i := by
    obtain ⟨_,hm⟩ := u.property
    exact hm
  have hAlt := R.family.restrictedAlternate_bound R.alternate R.alternate_bound (Q t i)
  have hspectrum' : ∀ j l u k xi eta,
      planarAngularFourier (Fsel.physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
        |xi+(R.slope+Fsel.rowSlope j l)*eta| ≤ cStar/Fsel.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hxi
    exact hspectrum j l u.val k xi eta hxi
  have haltSpectrum' : ∀ j l u k xi eta,
      planarAngularFourier ((Fsel.withProfile alt hAlt).physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
        |xi+(R.slope+Fsel.rowSlope j l)*eta| ≤ cStar/Fsel.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hxi
    exact haltSpectrum j l u.val k xi eta hxi
  have h := htail N κ Label (R.family.RestrictedPacketItem (Q t i)) Fsel horder hP
    alt hAlt R.slope R.angle c Cwide radius E Jcut hcutoff hc hc1 hC hwideError hradius
    hlocal R.selector hb hb1 hsupport hnear hfar R.direction hv R.test hg hg1 hJcut hE
    w hw hwide hfrequency hspectrum' haltSpectrum' hselector
    (fun j l u => R.packetTop j l u.val) (fun j l u => hlength j l u.val (hmem j l u))
    y ((pathTop t).length*tile) (pathTop t).length (pathTop t).length_pos hshort
    (fun j l u => hangle j l u.val (hmem j l u))
  have htile : sourceLineTile (pathTop t).length tile =
      Ico ((pathTop t).length*tile) ((pathTop t).length*tile+(pathTop t).length) := by
    unfold sourceLineTile
    congr 1
    ring
  have hmeasure : (volume.restrict (sourceLineTile (pathTop t).length tile)) univ =
      ENNReal.ofReal (pathTop t).length := by
    rw [htile,Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  rw [hmeasure,htile]
  have hbad : ((P t i).restrictPackets (Q t i)).bad L A (q+8) (2*q+9) (2*q+11) =
      Fsel.physicalReferenceBad alt hAlt R.slope R.angle R.selector R.direction R.test
        (fun j l u => R.packetTop j l u.val) L A (q+8) (2*q+9) (2*q+11) := rfl
  rw [hbad]
  have hslope' : R.slope = (pathTop t).slope := hslope
  simpa only [hslope'] using h

end LipschitzHilbert

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path_oai.{u_1, u_2} := @OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path_oai.{u_1, u_2}
