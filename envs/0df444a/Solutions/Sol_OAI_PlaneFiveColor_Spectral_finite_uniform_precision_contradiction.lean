-- Prove2me | solution 1 for OAI.PlaneFiveColor.Spectral.finite_uniform_precision_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:15:47.246999+00:00
-- url     : https://prove2.me/submissions/88e0cd41-aee3-4ab6-9d8a-8d6453eaf4a3

import Mathlib
import Definitions.Def_OAIQ5T4002

section
-- module Solutions.OAIQ5_T4.Compat
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_PhaseEncoding
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators

open scoped BigOperators
open Polynomial
namespace EuclideanFiveColor.PhaseEncoding

section

theorem polynomial_expansion {m : ℕ} (z : Fin m → Circle) :
    phasePolynomial z = ∑ n ∈ Finset.range (m + 1),
      (-1) ^ n * (C (elem z n) * X ^ (m - n)) := by
  have he : phasePolynomial z = ((phases z).map (fun t => X - C t)).prod := by
    rw [phasePolynomial, Finset.prod_eq_multiset_prod]
    simp only [phases, Multiset.map_map, Function.comp_def]
  rw [he, Multiset.prod_X_sub_X_eq_sum_esymm, card_phases]
  rfl

theorem eval_expansion {m : ℕ} (z : Fin m → Circle) (a : ℂ) :
    (phasePolynomial z).eval a = ∑ n ∈ Finset.range (m + 1),
      (-1 : ℂ) ^ n * (elem z n * a ^ (m - n)) := by
  rw [polynomial_expansion, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  simp

theorem eval_difference {m : ℕ} (z w : Fin m → Circle) (a : ℂ) :
    (phasePolynomial w).eval a - (phasePolynomial z).eval a =
      ∑ n ∈ Finset.range m,
        (-1 : ℂ) ^ (n+1) * ((elem w (n+1) - elem z (n+1)) * a ^ (m-(n+1))) := by
  rw [eval_expansion, eval_expansion, ← Finset.sum_sub_distrib,
    Finset.sum_range_succ']
  simp only [pow_zero, elem_zero, one_mul, sub_self, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- A coefficient bound on the unit circle, with the common leading term removed. -/
theorem eval_difference_bound {m : ℕ} (z w : Fin m → Circle) (a : Circle) :
    ‖(phasePolynomial w).eval (a : ℂ) - (phasePolynomial z).eval (a : ℂ)‖ ≤
      m * dist (encoding z) (encoding w) := by
  rw [eval_difference]
  calc
    _ ≤ ∑ n ∈ Finset.range m,
      ‖(-1 : ℂ) ^ (n+1) * ((elem w (n+1) - elem z (n+1)) * (a : ℂ) ^ (m-(n+1)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range m, dist (encoding z) (encoding w) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, Circle.norm_coe,
        one_mul, mul_one]
      have h := dist_le_pi_dist (encoding z) (encoding w) ⟨n, Finset.mem_range.mp hn⟩
      simpa only [dist_eq_norm, encoding, norm_sub_rev] using h
    _ = _ := by simp

/-- An explicit uniform inverse estimate sufficient for the phase collision step. -/
theorem close_encoding_each_phase {m : ℕ} (hm : 0 < m)
    (z w : Fin m → Circle) {ρ : ℝ} (hρ : 0 < ρ)
    (hzw : dist (encoding z) (encoding w) < ρ ^ m / m) :
    ∀ i, ∃ j, dist (z i : ℂ) (w j : ℂ) < ρ := by
  intro i
  by_contra h
  push Not at h
  have hl : ρ ^ m ≤ ‖(phasePolynomial w).eval (z i : ℂ)‖ := by
    rw [phasePolynomial, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [norm_prod]
    calc
      ρ ^ m = ∏ _j : Fin m, ρ := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hρ.le) (fun j _ => by
        simpa only [dist_eq_norm] using h j)
  have hu := eval_difference_bound z w (z i)
  rw [eval_at_phase, sub_zero] at hu
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hb : (m : ℝ) * dist (encoding z) (encoding w) < ρ ^ m := by
    simpa only [mul_comm] using (lt_div_iff₀ hm').mp hzw
  exact (not_lt_of_ge (hl.trans hu)) hb

open scoped BigOperators

lemma measurable_fromPowers {Y : Type*} [MeasurableSpace Y] (p : Y → ℕ → ℂ)
    (hp : ∀ n, Measurable (fun y => p y n)) (n : ℕ) :
    Measurable (fun y => fromPowers (p y) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [fromPowers]; exact measurable_const
    | succ k =>
      simp only [fromPowers]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i _
      exact (Measurable.const_mul (ih i i.isLt) _).mul (hp _)

lemma newton_elem {m : ℕ} (z : Fin m → Circle) (k : ℕ) :
    (k : ℂ) * elem z k = (-1) ^ (k + 1) *
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * elem z a.1 * (∑ i, (z i : ℂ) ^ a.2) := by
  have h := congrArg (MvPolynomial.aeval (fun i => (z i : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum (Fin m) ℂ k)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X,
    elem, phases] using h

lemma filtered_antidiagonal_sum (f : ℕ → ℕ → ℂ) (k : ℕ) :
    (∑ a ∈ (Finset.HasAntidiagonal.antidiagonal (k+1)).filter (fun a => a.1 < k+1), f a.1 a.2) =
      ∑ i : Fin (k+1), f i (k+1-i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f i (k+1-i)) (k+1), Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

theorem fromPowers_eq_elem {m : ℕ} (z : Fin m → Circle) (n : ℕ) :
    fromPowers (fun k => ∑ i, (z i : ℂ) ^ k) n = elem z n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [fromPowers]
    | succ k =>
      rw [fromPowers]
      have hs : (∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) *
          fromPowers (fun n => ∑ j, (z j : ℂ)^n) i * (∑ j, (z j : ℂ)^(k+1-i))) =
          ∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) * elem z i *
            (∑ j, (z j : ℂ)^(k+1-i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ih i i.isLt]
      rw [hs, mul_assoc, ← filtered_antidiagonal_sum
        (fun i j => (-1 : ℂ)^i * elem z i * (∑ l, (z l : ℂ)^j)) k]
      have hn := newton_elem z (k+1)
      rw [Nat.cast_add, Nat.cast_one] at hn
      rw [← hn, inv_mul_cancel_left₀]
      exact_mod_cast (Nat.succ_ne_zero k)

end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Y G : Type*} [MeasurableSpace Y] [MeasurableSpace G]

theorem measurable_kernelEncoding (β : Kernel Y G) [IsMarkovKernel β]
    (χ : G → ℂ) (hχ : Measurable χ) (m : ℕ) :
    Measurable (kernelEncoding β χ m) := by
  apply Measurable.of_eval
  intro i
  apply measurable_fromPowers
  intro n
  exact (((hχ.pow_const n).stronglyMeasurable.integral_kernel).measurable).const_mul _

theorem moments_uniform_list [MeasurableSingletonClass G] (χ : G → ℂ) (m : ℕ) (hm : 0 < m) (g : Fin m → G)
    (μ : Measure G) (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i))
    (n : ℕ) :
    (m : ℂ) * (∫ d, χ d ^ n ∂μ) = ∑ i, χ (g i) ^ n := by
  classical
  rw [hμ, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [← mul_assoc, mul_inv_cancel₀, one_mul]
    exact_mod_cast hm.ne'
  · intro i _
    exact integrable_dirac (by simp)

/-- On every uniform finite fiber, the formula is exactly the source's
 elementary-symmetric vector, including repetitions of equal phases. -/
theorem kernelEncoding_eq_encoding [MeasurableSingletonClass G] (β : Kernel Y G) (χ : G → Circle)
    (m : ℕ) (hm : 0 < m) (y : Y) (g : Fin m → G)
    (hβ : β y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i)) :
    kernelEncoding β (fun d => (χ d : ℂ)) m y = encoding (fun i => χ (g i)) := by
  have hp : (fun n => (m : ℂ) * ∫ d, (χ d : ℂ)^n ∂β y) =
      fun n => ∑ i, (χ (g i) : ℂ)^n := by
    funext n
    exact moments_uniform_list (fun d => (χ d : ℂ)) m hm g (β y) hβ n
  funext i
  change fromPowers _ (i.val+1) = elem _ (i.val+1)
  rw [hp]
  exact fromPowers_eq_elem (fun i => χ (g i)) (i.val+1)

end

end EuclideanFiveColor.PhaseEncoding

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_PhaseCollision
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

open scoped BigOperators
namespace EuclideanFiveColor.PhaseCollision

section

variable {ι κ V : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] OAI.EuclideanFiveColor.PhaseCollision.instDecidableEq_solutions_1
omit [Fintype ι] in
lemma sameBin_card (s : Finset ι) (f : ι → κ) :
    ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card =
      ∑ b : κ, (s.filter (fun i => f i = b)).card ^ 2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ι × ι => f p.1)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro b _
  have he : (((s ×ˢ s).filter (fun p => f p.1 = f p.2)).filter
      (fun p => f p.1 = b)) =
      (s.filter (fun i => f i = b)) ×ˢ (s.filter (fun i => f i = b)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    aesop
  rw [he, Finset.card_product, pow_two]

omit [Fintype ι] [Fintype κ] in
lemma sameBin_card_eq (s : Finset ι) (f : ι → κ) :
    ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card =
      (repeatedPairs s f).card + s.card := by
  classical
  let T := (s ×ˢ s).filter (fun p => f p.1 = f p.2)
  have hsplit := Finset.card_filter_add_card_filter_not (s := T)
    (p := fun p => p.1 ≠ p.2)
  have hfirst : T.filter (fun p => p.1 ≠ p.2) = repeatedPairs s f := by
    ext p
    simp only [T, repeatedPairs, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsecond : T.filter (fun p => ¬p.1 ≠ p.2) = s.diag := by
    ext p
    simp only [T, Finset.mem_filter, Finset.mem_product, not_not, Finset.mem_diag]
    aesop
  rw [hfirst, hsecond, Finset.diag_card] at hsplit
  exact hsplit.symm

/- Sum of squares, with diagonal pairs removed. -/
omit [Fintype ι] in
theorem repeated_bin_lower_bound (s : Finset ι) (f : ι → κ) :
    (s.card : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) *
      ((repeatedPairs s f).card + (s.card : ℝ)) := by
  classical
  have hs : ∑ b : κ, (s.filter (fun i => f i = b)).card = s.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hs' : ∑ b : κ, ((s.filter (fun i => f i = b)).card : ℝ) = s.card := by
    exact_mod_cast hs
  have hpair : ∑ b : κ, ((s.filter (fun i => f i = b)).card : ℝ) ^ 2 =
      (repeatedPairs s f).card + (s.card : ℝ) := by
    exact_mod_cast (sameBin_card s f).symm.trans (sameBin_card_eq s f)
  simpa only [hs', hpair, Finset.card_univ] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun b : κ => ((s.filter (fun i => f i = b)).card : ℝ)))

variable [PseudoMetricSpace V]

theorem close_pair_lower_bound (s : Finset ι) (f : ι → κ)
    (v : ι → V) (w : κ → V) (r : ℝ)
    (h : ∀ i ∈ s, dist (v i) (w (f i)) ≤ r) :
    (s.card : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) *
      ((closePairs v (2 * r)).card + (Fintype.card ι : ℝ)) := by
  classical
  have hsub : repeatedPairs s f ⊆ closePairs v (2 * r) := by
    intro p hp
    simp only [repeatedPairs, Finset.mem_filter, Finset.mem_product] at hp
    simp only [closePairs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hp.2.1, ?_⟩
    calc
      dist (v p.1) (v p.2) ≤ dist (v p.1) (w (f p.1)) +
          dist (w (f p.1)) (v p.2) := dist_triangle _ _ _
      _ ≤ r + r := by
        apply add_le_add (h p.1 hp.1.1)
        rw [hp.2.2, dist_comm]
        exact h p.2 hp.1.2
      _ = 2 * r := by ring
  calc
    _ ≤ (Fintype.card κ : ℝ) * ((repeatedPairs s f).card + (s.card : ℝ)) :=
      repeated_bin_lower_bound s f
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (Nat.cast_le.mpr (Finset.card_le_card hsub))
        (Nat.cast_le.mpr (Finset.card_le_univ s))) (Nat.cast_nonneg _)

/-- The normalized source estimate `q² / #bins - 1/#indices`. -/
theorem normalized_close_pair_lower_bound [Nonempty ι] [Nonempty κ]
    (s : Finset ι) (f : ι → κ) (v : ι → V) (w : κ → V) (r : ℝ)
    (h : ∀ i ∈ s, dist (v i) (w (f i)) ≤ r) :
    ((s.card : ℝ) / Fintype.card ι) ^ 2 / Fintype.card κ - 1 / Fintype.card ι ≤
      (closePairs v (2 * r)).card / (Fintype.card ι : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hm : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  have hc := close_pair_lower_bound s f v w r h
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  field_simp
  nlinarith

end

open MeasureTheory
open scoped BigOperators

variable {Ω ι κ V : Type*} [MeasurableSpace Ω]
variable [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] [PseudoMetricSpace V]

/-- Larger than 95 percent average phase coverage forces a colliding pair.
The bins and assignments may depend on the sampled point; no measurable
choice of assignments is required. -/
theorem average_cover_forces_collision (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Finset ι) (f : Ω → ι → κ) (v : Ω → ι → V) (w : Ω → κ → V)
    (r : ℝ)
    (hcov : ∀ᵐ x ∂μ, ∀ i ∈ s x, dist (v x i) (w x (f x i)) ≤ r)
    (hm : ∀ i j, Measurable (fun x => dist (v x i) (v x j)))
    (hq : Measurable (fun x => ((s x).card : ℝ) / Fintype.card ι))
    (hlarge : 10 * Fintype.card κ < Fintype.card ι)
    (havg : (19/20 : ℝ) < ∫ x, ((s x).card : ℝ) / Fintype.card ι ∂μ) :
    ∃ i j : ι, i ≠ j ∧
      1 / (4 * (Fintype.card κ : ℝ)) ≤ μ.real {x | dist (v x i) (v x j) ≤ 2*r} := by
  classical
  let n : ℝ := Fintype.card ι
  let k : ℝ := Fintype.card κ
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hk : 0 < k := Nat.cast_pos.mpr Fintype.card_pos
  have hlarge' : 10*k < n := by dsimp [k, n]; exact_mod_cast hlarge
  let q : Ω → ℝ := fun x => (s x).card / n
  have hq0 (x) : 0 ≤ q x := div_nonneg (Nat.cast_nonneg _) hn.le
  have hq1 (x) : q x ≤ 1 := by
    apply (div_le_one hn).mpr
    dsimp [n]
    exact_mod_cast Finset.card_le_univ (s x)
  have hiq : Integrable q μ := Integrable.of_bound hq.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hq0 x)]; exact hq1 x))
  have hiq2 : Integrable (fun x => (q x)^2) μ := Integrable.of_bound
    (hq.pow_const 2).aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (hq0 x) (hq1 x)))
  have hsq : (19/20 : ℝ)^2 < ∫ x, (q x)^2 ∂μ := by
    have hv : 0 ≤ ∫ x, (q x-19/20)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (q x - 19/20))
    have he : (fun x => (q x-19/20)^2) =
        (fun x => (q x)^2 - (19/10)*q x + (19/20)^2) := by funext x; ring
    have hsub : Integrable (fun x => (q x)^2 - (19/10)*q x) μ :=
      hiq2.sub (hiq.const_mul (19/10))
    rw [he, integral_add hsub (integrable_const ((19/20 : ℝ)^2)),
      integral_sub hiq2 (hiq.const_mul (19/10)), integral_const_mul] at hv
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul] at hv
    change 19/20 < ∫ x, q x ∂μ at havg
    linarith
  let a : (ι × ι) → Ω → ℝ := fun p x =>
    if p.1 ≠ p.2 ∧ dist (v x p.1) (v x p.2) ≤ 2*r then 1 else 0
  have hma (p : ι × ι) : Measurable (a p) := by
    have hset : MeasurableSet {x | p.1 ≠ p.2 ∧ dist (v x p.1) (v x p.2) ≤ 2*r} := by
      by_cases h : p.1 = p.2
      · simp [h]
      · simpa [h] using
          (measurableSet_le (hm p.1 p.2) (measurable_const (a := 2*r)))
    exact measurable_const.ite hset measurable_const
  have hia (p : ι × ι) : Integrable (a p) μ := Integrable.of_bound
    (hma p).aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun x => by
      dsimp [a]; split_ifs <;> norm_num))
  have hcnt (x : Ω) : ((closePairs (v x) (2*r)).card : ℝ) = ∑ p, a p x := by
    simp only [closePairs, a, Finset.cast_card, Finset.sum_filter]
  have hic : Integrable (fun x => ((closePairs (v x) (2*r)).card : ℝ)/n^2) μ := by
    simp_rw [hcnt]
    exact (integrable_finsetSum _ (fun p _ => hia p)).div_const _
  have hlow := integral_mono_ae (μ := μ) ((hiq2.div_const k).sub (integrable_const (1/n))) hic
    (hcov.mono (fun x hx =>
      normalized_close_pair_lower_bound (s x) (f x) (v x) (w x) r hx))
  simp only [Pi.sub_apply] at hlow
  rw [integral_sub (hiq2.div_const k) (integrable_const (1/n)), integral_div,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlow
  have hstrict : 1/(4*k) < (∫ x, (q x)^2 ∂μ)/k - 1/n := by
    have hi : 1/n < 1/(10*k) := one_div_lt_one_div_of_lt (by positivity) hlarge'
    have hsq' := (div_lt_div_iff_of_pos_right hk).mpr hsq
    apply lt_of_lt_of_le _ (le_of_lt (sub_lt_sub hsq' hi))
    field_simp
    norm_num
  by_contra hh
  push Not at hh
  have hailt (p : ι × ι) : ∫ x, a p x ∂μ < 1/(4*k) := by
    by_cases hp : p.1 = p.2
    · simp only [a, hp, ne_eq, not_true_eq_false, false_and, ↓reduceIte, integral_zero]
      positivity
    · have he : a p = Set.indicator {x | dist (v x p.1) (v x p.2) ≤ 2*r}
          (fun _ => (1 : ℝ)) := by
        funext x
        simp [a, hp, Set.indicator_apply]
      rw [he, integral_indicator (measurableSet_le (hm p.1 p.2) measurable_const)]
      simpa only [setIntegral_const, Measure.real, smul_eq_mul, mul_one] using hh p.1 p.2 hp
  have hiupper : (∫ x, ((closePairs (v x) (2*r)).card : ℝ)/n^2 ∂μ) < 1/(4*k) := by
    simp_rw [hcnt]
    rw [integral_div, integral_finsetSum _ (fun p _ => hia p)]
    have hsum := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (ι × ι)))
      Finset.univ_nonempty (fun p _ => hailt p)
    have hnum : (∑ _p : ι × ι, 1/(4*k)) = n^2/(4*k) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
        Nat.cast_mul, n, pow_two, mul_div_assoc]
      ring
    rw [hnum] at hsum
    apply (div_lt_iff₀ (sq_pos_of_pos hn)).mpr
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact (not_lt_of_ge (hstrict.le.trans hlow)) hiupper

end EuclideanFiveColor.PhaseCollision

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial

open MeasureTheory
open scoped BigOperators
namespace EuclideanFiveColor.AverageErrors
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

omit [MeasurableSpace Ω] [Nonempty ι] in
lemma goodFraction_eq_sum (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    goodFraction e t x = (∑ i, if e i x < t then (1 : ℝ) else 0) / Fintype.card ι := by
  classical
  simp only [goodFraction, Finset.cast_card, Finset.sum_filter]

omit [Nonempty ι] in
lemma measurable_goodFraction (e : ι → Ω → ℝ) (t : ℝ)
    (he : ∀ i, Measurable (e i)) : Measurable (goodFraction e t) := by
  classical
  change Measurable (fun x => goodFraction e t x)
  simp_rw [goodFraction_eq_sum]
  exact (Finset.measurable_sum _ (fun i _ => measurable_const.ite
    (measurableSet_lt (he i) measurable_const) measurable_const)).div_const _

omit [MeasurableSpace Ω] [Nonempty ι] in
lemma goodFraction_nonneg (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    0 ≤ goodFraction e t x := by unfold goodFraction; positivity

omit [MeasurableSpace Ω] in
lemma goodFraction_le_one (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    goodFraction e t x ≤ 1 := by
  classical
  apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
  exact_mod_cast Finset.card_le_univ (Finset.univ.filter (fun i => e i x < t))

lemma integrable_goodFraction (μ : Measure Ω) [IsFiniteMeasure μ]
    (e : ι → Ω → ℝ) (t : ℝ) (he : ∀ i, Measurable (e i)) :
    Integrable (goodFraction e t) μ :=
  Integrable.of_bound (measurable_goodFraction e t he).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (goodFraction_nonneg e t x)]
      exact goodFraction_le_one e t x)

/-- Less than 5% average error gives more than 95% good indices on average. -/
theorem average_goodFraction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ι → Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, Measurable (e i)) (hi : ∀ i, Integrable (e i) μ)
    (hn : ∀ᵐ x ∂μ, ∀ i, 0 ≤ e i x)
    (havg : ∀ i, ∫ x, e i x ∂μ < t/20) :
    (19/20 : ℝ) < ∫ x, goodFraction e t x ∂μ := by
  classical
  let n : ℝ := Fintype.card ι
  have hnpos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint : ∀ᵐ x ∂μ,
      1 - (∑ i, e i x) / (n*t) ≤ goodFraction e t x := by
    filter_upwards [hn] with x hx
    have hi' (i) : 1 - e i x / t ≤ if e i x < t then (1 : ℝ) else 0 := by
      split_ifs with h
      · have : 0 ≤ e i x / t := div_nonneg (hx i) ht.le
        linarith
      · have : 1 ≤ e i x / t := (le_div_iff₀ ht).mpr (by simpa using le_of_not_gt h)
        linarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi' i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← Finset.sum_div] at hs
    rw [goodFraction_eq_sum]
    apply (le_div_iff₀ hnpos).mpr
    have heq : (1 - (∑ i, e i x)/(n*t))*n = n - (∑ i, e i x)/t := by
      field_simp
    rw [heq]
    exact hs
  have hil : Integrable (fun x => 1 - (∑ i, e i x)/(n*t)) μ :=
    (integrable_const 1).sub ((integrable_finsetSum _ (fun i _ => hi i)).div_const _)
  have hlow := integral_mono_ae hil (integrable_goodFraction μ e t he) hpoint
  rw [integral_sub (integrable_const 1) ((integrable_finsetSum _ (fun i _ => hi i)).div_const _),
    integral_div, integral_finsetSum _ (fun i _ => hi i)] at hlow
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlow
  have hu := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset ι))
    Finset.univ_nonempty (fun i _ => havg i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
  have hr : (∑ i, ∫ x, e i x ∂μ) / (n*t) < 1/20 := by
    apply (div_lt_iff₀ (mul_pos hnpos ht)).mpr
    convert hu using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [n]
    ring
  linarith

end EuclideanFiveColor.AverageErrors

namespace EuclideanFiveColor.PhaseCollision
open MeasureTheory
open scoped BigOperators

variable {Ω ι κ V : Type*} [MeasurableSpace Ω]
variable [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] [PseudoMetricSpace V]

/-- The assignment itself need not be measurable and may be chosen separately
at every sample. Only the phase distances and fraction are measured. -/
theorem average_exists_cover_forces_collision (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Finset ι) (v : Ω → ι → V) (w : Ω → κ → V) (r : ℝ)
    (hcov : ∀ᵐ x ∂μ, ∀ i ∈ s x, ∃ j, dist (v x i) (w x j) ≤ r)
    (hm : ∀ i j, Measurable (fun x => dist (v x i) (v x j)))
    (hq : Measurable (fun x => ((s x).card : ℝ) / Fintype.card ι))
    (hlarge : 10 * Fintype.card κ < Fintype.card ι)
    (havg : (19/20 : ℝ) < ∫ x, ((s x).card : ℝ) / Fintype.card ι ∂μ) :
    ∃ i j : ι, i ≠ j ∧
      1 / (4 * (Fintype.card κ : ℝ)) ≤ μ.real {x | dist (v x i) (v x j) ≤ 2*r} := by
  classical
  let f : Ω → ι → κ := fun x i =>
    if h : ∃ j, dist (v x i) (w x j) ≤ r then h.choose else Classical.choice inferInstance
  apply average_cover_forces_collision μ s f v w r _ hm hq hlarge havg
  filter_upwards [hcov] with x hx
  intro i hi
  dsimp [f]
  rw [dite_eq_left (hx i hi)]
  exact (hx i hi).choose_spec

omit [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
  [PseudoMetricSpace V] in
lemma circle_product_dist (a b c d : Circle) :
    dist ((a : ℂ)*(b : ℂ)) ((c : ℂ)*(d : ℂ)) ≤
      dist (a : ℂ) (c : ℂ) + dist (b : ℂ) (d : ℂ) := by
  simp only [dist_eq_norm]
  have he : (a : ℂ)*(b : ℂ)-(c : ℂ)*(d : ℂ) =
      ((a : ℂ)-(c : ℂ))*(b : ℂ) + (c : ℂ)*((b : ℂ)-(d : ℂ)) := by ring
  rw [he]
  simpa only [norm_mul, Circle.norm_coe, mul_one, one_mul] using
    norm_add_le (((a : ℂ)-(c : ℂ))*(b : ℂ)) ((c : ℂ)*((b : ℂ)-(d : ℂ)))

end EuclideanFiveColor.PhaseCollision

namespace EuclideanFiveColor.EncodedCollision
attribute [local instance] OAI.EuclideanFiveColor.EncodedCollision.instMeasurableSpaceCircle_solutions
local instance instBorelSpaceCircle_solutions : BorelSpace Circle := ⟨rfl⟩
open MeasureTheory
open scoped BigOperators
open PhaseEncoding AverageErrors PhaseCollision
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

/-- This is the source's collision contradiction on one selected predecessor
fiber. The lists need not be measurably enumerated. Measurability is required
only of their symmetric encodings and the actual sampled phases. -/
theorem collision_from_measurable_encodings (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (zp zm : Ω → ι → Fin m → Circle) (ap am : ι → Ω → Circle) (j₀ : ι)
    (Hp Hm : ι → Ω → Fin m → ℂ)
    (henc : ∀ᵐ x ∂μ, ∀ j, encoding (zp x j) = Hp j x ∧ encoding (zm x j) = Hm j x)
    (hap : ∀ j, Measurable (ap j)) (ham : ∀ j, Measurable (am j))
    (hDp : ∀ j, Measurable (fun x => dist (Hp j x) (Hp j₀ x)))
    (hDm : ∀ j, Measurable (fun x => dist (Hm j x) (Hm j₀ x)))
    (hmem : ∀ᵐ x ∂μ, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r))
    (hi : ∀ j, Integrable (fun x =>
       dist (Hp j x) (Hp j₀ x)^2 +
       dist (Hm j x) (Hm j₀ x)^2) μ)
    (he : ∀ j, (∫ x,
       dist (Hp j x) (Hp j₀ x)^2 +
       dist (Hm j x) (Hm j₀ x)^2 ∂μ) <
       (ρ^m / m)^2 / 20)
    (hlarge : 10 * m^2 < Fintype.card ι) :
    ∃ i j : ι, i ≠ j ∧ 1/(4*(m : ℝ)^2) ≤ μ.real {x |
      dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ} := by
  classical
  let δ : ℝ := ρ^m / m
  have hδ : 0 < δ := div_pos (pow_pos hρ _) (Nat.cast_pos.mpr hm)
  let e : ι → Ω → ℝ := fun j x =>
    dist (Hp j x) (Hp j₀ x)^2 +
    dist (Hm j x) (Hm j₀ x)^2
  have hem (i) : Measurable (e i) :=
    (hDp i |>.pow_const 2).add (hDm i |>.pow_const 2)
  have hen (x) (i) : 0 ≤ e i x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have havg := average_goodFraction μ e (δ^2) (sq_pos_of_pos hδ) hem hi
    (Filter.Eventually.of_forall hen) he
  let s : Ω → Finset ι := fun x => Finset.univ.filter (fun i => e i x < δ^2)
  let v : Ω → ι → ℂ := fun x i => (ap i x : ℂ)*(am i x : ℂ)
  let w : Ω → (Fin m × Fin m) → ℂ := fun x p =>
    (zp x j₀ p.1 : ℂ)*(zm x j₀ p.2 : ℂ)
  have hcover : ∀ᵐ x ∂μ, ∀ i ∈ s x, ∃ p, dist (v x i) (w x p) ≤ 2*ρ := by
    filter_upwards [hmem, henc] with x hx hxe
    intro i hi'
    have hie : e i x < δ^2 := (Finset.mem_filter.mp hi').2
    have hp : dist (Hp i x) (Hp j₀ x) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (Hm i x) (Hm j₀ x)), dist_nonneg
        (x := Hp i x) (y := Hp j₀ x)]
    have hm' : dist (Hm i x) (Hm j₀ x) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (Hp i x) (Hp j₀ x)), dist_nonneg
        (x := Hm i x) (y := Hm j₀ x)]
    have hp' : dist (encoding (zp x i)) (encoding (zp x j₀)) < δ := by
      rw [(hxe i).1, (hxe j₀).1]; exact hp
    have hm'' : dist (encoding (zm x i)) (encoding (zm x j₀)) < δ := by
      rw [(hxe i).2, (hxe j₀).2]; exact hm'
    obtain ⟨⟨rp, hrp⟩, ⟨rm, hrm⟩⟩ := hx i
    obtain ⟨cp, hcp⟩ := close_encoding_each_phase hm (zp x i) (zp x j₀) hρ hp' rp
    obtain ⟨cm, hcm⟩ := close_encoding_each_phase hm (zm x i) (zm x j₀) hρ hm'' rm
    refine ⟨(cp, cm), ?_⟩
    dsimp [v, w]
    rw [hrp, hrm]
    exact (circle_product_dist _ _ _ _).trans (by linarith)
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hv' (i j) : Measurable (fun x => dist (v x i) (v x j)) := by
    have hco : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    have hvm (i) : Measurable (fun x => v x i) :=
      (hco.measurable.comp (hap i)).mul (hco.measurable.comp (ham i))
    exact (hvm i).dist (hvm j)
  obtain ⟨i, j, hij, hc⟩ := average_exists_cover_forces_collision μ s v w (2*ρ)
    hcover hv' (measurable_goodFraction e (δ^2) hem)
    (by simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hlarge) havg
  refine ⟨i, j, hij, ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two,
    v, show 2*(2*ρ)=4*ρ by ring] using hc

end EuclideanFiveColor.EncodedCollision

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalSelection
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators
namespace EuclideanFiveColor.GoodFiber

variable {W ι T : Type*} [MeasurableSpace W] [Fintype ι] [Nonempty ι] [Fintype T]

omit [Fintype ι] [Nonempty ι] [Fintype T] in
theorem exists_lt_on_conull (μ : Measure W) [IsProbabilityMeasure μ]
    (g : W → ℝ) (hg : Integrable g μ) (havg : ∫ w, g w ∂μ < 1)
    (P : W → Prop) (hP : ∀ᵐ w ∂μ, P w) : ∃ w, P w ∧ g w < 1 := by
  by_contra h
  push Not at h
  have hle : ∀ᵐ w ∂μ, (1 : ℝ) ≤ g w := hP.mono fun w hw => h w hw
  have hi := integral_mono_ae (integrable_const 1) hg hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  exact (not_lt_of_ge hi) havg

omit [MeasurableSpace W] [Fintype T] in
lemma fraction_lower_bound (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (τ : ℝ) (hτ : 0 < τ) :
    (1 - (∑ i, e i)/((Fintype.card ι : ℝ)*τ)) ≤
      ((Finset.univ.filter (fun i => e i < τ)).card : ℝ) / Fintype.card ι := by
  classical
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint (i) : 1-e i/τ ≤ if e i < τ then (1 : ℝ) else 0 := by
    split_ifs with h
    · have := div_nonneg (he i) hτ.le; linarith
    · have : 1 ≤ e i/τ := (le_div_iff₀ hτ).mpr (by simpa using le_of_not_gt h)
      linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Finset.sum_div] at hs
  simp only [Finset.cast_card, Finset.sum_filter]
  apply (le_div_iff₀ hn).mpr
  have heq : (1 - (∑ i, e i)/((Fintype.card ι : ℝ)*τ)) * Fintype.card ι =
      Fintype.card ι - (∑ i, e i)/τ := by field_simp
  rw [heq]
  exact hs

/-- A single explicit budget gives all small-moment tests and over 90% good
approximation indices on the same fiber, together with any conull identities. -/
theorem simultaneous_good_fiber (μ : Measure W) [IsProbabilityMeasure μ]
    (f : T → W → ℝ) (e : ι → W → ℝ) (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ)
    (hf : ∀ t, Integrable (f t) μ) (he : ∀ i, Integrable (e i) μ)
    (hf0 : ∀ᵐ w ∂μ, ∀ t, 0 ≤ f t w) (he0 : ∀ᵐ w ∂μ, ∀ i, 0 ≤ e i w)
    (hbudget : (∑ t, ∫ w, f t w ∂μ)/c +
      10*(∑ i, ∫ w, e i w ∂μ)/((Fintype.card ι : ℝ)*τ) < 1)
    (P : W → Prop) (hP : ∀ᵐ w ∂μ, P w) :
    ∃ w, P w ∧ (∀ t, f t w < c) ∧
      (9/10 : ℝ)*(Fintype.card ι) <
        (Finset.univ.filter (fun i => e i w < τ)).card := by
  classical
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let g : W → ℝ := fun w => (∑ t, f t w)/c + 10*(∑ i, e i w)/(n*τ)
  have hig : Integrable g μ := ((integrable_finsetSum _ (fun t _ => hf t)).div_const c).add
    (((integrable_finsetSum _ (fun i _ => he i)).const_mul 10).div_const _)
  have hi : ∫ w, g w ∂μ < 1 := by
    dsimp [g]
    rw [integral_add ((integrable_finsetSum _ (fun t _ => hf t)).div_const c)
      (((integrable_finsetSum _ (fun i _ => he i)).const_mul 10).div_const _),
      integral_div, integral_div, integral_const_mul,
      integral_finsetSum _ (fun t _ => hf t), integral_finsetSum _ (fun i _ => he i)]
    exact hbudget
  obtain ⟨w, ⟨hwP, hwf, hwe⟩, hw⟩ := exists_lt_on_conull μ g hig hi
    (fun w => P w ∧ (∀ t, 0 ≤ f t w) ∧ ∀ i, 0 ≤ e i w) (hP.and (hf0.and he0))
  have hfs : 0 ≤ ∑ t, f t w := Finset.sum_nonneg (fun t _ => hwf t)
  have hes : 0 ≤ ∑ i, e i w := Finset.sum_nonneg (fun i _ => hwe i)
  refine ⟨w, hwP, ?_, ?_⟩
  · intro t
    have ht : f t w ≤ ∑ t, f t w :=
      Finset.single_le_sum (fun t _ => hwf t) (Finset.mem_univ t)
    have hb : f t w/c ≤ g w := by
      dsimp [g]
      have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hes) (mul_pos hn hτ).le
      have := (div_le_div_iff_of_pos_right hc).mpr ht
      linarith
    exact (div_lt_one hc).mp (hb.trans_lt hw)
  · have hew : (∑ i, e i w)/(n*τ) < 1/10 := by
      dsimp [g] at hw
      have : 0 ≤ (∑ t, f t w)/c := div_nonneg hfs hc.le
      rw [mul_div_assoc] at hw
      linarith
    have hlo := fraction_lower_bound (fun i => e i w) hwe τ hτ
    have hfrac : (9/10 : ℝ) <
        ((Finset.univ.filter (fun i => e i w < τ)).card : ℝ)/n := by
      change 1 - (∑ i, e i w)/(n*τ) ≤ _ at hlo
      linarith
    exact (lt_div_iff₀ hn).mp hfrac

omit [MeasurableSpace W] [Fintype T] [Nonempty ι] in
/-- Pigeonholing happens only after the common good fiber is fixed. -/
theorem large_common_bin {L B : ℕ} (s : Finset ι) (b : ι → Fin L)
    (hs : (9/10 : ℝ)*Fintype.card ι < s.card)
    (hLB : (L : ℝ)*B < (9/10 : ℝ)*Fintype.card ι) :
    ∃ J : Finset ι, J ⊆ s ∧ B < J.card ∧ ∀ i ∈ J, ∀ j ∈ J, b i = b j := by
  classical
  have hcard : L*B < s.card := by exact_mod_cast hLB.trans hs
  obtain ⟨k, _, hk⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := s) (t := Finset.univ) (f := b) (fun _ _ => Finset.mem_univ _)
    (by simpa using hcard)
  refine ⟨s.filter (fun i => b i = k), Finset.filter_subset _ _, hk, ?_⟩
  intro i hi j hj
  exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm

end EuclideanFiveColor.GoodFiber

open MeasureTheory
namespace EuclideanFiveColor.Approximation
variable {A X : Type*} [PseudoMetricSpace A] [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma dist_sq_four_points (a b c d : A) :
    dist a d ^ 2 ≤ 3*(dist a b ^ 2 + dist b c ^ 2 + dist d c ^ 2) := by
  have ht : dist a d ≤ dist a b + dist b c + dist d c := by
    have := dist_triangle a b d
    have := dist_triangle b c d
    rw [dist_comm c d] at this
    linarith
  have ha := dist_nonneg (x := a) (y := b)
  have hb := dist_nonneg (x := b) (y := c)
  have hc := dist_nonneg (x := d) (y := c)
  have hd := dist_nonneg (x := a) (y := d)
  nlinarith [sq_nonneg (dist a b - dist b c), sq_nonneg (dist a b - dist d c),
    sq_nonneg (dist b c - dist d c)]

variable [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
/-- Closeness of approximants costs τ, and each of the two approximation
errors costs less than τ in conditional L². -/
theorem integrated_distance_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (H A' H₀ A₀ : X → A) (τ : ℝ)
    (hHm : Measurable H) (hH₀m : Measurable H₀)
    (hj : Integrable (fun x => dist (H x) (A' x)^2) μ)
    (h₀ : Integrable (fun x => dist (H₀ x) (A₀ x)^2) μ)
    (hAj : ∫ x, dist (H x) (A' x)^2 ∂μ < τ^2)
    (hA₀ : ∫ x, dist (H₀ x) (A₀ x)^2 ∂μ < τ^2)
    (hbin : ∀ᵐ x ∂μ, dist (A' x) (A₀ x) ≤ τ) :
    Integrable (fun x => dist (H x) (H₀ x)^2) μ ∧
      (∫ x, dist (H x) (H₀ x)^2 ∂μ) < 9*τ^2 := by
  have hdom : Integrable (fun x => 3*(dist (H x) (A' x)^2 + τ^2 +
      dist (H₀ x) (A₀ x)^2)) μ := ((hj.add (integrable_const _)).add h₀).const_mul 3
  have hle : ∀ᵐ x ∂μ, dist (H x) (H₀ x)^2 ≤
      3*(dist (H x) (A' x)^2 + τ^2 + dist (H₀ x) (A₀ x)^2) := by
    filter_upwards [hbin] with x hx
    have hs : dist (A' x) (A₀ x)^2 ≤ τ^2 :=
      pow_le_pow_left₀ dist_nonneg hx 2
    exact (dist_sq_four_points _ _ _ _).trans (by linarith)
  have hi : Integrable (fun x => dist (H x) (H₀ x)^2) μ := by
    apply hdom.mono' ((hHm.dist hH₀m).pow_const 2).aestronglyMeasurable
    exact hle.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_sq] using hx
  refine ⟨hi, ?_⟩
  have he := integral_mono_ae hi hdom hle
  have hc : Integrable (fun _ : X => τ^2) μ := integrable_const _
  have hjc : Integrable (fun x => dist (H x) (A' x)^2 + τ^2) μ := hj.add hc
  rw [integral_const_mul, integral_add hjc h₀,
    integral_add hj hc, integral_const, probReal_univ, smul_eq_mul, one_mul] at he
  linarith

end EuclideanFiveColor.Approximation

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.ConditionalFiber
variable {X W G V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma comp_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) :
    (condDistrib id p μ) ∘ₘ μ.map p = μ := by
  simpa using condDistrib_comp_map hp.aemeasurable (measurable_id.aemeasurable (μ := μ))

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_fiber_of_ae (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, P x := by
  exact Measure.ae_ae_of_ae_comp (by rwa [comp_identity_fiber μ p hp])

lemma map_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : AEMeasurable p μ) (b : X → G) (hb : Measurable b) :
    ∀ᵐ w ∂μ.map p, (condDistrib id p μ w).map b = condDistrib b p μ w := by
  filter_upwards [condDistrib_comp p
    (measurable_id.aemeasurable (μ := μ)) hb] with w hw
  simpa [Kernel.map_apply _ hb] using hw.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_in_own_fiber [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsFiniteMeasure μ] (p : X → W) (hp : Measurable p) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, p x = w := by
  filter_upwards [map_identity_fiber μ p hp.aemeasurable p hp,
    condDistrib_self p] with w hw hs
  have he : (condDistrib id p μ w).map p = Measure.dirac w := by
    rw [hw, hs]; rfl
  apply ae_of_ae_map (p := fun z : W => z = w) hp.aemeasurable
  rw [he]
  simp

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integral_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∫ w, (∫ x, f x ∂condDistrib id p μ w) ∂μ.map p = ∫ x, f x ∂μ := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply,
    comp_identity_fiber μ p hp] using he.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] [NormedSpace ℝ V] in
lemma integrable_ae_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∀ᵐ w ∂μ.map p, Integrable f (condDistrib id p μ w) := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  exact ((Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi).1

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integrable_fiber_integral (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    Integrable (fun w => ∫ x, f x ∂condDistrib id p μ w) (μ.map p) := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  exact hi.integral_comp

end EuclideanFiveColor.ConditionalFiber

namespace EuclideanFiveColor.FiniteModule
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open ConditionalFiber
variable {X W ι T : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [Fintype ι] [Nonempty ι] [Fintype T]

attribute [local instance] OAI.EuclideanFiveColor.FiniteModule.instMeasurableSpaceCircle_solutions
/-- The actual common-fiber contradiction. The budget is global; all phase
upper bounds are required simultaneously on that fiber before a bin is chosen.
The phase lists are not assumed measurable. -/
theorem common_fiber_contradiction (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (hp : Measurable p) (m : ℕ) (hm : 0 < m)
    (ρ τ c : ℝ) (hρ : 0 < ρ) (hτ : 0 < τ) (hc : 0 < c)
    (hτδ : 18*τ^2 < (ρ^m/m)^2/20)
    (Hp Hm Ap Am : ι → X → Fin m → ℂ)
    (hHp : ∀ j, Measurable (Hp j)) (hHm : ∀ j, Measurable (Hm j))
    (hIp : ∀ j, Integrable (fun x => dist (Hp j x) (Ap j x)^2) μ)
    (hIm : ∀ j, Integrable (fun x => dist (Hm j x) (Am j x)^2) μ)
    (zp zm : X → ι → Fin m → Circle) (ap am : ι → X → Circle)
    (hap : ∀ j, Measurable (ap j)) (ham : ∀ j, Measurable (am j))
    (henc : ∀ᵐ x ∂μ, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x)
    (hmem : ∀ᵐ x ∂μ, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r))
    (f : T → W → ℝ) (hf : ∀ t, Integrable (f t) (μ.map p))
    (hf0 : ∀ᵐ w ∂μ.map p, ∀ t, 0 ≤ f t w)
    (hbudget : (∑ t, ∫ w, f t w ∂μ.map p)/c +
      10*(∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
        (∫ x, dist (Hm j x) (Am j x)^2 ∂μ)))/((Fintype.card ι : ℝ)*τ^2) < 1)
    (L : ℕ) (bin : W → ι → Fin L)
    (hlarge : (L : ℝ)*(10*m^2 : ℕ) < (9/10 : ℝ)*Fintype.card ι)
    (hbin : ∀ᵐ w ∂μ.map p, ∀ i j, bin w i = bin w j →
      ∀ᵐ x ∂condDistrib id p μ w, dist (Ap i x) (Ap j x) ≤ τ ∧
        dist (Am i x) (Am j x) ≤ τ)
    (hupper : ∀ᵐ w ∂μ.map p, (∀ t, f t w < c) → ∀ i j, i ≠ j →
      (condDistrib id p μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2)) : False := by
  classical
  let e : ι → W → ℝ := fun j w =>
    (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) +
    (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w)
  have he (j : ι) : Integrable (e j) (μ.map p) :=
    (integrable_fiber_integral μ p hp _ (hIp j)).add
      (integrable_fiber_integral μ p hp _ (hIm j))
  have hinte (j : ι) : (∫ w, e j w ∂μ.map p) =
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂μ) := by
    rw [show e j = fun w =>
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w) from rfl,
      integral_add (integrable_fiber_integral μ p hp _ (hIp j))
        (integrable_fiber_integral μ p hp _ (hIm j)),
      integral_fiber μ p hp _ (hIp j), integral_fiber μ p hp _ (hIm j)]
  have he0 (w) (j) : 0 ≤ e j w :=
    add_nonneg (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  have hbudget' : (∑ t, ∫ w, f t w ∂μ.map p)/c +
      10*(∑ j, ∫ w, e j w ∂μ.map p)/((Fintype.card ι : ℝ)*τ^2) < 1 := by
    simpa only [hinte] using hbudget
  have hcondp : ∀ᵐ w ∂μ.map p, ∀ j, Integrable
      (fun x => dist (Hp j x) (Ap j x)^2) (condDistrib id p μ w) :=
    ae_all_iff.mpr fun j => integrable_ae_fiber μ p hp _ (hIp j)
  have hcondm : ∀ᵐ w ∂μ.map p, ∀ j, Integrable
      (fun x => dist (Hm j x) (Am j x)^2) (condDistrib id p μ w) :=
    ae_all_iff.mpr fun j => integrable_ae_fiber μ p hp _ (hIm j)
  let P : W → Prop := fun w =>
    (∀ᵐ x ∂condDistrib id p μ w, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x) ∧
    (∀ᵐ x ∂condDistrib id p μ w, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r)) ∧
    (∀ j, Integrable (fun x => dist (Hp j x) (Ap j x)^2) (condDistrib id p μ w)) ∧
    (∀ j, Integrable (fun x => dist (Hm j x) (Am j x)^2) (condDistrib id p μ w)) ∧
    (∀ i j, bin w i = bin w j → ∀ᵐ x ∂condDistrib id p μ w,
      dist (Ap i x) (Ap j x) ≤ τ ∧ dist (Am i x) (Am j x) ≤ τ) ∧
    ((∀ t, f t w < c) → ∀ i j, i ≠ j →
      (condDistrib id p μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2))
  have hP : ∀ᵐ w ∂μ.map p, P w := by
    filter_upwards [ae_fiber_of_ae μ p hp henc, ae_fiber_of_ae μ p hp hmem,
      hcondp, hcondm, hbin, hupper] with w h₁ h₂ h₃ h₄ h₅ h₆
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  haveI : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map hp.aemeasurable
  obtain ⟨w, ⟨hwenc, hwmem, hwIp, hwIm, hwbin, hwup⟩, hwf, hmany⟩ :=
    GoodFiber.simultaneous_good_fiber (μ.map p) f e c (τ^2) hc (sq_pos_of_pos hτ)
      hf he hf0 (Filter.Eventually.of_forall he0) hbudget' P hP
  let s := Finset.univ.filter (fun j => e j w < τ^2)
  obtain ⟨J, hJs, hJ, hJbin⟩ := GoodFiber.large_common_bin s (bin w) hmany hlarge
  have hJpos : 0 < J.card := lt_of_le_of_lt (Nat.zero_le _) hJ
  let : Nonempty J := Set.Nonempty.to_subtype (Finset.card_pos.mp hJpos)
  obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
  have herr (j : J) :
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) < τ^2 ∧
      (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w) < τ^2 := by
    have hj : e j w < τ^2 := (Finset.mem_filter.mp (hJs j.property)).2
    have hn1 : 0 ≤ ∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w :=
      integral_nonneg fun _ => sq_nonneg _
    have hn2 : 0 ≤ ∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w :=
      integral_nonneg fun _ => sq_nonneg _
    dsimp [e] at hj
    constructor <;> linarith
  have hd (j : J) := hwbin j j₀ (hJbin j j.property j₀ j₀.property)
  have hdp (j : J) := Approximation.integrated_distance_bound
    (condDistrib id p μ w) (Hp j) (Ap j) (Hp j₀) (Ap j₀) τ
    (hHp j) (hHp j₀) (hwIp j) (hwIp j₀) (herr j).1 (herr j₀).1
    ((hd j).mono fun x hx => hx.1)
  have hdm (j : J) := Approximation.integrated_distance_bound
    (condDistrib id p μ w) (Hm j) (Am j) (Hm j₀) (Am j₀) τ
    (hHm j) (hHm j₀) (hwIm j) (hwIm j₀) (herr j).2 (herr j₀).2
    ((hd j).mono fun x hx => hx.2)
  obtain ⟨i, j, hij, hlo⟩ := EncodedCollision.collision_from_measurable_encodings
    (condDistrib id p μ w) m hm ρ hρ
    (fun x (j : J) => zp x j) (fun x (j : J) => zm x j)
    (fun j : J => ap j) (fun j : J => am j) j₀ (fun j : J => Hp j) (fun j : J => Hm j)
    (hwenc.mono fun x hx j => hx j) (fun j => hap j) (fun j => ham j)
    (fun j => (hHp j).dist (hHp j₀)) (fun j => (hHm j).dist (hHm j₀))
    (hwmem.mono fun x hx j => hx j)
    (fun j => (hdp j).1.add (hdm j).1)
    (fun j => by
      rw [integral_add (hdp j).1 (hdm j).1]
      exact (add_lt_add (hdp j).2 (hdm j).2).trans (by nlinarith [hτδ]))
    (by simpa only [Fintype.card_coe] using hJ)
  exact (not_lt_of_ge hlo) (hwup hwf i j (fun heq => hij (Subtype.ext heq)))

end EuclideanFiveColor.FiniteModule

open scoped BigOperators
namespace EuclideanFiveColor.FiniteBins

variable {A : Type*} [PseudoMetricSpace A]

theorem compact_bins {s : Set A} (hs : IsCompact s) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℕ, ∃ f : s → Fin L, ∀ x y, f x = f y → dist (x : A) (y : A) < r := by
  classical
  obtain ⟨u, _, hu, hucover⟩ := hs.finite_cover_balls (half_pos hr)
  let t := hu.toFinset
  have ht : s ⊆ ⋃ a ∈ t, Metric.ball a (r/2) := by simpa only [t, hu.mem_toFinset] using hucover
  have hx (x : s) : ∃ a ∈ t, dist (x : A) a < r/2 := by
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (ht x.property)
    obtain ⟨hat, hx⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, hat, hx⟩
  let c : s → t := fun x => ⟨(hx x).choose, (hx x).choose_spec.1⟩
  let e : t ≃ Fin t.card := t.equivFin
  refine ⟨t.card, fun x => e (c x), ?_⟩
  intro x y hxy
  have hc : c x = c y := e.injective hxy
  have hdx : dist (x : A) (c x : A) < r/2 := (hx x).choose_spec.2
  have hdy : dist (y : A) (c x : A) < r/2 := by rw [hc]; exact (hx y).choose_spec.2
  calc
    _ ≤ dist (x : A) (c x : A) + dist (c x : A) (y : A) := dist_triangle _ _ _
    _ < r/2+r/2 := add_lt_add hdx (by simpa only [dist_comm] using hdy)
    _ = r := by ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma linear_combination_dist_bound {q : ℕ} (H : Fin q → V)
    (b c : Fin q → ℂ) :
    dist (∑ i, b i • H i) (∑ i, c i • H i) ≤
      dist b c * ∑ i, ‖H i‖ := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖b i • H i - c i • H i‖ := norm_sum_le _ _
    _ ≤ ∑ i, dist b c * ‖H i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_smul, norm_smul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [dist_eq_norm] using dist_le_pi_dist b c i) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- A common finite partition simultaneously controls both coefficient arrays. -/
theorem bounded_coefficient_bins (q : ℕ) (B D τ : ℝ) (hD : 0 ≤ D) (hτ : 0 < τ) :
    ∃ L : ℕ, ∃ f : {b : Fin 2 → Fin q → ℂ // ‖b‖ ≤ B} → Fin L,
      ∀ b c, f b = f c → ∀ H : Fin q → V, (∑ i, ‖H i‖) ≤ D →
      ∀ j : Fin 2, dist (∑ i, b.val j i • H i) (∑ i, c.val j i • H i) < τ := by
  have hden : 0 < 1+D := by linarith
  have hs : IsCompact {b : Fin 2 → Fin q → ℂ | ‖b‖ ≤ B} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : Fin 2 → Fin q → ℂ) B)
  obtain ⟨L, f, hf⟩ := compact_bins hs (div_pos hτ hden)
  refine ⟨L, f, ?_⟩
  intro b c hbc H hH j
  have hdist : dist (b.val j) (c.val j) < τ/(1+D) :=
    (dist_le_pi_dist b.val c.val j).trans_lt (hf b c hbc)
  calc
    _ ≤ dist (b.val j) (c.val j) * ∑ i, ‖H i‖ := linear_combination_dist_bound H _ _
    _ ≤ dist (b.val j) (c.val j) * D :=
      mul_le_mul_of_nonneg_left hH dist_nonneg
    _ ≤ dist (b.val j) (c.val j) * (1+D) :=
      mul_le_mul_of_nonneg_left (by linarith) dist_nonneg
    _ < τ := (lt_div_iff₀ hden).mp hdist

end EuclideanFiveColor.FiniteBins

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Basic
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral

/-- The group-theoretic step behind the zero-mass coset argument. -/
theorem finite_image_trivial {G H : Type*} [Group G] [Group H] [Finite H]
    [RootableBy G ℕ] (f : G →* H) (g : G) : f g = 1 := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨x, hx⟩ := RootableBy.surjective_pow G ℕ (Fintype.card_ne_zero : Fintype.card H ≠ 0) g
  rw [← hx, map_pow, pow_card_eq_one]

theorem scalar_mem_C_iff {a : E} (ha : a ≠ 0) (d : D) : scalar a d ∈ C ↔ d ∈ C := by
  constructor
  · intro h
    have h' := scalar_mem_C a⁻¹ h
    simpa [ha] using h'
  · exact scalar_mem_C a

/-- Ordinary one-dimensional characters, proved from the covering property of exp. -/
theorem real_character (f : ℝ → Circle) (hf : Continuous f)
    (hmul : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ t, f t = Circle.exp (a * t) := by
  have hzero : f 0 = 1 := by
    have h := hmul 0 0
    exact (mul_left_cancel (show f 0 * 1 = f 0 * f 0 by simpa using h)).symm
  obtain ⟨F, ⟨hFzero, hFexp⟩, hFuniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      ⟨f, hf⟩ 0 0 (by simpa using hzero.symm)
  have hF (t : ℝ) : Circle.exp (F t) = f t := congrFun hFexp t
  have hadd (x y : ℝ) : F (x + y) = F x + F y := by
    let G : C(ℝ, ℝ) := ⟨fun t => F (t + y) - F y,
      (F.continuous.comp (continuous_id.add continuous_const)).sub continuous_const⟩
    have hG : G = F := hFuniq G ⟨by simp [G], by
      funext t
      change Circle.exp (F (t + y) - F y) = f t
      rw [Circle.exp_sub, hF, hF, hmul, mul_div_cancel_right]⟩
    have hh := congrArg (fun g : C(ℝ, ℝ) => g x) hG
    dsimp [G] at hh
    linarith
  let Fadd : ℝ →+ ℝ := { toFun := F, map_zero' := hFzero, map_add' := hadd }
  have hrat (q : ℚ) : F (q : ℝ) = (q : ℝ) * F 1 := by
    simpa [Fadd, Rat.smul_def] using map_rat_smul Fadd q (1 : ℝ)
  have hlinear : (fun t : ℝ => F t) = fun t => t * F 1 :=
    Rat.denseRange_cast.equalizer F.continuous
      (continuous_id.mul continuous_const) (funext hrat)
  refine ⟨F 1, fun t => ?_⟩
  rw [← hF, congrFun hlinear t, mul_comm]

theorem dense_F : Dense (F : Set ℝ) :=
  Dense.mono (Set.range_subset_iff.mpr fun q : ℚ =>
    mem_algebraicClosure_iff.mpr (isAlgebraic_ratCast ℚ q))
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))

/-- The source's exact ordinary-character description on the dense real algebraic field. -/
theorem algebraic_real_character (f : F → Circle) (hf : Continuous f)
    (hmul : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ t : F, f t = Circle.exp (a * (t : ℝ)) := by
  have hzero : f 0 = 1 := by
    have h := hmul 0 0
    exact (mul_left_cancel (show f 0 * 1 = f 0 * f 0 by simpa using h)).symm
  let fHom : Multiplicative F →* Circle := {
    toFun := fun t => f t.toAdd
    map_one' := hzero
    map_mul' := fun _ _ => hmul _ _ }
  have hu : UniformContinuous f :=
    uniformContinuous_monoidHom_of_continuous (f := fHom) hf
  let g := dense_F.extend f
  have hg : Continuous g := (dense_F.uniformContinuous_extend hu).continuous
  have hext (t : F) : g (t : ℝ) = f t := dense_F.extend_eq hf t
  have hgmul : ∀ x y : ℝ, g (x + y) = g x * g y := by
    intro x y
    refine dense_F.denseRange_val.induction_on₂
      (p := fun x y => g (x + y) = g x * g y) ?_ ?_ x y
    · exact isClosed_eq (hg.comp (continuous_fst.add continuous_snd))
        ((hg.comp continuous_fst).mul (hg.comp continuous_snd))
    · intro x y
      change g ((x + y : F) : ℝ) = g (x : ℝ) * g (y : ℝ)
      simp only [hext, hmul]
  obtain ⟨a, ha⟩ := real_character g hg hgmul
  exact ⟨a, fun t => (hext t).symm.trans (ha t)⟩

theorem continuous_jF : Continuous jF := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro z
  exact Circle.exp.continuous.comp (continuous_id.mul continuous_const)

theorem measurableSet_CF : MeasurableSet CF := by
  change MeasurableSet (Set.range jF)
  rw [← Set.image_univ, ← Metric.iUnion_closedBall_nat (0 : ℝ), Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    ((isCompact_closedBall (0 : ℝ) (n : ℝ)).image continuous_jF).measurableSet

theorem continuous_restrictLine (a : E) : Continuous (restrictLine a) :=
  (lineHom a).continuous_comp_left

theorem mem_L_iff (a : E) (d : D) : d ∈ L a ↔ restrictLine a d ∈ CF := by
  constructor
  · intro hd
    obtain ⟨l, hl⟩ := algebraic_real_character
      (fun t : F => d (Multiplicative.ofAdd (a * ofF t))) hd (by
        intro t s
        rw [map_add, mul_add]
        exact map_mul d _ _)
    use l
    apply PontryaginDual.ext
    intro t
    exact (hl (Multiplicative.toAdd t)).symm
  · rintro ⟨l, hl⟩
    have h (t : F) : d (Multiplicative.ofAdd (a * ofF t)) = Circle.exp (l * (t : ℝ)) :=
      (congrArg (fun χ : DF => χ (Multiplicative.ofAdd t)) hl).symm
    change Continuous (fun t : F => d (Multiplicative.ofAdd (a * ofF t)))
    simp_rw [h]
    exact Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)

theorem measurableSet_L (a : E) : MeasurableSet (L a) := by
  have h : L a = restrictLine a ⁻¹' CF := by ext d; exact mem_L_iff a d
  rw [h]
  exact measurableSet_CF.preimage (continuous_restrictLine a).measurable

theorem reF_add_imF (z : E) : ofF (reF z) + imagUnit * ofF (imF z) = z := by
  apply Subtype.ext
  change ((z : ℂ).re : ℂ) + Complex.I * (z : ℂ).im = (z : ℂ)
  rw [mul_comm, Complex.re_add_im]

theorem line_add {a b : E} {d : D} (ha : d ∈ L a) (hb : d ∈ L b) :
    d ∈ L (a + b) := by
  have h (t : F) : d (Multiplicative.ofAdd ((a + b) * ofF t)) =
      d (Multiplicative.ofAdd (a * ofF t)) * d (Multiplicative.ofAdd (b * ofF t)) := by
    rw [add_mul]; exact map_mul d _ _
  change Continuous _
  simp_rw [h]
  exact ha.mul hb

theorem line_mul_real {a : E} {d : D} (ha : d ∈ L a) (t : F) :
    d ∈ L (a * ofF t) := by
  change Continuous _ at ha ⊢
  convert ha.comp (continuous_const.mul continuous_id : Continuous (fun s : F => t * s)) using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  simp only [Function.comp_apply, Pi.mul_apply, map_mul, mul_assoc]

theorem line_sub {a b : E} {d : D} (ha : d ∈ L a) (hb : d ∈ L b) :
    d ∈ L (a - b) := by
  have hn : d ∈ L (-b) := by simpa using line_mul_real hb (-1)
  simpa only [sub_eq_add_neg] using line_add ha hn

theorem orthogonal_lines {d : D} (h1 : d ∈ L 1) (hi : d ∈ L imagUnit) : d ∈ C := by
  obtain ⟨l, hl⟩ := (mem_L_iff 1 d).mp h1
  obtain ⟨e, he⟩ := (mem_L_iff imagUnit d).mp hi
  refine ⟨Multiplicative.ofAdd ((l : ℂ) + (e : ℂ) * Complex.I), ?_⟩
  apply PontryaginDual.ext
  intro z
  have hr (t : F) : d (Multiplicative.ofAdd (ofF t)) = Circle.exp (l * (t : ℝ)) := by
    have hh := congrArg (fun f : DF => f (Multiplicative.ofAdd t)) hl
    change Circle.exp (l * (t : ℝ)) = d (Multiplicative.ofAdd (1 * ofF t)) at hh
    simpa only [one_mul] using hh.symm
  have hi' (t : F) : d (Multiplicative.ofAdd (imagUnit * ofF t)) = Circle.exp (e * (t : ℝ)) :=
    (congrArg (fun f : DF => f (Multiplicative.ofAdd t)) he).symm
  change Circle.exp (inner ℝ ((l : ℂ) + (e : ℂ) * Complex.I) (embed z)) = d z
  have hd : d z = d (Multiplicative.ofAdd (ofF (reF (Multiplicative.toAdd z)))) *
      d (Multiplicative.ofAdd (imagUnit * ofF (imF (Multiplicative.toAdd z)))) := by
    calc
      d z = d (Multiplicative.ofAdd (ofF (reF (Multiplicative.toAdd z)) +
        imagUnit * ofF (imF (Multiplicative.toAdd z)))) :=
          congrArg d (congrArg Multiplicative.ofAdd (reF_add_imF (Multiplicative.toAdd z))).symm
      _ = _ := map_mul d _ _
  rw [hd, hr, hi', ← Circle.exp_add]
  congr 1
  simp [Complex.inner, embed, Complex.mul_re, Complex.mul_im, mul_comm]

/-- Two genuinely independent algebraic directions force an ordinary character. -/
theorem line_one_and_nonreal {d : D} (h1 : d ∈ L 1) {w : E}
    (hw : d ∈ L w) (hn : imF w ≠ 0) : d ∈ C := by
  have hr : d ∈ L (ofF (reF w)) := by simpa using line_mul_real h1 (reF w)
  have hsub := line_sub hw hr
  have him := line_mul_real hsub (imF w)⁻¹
  have heq : (w - ofF (reF w)) * ofF (imF w)⁻¹ = imagUnit := by
    have hz := reF_add_imF w
    have hzero : ofF (imF w) ≠ 0 := fun h => hn (ofF.injective (by simpa using h))
    rw [map_inv₀]
    calc
      (w - ofF (reF w)) * (ofF (imF w))⁻¹ =
        (imagUnit * ofF (imF w)) * (ofF (imF w))⁻¹ := by congr 1; linear_combination -hz
      _ = imagUnit := by rw [mul_assoc, mul_inv_cancel₀ hzero, mul_one]
  rw [heq] at him
  exact orthogonal_lines h1 him

theorem independent_lines {a b : E} (ha : a ≠ 0) (hn : imF (a⁻¹ * b) ≠ 0)
    {d : D} (hda : d ∈ L a) (hdb : d ∈ L b) : d ∈ C := by
  apply (scalar_mem_C_iff ha d).mp
  apply line_one_and_nonreal (w := a⁻¹ * b) (by simpa using hda) _ hn
  simpa [← mul_assoc, ha] using hdb

theorem real_rotation_square (u : K) (hi : imF (kCoeff u) = 0) : u ^ 2 = 1 := by
  have him : (u.val : ℂ).im = 0 := congrArg (fun x : F => (x : ℝ)) hi
  have hn : (u.val : ℂ).re * (u.val : ℂ).re = 1 := by
    have hh := Complex.sq_norm (u.val : ℂ)
    rw [Circle.norm_coe] at hh
    simpa [Complex.normSq_apply, him] using hh.symm
  apply Subtype.ext
  apply Subtype.ext
  change (u.val : ℂ) ^ 2 = 1
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, him, hn]

/-- Squared rotations index the distinct unoriented algebraic lines. -/
theorem rotated_directions_independent {a : E} (ha : a ≠ 0) {u v : K}
    (huv : u ^ 2 ≠ v ^ 2) : imF ((a * kCoeff u)⁻¹ * (a * kCoeff v)) ≠ 0 := by
  intro h
  have heq : (a * kCoeff u)⁻¹ * (a * kCoeff v) = kCoeff (u⁻¹ * v) := by
    simp [mul_inv_rev, mul_assoc, ha]
  rw [heq] at h
  have hp := real_rotation_square (u⁻¹ * v) h
  apply huv
  have hp' : (u ^ 2)⁻¹ * (v ^ 2) = 1 := by simpa only [mul_pow, inv_pow] using hp
  exact inv_mul_eq_one.mp hp'

/-- Complete line-event conclusion of the source's null-events lemma. -/
theorem wild_line_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0) : ν (L a) = 0 := by
  classical
  by_contra hn
  have hp : 0 < ν (L a) := pos_iff_ne_zero.mpr hn
  let root : K → K := fun u => Classical.choose (K_pow_surjective 2 (by norm_num) u)
  have hroot (u : K) : (root u) ^ 2 = u := Classical.choose_spec (K_pow_surjective 2 (by norm_num) u)
  let B (u : K) : Set D := L (a * kCoeff (root u)) \ (C : Set D)
  have hBm (u : K) : MeasurableSet (B u) := (measurableSet_L _).diff measurableSet_C
  have hpre (u : K) : (fun d : D => (root u) • d) ⁻¹' L a = L (a * kCoeff (root u)) := by
    ext d
    change scalar (kCoeff (root u)) d ∈ L a ↔ _
    rw [scalar_line, mul_comm]
  have hmass (u : K) : ν (B u) = ν (L a) := by
    change ν (L (a * kCoeff (root u)) \ (C : Set D)) = _
    rw [MeasureTheory.measure_sdiff_null hν.2, ← hpre]
    exact (hν.1 (root u)).measure_preimage (measurableSet_L a).nullMeasurableSet
  have hd : Pairwise (Function.onFun Disjoint B) := by
    intro u v huv
    change Disjoint (B u) (B v)
    rw [Set.disjoint_left]
    rintro d ⟨hdu, hdc⟩ ⟨hdv, _⟩
    apply hdc
    apply independent_lines (mul_ne_zero ha (kCoeff_ne_zero _))
      (rotated_directions_independent ha _) hdu hdv
    simpa only [hroot] using huv
  have hf := MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion ν hp (As := B)
    hBm hd (MeasureTheory.measure_ne_top ν _)
  have hu : {u : K | ν (L a) ≤ ν (B u)} = Set.univ := by ext u; simp [hmass]
  rw [hu] at hf
  let := Set.finite_univ_iff.mp hf
  have hm := finite_image_trivial (MonoidHom.id K) minusOne
  have hb := congrArg (fun u : K => (u.val : ℂ)) hm
  norm_num [minusOne] at hb

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Characters
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators
namespace PlaneFiveColor.ContinuousCharacters

theorem abs_arg_exp_le (t : ℝ) : |Complex.arg (Circle.exp t : ℂ)| ≤ |t| := by
  by_cases h : |t| ≤ Real.pi
  · rcases (abs_le.mp h) with ⟨hl, hr⟩
    rcases eq_or_lt_of_le hl with hh | hh
    · have ht : t = -Real.pi := hh.symm
      rw [ht, Circle.coe_exp]
      simp [Complex.arg_neg_one]
    · rw [Circle.arg_exp hh hr]
  · have ha : |Complex.arg (Circle.exp t : ℂ)| ≤ Real.pi :=
      abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
    exact ha.trans (le_of_not_ge h)

theorem abs_arg_pow_le (z : Circle) (n : ℕ) :
    |Complex.arg (z ^ n : Circle)| ≤ n * |Complex.arg (z : ℂ)| := by
  have he : Circle.exp ((n : ℝ) * Complex.arg (z : ℂ)) = z ^ n := by
    rw [Circle.exp_natCast_mul, Circle.exp_arg]
  rw [← he]
  simpa [abs_mul] using abs_arg_exp_le ((n : ℝ) * Complex.arg (z : ℂ))

theorem frequency_abs_mono (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1) ^ 2) :
    Monotone (fun n => |frequency X n|) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [frequency, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
  rw [hX n]
  calc
    2 ^ n * |Complex.arg (X (n+1) ^ 2 : Circle)| ≤
        2 ^ n * (2 * |Complex.arg (X (n+1) : ℂ)|) := by
      gcongr
      simpa using abs_arg_pow_le (X (n+1)) 2
    _ = _ := by ring

theorem frequency_exp_previous (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (n : ℕ) : Circle.exp (frequency X (n+1) / (2 : ℝ)^n) = X n := by
  rw [hX n, ← exp_frequency_div X (n+1), ← Circle.exp_natCast_mul]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem frequency_stabilizes (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (R : ℝ) (hR : ∀ n, |frequency X n| ≤ R) :
    ∃ N, ∀ n, N ≤ n → frequency X n = frequency X N := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
    (R / Real.pi + 1))
  have hp (n : ℕ) (hn : N ≤ n) : R < Real.pi * (2 : ℝ)^n := by
    have ht := hN n hn
    have hπ := Real.pi_pos
    have heq : R / Real.pi * Real.pi = R := div_mul_cancel₀ _ Real.pi_ne_zero
    nlinarith
  have hstep (n : ℕ) (hn : N ≤ n) : frequency X (n+1) = frequency X n := by
    have hb (m : ℕ) : |frequency X m / (2 : ℝ)^n| < Real.pi := by
      rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
      exact (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
        ((hR m).trans_lt (hp n hn))
    have he : frequency X (n+1) / (2 : ℝ)^n = frequency X n / (2 : ℝ)^n := by
      apply Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi) (by linarith)
      · exact ⟨(abs_lt.mp (hb (n+1))).1.le, (abs_lt.mp (hb (n+1))).2⟩
      · exact ⟨(abs_lt.mp (hb n)).1.le, (abs_lt.mp (hb n)).2⟩
      · rw [frequency_exp_previous X hX, exp_frequency_div]
    exact (div_left_inj' (pow_ne_zero _ (by norm_num))).mp he
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact (hstep n hn).trans ih

/-- The quantitative lower chord bound on the principal argument. -/
theorem chord_bound (z : Circle) :
    2 / Real.pi * |Complex.arg (z : ℂ)| ≤ ‖(z : ℂ) - 1‖ := by
  have ha : |Complex.arg (z : ℂ)| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hc := Real.cos_le_one_sub_mul_cos_sq ha
  have hr := Complex.norm_mul_cos_arg (z : ℂ)
  have hn := Complex.normSq_sub (z : ℂ) 1
  simp only [Circle.norm_coe, one_mul] at hr
  simp only [Complex.normSq_eq_norm_sq, Circle.norm_coe, map_one,
    mul_one, one_pow] at hn
  have hp := Real.pi_pos
  have hπ : (0 : ℝ) < Real.pi ^ 2 := sq_pos_of_pos hp
  have h0 : 0 ≤ 2 / Real.pi * |Complex.arg (z : ℂ)| := by positivity
  have hsq : (2 / Real.pi * |Complex.arg (z : ℂ)|)^2 ≤ ‖(z : ℂ)-1‖^2 := by
    rw [mul_pow, sq_abs, div_pow]
    rw [hr] at hc
    calc
      2 ^ 2 / Real.pi ^ 2 * (Complex.arg (z : ℂ))^2 =
          2 * (2 / Real.pi ^ 2 * (Complex.arg (z : ℂ))^2) := by ring
      _ ≤ 2 * (1 - (z : ℂ).re) := by linarith
      _ = _ := by linarith
  exact (sq_le_sq₀ h0 (norm_nonneg _)).mp hsq

/-- Cesàro averages of a circle point are small away from one. -/
theorem geom_sum_chord_bound (z : Circle) (m : ℕ) :
    ‖∑ k ∈ Finset.range m, (z : ℂ)^k‖ * ‖(z : ℂ)-1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    ‖(z : ℂ)^m-1‖ ≤ ‖(z : ℂ)^m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp only [norm_pow, Circle.norm_coe, norm_one, one_pow]; norm_num

/-- A large canonical frequency has a large averaged real deviation. -/
theorem average_deviation (z : Circle) (m : ℕ)
    (h : 4 ≤ (m : ℝ) * ‖(z : ℂ)-1‖) :
    (m : ℝ) / 2 ≤ ∑ k ∈ Finset.range m, (1 - ((z : ℂ)^k).re) := by
  have hn : 0 < ‖(z : ℂ)-1‖ := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (norm_nonneg ((z : ℂ)-1))
    rw [hz, mul_zero] at h
    norm_num at h
  have hb := geom_sum_chord_bound z m
  have hr := (Complex.re_le_norm (∑ k ∈ Finset.range m, (z : ℂ)^k))
  have hs : (∑ k ∈ Finset.range m, (z : ℂ)^k).re ≤ (m : ℝ)/2 := by
    nlinarith [norm_nonneg (∑ k ∈ Finset.range m, (z : ℂ)^k)]
  simp only [Complex.re_sum] at hs
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  linarith

open MeasureTheory

lemma deviation_bound (z : Circle) (k : ℕ) : 0 ≤ deviation z k ∧ deviation z k ≤ 2 := by
  have h := Complex.abs_re_le_norm ((z : ℂ)^k)
  simp only [norm_pow, Circle.norm_coe, one_pow] at h
  have hh := abs_le.mp h
  constructor <;> dsimp [deviation] <;> linarith

lemma deviation_measurable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → Circle)
    (hX : Measurable (fun x => (X x : ℂ))) (k : ℕ) : Measurable (fun x => deviation (X x) k) := by
  exact measurable_const.sub (Complex.measurable_re.comp (hX.pow_const k))

lemma deviation_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → Circle) (hX : Measurable (fun x => (X x : ℂ))) (k : ℕ) :
    Integrable (fun x => deviation (X x) k) μ := by
  apply Integrable.of_bound (deviation_measurable X hX k).aestronglyMeasurable 2
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (deviation_bound (X x) k).1] using
    (deviation_bound (X x) k).2

/-- Uniform small deviations imply a quantitative frequency-tail bound. -/
theorem frequency_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → Circle) (hX : Measurable (fun x => (X x : ℂ)))
    (n m : ℕ) (hm : 0 < m) (R ε : ℝ)
    (hR : 4 ≤ (m : ℝ) * (2 / Real.pi) * (R / (2 : ℝ)^n))
    (hε : ∀ k ∈ Finset.range m, ∫ x, deviation (X x) k ∂μ ≤ ε) :
    μ.real {x | R ≤ |(2 : ℝ)^n * Complex.arg (X x : ℂ)|} ≤ 2 * ε := by
  let S : Ω → ℝ := fun x => ∑ k ∈ Finset.range m, deviation (X x) k
  have hS : Integrable S μ := by
    apply integrable_finsetSum
    intro k hk
    exact deviation_integrable μ X hX k
  have hSn : 0 ≤ᵐ[μ] S := Filter.Eventually.of_forall fun x =>
    Finset.sum_nonneg fun k hk => (deviation_bound (X x) k).1
  have hi : ∫ x, S x ∂μ ≤ (m : ℝ)*ε := by
    dsimp [S]
    rw [integral_finsetSum _ (fun k _ => deviation_integrable μ X hX k)]
    calc
      _ ≤ ∑ _k ∈ Finset.range m, ε := Finset.sum_le_sum hε
      _ = _ := by simp
  have ht : {x | R ≤ |(2 : ℝ)^n * Complex.arg (X x : ℂ)|} ⊆
      {x | (m : ℝ)/2 ≤ S x} := by
    intro x hx
    apply average_deviation (X x) m
    have hn : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
    have hf : R / (2 : ℝ)^n ≤ |Complex.arg (X x : ℂ)| := by
      apply (div_le_iff₀ hn).mpr
      simpa only [Set.mem_ofPred_eq, abs_mul, abs_of_pos hn, mul_comm] using hx
    calc
      4 ≤ (m : ℝ) * (2 / Real.pi) * (R / (2 : ℝ)^n) := hR
      _ ≤ (m : ℝ) * (2 / Real.pi) * |Complex.arg (X x : ℂ)| := by gcongr
      _ = (m : ℝ) * (2 / Real.pi * |Complex.arg (X x : ℂ)|) := by ring
      _ ≤ _ := by gcongr; exact chord_bound (X x)
  have hmark := mul_meas_ge_le_integral_of_nonneg hSn hS ((m : ℝ)/2)
  have hmono := measureReal_mono (μ := μ) ht
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  nlinarith

/-- Choosing a Cesàro window within a fixed neighborhood of zero gives
frequency tightness with a bound independent of the dyadic level. -/
theorem dyadic_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (δ ε : ℝ) (hδ : 0 < δ)
    (he : ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ →
      ∫ x, deviation (X n x) k ∂μ ≤ ε) (n : ℕ) :
    μ.real {x | 2 * Real.pi / δ ≤ |frequency (fun j => X j x) n|} ≤ 2*ε := by
  let m := Nat.ceil (δ * (2 : ℝ)^n)
  have hn : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hm : 0 < m := Nat.ceil_pos.mpr (mul_pos hδ hn)
  apply frequency_tail_bound μ (X n) (hX n) n m hm
  · calc
      4 = (δ * (2 : ℝ)^n) * (2 / Real.pi) * ((2 * Real.pi / δ)/(2 : ℝ)^n) := by
        field_simp
        ring
      _ ≤ _ := by
        gcongr
        exact Nat.le_ceil _
  · intro k hk
    apply he
    apply (div_lt_iff₀ hn).mpr
    simpa only [mul_comm] using Nat.lt_ceil.mp (Finset.mem_range.mp hk)

/-- A measure with coefficients continuous at zero is almost surely supported
on dyadic paths whose principal frequencies are bounded. -/
theorem dyadic_frequencies_ae_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (hcoh : ∀ x n, X n x = X (n+1) x ^ 2)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε) :
    ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ n, |frequency (fun j => X j x) n| ≤ R := by
  rw [ae_iff]
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  apply le_antisymm _ measureReal_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, he⟩ := hcont (ε/2) (by positivity)
  let R := 2 * Real.pi / δ
  let A : ℕ → Set Ω := fun n => {x | R ≤ |frequency (fun j => X j x) n|}
  have hmono : Monotone A := by
    intro n m hnm x hx
    exact hx.trans (frequency_abs_mono _ (hcoh x) hnm)
  have hA (n : ℕ) : μ (A n) ≤ ENNReal.ofReal ε := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hε.le).mpr
    have ht := dyadic_tail_bound μ X hX δ (ε/2) hδ he n
    dsimp [A, R]
    simpa only [measureReal_def, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using ht
  have hi : μ (⋃ n, A n) ≤ ENNReal.ofReal ε := by
    rw [hmono.measure_iUnion]
    exact iSup_le hA
  have hsub : {x | ¬ ∃ R : ℝ, ∀ n, |frequency (fun j => X j x) n| ≤ R} ⊆
      ⋃ n, A n := by
    intro x hx
    push Not at hx
    obtain ⟨n, hn⟩ := hx R
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  have hz := ENNReal.toReal_le_of_le_ofReal hε.le ((measure_mono hsub).trans hi)
  simpa only [zero_add, measureReal_def] using hz

/-- The canonical frequencies of almost every such path eventually stabilize. -/
theorem dyadic_frequencies_ae_stable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (hcoh : ∀ x n, X n x = X (n+1) x ^ 2)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε) :
    ∀ᵐ x ∂μ, ∃ N, ∀ n, N ≤ n →
      frequency (fun j => X j x) n = frequency (fun j => X j x) N := by
  filter_upwards [dyadic_frequencies_ae_bounded μ X hX hcoh hcont] with x hx
  obtain ⟨R, hR⟩ := hx
  exact frequency_stabilizes _ (hcoh x) R hR

/-- A stable coherent path is an ordinary frequency on every dyadic scale. -/
theorem ordinary_of_stable (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (N : ℕ) (hN : ∀ n, N ≤ n → frequency X n = frequency X N) :
    ∀ n, X n = Circle.exp (frequency X N / (2 : ℝ)^n) := by
  intro n
  refine Nat.decreasingInduction (n := max N n)
    (motive := fun k _ => X k = Circle.exp (frequency X N / (2 : ℝ)^k))
    ?_ ?_ (Nat.le_max_right N n)
  · intro k hk ih
    rw [hX k, ih, ← Circle.exp_natCast_mul]
    congr 1
    push_cast
    rw [pow_succ]
    field_simp
  · rw [← exp_frequency_div X (max N n), hN _ (Nat.le_max_left N n)]

lemma dyadicApprox_error (t : F) (n : ℕ) :
    |(dyadicApprox t n : ℝ) - (t : ℝ)| ≤ ((2 : ℝ)^n)⁻¹ := by
  have hpos : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hl := Int.floor_le ((2 : ℝ)^n * (t : ℝ))
  have hr := Int.lt_floor_add_one ((2 : ℝ)^n * (t : ℝ))
  change |(Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n - (t : ℝ)| ≤ _
  calc
    _ = |(Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) - (2 : ℝ)^n * (t : ℝ)| /
        (2 : ℝ)^n := by
      have heq : (Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n - (t : ℝ) =
          ((Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) - (2 : ℝ)^n * (t : ℝ))/(2 : ℝ)^n := by
        field_simp
      rw [heq, abs_div, abs_of_pos hpos]
    _ ≤ 1 / (2 : ℝ)^n := by
      gcongr
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = _ := one_div _

lemma dyadicApprox_tendsto (t : F) :
    Filter.Tendsto (fun n => (dyadicApprox t n : ℝ)) Filter.atTop (nhds (t : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => dyadicApprox_error t n)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- Exact squared distance identity for unit characters. -/
lemma circle_sq_dist (z w : Circle) :
    ‖(z : ℂ)-(w : ℂ)‖^2 = 2 * deviation (z/w) 1 := by
  have h := Complex.normSq_sub (z : ℂ) (w : ℂ)
  simp only [Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow] at h
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← div_eq_mul_inv] at h
  simp only [Circle.coe_div] at h
  dsimp [deviation]
  rw [pow_one]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

lemma coeff_small (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle)
    (hc : ContinuousAt (coeff μ χ) 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, |(t : ℝ)| < δ → coeff μ χ t ≤ ε := by
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hdist : dist t 0 < δ := by
    rw [dist_eq_norm, sub_zero]
    change ‖(t : ℝ)‖ < δ
    exact ht
  have hb := hh hdist
  rw [coeff_zero, dist_zero_right, Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb.le

lemma char_nat_dyadic (χ : Multiplicative F →* Circle) (n k : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) ^ k =
      χ (Multiplicative.ofAdd ((k : F)/(2 : F)^n)) := by
  rw [← map_pow]
  congr 1
  change Multiplicative.ofAdd ((k : ℕ) • ((2 : F)^n)⁻¹) = _
  simp only [nsmul_eq_mul, div_eq_mul_inv]

lemma char_int_dyadic (χ : Multiplicative F →* Circle) (k : ℤ) (m : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^m)⁻¹)) ^ k =
      χ (Multiplicative.ofAdd ((k : F)/(2 : F)^m)) := by
  rw [← map_zpow]
  congr 1
  change Multiplicative.ofAdd ((k : ℤ) • ((2 : F)^m)⁻¹) = _
  simp only [zsmul_eq_mul, div_eq_mul_inv]

lemma char_dyadic_coherent (χ : Multiplicative F →* Circle) (n : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) =
      χ (Multiplicative.ofAdd (((2 : F)^(n+1))⁻¹)) ^ 2 := by
  rw [char_nat_dyadic]
  congr 2
  norm_num only [Nat.cast_ofNat]
  rw [pow_succ]
  field_simp

/-- Continuous averaged coefficients give ordinary frequencies on dyadics a.e. -/
theorem character_ae_dyadic (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, ∀ n : ℕ,
      χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n) := by
  let X : ℕ → Ω → Circle := fun n x => χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹))
  have hX : ∀ n, Measurable (fun x => (X n x : ℂ)) := fun n => hχ _
  have hcoh : ∀ x n, X n x = X (n+1) x ^ 2 := fun x n => char_dyadic_coherent _ _
  have hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := coeff_small μ χ hc ε hε
    refine ⟨δ, hδ, fun n k hk => ?_⟩
    have he : (∫ x, deviation (X n x) k ∂μ) = coeff μ χ ((k : F)/(2 : F)^n) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [coeff, deviation, X]
      rw [← Circle.coe_pow, char_nat_dyadic, pow_one]
    rw [he]
    apply hh
    change |(k : ℝ)/(2 : ℝ)^n| < δ
    simpa only [abs_of_nonneg
      (div_nonneg (Nat.cast_nonneg k) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))] using hk
  filter_upwards [dyadic_frequencies_ae_stable μ X hX hcoh hcont] with x hx
  obtain ⟨N, hN⟩ := hx
  exact ⟨frequency (fun n => X n x) N, ordinary_of_stable _ (hcoh x) N hN⟩

lemma char_sub (χ : Multiplicative F →* Circle) (t s : F) :
    χ (Multiplicative.ofAdd (t-s)) =
      χ (Multiplicative.ofAdd t) / χ (Multiplicative.ofAdd s) := by
  exact map_div χ (Multiplicative.ofAdd t) (Multiplicative.ofAdd s)

lemma char_sq_distance (χ : Multiplicative F →* Circle) (t s : F) :
    ‖(χ (Multiplicative.ofAdd t) : ℂ)-(χ (Multiplicative.ofAdd s) : ℂ)‖^2 =
      2 * deviation (χ (Multiplicative.ofAdd (t-s))) 1 := by
  rw [circle_sq_dist, char_sub]

lemma char_sq_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ))) (t s : F) :
    Integrable (fun x => ‖(χ x (Multiplicative.ofAdd t) : ℂ)-
      (χ x (Multiplicative.ofAdd s) : ℂ)‖^2) μ := by
  simp_rw [char_sq_distance]
  exact (deviation_integrable μ _ (hχ (t-s)) 1).const_mul 2

lemma char_sq_integral (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) (t s : F) :
    (∫ x, ‖(χ x (Multiplicative.ofAdd t) : ℂ)-
      (χ x (Multiplicative.ofAdd s) : ℂ)‖^2 ∂μ) = 2 * coeff μ χ (t-s) := by
  simp_rw [char_sq_distance]
  exact integral_const_mul _ _

/-- At coefficient-continuity points, dyadic character evaluations converge in measure. -/
lemma character_tendstoInMeasure (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) (r : ℕ → F) (t : F)
    (hr : Filter.Tendsto r Filter.atTop (nhds t)) :
    TendstoInMeasure μ (fun n x => (χ x (Multiplicative.ofAdd (r n)) : ℂ))
      Filter.atTop (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hpos : 0 < ε^2 := sq_pos_of_pos hε
  have hdiff : Filter.Tendsto (fun n => r n - t) Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hr.sub (tendsto_const_nhds (x := t))
  have hint : Filter.Tendsto (fun n => (∫ x, ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
      (χ x (Multiplicative.ofAdd t) : ℂ)‖^2 ∂μ)/ε^2) Filter.atTop (nhds 0) := by
    simp_rw [char_sq_integral]
    simpa only [Function.comp_def, coeff_zero, mul_zero, zero_div] using
      ((hc.tendsto.comp hdiff).const_mul 2).div_const (ε^2)
  apply squeeze_zero (fun n => measureReal_nonneg) _ hint
  intro n
  apply (le_div_iff₀ hpos).mpr
  have hh := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg
      ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-(χ x (Multiplicative.ofAdd t) : ℂ)‖)
    (char_sq_integrable μ χ hχ (r n) t) (ε^2)
  have heq : {x | ε^2 ≤ ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
    (χ x (Multiplicative.ofAdd t) : ℂ)‖^2} =
      {x | ε ≤ ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
    (χ x (Multiplicative.ofAdd t) : ℂ)‖} := by
    ext x
    exact sq_le_sq₀ hε.le (norm_nonneg _)
  rw [heq] at hh
  simpa only [mul_comm] using hh

lemma char_dyadicApprox_eq (χ : Multiplicative F →* Circle) (l : ℝ)
    (hl : ∀ n : ℕ, χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) =
      Circle.exp (l/(2 : ℝ)^n)) (t : F) (n : ℕ) :
    χ (Multiplicative.ofAdd (dyadicApprox t n)) = Circle.exp (l * (dyadicApprox t n : ℝ)) := by
  rw [dyadicApprox, ← char_int_dyadic, hl, ← Circle.exp_intCast_mul]
  congr 1
  change (Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) * (l/(2 : ℝ)^n) =
    l * ((Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n)
  ring

/-- Direct ordinary-character support theorem on the algebraic real line.
No Bochner representing-measure theorem is an input: frequency tightness and
an a.e. subsequence argument prove the actual simultaneous character formula. -/
theorem character_ae_ordinary (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, ∀ t : F,
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := by
  have ha (t : F) : ∀ᵐ x ∂μ, ∀ l : ℝ,
      (∀ n : ℕ, χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n)) →
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := by
    have hr : Filter.Tendsto (dyadicApprox t) Filter.atTop (nhds t) :=
      tendsto_subtype_rng.mpr (dyadicApprox_tendsto t)
    obtain ⟨ns, hns, hae⟩ :=
      (character_tendstoInMeasure μ χ hχ hc (dyadicApprox t) t hr).exists_seq_tendsto_ae
    filter_upwards [hae] with x hx
    intro l hl
    have hlim : Filter.Tendsto
        (fun n => (Circle.exp (l*(dyadicApprox t (ns n) : ℝ)) : ℂ)) Filter.atTop
        (nhds (Circle.exp (l*(t : ℝ)) : ℂ)) := by
      apply (continuous_subtype_val.comp Circle.exp.continuous).continuousAt.tendsto.comp
      exact tendsto_const_nhds.mul ((dyadicApprox_tendsto t).comp hns.tendsto_atTop)
    have heq : (fun n => (χ x (Multiplicative.ofAdd (dyadicApprox t (ns n))) : ℂ)) =
        fun n => (Circle.exp (l*(dyadicApprox t (ns n) : ℝ)) : ℂ) := by
      funext n
      rw [char_dyadicApprox_eq _ l hl]
    rw [heq] at hx
    exact Subtype.ext (tendsto_nhds_unique hx hlim)
  have hall : ∀ᵐ x ∂μ, ∀ t : F, ∀ l : ℝ,
      (∀ n : ℕ, χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n)) →
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := ae_all_iff.mpr ha
  filter_upwards [character_ae_dyadic μ χ hχ hc, hall] with x hx hxall
  obtain ⟨l, hl⟩ := hx
  exact ⟨l, fun t => hxall t l hl⟩

end PlaneFiveColor.ContinuousCharacters

namespace PlaneFiveColor.Spectral
open MeasureTheory

/-- The exact replacement of Bochner's support step for an arbitrary finite
weight absolutely continuous with respect to a wild law. -/
theorem wild_continuous_coefficient_zero (ν μ : Measure D) [IsProbabilityMeasure ν]
    [IsFiniteMeasure μ] (hν : IsWild ν) (hμ : μ ≪ ν) {a : E} (ha : a ≠ 0)
    (hc : ContinuousAt (ContinuousCharacters.coeff μ (lineCharacter a)) 0) : μ = 0 := by
  have hs := ContinuousCharacters.character_ae_ordinary μ (lineCharacter a)
    (lineCharacter_measurable a) hc
  have hL : ∀ᵐ d ∂μ, d ∈ L a := by
    filter_upwards [hs] with d hd
    obtain ⟨l, hl⟩ := hd
    apply (mem_L_iff a d).mpr
    refine ⟨l, ?_⟩
    apply PontryaginDual.ext
    intro t
    exact (hl (Multiplicative.toAdd t)).symm
  have hnull : μ (L a) = 0 := hμ (wild_line_null ν hν ha)
  have hnot : ∀ᵐ d ∂μ, d ∉ L a := (measure_eq_zero_iff_ae_notMem).mp hnull
  have hf : ∀ᵐ _d ∂μ, False := by
    filter_upwards [hL, hnot] with d hl hn
    exact hn hl
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hf

end PlaneFiveColor.Spectral

end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_InvariantMean
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
/-! A discrete abelian invariant mean, constructed from weighted cube
averages. Repeated group elements keep their multiplicities. -/
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
namespace PlaneFiveColor.InvariantMean

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

lemma cmean_const (z : ℂ) : cmean (BoundedContinuousFunction.const G z) = z := by
  have hr : realPart (BoundedContinuousFunction.const G z) = BoundedContinuousFunction.const G z.re := rfl
  have hi : imagPart (BoundedContinuousFunction.const G z) = BoundedContinuousFunction.const G z.im := rfl
  simp only [cmean, hr, hi, mean_const, Complex.re_add_im]

lemma cmean_shift (g : G) (f : G →ᵇ ℂ) : cmean (cshift g f) = cmean f := by
  have hr : realPart (cshift g f) = shift g (realPart f) := rfl
  have hi : imagPart (cshift g f) = shift g (imagPart f) := rfl
  simp only [cmean, hr, hi, mean_shift]

open MeasureTheory AddCircle

/-- An ordinary nonconstant Fourier monomial has zero mean as soon as its
half-period is represented in the discrete group. -/
lemma circleMean_fourier_nonzero (ρ : G →+ UnitAddCircle) {n : ℤ} (hn : n ≠ 0)
    (hρ : ∃ g, ρ g = ((1 / 2 / n : ℝ) : UnitAddCircle)) : circleMean ρ (fourier n) = 0 := by
  obtain ⟨g, hg⟩ := hρ
  have he : cshift g (circlePull ρ (fourier n)) = -(circlePull ρ (fourier n)) := by
    ext x
    simp only [cshift_apply, circlePull_apply, map_add, hg, BoundedContinuousFunction.neg_apply]
    exact fourier_add_half_inv_index hn zero_lt_one _
  have hm := cmean_shift g (circlePull ρ (fourier n))
  rw [he] at hm
  have hn' : cmean (-circlePull ρ (fourier n)) = -cmean (circlePull ρ (fourier n)) :=
    cmeanCLM.map_neg _
  rw [hn'] at hm
  apply neg_eq_self.mp at hm
  exact hm

theorem circleMean_eq_integral (ρ : G →+ UnitAddCircle)
    (hρ : ∀ n : ℤ, n ≠ 0 → ∃ g, ρ g = ((1 / 2 / n : ℝ) : UnitAddCircle))
    (f : C(UnitAddCircle, ℂ)) : cmean (circlePull ρ f) = ∫ x, f x ∂haarAddCircle := by
  have he : circleMean ρ = circleIntegral := by
    apply ContinuousLinearMap.ext_on (s := Set.range (@fourier 1))
    · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
    · rintro _ ⟨n, rfl⟩
      by_cases hn : n = 0
      · subst n
        have hp : circlePull ρ (fourier 0) = BoundedContinuousFunction.const G 1 := by
          ext x; simp
        simp only [circleMean_apply, hp, cmean_const, circleIntegral_apply]
        simp
      · rw [circleMean_fourier_nonzero ρ hn (hρ n hn), circleIntegral_apply]
        exact (integral_eq_zero_of_add_right_eq_neg
          (fourier_add_half_inv_index hn zero_lt_one)).symm
  exact DFunLike.congr_fun he f

lemma periodMap_half_period (n : ℤ) : ∃ g, periodMap g = ((1 / 2 / n : ℝ) : UnitAddCircle) := by
  refine ⟨QuotientAddGroup.mk (1 / 2 / n : AF), ?_⟩
  rw [periodMap_apply]
  congr 1

/-- The exact identification of the chosen mean on ordinary continuous
periodic functions asserted in spectral.tex113–123. -/
theorem ordinary_mean_integral (f : C(UnitAddCircle, ℂ)) :
    cmean (circlePull periodMap f) = ∫ x, f x ∂haarAddCircle :=
  circleMean_eq_integral periodMap (fun n _ => periodMap_half_period n) f

section WeakMean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weakMean_pair (V : G →ᵇ H) (v : H) :
    inner ℝ (weakMean V) v = mean (pairing V v) :=
  InnerProductSpace.toDual_symm_apply

lemma weakMean_norm_bound (V : G →ᵇ H) : ‖weakMean V‖ ≤ mean (normFn V) := by
  rw [weakMean, LinearIsometryEquiv.norm_map]
  apply (pairingMean V).opNorm_le_bound (mean_nonneg _ (fun x => by rw [normFn_apply]; exact norm_nonneg _))
  intro v
  change |mean (pairing V v)| ≤ mean (normFn V) * ‖v‖
  simpa only [mul_comm] using pairing_mean_bound V v

lemma weakMean_sub (V W : G →ᵇ H) : weakMean (V-W) = weakMean V - weakMean W := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_sub_left, weakMean_pair, weakMean_pair, weakMean_pair]
  have he : pairing (V-W) v = pairing V v - pairing W v := by
    ext x; simp [inner_sub_right]
  rw [he]
  exact meanCLM.map_sub _ _

lemma weakMean_shift (V : G →ᵇ H) (g : G) :
    weakMean (V.compContinuous ⟨fun x => x+g, continuous_of_discreteTopology⟩) = weakMean V := by
  apply ext_inner_right ℝ
  intro v
  rw [weakMean_pair, weakMean_pair]
  exact mean_shift g (pairing V v)

lemma weakMean_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [CompleteSpace J] (L : H →L[ℝ] J) (V : G →ᵇ H) :
    weakMean (L.compLeftContinuousBounded G V) = L (weakMean V) := by
  apply ext_inner_right ℝ
  intro v
  rw [weakMean_pair, ← L.adjoint_inner_right, weakMean_pair]
  congr 1
  ext x
  exact (L.adjoint_inner_left (V x) v).symm

end WeakMean

section Periodization
variable {H : Type*} [NormedAddCommGroup H]

/-- Absolute finiteness of each period sum. -/
lemma period_summable {h : AF → H} {N : ℕ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0) (t : AF) :
    Summable (fun k : ℤ => h (t+k)) := by
  obtain ⟨M, hM⟩ := exists_nat_gt |(t : ℝ)|
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc
    (-((N+M : ℕ) : ℤ)-2) (((N+M : ℕ) : ℤ)+2)))
  intro k hk
  by_contra hn
  apply hk
  apply hs
  simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
  change (N : ℝ) < |(t : ℝ)+(k : ℝ)|
  have hM1 := (abs_lt.mp hM).1
  have hM2 := (abs_lt.mp hM).2
  rcases hn with hn | hn
  · have hk' : (k : ℝ) < -((N : ℝ)+M)-2 := by exact_mod_cast hn
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+M+2 < (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_pos] <;> linarith

lemma periodSum_shift (h : AF → H) (s t : AF) :
    periodSum (fun x => h (x+s)) t = periodSum h (t+s) := by
  unfold periodSum
  congr 1
  ext k
  abel_nf

lemma periodBCF_norm_le (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hB : 0 ≤ B) :
    ‖periodBCF h hs hb‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  apply BoundedContinuousFunction.norm_le (mul_nonneg (Nat.cast_nonneg _) hB) |>.mpr
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact periodSum_norm_le hs hb t

lemma integralReal_mono (h j : AF → ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C) (hle : ∀ t, h t ≤ j t) :
    integralReal h hs hb ≤ integralReal j js jb := by
  apply mean_mono
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact (period_summable hs t).tsum_le_tsum (fun k => hle (t+k)) (period_summable js t)

variable [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weakIntegral_norm_bound (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hB : 0 ≤ B) :
    ‖weakIntegral h hs hb‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  apply (weakMean_norm_bound _).trans
  rw [← mean_const (G := PeriodGroup) ((Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B)]
  apply mean_mono
  intro x
  exact ((periodBCF h hs hb).norm_coe_le_norm x).trans (periodBCF_norm_le h hs hb hB)

lemma weakIntegral_shift (h : AF → H) (s : AF) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (hss : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → h (t+s) = 0)
    (hbs : ∀ t, ‖h (t+s)‖ ≤ C) :
    weakIntegral (fun t => h (t+s)) hss hbs = weakIntegral h hs hb := by
  have he : periodBCF (fun t => h (t+s)) hss hbs =
      (periodBCF h hs hb).compContinuous
        (⟨fun x : PeriodGroup => x+periodMk s,
          continuous_of_discreteTopology⟩) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact periodSum_shift h s t
  unfold weakIntegral
  rw [he, weakMean_shift]

lemma weakIntegral_sub (h j : AF → H) {N M L : ℕ} {B C Q : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C)
    (ds : ∀ t : AF, (L : ℝ) < |(t : ℝ)| → h t-j t = 0)
    (db : ∀ t, ‖h t-j t‖ ≤ Q) :
    weakIntegral (fun t => h t-j t) ds db = weakIntegral h hs hb - weakIntegral j js jb := by
  have he : periodBCF (fun t => h t-j t) ds db = periodBCF h hs hb - periodBCF j js jb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (period_summable hs t).tsum_sub (period_summable js t)
  unfold weakIntegral
  rw [he, weakMean_sub]

lemma weakIntegral_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [CompleteSpace J] (L : H →L[ℝ] J) (h : AF → H) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → L (h t) = 0)
    (jb : ∀ t, ‖L (h t)‖ ≤ C) :
    weakIntegral (fun t => L (h t)) js jb = L (weakIntegral h hs hb) := by
  have he : periodBCF (fun t => L (h t)) js jb =
      L.compLeftContinuousBounded PeriodGroup (periodBCF h hs hb) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (L.map_tsum (period_summable hs t)).symm
  unfold weakIntegral
  rw [he, weakMean_map]

end Periodization
section OrdinaryIntegral
open ContinuousMap TopologicalSpace

/-- Compact support makes all local norm sums finite, before any interchange
of sums, evaluations or integrals. -/
lemma compact_local_summable (f : C(ℝ, ℂ)) {N : ℕ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (K : Compacts ℝ) :
    Summable (fun k : ℤ => ‖(f.comp (ContinuousMap.addRight k)).restrict K‖) := by
  obtain ⟨C, hC⟩ := K.isCompact.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := exists_nat_gt C
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc
    (-((N+M : ℕ) : ℤ)-2) (((N+M : ℕ) : ℤ)+2)))
  intro k hk
  by_contra hn
  apply hk
  rw [norm_eq_zero]
  ext x
  apply hs
  change (N : ℝ) < |(x : ℝ)+(k : ℝ)|
  have hx : |(x : ℝ)| < (M : ℝ) := lt_of_le_of_lt (hC x x.property) hM
  simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
  have hx1 := (abs_lt.mp hx).1
  have hx2 := (abs_lt.mp hx).2
  rcases hn with hn | hn
  · have hk' : (k : ℝ) < -((N : ℝ)+M)-2 := by exact_mod_cast hn
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+M+2 < (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_pos] <;> linarith

lemma ordinaryPeriod_apply (f : C(ℝ, ℂ)) {N : ℕ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (t : ℝ) :
    ordinaryPeriod f (t : UnitAddCircle) = ∑' k : ℤ, f (t+k) := by
  change (∑' k : ℤ, f.comp (ContinuousMap.addRight (k • (1 : ℝ)) )) t = _
  have hf := ContinuousMap.summable_of_locally_summable_norm (compact_local_summable f hs)
  simpa only [zsmul_eq_mul, mul_one, ContinuousMap.comp_apply,
    ContinuousMap.addRight, ContinuousMap.coe_mk] using (ContinuousMap.tsum_apply hf t).symm

/-- Exact agreement of the manuscript's invariant integral with the usual
Lebesgue integral on every continuous boundedly supported test function. -/
theorem integralComplex_ordinary (f : C(ℝ, ℂ)) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (hb : ∀ t, ‖f t‖ ≤ B) :
    integralComplex (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      ∫ t : ℝ, f t := by
  have he : periodBCF (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      circlePull periodMap (ordinaryPeriod f) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      change (∑' k : ℤ, f ((t+k : AF) : ℝ)) = ordinaryPeriod f ((t : ℝ) : UnitAddCircle)
      rw [ordinaryPeriod_apply f hs]
      rfl
  unfold integralComplex
  rw [he, ordinary_mean_integral]
  have hf := Real.fourierCoeff_tsum_comp_add (compact_local_summable f hs) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Int.cast_zero,
    Real.fourier_real_eq_integral_exp_smul, mul_zero, zero_mul, Complex.exp_zero, Complex.ofReal_zero,
    ordinaryPeriod, ContinuousMap.coe_mk] using hf

lemma integralComplex_re (h : AF → ℂ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (rs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → (h t).re = 0)
    (rb : ∀ t, ‖(h t).re‖ ≤ C) :
    (integralComplex h hs hb).re = integralReal (fun t => (h t).re) rs rb := by
  have he : realPart (periodBCF h hs hb) = periodBCF (fun t => (h t).re) rs rb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact Complex.reCLM.map_tsum (period_summable hs t)
  simp only [integralComplex, cmean, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_self, add_zero, he, integralReal]

theorem integralReal_ordinary (f : C(ℝ, ℝ)) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (hb : ∀ t, ‖f t‖ ≤ B) :
    integralReal (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      ∫ t : ℝ, f t := by
  let fc : C(ℝ, ℂ) := ⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hcs : ∀ t : ℝ, (N : ℝ) < |t| → fc t = 0 := by
    intro t ht
    simp [fc, hs t ht]
  have hcb : ∀ t, ‖fc t‖ ≤ B := by
    intro t
    simpa only [fc, coe_mk, Complex.norm_real] using hb t
  have hi := integralComplex_ordinary fc hcs hcb
  have hre := congrArg Complex.re hi
  rw [integralComplex_re _ _ _ (fun t ht => hs t ht) (fun t => hb t)] at hre
  change integralReal (fun t : AF => f t) _ _ = (∫ t : ℝ, (f t : ℂ)).re at hre
  rw [integral_complex_ofReal] at hre
  exact hre

end OrdinaryIntegral

section Smoothing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weakIntegral_congr (h j : AF → H) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C) (he : ∀ t, h t = j t) :
    weakIntegral h hs hb = weakIntegral j js jb := by
  unfold weakIntegral
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact tsum_congr (fun k => he (t+k))

lemma shifted_support {φ : AF → ℝ} {N : ℕ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (s : AF) (hs : |(s : ℝ)| ≤ 1) :
    ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → φ (t-s) = 0 := by
  intro t ht
  apply hφ
  have hi : |(t : ℝ)| ≤ |(t : ℝ)-(s : ℝ)| + |(s : ℝ)| := by
    simpa using abs_add_le ((t : ℝ)-(s : ℝ)) (s : ℝ)
  change (N : ℝ) < |(t : ℝ)-(s : ℝ)|
  push_cast at ht
  linarith

variable (U : AF → H ≃ₗᵢ[ℝ] H)

/-- Translation continuity of smoothing rests only on regularity of the scalar
window, not on any measurability of the discrete representation. -/
theorem smoothed_translation_bound
    (hu : ∀ s t v, U s (U t v) = U (s+t) v)
    (φ : AF → ℝ) {N : ℕ} {B C : ℝ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) (s : AF) (hs : |(s : ℝ)| ≤ 1)
    (hC : 0 ≤ C) (hd : ∀ t, |φ (t-s)-φ t| ≤ C) :
    ‖U s (smoothedVector U φ hφ hb v) - smoothedVector U φ hφ hb v‖ ≤
      (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * (C * ‖v‖) := by
  let h : AF → H := fun t => φ t • U t v
  let j : AF → H := fun t => φ (t-s) • U t v
  have hh := smoothed_support U φ hφ v
  have bh := smoothed_bound U φ hb v
  have hj := smoothed_support U (fun t => φ (t-s)) (shifted_support hφ s hs) v
  have bj := smoothed_bound U (fun t => φ (t-s)) (fun t => hb (t-s)) v
  have dh : ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → j t-h t = 0 := by
    intro t ht
    change φ (t-s) • U t v - φ t • U t v = 0
    rw [hj t ht, hh t (by push_cast at ht; linarith), sub_self]
  have db : ∀ t, ‖j t-h t‖ ≤ C*‖v‖ := by
    intro t
    change ‖φ (t-s) • U t v - φ t • U t v‖ ≤ _
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, (U t).norm_map]
    exact mul_le_mul_of_nonneg_right (hd t) (norm_nonneg v)
  have kh : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → U s (h t) = 0 := by
    intro t ht
    change U s (φ t • U t v) = 0
    rw [hh t ht, map_zero]
  have kb : ∀ t, ‖U s (h t)‖ ≤ B*‖v‖ := by
    intro t
    rw [(U s).norm_map]
    exact bh t
  have je : ∀ t, j t = U s (h (t+(-s))) := by
    intro t
    simp only [j, h, map_smul, hu, sub_eq_add_neg]
    congr 2
    abel_nf
  have kjs : ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → U s (h (t+(-s))) = 0 := by
    intro t ht
    rw [← je]
    exact hj t ht
  have kjb : ∀ t, ‖U s (h (t+(-s)))‖ ≤ B*‖v‖ := by
    intro t
    rw [← je]
    exact bj t
  have ji : weakIntegral j hj bj = U s (weakIntegral h hh bh) := by
    calc
      _ = weakIntegral (fun t => U s (h (t+(-s)))) kjs kjb :=
        weakIntegral_congr _ _ _ _ _ _ je
      _ = weakIntegral (fun t => U s (h t)) kh kb :=
        weakIntegral_shift (fun t => U s (h t)) (-s) kh kb kjs kjb
      _ = U s (weakIntegral h hh bh) :=
        weakIntegral_map (U s).toContinuousLinearEquiv.toContinuousLinearMap h hh bh kh kb
  have di := weakIntegral_sub j h hj bj hh bh dh db
  change ‖U s (weakIntegral h hh bh) - weakIntegral h hh bh‖ ≤ _
  rw [← ji, ← di]
  exact weakIntegral_norm_bound _ dh db (mul_nonneg hC (norm_nonneg v))

/-- Every uniformly continuous compact window produces a strongly continuous
vector even for a completely discontinuous representation of the discrete F. -/
theorem smoothed_tendsto
    (hu : ∀ s t v, U s (U t v) = U (s+t) v)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hφ : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) :
    Tendsto (fun s : AF => U s
      (smoothedVector U (fun t => φ t) (fun t ht => hφ t ht) (fun t => hb t) v))
      (𝓝 0) (𝓝 (smoothedVector U (fun t => φ t)
        (fun t ht => hφ t ht) (fun t => hb t) v)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let Q : ℝ := (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * ‖v‖
  have hQ : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg v)
  have hp : 0 < ε/(Q+1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hc _ hp
  have hnorm : ∀ᶠ s : AF in 𝓝 0, ‖s‖ < min δ 1 :=
    (show Tendsto (fun s : AF => ‖s‖) (𝓝 0) (𝓝 (0 : ℝ)) by
      simpa using continuous_norm.tendsto (0 : AF)).eventually
        (eventually_lt_nhds (lt_min hδ zero_lt_one))
  filter_upwards [hnorm] with s hs
  have hsδ : |(s : ℝ)| < δ := (lt_min_iff.mp hs).1
  have hs1 : |(s : ℝ)| ≤ 1 := le_of_lt (lt_min_iff.mp hs).2
  have hdiff : ∀ t : AF, |φ ((t-s : AF) : ℝ) - φ t| ≤ ε/(Q+1) := by
    intro t
    apply le_of_lt
    apply hd
    change |(t : ℝ)-(s : ℝ)-(t : ℝ)| < δ
    rw [show (t : ℝ)-(s : ℝ)-(t : ℝ) = -(s : ℝ) by ring, abs_neg]
    exact hsδ
  have hbound := smoothed_translation_bound U hu (fun t => φ t)
    (fun t ht => hφ t ht) (fun t => hb t) v s hs1 hp.le hdiff
  rw [dist_zero_right]
  apply hbound.trans_lt
  have hr : Q * (ε/(Q+1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < Q+1)]
    nlinarith
  simpa only [Q, mul_assoc, mul_comm (ε/(Q+1)) ‖v‖] using hr

end Smoothing
end PlaneFiveColor.InvariantMean
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Multipliers
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
namespace PlaneFiveColor.LpMultiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma weight_measurable (v : Lp ℂ 2 μ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖v x‖^2)) μ :=
  ((Lp.aestronglyMeasurable v).norm.pow 2).aemeasurable.ennreal_ofReal

lemma weight_ac (v : Lp ℂ 2 μ) : weight v ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma weight_eq_zero_iff (v : Lp ℂ 2 μ) : weight v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    have he := (withDensity_eq_zero_iff (weight_measurable v)).mp hz
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [he] with x hx
    have hsq : ‖v x‖^2 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hv
    apply (withDensity_eq_zero_iff (weight_measurable v)).mpr
    filter_upwards [Lp.eq_zero_iff_ae_eq_zero.mp hv] with x hx
    simp [hx]

lemma norm_mul_sub_sq (z w : ℂ) (hz : ‖z‖ = 1) :
    ‖z*w-w‖^2 = 2 * (‖w‖^2 * (1-z.re)) := by
  have he := Complex.normSq_sub z 1
  simp only [Complex.normSq_eq_norm_sq, hz, one_pow, map_one, mul_one] at he
  rw [show z*w-w = (z-1)*w by ring, norm_mul, mul_pow, he]
  ring

lemma lp_norm_sq_integral (v : Lp ℂ 2 μ) :
    (∫ x, ‖v x‖^2 ∂μ) = ‖v‖^2 := by
  have he := L2.inner_def (𝕜 := ℝ) v v
  simpa only [real_inner_self_eq_norm_sq] using he.symm

lemma weight_deviation (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    (∫ x, 1-(h x).re ∂weight v) = ‖mul h hm hn v - v‖^2 / 2 := by
  rw [weight, integral_withDensity_eq_integral_toReal_smul₀ (weight_measurable v)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ x, ‖(mul h hm hn v-v) x‖^2 /2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [mul_ae h hm hn v, Lp.coeFn_sub (mul h hm hn v) v] with x hx hy
      rw [hy, Pi.sub_apply, hx, norm_mul_sub_sq _ _ (hn x),
        ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
      ring
    _ = _ := by rw [integral_div, lp_norm_sq_integral]

end PlaneFiveColor.LpMultiplier

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

lemma lineU_apply (ν : Measure D) (a : E) (t : F) (v : Lp ℂ 2 ν) :
    lineU ν a t v = LpMultiplier.mul
      (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
      (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _) v := rfl

lemma lineU_ae (ν : Measure D) (a : E) (t : F) (v : Lp ℂ 2 ν) :
    lineU ν a t v =ᵐ[ν] (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) * v d) :=
  LpMultiplier.mul_ae _ (lineCharacter_measurable a t).aestronglyMeasurable
    (fun _ => Circle.norm_coe _) v

lemma lineU_add (ν : Measure D) (a : E) (s t : F) (v : Lp ℂ 2 ν) :
    lineU ν a s (lineU ν a t v) = lineU ν a (s+t) v := by
  apply Lp.ext
  filter_upwards [lineU_ae ν a s (lineU ν a t v), lineU_ae ν a t v,
    lineU_ae ν a (s+t) v] with d hs ht hst
  rw [hs, ht, hst]
  have he := congrArg (fun z : Circle => (z : ℂ))
    ((lineCharacter a d).map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t))
  change (lineCharacter a d (Multiplicative.ofAdd (s+t)) : ℂ) =
    (lineCharacter a d (Multiplicative.ofAdd s) : ℂ) *
      (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) at he
  rw [he, mul_assoc]

lemma lineU_zero (ν : Measure D) (a : E) (v : Lp ℂ 2 ν) : lineU ν a 0 v = v := by
  apply Lp.ext
  filter_upwards [lineU_ae ν a 0 v] with d hd
  simpa using hd

lemma weighted_coeff (ν : Measure D) (a : E) (v : Lp ℂ 2 ν) (t : F) :
    ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a) t =
      ‖lineU ν a t v-v‖^2/2 := by
  rw [lineU_apply]
  simpa only [ContinuousCharacters.coeff, ContinuousCharacters.deviation, pow_one]
    using LpMultiplier.weight_deviation
      (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
      (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _) v

/-- A wild law has no nonzero strongly continuous vector for any nonzero
algebraic line. The arbitrary L² vector is handled by its actual |v|² weight. -/
theorem strong_vector_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0) (v : Lp ℂ 2 ν)
    (hc : Tendsto (fun t => lineU ν a t v) (𝓝 0) (𝓝 v)) : v = 0 := by
  have hcoef : ContinuousAt
      (ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a)) 0 := by
    have he : ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a) =
        fun t => ‖lineU ν a t v-v‖^2/2 := funext (weighted_coeff ν a v)
    rw [he]
    change Tendsto _ (𝓝 0) (𝓝 (_ / 2))
    have hh := ((hc.sub (tendsto_const_nhds (x := v))).norm.pow 2).div_const 2
    simpa only [lineU_zero, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
      using hh
  exact (LpMultiplier.weight_eq_zero_iff v).mp
    (wild_continuous_coefficient_zero ν (LpMultiplier.weight v) hν
      (LpMultiplier.weight_ac v) ha hcoef)

/-- Every ordinary compact window has zero weak vector average along a
nonzero algebraic line of a wild law. -/
theorem wild_smoothed_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : Lp ℂ 2 ν) :
    InvariantMean.smoothedVector (lineU ν a) (fun t => φ t)
      (fun t ht => hs t ht) (fun t => hb t) v = 0 := by
  apply strong_vector_zero ν hν ha
  exact InvariantMean.smoothed_tendsto (lineU ν a) (lineU_add ν a) φ hc hs hb v

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.InvariantMean
open MeasureTheory
lemma weakMean_complex {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (V : G →ᵇ ℂ) : weakMean V = cmean V := by
  have hr := weakMean_pair V (1 : ℂ)
  have hi := weakMean_pair V Complex.I
  have hpr : pairing V (1 : ℂ) = realPart V := by
    ext x
    simp [pairing_apply, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  have hpi : pairing V Complex.I = imagPart V := by
    ext x
    simp [pairing_apply, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  rw [hpr] at hr
  rw [hpi] at hi
  apply Complex.ext <;>
    simp_all [real_inner_eq_re_inner ℂ, RCLike.inner_apply, cmean]

lemma weakIntegral_complex (h : AF → ℂ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : weakIntegral h hs hb = integralComplex h hs hb :=
  weakMean_complex _
end PlaneFiveColor.InvariantMean

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

lemma lineFourier_inner (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    inner ℂ (Lp.const 2 ν (1 : ℂ)) (lineU ν a t (Lp.const 2 ν (1 : ℂ))) =
      lineFourier ν a t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lineU_ae ν a t (Lp.const 2 ν (1 : ℂ)),
    Lp.coeFn_const (2 : ℝ≥0∞) ν (1 : ℂ)] with d hu hc
  simp [hu, RCLike.inner_apply]

/-- The invariant scalar Fourier average on a nonzero algebraic line vanishes
for every real ordinary compact window; no measurability of t ↦ fν(at). -/
theorem wild_line_average_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) :
    InvariantMean.integralComplex
      (fun t : F => (φ t : ℂ) * lineFourier ν a t)
      (fun t ht => by rw [hs t ht, Complex.ofReal_zero, zero_mul])
      (fun t => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)) = 0 := by
  let v := Lp.const 2 ν (1 : ℂ)
  let L : Lp ℂ 2 ν →L[ℝ] ℂ := (innerSL ℂ v).restrictScalars ℝ
  have he (t : F) : L (φ t • lineU ν a t v) = (φ t : ℂ) * lineFourier ν a t := by
    rw [map_smul]
    change φ t • inner ℂ v (lineU ν a t v) = _
    rw [lineFourier_inner]
    rfl
  have hjs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → L (φ t • lineU ν a t v) = 0 := by
    intro t ht
    rw [he, hs t ht, Complex.ofReal_zero, zero_mul]
  have hjb : ∀ t : F, ‖L (φ t • lineU ν a t v)‖ ≤ B := by
    intro t
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)
  have hm := InvariantMean.weakIntegral_map L
    (fun t : F => φ t • lineU ν a t v)
    (InvariantMean.smoothed_support (lineU ν a) (fun t => φ t) (fun t ht => hs t ht) v)
    (InvariantMean.smoothed_bound (lineU ν a) (fun t => φ t) (fun t => hb t) v)
    hjs hjb
  change InvariantMean.weakIntegral _ _ _ = L (InvariantMean.smoothedVector
    (lineU ν a) (fun t : F => φ t) (fun t ht => hs t ht) (fun t => hb t) v) at hm
  rw [wild_smoothed_zero ν hν ha φ hc hs hb v, map_zero] at hm
  rw [← InvariantMean.weakIntegral_complex]
  exact (InvariantMean.weakIntegral_congr _ _ _ _ hjs hjb (fun t => (he t).symm)).trans hm

end PlaneFiveColor.Spectral
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_FourierTests
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PlaneFiveColor.InvariantMean
open scoped BigOperators
open MeasureTheory Filter Topology

lemma integralReal_congr (f g : AF → ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f t = 0)
    (hb : ∀ t, ‖f t‖ ≤ B)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → g t = 0)
    (gb : ∀ t, ‖g t‖ ≤ C) (he : ∀ t, f t = g t) :
    integralReal f hs hb = integralReal g gs gb := by
  unfold integralReal
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => simp only [periodBCF_mk, periodSum, he]

lemma integralReal_mul (f : AF → ℝ) (c : ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f t = 0)
    (hb : ∀ t, ‖f t‖ ≤ B)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → c*f t = 0)
    (gb : ∀ t, ‖c*f t‖ ≤ C) :
    integralReal (fun t => c*f t) gs gb = c * integralReal f hs hb := by
  have he : periodBCF (fun t => c*f t) gs gb = c • periodBCF f hs hb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      change (∑' k : ℤ, c * f (t+k)) = c * (∑' k : ℤ, f (t+k))
      exact tsum_mul_left
  exact (congrArg mean he).trans (mean_smul _ _)

lemma integralReal_sum {ι : Type*} (s : Finset ι) (f : ι → AF → ℝ)
    {N M : ℕ} {B : ι → ℝ} {C : ℝ}
    (hs : ∀ i, ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f i t = 0)
    (hb : ∀ i t, ‖f i t‖ ≤ B i)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → (∑ i ∈ s, f i t) = 0)
    (gb : ∀ t, ‖∑ i ∈ s, f i t‖ ≤ C) :
    integralReal (fun t => ∑ i ∈ s, f i t) gs gb =
      ∑ i ∈ s, integralReal (f i) (hs i) (hb i) := by
  have he : periodBCF (fun t => ∑ i ∈ s, f i t) gs gb =
      ∑ i ∈ s, periodBCF (f i) (hs i) (hb i) := by
    ext x
    rw [BoundedContinuousFunction.sum_apply]
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      simp only [periodBCF_mk, periodSum]
      exact Summable.tsum_finsetSum (fun i _ => period_summable (hs i) t)
  unfold integralReal
  rw [he]
  exact map_sum (meanCLM (G := PeriodGroup)) _ _

/-- Positivity of the literal invariant integral supplies a common small
parameter for finitely many nonnegative tests. This makes no ordinary
measurability assumption on any test. -/
theorem exists_small_nonnegative_tests {ι : Type*} (s : Finset ι)
    (φ : AF → ℝ) (f : ι → AF → ℝ) {N : ℕ} {B ε : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, ‖φ t‖ ≤ B) (hp : ∀ t, 0 ≤ φ t)
    (hI : 0 < integralReal φ hs hb) (hε : 0 < ε)
    (hf : ∀ i t, 0 ≤ f i t ∧ f i t ≤ 1)
    (hz : ∀ i, integralReal (fun t => φ t * f i t)
      (fun t ht => by rw [hs t ht, zero_mul])
      (weighted_bound φ (f i) hb (hf i)) = 0) :
    ∃ t : AF, 0 < φ t ∧ ∀ i ∈ s, f i t < ε := by
  classical
  by_contra hn
  push Not at hn
  let g : AF → ℝ := fun t => ∑ i ∈ s, φ t * f i t
  have gs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → g t = 0 := by
    intro t ht
    simp [g, hs t ht]
  have gb : ∀ t, ‖g t‖ ≤ (s.card : ℝ) * B := by
    intro t
    calc
      _ ≤ ∑ i ∈ s, ‖φ t*f i t‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum (fun i _ => weighted_bound φ (f i) hb (hf i) t)
      _ = _ := by simp
  have gi : integralReal g gs gb = 0 := by
    rw [integralReal_sum s (fun i t => φ t*f i t)
      (fun i t ht => by rw [hs t ht, zero_mul])
      (fun i => weighted_bound φ (f i) hb (hf i)) gs gb]
    simp only [hz, Finset.sum_const_zero]
  have cs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → ε*φ t = 0 := by
    intro t ht; rw [hs t ht, mul_zero]
  have cb : ∀ t, ‖ε*φ t‖ ≤ |ε| * B := by
    intro t
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb t) (abs_nonneg _)
  have hle : ∀ t, ε*φ t ≤ g t := by
    intro t
    by_cases ht : 0 < φ t
    · obtain ⟨i, hi, hfi⟩ := hn t ht
      have hterm : φ t*f i t ≤ g t :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hp t) (hf j t).1) hi
      exact (by nlinarith : ε*φ t ≤ φ t*f i t).trans hterm
    · have hφ : φ t = 0 := le_antisymm (le_of_not_gt ht) (hp t)
      simp [g, hφ]
  have hmono := integralReal_mono (fun t => ε*φ t) g cs cb gs gb hle
  rw [integralReal_mul φ ε hs hb cs cb, gi] at hmono
  exact (not_le_of_gt (mul_pos hε hI)) hmono

end PlaneFiveColor.InvariantMean

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped BigOperators
open InvariantMean

lemma lineFourier_re_le_one (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    (lineFourier ν a t).re ≤ 1 :=
  (Complex.re_le_norm _).trans (lineFourier_norm_le ν a t)

/-- Real part of the checked vanishing line average, with the same invariant
integral and the same compact window. -/
lemma wild_line_average_re_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) :
    integralReal (fun t : F => φ t * (lineFourier ν a t).re)
      (fun t ht => by rw [hs t ht, zero_mul])
      (fun t => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _)
          ((Complex.abs_re_le_norm _).trans (lineFourier_norm_le ν a t))).trans (hb t)) = 0 := by
  let f : F → ℂ := fun t => (φ t : ℂ) * lineFourier ν a t
  have fs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → f t = 0 := by
    intro t ht; simp [f, hs t ht]
  have fb : ∀ t, ‖f t‖ ≤ B := by
    intro t
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)
  have rs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → (f t).re = 0 := by
    intro t ht; rw [fs t ht]; rfl
  have rb : ∀ t, ‖(f t).re‖ ≤ B := by
    intro t
    simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm (f t)).trans (fb t)
  have hz : integralReal (fun t => (f t).re) rs rb = 0 := by
    rw [← integralComplex_re f fs fb rs rb]
    rw [show integralComplex f fs fb = 0 from wild_line_average_zero ν hν ha φ hc hs hb]
    rfl
  exact (integralReal_congr _ _ _ _ rs rb (fun t => by simp [f])).trans hz

/-- A compact tent window strictly inside the requested parameter radius. -/
lemma exists_positive_window {r : ℝ} (hr : 0 < r) :
    ∃ (φ : C(ℝ, ℝ)) (N : ℕ) (B : ℝ),
      (∀ t : ℝ, (N : ℝ) < |t| → φ t = 0) ∧
      (∀ t, ‖φ t‖ ≤ B) ∧ (∀ t, 0 ≤ φ t) ∧
      UniformContinuous φ ∧ (0 < ∫ t : ℝ, φ t) ∧
      (∀ t, 0 < φ t → |t| < r) := by
  let φ : C(ℝ, ℝ) := ⟨fun t => max 0 (r-|t|), by fun_prop⟩
  have hp (t : ℝ) : 0 ≤ φ t := le_max_left _ _
  have hb (t : ℝ) : ‖φ t‖ ≤ r := by
    rw [Real.norm_of_nonneg (hp t)]
    exact max_le hr.le (sub_le_self _ (abs_nonneg _))
  have houtside (t : ℝ) (ht : r ≤ |t|) : φ t = 0 := max_eq_left (sub_nonpos.mpr ht)
  have hcomp : HasCompactSupport φ := by
    apply HasCompactSupport.intro' (K := Set.Icc (-r) r) isCompact_Icc isClosed_Icc
    intro t ht
    apply houtside
    by_contra hn
    exact ht (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
  have hi : 0 < ∫ t : ℝ, φ t :=
    φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcomp hp
      (show φ 0 ≠ 0 by simpa [φ, max_eq_right hr.le] using hr.ne')
  obtain ⟨N, hN⟩ := exists_nat_gt r
  refine ⟨φ, N, r, (fun t ht => houtside t (le_of_lt (hN.trans ht))), hb, hp,
    hcomp.uniformContinuous_of_continuous φ.continuous, hi, ?_⟩
  intro t ht
  by_contra hn
  rw [houtside t (le_of_not_gt hn)] at ht
  exact lt_irrefl _ ht

theorem exists_small_wild_parameter {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (ν : Measure D) [IsProbabilityMeasure ν] (hν : IsWild ν)
    (a : ι → E) (ha : ∀ i, a i ≠ 0)
    (hn : ∀ i t, 0 ≤ (lineFourier ν (a i) t).re)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ t : F, t ≠ 0 ∧ |(t : ℝ)| < r ∧
      ∀ i ∈ s, (lineFourier ν (a i) t).re < ε := by
  obtain ⟨φ, N, B, hs, hb, hp, hc, hi, hradius⟩ := exists_positive_window hr
  have hz := fun i => wild_line_average_re_zero ν hν (ha i) φ hc hs
    (fun t => by simpa only [← Real.norm_eq_abs] using hb t)
  have hI : 0 < integralReal (fun t : F => φ t)
      (fun t ht => hs t ht) (fun t => hb t) := by
    rw [integralReal_ordinary φ hs hb]
    exact hi
  obtain ⟨t, ht, htest⟩ := exists_small_nonnegative_tests s
    (fun t : F => φ t) (fun i t => (lineFourier ν (a i) t).re)
    (fun t ht => hs t ht) (fun t => hb t) (fun t => hp t) hI hε
    (fun i t => ⟨hn i t, lineFourier_re_le_one ν (a i) t⟩)
    (fun i => by convert hz i using 1)
  refine ⟨t, ?_, hradius t ht, htest⟩
  intro he
  obtain ⟨i, his⟩ := hne
  have hh := htest i his
  rw [he, lineFourier_zero, Complex.one_re] at hh
  exact (not_lt_of_ge hε1) hh

end PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.DifferenceFourier

variable {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]
  [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G]

variable (χ : G →* Circle)

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma coe_character_div (d e : G) :
    (χ (d / e) : ℂ) = (χ d : ℂ) * conj (χ e : ℂ) := by
  rw [map_div, div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]

omit [MeasurableMul₂ G] [MeasurableInv G] in
lemma independent_coefficient (κ : Measure G) [IsProbabilityMeasure κ] :
    (∫ p : G × G, (χ (p.1 / p.2) : ℂ) ∂κ.prod κ) =
      (‖∫ d, (χ d : ℂ) ∂κ‖ ^ 2 : ℝ) := by
  calc
    _ = ∫ p : G × G, (χ p.1 : ℂ) * conj (χ p.2 : ℂ) ∂κ.prod κ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => coe_character_div χ p.1 p.2))
    _ = (∫ d, (χ d : ℂ) ∂κ) * (∫ d, conj (χ d : ℂ) ∂κ) := by
      convert integral_prod_mul (fun d => (χ d : ℂ)) (fun d => conj (χ d : ℂ)) using 1 <;> infer_instance
    _ = _ := by rw [integral_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma difference_coefficient (hχ : Measurable (fun d => (χ d : ℂ))) (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    (∫ d, (χ d : ℂ) ∂differenceLaw ν κ) =
      ((∫ y, (‖∫ d, (χ d : ℂ) ∂κ y‖ ^ 2 : ℝ) ∂ν : ℝ) : ℂ) := by
  have hm := hχ
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) :=
    measurable_fst.div measurable_snd
  rw [differenceLaw, integral_map hdiv.aemeasurable hm.aestronglyMeasurable,
    Measure.comp_eq_comp_const_apply]
  rw [Kernel.integral_comp]
  · simp only [Kernel.const_apply, Kernel.prod_apply]
    change (∫ y, (∫ p : G × G, (χ (p.1 / p.2) : ℂ) ∂(κ y).prod (κ y)) ∂ν) = _
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => independent_coefficient χ (κ y))
  · exact Integrable.of_bound (hm.comp hdiv).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun _ => (Circle.norm_coe _).le))

end EuclideanFiveColor.DifferenceFourier

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_SmallArcs
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators ComplexConjugate

/-! Fiberwise (possibly nonmeasurable) enumerations cause no measurability gap:
actual conditional samples lie in them by the measurable positive-atom event. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace EuclideanFiveColor.SampledAtoms
noncomputable section
variable {X Y G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace G] [MeasurableEq G]

lemma measurable_atom_mass (κ : Kernel Y G) [IsSFiniteKernel κ] :
    Measurable (fun p : Y × G => κ p.1 {p.2}) := by
  classical
  let η : Kernel (Y × G) G := κ.comap Prod.fst measurable_fst
  have hm : Measurable (fun p : (Y × G) × G =>
      if p.2 = p.1.2 then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd (measurable_snd.comp measurable_fst))
      measurable_const measurable_const
  have h := hm.lintegral_kernel_prod_right' (κ := η)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  change κ p.1 {p.2} = ∫⁻ d, (if d=p.2 then (1:ℝ≥0∞) else 0) ∂κ p.1
  simpa only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply] using
    (lintegral_indicator_one (μ := κ p.1) (measurableSet_singleton p.2)).symm

variable [StandardBorelSpace G] [Nonempty G]
lemma ae_sampled_positive_atom (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (b : X → G) (hp : Measurable p) (hb : Measurable b)
    (ha : ∀ᵐ y ∂μ.map p, ∀ᵐ d ∂condDistrib b p μ y, 0 < condDistrib b p μ y {d}) :
    ∀ᵐ x ∂μ, 0 < condDistrib b p μ (p x) {b x} := by
  have hm : MeasurableSet {z : Y × G | 0 < condDistrib b p μ z.1 {z.2}} :=
    measurableSet_lt measurable_const (measurable_atom_mass _)
  have he : ∀ᵐ z ∂μ.map p ⊗ₘ condDistrib b p μ,
      0 < condDistrib b p μ z.1 {z.2} := (Measure.ae_compProd_iff hm).mpr ha
  rw [compProd_map_condDistrib hb.aemeasurable] at he
  exact ae_of_ae_map (hp.prodMk hb).aemeasurable he

omit [StandardBorelSpace G] [Nonempty G] in
lemma uniform_list_positive_atoms (μ : Measure G) {m : ℕ} (_hm : 0 < m)
    (g : Fin m → G) (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i)) :
    ∀ᵐ d ∂μ, 0 < μ {d} := by
  classical
  have hi : (m : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
  have hpt (i : Fin m) : 0 < μ {g i} := by
    rw [hμ, Measure.smul_apply, smul_eq_mul]
    apply ENNReal.mul_pos hi
    have hle : (1 : ℝ≥0∞) ≤ (∑ j, Measure.dirac (g j)) {g i} := by
      rw [Measure.finsetSum_apply]
      calc
        _ = Measure.dirac (g i) {g i} := by simp
        _ ≤ ∑ j, Measure.dirac (g j) {g i} :=
          Finset.single_le_sum (f := fun j : Fin m => Measure.dirac (g j) {g i})
            (fun j _ => bot_le) (Finset.mem_univ i)
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle)
  rw [hμ] at hpt ⊢
  rw [Measure.ae_ennreal_smul_measure_iff hi, ae_finsetSum_measure_iff]
  intro i _
  simpa only [ae_dirac_eq, Filter.eventually_pure] using hpt i

omit [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace G] [Nonempty G] in
lemma in_list_of_positive_atom (μ : Measure G) {m : ℕ} (g : Fin m → G)
    (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i))
    {d : G} (hd : 0 < μ {d}) : ∃ i, d = g i := by
  classical
  by_contra hn
  have hne (i : Fin m) : g i ≠ d := by intro hi; exact hn ⟨i, hi.symm⟩
  have hz : μ {d} = 0 := by
    rw [hμ, Measure.smul_apply, Measure.finsetSum_apply]
    simp [Measure.dirac_apply', hne]
  exact (ne_of_gt hd) hz

lemma ae_sampled_list (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (b : X → G) (hp : Measurable p) (hb : Measurable b)
    {m : ℕ} (hm : 0 < m) (g : Y → Fin m → G)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i)) :
    ∀ᵐ x ∂μ, ∃ i, b x = g (p x) i := by
  have hat := ae_sampled_positive_atom μ p b hp hb
    (hg.mono fun y hy => uniform_list_positive_atoms _ hm (g y) hy)
  filter_upwards [hat, ae_of_ae_map hp.aemeasurable hg] with x hx hxl
  exact in_list_of_positive_atom _ _ hxl hx

end
end EuclideanFiveColor.SampledAtoms

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_ConditionalSpectrum
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators ComplexConjugate

attribute [local instance] OAI.PlaneFiveColor.Spectral.instMeasurableSpaceCircle_solutions
local instance instBorelSpaceCircle_solutions : BorelSpace Circle := ⟨rfl⟩

lemma measurable_eval (a : E) : Measurable (eval a) := (continuous_eval a).measurable
lemma eval_add (a b : E) (d : D) : eval (a+b) d = eval a d * eval b d :=
  map_mul d (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
lemma eval_neg (a : E) (d : D) : eval (-a) d = (eval a d)⁻¹ :=
  d.map_inv (Multiplicative.ofAdd a)
lemma eval_sub (a b : E) (d : D) : eval (a-b) d = eval a d / eval b d := by
  rw [sub_eq_add_neg, eval_add, eval_neg, div_eq_mul_inv]
lemma eval_nat_mul (n : ℕ) (a : E) (d : D) : eval (n*a) d = eval a d ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      eval_add, ih, pow_succ]
lemma lineFourier_eq (ν : Measure D) (a : E) (t : F) :
    lineFourier ν a t = ∫ d, (eval (a * ofF t) d : ℂ) ∂ν := rfl

variable {X W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W]

/-- The actual conditional moment on a predecessor fiber is the Fourier
coefficient of the actual relative difference law, not an extra hypothesis. -/
lemma predecessor_moment_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (b : X → D) (hp : Measurable p) (hb : Measurable b) (a : E) :
    (∫ w, ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖^2 ∂μ.map p) =
      (∫ d, (eval a d : ℂ) ∂DifferenceFourier.differenceLaw (μ.map p)
        (condDistrib b p μ)).re := by
  let : IsProbabilityMeasure (μ.map p) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  rw [DifferenceFourier.difference_coefficient (eval a) (measurable_eval_coe a),
    Complex.ofReal_re]
  apply integral_congr_ae
  filter_upwards [ConditionalFiber.map_identity_fiber μ p hp.aemeasurable b hb] with w hw
  congr 1
  rw [← hw, integral_map hb.aemeasurable (measurable_eval_coe a).aestronglyMeasurable]

lemma integrable_predecessor_moment_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (b : X → D) (hp : Measurable p) (hb : Measurable b) (a : E) :
    Integrable (fun w => ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖^2) (μ.map p) := by
  let : IsProbabilityMeasure (μ.map p) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hm := ((measurable_eval_coe a).comp hb).stronglyMeasurable.integral_kernel
    (κ := condDistrib id p μ)
  apply Integrable.of_bound (hm.norm.pow 2).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro w
  have hh : ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := condDistrib id p μ w)
      (C := (1 : ℝ)) (Filter.Eventually.of_forall (fun x => (Circle.norm_coe _).le))
  simpa only [Real.norm_eq_abs, Pi.pow_apply, Function.comp_apply, abs_sq, one_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2

end

theorem real_algebraic_sum_two_rotations (x : F) (hx : |(x : ℝ)| < 2) :
    ∃ u v : K, ofF x = kCoeff u + kCoeff v := by
  let r : ℝ := (x : ℝ)/2
  have hr : |r| < 1 := by dsimp [r]; rw [abs_div]; norm_num; linarith
  have hnon : 0 ≤ 1-r^2 := by nlinarith [sq_abs r, abs_nonneg r]
  let s : ℝ := Real.sqrt (1-r^2)
  have hs : s^2 = 1-r^2 := Real.sq_sqrt hnon
  have hrAlg : IsAlgebraic ℚ r := by
    change IsAlgebraic ℚ ((x / 2 : F) : ℝ)
    exact mem_algebraicClosure_iff.mp (x / 2 : F).property
  have hsAlg : IsAlgebraic ℚ s := IsAlgebraic.of_pow (by norm_num : 0 < 2) (by
    rw [hs]; exact isAlgebraic_one.sub (hrAlg.pow 2))
  have huAlg : IsAlgebraic ℚ ((r : ℂ) + Complex.I * s) :=
    (hrAlg.algebraMap (A := ℂ)).add
      ((isAlgebraic_iff_isIntegral.mpr (show IsIntegral ℚ Complex.I from ⟨Polynomial.X ^ 2 + 1, Polynomial.monic_X_pow_add_C (n := 2) 1 (by norm_num), by simp⟩)).mul (hsAlg.algebraMap (A := ℂ)))
  have hvAlg : IsAlgebraic ℚ ((r : ℂ) - Complex.I * s) :=
    (hrAlg.algebraMap (A := ℂ)).sub
      ((isAlgebraic_iff_isIntegral.mpr (show IsIntegral ℚ Complex.I from ⟨Polynomial.X ^ 2 + 1, Polynomial.monic_X_pow_add_C (n := 2) 1 (by norm_num), by simp⟩)).mul (hsAlg.algebraMap (A := ℂ)))
  have huNorm : ‖(r : ℂ)+Complex.I*s‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  have hvNorm : ‖(r : ℂ)-Complex.I*s‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  let u : K := ⟨⟨(r : ℂ)+Complex.I*s, mem_sphere_zero_iff_norm.mpr huNorm⟩, huAlg⟩
  let v : K := ⟨⟨(r : ℂ)-Complex.I*s, mem_sphere_zero_iff_norm.mpr hvNorm⟩, hvAlg⟩
  refine ⟨u, v, ?_⟩
  apply Subtype.ext
  change ((x : ℝ) : ℂ) = ((r : ℂ)+Complex.I*s)+((r : ℂ)-Complex.I*s)
  simp only [r, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators
attribute [local instance] OAI.PlaneFiveColor.Spectral.instMeasurableSpaceCircle_solutions_1
local instance instBorelSpaceCircle_solutions_1 : BorelSpace Circle := ⟨rfl⟩

lemma momentArgument_ne_zero {M N : ℕ} (z : MomentTest M N) : momentArgument z ≠ 0 := by
  unfold momentArgument
  apply mul_ne_zero
  · exact_mod_cast Nat.succ_ne_zero z.1.val
  · apply sub_ne_zero.mpr
    intro h
    have hh : z.2.val.1.val = z.2.val.2.val := by exact_mod_cast h
    exact z.2.property (Fin.ext hh)

lemma momentTest_nonempty {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N) :
    Nonempty (MomentTest M N) := by
  refine ⟨⟨⟨0, hN⟩, ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩⟩⟩
  intro h
  have hh := congrArg Fin.val h
  norm_num at hh

/-- All integer multiples of all distinct pair differences are tested before
any coefficient bin is selected. -/
theorem exists_simultaneous_moment_parameter (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) (hn : ∀ a : E, 0 ≤ (∫ d, (eval a d : ℂ) ∂ν).re)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ t : F, t ≠ 0 ∧ |(t : ℝ)| < 1/(M : ℝ) ∧
      ∀ z : MomentTest M N, (∫ d, (eval (momentArgument z * ofF t) d : ℂ) ∂ν).re < ε := by
  let : Nonempty (MomentTest M N) := momentTest_nonempty hM hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  obtain ⟨t, ht, htr, hh⟩ := exists_small_wild_parameter
    (Finset.univ : Finset (MomentTest M N)) Finset.univ_nonempty ν hν
    momentArgument momentArgument_ne_zero
    (fun z t => by simpa only [lineFourier_eq] using hn (momentArgument z * ofF t))
    (one_div_pos.mpr hMr) hε hε1
  exact ⟨t, ht, htr, fun z => hh z (Finset.mem_univ z)⟩

lemma eval_dist (a b : E) (d : D) :
    dist (eval a d : ℂ) (eval b d : ℂ) = ‖(eval (a-b) d : ℂ)-1‖ := by
  rw [eval_sub, Circle.coe_div, dist_eq_norm]
  have he : (eval a d : ℂ) / (eval b d : ℂ) - 1 =
      ((eval a d : ℂ) - (eval b d : ℂ)) / (eval b d : ℂ) := by
    field_simp
  rw [he, norm_div, Circle.norm_coe, div_one]

/-- The finite Fejér implication is applied to the actual phase law on an
individual conditional fiber. -/
theorem pair_collision_upper {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (b : X → D) (hb : Measurable b)
    (a₁ a₂ : E) (m N : ℕ) (ρ c : ℝ)
    (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
    (hMom : ∀ n, 0 < n → n ≤ N →
      ‖∫ x, (eval ((n : E)*(a₁-a₂)) (b x) : ℂ) ∂μ‖ < c) :
    μ.real {x | dist (eval a₁ (b x) : ℂ) (eval a₂ (b x) : ℂ) ≤ 4*ρ}
      < 1/(4*(m : ℝ)^2) := by
  let φ : X → Circle := fun x => eval (a₁-a₂) (b x)
  have hφ : Measurable φ := (measurable_eval _).comp hb
  let ω := μ.map φ
  let : IsProbabilityMeasure ω :=
    (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  have hco : Measurable (fun z : Circle => (z : ℂ)) :=
    (show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).measurable
  have hmom : ∀ n, 0 < n → n ≤ N → ‖∫ z, (z : ℂ)^n ∂ω‖ < c := by
    intro n hn hnN
    rw [show ω = μ.map φ from rfl,
      integral_map hφ.aemeasurable (hco.pow_const n).aestronglyMeasurable]
    simpa only [φ, eval_nat_mul, Circle.coe_pow] using hMom n hn hnN
  have hu := harc ω hmom
  have hs : MeasurableSet {z : Circle | ‖(z : ℂ)-1‖ ≤ 4*ρ} :=
    measurableSet_le ((hco.sub_const 1).norm) measurable_const
  rw [Measure.real, show ω = μ.map φ from rfl, Measure.map_apply hφ hs] at hu
  simpa only [Measure.real, Set.preimage_ofPred_eq, φ, eval_dist] using hu

end

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators

variable {X Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

lemma two_array_norm_bound {r : ℕ} {a b : Fin r → ℂ} {B : ℝ}
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hB : 0 ≤ B) : ‖![a,b]‖ ≤ B := by
  rw [pi_norm_le_iff_of_nonneg hB]
  intro j
  fin_cases j <;> assumption

lemma simultaneous_test_budget {T : Type*} [Fintype T]
    (v : T → ℝ) (c : ℝ) (hc : 0 < c)
    (hv : ∀ t, v t < min 1 (c^2 / (4*(Fintype.card T+1)))) :
    (∑ t, v t)/(c^2) < 1/4 := by
  have hs : (∑ t, v t) ≤ (Fintype.card T : ℝ) *
      (c^2 / (4*(Fintype.card T+1))) := by
    calc
      _ ≤ ∑ _t : T, c^2 / (4*(Fintype.card T+1)) :=
        Finset.sum_le_sum fun t _ => (hv t).le.trans (min_le_right _ _)
      _ = _ := by simp
  have hn : (0 : ℝ) < Fintype.card T+1 := by positivity
  rw [div_lt_iff₀ (sq_pos_of_pos hc)]
  apply hs.trans_lt
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < 4*(Fintype.card T+1))]
  nlinarith [sq_pos_of_pos hc]

attribute [local instance] OAI.PlaneFiveColor.Spectral.instMeasurableSpaceCircle_solutions_2
omit [StandardBorelSpace Y] [Nonempty Y] in

theorem finite_uniform_precision_contradiction_oai
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p))
      (condDistrib b (q ∘ p) μ)))
    (ρ c : ℝ) (N : ℕ) (hρ : 0 < ρ) (hc : 0 < c) (hN : 0 < N)
    (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
    (happrox : FiniteEncodingApproximationAt μ p q b m (((ρ^m/(m : ℝ))/100)/100)) : False := by
  classical
  let P : X → W := q ∘ p
  have hP : Measurable P := hq.comp hp
  let : IsProbabilityMeasure (μ.map P) :=
    (Measure.isProbabilityMeasure_map_iff hP.aemeasurable).mpr inferInstance
  let ν := DifferenceFourier.differenceLaw (μ.map P) (condDistrib b P μ)
  let : IsProbabilityMeasure ν := inferInstance
  have hn (a : E) : 0 ≤ (∫ d, (eval a d : ℂ) ∂ν).re := by
    rw [← predecessor_moment_sq μ P b hP hb a]
    exact integral_nonneg fun _ => sq_nonneg _
  let τ := (ρ^m/(m : ℝ))/100
  let γ := τ/100
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτδ : 18*τ^2 < (ρ^m/(m : ℝ))^2/20 := by
    dsimp [τ]
    nlinarith [sq_pos_of_pos (div_pos (pow_pos hρ m) hmr)]
  obtain ⟨r, B, C, H, hB, hC, hH, happ⟩ := happrox
  choose coeff hcoeff hInt hErr using happ
  obtain ⟨L, bins, hbins⟩ := FiniteBins.bounded_coefficient_bins
    (V := Fin m → ℂ) r B C τ hC hτ
  let M := 20*(L+1)*m^2
  have hM : 2 ≤ M := by dsimp [M]; nlinarith [Nat.one_le_iff_ne_zero.mpr hm.ne']
  let : NeZero M := ⟨by omega⟩
  let T := MomentTest M N
  let ε := min 1 (c^2/(4*(Fintype.card T+1)))
  have hε : 0 < ε := by dsimp [ε]; apply lt_min (by norm_num); positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨t, ht, htM, hTest⟩ := exists_simultaneous_moment_parameter ν hwild hn M N hM hN ε hε hε1
  let xs : Fin M → F := fun j => (j.val+1)*t
  have hxs (j : Fin M) : |(xs j : ℝ)| < 2 := by
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
    have hj : (j.val+1 : ℝ) ≤ M := by exact_mod_cast j.isLt
    have hx : |(xs j : ℝ)| = (j.val+1 : ℝ)*|(t : ℝ)| := by
      simp [xs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ j.val+1 by positivity)]
    rw [hx]
    have hmul := mul_lt_mul_of_pos_left htM (by positivity : (0 : ℝ) < j.val+1)
    have hbound : (j.val+1 : ℝ) * (1/(M : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hMr]
      exact hj
    linarith
  choose u v huv using fun j => real_algebraic_sum_two_rotations (xs j) (hxs j)
  let β := condDistrib b p μ
  let enc : K → Y → Fin m → ℂ := fun k =>
    PhaseEncoding.kernelEncoding β (fun d => (eval (kCoeff k) d : ℂ)) m
  let Hp : Fin M → X → Fin m → ℂ := fun j x => enc (u j) (p x)
  let Hm : Fin M → X → Fin m → ℂ := fun j x => enc (v j) (p x)
  let Ap : Fin M → X → Fin m → ℂ := fun j x => ∑ i, coeff (u j) (P x) i • H i (p x)
  let Am : Fin M → X → Fin m → ℂ := fun j x => ∑ i, coeff (v j) (P x) i • H i (p x)
  let ap : Fin M → X → Circle := fun j x => eval (kCoeff (u j)) (b x)
  let am : Fin M → X → Circle := fun j x => eval (kCoeff (v j)) (b x)
  let zp : X → Fin M → Fin m → Circle := fun x j i => eval (kCoeff (u j)) (g (p x) i)
  let zm : X → Fin M → Fin m → Circle := fun x j i => eval (kCoeff (v j)) (g (p x) i)
  have henc : ∀ᵐ x ∂μ, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x := by
    filter_upwards [ae_of_ae_map hp.aemeasurable hg] with x hx
    intro j
    exact ⟨(PhaseEncoding.kernelEncoding_eq_encoding β (eval (kCoeff (u j))) m hm (p x) (g (p x)) hx).symm,
      (PhaseEncoding.kernelEncoding_eq_encoding β (eval (kCoeff (v j))) m hm (p x) (g (p x)) hx).symm⟩
  have hmem : ∀ᵐ x ∂μ, ∀ j, (∃ i, ap j x = zp x j i) ∧ (∃ i, am j x = zm x j i) := by
    filter_upwards [SampledAtoms.ae_sampled_list μ p b hp hb hm g hg] with x hx
    obtain ⟨i, hi⟩ := hx
    intro j
    exact ⟨⟨i, congrArg (eval (kCoeff (u j))) hi⟩, ⟨i, congrArg (eval (kCoeff (v j))) hi⟩⟩
  let f : T → W → ℝ := fun z w =>
    ‖∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ) ∂condDistrib id P μ w‖^2
  have hf (z : T) : Integrable (f z) (μ.map P) :=
    integrable_predecessor_moment_sq μ P b hP hb _
  have hfTest (z : T) : (∫ w, f z w ∂μ.map P) < ε := by
    rw [show (∫ w, f z w ∂μ.map P) =
      (∫ d, (eval (momentArgument z * ofF t) d : ℂ) ∂ν).re from
        predecessor_moment_sq μ P b hP hb _]
    exact hTest z
  have hfBudget : (∑ z, ∫ w, f z w ∂μ.map P)/(c^2) < 1/4 :=
    simultaneous_test_budget _ c hc hfTest
  have heBudget : 10*(∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂μ)))/((M : ℝ)*τ^2) < 1/4 := by
    have hs : (∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
        (∫ x, dist (Hm j x) (Am j x)^2 ∂μ))) < (M : ℝ)*(2*γ^2) := by
      calc
        _ < ∑ _j : Fin M, 2*γ^2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun j _ => by
            have h1 : (∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) < γ^2 := hErr (u j)
            have h2 : (∫ x, dist (Hm j x) (Am j x)^2 ∂μ) < γ^2 := hErr (v j)
            linarith)
        _ = _ := by simp
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
    rw [div_lt_iff₀ (mul_pos hMr (sq_pos_of_pos hτ))]
    dsimp [γ] at hs
    nlinarith
  let arr : W → Fin M → {a : Fin 2 → Fin r → ℂ // ‖a‖ ≤ B} := fun w j =>
    ⟨![coeff (u j) w, coeff (v j) w], two_array_norm_bound (hcoeff _ _) (hcoeff _ _) hB⟩
  let bin : W → Fin M → Fin L := fun w j => bins (arr w j)
  have hlarge : (L : ℝ)*(10*m^2 : ℕ) < (9/10 : ℝ)*Fintype.card (Fin M) := by
    simp only [Fintype.card_fin]
    dsimp [M]
    push_cast
    nlinarith [sq_pos_of_pos hmr, Nat.cast_nonneg (α := ℝ) L]
  have hbin : ∀ᵐ w ∂μ.map P, ∀ i j, bin w i = bin w j →
      ∀ᵐ x ∂condDistrib id P μ w, dist (Ap i x) (Ap j x) ≤ τ ∧
        dist (Am i x) (Am j x) ≤ τ := by
    filter_upwards [ConditionalFiber.ae_in_own_fiber μ P hP] with w hw
    intro i j hij
    filter_upwards [hw] with x hx
    have hh := hbins (arr w i) (arr w j) hij (fun k => H k (p x)) (hH (p x))
    have h0 := (hh 0).le
    have h1 := (hh 1).le
    change dist (∑ k, coeff (u i) (P x) k • H k (p x))
      (∑ k, coeff (u j) (P x) k • H k (p x)) ≤ τ ∧
      dist (∑ k, coeff (v i) (P x) k • H k (p x))
      (∑ k, coeff (v j) (P x) k • H k (p x)) ≤ τ
    rw [hx]
    exact ⟨h0, h1⟩
  have hupper : ∀ᵐ w ∂μ.map P, (∀ z, f z w < c^2) → ∀ i j, i ≠ j →
      (condDistrib id P μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2) := by
    apply Filter.Eventually.of_forall
    intro w hw i j hij
    have hMom : ∀ n : ℕ, 0 < n → n ≤ N →
        ‖∫ x, (eval ((n : E)*(ofF (xs i)-ofF (xs j))) (b x) : ℂ)
          ∂condDistrib id P μ w‖ < c := by
      intro n hn hnN
      let z : T := (⟨n-1, by omega⟩, ⟨(i,j), hij⟩)
      have he : (n : E)*(ofF (xs i)-ofF (xs j)) = momentArgument z * ofF t := by
        have hnv : (n-1)+1 = n := by omega
        have hnv' : ((n-1 : ℕ) : E)+1=(n : E) := by exact_mod_cast hnv
        simp only [momentArgument, z, hnv']
        dsimp [xs]
        simp only [map_mul, map_add, map_natCast, map_one]
        ring
      have hh := hw z
      change ‖∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ)
         ∂condDistrib id P μ w‖^2 < c^2 at hh
      rw [he]
      nlinarith [norm_nonneg (∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ)
         ∂condDistrib id P μ w)]
    have hh := pair_collision_upper (condDistrib id P μ w) b hb
      (ofF (xs i)) (ofF (xs j)) m N ρ c harc hMom
    have he (j : Fin M) (x : X) : (ap j x : ℂ)*(am j x : ℂ) =
        (eval (ofF (xs j)) (b x) : ℂ) := by
      change (eval (kCoeff (u j)) (b x) : ℂ) * (eval (kCoeff (v j)) (b x) : ℂ) = _
      rw [huv j]
      exact congrArg (fun z : Circle => (z : ℂ)) (eval_add _ _ _).symm
    simpa only [he] using hh
  apply FiniteModule.common_fiber_contradiction μ P hP m hm ρ τ (c^2) hρ hτ
    (sq_pos_of_pos hc) hτδ Hp Hm Ap Am
    (fun j => (PhaseEncoding.measurable_kernelEncoding β _ (measurable_eval_coe _) m).comp hp)
    (fun j => (PhaseEncoding.measurable_kernelEncoding β _ (measurable_eval_coe _) m).comp hp)
    (fun j => hInt (u j)) (fun j => hInt (v j)) zp zm ap am
    (fun j => (measurable_eval _).comp hb) (fun j => (measurable_eval _).comp hb)
    henc hmem f hf (Filter.Eventually.of_forall (fun w z => sq_nonneg _))
    (by simp only [Fintype.card_fin]; linarith) L bin hlarge hbin hupper

end PlaneFiveColor.Spectral

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PlaneFiveColor.Spectral.finite_uniform_precision_contradiction_oai.{u_1, u_2, u_3} := @OAI.PlaneFiveColor.Spectral.finite_uniform_precision_contradiction_oai.{u_1, u_2, u_3}
