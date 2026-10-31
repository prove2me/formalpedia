-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:27:08.551032+00:00
-- url     : https://prove2.me/submissions/038becb8-d5d9-4068-9567-a3f9ed919614

import Mathlib
import Definitions.Def_OAIQ095D008

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkIntegrands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable bulk integrands, including sharp gates

The sharp terminal windows need not be continuous. This small function space
retains their actual values while providing the finite-measure operations used
in the bulk comparison.
-/

namespace Ostmann
open MeasureTheory
open scoped Classical

theorem BulkIntegrand.integrable {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (μ : Measure (σ → ℝ)) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C, _, hC⟩ := f.bounded
  exact ⟨f.measurable.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hC)⟩

theorem BulkIntegrand.slice_integrable {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (x : σ → ℝ) :
    Integrable (fun t => f (Function.update x i t)) μ := by
  obtain ⟨C, _, hC⟩ := f.bounded
  exact ⟨(f.measurable.comp (continuous_const.update i continuous_id).measurable).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun t => hC _)⟩

theorem BulkIntegrand.average_bound {σ : Type*} [Fintype σ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (f : BulkIntegrand σ)
    (C : ℝ) (hf : ∀ x, ‖f x‖ ≤ C) (x : σ → ℝ) :
    ‖f.average μ i x‖ ≤ C * μ.real Set.univ :=
  norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun _t => hf _)

theorem BulkIntegrand.average_sub {σ : Type*} [Fintype σ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (f g : BulkIntegrand σ) :
    (f.sub g).average μ i = (f.average μ i).sub (g.average μ i) := by
  ext x
  exact integral_sub (f.slice_integrable μ i x) (g.slice_integrable μ i x)

theorem BulkIntegrand.average_commute {σ : Type*} [Fintype σ]
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (i j : σ) (hij : i ≠ j) (f : BulkIntegrand σ) :
    (f.average ν j).average μ i = (f.average μ i).average ν j := by
  ext x
  obtain ⟨C, _, hC⟩ := f.bounded
  have hj : Measurable (fun z : ℝ × ℝ => f (Function.update (Function.update x i z.1) j z.2)) :=
    f.measurable.comp (((show Continuous (fun _ : ℝ × ℝ => x) from continuous_const).update i
      continuous_fst).update j continuous_snd).measurable
  have hg : Integrable (fun z : ℝ × ℝ => f (Function.update (Function.update x i z.1) j z.2))
      (μ.prod ν) := ⟨hj.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun z => hC _)⟩
  have he := integral_integral_swap (μ := μ) (ν := ν)
    (f := fun t s => f (Function.update (Function.update x i t) j s)) hg
  change (∫ t, ∫ s, f (Function.update (Function.update x i t) j s) ∂ν ∂μ) = _
  rw [he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => integral_congr_ae
    (Filter.Eventually.of_forall fun t => by dsimp only; rw [Function.update_comm hij])

theorem BulkIntegrand.averages_sub {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (l : List σ) (f g : BulkIntegrand σ) :
    (f.sub g).averages μ l = (f.averages μ l).sub (g.averages μ l) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [averages, ih, average_sub]

theorem BulkIntegrand.averages_bound {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (l : List σ)
    (hμ : ∀ i ∈ l, (μ i).real Set.univ ≤ 2) (f : BulkIntegrand σ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) :
    ∀ x, ‖f.averages μ l x‖ ≤ 2 ^ l.length * C := by
  induction l with
  | nil => simpa only [averages, List.length_nil, pow_zero, one_mul] using hf
  | cons i l ih =>
    intro x
    have ht := ih (fun j hj => hμ j (by simp [hj]))
    calc
      _ ≤ (2 ^ l.length * C) * (μ i).real Set.univ := average_bound _ _ _ _ ht x
      _ ≤ (2 ^ l.length * C) * 2 := mul_le_mul_of_nonneg_left (hμ i (by simp)) (by positivity)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

theorem BulkIntegrand.averages_commute {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (ν : Measure ℝ) [IsFiniteMeasure ν]
    (l : List σ) (i : σ) (hi : i ∉ l) (f : BulkIntegrand σ) :
    (f.averages μ l).average ν i = (f.average ν i).averages μ l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hil : i ∉ l := fun h => hi (by simp [h])
    simp only [averages, average_commute ν (μ j) i j hij, ih hil]

/-- Pointwise product comparison, valid also for the original sharp windows. -/
theorem BulkIntegrand.averages_comparison {σ : Type*} [Fintype σ] (μ ν : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (l : List σ) (hl : l.Nodup)
    (hμ : ∀ i ∈ l, (μ i).real Set.univ ≤ 2) (hν : ∀ i ∈ l, (ν i).real Set.univ ≤ 2)
    (f : BulkIntegrand σ) (ε : σ → ℝ) (hε : ∀ i ∈ l, 0 ≤ ε i)
    (herr : ∀ i ∈ l, ∀ x, ‖f.average (μ i) i x - f.average (ν i) i x‖ ≤ ε i) :
    ∀ x, ‖f.averages μ l x - f.averages ν l x‖ ≤ 2 ^ l.length * (l.map ε).sum := by
  induction l with
  | nil => simp [averages]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    have hμl : ∀ j ∈ l, (μ j).real Set.univ ≤ 2 := fun j hj => hμ j (by simp [hj])
    have hνl : ∀ j ∈ l, (ν j).real Set.univ ≤ 2 := fun j hj => hν j (by simp [hj])
    have he0 := hε i (by simp)
    have heSum : 0 ≤ (l.map ε).sum := List.sum_nonneg (by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact hε j (by simp [hj]))
    have htail := ih hl hμl hνl (fun j hj => hε j (by simp [hj]))
      (fun j hj => herr j (by simp [hj]))
    have hfirst (x : σ → ℝ) :
        ‖(f.averages ν l).average (μ i) i x - (f.averages ν l).average (ν i) i x‖ ≤
          2 ^ l.length * ε i := by
      rw [averages_commute ν (μ i) l i hi, averages_commute ν (ν i) l i hi]
      have hb := averages_bound ν l hνl ((f.average (μ i) i).sub (f.average (ν i) i))
        (ε i) he0 (herr i (by simp)) x
      rw [averages_sub] at hb
      exact hb
    intro x
    change ‖(f.averages μ l).average (μ i) i x - (f.averages ν l).average (ν i) i x‖ ≤ _
    calc
      _ ≤ ‖(f.averages μ l).average (μ i) i x - (f.averages ν l).average (μ i) i x‖ +
          ‖(f.averages ν l).average (μ i) i x - (f.averages ν l).average (ν i) i x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (2 ^ l.length * (l.map ε).sum) + 2 ^ l.length * ε i := by
        apply add_le_add _ (hfirst x)
        have ha := average_bound (μ i) i ((f.averages μ l).sub (f.averages ν l))
          (2 ^ l.length * (l.map ε).sum) htail x
        rw [average_sub] at ha
        apply ha.trans
        calc
          _ ≤ (2 ^ l.length * (l.map ε).sum) * 2 :=
            mul_le_mul_of_nonneg_left (hμ i (by simp)) (mul_nonneg (by positivity) heSum)
          _ = _ := by ring
      _ ≤ _ := by
        simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) l.length]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_WeightedPhaseExtraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting an unweighted interval sum from a weighted phase -/

namespace Ostmann

open scoped BigOperators

/-- Finite Abel summation bounds a weighted sum by the largest prefix sum
and the endpoint-plus-variation of the actual weights. -/
theorem weighted_sum_le_variation (w f : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hprefix : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, f j‖ ≤ M) :
    ‖∑ j ∈ Finset.range N, w j * f j‖ ≤ discreteVariation w N * M := by
  have hab := Finset.sum_range_by_parts w f N
  simp only [smul_eq_mul] at hab
  rw [hab]
  calc
    _ ≤ ‖w (N - 1) * ∑ j ∈ Finset.range N, f j‖ +
        ‖∑ j ∈ Finset.range (N - 1), (w (j + 1) - w j) * ∑ i ∈ Finset.range (j + 1), f i‖ :=
      norm_sub_le _ _
    _ ≤ ‖w (N - 1)‖ * M +
        ∑ j ∈ Finset.range (N - 1), ‖w (j + 1) - w j‖ * M := by
      apply add_le_add
      · rw [Complex.norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [Complex.norm_mul]
        apply mul_le_mul_of_nonneg_left (hprefix (j + 1) (by
          have hh := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = _ := by rw [discreteVariation, ← Finset.sum_mul]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimePartialSummation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial summation for the reciprocal-prime progression measure

This is the bridge from the published theta estimate (Montgomery--Vaughan,
Corollary 11.20, equations (11.32) and (11.34)) to the interval weights used
in Section 8. The conversion itself is proved here.
-/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem hasDerivAt_primeHarmonicWeight {x : ℝ} (hx : 1 < x) :
    HasDerivAt primeHarmonicWeight (primeHarmonicDerivative x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv (mul_ne_zero hx0 hlog)
  change HasDerivAt (fun y : ℝ => (y * Real.log y)⁻¹)
    (-(1 * Real.log x + x * x⁻¹) / (x * Real.log x) ^ 2) x at h
  change HasDerivAt (fun y : ℝ => (y * Real.log y)⁻¹)
    (-(Real.log x + 1) / (x * Real.log x) ^ 2) x
  simpa only [one_mul, mul_inv_cancel₀ hx0] using h

theorem continuousOn_primeHarmonicDerivative {u v : ℝ} (hu : 1 < u) :
    ContinuousOn primeHarmonicDerivative (Set.Icc u v) := by
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le hu hx.1
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  exact (((Real.continuousAt_log hx0).add continuousAt_const).neg.div
    ((continuousAt_id.mul (Real.continuousAt_log hx0)).pow 2)
    (pow_ne_zero 2 (mul_ne_zero hx0 hlog))).continuousWithinAt

/-- The exact Abel formula on the actual prime progression, with arbitrary
real endpoints greater than one. -/
theorem reciprocalPrimeInterval_eq_partialSummation (q a : ℕ)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    reciprocalPrimeInterval q a u v =
      primeHarmonicWeight v * primeProgressionTheta q a v -
      primeHarmonicWeight u * primeProgressionTheta q a u -
        ∫ t in Set.Ioc u v, primeHarmonicDerivative t * primeProgressionTheta q a t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc u v) :=
    hasDerivAt_primeHarmonicWeight (lt_of_lt_of_le hu ht.1)
  have hdi : Set.EqOn (deriv primeHarmonicWeight) primeHarmonicDerivative (Set.Icc u v) :=
    fun t ht => (hd t ht).deriv
  have hint : IntegrableOn (deriv primeHarmonicWeight) (Set.Icc u v) :=
    ((continuousOn_primeHarmonicDerivative hu).congr hdi).integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul (primeProgressionLog q a)
    (le_of_lt (lt_trans zero_lt_one hu)) huv (fun t ht => (hd t ht).differentiableAt) hint
  have hs : (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
      primeHarmonicWeight n * primeProgressionLog q a n) = reciprocalPrimeInterval q a u v := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : n.Prime ∧ Nat.ModEq q n a
    · have hn1 : (1 : ℝ) < n := by exact_mod_cast h.1.one_lt
      have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn1)
      simp [primeProgressionLog, h, primeHarmonicWeight, mul_inv_rev,
        mul_comm, hlog]
    · simp [primeProgressionLog, h]
  rw [hs] at hab
  change reciprocalPrimeInterval q a u v =
    primeHarmonicWeight v * primeProgressionTheta q a v -
    primeHarmonicWeight u * primeProgressionTheta q a u -
    ∫ t in Set.Ioc u v, deriv primeHarmonicWeight t * primeProgressionTheta q a t at hab
  have hi : (∫ t in Set.Ioc u v, deriv primeHarmonicWeight t * primeProgressionTheta q a t) =
      ∫ t in Set.Ioc u v, primeHarmonicDerivative t * primeProgressionTheta q a t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact congrArg (fun z => z * primeProgressionTheta q a t)
      (hdi (Set.Ioc_subset_Icc_self ht))
  rwa [hi] at hab

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ThetaMainTerm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exceptional theta term and its harmonic density

Differentiating the published theta main term cancels its factor `β`.
The corresponding harmonic density is retained exactly.
-/

namespace Ostmann

open MeasureTheory

theorem continuousOn_thetaMainDensity (φ χ β : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (thetaMainDensity φ χ β) (Set.Icc u v) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hu hx.1)
  exact ((continuousAt_const.sub ((Real.continuousAt_rpow_const x (β - 1)
    (Or.inl hx0)).const_mul χ)).div_const φ).continuousWithinAt

theorem thetaMain_harmonic_integral (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    (∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t) =
      primeHarmonicWeight v * thetaMainTerm φ χ β v -
      primeHarmonicWeight u * thetaMainTerm φ χ β u -
        ∫ t in Set.Ioc u v, primeHarmonicDerivative t * thetaMainTerm φ χ β t := by
  have hi1 : IntervalIntegrable primeHarmonicDerivative volume u v :=
    (continuousOn_primeHarmonicDerivative hu).intervalIntegrable_of_Icc huv
  have hi2 : IntervalIntegrable (thetaMainDensity φ χ β) volume u v :=
    (continuousOn_thetaMainDensity φ χ β (lt_trans zero_lt_one hu)).intervalIntegrable_of_Icc huv
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hasDerivAt_primeHarmonicWeight
      (lt_of_lt_of_le hu ((Set.uIcc_of_le huv) ▸ hx).1))
    (fun x hx => hasDerivAt_thetaMainTerm φ χ β hβ
      (lt_trans zero_lt_one (lt_of_lt_of_le hu ((Set.uIcc_of_le huv) ▸ hx).1))) hi1 hi2
  simpa only [intervalIntegral.integral_of_le huv] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeHarmonicError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative transfer from theta errors to harmonic interval errors -/

namespace Ostmann

open MeasureTheory

/-- Partial summation loses only endpoint weights and the variation of the
harmonic weight. The theta estimate is used on exactly this interval. -/
theorem primeHarmonic_error_le (q a : ℕ) (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v)
    (E B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hθ : ∀ t ∈ Set.Icc u v, |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E)
    (hf : ∀ t ∈ Set.Icc u v, |primeHarmonicWeight t| ≤ B)
    (hdf : ∀ t ∈ Set.Icc u v, |primeHarmonicDerivative t| ≤ D) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤
        E * (2 * B + (v - u) * D) := by
  let A := primeProgressionTheta q a
  let M := thetaMainTerm φ χ β
  let f := primeHarmonicWeight
  let f' := primeHarmonicDerivative
  have hdint : IntegrableOn f' (Set.Icc u v) :=
    (continuousOn_primeHarmonicDerivative hu).integrableOn_Icc
  have hAint : IntegrableOn (fun t => f' t * A t) (Set.Icc u v) :=
    integrableOn_mul_sum_Icc (primeProgressionLog q a)
      (le_of_lt (lt_trans zero_lt_one hu)) hdint
  have hMcont : ContinuousOn M (Set.Icc u v) := by
    intro x hx
    exact (hasDerivAt_thetaMainTerm φ χ β hβ
      (lt_trans zero_lt_one (lt_of_lt_of_le hu hx.1))).continuousAt.continuousWithinAt
  have hMint : IntegrableOn (fun t => f' t * M t) (Set.Icc u v) :=
    ((continuousOn_primeHarmonicDerivative hu).mul hMcont).integrableOn_Icc
  have hsub : (∫ t in Set.Ioc u v, f' t * A t) -
      (∫ t in Set.Ioc u v, f' t * M t) = ∫ t in Set.Ioc u v, f' t * (A t - M t) := by
    rw [← integral_sub (hAint.mono_set Set.Ioc_subset_Icc_self)
      (hMint.mono_set Set.Ioc_subset_Icc_self)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp
    ring
  have heq : reciprocalPrimeInterval q a u v -
      (∫ t in Set.Ioc u v, f t * thetaMainDensity φ χ β t) =
        f v * (A v - M v) - f u * (A u - M u) -
          ∫ t in Set.Ioc u v, f' t * (A t - M t) := by
    rw [reciprocalPrimeInterval_eq_partialSummation q a hu huv,
      thetaMain_harmonic_integral φ χ β hβ hu huv, ← hsub]
    dsimp [f, f', A, M]
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc u v) : |f t * (A t - M t)| ≤ B * E := by
    rw [abs_mul]
    exact mul_le_mul (hf t ht) (hθ t ht) (abs_nonneg _) hB
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := D * E) (f := fun t => f' t * (A t - M t)) (fun t ht => by
      have ht' : t ∈ Set.Icc u v := Set.Ioc_subset_Icc_self ((Set.uIoc_of_le huv) ▸ ht)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hdf t ht') (hθ t ht') (abs_nonneg _) hD)
  rw [intervalIntegral.integral_of_le huv, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr huv)] at hi
  rw [heq]
  have h1 := norm_sub_le (f v * (A v - M v)) (f u * (A u - M u))
  have h2 := norm_sub_le (f v * (A v - M v) - f u * (A u - M u))
    (∫ t in Set.Ioc u v, f' t * (A t - M t))
  simp only [Real.norm_eq_abs] at h1 h2
  have hv := hbound v ⟨huv, le_rfl⟩
  have hu' := hbound u ⟨le_rfl, huv⟩
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeHarmonicWeightBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit variation cost on a short logarithmic interval -/

namespace Ostmann

open MeasureTheory

theorem primeHarmonicWeight_le {u t : ℝ} (hu : 0 < u)
    (hlogu : 1 ≤ Real.log u) (hut : u ≤ t) :
    |primeHarmonicWeight t| ≤ 1 / u := by
  have ht : 0 < t := hu.trans_le hut
  have hlogt : 1 ≤ Real.log t := hlogu.trans (Real.log_le_log hu hut)
  have hp : u ≤ t * Real.log t := hut.trans (le_mul_of_one_le_right ht.le hlogt)
  rw [primeHarmonicWeight, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  simpa only [one_div] using one_div_le_one_div_of_le hu hp

theorem primeHarmonicDerivative_le {u t : ℝ} (hu : 0 < u)
    (hlogu : 1 ≤ Real.log u) (hut : u ≤ t) :
    |primeHarmonicDerivative t| ≤ 2 / u ^ 2 := by
  have ht : 0 < t := hu.trans_le hut
  have hlogt : 1 ≤ Real.log t := hlogu.trans (Real.log_le_log hu hut)
  have hl : 0 < Real.log t := by linarith
  have hb : (Real.log t + 1) / Real.log t ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    nlinarith [sq_nonneg (Real.log t - 1)]
  have heq : |primeHarmonicDerivative t| =
      ((Real.log t + 1) / Real.log t ^ 2) * (1 / t) ^ 2 := by
    rw [primeHarmonicDerivative, abs_div, abs_neg, abs_of_pos (by linarith),
      abs_of_nonneg (sq_nonneg _)]
    field_simp
  rw [heq]
  calc
    _ ≤ 2 * (1 / t) ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ ≤ 2 * (1 / u) ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hu hut) 2) (by norm_num)
    _ = _ := by ring

/-- A theta error of size `E` on an interval with `v ≤ 3u` costs at most
`6E/u` in the reciprocal-prime measure. -/
theorem primeHarmonic_short_interval_error (q a : ℕ) (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (hlogu : 1 ≤ Real.log u)
    (huv : u ≤ v) (hshort : v ≤ 3 * u) (E : ℝ) (hE : 0 ≤ E)
    (hθ : ∀ t ∈ Set.Icc u v, |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤ 6 * E / u := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have h := primeHarmonic_error_le q a φ χ β hβ hu huv E (1 / u) (2 / u ^ 2)
    (by positivity) (by positivity) hθ
    (fun t ht => primeHarmonicWeight_le hu0 hlogu ht.1)
    (fun t ht => primeHarmonicDerivative_le hu0 hlogu ht.1)
  refine h.trans ?_
  calc
    _ ≤ E * (2 * (1 / u) + (3 * u - u) * (2 / u ^ 2)) := by gcongr
    _ = 6 * E / u := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ThetaToHarmonic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal-prime estimates derived from the published theta bound -/

namespace Ostmann

open MeasureTheory

/-- The classical theta error on a multiplicative interval transfers with
an absolute factor of eighteen, uniformly in the modulus and residue. -/
theorem theta_to_harmonic_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {u v : ℝ} (hu : 1 < u)
    (hlogu : 1 ≤ Real.log u) (huv : u ≤ v) (hshort : v ≤ 3 * u)
    (hθ : ∀ t ∈ Set.Icc u v,
      |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤
        C * t * Real.exp (-c * Real.sqrt (Real.log t))) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤
        18 * C * Real.exp (-c * Real.sqrt (Real.log u)) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hv0 : 0 < v := hu0.trans_le huv
  let E := C * v * Real.exp (-c * Real.sqrt (Real.log u))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hθ' (t : ℝ) (ht : t ∈ Set.Icc u v) :
      |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E := by
    apply (hθ t ht).trans
    dsimp [E]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left ht.2 hC
    · apply Real.exp_le_exp.mpr
      have hs := Real.sqrt_le_sqrt (Real.log_le_log hu0 ht.1)
      nlinarith
    · positivity
    · positivity
  apply (primeHarmonic_short_interval_error q a φ χ β hβ hu hlogu huv hshort E hE hθ').trans
  dsimp [E]
  apply (div_le_iff₀ hu0).mpr
  nlinarith [mul_le_mul_of_nonneg_right hshort
    (mul_nonneg hC (Real.exp_pos (-c * Real.sqrt (Real.log u))).le)]

/-- A log interval of length at most one is a multiplicative interval with
ratio less than three, as required by the uniform partial-summation bound. -/
theorem exp_short_interval_le_three {s t : ℝ} (hst : t ≤ s + 1) :
    Real.exp t ≤ 3 * Real.exp s := by
  calc
    _ ≤ Real.exp (s + 1) := Real.exp_le_exp.mpr hst
    _ = Real.exp s * Real.exp 1 := Real.exp_add s 1
    _ ≤ Real.exp s * 3 := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (Real.exp_pos s).le
    _ = _ := mul_comm _ _

/-- The form used in the finite log-cell partition, before the harmless
change of variables in the main integral. -/
theorem theta_to_log_interval_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {s t : ℝ} (hs : 1 ≤ s)
    (hst : s ≤ t) (hshort : t ≤ s + 1)
    (hθ : ∀ x ∈ Set.Icc (Real.exp s) (Real.exp t),
      |primeProgressionTheta q a x - thetaMainTerm φ χ β x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ x in Set.Ioc (Real.exp s) (Real.exp t),
        primeHarmonicWeight x * thetaMainDensity φ χ β x| ≤
        18 * C * Real.exp (-c * Real.sqrt s) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  simpa only [Real.log_exp] using theta_to_harmonic_error q a φ χ β c C hβ hc hC
    (Real.one_lt_exp_iff.mpr hs0) (by simpa only [Real.log_exp] using hs)
    (Real.exp_le_exp.mpr hst) (exp_short_interval_le_three hshort) hθ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained Page density in logarithmic coordinates -/

namespace Ostmann

open MeasureTheory

/-- The Jacobian cancels the `1/x` part of the harmonic weight. The
exceptional contribution has no extra factor of its zero `β`. -/
theorem thetaMain_log_substitution (φ χ β : ℝ) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    (∫ x in Set.Ioc (Real.exp s) (Real.exp t),
      primeHarmonicWeight x * thetaMainDensity φ χ β x) =
        ∫ y in Set.Ioc s t, primeLogDensity φ χ β y := by
  let g := fun x => primeHarmonicWeight x * thetaMainDensity φ χ β x
  have hg : ContinuousOn g (Real.exp '' Set.uIcc s t) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy0 : 0 < y := hs.trans_le (((Set.uIcc_of_le hst) ▸ hy).1)
    have hexp : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy0
    have hw := (hasDerivAt_primeHarmonicWeight hexp).continuousAt
    have hd : ContinuousAt (thetaMainDensity φ χ β) (Real.exp y) :=
      (continuousAt_const.sub ((Real.continuousAt_rpow_const _ (β - 1)
        (Or.inl (Real.exp_ne_zero y))).const_mul χ)).div_const φ
    exact (hw.mul hd).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (fun y (_ : y ∈ Set.uIcc s t) => Real.hasDerivAt_exp y)
    Real.continuous_exp.continuousOn hg
  calc
    _ = ∫ x in Real.exp s..Real.exp t, g x :=
      (intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hst)).symm
    _ = ∫ y in s..t, (g ∘ Real.exp) y * Real.exp y := hsub.symm
    _ = ∫ y in s..t, primeLogDensity φ χ β y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy0 : 0 < y := hs.trans_le (((Set.uIcc_of_le hst) ▸ hy).1)
      dsimp [g, primeHarmonicWeight, thetaMainDensity, primeLogDensity]
      rw [Real.log_exp, ← Real.exp_mul]
      rw [mul_comm y (β - 1)]
      field_simp
    _ = _ := intervalIntegral.integral_of_le hst

/-- The actual reciprocal-prime interval estimate in logarithmic coordinates,
proved from the precise theta estimate. -/
theorem prime_log_interval_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {s t : ℝ} (hs : 1 ≤ s)
    (hst : s ≤ t) (hshort : t ≤ s + 1)
    (hθ : ∀ x ∈ Set.Icc (Real.exp s) (Real.exp t),
      |primeProgressionTheta q a x - thetaMainTerm φ χ β x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity φ χ β y| ≤
        18 * C * Real.exp (-c * Real.sqrt s) := by
  have h := theta_to_log_interval_error q a φ χ β c C hβ hc hC hs hst hshort hθ
  rwa [thetaMain_log_substitution φ χ β (lt_of_lt_of_le zero_lt_one hs) hst] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedProgressionInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Precisely stated published inputs for primes in progressions

Reference: H. L. Montgomery and R. C. Vaughan, *Multiplicative Number
Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics 97,
Chapter 11, DOI 10.1017/CBO9780511618314.013.

`PublishedProgressionInput.theta` is Corollary 11.20, equations (11.32) and
(11.34), p. 381. `complete` specifies the exceptional zero in Theorem 11.3,
p. 360. `unique` is the real-zero specialization of Corollary 11.10 (Page),
p. 369. The positive zero-free constant can be decreased so these use one
constant and the harmless denominator `log (4*q)` throughout.

These are explicit conditional inputs. In particular, no logarithmic
interval estimate or arithmetic comparison is assumed here.
-/

namespace Ostmann

/-- The logarithmic prime estimate is derived by partial summation; it is
not included among the published assumptions. -/
theorem PublishedProgressionInput.local_log_interval (P : PublishedProgressionInput)
    (q a : ℕ) (hq : 1 ≤ q) (ha : a.Coprime q) {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (P.localZero q) a) (pageBeta (P.localZero q)) y| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) := by
  apply prime_log_interval_error q a _ _ _ _ _ (ne_of_gt (pageBeta_pos _))
    P.decay_pos.le P.errorConstant_nonneg hs hst hshort
  intro x hx
  apply P.theta q hq a ha x
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have htwo : (2 : ℝ) ≤ Real.exp s := by
    have h := Real.add_one_le_exp s
    linarith
  exact htwo.trans hx.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single exceptional character for every modulus in a row

Only zeros in Page's common region are retained. Local exceptional zeros
outside that region will be bounded as an error, rather than identified
with a character belonging to a different modulus.
-/

namespace Ostmann

open Classical

theorem selectedPageZero_spec (P : PublishedProgressionInput) (Q : ℕ)
    (e : PrimitiveRealZero) (he : selectedPageZero P Q = some e) :
    e.modulus ≤ Q ∧ 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta := by
  unfold selectedPageZero at he
  split at he
  next hex =>
    have h := Option.some.inj he
    exact h ▸ hex.choose_spec
  next => simp at he

theorem selectedPageZero_eq (P : PublishedProgressionInput) (Q : ℕ)
    (hQ : 2 ≤ Q) (e : PrimitiveRealZero) (hmod : e.modulus ≤ Q)
    (hnear : 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta) :
    selectedPageZero P Q = some e := by
  have hex : ∃ f : PrimitiveRealZero, f.modulus ≤ Q ∧
      1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ f.beta := ⟨e, hmod, hnear⟩
  have heq := P.unique Q hQ hex.choose e hex.choose_spec.1 hmod hex.choose_spec.2 hnear
  unfold selectedPageZero
  rw [dite_eq_left hex, heq]

theorem page_region_mono (P : PublishedProgressionInput) {q Q : ℕ}
    (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    1 - P.kappa / Real.log (4 * (q : ℝ)) ≤
      1 - P.kappa / Real.log (4 * (Q : ℝ)) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hlog : Real.log (4 * (q : ℝ)) ≤ Real.log (4 * (Q : ℝ)) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 4 hqQ)
  have hdiv := div_le_div_of_nonneg_left P.kappa_pos.le hpos hlog
  linarith

theorem localZero_eq_of_selected (P : PublishedProgressionInput) {q Q : ℕ}
    (hq : 1 ≤ q) (hqQ : q ≤ Q) (e : PrimitiveRealZero)
    (he : selectedPageZero P Q = some e) (hd : e.modulus ∣ q) :
    P.localZero q = some e :=
  P.complete q hq e hd
    ((page_region_mono P hq hqQ).trans (selectedPageZero_spec P Q e he).2)

/-- Every local correction either equals the restriction of the same global
Page correction, or is a zero lying strictly outside the common region.
In the latter case the global correction is absent from that modulus. -/
theorem localZero_selected_alternative (P : PublishedProgressionInput) {q Q : ℕ}
    (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    P.localZero q = pageAtModulus q (selectedPageZero P Q) ∨
      ∃ e : PrimitiveRealZero, P.localZero q = some e ∧
        e.beta < 1 - P.kappa / Real.log (4 * (Q : ℝ)) ∧
        pageAtModulus q (selectedPageZero P Q) = none := by
  cases hl : P.localZero q with
  | none =>
    left
    cases hg : selectedPageZero P Q with
    | none => simp [pageAtModulus]
    | some e =>
      by_cases hd : e.modulus ∣ q
      · have hc := localZero_eq_of_selected P hq hqQ e hg hd
        rw [hl] at hc
        contradiction
      · simp [pageAtModulus, hd]
  | some e =>
    have hd := P.divides q e hl
    by_cases hn : 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta
    · left
      have he := selectedPageZero_eq P Q hQ e
        ((Nat.le_of_dvd (by omega) hd).trans hqQ) hn
      simp [he, pageAtModulus, hd]
    · right
      refine ⟨e, rfl, lt_of_not_ge hn, ?_⟩
      cases hg : selectedPageZero P Q with
      | none => simp [pageAtModulus]
      | some f =>
        by_cases hf : f.modulus ∣ q
        · have hc := localZero_eq_of_selected P hq hqQ f hg hf
          rw [hl] at hc
          have hef := Option.some.inj hc
          exact False.elim (hn (hef ▸ (selectedPageZero_spec P Q f hg).2))
        · simp [pageAtModulus, hf]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CRTResidueAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independent residue averages from the Chinese remainder theorem -/

namespace Ostmann

open scoped BigOperators

theorem crtUnitEquiv_apply {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (u : (ZMod (∏ i, a i))ˣ) (i : I) :
    crtUnitEquiv a hc u i = Units.map
      ((ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i))).toMonoidHom) u := by
  apply Units.ext
  change ZMod.prodEquivPi a hc (u : ZMod (∏ i, a i)) i = _
  exact ZMod.prodEquivPi_apply a hc u i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteProductPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite independent priors used for the arithmetic samples -/

namespace Ostmann

open scoped BigOperators

theorem productPrior_nonneg {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (x : Fin n → A) :
    0 ≤ productPrior μ x := Finset.prod_nonneg fun i _ => hμ i (x i)

theorem productPrior_mass {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i, ∑ a, μ i a = 1) :
    (∑ x : Fin n → A, productPrior μ x) = 1 := by
  unfold productPrior
  rw [← Fintype.prod_sum]
  simp only [hμ, Finset.prod_const_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDensityBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds on the retained density and on discarded real zeros -/

namespace Ostmann

open MeasureTheory

/-- A zero separated from one by `d` contributes at most `exp (-d*s)`
throughout a logarithmic interval beginning at `s ≥ 1`. -/
theorem primeLogDensity_correction_le (φ χ β d : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hd : 0 ≤ d) (hβ : β ≤ 1 - d)
    {s y : ℝ} (hs : 1 ≤ s) (hsy : s ≤ y) :
    |primeLogDensity φ χ β y - primeLogDensity φ 0 1 y| ≤
      Real.exp (-d * s) := by
  have hy : (1 : ℝ) ≤ y := hs.trans hsy
  have hden : (1 : ℝ) ≤ φ * y := by nlinarith
  have hden0 : 0 < φ * y := lt_of_lt_of_le zero_lt_one hden
  have hid : primeLogDensity φ χ β y - primeLogDensity φ 0 1 y =
      -(χ * Real.exp ((β - 1) * y)) / (φ * y) := by
    dsimp [primeLogDensity]
    ring
  rw [hid, abs_div, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hden0]
  have hexp : Real.exp ((β - 1) * y) ≤ Real.exp (-d * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp ((β - 1) * y) / (φ * y) :=
      div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right hχ (Real.exp_pos _).le) hden0.le
    _ ≤ Real.exp (-d * s) / (φ * y) := div_le_div_of_nonneg_right hexp hden0.le
    _ ≤ Real.exp (-d * s) := (div_le_self (Real.exp_pos _).le hden)

theorem primeLogDensity_integral_correction_le (φ χ β d : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hd : 0 ≤ d) (hβ : β ≤ 1 - d)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |(∫ y in Set.Ioc s t, primeLogDensity φ χ β y) -
      (∫ y in Set.Ioc s t, primeLogDensity φ 0 1 y)| ≤ Real.exp (-d * s) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hI (χ β : ℝ) : IntegrableOn (primeLogDensity φ χ β) (Set.Ioc s t) :=
    (continuousOn_primeLogDensity φ χ β hs0).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [← integral_sub (hI χ β) (hI 0 1)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := Real.exp (-d * s))
    (f := fun y => primeLogDensity φ χ β y - primeLogDensity φ 0 1 y)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact primeLogDensity_correction_le φ χ β d hφ hχ hd hβ hs
        (((Set.uIoc_of_le hst) ▸ hy).1.le))
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at hi
  exact hi.trans (by nlinarith [Real.exp_pos (-d * s)])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_UniformPrimeProgressions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform prime intervals with one retained Page character

The second error below accounts for local exceptional zeros outside Page's
common region. This derives simultaneous compatibility across moduli from
the published zero uniqueness, rather than assuming compatibility of the
short-interval estimates.
-/

namespace Ostmann

open MeasureTheory

theorem PublishedProgressionInput.uniform_log_interval (P : PublishedProgressionInput)
    {q Q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
        (pageBeta (pageAtModulus q (selectedPageZero P Q))) y| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) +
        Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ))) := by
  have hlocal := P.local_log_interval q a hq ha hs hst hshort
  rcases localZero_selected_alternative P hQ hq hqQ with heq | ⟨e, he, hfar, hn⟩
  · rw [heq] at hlocal
    exact hlocal.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hφ : (1 : ℝ) ≤ Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
    have hlog : 0 < Real.log (4 * (Q : ℝ)) := by
      apply Real.log_pos
      have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have hcorr := primeLogDensity_integral_correction_le (Nat.totient q)
      (pageCoefficient (some e) a) e.beta (P.kappa / Real.log (4 * (Q : ℝ)))
      hφ (pageCoefficient_abs_le_one _ _) (div_nonneg P.kappa_pos.le hlog.le)
      hfar.le hs hst hshort
    rw [he] at hlocal
    rw [hn]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t))
      (∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (some e) a) e.beta y)
      (∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q) 0 1 y)
    simp only [Real.norm_eq_abs] at htri
    have hbound := htri.trans (add_le_add hlocal hcorr)
    have hexp : Real.exp (-(P.kappa / Real.log (4 * (Q : ℝ))) * s) =
        Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ))) := by
      congr 1
      ring
    rw [hexp] at hbound
    exact hbound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeIntervalVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted short prime intervals from the published progression input -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem reciprocalPrimeInterval_add (q a : ℕ) (u v w : ℝ) (huv : u ≤ v) (hvw : v ≤ w) :
    reciprocalPrimeInterval q a u v + reciprocalPrimeInterval q a v w =
      reciprocalPrimeInterval q a u w := by
  exact Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor huv) (Nat.floor_le_floor hvw)

theorem primeLogDensity_integral_add (φ χ β u v w : ℝ) (hu : 0 < u) (huv : u ≤ v) (hvw : v ≤ w) :
    (∫ y in Set.Ioc u v, primeLogDensity φ χ β y) +
      (∫ y in Set.Ioc v w, primeLogDensity φ χ β y) =
        ∫ y in Set.Ioc u w, primeLogDensity φ χ β y := by
  rw [← intervalIntegral.integral_of_le huv, ← intervalIntegral.integral_of_le hvw,
    ← intervalIntegral.integral_of_le (huv.trans hvw)]
  exact intervalIntegral.integral_add_adjacent_intervals
    ((continuousOn_primeLogDensity φ χ β hu).intervalIntegrable_of_Icc huv)
    ((continuousOn_primeLogDensity φ χ β (hu.trans_le huv)).intervalIntegrable_of_Icc hvw)

/-- Finite Abel summation turns the uniform interval error into a variation
error for the actual complex weights. There is no factor for the number of
partition intervals. -/
theorem PublishedProgressionInput.weighted_prime_interval_variation
    (P : PublishedProgressionInput) {Q q a : ℕ}
    (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (hs0 : 1 ≤ s 0) (N : ℕ) (hshort : s N ≤ s 0 + 1)
    (w : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range N, w j *
      ((reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) -
        ∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y : ℝ) : ℂ)‖ ≤
      discreteVariation w N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) := by
  let E : ℝ → ℝ := fun t => reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp t) -
    ∫ y in Set.Ioc (s 0) t, selectedPrimeLogDensity P Q q a y
  have hzero : E (s 0) = 0 := by simp [E, reciprocalPrimeInterval]
  have hstep (j : ℕ) :
      reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) -
        (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y) =
          E (s (j + 1)) - E (s j) := by
    have hp := reciprocalPrimeInterval_add q a (Real.exp (s 0)) (Real.exp (s j))
      (Real.exp (s (j + 1))) (Real.exp_le_exp.mpr (hs (Nat.zero_le _)))
      (Real.exp_le_exp.mpr (hs (Nat.le_succ _)))
    have hi := primeLogDensity_integral_add (Nat.totient q)
      (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
      (pageBeta (pageAtModulus q (selectedPageZero P Q))) (s 0) (s j) (s (j + 1))
      (by linarith) (hs (Nat.zero_le _)) (hs (Nat.le_succ _))
    change (∫ y in Set.Ioc (s 0) (s j), selectedPrimeLogDensity P Q q a y) +
      (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y) =
        (∫ y in Set.Ioc (s 0) (s (j + 1)), selectedPrimeLogDensity P Q q a y) at hi
    dsimp only [E]
    linarith
  have hprefix (k : ℕ) (hk : k ≤ N) :
      ‖∑ j ∈ Finset.range k, ((E (s (j + 1)) - E (s j) : ℝ) : ℂ)‖ ≤
        18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ))) := by
    rw [← Complex.ofReal_sum, Finset.sum_range_sub (fun j => E (s j)), hzero, sub_zero,
      Complex.norm_real, Real.norm_eq_abs]
    exact P.uniform_log_interval hQ hq hqQ ha hs0 (hs (Nat.zero_le k))
      ((hs hk).trans hshort)
  simp_rw [hstep]
  exact weighted_sum_le_variation w _ N _ hprefix

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing a smooth cutoff on an actual prime log cell -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem log_mem_of_mem_exp_interval {p : ℕ} {s t : ℝ}
    (hp : p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊) :
    Real.log (p : ℝ) ∈ Set.Ioc s t := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
  have hexp : Real.exp s < p := Nat.lt_of_floor_lt hlo
  have hp0 : (0 : ℝ) < p := (Real.exp_pos s).trans hexp
  exact ⟨(Real.lt_log_iff_exp_lt hp0).mpr hexp,
    (Real.log_le_iff_le_exp hp0).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hhi)⟩

theorem reciprocalPrimeInterval_nonneg (q a : ℕ) (u v : ℝ) :
    0 ≤ reciprocalPrimeInterval q a u v := by
  apply Finset.sum_nonneg
  intro p _
  split <;> positivity

theorem primeLogDensity_abs_le_two (φ χ β : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    |primeLogDensity φ χ β y| ≤ 2 := by
  obtain ⟨hn, hu⟩ := primeLogDensity_bounds φ χ β (by linarith) hχ hβ (by linarith)
  rw [abs_of_nonneg hn]
  apply hu.trans
  exact div_le_self (by norm_num) (by nlinarith : (1 : ℝ) ≤ φ * y)

theorem primeLogDensity_integral_abs_le_two (φ χ β : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |∫ y in Set.Ioc s t, primeLogDensity φ χ β y| ≤ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := (2 : ℝ)) (f := primeLogDensity φ χ β)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact primeLogDensity_abs_le_two φ χ β hφ hχ hβ
        (hs.trans (((Set.uIoc_of_le hst) ▸ hy).1.le)))
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at h
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexPrimeWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex smooth weights on actual prime intervals -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexPrimeInterval_add (q a : ℕ) (u v t : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexPrimeInterval q a u v w + complexPrimeInterval q a v t w =
      complexPrimeInterval q a u t w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

theorem complexPrimeInterval_freeze (q a : ℕ) (s t : ℝ) (w : ℝ → ℂ) (c : ℂ) (η : ℝ)
    (hw : ∀ y ∈ Set.Ioc s t, ‖w y - c‖ ≤ η) :
    ‖complexPrimeInterval q a s t w -
      c * (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) : ℂ)‖ ≤
        η * reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) := by
  have heq : complexPrimeInterval q a s t w -
      c * (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) : ℂ) =
      ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
        if p.Prime ∧ Nat.ModEq q p a then (w (Real.log p) - c) * ((p : ℝ)⁻¹ : ℂ) else 0 := by
    unfold complexPrimeInterval reciprocalPrimeInterval
    rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split <;> simp_all [sub_mul]
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
        η * (if p.Prime ∧ Nat.ModEq q p a then (p : ℝ)⁻¹ else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : p.Prime ∧ Nat.ModEq q p a
      · rw [ite_eq_left h, ite_eq_left h, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg p)]
        exact mul_le_mul_of_nonneg_right (hw _ (log_mem_of_mem_exp_interval hp)) (by positivity)
      · simp [h]
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Freezing a continuous complex weight costs its oscillation times the
length of the log interval. In particular the cost is additive over meshes. -/
theorem complex_density_integral_freeze (φ χ β s t : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) (hs : 1 ≤ s) (hst : s ≤ t)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc s t)) (c : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc s t, ‖w y - c‖ ≤ η) :
    ‖(∫ y in Set.Ioc s t, w y * (primeLogDensity φ χ β y : ℂ)) -
      c * (∫ y in Set.Ioc s t, primeLogDensity φ χ β y : ℝ)‖ ≤ 2 * η * (t - s) := by
  have hc := continuousOn_primeLogDensity φ χ β (t := t) (by linarith : 0 < s)
  have hiw : IntegrableOn (fun y => w y * (primeLogDensity φ χ β y : ℂ)) (Set.Ioc s t) :=
    (hwc.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hic : IntegrableOn (fun y => c * (primeLogDensity φ χ β y : ℂ)) (Set.Ioc s t) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have heq : (∫ y in Set.Ioc s t, w y * (primeLogDensity φ χ β y : ℂ)) -
      c * (∫ y in Set.Ioc s t, primeLogDensity φ χ β y : ℝ) =
      ∫ y in Set.Ioc s t, (w y - c) * (primeLogDensity φ χ β y : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul, ← integral_sub hiw hic]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    ring
  rw [heq]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := 2 * η)
    (f := fun y => (w y - c) * (primeLogDensity φ χ β y : ℂ))
    (fun y hy => by
      have hy' := (Set.uIoc_of_le hst) ▸ hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hw y hy')
        (primeLogDensity_abs_le_two φ χ β hφ hχ hβ (hs.trans hy'.1.le))
        (abs_nonneg _) hη).trans_eq (mul_comm η 2))
  rwa [intervalIntegral.integral_of_le hst, abs_of_nonneg (sub_nonneg.mpr hst)] at hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimePartitionVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partition approximation without a partition-count loss -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complexPrimeInterval_partition (q a : ℕ) (s : ℕ → ℝ) (hs : Monotone s)
    (w : ℝ → ℂ) (N : ℕ) :
    (∑ j ∈ Finset.range N, complexPrimeInterval q a (s j) (s (j + 1)) w) =
      complexPrimeInterval q a (s 0) (s N) w := by
  induction N with
  | zero => simp [complexPrimeInterval]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact complexPrimeInterval_add q a _ _ _ w (hs (Nat.zero_le _)) (hs (Nat.le_succ _))

theorem reciprocalPrimeInterval_partition (q a : ℕ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) :
    (∑ j ∈ Finset.range N, reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1)))) =
      reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) := by
  induction N with
  | zero => simp [reciprocalPrimeInterval]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact reciprocalPrimeInterval_add q a _ _ _
        (Real.exp_le_exp.mpr (hs (Nat.zero_le _))) (Real.exp_le_exp.mpr (hs (Nat.le_succ _)))

theorem integral_Ioc_partition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) (f : ℝ → E)
    (hf : ContinuousOn f (Set.Icc (s 0) (s N))) :
    (∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)), f y) =
      ∫ y in Set.Ioc (s 0) (s N), f y := by
  have heq (j : ℕ) : (∫ y in Set.Ioc (s j) (s (j + 1)), f y) =
      ∫ y in (s j)..(s (j + 1)), f y :=
    (intervalIntegral.integral_of_le (hs (Nat.le_succ _))).symm
  simp_rw [heq]
  rw [← intervalIntegral.integral_of_le (hs (Nat.zero_le _))]
  apply intervalIntegral.sum_integral_adjacent_intervals
  intro j hj
  apply (hf.mono ?_).intervalIntegrable_of_Icc (hs (Nat.le_succ _))
  intro y hy
  exact ⟨(hs (Nat.zero_le _)).trans hy.1, hy.2.trans (hs (by omega))⟩

/-- The oscillation error is proportional to total mass and total interval
length. The progression error is proportional to variation, with neither
error multiplied by the number of intervals. -/
theorem PublishedProgressionInput.prime_partition_variation (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (hs0 : 1 ≤ s 0) (N : ℕ) (hshort : s N ≤ s 0 + 1)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc (s 0) (s N))) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖w y - w (s j)‖ ≤ η) :
    ‖complexPrimeInterval q a (s 0) (s N) w -
        ∫ y in Set.Ioc (s 0) (s N), w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      discreteVariation (fun j => w (s j)) N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) +
      η * (reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) +
        2 * (s N - s 0)) := by
  let A (j : ℕ) := complexPrimeInterval q a (s j) (s (j + 1)) w
  let B (j : ℕ) := w (s j) * (reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) : ℂ)
  let C (j : ℕ) := w (s j) * (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y : ℝ)
  let D (j : ℕ) := ∫ y in Set.Ioc (s j) (s (j + 1)), w y * (selectedPrimeLogDensity P Q q a y : ℂ)
  have hρ : ContinuousOn (selectedPrimeLogDensity P Q q a) (Set.Icc (s 0) (s N)) :=
    continuousOn_primeLogDensity _ _ _ (by linarith)
  have hA : ‖∑ j ∈ Finset.range N, (A j - B j)‖ ≤
      η * reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp (s N)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, η * reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) := by
        apply Finset.sum_le_sum
        intro j hj
        exact complexPrimeInterval_freeze q a _ _ w _ η (hw j (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.mul_sum, reciprocalPrimeInterval_partition q a s hs N]
  have hD : ‖∑ j ∈ Finset.range N, (C j - D j)‖ ≤ 2 * η * (s N - s 0) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, 2 * η * (s (j + 1) - s j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_sub_rev]
        apply complex_density_integral_freeze _ _ _ _ _
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q))
          (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _)
          (hs0.trans (hs (Nat.zero_le _))) (hs (Nat.le_succ _)) w
        · apply hwc.mono
          intro y hy
          exact ⟨(hs (Nat.zero_le _)).trans hy.1,
            hy.2.trans (hs (by have := Finset.mem_range.mp hj; omega))⟩
        · exact hη
        · exact hw j (Finset.mem_range.mp hj)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub s]
  have hBC : ‖∑ j ∈ Finset.range N, (B j - C j)‖ ≤
      discreteVariation (fun j => w (s j)) N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) := by
    simpa only [B, C, ← mul_sub, ← Complex.ofReal_sub] using
      P.weighted_prime_interval_variation hQ hq hqQ ha s hs hs0 N hshort (fun j => w (s j))
  have hid : complexPrimeInterval q a (s 0) (s N) w -
        (∫ y in Set.Ioc (s 0) (s N), w y * (selectedPrimeLogDensity P Q q a y : ℂ)) =
      (∑ j ∈ Finset.range N, (A j - B j)) +
        (∑ j ∈ Finset.range N, (B j - C j)) + (∑ j ∈ Finset.range N, (C j - D j)) := by
    have hcont : ContinuousOn (fun y => w y * (selectedPrimeLogDensity P Q q a y : ℂ))
        (Set.Icc (s 0) (s N)) := hwc.mul (Complex.continuous_ofReal.comp_continuousOn hρ)
    rw [← complexPrimeInterval_partition q a s hs w N,
      ← integral_Ioc_partition s hs N (fun y => w y * (selectedPrimeLogDensity P Q q a y : ℂ)) hcont]
    simp only [Finset.sum_sub_distrib, A, D]
    ring
  rw [hid]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (by linarith [add_le_add (add_le_add hA hBC) hD])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ContinuousIntervalMesh
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite meshes for the continuous factors in prime comparison -/

namespace Ostmann

/-- Mesh fineness is arbitrary and has no arithmetic cost: the progression
comparison uses total variation instead of counting the subintervals. -/
theorem continuous_interval_mesh (u v : ℝ) (huv : u ≤ v) (w : ℝ → ℂ)
    (hw : ContinuousOn w (Set.Icc u v)) (η : ℝ) (hη : 0 < η) :
    ∃ (s : ℕ → ℝ) (N : ℕ), 0 < N ∧ Monotone s ∧ s 0 = u ∧ s N = v ∧
      ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖w y - w (s j)‖ ≤ η := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hw) η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((v - u) / δ)
  let N := n + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hmesh : (v - u) / N < δ := by
    apply (div_lt_iff₀ hN).mpr
    have hh : (v - u) / δ < (N : ℝ) := hn.trans (by dsimp [N]; push_cast; linarith)
    have := (div_lt_iff₀ hδ).mp hh
    nlinarith
  let s : ℕ → ℝ := fun j => u + (v - u) * j / N
  have hs : Monotone s := by
    intro i j hij
    dsimp [s]
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hij)
      (sub_nonneg.mpr huv)) hN.le
  have hs0 : s 0 = u := by simp [s]
  have hsN : s N = v := by dsimp [s]; field_simp; ring
  refine ⟨s, N, by dsimp [N]; omega, hs, hs0, hsN, ?_⟩
  intro j hj y hy
  have hsju : u ≤ s j := by rw [← hs0]; exact hs (Nat.zero_le _)
  have hsjv : s (j + 1) ≤ v := by rw [← hsN]; exact hs (by omega)
  have hsj : s j ∈ Set.Icc u v := ⟨hsju, (hs (Nat.le_succ _)).trans hsjv⟩
  have hyuv : y ∈ Set.Icc u v := ⟨hsju.trans hy.1.le, hy.2.trans hsjv⟩
  have hwidth : s (j + 1) - s j = (v - u) / N := by dsimp [s]; push_cast; ring
  have hdist : dist y (s j) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1.le)]
    calc
      y - s j ≤ s (j + 1) - s j := sub_le_sub_right hy.2 _
      _ < δ := hwidth ▸ hmesh
  simpa only [dist_eq_norm] using (hmod y hyuv (s j) hsj hdist).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MonotoneWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variation of the smooth factors on monotone argument intervals -/

namespace Ostmann

open scoped BigOperators

theorem clipRealInterval_monotone (lo hi : ℝ) : Monotone (clipRealInterval lo hi) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

/-- Only bounds on the actual compact argument interval are needed. -/
theorem discreteVariation_comp_monotoneOn (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc lo hi, ‖Φ x‖ ≤ B)
    (hlip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, u j ∈ Set.Icc lo hi)
    (hmono : ∀ j < N - 1, u j ≤ u (j + 1)) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u (N - 1) - u 0) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u (j + 1) - u j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simpa only [abs_of_nonneg (sub_nonneg.mpr (hmono j hj'))] using
          hlip (u (j + 1)) (hrange (j + 1) (by omega)) (u j) (hrange j (by omega))
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]
  have hw : u (N - 1) - u 0 ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).2
    have h0 := (hrange 0 (Nat.zero_le _)).1
    linarith
  exact add_le_add (hbound _ (hrange _ le_rfl))
    (hs.trans (mul_le_mul_of_nonneg_left hw hD))

theorem discreteVariation_comp_antitoneOn (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc lo hi, ‖Φ x‖ ≤ B)
    (hlip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, u j ∈ Set.Icc lo hi)
    (hanti : ∀ j < N - 1, u (j + 1) ≤ u j) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u 0 - u (N - 1)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u j - u (j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hh := hlip (u (j + 1)) (hrange (j + 1) (by omega)) (u j) (hrange j (by omega))
        rw [abs_of_nonpos (sub_nonpos.mpr (hanti j hj'))] at hh
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub']
  have hw : u 0 - u (N - 1) ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).1
    have h0 := (hrange 0 (Nat.zero_le _)).2
    linarith
  exact add_le_add (hbound _ (hrange _ le_rfl))
    (hs.trans (mul_le_mul_of_nonneg_left hw hD))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialRootCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root cells used to split the long-variable weights

A cell records the side of each real root, retaining the roots themselves as
separate cells. Polynomial inequalities are constant on a cell; polynomial
arguments are monotone when the derivative roots are included among the cuts.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem rootCellCode_no_root_between (S : Finset ℝ) {x y : ℝ}
    (hxy : x < y) (hcode : rootCellCode S x = rootCellCode S y) :
    ∀ r ∈ S, r ∉ Set.Icc x y := by
  intro r hr hrange
  have he := congrFun hcode ⟨r, hr⟩
  change compare x r = compare y r at he
  rcases lt_or_eq_of_le hrange.1 with hxr | hxr
  · have hyr : y < r := compare_lt_iff_lt.mp (he.symm.trans (compare_lt_iff_lt.mpr hxr))
    linarith [hrange.2]
  · have hyr : y = r := compare_eq_iff_eq.mp (he.symm.trans (compare_eq_iff_eq.mpr hxr))
    linarith

/-- A continuous real function with no zeros on an interval has one sign. -/
theorem continuous_sign_on_interval (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Ioo a b)) (hn : ∀ x ∈ Set.Ioo a b, f x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 ≤ f x) ∨ (∀ x ∈ Set.Ioo a b, f x ≤ 0) := by
  by_cases hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x
  · exact Or.inl hpos
  · right
    push Not at hpos
    obtain ⟨x, hx, hfx⟩ := hpos
    intro y hy
    by_contra hfy
    have hfy' : 0 < f y := lt_of_not_ge hfy
    obtain ⟨z, hz, hfz⟩ := isPreconnected_Ioo.intermediate_value hx hy hf
      (show (0 : ℝ) ∈ Set.Icc (f x) (f y) from ⟨hfx.le, hfy'.le⟩)
    exact hn z hz hfz

theorem polynomialRootCuts_card {I : Type*} [Fintype I] (P : I → Polynomial ℝ) :
    (polynomialRootCuts P).card ≤ ∑ i, (P i).natDegree := by
  apply (Finset.card_biUnion_le).trans
  apply Finset.sum_le_sum
  intro i _
  exact (P i).roots.toFinset_card_le.trans (P i).card_roots'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FiniteRootMesh
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite interval partition at every arithmetic root -/

namespace Ostmann
open scoped Classical

/-- Partition a bounded interval at all roots in it, retaining the roots as
endpoints. The number of intervals is at most the number of cuts plus one. -/
theorem finite_root_mesh (S : Finset ℝ) (u v : ℝ) (huv : u ≤ v) :
    ∃ (s : ℕ → ℝ) (N : ℕ), Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧
      ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (s j) (s (j + 1)) := by
  let R := insert u (insert v (S.filter (fun r => r ∈ Set.Icc u v)))
  have hu : u ∈ R := by simp [R]
  have hv : v ∈ R := by simp [R]
  have hpos : 0 < R.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hmem (r : ℝ) (hr : r ∈ R) : r ∈ Set.Icc u v := by
    simp only [R, Finset.mem_insert, Finset.mem_filter] at hr
    rcases hr with rfl | rfl | ⟨_, hr⟩
    · exact ⟨le_rfl, huv⟩
    · exact ⟨huv, le_rfl⟩
    · exact hr
  let f := R.orderEmbOfFin rfl
  have hf0 : f ⟨0, hpos⟩ = u := by
    rw [Finset.orderEmbOfFin_zero rfl hpos]
    exact le_antisymm (Finset.min'_le R u hu)
      (hmem _ (Finset.min'_mem R _)).1
  have hflast : f ⟨R.card - 1, Nat.sub_lt hpos (by decide)⟩ = v := by
    rw [Finset.orderEmbOfFin_last rfl hpos]
    exact le_antisymm (hmem _ (Finset.max'_mem R _)).2 (Finset.le_max' R v hv)
  let N := R.card - 1
  let s := fun j : ℕ => f ⟨min j N, lt_of_le_of_lt (min_le_right _ _) (by omega)⟩
  have hs : Monotone s := by
    intro i j hij
    exact f.monotone (show min i N ≤ min j N from min_le_min hij le_rfl)
  have hs0 : s 0 = u := by simpa only [s, Nat.zero_min] using hf0
  have hsN : s N = v := by simpa only [s, min_self, N] using hflast
  refine ⟨s, N, hs, hs0, hsN, ?_, ?_⟩
  · have hcard : R.card ≤ S.card + 2 := by
      calc
        R.card ≤ (insert v (S.filter (fun r => r ∈ Set.Icc u v))).card + 1 := Finset.card_insert_le _ _
        _ ≤ (S.filter (fun r => r ∈ Set.Icc u v)).card + 1 + 1 := by
          gcongr
          exact Finset.card_insert_le _ _
        _ ≤ S.card + 2 := by have := Finset.card_filter_le S (fun r => r ∈ Set.Icc u v); omega
    omega
  · intro j hj r hr hin
    have hjc : j < R.card := by omega
    have hj1c : j + 1 < R.card := by omega
    have he0 : s j = f ⟨j, hjc⟩ := by simp only [s, min_eq_left (by omega : j ≤ N)]
    have he1 : s (j + 1) = f ⟨j + 1, hj1c⟩ := by
      simp only [s, min_eq_left (by omega : j + 1 ≤ N)]
    have hrange : r ∈ Set.Icc u v :=
      ⟨(hs0 ▸ hs (Nat.zero_le j)).trans hin.1.le,
        hin.2.le.trans (hsN ▸ hs (by omega : j + 1 ≤ N))⟩
    have hrR : r ∈ R := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hr, hrange⟩))
    let k := (R.orderIsoOfFin rfl).symm ⟨r, hrR⟩
    have hk : f k = r := congrArg Subtype.val ((R.orderIsoOfFin rfl).apply_symm_apply ⟨r, hrR⟩)
    have hleft : (⟨j, hjc⟩ : Fin R.card) < k := f.lt_iff_lt.mp (by rw [← he0, hk]; exact hin.1)
    have hright : k < (⟨j + 1, hj1c⟩ : Fin R.card) := f.lt_iff_lt.mp (by rw [← he1, hk]; exact hin.2)
    have hl : j < k.val := hleft
    have hr' : k.val < j + 1 := hright
    omega

/-- The side of every root is constant in the open part of one partition cell. -/
theorem rootCellCode_eq_of_root_free (S : Finset ℝ) (a b x y : ℝ)
    (hfree : ∀ r ∈ S, r ∉ Set.Ioo a b)
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    rootCellCode S x = rootCellCode S y := by
  funext r
  change compare x r.val = compare y r.val
  by_cases hr : r.val ≤ a
  · rw [compare_gt_iff_gt.mpr (hr.trans_lt hx.1), compare_gt_iff_gt.mpr (hr.trans_lt hy.1)]
  · have hb : b ≤ r.val := by
      by_contra hb
      exact hfree r.val r.property ⟨lt_of_not_ge hr, lt_of_not_ge hb⟩
    rw [compare_lt_iff_lt.mpr (hx.2.trans_le hb), compare_lt_iff_lt.mpr (hy.2.trans_le hb)]

/-- A partition in logarithmic coordinates still includes every positive
root of the original giant-variable polynomials. -/
theorem finite_log_root_mesh (S : Finset ℝ) (u v : ℝ) (huv : u ≤ v) :
    ∃ (s : ℕ → ℝ) (N : ℕ), Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧
      ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))) := by
  obtain ⟨x, N, hx, hx0, hxN, hN, hfree⟩ :=
    finite_root_mesh S (Real.exp u) (Real.exp v) (Real.exp_le_exp.mpr huv)
  have hpos (j : ℕ) : 0 < x j := by
    have hh := hx (Nat.zero_le j)
    rw [hx0] at hh
    exact (Real.exp_pos u).trans_le hh
  let s := fun j => Real.log (x j)
  refine ⟨s, N, ?_, ?_, ?_, hN, ?_⟩
  · intro i j hij
    exact Real.log_le_log (hpos i) (hx hij)
  · simp only [s, hx0, Real.log_exp]
  · simp only [s, hxN, Real.log_exp]
  · intro j hj r hr
    simpa only [s, Real.exp_log (hpos _)] using hfree j hj r hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ContinuousPrimeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the full continuous weight with the retained Page measure -/

namespace Ostmann
open MeasureTheory

/-- A continuous weight with a uniform variation budget can be used directly
in the published progression estimate. No mesh parameter survives. -/
theorem PublishedProgressionInput.continuous_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V : ℝ)
    (hV : ∀ (s : ℕ → ℝ), Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V) :
    ‖complexPrimeInterval q a u v w -
        ∫ y in Set.Ioc u v, w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) := by
  let M := reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) + 2 * (v - u)
  have hM : 0 ≤ M := add_nonneg (reciprocalPrimeInterval_nonneg q a _ _)
    (mul_nonneg (by norm_num) (sub_nonneg.mpr huv))
  have hM1 : 0 < M + 1 := by linarith
  have hE : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) := by
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.errorConstant_nonneg)
      (Real.exp_pos _).le) (Real.exp_pos _).le
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (M + 1)
  have hη : 0 < η := div_pos hε hM1
  obtain ⟨s, N, _hN, hs, hs0, hsN, hosc⟩ := continuous_interval_mesh u v huv w hwc η hη
  have hc : ContinuousOn w (Set.Icc (s 0) (s N)) := by simpa only [hs0, hsN] using hwc
  have hb := P.prime_partition_variation hQ hq hqQ ha s hs
    (by simpa only [hs0] using hu) N (by simpa only [hs0, hsN] using hshort)
    w hc η hη.le hosc
  rw [hs0, hsN] at hb
  apply hb.trans
  have hvar := mul_le_mul_of_nonneg_right (hV s hs N hs0 hsN) hE
  have hsmall : η * M ≤ ε := by
    have hid : η * (M + 1) = ε := by dsimp [η]; field_simp
    nlinarith
  exact add_le_add hvar hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeExceptionalPoints
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining prime atoms on the boundaries of arithmetic root cells -/

namespace Ostmann
open scoped BigOperators Classical

/-- Changing the weight at finitely many primes costs their actual atom
masses. The estimate is uniform in the residue class and keeps endpoints. -/
theorem complexPrimeInterval_exceptional_bound (q a : ℕ) (u v : ℝ)
    (w g : ℝ → ℂ) (S : Finset ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      p.Prime → Nat.ModEq q p a → ‖w (Real.log p) - g (Real.log p)‖ ≤ B)
    (heq : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      p.Prime → Nat.ModEq q p a → p ∉ S → w (Real.log p) = g (Real.log p)) :
    ‖complexPrimeInterval q a u v w - complexPrimeInterval q a u v g‖ ≤
      (S.card : ℝ) * B * Real.exp (-u) := by
  let T := Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊
  have he : complexPrimeInterval q a u v w - complexPrimeInterval q a u v g =
      ∑ p ∈ T, if p.Prime ∧ Nat.ModEq q p a then
        (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0 := by
    simp only [complexPrimeInterval, ← Finset.sum_sub_distrib, T]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp [sub_mul]
  have hC : 0 ≤ B * Real.exp (-u) := mul_nonneg hB (Real.exp_pos _).le
  have hpoint (p : ℕ) (hp : p ∈ T) :
      ‖(if p.Prime ∧ Nat.ModEq q p a then
        (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0)‖ ≤
        if p ∈ S then B * Real.exp (-u) else 0 := by
    by_cases hs : p ∈ S
    · rw [ite_eq_left hs]
      by_cases hc : p.Prime ∧ Nat.ModEq q p a
      · rw [ite_eq_left hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg p)]
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hc.1.pos
        have hlog := log_mem_of_mem_exp_interval hp
        have hexp : Real.exp u ≤ (p : ℝ) := by
          calc
            Real.exp u ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr hlog.1.le
            _ = _ := Real.exp_log hp0
        have hinv : (p : ℝ)⁻¹ ≤ Real.exp (-u) := by
          rw [Real.exp_neg]
          exact inv_anti₀ (Real.exp_pos _) hexp
        exact mul_le_mul (hbound p hp hc.1 hc.2) hinv (inv_nonneg.mpr hp0.le) hB
      · simpa only [ite_eq_right hc, norm_zero] using hC
    · rw [ite_eq_right hs]
      by_cases hc : p.Prime ∧ Nat.ModEq q p a
      · simp only [ite_eq_left hc, heq p hp hc.1 hc.2 hs, sub_self, zero_mul, norm_zero, le_refl]
      · simp only [ite_eq_right hc, norm_zero, le_refl]
  rw [he]
  calc
    _ ≤ ∑ p ∈ T, ‖(if p.Prime ∧ Nat.ModEq q p a then
      (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ T, if p ∈ S then B * Real.exp (-u) else 0 :=
      Finset.sum_le_sum hpoint
    _ = ((T.filter (· ∈ S)).card : ℝ) * (B * Real.exp (-u)) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (S.card : ℝ) * (B * Real.exp (-u)) := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (show T.filter (· ∈ S) ⊆ S from
        fun _ h => (Finset.mem_filter.mp h).2)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_OpenCellPrimeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison on open root cells, with boundary atoms retained -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem complexPrimeInterval_open_cell_bound (q a : ℕ) (u v : ℝ)
    (W w : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexPrimeInterval q a u v W - complexPrimeInterval q a u v w‖ ≤
      B * Real.exp (-u) := by
  have h := complexPrimeInterval_exceptional_bound q a u v W w {⌊Real.exp v⌋₊} B hB
    (fun p hp _ _ => hbound _ (log_mem_of_mem_exp_interval hp)) (by
      intro p hp hprime _ hnot
      have hlog := log_mem_of_mem_exp_interval hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hne : Real.log p ≠ v := by
        intro he
        apply hnot
        simp only [Finset.mem_singleton]
        rw [← he, Real.exp_log hp0, Nat.floor_natCast]
      exact heq _ ⟨hlog.1, lt_of_le_of_ne hlog.2 hne⟩)
  simpa only [Finset.card_singleton, Nat.cast_one, one_mul] using h

/-- A cell's interior uses its continuous smooth factor; the right endpoint
is accounted for by its prime atom, even when it is an arithmetic root. -/
theorem PublishedProgressionInput.open_cell_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    (W w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V B : ℝ)
    (hV : ∀ s : ℕ → ℝ, Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V)
    (hB : 0 ≤ B) (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexPrimeInterval q a u v W -
      ∫ y in Set.Ioc u v, w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) + B * Real.exp (-u) := by
  have h1 := complexPrimeInterval_open_cell_bound q a u v W w B hB hbound heq
  have h2 := P.continuous_prime_comparison hQ hq hqQ ha u v hu huv hshort w hwc V hV
  exact (norm_sub_le_norm_sub_add_norm_sub _ (complexPrimeInterval q a u v w) _).trans
    (by linarith)

/-- Sum the actual prime weights over the constructed root partition. The
ideal term is the sum of its continuous cell integrals with the Page factor. -/
theorem PublishedProgressionInput.piecewise_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) (hs0 : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    (W : ℝ → ℂ) (w : ℕ → ℝ → ℂ) (V B : ℕ → ℝ)
    (hwc : ∀ j < N, ContinuousOn (w j) (Set.Icc (s j) (s (j + 1))))
    (hV : ∀ j < N, ∀ r : ℕ → ℝ, Monotone r → ∀ M,
      r 0 = s j → r M = s (j + 1) → discreteVariation (fun k => w j (r k)) M ≤ V j)
    (hB : ∀ j < N, 0 ≤ B j)
    (hbound : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖W y - w j y‖ ≤ B j)
    (heq : ∀ j < N, ∀ y ∈ Set.Ioo (s j) (s (j + 1)), W y = w j y) :
    ‖complexPrimeInterval q a (s 0) (s N) W -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        w j y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N, (V j *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
          Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) + B j * Real.exp (-(s j))) := by
  rw [← complexPrimeInterval_partition q a s hs W N, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  apply P.open_cell_prime_comparison hQ hq hqQ ha _ _
    (hs0.trans (hs (Nat.zero_le _))) (hs (Nat.le_succ _))
  · have h1 := hs (by omega : j + 1 ≤ N)
    have h0 := hs (Nat.zero_le j)
    linarith
  · exact hwc j hjN
  · exact hV j hjN
  · exact hB j hjN
  · exact hbound j hjN
  · exact heq j hjN

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ProductWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of the original smooth factors retain finite variation -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_mul (f g : ℕ → ℂ) (B D : ℝ) (N : ℕ)
    (hD : 0 ≤ D) (hf : ∀ j, ‖f j‖ ≤ B) (hg : ∀ j, ‖g j‖ ≤ D) :
    discreteVariation (fun j => f j * g j) N ≤
      B * discreteVariation g N + D * discreteVariation f N := by
  have hend : ‖f (N - 1) * g (N - 1)‖ ≤ B * ‖g (N - 1)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
  have hstep (j : ℕ) : ‖f (j + 1) * g (j + 1) - f j * g j‖ ≤
      B * ‖g (j + 1) - g j‖ + D * ‖f (j + 1) - f j‖ := by
    rw [show f (j + 1) * g (j + 1) - f j * g j =
      f (j + 1) * (g (j + 1) - g j) + (f (j + 1) - f j) * g j by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
    · simpa only [mul_comm D] using mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.range (N - 1)) (fun j _ => hstep j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  unfold discreteVariation
  nlinarith [mul_nonneg hD (norm_nonneg (f (N - 1)))]

theorem discreteVariation_prod (n : ℕ) (f : Fin n → ℕ → ℂ) (B V : Fin n → ℝ) (N : ℕ)
    (hB : ∀ i, 0 ≤ B i) (hV : ∀ i, 0 ≤ V i)
    (hf : ∀ i j, ‖f i j‖ ≤ B i) (hv : ∀ i, discreteVariation (f i) N ≤ V i) :
    discreteVariation (fun j => ∏ i, f i j) N ≤ ∏ i, (B i + V i) := by
  induction n with
  | zero => simp [discreteVariation]
  | succ n ih =>
    let g : ℕ → ℂ := fun j => ∏ i : Fin n, f i.succ j
    let C : ℝ := ∏ i : Fin n, B i.succ
    let E : ℝ := ∏ i : Fin n, (B i.succ + V i.succ)
    have hC : 0 ≤ C := Finset.prod_nonneg fun i _ => hB i.succ
    have hg (j : ℕ) : ‖g j‖ ≤ C := by
      change ‖∏ i : Fin n, f i.succ j‖ ≤ C
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hf i.succ j)
    have hCE : C ≤ E := Finset.prod_le_prod (fun i _ => hB i.succ)
      (fun i _ => le_add_of_nonneg_right (hV i.succ))
    have hvg : discreteVariation g N ≤ E := ih (fun i => f i.succ) (fun i => B i.succ)
      (fun i => V i.succ) (fun i => hB i.succ) (fun i => hV i.succ)
      (fun i => hf i.succ) (fun i => hv i.succ)
    have hp : (fun j => ∏ i, f i j) = fun j => f 0 j * g j := by
      funext j
      exact Fin.prod_univ_succ _
    rw [hp, Fin.prod_univ_succ]
    apply (discreteVariation_mul (f 0) g (B 0) C N hC (hf 0) hg).trans
    calc
      _ ≤ B 0 * E + C * V 0 := add_le_add
        (mul_le_mul_of_nonneg_left hvg (hB 0)) (mul_le_mul_of_nonneg_left (hv 0) hC)
      _ ≤ B 0 * E + E * V 0 := add_le_add le_rfl (mul_le_mul_of_nonneg_right hCE (hV 0))
      _ = _ := by change B 0 * E + E * V 0 = (B 0 + V 0) * E; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the Fourier matrix of the affine action

The finite matrix from `AffineFourier` is the action of
`F(t) ↦ ∑ c(a,b) F(at+b)` on nonzero additive frequencies.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_units_eq_sum_of_zero {p : ℕ} [Fact p.Prime]
    {R : Type*} [AddCommMonoid R] (F : ZMod p → R) (hF : F 0 = 0) :
    (∑ u : (ZMod p)ˣ, F u) = ∑ x : ZMod p, F x := by
  classical
  calc
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, F x := by
      apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
      · intro u _
        exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
      · intro u _ v _ huv
        exact Units.val_injective huv
      · intro x hx
        refine ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
      · intro _ _
        rfl
    _ = ∑ x : ZMod p, F x := by
      simpa only [hF, add_zero] using
        Finset.sum_erase_add (Finset.univ : Finset (ZMod p)) F (Finset.mem_univ 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCellVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual interval pieces and smooth polynomial weights -/

namespace Ostmann

open scoped BigOperators Classical

/-- On a root cell, polynomial inequality supports really are constant. -/
theorem polynomial_nonneg_iff_of_root_cell (P : Polynomial ℝ) (S : Finset ℝ)
    (hroots : ∀ r ∈ P.roots, r ∈ S) {x y : ℝ}
    (hcode : rootCellCode S x = rootCellCode S y) :
    0 ≤ P.eval x ↔ 0 ≤ P.eval y := by
  by_cases hp : P = 0
  · simp [hp]
  have hordered (a b : ℝ) (hab : a < b)
      (hc : rootCellCode S a = rootCellCode S b) : 0 ≤ P.eval a ↔ 0 ≤ P.eval b := by
    have hn (z : ℝ) (hz : z ∈ Set.Icc a b) : P.eval z ≠ 0 := by
      intro he
      have hm : z ∈ P.roots := (Polynomial.mem_roots hp).mpr he
      exact rootCellCode_no_root_between S hab hc z (hroots z hm) hz
    constructor
    · intro ha
      by_contra hb
      have hb' : P.eval b < 0 := lt_of_not_ge hb
      obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hab.le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (P.eval b) (P.eval a) from ⟨hb'.le, ha⟩)
      exact hn z hz he
    · intro hb
      by_contra ha
      have ha' : P.eval a < 0 := lt_of_not_ge ha
      obtain ⟨z, hz, he⟩ := intermediate_value_Icc hab.le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (P.eval a) (P.eval b) from ⟨ha'.le, hb⟩)
      exact hn z hz he
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact hordered x y hxy hcode
  · rfl
  · exact (hordered y x hyx hcode.symm).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ReciprocalProgressionVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original reciprocal-integer weight in partial summation -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_const_mul (c : ℂ) (f : ℕ → ℂ) (N : ℕ) :
    discreteVariation (fun j => c * f j) N = ‖c‖ * discreteVariation f N := by
  simp only [discreteVariation, ← mul_sub, norm_mul, Finset.mul_sum, mul_add]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothPolynomialWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite products of the smooth factors appearing in a history

Profiles are clipped to their prescribed argument ranges. This leaves their
values unchanged on the retained range and requires no continuity of the sharp
range indicator; those indicators are separate functions of the root cell.
-/

namespace Ostmann

open scoped BigOperators

theorem smoothPolynomialBudget_nonneg {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    0 ≤ smoothPolynomialBudget F := by
  apply Finset.prod_nonneg
  intro i _
  exact add_nonneg (mul_nonneg (by norm_num) (F i).bound_nonneg)
    (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothPrimeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison for the actual clipped polynomial factors -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem continuous_smoothPolynomialWeight {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    Continuous (smoothPolynomialWeight F) :=
  continuous_finsetProd _ (fun i _ => (F i).continuous_value)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RootFreeSmoothWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth variation when roots are retained at the cell endpoints -/

namespace Ostmann
open scoped BigOperators

theorem polynomial_monotoneOn_no_roots (P : Polynomial ℝ) (a b : ℝ)
    (hroots : ∀ r ∈ P.derivative.roots, r ∉ Set.Ioo a b) :
    MonotoneOn P.eval (Set.Icc a b) ∨ AntitoneOn P.eval (Set.Icc a b) := by
  by_cases hd : P.derivative = 0
  · left
    have hp := Polynomial.eq_C_of_derivative_eq_zero hd
    intro x hx y hy hxy
    have hv (t : ℝ) : P.eval t = P.coeff 0 := by
      have hh := congrArg (fun Q : Polynomial ℝ => Q.eval t) hp
      simpa only [Polynomial.eval_C] using hh
    change P.eval x ≤ P.eval y
    rw [hv x, hv y]
  · have hn : ∀ x ∈ Set.Ioo a b, P.derivative.eval x ≠ 0 := by
      intro x hx hz
      exact hroots x ((Polynomial.mem_roots hd).mpr hz) hx
    rcases continuous_sign_on_interval P.derivative.eval a b
        P.derivative.continuous.continuousOn hn with hpos | hneg
    · left
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hpos x hx
    · right
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hneg x hx

theorem ClippedPolynomialFactor.variation_no_roots (f : ClippedPolynomialFactor)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hroots : ∀ r ∈ f.polynomial.derivative.roots, r ∉ Set.Ioo (u 0) (u (N - 1))) :
    discreteVariation (fun j => f.value (u j)) N ≤ f.bound + f.lip * (f.hi - f.lo) := by
  let v : ℕ → ℝ := fun j => clipRealInterval f.lo f.hi (f.polynomial.eval (u j))
  have hr (j : ℕ) (_hj : j ≤ N - 1) : v j ∈ Set.Icc f.lo f.hi :=
    clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi
  have hu' (j : ℕ) (hj : j ≤ N - 1) : u j ∈ Set.Icc (u 0) (u (N - 1)) :=
    ⟨hu (Nat.zero_le _), hu hj⟩
  change discreteVariation (fun j => f.profile (v j)) N ≤ _
  rcases polynomial_monotoneOn_no_roots f.polynomial (u 0) (u (N - 1)) hroots with hm | hm
  · apply discreteVariation_comp_monotoneOn f.profile v f.lo f.hi f.bound f.lip N
      f.lip_nonneg f.norm_le f.lipschitz hr
    intro j hj
    exact clipRealInterval_monotone f.lo f.hi
      (hm (hu' j hj.le) (hu' (j + 1) (by omega)) (hu (by omega)))
  · apply discreteVariation_comp_antitoneOn f.profile v f.lo f.hi f.bound f.lip N
      f.lip_nonneg f.norm_le f.lipschitz hr
    intro j hj
    exact clipRealInterval_monotone f.lo f.hi
      (hm (hu' j hj.le) (hu' (j + 1) (by omega)) (hu (by omega)))

theorem smoothPolynomialWeight_variation_no_roots {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots →
      r ∉ Set.Ioo (u 0) (u (N - 1))) :
    discreteVariation (fun j => smoothPolynomialWeight F (u j)) N ≤ smoothPolynomialBudget F := by
  have hV (i : Fin n) : 0 ≤ (F i).bound + (F i).lip * ((F i).hi - (F i).lo) :=
    add_nonneg (F i).bound_nonneg
      (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))
  have ht := discreteVariation_prod n (fun i j => (F i).value (u j))
    (fun i => (F i).bound) (fun i => (F i).bound + (F i).lip * ((F i).hi - (F i).lo)) N
    (fun i => (F i).bound_nonneg) hV (fun i j => (F i).norm_value (u j))
    (fun i => (F i).variation_no_roots u hu N (hroots i))
  change discreteVariation (fun j => ∏ i, (F i).value (u j)) N ≤ _
  apply ht.trans_eq
  apply Finset.prod_congr rfl
  intro i _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CommonRootMesh
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One explicit root mesh for all residue classes -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem rootMeshWeight_continuous {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (s : ℕ → ℝ) (j : ℕ) : Continuous (rootMeshWeight F w s j) :=
  continuous_const.mul ((continuous_smoothPolynomialWeight F).comp Real.continuous_exp)

theorem rootMeshWeight_variation {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (s : ℕ → ℝ) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (j : ℕ) (hj : j < N) (r : ℕ → ℝ) (hr : Monotone r) (M : ℕ)
    (hr0 : r 0 = s j) (hrM : r M = s (j + 1)) :
    discreteVariation (fun l => rootMeshWeight F w s j (r l)) M ≤
      ‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F := by
  unfold rootMeshWeight
  rw [discreteVariation_const_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply smoothPolynomialWeight_variation_no_roots F (fun l => Real.exp (r l))
    (Real.exp_monotone.comp hr) M
  intro i x hx hxin
  apply hfree j hj x (hroots i x hx)
  refine ⟨?_, ?_⟩
  · simpa only [hr0] using hxin.1
  · have hlast : Real.exp (r (M - 1)) ≤ Real.exp (s (j + 1)) := by
      rw [← hrM]
      exact Real.exp_le_exp.mpr (hr (Nat.sub_le M 1))
    exact hxin.2.trans_le hlast

theorem rootMeshWeight_bound {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (s : ℕ → ℝ) (j : ℕ) (y : ℝ) :
    ‖w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) - rootMeshWeight F w s j y‖ ≤
      2 * C * smoothPolynomialBudget F := by
  calc
    _ ≤ ‖w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)‖ +
        ‖rootMeshWeight F w s j y‖ := norm_sub_le _ _
    _ ≤ C * smoothPolynomialBudget F + C * smoothPolynomialBudget F := by
      simp only [rootMeshWeight, norm_mul]
      exact add_le_add
        (mul_le_mul (hw _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
        (mul_le_mul (hw _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
    _ = _ := by ring

theorem rootMeshWeight_eq {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y)
    (s : ℕ → ℝ) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (j : ℕ) (hj : j < N) (y : ℝ) (hy : y ∈ Set.Ioo (s j) (s (j + 1))) :
    w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) = rootMeshWeight F w s j y := by
  unfold rootMeshWeight
  congr 1
  apply hconst
  apply rootCellCode_eq_of_root_free S (Real.exp (s j)) (Real.exp (s (j + 1)))
    (Real.exp y) (Real.exp ((s j + s (j + 1)) / 2)) (hfree j hj)
  · exact ⟨Real.exp_lt_exp.mpr hy.1, Real.exp_lt_exp.mpr hy.2⟩
  · constructor <;> apply Real.exp_lt_exp.mpr <;> linarith [hy.1, hy.2]

/-- The mesh is supplied before the residue class and coefficient. -/
theorem PublishedProgressionInput.common_root_mesh_prime_comparison (P : PublishedProgressionInput)
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (hu : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexPrimeInterval q a (s 0) (s N)
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        rootMeshWeight F w s j y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
            Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
          2 * C * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  apply P.piecewise_prime_comparison hQ hq hqQ ha s hs N hu hshort
    _ (rootMeshWeight F w s) _ _
  · exact fun j _ => (rootMeshWeight_continuous F w s j).continuousOn
  · exact fun j hj r hr M hr0 hrM => rootMeshWeight_variation F w S hroots s N hfree j hj r hr M hr0 hrM
  · exact fun _ _ => mul_nonneg (mul_nonneg (by positivity) hC) (smoothPolynomialBudget_nonneg F)
  · exact fun j _ y _ => rootMeshWeight_bound F w C hC hw s j y
  · exact fun j hj y hy => rootMeshWeight_eq F w S hconst s N hfree j hj y hy

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialWeightPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual off-diagonal product of two polynomial weights -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem pairedPolynomialFactors_weight {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) (x : ℝ) :
    smoothPolynomialWeight (pairedPolynomialFactors F G) x =
      smoothPolynomialWeight F x * conj (smoothPolynomialWeight G x) := by
  simp only [smoothPolynomialWeight, pairedPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate_value, map_prod]

theorem pairedPolynomialFactors_budget {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) :
    smoothPolynomialBudget (pairedPolynomialFactors F G) =
      smoothPolynomialBudget F * smoothPolynomialBudget G := by
  simp only [smoothPolynomialBudget, pairedPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_IndependentCoordinate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating an internal-prime representative from the other samples -/

namespace Ostmann

open scoped BigOperators

theorem productPrior_insertNth {A : Type*} {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (i : Fin (n + 1)) (a : A) (x : Fin n → A) :
    productPrior μ (i.insertNth a x) = μ i a * productPrior (fun j => μ (i.succAbove j)) x := by
  unfold productPrior
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem sum_productPrior_insertNth {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin (n + 1) → A → ℝ) (i : Fin (n + 1)) (f : (Fin (n + 1) → A) → ℝ) :
    (∑ v, productPrior μ v * f v) =
      ∑ x : Fin n → A, productPrior (fun j => μ (i.succAbove j)) x *
        ∑ a : A, μ i a * f (i.insertNth a x) := by
  have h := (Fin.insertNthEquiv (fun _ : Fin (n + 1) => A) i).sum_comp
    (fun v => productPrior μ v * f v)
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change productPrior μ (i.insertNth a x) * f (i.insertNth a x) = _
  rw [productPrior_insertNth]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellPartitionConstruction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the actual prime log/residue partition

The fiber identities used by the joint comparison follow from separated
log intervals and residue classes. They are not additional distribution
hypotheses.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem primeLogCellSet_disjoint (q a b : ℕ) (s t u v : ℝ)
    (hsep : ¬Nat.ModEq q a b ∨ t ≤ u ∨ v ≤ s) :
    Disjoint (primeLogCellSet q a s t) (primeLogCellSet q b u v) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨hpI, hpP, hpA⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpJ, _, hpB⟩ := Finset.mem_filter.mp hp'
  have hi := log_mem_of_mem_exp_interval hpI
  have hj := log_mem_of_mem_exp_interval hpJ
  rcases hsep with hres | htu | hvs
  · exact hres (hpA.symm.trans hpB)
  · linarith [hi.2, hj.1]
  · linarith [hj.2, hi.1]

theorem primeCellLabel_mem {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C) (p : ℕ)
    (hp : p ∈ primeCellSupport q a s t) :
    p ∈ primeLogCellSet q (a (primeCellLabel q a s t c₀ p))
      (s (primeCellLabel q a s t c₀ p)) (t (primeCellLabel q a s t c₀ p)) := by
  have hex : ∃ c, p ∈ primeLogCellSet q (a c) (s c) (t c) := by
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    exact ⟨c, hc⟩
  unfold primeCellLabel
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem primeCellLabel_fiber {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ t c ≤ s d ∨ t d ≤ s c)
    (c : C) :
    (primeCellSupport q a s t).filter (fun p => primeCellLabel q a s t c₀ p = c) =
      primeLogCellSet q (a c) (s c) (t c) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hps, hlabel⟩ := Finset.mem_filter.mp hp
    simpa only [hlabel] using primeCellLabel_mem q a s t c₀ p hps
  · intro hp
    have hps : p ∈ primeCellSupport q a s t :=
      Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hp⟩
    refine Finset.mem_filter.mpr ⟨hps, ?_⟩
    by_contra hne
    have hdisj := primeLogCellSet_disjoint q
      (a (primeCellLabel q a s t c₀ p)) (a c)
      (s (primeCellLabel q a s t c₀ p)) (t (primeCellLabel q a s t c₀ p)) (s c) (t c)
      (hsep _ _ hne)
    exact Finset.disjoint_left.mp hdisj (primeCellLabel_mem q a s t c₀ p hps) hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete equal-mesh log cells and unit residues -/

namespace Ostmann

open scoped Classical

theorem mem_primeLogCellSet_iff {q a p : ℕ} {s t : ℝ} :
    p ∈ primeLogCellSet q a s t ↔
      p.Prime ∧ Nat.ModEq q p a ∧ Real.log (p : ℝ) ∈ Set.Ioc s t := by
  constructor
  · intro hp
    obtain ⟨hI, hprime, hres⟩ := Finset.mem_filter.mp hp
    exact ⟨hprime, hres, log_mem_of_mem_exp_interval hI⟩
  · rintro ⟨hprime, hres, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hprime, hres⟩
    · exact (Nat.floor_lt (Real.exp_pos s).le).mpr ((Real.lt_log_iff_exp_lt hp0).mp hlo)
    · exact (Nat.le_floor_iff (Real.exp_pos t).le).mpr ((Real.log_le_iff_le_exp hp0).mp hhi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_nonneg (P Q : Finset ℕ) (p : P) :
    0 ≤ primeSubsetPrior P Q p := by
  unfold primeSubsetPrior
  split_ifs
  · exact div_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact le_rfl

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

theorem primeSubsetPrior_atom (P Q : Finset ℕ) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := by
  unfold primeSubsetPrior
  split_ifs
  · exact le_of_eq (by ring)
  · positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The moving-giant arithmetic in Section 8.1

The integer constants record actual products of regular small entries. At a
reversal, the sampled compensation product `u` is inserted into both children:
their constants are `u * CL` and `u * CR`. The pivot is reconstructed over the
integers first, and only its giant factor is passed to either child.
-/

namespace Ostmann
open scoped Classical ComplexConjugate

theorem TreeNaturalLift.product {q : ℕ} {n : ℕ}
    {x : TreeLeafTuple ℕ n} {y : TreeLeafTuple (ZMod q)ˣ n}
    (h : TreeNaturalLift n x y) :
    ((treeLeafProduct n x : ℕ) : ZMod q) = (treeLeafProduct n y : (ZMod q)ˣ) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [treeLeafProduct, Nat.cast_mul, Units.val_mul]
    rw [ih h.1, ih h.2]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantSamples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the moving-giant tree from the sampled compensation slots

Each reversing node samples four positions per leaf of either child. Their
products are inserted into both child regular lists. The constructor proves
the required product consistency; it does not ask for a pre-existing diagram.
-/

namespace Ostmann
open scoped BigOperators

theorem buildMovingGiantTree_frequency (n : ℕ) (t : FrequencyTree ℤ n)
    (small : TreeLeafTuple ℕ n) (samples : MovingGiantSamples n) :
    (buildMovingGiantTree n t small samples).frequency = frequencyRoot n t := by
  cases samples <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

theorem movingNaturalProduct_append {σ : Type*} (value : σ → ℕ) (x y : List σ) :
    MovingSlotReversal.naturalProduct value (x ++ y) =
      MovingSlotReversal.naturalProduct value x * MovingSlotReversal.naturalProduct value y := by
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]

theorem movingSlotValues_flatten {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (List σ) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n x) =
      treeLeafProduct n (movingSlotValues value n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flattenMovingSlots, MovingSlotReversal.naturalProduct, List.map_append,
      List.prod_append, movingSlotValues, treeLeafProduct]
    exact congrArg₂ (· * ·) (ih x.1) (ih x.2)

theorem movingSlotValues_append {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) :
    movingSlotValues value n (appendMovingSlotLeaves n x y) =
      multiplySmallLeaves n (movingSlotValues value n x) (movingSlotValues value n y) := by
  induction n with
  | zero =>
    simp only [movingSlotValues, appendMovingSlotLeaves, multiplySmallLeaves,
      MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]
  | succ n ih => exact Prod.ext (ih x.1 y.1) (ih x.2 y.2)

theorem movingCompensationValues_product {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (Fin 4 → σ) n) :
    movingSlotValues value n (movingCompensationSlots n x) =
      compensationLeafProducts n (movingCompensationValues value n x) := by
  induction n with
  | zero =>
    change ((List.ofFn (show Fin 4 → σ from x)).map value).prod = ∏ i : Fin 4, value (x i)
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem buildMovingSlotData_frequency {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).frequency = frequencyRoot n t := by
  cases samples <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact root-cell multipliers for the original moving arithmetic support -/

namespace Ostmann
open scoped Classical

theorem rootCellCode_eq_of_subset (S T : Finset ℝ) (hST : S ⊆ T) (x y : ℝ)
    (h : rootCellCode T x = rootCellCode T y) : rootCellCode S x = rootCellCode S y := by
  funext r
  exact congrFun h ⟨r.val, hST r.property⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed residue representatives for the literal spectator recursion -/

namespace Ostmann
open scoped Classical

/-- Clearing the input period makes division compatible with congruence,
even when the individual numerators are not divisible by the denominator. -/
theorem int_modEq_ediv (c m x y : ℤ) (hc : c ≠ 0)
    (h : x ≡ y [ZMOD c * m]) : x / c ≡ y / c [ZMOD m] := by
  have hr : x % c = y % c := h.of_mul_right m
  have hrem : x % c ≡ y % c [ZMOD c * m] := by rw [hr]
  have hx : x - x % c = c * (x / c) := by
    linear_combination -(Int.emod_add_mul_ediv x c)
  have hy : y - y % c = c * (y / c) := by
    linear_combination -(Int.emod_add_mul_ediv y c)
  have hh := h.sub hrem
  rw [hx, hy] at hh
  exact Int.ModEq.mul_left_cancel' hc hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RootMeshIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reassembling root cells into the original real integral -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem rootMeshWeight_integral {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (ρ : ℝ → ℂ) (hρ : ContinuousOn ρ (Set.Icc (s 0) (s N))) :
    IntervalIntegrable (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y)
      volume (s 0) (s N) ∧
    (∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
      rootMeshWeight F w s j y * ρ y) =
      ∫ y in Set.Ioc (s 0) (s N),
        w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y := by
  let f := fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y
  have heq (j : ℕ) (hj : j < N) (y : ℝ) (hy : y ∈ Set.Ioo (s j) (s (j + 1))) :
      rootMeshWeight F w s j y * ρ y = f y := by
    rw [← rootMeshWeight_eq F w S hconst s N hfree j hj y hy]
  have hc (j : ℕ) (hj : j < N) :
      IntervalIntegrable (fun y => rootMeshWeight F w s j y * ρ y) volume (s j) (s (j + 1)) := by
    apply ((rootMeshWeight_continuous F w s j).continuousOn.mul (hρ.mono ?_)).intervalIntegrable_of_Icc
      (hs (Nat.le_succ _))
    intro y hy
    exact ⟨(hs (Nat.zero_le _)).trans hy.1, hy.2.trans (hs (by omega))⟩
  have hf (j : ℕ) (hj : j < N) : IntervalIntegrable f volume (s j) (s (j + 1)) := by
    apply (hc j hj).congr_uIoo
    rw [Set.uIoo_of_le (hs (Nat.le_succ _))]
    exact heq j hj
  refine ⟨IntervalIntegrable.trans_iterate hf, ?_⟩
  have heqI (j : ℕ) (hj : j < N) :
      (∫ y in Set.Ioc (s j) (s (j + 1)), rootMeshWeight F w s j y * ρ y) =
        ∫ y in (s j)..(s (j + 1)), f y := by
    rw [← intervalIntegral.integral_of_le (hs (Nat.le_succ _))]
    exact intervalIntegral.integral_congr_Ioo_of_le (hs (Nat.le_succ _)) (heq j hj)
  calc
    _ = ∑ j ∈ Finset.range N, ∫ y in (s j)..(s (j + 1)), f y := by
      apply Finset.sum_congr rfl
      intro j hj
      exact heqI j (Finset.mem_range.mp hj)
    _ = ∫ y in (s 0)..(s N), f y := intervalIntegral.sum_integral_adjacent_intervals hf
    _ = _ := intervalIntegral.integral_of_le (hs (Nat.zero_le _))

/-- No root-dependent main term survives the partition. The full density
and the sharp real gate remain inside one integral. -/
theorem PublishedProgressionInput.common_root_prime_integral (P : PublishedProgressionInput)
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (hu : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexPrimeInterval q a (s 0) (s N)
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc (s 0) (s N), w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
            Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
          2 * C * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  have h := P.common_root_mesh_prime_comparison S s hs N hfree hQ hq hqQ ha hu hshort F hroots
    w C hC hw hconst
  have hρ : ContinuousOn (fun y => (selectedPrimeLogDensity P Q q a y : ℂ)) (Set.Icc (s 0) (s N)) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_primeLogDensity _ _ _ (by linarith))
  rwa [(rootMeshWeight_integral F w S hconst s hs N hfree _ hρ).2] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantLogMeasures
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual ideal giant measures, including the retained Page density -/

namespace Ostmann
open MeasureTheory
open scoped ENNReal

theorem intervalDensityMeasure_integral (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : AEMeasurable ρ (volume.restrict (Set.Ioc u v)))
    (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) (f : ℝ → ℂ) :
    (∫ x, f x ∂intervalDensityMeasure u v ρ) =
      ∫ x in Set.Ioc u v, f x * (ρ x : ℂ) := by
  unfold intervalDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ hρ.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [ENNReal.toReal_ofReal (hpos x hx), Complex.real_smul, mul_comm]

theorem intervalDensityMeasure_mass (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : IntegrableOn ρ (Set.Ioc u v)) (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) :
    (intervalDensityMeasure u v ρ).real Set.univ = ∫ x in Set.Ioc u v, ρ x := by
  have hp : ∀ᵐ x ∂volume.restrict (Set.Ioc u v), 0 ≤ ρ x :=
    ae_restrict_of_forall_mem measurableSet_Ioc hpos
  rw [Measure.real, intervalDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hρ hp,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hp)]

theorem measurable_selectedPrimeLogDensity (P : PublishedProgressionInput) (Q q a : ℕ) :
    Measurable (selectedPrimeLogDensity P Q q a) := by
  unfold selectedPrimeLogDensity primeLogDensity
  fun_prop

theorem primeGiantMeasure_integral (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 ≤ u) (f : ℝ → ℂ) :
    (∫ x, f x ∂primeGiantMeasure P Q q a u v) =
      ∫ x in Set.Ioc u v, f x * (selectedPrimeLogDensity P Q q a x : ℂ) :=
  intervalDensityMeasure_integral u v _ (measurable_selectedPrimeLogDensity P Q q a).aemeasurable
    (selectedPrimeLogDensity_nonneg P Q q a u v hu) f

theorem primeGiantMeasure_mass_le_two (P : PublishedProgressionInput) (Q q a : ℕ)
    (hq : 1 ≤ q) (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    (primeGiantMeasure P Q q a u v).real Set.univ ≤ 2 := by
  rw [primeGiantMeasure, intervalDensityMeasure_mass u v _
    (selectedPrimeLogDensity_integrable P Q q a u v (by linarith))
    (selectedPrimeLogDensity_nonneg P Q q a u v (by linarith))]
  apply (le_abs_self _).trans
  exact primeLogDensity_integral_abs_le_two _ _ _
    (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q))
    (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _) hu huv hshort

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_BulkProductDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product densities for the joint Page integral -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- The scalar-density factors of the ideal bulk laws multiply inside one
finite product integral. This is used with the nonnegative Page densities. -/
theorem bulk_pi_withDensity {J : Type*} [Fintype J]
    (μ : J → Measure ℝ) [∀ j, IsFiniteMeasure (μ j)]
    (ρ : J → ℝ → ℝ)
    (hi : ∀ j, Integrable (ρ j) (μ j)) (hpos : ∀ j x, 0 ≤ ρ j x) :
    Measure.pi (fun j => (μ j).withDensity (fun x => ENNReal.ofReal (ρ j x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ j, ρ j (x j))) := by
  let ν := fun j => (μ j).withDensity (fun x => ENNReal.ofReal (ρ j x))
  let _ : ∀ j, IsFiniteMeasure (ν j) := fun j =>
    isFiniteMeasure_withDensity ((lintegral_ofReal_ne_top_iff_integrable
      (hi j).aestronglyMeasurable (Filter.Eventually.of_forall (hpos j))).mpr (hi j))
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hp : Integrable (fun x : J → ℝ => ∏ j, ρ j (x j))
      ((Measure.pi μ).restrict (Set.univ.pi s)) := by
    rw [Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (fun j => (hi j).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hp
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun j _ => hpos j (x j)),
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hn (j : J) : 0 ≤ ∫ x in s j, ρ j x ∂μ j :=
    integral_nonneg (hpos j)
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hn j)]
  apply Finset.prod_congr rfl
  intro j _
  rw [withDensity_apply _ (hs j),
    ← ofReal_integral_eq_lintegral_ofReal (hi j).restrict
      (Filter.Eventually.of_forall (hpos j))]

/-- Exact complex integral form of the joint density identity. -/
theorem bulk_integral_product_density {J : Type*} [Fintype J]
    (μ : J → Measure ℝ) [∀ j, IsFiniteMeasure (μ j)]
    (ρ : J → ℝ → ℝ) (hρ : ∀ j, Measurable (ρ j))
    (hi : ∀ j, Integrable (ρ j) (μ j)) (hpos : ∀ j x, 0 ≤ ρ j x)
    (f : (J → ℝ) → ℂ) :
    (∫ x, f x ∂Measure.pi (fun j => (μ j).withDensity (fun y => ENNReal.ofReal (ρ j y)))) =
      ∫ x, f x * ((∏ j, ρ j (x j) : ℝ) : ℂ) ∂Measure.pi μ := by
  rw [bulk_pi_withDensity μ ρ hi hpos]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => hpos j (x j)),
      Complex.real_smul, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkPageProductIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full Page density inside one product integral -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem bulk_page_product_integral {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q : ℕ) (q a : J → ℕ) (u v : J → ℝ)
    (hu : ∀ j, 0 < u j) (f : (J → ℝ) → ℂ) :
    (∫ x, f x ∂Measure.pi (fun j => primeGiantMeasure P Q (q j) (a j) (u j) (v j))) =
      ∫ x, f x * ∏ j, (selectedPrimeLogDensity P Q (q j) (a j) (x j) : ℂ)
        ∂Measure.pi (fun j => volume.restrict (Set.Ioc (u j) (v j))) := by
  let μ : J → Measure ℝ := fun j => volume.restrict (Set.Ioc (u j) (v j))
  let ρ : J → ℝ → ℝ := fun j x => max (selectedPrimeLogDensity P Q (q j) (a j) x) 0
  have hρ (j : J) : Measurable (ρ j) := (measurable_selectedPrimeLogDensity P Q (q j) (a j)).max measurable_const
  have hi (j : J) : Integrable (ρ j) (μ j) := by
    have hb : Integrable (selectedPrimeLogDensity P Q (q j) (a j)) (μ j) :=
      selectedPrimeLogDensity_integrable P Q (q j) (a j) (u j) (v j) (hu j)
    apply hb.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (max_eq_left (selectedPrimeLogDensity_nonneg P Q (q j) (a j)
      (u j) (v j) (hu j).le x hx)).symm
  have hpos (j : J) (x : ℝ) : 0 ≤ ρ j x := le_max_right _ _
  have he (j : J) : (μ j).withDensity (fun x => ENNReal.ofReal (ρ j x)) =
      primeGiantMeasure P Q (q j) (a j) (u j) (v j) := by
    unfold primeGiantMeasure intervalDensityMeasure
    congr 1
    funext x
    dsimp only [ρ]
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_eq_left bot_le
  have h := bulk_integral_product_density μ ρ hρ hi hpos f
  simp only [he] at h
  refine h.trans (integral_congr_ae ?_)
  have hm : ∀ᵐ x ∂Measure.pi μ, ∀ j, x j ∈ Set.Ioc (u j) (v j) :=
    Filter.eventually_all.mpr (fun j =>
      (Measure.tendsto_eval_ae_ae (μ := μ) (i := j)).eventually (ae_restrict_mem measurableSet_Ioc))
  filter_upwards [hm] with x hx
  congr 1
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  exact max_eq_left (selectedPrimeLogDensity_nonneg P Q (q j) (a j) (u j) (v j)
    (hu j).le (x j) (hx j))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkResidueIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping residue sums inside the real bulk integral -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- The full bounded sharp kernel is integrable against the product density. -/
theorem BulkIntegrand.page_density_integrable {J : Type*} [Fintype J]
    (f : BulkIntegrand J) (P : PublishedProgressionInput) (Q : ℕ)
    (q a : J → ℕ) (u v : J → ℝ) (hu : ∀ j, 0 < u j) :
    Integrable (fun x => f x * ∏ j, (selectedPrimeLogDensity P Q (q j) (a j) (x j) : ℂ))
      (Measure.pi (fun j => volume.restrict (Set.Ioc (u j) (v j)))) := by
  have hp : Integrable (fun x : J → ℝ => ∏ j, (selectedPrimeLogDensity P Q (q j) (a j) (x j) : ℂ))
      (Measure.pi (fun j => volume.restrict (Set.Ioc (u j) (v j)))) := by
    exact Integrable.fintype_prod (f := fun j x =>
      (selectedPrimeLogDensity P Q (q j) (a j) x : ℂ))
      (fun j => (selectedPrimeLogDensity_integrable P Q (q j) (a j) (u j) (v j) (hu j)).ofReal)
  obtain ⟨C, _, hC⟩ := f.bounded
  exact hp.bdd_mul f.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- Residue classes are summed inside the real integral. In particular there
is no number-of-boxes factor on the main term. -/
theorem bulk_page_residue_integral {J Z : Type*} [Fintype J] [Fintype Z]
    (P : PublishedProgressionInput) (Q : ℕ) (q : J → ℕ) (a : Z → J → ℕ)
    (u v : J → ℝ) (hu : ∀ j, 0 < u j) (f : Z → BulkIntegrand J) :
    (∑ z, ∫ x, f z x ∂Measure.pi (fun j => primeGiantMeasure P Q (q j) (a z j) (u j) (v j))) =
      ∫ x, ∑ z, f z x * ∏ j, (selectedPrimeLogDensity P Q (q j) (a z j) (x j) : ℂ)
        ∂Measure.pi (fun j => volume.restrict (Set.Ioc (u j) (v j))) := by
  simp_rw [bulk_page_product_integral P Q q _ u v hu]
  exact (integral_finsetSum _ (fun z _ => (f z).page_density_integrable P Q q (a z) u v hu)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkPiIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint bulk integral in ordinary finite product coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem fin_cons_update {n : ℕ} (a b : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (show Fin (n + 1) → ℝ from Fin.cons a
      (@Function.update (Fin n) (fun _ => ℝ) (Classical.decEq _) x i b)) =
      @Function.update (Fin (n + 1)) (fun _ => ℝ) (Classical.decEq _)
        (Fin.cons a x) i.succ b := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Function.update, Ne.symm (Fin.succ_ne_zero i)]
  · by_cases hj : j = i
    · subst j; simp [Function.update]
    · simp [Function.update, hj]

theorem BulkIntegrand.headSlice_average {n : ℕ} (f : BulkIntegrand (Fin (n + 1)))
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : Fin n) (a : ℝ) :
    (f.average μ i.succ).headSlice a = (f.headSlice a).average μ i := by
  ext x
  dsimp only [headSlice, average]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => congrArg f (fin_cons_update a b x i).symm

theorem BulkIntegrand.headSlice_averages {n : ℕ} (f : BulkIntegrand (Fin (n + 1)))
    (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (l : List (Fin n)) (a : ℝ) :
    (f.averages μ (l.map Fin.succ)).headSlice a =
      (f.headSlice a).averages (fun i => μ i.succ) l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, averages, headSlice_average, ih]

/-- Finite-measure Fubini, with the first coordinate displayed explicitly. -/
theorem BulkIntegrand.integral_headSlice {n : ℕ} (f : BulkIntegrand (Fin (n + 1)))
    (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] :
    (∫ x, f x ∂Measure.pi μ) =
      ∫ a, ∫ x, f.headSlice a x ∂Measure.pi (fun i => μ i.succ) ∂μ 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he := (measurePreserving_piFinSuccAbove μ 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr (f.integrable (Measure.pi μ))
  rw [← he.integral_comp' (fun x => f x)]
  change (∫ z, (f ∘ e.symm) z ∂(μ 0).prod (Measure.pi (fun j => μ (Fin.succAbove 0 j)))) = _
  rw [integral_prod (f ∘ e.symm) hi]
  congr 1
  funext a
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, headSlice, Function.comp_apply, Equiv.coe_fn_mk, cast_eq]

theorem BulkIntegrand.averages_finRange {n : ℕ} (f : BulkIntegrand (Fin n))
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (x : Fin n → ℝ) :
    f.averages μ (List.finRange n) x = ∫ y, f y ∂Measure.pi μ := by
  induction n with
  | zero =>
    have hf (y : Fin 0 → ℝ) : f y = f x := congrArg f (Subsingleton.elim _ _)
    simp only [List.finRange_zero, averages]
    simp_rw [hf]
    have hm : (Measure.pi μ).real Set.univ = 1 := by
      rw [Measure.real, Measure.pi_univ]
      simp
    simp only [integral_const, Complex.real_smul, hm, Complex.ofReal_one, one_mul]
  | succ n ih =>
    rw [f.integral_headSlice μ, List.finRange_succ]
    dsimp only [averages, average]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun a => ?_
    have hx : @Function.update (Fin (n + 1)) (fun _ => ℝ) (Classical.decEq _)
        x 0 a = Fin.cons a (fun i => x i.succ) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    dsimp only
    calc
      _ = (f.averages μ ((List.finRange n).map Fin.succ)) (Fin.cons a (fun i => x i.succ)) :=
        congrArg (fun z => (f.averages μ ((List.finRange n).map Fin.succ)) z) hx
      _ = _ := by
        change ((f.averages μ ((List.finRange n).map Fin.succ)).headSlice a) (fun i => x i.succ) = _
        rw [f.headSlice_averages]
        exact ih _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkCoordinateInsertion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freeze the nonbulk coordinates and integrate the selected bulk slots -/

namespace Ostmann
open MeasureTheory
open scoped Classical

theorem bulkCoordinateInsert_at {σ J : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (y : J → ℝ) (j : J) :
    bulkCoordinateInsert base e y (e j) = y j := by
  have h : ∃ k, e k = e j := ⟨j, rfl⟩
  rw [bulkCoordinateInsert, dite_eq_left h]
  congr 1
  exact e.injective h.choose_spec

theorem bulkCoordinateInsert_update {σ J : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (y : J → ℝ) (j : J) (a : ℝ) :
    bulkCoordinateInsert base e (Function.update y j a) =
      Function.update (bulkCoordinateInsert base e y) (e j) a := by
  funext i
  by_cases h : ∃ k, e k = i
  · obtain ⟨k, rfl⟩ := h
    rw [bulkCoordinateInsert_at]
    by_cases hkj : k = j
    · subst k
      simp
    · rw [Function.update_of_ne hkj, Function.update_of_ne (fun h => hkj (e.injective h)),
        bulkCoordinateInsert_at]
  · have hne : i ≠ e j := fun hi => h ⟨j, hi.symm⟩
    rw [Function.update_of_ne hne]
    simp only [bulkCoordinateInsert, dite_eq_right h]

theorem BulkIntegrand.pullBulk_average {σ J : Type*} [Fintype σ] [Fintype J]
    (f : BulkIntegrand σ) (base : σ → ℝ) (e : J ↪ σ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (j : J) :
    (f.average μ (e j)).pullBulk base e = (f.pullBulk base e).average μ j := by
  ext y
  change (∫ a, f (Function.update (bulkCoordinateInsert base e y) (e j) a) ∂μ) =
    ∫ a, f (bulkCoordinateInsert base e (Function.update y j a)) ∂μ
  simp_rw [bulkCoordinateInsert_update]

theorem BulkIntegrand.pullBulk_averages {σ J : Type*} [Fintype σ] [Fintype J]
    (f : BulkIntegrand σ) (base : σ → ℝ) (e : J ↪ σ)
    (μ : σ → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (l : List J) :
    (f.averages μ (l.map e)).pullBulk base e =
      (f.pullBulk base e).averages (fun j => μ (e j)) l := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.map_cons, averages, pullBulk_average, ih]

theorem BulkIntegrand.selected_bulk_integral {σ : Type*} [Fintype σ]
    {k : ℕ} (f : BulkIntegrand σ) (base : σ → ℝ) (e : Fin k ↪ σ)
    (μ : σ → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (y : Fin k → ℝ) :
    f.averages μ ((List.finRange k).map e) (bulkCoordinateInsert base e y) =
      ∫ z, f (bulkCoordinateInsert base e z) ∂Measure.pi (fun j => μ (e j)) := by
  have h := congrArg (fun g : BulkIntegrand (Fin k) => g y)
    (f.pullBulk_averages base e μ (List.finRange k))
  rw [BulkIntegrand.averages_finRange] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkCoordinateEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the actual bulk slots leaves their product law unchanged -/

namespace Ostmann
open MeasureTheory
open scoped Classical

theorem bulkCoordinateInsert_reindex {σ J K : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (g : K ≃ J) (y : J → ℝ) :
    bulkCoordinateInsert base (g.toEmbedding.trans e) (y ∘ g) =
      bulkCoordinateInsert base e y := by
  funext i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    obtain ⟨k, rfl⟩ := g.surjective j
    change bulkCoordinateInsert base (g.toEmbedding.trans e) (y ∘ g)
      ((g.toEmbedding.trans e) k) = _
    rw [bulkCoordinateInsert_at, bulkCoordinateInsert_at]
    rfl
  · have hk : ¬∃ k, (g.toEmbedding.trans e) k = i := by
      rintro ⟨k, hk⟩
      exact hi ⟨g k, hk⟩
    simp only [bulkCoordinateInsert, dite_eq_right hi, dite_eq_right hk]

/-- The finite enumeration may be chosen for the proof while the product
integral remains indexed by the original tree-and-word bulk coordinates. -/
theorem BulkIntegrand.selected_bulk_integral_enum {σ J : Type*} [Fintype σ] [Fintype J]
    {k : ℕ} (f : BulkIntegrand σ) (base : σ → ℝ) (e : J ↪ σ) (g : Fin k ≃ J)
    (μ : σ → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (y : J → ℝ) :
    f.averages μ ((List.finRange k).map (fun j => e (g j))) (bulkCoordinateInsert base e y) =
      ∫ z, f (bulkCoordinateInsert base e z) ∂Measure.pi (fun j => μ (e j)) := by
  let eg := g.toEmbedding.trans e
  have h := f.selected_bulk_integral base eg μ (y ∘ g)
  rw [bulkCoordinateInsert_reindex] at h
  refine h.trans ?_
  have he := ((measurePreserving_piCongrLeft (fun j => μ (e j)) g).symm).integral_comp'
    (fun z => f (bulkCoordinateInsert base eg z))
  refine he.symm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change f (bulkCoordinateInsert base eg (z ∘ g)) = f (bulkCoordinateInsert base e z)
    exact congrArg f (bulkCoordinateInsert_reindex base e g z)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkProductMixtures
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact reassembly of the joint bulk cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- Expanding all cell mixtures counts each joint box once and keeps the
original product of harmonic normalization constants. -/
theorem bulk_product_mixtures {J C : Type*} [Fintype J] [Fintype C]
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ : J → C → Measure ℝ) [∀ j c, IsFiniteMeasure (μ j c)] :
    Measure.pi (fun j => bulkCellMixture (Z j) (μ j)) =
      ENNReal.ofReal (∏ j, Z j) • ∑ c : J → C, Measure.pi (fun j => μ j (c j)) := by
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.pi_pi,
    bulkCellMixture, smul_eq_mul]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hZ j), Finset.prod_mul_distrib,
    Fintype.prod_sum]

/-- The exact joint integral corresponding to the original normalized cell
mixture; cell counts enter through a sum of integrals, not as a main-term loss. -/
theorem BulkIntegrand.integral_product_mixtures {J C : Type*} [Fintype J] [Fintype C]
    (f : BulkIntegrand J) (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ : J → C → Measure ℝ) [∀ j c, IsFiniteMeasure (μ j c)] :
    (∫ x, f x ∂Measure.pi (fun j => bulkCellMixture (Z j) (μ j))) =
      ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∫ x, f x ∂Measure.pi (fun j => μ j (c j)) := by
  rw [bulk_product_mixtures Z hZ μ, integral_smul_measure,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => hZ j), Complex.real_smul,
    integral_finsetSum_measure]
  intro c _
  exact f.integrable _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkResidueMixtures
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact joint cell and residue reconstruction -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- Sum the residue classes before estimating. The common original
normalization stays outside the sum, and the cell boxes are counted once. -/
theorem bulk_residue_mixture_integral {J C R : Type*}
    [Fintype J] [Fintype C] [Fintype R]
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ : R → J → C → Measure ℝ) [∀ z j c, IsFiniteMeasure (μ z j c)]
    (f : R → BulkIntegrand J) :
    (∑ z, ∫ y, f z y ∂Measure.pi (fun j => bulkCellMixture (Z j) (μ z j))) =
      ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
        ∫ y, f z y ∂Measure.pi (fun j => μ z j (c j)) := by
  simp_rw [BulkIntegrand.integral_product_mixtures _ Z hZ]
  rw [← Finset.mul_sum, Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkBoxReassembly
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic box masses absorb the joint cell sum -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- Reassembling boxes costs the product of their normalized masses. It does
not cost the number of boxes in the main term. -/
theorem bulk_box_sum_bound {J C : Type*} [Fintype J] [Fintype C]
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j) (H : J → C → ℝ)
    (hH : ∀ j c, 0 ≤ H j c) (hmass : ∀ j, Z j * ∑ c, H j c ≤ 2)
    (B : ℝ) (hB : 0 ≤ B) (E : (J → C) → ℂ)
    (hE : ∀ c, ‖E c‖ ≤ B * ∏ j, H j (c j)) :
    ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c, E c‖ ≤ B * 2 ^ Fintype.card J := by
  have hZp : 0 ≤ ∏ j, Z j := Finset.prod_nonneg fun j _ => hZ j
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hZp]
  calc
    _ ≤ (∏ j, Z j) * ∑ c : J → C, B * ∏ j, H j (c j) := by
      apply mul_le_mul_of_nonneg_left _ hZp
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hE c)
    _ = B * ∏ j, (Z j * ∑ c, H j c) := by
      rw [← Finset.mul_sum, ← Fintype.prod_sum, Finset.prod_mul_distrib]
      ring
    _ ≤ B * 2 ^ Fintype.card J := by
      apply mul_le_mul_of_nonneg_left _ hB
      calc
        _ ≤ ∏ _j : J, (2 : ℝ) := Finset.prod_le_prod
          (fun j _ => mul_nonneg (hZ j) (Finset.sum_nonneg fun c _ => hH j c))
          (fun j _ => hmass j)
        _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original regular slot lists in every moving child -/

namespace Ostmann
open scoped Classical

theorem flattenMovingSlots_append_perm {σ : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) :
    (flattenMovingSlots n (appendMovingSlotLeaves n x y)).Perm
      (flattenMovingSlots n x ++ flattenMovingSlots n y) := by
  apply List.perm_iff_count.mpr
  intro a
  induction n with
  | zero => simp [flattenMovingSlots, appendMovingSlotLeaves]
  | succ n ih =>
    have hx := ih x.1 y.1
    have hy := ih x.2 y.2
    simpa only [flattenMovingSlots, appendMovingSlotLeaves, List.count_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg₂ (· + ·) hx hy

theorem buildMovingSlotData_regular_perm {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).regularSlots.Perm
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) := by
  cases samples with
  | leaf => exact List.Perm.refl _
  | @node n samples left right =>
    apply List.perm_iff_count.mpr
    intro a
    simp only [buildMovingSlotData, MovingSlotData.regularSlots, flattenMovingSlots,
      List.count_append]
    omega

/-- Coherence is proved for the actual sampler, not supplied as a new
assumption about the original history. -/
theorem buildMovingSlotData_regular_coherent {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).RegularCoherent := by
  induction samples with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    let U := movingCompensationSlots n samples
    have hL := (buildMovingSlotData_regular_perm n t.2.1
      (appendMovingSlotLeaves n U small.1) bulk.1 left).trans
      ((flattenMovingSlots_append_perm n U small.1).append_right (flattenMovingSlots n bulk.1))
    have hR := (buildMovingSlotData_regular_perm n t.2.2
      (appendMovingSlotLeaves n U small.2) bulk.2 right).trans
      ((flattenMovingSlots_append_perm n U small.2).append_right (flattenMovingSlots n bulk.2))
    refine ⟨?_, ?_, ihL _ _ _, ihR _ _ _⟩
    · simpa only [List.append_assoc] using hL
    · simpa only [List.append_assoc] using hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

theorem int_modEq_isCoprime_iff {x y m : ℤ} (h : x ≡ y [ZMOD m]) :
    IsCoprime x m ↔ IsCoprime y m := by
  have transport {a b : ℤ} (hab : a ≡ b [ZMOD m]) (ha : IsCoprime a m) :
      IsCoprime b m := by
    obtain ⟨k, hk⟩ := hab.dvd
    obtain ⟨u, v, huv⟩ := ha
    refine ⟨u, v - u * k, ?_⟩
    linear_combination huv + u * hk
  exact ⟨transport h, transport h.symm⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency residues with compensation factors inverted

Unlike the signed integer recursion, this recursion divides only by the
frequency. Compensation factors are inverted modulo a frequency power, so
no internal prime enters its period. One power is consumed per reversal.
-/

namespace Ostmann
open scoped Classical

theorem movingFrequencyLocalUnits_modEq {σ : Type*} {n : ℕ} (T : MovingSlotData σ n)
    (XL XR YL YR M : ℤ) (hM : T.frequencyProduct ∣ M)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    movingFrequencyLocalUnits T XL XR ↔ movingFrequencyLocalUnits T YL YR := by
  exact and_congr (int_modEq_isCoprime_iff (hL.of_dvd hM))
    (int_modEq_isCoprime_iff (hR.of_dvd hM))

theorem MovingSlotData.frequencyProduct_node_dvd {σ : Type*} {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (R : ℤ)
    (h : (MovingSlotData.node s CL CR U left right).frequencyProduct ∣ R) :
    s ∣ R ∧ left.frequencyProduct ∣ R ∧ right.frequencyProduct ∣ R := by
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_trans ⟨left.frequencyProduct * right.frequencyProduct, by
      simp only [frequencyProduct]; ring⟩ h
  · exact dvd_trans ⟨s * right.frequencyProduct, by
      simp only [frequencyProduct]; ring⟩ h
  · exact (dvd_mul_left _ _).trans h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFieldSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated spectator factor on every field residue pair -/

namespace Ostmann
open scoped Classical

theorem buildMovingSlotData_modular_spectator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (x y : ZMod q)
    (z : TreeLeafTuple (ZMod q)ˣ n)
    (hz : TreeNaturalLift n (movingSlotValues value n bulk) z) :
    movingModularSpectator value q g D (buildMovingSlotData n t small bulk samples) x y =
      movingFieldGiantAmplitude g D
        (buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value)) x y z := by
  induction samples generalizing x y with
  | leaf =>
    change (MovingSlotReversal.naturalProduct value (show List σ from bulk) : ZMod q) =
      (show (ZMod q)ˣ from z) at hz
    simp only [buildMovingSlotData, movingModularSpectator, MovingSampleSlots.values,
      buildMovingGiantTree, movingFieldGiantAmplitude, movingSlotValues, treeLeafProduct,
      flattenMovingSlots, movingNaturalProduct_append, Nat.cast_mul, hz]
    congr 2
    ring
  | @node n samples left right ihL ihR =>
    change TreeNaturalLift n (movingSlotValues value n bulk.1) z.1 ∧
      TreeNaturalLift n (movingSlotValues value n bulk.2) z.2 at hz
    let u := movingCompensationSlots n samples
    let L := buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 left
    let R := buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 right
    let p := (MovingSlotData.step t.1
      (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
      (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
      (flattenMovingSlots n u) L R false).modularPivot value q x y
    have hp : p = reconstructedEntry (t.1 : ZMod q)
        ((frequencyRoot n t.2.1 : ℤ) : ZMod q) ((frequencyRoot n t.2.2 : ℤ) : ZMod q)
        (treeLeafProduct n (compensationLeafProducts n (movingCompensationValues value n samples)) : ℕ)
        (x * (treeLeafProduct n (movingSlotValues value n small.1) : ℕ) *
          (treeLeafProduct n z.1 : (ZMod q)ˣ))
        (y * (treeLeafProduct n (movingSlotValues value n small.2) : ℕ) *
          (treeLeafProduct n z.2 : (ZMod q)ˣ)) := by
      simp only [p, L, R, MovingSlotReversal.modularPivot, MovingSlotData.step,
        buildMovingSlotData_frequency, movingNaturalProduct_append, movingSlotValues_flatten,
        reconstructedEntry, Nat.cast_mul]
      rw [hz.1.product, hz.2.product, ← movingCompensationValues_product]
      congr 1
      ring
    have hL := ihL t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 p x z.1 hz.1
    have hR := ihR t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 p y z.2 hz.2
    change (if p = 0 then 0 else
      movingModularSpectator value q g D L p x * star (movingModularSpectator value q g D R p y)) = _
    rw [hL, hR]
    simp only [buildMovingGiantTree, MovingSampleSlots.values, movingSlotValues,
      movingFieldGiantAmplitude, MovingGiantTree.castConstant_frequency,
      buildMovingGiantTree_frequency, MovingGiantTree.castConstant_fieldAmplitude]
    rw [← hp]
    dsimp only [u]
    rw [movingSlotValues_append, movingSlotValues_append, movingCompensationValues_product]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotFieldBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original labelled bulk slots produce the quartet leaf arrays -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem treeNaturalLift_iff_indexed {q : ℕ} (n : ℕ)
    (x : TreeLeafTuple ℕ n) (y : TreeLeafTuple (ZMod q)ˣ n) :
    TreeNaturalLift n x y ↔ ∀ j : TreeLeafIndex n,
      (treeLeafTupleEquiv ℕ n x j : ZMod q) = (treeLeafTupleEquiv (ZMod q)ˣ n y j : ZMod q) := by
  induction n with
  | zero =>
    constructor
    · intro h _; exact h
    · intro h; exact h ()
  | succ n ih =>
    constructor
    · rintro ⟨hL, hR⟩ (j | j)
      · exact (ih x.1 y.1).mp hL j
      · exact (ih x.2 y.2).mp hR j
    · intro h
      exact ⟨(ih x.1 y.1).mpr (fun j => h (.inl j)),
        (ih x.2 y.2).mpr (fun j => h (.inr j))⟩

theorem movingSlotValues_indexed {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (s : TreeLeafTuple (List σ) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv ℕ n (movingSlotValues value n s) j =
      MovingSlotReversal.naturalProduct value (treeLeafTupleEquiv (List σ) n s j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact ih s.1 j
    | inr j => exact ih s.2 j

theorem bulkSlotLeaves_naturalLift {σ : Type*} {q : ℕ} (value : σ → ℕ)
    (n m : ℕ) (slot : TreeLeafIndex n × Fin m → σ)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (hz : ∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) :
    TreeNaturalLift n (movingSlotValues value n (bulkSlotLeaves n m slot))
      ((treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct z)) := by
  rw [treeNaturalLift_iff_indexed]
  intro j
  rw [movingSlotValues_indexed]
  simp only [bulkSlotLeaves, Equiv.apply_symm_apply, MovingSlotReversal.naturalProduct,
    List.map_ofFn, List.prod_ofFn, Nat.cast_prod, bulkBlockProduct, Units.coe_prod]
  exact Finset.prod_congr rfl (fun i _ => hz (j, i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleSizes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete degree budgets for the sampled moving-giant paths -/

namespace Ostmann

theorem moving_flatten_length_le {σ : Type*} (n : ℕ) (x : TreeLeafTuple (List σ) n)
    (A : ℕ) (hx : MovingLeafLengthLE n x A) :
    (flattenMovingSlots n x).length ≤ 2 ^ n * A := by
  induction n with
  | zero => simpa only [MovingLeafLengthLE, flattenMovingSlots, pow_zero, one_mul] using hx
  | succ n ih =>
    simp only [flattenMovingSlots, List.length_append]
    have h := Nat.add_le_add (ih x.1 hx.1) (ih x.2 hx.2)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [pow_succ]
    ring

theorem moving_append_length_le {σ : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) (A B : ℕ)
    (hx : MovingLeafLengthLE n x A) (hy : MovingLeafLengthLE n y B) :
    MovingLeafLengthLE n (appendMovingSlotLeaves n x y) (A + B) := by
  induction n with
  | zero =>
    change ((show List σ from x) ++ (show List σ from y)).length ≤ A + B
    rw [List.length_append]
    exact Nat.add_le_add hx hy
  | succ n ih => exact ⟨ih x.1 y.1 hx.1 hy.1, ih x.2 y.2 hx.2 hy.2⟩

theorem moving_compensation_length {σ : Type*} (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → σ) n) :
    MovingLeafLengthLE n (movingCompensationSlots n samples) 4 := by
  induction n with
  | zero => simp [MovingLeafLengthLE, movingCompensationSlots]
  | succ n ih => exact ⟨ih samples.1, ih samples.2⟩

theorem MovingSlotData.SizeLE.mono {σ : Type*} {n D E : ℕ} {T : MovingSlotData σ n}
    (h : T.SizeLE D) (hDE : D ≤ E) : T.SizeLE E := by
  induction T with
  | leaf => trivial
  | node s CL CR u left right ihL ihR =>
    exact ⟨h.1.trans hDE, h.2.1.trans hDE, h.2.2.1.trans hDE, ihL h.2.2.2.1, ihR h.2.2.2.2⟩

/-- Compensation adds exactly four labels per bottom leaf per level. -/
theorem buildMovingSlotData_size {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (A B : ℕ) (hsmall : MovingLeafLengthLE n small A) (hbulk : MovingLeafLengthLE n bulk B) :
    (buildMovingSlotData n t small bulk samples).SizeLE (2 ^ n * (A + B + 4 * n + 4)) := by
  induction samples generalizing A B with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    have hp : 0 < 2 ^ n := by positivity
    have hleft := ihL t.2.1 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
      bulk.1 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.1) hbulk.1
    have hright := ihR t.2.2 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
      bulk.2 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.2) hbulk.2
    have hD : 2 ^ n * (4 + A + B + 4 * n + 4) ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    have hbase : 2 ^ n * A + 2 ^ n * B ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    have hcomp : 2 ^ n * 4 ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    refine ⟨?_, ?_, ?_, hleft.mono hD, hright.mono hD⟩
    · rw [List.length_append]
      exact (Nat.add_le_add (moving_flatten_length_le n _ A hsmall.1)
        (moving_flatten_length_le n _ B hbulk.1)).trans hbase
    · rw [List.length_append]
      exact (Nat.add_le_add (moving_flatten_length_le n _ A hsmall.2)
        (moving_flatten_length_le n _ B hbulk.2)).trans hbase
    · exact (moving_flatten_length_le n _ 4 (moving_compensation_length n samples)).trans hcomp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingUnitSampleBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual sampled regular lists in the full unit-period estimate -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.RegularLengthLE.mono {σ : Type*} {n D E : ℕ}
    {T : MovingSlotData σ n} (h : T.RegularLengthLE D) (hDE : D ≤ E) :
    T.RegularLengthLE E := by
  induction T with
  | leaf => exact h.trans hDE
  | node s CL CR U left right ihL ihR =>
    exact ⟨h.1.trans hDE, ihL h.2.1, ihR h.2.2⟩

theorem buildMovingSlotData_regular_length {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (A B : ℕ) (hsmall : MovingLeafLengthLE n small A) (hbulk : MovingLeafLengthLE n bulk B) :
    (buildMovingSlotData n t small bulk samples).RegularLengthLE (2 ^ n * (A + B + 4 * n)) := by
  induction samples generalizing A B with
  | leaf =>
    simpa only [buildMovingSlotData, MovingSlotData.RegularLengthLE, MovingSlotData.regularSlots,
      flattenMovingSlots, List.length_append, pow_zero, Nat.mul_zero, Nat.add_zero, one_mul] using
      Nat.add_le_add hsmall hbulk
  | @node n samples left right ihL ihR =>
    have hleft := ihL t.2.1 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
      bulk.1 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.1) hbulk.1
    have hright := ihR t.2.2 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
      bulk.2 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.2) hbulk.2
    have hD : 2 ^ n * (4 + A + B + 4 * n) ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1)) := by
      rw [show 4 + A + B + 4 * n = A + B + 4 * (n + 1) by omega]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨?_, hleft.mono hD, hright.mono hD⟩
    have hp := (buildMovingSlotData_regular_perm (n + 1) t small bulk (.node samples left right)).length_eq
    change (buildMovingSlotData (n + 1) t small bulk (.node samples left right)).regularSlots.length ≤ _
    rw [hp, List.length_append]
    have hs := moving_flatten_length_le (n + 1) small A hsmall
    have hb := moving_flatten_length_le (n + 1) bulk B hbulk
    exact (Nat.add_le_add hs hb).trans (by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal product of the two histories in a diagonal comparison -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem pairedPolynomialFactors_roots {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (S U : Finset ℝ)
    (hS : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (hU : ∀ i r, r ∈ (G i).polynomial.derivative.roots → r ∈ U) :
    ∀ i r, r ∈ ((pairedPolynomialFactors F G) i).polynomial.derivative.roots → r ∈ S ∪ U := by
  intro i r
  refine Fin.addCases ?_ ?_ i
  · intro j hr
    simp only [pairedPolynomialFactors, Fin.append_left] at hr
    exact Finset.mem_union_left _ (hS j r hr)
  · intro j hr
    simp only [pairedPolynomialFactors, Fin.append_right, ClippedPolynomialFactor.conjugate] at hr
    exact Finset.mem_union_right _ (hU j r hr)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GiantHaarDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Haar residue factors inside the real giant integral -/

namespace Ostmann
open scoped BigOperators Classical

theorem selectedPrimeLogDensity_page (P : PublishedProgressionInput) (Q q a : ℕ) (x : ℝ) :
    (selectedPrimeLogDensity P Q q a x : ℂ) =
      pageGiantWeight P Q q a x / ((Nat.totient q : ℂ) * (x : ℂ)) := by
  simp only [selectedPrimeLogDensity, primeLogDensity, pageGiantWeight, pageMultiplier,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_BulkHaarDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint harmonic density exposes the exact bulk Haar average -/

namespace Ostmann
open scoped Classical BigOperators

/-- Every prime density contributes one Haar-unit normalization and one
harmonic factor. Page multipliers remain inside the residue average. -/
theorem bulk_prime_density_haar {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q M : ℕ) [NeZero M]
    (y : J → ℝ) (C : (J → (ZMod M)ˣ) → ℂ) :
    (∑ z, C z * ∏ j, (selectedPrimeLogDensity P Q M (z j).val.val (y j) : ℂ)) =
      ((Fintype.card (J → (ZMod M)ˣ) : ℂ)⁻¹ *
        ∑ z, C z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)) *
          ∏ j, (y j : ℂ)⁻¹ := by
  have hc : (Fintype.card (J → (ZMod M)ˣ) : ℂ) =
      (Nat.totient M : ℂ) ^ Fintype.card J := by
    simp only [Fintype.card_fun, ZMod.card_units_eq_totient, Nat.cast_pow]
  simp_rw [selectedPrimeLogDensity_page]
  simp only [hc, div_eq_mul_inv, mul_inv_rev, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ← inv_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedAverageNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete norm budgets for the retained arithmetic averages -/

namespace Ostmann
open scoped Classical BigOperators

theorem pageGiantWeight_norm_le_two (input : PublishedProgressionInput) (Q q a : ℕ)
    (y : ℝ) (hy : 0 ≤ y) : ‖pageGiantWeight input Q q a y‖ ≤ 2 := by
  have h := pageMultiplier_bounds
    (fun a => pageCoefficient (pageAtModulus q (selectedPageZero input Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero input Q))) y
    (pageCoefficient_abs_le_one _) (pageBeta_le_one _) hy a
  rw [pageGiantWeight, Complex.norm_real, Real.norm_of_nonneg h.1]
  exact h.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealSlotEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real bulk coordinates in the original smooth moving tree -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realSlotProduct_nat {σ : Type*} (value : σ → ℕ) (slots : List σ) :
    realSlotProduct (fun j => (value j : ℝ)) slots =
      (MovingSlotReversal.naturalProduct value slots : ℝ) := by
  induction slots with
  | nil => simp [realSlotProduct, MovingSlotReversal.naturalProduct]
  | cons j slots ih => simpa only [realSlotProduct, MovingSlotReversal.naturalProduct,
      List.map_cons, List.prod_cons, Nat.cast_mul] using congrArg ((value j : ℝ) * ·) ih

theorem MovingSlotReversal.realValuePivot_nat {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (L R : ℝ) :
    s.realValuePivot (fun j => (value j : ℝ)) L R = s.realPivot value L R := by
  simp only [realValuePivot, realPivot, realSlotProduct_nat]

theorem MovingSlotData.realValueLeafModuli_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) (j : TreeLeafIndex n) :
    T.realValueLeafModuli (fun i => (value i : ℝ)) L R j = T.realLeafModuli value L R j := by
  induction T generalizing L R with
  | leaf => simp only [realValueLeafModuli, realLeafModuli, realSlotProduct_nat]
  | node s CL CR u left right ihL ihR =>
    cases j with
    | inl j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihL]
    | inr j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihR]

theorem realValueNodeCutoff_nat {σ : Type*} (value : σ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    realValueNodeCutoff (fun i => (value i : ℝ)) φ G T L R = movingRealNodeCutoff value φ G T L R := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [realValueNodeCutoff, movingRealNodeCutoff, MovingSlotReversal.realValuePivot_nat, ihL, ihR]

/-- The extension agrees exactly with the original function at every natural
prime tuple, including points where a cutoff vanishes. -/
theorem realValueSmoothWeight_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueSmoothWeight (fun i => (value i : ℝ)) T ψ X lo hi hlo hhi φ G L R =
      movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R := by
  simp only [realValueSmoothWeight, movingRealSmoothWeight, realValueFourierWeight,
    movingRealFourierWeight, realValueNodeCutoff_nat, MovingSlotData.realValueLeafModuli_nat]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial dependence on one original bulk-prime slot -/

namespace Ostmann
open scoped Classical

theorem bulkSlotProduct_degree {σ : Type*} (value : σ → ℝ)
    (i : σ) (slots : List σ) : (bulkSlotProduct value i slots).natDegree ≤ slots.length := by
  induction slots with
  | nil => simp [bulkSlotProduct]
  | cons j slots ih =>
    change ((if j = i then Polynomial.X else Polynomial.C (value j)) *
      bulkSlotProduct value i slots).natDegree ≤ slots.length + 1
    have hj : (if j = i then Polynomial.X else Polynomial.C (value j)).natDegree ≤ 1 := by
      split_ifs <;> simp
    exact Polynomial.natDegree_mul_le.trans (by omega)

theorem MovingSlotReversal.bulkPivotPolynomial_degree {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ)
    (L R : Polynomial ℝ) (d e : ℕ) (hs : s.lengthLE d)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    (s.bulkPivotPolynomial value i L R).natDegree ≤ d + e := by
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (by
        simpa only [Polynomial.natDegree_C, zero_add] using
          (bulkSlotProduct_degree value i s.rightSlots).trans hs.1)) hR)
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (by
        simpa only [Polynomial.natDegree_C, zero_add] using
          (bulkSlotProduct_degree value i s.leftSlots).trans hs.2.1)) hL)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLeafPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal moduli as polynomials in a bulk-prime coordinate -/

namespace Ostmann
open scoped Classical

/-- Degree grows with the fixed tree depth and the actual list lengths;
the size of a prime and every coefficient are irrelevant. -/
theorem MovingSlotData.bulkLeafPolynomials_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (d D e : ℕ)
    (hsize : T.SizeLE d) (hregular : T.RegularLengthLE D)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) (j : TreeLeafIndex n) :
    (T.bulkLeafPolynomials value i L R j).natDegree ≤ 2 * (n * d + e) + D := by
  induction T generalizing L R e with
  | leaf s regular =>
    change (L * R * bulkSlotProduct value i regular).natDegree ≤ _
    apply Polynomial.natDegree_mul_le.trans
    have hr := bulkSlotProduct_degree value i regular
    have hLR := Polynomial.natDegree_mul_le (p := L) (q := R)
    change regular.length ≤ D at hregular
    omega
  | @node n s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_degree
      value i L R d e ⟨hsize.2.1, hsize.1, hsize.2.2.1⟩ hL hR
    have hLe : L.natDegree ≤ d + e := hL.trans (Nat.le_add_left _ _)
    have hRe : R.natDegree ≤ d + e := hR.trans (Nat.le_add_left _ _)
    have hn : n * d + (d + e) = (n + 1) * d + e := by ring
    cases j with
    | inl j =>
      simpa only [bulkLeafPolynomials, hn] using
        ihL _ _ (d + e) hsize.2.2.2.1 hregular.2.1 hp hLe j
    | inr j =>
      simpa only [bulkLeafPolynomials, hn] using
        ihR _ _ (d + e) hsize.2.2.2.2 hregular.2.2 hp hRe j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFourierFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clipped Fourier factors along an original bulk-prime coordinate -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem bulkFourierFactors_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (d D e : ℕ)
    (hsize : T.SizeLE d) (hregular : T.RegularLengthLE D)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) (j : Fin (2 ^ n)) :
    (bulkFourierFactors value i T L R ψ X lo hi hlo hhi j).polynomial.natDegree ≤
      2 * (n * d + e) + D := by
  have hp := T.bulkLeafPolynomials_degree value i L R d D e hsize hregular hL hR
    ((movingLeafIndexEquiv n).symm j)
  have hn : (Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R
      ((movingLeafIndexEquiv n).symm j)).natDegree ≤ 2 * (n * d + e) + D := by
    exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using hp)
  dsimp only [bulkFourierFactors]
  split_ifs <;> exact hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkNodePolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every node cutoff in the same bulk-prime polynomial coordinate -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.bulkNodePolynomials_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (d e : ℕ)
    (hsize : T.SizeLE d) (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∀ f ∈ T.bulkNodePolynomials value i L R, f.2.natDegree ≤ n * d + e := by
  induction T generalizing L R e with
  | leaf => simp [bulkNodePolynomials]
  | @node n s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_degree
      value i L R d e ⟨hsize.2.1, hsize.1, hsize.2.2.1⟩ hL hR
    have hLe : L.natDegree ≤ d + e := hL.trans (Nat.le_add_left _ _)
    have hRe : R.natDegree ≤ d + e := hR.trans (Nat.le_add_left _ _)
    intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · subst f
      exact hp.trans (by rw [Nat.succ_mul]; omega)
    · have hn : n * d + (d + e) = (n + 1) * d + e := by ring
      rcases List.mem_append.mp hf with hf | hf
      · simpa only [hn] using ihL _ _ (d + e) hsize.2.2.2.1 hp hLe f hf
      · simpa only [hn] using ihR _ _ (d + e) hsize.2.2.2.2 hp hRe f hf

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkNodeFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original node cutoffs with one free bulk coordinate -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulkNodeFactors_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (d e : ℕ) (hsize : T.SizeLE d) (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e)
    (j : Fin (T.bulkNodePolynomials value i L R).length) :
    (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip j).polynomial.natDegree ≤ n * d + e :=
  T.bulkNodePolynomials_degree value i L R d e hsize hL hR _ (List.getElem_mem j.isLt)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLogContinuity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth tree as a continuous function of the bulk logarithms -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate BoundedContinuousFunction

theorem bulkLogValues_update {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (x : σ → ℝ) (i : σ) (hi : i ∈ S) (t : ℝ) :
    bulkLogValues base S (Function.update x i t) =
      Function.update (bulkLogValues base S x) i (Real.exp t) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [bulkLogValues, hi, ite_true, if_true, Function.update_self]
  · simp only [bulkLogValues, Function.update_of_ne hj]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSmoothRootCuts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete finite root bound for the bulk-coordinate smooth factor -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- All cuts are constructed derivative roots of actual bulk polynomials.
Their number depends on degree, never on coefficient height or prime values. -/
theorem bulkSmoothFactors_root_cuts {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (d r e : ℕ) (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∃ S : Finset ℝ,
      S.card ≤ (2 ^ n + (T.bulkNodePolynomials value i L R).length) * (2 * (n * d + e) + r) ∧
      ∀ j z, z ∈ (bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip j).polynomial.derivative.roots → z ∈ S := by
  let F := bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  let H := 2 * (n * d + e) + r
  let S := polynomialRootCuts (fun j => (F j).polynomial.derivative)
  have hd (j) : (F j).polynomial.natDegree ≤ H := by
    refine Fin.addCases ?_ ?_ j
    · intro j
      simp only [F, bulkSmoothFactors, Fin.append_left]
      exact bulkFourierFactors_degree value i T L R ψ X lo hi hlo hhi d r e hsize hregular hL hR j
    · intro j
      simp only [F, bulkSmoothFactors, Fin.append_right]
      have h := bulkNodeFactors_degree value i T L R φ G B D hB hD hφ hlip d e hsize hL hR j
      exact h.trans (by dsimp only [H]; omega)
  have hdr (j) : (F j).polynomial.derivative.natDegree ≤ H :=
    (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (hd j))
  refine ⟨S, ?_, ?_⟩
  · apply (polynomialRootCuts_card _).trans
    calc
      _ ≤ ∑ _j, H := Finset.sum_le_sum (fun j _ => hdr j)
      _ = _ := by simp [H]
  · intro j z hz
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hz⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellMeasure
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact atomic measure of a harmonic prime cell -/

namespace Ostmann
open MeasureTheory Filter
open scoped BigOperators ENNReal BoundedContinuousFunction

theorem primeLogCellMeasure_integral (q a : ℕ) (u v : ℝ) (f : ℝ →ᵇ ℂ) :
    (∫ t, f t ∂primeLogCellMeasure q a u v) =
      ∑ p ∈ primeLogCellSet q a u v, f (Real.log p) * ((p : ℝ)⁻¹ : ℂ) := by
  unfold primeLogCellMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul, mul_comm]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  · intro p _
    exact f.integrable _

theorem primeLogCellMeasure_mass (q a : ℕ) (u v : ℝ) :
    (primeLogCellMeasure q a u v).real Set.univ =
      ∑ p ∈ primeLogCellSet q a u v, (p : ℝ)⁻¹ := by
  have h := primeLogCellMeasure_integral q a u v (BoundedContinuousFunction.const ℝ (1 : ℂ))
  simp only [BoundedContinuousFunction.const_apply, integral_const, Complex.real_smul,
    mul_one, one_mul] at h
  exact_mod_cast h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkPrimeIntegrands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem BulkIntegrand.average_prime {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (q a : ℕ) (u v : ℝ) (i : σ) (x : σ → ℝ) :
    f.average (primeLogCellMeasure q a u v) i x =
      ∑ p ∈ primeLogCellSet q a u v,
        f (Function.update x i (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) := by
  change (∫ t, f (Function.update x i t) ∂primeLogCellMeasure q a u v) = _
  unfold primeLogCellMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul, mul_comm]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  · intro p _
    exact f.slice_integrable _ i x

theorem BulkIntegrand.average_prime_eq_interval {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (q a : ℕ) (u v : ℝ) (i : σ) (x : σ → ℝ) (H : ℝ → ℂ)
    (hH : ∀ y, f (Function.update x i y) = H y) :
    f.average (primeLogCellMeasure q a u v) i x = complexPrimeInterval q a u v H := by
  rw [f.average_prime]
  unfold primeLogCellSet complexPrimeInterval
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime ∧ Nat.ModEq q p a
  · rw [ite_eq_left hp, ite_eq_left hp, hH]
  · rw [ite_eq_right hp, ite_eq_right hp]

theorem BulkIntegrand.average_page {σ : Type*} [Fintype σ] (f : BulkIntegrand σ)
    (P : PublishedProgressionInput) (Q q a : ℕ) (u v : ℝ) (hu : 0 < u)
    (i : σ) (x : σ → ℝ) :
    letI := finite_primeGiantMeasure P Q q a u v hu
    f.average (primeGiantMeasure P Q q a u v) i x =
      ∫ y in Set.Ioc u v, f (Function.update x i y) * (selectedPrimeLogDensity P Q q a y : ℂ) := by
  exact primeGiantMeasure_integral P Q q a u v hu.le _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkAbsoluteIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the nonnegative arithmetic norm under the original Page density -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- The absolute residue average is integrated with the true harmonic box
volume. The Page factors remain inside the arithmetic norm estimate. -/
theorem bulk_absolute_integral_bound {J : Type*} [Fintype J]
    (P : PublishedProgressionInput) (Q M : ℕ) [NeZero M]
    (u v : J → ℝ) (hu : ∀ j, 0 < u j)
    (K : BulkIntegrand J) (a : (J → (ZMod M)ˣ) → ℂ) (W A : ℝ)
    (hW : 0 ≤ W) (hK : ∀ y, ‖K y‖ ≤ W)
    (hA : ∀ y : J → ℝ, (∀ j, y j ∈ Set.Ioc (u j) (v j)) →
      (Fintype.card (J → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ z, ‖a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A) :
    ‖∑ z : J → (ZMod M)ˣ, ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun j =>
      primeGiantMeasure P Q M (z j).val.val (u j) (v j))‖ ≤
      (W * A) * ∏ j, ∫ x in Set.Ioc (u j) (v j), (x : ℝ)⁻¹ := by
  let μ : J → Measure ℝ := fun j => volume.restrict (Set.Ioc (u j) (v j))
  have hi (j : J) : Integrable (fun x : ℝ => x⁻¹) (μ j) := by
    have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (u j) (v j)) :=
      continuousOn_inv₀.mono (fun x hx => ne_of_gt (lt_of_lt_of_le (hu j) hx.1))
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hp : Integrable (fun y : J → ℝ => ∏ j, (y j)⁻¹) (Measure.pi μ) :=
    Integrable.fintype_prod hi
  rw [bulk_page_residue_integral P Q (fun _ => M) (fun z j => (z j).val.val) u v hu (fun z => K.constMul (a z))]
  have hb : ∀ᵐ y ∂Measure.pi μ,
      ‖∑ z, (K.constMul (a z)) y *
        ∏ j, (selectedPrimeLogDensity P Q M (z j).val.val (y j) : ℂ)‖ ≤
      (W * A) * ∏ j, (y j)⁻¹ := by
    have hm : ∀ᵐ y ∂Measure.pi μ, ∀ j, y j ∈ Set.Ioc (u j) (v j) :=
      Filter.eventually_all.mpr (fun j =>
        (Measure.tendsto_eval_ae_ae (μ := μ) (i := j)).eventually (ae_restrict_mem measurableSet_Ioc))
    filter_upwards [hm] with y hy
    have hny (j : J) : 0 < y j := (hu j).trans (hy j).1
    have he : (∑ z, (K.constMul (a z)) y *
        ∏ j, (selectedPrimeLogDensity P Q M (z j).val.val (y j) : ℂ)) =
        K y * ∑ z, a z * ∏ j, (selectedPrimeLogDensity P Q M (z j).val.val (y j) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      change (a z * K y) * _ = _
      ring
    rw [he, bulk_prime_density_haar P Q M y a, norm_mul, norm_mul]
    have hmean : ‖(Fintype.card (J → (ZMod M)ˣ) : ℂ)⁻¹ *
        ∑ z, a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans (hA y hy)
    have hprod : ‖∏ j, (y j : ℂ)⁻¹‖ = ∏ j, (y j)⁻¹ := by
      rw [norm_prod]
      apply Finset.prod_congr rfl
      intro j _
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hny j).le]
    rw [hprod, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hK y) hmean (norm_nonneg _) hW)
      (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (hny j).le)
  have hn := norm_integral_le_of_norm_le (hp.const_mul (W * A)) hb
  simpa only [integral_const_mul, integral_fintype_prod_eq_prod] using hn

/-- Sum all original boxes with their unchanged reciprocal-prime normalizers. -/
theorem bulk_absolute_mixture_bound {J C : Type*} [Fintype J] [Fintype C]
    (P : PublishedProgressionInput) (Q M : ℕ) [NeZero M]
    (u v : J → C → ℝ) (hu : ∀ j c, 0 < u j c)
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (hmass : ∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2)
    (K : BulkIntegrand J) (a : (J → (ZMod M)ˣ) → ℂ) (W A : ℝ)
    (hW : 0 ≤ W) (hA0 : 0 ≤ A) (hK : ∀ y, ‖K y‖ ≤ W)
    (hA : ∀ y : J → ℝ, (∀ j, 0 ≤ y j) →
      (Fintype.card (J → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ z, ‖a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A) :
    ‖∑ z : J → (ZMod M)ˣ, ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun j =>
      bulkCellMixture (Z j) (fun c => primeGiantMeasure P Q M (z j).val.val (u j c) (v j c)))‖ ≤
      (W * A) * 2 ^ Fintype.card J := by
  let μ := fun (z : J → (ZMod M)ˣ) j c =>
    primeGiantMeasure P Q M (z j).val.val (u j c) (v j c)
  let _ : ∀ z j c, IsFiniteMeasure (μ z j c) := fun z j c =>
    finite_primeGiantMeasure P Q _ _ _ _ (hu j c)
  change ‖∑ z, ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun j => bulkCellMixture (Z j) (μ z j))‖ ≤ _
  rw [bulk_residue_mixture_integral Z hZ μ (fun z => K.constMul (a z))]
  let H := fun j c => ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹
  have hH (j : J) (c : C) : 0 ≤ H j c := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact inv_nonneg.mpr ((hu j c).trans hx.1).le
  apply bulk_box_sum_bound Z hZ H hH hmass (W * A) (mul_nonneg hW hA0)
  intro c
  exact bulk_absolute_integral_bound P Q M (fun j => u j (c j)) (fun j => v j (c j))
    (fun j => hu j (c j)) K a W A hW hK (fun y hy => hA y (fun j => ((hu j (c j)).trans (hy j).1).le))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkAtomicProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite atomic product integrals for the original prime cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem bulk_pi_scaled_dirac {J : Type*} [Fintype J]
    (x : J → ℝ) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Measure.pi (fun j => ENNReal.ofReal (w j) • Measure.dirac (x j)) =
      ENNReal.ofReal (∏ j, w j) • Measure.dirac x := by
  let _ : ∀ j, IsFiniteMeasure (ENNReal.ofReal (w j) • Measure.dirac (x j)) :=
    fun j => (Measure.dirac (x j)).smul_finite ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
    Measure.dirac_apply' _ (hs _), smul_eq_mul]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hw j), Finset.prod_mul_distrib]
  by_cases h : ∀ j, x j ∈ s j
  · simp [h]
  · have hex : ∃ j, x j ∉ s j := not_forall.mp h
    obtain ⟨j, hj⟩ := hex
    have hz : (∏ i, (s i).indicator (fun _ => (1 : ENNReal)) (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)
    change (∏ i, ENNReal.ofReal (w i)) *
        (Set.univ.pi s).indicator (fun _ => (1 : ENNReal)) x =
      (∏ i, ENNReal.ofReal (w i)) * ∏ i, (s i).indicator (fun _ => (1 : ENNReal)) (x i)
    rw [hz, Set.indicator_of_notMem (by simpa only [Set.mem_univ_pi] using h)]

theorem BulkIntegrand.integral_atomic_product {J A : Type*} [Fintype J] [Fintype A]
    (f : BulkIntegrand J) (x : J → A → ℝ) (w : J → A → ℝ)
    (hw : ∀ j a, 0 ≤ w j a) :
    (∫ y, f y ∂Measure.pi (fun j => ∑ a, ENNReal.ofReal (w j a) • Measure.dirac (x j a))) =
      ∑ a : J → A, ((∏ j, w j (a j) : ℝ) : ℂ) * f (fun j => x j (a j)) := by
  let _ : ∀ j a, IsFiniteMeasure (ENNReal.ofReal (w j a) • Measure.dirac (x j a)) :=
    fun j a => (Measure.dirac (x j a)).smul_finite ENNReal.ofReal_ne_top
  have he := f.integral_product_mixtures (fun _ => 1) (fun _ => zero_le_one)
    (fun j a => ENNReal.ofReal (w j a) • Measure.dirac (x j a))
  simp only [bulkCellMixture, ENNReal.ofReal_one, one_smul, Finset.prod_const_one,
    Complex.ofReal_one, one_mul] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  rw [bulk_pi_scaled_dirac (fun j => x j (a j)) (fun j => w j (a j)) (fun j => hw j (a j)),
    integral_smul_measure, ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => hw j (a j)),
    integral_dirac, Complex.real_smul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkRegularSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keep nonbulk coprimalities when bulk collisions are removed -/

namespace Ostmann
open scoped Classical

theorem pairwise_split_bulk {α : Type*} (R : α → α → Prop)
    (bulk : α → Bool) (L : List α)
    (hcross : ∀ a ∈ L, ∀ b ∈ L, bulk a ≠ bulk b → R a b) :
    L.Pairwise R ↔ (L.filter bulk).Pairwise R ∧ (L.filter fun a => !(bulk a)).Pairwise R := by
  constructor
  · intro h
    exact ⟨h.filter bulk, h.filter (fun a => !(bulk a))⟩
  · induction L with
    | nil => simp
    | cons a L ih =>
      rintro ⟨hb, hs⟩
      have htail := ih (fun b hb c hc => hcross b (List.mem_cons_of_mem a hb)
        c (List.mem_cons_of_mem a hc))
      cases ha : bulk a with
      | false =>
        simp only [List.filter_cons, ha, Bool.not_false, Bool.false_eq_true, ite_false, if_false,
          ite_true, if_true, List.pairwise_cons] at hb hs
        refine List.pairwise_cons.mpr ⟨?_, htail ⟨hb, hs.2⟩⟩
        intro b hbL
        cases hbB : bulk b with
        | false => exact hs.1 b (List.mem_filter.mpr ⟨hbL, by simp [hbB]⟩)
        | true => exact hcross a List.mem_cons_self b (List.mem_cons_of_mem a hbL) (by simp [ha, hbB])
      | true =>
        simp only [List.filter_cons, ha, Bool.not_true, Bool.false_eq_true, ite_false, if_false,
          ite_true, if_true, List.pairwise_cons] at hb hs
        refine List.pairwise_cons.mpr ⟨?_, htail ⟨hb.2, hs⟩⟩
        intro b hbL
        cases hbB : bulk b with
        | false => exact hcross a List.mem_cons_self b (List.mem_cons_of_mem a hbL) (by simp [ha, hbB])
        | true => exact hb.1 b (List.mem_filter.mpr ⟨hbL, hbB⟩)

/-- Under the original distinct-bulk event, all bulk coprimality tests are
automatic. The nonbulk tests are retained exactly. -/
theorem prime_list_pairwise_iff_nonbulk {σ : Type*} (value : σ → ℕ)
    (bulk : σ → Bool) (L : List σ)
    (hprime : ∀ i ∈ L, (value i).Prime)
    (hnodup : (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ i ∈ L, ∀ j ∈ L, bulk i ≠ bulk j → value i ≠ value j) :
    (L.map value).Pairwise Nat.Coprime ↔
      ((L.filter fun i => !(bulk i)).map value).Pairwise Nat.Coprime := by
  rw [List.pairwise_map, List.pairwise_map]
  have hb : (L.filter bulk).Pairwise (fun i j => (value i).Coprime (value j)) := by
    apply hnodup.imp_of_mem
    intro i j hi hj hij
    obtain ⟨hiL, hiB⟩ := List.mem_filter.mp hi
    obtain ⟨hjL, hjB⟩ := List.mem_filter.mp hj
    exact (Nat.coprime_primes (hprime i hiL) (hprime j hjL)).mpr
      (fun h => hij (hinj i j hiB hjB h))
  rw [pairwise_split_bulk _ bulk L (fun i hi j hj h =>
    (Nat.coprime_primes (hprime i hi) (hprime j hj)).mpr (hcross i hi j hj h))]
  exact and_iff_right hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenRegularSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained nonbulk coprimality support for the complete sampled tree -/

namespace Ostmann
open scoped Classical

theorem prime_list_outside_pairwise_iff_nonbulk {σ : Type*} (value : σ → ℕ)
    (bulk : σ → Bool) (L : List σ) (outside : List ℕ)
    (hprime : ∀ i ∈ L, (value i).Prime) (hnodup : (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ i ∈ L, ∀ j ∈ L, bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ i ∈ L, bulk i = true → ∀ p ∈ outside, (value i).Coprime p) :
    (L.map value ++ outside).Pairwise Nat.Coprime ↔
      ((L.filter fun i => !(bulk i)).map value ++ outside).Pairwise Nat.Coprime := by
  rw [List.pairwise_append, List.pairwise_append,
    prime_list_pairwise_iff_nonbulk value bulk L hprime hnodup hinj hcross]
  constructor
  · rintro ⟨hl, ho, hc⟩
    refine ⟨hl, ho, ?_⟩
    intro v hv p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hc _ (List.mem_map.mpr ⟨i, (List.mem_filter.mp hi).1, rfl⟩) p hp
  · rintro ⟨hl, ho, hc⟩
    refine ⟨hl, ho, ?_⟩
    intro v hv p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    cases hb : bulk i with
    | true => exact hout i hi hb p hp
    | false => exact hc _ (List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hb]⟩, rfl⟩) p hp

theorem movingRegularOutsidePairwise_iff_lists {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) :
    movingRegularOutsidePairwise value outside T ↔
      ∀ L ∈ T.regularLists, (L.map value ++ outside).Pairwise Nat.Coprime := by
  induction T with
  | leaf => simp [movingRegularOutsidePairwise, MovingSlotData.regularLists, MovingSlotData.regularSlots]
  | node s CL CR U left right ihL ihR =>
    simp only [movingRegularOutsidePairwise, MovingSlotData.regularSlots,
      MovingSlotData.regularLists, List.mem_cons, List.mem_append, or_imp, forall_and,
      forall_eq, ihL, ihR]

theorem movingRegularOutsidePairwise_iff_nonbulk {σ : Type*} (value : σ → ℕ)
    (bulk : σ → Bool) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hprime : ∀ L ∈ T.regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ L ∈ T.regularLists, (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ L ∈ T.regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ L ∈ T.regularLists, ∀ i ∈ L, bulk i = true →
      ∀ p ∈ outside, (value i).Coprime p) :
    movingRegularOutsidePairwise value outside T ↔ movingNonbulkOutsidePairwise value bulk outside T := by
  rw [movingRegularOutsidePairwise_iff_lists]
  exact forall_congr' fun L => forall_congr' fun hL =>
    prime_list_outside_pairwise_iff_nonbulk value bulk L outside (hprime L hL)
      (hnodup L hL) hinj (hcross L hL) (hout L hL)

theorem movingNonbulkOutsidePairwise_congr {σ : Type*} (v w : σ → ℕ)
    (bulk : σ → Bool) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hv : ∀ i, bulk i = false → v i = w i) :
    movingNonbulkOutsidePairwise v bulk outside T ↔ movingNonbulkOutsidePairwise w bulk outside T := by
  have he (L : List σ) : (L.filter fun i => !(bulk i)).map v =
      (L.filter fun i => !(bulk i)).map w := by
    apply List.map_congr_left
    intro i hi
    apply hv
    simpa using (List.mem_filter.mp hi).2
  unfold movingNonbulkOutsidePairwise
  simp_rw [he]

theorem movingRegularOutsidePairwise_frozen {σ : Type*} (value base : σ → ℕ)
    (bulk : σ → Bool) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hv : ∀ i, bulk i = false → value i = base i)
    (hprime : ∀ L ∈ T.regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ L ∈ T.regularLists, (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ L ∈ T.regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ L ∈ T.regularLists, ∀ i ∈ L, bulk i = true →
      ∀ p ∈ outside, (value i).Coprime p) :
    movingRegularOutsidePairwise value outside T ↔ movingNonbulkOutsidePairwise base bulk outside T :=
  (movingRegularOutsidePairwise_iff_nonbulk value bulk outside T hprime hnodup hinj hcross hout).trans
    (movingNonbulkOutsidePairwise_congr value base bulk outside T hv)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkNodup
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bulk labels remain distinct throughout the actual coherent sampled tree -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.regularLists_bulk_nodup {σ : Type*} (bulk : σ → Bool)
    {n : ℕ} (T : MovingSlotData σ n) :
    T.RegularCoherent →
    (∀ i, bulk i = true → T.CompensationAbsent i) →
    (T.regularSlots.filter bulk).Nodup →
    ∀ L ∈ T.regularLists, (L.filter bulk).Nodup := by
  induction T with
  | leaf s regular =>
    intro _ _ hn L hL
    simpa only [MovingSlotData.regularLists, MovingSlotData.regularSlots,
      List.mem_singleton.mp hL] using hn
  | node s CL CR U left right ihL ihR =>
    intro hc ha hn
    have hu : U.filter bulk = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro i hi
      cases hb : bulk i with
      | false => simp
      | true => exact False.elim ((ha i hb).1 hi)
    have hn' : (CL.filter bulk ++ CR.filter bulk).Nodup := by
      simpa only [MovingSlotData.regularSlots, List.filter_append] using hn
    have hleft : (left.regularSlots.filter bulk).Nodup := by
      have hp := hc.1.filter bulk
      rw [List.filter_append, hu, List.nil_append] at hp
      exact hp.nodup_iff.mpr (List.nodup_append.mp hn').1
    have hright : (right.regularSlots.filter bulk).Nodup := by
      have hp := hc.2.1.filter bulk
      rw [List.filter_append, hu, List.nil_append] at hp
      exact hp.nodup_iff.mpr (List.nodup_append.mp hn').2.1
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hn
    · rcases List.mem_append.mp hL with hL | hL
      · exact ihL hc.2.2.1 (fun i hi => (ha i hi).2.1) hleft L hL
      · exact ihR hc.2.2.2 (fun i hi => (ha i hi).2.2) hright L hL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotNodup
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distinct selected bulk labels in the concrete leaf constructor -/

namespace Ostmann
open scoped Classical

theorem buildMovingSlotData_root_bulk_nodup {σ : Type*} (n m : ℕ)
    (bulk : σ → Bool) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (hbulk : ∀ j, bulk (slot j) = true)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, bulk i = false) :
    ((buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples).regularSlots.filter bulk).Nodup := by
  have hs : (flattenMovingSlots n small).filter bulk = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    simp [hsmall i hi]
  have hb : (flattenMovingSlots n (bulkSlotLeaves n m slot)).filter bulk =
      flattenMovingSlots n (bulkSlotLeaves n m slot) := by
    apply List.filter_eq_self.mpr
    intro i hi
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m slot i).mp hi
    exact hbulk j
  have hp := (buildMovingSlotData_regular_perm n t small (bulkSlotLeaves n m slot) samples).filter bulk
  rw [List.filter_append, hs, List.nil_append, hb] at hp
  exact hp.nodup_iff.mpr (bulkSlotLeaves_nodup n m slot slot.injective)

theorem buildMovingSlotData_bulk_nodup {σ : Type*} (n m : ℕ)
    (bulk : σ → Bool) (tier : σ → ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (hbulk : ∀ j, bulk (slot j) = true) (htier : ∀ i, bulk i = true → n ≤ tier i)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, bulk i = false)
    (hsmallTier : ∀ i ∈ flattenMovingSlots n small, n ≤ tier i)
    (hsamples : samples.Levels tier) :
    ∀ L ∈ (buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples).regularLists,
      (L.filter bulk).Nodup := by
  have hlevels := buildMovingSlotData_levels tier n t small (bulkSlotLeaves n m slot) samples
    hsmallTier (fun i hi => by
      obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m slot i).mp hi
      exact htier _ (hbulk j)) hsamples
  apply MovingSlotData.regularLists_bulk_nodup bulk _
    (buildMovingSlotData_regular_coherent n t small (bulkSlotLeaves n m slot) samples)
  · intro i hi
    exact MovingSlotData.compensationAbsent_of_levels tier _ hlevels i (htier i hi)
  · exact buildMovingSlotData_root_bulk_nodup n m bulk slot hbulk t small samples hsmall

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFrequencyResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency support depends only on bulk residue classes -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.compensationAgreement_of_eq_off {σ : Type*}
    (v w : σ → ℕ) (S : Set σ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i) (hvalue : ∀ i ∉ S, v i = w i) :
    T.CompensationAgreement v w := by
  induction T with
  | leaf => trivial
  | node s CL CR u left right ihL ihR =>
    refine ⟨?_, ihL (fun i hi => (hT i hi).2.1), ihR (fun i hi => (hT i hi).2.2)⟩
    unfold MovingSlotReversal.naturalProduct
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hvalue i (fun hS => (hT i hS).1 hi)

theorem naturalProduct_modEq_values {σ : Type*} (v w : σ → ℕ) (M : ℤ)
    (h : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD M]) (s : List σ) :
    (MovingSlotReversal.naturalProduct v s : ℤ) ≡
      (MovingSlotReversal.naturalProduct w s : ℤ) [ZMOD M] := by
  induction s with
  | nil => exact Int.ModEq.refl _
  | cons i s ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons,
      Nat.cast_mul] using (h i).mul ih

theorem MovingSlotReversal.signedNumerator_values_modEq {σ : Type*}
    (s : MovingSlotReversal σ) (v w : σ → ℕ) (M XL XR YL YR : ℤ)
    (hv : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD M])
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    s.signedNumerator v XL XR ≡ s.signedNumerator w YL YR [ZMOD M] := by
  exact ((hR.mul (naturalProduct_modEq_values v w M hv s.rightSlots)).mul_left _).sub
    ((hL.mul (naturalProduct_modEq_values v w M hv s.leftSlots)).mul_left _)

theorem MovingSlotReversal.frequencyPivot_values_modEq {σ : Type*}
    (s : MovingSlotReversal σ) (v w : σ → ℕ) (R : ℤ) (k : ℕ)
    (hs : s.rootFrequency ≠ 0) (hsR : s.rootFrequency ∣ R)
    (hc : MovingSlotReversal.naturalProduct v s.compensationSlots =
      MovingSlotReversal.naturalProduct w s.compensationSlots)
    (XL XR YL YR : ℤ)
    (hv : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD R ^ (k + 1)])
    (hL : XL ≡ YL [ZMOD R ^ (k + 1)]) (hR : XR ≡ YR [ZMOD R ^ (k + 1)]) :
    s.frequencyPivot v R k XL XR ≡ s.frequencyPivot w R k YL YR [ZMOD R ^ k] := by
  have hd : s.rootFrequency * R ^ k ∣ R ^ (k + 1) := by
    simpa only [pow_succ, mul_comm] using mul_dvd_mul hsR (dvd_refl (R ^ k))
  have hn := s.signedNumerator_values_modEq v w _ XL XR YL YR hv hL hR
  unfold frequencyPivot
  rw [hc]
  exact (int_modEq_ediv _ _ _ _ hs (hn.of_dvd hd)).mul_right _

/-- All frequency divisibility and unit tests survive simultaneous bulk
replacement. Only one frequency power is consumed at each tree level. -/
theorem movingFrequencyGate_values_modEq {σ : Type*} (v w : σ → ℕ) (R : ℤ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hcomp : T.CompensationAgreement v w) (hR : T.frequencyProduct ∣ R)
    (hv : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD R ^ (n + 1)])
    (XL XR YL YR : ℤ) (hL : XL ≡ YL [ZMOD R ^ (n + 1)])
    (hRight : XR ≡ YR [ZMOD R ^ (n + 1)]) :
    movingFrequencyGate v R T XL XR ↔ movingFrequencyGate w R T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular =>
    exact movingFrequencyLocalUnits_modEq _ _ _ _ _ _ (by simpa using hR) hL hRight
  | @node n s CL CR u left right ihL ihR =>
    have hd := MovingSlotData.frequencyProduct_node_dvd s CL CR u left right R hR
    let step := MovingSlotData.step s CL CR u left right false
    have hp := step.frequencyPivot_values_modEq v w R (n + 1) hf.1 hd.1 hcomp.1
      XL XR YL YR hv hL hRight
    have hpow : R ∣ R ^ (n + 1 + 1) := dvd_pow_self R (by omega)
    have hn := step.signedNumerator_values_modEq v w _ XL XR YL YR hv hL hRight
    have hdiv := (hn.of_dvd (hd.1.trans hpow)).dvd_iff
    have hlocal := movingFrequencyLocalUnits_modEq
      (MovingSlotData.node s CL CR u left right) XL XR YL YR _ (hR.trans hpow) hL hRight
    have hdown : R ^ (n + 1) ∣ R ^ (n + 1 + 1) := pow_dvd_pow R (by omega)
    change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
    exact and_congr hlocal (and_congr hdiv (and_congr
      (ihL hf.2.1 hcomp.2.1 hd.2.1 (fun i => (hv i).of_dvd hdown)
        _ _ _ _ hp (hL.of_dvd hdown))
      (ihR hf.2.2 hcomp.2.2 hd.2.2 (fun i => (hv i).of_dvd hdown)
        _ _ _ _ hp (hRight.of_dvd hdown))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFrequencyFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separate the nonperiodic prime coincidences from frequency support -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The only nonperiodic part of this factor consists of the explicit
regular-prime coincidence tests. The remaining node bounds are independent
of the numerical bulk values. -/
theorem movingFrequencyPairFactor_core {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R x y : ℤ) :
    movingFrequencyPairFactor value outside F E T nodes R x y =
      (if ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCore value F E T R x y := by
  have he : movingFrequencyPairSupport value outside T nodes R x y ↔
      (∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds)) ∧
      (∀ b, movingFrequencyGate value R (T b) x y) := by
    simp only [movingFrequencyPairSupport, Bool.forall_bool]
    tauto
  unfold movingFrequencyPairFactor movingFrequencyCore
  rw [he]
  by_cases hs : ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds)
  · by_cases hc : ∀ b, movingFrequencyGate value R (T b) x y
    · rw [ite_eq_left ⟨hs, hc⟩, ite_eq_left hs, ite_eq_left hc, one_mul]
    · rw [ite_eq_right (fun h => hc h.2), ite_eq_left hs, ite_eq_right hc, mul_zero]
  · rw [ite_eq_right (fun h => hs h.1), ite_eq_right hs, zero_mul]

/-- Unlike the removed coincidence tests, the actual frequency core is
constant on the joint bulk residue cells. -/
theorem movingFrequencyCore_values_modEq {σ : Type*} (v w : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hcomp : ∀ b, (T b).CompensationAgreement v w)
    (hR : ∀ b, (T b).frequencyProduct ∣ R)
    (hv : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD R ^ (n + 1)])
    (XL XR YL YR : ℤ) (hL : XL ≡ YL [ZMOD R ^ (n + 1)])
    (hRight : XR ≡ YR [ZMOD R ^ (n + 1)]) :
    movingFrequencyCore v F E T R XL XR = movingFrequencyCore w F E T R YL YR := by
  have he : (∀ b, movingFrequencyGate v R (T b) XL XR) ↔
      (∀ b, movingFrequencyGate w R (T b) YL YR) :=
    forall_congr' fun b => movingFrequencyGate_values_modEq v w R (T b)
      (hf b) (hcomp b) (hR b) hv XL XR YL YR hL hRight
  simp only [movingFrequencyCore, he]

theorem MovingSlotData.formulaNodes_frequencyBounds {σ : Type*} (value : σ → ℕ)
    (hv : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : HistoryFormula Bool) :
    (∀ f ∈ T.formulaNodes value hv childBound pivotBound hf L R,
      f.guard.frequencyBounds) ↔ T.FrequencyBounds childBound := by
  induction T generalizing L R with
  | leaf => simp [formulaNodes, FrequencyBounds]
  | node s CL CR u left right ihL ihR =>
    simp only [formulaNodes, List.mem_cons, List.mem_append,
      or_imp, forall_and, forall_eq, ihL, ihR, FrequencyBounds]
    change ((_ ∧ _) ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
    tauto

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeGridResidueLift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original grid labels give the actual CRT unit lifts -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulkResidueEquiv_spectator_lift {I J : Type*} [Fintype I]
    (r : ℕ) (p : I → ℕ)
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (value : J → ℕ) (z : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value j : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (i : I) (j : J) :
    (value j : ZMod (p i)) = ((bulkResidueEquiv r p hc z).2 i j : ZMod (p i)) := by
  have he := congrArg (ZMod.castHom
    (Finset.dvd_prod_of_mem (bulkResidueModuli r p) (Finset.mem_univ (Sum.inr i : Unit ⊕ I)))
    (ZMod (p i))) (hz j)
  rw [map_natCast] at he
  change (value j : ZMod (p i)) =
    ((show (ZMod (p i))ˣ from crtUnitEquiv (bulkResidueModuli r p) hc (z j) (.inr i)) : ZMod (p i))
  rw [crtUnitEquiv_apply]
  exact he

theorem bulkResidueEquiv_frequency_lift {I J : Type*} [Fintype I]
    (r : ℕ) (p : I → ℕ)
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (value : J → ℕ) (z : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value j : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (j : J) :
    (value j : ZMod r) = ((bulkResidueEquiv r p hc z).1 j : ZMod r) := by
  have he := congrArg (ZMod.castHom
    (Finset.dvd_prod_of_mem (bulkResidueModuli r p) (Finset.mem_univ (Sum.inl () : Unit ⊕ I)))
    (ZMod r)) (hz j)
  rw [map_natCast] at he
  change (value j : ZMod r) =
    ((show (ZMod r)ˣ from crtUnitEquiv (bulkResidueModuli r p) hc (z j) (.inl ())) : ZMod r)
  rw [crtUnitEquiv_apply]
  exact he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFrequencyRepresentative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency factor evaluated on the actual bulk residue representative -/

namespace Ostmann
open scoped Classical

/-- Once the nonbulk coordinates have been fixed, the frequency factor is
a function of the frequency-unit array alone. The representative does not
alter any compensation denominator. -/
theorem movingFrequencyCore_bulk_residues {σ J : Type*}
    (value : σ → ℕ) (e : J ↪ σ) (r : ℕ) [NeZero r]
    (a : J → (ZMod r)ˣ) (ha : ∀ j, (value (e j) : ZMod r) = (a j : ZMod r))
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hT : ∀ b j, (T b).CompensationAbsent (e j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (XL XR : ℤ) :
    movingFrequencyCore value F E T R XL XR =
      movingFrequencyCore (Function.extend e (fun j => (a j).val.val) value) F E T R XL XR := by
  let w := Function.extend e (fun j => (a j).val.val) value
  have hcomp (b : Bool) : (T b).CompensationAgreement value w := by
    apply (T b).compensationAgreement_of_eq_off value w (Set.range e)
    · rintro i ⟨j, rfl⟩
      exact hT b j
    · intro i hi
      exact (Function.extend_apply' _ value i hi).symm
  have hv (i : σ) : (value i : ℤ) ≡ (w i : ℤ) [ZMOD R ^ (n + 1)] := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      have he : (value (e j) : ℤ) ≡ ((a j).val.val : ℤ) [ZMOD (r : ℤ)] := by
        apply (ZMod.intCast_eq_intCast_iff _ _ r).mp
        simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using ha j
      simpa only [w, e.injective.extend_apply] using he.of_dvd hr
    · rw [show w i = value i from Function.extend_apply' _ value i hi]
  exact movingFrequencyCore_values_modEq value w F E T R hf hcomp hR hv
    XL XR XL XR (Int.ModEq.refl _) (Int.ModEq.refl _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenFrequencyAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency/Page average on the fixed bulk residue representative -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem extend_eq_of_eq_off_range {σ J A : Type*} (e : J ↪ σ) (f : J → A)
    (v w : σ → A) (h : ∀ i ∉ Set.range e, v i = w i) :
    Function.extend e f v = Function.extend e f w := by
  funext i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [e.injective.extend_apply, e.injective.extend_apply]
  · rw [Function.extend_apply' _ v i hi, Function.extend_apply' _ w i hi, h i hi]

theorem movingFrequencyPageAverage_core {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y =
      (if ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCorePageAverage value F E T R r input Q y := by
  simp only [movingFrequencyPageAverage, movingFrequencyPairFactor_core,
    movingFrequencyCorePageAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem movingFrequencyCorePageAverage_bulk_residues {σ J : Type*}
    (base value : σ → ℕ) (e : J ↪ σ) (hv : ∀ i ∉ Set.range e, value i = base i)
    (r : ℕ) [NeZero r] (a : J → (ZMod r)ˣ)
    (ha : ∀ j, (value (e j) : ZMod r) = (a j : ZMod r))
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hT : ∀ b j, (T b).CompensationAbsent (e j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyCorePageAverage value F E T R r input Q y =
      movingFrequencyCorePageAverage (Function.extend e (fun j => (a j).val.val) base)
        F E T R r input Q y := by
  unfold movingFrequencyCorePageAverage
  apply congrArg ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro z _
  rw [movingFrequencyCore_bulk_residues value e r a ha F E T R hf hT hR hr,
    extend_eq_of_eq_off_range e _ value base hv]

theorem movingFrequencyCorePageAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) :
    ‖movingFrequencyCorePageAverage value F E T R r input Q y‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  let B := 2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
    ‖movingDataWeight (F true) (E true) (T true)‖)
  have hb (z : ZMod r × (ZMod r)ˣ) :
      ‖movingFrequencyCore value F E T R z.1.val z.2.val.val *
        pageGiantWeight input Q r z.2.val.val y‖ ≤ B := by
    unfold movingFrequencyCore
    split_ifs
    · rw [norm_mul, norm_mul, Complex.norm_conj]
      exact (mul_le_mul_of_nonneg_left (pageGiantWeight_norm_le_two input Q r _ y hy)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (mul_comm _ _)
    · simpa only [zero_mul, norm_zero] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hc : (Fintype.card (ZMod r × (ZMod r)ˣ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ZMod r × (ZMod r)ˣ) ≠ 0)
  rw [movingFrequencyCorePageAverage, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (ZMod r × (ZMod r)ˣ) : ℝ)⁻¹ * ∑ _z : ZMod r × (ZMod r)ˣ, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => hb z))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkCollisionSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original arithmetic support forces distinct bulk primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem prime_list_injective_of_pairwise {σ : Type*} (value : σ → ℕ)
    (L : List σ) (hprime : ∀ i ∈ L, (value i).Prime)
    (hp : (L.map value).Pairwise Nat.Coprime) :
    ∀ i ∈ L, ∀ j ∈ L, value i = value j → i = j := by
  have hn : (L.map value).Nodup := by
    apply hp.imp_of_mem
    intro a b ha hb hab
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact (Nat.coprime_primes (hprime i hi) (hprime j hj)).mp hab
  exact fun i hi j hj hij => List.inj_on_of_nodup_map hn hi hj hij

theorem buildMovingSlotData_injective_of_support {σ : Type*}
    (value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (outside : List ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hs : movingRegularOutsidePairwise value outside
      (buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples)) :
    Function.Injective (value ∘ slot) := by
  let T := buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples
  have hp : (T.regularSlots.map value).Pairwise Nat.Coprime := by
    have hroot : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
      cases hT : T with
      | leaf s L => simpa only [T, hT, movingRegularOutsidePairwise,
          MovingSlotData.regularSlots] using hs
      | node s CL CR u left right =>
        have hs' := hs
        change movingRegularOutsidePairwise value outside T at hs'
        rw [hT] at hs'
        exact hs'.1
    exact (List.pairwise_append.mp hroot).1
  have hm (j) : slot j ∈ T.regularSlots := by
    apply (buildMovingSlotData_regular_perm n t small (bulkSlotLeaves n m slot) samples).mem_iff.mpr
    exact List.mem_append_right _ ((mem_flatten_bulkSlotLeaves n m slot _).mpr ⟨j, rfl⟩)
  intro i j hij
  exact slot.injective (prime_list_injective_of_pairwise value T.regularSlots
    (fun i _ => hprime i) hp (slot i) (hm i) (slot j) (hm j) hij)

/-- The frequency factor vanishes on collisions before any averaging or
resampling is performed. -/
theorem movingFrequencyPageAverage_zero_of_bulk_collision {σ : Type*}
    (value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (outside : List ℕ)
    (hprime : ∀ i, (value i).Prime) (hbad : ¬Function.Injective (value ∘ slot))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (T : Bool → MovingSlotData σ n)
    (hT : T false = buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples)
    (nodes : Bool → List MovingFormulaNode) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y = 0 := by
  have hsupport : ¬(∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      ∀ f ∈ nodes b, f.guard.frequencyBounds) := by
    intro hs
    apply hbad
    apply buildMovingSlotData_injective_of_support value n m slot t small samples outside hprime
    rw [← hT]
    exact (hs false).1
  rw [movingFrequencyPageAverage_core]
  simp only [hsupport, ite_false, if_false, zero_mul]

/-- Inserting the distinctness gate leaves the literal supported arithmetic
coefficient unchanged. -/
theorem movingFrequencyPageAverage_collision_gate {σ : Type*}
    (value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (outside : List ℕ)
    (hprime : ∀ i, (value i).Prime)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (T : Bool → MovingSlotData σ n)
    (hT : T false = buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples)
    (nodes : Bool → List MovingFormulaNode) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) (A : ℂ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y * A =
      if Function.Injective (value ∘ slot) then
        movingFrequencyPageAverage value outside F E T nodes R r input Q y * A else 0 := by
  by_cases h : Function.Injective (value ∘ slot)
  · simp only [h, ite_true, if_true]
  · rw [ite_eq_right h, movingFrequencyPageAverage_zero_of_bulk_collision value n m slot
      t small samples outside hprime h F E T hT nodes R r input Q y, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimePriorDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual harmonic-prime point masses on the separated scales -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem primeSubsetPrior_le_exp (P Q : Finset ℕ) (p : P) (H T : ℝ)
    (hmass : (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hp : Real.exp T ≤ (p : ℝ)) :
    primeSubsetPrior P Q p ≤ Real.exp (H - T) := by
  have hp0 : 0 < (p : ℝ) := (Real.exp_pos T).trans_le hp
  have hi : (p : ℝ)⁻¹ ≤ Real.exp (-T) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hp
  calc
    _ ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := primeSubsetPrior_atom P Q p
    _ ≤ Real.exp H * Real.exp (-T) :=
      mul_le_mul hmass hi (inv_nonneg.mpr hp0.le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkDistinctnessRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing bulk-prime collisions under the original independent priors -/

namespace Ostmann
open scoped Classical BigOperators

theorem productPrior_pair_collision_le {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (α : ℝ) (hmax : ∀ i a, μ i a ≤ α)
    (i j : Fin n) (hij : i ≠ j) :
    (∑ x : Fin n → A, productPrior μ x * if x i = x j then (1 : ℝ) else 0) ≤ α := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hij.symm
    rw [sum_productPrior_insertNth μ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have hs (x : Fin n → A) :
        (∑ a, μ i a * if a = x t then (1 : ℝ) else 0) = μ i (x t) := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    simp_rw [hs]
    calc
      _ ≤ ∑ x : Fin n → A, productPrior (fun j => μ (i.succAbove j)) x * α :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hmax i (x t))
          (productPrior_nonneg _ (fun j a => hμ (i.succAbove j) a) x)
      _ = α := by rw [← Finset.sum_mul, productPrior_mass _ (fun j => hmass (i.succAbove j)), one_mul]

/-- Ordered pairs suffice; the harmless square count avoids selecting an
ordering of the actual bulk positions. -/
theorem productPrior_noninjective_le {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (α : ℝ) (hα : 0 ≤ α)
    (hmax : ∀ i a, μ i a ≤ α) :
    (∑ x : Fin n → A, productPrior μ x * if Function.Injective x then (0 : ℝ) else 1) ≤
      (n : ℝ) ^ 2 * α := by
  let bad := fun (x : Fin n → A) (ij : Fin n × Fin n) =>
    if ij.1 ≠ ij.2 ∧ x ij.1 = x ij.2 then (1 : ℝ) else 0
  have hpoint (x : Fin n → A) :
      (if Function.Injective x then (0 : ℝ) else 1) ≤ ∑ ij, bad x ij := by
    by_cases hx : Function.Injective x
    · rw [ite_eq_left hx]
      exact Finset.sum_nonneg fun ij _ => by dsimp [bad]; positivity
    · rw [ite_eq_right hx]
      have hw : ∃ i j, i ≠ j ∧ x i = x j := by
        by_contra! h
        exact hx (fun i j hij => by by_contra hne; exact h i j hne hij)
      obtain ⟨i, j, hij, heq⟩ := hw
      calc
        (1 : ℝ) = bad x (i, j) := by simp [bad, hij, heq]
        _ ≤ ∑ ij, bad x ij := Finset.single_le_sum
          (fun ij _ => by dsimp [bad]; positivity) (Finset.mem_univ _)
  calc
    _ ≤ ∑ x : Fin n → A, productPrior μ x * ∑ ij, bad x ij :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x)
        (productPrior_nonneg μ hμ x)
    _ = ∑ ij, ∑ x : Fin n → A, productPrior μ x * bad x ij := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ _ij : Fin n × Fin n, α := by
      apply Finset.sum_le_sum
      intro ij _
      by_cases hij : ij.1 = ij.2
      · simpa [bad, hij] using hα
      · simpa [bad, hij] using
          productPrior_pair_collision_le μ hμ hmass α hmax ij.1 ij.2 hij
    _ = (n : ℝ) ^ 2 * α := by simp [pow_two, mul_assoc]

/-- Removing the distinctness gate costs its original collision probability,
even when the complex integrand includes all the retained arithmetic factors. -/
theorem bulk_distinctness_removal {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (α : ℝ) (hα : 0 ≤ α)
    (hmax : ∀ i a, μ i a ≤ α) (F : (Fin n → A) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x : Fin n → A, (productPrior μ x : ℂ) *
        (if Function.Injective x then F x else 0)) -
      ∑ x : Fin n → A, (productPrior μ x : ℂ) * F x‖ ≤ B * (n : ℝ) ^ 2 * α := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : Fin n → A, B * (productPrior μ x *
        if Function.Injective x then (0 : ℝ) else 1) := by
      apply norm_sum_le_of_le
      intro x _
      by_cases hx : Function.Injective x
      · simp [hx]
      · simp only [hx, ite_false, if_false, mul_zero, zero_sub, norm_neg, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (productPrior_nonneg μ hμ x), mul_one]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hF x)
          (productPrior_nonneg μ hμ x)
    _ = B * ∑ x : Fin n → A, productPrior μ x *
        if Function.Injective x then (0 : ℝ) else 1 := (Finset.mul_sum _ _ _).symm
    _ ≤ B * ((n : ℝ) ^ 2 * α) := mul_le_mul_of_nonneg_left
      (productPrior_noninjective_le μ hμ hmass α hα hmax) hB
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryRealEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real evaluation of the original cleared history formulas -/

namespace Ostmann.HistoryFormula
open scoped Classical BigOperators

theorem realEval_bind {σ τ : Type*} (F : HistoryFormula σ) (f : σ → HistoryFormula τ)
    (x : τ → ℝ) : (F.bind f).realEval x = F.realEval (fun i => (f i).realEval x) := by
  induction F with
  | prime i => simp only [bind, realEval_prime]
  | external z => simp only [bind, realEval_external]
  | product l r hl hr => simp only [bind, realEval_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, realEval_solve, hl, hr]

theorem realEval_listProduct {σ : Type*} (fs : List (HistoryFormula σ)) (x : σ → ℝ) :
    (listProduct fs).realEval x = (fs.map (fun F => F.realEval x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, realEval_product, List.map_cons, List.prod_cons, ih]

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealNodeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original real node inequalities with variable bulk values -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.giantFormula_realEval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (hs : s.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value s.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (s.giantFormula value hs hu L R).realEval x =
      s.realValuePivot (fun i => (value i : ℝ)) (L.realEval x) (R.realEval x) := by
  simp only [giantFormula, HistoryFormula.realEval_solve, HistoryFormula.realEval_product,
    HistoryFormula.realEval_external, Int.cast_mul, Int.cast_natCast, realValuePivot,
    realSlotProduct_nat]
  ring

theorem movingNodeGuard_realEval (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).archimedeanAt x ↔
      1 ≤ ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ∧
      ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ≤ pivotBound ∧
      ((2 * pivotBound * childBound + 1 : ℕ) : ℝ) ≤ R.realEval x * CR := by
  simp only [movingNodeGuard, wordTransferGuard, WordTransferGuard.archimedeanAt,
    HistoryFormula.realEval_bind, HistoryPivotStep.formula, wordTransferStep, movingNodeWord,
    HistoryFormula.realEval_solve, HistoryFormula.realEval_listProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, HistoryFormula.realEval_prime, Bool.false_eq_true, ite_false, if_false,
    ite_true, if_true, HistoryFormula.realEval_product, HistoryFormula.realEval_external, Int.cast_natCast, mul_one]
  ring_nf

/-- Exact agreement with all original archimedean formula-node tests. -/
theorem realValueNodeSupport_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    movingArchimedeanGate (T.formulaNodes value hvalue childBound pivotBound hf L R) x ↔
      realValueNodeSupport (fun i => (value i : ℝ)) childBound pivotBound T (L.realEval x) (R.realEval x) := by
  induction T generalizing L R with
  | leaf => simp [MovingSlotData.formulaNodes, movingArchimedeanGate, realValueNodeSupport]
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.formulaNodes, movingArchimedeanGate, List.forall_mem_cons,
      List.forall_mem_append, realValueNodeSupport]
    rw [show (∀ f ∈ left.formulaNodes value hvalue childBound pivotBound hf.2.1
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) L, f.guard.archimedeanAt x) ↔ _ from
      ihL hf.2.1 _ L,
      show (∀ f ∈ right.formulaNodes value hvalue childBound pivotBound hf.2.2
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) R, f.guard.archimedeanAt x) ↔ _ from
      ihR hf.2.2 _ R]
    rw [movingNodeGuard_realEval]
    simp only [MovingSlotReversal.giantFormula_realEval, MovingSlotReversal.realCompositePivot,
      MovingSlotData.step, realSlotProduct_nat]
    tauto

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkNodeSupportPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact polynomial inequalities for all original bulk node supports -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.bulkCompositePolynomial_eval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ) (L R : Polynomial ℝ) (z : ℝ) :
    (s.bulkCompositePolynomial value i L R).eval z =
      s.realCompositePivot (Function.update value i z) (L.eval z) (R.eval z) := by
  rw [bulkCompositePolynomial, bulkPivotPolynomial_eval _ _ _ (by simp) L R z]
  simp only [realValuePivot, realCompositePivot, realSlotProduct, List.map_nil, List.prod_nil, mul_one]

theorem MovingSlotReversal.bulkCompositePolynomial_degree {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ) (L R : Polynomial ℝ)
    (d e : ℕ) (hs : s.lengthLE d) (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    (s.bulkCompositePolynomial value i L R).natDegree ≤ d + e :=
  bulkPivotPolynomial_degree _ value i L R d e ⟨hs.1, hs.2.1, by simp⟩ hL hR

theorem MovingSlotData.bulkNodeSupportPolynomials_eval {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (z : ℝ) :
    (∀ P ∈ T.bulkNodeSupportPolynomials value i childBound pivotBound L R, 0 ≤ P.eval z) ↔
      realValueNodeSupport (Function.update value i z) childBound pivotBound T (L.eval z) (R.eval z) := by
  induction T generalizing L R with
  | leaf => simp [bulkNodeSupportPolynomials, realValueNodeSupport]
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_eval
      value i hT.1 L R z
    simp only [bulkNodeSupportPolynomials, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, bulkSlotProduct_eval,
      MovingSlotReversal.bulkCompositePolynomial_eval,
      ihL hT.2.1, ihR hT.2.2, hp, realValueNodeSupport, sub_nonneg]
    tauto

theorem MovingSlotData.bulkNodeSupportPolynomials_length {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) :
    (T.bulkNodeSupportPolynomials value i childBound pivotBound L R).length = 3 * (2 ^ n - 1) := by
  induction T generalizing L R with
  | leaf => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [bulkNodeSupportPolynomials, List.length_append, List.length_cons,
      List.length_nil, ihL, ihR, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

/-- Every inequality has degree bounded by the depth times the actual slot
length. No coefficient-size assumption is needed. -/
theorem MovingSlotData.bulkNodeSupportPolynomials_degree {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (d e : ℕ)
    (hsize : T.SizeLE d) (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∀ P ∈ T.bulkNodeSupportPolynomials value i childBound pivotBound L R, P.natDegree ≤ n * d + e := by
  induction T generalizing L R e with
  | leaf => simp [bulkNodeSupportPolynomials]
  | @node n s CL CR u left right ihL ihR =>
    have hs : (MovingSlotData.step s CL CR u left right false).lengthLE d :=
      ⟨hsize.2.1, hsize.1, hsize.2.2.1⟩
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_degree
      value i L R d e hs hL hR
    have hQ := (MovingSlotData.step s CL CR u left right false).bulkCompositePolynomial_degree
      value i L R d e hs hL hR
    have hLR := Polynomial.natDegree_mul_le (p := R) (q := bulkSlotProduct value i CR)
    have hCR := (bulkSlotProduct_degree value i CR).trans hsize.2.1
    have hLe : L.natDegree ≤ d + e := hL.trans (Nat.le_add_left _ _)
    have hRe : R.natDegree ≤ d + e := hR.trans (Nat.le_add_left _ _)
    have hn : n * d + (d + e) = (n + 1) * d + e := by ring
    intro P hP
    simp only [bulkNodeSupportPolynomials, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hP
    rcases hP with (rfl | rfl | rfl) | hP | hP
    · have hd := Polynomial.natDegree_sub_le
        ((MovingSlotData.step s CL CR u left right false).bulkCompositePolynomial value i L R) (Polynomial.C 1)
      simp only [Polynomial.natDegree_C, max_zero] at hd
      exact hd.trans (hQ.trans (by omega))
    · have hd := Polynomial.natDegree_sub_le (Polynomial.C (pivotBound (n + 1) : ℝ))
        ((MovingSlotData.step s CL CR u left right false).bulkCompositePolynomial value i L R)
      simp only [Polynomial.natDegree_C, zero_max] at hd
      exact hd.trans (hQ.trans (by omega))
    · have hd := Polynomial.natDegree_sub_le (R * bulkSlotProduct value i CR)
        (Polynomial.C ((2 * pivotBound (n + 1) * childBound (n + 1) + 1 : ℕ) : ℝ))
      simp only [Polynomial.natDegree_C, max_zero] at hd
      exact hd.trans (hLR.trans (by omega))
    · simpa only [hn] using ihL _ _ (d + e) hsize.2.2.2.1 hp hLe P hP
    · simpa only [hn] using ihR _ _ (d + e) hsize.2.2.2.2 hp hRe P hP

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original kernel on real bulk coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- The real extension has precisely the old arithmetic gates and windows. -/
theorem realValueSupportFlag_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (X lo hi L R : ℝ) :
    realValueSupportFlag (fun i => (value i : ℝ)) childBound pivotBound T X lo hi L R =
      movingRealGateWeight value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        X lo hi (topGiantReal L R) := by
  have hn := realValueNodeSupport_nat value hv childBound pivotBound T hf
    (.prime false) (.prime true) (topGiantReal L R)
  simp only [HistoryFormula.realEval_prime, topGiantReal, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] at hn
  simp only [realValueSupportFlag, realValueFullSupport, movingRealGateWeight,
    movingArchimedeanFlag, movingRealWindowFlag, MovingSlotData.realValueLeafModuli_nat,
    topGiantReal, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  rw [hn]
  split_ifs <;> simp_all

theorem realValueKernel_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernel (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernel value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernel, realValueSupportFlag_nat value hv childBound pivotBound T hf,
    realValueSmoothWeight_nat]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFullSupportPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root cells for every original bulk support gate -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulkFullSupportPolynomials_eval {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.CompensationAbsent i) (L R : Polynomial ℝ) (X lo hi z : ℝ) :
    (∀ j, 0 ≤ (bulkFullSupportPolynomials value i childBound pivotBound T L R X lo hi j).eval z) ↔
      realValueFullSupport (Function.update value i z) childBound pivotBound T X lo hi (L.eval z) (R.eval z) := by
  have hn := T.bulkNodeSupportPolynomials_eval value i childBound pivotBound hT L R z
  rw [List.forall_mem_iff_get] at hn
  constructor
  · intro h
    refine ⟨hn.mp (fun j => h (.inl j)), ?_⟩
    intro j
    have hl := h (.inr (j, false))
    have hh := h (.inr (j, true))
    simp only [bulkFullSupportPolynomials, Sum.elim_inr, Bool.false_eq_true, ite_false, if_false,
      ite_true, if_true, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      T.bulkLeafPolynomials_eval value i hT L R z] at hl hh
    exact ⟨by simpa only [sub_nonneg, div_eq_mul_inv, mul_comm] using hl,
      by simpa only [sub_nonneg, div_eq_mul_inv, mul_comm] using hh⟩
  · rintro ⟨hnode, hwindow⟩ j
    cases j with
    | inl j => exact hn.mpr hnode j
    | inr j =>
      rcases j with ⟨j, b⟩
      have hj := hwindow j
      cases b
      · simpa only [bulkFullSupportPolynomials, Sum.elim_inr, Bool.false_eq_true, ite_false, if_false,
          Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
          T.bulkLeafPolynomials_eval value i hT L R z, sub_nonneg, div_eq_mul_inv, mul_comm] using hj.1
      · simpa only [bulkFullSupportPolynomials, Sum.elim_inr, ite_true, if_true,
          Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
          T.bulkLeafPolynomials_eval value i hT L R z, sub_nonneg, div_eq_mul_inv, mul_comm] using hj.2

theorem bulkFullSupportPolynomials_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (L R : Polynomial ℝ) (X lo hi : ℝ) (d r e : ℕ)
    (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∀ j, (bulkFullSupportPolynomials value i childBound pivotBound T L R X lo hi j).natDegree ≤
      2 * (n * d + e) + r := by
  intro j
  cases j with
  | inl j =>
    exact (T.bulkNodeSupportPolynomials_degree value i childBound pivotBound L R d e hsize hL hR
      _ (List.getElem_mem j.isLt)).trans (by omega)
  | inr j =>
    have hM : (Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R j.1).natDegree ≤
        2 * (n * d + e) + r := by
      have ht := T.bulkLeafPolynomials_degree value i L R d r e hsize hregular hL hR j.1
      exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using ht)
    rcases j with ⟨j, b⟩
    cases b
    · exact (Polynomial.natDegree_sub_le _ _).trans (by
        simpa only [Polynomial.natDegree_C, max_zero] using hM)
    · exact (Polynomial.natDegree_sub_le _ _).trans (by
        simpa only [Polynomial.natDegree_C, zero_max] using hM)

/-- These roots include all node ranges and terminal windows. The count is
uniform in all other real bulk values and both giant coefficients. -/
theorem bulkFullSupport_root_cuts {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.CompensationAbsent i) (L R : Polynomial ℝ) (X lo hi : ℝ) (d r e : ℕ)
    (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∃ S : Finset ℝ, S.card ≤ (3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r) ∧
      ∀ x y, rootCellCode S x = rootCellCode S y →
        realValueSupportFlag (Function.update value i x) childBound pivotBound T X lo hi (L.eval x) (R.eval x) =
        realValueSupportFlag (Function.update value i y) childBound pivotBound T X lo hi (L.eval y) (R.eval y) := by
  let J := Fin (T.bulkNodeSupportPolynomials value i childBound pivotBound L R).length ⊕
    (TreeLeafIndex n × Bool)
  let H := bulkFullSupportPolynomials value i childBound pivotBound T L R X lo hi
  let S := polynomialRootCuts H
  have hroot (j) (z) (hz : z ∈ (H j).roots) : z ∈ S :=
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hz⟩
  refine ⟨S, ?_, ?_⟩
  · apply (polynomialRootCuts_card H).trans
    calc
      _ ≤ ∑ _j : J, (2 * (n * d + e) + r) := Finset.sum_le_sum (fun j _ =>
        bulkFullSupportPolynomials_degree value i childBound pivotBound T L R X lo hi d r e
          hsize hregular hL hR j)
      _ = _ := by
        simp only [J, Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
          Fintype.card_prod, Fintype.card_bool, card_treeLeafIndex,
          MovingSlotData.bulkNodeSupportPolynomials_length, smul_eq_mul]
        ring
  · intro x y hxy
    have hp : (∀ j, 0 ≤ (H j).eval x) ↔ ∀ j, 0 ≤ (H j).eval y :=
      forall_congr' (fun j => polynomial_nonneg_iff_of_root_cell (H j) S (hroot j) hxy)
    have hx := bulkFullSupportPolynomials_eval value i childBound pivotBound T hT L R X lo hi x
    have hy := bulkFullSupportPolynomials_eval value i childBound pivotBound T hT L R X lo hi y
    have he := hx.symm.trans (hp.trans hy)
    exact if_congr he rfl rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothGatedPrimeRoots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison with the original sharp support gates retained -/

namespace Ostmann
open scoped Classical BigOperators
open MeasureTheory

/-- A sharp gate can change at every included polynomial root. Its exact values
at the roots are retained in the prime sum; endpoint atoms are part of the error. -/
theorem PublishedProgressionInput.gated_smooth_prime_all_roots (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexPrimeInterval q a u v (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc u v, w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      (S.card + 1 : ℕ) * (C * smoothPolynomialBudget F) *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)) := by
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  have h := P.common_root_prime_integral S s hs N hfree hQ hq hqQ ha
    (by simpa only [hs0] using hu) (by simpa only [hs0, hsN] using hshort)
    F hroots w C hC hw hconst
  simp only [hs0, hsN] at h
  have hlog : 0 ≤ Real.log (4 * (Q : ℝ)) := by
    apply Real.log_nonneg
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hB := smoothPolynomialBudget_nonneg F
  let E := 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
    Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)
  have hPC := P.errorConstant_nonneg
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  apply h.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range N, (C * smoothPolynomialBudget F) * E := by
      apply Finset.sum_le_sum
      intro j _
      have hj : u ≤ s j := by rw [← hs0]; exact hs (Nat.zero_le _)
      have ht : Real.exp (-P.decay * Real.sqrt (s j)) ≤ Real.exp (-P.decay * Real.sqrt u) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt hj) (by linarith [P.decay_pos]))
      have hp : Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ))) ≤
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonpos_left hj (by linarith [P.kappa_pos])) hlog)
      have ha' : Real.exp (-(s j)) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (neg_le_neg hj)
      have he := add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left ht (show 0 ≤ 18 * P.errorConstant from mul_nonneg (by norm_num) hPC)) hp)
        (mul_le_mul_of_nonneg_left ha' (by norm_num : (0 : ℝ) ≤ 2))
      have hA : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
          Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ))) := by positivity
      calc
        _ ≤ C * smoothPolynomialBudget F *
              (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
                Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
              2 * C * smoothPolynomialBudget F * Real.exp (-(s j)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hw _) hB) hA) le_rfl
        _ = (C * smoothPolynomialBudget F) *
              ((18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
                Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) + 2 * Real.exp (-(s j))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg hC hB)
    _ = (N : ℝ) * (C * smoothPolynomialBudget F) * E := by simp; ring
    _ ≤ (S.card + 1 : ℕ) * (C * smoothPolynomialBudget F) * E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (mul_nonneg hC hB)) hE

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkKernelPairComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison for the full original pair, with every sharp gate -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- The original node inequalities and terminal windows remain in both the
atomic prime sum and the Page integral. Their derivative-free polynomial root
cuts are included alongside all smooth derivative roots. -/
theorem PublishedProgressionInput.bulk_kernel_pair_prime_comparison (P : PublishedProgressionInput)
    {σ : Type*} (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hT : ∀ b, (T b).CompensationAbsent i)
    (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r e : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    let H := fun y => realValueKernelPair (Function.update value i (Real.exp y)) childBound pivotBound T
      ψ X lo hi hlo hhi φ G (L.eval (Real.exp y)) (R.eval (Real.exp y))
    ‖complexPrimeInterval q a u v H -
      ∫ y in Set.Ioc u v, H y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        bulkKernelPairComparisonBudget ψ V lo hi n d r e B D * bulkPrimeErrorFactor P Q u := by
  dsimp only
  let F (b : Bool) := bulkSmoothFactors value i (T b) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  let W := movingFourierVariationBudget ψ V lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)
  let A := (2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)
  let B' := (3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r)
  obtain ⟨S, hS, hrS⟩ := bulkSmoothFactors_root_cuts value i (T false) L R ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip d r e (hsize false) (hregular false) hL hR
  obtain ⟨U, hU, hrU⟩ := bulkSmoothFactors_root_cuts value i (T true) L R ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip d r e (hsize true) (hregular true) hL hR
  obtain ⟨S', hS', hcS⟩ := bulkFullSupport_root_cuts value i childBound pivotBound (T false)
    (hT false) L R X lo hi d r e (hsize false) (hregular false) hL hR
  obtain ⟨U', hU', hcU⟩ := bulkFullSupport_root_cuts value i childBound pivotBound (T true)
    (hT true) L R X lo hi d r e (hsize true) (hregular true) hL hR
  let V' := (S ∪ U) ∪ (S' ∪ U')
  have hcard : V'.card + 1 ≤ 2 * (A + B') + 1 := by
    simp only [MovingSlotData.bulkNodePolynomials_length] at hS hU
    have hsu := Finset.card_union_le S U
    have hsu' := Finset.card_union_le S' U'
    have hall := Finset.card_union_le (S ∪ U) (S' ∪ U')
    dsimp only [A, B', V']
    omega
  let w := fun z => realValueSupportFlag (Function.update value i z) childBound pivotBound
    (T false) X lo hi (L.eval z) (R.eval z) *
      conj (realValueSupportFlag (Function.update value i z) childBound pivotBound
        (T true) X lo hi (L.eval z) (R.eval z))
  have hw (z : ℝ) : ‖w z‖ ≤ 1 := by
    rw [show w z = _ * conj _ from rfl, norm_mul, Complex.norm_conj]
    exact (mul_le_mul (realValueSupportFlag_norm _ _ _ _ _ _ _ _ _)
      (realValueSupportFlag_norm _ _ _ _ _ _ _ _ _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hconst (x y : ℝ) (hxy : rootCellCode V' x = rootCellCode V' y) : w x = w y := by
    have hsxy := rootCellCode_eq_of_subset S' V'
      (Finset.subset_union_left.trans Finset.subset_union_right) x y hxy
    have huxy := rootCellCode_eq_of_subset U' V'
      (Finset.subset_union_right.trans Finset.subset_union_right) x y hxy
    change _ * conj _ = _ * conj _
    rw [hcS x y hsxy, hcU x y huxy]
  have hroots (j) (z) (hz : z ∈ ((pairedPolynomialFactors (F false) (F true)) j).polynomial.derivative.roots) : z ∈ V' :=
    Finset.mem_union_left _ (pairedPolynomialFactors_roots (F false) (F true) S U hrS hrU j z hz)
  have hbudget : smoothPolynomialBudget (pairedPolynomialFactors (F false) (F true)) ≤ W ^ 2 := by
    rw [pairedPolynomialFactors_budget, pow_two]
    have h0 := bulkSmoothFactors_budget value i (T false) L R ψ X lo hi V hlo hhi
      (hV false) φ G B D hB hD hφ hlip
    have h1 := bulkSmoothFactors_budget value i (T true) L R ψ X lo hi V hlo hhi
      (hV true) φ G B D hB hD hφ hlip
    exact mul_le_mul h0 h1 (smoothPolynomialBudget_nonneg _) ((smoothPolynomialBudget_nonneg _).trans h0)
  have he (z : ℝ) : w z * smoothPolynomialWeight (pairedPolynomialFactors (F false) (F true)) z =
      realValueKernelPair (Function.update value i z) childBound pivotBound T
        ψ X lo hi hlo hhi φ G (L.eval z) (R.eval z) := by
    rw [pairedPolynomialFactors_weight]
    simp only [F, bulkSmoothFactors_value value i (T false) (hT false) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout z,
      bulkSmoothFactors_value value i (T true) (hT true) L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout z]
    simp only [w, realValueKernelPair, realValueKernel, map_mul]
    ring
  have h := P.gated_smooth_prime_all_roots hQ hq hqQ ha u v hu huv hshort
    (pairedPolynomialFactors (F false) (F true)) V' hroots w 1 (by norm_num) hw hconst
  simp only [he, one_mul] at h
  apply h.trans
  change (V'.card + 1 : ℕ) * smoothPolynomialBudget (pairedPolynomialFactors (F false) (F true)) *
      bulkPrimeErrorFactor P Q u ≤ ((2 * (A + B') + 1 : ℕ) : ℝ) * W ^ 2 * bulkPrimeErrorFactor P Q u
  apply mul_le_mul_of_nonneg_right _ (by
    dsimp only [bulkPrimeErrorFactor]
    have := P.errorConstant_nonneg
    positivity)
  exact mul_le_mul (by exact_mod_cast hcard) hbudget (smoothPolynomialBudget_nonneg _) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkPrimeAtoms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding the actual joint prime cells on the common sample space -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem primeCellAtomWeight_nonneg (q a : ℕ) (u v : ℝ) (p : ℕ) :
    0 ≤ primeCellAtomWeight q a u v p := by
  unfold primeCellAtomWeight
  split_ifs <;> positivity

theorem primeLogCellMeasure_ambient (P : Finset ℕ) (q a : ℕ) (u v : ℝ)
    (hP : primeLogCellSet q a u v ⊆ P) :
    primeLogCellMeasure q a u v =
      ∑ p : P, ENNReal.ofReal (primeCellAtomWeight q a u v p) • Measure.dirac (Real.log (p : ℕ)) := by
  have hs : P.filter (fun p => p ∈ primeLogCellSet q a u v) = primeLogCellSet q a u v := by
    ext p
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hP h, h⟩⟩
  rw [Finset.sum_coe_sort P (fun p => ENNReal.ofReal (primeCellAtomWeight q a u v p) •
    Measure.dirac (Real.log p))]
  unfold primeLogCellMeasure
  rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ primeLogCellSet q a u v <;> simp [primeCellAtomWeight, hp]

/-- This equality retains each original atom and all residue restrictions;
there is no replacement by an independent uniform prime sample. -/
theorem BulkIntegrand.integral_prime_cell_product {J : Type*} [Fintype J]
    (f : BulkIntegrand J) (P : Finset ℕ) (q a : J → ℕ) (u v : J → ℝ)
    (hP : ∀ j, primeLogCellSet (q j) (a j) (u j) (v j) ⊆ P) :
    (∫ y, f y ∂Measure.pi (fun j => primeLogCellMeasure (q j) (a j) (u j) (v j))) =
      ∑ x : J → P, ((∏ j, primeCellAtomWeight (q j) (a j) (u j) (v j) (x j) : ℝ) : ℂ) *
        f (fun j => Real.log (x j : ℕ)) := by
  simp_rw [primeLogCellMeasure_ambient P _ _ _ _ (hP _)]
  exact f.integral_atomic_product _ _ (fun j x => primeCellAtomWeight_nonneg _ _ _ _ x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original paired kernel as a bounded measurable bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realValueKernelPair_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernelPair (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernelPair value T
        (fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernelPair, realValueKernel_nat value hv childBound pivotBound (T false) (hf false),
    realValueKernel_nat value hv childBound pivotBound (T true) (hf true)]
  rfl

/-- The full sharp paired kernel has the same derived one-coordinate Page
comparison, uniformly in every other real bulk coordinate. -/
theorem PublishedProgressionInput.bulk_kernel_log_slice_comparison
    (P : PublishedProgressionInput) {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (S : Finset σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (i : σ) (hiS : i ∈ S)
    (hT : ∀ b, (T b).CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r)
    (L R : ℝ) (f : BulkIntegrand σ)
    (hf : ∀ x, f x = realValueKernelPair (bulkLogValues base S x) childBound pivotBound T ψ X lo hi hlo hhi φ G L R)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) (x : σ → ℝ) :
    letI := finite_primeGiantMeasure P Q q a u v (lt_of_lt_of_le zero_lt_one hu)
    ‖f.average (primeLogCellMeasure q a u v) i x - f.average (primeGiantMeasure P Q q a u v) i x‖ ≤
      bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D * bulkPrimeErrorFactor P Q u := by
  let _ := finite_primeGiantMeasure P Q q a u v (lt_of_lt_of_le zero_lt_one hu)
  let value := bulkLogValues base S x
  let H := fun y => realValueKernelPair (Function.update value i (Real.exp y)) childBound pivotBound T
    ψ X lo hi hlo hhi φ G L R
  have hH (y : ℝ) : f (Function.update x i y) = H y := by
    rw [hf, bulkLogValues_update base S x i hiS]
  rw [f.average_prime_eq_interval q a u v i x H hH,
    f.average_page P Q q a u v (lt_of_lt_of_le zero_lt_one hu) i x]
  simp_rw [hH]
  have h := P.bulk_kernel_pair_prime_comparison value i childBound pivotBound T hT (Polynomial.C L) (Polynomial.C R)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r 0 hsize hregular
    (by simp) (by simp) hQ hq hqQ ha u v hu huv hshort
  simpa only [Polynomial.eval_C] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkWeightedCellComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keep all cell and residue costs in the prime replacement error -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- A residue-dependent arithmetic coefficient is held fixed during prime
replacement. Its absolute value only multiplies the replacement error. -/
theorem bulk_weighted_cell_comparison {J C R : Type*}
    [Fintype J] [Fintype C] [Fintype R]
    (K : BulkIntegrand J) (a : R → ℂ) (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ ν : (J → C) → R → J → Measure ℝ)
    [∀ c z j, IsFiniteMeasure (μ c z j)] [∀ c z j, IsFiniteMeasure (ν c z j)]
    (E : (J → C) → R → ℝ)
    (hE : ∀ c z, ‖(∫ y, K y ∂Measure.pi (μ c z)) -
      ∫ y, K y ∂Measure.pi (ν c z)‖ ≤ E c z) :
    ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
        ∫ y, (K.constMul (a z)) y ∂Measure.pi (μ c z) -
      ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
        ∫ y, (K.constMul (a z)) y ∂Measure.pi (ν c z)‖ ≤
      (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * E c z := by
  have hprod : 0 ≤ ∏ j, Z j := Finset.prod_nonneg fun j _ => hZ j
  simp only [BulkIntegrand.constMul, integral_const_mul]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprod]
  apply mul_le_mul_of_nonneg_left _ hprod
  rw [← Finset.sum_sub_distrib]
  apply norm_sum_le_of_le
  intro c _
  rw [← Finset.sum_sub_distrib]
  apply norm_sum_le_of_le
  intro z _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (hE c z) (norm_nonneg _)

/-- Combine the separately derived signed main term and replacement error. -/
theorem bulk_weighted_cell_bound {J C R : Type*}
    [Fintype J] [Fintype C] [Fintype R]
    (K : BulkIntegrand J) (a : R → ℂ) (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ ν : (J → C) → R → J → Measure ℝ)
    [∀ c z j, IsFiniteMeasure (μ c z j)] [∀ c z j, IsFiniteMeasure (ν c z j)]
    (E : (J → C) → R → ℝ)
    (hE : ∀ c z, ‖(∫ y, K y ∂Measure.pi (μ c z)) -
      ∫ y, K y ∂Measure.pi (ν c z)‖ ≤ E c z)
    (B : ℝ)
    (hmain : ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
      ∫ y, (K.constMul (a z)) y ∂Measure.pi (ν c z)‖ ≤ B) :
    ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
      ∫ y, (K.constMul (a z)) y ∂Measure.pi (μ c z)‖ ≤
      B + (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * E c z := by
  have he := bulk_weighted_cell_comparison K a Z hZ μ ν E hE
  rw [norm_sub_rev] at he
  exact (norm_le_norm_add_norm_sub _ _).trans (add_le_add hmain he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenMovingSamples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual low-tier samples stay fixed when bulk slots vary -/

namespace Ostmann
open scoped Classical

theorem movingSlotValues_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n)
    (h : ∀ i ∈ flattenMovingSlots n small, v i = w i) :
    movingSlotValues v n small = movingSlotValues w n small := by
  induction n with
  | zero =>
    unfold movingSlotValues MovingSlotReversal.naturalProduct
    congr 1
    exact List.map_congr_left h
  | succ n ih =>
    exact Prod.ext
      (ih small.1 (fun i hi => h i (List.mem_append_left _ hi)))
      (ih small.2 (fun i hi => h i (List.mem_append_right _ hi)))

theorem movingCompensationValues_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → σ) n)
    (h : ∀ i ∈ flattenMovingSlots n (movingCompensationSlots n samples), v i = w i) :
    movingCompensationValues v n samples = movingCompensationValues w n samples := by
  induction n with
  | zero =>
    funext i
    apply h
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  | succ n ih =>
    exact Prod.ext
      (ih samples.1 (fun i hi => h i (List.mem_append_left _ hi)))
      (ih samples.2 (fun i hi => h i (List.mem_append_right _ hi)))

/-- All internal samples have lower tier than the current bulk. This proves
equality of the complete sampled tree, including its shared child samples. -/
theorem MovingSampleSlots.values_eq_of_levels {σ : Type*} (tier : σ → ℕ)
    (v w : σ → ℕ) (k : ℕ) (heq : ∀ i, tier i < k → v i = w i)
    {n : ℕ} (samples : MovingSampleSlots σ n) (hn : n ≤ k)
    (hlevels : samples.Levels tier) : samples.values v = samples.values w := by
  induction samples with
  | leaf => rfl
  | @node n s left right ihL ihR =>
    change MovingGiantSamples.node (movingCompensationValues v n s) (left.values v) (right.values v) =
      MovingGiantSamples.node (movingCompensationValues w n s) (left.values w) (right.values w)
    congr 1
    · apply movingCompensationValues_congr
      intro i hi
      apply heq
      rw [hlevels.1 i hi]
      omega
    · exact ihL (by omega) hlevels.2.1
    · exact ihR (by omega) hlevels.2.2

/-- Replacing precisely the selected bulk coordinates preserves both sources
of nonbulk data used to construct the field diagram. -/
theorem frozenMoving_nonbulk_values {σ J : Type*} (tier : σ → ℕ)
    (base value : σ → ℕ) (e : J ↪ σ) (n : ℕ)
    (he : ∀ j, n ≤ tier (e j))
    (hv : ∀ i ∉ Set.range e, value i = base i)
    (small : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range e)
    (hsamples : samples.Levels tier) :
    movingSlotValues value n small = movingSlotValues base n small ∧
      samples.values value = samples.values base := by
  refine ⟨movingSlotValues_congr value base n small (fun i hi => hv i (hsmall i hi)), ?_⟩
  apply samples.values_eq_of_levels tier value base n _ (le_refl _) hsamples
  intro i hi
  apply hv
  rintro ⟨j, rfl⟩
  exact (not_lt_of_ge (he j)) hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFieldUnitAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact restriction of a spectator's mixed average to unit pairs -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingModularSpectator_zero {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (hg : g 0 = 0) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q) (hzero : x = 0 ∨ y = 0) :
    movingModularSpectator value q g D T x y = 0 := by
  induction T generalizing x y with
  | leaf s regular =>
    rcases hzero with h | h <;>
      simp only [movingModularSpectator, h, zero_mul, mul_zero, div_zero, hg]
  | node s CL CR U left right ihL ihR =>
    simp only [movingModularSpectator]
    split_ifs
    · rfl
    · rcases hzero with h | h
      · rw [ihL _ _ (Or.inr h), zero_mul]
      · rw [ihR _ _ (Or.inr h), star_zero, mul_zero]

theorem movingSpectatorHaarAverage_eq_units {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (hg : g 0 = 0) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) :
    movingSpectatorHaarAverage value q g D T =
      ((Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)) *
        ((Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℂ)⁻¹ *
          ∑ z : (ZMod q)ˣ × (ZMod q)ˣ, movingSpectatorPairFactor value q g D T z.1 z.2) := by
  have hz (y : (ZMod q)ˣ) : movingSpectatorPairFactor value q g D T 0 y = 0 := by
    rw [movingSpectatorPairFactor, movingModularSpectator_zero value g hg (D false) (T false)
      0 y (Or.inl rfl), zero_mul]
  have hs : (∑ z : ZMod q × (ZMod q)ˣ, movingSpectatorPairFactor value q g D T z.1 z.2) =
      ∑ z : (ZMod q)ˣ × (ZMod q)ˣ, movingSpectatorPairFactor value q g D T z.1 z.2 := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x y : (ZMod q)ˣ =>
      movingSpectatorPairFactor value q g D T x y)]
    apply Finset.sum_congr rfl
    intro y _
    exact (sum_units_eq_sum_of_zero (fun x => movingSpectatorPairFactor value q g D T x y) (hz y)).symm
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hu : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ZMod q)ˣ ≠ 0)
  simp only [movingSpectatorHaarAverage, hs, Fintype.card_prod, ZMod.card, Nat.cast_mul]
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSpectatorAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual spectator Haar factor as a fixed function of the bulk residues -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {σ : Type*} {q : ℕ} [Fact q.Prime]
  (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
  (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))

theorem frozenBulkSpectatorPair_actual (value : σ → ℕ)
    (hv : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hs : ∀ b, (samples b).values value = (samples b).values base)
    (slot : TreeLeafIndex n × Fin m → σ) (g : ZMod q → ℂ)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (hz : ∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) :
    movingSpectatorPairFactor value q g D
      (fun b => buildMovingSlotData n (t b) (small b)
        (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot)
        (samples b)) a.1 a.2 =
      frozenBulkSpectatorPair base n m t small samples D e g a z := by
  unfold movingSpectatorPairFactor
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [buildMovingSlotData_modular_spectator value g (D false) n (t false)
      (small false) _ (samples false) a.1 a.2 _
      (bulkSlotLeaves_naturalLift value n m slot z hz),
    buildMovingSlotData_modular_spectator value g (D true) n (t true)
      (small true) _ (samples true) a.1 a.2 _
      (bulkSlotLeaves_naturalLift value n m (slot ∘ e.symm) (z ∘ e.symm)
        (fun j => hz (e.symm j))), hv, hv, hs, hs]
  rfl

theorem frozenBulkSpectatorHaar_actual (value : σ → ℕ)
    (hv : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hs : ∀ b, (samples b).values value = (samples b).values base)
    (slot : TreeLeafIndex n × Fin m → σ) (g : ZMod q → ℂ) (hg : g 0 = 0)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (hz : ∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) :
    movingSpectatorHaarAverage value q g D
      (fun b => buildMovingSlotData n (t b) (small b)
        (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot)
        (samples b)) = frozenBulkSpectatorHaar base n m t small samples D e g z := by
  rw [movingSpectatorHaarAverage_eq_units value g hg]
  simp_rw [frozenBulkSpectatorPair_actual base n m t small samples D e value hv hs slot g _ z hz]
  rfl

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenArithmeticFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # CRT identification of the actual bulk arithmetic factors -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingCoreSpectator_bulk_residues {σ I : Type*} [Fintype I]
    (base value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (hv : ∀ i ∉ Set.range slot, value i = base i)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (samples : Bool → MovingSampleSlots σ n)
    (hvsmall : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hvsamples : ∀ b, (samples b).values value = (samples b).values base)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (T : Bool → MovingSlotData σ n)
    (hT : ∀ b, T b = buildMovingSlotData n (t b) (small b)
      (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot) (samples b))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (R : ℤ) (r : ℕ) [NeZero r]
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hcomp : ∀ b j, (T b).CompensationAbsent (slot j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (D : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (slot j) : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyCorePageAverage value F E T R r input Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (D i) T =
    movingFrequencyCorePageAverage
        (Function.extend slot (fun j => ((bulkResidueEquiv r p hc z).1 j).val.val) base)
        F E T R r input Q y *
      ∏ i, frozenBulkSpectatorHaar base n m t small samples (D i) e (g i)
        ((bulkResidueEquiv r p hc z).2 i) := by
  rw [movingFrequencyCorePageAverage_bulk_residues base value slot hv r
    (bulkResidueEquiv r p hc z).1
    (bulkResidueEquiv_frequency_lift r p hc (value ∘ slot) z hz)
    F E T R hf hcomp hR hr input Q y]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have ht : T = fun b => buildMovingSlotData n (t b) (small b)
      (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot) (samples b) :=
    funext hT
  rw [ht]
  exact frozenBulkSpectatorHaar_actual base n m t small samples (D i) e value
    hvsmall hvsamples slot (g i) (hg i) ((bulkResidueEquiv r p hc z).2 i)
    (bulkResidueEquiv_spectator_lift r p hc (value ∘ slot) z hz i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full frequency factor retains precisely the fixed nonbulk support -/

namespace Ostmann
open scoped Classical

theorem movingFrequencyPageAverage_nonbulk {σ : Type*}
    (value base : σ → ℕ) (bulk : σ → Bool) (outside : List ℕ)
    (hv : ∀ i, bulk i = false → value i = base i)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (hprime : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ b, ∀ L ∈ (T b).regularLists, (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, bulk i = true →
      ∀ p ∈ outside, (value i).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y =
      (if ∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCorePageAverage value F E T R r input Q y := by
  have hsupport : (∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds)) ↔
      (∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds)) := by
    apply forall_congr'
    intro b
    exact and_congr (movingRegularOutsidePairwise_frozen value base bulk outside (T b)
      hv (hprime b) (hnodup b) hinj (hcross b) (hout b)) Iff.rfl
  rw [movingFrequencyPageAverage_core]
  simp only [hsupport]

/-- For the literal formula-node list, the remaining frequency-size tests
depend on the frequency tree alone. -/
theorem movingFrequencyPageAverage_actual_nonbulk {σ : Type*}
    (value base : σ → ℕ) (bulk : σ → Bool) (outside : List ℕ)
    (hv : ∀ i, bulk i = false → value i = base i)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hprime : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ b, ∀ L ∈ (T b).regularLists, (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, bulk i = true →
      ∀ p ∈ outside, (value i).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T
      (fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b)
        (.prime false) (.prime true)) R r input Q y =
      (if ∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (T b).FrequencyBounds childBound then (1 : ℂ) else 0) *
      movingFrequencyCorePageAverage value F E T R r input Q y := by
  rw [movingFrequencyPageAverage_nonbulk value base bulk outside hv F E T _
    hprime hnodup hinj hcross hout]
  have he : (∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
      ∀ f ∈ (T b).formulaNodes value hvalue childBound pivotBound (hf b)
        (.prime false) (.prime true), f.guard.frequencyBounds) ↔
      (∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (T b).FrequencyBounds childBound) := by
    apply forall_congr'
    intro b
    exact and_congr Iff.rfl ((T b).formulaNodes_frequencyBounds value hvalue childBound
      pivotBound (hf b) (.prime false) (.prime true))
  simp only [he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSpectatorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem movingFieldGiantAmplitude_norm_le {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (D : (ZMod q)ˣ) {n C : ℕ} (T : MovingGiantTree n C)
    (x y : ZMod q) (z : TreeLeafTuple (ZMod q)ˣ n) :
    ‖movingFieldGiantAmplitude g D T x y z‖ ≤ K ^ (2 ^ n) := by
  induction T generalizing x y with
  | leaf s C =>
    simpa only [movingFieldGiantAmplitude, pow_zero, pow_one] using hg _
  | @node n s CL CR u left right ihL ihR =>
    simp only [movingFieldGiantAmplitude]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hK (2 ^ (n + 1))
    · rw [norm_mul, Complex.norm_conj]
      calc
        _ ≤ K ^ (2 ^ n) * K ^ (2 ^ n) :=
          mul_le_mul (ihL _ _ _) (ihR _ _ _) (norm_nonneg _) (pow_nonneg hK _)
        _ = K ^ (2 ^ (n + 1)) := by
          rw [← pow_add, pow_succ]
          congr 1
          omega

theorem frozenBulkSpectatorPair_norm_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
    ‖frozenBulkSpectatorPair base n m t small samples D e g a z‖ ≤ K ^ (2 ^ (n + 1)) := by
  rw [frozenBulkSpectatorPair, norm_mul, Complex.norm_conj]
  calc
    _ ≤ K ^ (2 ^ n) * K ^ (2 ^ n) :=
      mul_le_mul (movingFieldGiantAmplitude_norm_le g K hK hg _ _ _ _ _)
        (movingFieldGiantAmplitude_norm_le g K hK hg _ _ _ _ _) (norm_nonneg _) (pow_nonneg hK _)
    _ = K ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

/-- The mixed Haar normalization has norm at most one, so the field bound
survives without a factor depending on the spectator prime. -/
theorem frozenBulkSpectatorHaar_norm_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
    ‖frozenBulkSpectatorHaar base n m t small samples D e g z‖ ≤ K ^ (2 ^ (n + 1)) := by
  let A := (ZMod q)ˣ × (ZMod q)ˣ
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ha : ‖(Fintype.card A : ℂ)⁻¹ * ∑ a : A,
      frozenBulkSpectatorPair base n m t small samples D e g a z‖ ≤ K ^ (2 ^ (n + 1)) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, K ^ (2 ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
          frozenBulkSpectatorPair_norm_le base n m t small samples D e g K hK hg a z))
          (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = K ^ (2 ^ (n + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hr : ‖(Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_one (by exact_mod_cast (Fact.out : q.Prime).pos)).mpr
    exact_mod_cast (ZMod.card_units q ▸ Nat.sub_le q 1)
  rw [frozenBulkSpectatorHaar, norm_mul]
  exact (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (pow_nonneg hK (2 ^ (n + 1))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSupportedArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem frozenBulkFrequencyFactor_norm_le {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput)
    (Q : ℕ) (y : ℝ) (hy : 0 ≤ y) (a : J → (ZMod r)ˣ) :
    ‖frozenBulkFrequencyFactor base slot outside F E T childBound R r input Q y a‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  unfold frozenBulkFrequencyFactor
  split_ifs
  · rw [one_mul]
    exact movingFrequencyCorePageAverage_norm_le _ F E T R r input Q y hy
  · rw [zero_mul, norm_zero]
    positivity

/-- The nonbulk coprimalities stay inside the fixed frequency factor. The
only injectivity used here is the actual distinct-bulk event, removed later
under its original product prior. -/
theorem movingSupportedArithmetic_bulk_residues {σ I : Type*} [Fintype I]
    (base value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (hv : ∀ i ∉ Set.range slot, value i = base i)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (samples : Bool → MovingSampleSlots σ n)
    (hvsmall : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hvsamples : ∀ b, (samples b).values value = (samples b).values base)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (T : Bool → MovingSlotData σ n)
    (hT : ∀ b, T b = buildMovingSlotData n (t b) (small b)
      (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot) (samples b))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hprime : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ b, ∀ L ∈ (T b).regularLists,
      (L.filter (bulkIndexPredicate slot)).Nodup)
    (hinj : Function.Injective (value ∘ slot))
    (hcross : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulkIndexPredicate slot i ≠ bulkIndexPredicate slot j → value i ≠ value j)
    (hout : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, i ∈ Set.range slot →
      ∀ p ∈ outside, (value i).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r]
    (hcomp : ∀ b j, (T b).CompensationAbsent (slot j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (D : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (slot j) : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T
        (fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b)
          (.prime false) (.prime true)) R r input Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (D i) T =
    frozenBulkFrequencyFactor base slot outside F E T childBound R r input Q y
        (bulkResidueEquiv r p hc z).1 *
      ∏ i, frozenBulkSpectatorHaar base n m t small samples (D i) e (g i)
        ((bulkResidueEquiv r p hc z).2 i) := by
  have hinj' : ∀ i j, bulkIndexPredicate slot i = true →
      bulkIndexPredicate slot j = true → value i = value j → i = j := by
    intro i j hi hj hij
    obtain ⟨a, rfl⟩ := (bulkIndexPredicate_eq_true slot i).mp hi
    obtain ⟨b, rfl⟩ := (bulkIndexPredicate_eq_true slot j).mp hj
    exact congrArg slot (hinj hij)
  rw [movingFrequencyPageAverage_actual_nonbulk value base
    (bulkIndexPredicate slot) outside
    (fun i hi => hv i ((bulkIndexPredicate_eq_false slot i).mp hi)) hvalue childBound pivotBound F E T hf
    hprime hnodup hinj' hcross (fun b L hL i hi hb => hout b L hL i hi ((bulkIndexPredicate_eq_true slot i).mp hb))]
  rw [mul_assoc, movingCoreSpectator_bulk_residues base value n m slot hv t small samples
    hvsmall hvsamples e T hT F E R r hf hcomp hR hr p hc g hg D z hz input Q y]
  simp only [frozenBulkFrequencyFactor, mul_assoc, finite_univ_canonical]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFormulaRenaming
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_prior_reindex {V W A : Type*} [Fintype V] [Fintype W] [Fintype A]
    (e : V ≃ W) (μ : W → A → ℝ) (F : (W → A) → ℂ) :
    (∑ x : V → A, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm)) =
      ∑ x : W → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x := by
  have he := (Equiv.arrowCongr e (Equiv.refl A)).sum_comp
    (fun x : W → A => ((∏ i, μ i (x i) : ℝ) : ℂ) * F x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  change ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm) =
    ((∏ i, μ i (x (e.symm i)) : ℝ) : ℂ) * F (x ∘ e.symm)
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun i => μ i (x (e.symm i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IndexedBulkDistinctness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bulk collision removal on the original tree-and-word positions -/

namespace Ostmann
open scoped Classical BigOperators

theorem bulk_distinctness_removal_indexed {J A : Type*} [Fintype J] [Fintype A]
    (μ : J → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1) (α : ℝ) (hα : 0 ≤ α)
    (hmax : ∀ i a, μ i a ≤ α) (F : (J → A) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x : J → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * (if Function.Injective x then F x else 0)) -
      ∑ x : J → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x‖ ≤ B * (Fintype.card J : ℝ) ^ 2 * α := by
  let e := (Fintype.equivFin J).symm
  have hi (x : Fin (Fintype.card J) → A) :
      Function.Injective (x ∘ e.symm) ↔ Function.Injective x := by
    constructor
    · intro h
      simpa only [Function.comp_def, Equiv.symm_apply_apply] using h.comp e.injective
    · intro h
      exact h.comp e.symm.injective
  have he₁ := finite_prior_reindex e μ (fun x => if Function.Injective x then F x else 0)
  simp_rw [hi] at he₁
  have he₂ := finite_prior_reindex e μ F
  have h := bulk_distinctness_removal (fun i => μ (e i))
    (fun i => hμ (e i)) (fun i => hmass (e i)) α hα (fun i => hmax (e i))
    (fun x => F (x ∘ e.symm)) B hB (fun x => hF (x ∘ e.symm))
  change ‖(∑ x, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) *
      (if Function.Injective x then F (x ∘ e.symm) else 0)) -
    ∑ x, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm)‖ ≤ _ at h
  simp only [finite_univ_canonical] at he₁ he₂ h ⊢
  rw [he₁, he₂] at h
  exact h

theorem original_bulk_distinctness_removal_indexed {J : Type*} [Fintype J]
    (P : Finset ℕ) (Q : J → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (H T : ℝ) (hmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hlow : ∀ i p, p ∈ Q i → Real.exp T ≤ (p : ℝ))
    (F : (J → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x : J → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
        (if Function.Injective x then F x else 0)) -
      ∑ x : J → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * F x‖ ≤
      B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) := by
  have hmax (i : J) (p : P) : primeSubsetPrior P (Q i) p ≤ Real.exp (H - T) := by
    by_cases hp : (p : ℕ) ∈ Q i
    · exact primeSubsetPrior_le_exp P (Q i) p H T (hmass i) (hlow i p hp)
    · simpa only [primeSubsetPrior, hp, ite_false, if_false] using Real.exp_nonneg (H - T)
  have h := bulk_distinctness_removal_indexed (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i))
    (Real.exp (H - T)) (Real.exp_nonneg _) hmax F B hB hF
  simp only [finite_univ_canonical] at h ⊢
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  split_ifs <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IndexedBulkKernelComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp-kernel comparison in the original tree-and-word coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem BulkIntegrand.averages_enum {J : Type*} [Fintype J] {k : ℕ}
    (f : BulkIntegrand J) (g : Fin k ≃ J)
    (μ : J → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (x : J → ℝ) :
    f.averages μ ((List.finRange k).map g) x = ∫ y, f y ∂Measure.pi μ := by
  have he (y : J → ℝ) : bulkCoordinateInsert (fun _ : J => (0 : ℝ)) (Function.Embedding.refl J) y = y := by
    funext j
    exact bulkCoordinateInsert_at _ (Function.Embedding.refl J) y j
  have h := f.selected_bulk_integral_enum (fun _ => 0) (Function.Embedding.refl J) g μ x
  simpa only [Function.Embedding.refl_apply, he] using h

theorem BulkIntegrand.integral_comparison_indexed {J : Type*} [Fintype J]
    (f : BulkIntegrand J) (μ ν : J → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (hμ : ∀ i, (μ i).real Set.univ ≤ 2) (hν : ∀ i, (ν i).real Set.univ ≤ 2)
    (ε : J → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (herr : ∀ i x, ‖f.average (μ i) i x - f.average (ν i) i x‖ ≤ ε i) :
    ‖(∫ x, f x ∂Measure.pi μ) - ∫ x, f x ∂Measure.pi ν‖ ≤
      2 ^ Fintype.card J * ∑ i, ε i := by
  let g := (Fintype.equivFin J).symm
  have hn : ((List.finRange (Fintype.card J)).map g).Nodup :=
    (List.nodup_finRange _).map g.injective
  have h := f.averages_comparison μ ν _ hn (fun i _ => hμ i) (fun i _ => hν i)
    ε (fun i _ => hε i) (fun i _ => herr i) (fun _ => 0)
  rw [f.averages_enum g, f.averages_enum g] at h
  have hs : (((List.finRange (Fintype.card J)).map g).map ε).sum = ∑ i, ε i := by
    rw [List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
    exact g.sum_comp ε
  simpa only [List.length_map, List.length_finRange, hs] using h

theorem PublishedProgressionInput.bulk_kernel_integral_comparison_indexed
    (P : PublishedProgressionInput) {σ J : Type*} [Fintype σ] [Fintype J] {n : ℕ}
    (base : σ → ℝ) (S : Finset σ) (e : J ↪ σ) (he : ∀ i, e i ∈ S)
    (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
    (hT : ∀ b i, (T b).CompensationAbsent (e i))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (d r : ℕ) (hsize : ∀ b, (T b).SizeLE d) (hregular : ∀ b, (T b).RegularLengthLE r)
    (L R : ℝ) (f : BulkIntegrand σ)
    (hf : ∀ x, f x = realValueKernelPair (bulkLogValues base S x)
      childBound pivotBound T ψ X lo hi hlo hhi φ G L R)
    {Q : ℕ} (hQ : 2 ≤ Q) (q a : J → ℕ) (u v : J → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
    let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
    ‖(∫ y, f (bulkCoordinateInsert base e y) ∂Measure.pi μ) -
      ∫ y, f (bulkCoordinateInsert base e y) ∂Measure.pi ν‖ ≤
      2 ^ Fintype.card J * ∑ i, bulkKernelPairComparisonBudget ψ V lo hi n d r 0 B D *
        bulkPrimeErrorFactor P Q (u i) := by
  let μ := fun i => primeLogCellMeasure (q i) (a i) (u i) (v i)
  let ν := fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i)
  let _ : ∀ i, IsFiniteMeasure (ν i) := fun i =>
    finite_primeGiantMeasure P Q _ _ _ _ (lt_of_lt_of_le zero_lt_one (hu i))
  have hs (i : J) (x : σ → ℝ) := P.bulk_kernel_log_slice_comparison
    base S childBound pivotBound T (e i) (he i) (fun b => hT b i)
    ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout d r hsize hregular L R f hf
    hQ (hq i) (hqQ i) (ha i) (u i) (v i) (hu i) (huv i) (hshort i) x
  have hμ (i : J) : (μ i).real Set.univ ≤ 2 := by
    rw [primeLogCellMeasure_mass]
    exact hmass i
  have hν (i : J) : (ν i).real Set.univ ≤ 2 :=
    primeGiantMeasure_mass_le_two P Q _ _ (hq i) _ _ (hu i) (huv i) (hshort i)
  apply (f.pullBulk base e).integral_comparison_indexed μ ν hμ hν _
    (fun i => (norm_nonneg _).trans (hs i base))
  intro i y
  have h := hs i (bulkCoordinateInsert base e y)
  change ‖((f.average (μ i) (e i)).pullBulk base e) y -
    ((f.average (ν i) (e i)).pullBulk base e) y‖ ≤ _ at h
  simpa only [BulkIntegrand.pullBulk_average] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern pair in selected bulk coordinates -/

namespace Ostmann
open scoped Classical

theorem movingPatternFiniteSamples_levels {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) (side : Bool) :
    (movingPatternFiniteSamples e n pattern side).Levels ((Sum.elim tierB tierC) ∘ e) := by
  apply movingSampleCoordinates_levels
  intro i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inr] using htier (side, i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkFrozen
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern has fixed nonbulk data under bulk resampling -/

namespace Ostmann
open scoped Classical

theorem movingPatternBulkEmbedding_external_mem {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B) (b : B) :
    e.symm (.inl b) ∈ Set.range (movingPatternBulkEmbedding e slot) ↔ b ∈ Set.range slot := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, Sum.inl.inj (e.symm.injective hj)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

theorem movingPatternFiniteSmall_absent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (small : TreeLeafTuple (List B) n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    ∀ i ∈ flattenMovingSlots n (movingPatternFiniteSmall e n small),
      i ∉ Set.range (movingPatternBulkEmbedding e slot) := by
  intro i hi
  rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
  exact fun h => hsmall b hb ((movingPatternBulkEmbedding_external_mem e slot b).mp h)

theorem movingPattern_nonbulk_values {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (base value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base i)
    (small : TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (side : Bool) :
    movingSlotValues value n (movingPatternFiniteSmall e n small) =
        movingSlotValues base n (movingPatternFiniteSmall e n small) ∧
      (movingPatternFiniteSamples e n pattern side).values value =
        (movingPatternFiniteSamples e n pattern side).values base := by
  apply frozenMoving_nonbulk_values ((Sum.elim tierB tierC) ∘ e) base value
    (movingPatternBulkEmbedding e slot) n _ hv _ _
    (movingPatternFiniteSmall_absent e slot small hsmall)
    (movingPatternFiniteSamples_levels e tierB tierC n pattern htier side)
  intro j
  change n ≤ Sum.elim tierB tierC (e (e.symm (.inl (slot j))))
  simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hB (slot j)

theorem movingPatternFinBulkData_bulk_nodup {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) :
    ∀ b, ∀ L ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).regularLists,
      (L.filter (bulkIndexPredicate (movingPatternBulkEmbedding e slot))).Nodup := by
  let lift := movingPatternBulkEmbedding e slot
  let tier := (Sum.elim tierB tierC) ∘ e
  have hgrade (i) (hi : bulkIndexPredicate lift i = true) : n ≤ tier i := by
    obtain ⟨j, rfl⟩ := (bulkIndexPredicate_eq_true lift i).mp hi
    change n ≤ Sum.elim tierB tierC (e (e.symm (.inl (slot j))))
    simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hB (slot j)
  have hs (b) (i) (hi : i ∈ flattenMovingSlots n (movingPatternFiniteSmall e n (small b))) :
      bulkIndexPredicate lift i = false :=
    (bulkIndexPredicate_eq_false lift i).mpr (movingPatternFiniteSmall_absent e slot _ (hsmall b) i hi)
  have hst (b) (i) (hi : i ∈ flattenMovingSlots n (movingPatternFiniteSmall e n (small b))) :
      n ≤ tier i := by
    rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    simpa only [tier, Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inl] using hB j
  intro b
  rw [movingPatternFinBulkData_build]
  cases b
  · exact buildMovingSlotData_bulk_nodup n m (bulkIndexPredicate lift) tier lift
      (fun j => (bulkIndexPredicate_eq_true lift _).mpr ⟨j, rfl⟩) hgrade
      (t false) (movingPatternFiniteSmall e n (small false))
      (movingPatternFiniteSamples e n pattern false) (hs false) (hst false)
      (movingPatternFiniteSamples_levels e tierB tierC n pattern htier false)
  · exact buildMovingSlotData_bulk_nodup n m (bulkIndexPredicate lift) tier
      (perm.symm.toEmbedding.trans lift)
      (fun j => (bulkIndexPredicate_eq_true lift _).mpr ⟨perm.symm j, rfl⟩) hgrade
      (t true) (movingPatternFiniteSmall e n (small true))
      (movingPatternFiniteSamples e n pattern true) (hs true) (hst true)
      (movingPatternFiniteSamples_levels e tierB tierC n pattern htier true)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported arithmetic of the original equality-pattern histories -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original pattern's Page and spectator factors separate on precisely
its selected bulk residues. The unchanged small and sampled data, denominator
independence and regular-list distinctness are derived from the constructor. -/
theorem movingPattern_supported_arithmetic {B C I : Type*} [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base i)
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hf : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).Frequencies (· ≠ 0))
    (hinj : Function.Injective (value ∘ movingPatternBulkEmbedding e slot))
    (hcross : ∀ i j, bulkIndexPredicate (movingPatternBulkEmbedding e slot) i ≠
      bulkIndexPredicate (movingPatternBulkEmbedding e slot) j → value i ≠ value j)
    (hout : ∀ j p, p ∈ outside → (value (movingPatternBulkEmbedding e slot j)).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r]
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (D : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (movingPatternBulkEmbedding e slot j) : ZMod (∏ i, bulkResidueModuli r p i)) =
      (z j : ZMod _))
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let hvalue := fun i => (hprime i).ne_zero
    movingFrequencyPageAverage value outside F E T
        (fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b)
          (.prime false) (.prime true)) R r input Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (D i) T =
    frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
        F E T childBound R r input Q y (bulkResidueEquiv r p hc z).1 *
      ∏ i, frozenBulkSpectatorHaar base n m t (fun b => movingPatternFiniteSmall e n (small b))
        (movingPatternFiniteSamples e n pattern) (D i) perm (g i)
        ((bulkResidueEquiv r p hc z).2 i) := by
  have hfixed := fun b => movingPattern_nonbulk_values e tierB tierC slot base value hv
    (small b) pattern (hsmall b) hB htier b
  exact movingSupportedArithmetic_bulk_residues base value n m (movingPatternBulkEmbedding e slot)
    hv t (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
    (fun b => (hfixed b).1) (fun b => (hfixed b).2) perm
    (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternFinBulkData_build e n m t small slot perm pattern) F E outside childBound pivotBound
    (fun i => (hprime i).ne_zero) hf (fun _ _ _ i _ => hprime i)
    (movingPatternFinBulkData_bulk_nodup e tierB tierC t small slot perm pattern hsmall hB htier)
    hinj (fun _ _ _ i _ j _ h => hcross i j h)
    (fun _ _ _ i _ hi p hp => by
      obtain ⟨j, rfl⟩ := hi
      exact hout j p hp)
    R r (movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier)
    hR hr p hc g hg D z hz input Q y

/-- Bulk collisions are already zero under the original pattern coefficient,
so inserting the distinctness indicator precedes all changes of measure. -/
theorem movingPattern_arithmetic_collision_gate {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (value : Fin (N + 1) → ℕ) (hprime : ∀ i, (value i).Prime)
    (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
    (nodes : Bool → List MovingFormulaNode) (R : ℤ) (r : ℕ) [NeZero r]
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) (A : ℂ) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    movingFrequencyPageAverage value outside F E T nodes R r input Q y * A =
      if Function.Injective (value ∘ movingPatternBulkEmbedding e slot) then
        movingFrequencyPageAverage value outside F E T nodes R r input Q y * A else 0 := by
  exact movingFrequencyPageAverage_collision_gate value n m (movingPatternBulkEmbedding e slot)
    (t false) (movingPatternFiniteSmall e n (small false)) (movingPatternFiniteSamples e n pattern false)
    outside hprime F E (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternFinBulkData_build e n m t small slot perm pattern false) nodes R r input Q y A

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkBudgets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete length and frequency budgets for the original pattern pair -/

namespace Ostmann
open scoped Classical

theorem movingLeafLengthLE_map {A B : Type*} (f : A → B) (n : ℕ)
    (x : TreeLeafTuple (List A) n) (r : ℕ) (hx : MovingLeafLengthLE n x r) :
    MovingLeafLengthLE n (treeLeafMap (List.map f) n x) r := by
  induction n with
  | zero => simpa only [MovingLeafLengthLE, treeLeafMap, List.length_map] using hx
  | succ n ih => exact ⟨ih x.1 hx.1, ih x.2 hx.2⟩

theorem bulkSlotLeaves_length {A : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    MovingLeafLengthLE n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => simp [bulkSlotLeaves, MovingLeafLengthLE, treeLeafTupleEquiv]
  | succ n ih =>
    change MovingLeafLengthLE n
      (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthLE n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

theorem movingPatternFinBulkData_size {B C : Type*} {N n m r : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).SizeLE
      (2 ^ n * (r + m + 4 * n + 4)) := by
  rw [movingPatternFinBulkData_build]
  apply buildMovingSlotData_size n (t b) _ _ _ r m
    (movingLeafLengthLE_map _ n (small b) r (hsmall b))
  cases b <;> exact bulkSlotLeaves_length n m _

theorem movingPatternFinBulkData_regular_length {B C : Type*} {N n m r : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).RegularLengthLE
      (2 ^ n * (r + m + 4 * n)) := by
  rw [movingPatternFinBulkData_build]
  apply buildMovingSlotData_regular_length n (t b) _ _ _ r m
    (movingLeafLengthLE_map _ n (small b) r (hsmall b))
  cases b <;> exact bulkSlotLeaves_length n m _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkLog
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real bulk coordinates evaluate to the original pattern primes -/

namespace Ostmann
open scoped Classical

theorem selectedBulkLogValues {σ J : Type*} [Fintype σ]
    (base : σ → ℝ) (slot : J ↪ σ) (y : J → ℝ) :
    bulkLogValues base (selectedBulkSet slot) (bulkCoordinateInsert base slot y) =
      Function.extend slot (fun j => Real.exp (y j)) base := by
  funext i
  by_cases hi : i ∈ Set.range slot
  · obtain ⟨j, rfl⟩ := hi
    have hs : slot j ∈ selectedBulkSet slot := (mem_selectedBulkSet slot _).mpr ⟨j, rfl⟩
    rw [slot.injective.extend_apply]
    simp only [bulkLogValues, hs, ite_true, if_true, bulkCoordinateInsert_at]
  · rw [Function.extend_apply' _ base i hi]
    simp only [bulkLogValues, mem_selectedBulkSet, hi, ite_false, if_false]

theorem selectedBulkLogValues_nat {σ J : Type*} [Fintype σ]
    (base value : σ → ℕ) (slot : J ↪ σ)
    (hv : ∀ i ∉ Set.range slot, value i = base i) (hp : ∀ j, 0 < value (slot j)) :
    bulkLogValues (fun i => (base i : ℝ)) (selectedBulkSet slot)
        (bulkCoordinateInsert (fun i => (base i : ℝ)) slot (fun j => Real.log (value (slot j) : ℝ))) =
      fun i => (value i : ℝ) := by
  rw [selectedBulkLogValues]
  funext i
  by_cases hi : i ∈ Set.range slot
  · obtain ⟨j, rfl⟩ := hi
    rw [slot.injective.extend_apply, Real.exp_log (by exact_mod_cast hp j)]
  · rw [Function.extend_apply' _ _ i hi, hv i hi]

/-- At original prime tuples the real extension has exactly the original
sharp gates and Fourier windows. This includes every boundary point. -/
theorem movingPattern_bulk_kernel_nat {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (base value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base i)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (hf : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    realValueKernelPair
      (bulkLogValues (fun i => (base i : ℝ)) (selectedBulkSet (movingPatternBulkEmbedding e slot))
        (bulkCoordinateInsert (fun i => (base i : ℝ)) (movingPatternBulkEmbedding e slot)
          (fun j => Real.log (value (movingPatternBulkEmbedding e slot j) : ℝ))))
      childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
    movingRealKernelPair value T
      (fun b => (T b).formulaNodes value hvalue childBound pivotBound
        (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hf b)
        (.prime false) (.prime true)) ψ X lo hi hlo hhi φ G L R := by
  dsimp only
  rw [selectedBulkLogValues_nat base value (movingPatternBulkEmbedding e slot) hv
    (fun j => Nat.pos_of_ne_zero (hvalue _))]
  exact realValueKernelPair_nat value hvalue childBound pivotBound _ _ ψ X lo hi hlo hhi φ G L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-to-Page comparison for the actual pattern's sharp bulk kernel -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The sharp real kernel is constructed here. Compensation independence,
all frequency bounds and both polynomial length budgets come from the actual
pattern constructor, including its prescribed bulk permutation. -/
theorem PublishedProgressionInput.movingPattern_kernel_integral_comparison
    (P : PublishedProgressionInput) {B C : Type*} {N n m r₀ : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (base : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ)
    {Q : ℕ} (hQ : 2 ≤ Q)
    (q a : TreeLeafIndex n × Fin m → ℕ) (u v : TreeLeafIndex n × Fin m → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let lift := movingPatternBulkEmbedding e slot
    let S := selectedBulkSet lift
    let hcomp := movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier
    let hV := movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq
    let f := bulkLogKernelPairIntegrand base S childBound pivotBound T hcomp
      (lift j₀) ((mem_selectedBulkSet lift _).mpr ⟨j₀, rfl⟩)
      ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hout L R
    let K := f.pullBulk base lift
    ‖(∫ y, K y ∂Measure.pi (fun i => primeLogCellMeasure (q i) (a i) (u i) (v i))) -
      ∫ y, K y ∂Measure.pi (fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i))‖ ≤
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) *
        ∑ i, bulkKernelPairComparisonBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
          bulkPrimeErrorFactor P Q (u i) := by
  dsimp only
  let f := bulkLogKernelPairIntegrand base (selectedBulkSet (movingPatternBulkEmbedding e slot))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternBulkSet_compensationAbsent e tierB tierC t small slot perm pattern hB htier)
    (movingPatternBulkEmbedding e slot j₀)
    ((mem_selectedBulkSet _ _).mpr ⟨j₀, rfl⟩) ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L R
  exact P.bulk_kernel_integral_comparison_indexed base
    (selectedBulkSet (movingPatternBulkEmbedding e slot)) (movingPatternBulkEmbedding e slot)
    (fun j => (mem_selectedBulkSet _ _).mpr ⟨j, rfl⟩) childBound pivotBound
    (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout _ _
    (movingPatternFinBulkData_size e t small slot perm pattern hsmall)
    (movingPatternFinBulkData_regular_length e t small slot perm pattern hsmall)
    L R f (fun _ => rfl) hQ q a u v hq hqQ ha hu huv hshort hmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit size of the actual sharp bulk kernel -/

namespace Ostmann
open scoped Classical SchwartzMap

/-- The bound used in prime replacement is explicit, rather than an
unspecified boundedness constant of the constructed integrand. -/
theorem realValueKernelPair_norm_le {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hcomp : ∀ b, (T b).CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  have hb (b) := realValueKernel_norm value i childBound pivotBound (T b) (hcomp b)
    ψ X lo hi V hlo hhi (hV b) φ G B D hB hD hφ hlip hout L R
  have hpos := (norm_nonneg _).trans (hb false)
  rw [realValueKernelPair, norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul (hb false) (hb true) (norm_nonneg _) hpos

theorem movingPattern_kernel_norm_le {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (value : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound
      (movingPatternFinBulkData e n m t small slot perm pattern) ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 :=
  realValueKernelPair_norm_le value (movingPatternBulkEmbedding e slot j₀) childBound pivotBound _
    (fun b => movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier b j₀)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternIntegrand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pattern's bounded bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

theorem movingPatternBulkIntegrand_norm (z : (TreeLeafIndex n × Fin m) → ℝ) :
    ‖movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U z‖ ≤
    (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 :=
  movingPattern_kernel_norm_le e tierB tierC t small slot perm pattern hB htier
    (bulkLogValues base (selectedBulkSet (movingPatternBulkEmbedding e slot))
      (bulkCoordinateInsert base (movingPatternBulkEmbedding e slot) z))
    childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U

theorem movingPatternBulkIntegrand_nat
    (base₀ value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base₀ i)
    (hvalue : ∀ i, value i ≠ 0)
    (hf : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier
      (fun i => (base₀ i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
      φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
      (fun j => Real.log (value (movingPatternBulkEmbedding e slot j) : ℝ)) =
    movingRealKernelPair value T
      (fun b => (T b).formulaNodes value hvalue childBound pivotBound
        (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hf b)
        (.prime false) (.prime true)) ψ X lo hi hlo hhi φ G L U :=
  movingPattern_bulk_kernel_nat e t small slot perm pattern base₀ value hv hvalue
    childBound pivotBound hf ψ X lo hi hlo hhi φ G L U

theorem PublishedProgressionInput.movingPatternBulkIntegrand_comparison
    (P : PublishedProgressionInput) {r₀ : ℕ}
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀)
    {Q : ℕ} (hQ : 2 ≤ Q)
    (q a : TreeLeafIndex n × Fin m → ℕ) (u v : TreeLeafIndex n × Fin m → ℝ)
    (hq : ∀ i, 1 ≤ q i) (hqQ : ∀ i, q i ≤ Q) (ha : ∀ i, (a i).Coprime (q i))
    (hu : ∀ i, 1 ≤ u i) (huv : ∀ i, u i ≤ v i) (hshort : ∀ i, v i ≤ u i + 1)
    (hmass : ∀ i, ∑ p ∈ primeLogCellSet (q i) (a i) (u i) (v i), (p : ℝ)⁻¹ ≤ 2) :
    let K := movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
    ‖(∫ z, K z ∂Measure.pi (fun i => primeLogCellMeasure (q i) (a i) (u i) (v i))) -
      ∫ z, K z ∂Measure.pi (fun i => primeGiantMeasure P Q (q i) (a i) (u i) (v i))‖ ≤
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ i,
        bulkKernelPairComparisonBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
          bulkPrimeErrorFactor P Q (u i) :=
  P.movingPattern_kernel_integral_comparison e tierB tierC t small slot perm pattern hB htier hsmall
    base childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
    hQ q a u v hq hqQ ha hu huv hshort hmass

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Return the separated bulk kernel to the original supported histories -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- An exact identity for every original prime tuple.  Its bulk collision
indicator is derived from the original regular-product support, before any
prime replacement or change of normalization. -/
theorem movingPattern_bulk_supported_identity {B C I : Type*} [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base i)
    (hprime : ∀ i, (value i).Prime) (childBound pivotBound : ℕ → ℕ)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
    (outside : List ℕ)
    (hcross : ∀ i j, bulkIndexPredicate (movingPatternBulkEmbedding e slot) i ≠
      bulkIndexPredicate (movingPatternBulkEmbedding e slot) j → value i ≠ value j)
    (hout : ∀ j p, p ∈ outside → (value (movingPatternBulkEmbedding e slot j)).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r]
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (movingPatternBulkEmbedding e slot j) : ZMod (∏ i, bulkResidueModuli r p i)) =
      (z j : ZMod _))
    (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
    (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun b => (data b).formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
      (.prime false) (.prime true)
    movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
      (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
        ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data) =
      if Function.Injective (value ∘ movingPatternBulkEmbedding e slot) then
        movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier
          (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
          φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
          (fun j => Real.log (value (movingPatternBulkEmbedding e slot j) : ℝ)) *
        (frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
          F E data childBound R r P Q y (bulkResidueEquiv r p hc z).1 *
          ∏ i, frozenBulkSpectatorHaar base n m t (fun b => movingPatternFiniteSmall e n (small b))
            (movingPatternFiniteSamples e n pattern) (twist i) perm (g i)
            ((bulkResidueEquiv r p hc z).2 i))
      else 0 := by
  intro data nodes
  by_cases hinj : Function.Injective (value ∘ movingPatternBulkEmbedding e slot)
  · rw [ite_eq_left hinj]
    rw [movingPatternBulkIntegrand_nat e tierB tierC t small slot perm pattern hB htier
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
      base value hv (fun i => (hprime i).ne_zero) hfreq]
    congr 1
    exact movingPattern_supported_arithmetic e tierB tierC t small slot perm pattern hsmall hB htier
      base value hv F E outside childBound pivotBound hprime
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq)
      hinj hcross hout R r hR hr p hc g hg twist z hz P Q y
  · rw [ite_eq_right hinj]
    have hzero := movingPattern_arithmetic_collision_gate e t small slot perm pattern value hprime
      outside F E nodes R r P Q y (∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data)
    dsimp only at hzero
    rw [ite_eq_right hinj] at hzero
    rw [hzero, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FourierWindowDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The leaf-window decay retained in the Section 8 norm bound -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem normalizedFourierProfile_norm_window (ψ : ℝ → ℂ) (v B lo z : ℝ)
    (hψ : ∀ t, ‖ψ t‖ ≤ B) (hlo : 0 < lo) (hz : lo ≤ z) :
    ‖normalizedFourierProfile ψ v z‖ ≤ B / Real.sqrt lo := by
  have hs := Real.sqrt_pos.mpr hlo
  have hz' := Real.sqrt_le_sqrt hz
  rw [normalizedFourierProfile, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    _ ≤ (Real.sqrt z)⁻¹ * B :=
      mul_le_mul_of_nonneg_left (hψ _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ (Real.sqrt lo)⁻¹ * B :=
      mul_le_mul_of_nonneg_right (inv_anti₀ hs hz') ((norm_nonneg (ψ 0)).trans (hψ 0))
    _ = _ := by ring

theorem fourierPolynomialFactor_norm_window (P : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (x : ℝ) :
    ‖(fourierPolynomialFactor P ψ v lo hi hlo hhi).value x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo := by
  apply normalizedFourierProfile_norm_window ψ v _ lo _
    (fun t => ψ.norm_le_seminorm ℝ t) (by linarith)
  exact (clipRealInterval_bounds lo hi (P.eval x) hhi).1

theorem realValueFourierWeight_norm_window {σ : Type*} (value : σ → ℝ) {n : ℕ}
    (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (L R : ℝ) :
    ‖realValueFourierWeight value T ψ X lo hi hlo hhi L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) := by
  have he : (SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) =
      ∏ _i : TreeLeafIndex n, SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo := by
    simp only [Finset.prod_const, Finset.card_univ, card_treeLeafIndex]
  rw [he, realValueFourierWeight, norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i _
  have hb := fourierPolynomialFactor_norm_window Polynomial.X ψ (T.leafFrequencies i)
    lo hi hlo hhi (T.realValueLeafModuli value L R i / X)
  split_ifs
  · simpa only [Complex.norm_conj] using hb
  · exact hb

theorem realValueNodeCutoff_norm_bound {σ : Type*} (value : σ → ℝ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    ‖realValueNodeCutoff value φ G T L R‖ ≤ B ^ (2 ^ n - 1) := by
  have hb (G x : ℝ) : ‖(positiveLogCutoff φ G x : ℂ)‖ ≤ B := by
    unfold positiveLogCutoff
    split_ifs
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hφ _
    · simpa only [Complex.ofReal_zero, norm_zero] using hB
  induction T generalizing L R with
  | leaf => simp [realValueNodeCutoff]
  | @node n s CL CR u left right ihL ihR =>
    simp only [realValueNodeCutoff, norm_mul]
    calc
      _ ≤ (B * B ^ (2 ^ n - 1)) * B ^ (2 ^ n - 1) := by
        apply mul_le_mul _ (ihR _ _) (norm_nonneg _) (mul_nonneg hB (pow_nonneg hB _))
        exact mul_le_mul (hb _ _) (ihL _ _) (norm_nonneg _) hB
      _ = B ^ (2 ^ (n + 1) - 1) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        have := Nat.one_le_two_pow (n := n)
        rw [pow_succ]
        omega

theorem realValueKernel_norm_window {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖realValueKernel value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * B ^ (2 ^ n - 1) := by
  have hψ : 0 ≤ SchwartzMap.seminorm ℝ 0 0 ψ :=
    (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  rw [realValueKernel, norm_mul]
  apply (mul_le_mul_of_nonneg_right
    (realValueSupportFlag_norm value childBound pivotBound T X lo hi L R) (norm_nonneg _)).trans
  rw [one_mul, realValueSmoothWeight, norm_mul]
  exact mul_le_mul (realValueFourierWeight_norm_window value T ψ X lo hi hlo hhi L R)
    (realValueNodeCutoff_norm_bound value φ G B hB hφ T L R) (norm_nonneg _)
    (by positivity)

theorem realValueKernelPair_norm_window {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 := by
  have hb b := realValueKernel_norm_window value childBound pivotBound (T b)
    ψ X lo hi hlo hhi φ G B hB hφ L R
  rw [realValueKernelPair, norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul (hb false) (hb true) (norm_nonneg _) ((norm_nonneg _).trans (hb false))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternNormKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The window decay for the literal prime-cell integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

theorem movingPatternBulkIntegrand_norm_window (z : (TreeLeafIndex n × Fin m) → ℝ) :
    ‖movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U z‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2 :=
  realValueKernelPair_norm_window
    (bulkLogValues base (selectedBulkSet (movingPatternBulkEmbedding e slot))
      (bulkCoordinateInsert base (movingPatternBulkEmbedding e slot) z))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    ψ X lo hi hlo hhi φ G Bφ hBφ hφ L U

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalPrimeCellExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue-dependent kernels under the exact original prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem primeSubsetPrior_cell_atom {C : Type*} [Fintype C]
    (P : Finset ℕ) (q : ℕ) (a : C → ℕ) (u v : C → ℝ) (c₀ c : C) (p : P)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ v c ≤ u d ∨ v d ≤ u c) :
    (∑ t ∈ primeCellSupport q a u v, (t : ℝ)⁻¹)⁻¹ * primeCellAtomWeight q (a c) (u c) (v c) p =
      if primeCellLabel q a u v c₀ p = c then primeSubsetPrior P (primeCellSupport q a u v) p else 0 := by
  have hm : (p : ℕ) ∈ primeLogCellSet q (a c) (u c) (v c) ↔
      (p : ℕ) ∈ primeCellSupport q a u v ∧ primeCellLabel q a u v c₀ p = c := by
    rw [← primeCellLabel_fiber q a u v c₀ hsep c, Finset.mem_filter]
  unfold primeCellAtomWeight primeSubsetPrior
  by_cases hp : (p : ℕ) ∈ primeCellSupport q a u v <;>
    by_cases hc : primeCellLabel q a u v c₀ p = c <;>
      simp [hm, hp, hc, div_eq_mul_inv, mul_comm]

theorem sum_coordinate_delta {J C : Type*} [Fintype J] [Fintype C]
    (label : J → C) (w : J → ℝ) (F : (J → C) → ℂ) :
    (∑ c : J → C, ((∏ j, if label j = c j then w j else 0 : ℝ) : ℂ) * F c) =
      ((∏ j, w j : ℝ) : ℂ) * F label := by
  have hp (c : J → C) : (∏ j, if label j = c j then w j else 0) =
      if label = c then ∏ j, w j else 0 := by
    by_cases hc : label = c
    · subst c; simp
    · obtain ⟨j, hj⟩ : ∃ j, label j ≠ c j := by
        by_contra h
        exact hc (funext fun j => not_not.mp (not_exists.mp h j))
      rw [ite_eq_right hc]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
  simp_rw [hp]
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, if_true]

/-- The kernels may depend on the entire residue-cell assignment. Summing
their atomic integrals is exactly the original normalized prime expectation
of the appropriate kernel at each prime tuple. -/
theorem original_prime_cell_expansion {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (q : J → ℕ) (a : J → C → ℕ) (u v : J → C → ℝ) (c₀ : C)
    (hP : ∀ j, primeCellSupport (q j) (a j) (u j) (v j) ⊆ P)
    (hsep : ∀ j c d, c ≠ d →
      ¬Nat.ModEq (q j) (a j c) (a j d) ∨ v j c ≤ u j d ∨ v j d ≤ u j c)
    (f : (J → C) → BulkIntegrand J) :
    let S := fun j => primeCellSupport (q j) (a j) (u j) (v j)
    let Z := fun j => (∑ p ∈ S j, (p : ℝ)⁻¹)⁻¹
    ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C,
      ∫ y, f c y ∂Measure.pi (fun j => primeLogCellMeasure (q j) (a j (c j)) (u j (c j)) (v j (c j))) =
    ∑ x : J → P, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) *
      f (fun j => primeCellLabel (q j) (a j) (u j) (v j) c₀ (x j)) (fun j => Real.log (x j : ℕ)) := by
  dsimp only
  have hcell (j : J) (c : C) : primeLogCellSet (q j) (a j c) (u j c) (v j c) ⊆ P := by
    intro p hp
    exact hP j (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hp⟩)
  simp_rw [BulkIntegrand.integral_prime_cell_product _ P _ _ _ _ (fun j => hcell j _)]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  have hprod (c : J → C) :
      ((∏ j, (∑ p ∈ primeCellSupport (q j) (a j) (u j) (v j), (p : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) *
        (((∏ j, primeCellAtomWeight (q j) (a j (c j)) (u j (c j)) (v j (c j)) (x j) : ℝ) : ℂ) *
          f c (fun j => Real.log (x j : ℕ))) =
      ((∏ j, if primeCellLabel (q j) (a j) (u j) (v j) c₀ (x j) = c j then
        primeSubsetPrior P (primeCellSupport (q j) (a j) (u j) (v j)) (x j) else 0 : ℝ) : ℂ) *
          f c (fun j => Real.log (x j : ℕ)) := by
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
    congr 2
    apply Finset.prod_congr rfl
    intro j _
    exact primeSubsetPrior_cell_atom P (q j) (a j) (u j) (v j) c₀ (c j) (x j) (hsep j)
  simp_rw [hprod]
  exact sum_coordinate_delta _ _ (fun c => f c (fun j => Real.log (x j : ℕ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalBulkResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the real cells and residues of the original prime sample -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem sum_joint_cells_residues {J C R : Type*}
    [Fintype J] [Fintype C] [Fintype R] (F : (J → C × R) → ℂ) :
    (∑ a : J → C × R, F a) =
      ∑ c : J → C, ∑ z : J → R, F (fun j => (c j, z j)) := by
  let e := Equiv.arrowProdEquivProdArrow J (fun _ => C) (fun _ => R)
  rw [← e.symm.sum_comp F, Fintype.sum_prod_type]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RestoredPrimeCellExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keep the deleted-set normalization in the original cell expansion -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem harmonic_mass_ne_zero_of_sdiff (S D : Finset ℕ)
    (h : (∑ p ∈ S \ D, (p : ℝ)⁻¹) ≠ 0) : (∑ p ∈ S, (p : ℝ)⁻¹) ≠ 0 := by
  have hp : 0 < ∑ p ∈ S \ D, (p : ℝ)⁻¹ :=
    lt_of_le_of_ne (Finset.sum_nonneg fun p _ => by positivity) (Ne.symm h)
  exact ne_of_gt (hp.trans_le (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    (fun p _ _ => by positivity)))

/-- Restoring a prime atom multiplies the full-set normalized prior by
exactly the ratio of its harmonic masses, not by a new probability law. -/
theorem restored_prime_prior_atom (P S D : Finset ℕ)
    (h : (∑ p ∈ S \ D, (p : ℝ)⁻¹) ≠ 0) (p : P) :
    ((∑ t ∈ S \ D, (t : ℝ)⁻¹)⁻¹ * ∑ t ∈ S, (t : ℝ)⁻¹) * primeSubsetPrior P S p =
      if (p : ℕ) ∈ S then (∑ t ∈ S \ D, (t : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ else 0 := by
  unfold primeSubsetPrior
  by_cases hp : (p : ℕ) ∈ S
  · rw [ite_eq_left hp, ite_eq_left hp, div_eq_mul_inv]
    have hs := harmonic_mass_ne_zero_of_sdiff S D h
    calc
      _ = (∑ t ∈ S \ D, (t : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ *
          ((∑ t ∈ S, (t : ℝ)⁻¹) * (∑ t ∈ S, (t : ℝ)⁻¹)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hs, mul_one]
  · simp [hp]

theorem restored_prime_cell_expansion {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (q : J → ℕ) (a : J → C → ℕ) (u v : J → C → ℝ) (c₀ : C)
    (hP : ∀ j, primeCellSupport (q j) (a j) (u j) (v j) ⊆ P)
    (hsep : ∀ j c d, c ≠ d →
      ¬Nat.ModEq (q j) (a j c) (a j d) ∨ v j c ≤ u j d ∨ v j d ≤ u j c)
    (D : J → Finset ℕ)
    (hD : ∀ j, (∑ p ∈ primeCellSupport (q j) (a j) (u j) (v j) \ D j, (p : ℝ)⁻¹) ≠ 0)
    (f : (J → C) → BulkIntegrand J) :
    let S := fun j => primeCellSupport (q j) (a j) (u j) (v j)
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C,
      ∫ y, f c y ∂Measure.pi (fun j => primeLogCellMeasure (q j) (a j (c j)) (u j (c j)) (v j (c j))) =
    ∑ x : J → P,
      ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) *
        f (fun j => primeCellLabel (q j) (a j) (u j) (v j) c₀ (x j)) (fun j => Real.log (x j : ℕ)) := by
  let S := fun j => primeCellSupport (q j) (a j) (u j) (v j)
  let T := fun j => ∑ p ∈ S j, (p : ℝ)⁻¹
  let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
  let R := ∏ j, Z j * T j
  have ht (j : J) : T j ≠ 0 := harmonic_mass_ne_zero_of_sdiff (S j) (D j) (hD j)
  have hc : R * (∏ j, (T j)⁻¹) = ∏ j, Z j := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [mul_assoc, mul_inv_cancel₀ (ht j), mul_one]
  have h := congrArg ((R : ℂ) * ·) (original_prime_cell_expansion P q a u v c₀ hP hsep f)
  rw [← mul_assoc, ← Complex.ofReal_mul] at h
  change ((R * ∏ j, (T j)⁻¹ : ℝ) : ℂ) * _ = _ at h
  rw [hc] at h
  conv_rhs at h => rw [Finset.mul_sum]
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
  congr 2
  apply Finset.prod_congr rfl
  intro j _
  exact restored_prime_prior_atom P (S j) (D j) (hD j) (x j)

/-- Restored atoms retain both their actual residue labels and the original
deleted-set normalizer. -/
theorem restored_bulk_residue_expansion {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (M : ℕ) [NeZero M] (u v : J → C → ℝ)
    (c₀ : C × (ZMod M)ˣ)
    (hP : ∀ j, primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ P)
    (hsep : ∀ j (c d : C × (ZMod M)ˣ), c ≠ d →
      ¬Nat.ModEq M c.2.val.val d.2.val.val ∨ v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (D : J → Finset ℕ)
    (hD : ∀ j, (∑ p ∈ primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ D j, (p : ℝ)⁻¹) ≠ 0)
    (f : (J → C) → (J → (ZMod M)ˣ) → BulkIntegrand J) :
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    let label := fun (x : J → P) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z : J → (ZMod M)ˣ,
      ∫ y, f c z y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j))) =
    ∑ x : J → P,
      ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) *
        f (fun j => (label x j).1) (fun j => (label x j).2) (fun j => Real.log (x j : ℕ)) := by
  have h := restored_prime_cell_expansion P (fun _ : J => M)
    (fun _ (c : C × (ZMod M)ˣ) => c.2.val.val)
    (fun j c => u j c.1) (fun j c => v j c.1) c₀ hP hsep D hD
    (fun a => f (fun j => (a j).1) (fun j => (a j).2))
  rw [sum_joint_cells_residues] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RestoredBulkSignedBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Return the signed bulk integral estimate to the original prime atoms -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem restored_bulk_prime_bound {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (M : ℕ) [NeZero M] (u v : J → C → ℝ)
    (hu : ∀ j c, 0 < u j c) (c₀ : C × (ZMod M)ˣ)
    (hP : ∀ j, primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ P)
    (hsep : ∀ j (c d : C × (ZMod M)ˣ), c ≠ d →
      ¬Nat.ModEq M c.2.val.val d.2.val.val ∨ v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (D : J → Finset ℕ)
    (hD : ∀ j, (∑ p ∈ primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ D j, (p : ℝ)⁻¹) ≠ 0)
    (K : BulkIntegrand J) (a : (J → (ZMod M)ˣ) → ℂ)
    (input : PublishedProgressionInput) (Q : ℕ) (err : (J → C) → (J → (ZMod M)ˣ) → ℝ)
    (herror : ∀ c z,
      ‖(∫ y, K y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j)))) -
        ∫ y, K y ∂Measure.pi (fun j => primeGiantMeasure input Q M
          (z j).val.val (u j (c j)) (v j (c j)))‖ ≤ err c z)
    (B : ℝ) :
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    let label := fun (x : J → P) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    ‖∑ z, ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun j => bulkCellMixture (Z j)
      (fun c => primeGiantMeasure input Q M (z j).val.val (u j c) (v j c)))‖ ≤ B →
    ‖∑ x : J → P,
      ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) *
        (a (fun j => (label x j).2) * K (fun j => Real.log (x j : ℕ)))‖ ≤
      B + (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * err c z := by
  dsimp only
  intro hmain
  let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
    (fun c => u j c.1) (fun c => v j c.1)
  let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
  have hZ (j : J) : 0 ≤ Z j := by dsimp only [Z]; positivity
  let μ := fun (c : J → C) (z : J → (ZMod M)ˣ) j =>
    primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j))
  let ν := fun (c : J → C) (z : J → (ZMod M)ˣ) j =>
    primeGiantMeasure input Q M (z j).val.val (u j (c j)) (v j (c j))
  let _ : ∀ c z j, IsFiniteMeasure (ν c z j) := fun c z j =>
    finite_primeGiantMeasure input Q M (z j).val.val _ _ (hu j (c j))
  let _ : ∀ (z : J → (ZMod M)ˣ) j c,
      IsFiniteMeasure (primeGiantMeasure input Q M (z j).val.val (u j c) (v j c)) :=
    fun z j c => finite_primeGiantMeasure input Q M (z j).val.val _ _ (hu j c)
  have hm := bulk_residue_mixture_integral Z hZ
    (fun z j c => primeGiantMeasure input Q M (z j).val.val (u j c) (v j c))
    (fun z => K.constMul (a z))
  rw [hm] at hmain
  have he := restored_bulk_residue_expansion P M u v c₀ hP hsep D hD
    (fun _ z => K.constMul (a z))
  exact (congrArg norm he).symm.trans_le
    (bulk_weighted_cell_bound K a Z hZ μ ν err herror B hmain)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeRestorationDifference
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deletion and collision errors for arbitrary signed prime observables -/

namespace Ostmann
open scoped Classical BigOperators

/-- Monotone restoration costs exactly the excess mass of the product law.
The observable can retain residue classes and every other arithmetic factor. -/
theorem finite_product_restoration_difference {J A : Type*} [Fintype J] [Fintype A]
    (μ ν : J → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hle : ∀ j a, μ j a ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (F : (J → A) → ℂ)
    (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x, ((∏ j, μ j (x j) : ℝ) : ℂ) * F x) -
      ∑ x, ((∏ j, ν j (x j) : ℝ) : ℂ) * F x‖ ≤
      B * ((∏ j, ∑ a, ν j a) - 1) := by
  have hp (x : J → A) : (∏ j, μ j (x j)) ≤ ∏ j, ν j (x j) :=
    Finset.prod_le_prod (fun j _ => hμ j (x j)) (fun j _ => hle j (x j))
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : J → A, B * ((∏ j, ν j (x j)) - ∏ j, μ j (x j)) := by
      apply norm_sum_le_of_le
      intro x _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hp x))]
      exact (mul_le_mul_of_nonneg_left (hF x) (sub_nonneg.mpr (hp x))).trans_eq
        (mul_comm _ _)
    _ = B * ((∏ j, ∑ a, ν j a) - 1) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib,
        ← Fintype.prod_sum, ← Fintype.prod_sum]
      simp only [hmass, Finset.prod_const_one]

/-- Restoring deleted atoms retains the old normalization. -/
theorem original_prime_restoration_difference {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hS : ∀ j, (∑ p ∈ S j \ D j, (p : ℝ)⁻¹) ≠ 0)
    (F : (J → P) → ℂ) (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    ‖(∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x) -
      ∑ x, ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) * F x‖ ≤
      B * ((∏ j, (1 + Z j * ∑ p ∈ S j ∩ D j, (p : ℝ)⁻¹)) - 1) := by
  dsimp only
  let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
  let ν := fun j (p : P) => if (p : ℕ) ∈ S j then Z j * (p : ℝ)⁻¹ else 0
  have hle (j : J) (p : P) : primeSubsetPrior P (S j \ D j) p ≤ ν j p := by
    by_cases hp : (p : ℕ) ∈ S j \ D j
    · have hps := (Finset.mem_sdiff.mp hp).1
      simp only [primeSubsetPrior, hp, hps, ite_true, if_true, ν, Z, div_eq_mul_inv]
      exact le_of_eq (mul_comm _ _)
    · simp only [primeSubsetPrior, hp, ite_false, if_false]
      dsimp only [ν]
      split_ifs <;> positivity
  have hm (j : J) : (∑ p : P, ν j p) =
      1 + Z j * ∑ p ∈ S j ∩ D j, (p : ℝ)⁻¹ := by
    have he : (∑ p : P, ν j p) = Z j * ∑ p ∈ S j, (p : ℝ)⁻¹ := by
      dsimp only [ν]
      rw [Finset.sum_coe_sort P (fun p : ℕ => if p ∈ S j then Z j * (p : ℝ)⁻¹ else 0)]
      rw [← Finset.sum_filter]
      have hfilter : P.filter (· ∈ S j) = S j := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun hp => ⟨hSP j hp, hp⟩⟩
      rw [hfilter, Finset.mul_sum]
    rw [he, ← Finset.sum_inter_add_sum_sdiff (S j) (D j) (fun p : ℕ => (p : ℝ)⁻¹), mul_add]
    have hz : Z j * (∑ p ∈ S j \ D j, (p : ℝ)⁻¹) = 1 := inv_mul_cancel₀ (hS j)
    rw [hz, add_comm]
  have h := finite_product_restoration_difference
    (fun j => primeSubsetPrior P (S j \ D j)) ν
    (fun j p => primeSubsetPrior_nonneg P (S j \ D j) p) hle
    (fun j => primeSubsetPrior_mass P (S j \ D j) (Finset.sdiff_subset.trans (hSP j)) (hS j)) F B hF
  simpa only [hm] using h

private theorem norm_le_from_restoration {x y z : ℂ} {A B C : ℝ}
    (hx : ‖x - y‖ ≤ B) (hy : ‖y - z‖ ≤ C) (hz : ‖z‖ ≤ A) :
    ‖x‖ ≤ A + B + C := by
  have hxy : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub y x
  have hyz : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub z y
  linarith

/-- The original injective expectation is bounded by the restored expectation,
with separate collision and deleted-atom costs. -/
theorem original_bulk_collision_restoration_bound {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hS : ∀ j, (∑ p ∈ S j \ D j, (p : ℝ)⁻¹) ≠ 0)
    (H T : ℝ) (hmass : ∀ j, (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hlow : ∀ j p, p ∈ S j \ D j → Real.exp T ≤ (p : ℝ))
    (F : (J → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B)
    (M : ℝ)
    (hmain : ‖∑ x, ((∏ j, (if (x j : ℕ) ∈ S j then
      (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹ * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) * F x‖ ≤ M) :
    ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) *
      (if Function.Injective x then F x else 0)‖ ≤
      M + B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) +
        B * ((∏ j, (1 + (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹ *
          ∑ p ∈ S j ∩ D j, (p : ℝ)⁻¹)) - 1) := by
  have hc := original_bulk_distinctness_removal_indexed P (fun j => S j \ D j)
    (fun j => Finset.sdiff_subset.trans (hSP j)) hS H T hmass hlow F B hB hF
  have hd := original_prime_restoration_difference P S D hSP hS F B hF
  dsimp only at hd
  have h := norm_le_from_restoration hc hd hmain
  simpa only [finite_univ_canonical] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalAbsoluteBulkBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic norm estimate under the original deleted prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem original_absolute_bulk_bound {J C : Type*} [Fintype J] [Fintype C]
    (primes : Finset ℕ) (M : ℕ) [NeZero M] (u v : J → C → ℝ)
    (hu : ∀ j c, 0 < u j c) (c₀ : C × (ZMod M)ˣ)
    (hP : ∀ j, primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
    (hsep : ∀ j (c d : C × (ZMod M)ˣ), c ≠ d →
      ¬Nat.ModEq M c.2.val.val d.2.val.val ∨ v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (deleted : J → Finset ℕ)
    (hdeleted : ∀ j, (∑ q ∈ primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ deleted j, (q : ℝ)⁻¹) ≠ 0)
    (K : BulkIntegrand J) (a : (J → (ZMod M)ˣ) → ℂ)
    (P : PublishedProgressionInput) (Q : ℕ) (W A : ℝ) (hW : 0 ≤ W) (hA0 : 0 ≤ A)
    (hK : ∀ y, ‖K y‖ ≤ W)
    (hA : ∀ y : J → ℝ, (∀ j, 0 ≤ y j) →
      (Fintype.card (J → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ z, ‖a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A)
    (err : (J → C) → (J → (ZMod M)ˣ) → ℝ)
    (herror : ∀ c z,
      ‖(∫ y, K y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j)))) -
        ∫ y, K y ∂Measure.pi (fun j => primeGiantMeasure P Q M
          (z j).val.val (u j (c j)) (v j (c j)))‖ ≤ err c z)
    (H T B : ℝ) (hB : 0 ≤ B) :
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
    let label := fun (x : J → primes) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    (∀ j, Z j ≤ Real.exp H) →
    (∀ j q, q ∈ S j \ deleted j → Real.exp T ≤ (q : ℝ)) →
    (∀ x : J → primes, ‖a (fun j => (label x j).2) * K (fun j => Real.log (x j : ℕ))‖ ≤ B) →
    ‖∑ x : J → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        (if Function.Injective x then a (fun j => (label x j).2) *
          K (fun j => Real.log (x j : ℕ)) else 0)‖ ≤
      (W * A) * 2 ^ Fintype.card J +
        (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * err c z +
        B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) +
        B * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) := by
  dsimp only
  intro hmass hZ hlow hnorm
  have hmain := restored_bulk_prime_bound primes M u v hu c₀ hP hsep deleted hdeleted
    K a P Q err herror ((W * A) * 2 ^ Fintype.card J)
    (bulk_absolute_mixture_bound P Q M u v hu _ (fun j => by positivity) hmass K a W A hW hA0 hK hA)
  exact original_bulk_collision_restoration_bound primes _ deleted hP hdeleted H T hZ hlow
    _ B hB hnorm _ hmain

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelNormBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp pattern kernel under its original bulk prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The original deleted prime kernel inherits its full arithmetic norm bound;
the approximation errors use the existing variation budget. -/
theorem PublishedProgressionInput.movingPattern_norm_kernel_bound
    (P : PublishedProgressionInput) {B C Cell : Type*} [Fintype Cell]
    {N n m r₀ : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (base : Fin (N + 1) → ℕ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
    (r : ℕ) [NeZero r]
    (p : Fin m → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (freq : ((TreeLeafIndex n × Fin m) → (ZMod r)ˣ) → ℂ)
    (spec : ∀ i, ((TreeLeafIndex n × Fin m) → (ZMod (p i))ˣ) → ℂ)
    (A : ℝ) (hA : 0 ≤ A) (hf : ∀ a, ‖freq a‖ ≤ A)
    (Q : ℕ) (hQ : 2 ≤ Q) (hMQ : (∏ i, bulkResidueModuli r p i) ≤ Q)
    (primes : Finset ℕ) (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
    (hu : ∀ j c, 1 ≤ u j c) (huv : ∀ j c, u j c ≤ v j c)
    (hshort : ∀ j c, v j c ≤ u j c + 1)
    (hmassCell : ∀ j c (a : (ZMod (∏ i, bulkResidueModuli r p i))ˣ),
      ∑ q ∈ primeLogCellSet (∏ i, bulkResidueModuli r p i) a.val.val (u j c) (v j c),
        (q : ℝ)⁻¹ ≤ 2)
    (c₀ : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hP : ∀ j, primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
    (hsep : ∀ j (c d : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ), c ≠ d →
      ¬Nat.ModEq (∏ i, bulkResidueModuli r p i) c.2.val.val d.2.val.val ∨
        v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hdeleted : ∀ j, (∑ q ∈ primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ deleted j, (q : ℝ)⁻¹) ≠ 0)
    (A₀ : ℝ) (hA₀ : 0 ≤ A₀) (H T : ℝ) (Bspec : Fin m → ℝ)
    (hBspec : ∀ i, 0 ≤ Bspec i) :
    let K := movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier
      (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
      φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    let W₀ := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2
    let M := ∏ i, bulkResidueModuli r p i
    let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
    let label := fun (x : (TreeLeafIndex n × Fin m) → primes) j => primeCellLabel M
      (fun c : Cell × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
    let err := fun c : (TreeLeafIndex n × Fin m) → Cell =>
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ j,
        bulkKernelPairComparisonBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
          bulkPrimeErrorFactor P Q (u j (c j))
    (∀ y : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ y j) →
      (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ z, ‖a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A₀) →
    (∀ i z, ‖spec i z‖ ≤ Bspec i) →
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    (∀ j, Z j ≤ Real.exp H) →
    (∀ j q, q ∈ S j \ deleted j → Real.exp T ≤ (q : ℝ)) →
    ‖∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        (if Function.Injective x then a (fun j => (label x j).2) *
          K (fun j => Real.log (x j : ℕ)) else 0)‖ ≤
      (W₀ * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
        (∏ j, Z j) * ∑ c : (TreeLeafIndex n × Fin m) → Cell, ∑ z, ‖a z‖ * err c +
        (A * (∏ i, Bspec i) * W) * (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 *
          Real.exp (H - T) +
        (A * (∏ i, Bspec i) * W) * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) := by
  intro K W W₀ M S Z label a err hlocal hspec hmass hZ hlow
  have hW : 0 ≤ W := sq_nonneg _
  have hk : ∀ z, ‖K z‖ ≤ W := movingPatternBulkIntegrand_norm e tierB tierC t small slot perm pattern hB htier
    (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
  have hk₀ : ∀ z, ‖K z‖ ≤ W₀ := movingPatternBulkIntegrand_norm_window e tierB tierC t small slot perm pattern hB htier
    (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U
  have herr (c : (TreeLeafIndex n × Fin m) → Cell)
      (z : (TreeLeafIndex n × Fin m) → (ZMod M)ˣ) :
      ‖(∫ y, K y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j)))) -
        ∫ y, K y ∂Measure.pi (fun j => primeGiantMeasure P Q M (z j).val.val (u j (c j)) (v j (c j)))‖ ≤
        err c :=
    P.movingPatternBulkIntegrand_comparison e tierB tierC t small slot perm pattern hB htier
      (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ
      hBφ hDφ hφ hlip hout L U hsmall hQ (fun _ => ∏ i, bulkResidueModuli r p i)
      (fun j => (z j).val.val) (fun j => u j (c j)) (fun j => v j (c j))
      (fun _ => Nat.pos_of_ne_zero (NeZero.ne _)) (fun _ => hMQ)
      (fun j => ZMod.val_coe_unit_coprime (z j)) (fun j => hu j (c j))
      (fun j => huv j (c j)) (fun j => hshort j (c j)) (fun j => hmassCell j (c j) (z j))
  have hn (x : (TreeLeafIndex n × Fin m) → primes) :
      ‖a (fun j => (label x j).2) * K (fun j => Real.log (x j : ℕ))‖ ≤ A * (∏ i, Bspec i) * W := by
    rw [norm_mul]
    apply mul_le_mul _ (hk _) (norm_nonneg _) (mul_nonneg hA (Finset.prod_nonneg fun i _ => hBspec i))
    change ‖freq _ * ∏ i, spec i _‖ ≤ _
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hf _) (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => hspec i _)) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hA
  have hb := original_absolute_bulk_bound primes M u v
    (fun j c => lt_of_lt_of_le zero_lt_one (hu j c)) c₀ hP hsep deleted hdeleted
    K a P Q W₀ A₀ (sq_nonneg _) hA₀ hk₀
    (by
      intro y hy
      have hy' := hlocal y hy
      simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at hy' ⊢
      exact hy') (fun c _ => err c) herr H T
    (A * (∏ i, Bspec i) * W)
    (mul_nonneg (mul_nonneg hA (Finset.prod_nonneg fun i _ => hBspec i)) hW)
  have hh := hb hmass hZ hlow hn
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at hh ⊢
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_UnitPrimeCellSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All unit residues preserve the original selected prime cells -/

namespace Ostmann
open scoped Classical

theorem unitPrimeCellLabel_lift {C : Type*} [Fintype C]
    (q : ℕ) [NeZero q] (u v : C → ℝ) (c₀ : C × (ZMod q)ˣ) (p : ℕ)
    (hp : p ∈ primeCellSupport q (fun c : C × (ZMod q)ˣ => c.2.val.val)
      (fun c => u c.1) (fun c => v c.1)) :
    (p : ZMod q) = ((primeCellLabel q (fun c : C × (ZMod q)ˣ => c.2.val.val)
      (fun c => u c.1) (fun c => v c.1) c₀ p).2 : ZMod q) := by
  have hc := primeCellLabel_mem q (fun c : C × (ZMod q)ˣ => c.2.val.val)
    (fun c => u c.1) (fun c => v c.1) c₀ p hp
  have he := (ZMod.natCast_eq_natCast_iff _ _ q).mpr (mem_primeLogCellSet_iff.mp hc).2.1
  simpa only [ZMod.natCast_zmod_val] using he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeBulkInsertion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical

theorem primeBulkValues_injective_iff {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) :
    Function.Injective (primeBulkValues base slot x ∘ slot) ↔ Function.Injective x := by
  simp only [Function.comp_apply, primeBulkValues_at, Function.Injective]
  constructor
  · intro h i j hij
    exact h (congrArg Subtype.val hij)
  · intro h i j hij
    exact h (Subtype.ext hij)

/-- Removing each fixed nonbulk prime from the old cells enforces all cross
inequalities, while permitting equal bulk draws until their original gate. -/
theorem primeBulkValues_cross_of_deleted {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (S deleted : J → Finset ℕ)
    (hx : ∀ j, (x j : ℕ) ∈ S j \ deleted j)
    (hdeleted : ∀ j i, i ∉ Set.range slot → base i ∈ deleted j) :
    ∀ i k, bulkIndexPredicate slot i ≠ bulkIndexPredicate slot k →
      primeBulkValues base slot x i ≠ primeBulkValues base slot x k := by
  have hc (j : J) (i : σ) (hi : i ∉ Set.range slot) :
      primeBulkValues base slot x (slot j) ≠ primeBulkValues base slot x i := by
    rw [primeBulkValues_at, primeBulkValues_off base slot x i hi]
    intro he
    exact (Finset.mem_sdiff.mp (hx j)).2 (he ▸ hdeleted j i hi)
  intro i k hik
  by_cases hi : i ∈ Set.range slot <;> by_cases hk : k ∈ Set.range slot
  · simp only [bulkIndexPredicate, hi, hk, decide_true, ne_eq, not_true_eq_false] at hik
  · obtain ⟨j, rfl⟩ := hi
    exact hc j k hk
  · obtain ⟨j, rfl⟩ := hk
    exact (hc j i hi).symm
  · simp only [bulkIndexPredicate, hi, hk, decide_false, ne_eq, not_true_eq_false] at hik

theorem primeBulkValues_outside_coprime {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (S deleted : J → Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hx : ∀ j, (x j : ℕ) ∈ S j \ deleted j)
    (outside : List ℕ) (hout : ∀ p ∈ outside, p.Prime)
    (hdeleted : ∀ j p, p ∈ outside → p ∈ deleted j) :
    ∀ j p, p ∈ outside → (primeBulkValues base slot x (slot j)).Coprime p := by
  intro j p hp
  rw [primeBulkValues_at]
  apply (Nat.coprime_primes (hP _ (x j).property) (hout p hp)).mpr
  intro he
  exact (Finset.mem_sdiff.mp (hx j)).2 (he ▸ hdeleted j p hp)

theorem primeBulkValues_cell_label {σ J Cell : Type*} [Fintype Cell] {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (q : ℕ) [NeZero q]
    (u v : J → Cell → ℝ) (c₀ : Cell × (ZMod q)ˣ) (deleted : J → Finset ℕ)
    (hx : ∀ j, (x j : ℕ) ∈ primeCellSupport q
      (fun c : Cell × (ZMod q)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) \ deleted j) :
    ∀ j, (primeBulkValues base slot x (slot j) : ZMod q) =
      ((primeCellLabel q (fun c : Cell × (ZMod q)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)).2 : ZMod q) := by
  intro j
  rw [primeBulkValues_at]
  exact unitPrimeCellLabel_lift q (u j) (v j) c₀ (x j) (Finset.mem_sdiff.mp (hx j)).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeBulk
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact selected-prime mean of the original pattern kernel -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hsmall hR hr hg in
/-- Removing the fixed nonbulk primes is sufficient for the supported
arithmetic identity. The averaging law and its normalizers remain unchanged. -/
theorem movingPatternPrimeBulkHaar_mean
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
    (c₀ : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (S deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hS : ∀ j, S j ⊆ primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1))
    (hdeleted : ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j)
    (hout : ∀ q ∈ outside, q.Prime)
    (hdeletedOut : ∀ j q, q ∈ outside → q ∈ deleted j) :
    let M := ∏ i, bulkResidueModuli r p i
    let label := fun (x : (TreeLeafIndex n × Fin m) → primes) j => primeCellLabel M
      (fun c : Cell × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    let K := movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier
      (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
      φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
    let a := fun z => frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
      F E (movingPatternFinBulkData e n m t small slot perm pattern) childBound R r P Q y
        (bulkResidueEquiv r p hc z).1 *
      ∏ i, frozenBulkSpectatorHaar base n m t (fun b => movingPatternFiniteSmall e n (small b))
        (movingPatternFiniteSamples e n pattern) (twist i) perm (g i) ((bulkResidueEquiv r p hc z).2 i)
    (∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
          childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U x) =
    ∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        (if Function.Injective x then a (fun j => (label x j).2) *
          K (fun j => Real.log (x j : ℕ)) else 0) := by
  intro M label K a
  apply Finset.sum_congr rfl
  intro x _
  by_cases hw : (∏ j, primeSubsetPrior primes (S j \ deleted j) (x j)) = 0
  · simp only [hw, Complex.ofReal_zero, zero_mul]
  · have hx (j) : (x j : ℕ) ∈ S j \ deleted j :=
      primeSubsetPrior_support primes _ _ (Finset.prod_ne_zero_iff.mp hw j (Finset.mem_univ j))
    have hxcell (j) : (x j : ℕ) ∈ primeCellSupport M
        (fun c : Cell × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) \ deleted j :=
      Finset.mem_sdiff.mpr ⟨hS j (Finset.mem_sdiff.mp (hx j)).1, (Finset.mem_sdiff.mp (hx j)).2⟩
    let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
    have hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
    have hv (i) (hi : i ∉ Set.range (movingPatternBulkEmbedding e slot)) : value i = base i :=
      primeBulkValues_off base (movingPatternBulkEmbedding e slot) x i hi
    have hz (j) : (value (movingPatternBulkEmbedding e slot j) : ZMod M) =
        ((label x j).2 : ZMod M) :=
      primeBulkValues_cell_label base (movingPatternBulkEmbedding e slot) x M u v c₀ deleted hxcell j
    have hid := movingPattern_bulk_supported_identity e tierB tierC t small slot perm pattern
      hsmall hB htier base value hv hp childBound pivotBound hfreq F E outside
      (primeBulkValues_cross_of_deleted base (movingPatternBulkEmbedding e slot) x S deleted hx hdeleted)
      (primeBulkValues_outside_coprime base (movingPatternBulkEmbedding e slot) x S deleted
        hprimes hx outside hout hdeletedOut)
      R r hR hr p hc g hg twist (fun j => (label x j).2) hz P Q y
      j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
    dsimp only at hid
    have hinj : Function.Injective (value ∘ movingPatternBulkEmbedding e slot) ↔
        Function.Injective x := primeBulkValues_injective_iff base (movingPatternBulkEmbedding e slot) x
    simp only [hinj] at hid
    apply congrArg (fun z : ℂ => ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) * z)
    unfold movingPatternPrimeBulkHaar
    rw [hid]
    split_ifs <;> simp only [primeBulkValues_at, K, a, value, mul_comm]

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedPrimeNormBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The norm estimate for the literal mixed-giant prime mean -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell : Type*} [Fintype Cell] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q Qfreq : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hsmall hB htier hR hr hg hV hBφ hDφ hφ hlip hφout j₀ in
/-- Transfer a retained arithmetic absolute mean to the original prime law,
with the sharp window factor in the main term and the established variation
budget in the approximation errors. -/
theorem PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound_oai
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (r₀ : ℕ) (hsmallLen : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (hy : 0 ≤ y) (hQ : 2 ≤ Q) (hMQ : (∏ i, bulkResidueModuli r p i) ≤ Q)
    (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
    (hu : ∀ j c, 1 ≤ u j c) (huv : ∀ j c, u j c ≤ v j c)
    (hshort : ∀ j c, v j c ≤ u j c + 1)
    (hmassCell : ∀ j c (a : (ZMod (∏ i, bulkResidueModuli r p i))ˣ),
      ∑ q ∈ primeLogCellSet (∏ i, bulkResidueModuli r p i) a.val.val (u j c) (v j c),
        (q : ℝ)⁻¹ ≤ 2)
    (c₀ : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hP : ∀ j, primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
    (hsep : ∀ j (c d : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ), c ≠ d →
      ¬Nat.ModEq (∏ i, bulkResidueModuli r p i) c.2.val.val d.2.val.val ∨
        v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hdeleted : ∀ j, (∑ q ∈ primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ deleted j, (q : ℝ)⁻¹) ≠ 0)
    (hdeletedBase : ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j)
    (hout : ∀ q ∈ outside, q.Prime) (hdeletedOut : ∀ j q, q ∈ outside → q ∈ deleted j)
    (Kspec : Fin m → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (A₀ : ℝ) (hA₀ : 0 ≤ A₀) (H T : ℝ) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
      F E data childBound R r P Qfreq y
    let spec := fun i => frozenBulkSpectatorHaar base n m t
      (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
      (twist i) perm (g i)
    let A := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    let W₀ := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2
    let M := ∏ i, bulkResidueModuli r p i
    let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
    let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
    let err := fun c : (TreeLeafIndex n × Fin m) → Cell =>
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ j,
        bulkKernelPairComparisonBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
          bulkPrimeErrorFactor P Q (u j (c j))
    (∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
      (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ w, ‖a w * ∏ j, pageGiantWeight P Q M (w j).val.val (z j)‖ ≤ A₀) →
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    (∀ j, Z j ≤ Real.exp H) →
    (∀ j q, q ∈ S j \ deleted j → Real.exp T ≤ (q : ℝ)) →
    ‖∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
          childBound pivotBound hfreq F E outside R r p g twist P Qfreq y ψ X lo hi hlo hhi φ G L U x‖ ≤
      (W₀ * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
        (∏ j, Z j) * ∑ c : (TreeLeafIndex n × Fin m) → Cell, ∑ z, ‖a z‖ * err c +
        (A * (∏ i, Kspec i ^ (2 ^ (n + 1))) * W) *
          (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 * Real.exp (H - T) +
        (A * (∏ i, Kspec i ^ (2 ^ (n + 1))) * W) *
          ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) := by
  intro data freq spec A W W₀ M S Z a err hlocal hmass hZ hlow
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hf (z) : ‖freq z‖ ≤ A :=
    frozenBulkFrequencyFactor_norm_le base (movingPatternBulkEmbedding e slot) outside
      F E data childBound R r P Qfreq y hy z
  have hspec (i) (z) : ‖spec i z‖ ≤ Kspec i ^ (2 ^ (n + 1)) :=
    frozenBulkSpectatorHaar_norm_le base n m t _ _ (twist i) perm (g i) (Kspec i)
      (hKspec i) (hgnorm i) z
  have heq := movingPatternPrimeBulkHaar_mean e tierB tierC t small slot perm pattern hsmall hB htier
    base primes hprimes hbase childBound pivotBound hfreq F E outside R r hR hr p hc g hg twist
    P Qfreq y j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
    u v c₀ S deleted (fun _ => Finset.Subset.refl _) hdeletedBase hout hdeletedOut
  dsimp only at heq
  rw [heq]
  have hb := P.movingPattern_norm_kernel_bound e tierB tierC t small slot perm pattern hB htier
    hsmallLen base childBound pivotBound j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ
    hφ hlip hφout L U r p hc freq spec A hA hf Q hQ hMQ primes u v hu huv hshort
    hmassCell c₀ hP hsep deleted hdeleted A₀ hA₀ H T (fun i => Kspec i ^ (2 ^ (n + 1)))
    (fun i => pow_nonneg (hKspec i) _)
  exact hb hlocal hspec hmass hZ hlow

end
end Ostmann

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound_oai.{u_1, u_2, u_3} := @OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound_oai.{u_1, u_2, u_3}
