-- Prove2me | solution 1 for OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:32:51.580141+00:00
-- url     : https://prove2.me/submissions/bc7e7805-cbb9-4c68-8d84-f4b0fed6b0f1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity of finite sequence norms and the small-remainder estimate. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem sum_rpow_le_rpow_sum (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {p : ℝ} (hp : 1 ≤ p) : (∑ i, x i ^ p) ≤ (∑ i, x i) ^ p := by
  have hp0 : 0 < p := by linarith
  have h (s : Finset ι) : (∑ i ∈ s, x i ^ p) ≤ (∑ i ∈ s, x i) ^ p := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow hp0.ne']
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc
        x i ^ p + ∑ j ∈ s, x j ^ p ≤ x i ^ p + (∑ j ∈ s, x j) ^ p :=
          add_le_add le_rfl ih
        _ ≤ (x i + ∑ j ∈ s, x j) ^ p :=
          Real.add_rpow_le_rpow_add (hx i) (Finset.sum_nonneg (fun j _ => hx j)) hp
  exact h Finset.univ

theorem sum_powers_exponent_comparison (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i, x i ^ q) ≤ (∑ i, x i ^ p) ^ (q / p) := by
  have h := sum_rpow_le_rpow_sum (fun i => x i ^ p)
    (fun i => Real.rpow_nonneg (hx i) p) ((le_div_iff₀ hp).2 (by simpa using hpq))
  have heq (i : ι) : (x i ^ p) ^ (q / p) = x i ^ q := by
    rw [← Real.rpow_mul (hx i)]
    congr 1
    field_simp
  simpa only [heq] using h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MixedNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mixed-norm comparisons for the diagonal Hilbert-valued extension. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem finite_minkowski (x : ι → κ → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ j, (∑ i, x i j) ^ p) ^ (1 / p) ≤
      ∑ i, (∑ j, x i j ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h (s : Finset ι) : (∑ j, (∑ i ∈ s, x i j) ^ p) ^ (1 / p) ≤
      ∑ i ∈ s, (∑ j, x i j ^ p) ^ (1 / p) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hm := Real.Lp_add_le_of_nonneg (Finset.univ : Finset κ)
        (f := fun j => x i j) (g := fun j => ∑ k ∈ s, x k j) hp
        (fun j _ => hx i j) (fun j _ => Finset.sum_nonneg (fun k _ => hx k j))
      exact hm.trans (add_le_add le_rfl ih)
  exact h Finset.univ

end LipschitzHilbert.PhaseCombinatorics

end

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

theorem scalar_finiteCubicVariation {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) = variationCube F N x := by
  classical
  have heq (p : Fin (N + 1) → Fin (N + 1)) :
      ENNReal.ofReal (if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) =
      if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0 := by
    split_ifs
    · rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    · exact ENNReal.ofReal_zero
  apply le_antisymm
  · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0)
    change ENNReal.ofReal (Finset.univ.sup' _ _) ≤ _
    rw [hp, heq]
    change (if Monotone p then ∑ i : Fin N,
      ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0) ≤
      Finset.univ.sup _
    exact Finset.le_sup (f := fun q : Fin (N + 1) → Fin (N + 1) =>
      if Monotone q then ∑ i : Fin N,
        ‖F (q i.succ) x - F (q i.castSucc) x‖ₑ ^ 3 else 0) (Finset.mem_univ p)
  · apply Finset.sup_le
    intro p _
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    exact Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N,
        ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) (Finset.mem_univ p)

/-- Minkowski in `ℓ^(3/2)` moves the Euclidean coordinates outside the
variation. The constant does not depend on the number of coordinates. -/
theorem euclidean_partition_variation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℝ κ) (N : ℕ)
    (p : Fin (N + 1) → Fin (N + 1)) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (2 / 3 : ℝ) ≤
      ∑ k, (∑ i : Fin N,
        ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 3) ^ (2 / 3 : ℝ) := by
  have hpow (a : ℝ) (ha : 0 ≤ a) : (a ^ 2) ^ (3 / 2 : ℝ) = a ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have h := PhaseCombinatorics.finite_minkowski
    (fun k (i : Fin N) => ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (by norm_num : (1 : ℝ) ≤ 3 / 2)
  norm_num only [one_div_div, div_one] at h
  have hsum (i : Fin N) :
      (∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2) ^ (3 / 2 : ℝ) =
      ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 := by
    have heq : ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2 =
        ∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    rw [← heq]
    exact hpow _ (norm_nonneg _)
  simpa only [hsum, hpow _ (norm_nonneg _)] using h

theorem euclidean_finiteCubicVariation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℝ κ) (N : ℕ) :
    (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      ∑ k, (finiteCubicVariation (fun n => F n k) N) ^ (2 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (2 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    apply (euclidean_partition_variation_le F N p).trans
    apply Finset.sum_le_sum
    intro k _
    exact Real.rpow_le_rpow (by positivity)
      (partition_le_finiteCubicVariation (fun n => F n k) N p hmono) (by norm_num)
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    exact Finset.sum_nonneg fun k _ =>
      Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional Hilbert consequence of the published scalar input. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

theorem measurable_variationCube {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n)) (N : ℕ) :
    Measurable (variationCube F N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : Ω) =>
    if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Measurable (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact Finset.measurable_sum _ fun i _ => ((hF _).sub (hF _)).enorm.pow_const _
    · simpa only [g, ite_eq_right hp] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))
  have hs (s : Finset (Fin (N + 1) → Fin (N + 1))) :
      Measurable (fun x => s.sup (fun p => g p x)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      simpa only [Finset.sup_insert] using (hg p).max ih
  exact hs Finset.univ

/-- No extra Hilbert-valued input is assumed: coordinatewise scalar
martingales and finite Minkowski give the same squared Lépingle constant. -/
theorem lepingle_euclidean_bound (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℝ κ),
          (∀ k, Martingale (fun n x => F n x k) ℱ μ) →
          (∀ k n, MemLp (fun x => F n x k) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^
              (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C, hC, hbound⟩ := hL
  refine ⟨C, hC, ?_⟩
  intro Ω m μ hμ κ inst ℱ F hF hF2 N
  have hmeas (k : κ) (n : ℕ) : Measurable (fun x => F n x k) :=
    ((hF k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have hpoint (x : Ω) :
      ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ) ≤
        ∑ k, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
    have h := ENNReal.ofReal_le_ofReal (euclidean_finiteCubicVariation_le (fun n => F n x) N)
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg
      (finiteCubicVariation_nonneg _ _) _)] at h
    refine h.trans_eq (Finset.sum_congr rfl fun k _ => ?_)
    rw [← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
      (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    rw [scalar_finiteCubicVariation (fun n x => F n x k) N x]
  calc
    _ ≤ ∫⁻ x, ∑ k, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) ∂μ :=
      lintegral_mono hpoint
    _ = ∑ k, ∫⁻ x, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) ∂μ := by
      apply lintegral_finsetSum
      intro k _
      exact (measurable_variationCube _ (hmeas k) N).pow_const _
    _ ≤ ∑ k, (C : ℝ≥0∞) ^ 2 * squareIntegral μ (fun x => F N x k) :=
      Finset.sum_le_sum fun k _ => hbound Ω m μ hμ ℱ _ (hF k) (hF2 k) N
    _ = (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
      rw [← Finset.mul_sum]
      congr 1
      unfold squareIntegral
      rw [← lintegral_finsetSum]
      · apply lintegral_congr
        intro x
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          EuclideanSpace.norm_sq_eq, ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
        simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      · intro k _
        exact (hmeas k N).enorm.pow_const _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComplexVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realification preserves the cubic variation and the terminal L² norm
of the complex Hilbert-valued packet sums. -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace LipschitzHilbert

theorem complexRealify_sub {κ : Type*} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    complexRealify (v - w) = complexRealify v - complexRealify w := by
  ext ⟨k,j⟩
  fin_cases j <;> simp [complexRealify]

theorem norm_complexRealify {κ : Type*} [Fintype κ] (v : EuclideanSpace ℂ κ) :
    ‖complexRealify v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simpa [complexRealify, Fin.sum_univ_two, Complex.normSq_apply, pow_two] using
    Complex.normSq_eq_norm_sq (v k)

theorem finiteCubicVariation_complexRealify {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    finiteCubicVariation (fun n => complexRealify (F n)) N = finiteCubicVariation F N := by
  have hnorm (i j : ℕ) : ‖complexRealify (F i) - complexRealify (F j)‖ = ‖F i - F j‖ := by
    rw [← complexRealify_sub, norm_complexRealify]
  unfold finiteCubicVariation
  simp_rw [hnorm]

/-- Apply the scalar published input to real and imaginary coordinates.
Realification preserves both norms exactly, so there is no dimension loss. -/
theorem lepingle_complex_bound (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℂ κ),
          (∀ k, Martingale (fun n x => (F n x k).re) ℱ μ) →
          (∀ k, Martingale (fun n x => (F n x k).im) ℱ μ) →
          (∀ k n, MemLp (fun x => (F n x k).re) 2 μ) →
          (∀ k n, MemLp (fun x => (F n x k).im) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^
              (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C,hC,hbound⟩ := lepingle_euclidean_bound hL
  refine ⟨C,hC,?_⟩
  intro Ω m μ hμ κ inst ℱ F hFre hFim hF2re hF2im N
  let H := fun n x => complexRealify (F n x)
  have hH (i : κ × Fin 2) : Martingale (fun n x => H n x i) ℱ μ := by
    rcases i with ⟨k,j⟩
    fin_cases j
    · simpa [H, complexRealify] using hFre k
    · simpa [H, complexRealify] using hFim k
  have hH2 (i : κ × Fin 2) (n : ℕ) : MemLp (fun x => H n x i) 2 μ := by
    rcases i with ⟨k,j⟩
    fin_cases j
    · simpa [H, complexRealify] using hF2re k n
    · simpa [H, complexRealify] using hF2im k n
  have h := hbound Ω m μ hμ (κ × Fin 2) ℱ H hH hH2 N
  simpa only [H, finiteCubicVariation_complexRealify, ← ofReal_norm, norm_complexRealify] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComplexVariationCoordinates
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent variation comparison for complex coordinates. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem complex_partition_variation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ)
    (p : Fin (N + 1) → Fin (N + 1)) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (2 / 3 : ℝ) ≤
      ∑ k, (∑ i : Fin N,
        ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 3) ^ (2 / 3 : ℝ) := by
  have hpow (a : ℝ) (ha : 0 ≤ a) : (a ^ 2) ^ (3 / 2 : ℝ) = a ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have h := PhaseCombinatorics.finite_minkowski
    (fun k (i : Fin N) => ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (by norm_num : (1 : ℝ) ≤ 3 / 2)
  norm_num only [one_div_div, div_one] at h
  have hsum (i : Fin N) :
      (∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2) ^ (3 / 2 : ℝ) =
      ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 := by
    have heq : ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2 =
        ∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    rw [← heq]
    exact hpow _ (norm_nonneg _)
  simpa only [hsum, hpow _ (norm_nonneg _)] using h

theorem complex_finiteCubicVariation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      ∑ k, (finiteCubicVariation (fun n => F n k) N) ^ (2 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (2 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    apply (complex_partition_variation_le F N p).trans
    apply Finset.sum_le_sum
    intro k _
    exact Real.rpow_le_rpow (by positivity)
      (partition_le_finiteCubicVariation (fun n => F n k) N p hmono) (by norm_num)
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    exact Finset.sum_nonneg fun k _ =>
      Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _


end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteEnergySchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted energy summation for the smooth/dyadic comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_sum_norm_square {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (v : ι → E) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    ‖∑ j, v j‖ ^ 2 ≤ (∑ j, w j) * ∑ j, ‖v j‖ ^ 2 / w j := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := w) (g := fun j => ‖v j‖ ^ 2 / w j) (r := fun j => ‖v j‖)
    (fun j _ => (hw j).le) (fun j _ => div_nonneg (sq_nonneg _) (hw j).le)
    (fun j _ => by rw [mul_div_cancel₀ _ (hw j).ne'])
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs

theorem weighted_integral_sum_square {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] (μ : Measure Ω)
    (F : ι → Ω → E) (hF : ∀ j, MemLp (F j) 2 μ)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    (∫ x, ‖∑ j, F j x‖ ^ 2 ∂μ) ≤
      (∑ j, w j) * ∑ j, (∫ x, ‖F j x‖ ^ 2 ∂μ) / w j := by
  have hsum : MemLp (fun x => ∑ j, F j x) 2 μ := by
    simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun j _ => hF j)
  have hint (j : ι) : Integrable (fun x => ‖F j x‖ ^ 2 / w j) μ :=
    ((hF j).integrable_norm_pow (by decide : 2 ≠ 0)).div_const _
  calc
    _ ≤ ∫ x, (∑ j, w j) * ∑ j, ‖F j x‖ ^ 2 / w j ∂μ :=
      integral_mono (hsum.integrable_norm_pow (by decide : 2 ≠ 0))
        ((integrable_finsetSum _ (fun j _ => hint j)).const_mul _)
        (fun x => weighted_sum_norm_square (fun j => F j x) w hw)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact integral_div _ _

theorem finite_energy_schur {Ω ι κ E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [NormedAddCommGroup E]
    (μ : Measure Ω) (F : ι → κ → Ω → E)
    (hF : ∀ i j, MemLp (F i j) 2 μ) (a : ι → κ → ℝ)
    (ha : ∀ i j, 0 < a i j) (b : κ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {R C : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, a i j ≤ R) (hcol : ∀ j, ∑ i, a i j ≤ C)
    (hbound : ∀ i j, (∫ x, ‖F i j x‖ ^ 2 ∂μ) ≤ a i j ^ 2 * b j) :
    (∑ i, ∫ x, ‖∑ j, F i j x‖ ^ 2 ∂μ) ≤ R * C * ∑ j, b j := by
  have hcell (i : ι) (j : κ) :
      (∫ x, ‖F i j x‖ ^ 2 ∂μ) / a i j ≤ a i j * b j := by
    apply (div_le_iff₀ (ha i j)).mpr
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hbound i j
  have hrowbound (i : ι) : (∫ x, ‖∑ j, F i j x‖ ^ 2 ∂μ) ≤
      R * ∑ j, a i j * b j := by
    calc
      _ ≤ (∑ j, a i j) * ∑ j, (∫ x, ‖F i j x‖ ^ 2 ∂μ) / a i j :=
        weighted_integral_sum_square μ (F i) (hF i) (a i) (ha i)
      _ ≤ (∑ j, a i j) * ∑ j, a i j * b j :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hcell i j))
          (Finset.sum_nonneg (fun j _ => (ha i j).le))
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (ha i j).le (hb j)))
  calc
    _ ≤ ∑ i, R * ∑ j, a i j * b j := Finset.sum_le_sum (fun i _ => hrowbound i)
    _ = R * ∑ j, (∑ i, a i j) * b j := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ R * ∑ j, C * b j := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (hb j))) hR
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzBandEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two band-energy inequalities used by the actual cell-average
comparison, proved from Mathlib's Schwartz Plancherel theorem. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem schwartz_fourier_deriv (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ f) ξ =
      (2 * Real.pi * Complex.I * ξ) • 𝓕 f ξ := by
  exact congrFun (Real.fourier_deriv f.integrable f.differentiable
    (SchwartzMap.derivCLM ℂ ℂ f).integrable) ξ

theorem norm_fourier_deriv_coefficient (ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ : ℂ)‖ = 2 * Real.pi * |ξ| := by
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]

theorem schwartz_band_derivative_upper (f : SchwartzMap ℝ ℂ) {R : ℝ} (_hR : 0 ≤ R)
    (hband : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0) :
    (∫ x, ‖deriv f x‖ ^ 2) ≤ (2 * Real.pi * R) ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hpoint (ξ : ℝ) : ‖𝓕 df ξ‖ ^ 2 ≤ (2 * Real.pi * R) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
    by_cases hξ : |ξ| ≤ R
    · rw [schwartz_fourier_deriv, norm_smul, norm_fourier_deriv_coefficient, mul_pow]
      gcongr
    · rw [schwartz_fourier_deriv, hband ξ (lt_of_not_ge hξ)]
      simp
  calc
    _ = ∫ ξ, ‖𝓕 df ξ‖ ^ 2 := by
      simpa only [df, SchwartzMap.derivCLM_apply] using
        (SchwartzMap.integral_norm_sq_fourier df).symm
    _ ≤ ∫ ξ, (2 * Real.pi * R) ^ 2 * ‖𝓕 f ξ‖ ^ 2 :=
      integral_mono (((𝓕 df).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0))
        ((((𝓕 f).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul _) hpoint
    _ = _ := by rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier]

theorem schwartz_band_derivative_lower (f : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 < r)
    (hband : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0) :
    (2 * Real.pi * r) ^ 2 * (∫ x, ‖f x‖ ^ 2) ≤ ∫ x, ‖deriv f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hpoint (ξ : ℝ) : (2 * Real.pi * r) ^ 2 * ‖𝓕 f ξ‖ ^ 2 ≤ ‖𝓕 df ξ‖ ^ 2 := by
    by_cases hξ : r ≤ |ξ|
    · rw [schwartz_fourier_deriv, norm_smul, norm_fourier_deriv_coefficient, mul_pow]
      simp only [mul_pow]
      gcongr
    · rw [schwartz_fourier_deriv, hband ξ (lt_of_not_ge hξ)]
      simp
  calc
    _ = ∫ ξ, (2 * Real.pi * r) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
      rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier]
    _ ≤ ∫ ξ, ‖𝓕 df ξ‖ ^ 2 :=
      integral_mono ((((𝓕 f).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul _)
        (((𝓕 df).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)) hpoint
    _ = _ := by
      simpa only [df, SchwartzMap.derivCLM_apply] using SchwartzMap.integral_norm_sq_fourier df

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

theorem envelope_synthesis_square {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ι → ℂ) (f : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    {C D : ℝ} (hD : 0 ≤ D) (hover : ∑ i, w i ≤ D)
    (henv : ∀ i, ‖f i‖ ≤ C * w i) :
    ‖∑ i, c i • f i‖ ^ 2 ≤ D * C ^ 2 * ∑ i, ‖c i‖ ^ 2 * w i := by
  have hterm (i : ι) : ‖c i • f i‖ ^ 2 / w i ≤ C ^ 2 * (‖c i‖ ^ 2 * w i) := by
    rw [norm_smul, mul_pow]
    apply (div_le_iff₀ (hw i)).mpr
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (henv i) 2
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖c i‖)
    nlinarith
  calc
    _ ≤ (∑ i, w i) * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      weighted_sum_norm_square _ w hw
    _ ≤ D * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      mul_le_mul_of_nonneg_right hover (Finset.sum_nonneg (fun i _ =>
        div_nonneg (sq_nonneg _) (hw i).le))
    _ ≤ D * ∑ i, C ^ 2 * (‖c i‖ ^ 2 * w i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) hD
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

theorem packetSynthesis_fourier {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (packetSynthesis c f) ξ = ∑ i, c i * 𝓕 (f i) ξ := by
  have heq : (𝓕 (packetSynthesis c f) : SchwartzMap ℝ ℂ) = ∑ i, c i • 𝓕 (f i) := by
    rw [packetSynthesis, fourier_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact fourier_smul (c i) (f i)
  rw [heq]
  simp only [sum_apply, smul_apply, smul_eq_mul]

theorem packetSynthesis_fourier_zero {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (ξ : ℝ)
    (hf : ∀ i, 𝓕 (f i) ξ = 0) : 𝓕 (packetSynthesis c f) ξ = 0 := by
  rw [packetSynthesis_fourier]
  simp only [hf, mul_zero, Finset.sum_const_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteMeasureLepingle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a finite line cell, apply the published probability-space
inequality, then restore its unnormalized measure without loss. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem martingale_smul_measure {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m}
    {F : ℕ → Ω → ℝ} (hF : Martingale F ℱ μ) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Martingale F ℱ (c • μ) := by
  have : IsFiniteMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top _ _)⟩
  apply martingale_of_setIntegral_eq_succ hF.stronglyAdapted
    (fun n => (hF.integrable n).smul_measure hc)
  intro n s hs
  simp only [Measure.restrict_smul, integral_smul_measure]
  rw [hF.setIntegral_eq (Nat.le_succ n) hs]

/-- The scalar probability-space theorem gives the same constant on
every finite measure. This is the normalization used on coarsest line cells. -/
theorem lepingle_complex_finite_measure (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsFiniteMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℂ κ),
          (∀ k, Martingale (fun n x => (F n x k).re) ℱ μ) →
          (∀ k, Martingale (fun n x => (F n x k).im) ℱ μ) →
          (∀ k n, MemLp (fun x => (F n x k).re) 2 μ) →
          (∀ k n, MemLp (fun x => (F n x k).im) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C,hC,hbound⟩ := lepingle_complex_bound hL
  refine ⟨C,hC,?_⟩
  intro Ω m μ hμ κ inst ℱ F hRe hIm hRe2 hIm2 N
  let : IsFiniteMeasure μ := hμ
  by_cases hzero : μ = 0
  · simp [hzero]
  have hmass : μ Set.univ ≠ 0 := fun hz => hzero (Measure.measure_univ_eq_zero.mp hz)
  have htop : μ Set.univ ≠ ∞ := (measure_lt_top μ Set.univ).ne
  let c := (μ Set.univ)⁻¹
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.mpr htop
  have hctop : c ≠ ∞ := ENNReal.inv_ne_top.mpr hmass
  have hprob : IsProbabilityMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass htop⟩
  have h := hbound Ω m (c • μ) hprob κ ℱ F
    (fun k => martingale_smul_measure (hRe k) c hctop)
    (fun k => martingale_smul_measure (hIm k) c hctop)
    (fun k n => (hRe2 k n).smul_measure hctop)
    (fun k n => (hIm2 k n).smul_measure hctop) N
  simp only [lintegral_smul_measure, smul_eq_mul] at h
  rw [← mul_assoc, mul_comm ((C : ℝ≥0∞) ^ 2) c, mul_assoc] at h
  have hcancel := mul_le_mul_right h c⁻¹
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul] using hcancel

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricScaleWeights
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform row and column bounds for the actual geometric scale kernel. -/

open scoped BigOperators

noncomputable section

namespace LipschitzHilbert

theorem sum_half_powers_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
  have heq : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) =
      2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]

theorem sum_half_distance_le_four (N i : ℕ) :
    (∑ j : Fin N, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 4 := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => j.val ≤ i)
  let t := Finset.univ.filter (fun j : Fin N => ¬j.val ≤ i)
  have hs : (∑ j ∈ s, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 2 := by
    have hinj : Set.InjOn (fun j : Fin N => i - j.val) s := by
      intro j hj k hk heq
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      change i - j.val = i - k.val at heq
      apply Fin.ext
      omega
    have hmap : s.image (fun j : Fin N => i - j.val) ⊆
        Finset.range (i + N + 1) := by
      intro n hn
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
      simp only [Finset.mem_range]
      omega
    have h := OAI.sum_le_sum_of_injOn (fun j : Fin N => i - j.val) hinj hmap
      (s := s) (t := Finset.range (i + N + 1))
      (f := fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
      (g := fun n => (1 / 2 : ℝ) ^ n)
      (fun j hj => by rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hj).2])
      (fun n _ _ => pow_nonneg (by norm_num) n)
    exact h.trans (sum_half_powers_le_two _)
  have ht : (∑ j ∈ t, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 2 := by
    have hinj : Set.InjOn (fun j : Fin N => j.val - i) t := by
      intro j hj k hk heq
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      change j.val - i = k.val - i at heq
      apply Fin.ext
      omega
    have hmap : t.image (fun j : Fin N => j.val - i) ⊆
        Finset.range (i + N + 1) := by
      intro n hn
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
      simp only [Finset.mem_range]
      have := j.isLt
      omega
    have h := OAI.sum_le_sum_of_injOn (fun j : Fin N => j.val - i) hinj hmap
      (s := t) (t := Finset.range (i + N + 1))
      (f := fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
      (g := fun n => (1 / 2 : ℝ) ^ n)
      (fun j hj => by
        rw [Nat.dist_eq_sub_of_le (by have := (Finset.mem_filter.mp hj).2; omega)])
      (fun n _ _ => pow_nonneg (by norm_num) n)
    exact h.trans (sum_half_powers_le_two _)
  have heq := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin N => j.val ≤ i) (fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
  change (∑ j ∈ s, (1 / 2 : ℝ) ^ Nat.dist i j.val) +
    (∑ j ∈ t, (1 / 2 : ℝ) ^ Nat.dist i j.val) = _ at heq
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalOscillation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual maxima of subinterval sums on residual segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem intervalOscillation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) : 0 ≤ intervalOscillation F N a b := by
  classical
  apply Finset.le_sup'_of_le (b := ((0 : Fin (N + 1)), (0 : Fin (N + 1))))
    (f := fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0) (Finset.mem_univ _)
  split_ifs <;> positivity

theorem exists_intervalOscillation_eq {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) :
    ∃ c d : ℕ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ intervalOscillation F N a b = ‖F d - F c‖ := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0)
  change intervalOscillation F N a b = _ at hq
  by_cases h : a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b
  · rw [ite_eq_left h] at hq
    exact ⟨q.1, q.2, h.1, h.2.1, h.2.2, hq⟩
  · rw [ite_eq_right h] at hq
    exact ⟨a, a, le_rfl, le_rfl, hab, by simpa only [sub_self, norm_zero] using hq⟩

theorem increment_le_intervalOscillation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b c d : ℕ) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hb : b ≤ N) :
    ‖F d - F c‖ ≤ intervalOscillation F N a b := by
  classical
  let q : Fin (N + 1) × Fin (N + 1) :=
    (⟨c, by omega⟩, ⟨d, by omega⟩)
  have h := Finset.le_sup'
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0) (Finset.mem_univ q)
  simpa only [intervalOscillation, q,
    ite_eq_left (show a ≤ c ∧ c ≤ d ∧ d ≤ b from ⟨hac, hcd, hdb⟩)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalPoincare
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
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

theorem integral_square_le_mass_mul_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (g : Ω → ℝ)
    (hg : MemLp g 2 μ) (hgn : 0 ≤ᵐ[μ] g) :
    (∫ x, g x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, g x ^ 2 ∂μ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ)) (g := g) (by filter_upwards; norm_num) hgn
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
    (by simpa using hg)
  simp only [one_mul, integral_const, smul_eq_mul, mul_one, Real.rpow_two,
    one_pow] at h
  have hsq := pow_le_pow_left₀ (integral_nonneg_of_ae hgn) h 2
  have heq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  rwa [mul_pow, heq _ measureReal_nonneg, heq _ (integral_nonneg fun _ => sq_nonneg _)] at hsq

theorem interval_pair_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv f t‖ ^ 2 := by
  have hd1 : IntegrableOn (fun t => ‖deriv f t‖) (Icc a b) := hd.norm.integrable (by norm_num)
  have htotal : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      ‖f v - f u‖ ≤ ∫ t in Icc a b, ‖deriv f t‖ := by
    intro u hu v hv huv
    have hsub : Icc u v ⊆ Icc a b := fun t ht => ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩
    have hraw := norm_sub_le_integral_of_norm_deriv_le_of_le huv
      (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hf t (hsub ⟨ht.1.le,ht.2.le⟩)).differentiableWithinAt)
      (B := fun t => ‖deriv f t‖) (by filter_upwards; intros; rfl)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr (hd1.mono_set hsub))
    refine hraw.trans ?_
    rw [intervalIntegral.integral_of_le huv]
    exact setIntegral_mono_set hd1 (by filter_upwards with t; exact norm_nonneg _)
      (Filter.Eventually.of_forall fun t ht => hsub ⟨ht.1.le,ht.2⟩)
  have hnorm : ‖f x - f y‖ ≤ ∫ t in Icc a b, ‖deriv f t‖ := by
    rcases le_total x y with hxy | hyx
    · rw [norm_sub_rev]
      exact htotal x hx y hy hxy
    · exact htotal y hy x hx hyx
  have hcauchy := integral_square_le_mass_mul_square (volume.restrict (Icc a b))
    (fun t => ‖deriv f t‖) hd.norm (by filter_upwards with t; exact norm_nonneg _)
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hmass] at hcauchy
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcauchy

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

/-- Pointwise Poincaré on one interval, with the actual integral mean. -/
theorem interval_mean_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2 ≤
      (b - a) * ∫ y in Icc a b, ‖deriv f y‖ ^ 2 := by
  let energy := (b - a) * ∫ y in Icc a b, ‖deriv f y‖ ^ 2
  have he : 0 ≤ energy := mul_nonneg (sub_nonneg.mpr hab.le)
    (integral_nonneg fun _ => sq_nonneg _)
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hcont : ContinuousOn f (Icc a b) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hbound : ∀ᵐ y ∂volume.restrict (Icc a b), ‖f x - f y‖ ≤ Real.sqrt energy := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt he]
    exact interval_pair_energy f hab.le hf hd hx hy
  have h := norm_sub_mean_le (volume.restrict (Icc a b)) f hcont.integrableOn_Icc
    (by rw [hmass]; exact sub_pos.mpr hab) (f x) (Real.sqrt energy) hbound
  rw [hmass] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [Real.sq_sqrt he] at hsq

/-- Integrated Poincaré with the interval length squared, independent
of the dimension of the Hilbert packet space. -/
theorem interval_poincare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    (∫ x in Icc a b, ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Icc a b, ‖deriv f x‖ ^ 2 := by
  have hcont : ContinuousOn f (Icc a b) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have herr : IntegrableOn
      (fun x => ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2) (Icc a b) volume :=
    ((hcont.sub continuousOn_const).norm.pow 2).integrableOn_Icc
  have h := integral_mono_ae herr (integrable_const
    ((b - a) * ∫ x in Icc a b, ‖deriv f x‖ ^ 2))
    ((ae_restrict_mem measurableSet_Icc).mono fun x hx => interval_mean_energy f hab hf hd hx)
  rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] at h
  simpa only [pow_two, mul_assoc] using h

theorem interval_poincare_Ico {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    (∫ x in Ico a b, ‖f x - (b - a)⁻¹ • ∫ y in Ico a b, f y‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Ico a b, ‖deriv f x‖ ^ 2 := by
  simpa only [integral_Icc_eq_integral_Ico] using interval_poincare f hab hf hd

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

theorem finiteCubicVariation_congr {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) (h : ∀ i, i ≤ N → F i = G i) :
    finiteCubicVariation F N = finiteCubicVariation G N := by
  classical
  unfold finiteCubicVariation
  congr 1
  funext p
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [h (p i.succ) (by have := (p i.succ).isLt; omega),
    h (p i.castSucc) (by have := (p i.castSucc).isLt; omega)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationMeasurable
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable common exceptional set for all selected scale intervals. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem measurable_finiteCubicVariation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (F : ℕ → Ω → E) (hF : ∀ n, Measurable (F n)) (N : ℕ) :
    Measurable (fun x => finiteCubicVariation (fun n => F n x) N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : Ω) =>
    if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Measurable (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact Finset.measurable_sum _ fun i _ => ((hF _).sub (hF _)).norm.pow_const _
    · simpa only [g, ite_eq_right hp] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  have hs := Finset.measurable_sup' Finset.univ_nonempty (fun p _ => hg p)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [finiteCubicVariation, g, Finset.sup'_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationPerturbation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-summable error in the smooth/dyadic comparison controls
its entire cubic variation, uniformly in the number of scales. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem cubic_sum_rpow_le_square_sum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ 3) ^ (2 / 3 : ℝ) ≤ ∑ i, a i ^ 2 := by
  have h := PhaseCombinatorics.sum_powers_exponent_comparison a ha
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
  norm_num only [Real.rpow_ofNat] at h
  have hpow := Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => pow_nonneg (ha i) 3)
    h (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => sq_nonneg (a i))] at hpow
  norm_num at hpow ⊢
  exact hpow

theorem monotone_partition_square_sum {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2) ≤
      4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun i : Fin N => p i.castSucc < p i.succ)
  have hstep (i j : Fin N) (hij : i < j) : p i.succ ≤ p j.castSucc :=
    hp (by simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
      (show i.val + 1 ≤ j.val by omega))
  have hleft : Set.InjOn (fun i : Fin N => p i.castSucc) s := by
    intro i hi j hj heq
    change p i.castSucc = p j.castSucc at heq
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((not_lt_of_ge (hstep i j hij)) (by simpa only [heq] using hi'))
    · exact hij
    · exact False.elim ((not_lt_of_ge (hstep j i hij)) (by simpa only [heq] using hj'))
  have hright : Set.InjOn (fun i : Fin N => p i.succ) s := by
    intro i hi j hj heq
    change p i.succ = p j.succ at heq
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((not_lt_of_ge (hstep i j hij)) (by simpa only [heq] using hj'))
    · exact hij
    · exact False.elim ((not_lt_of_ge (hstep j i hij)) (by simpa only [heq] using hi'))
  have hsumleft : (∑ i ∈ s, ‖F (p i.castSucc)‖ ^ 2) ≤
      ∑ k : Fin (N + 1), ‖F k‖ ^ 2 :=
    OAI.sum_le_sum_of_injOn (fun i : Fin N => p i.castSucc) hleft
      (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)
  have hsumright : (∑ i ∈ s, ‖F (p i.succ)‖ ^ 2) ≤
      ∑ k : Fin (N + 1), ‖F k‖ ^ 2 :=
    OAI.sum_le_sum_of_injOn (fun i : Fin N => p i.succ) hright
      (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)
  have hrestrict : (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2) =
      ∑ i ∈ s, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hle : p i.castSucc ≤ p i.succ := hp (Fin.castSucc_le_succ i)
    have heq : p i.castSucc = p i.succ := le_antisymm hle
      (le_of_not_gt (by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi))
    simp [heq]
  rw [hrestrict]
  calc
    _ ≤ ∑ i ∈ s, 2 * (‖F (p i.succ)‖ ^ 2 + ‖F (p i.castSucc)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hnorm := norm_sub_le (F (p i.succ)) (F (p i.castSucc))
      have hsquare := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnorm
      nlinarith [sq_nonneg (‖F (p i.succ)‖ - ‖F (p i.castSucc)‖)]
    _ = 2 * ((∑ i ∈ s, ‖F (p i.succ)‖ ^ 2) +
        ∑ i ∈ s, ‖F (p i.castSucc)‖ ^ 2) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by linarith

theorem finiteCubicVariation_le_square_energy {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) :
    (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (2 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    exact (cubic_sum_rpow_le_square_sum _ (fun _ => norm_nonneg _)).trans
      (monotone_partition_square_sum F N p hmono)
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    positivity

theorem finiteCubicVariation_add_rpow {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun n => F n + G n) N) ^ (1 / 3 : ℝ) ≤
      (finiteCubicVariation F N) ^ (1 / 3 : ℝ) +
        (finiteCubicVariation G N) ^ (1 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖(F (p i.succ) + G (p i.succ)) -
        (F (p i.castSucc) + G (p i.castSucc))‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (1 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    calc
      _ ≤ (∑ i : Fin N, (‖F (p i.succ) - F (p i.castSucc)‖ +
          ‖G (p i.succ) - G (p i.castSucc)‖) ^ 3) ^ (1 / 3 : ℝ) := by
        apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [add_sub_add_comm]
        exact norm_add_le _ _
      _ ≤ (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (1 / 3 : ℝ) +
          (∑ i : Fin N, ‖G (p i.succ) - G (p i.castSucc)‖ ^ 3) ^ (1 / 3 : ℝ) := by
        simpa only [Real.rpow_ofNat] using Real.Lp_add_le_of_nonneg
          (Finset.univ : Finset (Fin N)) (by norm_num : (1 : ℝ) ≤ 3)
          (f := fun i => ‖F (p i.succ) - F (p i.castSucc)‖)
          (g := fun i => ‖G (p i.succ) - G (p i.castSucc)‖)
          (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      _ ≤ _ := add_le_add
        (Real.rpow_le_rpow (by positivity) (partition_le_finiteCubicVariation F N p hmono)
          (by norm_num))
        (Real.rpow_le_rpow (by positivity) (partition_le_finiteCubicVariation G N p hmono)
          (by norm_num))
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)]
    exact add_nonneg (Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _)
      (Real.rpow_nonneg (finiteCubicVariation_nonneg G N) _)

theorem finiteCubicVariation_add_square {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun n => F n + G n) N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation F N) ^ (2 / 3 : ℝ) +
        2 * (finiteCubicVariation G N) ^ (2 / 3 : ℝ) := by
  have h := finiteCubicVariation_add_rpow F G N
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _) h 2
  have heq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 3 : ℝ)) ^ 2 = a ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hcross := sq_nonneg ((finiteCubicVariation F N) ^ (1 / 3 : ℝ) -
    (finiteCubicVariation G N) ^ (1 / 3 : ℝ))
  rw [sub_sq, heq _ (finiteCubicVariation_nonneg F N),
    heq _ (finiteCubicVariation_nonneg G N)] at hcross
  rw [heq _ (finiteCubicVariation_nonneg _ _)] at hsq
  rw [add_sq, heq _ (finiteCubicVariation_nonneg F N),
    heq _ (finiteCubicVariation_nonneg G N)] at hsq
  linarith

/-- The manuscript's smooth partial sums are a dyadic martingale plus
the square-summable comparison error. No scale-count factor occurs. -/
theorem finiteCubicVariation_comparison {E : Type*} [NormedAddCommGroup E]
    (P M : ℕ → E) (N : ℕ) :
    (finiteCubicVariation P N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation M N) ^ (2 / 3 : ℝ) +
        8 * ∑ k : Fin (N + 1), ‖P k - M k‖ ^ 2 := by
  have heq : (fun n => M n + (P n - M n)) = P := by funext n; abel
  have h := finiteCubicVariation_add_square M (fun n => P n - M n) N
  rw [heq] at h
  exact h.trans (add_le_add le_rfl
    (by linarith [finiteCubicVariation_le_square_energy (fun n => P n - M n) N]))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PerturbedLepingle
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lépingle plus the actual square-summable smooth/dyadic error. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem lintegral_finiteCubicVariation_comparison {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (P M : ℕ → Ω → E)
    (hP : ∀ n, Measurable (P n)) (hM : ∀ n, Measurable (M n)) (N : ℕ) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => P n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) ∂μ) +
        8 * ∑ k : Fin (N + 1), ∫⁻ x, ‖P k x - M k x‖ₑ ^ 2 ∂μ := by
  have hpoint (x : Ω) :
      ENNReal.ofReal (finiteCubicVariation (fun n => P n x) N) ^ (2 / 3 : ℝ) ≤
        2 * ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) +
          8 * ∑ k : Fin (N + 1), ‖P k x - M k x‖ₑ ^ 2 := by
    have h := ENNReal.ofReal_le_ofReal
      (finiteCubicVariation_comparison (fun n => P n x) (fun n => M n x) N)
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _)) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)] at h
    simpa only [← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
      (by norm_num : (0 : ℝ) ≤ 2 / 3), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h
  calc
    _ ≤ ∫⁻ x, 2 * ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) +
        8 * ∑ k : Fin (N + 1), ‖P k x - M k x‖ₑ ^ 2 ∂μ := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left]
      · rw [lintegral_const_mul, lintegral_const_mul, lintegral_finsetSum]
        · intro k _
          exact ((hP _).sub (hM _)).enorm.pow_const _
        · exact Finset.measurable_sum _ fun k _ => ((hP _).sub (hM _)).enorm.pow_const _
        · exact (measurable_finiteCubicVariation M hM N).ennreal_ofReal.pow_const _
      · exact measurable_const.mul
          ((measurable_finiteCubicVariation M hM N).ennreal_ofReal.pow_const _)

theorem measurable_complex_martingale {Ω κ : Type*} [m : MeasurableSpace Ω] [Fintype κ]
    {μ : Measure Ω} {ℱ : Filtration ℕ m} {M : ℕ → Ω → EuclideanSpace ℂ κ}
    (hRe : ∀ k, Martingale (fun n x => (M n x k).re) ℱ μ)
    (hIm : ∀ k, Martingale (fun n x => (M n x k).im) ℱ μ) (n : ℕ) :
    Measurable (M n) := by
  have hre (k : κ) : Measurable (fun x => (M n x k).re) :=
    ((hRe k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have him (k : κ) : Measurable (fun x => (M n x k).im) :=
    ((hIm k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have hc (k : κ) : Measurable (fun x => M n x k) := by
    have h := (Complex.continuous_ofReal.measurable.comp (hre k)).add
      ((Complex.continuous_ofReal.measurable.comp (him k)).mul_const Complex.I)
    change Measurable (fun x => ((M n x k).re : ℂ) + (M n x k).im * Complex.I) at h
    simpa only [Complex.re_add_im] using h
  exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr hc)

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

theorem average_memLp (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 μ) (n : ℕ) : MemLp (g.average μ f n) 2 μ :=
  hf.condExp (by norm_num)

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ComplexLineAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex Hilbert-valued averages on the actual finite line grid. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem lintegral_square_condExp_le {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (m' : MeasurableSpace Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫⁻ x, ‖μ[f | m'] x‖ₑ ^ 2 ∂μ) ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have h := ENNReal.rpow_le_rpow
    (eLpNorm_condExp_le_eLpNorm (m := m') (m0 := m) (μ := μ) f
      (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (by norm_num : (0 : ℝ) ≤ 2)
  have hleft := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (f := μ[f | m']) (μ := μ)
  have hright := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (f := f) (μ := μ)
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h hleft hright
  rwa [hleft, hright] at h

theorem enorm_complex_sq (z : ℂ) : ‖z‖ₑ ^ 2 = ‖z.re‖ₑ ^ 2 + ‖z.im‖ₑ ^ 2 := by
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  congr 1
  have h : ‖z‖ * ‖z‖ = z.re * z.re + z.im * z.im := by
    simpa only [pow_two, Complex.normSq_apply] using (Complex.normSq_eq_norm_sq z).symm
  simp only [Real.norm_eq_abs, pow_two]
  nlinarith only [h, sq_abs z.re, sq_abs z.im]

theorem lintegral_complex_euclidean_sq {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (F : Ω → EuclideanSpace ℂ κ) (hF : Measurable F) :
    (∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ) = ∑ k,
      ((∫⁻ x, ‖(F x k).re‖ₑ ^ 2 ∂μ) + (∫⁻ x, ‖(F x k).im‖ₑ ^ 2 ∂μ)) := by
  have hpoint (x : Ω) : ‖F x‖ₑ ^ 2 = ∑ k, (‖(F x k).re‖ₑ ^ 2 + ‖(F x k).im‖ₑ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_complex_sq]
  simp_rw [hpoint]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_add_left]
    exact ((Complex.continuous_re.comp ((PiLp.continuous_apply 2 _ k))).measurable.comp hF).enorm.pow_const _
  · intro k _
    exact (((Complex.continuous_re.comp (PiLp.continuous_apply 2 _ k)).measurable.comp hF).enorm.pow_const _).add
      (((Complex.continuous_im.comp (PiLp.continuous_apply 2 _ k)).measurable.comp hF).enorm.pow_const _)

namespace FiniteLineGrid

theorem complexAverage_re {κ : Type*} [Fintype κ] (g : FiniteLineGrid) (μ : Measure ℝ)
    (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) (x : ℝ) (k : κ) :
    (g.complexAverage μ F n x k).re = g.average μ (fun y => (F y k).re) n x := by
  simp [complexAverage]

theorem complexAverage_im {κ : Type*} [Fintype κ] (g : FiniteLineGrid) (μ : Measure ℝ)
    (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) (x : ℝ) (k : κ) :
    (g.complexAverage μ F n x k).im = g.average μ (fun y => (F y k).im) n x := by
  simp [complexAverage]

theorem complexAverage_measurable {κ : Type*} [Fintype κ] (g : FiniteLineGrid)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) :
    Measurable (g.complexAverage μ F n) := by
  apply measurable_complex_martingale
  · intro k
    simpa only [complexAverage_re] using g.average_martingale μ (fun y => (F y k).re)
  · intro k
    simpa only [complexAverage_im] using g.average_martingale μ (fun y => (F y k).im)

theorem complexAverage_energy {κ : Type*} [Fintype κ] (g : FiniteLineGrid)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (F : ℝ → EuclideanSpace ℂ κ) (hF : Measurable F)
    (hRe : ∀ k, MemLp (fun y => (F y k).re) 2 μ)
    (hIm : ∀ k, MemLp (fun y => (F y k).im) 2 μ) (n : ℕ) :
    (∫⁻ x, ‖g.complexAverage μ F n x‖ₑ ^ 2 ∂μ) ≤ ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := by
  rw [lintegral_complex_euclidean_sq μ _ (g.complexAverage_measurable μ F n),
    lintegral_complex_euclidean_sq μ F hF]
  apply Finset.sum_le_sum
  intro k _
  simp only [complexAverage_re, complexAverage_im, average]
  exact add_le_add (lintegral_square_condExp_le μ _ _ (hRe k))
    (lintegral_square_condExp_le μ _ _ (hIm k))

end FiniteLineGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SeparatedSampling
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sampling estimate needed for a band primitive: use disjoint
intervals at the band scale, independently of the larger mesh spacing. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem sample_interval_energy (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    δ * A a ^ 2 ≤ 2 * (∫ x in Ico a (a + δ), A x ^ 2) +
      2 * δ ^ 2 * ∫ x in Ico a (a + δ), deriv A x ^ 2 := by
  have hab : a < a + δ := lt_add_of_pos_right a hδ
  let energy := ∫ x in Icc a (a + δ), deriv A x ^ 2
  have hpoint : ∀ᵐ y ∂volume.restrict (Icc a (a + δ)),
      A a ^ 2 ≤ 2 * A y ^ 2 + 2 * δ * energy := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hp := interval_pair_energy A hab.le (fun x _ => hA x)
      (hd2.restrict _) (show a ∈ Icc a (a + δ) from ⟨le_rfl, hab.le⟩) hy
    simp only [Real.norm_eq_abs, sq_abs, add_sub_cancel_left] at hp
    nlinarith [sq_nonneg (A a - 2 * A y)]
  have h := integral_mono_ae (integrable_const (A a ^ 2))
    (((hA2.restrict (Icc a (a + δ))).integrable_sq.const_mul 2).add
      (integrable_const (2 * δ * energy))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add ((hA2.restrict (Icc a (a + δ))).integrable_sq.const_mul 2)
      (integrable_const _), integral_const_mul, integral_const, integral_const] at h
  have hmass : (volume.restrict (Icc a (a + δ))).real univ = δ := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, add_sub_cancel_left,
      ENNReal.toReal_ofReal hδ.le]
  simp only [smul_eq_mul, hmass, energy, integral_Icc_eq_integral_Ico] at h
  nlinarith only [h]

theorem separated_sample_sum (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    (N : ℕ) (sample : Fin N → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hseparated : ∀ i j, i < j → sample i + δ ≤ sample j) :
    (∑ i, A (sample i) ^ 2) ≤
      (2 / δ) * (∫ x, A x ^ 2) + 2 * δ * ∫ x, deriv A x ^ 2 := by
  let cell := fun i => Ico (sample i) (sample i + δ)
  have hdisj : Pairwise (fun i j => Disjoint (cell i) (cell j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact (not_lt_of_ge (hseparated i j h)) (hxj.1.trans_lt hxi.2)
    · exact (not_lt_of_ge (hseparated j i h)) (hxi.1.trans_lt hxj.2)
  have hsumA : (∑ i, ∫ x in cell i, A x ^ 2) ≤ ∫ x, A x ^ 2 := by
    rw [← integral_iUnion_fintype (fun _ => measurableSet_Ico) hdisj
      (fun _ => hA2.integrable_sq.integrableOn)]
    exact setIntegral_le_integral hA2.integrable_sq (by filter_upwards with x; exact sq_nonneg _)
  have hsumd : (∑ i, ∫ x in cell i, deriv A x ^ 2) ≤ ∫ x, deriv A x ^ 2 := by
    rw [← integral_iUnion_fintype (fun _ => measurableSet_Ico) hdisj
      (fun _ => hd2.integrable_sq.integrableOn)]
    exact setIntegral_le_integral hd2.integrable_sq (by filter_upwards with x; exact sq_nonneg _)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => sample_interval_energy A hA hA2 hd2 (sample i) hδ)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at h
  have htotal : δ * (∑ i, A (sample i) ^ 2) ≤
      2 * (∫ x, A x ^ 2) + 2 * δ ^ 2 * ∫ x, deriv A x ^ 2 := by
    dsimp only [cell] at hsumA hsumd
    nlinarith [mul_le_mul_of_nonneg_left hsumd (sq_nonneg δ)]
  calc
    _ ≤ (2 * (∫ x, A x ^ 2) + 2 * δ ^ 2 * ∫ x, deriv A x ^ 2) / δ :=
      (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using htotal)
    _ = _ := by field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridPoincare
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

theorem cells_cover_root (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) :
    (⋃ i : Fin (g.branching ^ level), g.cell level i.val) = g.root := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact g.cell_subset_root level i.isLt hi
  · intro hx
    let i : Fin (g.branching ^ level) := ⟨(g.index level x).val, g.index_lt_level hl x⟩
    exact mem_iUnion.mpr ⟨i, (g.index_eq_iff_mem_cell hl hx i.val).mp rfl⟩

theorem cells_disjoint (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) :
    Pairwise (fun i j : Fin (g.branching ^ level) => Disjoint (g.cell level i.val) (g.cell level j.val)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hri := g.cell_subset_root level i.isLt hxi
  have hix := (g.index_eq_iff_mem_cell hl hri i.val).mpr hxi
  have hjx := (g.index_eq_iff_mem_cell hl hri j.val).mpr hxj
  exact hij (Fin.ext (hix.symm.trans hjx))

theorem cell_poincare (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) (hdf : Differentiable ℝ f)
    (hd : MemLp (deriv f) 2 volume) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    (∫ x in g.cell level i, |f x - g.average g.lineMeasure f level x| ^ 2) ≤
      g.meshWidth level ^ 2 * ∫ x in g.cell level i, |deriv f x| ^ 2 := by
  let a := g.origin + g.meshWidth level * i
  let b := g.origin + g.meshWidth level * (i + 1)
  have hlength : b - a = g.meshWidth level := by dsimp [a,b]; ring
  have hab : a < b := sub_pos.mp (hlength ▸ g.meshWidth_pos level)
  have h := interval_poincare_Ico f hab (fun x _ => hdf x) (hd.restrict (Icc a b))
  rw [hlength] at h
  calc
    _ = ∫ x in Ico a b, |f x - (g.meshWidth level)⁻¹ * ∫ y in Ico a b, f y| ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      dsimp only
      rw [g.average_eq_cell_mean f hf hl hi hx, div_eq_mul_inv, mul_comm]
      rfl
    _ ≤ _ := by simpa only [Real.norm_eq_abs, smul_eq_mul, cell, a, b] using h

/-- Summing the actual disjoint cells gives the low-frequency part of
the smooth/dyadic comparison, with no loss from their number. -/
theorem poincare (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : MemLp f 2 g.lineMeasure) (hdf : Differentiable ℝ f)
    (hd : MemLp (deriv f) 2 volume) {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, |f x - g.average g.lineMeasure f level x| ^ 2 ∂g.lineMeasure) ≤
      g.meshWidth level ^ 2 * ∫ x in g.root, |deriv f x| ^ 2 := by
  have herr : Integrable (fun x => |f x - g.average g.lineMeasure f level x| ^ 2)
      g.lineMeasure := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hf.sub (g.average_memLp g.lineMeasure f hf level)).integrable_norm_pow (by decide : 2 ≠ 0)
  have hder : Integrable (fun x => |deriv f x| ^ 2) volume := by
    simpa only [Real.norm_eq_abs] using hd.integrable_norm_pow (by decide : 2 ≠ 0)
  have hc (i : Fin (g.branching ^ level)) :
      IntegrableOn (fun x => |f x - g.average g.lineMeasure f level x| ^ 2)
        (g.cell level i.val) volume :=
    herr.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root level i.isLt))
  change (∫ x in g.root, |f x - g.average g.lineMeasure f level x| ^ 2) ≤ _
  have hpartf := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) hc
  have hpartd := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) (fun _ => hder.integrableOn)
  rw [g.cells_cover_root hl] at hpartf hpartd
  rw [hpartf]
  calc
    _ ≤ ∑ i : Fin (g.branching ^ level), g.meshWidth level ^ 2 *
        ∫ x in g.cell level i.val, |deriv f x| ^ 2 :=
      Finset.sum_le_sum fun i _ => g.cell_poincare f (hf.integrable (by norm_num)) hdf hd hl i.isLt
    _ = _ := by
      rw [← Finset.mul_sum, ← hpartd]

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridPrimitive
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell averages of a derivative are boundary differences. This is the
high-frequency half of the manuscript's dyadic comparison. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem average_deriv_eq (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A)) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure (deriv A) level x =
      (A (g.origin + g.meshWidth level * (i + 1)) -
        A (g.origin + g.meshWidth level * i)) / g.meshWidth level := by
  have hint : Integrable (deriv A) g.lineMeasure :=
    (hd.continuousOn.integrableOn_Icc :
      IntegrableOn (deriv A) (Icc g.origin (g.origin + g.width)) volume).mono_set Ico_subset_Icc_self
  rw [g.average_eq_cell_mean (deriv A) hint hl hi hx]
  congr 1
  let a := g.origin + g.meshWidth level * i
  let b := g.origin + g.meshWidth level * (i + 1)
  have hab : a ≤ b := by dsimp [a,b]; nlinarith [g.meshWidth_pos level]
  change (∫ y in Ico a b, deriv A y) = A b - A a
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_deriv_eq_sub (fun y _ => hA y) (hd.intervalIntegrable a b)

theorem average_deriv_cell_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A)) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    (∫ x in g.cell level i, |g.average g.lineMeasure (deriv A) level x| ^ 2) =
      (g.meshWidth level)⁻¹ *
        (A (g.origin + g.meshWidth level * (i + 1)) -
          A (g.origin + g.meshWidth level * i)) ^ 2 := by
  have heq := setIntegral_congr_fun (μ := volume) (s := g.cell level i) measurableSet_Ico
    (fun x hx => congrArg (fun t : ℝ => |t| ^ 2) (g.average_deriv_eq A hA hd hl hi hx))
  rw [heq, setIntegral_const, smul_eq_mul]
  have hmass : volume.real (g.cell level i) = g.meshWidth level := by
    rw [measureReal_def, cell, Real.volume_Ico]
    have he : g.origin + g.meshWidth level * (i + 1) -
        (g.origin + g.meshWidth level * i) = g.meshWidth level := by ring
    rw [he, ENNReal.toReal_ofReal (g.meshWidth_pos level).le]
  rw [hmass, sq_abs]
  field_simp [(g.meshWidth_pos level).ne']

/-- Each sample is charged by at most two adjacent cells, giving the
exact boundary-sampling reduction used for high-frequency bands. -/
theorem average_deriv_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A))
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, |g.average g.lineMeasure (deriv A) level x| ^ 2 ∂g.lineMeasure) ≤
      4 * (g.meshWidth level)⁻¹ * ∑ i : Fin (g.branching ^ level + 1),
        |A (g.origin + g.meshWidth level * i.val)| ^ 2 := by
  let boundary := fun i : ℕ => A (g.origin + g.meshWidth level * i)
  have hcellint (i : Fin (g.branching ^ level)) :
      IntegrableOn (fun x => |g.average g.lineMeasure (deriv A) level x| ^ 2)
        (g.cell level i.val) volume := by
    apply (integrableOn_const (C := |(boundary (i.val + 1) - boundary i.val) /
      g.meshWidth level| ^ 2) (by simp [Real.volume_Ico])).congr_fun _ measurableSet_Ico
    intro x hx
    dsimp only
    rw [g.average_deriv_eq A hA hd hl i.isLt hx]
    simp only [boundary, Nat.cast_add, Nat.cast_one]
  have hpart := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) hcellint
  rw [g.cells_cover_root hl] at hpart
  change (∫ x in g.root, |g.average g.lineMeasure (deriv A) level x| ^ 2) ≤ _
  rw [hpart]
  simp_rw [g.average_deriv_cell_energy A hA hd hl (Fin.isLt _)]
  rw [← Finset.mul_sum]
  have hsum := monotone_partition_square_sum boundary (g.branching ^ level) id monotone_id
  simp only [id_eq, Fin.val_succ, Fin.val_castSucc, Real.norm_eq_abs] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (g.meshWidth_pos level).le)
  simpa only [boundary, sq_abs, Nat.cast_add, Nat.cast_one,
    mul_left_comm (g.meshWidth level)⁻¹ 4, mul_assoc] using hmul

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HighFrequencyAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-frequency cell-average bound from a band-scale primitive. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem primitive_average_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A))
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ} (hδ : 0 < δ)
    (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, |g.average g.lineMeasure (deriv A) level x| ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, A x ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, deriv A x ^ 2 := by
  simp only [sq_abs]
  let sample := fun i : Fin (g.branching ^ level + 1) =>
    g.origin + g.meshWidth level * i.val
  have hsep (i j : Fin (g.branching ^ level + 1)) (hij : i < j) :
      sample i + δ ≤ sample j := by
    have hn : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show i.val + 1 ≤ j.val by omega)
    have hm := mul_le_mul_of_nonneg_left hn (g.meshWidth_pos level).le
    dsimp [sample]
    nlinarith
  have hs := separated_sample_sum A hA hA2 hd2 (g.branching ^ level + 1) sample hδ hsep
  have hav := g.average_deriv_energy A hA hd hl
  simp only [sq_abs] at hav
  calc
    _ ≤ 4 * (g.meshWidth level)⁻¹ * ∑ i, A (sample i) ^ 2 := hav
    _ ≤ 4 * (g.meshWidth level)⁻¹ *
        ((2 / δ) * (∫ x, A x ^ 2) + 2 * δ * ∫ x, deriv A x ^ 2) :=
      mul_le_mul_of_nonneg_left hs
        (mul_nonneg (by norm_num) (inv_nonneg.mpr (g.meshWidth_pos level).le))
    _ = _ := by field_simp; ring

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzBandPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual primitive of an annular Schwartz packet. The
Fourier quotient is smooth because the packet vanishes near frequency zero. -/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped FourierTransform Topology

namespace LipschitzHilbert

private theorem derivative_coefficient_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) :
    (2 * Real.pi * Complex.I * ξ : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hξ)

theorem exists_schwartz_band_primitive (f : SchwartzMap ℝ ℂ) {r R : ℝ}
    (hr : 0 < r) (hlow : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0) :
    ∃ A : SchwartzMap ℝ ℂ,
      (∀ x, deriv A x = f x) ∧
      (∀ ξ, |ξ| < r → 𝓕 A ξ = 0) ∧
      (∀ ξ, R < |ξ| → 𝓕 A ξ = 0) := by
  let q := fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ : ℂ)⁻¹ * 𝓕 f ξ
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hr) hr] with t ht
      dsimp only [q]
      rw [hlow t (abs_lt.mpr ht), mul_zero]
    · have hc : ContDiffAt ℝ (↑(⊤ : ℕ∞))
          (fun t : ℝ => (2 * Real.pi * Complex.I * t : ℂ)) ξ :=
        contDiffAt_const.mul Complex.ofRealCLM.contDiff.contDiffAt
      exact (hc.inv (derivative_coefficient_ne_zero hξ)).mul
        ((𝓕 f).smooth ⊤).contDiffAt
  have hcompact : HasCompactSupport q := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R) R))
    intro ξ hξ
    have hRξ : R < |ξ| := by
      by_contra h
      exact hξ (abs_le.mp (le_of_not_gt h))
    dsimp only [q]
    rw [hhigh ξ hRξ, mul_zero]
  let Q : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hq
  let A : SchwartzMap ℝ ℂ := 𝓕⁻ Q
  have hAQ : 𝓕 A = Q := fourier_fourierInv_eq Q
  have hderiv : SchwartzMap.derivCLM ℂ ℂ A = f := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
    ext ξ
    change 𝓕 (SchwartzMap.derivCLM ℂ ℂ A) ξ = 𝓕 f ξ
    rw [schwartz_fourier_deriv, hAQ]
    change (2 * Real.pi * Complex.I * ξ : ℂ) *
      ((2 * Real.pi * Complex.I * ξ : ℂ)⁻¹ * 𝓕 f ξ) = 𝓕 f ξ
    by_cases hξ : ξ = 0
    · subst ξ
      rw [hlow 0 (by simpa using hr)]
      simp
    · rw [← mul_assoc, mul_inv_cancel₀ (derivative_coefficient_ne_zero hξ), one_mul]
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x
    exact congrArg (fun F : SchwartzMap ℝ ℂ => F x) hderiv
  · intro ξ hξ
    rw [hAQ]
    change q ξ = 0
    simp only [q, hlow ξ hξ, mul_zero]
  · intro ξ hξ
    rw [hAQ]
    change q ξ = 0
    simp only [q, hhigh ξ hξ, mul_zero]

theorem schwartz_primitive_energy (A f : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 < r)
    (hderiv : ∀ x, deriv A x = f x)
    (hband : ∀ ξ, |ξ| < r → 𝓕 A ξ = 0) :
    (∫ x, ‖A x‖ ^ 2) ≤ (2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  have h := schwartz_band_derivative_lower A hr hband
  simp only [hderiv] at h
  have hc : 0 < (2 * Real.pi * r) ^ 2 := sq_pos_of_pos (by positivity)
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    (2 * Real.pi * r) ^ 2 * (∫ x, ‖A x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := h
    _ = (2 * Real.pi * r) ^ 2 *
        ((2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2) := by
      field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ComplexBandAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar complex packet averages on the actual line grid. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem integral_complex_square (μ : Measure ℝ) (f : ℝ → ℂ)
    (hre : MemLp (fun x => (f x).re) 2 μ)
    (him : MemLp (fun x => (f x).im) 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) =
      (∫ x, (f x).re ^ 2 ∂μ) + ∫ x, (f x).im ^ 2 ∂μ := by
  have h (x : ℝ) : ‖f x‖ ^ 2 = (f x).re ^ 2 + (f x).im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq (f x)).symm
  simp_rw [h]
  exact integral_add hre.integrable_sq him.integrable_sq

theorem schwartz_projection_deriv (f : SchwartzMap ℝ ℂ) (L : ℂ →L[ℝ] ℝ) :
    deriv (f.postcompCLM L) = fun x => L (deriv f x) := by
  funext x
  exact (L.hasFDerivAt.comp_hasDerivAt x (f.differentiable x).hasDerivAt).deriv

theorem schwartz_projection_coe (f : SchwartzMap ℝ ℂ) (L : ℂ →L[ℝ] ℝ) :
    (f.postcompCLM L : ℝ → ℝ) = fun x => L (f x) := by
  funext x
  rfl

theorem schwartz_re_memLp (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => (f x).re) 2 volume := by
  simpa only [schwartz_projection_coe, Complex.reCLM_apply] using
    (f.postcompCLM Complex.reCLM).memLp 2 volume

theorem schwartz_im_memLp (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => (f x).im) 2 volume := by
  simpa only [schwartz_projection_coe, Complex.imCLM_apply] using
    (f.postcompCLM Complex.imCLM).memLp 2 volume

namespace FiniteLineGrid

theorem schwartz_projection_average_energy (g : FiniteLineGrid)
    (A f : SchwartzMap ℝ ℂ) (hderiv : ∀ x, deriv A x = f x)
    (L : ℂ →L[ℝ] ℝ) {level : ℕ} (hl : level ≤ g.depth)
    {δ : ℝ} (hδ : 0 < δ) (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, |g.average g.lineMeasure (fun y => L (f y)) level x| ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, L (A x) ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, L (f x) ^ 2 := by
  let B := A.postcompCLM L
  have hd : deriv B = fun x => L (f x) := by
    rw [schwartz_projection_deriv]
    simp only [hderiv]
  have hc : Continuous (deriv B) := by rw [hd]; exact L.continuous.comp f.continuous
  have hm : MemLp (deriv B) 2 volume := by
    rw [hd]
    exact (f.postcompCLM L).memLp 2
  have h := g.primitive_average_energy B B.differentiable hc (B.memLp 2) hm hl hδ hδmesh
  simpa only [hd, B, SchwartzMap.postcompCLM_apply] using h

theorem schwartz_primitive_average_energy (g : FiniteLineGrid)
    (A f : SchwartzMap ℝ ℂ) (hderiv : ∀ x, deriv A x = f x)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ}
    (hδ : 0 < δ) (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, ‖g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, ‖A x‖ ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 := by
  have hRe := g.schwartz_projection_average_energy A f hderiv Complex.reCLM hl hδ hδmesh
  have hIm := g.schwartz_projection_average_energy A f hderiv Complex.imCLM hl hδ hδmesh
  have hre : MemLp (fun x => (f x).re) 2 g.lineMeasure :=
    (schwartz_re_memLp f).restrict g.root
  have him : MemLp (fun x => (f x).im) 2 g.lineMeasure :=
    (schwartz_im_memLp f).restrict g.root
  rw [integral_complex_square g.lineMeasure _
    (by simpa only [scalarAverage_re] using g.average_memLp g.lineMeasure _ hre level)
    (by simpa only [scalarAverage_im] using g.average_memLp g.lineMeasure _ him level)]
  simp only [scalarAverage_re, scalarAverage_im]
  rw [integral_complex_square volume A (schwartz_re_memLp A) (schwartz_im_memLp A),
    integral_complex_square volume f (schwartz_re_memLp f) (schwartz_im_memLp f)]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, sq_abs] at hRe hIm
  nlinarith only [hRe, hIm]

theorem schwartz_poincare (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, ‖f x - g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      g.meshWidth level ^ 2 * ∫ x, ‖deriv f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hre : MemLp (fun x => (f x).re) 2 g.lineMeasure :=
    (schwartz_re_memLp f).restrict g.root
  have him : MemLp (fun x => (f x).im) 2 g.lineMeasure :=
    (schwartz_im_memLp f).restrict g.root
  have hRe := g.poincare (f.postcompCLM Complex.reCLM) hre
    (f.postcompCLM Complex.reCLM).differentiable
    (by simpa only [schwartz_projection_deriv, df, SchwartzMap.derivCLM_apply,
      Complex.reCLM_apply] using schwartz_re_memLp df) hl
  have hIm := g.poincare (f.postcompCLM Complex.imCLM) him
    (f.postcompCLM Complex.imCLM).differentiable
    (by simpa only [schwartz_projection_deriv, df, SchwartzMap.derivCLM_apply,
      Complex.imCLM_apply] using schwartz_im_memLp df) hl
  have hRe' : (∫ x in g.root, (deriv f x).re ^ 2) ≤ ∫ x, (deriv f x).re ^ 2 := by
    apply setIntegral_le_integral
    · simpa only [df, SchwartzMap.derivCLM_apply] using (schwartz_re_memLp df).integrable_sq
    · filter_upwards with x
      exact sq_nonneg _
  have hIm' : (∫ x in g.root, (deriv f x).im ^ 2) ≤ ∫ x, (deriv f x).im ^ 2 := by
    apply setIntegral_le_integral
    · simpa only [df, SchwartzMap.derivCLM_apply] using (schwartz_im_memLp df).integrable_sq
    · filter_upwards with x
      exact sq_nonneg _
  have her : MemLp (fun x => (f x - g.scalarAverage g.lineMeasure f level x).re)
      2 g.lineMeasure := by
    convert hre.sub (g.average_memLp g.lineMeasure _ hre level) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.sub_apply, Complex.sub_re, scalarAverage_re]
  have hei : MemLp (fun x => (f x - g.scalarAverage g.lineMeasure f level x).im)
      2 g.lineMeasure := by
    convert him.sub (g.average_memLp g.lineMeasure _ him level) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.sub_apply, Complex.sub_im, scalarAverage_im]
  rw [integral_complex_square g.lineMeasure _ her hei]
  have hdecomp := integral_complex_square volume df (schwartz_re_memLp df) (schwartz_im_memLp df)
  simp only [df, SchwartzMap.derivCLM_apply] at hdecomp
  rw [hdecomp]
  rw [schwartz_projection_deriv] at hRe hIm
  simp only [schwartz_projection_coe, SchwartzMap.postcompCLM_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, sq_abs] at hRe hIm
  simp only [Complex.sub_re, Complex.sub_im, scalarAverage_re, scalarAverage_im]
  exact (add_le_add hRe hIm).trans (by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_left hRe' (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hIm' (sq_nonneg _)))

theorem schwartz_low_frequency_error (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hband : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0)
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, ‖f x - g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      (g.meshWidth level * (2 * Real.pi * R)) ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  calc
    _ ≤ g.meshWidth level ^ 2 * ∫ x, ‖deriv f x‖ ^ 2 := g.schwartz_poincare f hl
    _ ≤ g.meshWidth level ^ 2 * ((2 * Real.pi * R) ^ 2 * ∫ x, ‖f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (schwartz_band_derivative_upper f hR hband) (sq_nonneg _)
    _ = _ := by ring

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FourGridBandErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radix-four meshes and the geometric error bound for each band. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem four_pow_ratio {i j : ℕ} (h : j ≤ i) :
    ((4 : ℝ) ^ i)⁻¹ * (4 : ℝ) ^ j = (1 / 4 : ℝ) ^ (i - j) := by
  have heq : i = j + (i - j) := by omega
  rw [heq, pow_add]
  simp only [Nat.add_sub_cancel_left, one_div, inv_pow]
  field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandAverageComparison
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual annular packet errors without a scale-count loss. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

namespace FiniteLineGrid

theorem scalarAverage_memLp (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 μ) (i : ℕ) : MemLp (g.scalarAverage μ f i) 2 μ := by
  apply memLp_re_im_iff.mp
  constructor
  · convert g.average_memLp μ (fun x => (f x).re) hf.re i using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact scalarAverage_re g μ f i x
  · convert g.average_memLp μ (fun x => (f x).im) hf.im i using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact scalarAverage_im g μ f i x

theorem scalarAverage_fullBandSum {N : ℕ} (g : FiniteLineGrid)
    (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    g.scalarAverage g.lineMeasure (fullBandSum f) i =ᵐ[g.lineMeasure]
      fun x => ∑ j, g.scalarAverage g.lineMeasure (f j) i x := by
  have hr : (fun x => (fullBandSum f x).re) = ∑ j, (fun x => (f j x).re) := by
    funext x
    simp only [fullBandSum, Complex.re_sum, Finset.sum_apply]
  have hi : (fun x => (fullBandSum f x).im) = ∑ j, (fun x => (f j x).im) := by
    funext x
    simp only [fullBandSum, Complex.im_sum, Finset.sum_apply]
  have hR := condExp_finsetSum (μ := g.lineMeasure) (s := Finset.univ)
    (fun j _ => (show MemLp (fun x => (f j x).re) 2 g.lineMeasure from
      (schwartz_re_memLp (f j)).restrict g.root).integrable (by norm_num))
    (g.filtration i)
  have hI := condExp_finsetSum (μ := g.lineMeasure) (s := Finset.univ)
    (fun j _ => (show MemLp (fun x => (f j x).im) 2 g.lineMeasure from
      (schwartz_im_memLp (f j)).restrict g.root).integrable (by norm_num))
    (g.filtration i)
  filter_upwards [hR,hI] with x hxR hxI
  apply Complex.ext
  · simp only [Complex.re_sum, scalarAverage_re, average, hr]
    simpa only [Finset.sum_apply] using hxR
  · simp only [Complex.im_sum, scalarAverage_im, average, hi]
    simpa only [Finset.sum_apply] using hxI

end FiniteLineGrid

theorem bandErrorAt_memLp (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ) (level i j : ℕ) :
    MemLp (bandErrorAt g f level i j) 2 g.lineMeasure := by
  have hf : MemLp (f : ℝ → ℂ) 2 g.lineMeasure := (f.memLp 2 volume).restrict g.root
  have hav := g.scalarAverage_memLp g.lineMeasure f hf level
  by_cases hji : j < i
  · convert hf.sub hav using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [bandErrorAt, ite_eq_left hji, Pi.sub_apply]
  · convert hav.neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [bandErrorAt, ite_eq_right hji, zero_sub, Pi.neg_apply]

theorem bandErrorAt_sum {N : ℕ} (g : FiniteLineGrid)
    (f : Fin N → SchwartzMap ℝ ℂ) (level i : ℕ) :
    (fun x => ∑ j, bandErrorAt g (f j) level i j.val x) =ᵐ[g.lineMeasure]
      fun x => partialBandSum f i x - g.scalarAverage g.lineMeasure (fullBandSum f) level x := by
  filter_upwards [g.scalarAverage_fullBandSum f level] with x hx
  simp only [bandErrorAt, Finset.sum_sub_distrib, partialBandSum, hx]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ParityPartialSums
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact even/odd decomposition of the dyadic partial sums. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem sum_range_parity {E : Type*} [AddCommGroup E] (u : ℕ → E) (n : ℕ) :
    (∑ j ∈ Finset.range n, u j) =
      (∑ j ∈ Finset.range ((n + 1) / 2), u (2 * j)) +
        ∑ j ∈ Finset.range (n / 2), u (2 * j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmod := Nat.mod_lt n (by omega : 0 < 2)
    by_cases hn : n % 2 = 0
    · have h1 : (n + 1) / 2 = n / 2 := by omega
      have h2 : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      have h3 : 2 * (n / 2) = n := by omega
      simp only [h1, h2, Finset.sum_range_succ, h3] at ih ⊢
      rw [ih]
      abel
    · have h1 : (n + 1) / 2 = n / 2 + 1 := by omega
      have h2 : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      have h3 : 2 * (n / 2) + 1 = n := by omega
      simp only [h1, h2, Finset.sum_range_succ, h3] at ih ⊢
      rw [ih]
      abel

theorem partialBandSum_eq_sum_range {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {i : ℕ} (hi : i ≤ N) (x : ℝ) :
    partialBandSum f i x = ∑ j ∈ Finset.range i, paddedPacket f j x := by
  classical
  have hfin : partialBandSum f i x =
      ∑ j : Fin N, if j.val < i then paddedPacket f j.val x else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [paddedPacket, dite_eq_left j.isLt]
  rw [hfin]
  have heq := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < i then paddedPacket f j x else 0) N
  rw [heq]
  rw [← Finset.sum_filter]
  have hs : (Finset.range N).filter (fun j => j < i) = Finset.range i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]

theorem partialBandSum_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {i : ℕ} (hi : i ≤ N) (x : ℝ) :
    partialBandSum f i x =
      partialBandSum (parityPacket f 0) ((i + 1) / 2) x +
        partialBandSum (parityPacket f 1) (i / 2) x := by
  rw [partialBandSum_eq_sum_range f hi, sum_range_parity]
  rw [partialBandSum_eq_sum_range _ (by omega : (i + 1) / 2 ≤ N),
    partialBandSum_eq_sum_range _ (by omega : i / 2 ≤ N)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := by have := Finset.mem_range.mp hj; omega
    simp only [paddedPacket, dite_eq_left hjN, parityPacket, Nat.add_zero]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := by have := Finset.mem_range.mp hj; omega
    simp only [paddedPacket, dite_eq_left hjN, parityPacket]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScalarLineVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar complex form of the actual-grid variation comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

theorem scalarVector_sub (z w : ℂ) : scalarVector (z - w) = scalarVector z - scalarVector w := by
  ext u
  rfl

theorem norm_scalarVector (z : ℂ) : ‖scalarVector z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [scalarVector, Real.sqrt_sq (norm_nonneg z)]

theorem scalarVector_measurable : Measurable scalarVector := by
  exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr (fun _ => measurable_id))

theorem finiteCubicVariation_scalarVector (F : ℕ → ℂ) (N : ℕ) :
    finiteCubicVariation (fun i => scalarVector (F i)) N = finiteCubicVariation F N := by
  unfold finiteCubicVariation
  simp_rw [← scalarVector_sub, norm_scalarVector]

theorem scalarVector_average (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℂ)
    (i : ℕ) (x : ℝ) :
    g.complexAverage μ (fun y => scalarVector (f y)) i x =
      scalarVector (g.scalarAverage μ f i x) := by
  ext u
  rfl

theorem lintegral_enorm_square (μ : Measure ℝ) (f : ℝ → ℂ) (hf : MemLp f 2 μ) :
    (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (hf.integrable_norm_pow (by decide : 2 ≠ 0))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShiftedLineAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Start the actual mesh martingale at a prescribed finer level. This
allows the surrounding finite root interval to grow without changing
the packet scales used in the comparison. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert
namespace FiniteLineGrid

theorem shifted_average_martingale (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (offset : ℕ) :
    Martingale (fun i => g.average μ f (offset + i)) (g.shiftedFiltration offset) μ :=
  martingale_condExp f (g.shiftedFiltration offset) μ

end FiniteLineGrid

theorem lineGrid_shifted_lepingle (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (offset : ℕ) (κ : Type) [Fintype κ]
      (F : ℝ → EuclideanSpace ℂ κ), Measurable F →
      (∀ k, MemLp (fun x => (F x k).re) 2 g.lineMeasure) →
      (∀ k, MemLp (fun x => (F x k).im) 2 g.lineMeasure) → ∀ N : ℕ,
        (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
          (fun i => g.complexAverage g.lineMeasure F (offset + i) x) N) ^ (2 / 3 : ℝ) ∂g.lineMeasure) ≤
          (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F x‖ₑ ^ 2 ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lepingle_complex_finite_measure hL
  refine ⟨C,hC,?_⟩
  intro g offset κ inst F hF hRe hIm N
  have h := hbound ℝ inferInstance g.lineMeasure inferInstance κ (g.shiftedFiltration offset)
    (fun i => g.complexAverage g.lineMeasure F (offset + i))
    (fun k => by simpa only [FiniteLineGrid.complexAverage_re] using
      g.shifted_average_martingale g.lineMeasure (fun x => (F x k).re) offset)
    (fun k => by simpa only [FiniteLineGrid.complexAverage_im] using
      g.shifted_average_martingale g.lineMeasure (fun x => (F x k).im) offset)
    (fun k i => by simpa only [FiniteLineGrid.complexAverage_re] using
      g.average_memLp g.lineMeasure _ (hRe k) (offset + i))
    (fun k i => by simpa only [FiniteLineGrid.complexAverage_im] using
      g.average_memLp g.lineMeasure _ (hIm k) (offset + i)) N
  exact h.trans (mul_le_mul_right (g.complexAverage_energy g.lineMeasure F hF hRe hIm (offset + N)) _)

theorem scalar_shifted_line_comparison (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (offset : ℕ)
      (f : ℝ → ℂ) (P : ℕ → ℝ → ℂ), Measurable f →
      (∀ i, Measurable (P i)) → MemLp f 2 g.lineMeasure → ∀ N : ℕ,
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => P i x) N) ^ (2 / 3 : ℝ)
        ∂g.lineMeasure) ≤
      2 * (C : ℝ≥0∞) ^ 2 * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂g.lineMeasure) +
        8 * ∑ i : Fin (N + 1), ∫⁻ x,
          ‖P i.val x - g.scalarAverage g.lineMeasure f (offset + i.val) x‖ₑ ^ 2 ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lineGrid_shifted_lepingle hL
  refine ⟨C,hC,?_⟩
  intro g offset f P hf hP hf2 N
  let F := fun x => scalarVector (f x)
  let Q := fun i x => scalarVector (P i x)
  let M := fun i => g.complexAverage g.lineMeasure F (offset + i)
  have h := lintegral_finiteCubicVariation_comparison g.lineMeasure Q M
    (fun i => scalarVector_measurable.comp (hP i))
    (fun i => g.complexAverage_measurable g.lineMeasure F (offset + i)) N
  have hm := hbound g offset Unit F (scalarVector_measurable.comp hf)
    (fun _ => hf2.re) (fun _ => hf2.im) N
  have ht := h.trans (add_le_add (by
    simpa only [mul_assoc] using mul_le_mul_right hm 2) le_rfl)
  simpa only [Q, M, F, finiteCubicVariation_scalarVector, scalarVector_average,
    ← scalarVector_sub, ← ofReal_norm, norm_scalarVector, mul_assoc] using ht

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local annular variation from Lépingle's inequality,
with the smooth/dyadic comparison supplied by packet estimates. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem fullBandSum_coe {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    fullBandSum f = (∑ j, f j : SchwartzMap ℝ ℂ) := by
  funext x
  simp [fullBandSum]

theorem fullBandSum_memLp {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    MemLp (fullBandSum f) 2 volume := by
  rw [fullBandSum_coe]
  exact (∑ j, f j : SchwartzMap ℝ ℂ).memLp 2 volume

theorem partialBandSum_memLp {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    MemLp (partialBandSum f i) 2 volume := by
  have h (j : Fin N) : MemLp (fun x => if j.val < i then f j x else 0) 2 volume := by
    by_cases hj : j.val < i
    · simpa only [ite_eq_left hj] using (f j).memLp 2 volume
    · simp only [ite_eq_right hj]
      exact MemLp.zero
  convert memLp_finsetSum Finset.univ (fun j _ => h j) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [partialBandSum]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GlobalAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exhaust the line by growing roots while keeping the comparison mesh
fixed. The annular variation constant is independent of the root size. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem expandingGrid_root (N M : ℕ) :
    (expandingGrid N M).root = Ico (-((4 : ℝ) ^ M) / 2) ((4 : ℝ) ^ M / 2) := by
  unfold FiniteLineGrid.root expandingGrid
  congr 1
  ring

theorem expandingGrid_mesh (N M i : ℕ) :
    (expandingGrid N M).meshWidth (M + i) = ((4 : ℝ) ^ i)⁻¹ := by
  simp only [FiniteLineGrid.meshWidth, expandingGrid, Nat.cast_ofNat, pow_add]
  field_simp

theorem expandingGrid_mono (N : ℕ) : Monotone (fun M => (expandingGrid N M).root) := by
  intro M K hMK
  change (expandingGrid N M).root ⊆ (expandingGrid N K).root
  rw [expandingGrid_root, expandingGrid_root]
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hMK
  exact Ico_subset_Ico (by linarith) (by linarith)

theorem expandingGrid_cover (N : ℕ) : (⋃ M, (expandingGrid N M).root) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (2 * |x|) (by norm_num : (1 : ℝ) < 4)
  refine ⟨M,?_⟩
  rw [expandingGrid_root]
  constructor <;> linarith [neg_abs_le x, le_abs_self x]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertAnnularVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional complex annular variation estimate, with no
dependence of the constant on the number of coordinates. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem ennreal_complex_variation_coordinates {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    ENNReal.ofReal (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      ∑ k, ENNReal.ofReal (finiteCubicVariation (fun i => F i k) N) ^ (2 / 3 : ℝ) := by
  have h := ENNReal.ofReal_le_ofReal (complex_finiteCubicVariation_le F N)
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg
    (finiteCubicVariation_nonneg _ _) _)] at h
  simpa only [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
    (by norm_num : (0 : ℝ) ≤ 2 / 3)] using h

theorem partialBandSum_measurable {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    Measurable (partialBandSum f i) := by
  apply Finset.measurable_sum
  intro j _
  by_cases hj : j.val < i
  · simpa only [ite_eq_left hj] using (f j).continuous.measurable
  · simpa only [ite_eq_right hj] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))

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

theorem cubicVariation_sq {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) :
    cubicVariation F N ^ 2 = (finiteCubicVariation F N) ^ (2 / 3 : ℝ) := by
  unfold cubicVariation
  rw [← Real.rpow_natCast, ← Real.rpow_mul (finiteCubicVariation_nonneg F N)]
  norm_num

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_HilbertPacketSums
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Hilbert packet sums are continuous and agree with the generic
partial sums used for spatial oscillation estimates. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem hilbertPartialBandSum_eq_packetPartialSum {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    hilbertPartialBandSum f n x =
      packetPartialSum (fun j => WithLp.toLp 2 (fun k => f j k x)) n := by
  ext k
  change (∑ j : Fin N, if j.val < n then f j k x else 0) = _
  simp only [packetPartialSum, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ThresholdSynthesis
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A monotone threshold selects one terminal interval of dyadic scales.
Its synthesis is controlled by the actual partial-sum variation. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem increment_cube_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    ‖F b - F a‖^3 ≤ finiteCubicVariation F N := by
  classical
  by_cases hN : N = 0
  · subst N
    have : a = 0 ∧ b = 0 := by omega
    rcases this with ⟨rfl,rfl⟩
    simpa using finiteCubicVariation_nonneg F 0
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let p : Fin (N+1) → Fin (N+1) := fun i =>
    if i.val = 0 then ⟨a, by omega⟩ else ⟨b, by omega⟩
  have hp : Monotone p := by
    intro i j hij
    dsimp [p]
    split_ifs with hi hj hj
    · exact le_rfl
    · exact hab
    · have hij' : i.val ≤ j.val := hij
      omega
    · exact le_rfl
  have hsum := partition_le_finiteCubicVariation F N p hp
  have hs : ‖F b - F a‖^3 ≤
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖^3 := by
    have h := Finset.single_le_sum
      (f := fun i : Fin N => ‖F (p i.succ) - F (p i.castSucc)‖^3)
      (s := Finset.univ) (a := (⟨0,hNpos⟩ : Fin N))
      (fun i _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_univ _)
    simpa only [p, Fin.val_succ, Fin.val_castSucc, Nat.zero_add,
      Nat.one_ne_zero, ite_false, if_false, ite_true, if_true] using h
  exact hs.trans hsum

theorem increment_le_cubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    ‖F b - F a‖ ≤ cubicVariation F N := by
  have h := Real.rpow_le_rpow (pow_nonneg (norm_nonneg (F b-F a)) 3)
    (increment_cube_le_finiteCubicVariation F N a b hab hb)
    (by norm_num : (0:ℝ) ≤ 1/3)
  have heq : (‖F b-F a‖^3)^(1/3:ℝ) = ‖F b-F a‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simpa only [heq, cubicVariation] using h

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GeneralAnnularErrors
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The averaging error with arbitrary fixed annular constants. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem complex_band_average_energy (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {r R : ℝ} (hr : 0 < r)
    (hlow : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ} (hδ : 0 < δ)
    (hmesh : δ ≤ g.meshWidth level) :
    (∫ x, ‖g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      ((8 / (g.meshWidth level * δ)) * (2 * Real.pi * r)⁻¹ ^ 2 +
        8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 := by
  obtain ⟨A,hd,hlo,_⟩ := exists_schwartz_band_primitive f hr hlow hhigh
  have hav := g.schwartz_primitive_average_energy A f hd hl hδ hmesh
  have hp := schwartz_primitive_energy A f hr hd hlo
  have hc : 0 ≤ 8 / (g.meshWidth level * δ) :=
    div_nonneg (by norm_num) (mul_pos (g.meshWidth_pos level) hδ).le
  calc
    _ ≤ (8 / (g.meshWidth level * δ)) *
        ((2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 :=
      hav.trans (add_le_add (mul_le_mul_of_nonneg_left hp hc) le_rfl)
    _ = _ := by ring

theorem general_annular_error (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {a b D : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hDlow : (2 * Real.pi * b) ^ 2 ≤ D ^ 2)
    (hDhigh : 8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) ≤ D ^ 2)
    (j : ℕ) (hlow : ∀ ξ, |ξ| < a * (4 : ℝ) ^ j → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, b * (4 : ℝ) ^ j < |ξ| → 𝓕 f ξ = 0)
    {level i : ℕ} (hl : level ≤ g.depth)
    (hmesh : g.meshWidth level = ((4 : ℝ) ^ i)⁻¹) :
    (∫ x, ‖bandErrorAt g f level i j x‖ ^ 2 ∂g.lineMeasure) ≤
      D ^ 2 * (1 / 4 : ℝ) ^ Nat.dist i j * ∫ x, ‖f x‖ ^ 2 := by
  have he : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  by_cases hji : j < i
  · have h := g.schwartz_low_frequency_error f (mul_nonneg hb (by positivity)) hhigh hl
    simp only [bandErrorAt, ite_eq_left hji]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ he)
    rw [hmesh, Nat.dist_eq_sub_of_le_right hji.le]
    have hr := four_pow_ratio hji.le
    have hq : 0 ≤ (1 / 4 : ℝ) ^ (i - j) := by positivity
    have hq1 : (1 / 4 : ℝ) ^ (i - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have heq : ((4 : ℝ) ^ i)⁻¹ * (2 * Real.pi * (b * 4 ^ j)) =
        (2 * Real.pi * b) * (1 / 4 : ℝ) ^ (i - j) := by rw [← hr]; ring
    rw [heq, mul_pow]
    have hqq : ((1 / 4 : ℝ) ^ (i - j)) ^ 2 ≤ (1 / 4 : ℝ) ^ (i - j) := by nlinarith
    exact (mul_le_mul_of_nonneg_left hqq (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hDlow hq)
  · have hij : i ≤ j := by omega
    have hδ : 0 < ((4 : ℝ) ^ j)⁻¹ := by positivity
    have hm : ((4 : ℝ) ^ j)⁻¹ ≤ g.meshWidth level := by
      rw [hmesh]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)
    have h := complex_band_average_energy g f (mul_pos ha (by positivity)) hlow hhigh hl hδ hm
    simp only [bandErrorAt, ite_eq_right hji, zero_sub, norm_neg]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ he)
    rw [hmesh, Nat.dist_eq_sub_of_le hij]
    have hr := four_pow_ratio hij
    have heq : (8 / (((4 : ℝ) ^ i)⁻¹ * ((4 : ℝ) ^ j)⁻¹)) *
        (2 * Real.pi * (a * 4 ^ j))⁻¹ ^ 2 +
        8 * ((4 : ℝ) ^ j)⁻¹ / ((4 : ℝ) ^ i)⁻¹ =
        8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) * (1 / 4 : ℝ) ^ (j - i) := by
      rw [← hr]
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hDhigh (by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GeneralAnnularComparison
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square comparison for arbitrary fixed positive annular endpoints. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem annularErrorConstant_pos {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 < annularErrorConstant a b := by unfold annularErrorConstant; positivity

theorem annularErrorConstant_low {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (2 * Real.pi * b) ^ 2 ≤ annularErrorConstant a b ^ 2 := by
  apply pow_le_pow_left₀ (by positivity)
  unfold annularErrorConstant
  have hc : 0 ≤ (2 * Real.pi * a)⁻¹ := by positivity
  linarith

theorem annularErrorConstant_high {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) ≤ annularErrorConstant a b ^ 2 := by
  have hc : 0 ≤ (2 * Real.pi * a)⁻¹ := by positivity
  have hd : 4 + 4 * (2 * Real.pi * a)⁻¹ ≤ annularErrorConstant a b := by
    unfold annularErrorConstant
    have : 0 ≤ 2 * Real.pi * b := by positivity
    linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 4 + 4 * (2 * Real.pi * a)⁻¹) hd 2
  nlinarith [sq_nonneg ((2 * Real.pi * a)⁻¹)]

theorem general_annular_square_comparison {N : ℕ} (g : FiniteLineGrid) (offset : ℕ)
    (f : Fin N → SchwartzMap ℝ ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0)
    (hdepth : offset + N ≤ g.depth)
    (hmesh : ∀ i, g.meshWidth (offset + i) = ((4 : ℝ) ^ i)⁻¹) :
    (∑ i : Fin (N + 1), ∫ x, ‖partialBandSum f i.val x -
      g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2 ∂g.lineMeasure) ≤
      (4 * annularErrorConstant a b) ^ 2 * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  let D := annularErrorConstant a b
  have hD : 0 < D := annularErrorConstant_pos ha hb
  have h := finite_energy_schur g.lineMeasure
    (fun (i : Fin (N + 1)) (j : Fin N) => bandErrorAt g (f j) (offset + i.val) i.val j.val)
    (fun i j => bandErrorAt_memLp g (f j) (offset + i.val) i.val j.val)
    (fun i j => D * (1 / 2 : ℝ) ^ Nat.dist i.val j.val)
    (fun _ _ => mul_pos hD (by positivity))
    (fun j => ∫ x, ‖f j x‖ ^ 2) (fun j => integral_nonneg (fun _ => sq_nonneg _))
    (R := 4 * D) (C := 4 * D) (by positivity)
    (fun i => by
      rw [← Finset.mul_sum, mul_comm 4 D]
      exact mul_le_mul_of_nonneg_left (sum_half_distance_le_four N i.val) hD.le)
    (fun j => by
      simp only [Nat.dist_comm]
      rw [← Finset.mul_sum, mul_comm 4 D]
      exact mul_le_mul_of_nonneg_left (sum_half_distance_le_four (N + 1) j.val) hD.le)
    (fun i j => by
      have he := general_annular_error g (f j) ha hb
        (annularErrorConstant_low ha hb) (annularErrorConstant_high ha hb) j.val
        (hlow j) (hhigh j) (by have := i.isLt; omega) (hmesh i.val)
      have hsq : ((1 / 2 : ℝ) ^ Nat.dist i.val j.val) ^ 2 =
          (1 / 4 : ℝ) ^ Nat.dist i.val j.val := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      simpa only [mul_pow, hsq, mul_assoc] using he)
  have heq : (∑ i : Fin (N + 1), ∫ x,
      ‖∑ j, bandErrorAt g (f j) (offset + i.val) i.val j.val x‖ ^ 2 ∂g.lineMeasure) =
      ∑ i : Fin (N + 1), ∫ x, ‖partialBandSum f i.val x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2 ∂g.lineMeasure := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [bandErrorAt_sum g f (offset + i.val) i.val] with x hx
    rw [hx]
  rw [heq] at h
  simpa only [pow_two] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FiniteSpectralOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy of a packet sum with finite spectral overlap. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem norm_sum_square_le_of_overlap {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (M : ℕ)
    (hM : (Finset.univ.filter (fun j => v j ≠ 0)).card ≤ M) :
    ‖∑ j, v j‖ ^ 2 ≤ M * ∑ j, ‖v j‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun j => v j ≠ 0)
  have hv : (∑ j ∈ s, v j) = ∑ j, v j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hj
  have he : (∑ j ∈ s, ‖v j‖ ^ 2) = ∑ j, ‖v j‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hz : v j = 0 := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hj
    simp [hz]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun j => ‖v j‖) (f := fun _ => (1 : ℝ)) (g := fun j => ‖v j‖ ^ 2)
    (fun _ _ => by norm_num) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2
  rw [hv] at hn
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [he] at hcs
  exact (hn.trans hcs).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hM)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem finite_spectral_overlap_energy {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (M : ℕ)
    (hM : ∀ ξ, (Finset.univ.filter (fun j => 𝓕 (f j) ξ ≠ 0)).card ≤ M) :
    (∫ x, ‖∑ j, f j x‖ ^ 2) ≤ M * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  let F : SchwartzMap ℝ ℂ := ∑ j, f j
  have hsum (x : ℝ) : F x = ∑ j, f j x := by simp [F]
  have hf (ξ : ℝ) : 𝓕 F ξ = ∑ j, 𝓕 (f j) ξ := by
    change (SchwartzMap.fourierTransformCLM ℂ (∑ j, f j)) ξ = _
    rw [map_sum]
    simp
  have hi : Integrable (fun ξ => ∑ j, ‖𝓕 (f j) ξ‖ ^ 2) volume :=
    integrable_finsetSum _ (fun j _ => ((𝓕 (f j)).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0))
  calc
    _ = ∫ ξ, ‖𝓕 F ξ‖ ^ 2 := by
      rw [SchwartzMap.integral_norm_sq_fourier]
      simp only [hsum]
    _ ≤ ∫ ξ, (M : ℝ) * ∑ j, ‖𝓕 (f j) ξ‖ ^ 2 := by
      apply integral_mono (((𝓕 F).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)) (hi.const_mul M)
      intro ξ
      dsimp only
      rw [hf]
      exact norm_sum_square_le_of_overlap _ M (hM ξ)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      · simp only [SchwartzMap.integral_norm_sq_fourier]
      · intro j _
        exact ((𝓕 (f j)).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_GeometricSpectralOverlap
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral overlap count for fixed-width annuli at radix-four scales. -/

noncomputable section

open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem geometric_spectral_overlap {N M : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {a b : ℝ} (ha : 0 < a) (hsep : b < a * (4 : ℝ) ^ M)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0)
    (ξ : ℝ) : (Finset.univ.filter (fun j => 𝓕 (f j) ξ ≠ 0)).card ≤ M := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => 𝓕 (f j) ξ ≠ 0)
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := Finset.min'_mem s hs
    have hm0 : 𝓕 (f m) ξ ≠ 0 := (Finset.mem_filter.mp hm).2
    have hmupper : |ξ| ≤ b * (4 : ℝ) ^ m.val := by
      by_contra h
      exact hm0 (hhigh m ξ (lt_of_not_ge h))
    have hinterval (j : Fin N) (hj : j ∈ s) : j.val ∈ Finset.Ico m.val (m.val + M) := by
      have hlo : m ≤ j := Finset.min'_le s j hj
      have hj0 : 𝓕 (f j) ξ ≠ 0 := (Finset.mem_filter.mp hj).2
      have hjlower : a * (4 : ℝ) ^ j.val ≤ |ξ| := by
        by_contra h
        exact hj0 (hlow j ξ (lt_of_not_ge h))
      have hhi : j.val < m.val + M := by
        by_contra h
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (le_of_not_gt h)
        have hprod := mul_le_mul_of_nonneg_left hp ha.le
        rw [pow_add] at hprod
        have hsep' := mul_lt_mul_of_pos_right hsep
          (pow_pos (by norm_num : (0 : ℝ) < 4) m.val)
        nlinarith [hprod]
      exact Finset.mem_Ico.mpr ⟨hlo,hhi⟩
    have hsubset : s.image (fun j : Fin N => j.val) ⊆ Finset.Ico m.val (m.val + M) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      exact hinterval j hj
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_image_of_injective s Fin.val_injective, Nat.card_Ico] at hcard
    simpa only [Nat.add_sub_cancel_left] using hcard
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ M
    simp [he]

theorem geometric_annular_energy {N M : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {a b : ℝ} (ha : 0 < a) (hsep : b < a * (4 : ℝ) ^ M)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) :
    (∫ x, ‖∑ j, f j x‖ ^ 2) ≤ M * ∑ j, ∫ x, ‖f j x‖ ^ 2 :=
  finite_spectral_overlap_energy f M (geometric_spectral_overlap f ha hsep hlow hhigh)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GeneralAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-line annular variation with arbitrary fixed inner and outer
frequency constants. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem general_scalar_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ)) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨C,hC,hbound⟩ := scalar_shifted_line_comparison hL
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (b / a) (by norm_num : (1 : ℝ) < 4)
  have hsep : b < a * (4 : ℝ) ^ M := by
    have h := (div_lt_iff₀ ha).mp hM
    simpa only [mul_comm] using h
  let D : ℝ≥0 := ⟨annularErrorConstant a b, (annularErrorConstant_pos ha hb).le⟩
  let K : ℝ≥0 := 2 * C ^ 2 * M + 8 * (4 * D) ^ 2 + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N f hlow hhigh
  have hlocal (g : FiniteLineGrid) (offset : ℕ) (hdepth : offset + N ≤ g.depth)
      (hmesh : ∀ i, g.meshWidth (offset + i) = ((4 : ℝ) ^ i)⁻¹) :
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ) ∂g.lineMeasure) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
    have hf : Measurable (fullBandSum f) := by
      rw [fullBandSum_coe]
      exact (∑ j, f j : SchwartzMap ℝ ℂ).continuous.measurable
    have hf2 : MemLp (fullBandSum f) 2 g.lineMeasure := (fullBandSum_memLp f).restrict g.root
    have hp2 (i : ℕ) : MemLp (partialBandSum f i) 2 g.lineMeasure :=
      (partialBandSum_memLp f i).restrict g.root
    have he2 (i : ℕ) : MemLp (fun x => partialBandSum f i x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i) x) 2 g.lineMeasure := by
      convert (hp2 i).sub (g.scalarAverage_memLp g.lineMeasure _ hf2 (offset + i)) using 1
      all_goals try with_reducible_and_instances rfl
    have h := hbound g offset (fullBandSum f) (partialBandSum f) hf
      (partialBandSum_measurable f) hf2 N
    rw [lintegral_enorm_square _ _ hf2] at h
    simp_rw [lintegral_enorm_square _ _ (he2 _)] at h
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      integral_nonneg (fun x => sq_nonneg (‖partialBandSum f i.val x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖)))] at h
    have htotal : (∫ x, ‖fullBandSum f x‖ ^ 2 ∂g.lineMeasure) ≤
        M * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
      apply le_trans _ (geometric_annular_energy f ha hsep hlow hhigh)
      exact setIntegral_le_integral
        ((fullBandSum_memLp f).integrable_norm_pow (by decide : 2 ≠ 0))
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    have hsquare := general_annular_square_comparison g offset f ha hb hlow hhigh hdepth hmesh
    have ht := ENNReal.ofReal_le_ofReal htotal
    have hs := ENNReal.ofReal_le_ofReal hsquare
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast] at ht
    rw [ENNReal.ofReal_mul (sq_nonneg _)] at hs
    have hc : ENNReal.ofReal ((4 * annularErrorConstant a b) ^ 2) = (4 * (D : ℝ≥0∞)) ^ 2 := by
      change ENNReal.ofReal ((4 * (D : ℝ)) ^ 2) = _
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      simp only [ENNReal.ofReal_coe_nnreal]
    rw [hc] at hs
    calc
      _ ≤ 2 * (C : ℝ≥0∞) ^ 2 * (M * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) +
          8 * ((4 * (D : ℝ≥0∞)) ^ 2 * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) :=
        h.trans (add_le_add (mul_le_mul_right ht _) (mul_le_mul_right hs _))
      _ ≤ _ := by
        have hk : 2 * (C : ℝ≥0∞) ^ 2 * M + 8 * (4 * (D : ℝ≥0∞)) ^ 2 ≤ (K : ℝ≥0∞) := by
          dsimp [K]
          exact le_add_of_nonneg_right (by positivity)
        first | (convert mul_le_mul_right hk (ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_right hk (ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2))).trans (le_of_eq (by ring)))
  let V := fun x => ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
    (2 / 3 : ℝ)
  change (∫⁻ x, V x) ≤ _
  rw [← setLIntegral_univ, ← expandingGrid_cover N,
    setLIntegral_iUnion_of_directed V (expandingGrid_mono N).directed_le]
  apply iSup_le
  intro m
  exact hlocal (expandingGrid N m) m (by simp [expandingGrid]) (expandingGrid_mesh N m)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ParityPackets
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral support and energy of the even/odd packet subfamilies. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem two_pow_parity (j r : ℕ) :
    (2 : ℝ) ^ (2 * j + r) = 2 ^ r * (4 : ℝ) ^ j := by
  rw [pow_add, pow_mul]
  norm_num
  ring

theorem parityPacket_low {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (a : ℝ) (r : ℕ)
    (hlow : ∀ k ξ, |ξ| < a * (2 : ℝ) ^ k.val → 𝓕 (f k) ξ = 0)
    (j : Fin N) (ξ : ℝ) (hξ : |ξ| < (a * (2 : ℝ) ^ r) * (4 : ℝ) ^ j.val) :
    𝓕 (parityPacket f r j) ξ = 0 := by
  by_cases h : 2 * j.val + r < N
  · simp only [parityPacket, paddedPacket, dite_eq_left h]
    apply hlow ⟨2 * j.val + r,h⟩ ξ
    simpa only [two_pow_parity, mul_assoc] using hξ
  · simp [parityPacket, paddedPacket, h]

theorem parityPacket_high {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (b : ℝ) (r : ℕ)
    (hhigh : ∀ k ξ, b * (2 : ℝ) ^ k.val < |ξ| → 𝓕 (f k) ξ = 0)
    (j : Fin N) (ξ : ℝ) (hξ : (b * (2 : ℝ) ^ r) * (4 : ℝ) ^ j.val < |ξ|) :
    𝓕 (parityPacket f r j) ξ = 0 := by
  by_cases h : 2 * j.val + r < N
  · simp only [parityPacket, paddedPacket, dite_eq_left h]
    apply hhigh ⟨2 * j.val + r,h⟩ ξ
    simpa only [two_pow_parity, mul_assoc] using hξ
  · simp [parityPacket, paddedPacket, h]

theorem sum_parity_le (u : ℕ → ℝ) (N r : ℕ) (hu : ∀ j, 0 ≤ u j)
    (hzero : ∀ j, N ≤ j → u j = 0) :
    (∑ j : Fin N, u (2 * j.val + r)) ≤ ∑ j : Fin N, u j.val := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => 2 * j + r) (Finset.range N) := by
    intro i _ j _ h
    change 2 * i + r = 2 * j + r at h
    omega
  have hmap : (Finset.range N).image (fun j => 2 * j + r) ⊆ Finset.range (2 * N + r + 1) := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have hj' := Finset.mem_range.mp hj
    apply Finset.mem_range.mpr
    omega
  have h := OAI.sum_le_sum_of_injOn (fun j : ℕ => 2 * j + r) hinj hmap
    (f := fun j => u (2 * j + r)) (g := u) (fun _ _ => le_rfl) (fun j _ _ => hu j)
  have ht : (∑ j ∈ Finset.range N, u j) = ∑ j ∈ Finset.range (2 * N + r + 1), u j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    exact hzero j (by simpa only [Finset.mem_range, not_lt] using hj)
  rw [← ht] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => u (2 * j + r)) N,
    Fin.sum_univ_eq_sum_range u N]
  exact h

theorem parityPacket_energy {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (r : ℕ) :
    (∑ j, ∫ x, ‖parityPacket f r j x‖ ^ 2) ≤ ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  have h := sum_parity_le (fun j => ∫ x, ‖paddedPacket f j x‖ ^ 2) N r
    (fun j => integral_nonneg (fun x => sq_nonneg _)) (fun j hj => by
      simp [paddedPacket, Nat.not_lt.mpr hj])
  simpa only [parityPacket, paddedPacket, dite_eq_left (Fin.isLt _)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's dyadic annular variation estimate, obtained from
the two radix-four subfamilies with exact partial-sum indexing. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (x : ℝ) :
    (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation (fun i => partialBandSum (parityPacket f 0) i x) N) ^ (2 / 3 : ℝ) +
      2 * (finiteCubicVariation (fun i => partialBandSum (parityPacket f 1) i x) N) ^ (2 / 3 : ℝ) := by
  let E := fun i => partialBandSum (parityPacket f 0) i x
  let O := fun i => partialBandSum (parityPacket f 1) i x
  have heq := finiteCubicVariation_congr (fun i => partialBandSum f i x)
    (fun i => E ((i + 1) / 2) + O (i / 2)) N (fun i hi => partialBandSum_parity f hi x)
  rw [heq]
  have hE := finiteCubicVariation_comp_le E N (fun i => (i + 1) / 2)
    (fun i j hij => Nat.div_le_div_right (Nat.add_le_add_right hij 1)) (by omega)
  have hO := finiteCubicVariation_comp_le O N (fun i => i / 2)
    (fun _ _ hij => Nat.div_le_div_right hij) (by omega)
  have hsum := finiteCubicVariation_add_square (fun i => E ((i + 1) / 2)) (fun i => O (i / 2)) N
  exact hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hE (by norm_num)) (by norm_num))
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hO (by norm_num)) (by norm_num)))

theorem lintegral_variation_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (parityPacket f 0) i x) N) ^ (2 / 3 : ℝ)) +
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (parityPacket f 1) i x) N) ^ (2 / 3 : ℝ)) := by
  have hpoint (x : ℝ) := ENNReal.ofReal_le_ofReal (finiteCubicVariation_parity f x)
  have hpos (g : Fin N → SchwartzMap ℝ ℂ) (x : ℝ) :
      0 ≤ 2 * (finiteCubicVariation (fun i => partialBandSum g i x) N) ^ (2 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _)
  simp only [ENNReal.ofReal_add (hpos _ _) (hpos _ _),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 2 / 3)] at hpoint
  have h := lintegral_mono (μ := volume) hpoint
  have hm (r : ℕ) : Measurable (fun x => ENNReal.ofReal (finiteCubicVariation
      (fun i => partialBandSum (parityPacket f r) i x) N) ^ (2 / 3 : ℝ)) :=
    (measurable_finiteCubicVariation _
      (partialBandSum_measurable (parityPacket f r)) N).ennreal_ofReal.pow_const _
  rw [lintegral_add_left ((hm 0).const_mul (2 : ℝ≥0∞)),
    lintegral_const_mul _ (hm 0), lintegral_const_mul _ (hm 1)] at h
  exact h

theorem dyadic_scalar_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < a * (2 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, b * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ)) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨K0,hK0,h0⟩ := general_scalar_annular_variation hL ha hb
  obtain ⟨K1,hK1,h1⟩ := general_scalar_annular_variation hL
    (mul_pos ha (by norm_num : (0 : ℝ) < 2)) (mul_nonneg hb (by norm_num : (0 : ℝ) ≤ 2))
  refine ⟨2 * K0 + 2 * K1, by positivity, ?_⟩
  intro N f hlow hhigh
  have he := h0 N (parityPacket f 0)
    (by simpa using parityPacket_low f a 0 hlow)
    (by simpa using parityPacket_high f b 0 hhigh)
  have ho := h1 N (parityPacket f 1)
    (by simpa using parityPacket_low f a 1 hlow)
    (by simpa using parityPacket_high f b 1 hhigh)
  have heE := ENNReal.ofReal_le_ofReal (parityPacket_energy f 0)
  have hoE := ENNReal.ofReal_le_ofReal (parityPacket_energy f 1)
  calc
    _ ≤ 2 * ((K0 : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) +
        2 * ((K1 : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) :=
      (lintegral_variation_parity f).trans (add_le_add
        (mul_le_mul_right (he.trans (mul_le_mul_right heE _)) _)
        (mul_le_mul_right (ho.trans (mul_le_mul_right hoE _)) _))
    _ = _ := by push_cast; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact horizontal dilation for Schwartz packets, including the Fourier
and measure factors needed to normalize different top lengths. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert

theorem schwartzDilation_energy (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) :
    (∫ x, ‖schwartzDilation f r hr x‖^2) = |r⁻¹| * (∫ x, ‖f x‖^2) := by
  simpa only [schwartzDilation_apply,smul_eq_mul] using
    Measure.integral_comp_mul_left (fun x : ℝ => ‖f x‖^2) r

theorem lintegral_dilation (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (r : ℝ) (hr : r ≠ 0) :
    (∫⁻ x, g (r*x)) = ENNReal.ofReal |r⁻¹| * (∫⁻ x, g x) := by
  rw [← lintegral_map hg (show Measurable (fun x : ℝ => r*x) by fun_prop)]
  have hm : Measure.map (fun x : ℝ => r*x) volume = ENNReal.ofReal |r⁻¹| • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hr)
  rw [hm,lintegral_smul_measure,smul_eq_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScaledAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One annular-variation constant works for every common physical
frequency scale. This removes dependence on the top's horizontal length. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform NNReal ENNReal
namespace LipschitzHilbert

theorem partialBandSum_dilation {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : r ≠ 0) (i : ℕ) (x : ℝ) :
    partialBandSum (fun j => schwartzDilation (f j) r hr) i x = partialBandSum f i (r*x) := by
  simp only [partialBandSum,schwartzDilation_apply]

theorem scaled_dyadic_scalar_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (r : ℝ), 0 < r → ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < (a/r)*(2:ℝ)^j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, (b/r)*(2:ℝ)^j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2/3:ℝ)) ≤
        (K:ℝ≥0∞)*ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖^2) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_scalar_annular_variation hL ha hb
  refine ⟨K,hK,?_⟩
  intro r hr N f hlow hhigh
  let g := fun j => schwartzDilation (f j) r hr.ne'
  have hlo (j : Fin N) (ξ : ℝ) (hξ : |ξ| < a*(2:ℝ)^j.val) : 𝓕 (g j) ξ = 0 := by
    apply schwartzDilation_low (f j) r (a*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply hlow j η
    convert hη using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hhi (j : Fin N) (ξ : ℝ) (hξ : b*(2:ℝ)^j.val < |ξ|) : 𝓕 (g j) ξ = 0 := by
    apply schwartzDilation_high (f j) r (b*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply hhigh j η
    convert hη using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h := hbound N g hlo hhi
  have hv : (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum g i x) N) ^ (2/3:ℝ)) =
      ENNReal.ofReal |r⁻¹| * (∫⁻ x, ENNReal.ofReal
        (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2/3:ℝ)) := by
    simp only [g,partialBandSum_dilation]
    exact lintegral_dilation _
      ((measurable_finiteCubicVariation _ (partialBandSum_measurable f) N).ennreal_ofReal.pow_const _) r hr.ne'
  have he : (∑ j, ∫ x, ‖g j x‖^2) = |r⁻¹| * (∑ j, ∫ x, ‖f j x‖^2) := by
    simp only [g,schwartzDilation_energy,Finset.mul_sum]
  rw [hv,he,ENNReal.ofReal_mul (abs_nonneg _)] at h
  have hp : ENNReal.ofReal |r⁻¹| ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr
    (abs_pos.mpr (inv_ne_zero hr.ne')))
  rw [mul_left_comm (K:ℝ≥0∞)] at h
  exact (ENNReal.mul_le_mul_iff_right hp ENNReal.ofReal_ne_top).mp h

theorem scaled_dyadic_hilbert_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (r : ℝ), 0 < r → ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (f : Fin N → κ → SchwartzMap ℝ ℂ),
      (∀ j k ξ, |ξ| < (a/r) * (2 : ℝ) ^ j.val → 𝓕 (f j k) ξ = 0) →
      (∀ j k ξ, (b/r) * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∑ k, ∫ x, ‖f j k x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := scaled_dyadic_scalar_annular_variation hL ha hb
  refine ⟨K,hK,?_⟩
  intro r hr N κ inst f hlow hhigh
  calc
    _ ≤ ∫⁻ x, ∑ k, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_mono
      intro x
      exact ennreal_complex_variation_coordinates (fun i => hilbertPartialBandSum f i x) N
    _ = ∑ k, ∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_finsetSum
      intro k _
      exact (measurable_finiteCubicVariation _ (partialBandSum_measurable (fun j => f j k)) N).ennreal_ofReal.pow_const _
    _ ≤ ∑ k, (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j k x‖ ^ 2) :=
      Finset.sum_le_sum (fun k _ => hbound r hr N (fun j => f j k)
        (fun j => hlow j k) (fun j => hhigh j k))
    _ = _ := by
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg]
      · congr 2
        exact Finset.sum_comm
      · intro k _
        exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_WeightedPacketEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially localized packet synthesis energy with arbitrary dual
coefficients. No local coefficient budget is assumed here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_component_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (rho : ι → ℝ) :
    (∑ k, ∑ i, ‖c i k‖ ^ 2 * rho i) = ∑ i, ‖c i‖ ^ 2 * rho i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceTransversePacketEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Slice energy with the full transverse decay retained. This is the
estimate required for a transverse polynomial of order 103; no horizontal
polynomial or horizontal center restriction is introduced. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem lattice_slice_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ×ℤ) (len : Fin N → ℝ)
    (a0 b0 W y C : ℝ) (hW : 0<W) (hlen : ∀ j, 0<len j)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j i, X j i=a0+len j*(site j i).1)
    (hZ : ∀ j i, Z j i=b0+W*(site j i).2)
    (hf : ∀ j i k x, ‖f j i k x‖≤C*
      (lineEnvelope (X j i) (len j) 1 x*lineEnvelope (Z j i) W 207 y)) :
    (∑ j, ∑ k, ∫ x, ‖packetSynthesis (fun i => c j i k) (fun i => f j i k) x‖^2)≤
      ((4*Real.pi)^2*C^2*Real.pi)*
        ∑ j, len j*∑ i, ‖c j i‖^2*lineEnvelope (Z j i) W 207 y := by
  let D := (4*Real.pi)^2
  have hD : 0≤D := sq_nonneg _
  have hs (j : Fin N) (k : κ) :
      (∫ x, ‖packetSynthesis (fun i => c j i k) (fun i => f j i k) x‖^2)≤
        (D*C^2*Real.pi)*len j*∑ i, ‖c j i k‖^2*lineEnvelope (Z j i) W 207 y := by
    let rho := fun i : ι j => lineEnvelope (Z j i) W 207 y
    have hrho (i : ι j) : 0 < rho i := by unfold rho lineEnvelope; positivity
    have hpoint (x : ℝ) :
        ‖packetSynthesis (fun i => c j i k) (fun i => f j i k) x‖^2≤
          D*C^2*∑ i, ‖c j i k‖^2*rho i*lineEnvelope (X j i) (len j) 1 x := by
      have hover : (∑ i, lineEnvelope (X j i) (len j) 1 x*rho i)≤D := by
        dsimp only [rho]
        simp_rw [hX,hZ]
        exact injective_tile_lattice_overlap (site j) (hinj j) a0 b0 (len j) W x y
          (hlen j).ne' hW.ne' (by norm_num) (by norm_num)
      have h := envelope_synthesis_square (fun i => c j i k) (fun i => f j i k x)
        (fun i => lineEnvelope (X j i) (len j) 1 x*rho i)
        (fun i => mul_pos (by unfold lineEnvelope; positivity) (hrho i)) hD hover
        (fun i => hf j i k x)
      simpa only [packetSynthesis_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using h
    have hi (i : ι j) : Integrable (fun x => ‖c j i k‖^2*rho i*
        lineEnvelope (X j i) (len j) 1 x) :=
      (integrable_lineEnvelope_one _ _ (hlen j)).const_mul _
    calc
      _ ≤ ∫ x, D*C^2*∑ i, ‖c j i k‖^2*rho i*lineEnvelope (X j i) (len j) 1 x :=
        integral_mono (((packetSynthesis (fun i => c j i k) (fun i => f j i k)).memLp 2 volume).integrable_norm_pow
          (by decide : (2:ℕ)≠0))
          ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _) hpoint
      _ = _ := by
        rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
        simp_rw [integral_const_mul,integral_lineEnvelope_one _ _ (hlen j)]
        rw [←Finset.sum_mul]
        dsimp only [rho]
        ring
  calc
    _ ≤ ∑ j, ∑ k, (D*C^2*Real.pi)*len j*
        ∑ i, ‖c j i k‖^2*lineEnvelope (Z j i) W 207 y :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hs j k))
    _ = _ := by
      simp_rw [←Finset.mul_sum,weighted_component_energy]
      simp only [D,←Finset.mul_sum,mul_assoc]


/-- The fixed transverse polynomial is paid for by 207 powers of
transverse packet decay; one power remains for integration. -/
theorem transverse_lattice_slice_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ×ℤ) (len : Fin N → ℝ)
    (a0 b0 b W y C : ℝ) (hW : 0<W) (hlen : ∀ j, 0<len j)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j i, X j i=a0+len j*(site j i).1)
    (hZ : ∀ j i, Z j i=b0+W*(site j i).2)
    (hcenter : ∀ j i, |Z j i-b|≤2*W)
    (hf : ∀ j i k x, ‖f j i k x‖≤C*
      (lineEnvelope (X j i) (len j) 1 x*lineEnvelope (Z j i) W 207 y)) :
    polynomialWeight b (2*W) 103 y^2*
      (∑ j, ∑ k, ∫ x, ‖packetSynthesis (fun i => c j i k) (fun i => f j i k) x‖^2)≤
      ((4*Real.pi)^2*C^2*Real.pi*16^103)*
        ∑ j, len j*∑ i, ‖c j i‖^2*lineEnvelope (Z j i) W 1 y := by
  let A := (4*Real.pi)^2*C^2*Real.pi
  have hA : 0≤A := by positivity
  have he (j : Fin N) (i : ι j) := polynomialWeight_sq_mul_envelope y (Z j i)
    b W (2*W) 103 1 hW (by positivity) (by linarith) (hcenter j i)
  simp only [Nat.reduceMul,Nat.reduceAdd] at he
  calc
    _ ≤ polynomialWeight b (2*W) 103 y^2*
        (A*∑ j, len j*∑ i, ‖c j i‖^2*lineEnvelope (Z j i) W 207 y) :=
      mul_le_mul_of_nonneg_left (lattice_slice_energy c f X Z site len a0 b0 W y C hW hlen hinj hX hZ hf)
        (sq_nonneg _)
    _ = A*∑ j, len j*∑ i, ‖c j i‖^2*
        (polynomialWeight b (2*W) 103 y^2*lineEnvelope (Z j i) W 207 y) := by
      simp only [Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
    _ ≤ A*∑ j, len j*∑ i, ‖c j i‖^2*(16^103*lineEnvelope (Z j i) W 1 y) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hlen j).le
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (he j i) (sq_nonneg _))
    _ = _ := by simp only [Finset.mul_sum,A,mul_assoc,mul_left_comm,mul_comm]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLatticeMultiscaleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary multiscale energy estimate for the original physical
lattice packets. Residue coloring has a fixed cost determined only by
the annular constants, not the number of lengths or vector bins. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

/-- The cutoff at one retained coefficient needs only that packet's
selector separation; all other coefficients may vanish. -/
theorem raw_fourier_cutoffs_at (P : SourceLatticePacket N κ ι)
    (t w cStar cEta CEta cb Cb : ℝ) (hw : 0 < w)
    (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (j : Fin N) (u : ι j) (k : κ)
    (hspectrum : ∀ ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η) ≠ 0 →
      |ξ+(t+P.rowSlope j)*η| ≤ cStar/P.length j ∧ cEta ≤ w*η ∧ w*η ≤ CEta)
    (hselector : cb*w/P.length j ≤ |P.rowSlope j| ∧ |P.rowSlope j| ≤ Cb*w/P.length j)
    (i : Fin 3) (y : ℝ) :
    (∀ ξ, |ξ| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 (P.raw i j u k y) ξ = 0) ∧
    (∀ ξ, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |ξ| →
      𝓕 (P.raw i j u k y) ξ = 0) := by
  have hsel : cb*w/P.length j ≤ |t-(t+P.rowSlope j)| ∧
      |t-(t+P.rowSlope j)| ≤ Cb*w/P.length j := by
    have heq : t-(t+P.rowSlope j) = -P.rowSlope j := by ring
    simpa only [heq,abs_neg] using hselector
  have h := sourcePacket_jet_fourier_cutoffs (P.physicalPacket t j u k)
    y t (t+P.rowSlope j) (P.length j) w cStar cEta CEta cb Cb
    (P.length_pos j) hw hcEta hcb hCb hspectrum hsel (P.frequency k) P.scale i
  have hraw : P.raw i j u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale i) y t :=
    P.raw_eq_physical_slice i j u k y t
  have heq (A : ℝ) : A/(2*Real.pi*P.length j) =
      ((A/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val := by
    rw [SourceLatticePacket.length,packet_annulus_dyadic_scale A P.topLength j.val P.topLength_pos.ne']
    ring
  rw [← hraw,heq,heq] at h
  exact h

end SourceLatticePacket

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

theorem slotted_spectrum (t w cStar cEta CEta : ℝ)
    (hspectrum : ∀ j l u k ξ η,
      planarAngularFourier (P.physicalPacket t j l u k) (ξ, η) ≠ 0 →
        |ξ + (t + P.rowSlope j l) * η| ≤ cStar / P.length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta)
    (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) (k : κ) (ξ η : ℝ) :
    planarAngularFourier ((P.slotted hcard b).physicalPacket t j p k) (ξ, η) ≠ 0 →
      |ξ + (t + (P.slotted hcard b).rowSlope j) * η| ≤
          cStar / (P.slotted hcard b).length j ∧
        cEta ≤ w * η ∧ w * η ≤ CEta := by
  simpa only [P.slotted_physicalPacket hcard, P.slotted_rowSlope hcard b j p,
    P.slotted_length hcard] using hspectrum j p.1.1 p.1.2 k ξ η

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change the reference direction of an actual translated source
lattice. Profiles, sites and physical packets are preserved exactly.
The reference-cone and width hypotheses imply the new shear and carrier
bounds; the absolute raw envelope is independent of the carrier bound. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

variable (delta M : ℝ) (hM : 0 ≤ M)
  (hshear : ∀ j, |(P.rowSlope j+delta)*P.length j/P.width| ≤ 1)
  (hcarrier : ∀ j k, |P.frequency k*(P.rowSlope j+delta)*P.length j| ≤ M)

/-- Unlike derivative bounds, the raw absolute envelope has no carrier
factor, even when the reference cone is much wider than a main annulus. -/
theorem raw_absolute_envelope (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤
      ((2^P.order*P.profileBound)*P.ratioBound^2)*
        (lineEnvelope (P.actualX j u) (P.length j) P.order x*
          lineEnvelope (P.actualZ j u) P.width P.order y) := by
  let C := P.ratioBound^2*P.profileBound
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) P.profileBound_pos.le
  have hprofile : ∀ z, ‖planarProfileJet (P.profile j u k) (P.scale/P.width) i z‖ ≤ C*
      (lineEnvelope 0 1 (2*P.order) z.1*lineEnvelope 0 1 (2*P.order) z.2) := by
    intro z
    exact (planar_profile_envelope (P.profile j u k) (2*P.order) (P.scale/P.width)
      P.ratioBound P.ratioBound_ge_one P.scale_bound i z).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (P.profile_bound j u k) (sq_nonneg _))
        (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)))
  have h := modulatedPlanarSlice_envelope (planarProfileJet (P.profile j u k) (P.scale/P.width) i)
    (P.actualX j u) (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
    y C (P.length_pos j).ne' P.order hC (P.raw_shear_bound j) hprofile x
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [raw,modulatedPlanarJet,div_eq_mul_inv,C])
  ring

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCarrierFreeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive error envelope must not inherit the large carrier bound
of the wide reference cone. The exact raw norm is independent of it. -/

noncomputable section
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem absoluteConstant_pos (P : SourceLatticePacket N κ ι) : 0 < P.absoluteConstant := by
  have hR : 0 < P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  have hB := P.profileBound_pos
  unfold absoluteConstant
  positivity

theorem raw_absolute_lattice_envelope (P : SourceLatticePacket N κ ι)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.absoluteConstant*
      (lineEnvelope (P.length j*(P.snappedSite j u).1) (P.length j) P.order x*
        lineEnvelope (P.width*(P.snappedSite j u).2) P.width P.order y) := by
  apply (P.raw_absolute_envelope i j u k y x).trans
  have hB := P.profileBound_pos
  have hA : 0 ≤ (2^P.order*P.profileBound)*P.ratioBound^2 := by positivity
  have h := mul_le_mul_of_nonneg_left (P.snapped_envelope j u y x) hA
  simpa only [absoluteConstant,mul_assoc] using h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedTreeMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially weighted interval-maximal synthesis on actual separated
source trees, conditional only on the published scalar Lépingle input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert

private theorem continuous_interval_max {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => intervalOscillation (fun n => F n x) N 0 N) := by
  classical
  let v := fun (q : Fin (N+1)×Fin (N+1)) (x : X) =>
    if 0≤q.1.val ∧ q.1.val≤q.2.val ∧ q.2.val≤N then ‖F q.2 x-F q.1 x‖ else 0
  have hv (q) : Continuous (v q) := by
    by_cases hq : 0≤q.1.val ∧ q.1.val≤q.2.val ∧ q.2.val≤N
    · simpa only [v,ite_eq_left hq,Pi.sub_apply] using ((hF q.2).sub (hF q.1)).norm
    · simp only [v,ite_eq_right hq]; exact continuous_const
  have h := Continuous.finset_sup' Finset.univ_nonempty (fun q _ => hv q)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [intervalOscillation,v,Finset.sup'_apply]


namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem physicalTreePartial_continuous (P : SourceLatticePacket N κ ι)
    (t : ℝ) (c : ∀ j, ι j → EuclideanSpace ℂ κ) (n : ℕ) :
    Continuous (P.physicalTreePartial t c n) := by
  classical
  unfold physicalTreePartial packetPartialSum
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val<n
  · simp only [ite_eq_left hj]
    unfold planarFixedSynthesis
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_finsetSum _ fun u _ =>
      continuous_const.mul (P.physicalPacket t j u k).continuous
  · simp only [ite_eq_right hj]; exact continuous_const

theorem physicalTreeVariation_continuous (P : SourceLatticePacket N κ ι)
    (t : ℝ) (c : ∀ j, ι j → EuclideanSpace ℂ κ) : Continuous (P.physicalTreeVariation t c) :=
  continuous_cubicVariation _ (P.physicalTreePartial_continuous t c) N

theorem physicalTreeMaximal_continuous (P : SourceLatticePacket N κ ι)
    (t : ℝ) (c : ∀ j, ι j → EuclideanSpace ℂ κ) : Continuous (P.physicalTreeMaximal t c) :=
  continuous_interval_max _ (P.physicalTreePartial_continuous t c) N

end SourceLatticePacket


namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

theorem physicalTreePartial_continuous (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) :
    Continuous (P.physicalTreePartial t c n) := by
  classical
  unfold physicalTreePartial packetPartialSum
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val<n
  · simp only [ite_eq_left hj]
    unfold planarFixedSynthesis
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_finsetSum _ fun u _ =>
      continuous_const.mul (P.physicalPacket t j u.1 u.2 k).continuous
  · simp only [ite_eq_right hj]; exact continuous_const

theorem physicalTreeMaximal_continuous (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    Continuous (P.physicalTreeMaximal t c) :=
  continuous_interval_max _ (P.physicalTreePartial_continuous t c) N

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceTransverseTreeVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transverse order-103 tree estimate needed by the ordinary-tree
argument. It uses only the published scalar Lepingle input and retains
one integrable transverse decay power. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert

private theorem integral_from_lintegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (C : ℝ) (hC : 0≤C)
    (hfm : AEStronglyMeasurable f μ) (hf : ∀ x, 0≤f x)
    (hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ)≤ENNReal.ofReal C) :
    Integrable f μ ∧ (∫ x, f x ∂μ)≤C := by
  have hi : Integrable f μ := ⟨hfm,(hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hf)).mpr (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hlin

namespace SourceLatticePacket

theorem exists_transverse_physical_tree_variation (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j, ι j → EuclideanSpace ℂ κ,
      (∀ j u, |P.actualZ j u-b|≤P.width) →
      (∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (_u : ι j), cb*w/P.length j≤|P.rowSlope j| ∧
        |P.rowSlope j|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*
        P.physicalTreeVariation t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤C*P.absoluteConstant^2*
        ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  let lower := (cEta*cb-cStar)/(2*Real.pi)
  let upper := (CEta*Cb+cStar)/(2*Real.pi)
  have hlower : 0<lower := div_pos (sub_pos.mpr hgap) (by positivity)
  have hupper : 0≤upper := div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  obtain ⟨K,hK,hvar⟩ := scaled_dyadic_hilbert_annular_variation hL hlower hupper
  let A := (4*Real.pi)^2*Real.pi*(16:ℝ)^103
  have hA : 0<A := mul_pos (mul_pos (sq_pos_of_pos (by positivity)) Real.pi_pos)
    (pow_pos (by norm_num) _)
  have hKr : 0<(K:ℝ) := by exact_mod_cast hK
  refine ⟨(K:ℝ)*A*Real.pi,mul_pos (mul_pos hKr hA) Real.pi_pos,?_⟩
  intro N κ ι _ _ P t w b hw horder c hZ hspectrum hselector
  let f := fun y j k => packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y)
  let M := fun y => A*P.absoluteConstant^2*
    ∑ j, P.length j*∑ u, ‖c j u‖^2*
      lineEnvelope (P.width*(P.snappedSite j u).2) P.width 1 y
  have hPy (j : Fin N) (u : ι j) : |P.width*(P.snappedSite j u).2-b|≤2*P.width := by
    have he := snappedLatticeSite_vertical (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) P.width_pos (P.site j u)
    change |P.actualZ j u-P.width*(P.snappedSite j u).2|≤P.width at he
    calc
      _ ≤ |P.width*(P.snappedSite j u).2-P.actualZ j u|+|P.actualZ j u-b| := abs_sub_le _ _ _
      _ ≤ P.width+P.width := add_le_add (by simpa only [abs_sub_comm] using he) (hZ j u)
      _ = _ := by ring
  have hraw (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
      P.physicalPacket t j u k (x,y+t*x)=P.raw 0 j u k y x := by
    have hh : P.raw 0 j u k y = planarSchwartzSlice
        (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale 0) y t :=
      P.raw_eq_physical_slice 0 j u k y t
    simpa only [planarCovariantJet,ite_true, if_true,planarSchwartzSlice_apply] using
      (congrArg (fun g : SchwartzMap ℝ ℂ => g x) hh).symm
  have hpartial (y x : ℝ) (n : ℕ) : P.physicalTreePartial t c n (x,y+t*x)=
      hilbertPartialBandSum (f y) n x := by
    rw [hilbertPartialBandSum_eq_packetPartialSum]
    apply congrArg (fun v : Fin N → EuclideanSpace ℂ κ => packetPartialSum v n)
    funext j
    ext k
    simp only [planarFixedSynthesis,WithLp.ofLp_toLp,f,packetSynthesis_apply,hraw]
  have hlow (y : ℝ) (j : Fin N) (k : κ) (ξ : ℝ) (hξ : |ξ|<(lower/P.topLength)*(2:ℝ)^j.val) :
      𝓕 (f y j k) ξ=0 :=
    packetSynthesis_fourier_zero _ _ ξ fun u =>
      (P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u) 0 y).1 ξ hξ
  have hhigh (y : ℝ) (j : Fin N) (k : κ) (ξ : ℝ) (hξ : (upper/P.topLength)*(2:ℝ)^j.val < |ξ|) :
      𝓕 (f y j k) ξ=0 :=
    packetSynthesis_fourier_zero _ _ ξ fun u =>
      (P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u) 0 y).2 ξ hξ
  have hline (y : ℝ) := hvar P.topLength P.topLength_pos N κ (f y) (hlow y) (hhigh y)
  have henergy (y : ℝ) : polynomialWeight b (2*P.width) 103 y^2*
      (∑ j, ∑ k, ∫ x, ‖f y j k x‖^2)≤M y := by
    have h := transverse_lattice_slice_energy c (fun j u k => P.raw 0 j u k y)
      (fun j u => P.length j*(P.snappedSite j u).1)
      (fun j u => P.width*(P.snappedSite j u).2) P.snappedSite P.length
      0 0 b P.width y P.absoluteConstant P.width_pos P.length_pos P.snappedSite_injective
      (by intros; ring) (by intros; ring) hPy (by
        intro j u k x
        apply (P.raw_absolute_lattice_envelope 0 j u k y x).trans
        apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
        exact mul_le_mul (lineEnvelope_antitone _ _ _ (by omega : 1≤P.order))
          (lineEnvelope_antitone _ _ _ horder)
          (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    simpa only [f,M,A,mul_assoc,mul_left_comm,mul_comm] using h
  let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*
    P.physicalTreeVariation t c z^2
  have hEc : Continuous E := by
    have hp : Continuous (fun z : ℝ×ℝ => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)) := by
      unfold polynomialWeight
      fun_prop
    exact (hp.pow 2).mul ((P.physicalTreeVariation_continuous t c).pow 2)
  have hEeq (x y : ℝ) : ENNReal.ofReal (E (x,y+t*x))=
      ENNReal.ofReal (polynomialWeight b (2*P.width) 103 y^2)*
        ENNReal.ofReal (finiteCubicVariation (fun n => hilbertPartialBandSum (f y) n x) N)^(2/3:ℝ) := by
    simp only [E,physicalTreeVariation,hpartial,cubicVariation_sq]
    rw [show y+t*x-t*x=y by ring,ENNReal.ofReal_mul (sq_nonneg _),
      ←ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num : (0:ℝ)≤2/3)]
  have hM : Integrable M := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    apply Integrable.const_mul
    exact integrable_finsetSum _ fun u _ =>
      (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _
  have hM0 (y : ℝ) : 0≤M y := by
    exact mul_nonneg (mul_nonneg hA.le (sq_nonneg _)) (Finset.sum_nonneg fun j _ =>
      mul_nonneg (P.length_pos j).le (Finset.sum_nonneg fun u _ =>
        mul_nonneg (sq_nonneg _) (lineEnvelope_nonneg _ _ _ _)))
  have hIntM : (∫ y, M y)=A*P.absoluteConstant^2*Real.pi*
      ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
    dsimp only [M]
    rw [integral_const_mul,integral_finsetSum _ (fun j _ =>
      (integrable_finsetSum _ fun u _ =>
        (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _).const_mul _)]
    simp_rw [integral_const_mul,integral_finsetSum _ (fun u _ =>
      (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _),
      integral_const_mul,integral_lineEnvelope_one _ P.width P.width_pos]
    simp only [Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
  have hlin : (∫⁻ z, ENNReal.ofReal (E z) ∂volume.prod volume)≤
      (K:ℝ≥0∞)*ENNReal.ofReal (∫ y, M y) := by
    rw [←(slopeShear_measurePreserving t).lintegral_comp hEc.measurable.ennreal_ofReal]
    rw [lintegral_prod_symm (fun z : ℝ×ℝ => ENNReal.ofReal (E (slopeShear t z)))
      ((hEc.measurable.comp (slopeShear t).measurable).ennreal_ofReal.aemeasurable)]
    calc
      _ ≤ ∫⁻ y, (K:ℝ≥0∞)*ENNReal.ofReal (M y) := by
        apply lintegral_mono
        intro y
        change (∫⁻ x, ENNReal.ofReal (E (x,y+t*x)))≤_
        simp_rw [hEeq]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc
          _ ≤ ENNReal.ofReal (polynomialWeight b (2*P.width) 103 y^2)*
              ((K:ℝ≥0∞)*ENNReal.ofReal _) := mul_le_mul_right (hline y) _
          _ = (K:ℝ≥0∞)*ENNReal.ofReal (polynomialWeight b (2*P.width) 103 y^2*_) := by
            rw [ENNReal.ofReal_mul (sq_nonneg _)]; ac_rfl
          _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal (henergy y)) _
      _ = _ := by
        rw [lintegral_const_mul' _ _ (by simp),
          ←ofReal_integral_eq_lintegral_ofReal hM (Filter.Eventually.of_forall hM0)]
  have hsum0 : 0≤∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun u _ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos j).le) P.width_pos.le
  apply integral_from_lintegral (volume.prod volume) E _
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hKr.le hA.le) Real.pi_pos.le)
      (sq_nonneg P.absoluteConstant)) hsum0)
    hEc.aestronglyMeasurable (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hIntM] at hlin
  have hkc : ENNReal.ofReal (K:ℝ)=(K:ℝ≥0∞) := by simp
  rw [←hkc,←ENNReal.ofReal_mul K.coe_nonneg] at hlin
  convert hlin using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ac_rfl

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceTransverseTreeMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transverse polynomial energy for the actual interval maximum,
including finite label slots, from the published scalar Lépingle input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert

private theorem interval_max_le_variation_p0 {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : intervalOscillation F N 0 N ≤ cubicVariation F N := by
  obtain ⟨a,b,_,hab,hb,heq⟩ := exists_intervalOscillation_eq F N 0 N (Nat.zero_le _)
  rw [heq]
  exact increment_le_cubicVariation F N a b hab hb

private theorem interval_max_sum_le_p0 {I E : Type*} [Fintype I] [NormedAddCommGroup E]
    (F : I → ℕ → E) (N : ℕ) :
    intervalOscillation (fun n => ∑ i, F i n) N 0 N≤
      ∑ i, intervalOscillation (F i) N 0 N := by
  classical
  unfold intervalOscillation
  apply Finset.sup'_le
  intro q _
  split_ifs with hq
  · rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact increment_le_intervalOscillation (F i) N 0 N q.1 q.2
      (Nat.zero_le _) hq.2.1 hq.2.2 le_rfl
  · exact Finset.sum_nonneg fun i _ => intervalOscillation_nonneg (F i) N 0 N

namespace SourceLatticePacket

theorem exists_transverse_physical_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j, ι j → EuclideanSpace ℂ κ,
      (∀ j u, |P.actualZ j u-b|≤P.width) →
      (∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (_u : ι j), cb*w/P.length j≤|P.rowSlope j| ∧
        |P.rowSlope j|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2 *
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤C*P.absoluteConstant^2 *
        ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hbound⟩ := exists_transverse_physical_tree_variation hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ ι _ _ P t w b hw horder c hZ hspectrum hselector
  obtain ⟨hi,hb⟩ := hbound N κ ι P t w b hw horder c hZ hspectrum hselector
  have hp (z : ℝ×ℝ) : P.physicalTreeMaximal t c z≤P.physicalTreeVariation t c z :=
    interval_max_le_variation_p0 _ N
  have hle (z : ℝ×ℝ) : polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*P.physicalTreeMaximal t c z^2≤
      polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*P.physicalTreeVariation t c z^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (intervalOscillation_nonneg _ _ _ _) (hp z) 2) (sq_nonneg _)
  have hc : Continuous (fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*P.physicalTreeMaximal t c z^2) := by
    have hwc : Continuous (fun z : ℝ×ℝ => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)) := by
      unfold polynomialWeight; fun_prop
    exact (hwc.pow 2).mul ((P.physicalTreeMaximal_continuous t c).pow 2)
  have him : Integrable (fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*P.physicalTreeMaximal t c z^2)
      (volume.prod volume) := hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg (polynomialWeight b (2*P.width) 103 (z.2-t*z.1)))
          (sq_nonneg (P.physicalTreeMaximal t c z)))] using hle z)
  exact ⟨him,(integral_mono him hi hle).trans hb⟩

end SourceLatticePacket

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

theorem exists_transverse_labeled_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j l u, |P.actualZ j l u-b|≤P.width) →
      (∀ j l u k ξ η, planarAngularFourier (P.physicalPacket t j l u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j) (_u : Item j l), cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2 *
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(B:ℝ)*C*P.absoluteConstant^2 *
        ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hbound⟩ := SourceLatticePacket.exists_transverse_physical_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w b hw horder c hZ hspectrum hselector
  let weight := fun z : ℝ×ℝ => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)
  let coeff := fun (s : Fin B) j (u : P.SlotItem hcard s j) => c j u.1.1 u.1.2
  let M := fun s : Fin B => (P.slotted hcard s).physicalTreeMaximal t (coeff s)
  let mass := fun s : Fin B => ∑ j, ∑ u : P.SlotItem hcard s j,
    ‖coeff s j u‖^2*P.length j*P.width
  have hslot (s : Fin B) : Integrable (fun z => weight z^2*M s z^2) (volume.prod volume) ∧
      (∫ z, weight z^2*M s z^2 ∂volume.prod volume)≤C*P.absoluteConstant^2*mass s := by
    apply hbound N κ (P.SlotItem hcard s) (P.slotted hcard s) t w b hw horder (coeff s)
    · intro j u
      change |(P.slotted hcard s).actualZ j u-b|≤P.width
      simpa only [P.slotted_actualZ hcard] using hZ j u.1.1 u.1.2
    · exact P.slotted_spectrum hcard t w cStar cEta CEta hspectrum s
    · intro j u
      simpa only [P.slotted_length hcard,P.slotted_rowSlope hcard s j u] using
        hselector j u.1.1 u.1.2
  have hpartial (n : ℕ) (z : ℝ×ℝ) :
      (∑ s : Fin B, (P.slotted hcard s).physicalTreePartial t (coeff s) n z)=
        P.physicalTreePartial t c n z := by
    simp only [SourceLatticePacket.physicalTreePartial,physicalTreePartial,packetPartialSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val<n
    · simp only [ite_eq_left hj]
      ext k
      simp only [planarFixedSynthesis,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,
        P.slotted_physicalPacket hcard,coeff]
      simpa only [Fintype.sum_sigma] using P.sum_slotted hcard j
        (fun l u => c j l u k*P.physicalPacket t j l u k z)
    · simp only [ite_eq_right hj,Finset.sum_const_zero]
  have hmax (z : ℝ×ℝ) : P.physicalTreeMaximal t c z≤∑ s, M s z := by
    have heq : (fun n => P.physicalTreePartial t c n z)=
        (fun n => ∑ s : Fin B, (P.slotted hcard s).physicalTreePartial t (coeff s) n z) :=
      funext fun n => (hpartial n z).symm
    unfold physicalTreeMaximal
    rw [heq]
    exact interval_max_sum_le_p0 _ N
  have hwc : Continuous weight := by
    dsimp only [weight]
    unfold polynomialWeight
    fun_prop
  have hM0 (s : Fin B) (z : ℝ×ℝ) : 0≤M s z := intervalOscillation_nonneg _ _ _ _
  have hM2 (s : Fin B) : MemLp (fun z => weight z*M s z) 2 (volume.prod volume) := by
    have hm : AEStronglyMeasurable (fun z => weight z*M s z) (volume.prod volume) :=
      (hwc.mul ((P.slotted hcard s).physicalTreeMaximal_continuous t (coeff s))).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hm).2
    simpa only [mul_pow] using (hslot s).1
  have hsum2 := memLp_finsetSum Finset.univ (fun s _ => hM2 s)
  have hsumI := hsum2.integrable_norm_pow (by decide : 2≠0)
  have hcost := weighted_integral_sum_square (volume.prod volume)
    (fun s z => weight z*M s z) hM2 (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcost
  have hpoint (z : ℝ×ℝ) : weight z^2*P.physicalTreeMaximal t c z^2≤
      ‖∑ s, weight z*M s z‖^2 := by
    rw [←Finset.mul_sum,Real.norm_eq_abs,sq_abs,mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (intervalOscillation_nonneg _ _ _ _) (hmax z) 2) (sq_nonneg _)
  have hE : Integrable (fun z => weight z^2*P.physicalTreeMaximal t c z^2) (volume.prod volume) := by
    apply hsumI.mono'
      ((hwc.pow 2).mul ((P.physicalTreeMaximal_continuous t c).pow 2)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖weight z^2*P.physicalTreeMaximal t c z^2‖ ≤ ‖∑ s, weight z*M s z‖^2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg (weight z))
      (sq_nonneg (P.physicalTreeMaximal t c z)))]
    exact hpoint z
  have hmass : (∑ s, mass s)=
      ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
    dsimp only [mass,coeff]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact P.sum_slotted hcard j (fun l u => ‖c j l u‖^2*P.length j*P.width)
  refine ⟨hE,(integral_mono hE hsumI hpoint).trans (hcost.trans ?_)⟩
  simp only [Real.norm_eq_abs,mul_pow,sq_abs]
  calc
    _ ≤ (B:ℝ)*∑ s, C*P.absoluteConstant^2*mass s :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => (hslot s).2) (Nat.cast_nonneg B)
    _ = _ := by rw [←Finset.mul_sum,hmass]; ring

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

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedTreeMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transverse maximal energy needs separation only on packets whose
coefficients are nonzero. Restriction retains the original partial sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

private theorem partial_as_index_sum (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) (z : ℝ×ℝ) :
    P.physicalTreePartial t c n z=∑ q : P.PacketIndex,
      if q.1.val<n then WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        P.physicalPacket t q.1 q.2.1 q.2.2 k z) else 0 := by
  ext k
  simp only [physicalTreePartial,packetPartialSum,WithLp.ofLp_sum,Finset.sum_apply,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val<n
  · simp only [hj,ite_true, if_true,planarFixedSynthesis,WithLp.ofLp_toLp,Fintype.sum_sigma]
  · simp only [hj,ite_false, if_false,WithLp.ofLp_zero,Pi.zero_apply,Finset.sum_const_zero]

/-- Removing zero coefficients leaves every actual partial sum unchanged. -/
theorem restrict_nonzero_partial
    (Q : Finset P.PacketIndex) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ q : P.PacketIndex, q∉Q → c q.1 q.2.1 q.2.2=0)
    (n : ℕ) (z : ℝ×ℝ) :
    (P.restrictPackets Q).physicalTreePartial t (fun j l v => c j l v.val) n z=
      P.physicalTreePartial t c n z := by
  rw [partial_as_index_sum,partial_as_index_sum]
  change (∑ q : (P.restrictPackets Q).PacketIndex,
    if q.1.val<n then WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2.val k*
      P.physicalPacket t q.1 q.2.1 q.2.2.val k z) else 0)=_
  rw [P.sum_restrictPackets Q (fun q => if q.1.val<n then WithLp.toLp 2
    (fun k => c q.1 q.2.1 q.2.2 k*P.physicalPacket t q.1 q.2.1 q.2.2 k z) else 0)]
  apply Finset.sum_subset (Finset.subset_univ Q)
  intro q _ hq
  rw [hc q hq]
  simp only [WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
  split_ifs <;> rfl

theorem exists_supported_transverse_tree_maximal_oai (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j l v, |P.actualZ j l v-b|≤P.width) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j l v, c j l v≠0 → cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(B:ℝ)*C*P.absoluteConstant^2*
        ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hmax⟩ := exists_transverse_labeled_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w b hw horder c hZ hspectrum hselector
  let Q := Finset.univ.filter (fun q : P.PacketIndex => c q.1 q.2.1 q.2.2≠0)
  let R := P.restrictPackets Q
  let d := fun j (l : R.labels j) (v : P.RestrictedPacketItem Q j l) => c j l v.val
  have hnz (j : Fin N) (l : R.labels j) (v : P.RestrictedPacketItem Q j l) : c j l v.val≠0 := by
    have hm := (P.restrictedPacketEquiv Q ⟨j,⟨l,v⟩⟩).property
    exact (Finset.mem_filter.mp hm).2
  have hz (q : P.PacketIndex) (hq : q∉Q) : c q.1 q.2.1 q.2.2=0 := by
    simpa only [Q,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hq
  obtain ⟨hi,hb⟩ := hmax N κ Label (P.RestrictedPacketItem Q) R B hcard t w b hw horder d
    (fun j l v => hZ j l v.val) (fun j l v k ξ η => hspectrum j l v.val k ξ η)
    (fun j l v => hselector j l v.val (hnz j l v))
  have heq (z : ℝ×ℝ) : R.physicalTreeMaximal t d z=P.physicalTreeMaximal t c z := by
    unfold physicalTreeMaximal
    congr 1
    funext n
    exact P.restrict_nonzero_partial Q t c hz n z
  have hmass : (∑ j, ∑ l : R.labels j, ∑ v : P.RestrictedPacketItem Q j l,
      ‖d j l v‖^2*R.length j*R.width)=
      ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width := by
    have hsum := P.sum_restrictPackets Q
      (fun q => ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width)
    calc
      _ = ∑ q∈Q, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
        change (∑ j, ∑ l : P.labels j, ∑ v : P.RestrictedPacketItem Q j l,
          ‖c j l v.val‖^2*P.length j*P.width)=_
        simp only [Fintype.sum_sigma] at hsum
        convert hsum using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
      _ = ∑ q : P.PacketIndex, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
        apply Finset.sum_subset (Finset.subset_univ Q)
        intro q _ hq
        rw [hz q hq]
        simp only [norm_zero,zero_pow (by decide : 2≠0),zero_mul]
      _ = _ := by simp only [Fintype.sum_sigma]
  simp only [heq] at hi hb
  rw [hmass] at hb
  exact ⟨hi,hb⟩

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal_oai := @OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal_oai
