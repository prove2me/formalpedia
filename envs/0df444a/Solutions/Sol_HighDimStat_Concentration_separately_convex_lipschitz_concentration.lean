-- Prove2me | solution 1 for HighDimStat.Concentration.separately_convex_lipschitz_concentration
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T21:42:46.57268+00:00
-- url     : https://prove2.me/submissions/c31f4b3d-5000-4e7b-93db-9b1f0f86fbb1

import Mathlib
import Definitions.Def_HighDimStat_Concentration_IsSeparatelyConvex
import Definitions.Def_HighDimStat_Concentration_IsLLipschitz
import Definitions.Def_HighDimStat_Concentration_phiEntropy
import Theorems.Thm_bousquet_massart_modified_lsi_summand_psi
import Theorems.Thm_entropy_n_coordinate_han_subadditivity_measure_pi_pos
import Theorems.Thm_HighDimStat_Concentration_herbst_argument

-- Source module: ConcentrationGradientPair

open InnerProductSpace
open scoped RealInnerProductSpace

namespace GaussianConcentration

set_option maxHeartbeats 800000

/-- Contracting two derivatives over an orthonormal basis has the dimension-free bound
required in Gaussian covariance interpolation. -/
lemma dual_basis_product_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : OrthonormalBasis ι ℝ E) (p q : E →L[ℝ] ℝ) :
    |∑ i, p (b i) * q (b i)| ≤ ‖p‖ * ‖q‖ := by
  let u := (toDual ℝ E).symm p
  let v := (toDual ℝ E).symm q
  have hp (i : ι) : p (b i) = ⟪u, b i⟫ :=
    (toDual_symm_apply (𝕜 := ℝ) (y := p) (x := b i)).symm
  have hq (i : ι) : q (b i) = ⟪b i, v⟫ := by
    rw [real_inner_comm]
    exact (toDual_symm_apply (𝕜 := ℝ) (y := q) (x := b i)).symm
  simp_rw [hp, hq, b.sum_inner_mul_inner]
  exact (abs_real_inner_le_norm u v).trans_eq (by simp [u, v])

lemma lipschitz_gradient_pair_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (x y : EuclideanSpace ℝ (Fin n)) :
    |∑ i, fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) *
      fderiv ℝ f y (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ (K : ℝ)^2 := by
  apply (dual_basis_product_bound (EuclideanSpace.basisFun (Fin n) ℝ) _ _).trans
  have hx := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)
  have hy := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := y)
  simpa only [pow_two] using mul_le_mul hx hy (norm_nonneg _) K.coe_nonneg

end GaussianConcentration


-- Source module: ConcentrationLipschitzAveraging

open MeasureTheory Real

namespace GaussianConcentration

set_option maxHeartbeats 800000

/-- Averaging translates against a probability kernel preserves the exact Lipschitz constant.
This is the regularity invariant needed when smoothing the native concentration target. -/
lemma lipschitz_average {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {K : NNReal} {f : E → ℝ}
    (hf : LipschitzWith K f) (hi : ∀ x, Integrable (fun y => f (x-y)) μ) :
    LipschitzWith K (fun x => ∫ y, f (x-y) ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, ← integral_sub (hi x) (hi z), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y, ‖f (x-y)-f (z-y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (K : ℝ) * dist x z ∂μ := by
      apply integral_mono ((hi x).sub (hi z)).norm (integrable_const _)
      intro y
      have h := hf.dist_le_mul (x-y) (z-y)
      simpa only [Real.dist_eq, Real.norm_eq_abs, dist_sub_right, Pi.sub_apply] using h
    _ = (K : ℝ) * dist x z := by simp

/-- A probability kernel supported in a small ball gives a uniform smoothing error. -/
lemma average_sub_le {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {K : NNReal} {f : E → ℝ}
    (hf : LipschitzWith K f) (hi : ∀ x, Integrable (fun y => f (x-y)) μ)
    {ε : ℝ} (hsupport : ∀ᵐ y ∂μ, ‖y‖ ≤ ε) (x : E) :
    |(∫ y, f (x-y) ∂μ) - f x| ≤ (K : ℝ)*ε := by
  have hconst : (∫ _y : E, f x ∂μ) = f x := by simp
  rw [← hconst, ← integral_sub (hi x) (integrable_const _), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y, ‖f (x-y)-f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (K : ℝ)*ε ∂μ := by
      apply integral_mono_ae ((hi x).sub (integrable_const _)).norm (integrable_const _)
      filter_upwards [hsupport] with y hy
      have h := hf.dist_le_mul (x-y) x
      have hd : dist (x-y) x = ‖y‖ := by rw [dist_eq_norm]; simp
      rw [hd] at h
      exact (show ‖f (x-y)-f x‖ ≤ (K : ℝ)*‖y‖ from h).trans
        (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
    _ = _ := by simp

end GaussianConcentration


-- Source module: TalagrandGeometry

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 800000

/-- The native statement's explicit square-root distance is the Euclidean
metric. Using `|L|` also covers the zero-dimensional case without imposing
an extra sign assumption on the statement. -/
lemma native_lipschitz_euclidean {n : ℕ} {f : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hLip : IsLLipschitz f L) :
    LipschitzWith ‖L‖₊ (fun x : EuclideanSpace ℝ (Fin n) => f (fun i => x i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  have he : Real.sqrt (∑ i, (x i - y i) ^ 2) = ‖x - y‖ := by
    rw [EuclideanSpace.norm_eq]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  exact (hLip _ _).trans (by
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))

lemma native_lipschitz_continuous {n : ℕ} {f : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hLip : IsLLipschitz f L) : Continuous f := by
  convert (native_lipschitz_euclidean hLip).continuous.comp
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)) using 1
  funext x
  rfl

/-- The supporting-line inequality in the direction needed for the upper-tail
entropy estimate. The derivative is evaluated at the larger function value. -/
lemma convex_gap_le_deriv_mul {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g)
    {x y : ℝ} (hd : DifferentiableAt ℝ g x) :
    g x - g y ≤ deriv g x * (x - y) := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have h := hg.deriv_le_slope (Set.mem_univ x) (Set.mem_univ y) hxy hd
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hxy)).mp h
    nlinarith
  · subst y
    simp
  · have h := hg.slope_le_deriv (Set.mem_univ y) (Set.mem_univ x) hyx hd
    rw [slope_def_field] at h
    exact (div_le_iff₀ (sub_pos.mpr hyx)).mp h

/-- A nonnegative decrement of a convex coordinate function is controlled by
its derivative at the starting point and the width of the support interval. -/
lemma convex_coordinate_gap_sq_le {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g)
    {a b x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hd : DifferentiableAt ℝ g x) (hgap : g y ≤ g x) :
    (g x - g y) ^ 2 ≤ (deriv g x) ^ 2 * (b - a) ^ 2 := by
  have hwidth : 0 ≤ b - a := by linarith [hx.1, hx.2]
  have hdist : |x - y| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hbound : g x - g y ≤ |deriv g x| * (b - a) := by
    calc
      _ ≤ deriv g x * (x - y) := convex_gap_le_deriv_mul hg hd
      _ ≤ |deriv g x * (x - y)| := le_abs_self _
      _ = |deriv g x| * |x - y| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr hgap) hbound 2
  simpa only [mul_pow, sq_abs] using hsq

/-- The sum of squared directional derivatives inherits the Euclidean
Lipschitz constant without a factor depending on the number of coordinates. -/
lemma euclidean_gradient_sq_sum_le {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, (fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) ≤
      (K : ℝ) ^ 2 := by
  have h := GaussianConcentration.lipschitz_gradient_pair_bound hf x x
  simp only [← pow_two] at h
  exact (le_abs_self _).trans h

end HighDimStat.Concentration


-- Source module: TalagrandEntropy

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 800000

lemma exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let F := fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y)
  let D := fun y : ℝ => -1 + y + Real.exp (-y)
  have hd : ∀ y ∈ Set.Icc 0 x, HasDerivAt F (D y) y := by
    intro y hy
    convert (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      ((hasDerivAt_pow 2 y).div_const 2)).sub ((hasDerivAt_id y).neg.exp) using 1 <;>
      first | rfl | (dsimp [F, D]; ring)
  have hm : MonotoneOn F (Set.Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    dsimp [D]
    linarith [Real.add_one_le_exp (-y)]
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [F] using hh

/-- A constant lower reference gives an entropy estimate in terms of the
squared decrement. This is the one-coordinate input to tensorization. -/
lemma entropy_exp_le_sq_gap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {lam c : ℝ}
    (hlam : 0 ≤ lam)
    (hexp : Integrable (fun ω => Real.exp (lam * Z ω)) μ)
    (hzexp : Integrable (fun ω => lam * Z ω * Real.exp (lam * Z ω)) μ)
    (hgap : ∀ᵐ ω ∂μ, c ≤ Z ω)
    (hsq : Integrable (fun ω => Real.exp (lam * Z ω) * (Z ω - c) ^ 2) μ) :
    phiEntropy (fun ω => Real.exp (lam * Z ω)) μ ≤
      lam ^ 2 / 2 * ∫ ω, Real.exp (lam * Z ω) * (Z ω - c) ^ 2 ∂μ := by
  have hid (ω : Ω) :
      Real.exp (lam * Z ω) *
        (Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c)) =
      Real.exp (lam * c) - Real.exp (lam * Z ω) +
        lam * Z ω * Real.exp (lam * Z ω) -
        (lam * c) * Real.exp (lam * Z ω) := by
    have he : Real.exp (lam * Z ω) * Real.exp (-(lam * (Z ω - c))) =
        Real.exp (lam * c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_add, mul_sub, mul_one, he]
    ring
  have hpsi : Integrable (fun ω => Real.exp (lam * Z ω) *
      (Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c))) μ := by
    have hi := ((integrable_const (Real.exp (lam * c))).sub hexp).add hzexp
    have hi' := hi.sub (hexp.const_mul (lam * c))
    exact hi'.congr (ae_of_all _ (fun ω => (hid ω).symm))
  have hrhs : Integrable (fun ω => lam ^ 2 / 2 *
      (Real.exp (lam * Z ω) * (Z ω - c) ^ 2)) μ := hsq.const_mul _
  calc
    _ = lam * (∫ ω, Z ω * Real.exp (lam * Z ω) ∂μ) -
        (∫ ω, Real.exp (lam * Z ω) ∂μ) * Real.log (∫ ω, Real.exp (lam * Z ω) ∂μ) := by
      unfold phiEntropy
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      rw [Real.log_exp]
      ring
    _ ≤ ∫ ω, Real.exp (lam * Z ω) *
        (Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c)) ∂μ :=
      bousquet_massart_modified_lsi_summand_psi hexp hzexp
    _ ≤ ∫ ω, lam ^ 2 / 2 * (Real.exp (lam * Z ω) * (Z ω - c) ^ 2) ∂μ := by
      apply integral_mono_ae hpsi hrhs
      filter_upwards [hgap] with ω hω
      have h := exp_neg_le_quadratic (lam * (Z ω - c)) (mul_nonneg hlam (sub_nonneg.mpr hω))
      have h' : Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c) ≤
          (lam * (Z ω - c)) ^ 2 / 2 := by linarith
      calc
        _ ≤ Real.exp (lam * Z ω) * ((lam * (Z ω - c)) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h' (Real.exp_pos _).le
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

end HighDimStat.Concentration


-- Source module: TalagrandBoundedObservable

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 800000

/-- Bounded inputs give an almost-sure bound on the observable without
assuming measurability of the individual coordinates. -/
lemma native_observable_ae_bounded {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : Fin n → Ω → ℝ) {a b L : ℝ} (hab : a ≤ b)
    (hSupport : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b)
    {f : (Fin n → ℝ) → ℝ} (hLip : IsLLipschitz f L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂μ, |f (fun i => X i ω)| ≤ C := by
  refine ⟨|L| * Real.sqrt ((n : ℝ) * (b - a) ^ 2) + |f (fun _ => a)|,
    by positivity, ?_⟩
  have hs : ∀ᵐ ω ∂μ, ∀ i, X i ω ∈ Set.Icc a b := ae_all_iff.mpr hSupport
  filter_upwards [hs] with ω hω
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsum : (∑ i, (X i ω - a) ^ 2) ≤ (n : ℝ) * (b - a) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, (b - a) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (sub_nonneg.mpr (hω i).1)
          (by linarith [(hω i).2]) 2
      _ = _ := by simp
  have hdiff : |f (fun i => X i ω) - f (fun _ => a)| ≤
      |L| * Real.sqrt ((n : ℝ) * (b - a) ^ 2) := by
    calc
      _ ≤ L * Real.sqrt (∑ i, (X i ω - a) ^ 2) := hLip _ _
      _ ≤ |L| * Real.sqrt (∑ i, (X i ω - a) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self L) (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (abs_nonneg _)
  calc
    _ = |(f (fun i => X i ω) - f (fun _ => a)) + f (fun _ => a)| := by congr 1; ring
    _ ≤ |f (fun i => X i ω) - f (fun _ => a)| + |f (fun _ => a)| := abs_add_le _ _
    _ ≤ _ := add_le_add hdiff le_rfl

/-- All exponential moments of an integrable bounded observable exist. -/
lemma bounded_observable_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {C : ℝ} (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ C) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * Z ω)) μ := by
  refine Integrable.of_bound ((hZ.aemeasurable.const_mul lam).exp).aestronglyMeasurable
    (Real.exp (|lam| * C)) ?_
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |lam * Z ω| := le_abs_self _
    _ = |lam| * |Z ω| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

lemma bounded_observable_exp_log_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ C) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * Z ω) * Real.log (Real.exp (lam * Z ω))) μ := by
  have he := bounded_observable_exp_integrable hZ hbound lam
  refine Integrable.of_bound
    (he.aestronglyMeasurable.mul ((hZ.aestronglyMeasurable.const_mul lam)))
    (Real.exp (|lam| * C) * (|lam| * C)) ?_ |>.congr ?_
  · filter_upwards [hbound] with ω hω
    change ‖Real.exp (lam * Z ω) * (lam * Z ω)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    have he' : Real.exp (lam * Z ω) ≤ Real.exp (|lam| * C) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ |lam * Z ω| := le_abs_self _
        _ = |lam| * |Z ω| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
    exact mul_le_mul he' (mul_le_mul_of_nonneg_left hω (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
  · exact ae_of_all _ (fun ω => by
      change Real.exp (lam * Z ω) * (lam * Z ω) =
        Real.exp (lam * Z ω) * Real.log (Real.exp (lam * Z ω))
      rw [Real.log_exp])

end HighDimStat.Concentration


-- Source module: TalagrandPiTransport

open MeasureTheory

namespace HighDimStat.Concentration

theorem talagrand_upd_insertNth {m : ℕ} {α : Fin (m+1) → Type}
    (k : Fin (m+1)) (x0 t : α k) (rest : ∀ j, α (k.succAbove j)) :
    Function.update (Fin.insertNth k x0 rest) k t = Fin.insertNth k t rest := by
  ext i
  rcases eq_or_ne i k with h | h
  · subst h; simp
  · rw [Function.update_of_ne h]
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    simp [Fin.insertNth_apply_succAbove]

-- Single integral transport at coordinate k.
theorem talagrand_transport_at_k {m : ℕ} {α : Fin (m+1) → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (k : Fin (m+1)) (F : (∀ i, α i) → ℝ) :
    ∫ x, F x ∂(Measure.pi μ)
      = ∫ p : α k × (∀ j, α (k.succAbove j)),
          F (Fin.insertNth k p.1 p.2)
          ∂((μ k).prod (Measure.pi (fun j => μ (k.succAbove j)))) := by
  have hmp := measurePreserving_piFinSuccAbove μ k
  rw [← hmp.integral_comp (MeasurableEquiv.piFinSuccAbove α k).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  have : Fin.insertNth k ((MeasurableEquiv.piFinSuccAbove α k) x).1
      ((MeasurableEquiv.piFinSuccAbove α k) x).2
      = (MeasurableEquiv.piFinSuccAbove α k).symm ((MeasurableEquiv.piFinSuccAbove α k) x) := rfl
  rw [this, MeasurableEquiv.symm_apply_apply]



end HighDimStat.Concentration


-- Source module: TalagrandProductIntegral

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1200000

lemma bounded_measurable_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] {F : A → ℝ}
    (hF : Measurable F) {C : ℝ} (hbound : ∀ x, ‖F x‖ ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hbound)

/-- Averaging one coordinate with its own marginal leaves a product
expectation unchanged. -/
lemma integral_pi_coordinate_average {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (k : Fin n) (F : (∀ i, α i) → ℝ)
    (hF : Measurable F) {C : ℝ} (hbound : ∀ x, ‖F x‖ ≤ C) :
    (∫ x, (∫ t, F (Function.update x k t) ∂(μ k)) ∂(Measure.pi μ)) =
      ∫ x, F x ∂(Measure.pi μ) := by
  classical
  cases n with
  | zero => exact k.elim0
  | succ m =>
    let ν := Measure.pi (fun j : Fin m => μ (k.succAbove j))
    let G := fun p : α k × (∀ j : Fin m, α (k.succAbove j)) =>
      F (Fin.insertNth k p.1 p.2)
    have hG : Measurable G := hF.comp (MeasurableEquiv.piFinSuccAbove α k).symm.measurable
    have hGi : Integrable G ((μ k).prod ν) :=
      bounded_measurable_integrable hG (fun p => hbound _)
    let H := fun rest : (∀ j : Fin m, α (k.succAbove j)) => ∫ t, G (t, rest) ∂(μ k)
    have hH : Measurable H := by
      have hswap : Measurable (fun p : (∀ j : Fin m, α (k.succAbove j)) × α k => G (p.2, p.1)) :=
        hG.comp (measurable_snd.prodMk measurable_fst)
      exact hswap.stronglyMeasurable.integral_prod_right'.measurable
    have hHb (rest : ∀ j : Fin m, α (k.succAbove j)) : ‖H rest‖ ≤ C := by
      have h := norm_integral_le_of_norm_le_const (μ := μ k)
        (f := fun t => G (t, rest)) (C := C) (ae_of_all _ (fun t => hbound _))
      simpa [H, probReal_univ] using h
    have hHi : Integrable (fun p : α k × (∀ j : Fin m, α (k.succAbove j)) => H p.2)
        ((μ k).prod ν) := bounded_measurable_integrable (hH.comp measurable_snd) (fun p => hHb _)
    rw [talagrand_transport_at_k μ k (fun x => ∫ t, F (Function.update x k t) ∂(μ k)),
      talagrand_transport_at_k μ k F]
    simp_rw [talagrand_upd_insertNth]
    change (∫ p, H p.2 ∂((μ k).prod ν)) = ∫ p, G p ∂((μ k).prod ν)
    rw [integral_prod _ hHi, integral_prod_symm _ hGi]
    simp [H]

end HighDimStat.Concentration


-- Source module: TalagrandTensorization

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1200000

lemma log_abs_le_of_mem_positive_interval {cc CC v : ℝ} (hcc : 0 < cc)
    (hlo : cc ≤ v) (hhi : v ≤ CC) :
    |Real.log v| ≤ |Real.log cc| + |Real.log CC| := by
  have h1 := Real.log_le_log hcc hlo
  have h2 := Real.log_le_log (lt_of_lt_of_le hcc hlo) hhi
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log cc), abs_nonneg (Real.log CC)]
  · linarith [le_abs_self (Real.log CC), abs_nonneg (Real.log cc)]

lemma mul_log_norm_le_of_mem_positive_interval {cc CC v : ℝ} (hcc : 0 < cc)
    (hlo : cc ≤ v) (hhi : v ≤ CC) :
    ‖v * Real.log v‖ ≤ |CC| * (|Real.log cc| + |Real.log CC|) := by
  rw [Real.norm_eq_abs, abs_mul]
  apply mul_le_mul _ (log_abs_le_of_mem_positive_interval hcc hlo hhi) (abs_nonneg _) (abs_nonneg _)
  rw [abs_of_pos (lt_of_lt_of_le hcc hlo)]
  exact hhi.trans (le_abs_self CC)

lemma coordinate_average_measurable {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (k : Fin n) {F : (∀ i, α i) → ℝ} (hF : Measurable F) :
    Measurable (fun x => ∫ t, F (Function.update x k t) ∂(μ k)) := by
  have h : Measurable (fun p : (∀ i, α i) × α k => F (Function.update p.1 k p.2)) :=
    hF.comp (measurable_update'.comp (measurable_fst.prodMk measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

lemma bounded_positive_fiber_entropy_integrable {E A : Type*}
    [MeasurableSpace E] [MeasurableSpace A] (ν : Measure E) (ρ : Measure A)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {F : E × A → ℝ} (hF : Measurable F) {cc CC : ℝ} (hcc : 0 < cc)
    (hlo : ∀ p, cc ≤ F p) (hhi : ∀ p, F p ≤ CC) :
    Integrable (fun x => phiEntropy (fun t => F (x, t)) ρ) ν := by
  let B := |CC| * (|Real.log cc| + |Real.log CC|)
  let M := fun x => ∫ t, F (x, t) ∂ρ
  let A := fun x => ∫ t, F (x, t) * Real.log (F (x, t)) ∂ρ
  have hMb (x : E) : cc ≤ M x ∧ M x ≤ CC := by
    have hi : Integrable (fun t => F (x, t)) ρ :=
      bounded_measurable_integrable (hF.comp measurable_prodMk_left) (fun t => by
        rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hcc (hlo _))]
        exact (hhi _).trans (le_abs_self CC))
    constructor
    · calc cc = ∫ _t, cc ∂ρ := by simp
           _ ≤ _ := integral_mono (integrable_const _) hi (fun t => hlo _)
    · calc _ ≤ ∫ _t, CC ∂ρ := integral_mono hi (integrable_const _) (fun t => hhi _)
           _ = CC := by simp
  have hMmeas : Measurable M := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hAmeas : Measurable A :=
    (hF.mul hF.log).stronglyMeasurable.integral_prod_right'.measurable
  have hAi : Integrable A ν := by
    apply bounded_measurable_integrable hAmeas
    intro x
    have h := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun t => F (x, t) * Real.log (F (x, t))) (C := B)
      (ae_of_all _ (fun t => mul_log_norm_le_of_mem_positive_interval hcc (hlo _) (hhi _)))
    simpa [A, probReal_univ] using h
  have hMi : Integrable (fun x => M x * Real.log (M x)) ν :=
    bounded_measurable_integrable (hMmeas.mul hMmeas.log)
      (fun x => mul_log_norm_le_of_mem_positive_interval hcc (hMb x).1 (hMb x).2)
  exact hAi.sub hMi

/-- The accepted positive bounded product entropy theorem, expressed as a
sum of expected fiber entropies so that one-coordinate estimates can apply. -/
lemma phiEntropy_pi_le_sum_fiber {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (∀ i, α i) → ℝ) (cc CC : ℝ) (hcc : 0 < cc) (hF : Measurable F)
    (hlo : ∀ x, cc ≤ F x) (hhi : ∀ x, F x ≤ CC) :
    phiEntropy F (Measure.pi μ) ≤
      ∑ k : Fin n, ∫ x, phiEntropy (fun t => F (Function.update x k t)) (μ k) ∂(Measure.pi μ) := by
  classical
  let B := |CC| * (|Real.log cc| + |Real.log CC|)
  have hFlog : Measurable (fun x => F x * Real.log (F x)) := hF.mul hF.log
  have hFlogb (x) : ‖F x * Real.log (F x)‖ ≤ B :=
    mul_log_norm_le_of_mem_positive_interval hcc (hlo x) (hhi x)
  have hnormF (x) : ‖F x‖ ≤ |CC| := by
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hcc (hlo x))]
    exact (hhi x).trans (le_abs_self CC)
  let M := fun (k : Fin n) (x : ∀ i, α i) => ∫ t, F (Function.update x k t) ∂(μ k)
  have hMlo (k : Fin n) (x : ∀ i, α i) : cc ≤ M k x := by
    have hi : Integrable (fun t => F (Function.update x k t)) (μ k) :=
      bounded_measurable_integrable (hF.comp (measurable_update x)) (fun t => hnormF _)
    calc
      cc = ∫ _t, cc ∂(μ k) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi (fun t => hlo _)
  have hMhi (k : Fin n) (x : ∀ i, α i) : M k x ≤ CC := by
    have hi : Integrable (fun t => F (Function.update x k t)) (μ k) :=
      bounded_measurable_integrable (hF.comp (measurable_update x)) (fun t => hnormF _)
    calc
      _ ≤ ∫ _t, CC ∂(μ k) := integral_mono hi (integrable_const _) (fun t => hhi _)
      _ = CC := by simp
  have hMlogi (k : Fin n) : Integrable (fun x => M k x * Real.log (M k x)) (Measure.pi μ) := by
    have hm := coordinate_average_measurable μ k hF
    apply bounded_measurable_integrable (hm.mul hm.log)
    exact fun x => mul_log_norm_le_of_mem_positive_interval hcc (hMlo k x) (hMhi k x)
  have hFlogavgi (k : Fin n) : Integrable
      (fun x => ∫ t, F (Function.update x k t) * Real.log (F (Function.update x k t)) ∂(μ k))
      (Measure.pi μ) := by
    apply bounded_measurable_integrable (coordinate_average_measurable μ k hFlog)
    intro x
    have h := norm_integral_le_of_norm_le_const (μ := μ k)
      (f := fun t => F (Function.update x k t) * Real.log (F (Function.update x k t)))
      (C := B) (ae_of_all _ (fun t => hFlogb _))
    simpa [probReal_univ] using h
  have h := entropy_n_coordinate_han_subadditivity_measure_pi_pos μ F cc CC hcc hF hlo hhi
  change phiEntropy F (Measure.pi μ) ≤ _ at h
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro k hk
  unfold phiEntropy
  rw [integral_sub (hFlogavgi k) (hMlogi k),
    integral_pi_coordinate_average μ k (fun x => F x * Real.log (F x)) hFlog hFlogb]

end HighDimStat.Concentration


-- Source module: TalagrandProductEntropy

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1600000

/-- A bounded observable on a product probability space has dimension-free
exponential entropy whenever its coordinate decrements have a uniform
squared-sum bound. Each reference must be independent of its own coordinate. -/
lemma product_entropy_of_sq_decrements {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (∀ i, α i) → ℝ) (c : Fin n → (∀ i, α i) → ℝ)
    (hZ : Measurable Z) (hc : ∀ k, Measurable (c k))
    {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hZb : ∀ x, |Z x| ≤ C)
    (hclo : ∀ k x, c k x ≤ Z x)
    (hcfiber : ∀ k x t, c k (Function.update x k t) = c k x)
    (hsum : ∀ x, (∑ k, (Z x - c k x) ^ 2) ≤ V)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    phiEntropy (fun x => Real.exp (lam * Z x)) (Measure.pi μ) ≤
      lam ^ 2 / 2 * V * ∫ x, Real.exp (lam * Z x) ∂(Measure.pi μ) := by
  classical
  let F := fun x => Real.exp (lam * Z x)
  let D := fun (k : Fin n) x => (Z x - c k x) ^ 2
  let E := Real.exp (|lam| * C)
  have hF : Measurable F := (hZ.const_mul lam).exp
  have hFb (x) : ‖F x‖ ≤ E := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self (lam * Z x)).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hZb x) (abs_nonneg _))
  have hFlo (x) : Real.exp (-|lam| * C) ≤ F x := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hZb x) (abs_nonneg lam)
    have h' := neg_abs_le (lam * Z x)
    rw [abs_mul] at h'
    nlinarith
  have hFhi (x) : F x ≤ E := by
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), F] using hFb x
  have hDb (k : Fin n) (x) : ‖D k x‖ ≤ V := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (Z x - c j x)) (Finset.mem_univ k)).trans (hsum x)
  have hD (k : Fin n) : Measurable (D k) := (hZ.sub (hc k)).pow_const 2
  have hFDb (k : Fin n) (x) : ‖F x * D k x‖ ≤ E * V := by
    rw [norm_mul]
    exact mul_le_mul (hFb x) (hDb k x) (norm_nonneg _) (Real.exp_pos _).le
  have hFDi (k : Fin n) : Integrable (fun x => F x * D k x) (Measure.pi μ) :=
    bounded_measurable_integrable (hF.mul (hD k)) (hFDb k)
  have hcoord (k : Fin n) (x) :
      phiEntropy (fun t => F (Function.update x k t)) (μ k) ≤
        lam ^ 2 / 2 * ∫ t, F (Function.update x k t) * D k (Function.update x k t) ∂(μ k) := by
    let W := fun t => Z (Function.update x k t)
    have hWi : Integrable W (μ k) :=
      bounded_measurable_integrable (hZ.comp (measurable_update x)) (fun t => by
        simpa [Real.norm_eq_abs] using hZb (Function.update x k t))
    have hwExp := bounded_observable_exp_integrable hWi
      (ae_of_all _ (fun t => hZb (Function.update x k t))) lam
    have hwLog := bounded_observable_exp_log_integrable hWi hC
      (ae_of_all _ (fun t => hZb (Function.update x k t))) lam
    have hwZExp : Integrable (fun t => lam * W t * Real.exp (lam * W t)) (μ k) :=
      hwLog.congr (ae_of_all _ (fun t => by
        change Real.exp (lam * W t) * Real.log (Real.exp (lam * W t)) =
          lam * W t * Real.exp (lam * W t)
        rw [Real.log_exp]
        ring))
    have hwSq : Integrable (fun t => Real.exp (lam * W t) * (W t - c k x) ^ 2) (μ k) := by
      have hi : Integrable (fun t => F (Function.update x k t) * D k (Function.update x k t)) (μ k) :=
        bounded_measurable_integrable ((hF.mul (hD k)).comp (measurable_update x))
          (fun t => hFDb k (Function.update x k t))
      simpa only [F, D, hcfiber, W] using hi
    have h := entropy_exp_le_sq_gap hlam hwExp hwZExp
      (ae_of_all _ (fun t => by simpa only [W, ← hcfiber k x t] using hclo k (Function.update x k t))) hwSq
    simpa only [F, D, hcfiber, W] using h
  have hEnti (k : Fin n) : Integrable
      (fun x => phiEntropy (fun t => F (Function.update x k t)) (μ k)) (Measure.pi μ) := by
    apply bounded_positive_fiber_entropy_integrable (Measure.pi μ) (μ k)
      (hF.comp (measurable_update'.comp (measurable_fst.prodMk measurable_snd)))
      (Real.exp_pos (-|lam| * C))
    · exact fun p => hFlo _
    · exact fun p => hFhi _
  have hAvgi (k : Fin n) : Integrable
      (fun x => ∫ t, F (Function.update x k t) * D k (Function.update x k t) ∂(μ k))
      (Measure.pi μ) := by
    apply bounded_measurable_integrable (coordinate_average_measurable μ k (hF.mul (hD k)))
    intro x
    have h := norm_integral_le_of_norm_le_const (μ := μ k)
      (f := fun t => F (Function.update x k t) * D k (Function.update x k t)) (C := E * V)
      (ae_of_all _ (fun t => hFDb k _))
    simpa [probReal_univ] using h
  calc
    _ ≤ ∑ k : Fin n, ∫ x, phiEntropy (fun t => F (Function.update x k t)) (μ k) ∂(Measure.pi μ) :=
      phiEntropy_pi_le_sum_fiber μ F _ E (Real.exp_pos _) hF hFlo hFhi
    _ ≤ ∑ k : Fin n, ∫ x, lam ^ 2 / 2 *
        (∫ t, F (Function.update x k t) * D k (Function.update x k t) ∂(μ k)) ∂(Measure.pi μ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact integral_mono (hEnti k) ((hAvgi k).const_mul _) (hcoord k)
    _ = lam ^ 2 / 2 * ∑ k : Fin n, ∫ x, F x * D k x ∂(Measure.pi μ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul,
        integral_pi_coordinate_average μ k (fun x => F x * D k x) (hF.mul (hD k)) (hFDb k)]
    _ = lam ^ 2 / 2 * ∫ x, F x * (∑ k : Fin n, D k x) ∂(Measure.pi μ) := by
      rw [← integral_finsetSum _ (fun k _ => hFDi k)]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change (∑ k, F x * D k x) = F x * ∑ k, D k x
        rw [Finset.mul_sum])
    _ ≤ lam ^ 2 / 2 * ∫ x, F x * V ∂(Measure.pi μ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono
      · simpa only [Finset.mul_sum] using integrable_finsetSum _ (fun k _ => hFDi k)
      · exact (bounded_measurable_integrable hF hFb).mul_const V
      · intro x
        exact mul_le_mul_of_nonneg_left (hsum x) (Real.exp_pos _).le
    _ = _ := by rw [integral_mul_const]; ring

end HighDimStat.Concentration


-- Source module: TalagrandCoordinateMinimum

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

/-- The lowest value obtainable by changing one coordinate inside the support
interval. It is a reference independent of that coordinate. -/
noncomputable def coordinateMinimum {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (a b : ℝ) (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  sInf ((fun t => f (Function.update x k t)) '' Set.Icc a b)

lemma coordinateMinimum_continuous {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) (a b : ℝ) (k : Fin n) :
    Continuous (coordinateMinimum f a b k) := by
  apply isCompact_Icc.continuous_sInf
  exact hf.comp (continuous_update k)

lemma coordinateMinimum_update {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (a b : ℝ) (k : Fin n) (x : Fin n → ℝ) (t : ℝ) :
    coordinateMinimum f a b k (Function.update x k t) = coordinateMinimum f a b k x := by
  unfold coordinateMinimum
  simp only [Function.update_idem]

lemma coordinateMinimum_attained {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (k : Fin n) (x : Fin n → ℝ) :
    ∃ t ∈ Set.Icc a b, coordinateMinimum f a b k x = f (Function.update x k t) := by
  exact isCompact_Icc.exists_sInf_image_eq (Set.nonempty_Icc.mpr hab)
    (hf.comp (continuous_update k |>.comp (continuous_const.prodMk continuous_id))).continuousOn

lemma coordinateMinimum_le {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) {a b : ℝ} (k : Fin n) (x : Fin n → ℝ)
    (hx : x k ∈ Set.Icc a b) : coordinateMinimum f a b k x ≤ f x := by
  have hc : Continuous (fun t => f (Function.update x k t)) := by fun_prop
  have h := csInf_le (isCompact_Icc.bddBelow_image hc.continuousOn)
    (Set.mem_image_of_mem (fun t => f (Function.update x k t)) hx)
  simpa only [coordinateMinimum, Function.update_eq_self] using h

lemma coordinateMinimum_gap_sq_le {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) (hconv : IsSeparatelyConvex f) {a b : ℝ}
    (k : Fin n) (x : Fin n → ℝ) (hx : x k ∈ Set.Icc a b)
    (hd : DifferentiableAt ℝ (fun t => f (Function.update x k t)) (x k)) :
    (f x - coordinateMinimum f a b k x) ^ 2 ≤
      (deriv (fun t => f (Function.update x k t)) (x k)) ^ 2 * (b - a) ^ 2 := by
  obtain ⟨t, ht, he⟩ := coordinateMinimum_attained hf (hx.1.trans hx.2) k x
  have hgap := coordinateMinimum_le hf k x hx
  rw [he] at hgap ⊢
  have h := convex_coordinate_gap_sq_le (hconv k x) hx ht hd (by
    simpa only [Function.update_eq_self] using hgap)
  simpa only [Function.update_eq_self] using h

end HighDimStat.Concentration


-- Source module: TalagrandSmoothDecrements

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1200000

lemma update_toLp_eq_line {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    WithLp.toLp 2 (Function.update x k t) =
      WithLp.toLp 2 x + (t - x k) • EuclideanSpace.basisFun (Fin n) ℝ k := by
  ext j
  by_cases h : j = k
  · subst j
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  · simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, h]

lemma hasDerivAt_native_coordinate {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ}
    (hd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i))
      (WithLp.toLp 2 x)) (k : Fin n) :
    HasDerivAt (fun t => f (Function.update x k t))
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i))
        (WithLp.toLp 2 x) (EuclideanSpace.basisFun (Fin n) ℝ k)) (x k) := by
  let v := EuclideanSpace.basisFun (Fin n) ℝ k
  let p := fun t : ℝ => WithLp.toLp 2 x + (t - x k) • v
  have hp : HasDerivAt p v (x k) := by
    have h : HasDerivAt p (0 + (1 : ℝ) • v) (x k) := (hasDerivAt_const (x k) (WithLp.toLp 2 x)).add
      (((hasDerivAt_id (x k)).sub_const (x k)).smul_const v)
    simpa only [zero_add, one_smul] using h
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (x k) hp (by simp [p])
  have he : ((fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i)) ∘ p) =
      (fun t => f (Function.update x k t)) := by
    funext t
    change f (fun i => (WithLp.toLp 2 x + (t - x k) • EuclideanSpace.basisFun (Fin n) ℝ k) i) =
      f (Function.update x k t)
    rw [← update_toLp_eq_line]
  rw [he] at h
  exact h

/-- For a smooth separately convex observable, the coordinate minima give
the squared-decrement bound needed by the product entropy theorem. -/
lemma smooth_native_sq_decrements_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} {L a b : ℝ}
    (hLip : IsLLipschitz f L) (hconv : IsSeparatelyConvex f)
    (x : Fin n → ℝ) (hx : ∀ k, x k ∈ Set.Icc a b)
    (hd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i))
      (WithLp.toLp 2 x)) :
    (∑ k, (f x - coordinateMinimum f a b k x) ^ 2) ≤ L ^ 2 * (b - a) ^ 2 := by
  have hf := native_lipschitz_continuous hLip
  have hs (k : Fin n) := coordinateMinimum_gap_sq_le hf hconv k x (hx k)
    (hasDerivAt_native_coordinate hd k).differentiableAt
  simp_rw [(hasDerivAt_native_coordinate hd _).deriv] at hs
  calc
    _ ≤ ∑ k, (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i))
        (WithLp.toLp 2 x) (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 * (b - a) ^ 2 :=
      Finset.sum_le_sum (fun k _ => hs k)
    _ = (∑ k, (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i))
        (WithLp.toLp 2 x) (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2) * (b - a) ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ L ^ 2 * (b - a) ^ 2 := by
      have hg := euclidean_gradient_sq_sum_le (native_lipschitz_euclidean hLip) (WithLp.toLp 2 x)
      have hLsq : ((‖L‖₊ : NNReal) : ℝ) ^ 2 = L ^ 2 := by simp [Real.norm_eq_abs]
      rw [hLsq] at hg
      exact mul_le_mul_of_nonneg_right hg (sq_nonneg _)

end HighDimStat.Concentration


-- Source module: TalagrandSeparateConvex

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

lemma native_lift_line_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) (t : ℝ) :
    f (fun i => (x + t • EuclideanSpace.basisFun (Fin n) ℝ k) i) =
      f (Function.update (fun i => x i) k (x k + t)) := by
  congr 1
  funext i
  by_cases h : i = k
  · subst i
    simp [EuclideanSpace.basisFun_apply]
  · simp [EuclideanSpace.basisFun_apply, h]

lemma native_separate_convex_lift {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hconv : IsSeparatelyConvex f) (k : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ Set.univ (fun t : ℝ => f (fun i => (x + t • EuclideanSpace.basisFun (Fin n) ℝ k) i)) := by
  have h := (hconv k (fun i => x i)).translate_right (x k)
  simp only [Set.preimage_univ, Function.comp_def] at h
  have he : (fun t : ℝ => f (fun i => (x + t • EuclideanSpace.basisFun (Fin n) ℝ k) i)) =
      (fun t : ℝ => f (Function.update (fun i => x i) k (x k + t))) :=
    funext (fun t => native_lift_line_eq f x k t)
  rw [he]
  exact h

lemma euclidean_separate_convex_restrict {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hconv : ∀ k x, ConvexOn ℝ Set.univ (fun t : ℝ => g (x + t • EuclideanSpace.basisFun (Fin n) ℝ k))) :
    IsSeparatelyConvex (fun x : Fin n → ℝ => g (WithLp.toLp 2 x)) := by
  intro k x
  have h := (hconv k (WithLp.toLp 2 x)).translate_right (-x k)
  simp only [Set.preimage_univ, Function.comp_def] at h
  have he : (fun t : ℝ => g (WithLp.toLp 2 (Function.update x k t))) =
      (fun t : ℝ => g (WithLp.toLp 2 x + (-x k + t) • EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    funext t
    rw [update_toLp_eq_line]
    congr 1
    congr 1
    ring
  rw [he]
  exact h

lemma euclidean_lipschitz_restrict {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : NNReal} (hg : LipschitzWith K g) :
    IsLLipschitz (fun x : Fin n → ℝ => g (WithLp.toLp 2 x)) (K : ℝ) := by
  intro x y
  have h := hg.dist_le_mul (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rw [Real.dist_eq, dist_eq_norm, EuclideanSpace.norm_eq] at h
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs] using h

end HighDimStat.Concentration


-- Source module: TalagrandSmoothBoxEntropy

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1400000

lemma box_coe_update {n : ℕ} {a b : ℝ} (x : Fin n → Set.Icc a b)
    (k : Fin n) (t : Set.Icc a b) :
    (fun i => ((Function.update x k t) i : ℝ)) =
      Function.update (fun i => (x i : ℝ)) k (t : ℝ) := by
  funext i
  by_cases h : i = k <;> simp [h]

/-- The full entropy estimate for smooth separately convex functions on a
product of bounded intervals, with the sum of coordinate squares controlled
by the original Euclidean Lipschitz constant. -/
lemma smooth_separately_convex_box_entropy {n : ℕ} {a b L : ℝ}
    (μ : Fin n → Measure (Set.Icc a b)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → ℝ) → ℝ) (hLip : IsLLipschitz f L) (hconv : IsSeparatelyConvex f)
    (hd : Differentiable ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i)))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    phiEntropy (fun x : Fin n → Set.Icc a b => Real.exp (lam * f (fun i => (x i : ℝ))))
      (Measure.pi μ) ≤
      lam ^ 2 / 2 * (L ^ 2 * (b - a) ^ 2) *
        ∫ x : Fin n → Set.Icc a b, Real.exp (lam * f (fun i => (x i : ℝ))) ∂(Measure.pi μ) := by
  let Z := fun x : Fin n → Set.Icc a b => f (fun i => (x i : ℝ))
  let c := fun (k : Fin n) (x : Fin n → Set.Icc a b) =>
    coordinateMinimum f a b k (fun i => (x i : ℝ))
  have hf := native_lipschitz_continuous hLip
  have hcoe : Continuous (fun x : Fin n → Set.Icc a b => fun i => (x i : ℝ)) :=
    continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))
  have hZ : Continuous Z := hf.comp hcoe
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hZ.norm.continuousOn
  have hZb (x : Fin n → Set.Icc a b) : |Z x| ≤ |C| := by
    have h := hC (Set.mem_image_of_mem (fun x => ‖Z x‖) (Set.mem_univ x))
    exact (show |Z x| ≤ C by simpa only [Real.norm_eq_abs] using h).trans (le_abs_self C)
  have hc (k : Fin n) : Measurable (c k) :=
    ((coordinateMinimum_continuous hf a b k).comp hcoe).measurable
  have hclo (k : Fin n) (x : Fin n → Set.Icc a b) : c k x ≤ Z x :=
    coordinateMinimum_le hf k _ (x k).property
  have hcfiber (k : Fin n) (x : Fin n → Set.Icc a b) (t : Set.Icc a b) :
      c k (Function.update x k t) = c k x := by
    dsimp [c]
    rw [box_coe_update, coordinateMinimum_update]
  have hsum (x : Fin n → Set.Icc a b) :
      (∑ k, (Z x - c k x) ^ 2) ≤ L ^ 2 * (b - a) ^ 2 :=
    smooth_native_sq_decrements_le hLip hconv (fun i => (x i : ℝ))
      (fun i => (x i).property) (hd _)
  exact product_entropy_of_sq_decrements μ Z c hZ.measurable hc (abs_nonneg C)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hZb hclo hcfiber hsum lam hlam

end HighDimStat.Concentration


-- Source module: TalagrandEntropyMGF

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

lemma centered_mgf_of_entropy_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ C)
    (hEntropy : ∀ lam : ℝ, 0 ≤ lam →
      phiEntropy (fun ω => Real.exp (lam * Z ω)) μ ≤
        V * lam ^ 2 * ∫ ω, Real.exp (lam * Z ω) ∂μ)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∫ ω, Real.exp (lam * (Z ω - ∫ ω', Z ω' ∂μ)) ∂μ) ≤ Real.exp (V * lam ^ 2) := by
  let sigma := Real.sqrt (2 * V)
  have hsigma : sigma ^ 2 = 2 * V := Real.sq_sqrt (by positivity)
  have hh := herbst_argument Z sigma (Set.Ici 0) (Or.inl rfl)
    (fun lam _ => ⟨bounded_observable_exp_integrable hZ hbound lam,
      bounded_observable_exp_log_integrable hZ hC hbound lam⟩) (by
      intro t ht
      rw [hsigma]
      convert hEntropy t ht using 1 <;> ring)
  have hlog := hh lam hlam
  rw [hsigma] at hlog
  have hW : Integrable (fun ω => Z ω - ∫ ω', Z ω' ∂μ) μ :=
    hZ.sub (integrable_const _)
  have hWb : ∀ᵐ ω ∂μ, |Z ω - ∫ ω', Z ω' ∂μ| ≤ C + |∫ ω', Z ω' ∂μ| := by
    filter_upwards [hbound] with ω hω
    exact (abs_sub _ _).trans (add_le_add hω le_rfl)
  have hi := bounded_observable_exp_integrable hW hWb lam
  have hp := mgf_pos hi
  change 0 < ∫ ω, Real.exp (lam * (Z ω - ∫ ω', Z ω' ∂μ)) ∂μ at hp
  calc
    _ = Real.exp (Real.log (∫ ω, Real.exp (lam * (Z ω - ∫ ω', Z ω' ∂μ)) ∂μ)) :=
      (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by convert hlog using 1 <;> ring)

end HighDimStat.Concentration


-- Source module: TalagrandSmoothBoxMGF

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1200000

lemma smooth_separately_convex_box_mgf {n : ℕ} {a b L : ℝ}
    (μ : Fin n → Measure (Set.Icc a b)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → ℝ) → ℝ) (hLip : IsLLipschitz f L) (hconv : IsSeparatelyConvex f)
    (hd : Differentiable ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i)))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∫ x : Fin n → Set.Icc a b,
      Real.exp (lam * (f (fun i => (x i : ℝ)) -
        ∫ y : Fin n → Set.Icc a b, f (fun i => (y i : ℝ)) ∂(Measure.pi μ))) ∂(Measure.pi μ)) ≤
      Real.exp (L ^ 2 * (b - a) ^ 2 * lam ^ 2 / 2) := by
  let Z := fun x : Fin n → Set.Icc a b => f (fun i => (x i : ℝ))
  have hcoe : Continuous (fun x : Fin n → Set.Icc a b => fun i => (x i : ℝ)) :=
    continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))
  have hZ : Continuous Z := (native_lipschitz_continuous hLip).comp hcoe
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hZ.norm.continuousOn
  have hZb (x : Fin n → Set.Icc a b) : |Z x| ≤ |C| := by
    have h := hC (Set.mem_image_of_mem (fun x => ‖Z x‖) (Set.mem_univ x))
    exact (show |Z x| ≤ C by simpa only [Real.norm_eq_abs] using h).trans (le_abs_self C)
  have hZi : Integrable Z (Measure.pi μ) :=
    bounded_measurable_integrable hZ.measurable (fun x => by simpa only [Real.norm_eq_abs] using hZb x)
  have hEnt (t : ℝ) (ht : 0 ≤ t) : phiEntropy (fun x => Real.exp (t * Z x)) (Measure.pi μ) ≤
      (L ^ 2 * (b-a) ^ 2 / 2) * t ^ 2 * ∫ x, Real.exp (t * Z x) ∂(Measure.pi μ) := by
    convert smooth_separately_convex_box_entropy μ f hLip hconv hd t ht using 1 <;> ring
  have h := centered_mgf_of_entropy_bound hZi (abs_nonneg C) (by positivity)
    (ae_of_all _ hZb) hEnt lam hlam
  convert h using 1 <;> ring

end HighDimStat.Concentration


-- Source module: TalagrandSmoothing

open MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace HighDimStat.Concentration

set_option maxHeartbeats 1600000

/-- Compact normalized smoothing preserves convexity along each specified
coordinate direction and the exact Lipschitz constant. No global bound on
the original function is required. -/
lemma separately_convex_lipschitz_bump_smoothing {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {K : NNReal} {f : E → ℝ}
    (hf : LipschitzWith K f) (v : ι → E)
    (hconv : ∀ i x, ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • v i)))
    (φ : ContDiffBump (0 : E)) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ LipschitzWith K g ∧
      (∀ i x, ConvexOn ℝ Set.univ (fun t : ℝ => g (x + t • v i))) ∧
      ∀ x, |g x - f x| ≤ (K : ℝ) * φ.rOut := by
  let σ : Measure E := Measure.addHaar
  let ρ := φ.normed σ
  let ν := σ.withDensity (fun x => ENNReal.ofReal (ρ x))
  let g : E → ℝ := ρ ⋆[lsmul ℝ ℝ, σ] f
  have hρm : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
    φ.continuous_normed.measurable.ennreal_ofReal
  have hρi : Integrable ρ σ := φ.integrable_normed
  have hρnn (x : E) : 0 ≤ ρ x := φ.nonneg_normed x
  haveI : IsProbabilityMeasure ν := by
    constructor
    change σ.withDensity (fun x => ENNReal.ofReal (ρ x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρnn)]
    rw [φ.integral_normed]
    simp
  have hs : ∀ᵐ y ∂ν, ‖y‖ ≤ φ.rOut := by
    apply (ae_withDensity_iff hρm).mpr
    filter_upwards [] with y hy
    have hne : ρ y ≠ 0 := by
      intro hzero
      exact hy (by simp [hzero])
    have hb : y ∈ Metric.ball (0 : E) φ.rOut := by
      rw [← φ.support_normed_eq (μ := σ)]
      exact hne
    exact (show ‖y‖ < φ.rOut by simpa only [Metric.mem_ball, dist_zero_right] using hb).le
  have hi (x : E) : Integrable (fun y => f (x - y)) ν := by
    have hc : Continuous (fun y => f (x - y)) := hf.continuous.comp (continuous_const.sub continuous_id)
    refine Integrable.of_bound hc.aestronglyMeasurable ((K : ℝ) * φ.rOut + ‖f x‖) ?_
    filter_upwards [hs] with y hy
    have hl := hf.dist_le_mul (x-y) x
    have hdist : dist (x-y) x = ‖y‖ := by rw [dist_eq_norm]; simp
    rw [hdist, Real.dist_eq, ← Real.norm_eq_abs] at hl
    calc
      _ = ‖(f (x-y) - f x) + f x‖ := by congr 1; ring
      _ ≤ ‖f (x-y) - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hl.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)) le_rfl
  have he (x : E) : g x = ∫ y, f (x-y) ∂ν := by
    have h := integral_withDensity_eq_integral_toReal_smul (μ := σ) hρm
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top) (fun y => f (x-y))
    simpa only [ν, g, convolution_def, lsmul_apply, smul_eq_mul,
      ENNReal.toReal_ofReal (hρnn _)] using h.symm
  have hLip : LipschitzWith K g := by
    rw [show g = fun x => ∫ y, f (x-y) ∂ν from funext he]
    exact GaussianConcentration.lipschitz_average ν hf hi
  have hg : ContDiff ℝ 2 g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      φ.contDiff_normed hf.continuous.locallyIntegrable
  have hgc (i : ι) (x : E) : ConvexOn ℝ Set.univ (fun t : ℝ => g (x + t • v i)) := by
    have hc' : ConvexOn ℝ Set.univ (fun t : ℝ => ∫ y, f ((x-y) + t • v i) ∂ν) := by
      apply integral_convexOn_of_integrand_ae (convex_univ : Convex ℝ (Set.univ : Set ℝ))
        (ae_of_all _ (fun y => hconv i (x-y)))
      intro t ht
      convert hi (x + t • v i) using 1
      funext y
      congr 1
      abel
    convert hc' using 1
    funext t
    rw [he]
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    abel
  refine ⟨g, hg, hLip, hgc, ?_⟩
  intro x
  rw [he]
  exact GaussianConcentration.average_sub_le ν hf hi hs x

end HighDimStat.Concentration


-- Source module: TalagrandMGFLimit

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

lemma centered_exp_integral_factor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (lam : ℝ) :
    (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂μ)) ∂μ) =
      Real.exp (-lam * ∫ y, f y ∂μ) * ∫ x, Real.exp (lam * f x) ∂μ := by
  simp_rw [mul_sub, sub_eq_add_neg, Real.exp_add]
  rw [integral_mul_const]
  simp only [neg_mul]
  ring

/-- A uniformly bounded pointwise approximation preserves centered
exponential moments on every probability space. -/
lemma bounded_centered_mgf_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {fs : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (fs n) μ) {C : ℝ}
    (hbound : ∀ n x, ‖fs n x‖ ≤ C)
    (hpoint : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) (lam : ℝ) :
    Tendsto (fun n => ∫ x, Real.exp (lam * (fs n x - ∫ y, fs n y ∂μ)) ∂μ) atTop
      (𝓝 (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂μ)) ∂μ)) := by
  have hmean := tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
    hmeas (integrable_const C) (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hpoint)
  have hEmeas (n : ℕ) : AEStronglyMeasurable (fun x => Real.exp (lam * fs n x)) μ :=
    (((hmeas n).aemeasurable.const_mul lam).exp).aestronglyMeasurable
  have hEbound (n : ℕ) (x : Ω) : ‖Real.exp (lam * fs n x)‖ ≤ Real.exp (|lam| * C) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |lam * fs n x| := le_abs_self _
      _ = |lam| * ‖fs n x‖ := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound n x) (abs_nonneg _)
  have hEpoint (x : Ω) : Tendsto (fun n => Real.exp (lam * fs n x)) atTop
      (𝓝 (Real.exp (lam * f x))) :=
    (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul (hpoint x))
  have hExp := tendsto_integral_of_dominated_convergence (fun _ : Ω => Real.exp (|lam| * C))
    hEmeas (integrable_const _) (fun n => ae_of_all _ (hEbound n)) (ae_of_all _ hEpoint)
  have hmean' : Tendsto (fun n => -lam * ∫ y, fs n y ∂μ) atTop
      (𝓝 (-lam * ∫ y, f y ∂μ)) := tendsto_const_nhds.mul hmean
  have h := ((Real.continuous_exp.tendsto _).comp hmean').mul hExp
  simp_rw [centered_exp_integral_factor]
  exact h

end HighDimStat.Concentration


-- Source module: TalagrandBoxMGF

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace HighDimStat.Concentration

set_option maxHeartbeats 1600000

/-- The smoothness restriction is removed by normalized compact smoothing
that retains separate convexity and the exact Euclidean Lipschitz constant. -/
lemma separately_convex_box_mgf {n : ℕ} {a b L : ℝ}
    (μ : Fin n → Measure (Set.Icc a b)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → ℝ) → ℝ) (hLip : IsLLipschitz f L) (hconv : IsSeparatelyConvex f)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∫ x : Fin n → Set.Icc a b,
      Real.exp (lam * (f (fun i => (x i : ℝ)) -
        ∫ y : Fin n → Set.Icc a b, f (fun i => (y i : ℝ)) ∂(Measure.pi μ))) ∂(Measure.pi μ)) ≤
      Real.exp (L ^ 2 * (b - a) ^ 2 * lam ^ 2 / 2) := by
  let K : NNReal := ‖L‖₊
  let F := fun u : EuclideanSpace ℝ (Fin n) => f (fun i => u i)
  let φ (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := (1 / ((k : ℝ) + 1)) / 2
      rOut := 1 / ((k : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hs (k : ℕ) := separately_convex_lipschitz_bump_smoothing (native_lipschitz_euclidean hLip)
    (EuclideanSpace.basisFun (Fin n) ℝ) (native_separate_convex_lift hconv) (φ k)
  choose gs hgs using hs
  let fn := fun (k : ℕ) (x : Fin n → ℝ) => gs k (WithLp.toLp 2 x)
  let fs := fun (k : ℕ) (x : Fin n → Set.Icc a b) => fn k (fun i => (x i : ℝ))
  let Z := fun x : Fin n → Set.Icc a b => f (fun i => (x i : ℝ))
  have hcoe : Continuous (fun x : Fin n → Set.Icc a b => fun i => (x i : ℝ)) :=
    continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))
  have hZ : Continuous Z := (native_lipschitz_continuous hLip).comp hcoe
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hZ.norm.continuousOn
  have hZb (x : Fin n → Set.Icc a b) : |Z x| ≤ |C| := by
    have h := hC (Set.mem_image_of_mem (fun x => ‖Z x‖) (Set.mem_univ x))
    exact (show |Z x| ≤ C by simpa only [Real.norm_eq_abs] using h).trans (le_abs_self C)
  have herror (k : ℕ) (x : Fin n → Set.Icc a b) :
      |fs k x - Z x| ≤ (K : ℝ) * (1 / ((k : ℝ) + 1)) := (hgs k).2.2.2 _
  have hε : Tendsto (fun k : ℕ => (K : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpoint (x : Fin n → Set.Icc a b) : Tendsto (fun k => fs k x) atTop (𝓝 (Z x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun _ => dist_nonneg) ?_ hε
    intro k
    rw [Real.dist_eq]
    exact herror k x
  have hmeas (k : ℕ) : AEStronglyMeasurable (fs k) (Measure.pi μ) :=
    ((hgs k).2.1.continuous.comp ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp hcoe)).aestronglyMeasurable
  have hbound (k : ℕ) (x : Fin n → Set.Icc a b) : ‖fs k x‖ ≤ (K : ℝ) + |C| := by
    have hrad : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have he := (herror k x).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrad K.coe_nonneg)
    rw [Real.norm_eq_abs]
    calc
      _ = |(fs k x - Z x) + Z x| := by congr 1; ring
      _ ≤ |fs k x - Z x| + |Z x| := abs_add_le _ _
      _ ≤ _ := add_le_add he (hZb x)
  have hLsq : (K : ℝ) ^ 2 = L ^ 2 := by simp [K, Real.norm_eq_abs]
  have hmgf (k : ℕ) :
      (∫ x, Real.exp (lam * (fs k x - ∫ y, fs k y ∂(Measure.pi μ))) ∂(Measure.pi μ)) ≤
        Real.exp (L ^ 2 * (b-a) ^ 2 * lam ^ 2 / 2) := by
    have hfnLip := euclidean_lipschitz_restrict (hgs k).2.1
    have hfnConv := euclidean_separate_convex_restrict (gs k) (hgs k).2.2.1
    have hfnDiff : Differentiable ℝ (fun u : EuclideanSpace ℝ (Fin n) => fn k (fun i => u i)) := by
      have he : (fun u : EuclideanSpace ℝ (Fin n) => fn k (fun i => u i)) = gs k := by
        funext u
        rfl
      rw [he]
      exact (hgs k).1.differentiable (by norm_num)
    have h := smooth_separately_convex_box_mgf μ (fn k) hfnLip hfnConv hfnDiff lam hlam
    change _ ≤ Real.exp ((K : ℝ) ^ 2 * (b-a) ^ 2 * lam ^ 2 / 2) at h
    rwa [hLsq] at h
  exact le_of_tendsto (bounded_centered_mgf_tendsto (Measure.pi μ) hmeas hbound hpoint lam)
    (Eventually.of_forall hmgf)

end HighDimStat.Concentration


-- Source module: TalagrandIndependentMGF

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1400000

/-- Transfer from a product of interval-valued laws to independent bounded
random variables. Coordinate a.e. measurability is stated explicitly. -/
lemma separately_convex_independent_mgf {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, AEMeasurable (X i) Prob)
    (a b : ℝ) (hab : a ≤ b) (hIndep : iIndepFun X Prob)
    (hSupport : ∀ i, ∀ᵐ ω ∂Prob, X i ω ∈ Set.Icc a b)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hSepConvex : IsSeparatelyConvex f) (hLip : IsLLipschitz f L)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∫ ω, Real.exp (lam * (f (fun i => X i ω) -
      ∫ ω', f (fun i => X i ω') ∂Prob)) ∂Prob) ≤
      Real.exp (L ^ 2 * (b - a) ^ 2 * lam ^ 2 / 2) := by
  let Y := fun (i : Fin n) (ω : Ω) => Set.projIcc a b hab (X i ω)
  have hproj : Measurable (Set.projIcc a b hab) :=
    (continuous_projIcc (a := a) (b := b) (h := hab)).measurable
  have hYm (i : Fin n) : AEMeasurable (Y i) Prob :=
    hproj.comp_aemeasurable (hXm i)
  have hYi : iIndepFun Y Prob := hIndep.comp (fun _ => Set.projIcc a b hab)
    (fun _ => hproj)
  let μ := fun i => Prob.map (Y i)
  haveI : ∀ i, IsProbabilityMeasure (μ i) := fun i => Measure.isProbabilityMeasure_map (hYm i)
  let A := fun ω i => Y i ω
  have hAm : AEMeasurable A Prob := aemeasurable_pi_lambda _ hYm
  have hlaw : Prob.map A = Measure.pi μ := hYi.map_fun_eq_pi_map hYm
  let Z := fun x : Fin n → Set.Icc a b => f (fun i => (x i : ℝ))
  have hcoe : Continuous (fun x : Fin n → Set.Icc a b => fun i => (x i : ℝ)) :=
    continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))
  have hZ : Continuous Z := (native_lipschitz_continuous hLip).comp hcoe
  have hEq : (fun ω => f (fun i => X i ω)) =ᵐ[Prob] (fun ω => Z (A ω)) := by
    have hs : ∀ᵐ ω ∂Prob, ∀ i, X i ω ∈ Set.Icc a b := ae_all_iff.mpr hSupport
    filter_upwards [hs] with ω hω
    dsimp [Z, A, Y]
    congr 1
    funext i
    rw [Set.projIcc_of_mem hab (hω i)]
  have hMean : (∫ ω, f (fun i => X i ω) ∂Prob) = ∫ x, Z x ∂(Measure.pi μ) := by
    calc
      _ = ∫ ω, Z (A ω) ∂Prob := integral_congr_ae hEq
      _ = ∫ x, Z x ∂(Prob.map A) := (integral_map hAm hZ.aestronglyMeasurable).symm
      _ = _ := by rw [hlaw]
  have hExpMeas : AEStronglyMeasurable
      (fun x => Real.exp (lam * (Z x - ∫ y, Z y ∂(Measure.pi μ)))) (Prob.map A) :=
    (Real.continuous_exp.comp ((hZ.sub continuous_const).const_mul lam)).aestronglyMeasurable
  calc
    _ = ∫ ω, Real.exp (lam * (Z (A ω) - ∫ y, Z y ∂(Measure.pi μ))) ∂Prob := by
      rw [hMean]
      apply integral_congr_ae
      filter_upwards [hEq] with ω hω
      rw [hω]
    _ = ∫ x, Real.exp (lam * (Z x - ∫ y, Z y ∂(Measure.pi μ))) ∂(Prob.map A) :=
      (integral_map hAm hExpMeas).symm
    _ = ∫ x, Real.exp (lam * (Z x - ∫ y, Z y ∂(Measure.pi μ))) ∂(Measure.pi μ) := by rw [hlaw]
    _ ≤ _ := separately_convex_box_mgf μ f hLip hSepConvex lam hlam

end HighDimStat.Concentration


-- Source module: TalagrandMeasurableTail

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

set_option maxHeartbeats 1400000

/-- The usual random-variable formulation, with coordinate a.e. measurability
explicit. The platform's original theorem omits this hypothesis. -/
theorem separately_convex_lipschitz_concentration_of_aemeasurable
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, AEMeasurable (X i) Prob)
    (a b : ℝ) (hab : a < b) (hIndep : iIndepFun X Prob)
    (hSupport : ∀ i, ∀ᵐ ω ∂Prob, X i ω ∈ Set.Icc a b)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ)
    (hSepConvex : IsSeparatelyConvex f) (hLip : IsLLipschitz f L)
    (hInt : Integrable (fun ω => f (fun i => X i ω)) Prob)
    (δ : ℝ) (hδ : 0 < δ) :
    Prob.real {ω | (∫ ω', f (fun i => X i ω') ∂Prob) + δ ≤ f (fun i => X i ω)} ≤
      Real.exp (-(δ ^ 2) / (4 * L ^ 2 * (b - a) ^ 2)) := by
  by_cases hL : L = 0
  · simp only [hL, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, div_zero, Real.exp_zero]
    exact measureReal_le_one
  let V := L ^ 2 * (b - a) ^ 2
  have hV : 0 < V := mul_pos (sq_pos_of_ne_zero hL) (sq_pos_of_pos (sub_pos.mpr hab))
  let Z := fun ω => f (fun i => X i ω)
  let m := ∫ ω, Z ω ∂Prob
  let W := fun ω => Z ω - m
  obtain ⟨C, hC, hbound⟩ := native_observable_ae_bounded X hab.le hSupport hLip
  have hW : Integrable W Prob := hInt.sub (integrable_const m)
  have hWbound : ∀ᵐ ω ∂Prob, |W ω| ≤ C + |m| := by
    filter_upwards [hbound] with ω hω
    exact (abs_sub _ _).trans (add_le_add hω le_rfl)
  let lam := δ / (2 * V)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hi := bounded_observable_exp_integrable hW hWbound lam
  have hmgf : mgf W Prob lam ≤ Real.exp (V * lam ^ 2) := by
    have h := separately_convex_independent_mgf X hXm a b hab.le hIndep hSupport
      f L hSepConvex hLip lam hlam
    change mgf W Prob lam ≤ Real.exp (V * lam ^ 2 / 2) at h
    exact h.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg lam]))
  calc
    _ = Prob.real {ω | δ ≤ W ω} := by
      congr 1
      ext ω
      simp only [Set.mem_setOf_eq, W, Z, m]
      constructor <;> intro h <;> linarith
    _ ≤ Real.exp (-lam * δ) * mgf W Prob lam := measure_ge_le_exp_mul_mgf δ hlam hi
    _ ≤ Real.exp (-lam * δ) * Real.exp (V * lam ^ 2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-(δ ^ 2) / (4 * V)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      field_simp
      ring
    _ = _ := by congr 1; dsimp [V]; ring

end HighDimStat.Concentration


open MeasureTheory ProbabilityTheory HighDimStat.Concentration

-- Source module: TalagrandOuterMeasurable

open MeasureTheory Set Filter
open scoped ENNReal

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

/-- Sets separated by a null measurable set have additive outer measure,
even when the two sets themselves are not measurable. -/
lemma measure_union_of_null_measurable_separator {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {S T A : Set Ω} (hA : NullMeasurableSet A μ)
    (hS : S ⊆ A) (hT : T ⊆ Aᶜ) : μ (S ∪ T) = μ S + μ T := by
  have hi : (S ∪ T) ∩ A = S := by
    ext ω
    constructor
    · rintro ⟨h | h, ha⟩
      · exact h
      · exact False.elim (hT h ha)
    · intro h
      exact ⟨Or.inl h, hS h⟩
  have hd : (S ∪ T) \ A = T := by
    ext ω
    constructor
    · rintro ⟨h | h, ha⟩
      · exact False.elim (ha (hS h))
      · exact h
    · intro h
      exact ⟨Or.inr h, hT h⟩
  have h := measure_inter_add_sdiff₀ (S ∪ T) hA
  rw [hi, hd] at h
  exact h.symm

/-- Equality of outer and inner probability characterizes completion
measurability. No measurability of S is assumed in the hypothesis. -/
lemma nullMeasurableSet_of_outer_compl_add {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Set Ω}
    (h : μ S + μ Sᶜ = μ Set.univ) : NullMeasurableSet S μ := by
  let A := toMeasurable μ S
  let B := toMeasurable μ Sᶜ
  have hA : MeasurableSet A := measurableSet_toMeasurable _ _
  have hB : MeasurableSet B := measurableSet_toMeasurable _ _
  have hu : A ∪ B = Set.univ := by
    apply eq_univ_of_forall
    intro ω
    by_cases hω : ω ∈ S
    · exact Or.inl (subset_toMeasurable μ S hω)
    · exact Or.inr (subset_toMeasurable μ Sᶜ hω)
  have hInter : μ (A ∩ B) = 0 := by
    have he := measure_union_add_inter (μ := μ) A hB
    rw [hu, measure_toMeasurable, measure_toMeasurable, h] at he
    apply (ENNReal.add_right_inj (measure_ne_top μ Set.univ)).mp
    simpa only [add_zero] using he
  have hdiff : μ (A \ S) = 0 := by
    apply measure_mono_null _ hInter
    intro ω hω
    exact ⟨hω.1, subset_toMeasurable μ Sᶜ hω.2⟩
  have hae : A =ᵐ[μ] S := by
    have hnot : ∀ᵐ ω ∂μ, ω ∉ A \ S := ae_iff.mpr (by
      convert hdiff using 1
      congr 1
      ext ω
      simp)
    filter_upwards [hnot] with ω hω
    apply propext
    constructor
    · intro ha
      by_contra hs
      exact hω ⟨ha, hs⟩
    · intro hs
      exact subset_toMeasurable μ S hs
  exact hA.nullMeasurableSet.congr hae

end HighDimStat.Concentration


-- Source module: TalagrandSeparatedCapacity

open MeasureTheory Set Filter
open scoped ENNReal

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

/-- A real map whose separated level ranges have additive outer measure
is a.e. measurable. This permits establishing measurability from outer
independence and a measurable continuous observable. -/
lemma aemeasurable_of_separated_outer_add {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (g : Ω → ℝ)
    (hsep : ∀ r s : ℝ, r < s →
      μ ({ω | g ω ≤ r} ∪ {ω | s ≤ g ω}) =
        μ {ω | g ω ≤ r} + μ {ω | s ≤ g ω}) : AEMeasurable g μ := by
  have hpre (c : ℝ) : NullMeasurableSet {ω | g ω < c} μ := by
    let A := fun n : ℕ => {ω | g ω ≤ c - 1 / ((n : ℝ) + 1)}
    let B := {ω | c ≤ g ω}
    have hmono : Monotone A := by
      intro n m hnm ω hω
      have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hdiv : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      change g ω ≤ c - 1 / ((m : ℝ) + 1)
      change g ω ≤ c - 1 / ((n : ℝ) + 1) at hω
      linarith
    have hUnion : (⋃ n, A n) = {ω | g ω < c} := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, hn⟩
        change g ω ≤ c - 1 / ((n : ℝ) + 1) at hn
        have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro hω
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hω)
        exact ⟨n, by change g ω ≤ c - 1 / ((n : ℝ) + 1); linarith⟩
    have hmonoU : Monotone (fun n => A n ∪ B) := fun n m hnm => union_subset_union (hmono hnm) Subset.rfl
    have hUnionU : (⋃ n, A n ∪ B) = Set.univ := by
      rw [← Set.iUnion_union, hUnion]
      ext ω
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_or_ge (g ω) c
    have hAdd : μ {ω | g ω < c} + μ B = μ Set.univ := by
      calc
        _ = (⨆ n, μ (A n)) + μ B := by rw [← hmono.measure_iUnion, hUnion]
        _ = ⨆ n, (μ (A n) + μ B) := ENNReal.iSup_add _
        _ = ⨆ n, μ (A n ∪ B) := by
          congr 1
          funext n
          have hp : 0 < 1 / ((n : ℝ)+1) := by positivity
          exact (hsep (c - 1 / ((n : ℝ) + 1)) c (by linarith)).symm
        _ = μ (⋃ n, A n ∪ B) := hmonoU.measure_iUnion.symm
        _ = _ := by rw [hUnionU]
    apply nullMeasurableSet_of_outer_compl_add
    simpa only [B, Set.compl_setOf, not_lt] using hAdd
  have hm : @Measurable (NullMeasurableSpace Ω μ) ℝ inferInstance inferInstance g :=
    measurable_of_Iio (fun c => hpre c)
  exact (show NullMeasurable g μ from hm).aemeasurable

end HighDimStat.Concentration


-- Source module: TalagrandLocalMeasurability

open MeasureTheory Set
open scoped ENNReal

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

/-- A possibly nonmeasurable real map is a.e. measurable if, on events of
positive outer measure independent of all of its Borel preimages, it is
arbitrarily well approximated by a measurable observable. -/
lemma aemeasurable_of_independent_local_approximation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (W Z : Ω → ℝ) (hZ : AEMeasurable Z μ)
    (hApprox : ∀ ε : ℝ, 0 < ε → ∃ B : Set Ω, μ B ≠ 0 ∧
      (∀ U : Set ℝ, MeasurableSet U → μ ((W ⁻¹' U) ∩ B) = μ (W ⁻¹' U) * μ B) ∧
      ∀ ω ∈ B, |Z ω - W ω| ≤ ε) : AEMeasurable W μ := by
  apply aemeasurable_of_separated_outer_add W
  intro r s hrs
  let ε := (s-r)/4
  obtain ⟨B, hBp, hBi, hBa⟩ := hApprox ε (by dsimp [ε]; linarith)
  let A := W ⁻¹' Set.Iic r
  let C := W ⁻¹' Set.Ici s
  let D := {ω | Z ω < (r+s)/2}
  have hD : NullMeasurableSet D μ := hZ.nullMeasurableSet_preimage measurableSet_Iio
  have hA : A ∩ B ⊆ D := by
    intro ω hω
    have he := (abs_le.mp (hBa ω hω.2)).2
    have hw : W ω ≤ r := hω.1
    change Z ω < (r+s)/2
    dsimp [ε] at he
    linarith [hw]
  have hC : C ∩ B ⊆ Dᶜ := by
    intro ω hω
    have he := (abs_le.mp (hBa ω hω.2)).1
    have hw : s ≤ W ω := hω.1
    change ¬ Z ω < (r+s)/2
    dsimp [ε] at he
    linarith [hw]
  have hUnion := measure_union_of_null_measurable_separator hD hA hC
  rw [← Set.union_inter_distrib_right] at hUnion
  have hiA := hBi (Set.Iic r) measurableSet_Iic
  have hiC := hBi (Set.Ici s) measurableSet_Ici
  have hiAC := hBi (Set.Iic r ∪ Set.Ici s) (measurableSet_Iic.union measurableSet_Ici)
  rw [Set.preimage_union] at hiAC
  change μ ((A ∪ C) ∩ B) = μ (A ∪ C) * μ B at hiAC
  change μ (A ∩ B) = μ A * μ B at hiA
  change μ (C ∩ B) = μ C * μ B at hiC
  rw [hiAC, hiA, hiC, ← add_mul] at hUnion
  exact (ENNReal.mul_left_inj hBp (measure_ne_top μ B)).mp hUnion

end HighDimStat.Concentration


-- Source module: TalagrandOuterSupport

open MeasureTheory Set Filter
open scoped Topology

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

/-- On a second-countable space, a countably complete filter is supported
on its cluster points. This does not assume the underlying map measurable. -/
lemma eventually_clusterPt_of_countableInter {E : Type*} [TopologicalSpace E]
    [SecondCountableTopology E] (F : Filter E) [CountableInterFilter F] :
    ∀ᶠ x in F, ClusterPt x F := by
  let K := {x | ClusterPt x F}
  change K ∈ F
  by_contra hK
  have hf : ∃ᶠ x in F, x ∈ Kᶜ := by
    have hnot : ¬ ∀ᶠ x in F, x ∈ K := by
      simpa only [Filter.Eventually, Set.setOf_mem_eq] using hK
    simpa only [Filter.Frequently, Set.mem_compl_iff, not_not] using hnot
  haveI : NeBot (F ⊓ 𝓟 Kᶜ) := frequently_mem_iff_neBot.mp hf
  have hL : IsLindelof Kᶜ := IsLindelof.of_coe
  obtain ⟨x, hx, hc⟩ := hL (show F ⊓ 𝓟 Kᶜ ≤ 𝓟 Kᶜ from inf_le_right)
  exact hx (hc.mono inf_le_left)

/-- A bounded real map, measurable or not, has a compact nonempty outer
essential support and belongs to it almost everywhere. Every neighborhood
of a support point has preimage of positive outer measure. -/
lemma bounded_outer_support {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Ω → ℝ)
    {a b : ℝ} (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    ∃ K : Set ℝ, IsCompact K ∧ K.Nonempty ∧ K ⊆ Set.Icc a b ∧
      (∀ᵐ ω ∂μ, X ω ∈ K) ∧
      ∀ y ∈ K, ∀ r : ℝ, 0 < r → μ (X ⁻¹' Metric.ball y r) ≠ 0 := by
  let F := Filter.map X (ae μ)
  let K := {y : ℝ | ClusterPt y F}
  have hKae : ∀ᵐ ω ∂μ, X ω ∈ K := eventually_clusterPt_of_countableInter F
  have hSub : K ⊆ Set.Icc a b := by
    intro y hy
    have hc := hy.mem_closure_of_mem (Set.Icc a b) (show Set.Icc a b ∈ F from hbound)
    simpa only [isClosed_Icc.closure_eq] using hc
  have hCompact : IsCompact K := isCompact_Icc.of_isClosed_subset isClosed_setOfPred_clusterPt hSub
  have hNonempty : K.Nonempty := by
    obtain ⟨ω, hω⟩ := hKae.exists
    exact ⟨X ω, hω⟩
  refine ⟨K, hCompact, hNonempty, hSub, hKae, ?_⟩
  intro y hy r hr
  have hf : ∃ᶠ ω in ae μ, X ω ∈ Metric.ball y r :=
    (mapClusterPt_iff_frequently.mp hy) _ (Metric.ball_mem_nhds y hr)
  convert frequently_ae_iff.mp hf using 1
  congr 1

end HighDimStat.Concentration


-- Source module: TalagrandCompactRepresentative

open MeasureTheory Set Function

namespace HighDimStat.Concentration

set_option maxHeartbeats 1400000

/-- A continuous profile on a compact subset of the real line admits a
Borel measurable representative in that subset. The representative is the
least point of each compact fiber; its strict sublevels are countable
unions of compact images. -/
lemma exists_measurable_compact_representative {E : Type*}
    [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    {K : Set ℝ} (hK : IsCompact K) (hKn : K.Nonempty)
    (G : ℝ → E) (hG : Continuous G) :
    ∃ R : E → ℝ, Measurable R ∧ ∀ x ∈ K, R (G x) ∈ K ∧ G (R (G x)) = G x := by
  classical
  let S := G '' K
  let F := fun u : S => {t : ℝ | t ∈ K ∧ G t = u.1}
  let R := fun u : S => sInf (F u)
  have hFclosed (u : S) : IsClosed (F u) :=
    hK.isClosed.inter (isClosed_eq hG continuous_const)
  have hFn (u : S) : (F u).Nonempty := by
    obtain ⟨x, hx, hxu⟩ := u.2
    exact ⟨x, hx, hxu⟩
  have hFb (u : S) : BddBelow (F u) := hK.bddBelow.mono (fun _ h => h.1)
  have hR (u : S) : R u ∈ K ∧ G (R u) = u.1 := (hFclosed u).csInf_mem (hFn u) (hFb u)
  have hRm : Measurable R := by
    apply measurable_of_Iio
    intro c
    have he : R ⁻¹' Set.Iio c =
        ⋃ q : {q : ℚ // (q : ℝ) < c},
          Subtype.val ⁻¹' (G '' (K ∩ Set.Iic (q.1 : ℝ))) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion]
      constructor
      · intro hu
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hu
        refine ⟨⟨q, hq2⟩, ?_⟩
        exact ⟨R u, ⟨(hR u).1, hq1.le⟩, (hR u).2⟩
      · rintro ⟨q, x, hx, hxu⟩
        have hmin : R u ≤ x := csInf_le (hFb u) ⟨hx.1, hxu⟩
        exact hmin.trans_lt (hx.2.trans_lt q.2)
    rw [he]
    apply MeasurableSet.iUnion
    intro q
    exact ((hK.inter_right isClosed_Iic).image hG).isClosed.measurableSet.preimage measurable_subtype_coe
  obtain ⟨R', hR'm, hR'eq⟩ :=
    (MeasurableEmbedding.subtype_coe ((hK.image hG).isClosed.measurableSet)).exists_measurable_extend hRm
      (fun _ => inferInstance)
  refine ⟨R', hR'm, ?_⟩
  intro x hx
  let u : S := ⟨G x, ⟨x, hx, rfl⟩⟩
  have he : R' (G x) = R u := congr_fun hR'eq u
  rw [he]
  exact hR u

end HighDimStat.Concentration


-- Source module: TalagrandOuterRectangle

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

/-- Rectangle factorization uses the exact outer-measure definition of
independence and requires no measurability of coordinate maps. -/
lemma coordinate_rectangle_outer_independence {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : Fin n → Ω → ℝ) (hIndep : iIndepFun X μ)
    (k : Fin n) (J : Finset (Fin n)) (hk : k ∉ J)
    (U : Set ℝ) (hU : MeasurableSet U)
    (S : Fin n → Set ℝ) (hS : ∀ i, MeasurableSet (S i)) :
    μ ((X k ⁻¹' U) ∩ (⋂ i ∈ J, X i ⁻¹' S i)) =
      μ (X k ⁻¹' U) * μ (⋂ i ∈ J, X i ⁻¹' S i) := by
  classical
  let V := Function.update S k U
  have hV (i : Fin n) : MeasurableSet (V i) := by
    by_cases hi : i = k
    · subst i
      simpa only [V, Function.update_self] using hU
    · simpa only [V, Function.update_of_ne hi] using hS i
  have hfull := hIndep.measure_inter_preimage_eq_mul (insert k J) (fun i _ => hV i)
  have hInsert : (⋂ i ∈ insert k J, X i ⁻¹' V i) =
      (X k ⁻¹' V k) ∩ (⋂ i ∈ J, X i ⁻¹' V i) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
    aesop
  rw [hInsert, Finset.prod_insert hk] at hfull
  have he : (⋂ i ∈ J, X i ⁻¹' V i) = (⋂ i ∈ J, X i ⁻¹' S i) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor <;> intro h i hi
    · simpa only [V, Function.update_of_ne (show i ≠ k from fun he => hk (he ▸ hi))] using h i hi
    · simpa only [V, Function.update_of_ne (show i ≠ k from fun he => hk (he ▸ hi))] using h i hi
  have hp : (∏ i ∈ J, μ (X i ⁻¹' V i)) = ∏ i ∈ J, μ (X i ⁻¹' S i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [show V i = S i from Function.update_of_ne (show i ≠ k from fun he => hk (he ▸ hi)) U S]
  have hrect := hIndep.measure_inter_preimage_eq_mul J (fun i _ => hS i)
  rw [he, hp, show V k = U from Function.update_self k U S, ← hrect] at hfull
  exact hfull

end HighDimStat.Concentration


-- Source module: TalagrandCoordinateProfile

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HighDimStat.Concentration

set_option maxHeartbeats 1500000

/-- Fixing other coordinates at points of their outer essential supports
produces a measurable coordinate profile, even when the coordinates
themselves are not measurable. -/
lemma native_coordinate_slice_aemeasurable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : Fin n → Ω → ℝ)
    (hIndep : iIndepFun X μ) (f : (Fin n → ℝ) → ℝ) {L : ℝ}
    (hLip : IsLLipschitz f L) (hZ : AEMeasurable (fun ω => f (fun i => X i ω)) μ)
    (k : Fin n) (y : Fin n → ℝ)
    (hPositive : ∀ i, i ≠ k → ∀ r : ℝ, 0 < r → μ (X i ⁻¹' Metric.ball (y i) r) ≠ 0) :
    AEMeasurable (fun ω => f (Function.update y k (X k ω))) μ := by
  classical
  let g := fun t : ℝ => f (Function.update y k t)
  have hg : Continuous g := (native_lipschitz_continuous hLip).comp
    (show Continuous (fun t : ℝ => Function.update y k t) from by fun_prop)
  apply aemeasurable_of_independent_local_approximation
    (fun ω => g (X k ω)) (fun ω => f (fun i => X i ω)) hZ
  intro ε hε
  let A := |L| * Real.sqrt (n : ℝ)
  let ρ := ε / (A + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hden : 0 < A+1 := by linarith
  have hρ : 0 < ρ := div_pos hε hden
  have hAρ : A * ρ ≤ ε := by
    dsimp [ρ]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  let J := Finset.univ.erase k
  let S := fun i : Fin n => Metric.ball (y i) ρ
  let B := ⋂ i ∈ J, X i ⁻¹' S i
  have hS (i : Fin n) : MeasurableSet (S i) := Metric.isOpen_ball.measurableSet
  have hBp : μ B ≠ 0 := by
    change μ (⋂ i ∈ J, X i ⁻¹' S i) ≠ 0
    rw [hIndep.measure_inter_preimage_eq_mul J (fun i _ => hS i)]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hPositive i (Finset.ne_of_mem_erase hi) ρ hρ
  refine ⟨B, hBp, ?_, ?_⟩
  · intro U hU
    change μ ((X k ⁻¹' (g ⁻¹' U)) ∩ B) = μ (X k ⁻¹' (g ⁻¹' U)) * μ B
    exact coordinate_rectangle_outer_independence X hIndep k J (by simp [J])
      (g ⁻¹' U) (hg.measurable hU) S hS
  · intro ω hω
    have hsum : (∑ i, (X i ω - Function.update y k (X k ω) i) ^ 2) ≤ (n : ℝ) * ρ ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin n, ρ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hik : i = k
          · subst i
            simp only [Function.update_self, sub_self, zero_pow (by norm_num : 2 ≠ 0)]
            positivity
          · have hnear : X i ω ∈ Metric.ball (y i) ρ :=
              (Set.mem_iInter.mp (Set.mem_iInter.mp hω i)
                (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩))
            have hd : |X i ω - y i| ≤ ρ := by
              have hd' : |X i ω - y i| < ρ := by
                simpa only [Metric.mem_ball, Real.dist_eq] using hnear
              exact hd'.le
            rw [Function.update_of_ne hik]
            simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
        _ = _ := by simp
    have hsqrt : Real.sqrt (∑ i, (X i ω - Function.update y k (X k ω) i) ^ 2) ≤
        Real.sqrt (n : ℝ) * ρ := by
      have h := Real.sqrt_le_sqrt hsum
      simpa only [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs, abs_of_pos hρ] using h
    calc
      _ ≤ L * Real.sqrt (∑ i, (X i ω - Function.update y k (X k ω) i) ^ 2) := hLip _ _
      _ ≤ |L| * Real.sqrt (∑ i, (X i ω - Function.update y k (X k ω) i) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self L) (Real.sqrt_nonneg _)
      _ ≤ |L| * (Real.sqrt (n : ℝ) * ρ) :=
        mul_le_mul_of_nonneg_left hsqrt (abs_nonneg _)
      _ = A * ρ := by dsimp [A]; ring
      _ ≤ ε := hAρ

end HighDimStat.Concentration


-- Source module: TalagrandCoordinateReplacement

namespace HighDimStat.Concentration

set_option maxHeartbeats 1000000

/-- Coordinate replacements that preserve every admissible slice preserve
the whole observable, by replacing one coordinate at a time. -/
lemma coordinatewise_replacement_preserves {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (K : Fin n → Set ℝ) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ K i) (hy : ∀ i, y i ∈ K i)
    (hStep : ∀ i z, (∀ j, z j ∈ K j) →
      f (Function.update z i (x i)) = f (Function.update z i (y i))) : f x = f y := by
  classical
  let z := fun (I : Finset (Fin n)) (j : Fin n) => if j ∈ I then y j else x j
  have hz (I : Finset (Fin n)) (j : Fin n) : z I j ∈ K j := by
    dsimp [z]
    split_ifs
    · exact hy j
    · exact hx j
  have hI (I : Finset (Fin n)) : f (z I) = f x := by
    induction I using Finset.induction_on with
    | empty => simp [z]
    | @insert i I hi hIH =>
      have he : z (insert i I) = Function.update (z I) i (y i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [z]
        · simp [z, hji, Function.update_of_ne hji]
      have hu : Function.update (z I) i (x i) = z I := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [z, hi]
        · rw [Function.update_of_ne hji]
      calc
        _ = f (Function.update (z I) i (y i)) := congrArg f he
        _ = f (Function.update (z I) i (x i)) := (hStep i (z I) (hz I)).symm
        _ = f (z I) := congrArg f hu
        _ = f x := hIH
  have h := hI Finset.univ
  simpa only [z, Finset.mem_univ, ite_true] using h.symm

end HighDimStat.Concentration


-- Source module: TalagrandMeasurableRepresentation

open MeasureTheory ProbabilityTheory Set Function

namespace HighDimStat.Concentration

set_option maxHeartbeats 2000000

/-- Outer-independent bounded real maps admit measurable independent
representatives preserving any a.e. measurable Lipschitz observable.
The coordinate maps themselves need not be a.e. measurable. -/
lemma independent_measurable_representation_of_lipschitz_observable
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℝ) (hIndep : iIndepFun X μ)
    (a b : ℝ) (hSupport : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b)
    (f : (Fin n → ℝ) → ℝ) {L : ℝ} (hLip : IsLLipschitz f L)
    (hZ : AEMeasurable (fun ω => f (fun i => X i ω)) μ) :
    ∃ Y : Fin n → Ω → ℝ, (∀ i, AEMeasurable (Y i) μ) ∧ iIndepFun Y μ ∧
      (∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc a b) ∧
      (fun ω => f (fun i => X i ω)) =ᵐ[μ] (fun ω => f (fun i => Y i ω)) := by
  classical
  choose K hK hKn hKsub hXK hKpos using fun i => bounded_outer_support (X i) (hSupport i)
  haveI : ∀ i, Nonempty (K i) := fun i => (hKn i).to_subtype
  let C := ∀ i, K i
  let coeC := fun z : C => fun i => (z i : ℝ)
  have hcoe : Continuous coeC := continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i)
  obtain ⟨ys, hys⟩ := TopologicalSpace.exists_dense_seq C
  let ref := fun m => coeC (ys m)
  let G := fun (i : Fin n) (t : ℝ) (m : ℕ) => f (Function.update (ref m) i t)
  have hF : Continuous f := native_lipschitz_continuous hLip
  have hGc (i : Fin n) : Continuous (G i) := continuous_pi fun m =>
    hF.comp (show Continuous (fun t : ℝ => Function.update (ref m) i t) from by fun_prop)
  have hGXm (i : Fin n) : AEMeasurable (fun ω => G i (X i ω)) μ := by
    apply aemeasurable_pi_lambda
    intro m
    apply native_coordinate_slice_aemeasurable X hIndep f hLip hZ i (ref m)
    intro j hj r hr
    exact hKpos j (ref m j) (ys m j).2 r hr
  choose R hRm hRspec using fun i => exists_measurable_compact_representative (hK i) (hKn i) (G i) (hGc i)
  let T := fun (i : Fin n) (t : ℝ) => R i (G i t)
  let Y := fun (i : Fin n) (ω : Ω) => T i (X i ω)
  have hTm (i : Fin n) : Measurable (T i) := (hRm i).comp (hGc i).measurable
  have hYm (i : Fin n) : AEMeasurable (Y i) μ := (hRm i).comp_aemeasurable (hGXm i)
  have hYi : iIndepFun Y μ := hIndep.comp T hTm
  have hYK (i : Fin n) : ∀ᵐ ω ∂μ, Y i ω ∈ K i := by
    filter_upwards [hXK i] with ω hω
    exact (hRspec i (X i ω) hω).1
  have hYsupport (i : Fin n) : ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc a b := by
    filter_upwards [hYK i] with ω hω
    exact hKsub i hω
  refine ⟨Y, hYm, hYi, hYsupport, ?_⟩
  filter_upwards [ae_all_iff.mpr hXK, ae_all_iff.mpr hYK] with ω hω hYω
  apply coordinatewise_replacement_preserves f K (fun i => X i ω) (fun i => Y i ω) hω hYω
  intro i z hz
  have hp : G i (X i ω) = G i (Y i ω) := (hRspec i (X i ω) (hω i)).2.symm
  let Fa := fun w : C => f (Function.update (coeC w) i (X i ω))
  let Fb := fun w : C => f (Function.update (coeC w) i (Y i ω))
  have hFa : Continuous Fa := hF.comp
    (show Continuous (fun w : C => Function.update (coeC w) i (X i ω)) from by fun_prop)
  have hFb : Continuous Fb := hF.comp
    (show Continuous (fun w : C => Function.update (coeC w) i (Y i ω)) from by fun_prop)
  have hecomp : Fa ∘ ys = Fb ∘ ys := by
    funext m
    exact congr_fun hp m
  have he : Fa = Fb := hys.equalizer hFa hFb hecomp
  let w : C := fun j => ⟨z j, hz j⟩
  exact congr_fun he w

end HighDimStat.Concentration


-- Source module: TalagrandNativeTail

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 2000000

namespace HighDimStat.Concentration

/-- **Theorem 3.4**, Wainwright, *High-Dimensional Statistics* (2019), p. 62. Let `{Xᵢ}` be
independent random variables, each supported on `[a,b]`, and let `f : ℝⁿ → ℝ` be separately
convex and `L`-Lipschitz with respect to the Euclidean norm. Then for all `δ>0`,
`P[f(X) ≥ E[f(X)]+δ] ≤ exp(-δ²/(4L²(b-a)²))`. -/
theorem separately_convex_lipschitz_concentration {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (X : Fin n → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hIndep : iIndepFun X Prob) (hSupport : ∀ i, ∀ᵐ ω ∂Prob, X i ω ∈ Set.Icc a b)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hSepConvex : IsSeparatelyConvex f) (hLip : IsLLipschitz f L)
    (hInt : Integrable (fun ω => f (fun i => X i ω)) Prob) (δ : ℝ) (hδ : 0 < δ) :
    Prob.real {ω | (∫ ω', f (fun i => X i ω') ∂Prob) + δ ≤ f (fun i => X i ω)} ≤
      Real.exp (-(δ ^ 2) / (4 * L ^ 2 * (b - a) ^ 2)) := by
  obtain ⟨Y, hYm, hYi, hYs, hEq⟩ :=
    independent_measurable_representation_of_lipschitz_observable X hIndep a b hSupport f hLip hInt.aemeasurable
  have hIntY : Integrable (fun ω => f (fun i => Y i ω)) Prob := hInt.congr hEq
  have hm : (∫ ω, f (fun i => X i ω) ∂Prob) = ∫ ω, f (fun i => Y i ω) ∂Prob := integral_congr_ae hEq
  have hs : {ω | (∫ ω', f (fun i => X i ω') ∂Prob) + δ ≤ f (fun i => X i ω)} =ᵐ[Prob]
      {ω | (∫ ω', f (fun i => Y i ω') ∂Prob) + δ ≤ f (fun i => Y i ω)} := by
    filter_upwards [hEq] with ω hω
    change ((∫ ω', f (fun i => X i ω') ∂Prob) + δ ≤ f (fun i => X i ω)) =
      ((∫ ω', f (fun i => Y i ω') ∂Prob) + δ ≤ f (fun i => Y i ω))
    rw [hm, hω]
  have hp : Prob.real {ω | (∫ ω', f (fun i => X i ω') ∂Prob) + δ ≤ f (fun i => X i ω)} =
      Prob.real {ω | (∫ ω', f (fun i => Y i ω') ∂Prob) + δ ≤ f (fun i => Y i ω)} :=
    congrArg ENNReal.toReal (measure_congr hs)
  rw [hp]
  exact separately_convex_lipschitz_concentration_of_aemeasurable Y hYm a b hab hYi hYs f L hSepConvex hLip hIntY δ hδ

end HighDimStat.Concentration


open MeasureTheory ProbabilityTheory HighDimStat.Concentration

theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (X : Fin n → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hIndep : iIndepFun X Prob) (hSupport : ∀ i, ∀ᵐ ω ∂Prob, X i ω ∈ Set.Icc a b)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hSepConvex : IsSeparatelyConvex f) (hLip : IsLLipschitz f L)
    (hInt : Integrable (fun ω => f (fun i => X i ω)) Prob) (δ : ℝ) (hδ : 0 < δ) :
    Prob.real {ω | (∫ ω', f (fun i => X i ω') ∂Prob) + δ ≤ f (fun i => X i ω)} ≤
      Real.exp (-(δ ^ 2) / (4 * L ^ 2 * (b - a) ^ 2)) := by
  exact HighDimStat.Concentration.separately_convex_lipschitz_concentration
    X a b hab hIndep hSupport f L hSepConvex hLip hInt δ hδ


#print axioms solution
