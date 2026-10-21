-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.analytic_collision_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:06:24.860071+00:00
-- url     : https://prove2.me/submissions/b864cd03-dd30-48cf-ba09-3de92a8e36ef

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib

open scoped BigOperators Topology
open Complex Filter MeasureTheory
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

/-!
# The analytic collision factor bound

This file proves the analytic collision bound for Cauchy row tests of translated entire
functions: the determinant of the matrix of row tests is bounded by a factorial, the row orders
captured by `2 ^ (∑ ell r)`, a collision factor `s ^ (∑ choose(multiplicity, 2))` and a geometric
factor `(1 - s)⁻¹ ^ card`.  The proof ports the analytic collision estimate from the upstream
formalization into the `FinitePeriodCollision` definition bundle.
-/

namespace P2MCollisionPort

/-! ## Collision combinatorics -/

theorem p2m_choose_card_le_sum (s : Finset ℕ) : s.card.choose 2 ≤ ∑ d ∈ s, d := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := by
      intro h
      exact (lt_irrefl a) (hmax a h)
    have hsub : s ⊆ Finset.range a := by
      intro x hx
      exact Finset.mem_range.mpr (hmax x hx)
    have hcard : s.card ≤ a := by
      simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    rw [show s.card + 1 = s.card.succ from rfl,
      Nat.choose_succ_succ s.card 1, Nat.choose_one_right]
    exact Nat.add_le_add hcard ih

theorem p2m_choose_card_le_sum_of_injOn {ι : Type*} (s : Finset ι)
    (degree : ι → ℕ) (hinj : Set.InjOn degree (s : Set ι)) :
    s.card.choose 2 ≤ ∑ i ∈ s, degree i := by
  have h := p2m_choose_card_le_sum (s.image degree)
  rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj] at h
  exact h

/-- The multiplicity of a group value among the rows. -/
def p2m_multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (a : κ) : ℕ :=
  (rows.filter fun i => group i = a).card

theorem p2m_sum_choose_multiplicity_le_sum_degree {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) (degree : ι → ℕ)
    (hgroups : ∀ i ∈ rows, group i ∈ groups)
    (hinj : Set.InjOn (fun i => (group i, degree i)) (rows : Set ι)) :
    (∑ a ∈ groups, (p2m_multiplicity rows group a).choose 2) ≤
      ∑ i ∈ rows, degree i := by
  calc
    (∑ a ∈ groups, (p2m_multiplicity rows group a).choose 2) ≤
        ∑ a ∈ groups, ∑ i ∈ rows.filter (fun i => group i = a), degree i := by
      apply Finset.sum_le_sum
      intro a _
      apply p2m_choose_card_le_sum_of_injOn
      intro i hi j hj hdegree
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      apply hinj hi'.1 hj'.1
      exact Prod.ext (hi'.2.trans hj'.2.symm) hdegree
    _ = ∑ i ∈ rows, degree i :=
      Finset.sum_fiberwise_of_maps_to hgroups degree

theorem p2m_sum_choose_multiplicity_le_sum_degree_univ
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (degree : ι → ℕ)
    (hinj : Function.Injective (fun i => (group i, degree i))) :
    (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) ≤ ∑ i, degree i := by
  exact p2m_sum_choose_multiplicity_le_sum_degree Finset.univ Finset.univ group degree
    (by simp) hinj.injOn

/-! ## Geometric series estimates -/

theorem p2m_sum_pow_fin_le_inv_one_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (N : ℕ) : (∑ k : Fin N, s ^ (k : ℕ)) ≤ (1 - s)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => s ^ k), ← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hs1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self 1 (pow_nonneg hs0 N)

theorem p2m_sum_pow_degree_assignments_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) =
      (∑ k : Fin N, s ^ (k : ℕ)) ^ Fintype.card ι := by
  classical
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (_ : ι) (k : Fin N) => s ^ (k : ℕ))]
  simp

theorem p2m_sum_pow_degree_assignments_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) ≤
      ((1 - s)⁻¹) ^ Fintype.card ι := by
  rw [p2m_sum_pow_degree_assignments_eq]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => pow_nonneg hs0 _)
    (p2m_sum_pow_fin_le_inv_one_sub hs0 hs1 N) _

theorem p2m_collision_geometric_sum_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f ∈ (Finset.univ : Finset (ι → Fin N)).filter
        (fun f => Function.Injective (fun i => (group i, (f i : ℕ)))),
      (s * s) ^ (∑ i, (f i : ℕ))) ≤
      s ^ (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let C := ∑ a, (p2m_multiplicity Finset.univ group a).choose 2
  have hpoint : ∀ f ∈ good,
      (s * s) ^ (∑ i, (f i : ℕ)) ≤ s ^ C * s ^ (∑ i, (f i : ℕ)) := by
    intro f hf
    have hinj := (Finset.mem_filter.mp hf).2
    have hdeg : C ≤ ∑ i, (f i : ℕ) :=
      p2m_sum_choose_multiplicity_le_sum_degree_univ group (fun i => (f i : ℕ)) hinj
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1.le hdeg)
      (pow_nonneg hs0 _)
  calc
    _ ≤ ∑ f ∈ good, s ^ C * s ^ (∑ i, (f i : ℕ)) :=
      Finset.sum_le_sum hpoint
    _ = s ^ C * ∑ f ∈ good, s ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ s ^ C * ∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs0 C)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro f _ _
      exact pow_nonneg hs0 _
    _ ≤ _ := mul_le_mul_of_nonneg_left (p2m_sum_pow_degree_assignments_le hs0 hs1 N)
      (pow_nonneg hs0 C)

/-! ## Cauchy coefficient and row-test estimates -/

noncomputable def p2m_normalizedTaylorCoeff (f : ℂ → ℂ) (R : ℝ) (d : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))

theorem p2m_norm_normalizedTaylorCoeff_le {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R)
    (hD : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ D) (d : ℕ) :
    ‖p2m_normalizedTaylorCoeff f R d‖ ≤ D := by
  unfold p2m_normalizedTaylorCoeff
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ R * (R⁻¹ * D) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
      intro z hz
      have hzR : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, norm_inv, hzR, div_self (ne_of_gt hR),
        one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left (hD z hz) (inv_nonneg.mpr hR.le)
    _ = D := by field_simp

theorem p2m_norm_rowTest_le {f : ℂ → ℂ} {D : ℝ}
    (hD : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖f t‖ ≤ D) (ell : ℕ) :
    ‖rowTest ell f‖ ≤ (2 : ℝ) ^ ell * D := by
  unfold rowTest
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ (1 / 2 : ℝ) * (2 ^ ell * (2 * D)) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
      intro z hz
      have hzR : ‖z‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hzR]
      norm_num only [one_div, inv_div, div_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD z hz) (by norm_num))
        (by positivity)
    _ = _ := by ring

theorem p2m_norm_shifted_log_div_le_half {center t : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ht : ‖t‖ ≤ 1 / 2) :
    ‖(center + Complex.log (1 + t)) / (R : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  have hlog := Complex.norm_log_one_add_half_le_self ht
  have htri := norm_add_le center (Complex.log (1 + t))
  nlinarith

theorem p2m_norm_rowTest_shifted_power_le {center : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)‖ ≤
      (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  apply p2m_norm_rowTest_le
  intro t ht
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) (p2m_norm_shifted_log_div_le_half hR hc _)
  simpa only [Metric.mem_sphere, dist_zero_right] using ht.le

/-- The terms `cauchyPowerSeries f 0 R d (fun _ => z)` are the normalized Taylor coefficients
multiplied by `(z / R) ^ d`. -/
theorem p2m_cauchyPowerSeries_const_eq (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R) (z : ℂ) (d : ℕ) :
    cauchyPowerSeries f 0 R d (fun _ => z) =
      p2m_normalizedTaylorCoeff f R d * (z / (R : ℂ)) ^ d := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  rw [p2m_normalizedTaylorCoeff, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [div_pow, div_eq_mul_inv]
  field_simp

theorem p2m_hasSum_normalizedTaylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) (z : ℂ) :
    HasSum (fun d => p2m_normalizedTaylorCoeff f R d * (z / (R : ℂ)) ^ d) (f z) := by
  have hs : HasSum (fun d => cauchyPowerSeries f 0 (R : ℝ) d (fun _ => z)) (f z) := by
    have h := (hf.hasFPowerSeriesOnBall 0 hR).hasSum (y := z) (by simp)
    simpa only [zero_add] using h
  have heq : (fun d => cauchyPowerSeries f 0 (R : ℝ) d (fun _ => z)) =
      (fun d => p2m_normalizedTaylorCoeff f R d * (z / (R : ℂ)) ^ d) := by
    funext d
    exact p2m_cauchyPowerSeries_const_eq f (by exact_mod_cast hR) z d
  rw [heq] at hs
  exact hs

/-! ## Row-test series of dominated convergent families -/

theorem p2m_hasSum_rowTest {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {bound : ℕ → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n z, z ∈ Metric.sphere (0 : ℂ) (1 / 2) → ‖F n z‖ ≤ bound n)
    (hsum : Summable bound)
    (hpoint : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), HasSum (fun n => F n z) (f z))
    (ell : ℕ) : HasSum (fun n => rowTest ell (F n)) (rowTest ell f) := by
  simp only [rowTest, cauchyPowerSeries_apply]
  apply HasSum.const_smul
  change HasSum (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • F n (circleMap 0 (1 / 2) θ)))
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • f (circleMap 0 (1 / 2) θ)))
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => (2 : ℝ) ^ ell * bound n)
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [deriv_circleMap]
    exact (by fun_prop)
  · intro n
    apply Eventually.of_forall
    intro θ _
    have hb := hbound n (circleMap 0 (1 / 2) θ) (circleMap_mem_sphere 0 (by norm_num) θ)
    simp only [deriv_circleMap, norm_smul, norm_mul, norm_I, mul_one, sub_zero,
      norm_pow, norm_div, norm_one, norm_inv, norm_circleMap_zero]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), one_div, inv_div, div_one]
    calc
      _ = (2 : ℝ) ^ ell * ‖F n (circleMap 0 (1 / 2) θ)‖ := by ring
      _ ≤ (2 : ℝ) ^ ell * bound n := mul_le_mul_of_nonneg_left hb (by positivity)
  · exact Eventually.of_forall fun _ _ => hsum.mul_left _
  · simpa only [tsum_mul_left] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (2 : ℝ) ^ ell * ∑' n, bound n)
        volume 0 (2 * Real.pi))
  · apply Eventually.of_forall
    intro θ _
    exact (((hpoint _ (circleMap_mem_sphere 0 (by norm_num) θ)).const_smul _).const_smul _).const_smul _

theorem p2m_rowTest_const_mul (ell : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    rowTest ell (fun t => c * f t) = c * rowTest ell f := by
  simp only [rowTest, cauchyPowerSeries_apply, smul_eq_mul]
  have heq : (fun z : ℂ => (1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * (c * f z))) =
      (fun z : ℂ => c * ((1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * f z))) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring

theorem p2m_hasSum_translated_row {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ D)
    {center : ℂ} (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) :
    HasSum (fun d => rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
      p2m_normalizedTaylorCoeff f R d)
      (rowTest ell (fun t => f (center + Complex.log (1 + t)))) := by
  have h := p2m_hasSum_rowTest
    (F := fun d t => p2m_normalizedTaylorCoeff f R d *
      ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)
    (f := fun t => f (center + Complex.log (1 + t)))
    (bound := fun d => D * (1 / 2 : ℝ) ^ d)
    (by intro d; fun_prop) ?_ ?_ ?_ ell
  · convert h using 1
    funext d
    rw [p2m_rowTest_const_mul, mul_comm]
  · intro d t ht
    rw [norm_mul, norm_pow]
    apply mul_le_mul (p2m_norm_normalizedTaylorCoeff_le hR hfD d)
    · apply pow_le_pow_left₀ (norm_nonneg _) (p2m_norm_shifted_log_div_le_half hR hc _)
      simpa only [Metric.mem_sphere, dist_zero_right] using ht.le
    · positivity
    · exact hD
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left D
  · intro t _
    exact p2m_hasSum_normalizedTaylorCoeff hf hR _


/-! ## Determinant bounds -/

theorem p2m_det_finite_row_sum {ι κ δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype δ] (group : ι → κ) (B : ι → δ → ℂ) (C : κ → δ → ι → ℂ) :
    Matrix.det (fun i j => ∑ d, B i d * C (group i) d j) =
      ∑ f : ι → δ, (∏ i, B i (f i)) *
        Matrix.det (fun i j => C (group i) (f i) j) := by
  classical
  have hm := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
    (fun i d => B i d • C (group i) d)
  calc
    _ = Matrix.det (fun i => ∑ d, B i d • C (group i) d) := by
      congr 1
      funext i j
      simp
    _ = ∑ f : ι → δ, Matrix.det (fun i => B i (f i) • C (group i) (f i)) := hm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      exact Matrix.det_mul_column (fun i => B i (f i)) (fun i j => C (group i) (f i) j)

theorem p2m_norm_det_le_factorial_mul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {D : ℝ} (hD : 0 ≤ D) (hA : ∀ i j, ‖A i j‖ ≤ D) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * D ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖σ.sign • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A (σ i) i‖ := by
      apply Finset.sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or σ.sign with hs | hs <;> simp [hs, norm_prod]
    _ ≤ ∑ _σ : Equiv.Perm ι, D ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _index : ι, |D| := Finset.prod_le_prod
          (fun index _ => norm_nonneg _) (fun index _ => (hA (σ index) index).trans (le_abs_self D))
        _ = D ^ Fintype.card ι := by simp [abs_of_nonneg hD]
    _ = _ := by simp [Fintype.card_perm]

theorem p2m_finite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ a d j, ‖C a d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d) (N : ℕ) :
    ‖Matrix.det (fun i j => ∑ d : Fin N, B i d * C (group i) d j)‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let Q := (Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
      (Finset.prod_nonneg fun i _ => hL i)
  have hexpand : Matrix.det (fun i j => ∑ d : Fin N, B i d * C (group i) d j) =
      ∑ f ∈ good, (∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j) := by
    rw [p2m_det_finite_row_sum group (fun i (d : Fin N) => B i d)
      (fun a (d : Fin N) j => C a d j)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hn : ¬ Function.Injective (fun i => (group i, (f i : ℕ))) := by
      simpa [good] using hf
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hn
    have hg : group i = group j := congrArg Prod.fst hij
    have hd : (f i : ℕ) = (f j : ℕ) := congrArg Prod.snd hij
    have hz : Matrix.det (fun r c => C (group r) (f r) c) = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      funext c
      simp only [hg, hd]
    simp [hz]
  have hterm (f : ι → Fin N) :
      ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ ≤
        Q * (s * s) ^ (∑ i, (f i : ℕ)) := by
    have hbp : (∏ i, ‖B i (f i)‖) ≤ ∏ i, L i * (s * s) ^ (f i : ℕ) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hB i (f i))
    have hcp := p2m_norm_det_le_factorial_mul_pow
      (fun i j => C (group i) (f i) j) hD (fun i j => hC _ _ _)
    rw [norm_mul, norm_prod]
    calc
      _ ≤ (∏ i, L i * (s * s) ^ (f i : ℕ)) *
          ((Fintype.card ι).factorial * D ^ Fintype.card ι) :=
        mul_le_mul hbp hcp (norm_nonneg _) (Finset.prod_nonneg fun i _ =>
          mul_nonneg (hL i) (pow_nonneg (mul_self_nonneg s) _))
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        dsimp [Q]
        ring
  rw [hexpand]
  calc
    _ ≤ ∑ f ∈ good,
        ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f ∈ good, Q * (s * s) ^ (∑ i, (f i : ℕ)) :=
      Finset.sum_le_sum (fun f _ => hterm f)
    _ = Q * ∑ f ∈ good, (s * s) ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ Q * (s ^ (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι) :=
      mul_le_mul_of_nonneg_left (p2m_collision_geometric_sum_le group hs0 hs1 N) hQ
    _ = _ := by dsimp [Q]; ring

/-! ## Passage to infinite determinantal expansions -/

theorem p2m_norm_det_le_of_entrywise_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℂ) (T : Matrix ι ι ℂ) {B : ℝ}
    (hlim : ∀ i j, Tendsto (fun N => A N i j) atTop (𝓝 (T i j)))
    (hbound : ∀ N, ‖(A N).det‖ ≤ B) : ‖T.det‖ ≤ B := by
  have hmatrix : Tendsto A atTop (𝓝 T) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mpr (hlim i)
  have hdet : Tendsto (fun N => (A N).det) atTop (𝓝 T.det) :=
    (continuous_id.matrix_det.tendsto T).comp hmatrix
  exact le_of_tendsto' hdet.norm hbound

theorem p2m_norm_det_le_of_entrywise_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ℕ → ι → ℂ) (T : Matrix ι ι ℂ) {B : ℝ}
    (hsum : ∀ i j, HasSum (fun d => C i d j) (T i j))
    (hbound : ∀ N, ‖Matrix.det (fun i j => ∑ d ∈ Finset.range N, C i d j)‖ ≤ B) :
    ‖T.det‖ ≤ B := by
  exact p2m_norm_det_le_of_entrywise_limit
    (fun N i j => ∑ d ∈ Finset.range N, C i d j) T
    (fun i j => (hsum i j).tendsto_sum_nat) hbound

theorem p2m_norm_det_le_of_tested_series_hasSum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (group : ι → κ) (coeff : κ → ℕ → ι → ℂ) (test : ι → ℕ → ℂ)
    (T : Matrix ι ι ℂ) {B : ℝ}
    (hsum : ∀ i j, HasSum (fun d => test i d * coeff (group i) d j) (T i j))
    (hbound : ∀ N,
      ‖Matrix.det (fun i j => ∑ d ∈ Finset.range N, test i d * coeff (group i) d j)‖ ≤ B) :
    ‖T.det‖ ≤ B := by
  exact p2m_norm_det_le_of_entrywise_hasSum
    (fun i d j => test i d * coeff (group i) d j) T hsum hbound

theorem p2m_infinite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ a d j, ‖C a d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (T i j)) :
    ‖T.det‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  apply p2m_norm_det_le_of_tested_series_hasSum group C B T hsum
  intro N
  have hmatrix : (fun i j => ∑ d ∈ Finset.range N, B i d * C (group i) d j) =
      (fun i j => ∑ d : Fin N, B i d * C (group i) d j) := by
    funext i j
    exact (Fin.sum_univ_eq_sum_range (fun d : ℕ => B i d * C (group i) d j) N).symm
  rw [hmatrix]
  exact p2m_finite_collision_bound group B C D s L hD hs0 hs1
    hL hC hB N

end P2MCollisionPort

open P2MCollisionPort

/-- **Analytic collision factor bound.**  Entire column functions bounded by `D` on the circle of
radius `R`, whose translated logarithmic tests have centers in the half-radius region, satisfy the
explicit factorial, row-order and within-group collision determinant estimate. -/
theorem solution
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) (D s : ℝ)
    (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hss : s * s = 1 / 2)
    (hf : ∀ b c, Differentiable ℂ (f b c))
    (hfD : ∀ b c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f b c z‖ ≤ D)
    (hc : ∀ r, ‖center r‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun r c => rowTest (ell r)
      (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
      (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ r, ell r)) *
      s ^ (∑ b : κ,
        (((Finset.univ : Finset ι).filter (fun r => group r = b)).card).choose 2) *
      ((1 - s)⁻¹) ^ Fintype.card ι := by
  let B : ι → ℕ → ℂ := fun i d => rowTest (ell i)
    (fun t => ((center i + Complex.log (1 + t)) / (R : ℂ)) ^ d)
  let C : κ → ℕ → ι → ℂ := fun a d j => p2m_normalizedTaylorCoeff (f a j) R d
  have hb := p2m_infinite_collision_bound (group := group) (B := B) (C := C) (D := D) (s := s)
    (L := fun i => (2 : ℝ) ^ ell i) hD hs0 hs1 (fun _ => by positivity)
    (fun a d j => p2m_norm_normalizedTaylorCoeff_le (by exact_mod_cast hR) (hfD a j) d)
    (fun i d => by
      dsimp only [B]
      rw [hss]
      exact p2m_norm_rowTest_shifted_power_le (by exact_mod_cast hR) (hc i) (ell i) d)
    (T := fun r c => rowTest (ell r)
      (fun t => f (group r) c (center r + Complex.log (1 + t))))
    (fun i j => p2m_hasSum_translated_row (hf (group i) j) hR hD (hfD (group i) j) (hc i) (ell i))
  simpa only [Finset.prod_pow_eq_pow_sum, p2m_multiplicity] using hb
