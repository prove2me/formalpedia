-- Prove2me | solution 1 for HunterPDE.Parabolic.rellich_h10_l2_compact
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T10:34:05.654345+00:00
-- url     : https://prove2.me/submissions/ce7f5b36-2cfd-4afb-8343-e973c490a644

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10

/-! Child of the reduction of `HunterPDE.Parabolic.weak_solution_exists_unique` (Hunter, Thm 6.3):
Rellich compactness. For bounded open `Ω ⊂ ℝⁿ` the embedding `H¹₀(Ω) → L²(Ω)` is a compact operator.
Proof: approximate `toL2L` in operator norm by the finite-rank cube-average projections `Ph`
(piecewise constant on a grid of mesh `h`), using the translation estimate
`‖φ(· + z) − φ‖₂ ≤ |z| ‖Dφ‖₂` for test functions and density of test jets in `H¹₀`. -/

set_option autoImplicit false
set_option linter.all false

section Q4517_I
/-! Shortcut instances for `H¹₀(Ω)` and `H⁻¹(Ω)`: each one is exactly the instance that type-class
search finds anyway (`inferInstance`), declared once with high priority so that later searches stop at
it instead of re-deriving it through the submodule / continuous-linear-map hierarchy every time.
They are `scoped` (opened in each block below, not at the final `theorem solution`), so the
statement of `solution` is elaborated with the standard instances, exactly like the target's. -/
open MeasureTheory
namespace HunterPDE.Parabolic.Q4517Fast
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
noncomputable scoped instance (priority := high) q4517EMS : MeasureSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
noncomputable scoped instance (priority := high) q4517H10NACG : NormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517H10SACG : SeminormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517H10IPS : InnerProductSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517H10NS : NormedSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517H10Mod : Module ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1NACG : NormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1SACG : SeminormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1NS : NormedSpace ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1Mod : Module ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1CS : CompleteSpace (Hm1 n Ω) := inferInstance
end HunterPDE.Parabolic.Q4517Fast
end Q4517_I


section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q4517Fast

/-! ## R1: the translation inequality `‖φ(· + z) − φ‖₂ ≤ |z| ‖Dφ‖₂` for `C¹_c` functions -/

/-- Cauchy–Schwarz on `[0, 1]`: `(∫₀¹ a)² ≤ ∫₀¹ a²` for continuous `a`. -/
lemma sq_intervalIntegral_le {a : ℝ → ℝ} (ha : Continuous a) :
    (∫ s in (0 : ℝ)..1, a s) ^ 2 ≤ ∫ s in (0 : ℝ)..1, a s ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ s in (0 : ℝ)..1, a s := ⟨_, rfl⟩
  have key : 0 ≤ ∫ s in (0 : ℝ)..1, (a s - A) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => sq_nonneg _)
  have h1 : (fun s => (a s - A) ^ 2) = fun s => (a s ^ 2 - 2 * A * a s) + A ^ 2 := by
    funext s; ring
  have i1 : IntervalIntegrable (fun s => a s ^ 2) volume 0 1 := (ha.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => 2 * A * a s) volume 0 1 :=
    (continuous_const.mul ha).intervalIntegrable _ _
  rw [h1, intervalIntegral.integral_add (i1.sub i2) intervalIntegrable_const,
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, ← hA] at key
  simp only [sub_zero, smul_eq_mul, one_mul] at key
  rw [← hA]
  nlinarith

variable {n : ℕ}

lemma pt_transl {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (x z : EuclideanSpace ℝ (Fin n)) :
    ‖φ (x + z) - φ x‖ₑ ^ 2 ≤
      ‖z‖ₑ ^ 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x + s • z)‖ₑ ^ 2 := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hcf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hline : Continuous fun s : ℝ => x + s • z := continuous_const.add (continuous_id.smul continuous_const)
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => φ (x + s • z)) (fderiv ℝ φ (x + s • z) z) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • z) z s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_add x
    exact (hdiff (x + s • z)).hasFDerivAt.comp_hasDerivAt s h1
  have hgc : Continuous fun s : ℝ => fderiv ℝ φ (x + s • z) z :=
    (hcf.comp hline).clm_apply continuous_const
  have hftc : ∫ s in (0 : ℝ)..1, fderiv ℝ φ (x + s • z) z = φ (x + z) - φ x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hgc.intervalIntegrable _ _)]
    simp
  obtain ⟨a, ha⟩ : ∃ a : ℝ → ℝ, a = fun s => ‖fderiv ℝ φ (x + s • z)‖ := ⟨_, rfl⟩
  have hac : Continuous a := by rw [ha]; exact (hcf.comp hline).norm
  have hbound : |φ (x + z) - φ x| ≤ ‖z‖ * ∫ s in (0 : ℝ)..1, a s := by
    rw [← hftc, ← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine intervalIntegral.integral_mono_on zero_le_one ((hgc.abs).intervalIntegrable _ _)
      ((continuous_const.mul hac).intervalIntegrable _ _) fun s _ => ?_
    rw [ha, mul_comm]
    exact (fderiv ℝ φ (x + s • z)).le_opNorm z
  have hA0 : 0 ≤ ∫ s in (0 : ℝ)..1, a s :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ => by rw [ha]; exact norm_nonneg _
  have hsq : (φ (x + z) - φ x) ^ 2 ≤ ‖z‖ ^ 2 * ∫ s in (0 : ℝ)..1, a s ^ 2 := by
    have h1 : (φ (x + z) - φ x) ^ 2 ≤ (‖z‖ * ∫ s in (0 : ℝ)..1, a s) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
    have h2 := sq_intervalIntegral_le hac
    calc (φ (x + z) - φ x) ^ 2 ≤ (‖z‖ * ∫ s in (0 : ℝ)..1, a s) ^ 2 := h1
      _ = ‖z‖ ^ 2 * (∫ s in (0 : ℝ)..1, a s) ^ 2 := by ring
      _ ≤ ‖z‖ ^ 2 * ∫ s in (0 : ℝ)..1, a s ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hlin : ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x + s • z)‖ₑ ^ 2 =
      ENNReal.ofReal (∫ s in (0 : ℝ)..1, a s ^ 2) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun s => ?_
      rw [ha, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    · exact ((hac.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact Filter.Eventually.of_forall fun s => sq_nonneg _
  rw [hlin, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs, sq_abs]
  exact hsq

lemma transl_ineq {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (z : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ x, ‖φ (x + z) - φ x‖ₑ ^ 2 ≤ ‖z‖ₑ ^ 2 * ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ 2 := by
  have hcf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  calc ∫⁻ x, ‖φ (x + z) - φ x‖ₑ ^ 2
      ≤ ∫⁻ x, ‖z‖ₑ ^ 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x + s • z)‖ₑ ^ 2 :=
        lintegral_mono fun x => pt_transl hφ x z
    _ = ‖z‖ₑ ^ 2 * ∫⁻ x, ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x + s • z)‖ₑ ^ 2 := by
        rw [lintegral_const_mul']
        exact ENNReal.pow_ne_top enorm_ne_top
    _ = ‖z‖ₑ ^ 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x, ‖fderiv ℝ φ (x + s • z)‖ₑ ^ 2 := by
        rw [lintegral_lintegral_swap]
        exact ((hcf.comp (continuous_fst.add (continuous_snd.smul continuous_const))).enorm.measurable.pow_const 2).aemeasurable
    _ = ‖z‖ₑ ^ 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ 2 := by
        congr 1
        refine lintegral_congr fun s => ?_
        exact lintegral_add_right_eq_self (fun y => ‖fderiv ℝ φ y‖ₑ ^ 2) (s • z)
    _ = ‖z‖ₑ ^ 2 * ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ 2 := by
        rw [setLIntegral_const, Real.volume_Ioc]
        simp

/-! ## R2: the grid of cubes of side `h` -/

/-- The integer index of the grid cube of side `h` containing `x`. -/
noncomputable def idx (h : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Fin n → ℤ := fun i => ⌊x i / h⌋

/-- The grid cube of side `h` with index `k`. -/
def cube (h : ℝ) (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) := {x | idx h x = k}

lemma measurable_idx (h : ℝ) : Measurable (idx (n := n) h) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hc : Continuous fun x : EuclideanSpace ℝ (Fin n) => x i := (EuclideanSpace.proj i).continuous
  exact Int.measurable_floor.comp (hc.measurable.div_const h)

lemma measurableSet_cube (h : ℝ) (k : Fin n → ℤ) : MeasurableSet (cube (n := n) h k) :=
  measurable_idx h (measurableSet_singleton k)

lemma mem_cube_iff {h : ℝ} (hh : 0 < h) {k : Fin n → ℤ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ cube h k ↔ ∀ i, (k i : ℝ) * h ≤ x i ∧ x i < ((k i : ℝ) + 1) * h := by
  simp only [cube, idx, mem_setOf_eq, funext_iff, Int.floor_eq_iff, le_div_iff₀ hh, div_lt_iff₀ hh]

lemma mem_cube_idx (h : ℝ) (x : EuclideanSpace ℝ (Fin n)) : x ∈ cube h (idx h x) := rfl

lemma volume_cube {h : ℝ} (hh : 0 < h) (k : Fin n → ℤ) :
    volume (cube (n := n) h k) = ENNReal.ofReal h ^ n := by
  have hset : cube (n := n) h k =
      (WithLp.ofLp) ⁻¹' (univ.pi fun i => Ico ((k i : ℝ) * h) (((k i : ℝ) + 1) * h)) := by
    ext x
    rw [mem_cube_iff hh]
    simp [Set.mem_pi]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  simp only [add_mul, one_mul, add_sub_cancel_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

lemma dist_lt_of_mem_cube {h : ℝ} (hh : 0 < h) {k : Fin n → ℤ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ cube h k) (hy : y ∈ cube h k) : dist x y < (n + 1) * h := by
  rw [EuclideanSpace.dist_eq, Real.sqrt_lt' (by positivity)]
  have hi : ∀ i, dist (x i) (y i) ^ 2 ≤ h ^ 2 := fun i => by
    obtain ⟨a1, a2⟩ := (mem_cube_iff hh).1 hx i
    obtain ⟨b1, b2⟩ := (mem_cube_iff hh).1 hy i
    rw [Real.dist_eq, sq_abs]
    nlinarith
  calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin n, h ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = n * h ^ 2 := by simp
    _ < ((n + 1) * h) ^ 2 := by
        have : (0 : ℝ) < h ^ 2 := by positivity
        nlinarith

/-! ## R3: the cube-average approximation and its error -/

/-- The average of `φ` over the grid cube containing `x`. -/
noncomputable def cubeAvg (h : ℝ) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (h ^ n)⁻¹ * ∫ y in cube h (idx h x), φ y

lemma sq_integral_le_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {F : α → ℝ} (hF : Integrable F ν) (hF2 : Integrable (fun y => F y ^ 2) ν) :
    (∫ y, F y ∂ν) ^ 2 ≤ ν.real univ * ∫ y, F y ^ 2 ∂ν := by
  rcases eq_or_lt_of_le (measureReal_nonneg (μ := ν) (s := univ)) with hm | hm
  · have hν : ν = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      rw [Measure.real, eq_comm, ENNReal.toReal_eq_zero_iff] at hm
      exact hm.resolve_right (measure_ne_top ν univ)
    subst hν
    simp
  obtain ⟨c, hc⟩ : ∃ c, c = (∫ y, F y ∂ν) / ν.real univ := ⟨_, rfl⟩
  have hcm : c * ν.real univ = ∫ y, F y ∂ν := by rw [hc]; field_simp
  have key : 0 ≤ ∫ y, (F y - c) ^ 2 ∂ν := integral_nonneg fun y => sq_nonneg _
  have h1 : (fun y => (F y - c) ^ 2) = fun y => (F y ^ 2 - 2 * c * F y) + c ^ 2 := by
    funext y; ring
  have i1 : Integrable (fun y => F y ^ 2 - 2 * c * F y) ν := hF2.sub (hF.const_mul _)
  have i2 : Integrable (fun y => 2 * c * F y) ν := hF.const_mul _
  rw [h1, integral_add i1 (integrable_const _), integral_sub hF2 i2, integral_const_mul,
    integral_const, smul_eq_mul] at key
  rw [← hcm] at key ⊢
  nlinarith [mul_nonneg hm.le key]

lemma pt_avg {h : ℝ} (hh : 0 < h) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφc : Continuous φ)
    {M : ℝ} (hM : ∀ y, |φ y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    ‖φ x - cubeAvg h φ x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((h ^ n)⁻¹) * ∫⁻ y in cube h (idx h x), ‖φ x - φ y‖ₑ ^ 2 := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cube (n := n) h (idx h x) := ⟨_, rfl⟩
  have hvol : volume Q = ENNReal.ofReal h ^ n := by rw [hQ]; exact volume_cube hh _
  have : IsFiniteMeasure (volume.restrict Q) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, hvol]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hreal : (volume.restrict Q).real univ = h ^ n := by
    rw [Measure.real, Measure.restrict_apply_univ, hvol, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hh.le]
  have hbF : ∀ y, ‖φ x - φ y‖ ≤ 2 * M := fun y => by
    rw [Real.norm_eq_abs]
    have := abs_sub (φ x) (φ y)
    linarith [hM x, hM y]
  have hFi : Integrable (fun y => φ x - φ y) (volume.restrict Q) :=
    (memLp_top_of_bound (continuous_const.sub hφc).aestronglyMeasurable (2 * M)
      (Filter.Eventually.of_forall hbF)).integrable le_top
  have hφi : Integrable φ (volume.restrict Q) :=
    (memLp_top_of_bound hφc.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)).integrable le_top
  have hF2i : Integrable (fun y => (φ x - φ y) ^ 2) (volume.restrict Q) :=
    (memLp_top_of_bound (f := fun y => (φ x - φ y) ^ 2)
      ((continuous_const.sub hφc).pow 2).aestronglyMeasurable ((2 * M) ^ 2)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using hbF y) 2)).integrable le_top
  have hdiff : φ x - cubeAvg h φ x = (h ^ n)⁻¹ * ∫ y in Q, (φ x - φ y) := by
    rw [integral_sub (integrable_const _) hφi, integral_const, smul_eq_mul, hreal, cubeAvg, ← hQ]
    have : (h ^ n) ≠ 0 := by positivity
    field_simp
  have hCS := sq_integral_le_mul hFi hF2i
  rw [hreal] at hCS
  have hsq : (φ x - cubeAvg h φ x) ^ 2 ≤ (h ^ n)⁻¹ * ∫ y in Q, (φ x - φ y) ^ 2 := by
    rw [hdiff, mul_pow]
    have hpos : (0 : ℝ) < h ^ n := by positivity
    calc ((h ^ n)⁻¹) ^ 2 * (∫ y in Q, (φ x - φ y)) ^ 2
        ≤ ((h ^ n)⁻¹) ^ 2 * (h ^ n * ∫ y in Q, (φ x - φ y) ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ = (h ^ n)⁻¹ * ∫ y in Q, (φ x - φ y) ^ 2 := by field_simp
  have hlin : ∫⁻ y in Q, ‖φ x - φ y‖ₑ ^ 2 = ENNReal.ofReal (∫ y in Q, (φ x - φ y) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hF2i (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  rw [← hQ, hlin, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  exact ENNReal.ofReal_le_ofReal hsq

lemma lintegral_ball_shift (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (x : EuclideanSpace ℝ (Fin n))
    (R : ℝ) : ∫⁻ y in Metric.ball x R, g y = ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, g (x + z) := by
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← lintegral_add_left_eq_self _ x]
  refine lintegral_congr fun z => ?_
  have hiff : x + z ∈ Metric.ball x R ↔ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    simp [Metric.mem_ball, dist_eq_norm]
  by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
  · rw [indicator_of_mem (hiff.2 hz), indicator_of_mem hz]
  · rw [indicator_of_notMem (fun h' => hz (hiff.1 h')), indicator_of_notMem hz]

lemma vol_ball_scale {R : ℝ} (hR : 0 < R) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) =
      ENNReal.ofReal (R ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  by_cases hn : n = 0
  · subst hn
    have hz : ∀ x : EuclideanSpace ℝ (Fin 0), x = 0 := fun x => by ext i; exact i.elim0
    have h1 : ∀ r : ℝ, 0 < r → Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) r = univ :=
      fun r hr => by
        ext x
        simp [hz x, hr]
    rw [h1 R hR, h1 1 one_pos]
    simp
  · have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      ⟨⟨EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero hn⟩ 1, 0, by simp⟩⟩
    rw [Measure.addHaar_ball _ _ hR.le, finrank_euclideanSpace_fin]

lemma avg_error {h : ℝ} (hh : 0 < h) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    ∫⁻ x, ‖φ x - cubeAvg h φ x‖ₑ ^ 2 ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ (n + 2) * h ^ 2) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) * ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ 2 := by
  have hφc : Continuous φ := hφ.continuous
  obtain ⟨M, hM⟩ : ∃ M, ∀ y, |φ y| ≤ M := by
    obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hc
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((n : ℝ) + 1) * h := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨G, hG⟩ : ∃ G, G = ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ 2 := ⟨_, rfl⟩
  have hcont2 : Continuous fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖φ p.1 - φ (p.1 + p.2)‖ₑ :=
    (hφc.comp continuous_fst |>.sub (hφc.comp (continuous_fst.add continuous_snd))).enorm
  rw [← hG]
  calc ∫⁻ x, ‖φ x - cubeAvg h φ x‖ₑ ^ 2
      ≤ ∫⁻ x, ENNReal.ofReal ((h ^ n)⁻¹) * ∫⁻ y in cube h (idx h x), ‖φ x - φ y‖ₑ ^ 2 :=
        lintegral_mono fun x => pt_avg hh hφc hM x
    _ ≤ ∫⁻ x, ENNReal.ofReal ((h ^ n)⁻¹) * ∫⁻ y in Metric.ball x R, ‖φ x - φ y‖ₑ ^ 2 := by
        refine lintegral_mono fun x => mul_le_mul_right (lintegral_mono_set fun y hy => ?_) _
        rw [Metric.mem_ball, hR]
        exact dist_lt_of_mem_cube hh hy (mem_cube_idx h x)
    _ = ∫⁻ x, ENNReal.ofReal ((h ^ n)⁻¹) *
          ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖φ x - φ (x + z)‖ₑ ^ 2 := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_ball_shift (fun y => ‖φ x - φ y‖ₑ ^ 2) x R]
    _ = ENNReal.ofReal ((h ^ n)⁻¹) *
          ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, ∫⁻ x, ‖φ x - φ (x + z)‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap]
        exact (hcont2.measurable.pow_const 2).aemeasurable
    _ ≤ ENNReal.ofReal ((h ^ n)⁻¹) * ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal R ^ 2 * G := by
        refine mul_le_mul_right (setLIntegral_mono' Metric.isOpen_ball.measurableSet
          fun z hz => ?_) _
        have h1 := transl_ineq hφ z
        have h2 : ∫⁻ x, ‖φ x - φ (x + z)‖ₑ ^ 2 = ∫⁻ x, ‖φ (x + z) - φ x‖ₑ ^ 2 :=
          lintegral_congr fun x => by rw [enorm_sub_rev]
        rw [h2]
        rw [← hG] at h1
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
        rw [← ofReal_norm_eq_enorm]
        exact pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal
          (le_of_lt (by simpa using hz))) 2
    _ = ENNReal.ofReal ((h ^ n)⁻¹) * (ENNReal.ofReal R ^ 2 * G *
          (ENNReal.ofReal (R ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
        rw [setLIntegral_const, vol_ball_scale (by rw [hR]; positivity)]
    _ = ENNReal.ofReal ((h ^ n)⁻¹) * ENNReal.ofReal R ^ 2 * ENNReal.ofReal (R ^ n) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) * G := by ring
    _ = ENNReal.ofReal (((n : ℝ) + 1) ^ (n + 2) * h ^ 2) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) * G := by
        have hid : (h ^ n)⁻¹ * R ^ 2 * R ^ n = ((n : ℝ) + 1) ^ (n + 2) * h ^ 2 := by
          rw [hR, mul_pow, mul_pow]
          have : (h ^ n) ≠ 0 := by positivity
          field_simp
          ring
        congr 2
        rw [← ENNReal.ofReal_pow hR0,
          ← ENNReal.ofReal_mul (inv_nonneg.2 (by positivity) : (0 : ℝ) ≤ (h ^ n)⁻¹),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (h ^ n)⁻¹ * R ^ 2), hid]

/-! ## R4: finite-rank compact operators -/

lemma isCompactOperator_sum_rankOne {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {ι : Type*} (s : Finset ι) (ℓ : ι → X →L[ℝ] ℝ)
    (v : ι → Y) : IsCompactOperator (fun x => ∑ k ∈ s, ℓ k x • v k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun x : X => ∑ k ∈ (∅ : Finset ι), ℓ k x • v k) = (0 : X → Y) := by
      funext x; simp
    rw [this]
    exact isCompactOperator_zero
  | insert a s ha ih =>
    have h1 : IsCompactOperator (fun x => ℓ a x • v a) := by
      refine ⟨(fun t : ℝ => t • v a) '' Metric.closedBall 0 ‖ℓ a‖,
        (isCompact_closedBall 0 _).image (continuous_id.smul continuous_const), ?_⟩
      refine Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) fun x hx =>
        ⟨ℓ a x, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
      calc ‖ℓ a x‖ ≤ ‖ℓ a‖ * ‖x‖ := (ℓ a).le_opNorm x
        _ ≤ ‖ℓ a‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = ‖ℓ a‖ := mul_one _
    have h2 := h1.add ih
    have : (fun x => ∑ k ∈ insert a s, ℓ k x • v k) =
        (fun x => ℓ a x • v a) + fun x => ∑ k ∈ s, ℓ k x • v k := by
      funext x
      simp [Finset.sum_insert ha]
    rw [this]
    exact h2

/-! ## R5: the grid projection on `L²(Ω)` -/

section grid
variable {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma cube_fin (Ω : Set (EuclideanSpace ℝ (Fin n))) {h : ℝ} (hh : 0 < h) (k : Fin n → ℤ) :
    (volume.restrict Ω) (cube h k) ≠ ∞ :=
  ((Measure.restrict_le_self (cube h k)).trans_lt
    (by rw [volume_cube hh]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top)).ne

/-- The indicator of the grid cube `k`, in `L²(Ω)`. -/
noncomputable def eC (Ω : Set (EuclideanSpace ℝ (Fin n))) {h : ℝ} (hh : 0 < h) (k : Fin n → ℤ) :
    Lp ℝ 2 (volume.restrict Ω) :=
  indicatorConstLp 2 (measurableSet_cube h k) (cube_fin Ω hh k) (1 : ℝ)

/-- The finite index box `[-N, N]ⁿ`. -/
noncomputable def Kset (n : ℕ) (N : ℤ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-N) N

/-- The grid projection: cube averages over the cubes with index in `[-N, N]ⁿ`. -/
noncomputable def Ph (Ω : Set (EuclideanSpace ℝ (Fin n))) {h : ℝ} (hh : 0 < h) (N : ℤ) :
    Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ∑ k ∈ Kset n N, ((h ^ n)⁻¹ • innerSL ℝ (eC Ω hh k)).smulRight (eC Ω hh k)

lemma Ph_apply {h : ℝ} (hh : 0 < h) (N : ℤ) (f : Lp ℝ 2 (volume.restrict Ω)) :
    Ph Ω hh N f = ∑ k ∈ Kset n N, ((h ^ n)⁻¹ * inner ℝ (eC Ω hh k) f) • eC Ω hh k := by
  simp [Ph, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

lemma Ph_compact {h : ℝ} (hh : 0 < h) (N : ℤ) : IsCompactOperator (Ph Ω hh N) := by
  have := isCompactOperator_sum_rankOne (Kset n N)
    (fun k => (h ^ n)⁻¹ • innerSL ℝ (eC Ω hh k)) (fun k => eC Ω hh k)
  have e : ⇑(Ph Ω hh N) = fun f => ∑ k ∈ Kset n N,
      ((h ^ n)⁻¹ • innerSL ℝ (eC Ω hh k)) f • eC Ω hh k := by
    funext f
    rw [Ph_apply]
    simp
  rw [e]
  exact this

lemma coeFn_sum_smul {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (e : ι → Lp ℝ 2 μ) :
    ((∑ k ∈ s, a k • e k : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ] fun x => ∑ k ∈ s, a k * (e k : X → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    filter_upwards [Lp.coeFn_add (a b • e b) (∑ k ∈ s, a k • e k), Lp.coeFn_smul (a b) (e b), ih]
      with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

lemma idx_mem_Kset {h R0 : ℝ} (hh : 0 < h) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R0) :
    idx h x ∈ Kset n (⌈R0 / h⌉ + 1) := by
  rw [Kset, Fintype.mem_piFinset]
  intro i
  have hxi : |x i| ≤ R0 := (by simpa using PiLp.norm_apply_le x i : ‖x i‖ ≤ ‖x‖).trans hx
  have ht1 : x i / h ≤ R0 / h := div_le_div_of_nonneg_right (abs_le.1 hxi).2 hh.le
  have ht2 : -(R0 / h) ≤ x i / h := by
    rw [← neg_div]; exact div_le_div_of_nonneg_right (abs_le.1 hxi).1 hh.le
  have a1 : (⌊x i / h⌋ : ℝ) ≤ x i / h := Int.floor_le _
  have a2 : x i / h < ⌊x i / h⌋ + 1 := Int.lt_floor_add_one _
  have b1 : R0 / h ≤ (⌈R0 / h⌉ : ℝ) := Int.le_ceil _
  rw [Finset.mem_Icc]
  constructor
  · have : (-(⌈R0 / h⌉ + 1) : ℤ) < ⌊x i / h⌋ := by
      have : ((-(⌈R0 / h⌉ + 1) : ℤ) : ℝ) < (⌊x i / h⌋ : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact this.le
  · have : (⌊x i / h⌋ : ℝ) ≤ ((⌈R0 / h⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- `‖f‖² = ∫ ‖f‖²` for `L²` functions, in `ℝ≥0∞`. -/
lemma ofReal_norm_sq_Lp {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (f : Lp F 2 μ) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ x, ‖(f : X → F) x‖ₑ ^ 2 ∂μ := by
  have h1 : ‖f‖ ^ 2 = ∫ x, ‖(f : X → F) x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq _)
  have hint : Integrable (fun x => ‖(f : X → F) x‖ ^ 2) μ :=
    (L2.integrable_inner (𝕜 := ℝ) f f).congr
      (Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq _)
  rw [h1, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- The first-component map `L²(Ω; ℝ × ℝⁿ) → L²(Ω)`. -/
noncomputable def Gfst (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    JetL2 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)

lemma est_testJet (hΩo : IsOpen Ω) {R0 : ℝ} (hR0 : Ω ⊆ Metric.closedBall 0 R0) {h : ℝ}
    (hh : 0 < h) (y : JetL2 n Ω) (hy : y ∈ testJets n Ω) :
    ENNReal.ofReal (‖Gfst n Ω y - Ph Ω hh (⌈R0 / h⌉ + 1) (Gfst n Ω y)‖ ^ 2) ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ (n + 2) * h ^ 2) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) * ENNReal.ofReal (‖y‖ ^ 2) := by
  obtain ⟨φ, hφs, hφc, hφΩ, hyae⟩ := hy
  have hφ0 : ∀ x, x ∉ Ω → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h' => hx (hφΩ h'))
  have hGy : (Gfst n Ω y : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict Ω] φ := by
    have := (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLp
      (μ := volume.restrict Ω) (p := 2) y
    filter_upwards [this, hyae] with x h1 h2
    show ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp y :
      EuclideanSpace ℝ (Fin n) → ℝ) x = φ x
    rw [h1, h2]
    rfl
  have hcoef : ∀ k, inner ℝ (eC Ω hh k) (Gfst n Ω y) = ∫ x in cube h k, φ x := by
    intro k
    rw [eC, L2.inner_indicatorConstLp_one]
    rw [integral_congr_ae (ae_restrict_of_ae hGy), Measure.restrict_restrict
      (measurableSet_cube h k)]
    exact (setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_cube h k)
      inter_subset_left fun x hx => hφ0 x (fun h' => hx.2 ⟨hx.1, h'⟩)).symm
  have hPh := coeFn_sum_smul (μ := volume.restrict Ω) (Kset n (⌈R0 / h⌉ + 1))
    (fun k => (h ^ n)⁻¹ * inner ℝ (eC Ω hh k) (Gfst n Ω y)) (fun k => eC Ω hh k)
  have hind : ∀ᵐ x ∂(volume.restrict Ω), ∀ k ∈ Kset n (⌈R0 / h⌉ + 1),
      (eC Ω hh k : EuclideanSpace ℝ (Fin n) → ℝ) x = (cube h k).indicator (fun _ => (1 : ℝ)) x := by
    rw [Finset.eventually_all]
    intro k _
    exact indicatorConstLp_coeFn
  have hdiff : ∀ᵐ x ∂(volume.restrict Ω),
      ((Gfst n Ω y - Ph Ω hh (⌈R0 / h⌉ + 1) (Gfst n Ω y) : Lp ℝ 2 (volume.restrict Ω)) :
        EuclideanSpace ℝ (Fin n) → ℝ) x = φ x - cubeAvg h φ x := by
    filter_upwards [Lp.coeFn_sub (Gfst n Ω y) (Ph Ω hh (⌈R0 / h⌉ + 1) (Gfst n Ω y)), hGy, hPh,
      hind, ae_restrict_mem hΩo.measurableSet] with x h1 h2 h3 h4 hxΩ
    rw [h1, Pi.sub_apply, h2, Ph_apply, h3]
    congr 1
    have hmem := idx_mem_Kset hh (by simpa using hR0 hxΩ : ‖x‖ ≤ R0)
    rw [Finset.sum_eq_single (idx h x)]
    · rw [h4 _ hmem, indicator_of_mem (mem_cube_idx h x), mul_one, hcoef, cubeAvg]
    · intro k hk hne
      rw [h4 k hk, indicator_of_notMem, mul_zero]
      exact fun h' => hne h'.symm
    · exact fun h' => absurd hmem h'
  -- the gradient part of `‖y‖²`
  have hgrad : ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ 2 ≤ ENNReal.ofReal (‖y‖ ^ 2) := by
    rw [ofReal_norm_sq_Lp]
    calc ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ 2 = ∫⁻ x in Ω, ‖fderiv ℝ φ x‖ₑ ^ 2 := by
          refine (setLIntegral_eq_of_support_subset ?_).symm
          intro x hx
          by_contra hxΩ
          apply hx
          have : fderiv ℝ φ x = 0 := by
            by_contra hne
            exact hxΩ (hφΩ (support_fderiv_subset ℝ hne))
          show ‖fderiv ℝ φ x‖ₑ ^ 2 = 0
          rw [this, ← ofReal_norm_eq_enorm, norm_zero, ENNReal.ofReal_zero]
          simp
      _ ≤ ∫⁻ x, ‖(y : EuclideanSpace ℝ (Fin n) → Jet n) x‖ₑ ^ 2 ∂(volume.restrict Ω) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hyae] with x hx
          rw [hx, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
            ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hg : ‖gradient φ x‖ = ‖fderiv ℝ φ x‖ := by
            show ‖(InnerProductSpace.toDual ℝ _).symm (fderiv ℝ φ x)‖ = _
            exact LinearIsometryEquiv.norm_map _ _
          have key : ‖(WithLp.toLp 2 (φ x, gradient φ x) : Jet n)‖ ^ 2 =
              ‖φ x‖ ^ 2 + ‖gradient φ x‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _
          rw [key, hg]
          nlinarith [sq_nonneg ‖φ x‖]
  have hφ1 : ContDiff ℝ 1 φ := hφs.of_le (by exact_mod_cast le_top)
  have hmain := avg_error hh hφ1 hφc
  rw [ofReal_norm_sq_Lp]
  calc ∫⁻ x, ‖((Gfst n Ω y - Ph Ω hh (⌈R0 / h⌉ + 1) (Gfst n Ω y) : Lp ℝ 2 (volume.restrict Ω)) :
          EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ ^ 2 ∂(volume.restrict Ω)
      = ∫⁻ x in Ω, ‖φ x - cubeAvg h φ x‖ₑ ^ 2 := lintegral_congr_ae (by
          filter_upwards [hdiff] with x hx
          rw [hx])
    _ ≤ ∫⁻ x, ‖φ x - cubeAvg h φ x‖ₑ ^ 2 := setLIntegral_le_lintegral _ _
    _ ≤ _ := hmain
    _ ≤ _ := by gcongr

/-- Every element of the span of the test jets is a test jet. -/
lemma span_testJets_subset : (Submodule.span ℝ (testJets n Ω) : Set (JetL2 n Ω)) ⊆ testJets n Ω := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero =>
    refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, ?_⟩
    filter_upwards [Lp.coeFn_zero (Jet n) 2 (volume.restrict Ω)] with x hx
    have hg : gradient (0 : EuclideanSpace ℝ (Fin n) → ℝ) x = 0 := by
      show (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ (fun _ => (0 : ℝ)) x) = 0
      rw [fderiv_const_apply, map_zero]
    rw [hx]
    simp [hg]
    rw [Prod.mk_zero_zero, WithLp.toLp_zero]
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨φ₁, s₁, c₁, t₁, e₁⟩ := h₁
    obtain ⟨φ₂, s₂, c₂, t₂, e₂⟩ := h₂
    refine ⟨φ₁ + φ₂, s₁.add s₂, c₁.add c₂,
      (tsupport_add φ₁ φ₂).trans (union_subset t₁ t₂), ?_⟩
    filter_upwards [Lp.coeFn_add y₁ y₂, e₁, e₂] with x h0 h1 h2
    rw [h0, Pi.add_apply, h1, h2, ← WithLp.toLp_add]
    congr 1
    have hg : gradient (φ₁ + φ₂) x = gradient φ₁ x + gradient φ₂ x := by
      simp only [gradient]
      rw [fderiv_add (s₁.differentiable (by simp) x) (s₂.differentiable (by simp) x), map_add]
    simp [hg]
  | smul a y _ h =>
    obtain ⟨φ, s, c, t, e⟩ := h
    refine ⟨a • φ, s.const_smul a, c.smul_left,
      (show tsupport (a • φ) ⊆ tsupport φ from tsupport_smul_subset_right (fun _ => a) φ).trans t, ?_⟩
    filter_upwards [Lp.coeFn_smul a y, e] with x h0 h1
    rw [h0, Pi.smul_apply, h1, ← WithLp.toLp_smul]
    congr 1
    have hg : gradient (a • φ) x = a • gradient φ x := by
      simp only [gradient]
      rw [fderiv_const_smul (s.differentiable (by simp) x), map_smul]
    simp [hg]

/-- The `L²` error of the grid projection on all of `H¹₀(Ω)`. -/
lemma est_H10 (hΩo : IsOpen Ω) {R0 : ℝ} (hR0 : Ω ⊆ Metric.closedBall 0 R0) {h : ℝ}
    (hh : 0 < h) (u : H10 n Ω) :
    ‖toL2L n Ω u - Ph Ω hh (⌈R0 / h⌉ + 1) (toL2L n Ω u)‖ ^ 2 ≤
      (((n : ℝ) + 1) ^ (n + 2) * h ^ 2 *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) * ‖u‖ ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ((n : ℝ) + 1) ^ (n + 2) * h ^ 2 *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  have hB : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hclosed : IsClosed {y : JetL2 n Ω |
      ‖Gfst n Ω y - Ph Ω hh (⌈R0 / h⌉ + 1) (Gfst n Ω y)‖ ^ 2 ≤ A * ‖y‖ ^ 2} :=
    isClosed_le (((Gfst n Ω).continuous.sub
      ((Ph Ω hh (⌈R0 / h⌉ + 1)).continuous.comp (Gfst n Ω).continuous)).norm.pow 2)
      (continuous_const.mul (continuous_norm.pow 2))
  have hsub : (H10 n Ω : Set (JetL2 n Ω)) ⊆ {y : JetL2 n Ω |
      ‖Gfst n Ω y - Ph Ω hh (⌈R0 / h⌉ + 1) (Gfst n Ω y)‖ ^ 2 ≤ A * ‖y‖ ^ 2} := by
    rw [H10, Submodule.topologicalClosure_coe]
    refine closure_minimal (fun y hy => ?_) hclosed
    have h1 := est_testJet hΩo hR0 hh y (span_testJets_subset hy)
    rw [← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    show _ ≤ A * ‖y‖ ^ 2
    rw [hA]
    exact h1
  have := hsub u.2
  rw [← hA]
  exact this

end grid

/-! ## R7: Rellich -/

theorem toL2L_isCompactOperator {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) : IsCompactOperator (toL2L n Ω) := by
  obtain ⟨R0, hR0⟩ := hΩb.subset_closedBall 0
  have hh : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => by positivity
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ((n : ℝ) + 1) ^ (n + 2) *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  let F : ℕ → H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) := fun m =>
    (Ph Ω (hh m) (⌈R0 / (1 / ((m : ℝ) + 1))⌉ + 1)).comp (toL2L n Ω)
  have hF : ∀ m, IsCompactOperator (F m) := fun m => (Ph_compact (hh m) _).comp_clm _
  have hbound : ∀ m, ‖F m - toL2L n Ω‖ ≤ Real.sqrt B * (1 / ((m : ℝ) + 1)) := by
    intro m
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    have h1 := est_H10 hΩo hR0 (hh m) u
    have h2 : ‖(F m - toL2L n Ω) u‖ = ‖toL2L n Ω u -
        Ph Ω (hh m) (⌈R0 / (1 / ((m : ℝ) + 1))⌉ + 1) (toL2L n Ω u)‖ := by
      rw [norm_sub_rev]
      rfl
    rw [h2]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    calc _ ≤ _ := h1
      _ = (Real.sqrt B * (1 / ((m : ℝ) + 1)) * ‖u‖) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hB0, hBdef]
          ring
  have hT : Filter.Tendsto F Filter.atTop (𝓝 (toL2L n Ω)) := by
    refine (tendsto_iff_norm_sub_tendsto_zero (f := F)).2 ?_
    refine squeeze_zero (fun m => (norm_nonneg (F m - toL2L n Ω) :)) hbound ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Real.sqrt B)
    simpa using this
  exact isCompactOperator_of_tendsto hT (Filter.Eventually.of_forall hF)

end HunterPDE.Parabolic

end

open MeasureTheory HunterPDE.Parabolic in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) : IsCompactOperator (toL2L n Ω) :=
  toL2L_isCompactOperator Ω hΩo hΩb
